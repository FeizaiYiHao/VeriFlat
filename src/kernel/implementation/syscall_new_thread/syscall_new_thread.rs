use vstd::prelude::*;
use crate::*;
use super::syscall_new_thread_helpers::{
    add_new_thread_to_proc_container_and_scheduler,
    kernel_u_new_thread_changed,
};

verus! {
        /// syscall_new_thread: create a new thread in the running process on
        /// `cpu_id`. Lock order: cpu -> process -> current thread -> scheduler.
        pub fn syscall_new_thread(
            kernel: &mut KernelK,
            Tracked(lctx): Tracked<&mut LocalContext>,
            Tracked(steps): Tracked<&mut KernelSteps>,
            cpu_id: CpuId,
        ) -> (ret: RetValueType)
            requires
                index_valid(NUM_CPUS, cpu_id),
                old(kernel).inv(),
                old(kernel).cpu_array.spec_index(cpu_id).view().view().state == CpuState::Running,
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
                old(kernel).cpu_array.spec_index(cpu_id).view().locked_by(old(lctx)) == false,
                {
                    let process_ptr =
                        old(kernel).cpu_array.spec_index(cpu_id).view().view().current_process->Some_0;
                    let container_ptr =
                        old(kernel).process_map.spec_index(process_ptr)
                            .view_rodata().view().owning_container;
                    let scheduler_ptr =
                        old(kernel).container_map.spec_index(container_ptr)
                            .view_rodata().view().scheduler;
                    &&& old(kernel).process_map.spec_index(process_ptr)
                        .locked_by(old(lctx)) == false
                    &&& old(kernel).scheduler_map.spec_index(scheduler_ptr)
                        .locked_by(old(lctx)) == false
                },
                old(steps).steps.len() == 0,
                old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
                lock_id_aligned(old(kernel), old(lctx)),
                old(kernel).all_objects_unlocked(old(lctx)),
            ensures
                final(steps).steps.len() <= 1,
                final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
                lock_id_aligned(final(kernel), final(lctx)),
                final(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
                final(kernel).all_objects_unlocked(final(lctx)),
                !(ret is Success) ==> final(steps).steps.len() == 0,
                ret is Success ==> {
                    let process_ptr = old(kernel).cpu_array.spec_index(cpu_id).view().view().current_process->Some_0;
                    &&& final(steps).steps.len() == 1
                    &&& final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(kernel))
                    &&& kernel_u_new_thread_changed(
                            final(steps).steps.last().old_u,
                            final(steps).steps.last().new_u,
                            process_ptr,
                        )
                },
                ret is Success
                    || ret is ErrorProcessKilled
                    || ret is ErrorThreadKilled
                    || ret is ErrorNoQuota,
        {
            proof {
                assert(
                    kernel.cpu_array.spec_index(cpu_id).view().view().current_process is Some
                    && kernel.cpu_array.spec_index(cpu_id).view().view().current_thread is Some
                    && kernel.thread_map.spec_index(
                        kernel.cpu_array.spec_index(cpu_id).view().view()
                            .current_thread->Some_0
                    ).view().state == (ThreadState::RUNNING { cpu_id })
                ) by {
                    reveal(cpu_array_wf);
                    reveal(process_cpu_wf);
                    reveal(thread_cpu_wf);
                };
            }
            let Tracked(cpu_lock_perm) = kernel.wlock_cpu(cpu_id, Tracked(&mut *lctx));
            let cpu = kernel.cpu_array.borrow(cpu_id, Tracked(&cpu_lock_perm));
            let process_ptr = cpu.current_process.unwrap();
            let current_thread_ptr = cpu.current_thread.unwrap();

            assert({
                &&& kernel.process_map.dom().contains(process_ptr)
                &&& kernel.process_map.view().spec_index(process_ptr).is_init()
                &&& kernel.process_map.view().spec_index(process_ptr).addr() == process_ptr
            }) by {
                reveal(process_cpu_wf);
                reveal(process_perms_wf);
            };
            let proc_container = kernel.process_map.borrow_rodata(process_ptr).borrow().owning_container;
            assert({
                &&& kernel.container_map.dom().contains(proc_container)
                &&& kernel.container_map.view().spec_index(proc_container).is_init()
                &&& kernel.container_map.view().spec_index(proc_container).addr()
                    == proc_container
            }) by {
                reveal(container_process_wf);
                reveal(container_perms_wf);
            };
            let scheduler_ptr = kernel.container_map.borrow_rodata(proc_container).borrow().scheduler;

            proof {
                let process_lock_id = kernel.process_map.lock_id_by_key(process_ptr);
                assert(process_lock_id.spec_gt(kernel.cpu_array.lock_id_by_index(cpu_id))) by {
                    reveal(container_cpu_wf);
                    reveal(process_cpu_wf);
                    reveal(container_process_wf);
                };
            }
            let process_res = kernel.wlock_process_unless_killed(process_ptr, Tracked(&mut *lctx));
            if let (false, _) = process_res {
                release_cpu_and_finish_syscall(kernel,
                    Tracked(&mut *lctx),
                    Tracked(&mut *steps),
                    cpu_id,
                    Tracked(cpu_lock_perm),
                );
                return RetValueType::ErrorProcessKilled;
            }
            let Tracked(process_lock_perm) = process_res.1.unwrap();

            proof {
                assert({
                    &&& kernel.thread_map.dom().contains(current_thread_ptr)
                    &&& kernel.thread_map.spec_index(current_thread_ptr).view().owning_proc
                        == process_ptr
                    &&& kernel.thread_map.spec_index(current_thread_ptr).view().owning_container
                        == proc_container
                    &&& kernel.thread_map.spec_index(current_thread_ptr).view().container_depth
                        == kernel.process_map.spec_index(process_ptr).view_rodata().view().container_depth
                    &&& kernel.thread_map.spec_index(current_thread_ptr).view().process_depth
                        == kernel.process_map.spec_index(process_ptr).view_rodata().view().depth
                    &&& kernel.thread_map.lock_id_by_key(current_thread_ptr)
                        .spec_gt(kernel.process_map.lock_id_by_key(process_ptr))
                }) by {
                    reveal(thread_cpu_wf);
                    reveal(process_thread_wf);
                    reveal(process_perms_wf);
                    reveal(thread_perms_wf);
                };
            }
            let thread_res = kernel.wlock_thread_unless_killed(
                current_thread_ptr, Tracked(&mut *lctx),
            );
            if let (false, _) = thread_res {
                release_cpu_and_process_and_finish_syscall(kernel,
                    Tracked(&mut *lctx),
                    Tracked(&mut *steps),
                    cpu_id,
                    process_ptr,
                    Tracked(process_lock_perm),
                    Tracked(cpu_lock_perm),
                );
                return RetValueType::ErrorThreadKilled;
            }
            let Tracked(current_thread_lock_perm) = thread_res.1.unwrap();

            let thread_ref = kernel.thread_map.borrow(
                current_thread_ptr, Tracked(&current_thread_lock_perm),
            );
            if thread_ref.quota_4k < 1 {
                release_cpu_and_process_and_thread_and_finish_syscall(kernel,
                    Tracked(&mut *lctx),
                    Tracked(&mut *steps),
                    cpu_id,
                    process_ptr,
                    current_thread_ptr,
                    Tracked(current_thread_lock_perm),
                    Tracked(process_lock_perm),
                    Tracked(cpu_lock_perm),
                );
                return RetValueType::ErrorNoQuota;
            }

            proof {
                let scheduler_lock_id = kernel.scheduler_map.lock_id_by_key(scheduler_ptr);
                assert({
                    &&& kernel.scheduler_map.dom().contains(scheduler_ptr)
                    &&& scheduler_lock_id.major == SCHEDULER_LOCK_MAJOR
                    &&& process_lock_perm.ordering_lock_id().major
                        == PROCESS_LOCK_MAJOR
                    &&& current_thread_lock_perm.ordering_lock_id().major
                        == THREAD_LOCK_MAJOR
                    &&& lctx.lock_id_acyclic(scheduler_lock_id)
                }) by {
                    reveal(container_scheduler_wf);
                    reveal(scheduler_perms_wf);
                    reveal(process_perms_wf);
                    reveal(thread_cpu_wf);
                    reveal(thread_perms_wf);
                };
            }
            let Tracked(scheduler_lock_perm) = kernel.wlock_scheduler(
                scheduler_ptr, Tracked(&mut *lctx),
            );

            // ===== QUOTA SUFFICIENT =====
            proof {
                assert({
                    &&& kernel.thread_map.spec_index(current_thread_ptr).view().owning_proc
                        == process_ptr
                    &&& lctx.lock_entry_contains(
                        kernel.scheduler_map.lock_id_by_key(scheduler_ptr),
                        KernelObjId::Scheduler(scheduler_ptr),
                    )
                }) by {
                    reveal(thread_cpu_wf);
                };
            }
            add_new_thread_to_proc_container_and_scheduler(
                kernel,
                Tracked(&mut *lctx),
                Tracked(&mut *steps),
                cpu_id,
                process_ptr,
                current_thread_ptr,
                proc_container,
                scheduler_ptr,
                Tracked(process_lock_perm),
                Tracked(current_thread_lock_perm),
                Tracked(cpu_lock_perm),
                Tracked(scheduler_lock_perm),
            );
            return RetValueType::Success;
        }

}
