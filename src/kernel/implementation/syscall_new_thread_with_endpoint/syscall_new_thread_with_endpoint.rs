use vstd::prelude::*;
use crate::*;
use super::super::syscall_new_thread::syscall_new_thread_spec::*;
use super::super::syscall_new_thread::syscall_new_thread_trace::*;
use super::syscall_new_thread_with_endpoint_helpers::add_new_thread_with_endpoint;

verus! {
        /// Create a thread sharing the running thread's `endpoint_index`.
        pub fn syscall_new_thread_with_endpoint(
            krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
            cpu_id: CpuId, endpoint_index: EndpointIdx, initial_regs: &Registers,
        ) -> (ret: RetValueType)
            requires
                index_valid(NUM_CPUS, cpu_id),
                cpu_id == old(lctx).cpu_id(),
                edp_idx_valid(endpoint_index),
                old(krnl).inv(),
                old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state == CpuState::Running,
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).no_locks_held(),
                old(steps).nonlock_view().len() == 0,
                old(steps).snapshot_k() == *old(krnl),
                typed_lock_maps_aligned(old(krnl), old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
                final(steps).snapshot_k() == *final(krnl),
                old(steps).view().len() <= final(steps).view().len(),
                forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
                new_thread_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, *initial_regs, Some(endpoint_index), ret is Success),
                typed_lock_maps_aligned(final(krnl), final(lctx)),
                final(lctx).no_locks_held(),
                !(ret is Success) ==> final(steps).nonlock_view().len() == 0,
                ret is Success ==> final(steps).nonlock_view().len() == 2,
                ret is Success || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorNoQuota || ret is Error,
        {
            proof { use_type_invariant(&*steps); kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
            proof {
                assert({
                    &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process is Some
                    &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread is Some
                    &&& krnl.thr_mp.spec_index(krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0).view().state == (ThreadState::RUNNING { cpu_id })
                }) by { reveal(cpu_array_wf); reveal(process_cpu_wf); reveal(thread_cpu_wf); };
            }
            let Tracked(cpu_lock_perm) = krnl.wlock_cpu(cpu_id, Tracked(&mut *lctx));
            let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
            let process_ptr = cpu.current_process().unwrap();
            let current_thread_ptr = cpu.current_thread().unwrap();

            assert({
                &&& krnl.prc_mp.dom().contains(process_ptr)
                &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == krnl.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container
                &&& krnl.prc_mp.view().spec_index(process_ptr).is_init()
                &&& krnl.prc_mp.view().spec_index(process_ptr).addr() == process_ptr
            }) by { reveal(process_cpu_wf); reveal(process_perms_wf); };
            let container_ptr = krnl.prc_mp.borrow_rodata(process_ptr).borrow().owning_container;
            assert({
                &&& krnl.ctn_mp.dom().contains(container_ptr)
                &&& krnl.ctn_mp.view().spec_index(container_ptr).is_init()
                &&& krnl.ctn_mp.view().spec_index(container_ptr).addr() == container_ptr
            }) by { reveal(container_process_wf); reveal(container_perms_wf); };
            let scheduler_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().scheduler;

            let process_res = krnl.wlock_process_unless_killed(process_ptr, Ghost(cpu_id), Tracked(&mut *lctx));
            if process_res.is_none() {
                proof {
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            }
                release_cpu_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Tracked(cpu_lock_perm));
                proof {
                    assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(old(krnl), &*krnl); };
                }
                proof {
                    new_thread_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, *initial_regs, Some(endpoint_index));
                }
                return RetValueType::ErrorProcessKilled;
            }
            let Tracked(process_lock_perm) = process_res.unwrap();

            assert({
                &&& krnl.thr_mp.dom().contains(current_thread_ptr)
                &&& krnl.thr_mp.spec_index(current_thread_ptr).view().owning_proc == process_ptr
                &&& krnl.thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr
                &&& krnl.prc_mp.spec_index(process_ptr).view().owned_threads.view().len() != 0
            }) by { reveal(thread_cpu_wf); reveal(process_thread_wf); };
            let thread_res = krnl.wlock_thread_unless_killed(current_thread_ptr, Tracked(&mut *lctx));
            if thread_res.is_none() {
                proof {
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            }
                release_cpu_and_process_and_finish_syscall(
                    krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, Tracked(process_lock_perm), Tracked(cpu_lock_perm),
                );
                proof {
                    assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by {
                        broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, kernel_container_nonlock_fields_and_quotas_unchanged_transitive, kernel_endpoint_nonlock_fields_unchanged_transitive;
                        kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(old(krnl), &*krnl);
                    };
                }
                proof {
                    new_thread_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, *initial_regs, Some(endpoint_index));
                }
                return RetValueType::ErrorThreadKilled;
            }
            let Tracked(current_thread_lock_perm) = thread_res.unwrap();

            let thread_ref = krnl.thr_mp.borrow_typed(current_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&current_thread_lock_perm));
            if thread_ref.quota_4k == 0 {
                proof {
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            }
                release_cpu_and_process_and_thread_and_finish_syscall(
                    krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr,
                    Tracked(current_thread_lock_perm), Tracked(process_lock_perm), Tracked(cpu_lock_perm),
                );
                proof {
                    assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by {
                        broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, kernel_container_nonlock_fields_and_quotas_unchanged_transitive, kernel_endpoint_nonlock_fields_unchanged_transitive;
                        kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(old(krnl), &*krnl);
                    };
                }
                proof {
                    new_thread_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, *initial_regs, Some(endpoint_index));
                }
                return RetValueType::ErrorNoQuota;
            }

            let endpoint_ptr = match *thread_ref.endpoint_descriptors.get(endpoint_index) {
                Some(endpoint_ptr) => endpoint_ptr,
                None => {
                    proof {
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            }
                    release_cpu_and_process_and_thread_and_finish_syscall(
                        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr,
                        Tracked(current_thread_lock_perm), Tracked(process_lock_perm), Tracked(cpu_lock_perm),
                    );
                    proof {
                        assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by {
                            broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, kernel_container_nonlock_fields_and_quotas_unchanged_transitive, kernel_endpoint_nonlock_fields_unchanged_transitive;
                            kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(old(krnl), &*krnl);
                        };
                    }
                    proof {
                        new_thread_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, *initial_regs, Some(endpoint_index));
                    }
                    return RetValueType::Error;
                },
            };

            proof { assert(krnl.ep_mp.dom().contains(endpoint_ptr)) by { reveal(thread_endpoint_ref_counter_wf); }; }
            let Tracked(endpoint_lock_perm) = krnl.wlock_endpoint(endpoint_ptr, Tracked(&mut *lctx));

            assert(krnl.sched_mp.dom().contains(scheduler_ptr)) by { reveal(container_scheduler_wf); };
            let Tracked(scheduler_lock_perm) = krnl.wlock_scheduler(scheduler_ptr, Tracked(&mut *lctx));

            proof {
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            }
            proof { assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; }; }
            add_new_thread_with_endpoint(
                krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, container_ptr,
                scheduler_ptr, endpoint_ptr, endpoint_index, Tracked(process_lock_perm), Tracked(current_thread_lock_perm),
                Tracked(cpu_lock_perm), Tracked(scheduler_lock_perm), Tracked(endpoint_lock_perm), initial_regs,
            );
            RetValueType::Success
        }
}
