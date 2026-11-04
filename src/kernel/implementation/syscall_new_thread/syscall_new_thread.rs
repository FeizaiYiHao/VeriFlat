use vstd::prelude::*;
use crate::*;
use super::syscall_new_thread_helpers::add_new_thread_to_proc_container_and_scheduler;
use super::syscall_new_thread_spec::*;
use super::syscall_new_thread_trace::*;

verus! {
        /// Create a thread in the process running on `cpu_id`. The result is `new_thread_syscall_result`
        /// of the state at entry.
        pub fn syscall_new_thread(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, initial_regs: &Registers) -> (ret: RetValueType)
            requires
                index_valid(NUM_CPUS, cpu_id),
                cpu_id == old(lctx).cpu_id(),
                old(krnl).inv(),
                old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).no_locks_held(),
                old(steps).snapshot_k() == *old(krnl),
                typed_lock_maps_aligned(old(krnl), old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                final(steps).snapshot_k() == *final(krnl),
                old(steps).view().len() <= final(steps).view().len(),
                forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
                new_thread_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, *initial_regs, None, ret is Success),
                typed_lock_maps_aligned(final(krnl), final(lctx)),
                final(lctx).no_locks_held(),
                ret == new_thread_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, None),
        {
            proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
            let cpu_lock_res = wlock_cpu_if_running(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id);
            if cpu_lock_res.is_none() {
                proof {
                    new_thread_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, *initial_regs, None);
                    new_thread_result_from_k(&*old(krnl), cpu_id, None, RetValueType::CpuIdle);
                }
                return RetValueType::CpuIdle;
            }
            let Tracked(cpu_lock_perm) = cpu_lock_res.unwrap();
            proof {
                assert({
                    &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process is Some
                    &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread is Some
                    &&& krnl.thrd_mp.spec_index(krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0).view().state == (ThreadState::RUNNING { cpu_id })
                }) by { thread_cpu_wf_cpu_at(krnl.thrd_mp, krnl.cpu_arr, cpu_id); };
            }
            let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
            let prc_ptr = cpu.current_process().unwrap();
            let current_thrd_ptr = cpu.current_thread().unwrap();

            assert({
                &&& krnl.prc_mp.dom().contains(prc_ptr)
                &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container
                &&& krnl.prc_mp.view().spec_index(prc_ptr).is_init()
                &&& krnl.prc_mp.view().spec_index(prc_ptr).addr() == prc_ptr
                &&& krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().depth == krnl.cpu_arr.spec_index(cpu_id).view().view().view().process_depth
            }) by { process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); process_perms_wf_at(krnl.prc_mp, prc_ptr); };
            let ctn_ptr = krnl.prc_mp.borrow_rodata(prc_ptr).borrow().owning_container;
            assert({
                &&& krnl.ctn_mp.dom().contains(ctn_ptr)
                &&& krnl.ctn_mp.view().spec_index(ctn_ptr).is_init()
                &&& krnl.ctn_mp.view().spec_index(ctn_ptr).addr() == ctn_ptr
                &&& krnl.ctn_mp.spec_index(ctn_ptr).view_rodata().view().depth == krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().container_depth
                &&& krnl.ctn_mp.spec_index(ctn_ptr).view_rodata().view().depth == krnl.cpu_arr.spec_index(cpu_id).view().view().view().container_depth
            }) by {
                container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, prc_ptr); container_perms_wf_at(krnl.ctn_mp, ctn_ptr); container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id);
            };
            let sched_ptr = krnl.ctn_mp.borrow_rodata(ctn_ptr).borrow().scheduler;

            let process_res = krnl.wlock_process_unless_killed(prc_ptr, Ghost(cpu_id), Tracked(&mut *lctx));
            if process_res.is_none() {
                krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
                proof { assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view()); steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(prc_ptr), None, None, None, None); }
                proof { new_thread_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, *initial_regs, None); }
                proof { new_thread_result_from_k(&*old(krnl), cpu_id, None, RetValueType::ErrorProcessKilled); }
                return RetValueType::ErrorProcessKilled;
            }
            let Tracked(process_lock_perm) = process_res.unwrap();

            assert({
                &&& krnl.thrd_mp.dom().contains(current_thrd_ptr)
                &&& krnl.thrd_mp.spec_index(current_thrd_ptr).view().owning_proc == prc_ptr
                &&& krnl.thrd_mp.spec_index(current_thrd_ptr).view().owning_container == ctn_ptr
                &&& krnl.prc_mp.spec_index(prc_ptr).view().state.view() is Running
                &&& krnl.thrd_mp.spec_index(current_thrd_ptr).view().container_depth == krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().container_depth
                &&& krnl.thrd_mp.spec_index(current_thrd_ptr).view().process_depth == krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().depth
            }) by { thread_cpu_wf_cpu_at(krnl.thrd_mp, krnl.cpu_arr, cpu_id); process_thread_wf_at(krnl.prc_mp, krnl.thrd_mp, current_thrd_ptr); process_perms_wf_at(krnl.prc_mp, prc_ptr); };
            let thread_res = krnl.wlock_current_running_thread_unless_killed(current_thrd_ptr, Tracked(&mut *lctx));
            if thread_res.is_none() {
                krnl.wunlock_process(prc_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
                krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
                proof { assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view()); steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(prc_ptr), Some(current_thrd_ptr), None, None, None); }
                proof { new_thread_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, *initial_regs, None); }
                proof { new_thread_result_from_k(&*old(krnl), cpu_id, None, RetValueType::ErrorThreadKilled); }
                return RetValueType::ErrorThreadKilled;
            }
            let Tracked(current_thread_lock_perm) = thread_res.unwrap();

            let thread_ref = krnl.thrd_mp.borrow_typed(current_thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&current_thread_lock_perm));
            if thread_ref.quota_4k == 0 {
                krnl.wunlock_thread(current_thrd_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
                krnl.wunlock_process(prc_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
                krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
                proof { assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view()); steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(prc_ptr), Some(current_thrd_ptr), None, None, None); }
                proof { new_thread_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, *initial_regs, None); }
                proof { new_thread_result_from_k(&*old(krnl), cpu_id, None, RetValueType::ErrorNoQuota); }
                return RetValueType::ErrorNoQuota;
            }

            assert(krnl.sched_mp.dom().contains(sched_ptr)) by { container_scheduler_wf_at(krnl.ctn_mp, krnl.sched_mp, ctn_ptr); };
            proof { new_thread_result_from_k(&*old(krnl), cpu_id, None, RetValueType::Success); }
            let Tracked(scheduler_lock_perm) = krnl.wlock_scheduler_shard(sched_ptr, cpu_id, Tracked(&mut *lctx));
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            add_new_thread_to_proc_container_and_scheduler(
                krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, current_thrd_ptr, ctn_ptr,
                sched_ptr, Tracked(process_lock_perm), Tracked(current_thread_lock_perm), Tracked(cpu_lock_perm),
                Tracked(scheduler_lock_perm), initial_regs,
            );
            return RetValueType::Success;
        }
}
