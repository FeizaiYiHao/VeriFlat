use vstd::prelude::*;
use crate::*;
use super::super::syscall_new_thread::syscall_new_thread_helpers::kernel_u_new_thread_changed;
use super::syscall_new_thread_with_endpoint_helpers::add_new_thread_with_endpoint;

verus! {

    /// Create a thread whose endpoint descriptor 0 aliases descriptor
    /// `endpoint_index` of the thread currently running on `cpu_id`.
    pub fn syscall_new_thread_with_endpoint(
        krnl: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        endpoint_index: EndpointIdx,
    ) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            edp_idx_valid(endpoint_index),
            old(krnl).inv(),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().state == CpuState::Running,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().current_process is Some,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().current_thread is Some,
            old(krnl).prc_mp.dom().contains(old(krnl).cpu_arr.spec_index(cpu_id).view().view().current_process->Some_0),
            old(krnl).ctn_mp.dom().contains(old(krnl).prc_mp.spec_index(old(krnl).cpu_arr.spec_index(cpu_id).view().view().current_process->Some_0).view_rodata().view().owning_container),
            {
                let process_ptr = old(krnl).cpu_arr.spec_index(cpu_id).view().view().current_process->Some_0;
                let container_ptr = old(krnl).prc_mp.spec_index(process_ptr)
                    .view_rodata().view().owning_container;
                old(krnl).sched_mp.dom().contains(old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler)
            },
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).no_locks_held(),
            old(krnl).cpu_arr.spec_index(cpu_id).view().locked_by(old(lctx)) == false,
            {
                let process_ptr = old(krnl).cpu_arr.spec_index(cpu_id).view().view().current_process->Some_0;
                let container_ptr = old(krnl).prc_mp.spec_index(process_ptr)
                    .view_rodata().view().owning_container;
                let scheduler_ptr = old(krnl).ctn_mp.spec_index(container_ptr)
                    .view_rodata().view().scheduler;
                &&& old(krnl).cpu_arr.spec_index(cpu_id).view().view().current_process is Some
                &&& old(krnl).cpu_arr.spec_index(cpu_id).view().view().current_thread is Some
                &&& old(krnl).prc_mp.dom().contains(process_ptr)
                &&& old(krnl).ctn_mp.dom().contains(container_ptr)
                &&& old(krnl).sched_mp.dom().contains(scheduler_ptr)
                &&& old(krnl).prc_mp.spec_index(process_ptr).locked_by(old(lctx)) == false
                &&& old(krnl).sched_mp.spec_index(scheduler_ptr).locked_by(old(lctx)) == false
            },
            old(steps).steps.len() == 0,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            lock_id_set_aligned(old(lctx)),
            old(krnl).all_objects_unlocked(old(lctx)),
        ensures
            final(steps).steps.len() <= 1,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            final(lctx).no_locks_held(),
            final(krnl).all_objects_unlocked(final(lctx)),
            !(ret is Success) ==> final(steps).steps.len() == 0,
            ret is Success ==> { let process_ptr = old(krnl).cpu_arr.spec_index(cpu_id).view().view().current_process->Some_0; &&& final(steps).steps.len() == 1 &&& final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(krnl)) &&& kernel_u_new_thread_changed(final(steps).steps.last().old_u, final(steps).steps.last().new_u, process_ptr) },
            ret is Success || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorNoQuota || ret is Error,
    {
        proof {
            assert(
                krnl.cpu_arr.spec_index(cpu_id).view().view().current_process is Some
                && krnl.cpu_arr.spec_index(cpu_id).view().view().current_thread is Some
                && krnl.thr_mp.spec_index(krnl.cpu_arr.spec_index(cpu_id).view().view().current_thread->Some_0).view().state == (ThreadState::RUNNING { cpu_id })
            ) by { reveal(cpu_array_wf); reveal(process_cpu_wf); reveal(thread_cpu_wf); };
        }
        let Tracked(cpu_lock_perm) = krnl.wlock_cpu(cpu_id, Tracked(&mut *lctx));
        let cpu = krnl.cpu_arr.borrow(cpu_id, Tracked(&cpu_lock_perm));
        let process_ptr = cpu.current_process.unwrap();
        let current_thread_ptr = cpu.current_thread.unwrap();

        assert({
            &&& krnl.prc_mp.dom().contains(process_ptr)
            &&& krnl.prc_mp.view().spec_index(process_ptr).is_init()
            &&& krnl.prc_mp.view().spec_index(process_ptr).addr() == process_ptr
        }) by { reveal(process_cpu_wf); reveal(process_perms_wf); };
        let container_ptr = krnl.prc_mp.borrow_rodata(process_ptr)
            .borrow().owning_container;
        assert({
            &&& krnl.ctn_mp.dom().contains(container_ptr)
            &&& krnl.ctn_mp.view().spec_index(container_ptr).is_init()
            &&& krnl.ctn_mp.view().spec_index(container_ptr).addr() == container_ptr
        }) by { reveal(container_process_wf); reveal(container_perms_wf); };
        let scheduler_ptr = krnl.ctn_mp.borrow_rodata(container_ptr)
            .borrow().scheduler;

        proof {
            assert({
                &&& krnl.prc_mp.lock_id_by_key(process_ptr).major == PROCESS_LOCK_MAJOR
                &&& krnl.prc_mp.dom().contains(process_ptr)
                &&& !krnl.prc_mp.spec_index(process_ptr).locked_by(&*lctx)
                &&& krnl.prc_mp.lock_id_by_key(process_ptr).spec_gt(krnl.cpu_arr.lock_id_by_index(cpu_id))
            }) by { reveal(process_perms_wf); reveal(process_cpu_wf); reveal(container_cpu_wf); reveal(container_process_wf); };
        }
        let process_res = krnl.wlock_process_unless_killed(process_ptr, Tracked(&mut *lctx));
        if let (false, _) = process_res {
            release_cpu_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Tracked(cpu_lock_perm));
            return RetValueType::ErrorProcessKilled;
        }
        let Tracked(process_lock_perm) = process_res.1.unwrap();

        proof {
            assert({
                &&& krnl.thr_mp.dom().contains(current_thread_ptr)
                &&& krnl.thr_mp.spec_index(current_thread_ptr).view().owning_proc == process_ptr
                &&& krnl.thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr
                &&& krnl.thr_mp.spec_index(current_thread_ptr).view().container_depth == krnl.prc_mp.spec_index(process_ptr).view_rodata().view().container_depth
                &&& krnl.thr_mp.spec_index(current_thread_ptr).view().process_depth == krnl.prc_mp.spec_index(process_ptr).view_rodata().view().depth
                &&& krnl.thr_mp.lock_id_by_key(current_thread_ptr).spec_gt(krnl.prc_mp.lock_id_by_key(process_ptr))
            }) by { reveal(thread_cpu_wf); reveal(process_thread_wf); reveal(process_perms_wf); reveal(thread_perms_wf); };
        }
        let thread_res = krnl.wlock_thread_unless_killed(current_thread_ptr, Tracked(&mut *lctx));
        if let (false, _) = thread_res {
            release_cpu_and_process_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, Tracked(process_lock_perm), Tracked(cpu_lock_perm));
            return RetValueType::ErrorThreadKilled;
        }
        let Tracked(current_thread_lock_perm) = thread_res.1.unwrap();

        let thread_ref = krnl.thr_mp.borrow(current_thread_ptr, Tracked(&current_thread_lock_perm));
        let endpoint_option = *thread_ref.endpoint_descriptors.get(endpoint_index);
        if let None = endpoint_option {
            release_cpu_and_process_and_thread_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, Tracked(current_thread_lock_perm), Tracked(process_lock_perm), Tracked(cpu_lock_perm));
            return RetValueType::Error;
        }
        let endpoint_ptr = endpoint_option.unwrap();

        if thread_ref.quota_4k < 1 {
            release_cpu_and_process_and_thread_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, Tracked(current_thread_lock_perm), Tracked(process_lock_perm), Tracked(cpu_lock_perm));
            return RetValueType::ErrorNoQuota;
        }

        proof {
            assert({
                &&& krnl.ep_mp.dom().contains(endpoint_ptr)
                &&& krnl.ctn_mp.dom().contains(krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container)
                &&& krnl.ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((current_thread_ptr, endpoint_index))
            }) by { reveal(thread_endpoint_ref_counter_wf); reveal(container_endpoint_wf); };
            assert(
                krnl.ctn_mp.dom().contains(krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container)
                && {
                    ||| krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container == container_ptr
                    ||| krnl.ctn_mp.spec_index(krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container).view().subtree_set.view().contains(container_ptr)
                }
            ) by { reveal(container_endpoint_wf); reveal(container_thread_endpoint_wf); };
        }
        proof {
            assert({
                &&& current_thread_lock_perm.ordering_lock_id().major == THREAD_LOCK_MAJOR
                &&& krnl.ep_mp.lock_id_by_key(endpoint_ptr).major == ENDPOINT_LOCK_MAJOR
            }) by { reveal(thread_cpu_wf); reveal(process_perms_wf); reveal(thread_perms_wf); reveal(endpoint_perms_wf); };
        }
        let Tracked(endpoint_lock_perm) = krnl.wlock_endpoint(endpoint_ptr, Tracked(&mut *lctx));

        proof {
            let scheduler_lock_id = krnl.sched_mp.lock_id_by_key(scheduler_ptr);
            assert({
                &&& krnl.sched_mp.dom().contains(scheduler_ptr)
                &&& scheduler_lock_id.major == SCHEDULER_LOCK_MAJOR
            }) by { reveal(container_scheduler_wf); reveal(process_perms_wf); reveal(thread_perms_wf); reveal(endpoint_perms_wf); reveal(scheduler_perms_wf); };
        }
        let Tracked(scheduler_lock_perm) = krnl.wlock_scheduler(scheduler_ptr, Tracked(&mut *lctx));

        assert({
            &&& lctx.holds_no_allocator_locks(PageSize::SZ4k)
            &&& lctx.holds_no_allocator_locks(PageSize::SZ2m)
            &&& lctx.holds_no_allocator_locks(PageSize::SZ1g)
        }) by { reveal(LocalContext::no_locks_held); reveal(LocalContext::holds_no_allocator_locks); };
        add_new_thread_with_endpoint(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, container_ptr, scheduler_ptr, endpoint_ptr, endpoint_index, Tracked(process_lock_perm), Tracked(current_thread_lock_perm), Tracked(cpu_lock_perm), Tracked(scheduler_lock_perm), Tracked(endpoint_lock_perm));
        RetValueType::Success
    }

}
