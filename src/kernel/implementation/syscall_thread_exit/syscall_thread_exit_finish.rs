use vstd::prelude::*;
use crate::*;
use super::syscall_thread_exit_spec::*;
use super::syscall_thread_exit_finish_helpers::{thread_exit_finish_lock_page_and_cache, thread_exit_finish_destroy_and_record};

verus! {
/// Finish the exit of the running thread whose descriptors are all released: for its process's last thread `last`, take
/// the container's PCID allocator; then take the thread's page, the 4K allocator cache on `cpu_id` of the page's owner
/// (draining it first when full), that allocator's quota, and the default-pcid needflush cell of `cpu_id`, then remove
/// the thread, release every lock, and record the finish step.
pub(super) fn thread_exit_finish(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, container_ptr: RwLockContainerPtr,
    process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, last: bool, Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(container_lock_perm): Tracked<LockPerm>,
    Tracked(process_lock_perm): Tracked<LockPerm>, Tracked(thread_lock_perm): Tracked<LockPerm>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        thread_exit_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom() =~= set![container_ptr],
        old(lctx).process_lock_map().dom() =~= set![process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).prc_mp.dom().contains(process_ptr),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        container_lock_perm.state() is WriteLock,
        container_lock_perm.thread_id() == old(lctx).thread_id(),
        container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        process_lock_perm.state() is WriteLock,
        process_lock_perm.thread_id() == old(lctx).thread_id(),
        process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
        !old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        !old(krnl).prc_mp.spec_index(process_ptr).being_killed(),
        !old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().caller is None,
        old(krnl).thr_mp.spec_index(thread_ptr).view().callee is None,
        forall|j: int| #![trigger old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[j]]
            0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==> old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[j] is None,
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        last == (old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().len() == 1),
        if last {
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitZombie)
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k == 0
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().quota_2m == 0
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().quota_1g == 0
            &&& old(krnl).prc_mp.spec_index(process_ptr).view().quota_4k == 0
            &&& old(krnl).prc_mp.spec_index(process_ptr).view().quota_2m == 0
            &&& old(krnl).prc_mp.spec_index(process_ptr).view().quota_1g == 0
            &&& old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is TablesEmptied
        } else {
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() matches Some(SyscallProgress::ThreadExit { .. })
            &&& old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Running
        },
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        thread_exit_syscall_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, kernel_k_to_kernel_u(*final(krnl)), cpu_id, true),
{
    let ghost mut finish_lctx = *lctx;
    let (owner, allocator_ptr, pcid_allocator_ptr, Tracked(page_lock_perm), Tracked(cache_lock_perm), Tracked(pcid_allocator_lock_perm), full) =
        thread_exit_finish_lock_page_and_cache(krnl, Tracked(&mut *lctx), cpu_id, container_ptr, process_ptr, thread_ptr, last);
    if full {
        let Tracked(pool_lock_perm) = krnl.wlock_allocator_global_pool_4k(allocator_ptr, Tracked(&mut *lctx));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl);
        }
        drain_4k_cache_batch(krnl, allocator_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&cache_lock_perm), Tracked(&pool_lock_perm));
        krnl.wunlock_allocator_global_pool_4k(allocator_ptr, Tracked(&mut *lctx), Tracked(pool_lock_perm));
        proof {
            kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl);
            krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
            finish_lctx = *lctx;
        }
    }
    proof {
        assert(krnl.ctn_mp.dom().contains(owner) && krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr) by {
            container_page_owner_backward_at(krnl.ctn_mp, krnl.pg_arr, page_ptr2page_index(thread_ptr));
        };
    }
    thread_exit_finish_destroy_and_record(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), Ghost(finish_lctx), cpu_id, container_ptr, process_ptr, thread_ptr, owner, allocator_ptr,
        pcid_allocator_ptr, Tracked(cpu_lock_perm), Tracked(container_lock_perm), Tracked(process_lock_perm), Tracked(thread_lock_perm), Tracked(page_lock_perm),
        Tracked(cache_lock_perm), Tracked(pcid_allocator_lock_perm), Ghost(start), Ghost(pre));
}
} // verus!
