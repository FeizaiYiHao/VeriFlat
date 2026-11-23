use vstd::prelude::*;
use crate::*;
use super::syscall_thread_exit_spec::*;
use super::syscall_thread_exit_trace::*;
use super::syscall_thread_exit_finish_helpers::{thread_exit_finish_lock_page_and_cache, thread_exit_finish_destroy_and_record};

verus! {
/// Finish the exit of the running thread whose descriptors are all released: for its process's last thread `last`, take
/// the container's PCID allocator; then take the thread's page, the 4K allocator cache on `cpu_id` of the page's owner
/// (draining it first when full), that allocator's quota, and the default-pcid needflush cell of `cpu_id`, then remove
/// the thread, release every lock, and record the finish step.
pub(super) fn thread_exit_finish(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr,
    prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, last: bool, Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(container_lock_perm): Tracked<LockPerm>,
    Tracked(process_lock_perm): Tracked<LockPerm>, Tracked(thread_lock_perm): Tracked<LockPerm>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(bound): Ghost<nat>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        thread_exit_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id),
        thread_exit_reclaim_count(old(steps).view().subrange(start, old(steps).view().len() as int), cpu_id) <= process_tables_step_bound(),
        old(steps).view().len() - start + 3 <= bound,
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom() =~= set![ctn_ptr],
        old(lctx).process_lock_map().dom() =~= set![prc_ptr],
        old(lctx).thread_lock_map().dom() =~= set![thrd_ptr],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(krnl).ctn_mp.dom().contains(ctn_ptr),
        old(krnl).prc_mp.dom().contains(prc_ptr),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), ctn_ptr, TypedLockMode::Write),
        container_lock_perm.state() is WriteLock,
        container_lock_perm.thread_id() == old(lctx).thread_id(),
        container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(ctn_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), prc_ptr, TypedLockMode::Write),
        process_lock_perm.state() is WriteLock,
        process_lock_perm.thread_id() == old(lctx).thread_id(),
        process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(prc_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == ctn_ptr,
        !old(krnl).ctn_mp.spec_index(ctn_ptr).being_killed(),
        !old(krnl).prc_mp.spec_index(prc_ptr).being_killed(),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().caller is None,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().callee is None,
        forall|j: int| #![trigger old(krnl).thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors.view()[j]]
            0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==> old(krnl).thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors.view()[j] is None,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        last == (old(krnl).prc_mp.spec_index(prc_ptr).view().owned_threads.view().len() == 1),
        if last {
            &&& old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitZombie)
            &&& old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_4k == 0
            &&& old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_2m == 0
            &&& old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_1g == 0
            &&& old(krnl).prc_mp.spec_index(prc_ptr).view().quota_4k == 0
            &&& old(krnl).prc_mp.spec_index(prc_ptr).view().quota_2m == 0
            &&& old(krnl).prc_mp.spec_index(prc_ptr).view().quota_1g == 0
            &&& old(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is TablesEmptied
        } else {
            &&& old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() matches Some(SyscallProgress::ThreadExit { .. })
            &&& old(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is Running
        },
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        thread_exit_syscall_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, kernel_k_to_kernel_u(*final(krnl)), cpu_id, true, bound),
{
    let ghost mut finish_lctx = *lctx;
    let (owner, allc_ptr, pcid_allc_ptr, Tracked(page_lock_perm), Tracked(cache_lock_perm), Tracked(pcid_allocator_lock_perm), full) =
        thread_exit_finish_lock_page_and_cache(krnl, Tracked(&mut *lctx), cpu_id, ctn_ptr, prc_ptr, thrd_ptr, last);
    if full {
        let ghost locked_k = *krnl;
        let Tracked(pool_lock_perm) = krnl.wlock_allocator_global_pool_4k(allc_ptr, Tracked(&mut *lctx));
        let ghost snap = steps.snapshot_k();
        let ghost drain_before = steps.view();
        let ghost drain_k = *krnl;
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&snap, &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            if last {
                let mid = KernelK { pcid_allc_mp: snap.pcid_allc_mp, ..*krnl };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(&locked_k, &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(&KernelK { pcid_allc_mp: snap.pcid_allc_mp, ..locked_k }, &mid)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(&snap, &mid)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&snap, &mid)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
                kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&snap, &mid);
                krnl.pcid_allc_mp.typed_lock_map_aligned_write_at(lctx.pcid_allocator_lock_map(), lctx.thread_id(), pcid_allc_ptr);
                kernel_pcid_allocator_lock_mode_changed_implies_u_step(&mid, &*krnl, ctn_ptr);
                thread_exit_lock_pcid_allocator_step_pre_from_k(&snap, &finish_lctx, cpu_id, ctn_ptr, prc_ptr, thrd_ptr);
                thread_exit_lock_pcid_allocator_step_from_u(kernel_k_to_kernel_u(snap), kernel_k_to_kernel_u(*krnl), cpu_id, ctn_ptr);
            } else {
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(&snap, &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&snap, &*krnl);
            }
        }
        drain_4k_cache_batch(krnl, allc_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&cache_lock_perm), Tracked(&pool_lock_perm));
        proof { if last { thread_exit_trace_push(&*steps, drain_before, start, pre, kernel_k_to_kernel_u(snap), kernel_k_to_kernel_u(drain_k), cpu_id); } }
        krnl.wunlock_allocator_global_pool_4k(allc_ptr, Tracked(&mut *lctx), Tracked(pool_lock_perm));
        proof {
            kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl);
            krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
            finish_lctx = *lctx;
            if last { krnl.pcid_allc_mp.typed_lock_map_aligned_write_at(lctx.pcid_allocator_lock_map(), lctx.thread_id(), pcid_allc_ptr); }
        }
    }
    thread_exit_finish_destroy_and_record(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), Ghost(finish_lctx), cpu_id, ctn_ptr, prc_ptr, thrd_ptr, owner, allc_ptr,
        pcid_allc_ptr, Tracked(cpu_lock_perm), Tracked(container_lock_perm), Tracked(process_lock_perm), Tracked(thread_lock_perm), Tracked(page_lock_perm),
        Tracked(cache_lock_perm), Tracked(pcid_allocator_lock_perm), Ghost(start), Ghost(pre), Ghost(bound));
}
} // verus!
