use vstd::prelude::*;
use crate::*;
use super::staged_4k_page_chain::allocate_staged_4k_page_chain;
#[cfg(verus_keep_ghost)]
use super::staged_4k_page_chain::page_ptr_sets_disjoint_from_index_disjoint;
use super::*;
use super::syscall_new_container_spec::*;
use super::syscall_new_container_trace::*;
use super::syscall_new_container_share::end_new_container_created_step;
use super::syscall_new_container_commit_share::commit_new_container_share_and_finish;
use super::syscall_new_container_enter::enter_new_container_commit;

verus! {
pub(super) fn commit_new_container(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, caller_cpu_id: CpuId,
    parent_container_ptr: RwLockContainerPtr, parent_process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr,
    source_pagetable_ptr: RwLockPageTableRoot, source_range: &VaRange4K, funding_page_count: usize, process_quota_4k: usize, transfer_cpu_id: CpuId,
    parent_cpu_set: RwLockCpuSetPtr, endpoint: Option<RwLockEndpointPtr>, endpoint_index: EndpointIdx, caller_cpu_lock_perm: Tracked<LockPerm>,
    parent_container_lock_perm: Tracked<LockPerm>, parent_process_lock_perm: Tracked<LockPerm>, current_thread_lock_perm: Tracked<LockPerm>,
    source_pagetable_lock_perm: Tracked<LockPerm>, parent_cpu_set_lock_perm: Tracked<LockPerm>, endpoint_lock_perm: Tracked<Option<LockPerm>>,
    source_window_perms: Tracked<Map<WindowVa, LockPerm>>, initial_regs: &Registers,
) -> (ret: (RwLockContainerPtr, RwLockProcessPtr, RwLockThreadPtr))
    requires
        index_valid(NUM_CPUS, caller_cpu_id),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, ctn_mp: old(krnl).ctn_mp, prc_mp: old(krnl).prc_mp,
            thr_mp: old(krnl).thr_mp, ep_mp: old(krnl).ep_mp, pt_mp: old(krnl).pt_mp, pt_lower: old(krnl).pt_lower, cpu_set_mp: old(krnl).cpu_set_mp, ..old(steps).snapshot_k() }),
        match endpoint { Some(e) => old(krnl).ep_mp.unchanged_except(&old(steps).snapshot_k().ep_mp, e), None => old(krnl).ep_mp == old(steps).snapshot_k().ep_mp },
        endpoint is Some ==> old(steps).snapshot_k().ep_mp.spec_index(endpoint->Some_0).locking_thread() is None,
        old(krnl).cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, caller_cpu_id),
        old(krnl).ctn_mp.unchanged_except(&old(steps).snapshot_k().ctn_mp, parent_container_ptr),
        old(krnl).prc_mp.unchanged_except(&old(steps).snapshot_k().prc_mp, parent_process_ptr),
        old(krnl).thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, current_thread_ptr),
        old(krnl).pt_mp.unchanged_except(&old(steps).snapshot_k().pt_mp, source_pagetable_ptr),
        old(steps).snapshot_k().cpu_arr.spec_index(caller_cpu_id).value.locking_thread() is None,
        old(steps).snapshot_k().ctn_mp.spec_index(parent_container_ptr).locking_thread() is None,
        old(steps).snapshot_k().prc_mp.spec_index(parent_process_ptr).locking_thread() is None,
        old(steps).snapshot_k().thr_mp.spec_index(current_thread_ptr).locking_thread() is None,
        !(old(steps).snapshot_k().pt_mp.spec_index(source_pagetable_ptr).locking_thread() is Write),
        old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().state == CpuState::Running,
        old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), &KernelK { cpu_set_mp: old(steps).snapshot_k().cpu_set_mp, ..*old(krnl) }),
        old(krnl).cpu_set_mp.unchanged_except(&old(steps).snapshot_k().cpu_set_mp, parent_cpu_set),
        old(steps).snapshot_k().cpu_set_mp.spec_index(parent_cpu_set).locking_thread() is None,
        !old(steps).snapshot_k().cpu_set_mp.spec_index(parent_cpu_set).being_killed() && !old(krnl).cpu_set_mp.spec_index(parent_cpu_set).being_killed(),
        caller_cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_published[caller_cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_pcid),
        process_quota_4k <= funding_page_count,
        funding_page_count <= usize::MAX - 9 - 3 * source_range.len,
        source_range.wf(),
        source_range.len > 0,
        source_range.len <= (usize::MAX - 9) / 3,
        index_valid(NUM_CPUS, transfer_cpu_id),
        old(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().state is Off,
        old(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().owning_container == parent_container_ptr,
        transfer_cpu_id != caller_cpu_id,
        old(krnl).cpu_set_mp.dom().contains(parent_cpu_set),
        old(krnl).cpu_set_mp.spec_index(parent_cpu_set).view().owned_cpus.closed_view().contains(transfer_cpu_id),
        old(krnl).ctn_mp.spec_index(parent_container_ptr).view_rodata().view().cpu_set == parent_cpu_set,
        typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), parent_cpu_set, TypedLockMode::Write),
        parent_cpu_set_lock_perm.view().state() is WriteLock,
        parent_cpu_set_lock_perm.view().thread_id() == old(lctx).thread_id(),
        parent_cpu_set_lock_perm.view().lock_id() == old(krnl).cpu_set_mp.spec_index(parent_cpu_set).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(source_range.start),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable_ptr).wf(),
        forall|j: int| #![trigger source_range.view().spec_index(j)] 0 <= j < source_range.len ==> {
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable_ptr).mapping_4k().dom().contains(source_range.view().spec_index(j))
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable_ptr).mapping_4k().spec_index(source_range.view().spec_index(j)).present
        },
        forall|w: WindowVa| #![trigger va_range_2m_windows(*source_range).contains(w)]
            va_range_2m_windows(*source_range).contains(w) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable_ptr).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> source_window_perms.view().dom().contains(w),
        forall|w: WindowVa| #![trigger source_window_perms.view().dom().contains(w)] source_window_perms.view().dom().contains(w) ==> {
            &&& va_range_2m_windows(*source_range).contains(w)
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable_ptr).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
            &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (source_pagetable_ptr, w), TypedLockMode::Write)
            &&& source_window_perms.view().index(w).state() is WriteLock
            &&& source_window_perms.view().index(w).thread_id() == old(lctx).thread_id()
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable_ptr).lower.l2_lock_of(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable_ptr).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                .lock_perm_match(spec_v2l2index(w.va), &source_window_perms.view().index(w))
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable_ptr).window_leaves_present(w)
            &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable_ptr).lower.window_stale_cpus.dom().contains((pagetable_c(old(krnl).pt_mp,
                old(krnl).pt_lower.view(), source_pagetable_ptr).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
        },
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == source_pagetable_ptr && source_window_perms.view().dom().contains(w)),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![caller_cpu_id],
        old(lctx).container_lock_map().dom() =~= set![parent_container_ptr],
        old(lctx).process_lock_map().dom() =~= set![parent_process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        endpoint is None ==> old(lctx).endpoint_lock_map().dom().is_empty(),
        endpoint is Some ==> {
            let endpoint_ptr = endpoint->Some_0;
            &&& edp_idx_valid(endpoint_index)
            &&& old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr]
            &&& old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.wf()
            &&& old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == endpoint
            &&& old(krnl).ep_mp.dom().contains(endpoint_ptr)
            &&& old(krnl).ep_mp.spec_index(endpoint_ptr).is_init()
            &&& typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write)
            &&& !old(krnl).ep_mp.spec_index(endpoint_ptr).being_killed()
            &&& old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((current_thread_ptr, endpoint_index))
            &&& endpoint_lock_perm.view() is Some
            &&& endpoint_lock_perm.view()->Some_0.state() is WriteLock
            &&& endpoint_lock_perm.view()->Some_0.thread_id() == old(lctx).thread_id()
            &&& endpoint_lock_perm.view()->Some_0.lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id
        },
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom() =~= set![parent_cpu_set],
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr],
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), caller_cpu_id, TypedLockMode::Write),
        !old(krnl).cpu_arr.spec_index(caller_cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().owning_container == parent_container_ptr,
        caller_cpu_lock_perm.view().state() is WriteLock,
        caller_cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        caller_cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(caller_cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(parent_container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), parent_container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).view().zombie,
        old(krnl).ctn_mp.spec_index(parent_container_ptr).view_rodata().view().depth < MAX_CONTAINER_TREE_DEPTH,
        parent_container_lock_perm.view().state() is WriteLock,
        parent_container_lock_perm.view().thread_id() == old(lctx).thread_id(),
        parent_container_lock_perm.view().lock_id() == old(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(parent_process_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), parent_process_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(parent_process_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(parent_process_ptr).view().state.view() is Running || old(krnl).prc_mp.spec_index(parent_process_ptr).view().state.view() is Zombie,
        old(krnl).prc_mp.spec_index(parent_process_ptr).view_rodata().view().owning_container == parent_container_ptr,
        parent_process_lock_perm.view().state() is WriteLock,
        parent_process_lock_perm.view().thread_id() == old(lctx).thread_id(),
        parent_process_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(parent_process_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == parent_container_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_process_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == source_pagetable_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id: caller_cpu_id }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
        !old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 9 + funding_page_count + 3 * source_range.len,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_2m >= 2,
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Read),
        source_pagetable_lock_perm.view().state() is ReadLock,
        source_pagetable_lock_perm.view().thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread() is Read,
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), source_pagetable_lock_perm.view().lock_id()),
    ensures
        old(steps).view().len() as int + source_range.len as int + 3 <= final(steps).view().len() as int <= old(steps).view().len() as int + 4 * source_range.len as int + 3,
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        new_container_commit_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
            kernel_k_to_kernel_u(old(steps).snapshot_k()), caller_cpu_id, *source_range, funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs, if endpoint is Some { Some(endpoint_index) } else { None }),
        final(steps).view().last().new_u == kernel_k_to_kernel_u(*final(krnl)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        old(steps).nonlock_view().len() as int + source_range.len as int + 3 <= final(steps).nonlock_view().len() as int,
        final(steps).nonlock_view().len() as int <= old(steps).nonlock_view().len() as int + 4 * source_range.len as int + 3,
{
    let tracked caller_cpu_lock_perm = caller_cpu_lock_perm.get();
    let tracked parent_container_lock_perm = parent_container_lock_perm.get();
    let tracked parent_process_lock_perm = parent_process_lock_perm.get();
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked source_pagetable_lock_perm = source_pagetable_lock_perm.get();
    let tracked endpoint_lock_perm = endpoint_lock_perm.get();
    let tracked source_window_perms = source_window_perms.get();
    let ghost record = NewContainerProgress {
        range: *source_range, funding: funding_page_count, process_quota: process_quota_4k, transfer_cpu: transfer_cpu_id, regs: *initial_regs,
        endpoint_index: if endpoint is Some { Some(endpoint_index) } else { None }, child_container: None,
    };
    let (
        child_container_ptr, child_process_ptr, child_pagetable_ptr, child_scheduler_ptr, thread_page_ptr, child_allocator_4k_ptr, Tracked(child_container_lock_perm),
        Tracked(child_process_lock_perm), Tracked(child_pagetable_lock_perm), Tracked(thread_page_lock_perm),
    ) = commit_new_container_publish(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), caller_cpu_id, parent_container_ptr, parent_process_ptr, current_thread_ptr, source_pagetable_ptr,
        source_range, funding_page_count, process_quota_4k, transfer_cpu_id, parent_cpu_set, endpoint, endpoint_index, Tracked(&caller_cpu_lock_perm),
        Tracked(&parent_container_lock_perm), Tracked(&parent_process_lock_perm), Tracked(&current_thread_lock_perm), Tracked(&source_pagetable_lock_perm),
        parent_cpu_set_lock_perm, Tracked(&endpoint_lock_perm), Ghost(*initial_regs),
    );
    let new_thread_ptr = commit_new_container_share_and_finish(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), caller_cpu_id, source_range, parent_container_ptr, child_container_ptr, parent_process_ptr,
        child_process_ptr, current_thread_ptr, source_pagetable_ptr, child_pagetable_ptr, child_allocator_4k_ptr, child_scheduler_ptr, thread_page_ptr,
        endpoint, endpoint_index, Tracked(caller_cpu_lock_perm), Tracked(parent_container_lock_perm), Tracked(child_container_lock_perm),
        Tracked(parent_process_lock_perm), Tracked(child_process_lock_perm), Tracked(current_thread_lock_perm), Tracked(source_pagetable_lock_perm),
        Tracked(child_pagetable_lock_perm), Tracked(thread_page_lock_perm), Tracked(endpoint_lock_perm), initial_regs, Ghost(old(steps).view().len() as int),
        Ghost(kernel_k_to_kernel_u(old(steps).snapshot_k())), Ghost(record), Tracked(source_window_perms), Ghost(*old(krnl)), Ghost(*old(lctx)),
    );
    (child_container_ptr, child_process_ptr, new_thread_ptr)
}

/// Enters the call, allocates and stages the child's pages, and publishes the child container: the enter and publish steps.
#[verifier::spinoff_prover]
fn commit_new_container_publish(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, caller_cpu_id: CpuId,
    parent_container_ptr: RwLockContainerPtr, parent_process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, source_pagetable_ptr: RwLockPageTableRoot,
    source_range: &VaRange4K, funding_page_count: usize, process_quota_4k: usize, transfer_cpu_id: CpuId, parent_cpu_set: RwLockCpuSetPtr,
    endpoint: Option<RwLockEndpointPtr>, endpoint_index: EndpointIdx, Tracked(caller_cpu_lock_perm): Tracked<&LockPerm>,
    Tracked(parent_container_lock_perm): Tracked<&LockPerm>, Tracked(parent_process_lock_perm): Tracked<&LockPerm>,
    Tracked(current_thread_lock_perm): Tracked<&LockPerm>, Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>, parent_cpu_set_lock_perm: Tracked<LockPerm>,
    Tracked(endpoint_lock_perm): Tracked<&Option<LockPerm>>, Ghost(regs): Ghost<Registers>,
) -> (ret: (RwLockContainerPtr, RwLockProcessPtr, RwLockPageTableRoot, RwLockSchedulerPtr, PagePtr, RwLockPageAllocatorPtr, Tracked<LockPerm>, Tracked<LockPerm>,
    Tracked<LockPerm>, Tracked<LockPerm>))
    requires
        index_valid(NUM_CPUS, caller_cpu_id),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, ctn_mp: old(krnl).ctn_mp, prc_mp: old(krnl).prc_mp,
            thr_mp: old(krnl).thr_mp, ep_mp: old(krnl).ep_mp, pt_mp: old(krnl).pt_mp, pt_lower: old(krnl).pt_lower, cpu_set_mp: old(krnl).cpu_set_mp, ..old(steps).snapshot_k() }),
        match endpoint { Some(e) => old(krnl).ep_mp.unchanged_except(&old(steps).snapshot_k().ep_mp, e), None => old(krnl).ep_mp == old(steps).snapshot_k().ep_mp },
        endpoint is Some ==> old(steps).snapshot_k().ep_mp.spec_index(endpoint->Some_0).locking_thread() is None,
        old(krnl).cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, caller_cpu_id),
        old(krnl).ctn_mp.unchanged_except(&old(steps).snapshot_k().ctn_mp, parent_container_ptr),
        old(krnl).prc_mp.unchanged_except(&old(steps).snapshot_k().prc_mp, parent_process_ptr),
        old(krnl).thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, current_thread_ptr),
        old(krnl).pt_mp.unchanged_except(&old(steps).snapshot_k().pt_mp, source_pagetable_ptr),
        old(steps).snapshot_k().cpu_arr.spec_index(caller_cpu_id).value.locking_thread() is None,
        old(steps).snapshot_k().ctn_mp.spec_index(parent_container_ptr).locking_thread() is None,
        old(steps).snapshot_k().prc_mp.spec_index(parent_process_ptr).locking_thread() is None,
        old(steps).snapshot_k().thr_mp.spec_index(current_thread_ptr).locking_thread() is None,
        !(old(steps).snapshot_k().pt_mp.spec_index(source_pagetable_ptr).locking_thread() is Write),
        old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().state == CpuState::Running,
        old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), &KernelK { cpu_set_mp: old(steps).snapshot_k().cpu_set_mp, ..*old(krnl) }),
        old(krnl).cpu_set_mp.unchanged_except(&old(steps).snapshot_k().cpu_set_mp, parent_cpu_set),
        old(steps).snapshot_k().cpu_set_mp.spec_index(parent_cpu_set).locking_thread() is None,
        !old(steps).snapshot_k().cpu_set_mp.spec_index(parent_cpu_set).being_killed() && !old(krnl).cpu_set_mp.spec_index(parent_cpu_set).being_killed(),
        caller_cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_published[caller_cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_pcid),
        process_quota_4k <= funding_page_count,
        funding_page_count <= usize::MAX - 9 - 3 * source_range.len,
        source_range.wf(),
        source_range.len > 0,
        source_range.len <= (usize::MAX - 9) / 3,
        index_valid(NUM_CPUS, transfer_cpu_id),
        old(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().state is Off,
        old(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().owning_container == parent_container_ptr,
        transfer_cpu_id != caller_cpu_id,
        old(krnl).cpu_set_mp.dom().contains(parent_cpu_set),
        old(krnl).cpu_set_mp.spec_index(parent_cpu_set).view().owned_cpus.closed_view().contains(transfer_cpu_id),
        old(krnl).ctn_mp.spec_index(parent_container_ptr).view_rodata().view().cpu_set == parent_cpu_set,
        typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), parent_cpu_set, TypedLockMode::Write),
        parent_cpu_set_lock_perm.view().state() is WriteLock,
        parent_cpu_set_lock_perm.view().thread_id() == old(lctx).thread_id(),
        parent_cpu_set_lock_perm.view().lock_id() == old(krnl).cpu_set_mp.spec_index(parent_cpu_set).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(source_range.start),
        forall|j: int| #![trigger source_range.view().spec_index(j)] 0 <= j < source_range.len ==> {
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable_ptr).mapping_4k().dom().contains(source_range.view().spec_index(j))
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable_ptr).mapping_4k().spec_index(source_range.view().spec_index(j)).present
        },
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![caller_cpu_id],
        old(lctx).container_lock_map().dom() =~= set![parent_container_ptr],
        old(lctx).process_lock_map().dom() =~= set![parent_process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        endpoint is None ==> old(lctx).endpoint_lock_map().dom().is_empty(),
        endpoint is Some ==> {
            let endpoint_ptr = endpoint->Some_0;
            &&& edp_idx_valid(endpoint_index)
            &&& old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr]
            &&& old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.wf()
            &&& old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == endpoint
            &&& old(krnl).ep_mp.dom().contains(endpoint_ptr)
            &&& old(krnl).ep_mp.spec_index(endpoint_ptr).is_init()
            &&& typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write)
            &&& !old(krnl).ep_mp.spec_index(endpoint_ptr).being_killed()
            &&& old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((current_thread_ptr, endpoint_index))
            &&& endpoint_lock_perm is Some
            &&& endpoint_lock_perm->Some_0.state() is WriteLock
            &&& endpoint_lock_perm->Some_0.thread_id() == old(lctx).thread_id()
            &&& endpoint_lock_perm->Some_0.lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id
        },
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom() =~= set![parent_cpu_set],
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr],
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))] old(lctx).pagetable_window_lock_map().dom().contains((p, w)) ==> p == source_pagetable_ptr,
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), caller_cpu_id, TypedLockMode::Write),
        !old(krnl).cpu_arr.spec_index(caller_cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().owning_container == parent_container_ptr,
        caller_cpu_lock_perm.state() is WriteLock,
        caller_cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        caller_cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(caller_cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(parent_container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), parent_container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).view().zombie,
        old(krnl).ctn_mp.spec_index(parent_container_ptr).view_rodata().view().depth < MAX_CONTAINER_TREE_DEPTH,
        parent_container_lock_perm.state() is WriteLock,
        parent_container_lock_perm.thread_id() == old(lctx).thread_id(),
        parent_container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(parent_process_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), parent_process_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(parent_process_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(parent_process_ptr).view().state.view() is Running || old(krnl).prc_mp.spec_index(parent_process_ptr).view().state.view() is Zombie,
        old(krnl).prc_mp.spec_index(parent_process_ptr).view_rodata().view().owning_container == parent_container_ptr,
        parent_process_lock_perm.state() is WriteLock,
        parent_process_lock_perm.thread_id() == old(lctx).thread_id(),
        parent_process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(parent_process_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == parent_container_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_process_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == source_pagetable_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id: caller_cpu_id }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
        !old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 9 + funding_page_count + 3 * source_range.len,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_2m >= 2,
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Read),
        source_pagetable_lock_perm.state() is ReadLock,
        source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread() is Read,
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), source_pagetable_lock_perm.lock_id()),
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(steps).view().len() == old(steps).view().len() + 2,
        final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 2,
        new_container_trace_after_publish(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()),
            caller_cpu_id, *source_range, funding_page_count, process_quota_4k, transfer_cpu_id, regs, if endpoint is Some { Some(endpoint_index) } else { None }),
        final(steps).snapshot_k() == *final(krnl),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        index_valid(NUM_CPUS, caller_cpu_id),
        caller_cpu_id == final(lctx).cpu_id(),
        final(krnl).cpu_published[caller_cpu_id as int].view() == (final(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_cr3, final(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_pcid),
        page_ptr_valid(ret.4),
        parent_container_ptr != ret.0,
        source_pagetable_ptr != ret.2,
        final(lctx).page_lock_map().dom() =~= set![page_ptr2page_index(ret.4)],
        final(lctx).cpu_lock_map().dom() =~= set![caller_cpu_id],
        final(lctx).container_lock_map().dom() =~= set![parent_container_ptr, ret.0],
        final(lctx).process_lock_map().dom() =~= set![parent_process_ptr, ret.1],
        final(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        endpoint is None ==> final(lctx).endpoint_lock_map().dom().is_empty(),
        endpoint is Some ==> {
            let endpoint_ptr = endpoint->Some_0;
            &&& edp_idx_valid(endpoint_index)
            &&& final(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr]
            &&& final(krnl).ep_mp.dom().contains(endpoint_ptr)
            &&& final(krnl).ep_mp.spec_index(endpoint_ptr).is_init()
            &&& typed_lock_map_contains_mode(final(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write)
            &&& !final(krnl).ep_mp.spec_index(endpoint_ptr).being_killed()
            &&& final(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((current_thread_ptr, endpoint_index))
            &&& endpoint_lock_perm is Some
            &&& endpoint_lock_perm->Some_0.state() is WriteLock
            &&& endpoint_lock_perm->Some_0.thread_id() == final(lctx).thread_id()
            &&& endpoint_lock_perm->Some_0.lock_id() == final(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id
        },
        final(lctx).scheduler_lock_map().dom().is_empty(),
        final(lctx).pcid_allocator_lock_map().dom().is_empty(),
        final(lctx).cpu_set_lock_map().dom().is_empty(),
        final(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr, ret.2],
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map().dom().is_empty(),
        final(lctx).iommu_root_table_lock_map().dom().is_empty(),
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        final(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        final(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        final(lctx).pcid_needflush_lock_map().dom().is_empty(),
        final(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), caller_cpu_id, TypedLockMode::Write),
        !final(krnl).cpu_arr.spec_index(caller_cpu_id).view().being_killed(),
        final(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().state is Running,
        final(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        caller_cpu_lock_perm.state() is WriteLock,
        caller_cpu_lock_perm.thread_id() == final(lctx).thread_id(),
        caller_cpu_lock_perm.lock_id() == final(krnl).cpu_arr.spec_index(caller_cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(ret.4), TypedLockMode::Write),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.4)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.4)).view().view().owning_container == ret.0,
        ret.9.view().state() is WriteLock,
        ret.9.view().thread_id() == final(lctx).thread_id(),
        ret.9.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.4)).view().locking_thread()->Write_lock_id,
        final(krnl).ctn_mp.dom().contains(parent_container_ptr),
        final(krnl).ctn_mp.dom().contains(ret.0),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), parent_container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), ret.0, TypedLockMode::Write),
        !final(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        !final(krnl).ctn_mp.spec_index(ret.0).being_killed(),
        final(krnl).ctn_mp.spec_index(ret.0).view_rodata().view().parent == Some(parent_container_ptr),
        final(krnl).ctn_mp.spec_index(ret.0).view_rodata().view().allocator_ptr_4k == ret.5,
        final(krnl).ctn_mp.spec_index(ret.0).view_rodata().view().scheduler == ret.3,
        final(krnl).ctn_mp.spec_index(ret.0).view_ghost().uppertree_seq.view() == final(krnl).ctn_mp.spec_index(parent_container_ptr).view_ghost().uppertree_seq.view().push(parent_container_ptr),
        final(krnl).ctn_mp.spec_index(ret.0).view().root_process == ret.1,
        parent_container_lock_perm.state() is WriteLock,
        parent_container_lock_perm.thread_id() == final(lctx).thread_id(),
        parent_container_lock_perm.lock_id() == final(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        ret.6.view().state() is WriteLock,
        ret.6.view().thread_id() == final(lctx).thread_id(),
        ret.6.view().lock_id() == final(krnl).ctn_mp.spec_index(ret.0).locking_thread()->Write_lock_id,
        final(krnl).prc_mp.dom().contains(parent_process_ptr),
        final(krnl).prc_mp.dom().contains(ret.1),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), parent_process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), ret.1, TypedLockMode::Write),
        !final(krnl).prc_mp.spec_index(parent_process_ptr).being_killed(),
        final(krnl).prc_mp.spec_index(parent_process_ptr).view().state.view() is Running || final(krnl).prc_mp.spec_index(parent_process_ptr).view().state.view() is Zombie,
        final(krnl).prc_mp.spec_index(parent_process_ptr).view_rodata().view().owning_container == parent_container_ptr,
        !final(krnl).prc_mp.spec_index(ret.1).being_killed(),
        !final(krnl).prc_mp.spec_index(ret.1).view().zombie,
        final(krnl).prc_mp.spec_index(ret.1).view().state.view() is Creating,
        final(krnl).prc_mp.spec_index(ret.1).view_rodata().view().owning_container == ret.0,
        final(krnl).prc_mp.spec_index(ret.1).view_rodata().view().pagetable == ret.2,
        final(krnl).prc_mp.spec_index(ret.1).view().iommu_table is None,
        parent_process_lock_perm.state() is WriteLock,
        parent_process_lock_perm.thread_id() == final(lctx).thread_id(),
        parent_process_lock_perm.lock_id() == final(krnl).prc_mp.spec_index(parent_process_ptr).locking_thread()->Write_lock_id,
        ret.7.view().state() is WriteLock,
        ret.7.view().thread_id() == final(lctx).thread_id(),
        ret.7.view().lock_id() == final(krnl).prc_mp.spec_index(ret.1).locking_thread()->Write_lock_id,
        final(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !final(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == parent_container_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_process_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == source_pagetable_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id: caller_cpu_id }),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view() == set![ret.4],
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().is_empty(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_1g.view().is_empty(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Share4k {
            source_range: *source_range, target_range: *source_range, shared: 0,
            origin: Share4kOrigin::NewContainer(NewContainerProgress {
                range: *source_range, funding: funding_page_count, process_quota: process_quota_4k, transfer_cpu: transfer_cpu_id, regs,
                endpoint_index: if endpoint is Some { Some(endpoint_index) } else { None }, child_container: Some(ret.0),
            }),
        }),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 1 + 3 * source_range.len,
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == final(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        final(krnl).pt_mp.dom().contains(ret.2),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Read),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), ret.2, TypedLockMode::Write),
        source_pagetable_lock_perm.state() is ReadLock,
        source_pagetable_lock_perm.thread_id() == final(lctx).thread_id(),
        final(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread() is Read,
        final(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(final(lctx).thread_id(), source_pagetable_lock_perm.lock_id()),
        ret.8.view().state() is WriteLock,
        ret.8.view().thread_id() == final(lctx).thread_id(),
        ret.8.view().lock_id() == final(krnl).pt_mp.spec_index(ret.2).locking_thread()->Write_lock_id,
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), ret.2).is_empty(),
        source_range.wf(),
        source_range.len > 0,
        final(krnl).pt_mp.spec_index(source_pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(source_range.start),
        final(krnl).pt_mp.spec_index(source_pagetable_ptr).view() == old(krnl).pt_mp.spec_index(source_pagetable_ptr).view(),
        held_pagetable_windows_unchanged(old(krnl).pt_mp, old(krnl).pt_lower.view(), final(krnl).pt_mp, final(krnl).pt_lower.view(), old(lctx)),
{
    hide(Seq::contains);
    enter_new_container_commit(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), caller_cpu_id, parent_container_ptr, parent_process_ptr, current_thread_ptr, source_pagetable_ptr,
        source_range, funding_page_count, process_quota_4k, transfer_cpu_id, parent_cpu_set, endpoint, endpoint_index, Tracked(current_thread_lock_perm), Ghost(regs),
    );
    let (pages_4k, container_page, pcid_allocator_page, Tracked(page_4k_lock_perms), Tracked(container_page_lock_perm), Tracked(pcid_allocator_page_lock_perm)) =
        allocate_new_container_pages(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), current_thread_ptr, parent_container_ptr, caller_cpu_id, Tracked(current_thread_lock_perm));
    let (funding_page_head, Ghost(funding_pages), Tracked(funding_page_lock_perms)) = allocate_staged_4k_page_chain(krnl, funding_page_count, current_thread_ptr, parent_container_ptr, caller_cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(current_thread_lock_perm));
    proof {
        page_ptr_sets_disjoint_from_index_disjoint(funding_pages, pages_4k.view());
    }
    commit_new_container_publish_staged(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), caller_cpu_id, parent_container_ptr, parent_process_ptr, current_thread_ptr, source_pagetable_ptr,
        source_range, funding_page_count, process_quota_4k, transfer_cpu_id, parent_cpu_set, endpoint, endpoint_index, &pages_4k, container_page,
        pcid_allocator_page, funding_page_head, Ghost(funding_pages), Tracked(page_4k_lock_perms), Tracked(funding_page_lock_perms),
        Tracked(container_page_lock_perm), Tracked(pcid_allocator_page_lock_perm), Tracked(caller_cpu_lock_perm), Tracked(parent_container_lock_perm),
        Tracked(parent_process_lock_perm), Tracked(current_thread_lock_perm), Tracked(source_pagetable_lock_perm), parent_cpu_set_lock_perm,
        Tracked(endpoint_lock_perm), Ghost(regs), Ghost(old(steps).view().len() as int), Ghost(kernel_k_to_kernel_u(old(steps).snapshot_k())),
    )
}

/// Checks the staged pages are fresh objects, publishes the child container, and ends the publish step after the enter step from `start`.
fn commit_new_container_publish_staged(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, caller_cpu_id: CpuId,
    parent_container_ptr: RwLockContainerPtr, parent_process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, source_pagetable_ptr: RwLockPageTableRoot,
    source_range: &VaRange4K, funding_page_count: usize, process_quota_4k: usize, transfer_cpu_id: CpuId, parent_cpu_set: RwLockCpuSetPtr,
    endpoint: Option<RwLockEndpointPtr>, endpoint_index: EndpointIdx, pages_4k: &ArrayVec<PagePtr, 9>, container_page: PagePtr, pcid_allocator_page: PagePtr,
    funding_page_head: PagePtr, Ghost(funding_pages): Ghost<Seq<PagePtr>>, Tracked(page_4k_lock_perms): Tracked<Map<PagePtr, LockPerm>>,
    Tracked(funding_page_lock_perms): Tracked<Map<PagePtr, LockPerm>>, Tracked(container_page_lock_perm): Tracked<LockPerm>,
    Tracked(pcid_allocator_page_lock_perm): Tracked<LockPerm>, Tracked(caller_cpu_lock_perm): Tracked<&LockPerm>, Tracked(parent_container_lock_perm): Tracked<&LockPerm>,
    Tracked(parent_process_lock_perm): Tracked<&LockPerm>, Tracked(current_thread_lock_perm): Tracked<&LockPerm>, Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>,
    parent_cpu_set_lock_perm: Tracked<LockPerm>, Tracked(endpoint_lock_perm): Tracked<&Option<LockPerm>>, Ghost(regs): Ghost<Registers>, Ghost(start): Ghost<int>,
    Ghost(pre): Ghost<KernelU>,
) -> (ret: (RwLockContainerPtr, RwLockProcessPtr, RwLockPageTableRoot, RwLockSchedulerPtr, PagePtr, RwLockPageAllocatorPtr, Tracked<LockPerm>, Tracked<LockPerm>,
    Tracked<LockPerm>, Tracked<LockPerm>))
    requires
        0 <= start <= old(steps).view().len(),
        new_container_trace_after_enter(old(steps).view().subrange(start, old(steps).view().len() as int), pre, caller_cpu_id, *source_range, funding_page_count,
            process_quota_4k, transfer_cpu_id, regs, if endpoint is Some { Some(endpoint_index) } else { None }),
        old(steps).snapshot_k() == *old(krnl),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        index_valid(NUM_CPUS, caller_cpu_id),
        caller_cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_published[caller_cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_pcid),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(source_range.start),
        process_quota_4k <= funding_page_count,
        funding_page_count <= usize::MAX - 9 - 3 * source_range.len,
        source_range.wf(),
        source_range.len > 0,
        index_valid(NUM_CPUS, transfer_cpu_id),
        transfer_cpu_id != caller_cpu_id,
        old(krnl).cpu_set_mp.dom().contains(parent_cpu_set),
        old(krnl).cpu_set_mp.spec_index(parent_cpu_set).view().owned_cpus.closed_view().contains(transfer_cpu_id),
        !old(krnl).cpu_set_mp.spec_index(parent_cpu_set).being_killed(),
        old(krnl).ctn_mp.spec_index(parent_container_ptr).view_rodata().view().cpu_set == parent_cpu_set,
        typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), parent_cpu_set, TypedLockMode::Write),
        parent_cpu_set_lock_perm.view().state() is WriteLock,
        parent_cpu_set_lock_perm.view().thread_id() == old(lctx).thread_id(),
        parent_cpu_set_lock_perm.view().lock_id() == old(krnl).cpu_set_mp.spec_index(parent_cpu_set).locking_thread()->Write_lock_id,
        old(lctx).page_lock_map().dom() == page_ptrs_to_indices(pages_4k.view()).union(seq![page_ptr2page_index(container_page), page_ptr2page_index(pcid_allocator_page)].to_set()).union(page_ptrs_to_indices(funding_pages)),
        forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(krnl).pg_arr.lock_id_by_index(held_page).major < ALLOCATOR_CACHE_4K_MAJOR,
        old(lctx).cpu_lock_map().dom() =~= set![caller_cpu_id],
        old(lctx).container_lock_map().dom() =~= set![parent_container_ptr],
        old(lctx).process_lock_map().dom() =~= set![parent_process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        endpoint is None ==> old(lctx).endpoint_lock_map().dom().is_empty(),
        endpoint is Some ==> {
            let endpoint_ptr = endpoint->Some_0;
            &&& edp_idx_valid(endpoint_index)
            &&& old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr]
            &&& old(krnl).ep_mp.dom().contains(endpoint_ptr)
            &&& old(krnl).ep_mp.spec_index(endpoint_ptr).is_init()
            &&& typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write)
            &&& !old(krnl).ep_mp.spec_index(endpoint_ptr).being_killed()
            &&& old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((current_thread_ptr, endpoint_index))
            &&& endpoint_lock_perm is Some
            &&& endpoint_lock_perm->Some_0.state() is WriteLock
            &&& endpoint_lock_perm->Some_0.thread_id() == old(lctx).thread_id()
            &&& endpoint_lock_perm->Some_0.lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id
        },
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom() =~= set![parent_cpu_set],
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr],
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))] old(lctx).pagetable_window_lock_map().dom().contains((p, w)) ==> p == source_pagetable_ptr,
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), caller_cpu_id, TypedLockMode::Write),
        !old(krnl).cpu_arr.spec_index(caller_cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().owning_container == parent_container_ptr,
        old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().state == CpuState::Running,
        old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        caller_cpu_lock_perm.state() is WriteLock,
        caller_cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        caller_cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(caller_cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(parent_container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), parent_container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(parent_container_ptr).view_rodata().view().depth < MAX_CONTAINER_TREE_DEPTH,
        parent_container_lock_perm.state() is WriteLock,
        parent_container_lock_perm.thread_id() == old(lctx).thread_id(),
        parent_container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(parent_process_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), parent_process_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(parent_process_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(parent_process_ptr).view().state.view() is Running || old(krnl).prc_mp.spec_index(parent_process_ptr).view().state.view() is Zombie,
        old(krnl).prc_mp.spec_index(parent_process_ptr).view_rodata().view().owning_container == parent_container_ptr,
        parent_process_lock_perm.state() is WriteLock,
        parent_process_lock_perm.thread_id() == old(lctx).thread_id(),
        parent_process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(parent_process_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == parent_container_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_process_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == source_pagetable_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id: caller_cpu_id }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view() == pages_4k.view().to_set().union(funding_pages.to_set()),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view() == set![container_page, pcid_allocator_page],
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_1g.view().is_empty(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::NewContainer(NewContainerProgress {
            range: *source_range, funding: funding_page_count, process_quota: process_quota_4k, transfer_cpu: transfer_cpu_id, regs,
            endpoint_index: if endpoint is Some { Some(endpoint_index) } else { None }, child_container: None,
        })),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 9 + funding_page_count + 3 * source_range.len,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_2m >= 2,
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Read),
        source_pagetable_lock_perm.state() is ReadLock,
        source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread() is Read,
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), source_pagetable_lock_perm.lock_id()),
        pages_4k.wf(),
        pages_4k.len() == 9,
        pages_4k.view().no_duplicates(),
        page_4k_lock_perms.dom() == pages_4k.view().to_set(),
        allocated_4k_page_lock_perms_wf(page_4k_lock_perms, old(krnl), old(lctx), current_thread_ptr, parent_container_ptr),
        pages_4k.view().to_set().subset_of(old(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view()),
        funding_pages.len() == funding_page_count,
        funding_pages.no_duplicates(),
        funding_page_head == staged_4k_page_chain_head(funding_pages),
        staged_4k_page_chain(old(krnl).pg_arr, funding_pages),
        funding_page_lock_perms.dom() == funding_pages.to_set(),
        allocated_4k_page_lock_perms_wf(funding_page_lock_perms, old(krnl), old(lctx), current_thread_ptr, parent_container_ptr),
        funding_pages.to_set().disjoint(pages_4k.view().to_set()),
        funding_pages.to_set().subset_of(old(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view()),
        container_page != pcid_allocator_page,
        page_ptr_valid(pcid_allocator_page),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        page_index_2m_valid(page_ptr2page_index(container_page)),
        page_index_2m_valid(page_ptr2page_index(pcid_allocator_page)),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(container_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(container_page)).view().view().owning_container == parent_container_ptr,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().owning_container == parent_container_ptr,
        container_page_lock_perm.state() is WriteLock,
        container_page_lock_perm.thread_id() == old(lctx).thread_id(),
        container_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(container_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(container_page), TypedLockMode::Write),
        pcid_allocator_page_lock_perm.state() is WriteLock,
        pcid_allocator_page_lock_perm.thread_id() == old(lctx).thread_id(),
        pcid_allocator_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pcid_allocator_page), TypedLockMode::Write),
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(steps).view().len() == old(steps).view().len() + 1,
        final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
        new_container_trace_after_publish(final(steps).view().subrange(start, final(steps).view().len() as int), pre, caller_cpu_id, *source_range, funding_page_count,
            process_quota_4k, transfer_cpu_id, regs, if endpoint is Some { Some(endpoint_index) } else { None }),
        final(steps).snapshot_k() == *final(krnl),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        index_valid(NUM_CPUS, caller_cpu_id),
        caller_cpu_id == final(lctx).cpu_id(),
        final(krnl).cpu_published[caller_cpu_id as int].view() == (final(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_cr3, final(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_pcid),
        page_ptr_valid(ret.4),
        parent_container_ptr != ret.0,
        source_pagetable_ptr != ret.2,
        final(lctx).page_lock_map().dom() =~= set![page_ptr2page_index(ret.4)],
        final(lctx).cpu_lock_map().dom() =~= set![caller_cpu_id],
        final(lctx).container_lock_map().dom() =~= set![parent_container_ptr, ret.0],
        final(lctx).process_lock_map().dom() =~= set![parent_process_ptr, ret.1],
        final(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        endpoint is None ==> final(lctx).endpoint_lock_map().dom().is_empty(),
        endpoint is Some ==> {
            let endpoint_ptr = endpoint->Some_0;
            &&& edp_idx_valid(endpoint_index)
            &&& final(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr]
            &&& final(krnl).ep_mp.dom().contains(endpoint_ptr)
            &&& final(krnl).ep_mp.spec_index(endpoint_ptr).is_init()
            &&& typed_lock_map_contains_mode(final(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write)
            &&& !final(krnl).ep_mp.spec_index(endpoint_ptr).being_killed()
            &&& final(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((current_thread_ptr, endpoint_index))
            &&& endpoint_lock_perm is Some
            &&& endpoint_lock_perm->Some_0.state() is WriteLock
            &&& endpoint_lock_perm->Some_0.thread_id() == final(lctx).thread_id()
            &&& endpoint_lock_perm->Some_0.lock_id() == final(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id
        },
        final(lctx).scheduler_lock_map().dom().is_empty(),
        final(lctx).pcid_allocator_lock_map().dom().is_empty(),
        final(lctx).cpu_set_lock_map().dom().is_empty(),
        final(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr, ret.2],
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map().dom().is_empty(),
        final(lctx).iommu_root_table_lock_map().dom().is_empty(),
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        final(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        final(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        final(lctx).pcid_needflush_lock_map().dom().is_empty(),
        final(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), caller_cpu_id, TypedLockMode::Write),
        !final(krnl).cpu_arr.spec_index(caller_cpu_id).view().being_killed(),
        final(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().state is Running,
        final(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        caller_cpu_lock_perm.state() is WriteLock,
        caller_cpu_lock_perm.thread_id() == final(lctx).thread_id(),
        caller_cpu_lock_perm.lock_id() == final(krnl).cpu_arr.spec_index(caller_cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(ret.4), TypedLockMode::Write),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.4)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.4)).view().view().owning_container == ret.0,
        ret.9.view().state() is WriteLock,
        ret.9.view().thread_id() == final(lctx).thread_id(),
        ret.9.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.4)).view().locking_thread()->Write_lock_id,
        final(krnl).ctn_mp.dom().contains(parent_container_ptr),
        final(krnl).ctn_mp.dom().contains(ret.0),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), parent_container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), ret.0, TypedLockMode::Write),
        !final(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        !final(krnl).ctn_mp.spec_index(ret.0).being_killed(),
        final(krnl).ctn_mp.spec_index(ret.0).view_rodata().view().parent == Some(parent_container_ptr),
        final(krnl).ctn_mp.spec_index(ret.0).view_rodata().view().allocator_ptr_4k == ret.5,
        final(krnl).ctn_mp.spec_index(ret.0).view_rodata().view().scheduler == ret.3,
        final(krnl).ctn_mp.spec_index(ret.0).view_ghost().uppertree_seq.view() == final(krnl).ctn_mp.spec_index(parent_container_ptr).view_ghost().uppertree_seq.view().push(parent_container_ptr),
        final(krnl).ctn_mp.spec_index(ret.0).view().root_process == ret.1,
        parent_container_lock_perm.state() is WriteLock,
        parent_container_lock_perm.thread_id() == final(lctx).thread_id(),
        parent_container_lock_perm.lock_id() == final(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        ret.6.view().state() is WriteLock,
        ret.6.view().thread_id() == final(lctx).thread_id(),
        ret.6.view().lock_id() == final(krnl).ctn_mp.spec_index(ret.0).locking_thread()->Write_lock_id,
        final(krnl).prc_mp.dom().contains(parent_process_ptr),
        final(krnl).prc_mp.dom().contains(ret.1),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), parent_process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), ret.1, TypedLockMode::Write),
        !final(krnl).prc_mp.spec_index(parent_process_ptr).being_killed(),
        final(krnl).prc_mp.spec_index(parent_process_ptr).view().state.view() is Running || final(krnl).prc_mp.spec_index(parent_process_ptr).view().state.view() is Zombie,
        final(krnl).prc_mp.spec_index(parent_process_ptr).view_rodata().view().owning_container == parent_container_ptr,
        !final(krnl).prc_mp.spec_index(ret.1).being_killed(),
        !final(krnl).prc_mp.spec_index(ret.1).view().zombie,
        final(krnl).prc_mp.spec_index(ret.1).view().state.view() is Creating,
        final(krnl).prc_mp.spec_index(ret.1).view_rodata().view().owning_container == ret.0,
        final(krnl).prc_mp.spec_index(ret.1).view_rodata().view().pagetable == ret.2,
        final(krnl).prc_mp.spec_index(ret.1).view().iommu_table is None,
        parent_process_lock_perm.state() is WriteLock,
        parent_process_lock_perm.thread_id() == final(lctx).thread_id(),
        parent_process_lock_perm.lock_id() == final(krnl).prc_mp.spec_index(parent_process_ptr).locking_thread()->Write_lock_id,
        ret.7.view().state() is WriteLock,
        ret.7.view().thread_id() == final(lctx).thread_id(),
        ret.7.view().lock_id() == final(krnl).prc_mp.spec_index(ret.1).locking_thread()->Write_lock_id,
        final(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !final(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == parent_container_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_process_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == source_pagetable_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id: caller_cpu_id }),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view() == set![ret.4],
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().is_empty(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_1g.view().is_empty(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Share4k {
            source_range: *source_range, target_range: *source_range, shared: 0,
            origin: Share4kOrigin::NewContainer(NewContainerProgress {
                range: *source_range, funding: funding_page_count, process_quota: process_quota_4k, transfer_cpu: transfer_cpu_id, regs,
                endpoint_index: if endpoint is Some { Some(endpoint_index) } else { None }, child_container: Some(ret.0),
            }),
        }),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 1 + 3 * source_range.len,
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == final(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        final(krnl).pt_mp.dom().contains(ret.2),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Read),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), ret.2, TypedLockMode::Write),
        source_pagetable_lock_perm.state() is ReadLock,
        source_pagetable_lock_perm.thread_id() == final(lctx).thread_id(),
        final(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread() is Read,
        final(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(final(lctx).thread_id(), source_pagetable_lock_perm.lock_id()),
        ret.8.view().state() is WriteLock,
        ret.8.view().thread_id() == final(lctx).thread_id(),
        ret.8.view().lock_id() == final(krnl).pt_mp.spec_index(ret.2).locking_thread()->Write_lock_id,
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), ret.2).is_empty(),
        source_range.wf(),
        source_range.len > 0,
        final(krnl).pt_mp.spec_index(source_pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(source_range.start),
        final(krnl).pt_mp.spec_index(source_pagetable_ptr).view() == old(krnl).pt_mp.spec_index(source_pagetable_ptr).view(),
        held_pagetable_windows_unchanged(old(krnl).pt_mp, old(krnl).pt_lower.view(), final(krnl).pt_mp, final(krnl).pt_lower.view(), old(lctx)),
{
    hide(Seq::contains);
    let ghost endpoint_index_opt: Option<EndpointIdx> = if endpoint is Some { Some(endpoint_index) } else { None };
    let ghost record = NewContainerProgress {
        range: *source_range, funding: funding_page_count, process_quota: process_quota_4k, transfer_cpu: transfer_cpu_id, regs,
        endpoint_index: endpoint_index_opt, child_container: None,
    };
    let allocator_quota_4k = funding_page_count - process_quota_4k;
    let allocator_4k_page = *pages_4k.get(0);
    let allocator_2m_page = *pages_4k.get(1);
    let allocator_1g_page = *pages_4k.get(2);
    let child_scheduler_ptr = *pages_4k.get(3);
    let child_process_ptr = *pages_4k.get(4);
    let child_pagetable_ptr = *pages_4k.get(5);
    let l4_page = *pages_4k.get(6);
    let thread_page_ptr = *pages_4k.get(7);
    let child_cpu_set = *pages_4k.get(8);
    proof {
        distinct_2m_heads_have_disjoint_all_ptrs(page_ptr2page_index(container_page), page_ptr2page_index(pcid_allocator_page));
        owned_2m_all_ptrs_belong_to_container(krnl, page_ptr2page_index(container_page), parent_container_ptr);
        owned_2m_all_ptrs_belong_to_container(krnl, page_ptr2page_index(pcid_allocator_page), parent_container_ptr);
        let ghost parent_owned_pages = krnl.ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view();
        assert(!krnl.ctn_mp.dom().contains(container_page)) by { page_ptr_roundtrip(); if krnl.ctn_mp.dom().contains(container_page) { container_pages_backward_at(krnl.pg_arr, krnl.ctn_mp, container_page); } };
        assert(!krnl.pcid_allc_mp.dom().contains(pcid_allocator_page)) by { page_ptr_roundtrip(); pcid_allocator_pages_wf_at(krnl.pg_arr, krnl.pcid_allc_mp, pcid_allocator_page); };
        assert(!krnl.cpu_set_mp.dom().contains(child_cpu_set)) by { cpu_set_pages_wf_at(krnl.cpu_set_mp, krnl.pg_arr, child_cpu_set); assert(page_4k_lock_perms.dom().contains(child_cpu_set)) by { pages_4k.view().to_set_ensures(); }; };
        assert({
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(child_scheduler_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(child_process_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(child_pagetable_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })
        }) by {
            assert({
                &&& page_4k_lock_perms.dom().contains(allocator_4k_page)
                &&& page_4k_lock_perms.dom().contains(allocator_2m_page)
                &&& page_4k_lock_perms.dom().contains(allocator_1g_page)
                &&& page_4k_lock_perms.dom().contains(child_scheduler_ptr)
                &&& page_4k_lock_perms.dom().contains(child_process_ptr)
                &&& page_4k_lock_perms.dom().contains(child_pagetable_ptr)
            }) by { pages_4k.view().to_set_ensures(); };
        };
        assert(!krnl.allc_4k_mp.dom().contains(allocator_4k_page)) by { page_ptr_roundtrip(); allocator_4k_pages_wf_at(krnl.pg_arr, krnl.allc_4k_mp, allocator_4k_page); };
        assert(!krnl.allc_2m_mp.dom().contains(allocator_2m_page)) by { page_ptr_roundtrip(); allocator_2m_pages_wf_at(krnl.pg_arr, krnl.allc_2m_mp, allocator_2m_page); };
        assert(!krnl.allc_1g_mp.dom().contains(allocator_1g_page)) by { page_ptr_roundtrip(); allocator_1g_pages_wf_at(krnl.pg_arr, krnl.allc_1g_mp, allocator_1g_page); };
        assert(!krnl.sched_mp.dom().contains(child_scheduler_ptr)) by { page_ptr_roundtrip(); scheduler_pages_wf_at(krnl.sched_mp, krnl.pg_arr, child_scheduler_ptr); };
        assert(!krnl.prc_mp.dom().contains(child_process_ptr)) by { page_ptr_roundtrip(); if krnl.prc_mp.dom().contains(child_process_ptr) { process_pages_wf_process_entry_at(krnl.pg_arr, krnl.prc_mp, child_process_ptr); } };
        assert(!krnl.pt_mp.dom().contains(child_pagetable_ptr)) by { page_ptr_roundtrip(); if krnl.pt_mp.dom().contains(child_pagetable_ptr) { pagetable_pages_wf_root_entry_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, child_pagetable_ptr); } };
        new_container_staged_pages_disjoint(krnl, lctx, pages_4k, funding_pages, page_4k_lock_perms, funding_page_lock_perms, current_thread_ptr, parent_container_ptr, container_page, pcid_allocator_page);
        assert(new_container_moved_pages(
            container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, child_scheduler_ptr, child_cpu_set, child_process_ptr,
            child_pagetable_ptr, l4_page,
        ).subset_of(parent_owned_pages)) by { reveal(new_container_moved_pages); };
        assert(!steps.snapshot_k().prc_mp.dom().contains(child_process_ptr) && parent_process_ptr != child_process_ptr) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged); };
        assert({
            &&& !krnl.prc_mp.spec_index(parent_process_ptr).view().zombie
            &&& krnl.prc_mp.spec_index(parent_process_ptr).view().pagetable == source_pagetable_ptr
            &&& krnl.cpu_arr.spec_index(transfer_cpu_id).view().view().view().state is Off
            &&& krnl.cpu_arr.spec_index(transfer_cpu_id).view().view().view().owning_container == parent_container_ptr
        }) by {
            process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, current_thread_ptr); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, parent_process_ptr);
            cpu_set_perms_wf_at(krnl.cpu_set_mp, parent_cpu_set); container_cpu_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, parent_container_ptr, transfer_cpu_id);
        };
        new_container_publish_step_pre_from_k(&*krnl, &*lctx, caller_cpu_id, parent_process_ptr, current_thread_ptr, parent_container_ptr, record);
    }
    let ghost publish_before = steps.view();
    let ghost publish_k = *krnl;
    let (
        Tracked(child_container_lock_perm), Tracked(child_process_lock_perm), Tracked(child_pagetable_lock_perm),
        Tracked(thread_page_lock_perm), Tracked(transfer_cpu_lock_perm), Tracked(child_cpu_set_lock_perm), Ghost(publish_ks),
    ) = publish_new_container_base(
        krnl, Tracked(&mut *lctx), caller_cpu_id, transfer_cpu_id, parent_cpu_set, parent_container_ptr, parent_process_ptr,
        current_thread_ptr, source_pagetable_ptr, source_range, pages_4k, container_page, pcid_allocator_page,
        funding_page_count, funding_page_head, Ghost(funding_pages), allocator_quota_4k, process_quota_4k,
        Tracked(page_4k_lock_perms), Tracked(funding_page_lock_perms), Tracked(container_page_lock_perm), Tracked(pcid_allocator_page_lock_perm),
        Tracked(parent_container_lock_perm), Tracked(current_thread_lock_perm), Ghost(regs), Ghost(endpoint_index_opt),
    );
    let ghost published_k = *krnl;
    end_new_container_created_step(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), caller_cpu_id, transfer_cpu_id, parent_cpu_set, child_cpu_set,
        parent_container_ptr, parent_process_ptr, current_thread_ptr, source_pagetable_ptr, container_page, child_process_ptr,
        child_pagetable_ptr, thread_page_ptr, Tracked(parent_container_lock_perm), Tracked(&child_container_lock_perm),
        Tracked(&thread_page_lock_perm), Tracked(transfer_cpu_lock_perm), Tracked(parent_cpu_set_lock_perm.get()), Tracked(child_cpu_set_lock_perm),
    );
    proof {
        assert(new_container_trace_after_publish(steps.view().subrange(start, steps.view().len() as int), pre, caller_cpu_id,
            *source_range, funding_page_count, process_quota_4k, transfer_cpu_id, regs, endpoint_index_opt)) by {
            let progress = Some(SyscallProgress::Share4k { source_range: *source_range, target_range: *source_range, shared: 0,
                origin: Share4kOrigin::NewContainer(NewContainerProgress { child_container: Some(container_page), ..record }) });
            new_container_root_published_from_k(&publish_k, &publish_ks.0, &publish_ks.1, &publish_ks.2, parent_container_ptr, current_thread_ptr, transfer_cpu_id,
                container_page, pcid_allocator_page, pages_4k.view(), funding_page_count, funding_pages, allocator_quota_4k, process_quota_4k, progress);
            kernel_container_publication_composes(steps.view().last().old_u, kernel_k_to_kernel_u(published_k), steps.view().last().new_u,
                parent_container_ptr, container_page, child_process_ptr, current_thread_ptr, transfer_cpu_id, funding_page_count,
                process_quota_4k, new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page,
                    allocator_1g_page, child_scheduler_ptr, child_cpu_set, child_process_ptr, child_pagetable_ptr, l4_page).union(funding_pages.to_set()), thread_page_ptr, progress);
            new_container_publish_step_from_u(steps.view().last().old_u, steps.view().last().new_u, caller_cpu_id, current_thread_ptr, parent_container_ptr, container_page, child_process_ptr, record);
            new_container_trace_publish_step(&*steps, publish_before, start, pre, caller_cpu_id, *source_range,
                funding_page_count, process_quota_4k, transfer_cpu_id, regs, endpoint_index_opt);
        };
    }
    (container_page, child_process_ptr, child_pagetable_ptr, child_scheduler_ptr, thread_page_ptr, allocator_4k_page, Tracked(child_container_lock_perm),
        Tracked(child_process_lock_perm), Tracked(child_pagetable_lock_perm), Tracked(thread_page_lock_perm))
}
}
