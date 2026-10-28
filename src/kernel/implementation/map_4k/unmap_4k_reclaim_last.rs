use vstd::prelude::*;
use crate::*;
use super::unmap_4k_reclaim::remove_last_4k_mapping_to_allocator;
use super::unmap_iommu_4k_reclaim::remove_last_iommu_4k_mapping_to_allocator;
use super::unmap_4k_reclaim_last_cache::reclaim_last_lock_4k_cache_with_room;

verus! {
proof fn prove_unmapped_4k_page_owner_position_in_thread_container_chain(krnl: &KernelK, pagetable: RwLockPageTableRoot, va: VAddr, page_ptr: PagePtr, thread_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, depth: usize, thread_depth: usize)
    requires
        krnl.inv(),
        krnl.pt_mp.dom().contains(pagetable),
        pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().spec_index(va).addr == page_ptr,
        page_ptr_valid(page_ptr),
        krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == owner,
        krnl.ctn_mp.dom().contains(owner),
        krnl.ctn_mp.spec_index(owner).view_rodata().view().depth == depth,
        krnl.thr_mp.dom().contains(thread_ptr),
        !thread_is_dangling(krnl.thr_mp.spec_index(thread_ptr)),
        krnl.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable || krnl.prc_mp.spec_index(krnl.pt_mp.spec_index(pagetable).view().proc_ptr).view_rodata().view().owning_container == krnl.thr_mp.spec_index(thread_ptr).view().owning_container,
        krnl.thr_mp.spec_index(thread_ptr).view().container_depth == thread_depth,
    ensures
        depth <= thread_depth,
        thread_depth <= MAX_CONTAINER_TREE_DEPTH,
        if depth == thread_depth { owner == krnl.thr_mp.spec_index(thread_ptr).view().owning_container } else { krnl.thr_mp.spec_index(thread_ptr).view().upper_container_seq.view().spec_index(depth as int) == owner },
{
    let page_index = page_ptr2page_index(page_ptr);
    let proc_ptr = krnl.pt_mp.spec_index(pagetable).view().proc_ptr;
    let thread_proc = krnl.thr_mp.spec_index(thread_ptr).view().owning_proc;
    let thread_owner = krnl.thr_mp.spec_index(thread_ptr).view().owning_container;
    assert(krnl.pg_arr.spec_index(page_index).view().view().state == PageState::Mapped4k && krnl.pg_arr.spec_index(page_index).view().view().mappings().contains((pagetable, va))
        && pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().spec_index(va).owning_container.view() == owner) by { reveal(mapped_4k_page_pagetable_wf); };
    assert(krnl.prc_mp.dom().contains(proc_ptr) && {
            ||| krnl.prc_mp.spec_index(proc_ptr).view_rodata().view().owning_container == owner
            ||| krnl.ctn_mp.spec_index(owner).view_ghost().subtree_set.view().contains(krnl.prc_mp.spec_index(proc_ptr).view_rodata().view().owning_container)
        }) by { reveal(container_process_page_pagetable_wf); };
    assert(krnl.prc_mp.dom().contains(thread_proc) && krnl.prc_mp.spec_index(thread_proc).view_rodata().view().owning_container == thread_owner) by { reveal(process_thread_wf); };
    assert(krnl.prc_mp.spec_index(proc_ptr).view_rodata().view().owning_container == thread_owner) by {
        if krnl.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable {
            assert(!krnl.prc_mp.spec_index(thread_proc).view().zombie && krnl.prc_mp.spec_index(thread_proc).view().pagetable == pagetable) by { reveal(process_thread_wf); };
            assert(proc_ptr == thread_proc) by { reveal(process_pagetable_match); };
        }
    };
    assert(krnl.ctn_mp.dom().contains(thread_owner) && krnl.ctn_mp.spec_index(thread_owner).view_ghost().owned_threads.view().contains(thread_ptr)
        && krnl.thr_mp.spec_index(thread_ptr).view().upper_container_seq == krnl.ctn_mp.spec_index(thread_owner).view_ghost().uppertree_seq
        && thread_depth == krnl.ctn_mp.spec_index(thread_owner).view_rodata().view().depth) by { reveal(container_thread_wf); };
    assert(krnl.thr_mp.spec_index(thread_ptr).view().upper_container_seq.view().len() == thread_depth
        && thread_depth <= MAX_CONTAINER_TREE_DEPTH) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    if owner != thread_owner {
        assert(krnl.ctn_mp.spec_index(thread_owner).view_ghost().uppertree_seq.view().len() > depth
            && krnl.ctn_mp.spec_index(thread_owner).view_ghost().uppertree_seq.view().spec_index(depth as int) == owner) by { reveal(container_subtree_set_wf); };
    }
}

proof fn prove_unmapped_iommu_4k_page_owner_position_in_thread_container_chain(
    krnl: &KernelK, iommu_table: RwLockPageTableRoot, iova: VAddr, page_ptr: PagePtr, thread_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, depth: usize, thread_depth: usize,
)
    requires
        krnl.inv(),
        krnl.it_mp.dom().contains(iommu_table),
        krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(iova),
        krnl.it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(iova).addr == page_ptr,
        page_ptr_valid(page_ptr),
        krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == owner,
        krnl.ctn_mp.dom().contains(owner),
        krnl.ctn_mp.spec_index(owner).view_rodata().view().depth == depth,
        krnl.thr_mp.dom().contains(thread_ptr),
        !thread_is_dangling(krnl.thr_mp.spec_index(thread_ptr)),
        krnl.prc_mp.spec_index(krnl.thr_mp.spec_index(thread_ptr).view().owning_proc).view().iommu_table == Some(iommu_table)
            || krnl.prc_mp.spec_index(krnl.it_mp.spec_index(iommu_table).view().proc_ptr).view_rodata().view().owning_container == krnl.thr_mp.spec_index(thread_ptr).view().owning_container,
        krnl.thr_mp.spec_index(thread_ptr).view().container_depth == thread_depth,
    ensures
        depth <= thread_depth,
        thread_depth <= MAX_CONTAINER_TREE_DEPTH,
        if depth == thread_depth { owner == krnl.thr_mp.spec_index(thread_ptr).view().owning_container } else { krnl.thr_mp.spec_index(thread_ptr).view().upper_container_seq.view().spec_index(depth as int) == owner },
{
    let page_index = page_ptr2page_index(page_ptr);
    let proc_ptr = krnl.it_mp.spec_index(iommu_table).view().proc_ptr;
    let thread_proc = krnl.thr_mp.spec_index(thread_ptr).view().owning_proc;
    let thread_owner = krnl.thr_mp.spec_index(thread_ptr).view().owning_container;
    assert(krnl.pg_arr.spec_index(page_index).view().view().state == PageState::Mapped4k && krnl.pg_arr.spec_index(page_index).view().view().iommu_mappings().contains((iommu_table, iova))) by { reveal(page_iommu_table_wf); };
    assert(krnl.prc_mp.dom().contains(proc_ptr) && {
            ||| krnl.prc_mp.spec_index(proc_ptr).view_rodata().view().owning_container == owner
            ||| krnl.ctn_mp.spec_index(owner).view_ghost().subtree_set.view().contains(krnl.prc_mp.spec_index(proc_ptr).view_rodata().view().owning_container)
        }) by { reveal(page_iommu_table_wf); };
    assert(krnl.prc_mp.dom().contains(thread_proc) && krnl.prc_mp.spec_index(thread_proc).view_rodata().view().owning_container == thread_owner) by { reveal(process_thread_wf); };
    assert(krnl.prc_mp.spec_index(proc_ptr).view_rodata().view().owning_container == thread_owner) by { if krnl.prc_mp.spec_index(thread_proc).view().iommu_table == Some(iommu_table) { assert(proc_ptr == thread_proc) by { reveal(process_iommu_table_match); }; } };
    assert(krnl.ctn_mp.dom().contains(thread_owner) && krnl.ctn_mp.spec_index(thread_owner).view_ghost().owned_threads.view().contains(thread_ptr)
        && krnl.thr_mp.spec_index(thread_ptr).view().upper_container_seq == krnl.ctn_mp.spec_index(thread_owner).view_ghost().uppertree_seq
        && thread_depth == krnl.ctn_mp.spec_index(thread_owner).view_rodata().view().depth) by { reveal(container_thread_wf); };
    assert(krnl.thr_mp.spec_index(thread_ptr).view().upper_container_seq.view().len() == thread_depth
        && thread_depth <= MAX_CONTAINER_TREE_DEPTH) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    if owner != thread_owner {
        assert(krnl.ctn_mp.spec_index(thread_owner).view_ghost().uppertree_seq.view().len() > depth
            && krnl.ctn_mp.spec_index(thread_owner).view_ghost().uppertree_seq.view().spec_index(depth as int) == owner) by { reveal(container_subtree_set_wf); };
    }
}

/// Frees the page behind the last mapping, a hidden 4K leaf of a page table held in write mode iff `write_held`: drains a full CPU cache of the owner's allocator under its own step
/// boundary, then moves the page into that cache and credits the thread's pending free quota at the owner's depth. The page lock stays held. Across the drain only the held
/// windows of a read-held table keep their leaves.
pub fn reclaim_last_4k_mapping(
    krnl: &mut KernelK, pagetable: RwLockPageTableRoot, va: VAddr, page_ptr: PagePtr, owner: RwLockContainerPtr, thread_ptr: RwLockThreadPtr, cpu_id: CpuId, indirect: &mut [usize; MAX_CONTAINER_TREE_DEPTH],
    direct: &mut usize, write_held: bool, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, pagetable_perm: Tracked<&LockPerm>, page_perm: Tracked<&LockPerm>,
    thread_perm: Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        *old(krnl) == (KernelK { pt_mp: old(krnl).pt_mp, pt_lower: old(krnl).pt_lower, pg_arr: old(krnl).pg_arr, ..old(steps).snapshot_k() }),
        old(krnl).pt_mp.unchanged_except(&old(steps).snapshot_k().pt_mp, pagetable),
        old(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(steps).snapshot_k().pt_mp.spec_index(pagetable).locking_thread(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        !thread_is_dangling(old(krnl).thr_mp.spec_index(thread_ptr)),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable || old(krnl).prc_mp.spec_index(old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr).view_rodata().view().owning_container == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container,
        *old(direct) == old(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
        forall|depth: int| #![trigger old(indirect)[depth]] 0 <= depth < old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth ==> old(indirect)[depth] == old(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(depth),
        old(krnl).pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(va).0,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(va).present,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(va).addr == page_ptr,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(window_of(va)).stale_cpus is None,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, if write_held { TypedLockMode::Write } else { TypedLockMode::Read }),
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        write_held ==> pagetable_perm.view().state() is WriteLock,
        write_held ==> pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        !write_held ==> pagetable_perm.view().state() is ReadLock,
        !write_held ==> old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_perm.view().lock_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, WindowVa { va: spec_index2va((spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), 0usize)) }), TypedLockMode::Write),
        page_ptr_valid(page_ptr),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count == 1,
        !old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().is_io_page,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == owner,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        page_perm.view().state() is WriteLock,
        page_perm.view().thread_id() == old(lctx).thread_id(),
        page_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
    ensures
        final(steps).view() == old(steps).view(),
        final(steps).nonlock_view() == old(steps).nonlock_view(),
        *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, pg_arr: final(krnl).pg_arr, thr_mp: final(krnl).thr_mp, allc_4k_mp: final(krnl).allc_4k_mp, ..final(steps).snapshot_k() }),
        final(krnl).pt_mp.unchanged_except(&final(steps).snapshot_k().pt_mp, pagetable),
        final(krnl).pt_lower.view() == final(steps).snapshot_k().pt_lower.view().insert(pagetable, final(krnl).pt_lower.view().spec_index(pagetable)),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == final(steps).snapshot_k().pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).thr_mp.unchanged_except(&final(steps).snapshot_k().thr_mp, thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == final(steps).snapshot_k().thr_mp.spec_index(thread_ptr).locking_thread(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(krnl)),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(page_ptr)), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write }),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread(),
        held_threads_unchanged_except(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx), set![thread_ptr]),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { direct_free_quota_pending_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k,
            indirect_free_quota_pending_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        *final(direct) == final(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
        forall|depth: int| #![trigger final(indirect)[depth]] 0 <= depth < final(krnl).thr_mp.spec_index(thread_ptr).view().container_depth ==> final(indirect)[depth] == final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(depth),
        final(krnl).pt_mp.dom().contains(pagetable),
        write_held ==> final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        !write_held ==> held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        write_held ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().remove(va),
        write_held ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m(),
        write_held ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g(),
        write_held ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.l2_lock == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_lock,
        write_held ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus,
        final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end,
        final(krnl).pt_mp.spec_index(pagetable).view() == old(krnl).pt_mp.spec_index(pagetable).view(),
        !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) ==> {
            let pre = pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            let post = pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable);
            &&& post.window_view(w).lock_state == pre.window_view(w).lock_state
            &&& post.window_view(w).stale_cpus == pre.window_view(w).stale_cpus
            &&& post.mapping_2m().dom().contains(w.va) == pre.mapping_2m().dom().contains(w.va)
            &&& pre.mapping_2m().dom().contains(w.va) ==> post.mapping_2m().spec_index(w.va) == pre.mapping_2m().spec_index(w.va)
        },
        forall|w: WindowVa, v: VAddr|
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
            old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) && v != va ==> {
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                    ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(v)
            },
{
    let ghost page_index = page_ptr2page_index(page_ptr);
    let ghost entry_lctx = *lctx;
    proof {
        if write_held { krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable); } else { krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable); }
        spec_va_4k_valid_index_roundtrip(va);
        spec_va_4k_index_roundtrip_at(window_of(va).va, spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), 0usize);
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl);
        krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
        if write_held { pagetable_lower_backup_wf_at(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable); pagetable_lower_backup_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable); }
        process_pagetable_match_pagetable_at(old(krnl).prc_mp, old(krnl).pt_mp, pagetable); process_pagetable_match_pagetable_at(krnl.prc_mp, krnl.pt_mp, pagetable);
        held_pagetable_window_mapping_4k_unchanged_at(old(krnl).pt_mp, old(krnl).pt_lower.view(), krnl.pt_mp, krnl.pt_lower.view(), &entry_lctx, pagetable, window_of(va), va);
    }
    let ghost drained_pre = *krnl;
    proof { assert(krnl.ctn_mp.dom().contains(owner)) by { container_page_owner_backward_at(krnl.ctn_mp, krnl.pg_arr, page_index); }; container_perms_wf_at(krnl.ctn_mp, owner); }
    let owner_ro = krnl.ctn_mp.borrow_rodata(owner).borrow();
    let depth = owner_ro.depth;
    let allocator_ptr = owner_ro.allocator_ptr_4k;
    proof { thread_perms_wf_map(krnl.thr_mp); thread_perms_wf_at(krnl.thr_mp, thread_ptr); }
    let thread = krnl.thr_mp.borrow_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), thread_perm);
    let thread_depth = thread.container_depth;
    proof { prove_unmapped_4k_page_owner_position_in_thread_container_chain(krnl, pagetable, va, page_ptr, thread_ptr, owner, depth, thread_depth); }
    proof { assert(krnl.allc_4k_mp.dom().contains(allocator_ptr)) by { container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, owner); }; }
    let ghost cache_lctx = *lctx;
    let Tracked(cache_perm) = reclaim_last_lock_4k_cache_with_room(krnl, allocator_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps));
    proof {
        if write_held { pagetable_lower_backup_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable); }
        held_pagetable_window_mapping_4k_unchanged_at(drained_pre.pt_mp, drained_pre.pt_lower.view(), krnl.pt_mp, krnl.pt_lower.view(), &cache_lctx, pagetable, window_of(va), va);
    }
    assert(krnl.ctn_mp.dom().contains(owner) && krnl.ctn_mp.spec_index(owner).view_rodata().view().depth == depth
        && krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr) by { container_page_owner_backward_at(krnl.ctn_mp, krnl.pg_arr, page_index); };
    let mut counter = if depth == thread_depth { *direct } else { indirect[depth] };
    remove_last_4k_mapping_to_allocator(krnl, pagetable, va, page_ptr, thread_ptr, owner, depth, allocator_ptr, cpu_id, &mut counter, write_held, Tracked(&mut *lctx), pagetable_perm, page_perm, thread_perm,
        Tracked(&cache_perm));
    if depth == thread_depth { *direct = counter; } else { indirect[depth] = counter; }
    krnl.wunlock_allocator_cache_4k(allocator_ptr, cpu_id, Tracked(&mut *lctx), Tracked(cache_perm));
    proof {
        assert(lctx.allocator_cache_4k_lock_map() =~= old(lctx).allocator_cache_4k_lock_map());
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
}

/// Frees the page behind the last mapping, a 4K leaf of a write-locked IOMMU table that is hidden iff `!was_present` (a present leaf requires a table without a domain id): drains a
/// full CPU cache of the owner's allocator under its own step boundary, then moves the page into that cache and credits the thread's pending free quota at the owner's depth. The
/// page lock stays held.
pub fn reclaim_last_iommu_4k_mapping(
    krnl: &mut KernelK, iommu_table: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index, L1Index), page_ptr: PagePtr, l1_ptr: PageMapPtr, owner: RwLockContainerPtr, thread_ptr: RwLockThreadPtr, cpu_id: CpuId,
    indirect: &mut [usize; MAX_CONTAINER_TREE_DEPTH], direct: &mut usize, Ghost(was_present): Ghost<bool>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    iommu_table_perm: Tracked<&LockPerm>, page_perm: Tracked<&LockPerm>, thread_perm: Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        *old(krnl) == (KernelK { pg_arr: old(krnl).pg_arr, ..old(steps).snapshot_k() }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        !thread_is_dangling(old(krnl).thr_mp.spec_index(thread_ptr)),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc).view().iommu_table == Some(iommu_table)
            || old(krnl).prc_mp.spec_index(old(krnl).it_mp.spec_index(iommu_table).view().proc_ptr).view_rodata().view().owning_container == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container,
        *old(direct) == old(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
        forall|depth: int| #![trigger old(indirect)[depth]] 0 <= depth < old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth ==> old(indirect)[depth] == old(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(depth),
        old(krnl).it_mp.dom().contains(iommu_table),
        pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va(indices)),
        old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(spec_index2va(indices)).present == was_present,
        was_present ==> old(krnl).it_mp.spec_index(iommu_table).view().did is None,
        old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(spec_index2va(indices)).addr == page_ptr,
        old(krnl).it_mp.spec_index(iommu_table).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        old(krnl).it_mp.spec_index(iommu_table).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == l1_ptr,
        typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table, TypedLockMode::Write),
        iommu_table_perm.view().state() is WriteLock,
        iommu_table_perm.view().thread_id() == old(lctx).thread_id(),
        iommu_table_perm.view().lock_id() == old(krnl).it_mp.spec_index(iommu_table).locking_thread()->Write_lock_id,
        page_ptr_valid(page_ptr),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count == 1,
        !old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().is_io_page,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == owner,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        page_perm.view().state() is WriteLock,
        page_perm.view().thread_id() == old(lctx).thread_id(),
        page_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
        !was_present ==> iommu_table_tlb_entries_present(old(krnl).iommu_tlb, old(krnl).irt.view(), old(krnl).it_mp, iommu_table),
    ensures
        final(steps).view() == old(steps).view(),
        final(steps).nonlock_view() == old(steps).nonlock_view(),
        *final(krnl) == (KernelK { it_mp: final(krnl).it_mp, pg_arr: final(krnl).pg_arr, thr_mp: final(krnl).thr_mp, allc_4k_mp: final(krnl).allc_4k_mp, ..final(steps).snapshot_k() }),
        final(krnl).it_mp.unchanged_except(&final(steps).snapshot_k().it_mp, iommu_table),
        final(krnl).it_mp.spec_index(iommu_table).locking_thread() == final(steps).snapshot_k().it_mp.spec_index(iommu_table).locking_thread(),
        final(krnl).thr_mp.unchanged_except(&final(steps).snapshot_k().thr_mp, thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == final(steps).snapshot_k().thr_mp.spec_index(thread_ptr).locking_thread(),
        !was_present ==> kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
        was_present ==> kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), &KernelK { it_mp: final(steps).snapshot_k().it_mp, ..*final(krnl) }),
        kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(krnl)),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        iommu_table_tlb_entries_present(final(krnl).iommu_tlb, final(krnl).irt.view(), final(krnl).it_mp, iommu_table),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(page_ptr)), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write }),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread(),
        held_threads_unchanged_except(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx), set![thread_ptr]),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        forall|p: RwLockPageTableRoot| #![trigger old(lctx).pagetable_lock_map().dom().contains(p)] typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), p, TypedLockMode::Write)
            ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), p) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), p),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { direct_free_quota_pending_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k,
            indirect_free_quota_pending_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        *final(direct) == final(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
        forall|depth: int| #![trigger final(indirect)[depth]] 0 <= depth < final(krnl).thr_mp.spec_index(thread_ptr).view().container_depth ==> final(indirect)[depth] == final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(depth),
        final(krnl).it_mp.dom().contains(iommu_table),
        final(krnl).it_mp.spec_index(iommu_table).locking_thread() == old(krnl).it_mp.spec_index(iommu_table).locking_thread(),
        final(krnl).it_mp.spec_index(iommu_table).being_killed() == old(krnl).it_mp.spec_index(iommu_table).being_killed(),
        final(krnl).it_mp.spec_index(iommu_table).view().mapping_4k() == old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().remove(spec_index2va(indices)),
        final(krnl).it_mp.spec_index(iommu_table).view().mapping_2m() == old(krnl).it_mp.spec_index(iommu_table).view().mapping_2m(),
        final(krnl).it_mp.spec_index(iommu_table).view().mapping_1g() == old(krnl).it_mp.spec_index(iommu_table).view().mapping_1g(),
        final(krnl).it_mp.spec_index(iommu_table).view().kernel_l4_end == old(krnl).it_mp.spec_index(iommu_table).view().kernel_l4_end,
        final(krnl).it_mp.spec_index(iommu_table).view().did == old(krnl).it_mp.spec_index(iommu_table).view().did,
        final(krnl).it_mp.spec_index(iommu_table).view().cr3 == old(krnl).it_mp.spec_index(iommu_table).view().cr3,
        final(krnl).it_mp.spec_index(iommu_table).view().proc_ptr == old(krnl).it_mp.spec_index(iommu_table).view().proc_ptr,
        final(steps).snapshot_k().it_mp.spec_index(iommu_table) == old(krnl).it_mp.spec_index(iommu_table),
        process_iommu_table_match(final(steps).snapshot_k().prc_mp, final(steps).snapshot_k().it_mp),
        was_present ==> final(krnl).it_mp.spec_index(iommu_table).view().user_view(LockStateU::Unlocked).mapping_4k
            == old(krnl).it_mp.spec_index(iommu_table).view().user_view(LockStateU::Unlocked).mapping_4k.remove(spec_index2va(indices)),
{
    let ghost page_index = page_ptr2page_index(page_ptr);
    proof { assert(krnl.ctn_mp.dom().contains(owner)) by { container_page_owner_backward_at(krnl.ctn_mp, krnl.pg_arr, page_index); }; container_perms_wf_at(krnl.ctn_mp, owner); }
    let owner_ro = krnl.ctn_mp.borrow_rodata(owner).borrow();
    let depth = owner_ro.depth;
    let allocator_ptr = owner_ro.allocator_ptr_4k;
    proof { thread_perms_wf_map(krnl.thr_mp); thread_perms_wf_at(krnl.thr_mp, thread_ptr); }
    let thread = krnl.thr_mp.borrow_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), thread_perm);
    let thread_depth = thread.container_depth;
    proof { prove_unmapped_iommu_4k_page_owner_position_in_thread_container_chain(krnl, iommu_table, spec_index2va(indices), page_ptr, thread_ptr, owner, depth, thread_depth); }
    proof { assert(krnl.allc_4k_mp.dom().contains(allocator_ptr)) by { container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, owner); }; }
    let Tracked(cache_perm) = reclaim_last_lock_4k_cache_with_room(krnl, allocator_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps));
    assert(krnl.ctn_mp.dom().contains(owner) && krnl.ctn_mp.spec_index(owner).view_rodata().view().depth == depth
        && krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr) by { container_page_owner_backward_at(krnl.ctn_mp, krnl.pg_arr, page_index); };
    let mut counter = if depth == thread_depth { *direct } else { indirect[depth] };
    remove_last_iommu_4k_mapping_to_allocator(krnl, iommu_table, indices, page_ptr, l1_ptr, thread_ptr, owner, depth, allocator_ptr, cpu_id, &mut counter, Ghost(was_present),
        Tracked(&mut *lctx), iommu_table_perm, page_perm, thread_perm, Tracked(&cache_perm));
    if depth == thread_depth { *direct = counter; } else { indirect[depth] = counter; }
    krnl.wunlock_allocator_cache_4k(allocator_ptr, cpu_id, Tracked(&mut *lctx), Tracked(cache_perm));
    proof {
        assert(lctx.allocator_cache_4k_lock_map() =~= old(lctx).allocator_cache_4k_lock_map());
        if was_present {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &KernelK { it_mp: steps.snapshot_k().it_mp, ..*krnl })) by {
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
            };
        } else {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        }
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
}
}
