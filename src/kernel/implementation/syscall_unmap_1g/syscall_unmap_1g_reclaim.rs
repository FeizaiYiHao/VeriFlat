use vstd::prelude::*;
use crate::*;
use super::syscall_unmap_1g_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_unmap_1g_trace::*;
#[cfg(feature = "split-crates")]
use veriflat_map_4k::map_4k::reclaim_held_1g_page::reclaim_held_1g_page;
#[cfg(feature = "split-crates")]
use veriflat_alloc_page::free_1g_page::refund_unmap_1g_quota;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::map_4k::reclaim_held_1g_page::reclaim_held_1g_page;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::free_1g_page::refund_unmap_1g_quota;

verus! {
/// After every page of `range` was hidden and flushed in the write-held page table `pagetable`: reclaim each page, which records no step, and refund the 1G quota the reclaims left pending on the thread. Steps recorded from `start` stay range steps; only the range's 1G leaves change. `hv`
/// is the table record before the flush, whose held root and L3 entries resolve; the record differs from it only in its stale-CPU set, and reclaiming 1G leaves keeps every held root and L3 entry.
pub(super) fn unmap_1g_reclaim_range(
    krnl: &mut KernelK, range: &VaRange1G, pagetable: RwLockPageTableRoot, thrd_ptr: RwLockThreadPtr, cpu_id: CpuId, Ghost(start): Ghost<int>, Ghost(hv): Ghost<PageTableHigher<PT_TYPE>>, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>, thread_perm: Tracked<&LockPerm>, pagetable_perm: Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).page_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        forall|j: int| #![trigger old(steps).view()[j]] start <= j < old(steps).view().len() ==> unmap_1g_range_step(old(steps).view()[j], cpu_id),
        index_valid(NUM_CPUS, cpu_id),
        old(lctx).cpu_id() == cpu_id,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap1g { range: *range, unmapped: range.len, flushed: true }),
        !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
        old(krnl).pt_mp.dom().contains(pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        old(krnl).pt_mp.spec_index(pagetable).view() == (PageTableHigher { table_stale_cpus: old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus, ..hv }),
        forall|l4i: L4Index| #![trigger hv.spec_held_l4(l4i)] hv.kernel_l4_end <= l4i && pei_valid(l4i) && hv.spec_held_l4(l4i) is Some ==> hv.spec_resolve_mapping_l4(l4i) is Some,
        forall|l4i: L4Index, l3i: L3Index| #![trigger hv.spec_held_l3(l4i, l3i)]
            hv.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && hv.spec_held_l3(l4i, l3i) is Some ==> hv.spec_resolve_mapping_l3(l4i, l3i) is Some,
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        forall|v: VAddr| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(v).present,
        forall|v: VAddr| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(v)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(v) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(v).present,
        range.wf(),
        forall|j: int| #![trigger range.view()[j]] 0 <= j < range.len ==> {
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g().dom().contains(range.view()[j])
            &&& !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g().spec_index(range.view()[j]).present
        },
        forall|v: VAddr| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g().dom().contains(v)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g().dom().contains(v) && !range.view().contains(v)
            ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g().spec_index(v).present,
    ensures
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len() <= old(steps).view().len() + MAX_CONTAINER_TREE_DEPTH + 1,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|j: int| #![trigger final(steps).view()[j]] start <= j < final(steps).view().len() ==> unmap_1g_range_step(final(steps).view()[j], cpu_id),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        final(krnl).cpu_op.view().view()[cpu_id as int] == old(krnl).cpu_op.view().view()[cpu_id as int],
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(krnl).cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().killer_info() == old(krnl).cpu_arr.spec_index(cpu_id).view().killer_info(),
        final(krnl).thrd_mp.dom().contains(thrd_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == old(krnl).thrd_mp.spec_index(thrd_ptr).view(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        final(krnl).pt_mp.spec_index(pagetable).view().proc_ptr == old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr,
        final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end,
        final(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower,
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).leaves_present(),
        forall|l4i: L4Index| #![trigger final(krnl).pt_mp.spec_index(pagetable).view().spec_held_l4(l4i)]
            final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= l4i && pei_valid(l4i) && final(krnl).pt_mp.spec_index(pagetable).view().spec_held_l4(l4i) is Some
            ==> final(krnl).pt_mp.spec_index(pagetable).view().spec_resolve_mapping_l4(l4i) is Some,
        forall|l4i: L4Index, l3i: L3Index| #![trigger final(krnl).pt_mp.spec_index(pagetable).view().spec_held_l3(l4i, l3i)]
            final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && final(krnl).pt_mp.spec_index(pagetable).view().spec_held_l3(l4i, l3i) is Some
            ==> final(krnl).pt_mp.spec_index(pagetable).view().spec_resolve_mapping_l3(l4i, l3i) is Some,
        forall|j: int| #![trigger range.view()[j]] 0 <= j < range.len ==> !whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_1g().dom().contains(range.view()[j]),
{
    let ghost prc_ptr = krnl.thrd_mp.spec_index(thrd_ptr).view().owning_proc;
    let ghost ctn_ptr = krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container;
    let ghost entry = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
    assert(krnl.thrd_mp.spec_index(thrd_ptr).inv() && krnl.thrd_mp.spec_index(thrd_ptr).view().container_depth <= MAX_CONTAINER_TREE_DEPTH) by {
        thread_perms_wf_at(krnl.thrd_mp, thrd_ptr); container_thread_wf_thread_at(krnl.ctn_mp, krnl.thrd_mp, thrd_ptr);
        container_perms_wf_at(krnl.ctn_mp, krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container);
    };
    let mut indirect = [0usize; MAX_CONTAINER_TREE_DEPTH];
    let mut direct = 0usize;
    let mut i = 0usize;
    while i < range.len
        invariant
            prc_ptr == old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc,
            ctn_ptr == old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container,
            entry == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable),
            steps.view() == old(steps).view(),
            0 <= start <= old(steps).view().len(),
            forall|j: int| #![trigger old(steps).view()[j]] start <= j < old(steps).view().len() ==> unmap_1g_range_step(old(steps).view()[j], cpu_id),
            index_valid(NUM_CPUS, cpu_id),
            old(lctx).cpu_id() == cpu_id,
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
            old(krnl).thrd_mp.dom().contains(thrd_ptr),
            old(krnl).pt_mp.dom().contains(pagetable),
            thread_perm.view().state() is WriteLock,
            thread_perm.view().thread_id() == old(lctx).thread_id(),
            thread_perm.view().lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
            pagetable_perm.view().state() is WriteLock,
            pagetable_perm.view().thread_id() == old(lctx).thread_id(),
            pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
            old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
            old(krnl).thrd_mp.spec_index(thrd_ptr).inv(),
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth <= MAX_CONTAINER_TREE_DEPTH,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap1g { range: *range, unmapped: range.len, flushed: true }),
            !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
            old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
            steps.snapshot_k() == *krnl,
            krnl.cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
            krnl.cpu_op.view().view()[cpu_id as int] == old(krnl).cpu_op.view().view()[cpu_id as int],
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.kernel_view_locking_state() is Acquire,
            held_locks_order_below(krnl, lctx, ALLOCATOR_CACHE_4K_MAJOR),
            krnl.cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
            krnl.cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
            krnl.cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
            krnl.cpu_arr.spec_index(cpu_id).view().killer_info() == old(krnl).cpu_arr.spec_index(cpu_id).view().killer_info(),
            krnl.thrd_mp.dom().contains(thrd_ptr),
            krnl.thrd_mp.spec_index(thrd_ptr).view() == (Thread {
                direct_free_quota_pending_1g: krnl.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_1g,
                indirect_free_quota_pending_1g: krnl.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_1g, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view()
            }),
            krnl.thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
            krnl.thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
            krnl.thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
            direct == krnl.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_1g.view(),
            forall|d: int| #![trigger indirect[d]] 0 <= d < krnl.thrd_mp.spec_index(thrd_ptr).view().container_depth
                ==> indirect[d] == krnl.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_1g.view().spec_index(d),
            krnl.pt_mp.dom().contains(pagetable),
            krnl.pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
            krnl.pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
            krnl.pt_mp.spec_index(pagetable).view() == (PageTableHigher {
                l3_tables: krnl.pt_mp.spec_index(pagetable).view().l3_tables, mapping_1g: krnl.pt_mp.spec_index(pagetable).view().mapping_1g, ..old(krnl).pt_mp.spec_index(pagetable).view()
            }),
            whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower == entry.lower,
            old(krnl).pt_mp.spec_index(pagetable).view() == (PageTableHigher { table_stale_cpus: old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus, ..hv }),
            forall|l4i: L4Index| #![trigger hv.spec_held_l4(l4i)] hv.kernel_l4_end <= l4i && pei_valid(l4i) && hv.spec_held_l4(l4i) is Some ==> hv.spec_resolve_mapping_l4(l4i) is Some,
            forall|l4i: L4Index, l3i: L3Index| #![trigger hv.spec_held_l3(l4i, l3i)]
                hv.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && hv.spec_held_l3(l4i, l3i) is Some ==> hv.spec_resolve_mapping_l3(l4i, l3i) is Some,
            forall|l4i: L4Index| #![trigger krnl.pt_mp.spec_index(pagetable).view().spec_held_l4(l4i)]
                hv.kernel_l4_end <= l4i && pei_valid(l4i) ==> krnl.pt_mp.spec_index(pagetable).view().spec_held_l4(l4i) == hv.spec_held_l4(l4i) && krnl.pt_mp.spec_index(pagetable).view().spec_resolve_mapping_l4(l4i) == hv.spec_resolve_mapping_l4(l4i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger krnl.pt_mp.spec_index(pagetable).view().spec_held_l3(l4i, l3i)]
                hv.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> krnl.pt_mp.spec_index(pagetable).view().spec_held_l3(l4i, l3i) == hv.spec_held_l3(l4i, l3i),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pagetable_window_lock_map().dom().is_empty(),
            forall|v: VAddr| #![trigger entry.mapping_4k().dom().contains(v)] entry.mapping_4k().dom().contains(v) ==> entry.mapping_4k().spec_index(v).present,
            forall|v: VAddr| #![trigger entry.mapping_2m().dom().contains(v)] entry.mapping_2m().dom().contains(v) ==> entry.mapping_2m().spec_index(v).present,
            range.wf(),
            i <= range.len,
            forall|j: int| #![trigger range.view()[j]] 0 <= j < i ==> !whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_1g().dom().contains(range.view()[j]),
            forall|j: int| #![trigger range.view()[j]] i <= j < range.len ==> {
                &&& whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_1g().dom().contains(range.view()[j])
                &&& !whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_1g().spec_index(range.view()[j]).present
            },
            forall|v: VAddr| #![trigger whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_1g().dom().contains(v)]
                whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_1g().dom().contains(v) && !range.view().contains(v)
                ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_1g().spec_index(v).present,
        decreases range.len - i,
    {
        let va = range.index(i);
        unmap_1g_reclaim_leaf(krnl, pagetable, va, thrd_ptr, cpu_id, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), thread_perm, pagetable_perm);
        i = i + 1;
    }
    let ghost refund_before = steps.view();
    let ghost refund_progress = krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view();
    let ghost refund_k = *krnl;
    let ghost refund_lctx = *lctx;
    proof { process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr); }
    refund_unmap_1g_quota(krnl, thrd_ptr, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), thread_perm);
    proof {
        assert(krnl.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_1g.view() =~= old(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_1g.view()) by { thread_perms_wf_at(krnl.thrd_mp, thrd_ptr); };
        unmap_1g_range_steps_from_refund(&*steps, refund_before, start, cpu_id, thrd_ptr, prc_ptr, ctn_ptr, refund_progress);
        assert(refund_lctx.pagetable_lock_map().dom().contains(pagetable));
        assert(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable) == whole_pagetable(refund_k.pt_mp, refund_k.pt_lower.view(), pagetable));
        assert(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k() == entry.mapping_4k() && whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_2m() == entry.mapping_2m());
    }
    proof { broadcast use PageTableHigher::spec_resolve_mapping_l4_some_implies_spec_held_l4_eq, PageTableHigher::spec_resolve_mapping_l3_some_implies_spec_held_l3_eq; }
}

/// Reclaim the hidden, flushed 1G leaf `va` of the write-held page table `pagetable`: read the page it names, reclaim it, and close the unrecorded section, which leaves the user view unchanged.
fn unmap_1g_reclaim_leaf(
    krnl: &mut KernelK, pagetable: RwLockPageTableRoot, va: VAddr, thrd_ptr: RwLockThreadPtr, cpu_id: CpuId, indirect: &mut [usize; MAX_CONTAINER_TREE_DEPTH], direct: &mut usize,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, thread_perm: Tracked<&LockPerm>, pagetable_perm: Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).page_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        old(steps).snapshot_k() == *old(krnl),
        index_valid(NUM_CPUS, cpu_id),
        old(lctx).cpu_id() == cpu_id,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable,
        *old(direct) == old(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_1g.view(),
        forall|d: int| #![trigger old(indirect)[d]] 0 <= d < old(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth
            ==> old(indirect)[d] == old(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_1g.view().spec_index(d),
        old(krnl).pt_mp.dom().contains(pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
        spec_va_1g_valid(va),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g().dom().contains(va),
        !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g().spec_index(va).present,
    ensures
        final(steps).view() == old(steps).view(),
        final(steps).snapshot_k() == *final(krnl),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        final(krnl).cpu_op.view().view()[cpu_id as int] == old(krnl).cpu_op.view().view()[cpu_id as int],
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        held_locks_order_below(final(krnl), final(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        final(krnl).thrd_mp.dom().contains(thrd_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { direct_free_quota_pending_1g: final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_1g,
            indirect_free_quota_pending_1g: final(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_1g, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
        *final(direct) == final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_1g.view(),
        forall|d: int| #![trigger final(indirect)[d]] 0 <= d < final(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth
            ==> final(indirect)[d] == final(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_1g.view().spec_index(d),
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        ({
            let old_c = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            let new_c = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable);
            &&& new_c.lower == old_c.lower
            &&& new_c.higher == (PageTableHigher { l3_tables: new_c.higher.l3_tables, mapping_1g: new_c.higher.mapping_1g, ..old_c.higher })
            &&& new_c.mapping_1g() == old_c.mapping_1g().remove(va)
            &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.spec_held_l3(l4i, l3i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> new_c.spec_held_l3(l4i, l3i) == old_c.spec_held_l3(l4i, l3i)
        }),
{
    let l4i = v2l4index(va);
    let l3i = v2l3index(va);
    proof {
        spec_va_1g_valid_index_roundtrip(va); krnl.default_pagetable_wf_at(pagetable);
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
        krnl.pt_mp.spec_index(pagetable).view().wf_mapping_1g_at(l4i, l3i);
    }
    let table = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), pagetable_perm);
    let l4_entry = table.get_entry_l4(l4i).unwrap();
    let l3_entry = table.get_entry_1g_l3(l4i, l3i, &l4_entry).unwrap();
    let pg_ptr = l3_entry.addr;
    proof {
        let ghost c = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        c.higher.spec_held_l4_resolves_implies_spec_held_1g_l3_eq_resolve(l4i, l3i);
        mapped_1g_page_pagetable_wf_held_leaf_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pagetable, l4i, l3i);
        mapped_1g_page_pagetable_wf_page_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, page_ptr2page_index(pg_ptr), pagetable, va);
        page_index_valid_imply_page_ptr_valid(); krnl.thrd_mp.typed_lock_map_aligned_held_in_dom(lctx.thread_lock_map(), lctx.thread_id());
    }
    reclaim_held_1g_page(krnl, pagetable, va, pg_ptr, thrd_ptr, indirect, direct, Tracked(&mut *lctx), pagetable_perm, thread_perm);
    proof {
        kernel_restored_locks_implies_u_eq(&steps.snapshot_k(), &*krnl, cpu_id, None, None, Some(thrd_ptr), None, Some(pagetable));
        krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
    }
}
} // verus!
