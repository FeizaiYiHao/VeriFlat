use vstd::prelude::*;
use crate::*;
use super::syscall_kill_process_spec::*;
use super::syscall_kill_process_trace::*;
use super::syscall_kill_process_walk::KillScope;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_walk::kill_scope_progress;
use super::syscall_kill_process_reclaim_scoped::{kill_reclaim_held_4k_page_scoped, kill_reclaim_unmapped_iommu_4k_page_scoped};
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_reclaim_spec::*;
pub(crate) use super::syscall_kill_process_reclaim_zombify::*;
#[cfg(feature = "split-crates")]
use veriflat_map_4k::map_4k::hide_user_l4_entries::hide_user_l4_entries;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::map_4k::hide_user_l4_entries::hide_user_l4_entries;
#[cfg(feature = "split-crates")]
use veriflat_map_4k::map_4k::reclaim_held_4k_leaves::reclaim_held_4k_leaves;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::map_4k::reclaim_held_4k_leaves::reclaim_held_4k_leaves;

verus! {
/// Hide every user root entry of the target's write-locked page table, which lists every cpu stale, each root in its own
/// step; the lower half, the window locks, and every held entry under the roots stay.
pub(crate) fn kill_reclaim_hide_roots(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, pagetable: RwLockPageTableRoot,
    iommu_table: Option<RwLockPageTableRoot>, Tracked(pagetable_perm): Tracked<&LockPerm>, Tracked(iommu_perm): Tracked<&Option<LockPerm>>, Ghost(entry_pt): Ghost<WholePageTable<PT_TYPE>>,
    Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        kill_reclaim_state(*old(krnl), *old(lctx), cpu_id, scope, prc_ptr, thrd_ptr, chain, KillStage::Reclaim { flushed: false }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
            iommu_table, *pagetable_perm, *iommu_perm),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        target == chain[chain.len() - 1],
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower == entry_pt.lower,
        old(krnl).pt_mp.spec_index(pagetable).view() == (PageTableHigher { table_stale_cpus: old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus, ..entry_pt.higher }),
        old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::range(0usize, NUM_CPUS),
        entry_pt.kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
        entry_pt.lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        forall|p: PageMapPtr, i: L2Index| #![trigger entry_pt.lower.l2_owner(p, i)] entry_pt.lower.l2_perms.dom().contains(p) && pei_valid(i) ==> entry_pt.lower.l2_owner(p, i) is None,
        iommu_table is Some ==> old(krnl).it_mp.spec_index(iommu_table->Some_0).view().leaves_present() && old(krnl).it_mp.spec_index(iommu_table->Some_0).view().kernel_l4_end == 0 && old(krnl).it_mp.spec_index(iommu_table->Some_0).view().did is None,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_reclaim_state(*final(krnl), *final(lctx), cpu_id, scope, prc_ptr, thrd_ptr, chain, KillStage::Reclaim { flushed: false }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
            iommu_table, *pagetable_perm, *iommu_perm),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_1g().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.pagetable_window_locks.dom() =~= Set::<WindowVa>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
        final(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::range(0usize, NUM_CPUS),
        forall|l4i: L4Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i) is None,
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.l2_perms == entry_pt.lower.l2_perms,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i)] #![trigger entry_pt.spec_held_2m_l2(l4i, l3i, l2i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i) == entry_pt.spec_held_2m_l2(l4i, l3i, l2i),
        iommu_table is Some ==> final(krnl).it_mp.spec_index(iommu_table->Some_0).view().leaves_present() && final(krnl).it_mp.spec_index(iommu_table->Some_0).view().kernel_l4_end == 0 && final(krnl).it_mp.spec_index(iommu_table->Some_0).view().did is None,
        final(krnl).prc_mp.spec_index(prc_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(prc_ptr).view_ghost().subtree_set,
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
            &&& final(krnl).ctn_mp.dom().contains(c)
            &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
            &&& final(krnl).ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
            &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes
            &&& final(krnl).ctn_mp.spec_index(c).view().children == old(krnl).ctn_mp.spec_index(c).view().children
        },
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view(),
{
    proof { assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); }; }
    let ghost hide_before = steps.view();
    let ghost hide_k = *krnl;
    let ghost hide_lctx = *lctx;
    let Ghost(hidden) = hide_user_l4_entries(krnl, pagetable, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(pagetable_perm));
    proof {
        hidden_root_steps_implies_kill_trace(steps.view(), hide_before, start, pre, cpu_id, ctx, hide_k, hide_lctx, prc_ptr, thrd_ptr, target, scope, pagetable, iommu_table, hidden,
            hidden.len() as int);
        reveal(kernel_steps_prefix_unchanged);
    }
}

/// Flush the target's PCID from every cpu that publishes it and drop each cpu from the stale-CPU record of the target's
/// page table, then record the flush.
pub(crate) fn kill_reclaim_flush(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, pagetable: RwLockPageTableRoot,
    iommu_table: Option<RwLockPageTableRoot>, Tracked(pagetable_perm): Tracked<&LockPerm>, Tracked(iommu_perm): Tracked<&Option<LockPerm>>, Ghost(entry_pt): Ghost<WholePageTable<PT_TYPE>>,
    cr3: PageTableRoot, pcid: Pcid, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        kill_reclaim_state(*old(krnl), *old(lctx), cpu_id, scope, prc_ptr, thrd_ptr, chain, KillStage::Reclaim { flushed: false }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
            iommu_table, *pagetable_perm, *iommu_perm),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        target == chain[chain.len() - 1],
        old(krnl).prc_mp.spec_index(target).view_rodata().view().cr3 == cr3,
        old(krnl).prc_mp.spec_index(target).view_rodata().view().pcid == pcid,
        old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::range(0usize, NUM_CPUS),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.pagetable_window_locks.dom() =~= Set::<WindowVa>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_perms == entry_pt.lower.l2_perms,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i)] #![trigger entry_pt.spec_held_2m_l2(l4i, l3i, l2i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i) == entry_pt.spec_held_2m_l2(l4i, l3i, l2i),
        iommu_table is Some ==> old(krnl).it_mp.spec_index(iommu_table->Some_0).view().leaves_present() && old(krnl).it_mp.spec_index(iommu_table->Some_0).view().kernel_l4_end == 0 && old(krnl).it_mp.spec_index(iommu_table->Some_0).view().did is None,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_reclaim_state(*final(krnl), *final(lctx), cpu_id, scope, prc_ptr, thrd_ptr, chain, KillStage::Reclaim { flushed: true }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
            iommu_table, *pagetable_perm, *iommu_perm),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        final(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_1g().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.pagetable_window_locks.dom() =~= Set::<WindowVa>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
        forall|l4i: L4Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i)]
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.l2_perms == entry_pt.lower.l2_perms,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i)] #![trigger entry_pt.spec_held_2m_l2(l4i, l3i, l2i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i) == entry_pt.spec_held_2m_l2(l4i, l3i, l2i),
        iommu_table is Some ==> final(krnl).it_mp.spec_index(iommu_table->Some_0).view().leaves_present() && final(krnl).it_mp.spec_index(iommu_table->Some_0).view().kernel_l4_end == 0 && final(krnl).it_mp.spec_index(iommu_table->Some_0).view().did is None,
        final(krnl).prc_mp.spec_index(prc_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(prc_ptr).view_ghost().subtree_set,
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
            &&& final(krnl).ctn_mp.dom().contains(c)
            &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
            &&& final(krnl).ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
            &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes
            &&& final(krnl).ctn_mp.spec_index(c).view().children == old(krnl).ctn_mp.spec_index(c).view().children
        },
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view(),
{
    hide(Set::is_empty);
    proof {
        pagetable_perms_wf_at(krnl.pt_mp, pagetable); process_perms_wf_at(krnl.prc_mp, target);
        assert({
            &&& krnl.pt_mp.spec_index(pagetable).view().cr3 == cr3
            &&& krnl.pt_mp.spec_index(pagetable).view().pcid == Some(pcid)
            &&& page_ptr_valid(cr3)
            &&& pcid_valid(pcid)
            &&& pcid != KERNEL_DEFAULT_PCID
        }) by {
            process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, target); process_pcid_allocator_wf_process_at(krnl.ctn_mp, krnl.prc_mp, krnl.pcid_allc_mp, target);
            krnl.pt_mp.spec_index(pagetable).view().table_pages_wf_cr3_at();
        };
    }
    let mut c: usize = 0;
    proof { held_kernel_objects_unchanged_reflexive(&*krnl, &*lctx); }
    while c < NUM_CPUS
        invariant
            krnl.cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
            krnl.cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
            krnl.cpu_arr.spec_index(cpu_id).view().view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view(),
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            krnl.prc_mp.spec_index(prc_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(prc_ptr).view_ghost().subtree_set,
            forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
                &&& krnl.ctn_mp.dom().contains(c)
                &&& krnl.ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
                &&& krnl.ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
                &&& krnl.ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
                &&& krnl.ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
                &&& krnl.ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
                &&& krnl.ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes
                &&& krnl.ctn_mp.spec_index(c).view().children == old(krnl).ctn_mp.spec_index(c).view().children
            },
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.kernel_view_locking_state() is Acquire,
            steps.snapshot_k() == *krnl,
            0 <= start <= old(steps).view().len() <= steps.view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            kill_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, ctx),
            kill_reclaim_state(*krnl, *lctx, cpu_id, scope, prc_ptr, thrd_ptr, chain, KillStage::Reclaim { flushed: false }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
                iommu_table, *pagetable_perm, *iommu_perm),
            target == chain[chain.len() - 1],
            krnl.thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
            krnl.pt_mp.spec_index(pagetable).view() == (PageTableHigher { table_stale_cpus: krnl.pt_mp.spec_index(pagetable).view().table_stale_cpus, ..old(krnl).pt_mp.spec_index(pagetable).view() }),
            krnl.pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::range(c, NUM_CPUS),
            whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower,
            whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom() =~= Set::<VAddr>::empty(),
            iommu_table is Some ==> krnl.it_mp.spec_index(iommu_table->Some_0).view().leaves_present() && krnl.it_mp.spec_index(iommu_table->Some_0).view().kernel_l4_end == 0 && krnl.it_mp.spec_index(iommu_table->Some_0).view().did is None,
            c <= NUM_CPUS,
            krnl.pt_mp.spec_index(pagetable).view().cr3 == cr3,
            krnl.pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
            page_ptr_valid(cr3),
            pcid_valid(pcid),
            pcid != KERNEL_DEFAULT_PCID,
            krnl.prc_mp.spec_index(target).view_rodata().view().pcid == pcid,
        decreases NUM_CPUS - c,
    {
        let ghost iter_k = *krnl;
        let ghost iter_lctx = *lctx;
        let ghost iter_before = steps.view();
        let flushed = kill_reclaim_flush_cpu_tlb(krnl, Tracked(&mut *lctx), c, cpu_id, pagetable, cr3, pcid, Tracked(cpu_perm), Tracked(pagetable_perm));
        proof {
            let tlb_k = *krnl;
            kill_tlb_flush_step_from_k(&iter_k, &tlb_k, c, pcid, flushed);
            assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
            if tlb_k.cpu_tlb.view() == iter_k.cpu_tlb.view() { krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps); }
            else { krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps); }
            kill_step_pre_from_k(&iter_k, &iter_lctx, cpu_id, prc_ptr, thrd_ptr, target, KillStage::Reclaim { flushed: false }, scope);
            kill_reclaim_pre_from_k(&iter_k, &iter_lctx, cpu_id, thrd_ptr, target, KillStage::Reclaim { flushed: false }, pagetable, iommu_table); kill_user_4k_unmapped_pre_from_k(&iter_k, target);
            kill_trace_push_tlb_flush(&*steps, iter_before, start, pre, kernel_k_to_kernel_u(iter_k), kernel_k_to_kernel_u(tlb_k), cpu_id, ctx, pcid);
        }
        c = c + 1;
    }
    assert(Set::range(c, NUM_CPUS) =~= Set::<CpuId>::empty());
    let ghost flushed_k = *krnl;
    let ghost flushed_lctx = *lctx;
    let ghost flushed_before = steps.view();
    krnl.set_thread_syscall_progress(thrd_ptr, Ghost(kill_scope_progress(scope, target, KillStage::Reclaim { flushed: true })), Tracked(&*lctx), Tracked(thread_perm));
    proof {
        let flushed_pre = kernel_k_to_kernel_u(flushed_k);
        let flushed_post = kernel_k_to_kernel_u(*krnl);
        kill_step_pre_from_k(&flushed_k, &flushed_lctx, cpu_id, prc_ptr, thrd_ptr, target, KillStage::Reclaim { flushed: false }, scope);
        kill_reclaim_pre_from_k(&flushed_k, &flushed_lctx, cpu_id, thrd_ptr, target, KillStage::Reclaim { flushed: false }, pagetable, iommu_table); kill_user_4k_unmapped_pre_from_k(&flushed_k, target);
        kernel_thread_syscall_progress_changed_implies_u_step(&flushed_k, &*krnl, thrd_ptr);
        kill_flushed_step_from_u(flushed_pre, flushed_post, cpu_id, thrd_ptr, target, scope);
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thrd_ptr);
        kill_trace_push(&*steps, flushed_before, start, pre, flushed_pre, flushed_post, cpu_id, ctx);
        pagetable_perms_wf_at(krnl.pt_mp, pagetable);
    }
}

/// Flush `pcid` on cpu `c` under its needflush lock and drop `c` from the stale-CPU record of the write-held page table
/// `pagetable` with `cr3` and `pcid`; returns whether the hardware cr3/pcid word of `c` names the table. What `c` may
/// cache after a flush is stated in the state before the record drop, whose tables differ only in that record.
pub(crate) fn kill_reclaim_flush_cpu_tlb(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, c: usize, cpu_id: CpuId, pagetable: RwLockPageTableRoot, cr3: PageTableRoot, pcid: Pcid,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(pagetable_perm): Tracked<&LockPerm>,
) -> (flushed: bool)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        c < NUM_CPUS,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        forall|held: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held)] old(lctx).cpu_lock_map().dom().contains(held) ==> !(old(krnl).cpu_arr.spec_index(held).view().view().view().state is Off),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_perm.state() is WriteLock,
        cpu_perm.thread_id() == old(lctx).thread_id(),
        cpu_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).pt_mp.dom().contains(pagetable),
        old(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        page_ptr_valid(cr3),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.state() is WriteLock,
        pagetable_perm.thread_id() == old(lctx).thread_id(),
        pagetable_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::range(c, NUM_CPUS),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, cpu_tlb: final(krnl).cpu_tlb, pcid_needflush: final(krnl).pcid_needflush, pt_mp: final(krnl).pt_mp, ..*old(krnl) }),
        forall|cpu: CpuId| #![trigger final(krnl).cpu_arr.spec_index(cpu)] index_valid(NUM_CPUS, cpu) ==> final(krnl).cpu_arr.spec_index(cpu).value.locking_thread() == old(krnl).cpu_arr.spec_index(cpu).value.locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).pt_mp.dom() == old(krnl).pt_mp.dom(),
        forall|pt: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(pt)] old(krnl).pt_mp.dom().contains(pt) ==> {
            &&& final(krnl).pt_mp.spec_index(pt).view() == (PageTableHigher { table_stale_cpus: final(krnl).pt_mp.spec_index(pt).view().table_stale_cpus, ..old(krnl).pt_mp.spec_index(pt).view() })
            &&& final(krnl).pt_mp.spec_index(pt).locking_thread() == old(krnl).pt_mp.spec_index(pt).locking_thread()
            &&& final(krnl).pt_mp.spec_index(pt).being_killed() == old(krnl).pt_mp.spec_index(pt).being_killed()
            &&& final(krnl).pt_mp.lock_id_by_key(pt) == old(krnl).pt_mp.lock_id_by_key(pt)
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt).mapping_4k() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt).mapping_4k()
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt).mapping_2m() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt).mapping_2m()
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt).mapping_1g() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt).mapping_1g()
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt).lower.pagetable_window_locks == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt).lower.pagetable_window_locks
        },
        final(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::range((c + 1) as usize, NUM_CPUS),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        final(krnl).cpu_tlb.view() == if flushed { old(krnl).cpu_tlb.view().insert((c, pcid), final(krnl).cpu_tlb.spec_index((c, pcid))) } else { old(krnl).cpu_tlb.view() },
        (KernelK { pt_mp: old(krnl).pt_mp, pt_lower: old(krnl).pt_lower, ..*final(krnl) }).inv(),
        flushed ==> cpu_tlb_within_may_cache(KernelK { pt_mp: old(krnl).pt_mp, pt_lower: old(krnl).pt_lower, ..*final(krnl) }, c, pcid, final(krnl).cpu_tlb.spec_index((c, pcid)),
            final(krnl).cpu_tlb.structure_cache((c, pcid))),
{
    hide(typed_lock_maps_aligned);
    let Tracked(needflush_perm) = krnl.wlock_pcid_needflush(c, pcid, Tracked(&mut *lctx));
    let hw_cr3_pcid = mark_pcid_needflush_and_load(krnl, c, pcid, Tracked(&mut *lctx), Tracked(&needflush_perm));
    let flushed = hw_cr3_pcid.0 == cr3 && hw_cr3_pcid.1 == pcid;
    if flushed {
        if c == cpu_id {
            flush_local_pcid_and_clear(krnl, c, pcid, cr3, Tracked(&*lctx), Tracked(&needflush_perm), Tracked(cpu_perm));
        } else {
            flush_remote_pcid_and_clear(krnl, c, pcid, Tracked(&*lctx), Tracked(&needflush_perm));
        }
    }
    let ghost flush_k = *krnl;
    assert({
        let dirty_entry = krnl.cpu_arr.spec_index(c).view().view().tlb_dirty_bitmap().spec_index(pcid);
        let exempt = krnl.pcid_needflush.spec_index(c, pcid).view().needflush && krnl.cpu_arr.spec_index(c).view().view().view().current_pcid != pcid;
        let table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        &&& krnl.cpu_tlb.spec_index((c, pcid)).is_empty() || exempt || (dirty_entry is Some && dirty_entry.unwrap().pagetable_ptr != pagetable) || single_cpu_single_pcid_tlb_subset_of_present_pagetable(krnl.cpu_tlb.spec_index((c, pcid)), table)
        &&& krnl.cpu_tlb.structure_cache((c, pcid)).is_empty() || exempt || (dirty_entry is Some && dirty_entry.unwrap().pagetable_ptr != pagetable) || single_structure_cache_subset_of_present_pagetable(krnl.cpu_tlb.structure_cache((c, pcid)), table)
    }) by {
        cpu_current_pcid_pagetable_match_at(krnl.cpu_arr, krnl.dflt_pt.view(), krnl.prc_mp, krnl.pt_mp, c, pcid, pagetable);
        cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), c); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, c);
        process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, krnl.cpu_arr.spec_index(c).view().view().view().current_process.unwrap());
    };
    krnl.wunlock_pcid_needflush(c, pcid, Tracked(&mut *lctx), Tracked(needflush_perm));
    proof {
        assert(lctx.pcid_needflush_lock_map() =~= old(lctx).pcid_needflush_lock_map());
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged); };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    assert(Set::range(c, NUM_CPUS).remove(c) =~= Set::range((c + 1) as usize, NUM_CPUS));
    krnl.replace_table_stale_cpus(pagetable, Ghost(TableStaleUpdate::RemoveCpu { cpu_id: c }), Tracked(&*lctx), Tracked(pagetable_perm));
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        let cpu = flush_k.cpu_arr.spec_index(c).view().view().view();
        if cpu.current_pcid == pcid && cpu.current_pagetable is Some {
            assert(flush_k.pt_mp.dom().contains(cpu.current_pagetable->Some_0)) by {
                cpu_array_wf_at(flush_k.cpu_arr, flush_k.dflt_pt.view(), c); process_cpu_wf_at(flush_k.prc_mp, flush_k.cpu_arr, c);
                process_pagetable_match_process_at(flush_k.prc_mp, flush_k.pt_mp, cpu.current_process.unwrap());
            };
        }
    }
    flushed
}

/// Reclaim the page of every held 4K leaf of the target's hidden page table, clearing each leaf. In a process kill
/// (`same`), whose target shares the killer's container, the quota of each freed page accumulates as the killer's pending
/// refund, refunded to the killer's container chain at the end; otherwise each freed page credits its owner's quota in its
/// own step. The table holds no 2M leaf, since the target maps none.
pub(crate) fn kill_reclaim_held_leaves(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, pagetable: RwLockPageTableRoot,
    iommu_table: Option<RwLockPageTableRoot>, Tracked(pagetable_perm): Tracked<&LockPerm>, Tracked(iommu_perm): Tracked<&Option<LockPerm>>, Ghost(entry_pt): Ghost<WholePageTable<PT_TYPE>>,
    same: bool, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        same == (scope is Subtree),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        kill_reclaim_state(*old(krnl), *old(lctx), cpu_id, scope, prc_ptr, thrd_ptr, chain, KillStage::Reclaim { flushed: true }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
            iommu_table, *pagetable_perm, *iommu_perm),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        target == chain[chain.len() - 1],
        old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.pagetable_window_locks.dom() =~= Set::<WindowVa>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
        forall|l4i: L4Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i) is None,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_perms == entry_pt.lower.l2_perms,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i)] #![trigger entry_pt.spec_held_2m_l2(l4i, l3i, l2i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i) == entry_pt.spec_held_2m_l2(l4i, l3i, l2i),
        entry_pt.lower.hidden_l1_tables_in_locked_windows(),
        forall|p: PageMapPtr, i: L2Index| #![trigger entry_pt.lower.l2_owner(p, i)] entry_pt.lower.l2_perms.dom().contains(p) && pei_valid(i) ==> entry_pt.lower.l2_owner(p, i) is None,
        entry_pt.kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
        entry_pt.mapping_2m().dom() =~= Set::<VAddr>::empty(),
        entry_pt.wf_mapping_2m(),
        forall|l4i: L4Index, l3i: L3Index| #![trigger entry_pt.higher.spec_held_l3(l4i, l3i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && entry_pt.higher.spec_held_l3(l4i, l3i) is Some ==> entry_pt.higher.spec_resolve_mapping_l3(l4i, l3i) is Some,
        iommu_table is Some ==> old(krnl).it_mp.spec_index(iommu_table->Some_0).view().leaves_present() && old(krnl).it_mp.spec_index(iommu_table->Some_0).view().kernel_l4_end == 0 && old(krnl).it_mp.spec_index(iommu_table->Some_0).view().did is None,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_reclaim_state(*final(krnl), *final(lctx), cpu_id, scope, prc_ptr, thrd_ptr, chain, KillStage::Reclaim { flushed: true }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
            iommu_table, *pagetable_perm, *iommu_perm),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m().dom() =~= Set::<VAddr>::empty(),
        final(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.hidden_l1_tables_in_locked_windows(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_1g().dom() =~= Set::<VAddr>::empty(),
        forall|l4i: L4Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i) is None,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_4k_l1(l4i, l3i, l2i, l1i) is None,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i)] #![trigger entry_pt.spec_held_2m_l2(l4i, l3i, l2i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i) == entry_pt.spec_held_2m_l2(l4i, l3i, l2i),
        iommu_table is Some ==> final(krnl).it_mp.spec_index(iommu_table->Some_0).view().leaves_present() && final(krnl).it_mp.spec_index(iommu_table->Some_0).view().kernel_l4_end == 0 && final(krnl).it_mp.spec_index(iommu_table->Some_0).view().did is None,
        final(krnl).prc_mp.spec_index(prc_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(prc_ptr).view_ghost().subtree_set,
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
            &&& final(krnl).ctn_mp.dom().contains(c)
            &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
            &&& final(krnl).ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
            &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes
            &&& final(krnl).ctn_mp.spec_index(c).view().children == old(krnl).ctn_mp.spec_index(c).view().children
        },
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view(),
{
    hide(LockedMap::lock_id_by_key);
    proof {
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable); thread_perms_wf_at(krnl.thrd_mp, thrd_ptr);
        assert(!thread_is_dangling(krnl.thrd_mp.spec_index(thrd_ptr)) && krnl.thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id: cpu_id })) by { thread_cpu_wf_cpu_at(krnl.thrd_mp, krnl.cpu_arr, cpu_id); };
        assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
        held_kernel_objects_unchanged_reflexive(&*krnl, &*lctx);
    }
    if same {
        let ghost entry_thread = krnl.thrd_mp.spec_index(thrd_ptr).view();
        proof {
            assert(krnl.prc_mp.spec_index(target).view_rodata().view().owning_container == entry_thread.owning_container) by { process_thread_wf_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); };
            assert(entry_thread.container_depth <= MAX_CONTAINER_TREE_DEPTH) by { container_thread_wf_at(krnl.ctn_mp, krnl.thrd_mp, thrd_ptr); container_perms_wf_at(krnl.ctn_mp, entry_thread.owning_container); };
            process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, target);
        }
        let mut indirect = [0usize; MAX_CONTAINER_TREE_DEPTH];
        let mut direct = 0usize;
        let stopped_2m = reclaim_held_4k_leaves(krnl, pagetable, thrd_ptr, cpu_id, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(pagetable_perm),
            Tracked(thread_perm));
        proof {
            if let Some(s) = stopped_2m { entry_pt.higher.spec_resolve_mapping_l3_some_implies_spec_held_l3_eq(s.0, s.1); entry_pt.wf_mapping_2m_at(s.0, s.1, s.2); }
            assert(stopped_2m is None);
        }
        let ghost reclaimed_k = *krnl;
        proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
        let ghost refund_k = *krnl;
        let ghost refund_lctx = *lctx;
        let ghost refund_before = steps.view();
        proof {
            kill_step_pre_from_k(&refund_k, &refund_lctx, cpu_id, prc_ptr, thrd_ptr, target, KillStage::Reclaim { flushed: true }, scope); kill_refund_pre_from_k(&refund_k, target, entry_thread.owning_container);
            assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
        }
        refund_unmap_4k_quota(krnl, thrd_ptr, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_perm));
        proof {
            vstd::assert_seqs_equal!(krnl.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k.view(), entry_thread.indirect_free_quota_pending_4k.view());
            kill_trace_from_refund(&*steps, refund_before, start, pre, kernel_k_to_kernel_u(refund_k), cpu_id, ctx, prc_ptr, thrd_ptr, target, KillStage::Reclaim { flushed: true },
                entry_thread.owning_container, scope);
            assert(refund_lctx.pagetable_lock_map().dom().contains(pagetable));
            assert(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable) == whole_pagetable(reclaimed_k.pt_mp, reclaimed_k.pt_lower.view(), pagetable));
        }
    } else {
        let mut cursor: (L4Index, L3Index, L2Index, L1Index) = (KERNEL_MEM_END_L4INDEX, 0, 0, 0);
        let mut found = pagetable_map_next_held_leaf_from(&krnl.pt_mp, Tracked(krnl.pt_lower.borrow()), pagetable, cursor, Tracked(&*lctx), Tracked(pagetable_perm));
        while found.is_some()
            invariant
                krnl.cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
                krnl.cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
                krnl.cpu_arr.spec_index(cpu_id).view().view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view(),
                lctx.container_lock_map() == old(lctx).container_lock_map(),
                krnl.prc_mp.spec_index(prc_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(prc_ptr).view_ghost().subtree_set,
                forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
                    &&& krnl.ctn_mp.dom().contains(c)
                    &&& krnl.ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
                    &&& krnl.ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
                    &&& krnl.ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
                    &&& krnl.ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
                    &&& krnl.ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
                    &&& krnl.ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes
                    &&& krnl.ctn_mp.spec_index(c).view().children == old(krnl).ctn_mp.spec_index(c).view().children
                },
                krnl.inv(),
                typed_lock_maps_aligned(krnl, lctx),
                lctx.kernel_view_locking_state() is Acquire,
                steps.snapshot_k() == *krnl,
                0 <= start <= old(steps).view().len() <= steps.view().len(),
                forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
                kill_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, ctx),
                kill_reclaim_state(*krnl, *lctx, cpu_id, scope, prc_ptr, thrd_ptr, chain, KillStage::Reclaim { flushed: true }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
                    iommu_table, *pagetable_perm, *iommu_perm),
                target == chain[chain.len() - 1],
                krnl.thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
                !same,
                iommu_table is Some ==> krnl.it_mp.spec_index(iommu_table->Some_0).view().leaves_present() && krnl.it_mp.spec_index(iommu_table->Some_0).view().kernel_l4_end == 0 && krnl.it_mp.spec_index(iommu_table->Some_0).view().did is None,
                KERNEL_MEM_END_L4INDEX <= cursor.0,
                pei_valid(cursor.0),
                pei_valid(cursor.1),
                pei_valid(cursor.2),
                cursor.3 <= 512,
                krnl.pt_mp.spec_index(pagetable).view() == old(krnl).pt_mp.spec_index(pagetable).view(),
                krnl.pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
                whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
                forall|l4i: L4Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i)]
                    KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i) is None,
                entry_pt.kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
                entry_pt.mapping_2m().dom() =~= Set::<VAddr>::empty(),
                entry_pt.wf_mapping_2m(),
                forall|l4i: L4Index, l3i: L3Index| #![trigger entry_pt.higher.spec_held_l3(l4i, l3i)]
                    KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && entry_pt.higher.spec_held_l3(l4i, l3i) is Some ==> entry_pt.higher.spec_resolve_mapping_l3(l4i, l3i) is Some,
                whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k(),
                whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_2m() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m(),
                whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.pagetable_window_locks == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.pagetable_window_locks,
                whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.window_stale_cpus == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus,
                whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.hidden_l1_tables_in_locked_windows(),
                forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.l2_owner(p, i)]
                    whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.l2_perms.dom().contains(p) && pei_valid(i) ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.l2_owner(p, i) is None,
                forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i)] #![trigger entry_pt.spec_held_2m_l2(l4i, l3i, l2i)]
                    KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i) == entry_pt.spec_held_2m_l2(l4i, l3i, l2i),
                found is Some ==> {
                    let (n, is_2m, leaf) = found->Some_0;
                    &&& KERNEL_MEM_END_L4INDEX <= n.0
                    &&& pei_valid(n.0)
                    &&& pei_valid(n.1)
                    &&& pei_valid(n.2)
                    &&& pei_valid(n.3)
                    &&& spec_l4_index_path_le(cursor, n)
                    &&& is_2m ==> n.3 == 0 && whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_held_2m_l2(n.0, n.1, n.2) == Some(leaf)
                    &&& !is_2m ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_held_4k_l1(n.0, n.1, n.2, n.3) == Some(leaf)
                },
                forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                    KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (found is None || !spec_l4_index_path_le(found->Some_0.0, (l4i, l3i, l2i, l1i)))
                        ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_held_4k_l1(l4i, l3i, l2i, l1i) is None,
            decreases 512 - cursor.0, 512 - cursor.1, 512 - cursor.2, 513 - cursor.3,
        {
            let (next, is_2m, leaf) = found.unwrap();
            proof {
                if is_2m { entry_pt.higher.spec_resolve_mapping_l3_some_implies_spec_held_l3_eq(next.0, next.1); entry_pt.wf_mapping_2m_at(next.0, next.1, next.2); }
                assert(!is_2m);
            }
            let va = index2va(next);
            let pg_ptr = leaf.addr;
            proof {
                spec_va_4k_index_roundtrip_at(va, next.0, next.1, next.2, next.3);
                assert(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_resolve_mapping_l4(next.0) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(next.0));
                mapped_4k_page_pagetable_wf_held_leaf_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pagetable, next.0, next.1, next.2, next.3);
                mapped_4k_page_pagetable_wf_page_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, page_ptr2page_index(pg_ptr), pagetable, va);
                page_index_valid_imply_page_ptr_valid();
                assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
            }
            kill_reclaim_held_4k_page_scoped(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, thrd_ptr, target, pagetable, va, pg_ptr, Tracked(pagetable_perm),
                Ghost(KillStage::Reclaim { flushed: true }), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
            cursor = (next.0, next.1, next.2, next.3 + 1);
            proof {
                index_path_successor_implies_path_le_drops_only_predecessor(next, cursor); pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable);
                pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
            }
            found = pagetable_map_next_held_leaf_from(&krnl.pt_mp, Tracked(krnl.pt_lower.borrow()), pagetable, cursor, Tracked(&*lctx), Tracked(pagetable_perm));
        }
    }
    proof { pagetable_perms_wf_at(krnl.pt_mp, pagetable); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, target); }
}

/// Remove every 4K leaf of the target's write-locked IOMMU table, which lost its DID when the target's functions were
/// reassigned, so no domain caches it and no IOTLB flush is needed; one step per leaf. In a process kill (`same`), whose
/// target shares the killer's container, each present leaf is removed directly and the quota of the freed pages is refunded
/// to the killer's container chain at the end; otherwise each leaf is hidden in its own step and then unmapped, a freed
/// page crediting its owner's quota in its own step.
pub(crate) fn kill_reclaim_iommu_leaves(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, pagetable: RwLockPageTableRoot,
    iommu_table: RwLockPageTableRoot, Tracked(pagetable_perm): Tracked<&LockPerm>, Tracked(iommu_perm): Tracked<&LockPerm>, Ghost(held_pt): Ghost<WholePageTable<PT_TYPE>>,
    same: bool, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        same == (scope is Subtree),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        kill_reclaim_state(*old(krnl), *old(lctx), cpu_id, scope, prc_ptr, thrd_ptr, chain, KillStage::Reclaim { flushed: true }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
            Some(iommu_table), *pagetable_perm, Some(*iommu_perm)),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        target == chain[chain.len() - 1],
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable) == held_pt,
        old(krnl).it_mp.spec_index(iommu_table).view().leaves_present() && old(krnl).it_mp.spec_index(iommu_table).view().kernel_l4_end == 0,
        old(krnl).it_mp.spec_index(iommu_table).view().did is None,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_reclaim_state(*final(krnl), *final(lctx), cpu_id, scope, prc_ptr, thrd_ptr, chain, KillStage::Reclaim { flushed: true }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
            Some(iommu_table), *pagetable_perm, Some(*iommu_perm)),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable) == held_pt,
        final(krnl).it_mp.spec_index(iommu_table).view().leaves_present(),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger final(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> !final(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
        final(krnl).prc_mp.spec_index(prc_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(prc_ptr).view_ghost().subtree_set,
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
            &&& final(krnl).ctn_mp.dom().contains(c)
            &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
            &&& final(krnl).ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
            &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes
            &&& final(krnl).ctn_mp.spec_index(c).view().children == old(krnl).ctn_mp.spec_index(c).view().children
        },
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
{
    hide(LockCell::being_killed);
    let ghost entry_thread = krnl.thrd_mp.spec_index(thrd_ptr).view();
    proof {
        iommu_table_perms_wf_map(krnl.it_mp);
        iommu_table_perms_wf_at(krnl.it_mp, iommu_table); thread_perms_wf_at(krnl.thrd_mp, thrd_ptr);
        assert(same ==> krnl.prc_mp.spec_index(target).view_rodata().view().owning_container == entry_thread.owning_container) by { process_thread_wf_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); };
        assert(entry_thread.container_depth <= MAX_CONTAINER_TREE_DEPTH) by { container_thread_wf_at(krnl.ctn_mp, krnl.thrd_mp, thrd_ptr); container_perms_wf_at(krnl.ctn_mp, entry_thread.owning_container); };
    }
    let mut indirect = [0usize; MAX_CONTAINER_TREE_DEPTH];
    let mut direct = 0usize;
    let mut cursor: (L4Index, L3Index, L2Index, L1Index) = (0, 0, 0, 0);
    let mut found = krnl.it_mp.borrow_typed(iommu_table, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), Tracked(iommu_perm)).next_mapped_4k_from(cursor);
    proof { held_kernel_objects_unchanged_reflexive(&*krnl, &*lctx); }
    while found.is_some()
        invariant
            krnl.cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
                &&& krnl.ctn_mp.dom().contains(c)
                &&& krnl.ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
                &&& krnl.ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
                &&& krnl.ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
                &&& krnl.ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
                &&& krnl.ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
                &&& krnl.ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes
                &&& krnl.ctn_mp.spec_index(c).view().children == old(krnl).ctn_mp.spec_index(c).view().children
            },
            krnl.prc_mp.spec_index(prc_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(prc_ptr).view_ghost().subtree_set,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.kernel_view_locking_state() is Acquire,
            steps.snapshot_k() == *krnl,
            0 <= start <= old(steps).view().len() <= steps.view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            kill_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, ctx),
            kill_reclaim_state(*krnl, *lctx, cpu_id, scope, prc_ptr, thrd_ptr, chain, KillStage::Reclaim { flushed: true }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
                Some(iommu_table), *pagetable_perm, Some(*iommu_perm)),
            target == chain[chain.len() - 1],
            whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable) == held_pt,
            entry_thread.free_quota_pending_clean(),
            same == (scope is Subtree),
            same ==> krnl.prc_mp.spec_index(target).view_rodata().view().owning_container == entry_thread.owning_container,
            same ==> krnl.thrd_mp.spec_index(thrd_ptr).view() == (Thread {
                direct_free_quota_pending_4k: krnl.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k,
                indirect_free_quota_pending_4k: krnl.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k, ..entry_thread
            }),
            same ==> direct == krnl.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view(),
            same ==> forall|d: int| #![trigger indirect[d]] #![trigger krnl.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d)] 0 <= d < entry_thread.container_depth
                ==> indirect[d] == krnl.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d),
            !same ==> krnl.thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
            krnl.it_mp.spec_index(iommu_table).view().kernel_l4_end == 0,
            krnl.it_mp.spec_index(iommu_table).view().mapping_2m() == old(krnl).it_mp.spec_index(iommu_table).view().mapping_2m(),
            krnl.it_mp.spec_index(iommu_table).view().mapping_1g() == old(krnl).it_mp.spec_index(iommu_table).view().mapping_1g(),
            krnl.it_mp.spec_index(iommu_table).view().did is None,
            pei_valid(cursor.0),
            pei_valid(cursor.1),
            pei_valid(cursor.2),
            cursor.3 <= 512,
            found is Some ==> {
                let next = found->Some_0;
                &&& pei_valid(next.0)
                &&& pei_valid(next.1)
                &&& pei_valid(next.2)
                &&& pei_valid(next.3)
                &&& spec_l4_index_path_le(cursor, next)
                &&& krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va(next))
            },
            forall|va: VAddr| #![trigger krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(va)]
                krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(va) ==> krnl.it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(va).present,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (found is None || !spec_l4_index_path_le(found->Some_0, (l4i, l3i, l2i, l1i))) ==> !krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
        decreases 512 - cursor.0, 512 - cursor.1, 512 - cursor.2, 513 - cursor.3,
    {
        let found_next = found.unwrap();
        let next = (found_next.0, found_next.1, found_next.2, found_next.3);
        let iova = index2va(next);
        proof {
            let (l4i, l3i, l2i, l1i) = next;
            assert(spec_v2l4index(spec_index2va((l4i, l3i, l2i, l1i))) == l4i && spec_v2l3index(spec_index2va((l4i, l3i, l2i, l1i))) == l3i && spec_v2l2index(spec_index2va((l4i, l3i, l2i, l1i))) == l2i
                && spec_v2l1index(spec_index2va((l4i, l3i, l2i, l1i))) == l1i) by (bit_vector) requires l4i < 512, l3i < 512, l2i < 512, l1i < 512;
            assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
        }
        let ghost leaf_before = steps.view();
        if same {
            reclaim_detached_iommu_4k_page(krnl, iommu_table, next, thrd_ptr, cpu_id, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(iommu_perm),
                Tracked(thread_perm));
            proof {
                let snap = steps.snapshot_k();
                let leaf_post = *krnl;
                kernel_iommu_table_4k_mapping_removed_implies_u_step(&snap, &leaf_post, iommu_table, iova, thrd_ptr);
                kill_step_pre_from_k(&leaf_post, &*lctx, cpu_id, prc_ptr, thrd_ptr, target, KillStage::Reclaim { flushed: true }, scope);
                kill_reclaim_pre_from_k(&leaf_post, &*lctx, cpu_id, thrd_ptr, target, KillStage::Reclaim { flushed: true }, pagetable, Some(iommu_table));
                kill_iommu_leaf_step_from_u(kernel_k_to_kernel_u(snap), kernel_k_to_kernel_u(leaf_post), cpu_id, target, iova);
                krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
                kill_trace_push(&*steps, leaf_before, start, pre, kernel_k_to_kernel_u(snap), kernel_k_to_kernel_u(leaf_post), cpu_id, ctx);
            }
        } else {
            let ghost leaf_k = *krnl;
            clear_iommu_4k_mapping_present(krnl, iommu_table, next, Tracked(&mut *lctx), Tracked(iommu_perm));
            proof {
                let leaf_post = *krnl;
                kernel_iommu_table_4k_present_cleared_implies_u_step(&leaf_k, &leaf_post, iommu_table, iova);
                kill_step_pre_from_k(&leaf_post, &*lctx, cpu_id, prc_ptr, thrd_ptr, target, KillStage::Reclaim { flushed: true }, scope);
                kill_reclaim_pre_from_k(&leaf_post, &*lctx, cpu_id, thrd_ptr, target, KillStage::Reclaim { flushed: true }, pagetable, Some(iommu_table));
                kill_iommu_leaf_step_from_u(kernel_k_to_kernel_u(leaf_k), kernel_k_to_kernel_u(leaf_post), cpu_id, target, iova);
                krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
                kill_trace_push(&*steps, leaf_before, start, pre, kernel_k_to_kernel_u(leaf_k), kernel_k_to_kernel_u(leaf_post), cpu_id, ctx);
            }
            kill_reclaim_unmapped_iommu_4k_page_scoped(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, thrd_ptr, target, iommu_table, next, Tracked(iommu_perm),
                Ghost(KillStage::Reclaim { flushed: true }), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
        }
        cursor = (next.0, next.1, next.2, next.3 + 1);
        proof { index_path_successor_implies_path_le_drops_only_predecessor(next, cursor); iommu_table_perms_wf_map(krnl.it_mp); iommu_table_perms_wf_at(krnl.it_mp, iommu_table); process_iommu_table_match_process_at(krnl.prc_mp, krnl.it_mp, target); }
        found = krnl.it_mp.borrow_typed(iommu_table, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), Tracked(iommu_perm)).next_mapped_4k_from(cursor);
    }
    proof { assert(krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom() =~= Set::<VAddr>::empty()) by { iommu_table_perms_wf_at(krnl.it_mp, iommu_table); broadcast use iova_4k_valid_index_roundtrip; }; }
    if same {
        proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
        let ghost refund_k = *krnl;
        let ghost refund_lctx = *lctx;
        let ghost refund_before = steps.view();
        proof {
            kill_step_pre_from_k(&refund_k, &refund_lctx, cpu_id, prc_ptr, thrd_ptr, target, KillStage::Reclaim { flushed: true }, scope); kill_refund_pre_from_k(&refund_k, target, entry_thread.owning_container);
            assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
        }
        refund_unmap_4k_quota(krnl, thrd_ptr, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_perm));
        proof {
            assert(krnl.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k.view() =~= entry_thread.indirect_free_quota_pending_4k.view()) by { thread_perms_wf_at(krnl.thrd_mp, thrd_ptr); };
            kill_trace_from_refund(&*steps, refund_before, start, pre, kernel_k_to_kernel_u(refund_k), cpu_id, ctx, prc_ptr, thrd_ptr, target, KillStage::Reclaim { flushed: true },
                entry_thread.owning_container, scope);
        }
    }
    proof { iommu_table_perms_wf_at(krnl.it_mp, iommu_table); process_iommu_table_match_process_at(krnl.prc_mp, krnl.it_mp, target); }
}
} // verus!
