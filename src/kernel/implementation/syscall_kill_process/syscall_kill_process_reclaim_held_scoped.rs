use vstd::prelude::*;
use crate::*;
use super::syscall_kill_process_spec::*;
use super::syscall_kill_process_walk_spec::KillScope;
use super::syscall_kill_process_reclaim_scoped::kill_reclaim_held_4k_page_scoped;
use super::syscall_kill_process_reclaim_scoped_2m::kill_reclaim_held_2m_page_scoped;
use super::syscall_kill_process_reclaim_scoped_1g::kill_reclaim_held_1g_page_scoped;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_reclaim_spec::*;

verus! {
/// Reclaim the page of every held leaf of the target's hidden page table outside a process kill (`!same`), each freed
/// page crediting its owner's quota in its own step.
pub(crate) fn kill_reclaim_held_leaves_scoped(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, pagetable: RwLockPageTableRoot,
    iommu_table: Option<RwLockPageTableRoot>, Tracked(pagetable_perm): Tracked<&LockPerm>, Tracked(iommu_perm): Tracked<&Option<LockPerm>>, Ghost(entry_pt): Ghost<WholePageTable<PT_TYPE>>,
    same: bool, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        same == (scope is Subtree),
        !same,
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
        entry_pt.lower.hidden_l1_tables_in_locked_windows(),
        forall|p: PageMapPtr, i: L2Index| #![trigger entry_pt.lower.l2_owner(p, i)] entry_pt.lower.l2_perms.dom().contains(p) && pei_valid(i) ==> entry_pt.lower.l2_owner(p, i) is None,
        entry_pt.kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
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
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.pagetable_window_locks.dom() =~= Set::<WindowVa>::empty(),
        final(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.hidden_l1_tables_in_locked_windows(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_1g().dom() =~= Set::<VAddr>::empty(),
        forall|l4i: L4Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i) is None,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_4k_l1(l4i, l3i, l2i, l1i) is None,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i) is None,
        forall|l4i: L4Index, l3i: L3Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_1g_l3(l4i, l3i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_1g_l3(l4i, l3i) is None,
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
    proof {
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable); thread_perms_wf_at(krnl.thrd_mp, thrd_ptr);
        assert(!thread_is_dangling(krnl.thrd_mp.spec_index(thrd_ptr)) && krnl.thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id: cpu_id })) by { thread_cpu_wf_cpu_at(krnl.thrd_mp, krnl.cpu_arr, cpu_id); };
        assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
        held_kernel_objects_unchanged_reflexive(&*krnl, &*lctx);
    }
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
            krnl.pt_mp.spec_index(pagetable).view() == (PageTableHigher { l3_tables: krnl.pt_mp.spec_index(pagetable).view().l3_tables, mapping_1g: krnl.pt_mp.spec_index(pagetable).view().mapping_1g,
                ..old(krnl).pt_mp.spec_index(pagetable).view() }),
            krnl.pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
            whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
            forall|l4i: L4Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i)]
                KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i) is None,
            forall|l4i: L4Index| #![trigger whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i)]
                KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i),
            whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_1g().dom() =~= Set::<VAddr>::empty(),
            whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k(),
            whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_2m() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m(),
            whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.pagetable_window_locks == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.pagetable_window_locks,
            whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.window_stale_cpus == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus,
            whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.hidden_l1_tables_in_locked_windows(),
            forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.l2_owner(p, i)]
                whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.l2_perms.dom().contains(p) && pei_valid(i) ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.l2_owner(p, i) is None,
            found is Some ==> {
                let (n, kind, leaf) = found->Some_0;
                &&& KERNEL_MEM_END_L4INDEX <= n.0
                &&& pei_valid(n.0)
                &&& pei_valid(n.1)
                &&& pei_valid(n.2)
                &&& pei_valid(n.3)
                &&& spec_l4_index_path_le(cursor, n)
                &&& kind is L1g ==> n.2 == 0 && n.3 == 0 && whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_held_1g_l3(n.0, n.1) == Some(leaf)
                &&& kind is L2m ==> n.3 == 0 && whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_held_2m_l2(n.0, n.1, n.2) == Some(leaf)
                &&& kind is L4k ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_held_4k_l1(n.0, n.1, n.2, n.3) == Some(leaf)
            },
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (found is None || !spec_l4_index_path_le(found->Some_0.0, (l4i, l3i, l2i, l1i)))
                    ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_held_4k_l1(l4i, l3i, l2i, l1i) is None,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i)]
                KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (found is None || !spec_l4_index_path_le(found->Some_0.0, (l4i, l3i, l2i, 0)))
                    ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i) is None,
            forall|l4i: L4Index, l3i: L3Index| #![trigger whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_held_1g_l3(l4i, l3i)]
                KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && (found is None || !spec_l4_index_path_le(found->Some_0.0, (l4i, l3i, 0, 0)))
                    ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_held_1g_l3(l4i, l3i) is None,
        decreases 512 - cursor.0, 512 - cursor.1, 512 - cursor.2, 513 - cursor.3,
    {
        let (next, kind, leaf) = found.unwrap();
        let va = index2va(next);
        let pg_ptr = leaf.addr;
        proof {
            page_index_valid_imply_page_ptr_valid();
            assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
        }
        let ghost c = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        proof {
            pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable); c.higher.wf_l4_at(next.0);
        }
        match kind {
            HeldLeaf::L1g => {
                proof {
                    mapped_1g_page_pagetable_wf_held_leaf_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pagetable, next.0, next.1);
                    mapped_1g_page_pagetable_wf_page_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, page_ptr2page_index(pg_ptr), pagetable, va); page_index_valid_imply_page_ptr_valid();
                    spec_va_1g_valid_index_roundtrip(va); spec_index2va_injective();
                    assert(c.spec_held_l3(next.0, next.1) is None);
                }
                kill_reclaim_held_1g_page_scoped(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, thrd_ptr, target, pagetable, va, pg_ptr, Tracked(pagetable_perm),
                    Ghost(KillStage::Reclaim { flushed: true }), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
                cursor = (next.0, next.1, 511, 512);
                proof { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable); }
            },
            HeldLeaf::L2m => {
                proof {
                    c.l3_links_l2_wf_at(c.spec_held_l4(next.0)->0.addr, next.1); c.wf_l2_at(c.spec_held_l3(next.0, next.1)->0.addr, next.2);
                    spec_index2va_2m_valid(next.0, next.1, next.2);
                    mapped_2m_page_pagetable_wf_held_leaf_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pagetable, next.0, next.1, next.2);
                    mapped_2m_page_pagetable_wf_page_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, page_ptr2page_index(pg_ptr), pagetable, va); page_index_valid_imply_page_ptr_valid();
                }
                kill_reclaim_held_2m_page_scoped(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, thrd_ptr, target, pagetable, va, pg_ptr, Tracked(pagetable_perm),
                    Ghost(KillStage::Reclaim { flushed: true }), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
                cursor = (next.0, next.1, next.2, 512);
                proof {
                    assert(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_held_2m_l2(next.0, next.1, next.2) is None);
                    pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
                }
            },
            HeldLeaf::L4k => {
                proof {
                    c.l3_links_l2_wf_at(c.spec_held_l4(next.0)->0.addr, next.1); c.wf_l2_at(c.spec_held_l3(next.0, next.1)->0.addr, next.2);
                    spec_va_4k_index_roundtrip_at(va, next.0, next.1, next.2, next.3);
                    mapped_4k_page_pagetable_wf_held_leaf_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pagetable, next.0, next.1, next.2, next.3);
                    mapped_4k_page_pagetable_wf_page_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, page_ptr2page_index(pg_ptr), pagetable, va);
                }
                kill_reclaim_held_4k_page_scoped(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, thrd_ptr, target, pagetable, va, pg_ptr, Tracked(pagetable_perm),
                    Ghost(KillStage::Reclaim { flushed: true }), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
                cursor = (next.0, next.1, next.2, next.3 + 1);
                proof {
                    index_path_successor_implies_path_le_drops_only_predecessor(next, cursor); pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable);
                    pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
                }
            },
        }
        found = pagetable_map_next_held_leaf_from(&krnl.pt_mp, Tracked(krnl.pt_lower.borrow()), pagetable, cursor, Tracked(&*lctx), Tracked(pagetable_perm));
    }
    proof { pagetable_perms_wf_at(krnl.pt_mp, pagetable); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, target); }
}
}
