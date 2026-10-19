use vstd::prelude::*;
use crate::*;
use super::syscall_kill_process_spec::*;
use super::syscall_kill_process_trace::*;
use super::syscall_kill_process_walk::KillScope;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_walk::kill_walk_state;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_reclaim_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_reclaim_eof::{kill_quota_eof, kill_tables_emptied_eof, kill_zombify_eof};

verus! {
/// Clear every user 4K leaf of the target's write-locked page table, one step each.
pub(crate) fn kill_reclaim_clear_leaves(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, pagetable: RwLockPageTableRoot,
    iommu_table: Option<RwLockPageTableRoot>, Tracked(pagetable_perm): Tracked<&LockPerm>, Tracked(iommu_perm): Tracked<&Option<LockPerm>>, Ghost(kernel_l4_end): Ghost<usize>, start_l4: L4Index, Ghost(locked_pt): Ghost<PageTable<PT_TYPE>>,
    Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        scope == (KillScope::Subtree { process: process_ptr }),
        kill_reclaim_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Reclaim { flushed: false }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
            iommu_table, *pagetable_perm, *iommu_perm),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        target == chain[chain.len() - 1],
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
        old(krnl).pt_mp.spec_index(pagetable).view().mapping_2m() == locked_pt.mapping_2m(),
        old(krnl).pt_mp.spec_index(pagetable).view().mapping_1g() == locked_pt.mapping_1g(),
        locked_pt.leaves_present(),
        kernel_l4_end <= start_l4,
        KERNEL_MEM_END_L4INDEX <= start_l4,
        start_l4 == kernel_l4_end || start_l4 == KERNEL_MEM_END_L4INDEX,
        pei_valid(start_l4),
        forall|va: VAddr| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va)]
            old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va) && !old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).present ==> spec_va_4k_valid(va) && start_l4 <= spec_v2l4index(va),
        iommu_table is Some ==> old(krnl).it_mp.spec_index(iommu_table->Some_0).view().leaves_present() && old(krnl).it_mp.spec_index(iommu_table->Some_0).view().kernel_l4_end == 0,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_reclaim_state(*final(krnl), *final(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Reclaim { flushed: false }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
            iommu_table, *pagetable_perm, *iommu_perm),
        final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_2m() == locked_pt.mapping_2m(),
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_1g() == locked_pt.mapping_1g(),
        forall|va: VAddr| #![trigger final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va)]
            final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va) && !final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).present ==> spec_va_4k_valid(va) && start_l4 <= spec_v2l4index(va),
        iommu_table is Some ==> final(krnl).it_mp.spec_index(iommu_table->Some_0).view().leaves_present() && final(krnl).it_mp.spec_index(iommu_table->Some_0).view().kernel_l4_end == 0,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && start_l4 <= l4i && final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                ==> !final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present,
        final(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set,
{
    proof { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); }
    let mut cursor: (L4Index, L3Index, L2Index, L1Index) = (start_l4, 0, 0, 0);
    let mut found = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_perm)).next_mapped_4k_from(cursor);
    while found.is_some()
        invariant
            krnl.prc_mp.spec_index(process_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.kernel_view_locking_state() is Acquire,
            steps.snapshot_k() == *krnl,
            0 <= start <= old(steps).view().len() <= steps.view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            kill_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, ctx),
            scope == (KillScope::Subtree { process: process_ptr }),
            kill_reclaim_state(*krnl, *lctx, cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Reclaim { flushed: false }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
                iommu_table, *pagetable_perm, *iommu_perm),
            target == chain[chain.len() - 1],
            krnl.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
            krnl.pt_mp.spec_index(pagetable).view().mapping_2m() == locked_pt.mapping_2m(),
            krnl.pt_mp.spec_index(pagetable).view().mapping_1g() == locked_pt.mapping_1g(),
            locked_pt.leaves_present(),
            kernel_l4_end <= start_l4,
            KERNEL_MEM_END_L4INDEX <= start_l4,
            start_l4 == kernel_l4_end || start_l4 == KERNEL_MEM_END_L4INDEX,
            pei_valid(start_l4),
            forall|va: VAddr| #![trigger krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va)]
                krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va) && !krnl.pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).present ==> spec_va_4k_valid(va) && start_l4 <= spec_v2l4index(va),
            iommu_table is Some ==> krnl.it_mp.spec_index(iommu_table->Some_0).view().leaves_present() && krnl.it_mp.spec_index(iommu_table->Some_0).view().kernel_l4_end == 0,
            start_l4 <= cursor.0,
            pei_valid(cursor.0),
            pei_valid(cursor.1),
            pei_valid(cursor.2),
            cursor.3 <= 512,
            found is Some ==> {
                let next = found->Some_0;
                &&& kernel_l4_end <= next.0
                &&& pei_valid(next.0)
                &&& pei_valid(next.1)
                &&& pei_valid(next.2)
                &&& pei_valid(next.3)
                &&& spec_l4_index_path_le(cursor, next)
                &&& krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va(next))
            },
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_l4_index_path_le(cursor, (l4i, l3i, l2i, l1i))
                    && (found is None || !spec_l4_index_path_le(found->Some_0, (l4i, l3i, l2i, l1i))) ==> !krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && start_l4 <= l4i && !spec_l4_index_path_le(cursor, (l4i, l3i, l2i, l1i))
                    && krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                    ==> !krnl.pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present,
        decreases 512 - cursor.0, 512 - cursor.1, 512 - cursor.2, 513 - cursor.3,
    {
        let next = found.unwrap();
        let va = index2va(next);
        proof {
            pagetable_perms_wf_map(krnl.pt_mp);
            pagetable_perms_wf_at(krnl.pt_mp, pagetable);
            assert(spec_va_4k_valid(va) && spec_va2index(va) == next) by { spec_va_4k_index_roundtrip_at(va, next.0, next.1, next.2, next.3); };
        }
        let resolved = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_perm)).resolve_mapping_4k_l1(next.0, next.1, next.2, next.3);
        if resolved.2.is_some() && resolved.2.unwrap().present {
            let ghost leaf_k = *krnl;
            let ghost leaf_lctx = *lctx;
            let ghost leaf_before = steps.view();
            clear_4k_mapping_present(krnl, pagetable, va, Tracked(&mut *lctx), Tracked(pagetable_perm));
            proof {
                let leaf_post = *krnl;
                let before_u = kernel_k_to_kernel_u(leaf_k);
                assert(kernel_process_4k_mapping_changed(&leaf_k, &leaf_post, target, pagetable, va)) by { reveal(kernel_process_4k_mapping_changed); };
                kernel_process_4k_mapping_changed_implies_u_neq(&leaf_k, &leaf_post, target, pagetable, va);
                kill_step_pre_from_k(&leaf_k, &leaf_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Reclaim { flushed: false });
                kill_reclaim_pre_from_k(&leaf_k, &leaf_lctx, cpu_id, thread_ptr, target, KillStage::Reclaim { flushed: false }, pagetable, iommu_table); kill_leaf_pre_from_k(&leaf_k, pagetable, va);
                kernel_pagetable_4k_present_cleared_and_progress_changed_implies_u_step(&leaf_k, &leaf_post, pagetable, va, thread_ptr);
                kill_leaf_step_from_u(before_u, kernel_k_to_kernel_u(leaf_post), cpu_id, thread_ptr, target, va);
                krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
                kill_trace_push(&*steps, leaf_before, start, pre, before_u, kernel_k_to_kernel_u(leaf_post), cpu_id, ctx);
            }
        } else {
            proof { assert(!krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va) || !krnl.pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).present) by { reveal(PageTable::wf_mapping_4k); }; }
        }
        cursor = (next.0, next.1, next.2, next.3 + 1);
        proof { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); }
        found = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_perm)).next_mapped_4k_from(cursor);
    }
}

/// Flush the target's PCID from every cpu that publishes it, then record the flush.
pub(crate) fn kill_reclaim_flush(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, pagetable: RwLockPageTableRoot,
    iommu_table: Option<RwLockPageTableRoot>, Tracked(pagetable_perm): Tracked<&LockPerm>, Tracked(iommu_perm): Tracked<&Option<LockPerm>>, Ghost(kernel_l4_end): Ghost<usize>,
    Ghost(start_l4): Ghost<L4Index>, Ghost(locked_pt): Ghost<PageTable<PT_TYPE>>, cr3: PageTableRoot, pcid: Pcid, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
    Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        scope == (KillScope::Subtree { process: process_ptr }),
        kill_reclaim_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Reclaim { flushed: false }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
            iommu_table, *pagetable_perm, *iommu_perm),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        target == chain[chain.len() - 1],
        old(krnl).prc_mp.spec_index(target).view_rodata().view().cr3 == cr3,
        old(krnl).prc_mp.spec_index(target).view_rodata().view().pcid == pcid,
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
        old(krnl).pt_mp.spec_index(pagetable).view().mapping_2m() == locked_pt.mapping_2m(),
        old(krnl).pt_mp.spec_index(pagetable).view().mapping_1g() == locked_pt.mapping_1g(),
        locked_pt.leaves_present(),
        kernel_l4_end <= start_l4,
        KERNEL_MEM_END_L4INDEX <= start_l4,
        start_l4 == kernel_l4_end || start_l4 == KERNEL_MEM_END_L4INDEX,
        pei_valid(start_l4),
        forall|va: VAddr| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va)]
            old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va) && !old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).present ==> spec_va_4k_valid(va) && start_l4 <= spec_v2l4index(va),
        iommu_table is Some ==> old(krnl).it_mp.spec_index(iommu_table->Some_0).view().leaves_present() && old(krnl).it_mp.spec_index(iommu_table->Some_0).view().kernel_l4_end == 0,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && start_l4 <= l4i && old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                ==> !old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_reclaim_state(*final(krnl), *final(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Reclaim { flushed: true }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
            iommu_table, *pagetable_perm, *iommu_perm),
        final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_2m() == locked_pt.mapping_2m(),
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_1g() == locked_pt.mapping_1g(),
        forall|va: VAddr| #![trigger final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va)]
            final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va) && !final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).present ==> spec_va_4k_valid(va) && start_l4 <= spec_v2l4index(va),
        iommu_table is Some ==> final(krnl).it_mp.spec_index(iommu_table->Some_0).view().leaves_present() && final(krnl).it_mp.spec_index(iommu_table->Some_0).view().kernel_l4_end == 0,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && start_l4 <= l4i && final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                ==> !final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present,
        pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pagetable, final(krnl).pt_mp.spec_index(pagetable).view()),
        final(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set,
{
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
    while c < NUM_CPUS
        invariant
            krnl.prc_mp.spec_index(process_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.kernel_view_locking_state() is Acquire,
            steps.snapshot_k() == *krnl,
            0 <= start <= old(steps).view().len() <= steps.view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            kill_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, ctx),
            scope == (KillScope::Subtree { process: process_ptr }),
            kill_reclaim_state(*krnl, *lctx, cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Reclaim { flushed: false }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
                iommu_table, *pagetable_perm, *iommu_perm),
            target == chain[chain.len() - 1],
            krnl.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
            krnl.pt_mp.spec_index(pagetable).view().mapping_2m() == locked_pt.mapping_2m(),
            krnl.pt_mp.spec_index(pagetable).view().mapping_1g() == locked_pt.mapping_1g(),
            locked_pt.leaves_present(),
            kernel_l4_end <= start_l4,
            KERNEL_MEM_END_L4INDEX <= start_l4,
            start_l4 == kernel_l4_end || start_l4 == KERNEL_MEM_END_L4INDEX,
            pei_valid(start_l4),
            forall|va: VAddr| #![trigger krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va)]
                krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va) && !krnl.pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).present ==> spec_va_4k_valid(va) && start_l4 <= spec_v2l4index(va),
            iommu_table is Some ==> krnl.it_mp.spec_index(iommu_table->Some_0).view().leaves_present() && krnl.it_mp.spec_index(iommu_table->Some_0).view().kernel_l4_end == 0,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && start_l4 <= l4i && krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                    ==> !krnl.pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present,
            c <= NUM_CPUS,
            krnl.pt_mp.spec_index(pagetable).view().cr3 == cr3,
            krnl.pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
            page_ptr_valid(cr3),
            pcid_valid(pcid),
            pcid != KERNEL_DEFAULT_PCID,
            krnl.prc_mp.spec_index(target).view_rodata().view().pcid == pcid,
            forall|cc: CpuId| #![trigger krnl.cpu_tlb.spec_index((cc, pcid))] index_valid(c, cc)
                && (!krnl.pcid_needflush.spec_index(cc, pcid).view().needflush || krnl.cpu_arr.spec_index(cc).view().view().view().current_pcid == pcid)
                && krnl.cpu_arr.spec_index(cc).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some && krnl.cpu_arr.spec_index(cc).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr == pagetable
                    ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(krnl.cpu_tlb.spec_index((cc, pcid)), krnl.pt_mp.spec_index(pagetable).view()),
        decreases NUM_CPUS - c,
    {
        let ghost iter_k = *krnl;
        let ghost iter_lctx = *lctx;
        let ghost iter_before = steps.view();
        let Tracked(needflush_perm) = krnl.wlock_pcid_needflush(c, pcid, Tracked(&mut *lctx));
        let published = mark_pcid_needflush_and_load(krnl, c, pcid, Tracked(&mut *lctx), Tracked(&needflush_perm));
        let flushed = published.0 == cr3 && published.1 == pcid;
        if flushed {
            if c == cpu_id {
                flush_local_pcid_and_clear(krnl, c, pcid, cr3, Tracked(&*lctx), Tracked(&needflush_perm), Tracked(cpu_perm));
            } else {
                flush_remote_pcid_and_clear(krnl, c, pcid, Tracked(&*lctx), Tracked(&needflush_perm));
            }
        }
        assert((!krnl.pcid_needflush.spec_index(c, pcid).view().needflush || krnl.cpu_arr.spec_index(c).view().view().view().current_pcid == pcid)
            && krnl.cpu_arr.spec_index(c).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some
            && krnl.cpu_arr.spec_index(c).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr == pagetable
            ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(krnl.cpu_tlb.spec_index((c, pcid)), krnl.pt_mp.spec_index(pagetable).view())) by {
            cpu_current_pcid_pagetable_match_at(krnl.cpu_arr, krnl.dflt_pt.view(), krnl.prc_mp, krnl.pt_mp, c, pcid, pagetable);
        };
        krnl.wunlock_pcid_needflush(c, pcid, Tracked(&mut *lctx), Tracked(needflush_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by {
                broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
            };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            let tlb_k = *krnl;
            krnl.kernel_step_boundary_cpu_tlb_updated(&mut *lctx, &mut *steps, c, pcid, flushed);
            kill_step_pre_from_k(&iter_k, &iter_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Reclaim { flushed: false });
            kill_reclaim_pre_from_k(&iter_k, &iter_lctx, cpu_id, thread_ptr, target, KillStage::Reclaim { flushed: false }, pagetable, iommu_table); kill_user_4k_unmapped_pre_from_k(&iter_k, target);
            kill_trace_push_tlb_flush(&*steps, iter_before, start, pre, kernel_k_to_kernel_u(iter_k), kernel_k_to_kernel_u(tlb_k), cpu_id, ctx, pcid);
        }
        c = c + 1;
    }
    assert(pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pagetable, krnl.pt_mp.spec_index(pagetable).view())) by { reveal(cpu_dirty_map_contains_pagetable_pcid_match); };
    let ghost flushed_k = *krnl;
    let ghost flushed_lctx = *lctx;
    let ghost flushed_before = steps.view();
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(kill_progress(target, KillStage::Reclaim { flushed: true })), Tracked(&*lctx), Tracked(thread_perm));
    proof {
        let flushed_pre = kernel_k_to_kernel_u(flushed_k);
        let flushed_post = kernel_k_to_kernel_u(*krnl);
        kill_step_pre_from_k(&flushed_k, &flushed_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Reclaim { flushed: false });
        kill_reclaim_pre_from_k(&flushed_k, &flushed_lctx, cpu_id, thread_ptr, target, KillStage::Reclaim { flushed: false }, pagetable, iommu_table); kill_user_4k_unmapped_pre_from_k(&flushed_k, target);
        kernel_thread_syscall_progress_changed_implies_u_step(&flushed_k, &*krnl, thread_ptr);
        kill_flushed_step_from_u(flushed_pre, flushed_post, cpu_id, thread_ptr, target);
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        kill_trace_push(&*steps, flushed_before, start, pre, flushed_pre, flushed_post, cpu_id, ctx);
        pagetable_perms_wf_at(krnl.pt_mp, pagetable);
    }
}

/// Unmap every cleared leaf of the target's page table, accumulating the quota of its page as the killer's pending refund,
/// then refund that quota to the killer's container chain.
pub(crate) fn kill_reclaim_unmap_leaves(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, pagetable: RwLockPageTableRoot,
    iommu_table: Option<RwLockPageTableRoot>, Tracked(pagetable_perm): Tracked<&LockPerm>, Tracked(iommu_perm): Tracked<&Option<LockPerm>>, Ghost(kernel_l4_end): Ghost<usize>, start_l4: L4Index, Ghost(locked_pt): Ghost<PageTable<PT_TYPE>>,
    Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        scope == (KillScope::Subtree { process: process_ptr }),
        kill_reclaim_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Reclaim { flushed: true }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
            iommu_table, *pagetable_perm, *iommu_perm),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        target == chain[chain.len() - 1],
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
        old(krnl).pt_mp.spec_index(pagetable).view().mapping_2m() == locked_pt.mapping_2m(),
        old(krnl).pt_mp.spec_index(pagetable).view().mapping_1g() == locked_pt.mapping_1g(),
        locked_pt.leaves_present(),
        kernel_l4_end <= start_l4,
        KERNEL_MEM_END_L4INDEX <= start_l4,
        start_l4 == kernel_l4_end || start_l4 == KERNEL_MEM_END_L4INDEX,
        pei_valid(start_l4),
        forall|va: VAddr| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va)]
            old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va) && !old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).present ==> spec_va_4k_valid(va) && start_l4 <= spec_v2l4index(va),
        iommu_table is Some ==> old(krnl).it_mp.spec_index(iommu_table->Some_0).view().leaves_present() && old(krnl).it_mp.spec_index(iommu_table->Some_0).view().kernel_l4_end == 0,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && start_l4 <= l4i && old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                ==> !old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present,
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pagetable, old(krnl).pt_mp.spec_index(pagetable).view()),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_reclaim_state(*final(krnl), *final(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Reclaim { flushed: true }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
            iommu_table, *pagetable_perm, *iommu_perm),
        final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
        final(krnl).pt_mp.spec_index(pagetable).view().leaves_present(),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && KERNEL_MEM_END_L4INDEX <= l4i && kernel_l4_end <= l4i ==> !final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
        iommu_table is Some ==> final(krnl).it_mp.spec_index(iommu_table->Some_0).view().leaves_present() && final(krnl).it_mp.spec_index(iommu_table->Some_0).view().kernel_l4_end == 0,
        final(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set,
{
    let ghost entry_thread = krnl.thr_mp.spec_index(thread_ptr).view();
    proof {
        pagetable_perms_wf_map(krnl.pt_mp);
        pagetable_perms_wf_at(krnl.pt_mp, pagetable); thread_perms_wf_at(krnl.thr_mp, thread_ptr);
        assert(krnl.prc_mp.spec_index(target).view_rodata().view().owning_container == krnl.thr_mp.spec_index(thread_ptr).view().owning_container) by { process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, thread_ptr); };
        assert(entry_thread.container_depth <= MAX_CONTAINER_TREE_DEPTH) by { container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, thread_ptr); container_perms_wf_at(krnl.ctn_mp, entry_thread.owning_container); };
    }
    let mut indirect = [0usize; MAX_CONTAINER_TREE_DEPTH];
    let mut direct = 0usize;
    let mut cursor: (L4Index, L3Index, L2Index, L1Index) = (start_l4, 0, 0, 0);
    let mut found = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_perm)).next_mapped_4k_from(cursor);
    while found.is_some()
        invariant
            krnl.prc_mp.spec_index(process_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.kernel_view_locking_state() is Acquire,
            steps.snapshot_k() == *krnl,
            0 <= start <= old(steps).view().len() <= steps.view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            kill_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, ctx),
            scope == (KillScope::Subtree { process: process_ptr }),
            kill_reclaim_state(*krnl, *lctx, cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Reclaim { flushed: true }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
                iommu_table, *pagetable_perm, *iommu_perm),
            target == chain[chain.len() - 1],
            krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
            krnl.pt_mp.spec_index(pagetable).view().mapping_2m() == locked_pt.mapping_2m(),
            krnl.pt_mp.spec_index(pagetable).view().mapping_1g() == locked_pt.mapping_1g(),
            locked_pt.leaves_present(),
            kernel_l4_end <= start_l4,
            KERNEL_MEM_END_L4INDEX <= start_l4,
            start_l4 == kernel_l4_end || start_l4 == KERNEL_MEM_END_L4INDEX,
            pei_valid(start_l4),
            forall|va: VAddr| #![trigger krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va)]
                krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va) && !krnl.pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).present ==> spec_va_4k_valid(va) && start_l4 <= spec_v2l4index(va),
            iommu_table is Some ==> krnl.it_mp.spec_index(iommu_table->Some_0).view().leaves_present() && krnl.it_mp.spec_index(iommu_table->Some_0).view().kernel_l4_end == 0,
            pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pagetable, krnl.pt_mp.spec_index(pagetable).view()),
            entry_thread.free_quota_pending_clean(),
            krnl.prc_mp.spec_index(target).view_rodata().view().owning_container == entry_thread.owning_container,
            krnl.thr_mp.spec_index(thread_ptr).view() == (Thread {
                direct_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k,
                indirect_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..entry_thread
            }),
            direct == krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
            forall|d: int| #![trigger indirect[d]] #![trigger krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d)] 0 <= d < entry_thread.container_depth
                ==> indirect[d] == krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && start_l4 <= l4i && krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                    ==> !krnl.pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && start_l4 <= l4i && !spec_l4_index_path_le(cursor, (l4i, l3i, l2i, l1i)) ==> !krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
            start_l4 <= cursor.0,
            pei_valid(cursor.0),
            pei_valid(cursor.1),
            pei_valid(cursor.2),
            cursor.3 <= 512,
            found is Some ==> {
                let next = found->Some_0;
                &&& kernel_l4_end <= next.0
                &&& pei_valid(next.0)
                &&& pei_valid(next.1)
                &&& pei_valid(next.2)
                &&& pei_valid(next.3)
                &&& spec_l4_index_path_le(cursor, next)
                &&& krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va(next))
            },
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_l4_index_path_le(cursor, (l4i, l3i, l2i, l1i))
                    && (found is None || !spec_l4_index_path_le(found->Some_0, (l4i, l3i, l2i, l1i))) ==> !krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
        decreases 512 - cursor.0, 512 - cursor.1, 512 - cursor.2, 513 - cursor.3,
    {
        let next = found.unwrap();
        let va = index2va(next);
        proof {
            assert(spec_va_4k_valid(va) && spec_va2index(va) == next) by { spec_va_4k_index_roundtrip_at(va, next.0, next.1, next.2, next.3); };
        }
        reclaim_unmapped_4k_page(krnl, pagetable, va, thread_ptr, cpu_id, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(pagetable_perm), Tracked(thread_perm));
        cursor = (next.0, next.1, next.2, next.3 + 1);
        proof { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, target); }
        found = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_perm)).next_mapped_4k_from(cursor);
    }
    proof {
        assert(krnl.pt_mp.spec_index(pagetable).view().leaves_present()) by { broadcast use spec_va_4k_valid_index_roundtrip; };
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl);
    }
    let ghost refund_k = *krnl;
    let ghost refund_lctx = *lctx;
    let ghost refund_before = steps.view();
    proof {
        kill_step_pre_from_k(&refund_k, &refund_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Reclaim { flushed: true }); kill_refund_pre_from_k(&refund_k, target, entry_thread.owning_container);
    }
    refund_unmap_4k_quota(krnl, thread_ptr, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_perm));
    proof {
        vstd::assert_seqs_equal!(krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view(), entry_thread.indirect_free_quota_pending_4k.view());
        kill_trace_from_refund(&*steps, refund_before, start, pre, kernel_k_to_kernel_u(refund_k), cpu_id, ctx, process_ptr, thread_ptr, target, KillStage::Reclaim { flushed: true },
            entry_thread.owning_container);
        pagetable_perms_wf_at(krnl.pt_mp, pagetable); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, target);
    }
}

/// Clear and unmap every 4K leaf of the target's write-locked IOMMU table, one step per cleared leaf, then refund the
/// quota of the freed pages to the killer's container chain.
pub(crate) fn kill_reclaim_iommu_leaves(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, pagetable: RwLockPageTableRoot,
    iommu_table: RwLockPageTableRoot, Tracked(pagetable_perm): Tracked<&LockPerm>, Tracked(iommu_perm): Tracked<&LockPerm>, Ghost(kernel_l4_end): Ghost<usize>,
    Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        scope == (KillScope::Subtree { process: process_ptr }),
        kill_reclaim_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Reclaim { flushed: true }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
            Some(iommu_table), *pagetable_perm, Some(*iommu_perm)),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        target == chain[chain.len() - 1],
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
        old(krnl).pt_mp.spec_index(pagetable).view().leaves_present(),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && KERNEL_MEM_END_L4INDEX <= l4i && kernel_l4_end <= l4i ==> !old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
        old(krnl).it_mp.spec_index(iommu_table).view().leaves_present() && old(krnl).it_mp.spec_index(iommu_table).view().kernel_l4_end == 0,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_reclaim_state(*final(krnl), *final(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Reclaim { flushed: true }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
            Some(iommu_table), *pagetable_perm, Some(*iommu_perm)),
        final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
        final(krnl).pt_mp.spec_index(pagetable).view().leaves_present(),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && KERNEL_MEM_END_L4INDEX <= l4i && kernel_l4_end <= l4i ==> !final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
        final(krnl).it_mp.spec_index(iommu_table).view().leaves_present(),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger final(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> !final(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
        final(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set,
{
    let ghost entry_thread = krnl.thr_mp.spec_index(thread_ptr).view();
    proof {
        iommu_table_perms_wf_map(krnl.it_mp);
        iommu_table_perms_wf_at(krnl.it_mp, iommu_table); thread_perms_wf_at(krnl.thr_mp, thread_ptr);
        assert(entry_thread.container_depth <= MAX_CONTAINER_TREE_DEPTH) by { container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, thread_ptr); container_perms_wf_at(krnl.ctn_mp, entry_thread.owning_container); };
        assert(krnl.prc_mp.spec_index(target).view_rodata().view().owning_container == entry_thread.owning_container) by { process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, thread_ptr); };
    }
    let mut indirect = [0usize; MAX_CONTAINER_TREE_DEPTH];
    let mut direct = 0usize;
    let mut cursor: (L4Index, L3Index, L2Index, L1Index) = (0, 0, 0, 0);
    let mut found = krnl.it_mp.borrow_typed(iommu_table, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), Tracked(iommu_perm)).next_mapped_4k_from(cursor);
    while found.is_some()
        invariant
            krnl.prc_mp.spec_index(process_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.kernel_view_locking_state() is Acquire,
            steps.snapshot_k() == *krnl,
            0 <= start <= old(steps).view().len() <= steps.view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            kill_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, ctx),
            scope == (KillScope::Subtree { process: process_ptr }),
            kill_reclaim_state(*krnl, *lctx, cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Reclaim { flushed: true }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
                Some(iommu_table), *pagetable_perm, Some(*iommu_perm)),
            target == chain[chain.len() - 1],
            krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
            krnl.pt_mp.spec_index(pagetable).view().leaves_present(),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && KERNEL_MEM_END_L4INDEX <= l4i && kernel_l4_end <= l4i ==> !krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
            entry_thread.free_quota_pending_clean(),
            krnl.prc_mp.spec_index(target).view_rodata().view().owning_container == entry_thread.owning_container,
            krnl.thr_mp.spec_index(thread_ptr).view() == (Thread {
                direct_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k,
                indirect_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..entry_thread
            }),
            direct == krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
            forall|d: int| #![trigger indirect[d]] #![trigger krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d)] 0 <= d < entry_thread.container_depth
                ==> indirect[d] == krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d),
            krnl.it_mp.spec_index(iommu_table).view().leaves_present(),
            krnl.it_mp.spec_index(iommu_table).view().kernel_l4_end == 0,
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
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && !spec_l4_index_path_le(cursor, (l4i, l3i, l2i, l1i))
                    ==> !krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_l4_index_path_le(cursor, (l4i, l3i, l2i, l1i))
                    && (found is None || !spec_l4_index_path_le(found->Some_0, (l4i, l3i, l2i, l1i))) ==> !krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
        decreases 512 - cursor.0, 512 - cursor.1, 512 - cursor.2, 513 - cursor.3,
    {
        let next = found.unwrap();
        let iova = index2va(next);
        let ghost leaf_k = *krnl;
        let ghost leaf_lctx = *lctx;
        let ghost leaf_before = steps.view();
        clear_iommu_4k_mapping_present(krnl, iommu_table, next, Tracked(&mut *lctx), Tracked(iommu_perm));
        proof {
            let leaf_post = *krnl;
            let before_u = kernel_k_to_kernel_u(leaf_k);
            kill_step_pre_from_k(&leaf_k, &leaf_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Reclaim { flushed: true });
            kill_reclaim_pre_from_k(&leaf_k, &leaf_lctx, cpu_id, thread_ptr, target, KillStage::Reclaim { flushed: true }, pagetable, Some(iommu_table));
            kernel_iommu_table_4k_present_cleared_implies_u_step(&leaf_k, &leaf_post, iommu_table, iova);
            kill_iommu_leaf_step_from_u(before_u, kernel_k_to_kernel_u(leaf_post), cpu_id, target, iova);
            krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
            kill_trace_push(&*steps, leaf_before, start, pre, before_u, kernel_k_to_kernel_u(leaf_post), cpu_id, ctx);
        }
        reclaim_unmapped_iommu_4k_page(krnl, iommu_table, next, thread_ptr, cpu_id, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(iommu_perm),
            Tracked(thread_perm));
        cursor = (next.0, next.1, next.2, next.3 + 1);
        proof { iommu_table_perms_wf_map(krnl.it_mp); iommu_table_perms_wf_at(krnl.it_mp, iommu_table); process_iommu_table_match_process_at(krnl.prc_mp, krnl.it_mp, target); }
        found = krnl.it_mp.borrow_typed(iommu_table, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), Tracked(iommu_perm)).next_mapped_4k_from(cursor);
    }
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    let ghost refund_k = *krnl;
    let ghost refund_lctx = *lctx;
    let ghost refund_before = steps.view();
    proof {
        kill_step_pre_from_k(&refund_k, &refund_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Reclaim { flushed: true }); kill_refund_pre_from_k(&refund_k, target, entry_thread.owning_container);
    }
    refund_unmap_4k_quota(krnl, thread_ptr, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_perm));
    proof {
        assert(krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view() =~= entry_thread.indirect_free_quota_pending_4k.view()) by { thread_perms_wf_at(krnl.thr_mp, thread_ptr); };
        kill_trace_from_refund(&*steps, refund_before, start, pre, kernel_k_to_kernel_u(refund_k), cpu_id, ctx, process_ptr, thread_ptr, target, KillStage::Reclaim { flushed: true },
            entry_thread.owning_container);
        iommu_table_perms_wf_at(krnl.it_mp, iommu_table); process_iommu_table_match_process_at(krnl.prc_mp, krnl.it_mp, target);
    }
}

/// Return the target's quota of every size to its container, one size per step.
pub(crate) fn kill_reclaim_return_quota(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, pagetable: RwLockPageTableRoot,
    iommu_table: Option<RwLockPageTableRoot>, Tracked(pagetable_perm): Tracked<&LockPerm>, Tracked(iommu_perm): Tracked<&Option<LockPerm>>,
    Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        scope == (KillScope::Subtree { process: process_ptr }),
        kill_reclaim_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Reclaim { flushed: true }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
            iommu_table, *pagetable_perm, *iommu_perm),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        target == chain[chain.len() - 1],
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_reclaim_state(*final(krnl), *final(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Quota { returned: PageSize::SZ1g }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
            iommu_table, *pagetable_perm, *iommu_perm),
        final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        final(krnl).pt_mp.spec_index(pagetable) == old(krnl).pt_mp.spec_index(pagetable),
        iommu_table is Some ==> final(krnl).it_mp.spec_index(iommu_table->Some_0) == old(krnl).it_mp.spec_index(iommu_table->Some_0),
        final(krnl).prc_mp.spec_index(target).view().quota_4k == 0,
        final(krnl).prc_mp.spec_index(target).view().quota_2m == 0,
        final(krnl).prc_mp.spec_index(target).view().quota_1g == 0,
        final(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set,
{
    kill_reclaim_return_quota_size(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, Ghost(chain), Tracked(chain_perms), Tracked(cpu_perm),
        Tracked(process_perm), Tracked(thread_perm), pagetable, iommu_table, Tracked(pagetable_perm), Tracked(iommu_perm), PageSize::SZ4k, Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    kill_reclaim_return_quota_size(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, Ghost(chain), Tracked(chain_perms), Tracked(cpu_perm),
        Tracked(process_perm), Tracked(thread_perm), pagetable, iommu_table, Tracked(pagetable_perm), Tracked(iommu_perm), PageSize::SZ2m, Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    kill_reclaim_return_quota_size(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, Ghost(chain), Tracked(chain_perms), Tracked(cpu_perm),
        Tracked(process_perm), Tracked(thread_perm), pagetable, iommu_table, Tracked(pagetable_perm), Tracked(iommu_perm), PageSize::SZ1g, Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
}

/// Return the whole `size` quota of the target to its container's `size` allocator under that allocator's quota lock, and
/// record the return as the killer's progress.
pub(crate) fn kill_reclaim_return_quota_size(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, pagetable: RwLockPageTableRoot,
    iommu_table: Option<RwLockPageTableRoot>, Tracked(pagetable_perm): Tracked<&LockPerm>, Tracked(iommu_perm): Tracked<&Option<LockPerm>>, size: PageSize,
    Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        scope == (KillScope::Subtree { process: process_ptr }),
        kill_reclaim_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, kill_process_quota_stage_before(size), *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
            iommu_table, *pagetable_perm, *iommu_perm),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        target == chain[chain.len() - 1],
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_reclaim_state(*final(krnl), *final(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Quota { returned: size }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
            iommu_table, *pagetable_perm, *iommu_perm),
        final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        final(krnl).pt_mp.spec_index(pagetable) == old(krnl).pt_mp.spec_index(pagetable),
        iommu_table is Some ==> final(krnl).it_mp.spec_index(iommu_table->Some_0) == old(krnl).it_mp.spec_index(iommu_table->Some_0),
        final(krnl).prc_mp.spec_index(target).view().quota_4k == if size is SZ4k { 0 } else { old(krnl).prc_mp.spec_index(target).view().quota_4k },
        final(krnl).prc_mp.spec_index(target).view().quota_2m == if size is SZ2m { 0 } else { old(krnl).prc_mp.spec_index(target).view().quota_2m },
        final(krnl).prc_mp.spec_index(target).view().quota_1g == if size is SZ1g { 0 } else { old(krnl).prc_mp.spec_index(target).view().quota_1g },
        final(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set,
{
    let ghost entry_k = *krnl;
    let ghost entry_lctx = *lctx;
    let ghost entry_steps = steps.view();
    proof { process_perms_wf_map(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, target); }
    let container_ptr = krnl.prc_mp.borrow_rodata(target).borrow().owning_container;
    proof {
        assert({
            &&& krnl.ctn_mp.dom().contains(container_ptr)
            &&& krnl.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(target)
            &&& krnl.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().contains(thread_ptr)
            &&& krnl.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr
        }) by { container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, target); container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, thread_ptr); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, thread_ptr); };
        container_process_thread_quota_sums_bounded(&*krnl, container_ptr, target, thread_ptr);
        container_perms_wf_at(krnl.ctn_mp, container_ptr);
    }
    match size {
        PageSize::SZ4k => {
            let allocator_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().allocator_ptr_4k;
            proof { assert(krnl.allc_4k_mp.dom().contains(allocator_ptr) && krnl.allc_4k_mp.spec_index(allocator_ptr).wf()) by {
                container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr); allocator_perms_wf_at(krnl.allc_4k_mp, allocator_ptr);
            }; }
            let Tracked(quota_perm) = krnl.wlock_allocator_quota_4k(allocator_ptr, Tracked(&mut *lctx));
            let ghost locked = *krnl;
            let process_quota = {
                let tracked target_perm = chain_perms.tracked_borrow(target);
                let process = krnl.prc_mp.borrow_mut_typed(target, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(target_perm));
                let quota = process.quota_4k;
                process.quota_4k = 0;
                quota
            };
            {
                let quota = krnl.allc_4k_mp.borrow_mut_quota_typed(allocator_ptr, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
                    Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(&quota_perm));
                quota.value = quota.value + process_quota;
            }
            proof {
                assert(kill_quota_eof_transition_framing(locked, *krnl, target, allocator_ptr, size)) by { reveal(kill_quota_eof_transition_framing); };
                kill_quota_eof(locked, *krnl, target, thread_ptr, allocator_ptr, size);
                assert(krnl.allc_4k_mp.spec_index(allocator_ptr).wf() && krnl.allc_4k_mp.spec_index(allocator_ptr).quota.inv()) by { allocator_perms_wf_at(krnl.allc_4k_mp, allocator_ptr); };
            }
            krnl.wunlock_allocator_quota_4k(allocator_ptr, Tracked(&mut *lctx), Tracked(quota_perm));
        }
        PageSize::SZ2m => {
            let allocator_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().allocator_ptr_2m;
            proof { assert(krnl.allc_2m_mp.dom().contains(allocator_ptr) && krnl.allc_2m_mp.spec_index(allocator_ptr).wf()) by {
                container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr); allocator_perms_wf_at(krnl.allc_2m_mp, allocator_ptr);
            }; }
            let Tracked(quota_perm) = krnl.wlock_allocator_quota_2m(allocator_ptr, Tracked(&mut *lctx));
            let ghost locked = *krnl;
            let process_quota = {
                let tracked target_perm = chain_perms.tracked_borrow(target);
                let process = krnl.prc_mp.borrow_mut_typed(target, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(target_perm));
                let quota = process.quota_2m;
                process.quota_2m = 0;
                quota
            };
            {
                let quota = krnl.allc_2m_mp.borrow_mut_quota_typed(allocator_ptr, Ghost(lctx.allocator_quota_2m_lock_map()), Ghost(lctx.allocator_cache_2m_lock_map()),
                    Ghost(lctx.allocator_global_pool_2m_lock_map()), Tracked(&*lctx), Tracked(&quota_perm));
                quota.value = quota.value + process_quota;
            }
            proof {
                assert(kill_quota_eof_transition_framing(locked, *krnl, target, allocator_ptr, size)) by { reveal(kill_quota_eof_transition_framing); };
                kill_quota_eof(locked, *krnl, target, thread_ptr, allocator_ptr, size);
                assert(krnl.allc_2m_mp.spec_index(allocator_ptr).wf() && krnl.allc_2m_mp.spec_index(allocator_ptr).quota.inv()) by { allocator_perms_wf_at(krnl.allc_2m_mp, allocator_ptr); };
            }
            krnl.wunlock_allocator_quota_2m(allocator_ptr, Tracked(&mut *lctx), Tracked(quota_perm));
        }
        PageSize::SZ1g => {
            let allocator_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().allocator_ptr_1g;
            proof { assert(krnl.allc_1g_mp.dom().contains(allocator_ptr) && krnl.allc_1g_mp.spec_index(allocator_ptr).wf()) by {
                container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr); allocator_perms_wf_at(krnl.allc_1g_mp, allocator_ptr);
            }; }
            let Tracked(quota_perm) = krnl.wlock_allocator_quota_1g(allocator_ptr, Tracked(&mut *lctx));
            let ghost locked = *krnl;
            let process_quota = {
                let tracked target_perm = chain_perms.tracked_borrow(target);
                let process = krnl.prc_mp.borrow_mut_typed(target, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(target_perm));
                let quota = process.quota_1g;
                process.quota_1g = 0;
                quota
            };
            {
                let quota = krnl.allc_1g_mp.borrow_mut_quota_typed(allocator_ptr, Ghost(lctx.allocator_quota_1g_lock_map()), Ghost(lctx.allocator_cache_1g_lock_map()),
                    Ghost(lctx.allocator_global_pool_1g_lock_map()), Tracked(&*lctx), Tracked(&quota_perm));
                quota.value = quota.value + process_quota;
            }
            proof {
                assert(kill_quota_eof_transition_framing(locked, *krnl, target, allocator_ptr, size)) by { reveal(kill_quota_eof_transition_framing); };
                kill_quota_eof(locked, *krnl, target, thread_ptr, allocator_ptr, size);
                assert(krnl.allc_1g_mp.spec_index(allocator_ptr).wf() && krnl.allc_1g_mp.spec_index(allocator_ptr).quota.inv()) by { allocator_perms_wf_at(krnl.allc_1g_mp, allocator_ptr); };
            }
            krnl.wunlock_allocator_quota_1g(allocator_ptr, Tracked(&mut *lctx), Tracked(quota_perm));
        }
    }
    let ghost returned_k = *krnl;
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(kill_progress(target, KillStage::Quota { returned: size })), Tracked(&*lctx), Tracked(thread_perm));
    proof {
        let pre_u = kernel_k_to_kernel_u(entry_k);
        let post_u = kernel_k_to_kernel_u(*krnl);
        kernel_process_quota_returned_implies_u_step(&entry_k, &returned_k, target, size);
        kernel_thread_syscall_progress_changed_implies_u_step(&returned_k, &*krnl, thread_ptr);
        kill_step_pre_from_k(&entry_k, &entry_lctx, cpu_id, process_ptr, thread_ptr, target, kill_process_quota_stage_before(size));
        kill_reclaim_pre_from_k(&entry_k, &entry_lctx, cpu_id, thread_ptr, target, kill_process_quota_stage_before(size), pagetable, iommu_table);
        kill_quota_step_from_u(pre_u, kernel_k_to_kernel_u(returned_k), post_u, cpu_id, thread_ptr, target, size);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        kill_trace_push(&*steps, entry_steps, start, pre, pre_u, post_u, cpu_id, ctx);
    }
}

/// Unlock the target's emptied page table and IOMMU table.
pub(crate) fn kill_reclaim_unlock_table(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, pagetable: RwLockPageTableRoot,
    iommu_table: Option<RwLockPageTableRoot>, Tracked(pagetable_perm): Tracked<LockPerm>, Tracked(iommu_perm): Tracked<Option<LockPerm>>, Ghost(kernel_l4_end): Ghost<usize>,
    Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        scope == (KillScope::Subtree { process: process_ptr }),
        kill_reclaim_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Quota { returned: PageSize::SZ1g }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
            iommu_table, pagetable_perm, iommu_perm),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        target == chain[chain.len() - 1],
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
        old(krnl).pt_mp.spec_index(pagetable).view().leaves_present(),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && KERNEL_MEM_END_L4INDEX <= l4i && kernel_l4_end <= l4i ==> !old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
        iommu_table is Some ==> old(krnl).it_mp.spec_index(iommu_table->Some_0).view().leaves_present(),
        iommu_table is Some ==> forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger old(krnl).it_mp.spec_index(iommu_table->Some_0).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> !old(krnl).it_mp.spec_index(iommu_table->Some_0).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
        old(krnl).prc_mp.spec_index(target).view().quota_4k == 0,
        old(krnl).prc_mp.spec_index(target).view().quota_2m == 0,
        old(krnl).prc_mp.spec_index(target).view().quota_1g == 0,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_walk_state(*final(krnl), *final(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, None, KillStage::Zombie, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
        !final(krnl).prc_mp.spec_index(target).view().zombie,
        final(krnl).prc_mp.spec_index(target).view().state.view() is TablesEmptied,
        final(krnl).prc_mp.spec_index(target).view().children.view().len() == 0,
        final(krnl).prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        final(krnl).prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
        final(krnl).prc_mp.spec_index(target).view().quota_4k == 0,
        final(krnl).prc_mp.spec_index(target).view().quota_2m == 0,
        final(krnl).prc_mp.spec_index(target).view().quota_1g == 0,
        final(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set,
{
    let ghost unlock_before = steps.view();
    let ghost unlock_k = *krnl;
    let ghost unlock_lctx = *lctx;
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(kill_progress(target, KillStage::Zombie)), Tracked(&*lctx), Tracked(thread_perm));
    let ghost progressed = *krnl;
    proof {
        process_perms_wf_map(krnl.prc_mp);
        process_perms_wf_at(krnl.prc_mp, target);
        assert(krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom() =~= Set::<VAddr>::empty()) by {
            pagetable_perms_wf_at(krnl.pt_mp, pagetable); krnl.default_pagetable_wf_at(pagetable); broadcast use spec_va_4k_valid_index_roundtrip;
        };
        if let Some(it) = iommu_table {
            assert(krnl.it_mp.spec_index(it).view().mapping_4k().dom() =~= Set::<VAddr>::empty()) by {
                iommu_table_perms_wf_at(krnl.it_mp, it);
                broadcast use iova_4k_valid_index_roundtrip;
            };
        }
    }
    {
        let tracked target_perm = chain_perms.tracked_borrow(target);
        let process = krnl.prc_mp.borrow_mut_typed(target, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(target_perm));
        process.state = Ghost(ProcessState::TablesEmptied);
    }
    proof {
        assert(kill_tables_emptied_eof_transition_framing(progressed, *krnl, target)) by { reveal(kill_tables_emptied_eof_transition_framing); };
        kill_tables_emptied_eof(progressed, *krnl, target);
    }
    if let Some(it) = iommu_table {
        krnl.wunlock_iommu_table(it, Tracked(&mut *lctx), Tracked(iommu_perm.tracked_unwrap()));
    }
    proof { tlb_wf_pagetable_entries_present_at(*krnl, pagetable); }
    krnl.wunlock_pagetable(pagetable, Tracked(&mut *lctx), Tracked(pagetable_perm));
    proof {
        let unlocked_k = *krnl;
        let before_u = kernel_k_to_kernel_u(unlock_k);
        kill_step_pre_from_k(&unlock_k, &unlock_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Quota { returned: PageSize::SZ1g });
        kill_reclaim_pre_from_k(&unlock_k, &unlock_lctx, cpu_id, thread_ptr, target, KillStage::Quota { returned: PageSize::SZ1g }, pagetable, iommu_table);
        kill_user_4k_unmapped_pre_from_k(&unlock_k, target);
        if iommu_table is Some { kill_iommu_unmapped_pre_from_k(&unlock_k, target); }
        kernel_process_tables_lock_state_and_progress_changed_implies_u_step(&unlock_k, &unlocked_k, &*lctx, target, pagetable, thread_ptr, false);
        kill_unlock_table_step_from_u(before_u, kernel_k_to_kernel_u(unlocked_k), cpu_id, thread_ptr, target);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        kill_trace_push(&*steps, unlock_before, start, pre, before_u, kernel_k_to_kernel_u(unlocked_k), cpu_id, ctx);
    }
}

/// Make the unlocked reclaimed target a zombie, release its PCID to its container, and start retiring it.
pub(crate) fn kill_reclaim_zombify(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
    Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        scope == (KillScope::Subtree { process: process_ptr }),
        kill_walk_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, None, KillStage::Zombie, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
        0 < chain.len(),
        target == chain[chain.len() - 1],
        !old(krnl).prc_mp.spec_index(target).view().zombie,
        old(krnl).prc_mp.spec_index(target).view().state.view() is TablesEmptied,
        old(krnl).prc_mp.spec_index(target).view().children.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
        old(krnl).prc_mp.spec_index(target).view().quota_4k == 0,
        old(krnl).prc_mp.spec_index(target).view().quota_2m == 0,
        old(krnl).prc_mp.spec_index(target).view().quota_1g == 0,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_walk_state(*final(krnl), *final(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, None, KillStage::Retire, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
        final(krnl).prc_mp.spec_index(target).view().zombie,
        final(krnl).prc_mp.spec_index(target).view().children.view().len() == 0,
        final(krnl).prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        final(krnl).prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
        final(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set,
{
    let ghost entry_k = *krnl;
    let ghost entry_lctx = *lctx;
    let ghost entry_steps = steps.view();
    proof { process_perms_wf_at(krnl.prc_mp, target); }
    let (container_ptr, pcid) = {
        let target_ro = krnl.prc_mp.borrow_rodata(target).borrow();
        (target_ro.owning_container, target_ro.pcid)
    };
    proof {
        assert(krnl.ctn_mp.dom().contains(container_ptr) && krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr) by {
            container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, target); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id);
        };
        container_perms_wf_at(krnl.ctn_mp, container_ptr);
    }
    let pcid_allocator_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().pcid_allocator;
    proof {
        assert(krnl.pcid_allc_mp.dom().contains(pcid_allocator_ptr) && krnl.pcid_allc_mp.spec_index(pcid_allocator_ptr).view().owning_container.view() == container_ptr) by {
            container_pcid_allocator_wf_container_at(krnl.ctn_mp, krnl.pcid_allc_mp, container_ptr);
        };
        assert({
            &&& krnl.prc_mp.spec_index(target).view().pcid == pcid
            &&& pcid_valid(pcid)
            &&& pcid != KERNEL_DEFAULT_PCID
            &&& krnl.pcid_allc_mp.spec_index(pcid_allocator_ptr).view().id_to_proc.view().spec_index(pcid as int).contains(target)
        }) by { process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, target); process_pcid_allocator_wf_process_at(krnl.ctn_mp, krnl.prc_mp, krnl.pcid_allc_mp, target); };
    }
    let Tracked(pcid_allocator_perm) = krnl.wlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx));
    let ghost locked = *krnl;
    proof { pcid_allocator_perms_wf_at(krnl.pcid_allc_mp, pcid_allocator_ptr); process_perms_wf_map(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, target); }
    pcid_allocator_map_release(&mut krnl.pcid_allc_mp, pcid_allocator_ptr, target, pcid, Tracked(&*lctx), Tracked(&pcid_allocator_perm));
    {
        let tracked target_perm = chain_perms.tracked_borrow(target);
        let process = krnl.prc_mp.borrow_mut_typed(target, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(target_perm));
        process.zombie = true;
        process.state = Ghost(ProcessState::Zombie);
    }
    proof {
        assert(kill_zombify_eof_transition_framing(locked, *krnl, target, pcid_allocator_ptr)) by { reveal(kill_zombify_eof_transition_framing); };
        kill_zombify_eof(locked, *krnl, target, pcid_allocator_ptr);
    }
    krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_perm));
    let ghost zombified_k = *krnl;
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(kill_progress(target, KillStage::Retire)), Tracked(&*lctx), Tracked(thread_perm));
    proof {
        let pre_u = kernel_k_to_kernel_u(entry_k);
        let post_u = kernel_k_to_kernel_u(*krnl);
        kernel_process_zombified_implies_u_step(&entry_k, &zombified_k, target, pcid_allocator_ptr);
        kernel_thread_syscall_progress_changed_implies_u_step(&zombified_k, &*krnl, thread_ptr);
        kill_step_pre_from_k(&entry_k, &entry_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Zombie); kill_zombify_pre_from_k(&entry_k, target);
        kill_zombify_step_from_u(pre_u, kernel_k_to_kernel_u(zombified_k), post_u, cpu_id, thread_ptr, target);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        kill_trace_push(&*steps, entry_steps, start, pre, pre_u, post_u, cpu_id, ctx);
    }
}
} // verus!
