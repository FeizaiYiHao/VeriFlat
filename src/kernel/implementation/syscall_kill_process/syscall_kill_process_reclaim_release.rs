use vstd::prelude::*;
use crate::*;
use super::syscall_kill_process_spec::*;
use super::syscall_kill_process_trace::*;
use super::syscall_kill_process_walk::KillScope;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_walk::kill_scope_progress;
use super::syscall_kill_process_reclaim_scoped::{kill_reclaim_unmapped_4k_page_scoped, kill_reclaim_unmapped_iommu_4k_page_scoped};
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
    iommu_table: Option<RwLockPageTableRoot>, Tracked(pagetable_perm): Tracked<&LockPerm>, Tracked(iommu_perm): Tracked<&Option<LockPerm>>, Ghost(kernel_l4_end): Ghost<usize>, start_l4: L4Index, Ghost(locked_pt): Ghost<PageTableC<PT_TYPE>>,
    Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        kill_reclaim_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Reclaim { flushed: false }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
            iommu_table, *pagetable_perm, *iommu_perm),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        target == chain[chain.len() - 1],
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m() == locked_pt.mapping_2m(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g() == locked_pt.mapping_1g(),
        locked_pt.leaves_present(),
        forall|k: (PageMapPtr, L2Index)| #![trigger pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)]
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k) ==> pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.spec_index(k) == Set::range(0usize, NUM_CPUS),
        kernel_l4_end <= start_l4,
        KERNEL_MEM_END_L4INDEX <= start_l4,
        start_l4 == kernel_l4_end || start_l4 == KERNEL_MEM_END_L4INDEX,
        pei_valid(start_l4),
        forall|va: VAddr| #![trigger pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(va)]
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(va) && !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(va).present ==> spec_va_4k_valid(va) && start_l4 <= spec_v2l4index(va),
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
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m() == locked_pt.mapping_2m(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_1g() == locked_pt.mapping_1g(),
        forall|k: (PageMapPtr, L2Index)| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)]
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k) ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.spec_index(k) == Set::range(0usize, NUM_CPUS),
        forall|va: VAddr| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(va)]
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(va) && !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(va).present ==> spec_va_4k_valid(va) && start_l4 <= spec_v2l4index(va),
        iommu_table is Some ==> final(krnl).it_mp.spec_index(iommu_table->Some_0).view().leaves_present() && final(krnl).it_mp.spec_index(iommu_table->Some_0).view().kernel_l4_end == 0,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && start_l4 <= l4i && pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                ==> !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present,
        final(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set,
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
    proof { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable); }
    let mut cursor: (L4Index, L3Index, L2Index, L1Index) = (start_l4, 0, 0, 0);
    let mut found = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_perm)).next_mapped_4k_from(Tracked(krnl.pt_lower.borrow().tracked_borrow(pagetable)), cursor);
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
            krnl.prc_mp.spec_index(process_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.kernel_view_locking_state() is Acquire,
            steps.snapshot_k() == *krnl,
            0 <= start <= old(steps).view().len() <= steps.view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            kill_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, ctx),
            kill_reclaim_state(*krnl, *lctx, cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Reclaim { flushed: false }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
                iommu_table, *pagetable_perm, *iommu_perm),
            target == chain[chain.len() - 1],
            krnl.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_2m() == locked_pt.mapping_2m(),
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_1g() == locked_pt.mapping_1g(),
            locked_pt.leaves_present(),
            forall|k: (PageMapPtr, L2Index)| #![trigger pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)]
                pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k) ==> pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.window_stale_cpus.spec_index(k) == Set::range(0usize, NUM_CPUS),
            kernel_l4_end <= start_l4,
            KERNEL_MEM_END_L4INDEX <= start_l4,
            start_l4 == kernel_l4_end || start_l4 == KERNEL_MEM_END_L4INDEX,
            pei_valid(start_l4),
            forall|va: VAddr| #![trigger pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(va)]
                pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(va) && !pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().spec_index(va).present ==> spec_va_4k_valid(va) && start_l4 <= spec_v2l4index(va),
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
                &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va(next))
            },
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_l4_index_path_le(cursor, (l4i, l3i, l2i, l1i))
                    && (found is None || !spec_l4_index_path_le(found->Some_0, (l4i, l3i, l2i, l1i))) ==> !pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && start_l4 <= l4i && !spec_l4_index_path_le(cursor, (l4i, l3i, l2i, l1i))
                    && pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                    ==> !pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present,
        decreases 512 - cursor.0, 512 - cursor.1, 512 - cursor.2, 513 - cursor.3,
    {
        let next = found.unwrap();
        let va = index2va(next);
        proof {
            pagetable_perms_wf_map(krnl.pt_mp);
            pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
            assert(spec_va_4k_valid(va) && spec_va2index(va) == next) by { spec_va_4k_index_roundtrip_at(va, next.0, next.1, next.2, next.3); };
            krnl.cpu_arr.typed_lock_map_aligned_lock_id_at(lctx.cpu_lock_map(), lctx.thread_id(), cpu_id);
        }
        let resolved = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_perm)).resolve_mapping_4k_l1(Tracked(krnl.pt_lower.borrow().tracked_borrow(pagetable)), next.0, next.1, next.2, next.3);
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
                kill_step_pre_from_k(&leaf_k, &leaf_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Reclaim { flushed: false }, scope);
                kill_reclaim_pre_from_k(&leaf_k, &leaf_lctx, cpu_id, thread_ptr, target, KillStage::Reclaim { flushed: false }, pagetable, iommu_table); kill_leaf_pre_from_k(&leaf_k, pagetable, va);
                kernel_pagetable_4k_present_cleared_and_progress_changed_implies_u_step(&leaf_k, &leaf_post, pagetable, va, thread_ptr);
                kill_leaf_step_from_u(before_u, kernel_k_to_kernel_u(leaf_post), cpu_id, thread_ptr, target, va);
                krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
                kill_trace_push(&*steps, leaf_before, start, pre, before_u, kernel_k_to_kernel_u(leaf_post), cpu_id, ctx);
            }
        } else {
            proof { assert(!pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(va) || !pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().spec_index(va).present) by { reveal(PageTableC::wf_mapping_4k); }; }
        }
        cursor = (next.0, next.1, next.2, next.3 + 1);
        proof { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable); }
        found = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_perm)).next_mapped_4k_from(Tracked(krnl.pt_lower.borrow().tracked_borrow(pagetable)), cursor);
    }
}

/// Flush the target's PCID from every cpu that publishes it, then record the flush.
pub(crate) fn kill_reclaim_flush(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, pagetable: RwLockPageTableRoot,
    iommu_table: Option<RwLockPageTableRoot>, Tracked(pagetable_perm): Tracked<&LockPerm>, Tracked(iommu_perm): Tracked<&Option<LockPerm>>, Ghost(kernel_l4_end): Ghost<usize>,
    Ghost(start_l4): Ghost<L4Index>, Ghost(locked_pt): Ghost<PageTableC<PT_TYPE>>, cr3: PageTableRoot, pcid: Pcid, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
    Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        kill_reclaim_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Reclaim { flushed: false }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
            iommu_table, *pagetable_perm, *iommu_perm),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        target == chain[chain.len() - 1],
        old(krnl).prc_mp.spec_index(target).view_rodata().view().cr3 == cr3,
        old(krnl).prc_mp.spec_index(target).view_rodata().view().pcid == pcid,
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m() == locked_pt.mapping_2m(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g() == locked_pt.mapping_1g(),
        locked_pt.leaves_present(),
        forall|k: (PageMapPtr, L2Index)| #![trigger pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)]
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k) ==> pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.spec_index(k) == Set::range(0usize, NUM_CPUS),
        kernel_l4_end <= start_l4,
        KERNEL_MEM_END_L4INDEX <= start_l4,
        start_l4 == kernel_l4_end || start_l4 == KERNEL_MEM_END_L4INDEX,
        pei_valid(start_l4),
        forall|va: VAddr| #![trigger pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(va)]
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(va) && !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(va).present ==> spec_va_4k_valid(va) && start_l4 <= spec_v2l4index(va),
        iommu_table is Some ==> old(krnl).it_mp.spec_index(iommu_table->Some_0).view().leaves_present() && old(krnl).it_mp.spec_index(iommu_table->Some_0).view().kernel_l4_end == 0,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && start_l4 <= l4i && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                ==> !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present,
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
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m() == locked_pt.mapping_2m(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_1g() == locked_pt.mapping_1g(),
        forall|va: VAddr| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(va)]
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(va) && !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(va).present ==> spec_va_4k_valid(va) && start_l4 <= spec_v2l4index(va),
        iommu_table is Some ==> final(krnl).it_mp.spec_index(iommu_table->Some_0).view().leaves_present() && final(krnl).it_mp.spec_index(iommu_table->Some_0).view().kernel_l4_end == 0,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && start_l4 <= l4i && pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                ==> !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present,
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        final(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set,
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
            krnl.prc_mp.spec_index(process_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.kernel_view_locking_state() is Acquire,
            steps.snapshot_k() == *krnl,
            0 <= start <= old(steps).view().len() <= steps.view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            kill_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, ctx),
            kill_reclaim_state(*krnl, *lctx, cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Reclaim { flushed: false }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
                iommu_table, *pagetable_perm, *iommu_perm),
            target == chain[chain.len() - 1],
            krnl.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_2m() == locked_pt.mapping_2m(),
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_1g() == locked_pt.mapping_1g(),
            locked_pt.leaves_present(),
            kernel_l4_end <= start_l4,
            KERNEL_MEM_END_L4INDEX <= start_l4,
            start_l4 == kernel_l4_end || start_l4 == KERNEL_MEM_END_L4INDEX,
            pei_valid(start_l4),
            forall|va: VAddr| #![trigger pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(va)]
                pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(va) && !pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().spec_index(va).present ==> spec_va_4k_valid(va) && start_l4 <= spec_v2l4index(va),
            iommu_table is Some ==> krnl.it_mp.spec_index(iommu_table->Some_0).view().leaves_present() && krnl.it_mp.spec_index(iommu_table->Some_0).view().kernel_l4_end == 0,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && start_l4 <= l4i && pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                    ==> !pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present,
            c <= NUM_CPUS,
            krnl.pt_mp.spec_index(pagetable).view().cr3 == cr3,
            krnl.pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
            page_ptr_valid(cr3),
            pcid_valid(pcid),
            pcid != KERNEL_DEFAULT_PCID,
            krnl.prc_mp.spec_index(target).view_rodata().view().pcid == pcid,
            forall|k: (PageMapPtr, L2Index)| #![trigger pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)]
                pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k) ==> c < NUM_CPUS && pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.window_stale_cpus.spec_index(k) == Set::range(c, NUM_CPUS),
        decreases NUM_CPUS - c,
    {
        let ghost iter_k = *krnl;
        let ghost iter_lctx = *lctx;
        let ghost iter_before = steps.view();
        proof { krnl.cpu_arr.typed_lock_map_aligned_lock_id_at(lctx.cpu_lock_map(), lctx.thread_id(), cpu_id); }
        let flushed = kill_reclaim_flush_cpu_tlb(krnl, Tracked(&mut *lctx), c, cpu_id, pagetable, cr3, pcid, Tracked(cpu_perm));
        proof {
            let tlb_k = *krnl;
            krnl.kernel_step_boundary_cpu_tlb_updated(&mut *lctx, &mut *steps, c, pcid, flushed);
            kill_step_pre_from_k(&iter_k, &iter_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Reclaim { flushed: false }, scope);
            kill_reclaim_pre_from_k(&iter_k, &iter_lctx, cpu_id, thread_ptr, target, KillStage::Reclaim { flushed: false }, pagetable, iommu_table); kill_user_4k_unmapped_pre_from_k(&iter_k, target);
            kill_trace_push_tlb_flush(&*steps, iter_before, start, pre, kernel_k_to_kernel_u(iter_k), kernel_k_to_kernel_u(tlb_k), cpu_id, ctx, pcid);
        }
        c = c + 1;
    }
    assert(pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.window_stale_cpus =~= Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty());
    let ghost flushed_k = *krnl;
    let ghost flushed_lctx = *lctx;
    let ghost flushed_before = steps.view();
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(kill_scope_progress(scope, target, KillStage::Reclaim { flushed: true })), Tracked(&*lctx), Tracked(thread_perm));
    proof {
        let flushed_pre = kernel_k_to_kernel_u(flushed_k);
        let flushed_post = kernel_k_to_kernel_u(*krnl);
        kill_step_pre_from_k(&flushed_k, &flushed_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Reclaim { flushed: false }, scope);
        kill_reclaim_pre_from_k(&flushed_k, &flushed_lctx, cpu_id, thread_ptr, target, KillStage::Reclaim { flushed: false }, pagetable, iommu_table); kill_user_4k_unmapped_pre_from_k(&flushed_k, target);
        kernel_thread_syscall_progress_changed_implies_u_step(&flushed_k, &*krnl, thread_ptr);
        kill_flushed_step_from_u(flushed_pre, flushed_post, cpu_id, thread_ptr, target, scope);
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        kill_trace_push(&*steps, flushed_before, start, pre, flushed_pre, flushed_post, cpu_id, ctx);
        pagetable_perms_wf_at(krnl.pt_mp, pagetable);
    }
}

/// Flush `pcid` on cpu `c` under its needflush lock and drop `c` from every stale-CPU record of the write-held page table
/// `pagetable` with `cr3` and `pcid`, deleting the records after the last cpu; returns whether `c` published the table.
pub(crate) fn kill_reclaim_flush_cpu_tlb(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, c: usize, cpu_id: CpuId, pagetable: RwLockPageTableRoot, cr3: PageTableRoot, pcid: Pcid,
    Tracked(cpu_perm): Tracked<&LockPerm>,
) -> (flushed: bool)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        c < NUM_CPUS,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        typed_lock_map_majors_lt(old(lctx).cpu_lock_map(), CPU_LOCK_MAJOR_OFF),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_perm.state() is WriteLock,
        cpu_perm.thread_id() == old(lctx).thread_id(),
        cpu_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).pt_mp.dom().contains(pagetable),
        old(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        page_ptr_valid(cr3),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        forall|k: (PageMapPtr, L2Index)| #![trigger pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)]
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k) ==> pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.spec_index(k) == Set::range(c, NUM_CPUS),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, cpu_tlb: final(krnl).cpu_tlb, pcid_needflush: final(krnl).pcid_needflush, pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, ..*old(krnl) }),
        forall|cpu: CpuId| #![trigger final(krnl).cpu_arr.spec_index(cpu)] index_valid(NUM_CPUS, cpu) ==> final(krnl).cpu_arr.spec_index(cpu).value.locking_thread() == old(krnl).cpu_arr.spec_index(cpu).value.locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).pt_mp.dom() == old(krnl).pt_mp.dom(),
        forall|pt: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(pt)] old(krnl).pt_mp.dom().contains(pt) ==> {
            &&& final(krnl).pt_mp.spec_index(pt).view() == old(krnl).pt_mp.spec_index(pt).view()
            &&& final(krnl).pt_mp.spec_index(pt).locking_thread() == old(krnl).pt_mp.spec_index(pt).locking_thread()
            &&& final(krnl).pt_mp.spec_index(pt).being_killed() == old(krnl).pt_mp.spec_index(pt).being_killed()
            &&& final(krnl).pt_mp.lock_id_by_key(pt) == old(krnl).pt_mp.lock_id_by_key(pt)
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt).mapping_4k() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt).mapping_4k()
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt).mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt).mapping_2m()
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt).mapping_1g()
        },
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        final(krnl).cpu_tlb.view() == if flushed { old(krnl).cpu_tlb.view().insert((c, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }) } else { old(krnl).cpu_tlb.view() },
        forall|k: (PageMapPtr, L2Index)| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)]
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains(k)
                ==> c + 1 < NUM_CPUS && pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.spec_index(k) == Set::range((c + 1) as usize, NUM_CPUS),
{
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
    assert(krnl.cpu_tlb.spec_index((c, pcid)).is_empty()
        || (krnl.pcid_needflush.spec_index(c, pcid).view().needflush && krnl.cpu_arr.spec_index(c).view().view().view().current_pcid != pcid)
        || (krnl.cpu_arr.spec_index(c).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some
            && krnl.cpu_arr.spec_index(c).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr != pagetable)) by {
        cpu_current_pcid_pagetable_match_at(krnl.cpu_arr, krnl.dflt_pt.view(), krnl.prc_mp, krnl.pt_mp, c, pcid, pagetable);
        cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), c); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, c);
        process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, krnl.cpu_arr.spec_index(c).view().view().view().current_process.unwrap());
    };
    krnl.wunlock_pcid_needflush(c, pcid, Tracked(&mut *lctx), Tracked(needflush_perm));
    proof {
        assert(lctx.pcid_needflush_lock_map() =~= old(lctx).pcid_needflush_lock_map());
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by {
            broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
        };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    assert(Set::range(c, NUM_CPUS).remove(c) =~= Set::range((c + 1) as usize, NUM_CPUS));
    krnl.replace_window_stale_cpus(pagetable, Ghost(WindowStaleUpdate::RemoveCpu { cpu_id: c }), Tracked(&*lctx));
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    if c + 1 == NUM_CPUS {
        assert(Set::range((c + 1) as usize, NUM_CPUS) =~= Set::<CpuId>::empty());
        krnl.replace_window_stale_cpus(pagetable, Ghost(WindowStaleUpdate::ClearEmpty), Tracked(&*lctx));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        }
    }
    flushed
}

/// Unmap every cleared leaf of the target's page table. In a process kill (`same`), whose target shares the killer's
/// container, the quota of each freed page accumulates as the killer's pending refund, refunded to the killer's container
/// chain at the end; otherwise each freed page is credited to its owner's quota in its own step.
pub(crate) fn kill_reclaim_unmap_leaves(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, pagetable: RwLockPageTableRoot,
    iommu_table: Option<RwLockPageTableRoot>, Tracked(pagetable_perm): Tracked<&LockPerm>, Tracked(iommu_perm): Tracked<&Option<LockPerm>>, Ghost(kernel_l4_end): Ghost<usize>, start_l4: L4Index, Ghost(locked_pt): Ghost<PageTableC<PT_TYPE>>,
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
        kill_reclaim_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Reclaim { flushed: true }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
            iommu_table, *pagetable_perm, *iommu_perm),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        target == chain[chain.len() - 1],
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m() == locked_pt.mapping_2m(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g() == locked_pt.mapping_1g(),
        locked_pt.leaves_present(),
        kernel_l4_end <= start_l4,
        KERNEL_MEM_END_L4INDEX <= start_l4,
        start_l4 == kernel_l4_end || start_l4 == KERNEL_MEM_END_L4INDEX,
        pei_valid(start_l4),
        forall|va: VAddr| #![trigger pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(va)]
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(va) && !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(va).present ==> spec_va_4k_valid(va) && start_l4 <= spec_v2l4index(va),
        iommu_table is Some ==> old(krnl).it_mp.spec_index(iommu_table->Some_0).view().leaves_present() && old(krnl).it_mp.spec_index(iommu_table->Some_0).view().kernel_l4_end == 0,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && start_l4 <= l4i && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                ==> !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
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
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).leaves_present(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && KERNEL_MEM_END_L4INDEX <= l4i && kernel_l4_end <= l4i ==> !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
        iommu_table is Some ==> final(krnl).it_mp.spec_index(iommu_table->Some_0).view().leaves_present() && final(krnl).it_mp.spec_index(iommu_table->Some_0).view().kernel_l4_end == 0,
        final(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set,
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
    let ghost entry_thread = krnl.thr_mp.spec_index(thread_ptr).view();
    proof {
        pagetable_perms_wf_map(krnl.pt_mp);
        pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable); thread_perms_wf_at(krnl.thr_mp, thread_ptr);
        assert(same ==> krnl.prc_mp.spec_index(target).view_rodata().view().owning_container == entry_thread.owning_container) by { process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, thread_ptr); };
        assert(entry_thread.container_depth <= MAX_CONTAINER_TREE_DEPTH) by { container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, thread_ptr); container_perms_wf_at(krnl.ctn_mp, entry_thread.owning_container); };
    }
    let mut indirect = [0usize; MAX_CONTAINER_TREE_DEPTH];
    let mut direct = 0usize;
    let mut cursor: (L4Index, L3Index, L2Index, L1Index) = (start_l4, 0, 0, 0);
    let mut found = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_perm)).next_mapped_4k_from(Tracked(krnl.pt_lower.borrow().tracked_borrow(pagetable)), cursor);
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
            krnl.prc_mp.spec_index(process_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.kernel_view_locking_state() is Acquire,
            steps.snapshot_k() == *krnl,
            0 <= start <= old(steps).view().len() <= steps.view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            kill_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, ctx),
            kill_reclaim_state(*krnl, *lctx, cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Reclaim { flushed: true }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
                iommu_table, *pagetable_perm, *iommu_perm),
            target == chain[chain.len() - 1],
            krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_2m() == locked_pt.mapping_2m(),
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_1g() == locked_pt.mapping_1g(),
            locked_pt.leaves_present(),
            kernel_l4_end <= start_l4,
            KERNEL_MEM_END_L4INDEX <= start_l4,
            start_l4 == kernel_l4_end || start_l4 == KERNEL_MEM_END_L4INDEX,
            pei_valid(start_l4),
            forall|va: VAddr| #![trigger pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(va)]
                pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(va) && !pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().spec_index(va).present ==> spec_va_4k_valid(va) && start_l4 <= spec_v2l4index(va),
            iommu_table is Some ==> krnl.it_mp.spec_index(iommu_table->Some_0).view().leaves_present() && krnl.it_mp.spec_index(iommu_table->Some_0).view().kernel_l4_end == 0,
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
            entry_thread.free_quota_pending_clean(),
            same == (scope is Subtree),
            same ==> krnl.prc_mp.spec_index(target).view_rodata().view().owning_container == entry_thread.owning_container,
            same ==> krnl.thr_mp.spec_index(thread_ptr).view() == (Thread {
                direct_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k,
                indirect_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..entry_thread
            }),
            same ==> direct == krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
            same ==> forall|d: int| #![trigger indirect[d]] #![trigger krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d)] 0 <= d < entry_thread.container_depth
                ==> indirect[d] == krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d),
            !same ==> krnl.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && start_l4 <= l4i && pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                    ==> !pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && start_l4 <= l4i && !spec_l4_index_path_le(cursor, (l4i, l3i, l2i, l1i)) ==> !pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
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
                &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va(next))
            },
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_l4_index_path_le(cursor, (l4i, l3i, l2i, l1i))
                    && (found is None || !spec_l4_index_path_le(found->Some_0, (l4i, l3i, l2i, l1i))) ==> !pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
        decreases 512 - cursor.0, 512 - cursor.1, 512 - cursor.2, 513 - cursor.3,
    {
        let next = found.unwrap();
        let va = index2va(next);
        proof {
            assert(spec_va_4k_valid(va) && spec_va2index(va) == next) by { spec_va_4k_index_roundtrip_at(va, next.0, next.1, next.2, next.3); };
            krnl.cpu_arr.typed_lock_map_aligned_lock_id_at(lctx.cpu_lock_map(), lctx.thread_id(), cpu_id); krnl.thr_mp.typed_lock_map_aligned_lock_id_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr);
        }
        if same {
            reclaim_unmapped_4k_page(krnl, pagetable, va, thread_ptr, cpu_id, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(pagetable_perm), Tracked(thread_perm));
        } else {
            kill_reclaim_unmapped_4k_page_scoped(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, pagetable, va, Tracked(pagetable_perm),
                Ghost(KillStage::Reclaim { flushed: true }), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
        }
        cursor = (next.0, next.1, next.2, next.3 + 1);
        proof { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, target); }
        found = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_perm)).next_mapped_4k_from(Tracked(krnl.pt_lower.borrow().tracked_borrow(pagetable)), cursor);
    }
    proof { assert(pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).leaves_present()) by { broadcast use spec_va_4k_valid_index_roundtrip; }; }
    if same {
        proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
        let ghost refund_k = *krnl;
        let ghost refund_lctx = *lctx;
        let ghost refund_before = steps.view();
        proof {
            kill_step_pre_from_k(&refund_k, &refund_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Reclaim { flushed: true }, scope); kill_refund_pre_from_k(&refund_k, target, entry_thread.owning_container);
            krnl.cpu_arr.typed_lock_map_aligned_lock_id_at(lctx.cpu_lock_map(), lctx.thread_id(), cpu_id);
        }
        refund_unmap_4k_quota(krnl, thread_ptr, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_perm));
        proof {
            vstd::assert_seqs_equal!(krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view(), entry_thread.indirect_free_quota_pending_4k.view());
            kill_trace_from_refund(&*steps, refund_before, start, pre, kernel_k_to_kernel_u(refund_k), cpu_id, ctx, process_ptr, thread_ptr, target, KillStage::Reclaim { flushed: true },
                entry_thread.owning_container, scope);
            assert(pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable) == pagetable_c(refund_k.pt_mp, refund_k.pt_lower.view(), pagetable)) by {
                refund_k.pt_mp.typed_lock_map_aligned_write_at(refund_lctx.pagetable_lock_map(), refund_lctx.thread_id(), pagetable);
                pagetable_lower_backup_wf_at(refund_k.pt_mp, refund_k.pt_lower.view(), pagetable); pagetable_lower_backup_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
            };
        }
    }
    proof { pagetable_perms_wf_at(krnl.pt_mp, pagetable); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, target); }
}

/// Clear and unmap every 4K leaf of the target's write-locked IOMMU table, one step per cleared leaf. In a process kill
/// (`same`), whose target shares the killer's container, the quota of the freed pages is refunded to the killer's
/// container chain at the end; otherwise each freed page is credited to its owner's quota in its own step.
pub(crate) fn kill_reclaim_iommu_leaves(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, pagetable: RwLockPageTableRoot,
    iommu_table: RwLockPageTableRoot, Tracked(pagetable_perm): Tracked<&LockPerm>, Tracked(iommu_perm): Tracked<&LockPerm>, Ghost(kernel_l4_end): Ghost<usize>,
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
        kill_reclaim_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Reclaim { flushed: true }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
            Some(iommu_table), *pagetable_perm, Some(*iommu_perm)),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        target == chain[chain.len() - 1],
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).leaves_present(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && KERNEL_MEM_END_L4INDEX <= l4i && kernel_l4_end <= l4i ==> !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
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
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).leaves_present(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && KERNEL_MEM_END_L4INDEX <= l4i && kernel_l4_end <= l4i ==> !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
        final(krnl).it_mp.spec_index(iommu_table).view().leaves_present(),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger final(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> !final(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
        final(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set,
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
    let ghost entry_thread = krnl.thr_mp.spec_index(thread_ptr).view();
    proof {
        iommu_table_perms_wf_map(krnl.it_mp);
        iommu_table_perms_wf_at(krnl.it_mp, iommu_table); thread_perms_wf_at(krnl.thr_mp, thread_ptr);
        assert(same ==> krnl.prc_mp.spec_index(target).view_rodata().view().owning_container == entry_thread.owning_container) by { process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, thread_ptr); };
        assert(entry_thread.container_depth <= MAX_CONTAINER_TREE_DEPTH) by { container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, thread_ptr); container_perms_wf_at(krnl.ctn_mp, entry_thread.owning_container); };
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
            krnl.prc_mp.spec_index(process_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.kernel_view_locking_state() is Acquire,
            steps.snapshot_k() == *krnl,
            0 <= start <= old(steps).view().len() <= steps.view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            kill_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, ctx),
            kill_reclaim_state(*krnl, *lctx, cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Reclaim { flushed: true }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
                Some(iommu_table), *pagetable_perm, Some(*iommu_perm)),
            target == chain[chain.len() - 1],
            krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).leaves_present(),
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && KERNEL_MEM_END_L4INDEX <= l4i && kernel_l4_end <= l4i ==> !pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
            entry_thread.free_quota_pending_clean(),
            same == (scope is Subtree),
            same ==> krnl.prc_mp.spec_index(target).view_rodata().view().owning_container == entry_thread.owning_container,
            same ==> krnl.thr_mp.spec_index(thread_ptr).view() == (Thread {
                direct_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k,
                indirect_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..entry_thread
            }),
            same ==> direct == krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
            same ==> forall|d: int| #![trigger indirect[d]] #![trigger krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d)] 0 <= d < entry_thread.container_depth
                ==> indirect[d] == krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d),
            !same ==> krnl.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
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
        proof { krnl.cpu_arr.typed_lock_map_aligned_lock_id_at(lctx.cpu_lock_map(), lctx.thread_id(), cpu_id); krnl.thr_mp.typed_lock_map_aligned_lock_id_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr); }
        clear_iommu_4k_mapping_present(krnl, iommu_table, next, Tracked(&mut *lctx), Tracked(iommu_perm));
        proof {
            let leaf_post = *krnl;
            let before_u = kernel_k_to_kernel_u(leaf_k);
            kill_step_pre_from_k(&leaf_k, &leaf_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Reclaim { flushed: true }, scope);
            kill_reclaim_pre_from_k(&leaf_k, &leaf_lctx, cpu_id, thread_ptr, target, KillStage::Reclaim { flushed: true }, pagetable, Some(iommu_table));
            kernel_iommu_table_4k_present_cleared_implies_u_step(&leaf_k, &leaf_post, iommu_table, iova);
            kill_iommu_leaf_step_from_u(before_u, kernel_k_to_kernel_u(leaf_post), cpu_id, target, iova);
            krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
            kill_trace_push(&*steps, leaf_before, start, pre, before_u, kernel_k_to_kernel_u(leaf_post), cpu_id, ctx);
        }
        if same {
            reclaim_unmapped_iommu_4k_page(krnl, iommu_table, next, thread_ptr, cpu_id, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(iommu_perm),
                Tracked(thread_perm));
        } else {
            kill_reclaim_unmapped_iommu_4k_page_scoped(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, iommu_table, next, Tracked(iommu_perm),
                Ghost(KillStage::Reclaim { flushed: true }), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
        }
        proof {
            assert(pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable) == pagetable_c(leaf_k.pt_mp, leaf_k.pt_lower.view(), pagetable)) by {
                leaf_k.pt_mp.typed_lock_map_aligned_write_at(leaf_lctx.pagetable_lock_map(), leaf_lctx.thread_id(), pagetable);
                pagetable_lower_backup_wf_at(leaf_k.pt_mp, leaf_k.pt_lower.view(), pagetable); pagetable_lower_backup_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
            };
        }
        cursor = (next.0, next.1, next.2, next.3 + 1);
        proof { iommu_table_perms_wf_map(krnl.it_mp); iommu_table_perms_wf_at(krnl.it_mp, iommu_table); process_iommu_table_match_process_at(krnl.prc_mp, krnl.it_mp, target); }
        found = krnl.it_mp.borrow_typed(iommu_table, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), Tracked(iommu_perm)).next_mapped_4k_from(cursor);
    }
    if same {
        proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
        let ghost refund_k = *krnl;
        let ghost refund_lctx = *lctx;
        let ghost refund_before = steps.view();
        proof {
            kill_step_pre_from_k(&refund_k, &refund_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Reclaim { flushed: true }, scope); kill_refund_pre_from_k(&refund_k, target, entry_thread.owning_container);
            krnl.cpu_arr.typed_lock_map_aligned_lock_id_at(lctx.cpu_lock_map(), lctx.thread_id(), cpu_id);
        }
        refund_unmap_4k_quota(krnl, thread_ptr, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_perm));
        proof {
            assert(krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view() =~= entry_thread.indirect_free_quota_pending_4k.view()) by { thread_perms_wf_at(krnl.thr_mp, thread_ptr); };
            kill_trace_from_refund(&*steps, refund_before, start, pre, kernel_k_to_kernel_u(refund_k), cpu_id, ctx, process_ptr, thread_ptr, target, KillStage::Reclaim { flushed: true },
                entry_thread.owning_container, scope);
            assert(pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable) == pagetable_c(refund_k.pt_mp, refund_k.pt_lower.view(), pagetable)) by {
                refund_k.pt_mp.typed_lock_map_aligned_write_at(refund_lctx.pagetable_lock_map(), refund_lctx.thread_id(), pagetable);
                pagetable_lower_backup_wf_at(refund_k.pt_mp, refund_k.pt_lower.view(), pagetable); pagetable_lower_backup_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
            };
        }
    }
    proof { iommu_table_perms_wf_at(krnl.it_mp, iommu_table); process_iommu_table_match_process_at(krnl.prc_mp, krnl.it_mp, target); }
}

/// Return the emptied target's quota to its container, unlock its tables, and make it a zombie.
pub(crate) fn kill_reclaim_return_quota_and_zombify(
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
        kill_reclaim_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Reclaim { flushed: true }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
            iommu_table, pagetable_perm, iommu_perm),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        target == chain[chain.len() - 1],
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).leaves_present(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && KERNEL_MEM_END_L4INDEX <= l4i && kernel_l4_end <= l4i ==> !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
        iommu_table is Some ==> old(krnl).it_mp.spec_index(iommu_table->Some_0).view().leaves_present(),
        iommu_table is Some ==> forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger old(krnl).it_mp.spec_index(iommu_table->Some_0).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> !old(krnl).it_mp.spec_index(iommu_table->Some_0).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
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
    kill_reclaim_return_quota(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, Ghost(chain), Tracked(chain_perms), Tracked(cpu_perm),
        Tracked(process_perm), Tracked(thread_perm), pagetable, iommu_table, Tracked(&pagetable_perm), Tracked(&iommu_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    kill_reclaim_unlock_table(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, Ghost(chain), Tracked(chain_perms), Tracked(cpu_perm),
        Tracked(process_perm), Tracked(thread_perm), pagetable, iommu_table, Tracked(pagetable_perm), Tracked(iommu_perm), Ghost(kernel_l4_end), Ghost(start), Ghost(pre),
        Ghost(scope), Ghost(ctx));
    kill_reclaim_zombify(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, Ghost(chain), Tracked(chain_perms), Tracked(cpu_perm),
        Tracked(process_perm), Tracked(thread_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
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
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable),
        iommu_table is Some ==> final(krnl).it_mp.spec_index(iommu_table->Some_0) == old(krnl).it_mp.spec_index(iommu_table->Some_0),
        final(krnl).prc_mp.spec_index(target).view().quota_4k == 0,
        final(krnl).prc_mp.spec_index(target).view().quota_2m == 0,
        final(krnl).prc_mp.spec_index(target).view().quota_1g == 0,
        final(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set,
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
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable),
        iommu_table is Some ==> final(krnl).it_mp.spec_index(iommu_table->Some_0) == old(krnl).it_mp.spec_index(iommu_table->Some_0),
        final(krnl).prc_mp.spec_index(target).view().quota_4k == if size is SZ4k { 0 } else { old(krnl).prc_mp.spec_index(target).view().quota_4k },
        final(krnl).prc_mp.spec_index(target).view().quota_2m == if size is SZ2m { 0 } else { old(krnl).prc_mp.spec_index(target).view().quota_2m },
        final(krnl).prc_mp.spec_index(target).view().quota_1g == if size is SZ1g { 0 } else { old(krnl).prc_mp.spec_index(target).view().quota_1g },
        final(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set,
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
    let ghost entry_k = *krnl;
    let ghost entry_lctx = *lctx;
    let ghost entry_steps = steps.view();
    let tracked target_perm = chain_perms.tracked_borrow(target);
    proof { krnl.cpu_arr.typed_lock_map_aligned_lock_id_at(lctx.cpu_lock_map(), lctx.thread_id(), cpu_id); }
    kill_reclaim_return_quota_under_lock(krnl, Tracked(&mut *lctx), target, Tracked(target_perm), size);
    let ghost returned_k = *krnl;
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(kill_scope_progress(scope, target, KillStage::Quota { returned: size })), Tracked(&*lctx), Tracked(thread_perm));
    proof {
        let pre_u = kernel_k_to_kernel_u(entry_k);
        let post_u = kernel_k_to_kernel_u(*krnl);
        container_process_wf_process_at(entry_k.ctn_mp, entry_k.prc_mp, target);
        kernel_process_quota_returned_implies_u_step(&entry_k, &returned_k, target, size);
        kernel_thread_syscall_progress_changed_implies_u_step(&returned_k, &*krnl, thread_ptr);
        kill_step_pre_from_k(&entry_k, &entry_lctx, cpu_id, process_ptr, thread_ptr, target, kill_process_quota_stage_before(size), scope);
        kill_reclaim_pre_from_k(&entry_k, &entry_lctx, cpu_id, thread_ptr, target, kill_process_quota_stage_before(size), pagetable, iommu_table);
        kill_quota_step_from_u(pre_u, kernel_k_to_kernel_u(returned_k), post_u, cpu_id, thread_ptr, target, size, scope);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        kill_trace_push(&*steps, entry_steps, start, pre, pre_u, post_u, cpu_id, ctx);
    }
}

/// Under the `size` quota lock of the `size` allocator of the target's container, move the target's whole `size` quota to
/// that allocator.
pub(crate) fn kill_reclaim_return_quota_under_lock(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, target: RwLockProcessPtr, Tracked(target_perm): Tracked<&LockPerm>, size: PageSize,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        typed_lock_map_majors_lt(old(lctx).cpu_lock_map(), CPU_LOCK_MAJOR_OFF),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        old(krnl).prc_mp.dom().contains(target),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), target, TypedLockMode::Write),
        target_perm.state() is WriteLock,
        target_perm.thread_id() == old(lctx).thread_id(),
        target_perm.lock_id() == old(krnl).prc_mp.spec_index(target).locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { prc_mp: final(krnl).prc_mp, allc_4k_mp: final(krnl).allc_4k_mp, allc_2m_mp: final(krnl).allc_2m_mp, allc_1g_mp: final(krnl).allc_1g_mp, ..*old(krnl) }),
        final(krnl).prc_mp.unchanged_except(&old(krnl).prc_mp, target),
        final(krnl).prc_mp.spec_index(target).view() == match size {
            PageSize::SZ4k => Process { quota_4k: 0, ..old(krnl).prc_mp.spec_index(target).view() },
            PageSize::SZ2m => Process { quota_2m: 0, ..old(krnl).prc_mp.spec_index(target).view() },
            PageSize::SZ1g => Process { quota_1g: 0, ..old(krnl).prc_mp.spec_index(target).view() },
        },
        final(krnl).prc_mp.spec_index(target).view_rodata() == old(krnl).prc_mp.spec_index(target).view_rodata(),
        final(krnl).prc_mp.spec_index(target).view_ghost() == old(krnl).prc_mp.spec_index(target).view_ghost(),
        final(krnl).prc_mp.spec_index(target).locking_thread() == old(krnl).prc_mp.spec_index(target).locking_thread(),
        final(krnl).prc_mp.spec_index(target).being_killed() == old(krnl).prc_mp.spec_index(target).being_killed(),
        final(krnl).prc_mp.spec_index(target).killer_info() == old(krnl).prc_mp.spec_index(target).killer_info(),
        ({
            let container = old(krnl).ctn_mp.spec_index(old(krnl).prc_mp.spec_index(target).view_rodata().view().owning_container).view_rodata().view();
            let process = old(krnl).prc_mp.spec_index(target).view();
            &&& forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_4k_mp.spec_index(a)]
                old(krnl).allc_4k_mp.dom().contains(a) && a != container.allocator_ptr_4k ==> final(krnl).allc_4k_mp.spec_index(a).quota.view().view() == old(krnl).allc_4k_mp.spec_index(a).quota.view().view()
            &&& forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_2m_mp.spec_index(a)]
                old(krnl).allc_2m_mp.dom().contains(a) && a != container.allocator_ptr_2m ==> final(krnl).allc_2m_mp.spec_index(a).quota.view().view() == old(krnl).allc_2m_mp.spec_index(a).quota.view().view()
            &&& forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_1g_mp.spec_index(a)]
                old(krnl).allc_1g_mp.dom().contains(a) && a != container.allocator_ptr_1g ==> final(krnl).allc_1g_mp.spec_index(a).quota.view().view() == old(krnl).allc_1g_mp.spec_index(a).quota.view().view()
            &&& final(krnl).allc_4k_mp.spec_index(container.allocator_ptr_4k).quota.view().view() as int
                == old(krnl).allc_4k_mp.spec_index(container.allocator_ptr_4k).quota.view().view() as int + if size is SZ4k { process.quota_4k as int } else { 0 }
            &&& final(krnl).allc_2m_mp.spec_index(container.allocator_ptr_2m).quota.view().view() as int
                == old(krnl).allc_2m_mp.spec_index(container.allocator_ptr_2m).quota.view().view() as int + if size is SZ2m { process.quota_2m as int } else { 0 }
            &&& final(krnl).allc_1g_mp.spec_index(container.allocator_ptr_1g).quota.view().view() as int
                == old(krnl).allc_1g_mp.spec_index(container.allocator_ptr_1g).quota.view().view() as int + if size is SZ1g { process.quota_1g as int } else { 0 }
        }),
{
    match size {
        PageSize::SZ4k => kill_reclaim_return_quota_4k_under_lock(krnl, Tracked(&mut *lctx), target, Tracked(target_perm)),
        PageSize::SZ2m => kill_reclaim_return_quota_2m_under_lock(krnl, Tracked(&mut *lctx), target, Tracked(target_perm)),
        PageSize::SZ1g => kill_reclaim_return_quota_1g_under_lock(krnl, Tracked(&mut *lctx), target, Tracked(target_perm)),
    }
}

/// Under the quota lock of the 4K allocator of the target's container, move the target's whole 4K quota to that allocator.
pub(crate) fn kill_reclaim_return_quota_4k_under_lock(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, target: RwLockProcessPtr, Tracked(target_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        typed_lock_map_majors_lt(old(lctx).cpu_lock_map(), CPU_LOCK_MAJOR_OFF),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        old(krnl).prc_mp.dom().contains(target),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), target, TypedLockMode::Write),
        target_perm.state() is WriteLock,
        target_perm.thread_id() == old(lctx).thread_id(),
        target_perm.lock_id() == old(krnl).prc_mp.spec_index(target).locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { prc_mp: final(krnl).prc_mp, allc_4k_mp: final(krnl).allc_4k_mp, ..*old(krnl) }),
        final(krnl).prc_mp.unchanged_except(&old(krnl).prc_mp, target),
        final(krnl).prc_mp.spec_index(target).view() == (Process { quota_4k: 0, ..old(krnl).prc_mp.spec_index(target).view() }),
        final(krnl).prc_mp.spec_index(target).view_rodata() == old(krnl).prc_mp.spec_index(target).view_rodata(),
        final(krnl).prc_mp.spec_index(target).view_ghost() == old(krnl).prc_mp.spec_index(target).view_ghost(),
        final(krnl).prc_mp.spec_index(target).locking_thread() == old(krnl).prc_mp.spec_index(target).locking_thread(),
        final(krnl).prc_mp.spec_index(target).being_killed() == old(krnl).prc_mp.spec_index(target).being_killed(),
        final(krnl).prc_mp.spec_index(target).killer_info() == old(krnl).prc_mp.spec_index(target).killer_info(),
        ({
            let allocator_ptr = old(krnl).ctn_mp.spec_index(old(krnl).prc_mp.spec_index(target).view_rodata().view().owning_container).view_rodata().view().allocator_ptr_4k;
            &&& forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_4k_mp.spec_index(a)]
                old(krnl).allc_4k_mp.dom().contains(a) && a != allocator_ptr ==> final(krnl).allc_4k_mp.spec_index(a).quota.view().view() == old(krnl).allc_4k_mp.spec_index(a).quota.view().view()
            &&& final(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.view().view() as int
                == old(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.view().view() as int + old(krnl).prc_mp.spec_index(target).view().quota_4k as int
        }),
{
    proof { process_perms_wf_map(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, target); }
    let container_ptr = krnl.prc_mp.borrow_rodata(target).borrow().owning_container;
    proof {
        container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, target);
        container_process_quota_sums_bounded(&*krnl, container_ptr, target);
        container_perms_wf_at(krnl.ctn_mp, container_ptr);
    }
    let allocator_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().allocator_ptr_4k;
    proof { assert(krnl.allc_4k_mp.dom().contains(allocator_ptr) && krnl.allc_4k_mp.spec_index(allocator_ptr).wf()) by {
        container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr); allocator_perms_wf_at(krnl.allc_4k_mp, allocator_ptr);
    }; }
    let Tracked(quota_perm) = krnl.wlock_allocator_quota_4k(allocator_ptr, Tracked(&mut *lctx));
    let ghost locked = *krnl;
    let process_quota = {
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
        assert(kill_quota_eof_transition_framing(locked, *krnl, target, allocator_ptr, PageSize::SZ4k)) by { reveal(kill_quota_eof_transition_framing); };
        kill_quota_eof(locked, *krnl, target, allocator_ptr, PageSize::SZ4k);
        assert(krnl.allc_4k_mp.spec_index(allocator_ptr).wf() && krnl.allc_4k_mp.spec_index(allocator_ptr).quota.inv()) by { allocator_perms_wf_at(krnl.allc_4k_mp, allocator_ptr); };
    }
    krnl.wunlock_allocator_quota_4k(allocator_ptr, Tracked(&mut *lctx), Tracked(quota_perm));
    proof { assert(lctx.allocator_quota_4k_lock_map() =~= old(lctx).allocator_quota_4k_lock_map()); }
}

/// Under the quota lock of the 2M allocator of the target's container, move the target's whole 2M quota to that allocator.
pub(crate) fn kill_reclaim_return_quota_2m_under_lock(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, target: RwLockProcessPtr, Tracked(target_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        typed_lock_map_majors_lt(old(lctx).cpu_lock_map(), CPU_LOCK_MAJOR_OFF),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        old(krnl).prc_mp.dom().contains(target),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), target, TypedLockMode::Write),
        target_perm.state() is WriteLock,
        target_perm.thread_id() == old(lctx).thread_id(),
        target_perm.lock_id() == old(krnl).prc_mp.spec_index(target).locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { prc_mp: final(krnl).prc_mp, allc_2m_mp: final(krnl).allc_2m_mp, ..*old(krnl) }),
        final(krnl).prc_mp.unchanged_except(&old(krnl).prc_mp, target),
        final(krnl).prc_mp.spec_index(target).view() == (Process { quota_2m: 0, ..old(krnl).prc_mp.spec_index(target).view() }),
        final(krnl).prc_mp.spec_index(target).view_rodata() == old(krnl).prc_mp.spec_index(target).view_rodata(),
        final(krnl).prc_mp.spec_index(target).view_ghost() == old(krnl).prc_mp.spec_index(target).view_ghost(),
        final(krnl).prc_mp.spec_index(target).locking_thread() == old(krnl).prc_mp.spec_index(target).locking_thread(),
        final(krnl).prc_mp.spec_index(target).being_killed() == old(krnl).prc_mp.spec_index(target).being_killed(),
        final(krnl).prc_mp.spec_index(target).killer_info() == old(krnl).prc_mp.spec_index(target).killer_info(),
        ({
            let allocator_ptr = old(krnl).ctn_mp.spec_index(old(krnl).prc_mp.spec_index(target).view_rodata().view().owning_container).view_rodata().view().allocator_ptr_2m;
            &&& forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_2m_mp.spec_index(a)]
                old(krnl).allc_2m_mp.dom().contains(a) && a != allocator_ptr ==> final(krnl).allc_2m_mp.spec_index(a).quota.view().view() == old(krnl).allc_2m_mp.spec_index(a).quota.view().view()
            &&& final(krnl).allc_2m_mp.spec_index(allocator_ptr).quota.view().view() as int
                == old(krnl).allc_2m_mp.spec_index(allocator_ptr).quota.view().view() as int + old(krnl).prc_mp.spec_index(target).view().quota_2m as int
        }),
{
    proof { process_perms_wf_map(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, target); }
    let container_ptr = krnl.prc_mp.borrow_rodata(target).borrow().owning_container;
    proof {
        container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, target);
        container_process_quota_sums_bounded(&*krnl, container_ptr, target);
        container_perms_wf_at(krnl.ctn_mp, container_ptr);
    }
    let allocator_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().allocator_ptr_2m;
    proof { assert(krnl.allc_2m_mp.dom().contains(allocator_ptr) && krnl.allc_2m_mp.spec_index(allocator_ptr).wf()) by {
        container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr); allocator_perms_wf_at(krnl.allc_2m_mp, allocator_ptr);
    }; }
    let Tracked(quota_perm) = krnl.wlock_allocator_quota_2m(allocator_ptr, Tracked(&mut *lctx));
    let ghost locked = *krnl;
    let process_quota = {
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
        assert(kill_quota_eof_transition_framing(locked, *krnl, target, allocator_ptr, PageSize::SZ2m)) by { reveal(kill_quota_eof_transition_framing); };
        kill_quota_eof(locked, *krnl, target, allocator_ptr, PageSize::SZ2m);
        assert(krnl.allc_2m_mp.spec_index(allocator_ptr).wf() && krnl.allc_2m_mp.spec_index(allocator_ptr).quota.inv()) by { allocator_perms_wf_at(krnl.allc_2m_mp, allocator_ptr); };
    }
    krnl.wunlock_allocator_quota_2m(allocator_ptr, Tracked(&mut *lctx), Tracked(quota_perm));
    proof { assert(lctx.allocator_quota_2m_lock_map() =~= old(lctx).allocator_quota_2m_lock_map()); }
}

/// Under the quota lock of the 1G allocator of the target's container, move the target's whole 1G quota to that allocator.
pub(crate) fn kill_reclaim_return_quota_1g_under_lock(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, target: RwLockProcessPtr, Tracked(target_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        typed_lock_map_majors_lt(old(lctx).cpu_lock_map(), CPU_LOCK_MAJOR_OFF),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        old(krnl).prc_mp.dom().contains(target),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), target, TypedLockMode::Write),
        target_perm.state() is WriteLock,
        target_perm.thread_id() == old(lctx).thread_id(),
        target_perm.lock_id() == old(krnl).prc_mp.spec_index(target).locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { prc_mp: final(krnl).prc_mp, allc_1g_mp: final(krnl).allc_1g_mp, ..*old(krnl) }),
        final(krnl).prc_mp.unchanged_except(&old(krnl).prc_mp, target),
        final(krnl).prc_mp.spec_index(target).view() == (Process { quota_1g: 0, ..old(krnl).prc_mp.spec_index(target).view() }),
        final(krnl).prc_mp.spec_index(target).view_rodata() == old(krnl).prc_mp.spec_index(target).view_rodata(),
        final(krnl).prc_mp.spec_index(target).view_ghost() == old(krnl).prc_mp.spec_index(target).view_ghost(),
        final(krnl).prc_mp.spec_index(target).locking_thread() == old(krnl).prc_mp.spec_index(target).locking_thread(),
        final(krnl).prc_mp.spec_index(target).being_killed() == old(krnl).prc_mp.spec_index(target).being_killed(),
        final(krnl).prc_mp.spec_index(target).killer_info() == old(krnl).prc_mp.spec_index(target).killer_info(),
        ({
            let allocator_ptr = old(krnl).ctn_mp.spec_index(old(krnl).prc_mp.spec_index(target).view_rodata().view().owning_container).view_rodata().view().allocator_ptr_1g;
            &&& forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_1g_mp.spec_index(a)]
                old(krnl).allc_1g_mp.dom().contains(a) && a != allocator_ptr ==> final(krnl).allc_1g_mp.spec_index(a).quota.view().view() == old(krnl).allc_1g_mp.spec_index(a).quota.view().view()
            &&& final(krnl).allc_1g_mp.spec_index(allocator_ptr).quota.view().view() as int
                == old(krnl).allc_1g_mp.spec_index(allocator_ptr).quota.view().view() as int + old(krnl).prc_mp.spec_index(target).view().quota_1g as int
        }),
{
    proof { process_perms_wf_map(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, target); }
    let container_ptr = krnl.prc_mp.borrow_rodata(target).borrow().owning_container;
    proof {
        container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, target);
        container_process_quota_sums_bounded(&*krnl, container_ptr, target);
        container_perms_wf_at(krnl.ctn_mp, container_ptr);
    }
    let allocator_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().allocator_ptr_1g;
    proof { assert(krnl.allc_1g_mp.dom().contains(allocator_ptr) && krnl.allc_1g_mp.spec_index(allocator_ptr).wf()) by {
        container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr); allocator_perms_wf_at(krnl.allc_1g_mp, allocator_ptr);
    }; }
    let Tracked(quota_perm) = krnl.wlock_allocator_quota_1g(allocator_ptr, Tracked(&mut *lctx));
    let ghost locked = *krnl;
    let process_quota = {
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
        assert(kill_quota_eof_transition_framing(locked, *krnl, target, allocator_ptr, PageSize::SZ1g)) by { reveal(kill_quota_eof_transition_framing); };
        kill_quota_eof(locked, *krnl, target, allocator_ptr, PageSize::SZ1g);
        assert(krnl.allc_1g_mp.spec_index(allocator_ptr).wf() && krnl.allc_1g_mp.spec_index(allocator_ptr).quota.inv()) by { allocator_perms_wf_at(krnl.allc_1g_mp, allocator_ptr); };
    }
    krnl.wunlock_allocator_quota_1g(allocator_ptr, Tracked(&mut *lctx), Tracked(quota_perm));
    proof { assert(lctx.allocator_quota_1g_lock_map() =~= old(lctx).allocator_quota_1g_lock_map()); }
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
        kill_reclaim_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Quota { returned: PageSize::SZ1g }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
            iommu_table, pagetable_perm, iommu_perm),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        target == chain[chain.len() - 1],
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == kernel_l4_end,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).leaves_present(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && KERNEL_MEM_END_L4INDEX <= l4i && kernel_l4_end <= l4i ==> !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
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
    let ghost unlock_before = steps.view();
    let ghost unlock_k = *krnl;
    let ghost unlock_lctx = *lctx;
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(kill_scope_progress(scope, target, KillStage::Zombie)), Tracked(&*lctx), Tracked(thread_perm));
    let ghost progressed = *krnl;
    proof {
        process_perms_wf_map(krnl.prc_mp);
        process_perms_wf_at(krnl.prc_mp, target);
        assert(pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom() =~= Set::<VAddr>::empty()) by {
            pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable); krnl.default_pagetable_wf_at(pagetable); broadcast use spec_va_4k_valid_index_roundtrip;
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
    krnl.wunlock_pagetable(pagetable, Tracked(&mut *lctx), Tracked(pagetable_perm));
    proof {
        let unlocked_k = *krnl;
        let before_u = kernel_k_to_kernel_u(unlock_k);
        kill_step_pre_from_k(&unlock_k, &unlock_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Quota { returned: PageSize::SZ1g }, scope);
        kill_reclaim_pre_from_k(&unlock_k, &unlock_lctx, cpu_id, thread_ptr, target, KillStage::Quota { returned: PageSize::SZ1g }, pagetable, iommu_table);
        kill_user_4k_unmapped_pre_from_k(&unlock_k, target);
        if iommu_table is Some { kill_iommu_unmapped_pre_from_k(&unlock_k, target); }
        kernel_process_tables_lock_state_and_progress_changed_implies_u_step(&unlock_k, &unlocked_k, &*lctx, target, pagetable, thread_ptr, false);
        kill_unlock_table_step_from_u(before_u, kernel_k_to_kernel_u(unlocked_k), cpu_id, thread_ptr, target, scope);
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
    let ghost entry_k = *krnl;
    let ghost entry_lctx = *lctx;
    let ghost entry_steps = steps.view();
    proof { process_perms_wf_at(krnl.prc_mp, target); }
    let (container_ptr, pcid) = {
        let target_ro = krnl.prc_mp.borrow_rodata(target).borrow();
        (target_ro.owning_container, target_ro.pcid)
    };
    proof {
        container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, target);
        if scope is Subtree { process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); }
        container_perms_wf_at(krnl.ctn_mp, container_ptr);
    }
    let pcid_allocator_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().pcid_allocator;
    proof {
        let cpu = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
        assert({
            &&& krnl.pcid_allc_mp.dom().contains(pcid_allocator_ptr)
            &&& krnl.pcid_allc_mp.spec_index(pcid_allocator_ptr).view().owning_container.view() == container_ptr
            &&& container_ptr == cpu.owning_container || krnl.pcid_allc_mp.spec_index(pcid_allocator_ptr).view().container_depth.view() > cpu.container_depth
        }) by { container_pcid_allocator_wf_container_at(krnl.ctn_mp, krnl.pcid_allc_mp, container_ptr); };
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
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(kill_scope_progress(scope, target, KillStage::Retire)), Tracked(&*lctx), Tracked(thread_perm));
    proof {
        let pre_u = kernel_k_to_kernel_u(entry_k);
        let post_u = kernel_k_to_kernel_u(*krnl);
        kernel_process_zombified_implies_u_step(&entry_k, &zombified_k, target, pcid_allocator_ptr);
        kernel_thread_syscall_progress_changed_implies_u_step(&zombified_k, &*krnl, thread_ptr);
        kill_step_pre_from_k(&entry_k, &entry_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Zombie, scope); kill_zombify_pre_from_k(&entry_k, target);
        kill_zombify_step_from_u(pre_u, kernel_k_to_kernel_u(zombified_k), post_u, cpu_id, thread_ptr, target, scope);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        kill_trace_push(&*steps, entry_steps, start, pre, pre_u, post_u, cpu_id, ctx);
    }
}
} // verus!
