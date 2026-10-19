use vstd::prelude::*;
use crate::*;
use super::syscall_kill_process_spec::*;
use super::syscall_kill_process_walk::*;
use super::syscall_kill_process_retire_pages_lock::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_retire_spec::*;

verus! {
/// With the pages and tables that `kill_retire_hold_tables` returned write-held, write-hold the root table pages `cr3` of
/// the empty zombie target's page table `pagetable` and `iommu_cr3` of its IOMMU table `iommu_table`, sorted by index, and
/// end the step, which the projection does not show. Returns the pages the retirement frees with the permissions of every
/// held page.
pub(crate) fn kill_retire_hold_roots(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, Tracked(page_perms): Tracked<Map<PageIndex, LockPerm>>,
    Tracked(pt_perm): Tracked<&LockPerm>, Tracked(it_perm): Tracked<&Option<LockPerm>>, pagetable: RwLockPageTableRoot, iommu_table: Option<RwLockPageTableRoot>, cr3: usize,
    iommu_cr3: Option<usize>, container_ptr: RwLockContainerPtr, Ghost(scope): Ghost<KillScope>,
) -> (ret: (ArrayVec<PageIndex, 5>, Tracked<Map<PageIndex, LockPerm>>))
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        scope == (KillScope::Subtree { process: process_ptr }),
        kill_retire_held_state(*old(krnl), *old(lctx), scope, process_ptr, thread_ptr, target, page_perms, *pt_perm, *it_perm),
        held_locks_order_below(old(krnl), old(lctx), PAGETABLE_PAGE_MAJOR),
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        kill_chain_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Retire, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
        kill_retire_tables_emptied(*old(krnl), target),
        0 < chain.len(),
        target == chain[chain.len() - 1],
        old(krnl).prc_mp.spec_index(target).view().zombie,
        old(krnl).prc_mp.spec_index(target).view().pagetable == pagetable,
        old(krnl).prc_mp.spec_index(target).view().iommu_table == iommu_table,
        old(krnl).prc_mp.spec_index(target).view_rodata().view().cr3 == cr3,
        old(krnl).prc_mp.spec_index(target).view_rodata().view().iommu_cr3 == iommu_cr3,
        old(krnl).prc_mp.spec_index(target).view_rodata().view().owning_container == container_ptr,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view() == old(steps).view(),
        killer_held_context_except_tables(*final(krnl), *final(lctx), process_ptr, thread_ptr, kill_scope_containers(scope, *final(lctx))),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).page_lock_map().dom() == ret.0.view().to_set(),
        held_locks_order_below(final(krnl), final(lctx), ALLOCATOR_CACHE_MAJOR),
        final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        kill_chain_state(*final(krnl), *final(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Retire, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
        final(krnl).prc_mp.spec_index(target) == old(krnl).prc_mp.spec_index(target),
        final(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set,
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).pt_mp.spec_index(pagetable) == old(krnl).pt_mp.spec_index(pagetable),
        iommu_table is Some ==> final(krnl).it_mp.dom().contains(iommu_table->Some_0) && final(krnl).it_mp.spec_index(iommu_table->Some_0) == old(krnl).it_mp.spec_index(iommu_table->Some_0),
        ret.0.wf(),
        ret.0.view() == kill_retire_pages(*final(krnl), target),
        ret.0.view().no_duplicates(),
        index_valid(NUM_PAGES, ret.0.view()[0]),
        final(krnl).pg_arr.spec_index(ret.0.view()[0]).view().view().owning_container == container_ptr,
        ret.1.view().dom() == ret.0.view().to_set(),
        forall|p: PageIndex| #![trigger ret.1.view().dom().contains(p)] ret.1.view().dom().contains(p) ==> {
            &&& typed_lock_map_contains_mode(final(lctx).page_lock_map(), p, TypedLockMode::Write)
            &&& ret.1.view()[p].state() is WriteLock
            &&& ret.1.view()[p].thread_id() == final(lctx).thread_id()
            &&& ret.1.view()[p].lock_id() == final(krnl).pg_arr.spec_index(p).view().locking_thread()->Write_lock_id
        },
{
    proof {
        process_perms_wf_map(krnl.prc_mp);
        process_perms_wf_at(krnl.prc_mp, target);
        process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, target); process_iommu_table_match_process_at(krnl.prc_mp, krnl.it_mp, target);
        let pt = krnl.pt_mp.spec_index(pagetable).view();
        pagetable_perms_wf_at(krnl.pt_mp, pagetable);
        assert(page_ptr_valid(target) && krnl.pg_arr.spec_index(page_ptr2page_index(target)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsProcess })) by { process_pages_wf_process_entry_at(krnl.pg_arr, krnl.prc_mp, target); };
        pagetable_pages_wf_root_entry_at(krnl.pt_mp, krnl.pg_arr, pagetable);
        assert(pt.page_closure().contains(pt.cr3)) by { reveal(PageTable::wf_l4); };
        pagetable_pages_wf_closure_entry_at(krnl.pt_mp, krnl.pg_arr, pagetable, pt.cr3);
        if let Some(it) = iommu_table {
            let it_view = krnl.it_mp.spec_index(it).view();
            iommu_table_perms_wf_at(krnl.it_mp, it);
            pagetable_pages_wf_root_entry_at(krnl.it_mp, krnl.pg_arr, it);
            assert(it_view.page_closure().contains(it_view.cr3)) by { reveal(PageTable::wf_l4); };
            pagetable_pages_wf_closure_entry_at(krnl.it_mp, krnl.pg_arr, it, it_view.cr3);
        }
    }
    let mut pages: ArrayVec<PageIndex, 5> = ArrayVec::new();
    let mut roots: ArrayVec<PageIndex, 5> = ArrayVec::new();
    pages.push(page_ptr2page_index(target));
    pages.push(page_ptr2page_index(pagetable));
    pages.push(page_ptr2page_index(cr3));
    roots.push(page_ptr2page_index(cr3));
    if let Some(it) = iommu_table {
        let it_root = page_ptr2page_index(iommu_cr3.unwrap());
        pages.push(page_ptr2page_index(it));
        pages.push(it_root);
        roots.push(it_root);
    }
    proof { assert(pages.view() =~= kill_retire_pages(*krnl, target)); }
    let sorted_roots = kill_retire_sort_pages(&roots);
    let Tracked(page_lock_perms) = wlock_kill_retire_pages(krnl, &sorted_roots, Ghost(PAGETABLE_PAGE_MAJOR), Tracked(&mut *lctx), Tracked(page_perms));
    proof {
        assert(lctx.page_lock_map().dom() =~= pages.view().to_set()) by { broadcast use vstd::seq_lib::lemma_seq_contains_after_push; };
        assert(index_valid(NUM_PAGES, pages.view()[0]) && lctx.page_lock_map().dom().contains(pages.view()[0])
            && krnl.pg_arr.spec_index(pages.view()[0]).view().view().owning_container == container_ptr) by { page_ptr_roundtrip(); process_kernel_pages_owner_wf_at(krnl.pg_arr, krnl.prc_mp, krnl.pt_mp, krnl.it_mp, pages.view()[0]); };
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        kernel_lock_states_unchanged_except_tables_of_implies_u_eq(&steps.snapshot_k(), &*krnl, Some(target));
        krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
    }
    (pages, Tracked(page_lock_perms))
}
} // verus!
