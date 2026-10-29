use vstd::prelude::*;
use crate::*;
use super::syscall_kill_process_spec::*;
use super::syscall_kill_process_trace::*;
use super::syscall_kill_process_walk::*;
use super::syscall_kill_process_retire_pages::*;
use super::syscall_kill_process_retire_pages_lock::*;
use super::syscall_kill_process_retire_roots::kill_retire_hold_roots;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_retire_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_retire_eof::*;

verus! {
/// Retire the empty zombie target, which owns no PCI function, and walk its parent again: write-hold its process page, its
/// tables' object pages, and its tables, unlink their structure pages, then retire the process with its tables and their
/// root pages.
pub(crate) fn kill_retire_target(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&mut Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
    Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
) -> (parent: RwLockProcessPtr)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        kill_walk_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, None, KillStage::Retire, *cpu_perm, *process_perm, *thread_perm, *old(chain_perms)),
        0 < chain.len(),
        target == chain[chain.len() - 1],
        old(krnl).prc_mp.spec_index(target).view().zombie,
        old(krnl).prc_mp.spec_index(target).view().children.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
        scope is Subtree || 1 < chain.len(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_walk_state(*final(krnl), *final(lctx), cpu_id, scope, process_ptr, thread_ptr, chain.drop_last(), None, KillStage::Walk, *cpu_perm, *process_perm, *thread_perm,
            *final(chain_perms)),
        parent == if chain.len() == 1 { process_ptr } else { chain[chain.len() - 2] },
        scope is Subtree ==> final(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set.view() == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set.view().remove(target),
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
            &&& final(krnl).ctn_mp.dom().contains(c)
            &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
            &&& final(krnl).ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
            &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
            &&& c != scope->Container_container ==> final(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes
            &&& final(krnl).ctn_mp.spec_index(c).view().children == old(krnl).ctn_mp.spec_index(c).view().children
        },
        scope is Container ==> final(krnl).ctn_mp.spec_index(scope->Container_container).view_ghost().owned_processes.view() == old(krnl).ctn_mp.spec_index(scope->Container_container).view_ghost().owned_processes.view().remove(target),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
{
    proof { process_perms_wf_map(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, target); }
    let (pagetable, iommu_table) = {
        let tracked target_perm = chain_perms.tracked_borrow(target);
        let process = krnl.prc_mp.borrow_typed(target, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(target_perm));
        (process.pagetable, process.iommu_table)
    };
    let (_, Tracked(page_perms), Tracked(pt_perm), Tracked(it_perm)) = kill_retire_hold_tables(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr,
        thread_ptr, target, Ghost(chain), Tracked(&*chain_perms), Tracked(cpu_perm), Tracked(process_perm), Tracked(thread_perm), pagetable, iommu_table, Ghost(scope));
    kill_retire_structure_pages(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, Ghost(chain), Tracked(&*chain_perms), Tracked(cpu_perm),
        Tracked(process_perm), Tracked(thread_perm), Tracked(&page_perms), Tracked(&pt_perm), Tracked(&it_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    kill_retire_process(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, Ghost(chain), Tracked(&mut *chain_perms), Tracked(cpu_perm),
        Tracked(process_perm), Tracked(thread_perm), Tracked(page_perms), Tracked(pt_perm), Tracked(it_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx))
}

/// Write-hold the empty zombie target's process page and its tables' object pages, sorted by index, then its page table
/// `pagetable` and its IOMMU table `iommu_table`, and end the step, which the projection does not show. Returns those pages
/// with the permissions of the pages and tables.
pub(crate) fn kill_retire_hold_tables(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, pagetable: RwLockPageTableRoot,
    iommu_table: Option<RwLockPageTableRoot>, Ghost(scope): Ghost<KillScope>,
) -> (ret: (ArrayVec<PageIndex, 5>, Tracked<Map<PageIndex, LockPerm>>, Tracked<LockPerm>, Tracked<Option<LockPerm>>))
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        kill_walk_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, None, KillStage::Retire, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
        0 < chain.len(),
        target == chain[chain.len() - 1],
        old(krnl).prc_mp.spec_index(target).view().zombie,
        old(krnl).prc_mp.spec_index(target).view().pagetable == pagetable,
        old(krnl).prc_mp.spec_index(target).view().iommu_table == iommu_table,
        old(krnl).prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view() == old(steps).view(),
        kill_retire_held_state(*final(krnl), *final(lctx), process_ptr, thread_ptr, target, ret.1.view(), ret.2.view(), ret.3.view()),
        held_locks_order_below(final(krnl), final(lctx), PAGE_TABLE_LOCK_MAJOR),
        final(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        kill_chain_state(*final(krnl), *final(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Retire, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
        final(krnl).prc_mp.spec_index(target) == old(krnl).prc_mp.spec_index(target),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).leaves_present(),
        iommu_table is Some ==> final(krnl).it_mp.spec_index(iommu_table->Some_0).view().leaves_present(),
        ret.0.wf(),
        0 < ret.0.view().len(),
        ret.0.view().no_duplicates(),
        ret.0.view().to_set() == kill_retire_held_pages(*final(krnl), target),
        forall|k: int| #![trigger ret.0.view()[k]] 0 <= k < ret.0.view().len() ==> index_valid(NUM_PAGES, ret.0.view()[k]),
        final(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set,
        scope is Container ==> final(krnl).ctn_mp.spec_index(scope->Container_container) == old(krnl).ctn_mp.spec_index(scope->Container_container),
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
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
{
    proof {
        process_perms_wf_at(krnl.prc_mp, target);
        process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, target); process_iommu_table_match_process_at(krnl.prc_mp, krnl.it_mp, target);
        process_pages_wf_process_entry_at(krnl.pg_arr, krnl.prc_mp, target);
        pagetable_pages_wf_root_entry_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pagetable);
        if let Some(it) = iommu_table { iommu_table_pages_wf_root_entry_at(krnl.it_mp, krnl.pg_arr, it); }
    }
    let mut held: ArrayVec<PageIndex, 5> = ArrayVec::new();
    held.push(page_ptr2page_index(target));
    held.push(page_ptr2page_index(pagetable));
    if let Some(it) = iommu_table { held.push(page_ptr2page_index(it)); }
    let sorted = kill_retire_sort_pages(&held);
    let Tracked(page_perms) = wlock_kill_retire_pages(krnl, &sorted, Ghost(ALLOCATED_PAGE_MAJOR), Tracked(&mut *lctx), Tracked(Map::<PageIndex, LockPerm>::tracked_empty()));
    let Tracked(pt_perm) = krnl.wlock_pagetable(pagetable, Tracked(&mut *lctx));
    let Tracked(it_perm) = match iommu_table {
        Some(it) => {
            let Tracked(perm) = krnl.wlock_iommu_table(it, Tracked(&mut *lctx));
            Tracked(Some(perm))
        },
        None => Tracked(None),
    };
    proof {
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        kernel_lock_states_unchanged_except_tables_of_implies_u_eq(&steps.snapshot_k(), &*krnl, Some(target));
        assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
        krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
        assert(held.view().to_set() =~= kill_retire_held_pages(*krnl, target)) by { broadcast use vstd::seq_lib::lemma_seq_contains_after_push; };
        assert(lctx.page_lock_map().dom() =~= held.view().to_set() && lctx.pagetable_lock_map().dom() =~= set![pagetable]
            && lctx.iommu_table_lock_map().dom() =~= match iommu_table { Some(it) => set![it], None => Set::<RwLockPageTableRoot>::empty() });
    }
    (held, Tracked(page_perms), Tracked(pt_perm), Tracked(it_perm))
}

/// Retire the empty zombie target in one step once the pages that `kill_retire_hold_tables` returned and its tables, which
/// hold only their root tables, are write-held: take its tables' root pages, the 4K allocator cache on `cpu_id` of its
/// container (drained first when it lacks room for the pages), and that allocator's quota; then the process leaves its
/// parent, its ancestors' subtrees, and its container, its tables leave their maps, its pages return to the cache with
/// their quota, and the killer walks the parent again.
pub(crate) fn kill_retire_process(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&mut Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, Tracked(page_perms): Tracked<Map<PageIndex, LockPerm>>,
    Tracked(pt_perm): Tracked<LockPerm>, Tracked(it_perm): Tracked<Option<LockPerm>>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
) -> (parent: RwLockProcessPtr)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        kill_retire_held_state(*old(krnl), *old(lctx), process_ptr, thread_ptr, target, page_perms, pt_perm, it_perm),
        held_locks_order_below(old(krnl), old(lctx), PAGETABLE_PAGE_MAJOR),
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        kill_chain_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Retire, *cpu_perm, *process_perm, *thread_perm, *old(chain_perms)),
        kill_retire_tables_emptied(*old(krnl), target),
        0 < chain.len(),
        target == chain[chain.len() - 1],
        old(krnl).prc_mp.spec_index(target).view().zombie,
        old(krnl).prc_mp.spec_index(target).view().children.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
        scope is Subtree || 1 < chain.len(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_walk_state(*final(krnl), *final(lctx), cpu_id, scope, process_ptr, thread_ptr, chain.drop_last(), None, KillStage::Walk, *cpu_perm, *process_perm, *thread_perm,
            *final(chain_perms)),
        parent == if chain.len() == 1 { process_ptr } else { chain[chain.len() - 2] },
        scope is Subtree ==> final(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set.view() == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set.view().remove(target),
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
            &&& final(krnl).ctn_mp.dom().contains(c)
            &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
            &&& final(krnl).ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
            &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
            &&& c != scope->Container_container ==> final(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes
            &&& final(krnl).ctn_mp.spec_index(c).view().children == old(krnl).ctn_mp.spec_index(c).view().children
        },
        scope is Container ==> final(krnl).ctn_mp.spec_index(scope->Container_container).view_ghost().owned_processes.view() == old(krnl).ctn_mp.spec_index(scope->Container_container).view_ghost().owned_processes.view().remove(target),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
{
    hide(Seq::no_duplicates);
    proof {
        process_perms_wf_map(krnl.prc_mp);
        process_perms_wf_at(krnl.prc_mp, target);
        container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, process_ptr);
        if scope is Subtree {
            assert(krnl.prc_mp.spec_index(target).view_ghost().uppertree_seq.view().contains(process_ptr)) by {
                let owner = krnl.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container;
                let tree = krnl.ctn_mp.spec_index(owner).view_ghost().owned_processes.view();
                let root = krnl.ctn_mp.spec_index(owner).view().root_process;
                per_container_process_tree_wf_at(krnl.ctn_mp, krnl.prc_mp, owner); process_subtree_set_wf_at(root, tree, krnl.prc_mp, process_ptr, target);
            };
        }
    }
    let (pagetable, iommu_table) = {
        let tracked target_perm = chain_perms.tracked_borrow(target);
        let process = krnl.prc_mp.borrow_typed(target, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(target_perm));
        (process.pagetable, process.iommu_table)
    };
    let (container_ptr, parent, cr3, iommu_cr3) = {
        let target_ro = krnl.prc_mp.borrow_rodata(target).borrow();
        (target_ro.owning_container, target_ro.parent, target_ro.cr3, target_ro.iommu_cr3)
    };
    let (pages, Tracked(page_lock_perms)) = kill_retire_hold_roots(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, Ghost(chain),
        Tracked(&*chain_perms), Tracked(cpu_perm), Tracked(process_perm), Tracked(thread_perm), Tracked(page_perms), Tracked(&pt_perm), Tracked(&it_perm), pagetable, iommu_table, cr3,
        iommu_cr3, container_ptr, Ghost(scope));
    let tracked target_perm = chain_perms.tracked_remove(target);
    let tracked parent_perm = if chain.len() == 1 { process_perm } else { chain_perms.tracked_borrow(chain[chain.len() - 2]) };
    let parent = parent.unwrap();
    proof { container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, target); container_perms_wf_at(krnl.ctn_mp, container_ptr); }
    let allocator_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().allocator_ptr_4k;
    proof {
        assert(krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end == KERNEL_MEM_END_L4INDEX) by { krnl.default_pagetable_wf_at(pagetable); };
        container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr);
        assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
    }
    let Tracked(cache_lock_perm) = kill_retire_lock_cache(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), allocator_ptr, cpu_id, pages.len(), Ghost(pages.view()[0]));
    let ghost base = steps.snapshot_k();
    let ghost base_lctx = *lctx;
    proof {
        lemma_container_allocator_4k_quota_bounded(&*krnl, container_ptr); allocator_perms_wf_at(krnl.allc_4k_mp, allocator_ptr);
        assert(pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable)) by {
            old(krnl).pt_mp.typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable);
            pagetable_lower_backup_wf_at(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable); pagetable_lower_backup_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        };
    }
    let Tracked(quota_lock_perm) = krnl.wlock_allocator_quota_4k(allocator_ptr, Tracked(&mut *lctx));
    kill_retire_commit(krnl, Tracked(&mut *lctx), cpu_id, target, parent, container_ptr, allocator_ptr, pagetable, iommu_table, &pages, Tracked(target_perm), Tracked(parent_perm),
        Tracked(page_lock_perms), Tracked(pt_perm), Tracked(it_perm), Tracked(cache_lock_perm), Tracked(quota_lock_perm), Ghost(base));
    kill_retire_end_step(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, parent, container_ptr, allocator_ptr, Tracked(thread_perm),
        Ghost(base), Ghost(base_lctx), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    parent
}

/// End the step that retired the empty zombie `target` from `base`, which the killer `thread_ptr` on `cpu_id` began holding
/// `base_lctx`: record the killer's walk to the target's parent `parent_ptr` and pass the step boundary, which keeps the
/// held processes and containers, the cpu, and the killer.
pub(crate) fn kill_retire_end_step(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, parent_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr,
    Tracked(thread_perm): Tracked<&LockPerm>, Ghost(base): Ghost<KernelK>, Ghost(base_lctx): Ghost<LocalContext>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
    Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        base.inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        old(steps).snapshot_k() == base,
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_perm.state() is WriteLock,
        thread_perm.thread_id() == old(lctx).thread_id(),
        thread_perm.lock_id() == base.thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        typed_lock_maps_aligned(&base, &base_lctx),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(base_lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(base_lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(base_lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(base_lctx.process_lock_map(), target, TypedLockMode::Write),
        base.thr_mp.dom().contains(thread_ptr),
        base.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        base.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        base.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_scope_progress(scope, target, KillStage::Retire),
        scope matches KillScope::Container { container } ==> base.ctn_mp.dom().contains(container) && typed_lock_map_contains_mode(base_lctx.container_lock_map(), container, TypedLockMode::Write),
        scope is Subtree ==> container_ptr == base.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        scope matches KillScope::Container { container } ==> container_ptr == container
            && base.ctn_mp.spec_index(container).view_ghost().uppertree_seq.view().contains(base.cpu_arr.spec_index(cpu_id).view().view().view().owning_container),
        base.prc_mp.dom().contains(target),
        base.prc_mp.spec_index(target).being_killed(),
        base.prc_mp.spec_index(target).view().zombie,
        base.prc_mp.spec_index(target).view().children.view().len() == 0,
        base.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        base.prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
        base.prc_mp.spec_index(target).view_rodata().view().parent == Some(parent_ptr),
        base.prc_mp.spec_index(target).view_ghost().uppertree_seq.view().contains(parent_ptr),
        base.prc_mp.spec_index(target).view_rodata().view().owning_container == container_ptr,
        base.ctn_mp.dom().contains(container_ptr),
        base.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        *old(krnl) == (KernelK { prc_mp: old(krnl).prc_mp, ctn_mp: old(krnl).ctn_mp, pt_mp: old(krnl).pt_mp, pt_lower: old(krnl).pt_lower, it_mp: old(krnl).it_mp,
            pg_arr: old(krnl).pg_arr, allc_4k_mp: old(krnl).allc_4k_mp, ..base }),
        old(krnl).prc_mp.dom() == base.prc_mp.dom().remove(target),
        forall|p: RwLockProcessPtr| #![trigger old(krnl).prc_mp.spec_index(p)] old(krnl).prc_mp.dom().contains(p) ==> {
            let old_p = base.prc_mp.spec_index(p);
            let new_p = old(krnl).prc_mp.spec_index(p);
            &&& new_p.view() == if p == parent_ptr { Process { children: new_p.view().children, ..old_p.view() } } else { old_p.view() }
            &&& new_p.view_ghost() == if base.prc_mp.spec_index(target).view_ghost().uppertree_seq.view().contains(p) {
                ProcessGhost { subtree_set: Ghost(old_p.view_ghost().subtree_set.view().remove(target)), ..old_p.view_ghost() }
            } else { old_p.view_ghost() }
            &&& new_p.view_rodata() == old_p.view_rodata()
            &&& new_p.locking_thread() == old_p.locking_thread()
            &&& new_p.being_killed() == old_p.being_killed()
        },
        old(krnl).prc_mp.spec_index(parent_ptr).view().children.view() == base.prc_mp.spec_index(parent_ptr).view().children.view().remove_value(target),
        old(krnl).ctn_mp.dom() == base.ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger old(krnl).ctn_mp.spec_index(c)] base.ctn_mp.dom().contains(c) && c != container_ptr ==> old(krnl).ctn_mp.spec_index(c) == base.ctn_mp.spec_index(c),
        old(krnl).ctn_mp.spec_index(container_ptr).view() == base.ctn_mp.spec_index(container_ptr).view(),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata() == base.ctn_mp.spec_index(container_ptr).view_rodata(),
        old(krnl).ctn_mp.spec_index(container_ptr).view_ghost() == (ContainerGhost {
            owned_processes: Ghost(base.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().remove(target)), ..base.ctn_mp.spec_index(container_ptr).view_ghost() }),
        old(krnl).ctn_mp.spec_index(container_ptr).locking_thread() == base.ctn_mp.spec_index(container_ptr).locking_thread(),
        old(krnl).ctn_mp.spec_index(container_ptr).control() == base.ctn_mp.spec_index(container_ptr).control(),
        forall|a: RwLockPageAllocatorPtr| #![trigger old(krnl).allc_4k_mp.spec_index(a)]
            base.allc_4k_mp.dom().contains(a) && a != allocator_ptr ==> old(krnl).allc_4k_mp.spec_index(a).quota.view() == base.allc_4k_mp.spec_index(a).quota.view(),
        base.allc_4k_mp.spec_index(allocator_ptr).quota.view().view() < old(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.view().view(),
        old(krnl).pt_mp.dom() == base.pt_mp.dom().remove(base.prc_mp.spec_index(target).view().pagetable),
        forall|t: RwLockPageTableRoot| #![trigger old(krnl).pt_mp.spec_index(t)]
            old(krnl).pt_mp.dom().contains(t) ==> old(krnl).pt_mp.spec_index(t) == base.pt_mp.spec_index(t) && old(krnl).pt_lower.view().spec_index(t) == base.pt_lower.view().spec_index(t),
        old(krnl).it_mp.dom() == match base.prc_mp.spec_index(target).view().iommu_table { Some(it) => base.it_mp.dom().remove(it), None => base.it_mp.dom() },
        forall|t: RwLockPageTableRoot| #![trigger old(krnl).it_mp.spec_index(t)] old(krnl).it_mp.dom().contains(t) ==> old(krnl).it_mp.spec_index(t) == base.it_mp.spec_index(t),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().kernel_call_perm() is None,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|b: Seq<KernelStep>| kernel_steps_prefix_unchanged(b, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(b, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: Ghost(kill_scope_progress(scope, parent_ptr, KillStage::Walk)), ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
{
    let ghost retired = *krnl;
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(kill_scope_progress(scope, parent_ptr, KillStage::Walk)), Tracked(&*lctx), Tracked(thread_perm));
    proof {
        let pre_u = kernel_k_to_kernel_u(base);
        let post_u = kernel_k_to_kernel_u(*krnl);
        let before = steps.view();
        kill_step_pre_from_k(&base, &base_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Retire, scope); kill_retire_pre_from_k(&base, target, parent_ptr);
        kernel_zombie_process_retired_implies_u_step(&base, &retired, target, parent_ptr, container_ptr, allocator_ptr);
        kernel_thread_syscall_progress_changed_implies_u_step(&retired, &*krnl, thread_ptr);
        kill_retire_step_from_u(pre_u, kernel_k_to_kernel_u(retired), post_u, cpu_id, thread_ptr, target, parent_ptr, retired.allc_4k_mp.spec_index(allocator_ptr).quota.view().view(), scope);
        assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        kill_trace_push(&*steps, before, start, pre, pre_u, post_u, cpu_id, ctx);
    }
}

/// With the zombie target's pages, tables, and its container's 4K allocator cache on `cpu_id` and quota write-held,
/// retire the target: its tables leave their maps, it leaves its parent, its ancestors' subtrees, and its container,
/// its pages return to the cache with their quota, and those locks are released. The caller ends the step.
pub(crate) fn kill_retire_commit(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, target: RwLockProcessPtr, parent_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr,
    allocator_ptr: RwLockPageAllocatorPtr, pagetable: RwLockPageTableRoot, iommu_table: Option<RwLockPageTableRoot>, pages: &ArrayVec<PageIndex, 5>,
    Tracked(target_perm): Tracked<LockPerm>, Tracked(parent_perm): Tracked<&LockPerm>, Tracked(page_lock_perms): Tracked<Map<PageIndex, LockPerm>>,
    Tracked(pt_lock_perm): Tracked<LockPerm>, Tracked(it_lock_perm): Tracked<Option<LockPerm>>, Tracked(cache_lock_perm): Tracked<LockPerm>,
    Tracked(quota_lock_perm): Tracked<LockPerm>, Ghost(base): Ghost<KernelK>,
)
    requires
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(krnl).inv(),
        base.inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).prc_mp.dom().contains(target),
        old(krnl).prc_mp.spec_index(target).being_killed(),
        old(krnl).prc_mp.spec_index(target).view().zombie,
        old(krnl).prc_mp.spec_index(target).view().children.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
        old(krnl).prc_mp.spec_index(target).view_rodata().view().parent == Some(parent_ptr),
        old(krnl).prc_mp.spec_index(target).view_rodata().view().owning_container == container_ptr,
        old(krnl).prc_mp.spec_index(target).view().pagetable == pagetable,
        old(krnl).prc_mp.spec_index(target).view().iommu_table == iommu_table,
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), target, TypedLockMode::Write),
        target_perm.state() is WriteLock,
        target_perm.thread_id() == old(lctx).thread_id(),
        target_perm.lock_id() == old(krnl).prc_mp.spec_index(target).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(parent_ptr),
        parent_ptr != target,
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), parent_ptr, TypedLockMode::Write),
        parent_perm.state() is WriteLock,
        parent_perm.thread_id() == old(lctx).thread_id(),
        parent_perm.lock_id() == old(krnl).prc_mp.spec_index(parent_ptr).locking_thread()->Write_lock_id,
        old(lctx).pagetable_lock_map().dom() == set![pagetable],
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pt_lock_perm.state() is WriteLock,
        pt_lock_perm.thread_id() == old(lctx).thread_id(),
        pt_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        ({
            let pt = pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            &&& pt.page_closure() =~= set![pt.cr3()]
            &&& pt.mapping_4k().dom() =~= Set::<VAddr>::empty()
            &&& pt.mapping_2m().dom() =~= Set::<VAddr>::empty()
            &&& pt.mapping_1g().dom() =~= Set::<VAddr>::empty()
        }),
        old(lctx).iommu_table_lock_map().dom() == match iommu_table { Some(it) => set![it], None => Set::<RwLockPageTableRoot>::empty() },
        it_lock_perm is Some == iommu_table is Some,
        iommu_table is Some ==> {
            let it = old(krnl).it_mp.spec_index(iommu_table->Some_0);
            &&& typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table->Some_0, TypedLockMode::Write)
            &&& it_lock_perm->Some_0.state() is WriteLock
            &&& it_lock_perm->Some_0.thread_id() == old(lctx).thread_id()
            &&& it_lock_perm->Some_0.lock_id() == it.locking_thread()->Write_lock_id
            &&& it.view().page_closure() =~= set![it.view().cr3]
            &&& it.view().mapping_4k().dom() =~= Set::<VAddr>::empty()
            &&& it.view().mapping_2m().dom() =~= Set::<VAddr>::empty()
            &&& it.view().mapping_1g().dom() =~= Set::<VAddr>::empty()
        },
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        old(krnl).allc_4k_mp.dom().contains(allocator_ptr),
        old(lctx).allocator_cache_4k_lock_map().dom() == set![(allocator_ptr, cpu_id)],
        typed_lock_map_contains_mode(old(lctx).allocator_cache_4k_lock_map(), (allocator_ptr, cpu_id), TypedLockMode::Write),
        forall|d: RwLockProcessPtr| #![trigger old(lctx).process_lock_map().dom().contains(d)] old(lctx).process_lock_map().dom().contains(d) && old(krnl).prc_mp.spec_index(d).killer_info() is Some
            ==> old(krnl).prc_mp.spec_index(d).killer_info()->Some_0.process != target && old(krnl).prc_mp.spec_index(d).view_rodata().view().owning_container == container_ptr,
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) && old(krnl).ctn_mp.spec_index(c).killer_info() is Some
            ==> old(krnl).ctn_mp.spec_index(c).killer_info()->Some_0.process != target,
        cache_lock_perm.state() is WriteLock,
        cache_lock_perm.thread_id() == old(lctx).thread_id(),
        cache_lock_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().len() + pages.view().len() <= ALLOCATOR_MAX_WATERMARK,
        old(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.view().value <= old(krnl).allc_4k_mp.spec_index(allocator_ptr).total_free_pages.view(),
        old(krnl).allc_4k_mp.spec_index(allocator_ptr).total_free_pages.view() <= NUM_PAGES * 4096 + NUM_CPUS * ALLOCATOR_MAX_WATERMARK,
        old(lctx).allocator_quota_4k_lock_map().dom() == set![allocator_ptr],
        typed_lock_map_contains_mode(old(lctx).allocator_quota_4k_lock_map(), allocator_ptr, TypedLockMode::Write),
        quota_lock_perm.state() is WriteLock,
        quota_lock_perm.thread_id() == old(lctx).thread_id(),
        quota_lock_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.locking_thread()->Write_lock_id,
        old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        pages.wf(),
        pages.view() == kill_retire_pages(*old(krnl), target),
        pages.view().no_duplicates(),
        old(lctx).page_lock_map().dom() == pages.view().to_set(),
        page_lock_perms.dom() == pages.view().to_set(),
        forall|p: PageIndex| #![trigger page_lock_perms.dom().contains(p)] page_lock_perms.dom().contains(p) ==> {
            &&& typed_lock_map_contains_mode(old(lctx).page_lock_map(), p, TypedLockMode::Write)
            &&& page_lock_perms[p].state() is WriteLock
            &&& page_lock_perms[p].thread_id() == old(lctx).thread_id()
            &&& page_lock_perms[p].lock_id() == old(krnl).pg_arr.spec_index(p).view().locking_thread()->Write_lock_id
        },
        *old(krnl) == (KernelK { pg_arr: old(krnl).pg_arr, pt_mp: old(krnl).pt_mp, it_mp: old(krnl).it_mp, allc_4k_mp: old(krnl).allc_4k_mp, ..base }),
        old(krnl).pt_mp.dom() == base.pt_mp.dom(),
        forall|t: RwLockPageTableRoot| #![trigger old(krnl).pt_mp.spec_index(t)] old(krnl).pt_mp.dom().contains(t) && t != pagetable ==> old(krnl).pt_mp.spec_index(t) == base.pt_mp.spec_index(t),
        old(krnl).it_mp.dom() == base.it_mp.dom(),
        forall|t: RwLockPageTableRoot| #![trigger old(krnl).it_mp.spec_index(t)] old(krnl).it_mp.dom().contains(t) && Some(t) != iommu_table ==> old(krnl).it_mp.spec_index(t) == base.it_mp.spec_index(t),
        old(krnl).allc_4k_mp.dom() == base.allc_4k_mp.dom(),
        forall|a: RwLockPageAllocatorPtr| #![trigger old(krnl).allc_4k_mp.spec_index(a)]
            old(krnl).allc_4k_mp.dom().contains(a) ==> old(krnl).allc_4k_mp.spec_index(a).quota.view() == base.allc_4k_mp.spec_index(a).quota.view(),
        forall|held_thread: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(held_thread)]
            old(lctx).thread_lock_map().dom().contains(held_thread) ==> !old(krnl).thr_mp.spec_index(held_thread).being_killed(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).process_lock_map() == old(lctx).process_lock_map().remove(target),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).page_lock_map().dom().is_empty(),
        final(lctx).pagetable_lock_map().dom().is_empty(),
        final(lctx).pagetable_window_lock_map().dom().is_empty(),
        final(lctx).iommu_table_lock_map().dom().is_empty(),
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        final(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        final(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        *final(krnl) == (KernelK { prc_mp: final(krnl).prc_mp, ctn_mp: final(krnl).ctn_mp, pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, it_mp: final(krnl).it_mp,
            pg_arr: final(krnl).pg_arr, allc_4k_mp: final(krnl).allc_4k_mp, ..*old(krnl) }),
        final(krnl).prc_mp.dom() == old(krnl).prc_mp.dom().remove(target),
        final(krnl).allc_4k_mp.dom().contains(allocator_ptr),
        base.prc_mp.spec_index(target).view_ghost().uppertree_seq.view().contains(parent_ptr),
        forall|p: RwLockProcessPtr| #![trigger final(krnl).prc_mp.spec_index(p)] final(krnl).prc_mp.dom().contains(p) ==> {
            let old_p = base.prc_mp.spec_index(p);
            let new_p = final(krnl).prc_mp.spec_index(p);
            &&& new_p.view() == if p == parent_ptr { Process { children: new_p.view().children, ..old_p.view() } } else { old_p.view() }
            &&& new_p.view_ghost() == if base.prc_mp.spec_index(target).view_ghost().uppertree_seq.view().contains(p) {
                ProcessGhost { subtree_set: Ghost(old_p.view_ghost().subtree_set.view().remove(target)), ..old_p.view_ghost() }
            } else { old_p.view_ghost() }
            &&& new_p.view_rodata() == old_p.view_rodata()
            &&& new_p.locking_thread() == old_p.locking_thread()
            &&& new_p.being_killed() == old_p.being_killed()
            &&& new_p.killer_info() == old_p.killer_info()
        },
        final(krnl).prc_mp.spec_index(parent_ptr).view().children.view() == base.prc_mp.spec_index(parent_ptr).view().children.view().remove_value(target),
        final(krnl).ctn_mp.dom() == base.ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(c)] base.ctn_mp.dom().contains(c) && c != container_ptr ==> final(krnl).ctn_mp.spec_index(c) == base.ctn_mp.spec_index(c),
        final(krnl).ctn_mp.spec_index(container_ptr).view() == base.ctn_mp.spec_index(container_ptr).view(),
        final(krnl).ctn_mp.spec_index(container_ptr).view_rodata() == base.ctn_mp.spec_index(container_ptr).view_rodata(),
        final(krnl).ctn_mp.spec_index(container_ptr).view_ghost() == (ContainerGhost {
            owned_processes: Ghost(base.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().remove(target)), ..base.ctn_mp.spec_index(container_ptr).view_ghost() }),
        final(krnl).ctn_mp.spec_index(container_ptr).locking_thread() == base.ctn_mp.spec_index(container_ptr).locking_thread(),
        final(krnl).ctn_mp.spec_index(container_ptr).control() == base.ctn_mp.spec_index(container_ptr).control(),
        forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_4k_mp.spec_index(a)]
            base.allc_4k_mp.dom().contains(a) && a != allocator_ptr ==> final(krnl).allc_4k_mp.spec_index(a).quota.view() == base.allc_4k_mp.spec_index(a).quota.view(),
        base.allc_4k_mp.spec_index(allocator_ptr).quota.view().view() < final(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.view().view(),
        final(krnl).pt_mp.dom() == base.pt_mp.dom().remove(pagetable),
        forall|t: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(t)]
            final(krnl).pt_mp.dom().contains(t) ==> final(krnl).pt_mp.spec_index(t) == base.pt_mp.spec_index(t) && final(krnl).pt_lower.view().spec_index(t) == base.pt_lower.view().spec_index(t),
        final(krnl).it_mp.dom() == match iommu_table { Some(it) => base.it_mp.dom().remove(it), None => base.it_mp.dom() },
        forall|t: RwLockPageTableRoot| #![trigger final(krnl).it_mp.spec_index(t)] final(krnl).it_mp.dom().contains(t) ==> final(krnl).it_mp.spec_index(t) == base.it_mp.spec_index(t),
{
    hide(Seq::no_duplicates);
    let ghost entry = *krnl;
    proof {
        allocator_perms_wf_map(krnl.allc_4k_mp);
        allocator_perms_wf_at(krnl.allc_4k_mp, allocator_ptr);
        krnl.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), target);
        krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
        if let Some(it) = iommu_table { krnl.it_mp.typed_lock_map_aligned_write_at(lctx.iommu_table_lock_map(), lctx.thread_id(), it); }
        pagetable_pages_wf_closure_entry_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pagetable, krnl.pt_mp.spec_index(pagetable).view().cr3);
        if let Some(it) = iommu_table { iommu_table_pages_wf_closure_entry_at(krnl.it_mp, krnl.pg_arr, it, krnl.it_mp.spec_index(it).view().cr3); }
        process_pages_wf_process_entry_at(krnl.pg_arr, krnl.prc_mp, target);
        pagetable_pages_wf_root_entry_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pagetable);
        if let Some(it) = iommu_table { iommu_table_pages_wf_root_entry_at(krnl.it_mp, krnl.pg_arr, it); }
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        kill_retire_pages_held_and_owned(entry, target, old(lctx).page_lock_map().dom(), allocator_ptr, cpu_id);
    }
    let Tracked(process_page_perm) = kill_retire_unlink_process(krnl, Tracked(&mut *lctx), target, parent_ptr, container_ptr, Tracked(target_perm), Tracked(parent_perm));
    let tables = kill_retire_remove_tables(krnl, Tracked(&mut *lctx), pagetable, iommu_table, Tracked(pt_lock_perm), Tracked(it_lock_perm));
    let tracked mut page_perms = tables.get();
    proof { page_perms.tracked_insert(page_ptr2page_index(target), process_page_perm); }
    kill_retire_pages_to_cache(krnl, pages, Tracked(page_perms), allocator_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&page_lock_perms), Tracked(&cache_lock_perm));
    {
        let quota = krnl.allc_4k_mp.borrow_mut_quota_typed(allocator_ptr, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
            Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(&quota_lock_perm));
        quota.value = quota.value + pages.len();
    }
    let ghost mid = *krnl;
    proof {
        assert(kill_retire_eof_transition_framing(entry, mid, cpu_id, target, Some(parent_ptr), container_ptr, allocator_ptr)) by { reveal(kill_retire_eof_transition_framing); };
        assert(mid.inv()) by { reveal(LockedMap::typed_lock_map_aligned); kill_retire_eof(entry, mid, *old(lctx), cpu_id, target, parent_ptr, container_ptr, allocator_ptr); };
    }
    krnl.wunlock_allocator_quota_4k(allocator_ptr, Tracked(&mut *lctx), Tracked(quota_lock_perm));
    krnl.wunlock_allocator_cache_4k(allocator_ptr, cpu_id, Tracked(&mut *lctx), Tracked(cache_lock_perm));
    wunlock_kill_retire_pages(krnl, pages, Tracked(&mut *lctx), Tracked(page_lock_perms));
}

/// With the zombie target and its parent write-held in a released view, unlink the target from its parent, its ancestors'
/// subtrees, and its container, and remove it from the process map, returning its page permission.
pub(crate) fn kill_retire_unlink_process(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, target: RwLockProcessPtr, parent_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr,
    Tracked(target_perm): Tracked<LockPerm>, Tracked(parent_perm): Tracked<&LockPerm>,
) -> (ret: Tracked<PagePerm4k>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        old(krnl).prc_mp.dom().contains(target),
        old(krnl).prc_mp.spec_index(target).being_killed(),
        old(krnl).prc_mp.spec_index(target).view().children.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view_rodata().view().parent == Some(parent_ptr),
        old(krnl).prc_mp.spec_index(target).view_rodata().view().owning_container == container_ptr,
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), target, TypedLockMode::Write),
        target_perm.state() is WriteLock,
        target_perm.thread_id() == old(lctx).thread_id(),
        target_perm.lock_id() == old(krnl).prc_mp.spec_index(target).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(parent_ptr),
        parent_ptr != target,
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), parent_ptr, TypedLockMode::Write),
        parent_perm.state() is WriteLock,
        parent_perm.thread_id() == old(lctx).thread_id(),
        parent_perm.lock_id() == old(krnl).prc_mp.spec_index(parent_ptr).locking_thread()->Write_lock_id,
    ensures
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Process(target)),
        *final(krnl) == (KernelK { prc_mp: final(krnl).prc_mp, ctn_mp: final(krnl).ctn_mp, ..*old(krnl) }),
        process_perms_wf(final(krnl).prc_mp),
        container_perms_wf(final(krnl).ctn_mp),
        final(krnl).prc_mp.dom() == old(krnl).prc_mp.dom().remove(target),
        forall|p: RwLockProcessPtr| #![trigger final(krnl).prc_mp.spec_index(p)] final(krnl).prc_mp.dom().contains(p) ==> {
            let old_p = old(krnl).prc_mp.spec_index(p);
            let new_p = final(krnl).prc_mp.spec_index(p);
            &&& new_p.view() == if p == parent_ptr { Process { children: new_p.view().children, ..old_p.view() } } else { old_p.view() }
            &&& new_p.view_ghost().subtree_set.view() == if old(krnl).prc_mp.spec_index(target).view_ghost().uppertree_seq.view().contains(p) {
                old_p.view_ghost().subtree_set.view().remove(target) } else { old_p.view_ghost().subtree_set.view() }
            &&& new_p.view_ghost().uppertree_seq == old_p.view_ghost().uppertree_seq
            &&& new_p.view_ghost().owned_pci_functions == old_p.view_ghost().owned_pci_functions
            &&& new_p.view_rodata() == old_p.view_rodata()
            &&& new_p.is_init() == old_p.is_init()
            &&& new_p.locking_thread() == old_p.locking_thread()
            &&& new_p.being_killed() == old_p.being_killed()
            &&& new_p.killer_info() == old_p.killer_info()
            &&& final(krnl).prc_mp.view().spec_index(p).is_init() == old(krnl).prc_mp.view().spec_index(p).is_init()
            &&& final(krnl).prc_mp.view().spec_index(p).addr() == old(krnl).prc_mp.view().spec_index(p).addr()
        },
        ({
            let node_addr = old(krnl).prc_mp.spec_index(target).view().parent_linkedlist_node.addr();
            let old_children = old(krnl).prc_mp.spec_index(parent_ptr).view().children;
            let new_children = final(krnl).prc_mp.spec_index(parent_ptr).view().children;
            &&& old_children.map().dom().contains(node_addr)
            &&& old_children.map().spec_index(node_addr) == target
            &&& old(krnl).prc_mp.spec_index(target).view_ghost().uppertree_seq.view().contains(parent_ptr)
            &&& new_children.view() == old_children.view().remove_value(target)
            &&& new_children.map() == old_children.map().remove(node_addr)
            &&& new_children.dom() == old_children.dom().remove(node_addr)
        }),
        final(krnl).ctn_mp.dom() == old(krnl).ctn_mp.dom(),
        final(krnl).ctn_mp.unchanged_except(&old(krnl).ctn_mp, container_ptr),
        final(krnl).ctn_mp.spec_index(container_ptr).view() == old(krnl).ctn_mp.spec_index(container_ptr).view(),
        final(krnl).ctn_mp.spec_index(container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata(),
        final(krnl).ctn_mp.spec_index(container_ptr).view_ghost() == (ContainerGhost {
            owned_processes: Ghost(old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().remove(target)), ..old(krnl).ctn_mp.spec_index(container_ptr).view_ghost() }),
        final(krnl).ctn_mp.spec_index(container_ptr).is_init() == old(krnl).ctn_mp.spec_index(container_ptr).is_init(),
        final(krnl).ctn_mp.spec_index(container_ptr).locking_thread() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread(),
        final(krnl).ctn_mp.spec_index(container_ptr).control() == old(krnl).ctn_mp.spec_index(container_ptr).control(),
        ret.view().is_init(),
        ret.view().addr() == target,
{
    proof {
        let root = krnl.ctn_mp.spec_index(container_ptr).view().root_process;
        let tree = krnl.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view();
        process_perms_wf_at(krnl.prc_mp, target); container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, target); container_perms_wf_at(krnl.ctn_mp, container_ptr);
        assert(process_tree_wf(root, tree, krnl.prc_mp)) by { per_container_process_tree_wf_at(krnl.ctn_mp, krnl.prc_mp, container_ptr); };
        assert(root != target) by {
            process_root_wf_at(root, tree, krnl.prc_mp, target); process_children_parent_wf_parent_at(root, tree, krnl.prc_mp, target); process_children_parent_wf_at(root, tree, krnl.prc_mp, parent_ptr, target);
        };
        assert(krnl.prc_mp.spec_index(target).view_ghost().uppertree_seq.view().to_set().subset_of(krnl.prc_mp.dom())
            && krnl.prc_mp.spec_index(target).view_ghost().uppertree_seq.view().contains(parent_ptr)) by {
            krnl.prc_mp.spec_index(target).view_ghost().uppertree_seq.view().to_set_ensures(); process_uppertree_seq_wf_dom_at(root, tree, krnl.prc_mp, target);
            container_process_wf_container_at(krnl.ctn_mp, krnl.prc_mp, container_ptr, target); process_root_wf_at(root, tree, krnl.prc_mp, target); process_children_depth_wf_at(root, tree, krnl.prc_mp, target);
        };
        assert(krnl.prc_mp.spec_index(parent_ptr).view().children.map().dom().contains(krnl.prc_mp.spec_index(target).view().parent_linkedlist_node.addr())
            && krnl.prc_mp.spec_index(parent_ptr).view().children.map().spec_index(krnl.prc_mp.spec_index(target).view().parent_linkedlist_node.addr()) == target) by { process_linkedlist_wf_at(root, tree, krnl.prc_mp, target); };
    }
    let ghost uppers = krnl.prc_mp.spec_index(target).view_ghost().uppertree_seq.view();
    let Tracked(node_perm) = process_map_unlink_child(&mut krnl.prc_mp, parent_ptr, target, Ghost(uppers), Tracked(&*lctx), Tracked(parent_perm), Tracked(&target_perm));
    proof { container_map_remove_owned_process(&mut krnl.ctn_mp, container_ptr, target, lctx.container_lock_map(), lctx.thread_id()); }
    krnl.remove_process_and_reclaim_4k_page_perm(target, Tracked(node_perm), Tracked(target_perm), Tracked(&mut *lctx))
}

/// Remove the write-held page table `pagetable` and IOMMU table `iommu_table`, which hold only their root tables, from their
/// maps, returning the permissions of each table's object and root table pages.
pub(crate) fn kill_retire_remove_tables(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, pagetable: RwLockPageTableRoot, iommu_table: Option<RwLockPageTableRoot>,
    Tracked(pt_lock_perm): Tracked<LockPerm>, Tracked(it_lock_perm): Tracked<Option<LockPerm>>,
) -> (ret: Tracked<Map<PageIndex, PagePerm4k>>)
    requires
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        pagetable_perms_wf(old(krnl).pt_mp),
        pagetable_lower_wf(old(krnl).pt_mp, old(krnl).pt_lower.view()),
        pagetable_window_holders_hold_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(old(krnl).pt_mp, old(krnl).pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(old(krnl).pt_mp, old(krnl).pt_lower.view()),
        pagetable_lower_backup_wf(old(krnl).pt_mp, old(krnl).pt_lower.view()),
        iommu_table_perms_wf(old(krnl).it_mp),
        old(krnl).pt_mp.dom().contains(pagetable),
        page_ptr_valid(pagetable),
        page_ptr_valid(old(krnl).pt_mp.spec_index(pagetable).view().cr3),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).page_closure() =~= set![old(krnl).pt_mp.spec_index(pagetable).view().cr3],
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pt_lock_perm.state() is WriteLock,
        pt_lock_perm.thread_id() == old(lctx).thread_id(),
        pt_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        it_lock_perm is Some == iommu_table is Some,
        iommu_table is Some ==> {
            let it = old(krnl).it_mp.spec_index(iommu_table->Some_0);
            &&& old(krnl).it_mp.dom().contains(iommu_table->Some_0)
            &&& page_ptr_valid(iommu_table->Some_0)
            &&& page_ptr_valid(it.view().cr3)
            &&& it.view().page_closure() =~= set![it.view().cr3]
            &&& typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table->Some_0, TypedLockMode::Write)
            &&& it_lock_perm->Some_0.state() is WriteLock
            &&& it_lock_perm->Some_0.thread_id() == old(lctx).thread_id()
            &&& it_lock_perm->Some_0.lock_id() == it.locking_thread()->Write_lock_id
        },
    ensures
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map().remove(pagetable),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map() == match iommu_table { Some(it) => old(lctx).iommu_table_lock_map().remove(it), None => old(lctx).iommu_table_lock_map() },
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, it_mp: final(krnl).it_mp, ..*old(krnl) }),
        pagetable_perms_wf(final(krnl).pt_mp),
        pagetable_lower_wf(final(krnl).pt_mp, final(krnl).pt_lower.view()),
        pagetable_window_holders_hold_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(final(krnl).pt_mp, final(krnl).pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(final(krnl).pt_mp, final(krnl).pt_lower.view()),
        pagetable_lower_backup_wf(final(krnl).pt_mp, final(krnl).pt_lower.view()),
        final(krnl).pt_lower.view() == old(krnl).pt_lower.view().remove(pagetable),
        iommu_table_perms_wf(final(krnl).it_mp),
        final(krnl).pt_mp.dom() =~= old(krnl).pt_mp.dom().remove(pagetable),
        forall|t: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(t)] final(krnl).pt_mp.dom().contains(t) ==> final(krnl).pt_mp.spec_index(t) == old(krnl).pt_mp.spec_index(t),
        forall|t: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.lock_id_by_key(t)] final(krnl).pt_mp.dom().contains(t) ==> final(krnl).pt_mp.lock_id_by_key(t) == old(krnl).pt_mp.lock_id_by_key(t),
        final(krnl).it_mp.dom() =~= match iommu_table { Some(it) => old(krnl).it_mp.dom().remove(it), None => old(krnl).it_mp.dom() },
        forall|t: RwLockPageTableRoot| #![trigger final(krnl).it_mp.spec_index(t)] final(krnl).it_mp.dom().contains(t) ==> final(krnl).it_mp.spec_index(t) == old(krnl).it_mp.spec_index(t),
        forall|t: RwLockPageTableRoot| #![trigger final(krnl).it_mp.lock_id_by_key(t)] final(krnl).it_mp.dom().contains(t) ==> final(krnl).it_mp.lock_id_by_key(t) == old(krnl).it_mp.lock_id_by_key(t),
        ret.view().dom().contains(page_ptr2page_index(pagetable)),
        ret.view().dom().contains(page_ptr2page_index(old(krnl).pt_mp.spec_index(pagetable).view().cr3)),
        iommu_table is Some ==> ret.view().dom().contains(page_ptr2page_index(iommu_table->Some_0))
            && ret.view().dom().contains(page_ptr2page_index(old(krnl).it_mp.spec_index(iommu_table->Some_0).view().cr3)),
        forall|i: PageIndex| #![trigger ret.view().dom().contains(i)] ret.view().dom().contains(i) ==> ret.view()[i].is_init() && ret.view()[i].addr() == page_index2page_ptr(i),
{
    let ghost entry = *krnl;
    proof { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable); page_ptr_roundtrip(); }
    let (Tracked(pt_object_perm), Tracked(pt_root_perm)) = krnl.remove_pagetable_and_reclaim_4k_page_perms(pagetable, Tracked(pt_lock_perm), Tracked(&mut *lctx));
    let tracked mut page_perms: Map<PageIndex, PagePerm4k> = Map::tracked_empty();
    proof {
        page_perms.tracked_insert(page_ptr2page_index(pagetable), pt_object_perm);
        page_perms.tracked_insert(page_ptr2page_index(entry.pt_mp.spec_index(pagetable).view().cr3), pt_root_perm);
    }
    if let Some(it) = iommu_table {
        proof { iommu_table_perms_wf_map(krnl.it_mp); iommu_table_perms_wf_at(krnl.it_mp, it); }
        let tracked it_perm = it_lock_perm.tracked_unwrap();
        let (Tracked(it_object_perm), Tracked(it_root_perm)) = krnl.remove_iommu_table_and_reclaim_4k_page_perms(it, Tracked(it_perm), Tracked(&mut *lctx));
        proof {
            page_perms.tracked_insert(page_ptr2page_index(it), it_object_perm);
            page_perms.tracked_insert(page_ptr2page_index(entry.it_mp.spec_index(it).view().cr3), it_root_perm);
        }
    }
    Tracked(page_perms)
}
} // verus!
