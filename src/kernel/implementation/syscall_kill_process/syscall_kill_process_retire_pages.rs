use vstd::prelude::*;
use crate::*;
#[cfg(feature = "split-crates")]
use veriflat_alloc_page::free_4k_page::drain_4k_cache_batch;
use super::syscall_kill_process_spec::*;
use super::syscall_kill_process_trace::*;
use super::syscall_kill_process_walk_spec::KillScope;
use super::syscall_kill_process_retire_pages_scoped::kill_retire_next_table_page_scoped;
use super::syscall_kill_process_retire_table_page_lock::kill_retire_lock_table_page;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_walk_spec::kill_chain_state;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_retire_spec::{kill_retire_held_state, kill_retire_pages, kill_retire_tables_emptied};
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_retire_pages_spec::kill_retire_table_page_eof_transition_framing;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_retire_pages_eof::kill_retire_table_page_eof;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_state_lemma::mapped_1g_page_pagetable_wf_table_at;

verus! {
/// Retire every table page below the root of the empty zombie target's write-held page table and, once a scan finds that
/// root alone, of its write-held IOMMU table, one step per page, to the caches of their owner, the killer's container;
/// then refund their quota to the killer's container chain. Both tables then hold only their roots: a zombie's tables map
/// nothing (`process_emptied_tables_wf`, `mapped_1g_page_pagetable_wf`, `iommu_table_no_huge_leaf_wf`), so no scan is Blocked.
pub(crate) fn kill_retire_structure_pages(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>,
    Tracked(page_perms): Tracked<&Map<PageIndex, LockPerm>>, Tracked(pt_perm): Tracked<&LockPerm>, Tracked(it_perm): Tracked<&Option<LockPerm>>, Ghost(start): Ghost<int>,
    Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        kill_retire_held_state(*old(krnl), *old(lctx), prc_ptr, thrd_ptr, target, *page_perms, *pt_perm, *it_perm),
        held_locks_order_below(old(krnl), old(lctx), PAGE_TABLE_LOCK_MAJOR),
        old(lctx).thread_lock_map().dom() =~= set![thrd_ptr],
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        kill_chain_state(*old(krnl), *old(lctx), cpu_id, scope, prc_ptr, thrd_ptr, chain, KillStage::Retire, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
        0 < chain.len(),
        target == chain[chain.len() - 1],
        old(krnl).prc_mp.spec_index(target).view().zombie,
        old(krnl).prc_mp.spec_index(target).view().children.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), old(krnl).prc_mp.spec_index(target).view().pagetable).leaves_present(),
        ({
            let pt = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), old(krnl).prc_mp.spec_index(target).view().pagetable);
            &&& pt.lower.hidden_l1_tables_in_locked_windows()
            &&& pt.lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty()
            &&& pt.higher.table_stale_cpus.view() == Set::<CpuId>::empty()
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger pt.lower.l2_owner(p, i)] pt.lower.l2_perms.dom().contains(p) && pei_valid(i) ==> pt.lower.l2_owner(p, i) is None
        }),
        old(krnl).prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_retire_held_state(*final(krnl), *final(lctx), prc_ptr, thrd_ptr, target, *page_perms, *pt_perm, *it_perm),
        held_locks_order_below(final(krnl), final(lctx), PAGETABLE_PAGE_MAJOR),
        final(lctx).thread_lock_map().dom() =~= set![thrd_ptr],
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        kill_chain_state(*final(krnl), *final(lctx), cpu_id, scope, prc_ptr, thrd_ptr, chain, KillStage::Retire, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
        final(krnl).prc_mp.spec_index(target) == old(krnl).prc_mp.spec_index(target),
        kill_retire_tables_emptied(*final(krnl), target),
        ({
            let pt = old(krnl).prc_mp.spec_index(target).view().pagetable;
            let it = old(krnl).prc_mp.spec_index(target).view().iommu_table;
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt).leaves_present() ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt).leaves_present()
            &&& it is Some ==> (old(krnl).it_mp.spec_index(it->Some_0).view().leaves_present() ==> final(krnl).it_mp.spec_index(it->Some_0).view().leaves_present())
        }),
        final(krnl).prc_mp.spec_index(prc_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(prc_ptr).view_ghost().subtree_set,
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
        scope is Container ==> final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        scope is Container ==> final(krnl).prc_mp.spec_index(prc_ptr) == old(krnl).prc_mp.spec_index(prc_ptr),
        scope is Container ==> final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
        scope is Container ==> final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        scope is Container ==> final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
{
    let ghost entry_thread = krnl.thrd_mp.spec_index(thrd_ptr).view();
    proof {
        process_perms_wf_map(krnl.prc_mp);
        process_perms_wf_at(krnl.prc_mp, target);
        thread_perms_wf_map(krnl.thrd_mp);
        thread_perms_wf_at(krnl.thrd_mp, thrd_ptr);
        assert(entry_thread.container_depth <= MAX_CONTAINER_TREE_DEPTH) by { container_thread_wf_thread_at(krnl.ctn_mp, krnl.thrd_mp, thrd_ptr); container_perms_wf_at(krnl.ctn_mp, entry_thread.owning_container); };
    }
    let (pagetable, iommu_table) = {
        let tracked target_perm = chain_perms.tracked_borrow(target);
        let process = krnl.prc_mp.borrow_typed(target, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(target_perm));
        (process.pagetable, process.iommu_table)
    };
    let target_container = krnl.prc_mp.borrow_rodata(target).borrow().owning_container;
    let thread_container = krnl.thrd_mp.borrow_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(thread_perm)).owning_container;
    proof {
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr);
        container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, target); container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, prc_ptr);
        assert(target_container == thread_container <==> scope is Subtree);
    }
    let same = target_container == thread_container;
    let mut direct = 0usize;
    kill_retire_table_pages(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, thrd_ptr, target, Ghost(chain), Tracked(chain_perms), Tracked(cpu_perm),
        Tracked(process_perm), Tracked(thread_perm), Tracked(page_perms), Tracked(pt_perm), Tracked(it_perm), false, pagetable, Tracked(pt_perm), same, &mut direct, Ghost(entry_thread),
        Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    if let Some(it) = iommu_table {
        kill_retire_table_pages(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, thrd_ptr, target, Ghost(chain), Tracked(chain_perms), Tracked(cpu_perm),
            Tracked(process_perm), Tracked(thread_perm), Tracked(page_perms), Tracked(pt_perm), Tracked(it_perm), true, it, Tracked(it_perm.tracked_borrow()), same, &mut direct,
            Ghost(entry_thread), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    }
    if !same {
        return;
    }
    let mut indirect = [0usize; MAX_CONTAINER_TREE_DEPTH];
    let ghost refund_k = *krnl;
    let ghost refund_lctx = *lctx;
    let ghost refund_before = steps.view();
    proof {
        thread_perms_wf_at(krnl.thrd_mp, thrd_ptr);
        kill_step_pre_from_k(&refund_k, &refund_lctx, cpu_id, prc_ptr, thrd_ptr, target, KillStage::Retire, scope); kill_refund_pre_from_k(&refund_k, target, entry_thread.owning_container);
        assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
    }
    refund_unmap_4k_quota(krnl, thrd_ptr, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_perm));
    proof {
        vstd::assert_seqs_equal!(krnl.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k.view(), entry_thread.indirect_free_quota_pending_4k.view());
        kill_trace_from_refund(&*steps, refund_before, start, pre, kernel_k_to_kernel_u(refund_k), cpu_id, ctx, prc_ptr, thrd_ptr, target, KillStage::Retire,
            entry_thread.owning_container, scope);
        assert(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable) == whole_pagetable(refund_k.pt_mp, refund_k.pt_lower.view(), pagetable)) by {
            refund_k.pt_mp.typed_lock_map_aligned_write_at(refund_lctx.pagetable_lock_map(), refund_lctx.thread_id(), pagetable);
            pagetable_lower_backup_wf_at(refund_k.pt_mp, refund_k.pt_lower.view(), pagetable); pagetable_lower_backup_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        };
    }
}

/// Retire the table pages of the zombie target's write-held page table `table` (its write-held IOMMU table when
/// `iommu`), held with `table_perm`, until a scan of the table, which maps nothing, finds the root alone. In a process
/// kill (`same`) each page counts in the killer's direct pending 4K refund; otherwise each page is credited to its owner's
/// quota in its own step.
pub(crate) fn kill_retire_table_pages(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>,
    Tracked(page_perms): Tracked<&Map<PageIndex, LockPerm>>, Tracked(pt_perm): Tracked<&LockPerm>, Tracked(it_perm): Tracked<&Option<LockPerm>>, iommu: bool,
    table: RwLockPageTableRoot, Tracked(table_perm): Tracked<&LockPerm>, same: bool, direct: &mut usize, Ghost(entry_thread): Ghost<Thread>, Ghost(start): Ghost<int>,
    Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        same == (scope is Subtree),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        kill_retire_held_state(*old(krnl), *old(lctx), prc_ptr, thrd_ptr, target, *page_perms, *pt_perm, *it_perm),
        held_locks_order_below(old(krnl), old(lctx), PAGE_TABLE_LOCK_MAJOR),
        old(lctx).thread_lock_map().dom() =~= set![thrd_ptr],
        kill_chain_state(*old(krnl), *old(lctx), cpu_id, scope, prc_ptr, thrd_ptr, chain, KillStage::Retire, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
        0 < chain.len(),
        target == chain[chain.len() - 1],
        old(krnl).prc_mp.spec_index(target).view().zombie,
        !iommu ==> old(krnl).prc_mp.spec_index(target).view().pagetable == table && *table_perm == *pt_perm,
        !iommu ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).leaves_present(),
        !iommu ==> {
            let pt = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table);
            &&& pt.lower.hidden_l1_tables_in_locked_windows()
            &&& pt.lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty()
            &&& pt.higher.table_stale_cpus.view() == Set::<CpuId>::empty()
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger pt.lower.l2_owner(p, i)] pt.lower.l2_perms.dom().contains(p) && pei_valid(i) ==> pt.lower.l2_owner(p, i) is None
        },
        iommu ==> old(krnl).prc_mp.spec_index(target).view().iommu_table == Some(table) && *it_perm == Some(*table_perm),
        old(krnl).prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
        same ==> old(krnl).prc_mp.spec_index(target).view_rodata().view().owning_container == entry_thread.owning_container,
        same ==> old(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { direct_free_quota_pending_4k: old(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k, ..entry_thread }),
        same ==> *old(direct) == old(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view(),
        !same ==> old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_retire_held_state(*final(krnl), *final(lctx), prc_ptr, thrd_ptr, target, *page_perms, *pt_perm, *it_perm),
        held_locks_order_below(final(krnl), final(lctx), PAGE_TABLE_LOCK_MAJOR),
        final(lctx).thread_lock_map().dom() =~= set![thrd_ptr],
        kill_chain_state(*final(krnl), *final(lctx), cpu_id, scope, prc_ptr, thrd_ptr, chain, KillStage::Retire, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
        final(krnl).prc_mp.spec_index(target) == old(krnl).prc_mp.spec_index(target),
        same ==> final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { direct_free_quota_pending_4k: final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k, ..entry_thread }),
        same ==> *final(direct) == final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view(),
        !same ==> final(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        ({
            let pt = old(krnl).prc_mp.spec_index(target).view().pagetable;
            let it = old(krnl).prc_mp.spec_index(target).view().iommu_table;
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt).leaves_present() ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt).leaves_present()
            &&& it is Some ==> (old(krnl).it_mp.spec_index(it->Some_0).view().leaves_present() ==> final(krnl).it_mp.spec_index(it->Some_0).view().leaves_present())
            &&& iommu ==> final(krnl).pt_mp.spec_index(pt) == old(krnl).pt_mp.spec_index(pt)
            &&& iommu ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt)
        }),
        !iommu ==> {
            let pt = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), table);
            &&& pt.page_closure() =~= set![pt.cr3()]
            &&& pt.higher.table_stale_cpus.view() == Set::<CpuId>::empty()
            &&& pt.mapping_4k().dom() =~= Set::<VAddr>::empty()
            &&& pt.mapping_2m().dom() =~= Set::<VAddr>::empty()
            &&& pt.mapping_1g().dom() =~= Set::<VAddr>::empty()
        },
        iommu ==> {
            let it = final(krnl).it_mp.spec_index(table).view();
            &&& it.page_closure() =~= set![it.cr3]
            &&& it.mapping_4k().dom() =~= Set::<VAddr>::empty()
            &&& it.mapping_2m().dom() =~= Set::<VAddr>::empty()
            &&& it.mapping_1g().dom() =~= Set::<VAddr>::empty()
        },
        final(krnl).prc_mp.spec_index(prc_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(prc_ptr).view_ghost().subtree_set,
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
        scope is Container ==> final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        scope is Container ==> final(krnl).prc_mp.spec_index(prc_ptr) == old(krnl).prc_mp.spec_index(prc_ptr),
        scope is Container ==> final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
        scope is Container ==> final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        scope is Container ==> final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
{
    proof { held_kernel_objects_unchanged_reflexive(&*krnl, &*lctx); }
    loop
        invariant
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            krnl.cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
            scope is Container ==> krnl.cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
            scope is Container ==> krnl.prc_mp.spec_index(prc_ptr) == old(krnl).prc_mp.spec_index(prc_ptr),
            scope is Container ==> krnl.thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
            scope is Container ==> krnl.thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
            scope is Container ==> krnl.thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
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
            scope is Container ==> krnl.ctn_mp.spec_index(scope->Container_container) == old(krnl).ctn_mp.spec_index(scope->Container_container),
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.kernel_view_locking_state() is Acquire,
            steps.snapshot_k() == *krnl,
            0 <= start <= old(steps).view().len() <= steps.view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            kill_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, ctx),
            kill_retire_held_state(*krnl, *lctx, prc_ptr, thrd_ptr, target, *page_perms, *pt_perm, *it_perm),
            held_locks_order_below(krnl, lctx, PAGE_TABLE_LOCK_MAJOR),
            lctx.thread_lock_map().dom() =~= set![thrd_ptr],
            kill_chain_state(*krnl, *lctx, cpu_id, scope, prc_ptr, thrd_ptr, chain, KillStage::Retire, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
            0 < chain.len(),
            same == (scope is Subtree),
            target == chain[chain.len() - 1],
            krnl.prc_mp.spec_index(target) == old(krnl).prc_mp.spec_index(target),
            old(krnl).prc_mp.spec_index(target).view().zombie,
            !iommu ==> old(krnl).prc_mp.spec_index(target).view().pagetable == table && *table_perm == *pt_perm,
            !iommu ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).leaves_present(),
            !iommu ==> {
                let pt = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), table);
                &&& pt.lower.hidden_l1_tables_in_locked_windows()
                &&& pt.lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty()
                &&& pt.higher.table_stale_cpus.view() == Set::<CpuId>::empty()
                &&& forall|p: PageMapPtr, i: L2Index| #![trigger pt.lower.l2_owner(p, i)] pt.lower.l2_perms.dom().contains(p) && pei_valid(i) ==> pt.lower.l2_owner(p, i) is None
            },
            iommu ==> old(krnl).prc_mp.spec_index(target).view().iommu_table == Some(table) && *it_perm == Some(*table_perm),
            old(krnl).prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
            same ==> old(krnl).prc_mp.spec_index(target).view_rodata().view().owning_container == entry_thread.owning_container,
            same ==> krnl.thrd_mp.spec_index(thrd_ptr).view() == (Thread { direct_free_quota_pending_4k: krnl.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k, ..entry_thread }),
            same ==> *direct == krnl.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view(),
            !same ==> krnl.thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
            ({
                let pt = old(krnl).prc_mp.spec_index(target).view().pagetable;
                let it = old(krnl).prc_mp.spec_index(target).view().iommu_table;
                &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt).leaves_present() ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pt).leaves_present()
                &&& it is Some ==> (old(krnl).it_mp.spec_index(it->Some_0).view().leaves_present() ==> krnl.it_mp.spec_index(it->Some_0).view().leaves_present())
                &&& iommu ==> krnl.pt_mp.spec_index(pt) == old(krnl).pt_mp.spec_index(pt)
                &&& iommu ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pt) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt)
            }),
        decreases if iommu { krnl.it_mp.spec_index(table).view().page_closure().len() } else { whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), table).page_closure().len() },
    {
        let scan = if iommu {
            proof {
                process_iommu_table_wf_process_at(krnl.prc_mp, krnl.it_mp, target);
                iommu_table_perms_wf_map(krnl.it_mp);
                iommu_table_perms_wf_at(krnl.it_mp, table);
            }
            krnl.it_mp.borrow_typed(table, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), Tracked(table_perm)).next_structure_page()
        } else {
            proof {
                process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, target);
                process_perms_wf_at(krnl.prc_mp, target); process_emptied_tables_wf_at(krnl.prc_mp, krnl.pt_mp, krnl.pt_lower.view(), krnl.it_mp, krnl.pg_arr, target);
                pagetable_perms_wf_map(krnl.pt_mp);
                pagetable_perms_wf_at(krnl.pt_mp, table);
                pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), table); mapped_1g_page_pagetable_wf_table_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, table);
            }
            krnl.pt_mp.borrow_typed(table, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(table_perm)).next_structure_page(Tracked(krnl.pt_lower.borrow().tracked_borrow(table)))
        };
        if scan.table_page().is_none() {
            proof {
                if iommu {
                    assert(krnl.it_mp.spec_index(table).view().mapping_4k().dom() =~= Set::<VAddr>::empty()) by { process_perms_wf_at(krnl.prc_mp, target); process_emptied_tables_wf_at(krnl.prc_mp, krnl.pt_mp, krnl.pt_lower.view(), krnl.it_mp, krnl.pg_arr, target); };
                    assert(krnl.it_mp.spec_index(table).view().mapping_2m().dom() =~= Set::<VAddr>::empty() && krnl.it_mp.spec_index(table).view().mapping_1g().dom() =~= Set::<VAddr>::empty()) by { iommu_table_no_huge_leaf_wf_at(krnl.it_mp, table); };
                    assert(krnl.it_mp.spec_index(table).view().kernel_l4_end == 0) by { krnl.it_mp.spec_index(table).view().kernel_entries_wf_iommu_l4_end_at(); };
                } else {
                    assert(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), table).mapping_4k().dom() =~= Set::<VAddr>::empty()) by { process_perms_wf_at(krnl.prc_mp, target); process_emptied_tables_wf_at(krnl.prc_mp, krnl.pt_mp, krnl.pt_lower.view(), krnl.it_mp, krnl.pg_arr, target); };
                    assert(krnl.pt_mp.spec_index(table).view().kernel_l4_end == KERNEL_MEM_END_L4INDEX) by { krnl.default_pagetable_wf_at(table); };
                    assert(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), table).mapping_1g().dom() =~= Set::<VAddr>::empty()) by {
                        process_emptied_tables_wf_at(krnl.prc_mp, krnl.pt_mp, krnl.pt_lower.view(), krnl.it_mp, krnl.pg_arr, target);
                        mapped_1g_page_pagetable_wf_table_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, table);
                    };
                }
            }
            return;
        }
        let pg_ptr = scan.table_page().unwrap();
        proof {
            if iommu {
                iommu_table_pages_wf_closure_page_at(krnl.it_mp, krnl.pg_arr, table, pg_ptr);
            } else {
                pagetable_pages_wf_closure_page_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, table, pg_ptr);
            }
            if same {
                assert(krnl.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container) by {
                    process_object_pages_owner_wf_at(krnl.prc_mp, krnl.pt_mp, krnl.it_mp, krnl.pg_arr, page_ptr2page_index(pg_ptr));
                };
            }
        }
        let ghost closure = if iommu { krnl.it_mp.spec_index(table).view().page_closure() } else { whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), table).page_closure() };
        let ghost iter_k = *krnl;
        let ghost iter_lctx = *lctx;
        proof { assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); }; }
        if same {
            kill_retire_next_table_page(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, thrd_ptr, target, iommu, table, scan, pg_ptr, Tracked(table_perm), Tracked(thread_perm),
                direct);
        } else {
            kill_retire_next_table_page_scoped(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, thrd_ptr, target, iommu, table, scan, pg_ptr, Tracked(table_perm),
                Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
        }
        proof {
            vstd::set::lemma_set_remove_len(closure, pg_ptr);
            if iommu {
                let pt = old(krnl).prc_mp.spec_index(target).view().pagetable;
                assert(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pt) == whole_pagetable(iter_k.pt_mp, iter_k.pt_lower.view(), pt)) by {
                    iter_k.pt_mp.typed_lock_map_aligned_write_at(iter_lctx.pagetable_lock_map(), iter_lctx.thread_id(), pt);
                    pagetable_lower_backup_wf_at(iter_k.pt_mp, iter_k.pt_lower.view(), pt); pagetable_lower_backup_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pt);
                };
            }
        }
    }
}

/// Retire the table page `pg_ptr` that `scan` names from the write-held table `table` of the zombie `target` (its
/// write-held IOMMU table when `iommu`) to shard `cpu_id` of the 4K allocator of its owner, the container of the write-held
/// killer `thrd_ptr`, whose direct pending 4K refund grows by one; the page and cache locks taken for it are released.
pub(crate) fn kill_retire_next_table_page(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr,
    target: RwLockProcessPtr, iommu: bool, table: RwLockPageTableRoot, scan: StructureScan, pg_ptr: PagePtr, Tracked(table_perm): Tracked<&LockPerm>,
    Tracked(thread_perm): Tracked<&LockPerm>, direct: &mut usize,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        held_locks_order_below(old(krnl), old(lctx), PAGE_TABLE_LOCK_MAJOR),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        index_valid(NUM_CPUS, cpu_id),
        old(lctx).process_lock_map().dom().contains(target),
        old(krnl).prc_mp.spec_index(target).view().zombie,
        page_ptr_valid(pg_ptr),
        scan.spec_table_page() == Some(pg_ptr),
        table_perm.state() is WriteLock,
        table_perm.thread_id() == old(lctx).thread_id(),
        !iommu ==> {
            &&& old(krnl).prc_mp.spec_index(target).view().pagetable == table
            &&& old(krnl).pt_mp.dom().contains(table)
            &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), table, TypedLockMode::Write)
            &&& old(lctx).pagetable_lock_map().dom() == set![table]
            &&& table_perm.lock_id() == old(krnl).pt_mp.spec_index(table).locking_thread()->Write_lock_id
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).structure_scan_wf(scan)
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).leaves_present()
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).lower.hidden_l1_tables_in_locked_windows()
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty()
            &&& old(krnl).pt_mp.spec_index(table).view().table_stale_cpus.view() == Set::<CpuId>::empty()
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).lower.l2_owner(p, i)]
                whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).lower.l2_perms.dom().contains(p) && pei_valid(i) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).lower.l2_owner(p, i) is None
        },
        iommu ==> {
            &&& old(krnl).prc_mp.spec_index(target).view().iommu_table == Some(table)
            &&& old(krnl).it_mp.dom().contains(table)
            &&& typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), table, TypedLockMode::Write)
            &&& table_perm.lock_id() == old(krnl).it_mp.spec_index(table).locking_thread()->Write_lock_id
            &&& old(krnl).it_mp.spec_index(table).view().structure_scan_wf(scan)
        },
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: table, table_type: if iommu { IOMMU_TYPE } else { PT_TYPE } } }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container,
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_perm.state() is WriteLock,
        thread_perm.thread_id() == old(lctx).thread_id(),
        thread_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        *old(direct) == old(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
        old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view() == old(steps).view(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
        iommu ==> held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        !iommu ==> held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        !iommu ==> {
            &&& final(krnl).pt_mp.spec_index(table).locking_thread() == old(krnl).pt_mp.spec_index(table).locking_thread()
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).leaves_present() ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), table).leaves_present()
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), table).lower.hidden_l1_tables_in_locked_windows()
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), table).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty()
            &&& final(krnl).pt_mp.spec_index(table).view().table_stale_cpus.view() == Set::<CpuId>::empty()
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), table).lower.l2_owner(p, i)]
                whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), table).lower.l2_perms.dom().contains(p) && pei_valid(i) ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), table).lower.l2_owner(p, i) is None
        },
        iommu ==> {
            &&& final(krnl).it_mp.spec_index(table).locking_thread() == old(krnl).it_mp.spec_index(table).locking_thread()
            &&& old(krnl).it_mp.spec_index(table).view().leaves_present() ==> final(krnl).it_mp.spec_index(table).view().leaves_present()
        },
        final(krnl).thrd_mp.dom().contains(thrd_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { direct_free_quota_pending_4k: final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k,
            ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
        *final(direct) == final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view(),
        *final(direct) == *old(direct) + 1,
        !iommu ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).page_closure().contains(pg_ptr)
            && whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), table).page_closure() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).page_closure().remove(pg_ptr),
        iommu ==> old(krnl).it_mp.spec_index(table).view().page_closure().contains(pg_ptr) && final(krnl).it_mp.spec_index(table).view().page_closure() == old(krnl).it_mp.spec_index(table).view().page_closure().remove(pg_ptr),
{
    let ghost entry_lctx = *lctx;
    let (Tracked(page_perm), Tracked(cache_perm), _, allc_ptr, Ghost(page_lctx)) =
        kill_retire_lock_table_page(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, target, iommu, table, scan, pg_ptr);
    kill_retire_table_page_and_unlock(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), target, iommu, table, scan, pg_ptr, thrd_ptr, allc_ptr, cpu_id, direct,
        Tracked(table_perm), Tracked(page_perm), Tracked(thread_perm), Tracked(cache_perm), Ghost(entry_lctx), Ghost(page_lctx));
}

/// Retire the table page `pg_ptr` that `scan` names from the write-held table `table` of the zombie `target` (its
/// write-held IOMMU table when `iommu`) through the write-held cache shard `cpu_id` of the 4K allocator `allc_ptr`
/// of its owner, the container of the write-held killer `thrd_ptr`, then release the cache and page locks taken for it,
/// back to the lock maps `entry_lctx` held before the page lock; the projection does not change.
pub(crate) fn kill_retire_table_page_and_unlock(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, target: RwLockProcessPtr, iommu: bool, table: RwLockPageTableRoot,
    scan: StructureScan, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, direct: &mut usize, Tracked(table_perm): Tracked<&LockPerm>,
    Tracked(page_perm): Tracked<LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, Tracked(cache_perm): Tracked<LockPerm>, Ghost(entry_lctx): Ghost<LocalContext>,
    Ghost(page_lctx): Ghost<LocalContext>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        page_ptr_valid(pg_ptr),
        scan.spec_table_page() == Some(pg_ptr),
        table_perm.state() is WriteLock,
        table_perm.thread_id() == old(lctx).thread_id(),
        !iommu ==> {
            &&& old(krnl).pt_mp.dom().contains(table)
            &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), table, TypedLockMode::Write)
            &&& table_perm.lock_id() == old(krnl).pt_mp.spec_index(table).locking_thread()->Write_lock_id
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).structure_scan_wf(scan)
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).leaves_present()
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).lower.hidden_l1_tables_in_locked_windows()
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty()
            &&& old(krnl).pt_mp.spec_index(table).view().table_stale_cpus.view() == Set::<CpuId>::empty()
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).lower.l2_owner(p, i)]
                whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).lower.l2_perms.dom().contains(p) && pei_valid(i) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).lower.l2_owner(p, i) is None
        },
        iommu ==> {
            &&& old(krnl).it_mp.dom().contains(table)
            &&& typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), table, TypedLockMode::Write)
            &&& table_perm.lock_id() == old(krnl).it_mp.spec_index(table).locking_thread()->Write_lock_id
            &&& old(krnl).it_mp.spec_index(table).view().structure_scan_wf(scan)
        },
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write),
        page_perm.state() is WriteLock,
        page_perm.thread_id() == old(lctx).thread_id(),
        page_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: table, table_type: if iommu { IOMMU_TYPE } else { PT_TYPE } } }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container,
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_perm.state() is WriteLock,
        thread_perm.thread_id() == old(lctx).thread_id(),
        thread_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        *old(direct) == old(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view(),
        old(krnl).ctn_mp.dom().contains(old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container),
        old(krnl).ctn_mp.spec_index(old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container).view_rodata().view().allocator_ptr_4k == allc_ptr,
        old(krnl).allc_4k_mp.dom().contains(allc_ptr),
        old(krnl).allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().len() < ALLOCATOR_MAX_WATERMARK,
        typed_lock_map_contains_mode(old(lctx).allocator_cache_4k_lock_map(), (allc_ptr, cpu_id), TypedLockMode::Write),
        cache_perm.state() is WriteLock,
        cache_perm.thread_id() == old(lctx).thread_id(),
        cache_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(steps).snapshot_k() == *old(krnl),
        old(krnl).prc_mp.dom().contains(target),
        old(krnl).prc_mp.spec_index(target).view().zombie,
        !iommu ==> old(krnl).prc_mp.spec_index(target).view().pagetable == table,
        iommu ==> old(krnl).prc_mp.spec_index(target).view().iommu_table == Some(table),
        entry_lctx.thread_id() == old(lctx).thread_id(),
        !entry_lctx.page_lock_map().dom().contains(page_ptr2page_index(pg_ptr)),
        typed_lock_maps_inserted(&entry_lctx, &page_lctx, KernelObjId::Page(page_ptr2page_index(pg_ptr)), page_lctx.page_lock_map()[page_ptr2page_index(pg_ptr)]),
        !page_lctx.allocator_cache_4k_lock_map().dom().contains((allc_ptr, cpu_id)),
        typed_lock_maps_inserted(&page_lctx, old(lctx), KernelObjId::AllocatorCache(PageSize::SZ4k, allc_ptr, cpu_id), old(lctx).allocator_cache_4k_lock_map()[(allc_ptr, cpu_id)]),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_unchanged(&entry_lctx, final(lctx)),
        final(lctx).page_lock_map() == old(lctx).page_lock_map().remove(page_ptr2page_index(pg_ptr)),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view() == old(steps).view(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, &entry_lctx),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, &entry_lctx),
        held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, &entry_lctx),
        iommu ==> held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, &entry_lctx),
        !iommu ==> held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, &entry_lctx),
        !iommu ==> {
            &&& final(krnl).pt_mp.spec_index(table).locking_thread() == old(krnl).pt_mp.spec_index(table).locking_thread()
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).leaves_present() ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), table).leaves_present()
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), table).lower.hidden_l1_tables_in_locked_windows()
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), table).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty()
            &&& final(krnl).pt_mp.spec_index(table).view().table_stale_cpus.view() == Set::<CpuId>::empty()
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), table).lower.l2_owner(p, i)]
                whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), table).lower.l2_perms.dom().contains(p) && pei_valid(i) ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), table).lower.l2_owner(p, i) is None
        },
        iommu ==> {
            &&& final(krnl).it_mp.spec_index(table).locking_thread() == old(krnl).it_mp.spec_index(table).locking_thread()
            &&& old(krnl).it_mp.spec_index(table).view().leaves_present() ==> final(krnl).it_mp.spec_index(table).view().leaves_present()
        },
        final(krnl).thrd_mp.dom().contains(thrd_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { direct_free_quota_pending_4k: final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k,
            ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
        *final(direct) == final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view(),
        *final(direct) == *old(direct) + 1,
        !iommu ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).page_closure().contains(pg_ptr)
            && whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), table).page_closure() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).page_closure().remove(pg_ptr),
        iommu ==> old(krnl).it_mp.spec_index(table).view().page_closure().contains(pg_ptr) && final(krnl).it_mp.spec_index(table).view().page_closure() == old(krnl).it_mp.spec_index(table).view().page_closure().remove(pg_ptr),
{
    let pg_idx = page_ptr2page_index(pg_ptr);
    kill_retire_table_page_to_cache(krnl, Tracked(&mut *lctx), iommu, table, scan, pg_ptr, thrd_ptr, allc_ptr, cpu_id, direct, Tracked(table_perm), Tracked(&page_perm),
        Tracked(thread_perm), Tracked(&cache_perm), Ghost(target));
    krnl.wunlock_allocator_cache_4k(allc_ptr, cpu_id, Tracked(&mut *lctx), Tracked(cache_perm));
    krnl.wunlock_page(pg_idx, Tracked(&mut *lctx), Tracked(page_perm));
    proof {
        assert(lctx.page_lock_map() =~= entry_lctx.page_lock_map() && lctx.page_lock_map() =~= old(lctx).page_lock_map().remove(pg_idx) && lctx.allocator_cache_4k_lock_map() =~= entry_lctx.allocator_cache_4k_lock_map());
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        kernel_lock_states_unchanged_except_tables_of_implies_u_eq(&steps.snapshot_k(), &*krnl, Some(target));
        krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
    }
}

/// Write-lock the cache shard `cpu_id` of the 4K allocator `allc_ptr`, first moving a batch of a shard without room
/// for `room` more pages to the allocator's global pool, which ends the pending step from the snapshot; the lock changes
/// nothing the projection shows and keeps every held object. Without a pending step, a step boundary follows.
pub(crate) fn kill_retire_lock_cache(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    room: usize, Ghost(pg_idx): Ghost<PageIndex>,
) -> (ret: Tracked<LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl) || {
            &&& *old(krnl) == (KernelK { pt_mp: old(krnl).pt_mp, pt_lower: old(krnl).pt_lower, pg_arr: old(krnl).pg_arr, ..old(steps).snapshot_k() })
            &&& kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl))
            &&& kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp)
            &&& kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl))
        },
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).allc_4k_mp.dom().contains(allc_ptr),
        room <= ALLOCATOR_BATCH,
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        index_valid(NUM_PAGES, pg_idx),
        old(lctx).page_lock_map().dom().contains(pg_idx),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
        old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::AllocatorCache(PageSize::SZ4k, allc_ptr, cpu_id), final(lctx).allocator_cache_4k_lock_map()[(allc_ptr, cpu_id)]),
        typed_lock_map_contains_mode(final(lctx).allocator_cache_4k_lock_map(), (allc_ptr, cpu_id), TypedLockMode::Write),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).view() == old(steps).view() && final(steps).snapshot_k() == old(steps).snapshot_k() && old(steps).snapshot_k() != *old(krnl)
            && *final(krnl) == (KernelK { allc_4k_mp: final(krnl).allc_4k_mp, ..*old(krnl) }) && final(krnl).allc_4k_mp.unchanged_except(&old(krnl).allc_4k_mp, allc_ptr)
            && final(krnl).allc_4k_mp.spec_index(allc_ptr).quota == old(krnl).allc_4k_mp.spec_index(allc_ptr).quota
            || final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(krnl))) && old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()) && final(steps).snapshot_k() == *final(krnl),
        old(steps).snapshot_k() == *old(krnl) ==> final(steps).view() == old(steps).view(),
        ret.view().state() is WriteLock,
        ret.view().thread_id() == final(lctx).thread_id(),
        ret.view().lock_id() == final(krnl).allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        final(krnl).allc_4k_mp.dom().contains(allc_ptr),
        final(krnl).allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().len() + room <= ALLOCATOR_MAX_WATERMARK,
        final(krnl).ctn_mp.dom().contains(old(krnl).pg_arr.spec_index(pg_idx).view().view().owning_container),
        final(krnl).ctn_mp.spec_index(old(krnl).pg_arr.spec_index(pg_idx).view().view().owning_container).view_rodata() == old(krnl).ctn_mp.spec_index(old(krnl).pg_arr.spec_index(pg_idx).view().view().owning_container).view_rodata(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] == old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int],
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_threads_unchanged(old(krnl).thrd_mp, final(krnl).thrd_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        forall|p: RwLockPageTableRoot| #![trigger old(lctx).pagetable_lock_map().dom().contains(p)] typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), p, TypedLockMode::Write)
            ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), p) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), p),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        forall|it: RwLockPageTableRoot| #![trigger old(lctx).iommu_table_lock_map().dom().contains(it)]
            typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), it, TypedLockMode::Write) && iommu_table_tlb_entries_present(old(krnl).iommu_tlb, old(krnl).irt.view(), old(krnl).it_mp, it)
                ==> iommu_table_tlb_entries_present(final(krnl).iommu_tlb, final(krnl).irt.view(), final(krnl).it_mp, it),
        held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
{
    proof { container_owned_pages_wf_backward_at(krnl.ctn_mp, krnl.pg_arr, pg_idx); held_kernel_objects_unchanged_reflexive(&*krnl, &*lctx); }
    let Tracked(cache_perm) = krnl.wlock_allocator_cache_4k(allc_ptr, cpu_id, Tracked(&mut *lctx));
    let len = krnl.allc_4k_mp.borrow_cache_typed(allc_ptr, cpu_id, Ghost(lctx.allocator_cache_4k_lock_map()), Tracked(&*lctx), Tracked(&cache_perm)).linked_list.len();
    if len > ALLOCATOR_MAX_WATERMARK - room {
        let Tracked(pool_perm) = krnl.wlock_allocator_global_pool_4k(allc_ptr, Tracked(&mut *lctx));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl) && kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl) && kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
            kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(old(krnl), &*krnl);
        }
        drain_4k_cache_batch(krnl, allc_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&cache_perm), Tracked(&pool_perm));
        krnl.wunlock_allocator_global_pool_4k(allc_ptr, Tracked(&mut *lctx), Tracked(pool_perm));
        proof {
            assert(lctx.allocator_global_pool_4k_lock_map() =~= old(lctx).allocator_global_pool_4k_lock_map());
            kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl);
            krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
        }
    } else {
        proof {
            if old(steps).snapshot_k() == *old(krnl) {
                enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
                kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl);
                krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
            }
        }
    }
    Tracked(cache_perm)
}

/// Unlink the table page `pg_ptr` that `scan` names from the write-held table `table` of the zombie `target` (its IOMMU
/// table when `iommu`) and return it through the write-held cache shard `cpu_id` of the 4K allocator `allc_ptr` of its owner, the
/// container of the write-held killer `thrd_ptr`, whose direct pending 4K refund grows by one.
pub(crate) fn kill_retire_table_page_to_cache(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, iommu: bool, table: RwLockPageTableRoot, scan: StructureScan, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr,
    allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, direct: &mut usize, Tracked(table_perm): Tracked<&LockPerm>, Tracked(page_perm): Tracked<&LockPerm>,
    Tracked(thread_perm): Tracked<&LockPerm>, Tracked(cache_perm): Tracked<&LockPerm>, Ghost(target): Ghost<RwLockProcessPtr>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        page_ptr_valid(pg_ptr),
        scan.spec_table_page() == Some(pg_ptr),
        table_perm.state() is WriteLock,
        table_perm.thread_id() == old(lctx).thread_id(),
        !iommu ==> {
            &&& old(krnl).pt_mp.dom().contains(table)
            &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), table, TypedLockMode::Write)
            &&& table_perm.lock_id() == old(krnl).pt_mp.spec_index(table).locking_thread()->Write_lock_id
            &&& old(krnl).prc_mp.spec_index(target).view().pagetable == table
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).structure_scan_wf(scan)
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).leaves_present()
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).lower.hidden_l1_tables_in_locked_windows()
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty()
            &&& old(krnl).pt_mp.spec_index(table).view().table_stale_cpus.view() == Set::<CpuId>::empty()
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).lower.l2_owner(p, i)]
                whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).lower.l2_perms.dom().contains(p) && pei_valid(i) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).lower.l2_owner(p, i) is None
        },
        iommu ==> {
            &&& old(krnl).it_mp.dom().contains(table)
            &&& typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), table, TypedLockMode::Write)
            &&& table_perm.lock_id() == old(krnl).it_mp.spec_index(table).locking_thread()->Write_lock_id
            &&& old(krnl).it_mp.spec_index(table).view().structure_scan_wf(scan)
        },
        old(krnl).prc_mp.dom().contains(target),
        old(krnl).prc_mp.spec_index(target).view().zombie,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write),
        page_perm.state() is WriteLock,
        page_perm.thread_id() == old(lctx).thread_id(),
        page_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: table, table_type: if iommu { IOMMU_TYPE } else { PT_TYPE } } }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container,
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_perm.state() is WriteLock,
        thread_perm.thread_id() == old(lctx).thread_id(),
        thread_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        *old(direct) == old(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view(),
        old(krnl).ctn_mp.dom().contains(old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container),
        old(krnl).ctn_mp.spec_index(old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container).view_rodata().view().allocator_ptr_4k == allc_ptr,
        old(krnl).allc_4k_mp.dom().contains(allc_ptr),
        old(krnl).allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().len() < ALLOCATOR_MAX_WATERMARK,
        typed_lock_map_contains_mode(old(lctx).allocator_cache_4k_lock_map(), (allc_ptr, cpu_id), TypedLockMode::Write),
        cache_perm.state() is WriteLock,
        cache_perm.thread_id() == old(lctx).thread_id(),
        cache_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(pg_ptr)),
            TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(pg_ptr)), mode: TypedLockMode::Write }),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, it_mp: final(krnl).it_mp, pg_arr: final(krnl).pg_arr, thrd_mp: final(krnl).thrd_mp, allc_4k_mp: final(krnl).allc_4k_mp, ..*old(krnl) }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        !iommu ==> {
            &&& final(krnl).it_mp == old(krnl).it_mp
            &&& final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, table)
            &&& final(krnl).pt_lower.view() == old(krnl).pt_lower.view().insert(table, final(krnl).pt_lower.view().spec_index(table))
            &&& final(krnl).pt_mp.spec_index(table).locking_thread() == old(krnl).pt_mp.spec_index(table).locking_thread()
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).leaves_present() ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), table).leaves_present()
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), table).lower.hidden_l1_tables_in_locked_windows()
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), table).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty()
            &&& final(krnl).pt_mp.spec_index(table).view().table_stale_cpus.view() == Set::<CpuId>::empty()
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), table).lower.l2_owner(p, i)]
                whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), table).lower.l2_perms.dom().contains(p) && pei_valid(i) ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), table).lower.l2_owner(p, i) is None
        },
        iommu ==> {
            &&& final(krnl).pt_mp == old(krnl).pt_mp
            &&& final(krnl).pt_lower == old(krnl).pt_lower
            &&& final(krnl).it_mp.unchanged_except(&old(krnl).it_mp, table)
            &&& final(krnl).it_mp.spec_index(table).locking_thread() == old(krnl).it_mp.spec_index(table).locking_thread()
            &&& old(krnl).it_mp.spec_index(table).view().leaves_present() ==> final(krnl).it_mp.spec_index(table).view().leaves_present()
        },
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(pg_ptr)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread(),
        final(krnl).thrd_mp.unchanged_except(&old(krnl).thrd_mp, thrd_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { direct_free_quota_pending_4k: final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k,
            ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
        *final(direct) == final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k.view(),
        *final(direct) == *old(direct) + 1,
        final(krnl).allc_4k_mp.dom().contains(allc_ptr),
        final(krnl).allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread() == old(krnl).allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread(),
        !iommu ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).page_closure().contains(pg_ptr)
            && whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), table).page_closure() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).page_closure().remove(pg_ptr),
        iommu ==> old(krnl).it_mp.spec_index(table).view().page_closure().contains(pg_ptr) && final(krnl).it_mp.spec_index(table).view().page_closure() == old(krnl).it_mp.spec_index(table).view().page_closure().remove(pg_ptr),
{
    let pg_idx = page_ptr2page_index(pg_ptr);
    let ghost owner = krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container;
    proof {
        page_array_wf_at(krnl.pg_arr, pg_idx); thread_perms_wf_map(krnl.thrd_mp); thread_perms_wf_at(krnl.thrd_mp, thrd_ptr);
        allocator_perms_wf_map(krnl.allc_4k_mp);
        allocator_perms_wf_at(krnl.allc_4k_mp, allc_ptr);
        assert(!krnl.allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().contains(pg_ptr)) by { allocator_free_4k_pages_wf_cache_at(krnl.allc_4k_mp, krnl.pg_arr, allc_ptr, cpu_id, pg_ptr); };
        lemma_container_allocator_4k_quota_bounded(&*krnl, owner);
        assert(krnl.allc_4k_mp.spec_index(allc_ptr).quota.view().value as int + *direct as int <= krnl.allc_4k_mp.spec_index(allc_ptr).total_free_pages.view()) by {
            container_thread_wf_thread_at(krnl.ctn_mp, krnl.thrd_mp, thrd_ptr); lemma_thread_pending_4k_quota_bounded(&*krnl, thrd_ptr, owner, krnl.thrd_mp.spec_index(thrd_ptr).view().container_depth);
        };
        process_perms_wf_at(krnl.prc_mp, target); process_emptied_tables_wf_at(krnl.prc_mp, krnl.pt_mp, krnl.pt_lower.view(), krnl.it_mp, krnl.pg_arr, target);
        if iommu {
            iommu_table_page_implies_unreferenced_by_structure_caches(*krnl, table, pg_ptr);
        } else {
            old(krnl).pt_mp.typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), table);
            held_table_page_under_unresolvable_path_with_empty_table_record_implies_unreferenced_by_structure_caches(*krnl, table, pg_ptr);
        }
    }
    let depth = krnl.thrd_mp.borrow_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(thread_perm)).container_depth;
    let Tracked(page_4k_perm) = if iommu {
        let Tracked(page_map_perm) = iommu_table_map_remove_table_page(&mut krnl.it_mp, table, scan, Tracked(&mut *lctx), Tracked(table_perm));
        page_map_to_page_perm(pg_ptr, Tracked(page_map_perm), &krnl.cpu_tlb, &krnl.cpu_arr, &krnl.pcid_needflush)
    } else if let StructureScan::L1 { l4i, l3i, l2i, l2_p, l1_p } = scan {
        let Tracked(page_map_perm) = pagetable_map_unlink_unresolvable_l1_page(&mut krnl.pt_mp, Tracked(krnl.pt_lower.borrow_mut()), table, l4i, l3i, l2i, l2_p, l1_p, &krnl.pg_arr,
            Tracked(&mut *lctx), Tracked(table_perm));
        page_map_to_page_perm(pg_ptr, Tracked(page_map_perm), &krnl.cpu_tlb, &krnl.cpu_arr, &krnl.pcid_needflush)
    } else {
        let Tracked(page_4k_perm) = pagetable_map_remove_table_page(&mut krnl.pt_mp, Tracked(krnl.pt_lower.borrow_mut()), table, scan, &krnl.pg_arr, &krnl.cpu_tlb, &krnl.cpu_arr,
            &krnl.pcid_needflush, Tracked(table_perm), Tracked(&mut *lctx), Tracked(table_perm));
        proof { if scan is L2 { assert(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), table).lower.window_stale_cpus =~= Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty()); } }
        Tracked(page_4k_perm)
    };
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(pg_idx);
    let (node_addr, node_perm) = page_array_retire_kernel_object_4k_to_cache(&mut krnl.pg_arr, pg_idx, Tracked(page_4k_perm), allc_ptr, cpu_id, Tracked(&*lctx), Tracked(page_perm));
    proof { lctx.update_lock_id(KernelObjId::Page(pg_idx), old_page_lock_id, krnl.pg_arr.lock_id_by_index(pg_idx)); }
    krnl.allc_4k_mp.push_cache_page_typed(allc_ptr, cpu_id, node_addr, node_perm, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
        Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(cache_perm));
    thread_map_add_free_quota_pending_4k(&mut krnl.thrd_mp, thrd_ptr, depth, direct, Tracked(&*lctx), Tracked(thread_perm));
    proof {
        assert(kill_retire_table_page_eof_transition_framing(*old(krnl), *krnl, iommu, table, pg_ptr, thrd_ptr, allc_ptr, cpu_id, node_addr)) by { reveal(kill_retire_table_page_eof_transition_framing); };
        kill_retire_table_page_eof(*old(krnl), *krnl, iommu, table, pg_ptr, thrd_ptr, allc_ptr, cpu_id, node_addr);
    }
}

/// Each page `kill_retire_pages(k, target)` retires is a valid page in `held`, allocated as a 4K kernel page to the
/// container of `target`, and outside shard `cpu_id` of that container's 4K allocator `allc_ptr`.
pub(crate) proof fn kill_retire_pages_held_and_owned(k: KernelK, target: RwLockProcessPtr, held: Set<PageIndex>, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId)
    requires
        k.inv(),
        k.prc_mp.dom().contains(target),
        held == kill_retire_pages(k, target).to_set(),
        k.ctn_mp.spec_index(k.prc_mp.spec_index(target).view_rodata().view().owning_container).view_rodata().view().allocator_ptr_4k == allc_ptr,
        index_valid(NUM_CPUS, cpu_id),
    ensures
        forall|i: int| #![trigger kill_retire_pages(k, target)[i]] 0 <= i < kill_retire_pages(k, target).len() ==> {
            let p = kill_retire_pages(k, target)[i];
            &&& index_valid(NUM_PAGES, p)
            &&& held.contains(p)
            &&& k.pg_arr.spec_index(p).view().view().state is Allocated4k
            &&& k.pg_arr.spec_index(p).view().view().owning_container == k.prc_mp.spec_index(target).view_rodata().view().owning_container
            &&& !k.allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().contains(page_index2page_ptr(p))
        },
{
    let process = k.prc_mp.spec_index(target).view();
    let ctn_ptr = k.prc_mp.spec_index(target).view_rodata().view().owning_container;
    let pt = whole_pagetable(k.pt_mp, k.pt_lower.view(), process.pagetable);
    process_perms_wf_at(k.prc_mp, target);
    process_pagetable_wf_process_at(k.prc_mp, k.pt_mp, target); process_iommu_table_wf_process_at(k.prc_mp, k.it_mp, target);
    container_process_wf_process_at(k.ctn_mp, k.prc_mp, target); container_perms_wf_at(k.ctn_mp, ctn_ptr);
    container_allocator_wf_at(k.ctn_mp, k.allc_4k_mp, k.allc_2m_mp, k.allc_1g_mp, ctn_ptr); allocator_perms_wf_at(k.allc_4k_mp, allc_ptr);
    pagetable_perms_wf_at(k.pt_mp, process.pagetable);
    assert(page_ptr_valid(target) && k.pg_arr.spec_index(page_ptr2page_index(target)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsProcess })) by { process_pages_wf_process_at(k.prc_mp, k.pg_arr, target); };
    pagetable_pages_wf_root_page_at(k.pt_mp, k.pt_lower.view(), k.pg_arr, process.pagetable);
    assert(pt.page_closure().contains(pt.cr3())) by { reveal(PageTableHigher::wf_l4); };
    pagetable_pages_wf_closure_page_at(k.pt_mp, k.pt_lower.view(), k.pg_arr, process.pagetable, pt.cr3());
    if let Some(it) = process.iommu_table {
        let it_view = k.it_mp.spec_index(it).view();
        iommu_table_perms_wf_at(k.it_mp, it);
        iommu_table_pages_wf_root_page_at(k.it_mp, k.pg_arr, it);
        assert(it_view.page_closure().contains(it_view.cr3)) by { reveal(PageTable::wf_l4); };
        iommu_table_pages_wf_closure_page_at(k.it_mp, k.pg_arr, it, it_view.cr3);
    }
    reveal(process_object_pages_owner_wf); page_ptr_roundtrip();
    reveal(allocator_free_4k_pages_wf); reveal(allocator_cpu_cache_4k_pages_wf);
}
} // verus!
