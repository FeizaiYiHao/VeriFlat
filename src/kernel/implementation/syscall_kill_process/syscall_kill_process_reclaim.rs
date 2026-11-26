use vstd::prelude::*;
use crate::*;
use super::syscall_kill_process_spec::*;
use super::syscall_kill_process_trace::*;
use super::syscall_kill_process_walk::*;
use super::syscall_kill_process_walk_spec::*;
use super::syscall_kill_process_reclaim_release::*;
use super::syscall_kill_process_retire::kill_retire_target;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_reclaim_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_reclaim_eof::*;

verus! {
/// Reclaim the empty target and retire it, walking its parent again; the parent is returned. A live target has its memory,
/// PCI functions, PCID, and quota reclaimed and becomes a zombie.
pub(crate) fn kill_reclaim_target(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&mut Map<RwLockProcessPtr, LockPerm>>,
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
        kill_walk_state(*old(krnl), *old(lctx), cpu_id, scope, prc_ptr, thrd_ptr, chain, None, KillStage::Walk, *cpu_perm, *process_perm, *thread_perm, *old(chain_perms)),
        0 < chain.len(),
        target == chain[chain.len() - 1],
        old(krnl).prc_mp.spec_index(target).view().children.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
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
        scope is Subtree
            ==> kill_process_table_count(final(steps).view().subrange(start, final(steps).view().len() as int), cpu_id)
                <= kill_process_table_count(old(steps).view().subrange(start, old(steps).view().len() as int), cpu_id) + process_tables_step_bound(),
        kill_process_retire_count(old(steps).view().subrange(start, old(steps).view().len() as int), cpu_id) + 1 <= kill_process_retire_count(final(steps).view().subrange(start, final(steps).view().len() as int), cpu_id),
        kill_walk_state(*final(krnl), *final(lctx), cpu_id, scope, prc_ptr, thrd_ptr, chain.drop_last(), None, KillStage::Walk, *cpu_perm, *process_perm, *thread_perm, *final(chain_perms)),
        parent == if chain.len() == 1 { prc_ptr } else { chain[chain.len() - 2] },
        chain.len() > 1 ==> parent != prc_ptr,
        final(krnl).prc_mp.spec_index(parent).view().children.view() == old(krnl).prc_mp.spec_index(parent).view().children.view().remove_value(target),
        forall|p: RwLockProcessPtr| #![trigger old(lctx).process_lock_map().dom().contains(p)]
            old(lctx).process_lock_map().dom().contains(p) && p != parent && p != target ==> final(krnl).prc_mp.dom().contains(p)
                && final(krnl).prc_mp.spec_index(p).view().children == old(krnl).prc_mp.spec_index(p).view().children,
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
            &&& final(krnl).ctn_mp.dom().contains(c)
            &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
            &&& final(krnl).ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
            &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(c).view().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view().uppertree_seq
            &&& typed_lock_map_contains_mode(old(lctx).container_lock_map(), c, TypedLockMode::Write)
                ==> final(krnl).ctn_mp.spec_index(c).view().root_process_removed.view() == old(krnl).ctn_mp.spec_index(c).view().root_process_removed.view()
            &&& final(krnl).ctn_mp.spec_index(c).view().children == old(krnl).ctn_mp.spec_index(c).view().children
        },
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view(),
{
    proof { process_perms_wf_implies_map_perms_wf(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, target); }
    let zombie = {
        let tracked target_perm = chain_perms.tracked_borrow(target);
        krnl.prc_mp.borrow_typed(target, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(target_perm)).zombie
    };
    if zombie {
        kill_retire_zombie(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, thrd_ptr, target, Ghost(chain), Tracked(&*chain_perms), Tracked(cpu_perm),
            Tracked(process_perm), Tracked(thread_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    } else {
        kill_reclaim_live(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, thrd_ptr, target, Ghost(chain), Tracked(&*chain_perms), Tracked(cpu_perm),
            Tracked(process_perm), Tracked(thread_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    }
    proof {
        process_perms_wf_at(krnl.prc_mp, target);
        assert(kernel_steps_prefix_unchanged(old(steps).view(), old(steps).view())) by { reveal(kernel_steps_prefix_unchanged); };
        steps_extended_implies_kill_process_retire_count_monotone(old(steps).view(), steps.view(), start, cpu_id);
    }
    let parent = kill_retire_target(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, thrd_ptr, target, Ghost(chain), Tracked(&mut *chain_perms),
        Tracked(cpu_perm), Tracked(process_perm), Tracked(thread_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    proof { steps_extended_implies_kill_process_table_count_le_len_added(old(steps).view(), steps.view(), start, cpu_id); }
    parent
}

/// Send the empty target, already a zombie, straight to retiring.
pub(crate) fn kill_retire_zombie(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>,
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
        kill_walk_state(*old(krnl), *old(lctx), cpu_id, scope, prc_ptr, thrd_ptr, chain, None, KillStage::Walk, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
        0 < chain.len(),
        target == chain[chain.len() - 1],
        old(krnl).prc_mp.spec_index(target).view().children.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view().zombie,
    ensures
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        forall|p: RwLockProcessPtr| #![trigger old(lctx).process_lock_map().dom().contains(p)]
            old(lctx).process_lock_map().dom().contains(p) ==> final(krnl).prc_mp.dom().contains(p)
                && final(krnl).prc_mp.spec_index(p).view().children == old(krnl).prc_mp.spec_index(p).view().children,
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        final(steps).view().len() <= old(steps).view().len() + 1,
        old(steps).view().len() <= final(steps).view().len(),
        kill_walk_state(*final(krnl), *final(lctx), cpu_id, scope, prc_ptr, thrd_ptr, chain, None, KillStage::Retire, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
        ({
            &&& final(krnl).prc_mp.spec_index(target).view() == old(krnl).prc_mp.spec_index(target).view()
            &&& final(krnl).prc_mp.spec_index(target).view_rodata() == old(krnl).prc_mp.spec_index(target).view_rodata()
            &&& final(krnl).prc_mp.spec_index(target).locking_thread() == old(krnl).prc_mp.spec_index(target).locking_thread()
            &&& final(krnl).prc_mp.spec_index(target).control() == old(krnl).prc_mp.spec_index(target).control()
        }),
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
            &&& final(krnl).ctn_mp.dom().contains(c)
            &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
            &&& final(krnl).ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
            &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(c).view().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view().uppertree_seq
            &&& typed_lock_map_contains_mode(old(lctx).container_lock_map(), c, TypedLockMode::Write)
                ==> final(krnl).ctn_mp.spec_index(c).view().root_process_removed.view() == old(krnl).ctn_mp.spec_index(c).view().root_process_removed.view()
            &&& final(krnl).ctn_mp.spec_index(c).view().children == old(krnl).ctn_mp.spec_index(c).view().children
        },
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().control() == old(krnl).cpu_arr.spec_index(cpu_id).view().control(),
{
    let ghost before = *krnl;
    let ghost before_lctx = *lctx;
    let ghost before_steps = steps.view();
    krnl.set_thread_syscall_progress(thrd_ptr, Ghost(kill_scope_progress(scope, target, KillStage::Retire)), Tracked(&*lctx), Tracked(thread_perm));
    let ghost after = *krnl;
    proof {
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thrd_ptr);
        process_perms_wf_at(krnl.prc_mp, target);
        let before_u = kernel_k_to_kernel_u(before);
        kill_step_pre_from_k(&before, &before_lctx, cpu_id, prc_ptr, thrd_ptr, target, KillStage::Walk, scope); kill_zombie_retire_pre_from_k(&before, target);
        kernel_thread_syscall_progress_changed_implies_u_step(&before, &after, thrd_ptr);
        kill_zombie_retire_step_from_u(before_u, kernel_k_to_kernel_u(after), cpu_id, thrd_ptr, target, scope);
        kill_trace_push(&*steps, before_steps, start, pre, before_u, kernel_k_to_kernel_u(after), cpu_id, ctx);
    }
}

/// Reclaim the empty live target: write-lock its page table with every cpu listed stale, hide every user root entry, flush
/// its PCID from every cpu once, release its PCI functions while write-locking its IOMMU table, reclaim the page of every non-empty
/// leaf, reclaim the page of every IOMMU 4K leaf, refunding the quota of the freed pages, return the target's quota of every
/// size, unlock its tables, and make it a zombie.
pub(crate) fn kill_reclaim_live(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>,
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
        kill_walk_state(*old(krnl), *old(lctx), cpu_id, scope, prc_ptr, thrd_ptr, chain, None, KillStage::Walk, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
        0 < chain.len(),
        target == chain[chain.len() - 1],
        old(krnl).prc_mp.spec_index(target).view().children.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        !old(krnl).prc_mp.spec_index(target).view().zombie,
    ensures
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        forall|p: RwLockProcessPtr| #![trigger old(lctx).process_lock_map().dom().contains(p)]
            old(lctx).process_lock_map().dom().contains(p) ==> final(krnl).prc_mp.dom().contains(p)
                && final(krnl).prc_mp.spec_index(p).view().children == old(krnl).prc_mp.spec_index(p).view().children,
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        scope is Subtree ==> final(steps).view().len() <= old(steps).view().len() + 68_853_694_464 + 4 * MAX_CONTAINER_TREE_DEPTH + NUM_CPUS + 523,
        kill_walk_state(*final(krnl), *final(lctx), cpu_id, scope, prc_ptr, thrd_ptr, chain, None, KillStage::Retire, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
        final(krnl).prc_mp.spec_index(target).view().zombie,
        final(krnl).prc_mp.spec_index(target).view().children.view().len() == 0,
        final(krnl).prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
            &&& final(krnl).ctn_mp.dom().contains(c)
            &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
            &&& final(krnl).ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
            &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(c).view().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view().uppertree_seq
            &&& typed_lock_map_contains_mode(old(lctx).container_lock_map(), c, TypedLockMode::Write)
                ==> final(krnl).ctn_mp.spec_index(c).view().root_process_removed.view() == old(krnl).ctn_mp.spec_index(c).view().root_process_removed.view()
            &&& final(krnl).ctn_mp.spec_index(c).view().children == old(krnl).ctn_mp.spec_index(c).view().children
        },
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view(),
{
    hide(Set::is_empty);
    proof { process_perms_wf_implies_map_perms_wf(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, target); }
    let target_container = krnl.prc_mp.borrow_rodata(target).borrow().owning_container;
    proof { thread_perms_wf_implies_map_perms_wf(krnl.thrd_mp); thread_perms_wf_at(krnl.thrd_mp, thrd_ptr); }
    let thread_container = krnl.thrd_mp.borrow_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(thread_perm)).owning_container;
    proof {
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr);
        container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, target); container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, prc_ptr);
        assert(target_container == thread_container <==> scope is Subtree);
    }
    let (pagetable, iommu_table) = {
        let tracked target_perm = chain_perms.tracked_borrow(target);
        let process = krnl.prc_mp.borrow_typed(target, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(target_perm));
        (process.pagetable, process.iommu_table)
    };
    let ghost entry_pt = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
    let Tracked(pagetable_perm) = kill_reclaim_lock_table(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, thrd_ptr, target, Ghost(chain), Tracked(chain_perms),
        Tracked(cpu_perm), Tracked(process_perm), Tracked(thread_perm), pagetable, iommu_table, Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    kill_reclaim_hide_roots(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, thrd_ptr, target, Ghost(chain), Tracked(chain_perms), Tracked(cpu_perm),
        Tracked(process_perm), Tracked(thread_perm), pagetable, iommu_table, Tracked(&pagetable_perm), Ghost(entry_pt), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    proof { process_perms_wf_at(krnl.prc_mp, target); }
    let (cr3, pcid) = {
        let target_ro = krnl.prc_mp.borrow_rodata(target).borrow();
        (target_ro.cr3, target_ro.pcid)
    };
    kill_reclaim_flush(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, thrd_ptr, target, Ghost(chain), Tracked(chain_perms), Tracked(cpu_perm),
        Tracked(process_perm), Tracked(thread_perm), pagetable, iommu_table, Tracked(&pagetable_perm), Ghost(entry_pt), cr3, pcid, Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    let Tracked(iommu_perm) = kill_reclaim_unown_functions(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, thrd_ptr, target, Ghost(chain), Tracked(chain_perms),
        Tracked(cpu_perm), Tracked(process_perm), Tracked(thread_perm), pagetable, iommu_table, Tracked(&pagetable_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    kill_reclaim_nonempty_leaves(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, thrd_ptr, target, Ghost(chain), Tracked(chain_perms), Tracked(cpu_perm),
        Tracked(process_perm), Tracked(thread_perm), pagetable, iommu_table, Tracked(&pagetable_perm), Tracked(&iommu_perm), Ghost(entry_pt), target_container == thread_container,
        Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    let ghost held_pt = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
    if let Some(it) = iommu_table {
        kill_reclaim_iommu_leaves(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, thrd_ptr, target, Ghost(chain), Tracked(chain_perms), Tracked(cpu_perm),
            Tracked(process_perm), Tracked(thread_perm), pagetable, it, Tracked(&pagetable_perm), Tracked(iommu_perm.tracked_borrow()), Ghost(held_pt),
            target_container == thread_container, Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    }
    kill_reclaim_return_quota_and_zombify(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, thrd_ptr, target, Ghost(chain), Tracked(chain_perms),
        Tracked(cpu_perm), Tracked(process_perm), Tracked(thread_perm), pagetable, iommu_table, Tracked(pagetable_perm), Tracked(iommu_perm), Ghost(start), Ghost(pre),
        Ghost(scope), Ghost(ctx));
}

/// Write-lock the empty live target's page table, list every cpu stale for it, and record that nothing is flushed yet.
pub(crate) fn kill_reclaim_lock_table(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, pagetable: RwLockPageTableRoot,
    iommu_table: Option<RwLockPageTableRoot>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
) -> (ret: Tracked<LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        kill_walk_state(*old(krnl), *old(lctx), cpu_id, scope, prc_ptr, thrd_ptr, chain, None, KillStage::Walk, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
        0 < chain.len(),
        target == chain[chain.len() - 1],
        old(krnl).prc_mp.spec_index(target).view().children.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        !old(krnl).prc_mp.spec_index(target).view().zombie,
        old(krnl).prc_mp.spec_index(target).view().pagetable == pagetable,
        old(krnl).prc_mp.spec_index(target).view().iommu_table == iommu_table,
    ensures
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        forall|p: RwLockProcessPtr| #![trigger old(lctx).process_lock_map().dom().contains(p)]
            old(lctx).process_lock_map().dom().contains(p) ==> final(krnl).prc_mp.dom().contains(p)
                && final(krnl).prc_mp.spec_index(p).view().children == old(krnl).prc_mp.spec_index(p).view().children,
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        final(steps).view().len() <= old(steps).view().len() + 1,
        kill_reclaim_state(*final(krnl), *final(lctx), cpu_id, scope, prc_ptr, thrd_ptr, chain, KillStage::Reclaim { flushed: false }, *cpu_perm, *process_perm, *thread_perm,
            *chain_perms, pagetable, iommu_table, ret.view(), None),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower,
        final(krnl).pt_mp.spec_index(pagetable).view().higher == (PageTableHigher { table_stale_cpus: final(krnl).pt_mp.spec_index(pagetable).view().higher.table_stale_cpus, ..old(krnl).pt_mp.spec_index(pagetable).view().higher }),
        final(krnl).pt_mp.spec_index(pagetable).view().higher.table_stale_cpus.view() == Set::range(0usize, NUM_CPUS),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.hidden_l1_tables_in_locked_windows(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(p, i)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_perms.dom().contains(p) && pei_valid(i) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(p, i) is None,
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
            &&& final(krnl).ctn_mp.dom().contains(c)
            &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
            &&& final(krnl).ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
            &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(c).view().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view().uppertree_seq
            &&& typed_lock_map_contains_mode(old(lctx).container_lock_map(), c, TypedLockMode::Write)
                ==> final(krnl).ctn_mp.spec_index(c).view().root_process_removed.view() == old(krnl).ctn_mp.spec_index(c).view().root_process_removed.view()
            &&& final(krnl).ctn_mp.spec_index(c).view().children == old(krnl).ctn_mp.spec_index(c).view().children
        },
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().control() == old(krnl).cpu_arr.spec_index(cpu_id).view().control(),
{
    let ghost before = *krnl;
    let ghost before_lctx = *lctx;
    let ghost before_steps = steps.view();
    proof {
        process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, target);
        krnl.default_pagetable_wf_at(pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
    }
    let Tracked(pagetable_perm) = krnl.wlock_pagetable(pagetable, Tracked(&mut *lctx));
    proof { assert(krnl.prc_mp.spec_index(target).view().state.view() is Killing) by { process_perms_wf_implies_map_perms_wf(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, target); }; }
    krnl.set_thread_syscall_progress(thrd_ptr, Ghost(kill_scope_progress(scope, target, KillStage::Reclaim { flushed: false })), Tracked(&*lctx), Tracked(thread_perm));
    let ghost after = *krnl;
    let ghost after_lctx = *lctx;
    proof { enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); }
    krnl.replace_table_stale_cpus(pagetable, Ghost(TableStaleUpdate::Set { cpus: Set::range(0usize, NUM_CPUS) }), Tracked(&*lctx), Tracked(&pagetable_perm));
    proof {
        let stale = *krnl;
        let before_u = kernel_k_to_kernel_u(before);
        kill_step_pre_from_k(&before, &before_lctx, cpu_id, prc_ptr, thrd_ptr, target, KillStage::Walk, scope); kill_lock_table_pre_from_k(&before, target);
        kernel_cpu_nonlock_fields_unchanged_for_equal(after.cpu_arr, stale.cpu_arr); kernel_cpu_tlb_updated_implies_u_step(&after, &stale);
        kill_lock_table_step_from_k(&before, &after, &stale, &after_lctx, cpu_id, thrd_ptr, target, pagetable, scope);
        assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thrd_ptr);
        process_perms_wf_at(krnl.prc_mp, target);
        kill_trace_push(&*steps, before_steps, start, pre, before_u, kernel_k_to_kernel_u(stale), cpu_id, ctx);
        pagetable_perms_wf_at(krnl.pt_mp, pagetable);
    }
    Tracked(pagetable_perm)
}

/// Release every PCI function of the page table `pagetable` of the hidden, flushed live target. A target holding a function
/// takes the root-table lock and, when it has the IOMMU table `iommu_table`, that table's write lock, detaches each function
/// while the table drops its DID, makes each function unowned and empties the array, and releases the root table; a target
/// holding none only write-locks its IOMMU table, if any, and takes no root-table lock. The IOMMU table stays write-held. A
/// target holding no function and no IOMMU table records no step.
pub(crate) fn kill_reclaim_unown_functions(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, pagetable: RwLockPageTableRoot,
    iommu_table: Option<RwLockPageTableRoot>, Tracked(pagetable_perm): Tracked<&LockPerm>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>,
    Ghost(ctx): Ghost<KillTraceCtx>,
) -> (ret: Tracked<Option<LockPerm>>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        kill_reclaim_state(*old(krnl), *old(lctx), cpu_id, scope, prc_ptr, thrd_ptr, chain, KillStage::Reclaim { flushed: true }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
            iommu_table, *pagetable_perm, None),
        target == chain[chain.len() - 1],
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.pagetable_window_locks.dom() =~= Set::<WindowVa>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
        old(krnl).pt_mp.spec_index(pagetable).view().higher.table_stale_cpus.view() == Set::<CpuId>::empty(),
        forall|l4i: L4Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i) is None,
    ensures
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        final(steps).view().len() <= old(steps).view().len() + 1,
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_reclaim_state(*final(krnl), *final(lctx), cpu_id, scope, prc_ptr, thrd_ptr, chain, KillStage::Reclaim { flushed: true }, *cpu_perm, *process_perm, *thread_perm, *chain_perms, pagetable,
            iommu_table, *pagetable_perm, ret.view()),
        (ret.view() is Some) == (iommu_table is Some),
        forall|p: RwLockProcessPtr| #![trigger old(lctx).process_lock_map().dom().contains(p)]
            old(lctx).process_lock_map().dom().contains(p) ==> final(krnl).prc_mp.dom().contains(p)
                && final(krnl).prc_mp.spec_index(p).view().children == old(krnl).prc_mp.spec_index(p).view().children,
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
            &&& final(krnl).ctn_mp.dom().contains(c)
            &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
            &&& final(krnl).ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
            &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(c).view().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view().uppertree_seq
            &&& typed_lock_map_contains_mode(old(lctx).container_lock_map(), c, TypedLockMode::Write)
                ==> final(krnl).ctn_mp.spec_index(c).view().root_process_removed.view() == old(krnl).ctn_mp.spec_index(c).view().root_process_removed.view()
            &&& final(krnl).ctn_mp.spec_index(c).view().children == old(krnl).ctn_mp.spec_index(c).view().children
        },
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view(),
        final(krnl).pt_mp.spec_index(pagetable).view().higher.pci.view().dom() =~= Set::<PciBdf>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_1g().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.pagetable_window_locks.dom() =~= Set::<WindowVa>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower,
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
        final(krnl).pt_mp.spec_index(pagetable).view().higher.table_stale_cpus.view() == Set::<CpuId>::empty(),
        forall|l4i: L4Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i) is None,
        iommu_table is Some ==> final(krnl).it_mp.spec_index(iommu_table->Some_0).view().leaves_present(),
        iommu_table is Some ==> final(krnl).it_mp.spec_index(iommu_table->Some_0).view().did is None,
{
    let ghost before = *krnl;
    let ghost before_lctx = *lctx;
    let ghost before_steps = steps.view();
    proof {
        pagetable_perms_wf_implies_map_perms_wf(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); process_perms_wf_implies_map_perms_wf(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, target);
        process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, target); process_iommu_table_wf_process_at(krnl.prc_mp, krnl.it_mp, target);
    }
    let holds = !krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_perm)).higher.pci.is_empty();
    if !holds && iommu_table.is_none() {
        proof { held_kernel_objects_unchanged_reflexive(&*krnl, &*lctx); }
        return Tracked(None);
    }
    let ghost mut mid = *krnl;
    let Tracked(iommu_perm) = if holds {
        let Tracked(irt_perm) = krnl.wlock_iommu_root_table(Tracked(&mut *lctx));
        let iommu_perm = match iommu_table {
            Some(it) => {
                let Tracked(perm) = krnl.wlock_iommu_table(it, Tracked(&mut *lctx));
                let ghost locked = *krnl;
                proof { iommu_table_perms_wf_implies_map_perms_wf(krnl.it_mp); }
                iommu_root_table_detach_array(&mut krnl.irt, &mut krnl.iommu_tlb, &mut krnl.it_mp, it,
                    &krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_perm)).higher.pci, Ghost(locked), Tracked(&*lctx),
                    Tracked(&irt_perm), Tracked(&perm));
                proof {
                    assert(locked.it_mp.spec_index(it).view().did matches Some(d) ==> krnl.iommu_tlb.spec_index(d).tlb_4k() =~= Map::empty() && krnl.iommu_tlb.spec_index(d).tlb_2m() =~= Map::empty()
                        && krnl.iommu_tlb.spec_index(d).tlb_1g() =~= Map::empty() && krnl.iommu_tlb.structure_cache(d).is_empty()) by {
                        iommu_root_table_process_wf_table_at(locked.irt.view(), locked.prc_mp, locked.it_mp, it);
                        if let Some(d) = locked.it_mp.spec_index(it).view().did {
                            let anchor = pci_bdf_of_did(d);
                            pci_function_ownership_wf_function_at(locked.irt.view(), locked.prc_mp, locked.pt_mp, anchor.0, anchor.1, anchor.2);
                        }
                    };
                    assert(kill_unown_detach_eof_transition_framing(locked, *krnl, pagetable, it) && krnl.it_mp.spec_index(it).view().leaves_present()) by {
                        reveal(kill_unown_detach_eof_transition_framing);
                    };
                    kill_unown_detach_eof(locked, *krnl, pagetable, it);
                }
                Tracked(Some(perm))
            },
            None => Tracked(None),
        };
        proof { mid = *krnl; }
        krnl.release_pci_functions(pagetable, Tracked(&*lctx), Tracked(pagetable_perm), Tracked(&irt_perm));
        krnl.wunlock_iommu_root_table(Tracked(&mut *lctx), Tracked(irt_perm));
        iommu_perm
    } else {
        let it = iommu_table.unwrap();
        proof {
            iommu_root_table_process_wf_table_at(krnl.irt.view(), krnl.prc_mp, krnl.it_mp, it);
            if let Some(d) = krnl.it_mp.spec_index(it).view().did {
                let anchor = pci_bdf_of_did(d);
                pci_function_ownership_wf_function_at(krnl.irt.view(), krnl.prc_mp, krnl.pt_mp, anchor.0, anchor.1, anchor.2);
            }
        }
        let Tracked(perm) = krnl.wlock_iommu_table(it, Tracked(&mut *lctx));
        proof {
            enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
            mid = *krnl;
            assert(krnl.pt_mp.spec_index(pagetable).view().higher.pci.view() =~= Map::<PciBdf, Set<PciBarMapping>>::empty());
        }
        Tracked(Some(perm))
    };
    let ghost after = *krnl;
    proof {
        if let Some(it) = iommu_table {
            iommu_table_perms_wf_implies_map_perms_wf(krnl.it_mp); iommu_table_perms_wf_at(krnl.it_mp, it);
        }
        kill_step_pre_from_k(&before, &before_lctx, cpu_id, prc_ptr, thrd_ptr, target, KillStage::Reclaim { flushed: true }, scope);
        kill_reclaim_pre_from_k(&before, &before_lctx, cpu_id, thrd_ptr, target, KillStage::Reclaim { flushed: true }, pagetable, iommu_table);
        kill_unown_step_from_k(&before, &mid, &after, &*lctx, cpu_id, target, pagetable, iommu_table);
        assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
        krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
        kill_trace_push(&*steps, before_steps, start, pre, kernel_k_to_kernel_u(before), kernel_k_to_kernel_u(after), cpu_id, ctx);
    }
    Tracked(iommu_perm)
}
} // verus!
