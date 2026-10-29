use vstd::prelude::*;
use crate::*;
use super::super::syscall_kill_process::syscall_kill_process_spec::*;
use super::super::syscall_kill_process::syscall_kill_process_walk::*;
use super::super::syscall_kill_process::syscall_kill_process_reclaim::{kill_reclaim_target, kill_reassign_functions, kill_retire_zombie, kill_reclaim_live};
use super::syscall_kill_container_retire_root::kill_container_retire_root;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_trace::kill_container_trace_push;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_cpus_trace::kill_container_cpus_pre_from_k;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_walk_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_walk_trace::*;

verus! {
/// Kill every process of the target `target`, which has no child container: mark its root process, walk the process
/// tree below it as a process kill scoped to the container, and retire the emptied root.
pub(crate) fn kill_container_kill_processes(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, owner_ptr: RwLockContainerPtr, target: RwLockContainerPtr, killer_info: KillerInfo, Ghost(chain): Ghost<Seq<RwLockContainerPtr>>,
    Tracked(chain_perms): Tracked<&Map<RwLockContainerPtr, LockPerm>>, Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>,
    Tracked(thread_perm): Tracked<&LockPerm>, Tracked(owner_perm): Tracked<&LockPerm>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        ctx is Container,
        kill_container_walk_state(*old(krnl), *old(lctx), cpu_id, process_ptr, thread_ptr, owner_ptr, killer_info, chain, *cpu_perm, *process_perm, *thread_perm, *owner_perm,
            *chain_perms),
        0 < chain.len(),
        target == chain[chain.len() - 1],
        old(krnl).ctn_mp.spec_index(target).view().children.view().len() == 0,
        !old(krnl).ctn_mp.spec_index(target).view_ghost().owned_processes.view().is_empty(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_container_walk_state(*final(krnl), *final(lctx), cpu_id, process_ptr, thread_ptr, owner_ptr, killer_info, chain, *cpu_perm, *process_perm, *thread_perm, *owner_perm,
            *chain_perms),
        final(krnl).ctn_mp.spec_index(target).view_ghost().owned_processes.view().is_empty(),
        final(krnl).ctn_mp.spec_index(target).view().children.view().len() == 0,
        final(krnl).ctn_mp.spec_index(owner_ptr).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(owner_ptr).view_ghost().subtree_set,
{
    let ghost scope = KillScope::Container { container: target };
    let tracked container_perm = chain_perms.tracked_borrow(target);
    let (root_ptr, Tracked(pchain_perms)) = kill_container_mark_root(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, owner_ptr, target,
        killer_info, Ghost(chain), Tracked(chain_perms), Tracked(cpu_perm), Tracked(process_perm), Tracked(thread_perm), Tracked(owner_perm), Ghost(start), Ghost(pre), Ghost(ctx));
    let tracked mut pchain_perms = pchain_perms;
    let ghost marked_k = *krnl;
    let ghost marked_lctx = *lctx;
    let ghost mut pchain: Seq<RwLockProcessPtr> = seq![root_ptr];
    let mut ptarget = root_ptr;
    let mut done = false;
    while !done
        invariant
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.kernel_view_locking_state() is Acquire,
            steps.snapshot_k() == *krnl,
            0 <= start <= old(steps).view().len() <= steps.view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            kill_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, ctx),
            ctx is Container,
            scope == (KillScope::Container { container: target }),
            kill_walk_state(*krnl, *lctx, cpu_id, scope, process_ptr, thread_ptr, pchain, None, KillStage::Walk, *cpu_perm, *process_perm, *thread_perm, pchain_perms),
            0 < pchain.len(),
            ptarget == pchain[pchain.len() - 1],
            pchain[0] == root_ptr,
            done ==> pchain.len() == 1,
            done ==> krnl.prc_mp.spec_index(ptarget).view().children.view().len() == 0 && krnl.prc_mp.spec_index(ptarget).view().owned_threads.view().len() == 0,
            killer_info.process == process_ptr,
            lctx.container_lock_map() == marked_lctx.container_lock_map(),
            krnl.cpu_arr.spec_index(cpu_id).view().view().view() == marked_k.cpu_arr.spec_index(cpu_id).view().view().view(),
            forall|c: RwLockContainerPtr| #![trigger marked_lctx.container_lock_map().dom().contains(c)] marked_lctx.container_lock_map().dom().contains(c) ==> {
                &&& krnl.ctn_mp.dom().contains(c)
                &&& krnl.ctn_mp.spec_index(c).locking_thread() == marked_k.ctn_mp.spec_index(c).locking_thread()
                &&& krnl.ctn_mp.spec_index(c).killer_info() == marked_k.ctn_mp.spec_index(c).killer_info()
                &&& krnl.ctn_mp.spec_index(c).view_rodata() == marked_k.ctn_mp.spec_index(c).view_rodata()
                &&& krnl.ctn_mp.spec_index(c).view_ghost().uppertree_seq == marked_k.ctn_mp.spec_index(c).view_ghost().uppertree_seq
                &&& krnl.ctn_mp.spec_index(c).view_ghost().subtree_set == marked_k.ctn_mp.spec_index(c).view_ghost().subtree_set
                &&& krnl.ctn_mp.spec_index(c).view().children == marked_k.ctn_mp.spec_index(c).view().children
                &&& c != target ==> krnl.ctn_mp.spec_index(c).view_ghost().owned_processes == marked_k.ctn_mp.spec_index(c).view_ghost().owned_processes
            },
        decreases
            krnl.ctn_mp.spec_index(target).view_ghost().owned_processes.view().len(), usize::MAX as int + 1 - pchain.len(),
            if done { 0int } else { krnl.prc_mp.spec_index(ptarget).view().owned_threads.view().len() as int + 1 },
    {
        proof {
            process_perms_wf_map(krnl.prc_mp);
            process_perms_wf_at(krnl.prc_mp, ptarget);
            krnl.prc_mp.spec_index(ptarget).view().children.lemma_len_view(); krnl.prc_mp.spec_index(ptarget).view().owned_threads.lemma_len_view();
        }
        let (has_children, has_threads) = {
            let tracked ptarget_perm = pchain_perms.tracked_borrow(ptarget);
            let process = krnl.prc_mp.borrow_typed(ptarget, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(ptarget_perm));
            (process.children.len() != 0, process.owned_threads.len() != 0)
        };
        if has_children {
            let next = kill_mark_child(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, ptarget, killer_info, Ghost(pchain),
                Tracked(&mut pchain_perms), Tracked(cpu_perm), Tracked(process_perm), Tracked(thread_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
            proof { pchain = pchain.push(next); }
            ptarget = next;
        } else if has_threads {
            kill_first_thread(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, ptarget, killer_info, Ghost(pchain), Tracked(&pchain_perms),
                Tracked(cpu_perm), Tracked(process_perm), Tracked(thread_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
        } else if ptarget == root_ptr {
            done = true;
        } else {
            let ghost owned = krnl.ctn_mp.spec_index(target).view_ghost().owned_processes.view();
            proof { container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, ptarget); }
            let parent = kill_reclaim_target(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, ptarget, Ghost(pchain), Tracked(&mut pchain_perms),
                Tracked(cpu_perm), Tracked(process_perm), Tracked(thread_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
            proof { vstd::set::lemma_set_remove_len(owned, ptarget); pchain = pchain.drop_last(); }
            ptarget = parent;
        }
    }
    kill_reassign_functions(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, ptarget, Ghost(pchain), Tracked(&pchain_perms), Tracked(cpu_perm),
        Tracked(process_perm), Tracked(thread_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    proof { process_perms_wf_map(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, ptarget); }
    let zombie = {
        let tracked ptarget_perm = pchain_perms.tracked_borrow(ptarget);
        krnl.prc_mp.borrow_typed(ptarget, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(ptarget_perm)).zombie
    };
    if zombie {
        kill_retire_zombie(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, ptarget, Ghost(pchain), Tracked(&pchain_perms), Tracked(cpu_perm),
            Tracked(process_perm), Tracked(thread_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    } else {
        kill_reclaim_live(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, ptarget, Ghost(pchain), Tracked(&pchain_perms), Tracked(cpu_perm),
            Tracked(process_perm), Tracked(thread_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    }
    kill_container_retire_root(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, ptarget, Ghost(pchain), Tracked(&mut pchain_perms),
        Tracked(cpu_perm), Tracked(process_perm), Tracked(thread_perm), Tracked(container_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    proof {
        process_perms_wf_map(krnl.prc_mp); krnl.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), process_ptr);
        krnl.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr);
    }
}

/// Mark and write-lock the root process of the target `target`, which has no child container but owns processes, and
/// walk that process as a process kill scoped to the container. The killer's own process marks no root, so the root
/// carries no mark.
pub(crate) fn kill_container_mark_root(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, owner_ptr: RwLockContainerPtr, target: RwLockContainerPtr, killer_info: KillerInfo, Ghost(chain): Ghost<Seq<RwLockContainerPtr>>,
    Tracked(chain_perms): Tracked<&Map<RwLockContainerPtr, LockPerm>>, Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>,
    Tracked(thread_perm): Tracked<&LockPerm>, Tracked(owner_perm): Tracked<&LockPerm>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(ctx): Ghost<KillTraceCtx>,
) -> (ret: (RwLockProcessPtr, Tracked<Map<RwLockProcessPtr, LockPerm>>))
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        ctx is Container,
        kill_container_walk_state(*old(krnl), *old(lctx), cpu_id, process_ptr, thread_ptr, owner_ptr, killer_info, chain, *cpu_perm, *process_perm, *thread_perm, *owner_perm,
            *chain_perms),
        0 < chain.len(),
        target == chain[chain.len() - 1],
        old(krnl).ctn_mp.spec_index(target).view().children.view().len() == 0,
        !old(krnl).ctn_mp.spec_index(target).view_ghost().owned_processes.view().is_empty(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_walk_state(*final(krnl), *final(lctx), cpu_id, KillScope::Container { container: target }, process_ptr, thread_ptr, seq![ret.0], None, KillStage::Walk, *cpu_perm,
            *process_perm, *thread_perm, ret.1.view()),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c)
            ==> final(krnl).ctn_mp.dom().contains(c) && final(krnl).ctn_mp.spec_index(c) == old(krnl).ctn_mp.spec_index(c),
{
    let ghost before = *krnl;
    let ghost before_lctx = *lctx;
    let ghost before_steps = steps.view();
    proof { container_perms_wf_map(krnl.ctn_mp); container_perms_wf_at(krnl.ctn_mp, target); }
    let root_ptr = {
        let tracked target_perm = chain_perms.tracked_borrow(target);
        krnl.ctn_mp.borrow_typed(target, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(target_perm)).root_process
    };
    proof {
        let tree = krnl.ctn_mp.spec_index(target).view_ghost().owned_processes.view();
        container_process_wf_root_at(krnl.ctn_mp, krnl.prc_mp, target); container_process_wf_container_at(krnl.ctn_mp, krnl.prc_mp, target, root_ptr);
        container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, root_ptr); per_container_process_tree_wf_at(krnl.ctn_mp, krnl.prc_mp, target);
        process_root_wf_at(root_ptr, tree, krnl.prc_mp, root_ptr); process_children_parent_wf_parent_at(root_ptr, tree, krnl.prc_mp, root_ptr);
        if let Some(parent_ptr) = krnl.prc_mp.spec_index(root_ptr).view_rodata().view().parent { process_children_parent_wf_at(root_ptr, tree, krnl.prc_mp, parent_ptr, root_ptr); }
        assert(root_ptr != process_ptr);
        assert(krnl.prc_mp.spec_index(root_ptr).view_rodata().view().owning_container != krnl.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container) by {
            container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, process_ptr);
        };
        assert(!krnl.prc_mp.spec_index(root_ptr).being_killed()) by {
            process_kill_mark_wf_at(krnl.ctn_mp, krnl.prc_mp, root_ptr); krnl.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), process_ptr);
            krnl.prc_mp.typed_lock_map_aligned_locked_at(lctx.process_lock_map(), lctx.thread_id(), root_ptr);
        };
    }
    let Tracked(root_perm) = krnl.try_wlock_process_and_mark_kill(root_ptr, process_ptr, thread_ptr, killer_info, Tracked(&mut *lctx)).unwrap();
    let ghost marked_k = *krnl;
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(kill_scope_progress(KillScope::Container { container: target }, root_ptr, KillStage::Walk)), Tracked(&*lctx),
        Tracked(thread_perm));
    let ghost entered_k = *krnl;
    proof {
        assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        let before_u = kernel_k_to_kernel_u(before);
        kill_container_cpus_pre_from_k(&before, &before_lctx, cpu_id, process_ptr, thread_ptr, target, ContainerKillStage::Walk);
        kill_container_mark_root_pre_from_k(&before, target, root_ptr);
        kernel_process_locked_and_marked_implies_u_step(&before, &marked_k, root_ptr);
        kernel_thread_syscall_progress_changed_implies_u_step(&marked_k, &entered_k, thread_ptr);
        kill_container_mark_root_step_from_u(before_u, kernel_k_to_kernel_u(marked_k), kernel_k_to_kernel_u(entered_k), cpu_id, thread_ptr, target, root_ptr);
        kill_container_trace_push(&*steps, before_steps, start, pre, before_u, kernel_k_to_kernel_u(entered_k), cpu_id, ctx);
    }
    let tracked mut pchain_perms = Map::<RwLockProcessPtr, LockPerm>::tracked_empty();
    proof { pchain_perms.tracked_insert(root_ptr, root_perm); }
    (root_ptr, Tracked(pchain_perms))
}
} // verus!
