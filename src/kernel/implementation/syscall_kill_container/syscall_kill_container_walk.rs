use vstd::prelude::*;
use crate::*;
use super::super::syscall_kill_process::syscall_kill_process_spec::*;
use super::syscall_kill_container_cpus::kill_container_cpus;
use super::syscall_kill_container_pages::kill_container_pages;
use super::syscall_kill_container_retire::kill_container_retire;
use super::syscall_kill_container_walk_processes::kill_container_kill_processes;
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
/// Walk the marked child container `child_ptr` of the killer's container `owner_ptr` until every container below it is
/// retired, then clear the kill and unlock the cpu, the killer's container, the process, and the thread.
pub(crate) fn kill_container_walk_and_finish(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, owner_ptr: RwLockContainerPtr, child_ptr: RwLockContainerPtr, killer_info: KillerInfo, Tracked(cpu_perm): Tracked<LockPerm>,
    Tracked(process_perm): Tracked<LockPerm>, Tracked(thread_perm): Tracked<LockPerm>, Tracked(owner_perm): Tracked<LockPerm>,
    Tracked(chain_perms): Tracked<Map<RwLockContainerPtr, LockPerm>>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(child_index): Ghost<usize>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, KillTraceCtx::Container { child_index }),
        kill_container_walk_state(*old(krnl), *old(lctx), cpu_id, process_ptr, thread_ptr, owner_ptr, killer_info, seq![child_ptr], cpu_perm, process_perm, thread_perm, owner_perm,
            chain_perms),
        !old(krnl).ctn_mp.spec_index(child_ptr).view_ghost().owned_processes.view().is_empty(),
    ensures
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_container_syscall_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, kernel_k_to_kernel_u(*final(krnl)), cpu_id, child_index, true),
{
    let ghost ctx = KillTraceCtx::Container { child_index };
    let tracked mut chain_perms = chain_perms;
    let ghost mut chain: Seq<RwLockContainerPtr> = seq![child_ptr];
    let mut target = child_ptr;
    let mut processes_left = true;
    let mut walking = true;
    while walking
        invariant
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.kernel_view_locking_state() is Acquire,
            steps.snapshot_k() == *krnl,
            0 <= start <= old(steps).view().len() <= steps.view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            kill_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, ctx),
            ctx == (KillTraceCtx::Container { child_index }),
            kill_container_walk_state(*krnl, *lctx, cpu_id, process_ptr, thread_ptr, owner_ptr, killer_info, chain, cpu_perm, process_perm, thread_perm, owner_perm, chain_perms),
            old(lctx).cpu_id() == cpu_id,
            chain.len() <= MAX_CONTAINER_TREE_DEPTH,
            walking == (0 < chain.len()),
            walking ==> target == chain[chain.len() - 1],
            walking ==> processes_left == !krnl.ctn_mp.spec_index(target).view_ghost().owned_processes.view().is_empty(),
            walking && !processes_left ==> krnl.ctn_mp.spec_index(target).view().children.view().len() == 0,
        decreases krnl.ctn_mp.spec_index(owner_ptr).view_ghost().subtree_set.view().len(), MAX_CONTAINER_TREE_DEPTH - chain.len(), if processes_left { 1int } else { 0int },
    {
        if processes_left {
            proof { container_perms_wf_map(krnl.ctn_mp); container_perms_wf_at(krnl.ctn_mp, target); krnl.ctn_mp.spec_index(target).view().children.lemma_len_view(); }
            let has_children = {
                let tracked target_perm = chain_perms.tracked_borrow(target);
                krnl.ctn_mp.borrow_typed(target, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(target_perm)).children.len() != 0
            };
            if has_children {
                let next = kill_container_mark_child(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, owner_ptr, target, killer_info, Ghost(chain),
                    Tracked(&mut chain_perms), Tracked(&cpu_perm), Tracked(&process_perm), Tracked(&thread_perm), Tracked(&owner_perm), Ghost(start), Ghost(pre), Ghost(ctx));
                proof { chain = chain.push(next); }
                target = next;
            } else {
                kill_container_kill_processes(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, owner_ptr, target, killer_info, Ghost(chain),
                    Tracked(&chain_perms), Tracked(&cpu_perm), Tracked(&process_perm), Tracked(&thread_perm), Tracked(&owner_perm), Ghost(start), Ghost(pre), Ghost(ctx));
                processes_left = false;
            }
        } else {
            let parent = kill_container_retire_target(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, owner_ptr, target, killer_info, Ghost(chain),
                Tracked(&mut chain_perms), Tracked(&cpu_perm), Tracked(&process_perm), Tracked(&thread_perm), Tracked(&owner_perm), Ghost(start), Ghost(pre), Ghost(ctx));
            proof { chain = chain.drop_last(); }
            if parent == owner_ptr { walking = false; } else { target = parent; processes_left = true; }
        }
    }
    proof { enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); }
    let ghost walk_k = *krnl;
    let ghost walk_lctx = *lctx;
    let ghost finish_before = steps.view();
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(None), Tracked(&*lctx), Tracked(&thread_perm));
    let ghost cleared_k = *krnl;
    proof {
        assert(krnl.prc_mp.spec_index(process_ptr).view().owned_threads.view().len() != 0) by { process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, thread_ptr); };
        assert(!krnl.ctn_mp.spec_index(owner_ptr).view_ghost().owned_processes.view().is_empty()) by {
            process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, process_ptr);
        };
    }
    krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_perm));
    krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_perm));
    krnl.wunlock_container(owner_ptr, Tracked(&mut *lctx), Tracked(owner_perm));
    assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep && krnl.cpu_arr.spec_index(cpu_id).view().view_ghost() == Some(cpu_id)) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
    krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
    proof {
        steps.end_kernel_step_thread_syscall_progress_changed(&*krnl, &*lctx, thread_ptr);
        kill_container_finish_pre_from_k(&walk_k, &walk_lctx, cpu_id, owner_ptr, process_ptr, thread_ptr);
        kernel_thread_syscall_progress_changed_implies_u_step(&walk_k, &cleared_k, thread_ptr);
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&cleared_k, krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&cleared_k, krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        assert(kernel_endpoint_nonlock_fields_unchanged(cleared_k.ep_mp, krnl.ep_mp)) by { broadcast use kernel_endpoint_nonlock_fields_unchanged_for_equal; };
        kernel_cpu_process_thread_endpoint_lock_modes_changed_implies_u_step(&cleared_k, &*krnl, &*lctx, cpu_id, process_ptr, thread_ptr, None, false, Some(owner_ptr), false, None);
        kill_container_finish_step_from_u(kernel_k_to_kernel_u(walk_k), kernel_k_to_kernel_u(cleared_k), kernel_k_to_kernel_u(*krnl), cpu_id, owner_ptr, process_ptr, thread_ptr);
        kill_container_trace_finish_step(&*steps, finish_before, start, pre, kernel_k_to_kernel_u(walk_k), kernel_k_to_kernel_u(*krnl), cpu_id, child_index);
        no_locks_held_imply_all_objects_unlocked(&*krnl, &*lctx);
    }
}

/// Descend from the target `target` into its first child container: mark and write-lock the child and record its walk.
/// The child of the write-held target carries no mark of another killer and still owns processes.
pub(crate) fn kill_container_mark_child(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, owner_ptr: RwLockContainerPtr, target: RwLockContainerPtr, killer_info: KillerInfo, Ghost(chain): Ghost<Seq<RwLockContainerPtr>>,
    Tracked(chain_perms): Tracked<&mut Map<RwLockContainerPtr, LockPerm>>, Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>,
    Tracked(thread_perm): Tracked<&LockPerm>, Tracked(owner_perm): Tracked<&LockPerm>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(ctx): Ghost<KillTraceCtx>,
) -> (ret: RwLockContainerPtr)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        ctx is Container,
        kill_container_walk_state(*old(krnl), *old(lctx), cpu_id, process_ptr, thread_ptr, owner_ptr, killer_info, chain, *cpu_perm, *process_perm, *thread_perm, *owner_perm,
            *old(chain_perms)),
        0 < chain.len(),
        target == chain[chain.len() - 1],
        0 < old(krnl).ctn_mp.spec_index(target).view().children.view().len(),
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
        kill_container_walk_state(*final(krnl), *final(lctx), cpu_id, process_ptr, thread_ptr, owner_ptr, killer_info, chain.push(ret), *cpu_perm, *process_perm, *thread_perm,
            *owner_perm, *final(chain_perms)),
        !final(krnl).ctn_mp.spec_index(ret).view_ghost().owned_processes.view().is_empty(),
        final(krnl).ctn_mp.spec_index(owner_ptr).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(owner_ptr).view_ghost().subtree_set,
        chain.len() < MAX_CONTAINER_TREE_DEPTH,
{
    let ghost before = *krnl;
    let ghost before_lctx = *lctx;
    let ghost before_steps = steps.view();
    proof { container_perms_wf_map(krnl.ctn_mp); container_perms_wf_at(krnl.ctn_mp, target); krnl.ctn_mp.spec_index(target).view().children.lemma_len_view(); }
    let child_ptr = {
        let tracked target_perm = chain_perms.tracked_borrow(target);
        krnl.ctn_mp.borrow_typed(target, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(target_perm)).children.get(0)
    };
    proof {
        let target_depth = krnl.ctn_mp.spec_index(target).view_rodata().view().depth;
        let owner_depth = krnl.ctn_mp.spec_index(owner_ptr).view_rodata().view().depth;
        let child_uppers = krnl.ctn_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view();
        assert({
            let child_ro = krnl.ctn_mp.spec_index(child_ptr).view_rodata().view();
            &&& krnl.ctn_mp.dom().contains(child_ptr)
            &&& child_ro.parent == Some(target)
            &&& child_ro.depth == target_depth + 1
            &&& child_ro.depth <= MAX_CONTAINER_TREE_DEPTH
            &&& child_uppers.contains(owner_ptr)
        }) by {
            container_children_parent_wf_at(krnl.rt_ctn, krnl.ctn_mp, target, child_ptr); container_root_wf_at(krnl.rt_ctn, krnl.ctn_mp, child_ptr);
            container_perms_wf_at(krnl.ctn_mp, child_ptr); container_children_depth_wf_at(krnl.rt_ctn, krnl.ctn_mp, child_ptr);
            assert(child_uppers[target_depth as int] == target);
            container_uppertree_seq_wf_at(krnl.rt_ctn, krnl.ctn_mp, target, owner_ptr); container_uppertree_seq_wf_at(krnl.rt_ctn, krnl.ctn_mp, child_ptr, target);
            assert(child_uppers[owner_depth as int] == owner_ptr);
        };
        assert(!lctx.container_lock_map().dom().contains(child_ptr));
        assert(!krnl.ctn_mp.spec_index(child_ptr).being_killed()) by {
            container_kill_mark_wf_at(krnl.ctn_mp, krnl.prc_mp, child_ptr); krnl.ctn_mp.typed_lock_map_aligned_write_at(lctx.container_lock_map(), lctx.thread_id(), target);
            krnl.ctn_mp.typed_lock_map_aligned_locked_at(lctx.container_lock_map(), lctx.thread_id(), child_ptr);
        };
    }
    let Tracked(child_perm) = krnl.try_wlock_container_and_mark_kill(child_ptr, killer_info, Tracked(&mut *lctx)).unwrap();
    let ghost marked_k = *krnl;
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(kill_container_progress(child_ptr, ContainerKillStage::Walk)), Tracked(&*lctx), Tracked(thread_perm));
    let ghost entered_k = *krnl;
    proof {
        assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        let before_u = kernel_k_to_kernel_u(before);
        kill_container_cpus_pre_from_k(&before, &before_lctx, cpu_id, process_ptr, thread_ptr, target, ContainerKillStage::Walk);
        kill_container_mark_child_pre_from_k(&before, child_ptr);
        kernel_container_locked_and_marked_implies_u_step(&before, &marked_k, child_ptr);
        kernel_thread_syscall_progress_changed_implies_u_step(&marked_k, &entered_k, thread_ptr);
        kill_container_mark_child_step_from_u(before_u, kernel_k_to_kernel_u(marked_k), kernel_k_to_kernel_u(entered_k), cpu_id, thread_ptr, target, child_ptr);
        kill_container_trace_push(&*steps, before_steps, start, pre, before_u, kernel_k_to_kernel_u(entered_k), cpu_id, ctx);
        chain_perms.tracked_insert(child_ptr, child_perm);
    }
    child_ptr
}

/// Retire the target `target`, which has no child container and no process left: move its cpus and free pages to the
/// killer's container `owner_ptr`, retire it, and walk its parent, which is returned.
pub(crate) fn kill_container_retire_target(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, owner_ptr: RwLockContainerPtr, target: RwLockContainerPtr, killer_info: KillerInfo, Ghost(chain): Ghost<Seq<RwLockContainerPtr>>,
    Tracked(chain_perms): Tracked<&mut Map<RwLockContainerPtr, LockPerm>>, Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>,
    Tracked(thread_perm): Tracked<&LockPerm>, Tracked(owner_perm): Tracked<&LockPerm>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(ctx): Ghost<KillTraceCtx>,
) -> (parent: RwLockContainerPtr)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        ctx is Container,
        kill_container_walk_state(*old(krnl), *old(lctx), cpu_id, process_ptr, thread_ptr, owner_ptr, killer_info, chain, *cpu_perm, *process_perm, *thread_perm, *owner_perm,
            *old(chain_perms)),
        0 < chain.len(),
        target == chain[chain.len() - 1],
        old(krnl).ctn_mp.spec_index(target).view().children.view().len() == 0,
        old(krnl).ctn_mp.spec_index(target).view_ghost().owned_processes.view().is_empty(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_container_walk_state(*final(krnl), *final(lctx), cpu_id, process_ptr, thread_ptr, owner_ptr, killer_info, chain.drop_last(), *cpu_perm, *process_perm, *thread_perm,
            *owner_perm, *final(chain_perms)),
        parent == if chain.len() == 1 { owner_ptr } else { chain[chain.len() - 2] },
        chain.len() > 1 ==> parent != owner_ptr,
        chain.len() > 1 ==> !final(krnl).ctn_mp.spec_index(parent).view_ghost().owned_processes.view().is_empty(),
        final(krnl).ctn_mp.spec_index(owner_ptr).view_ghost().subtree_set.view().len() < old(krnl).ctn_mp.spec_index(owner_ptr).view_ghost().subtree_set.view().len(),
{
    proof {
        container_perms_wf_map(krnl.ctn_mp); container_perms_wf_at(krnl.ctn_mp, target); container_without_children_and_processes_owns_no_threads(*krnl, target);
        if chain.len() > 1 { assert(krnl.ctn_mp.spec_index(chain[chain.len() - 1]).view_rodata().view().parent == Some(chain[chain.len() - 2])); }
        assert(krnl.ctn_mp.spec_index(owner_ptr).view_ghost().subtree_set.view().contains(target)) by {
            container_subtree_set_exclusive_at(krnl.rt_ctn, krnl.ctn_mp, owner_ptr, target);
        };
    }
    let ghost entry_k = *krnl;
    let parent = krnl.ctn_mp.borrow_rodata(target).borrow().parent.unwrap();
    let tracked container_perm = chain_perms.tracked_remove(target);
    let (cpu_set_ptr, Tracked(cpu_set_perm)) = kill_container_cpus(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, owner_ptr,
        killer_info, Tracked(cpu_perm), Tracked(process_perm), Tracked(thread_perm), Tracked(&container_perm), Ghost(start), Ghost(pre), Ghost(ctx));
    proof {
        process_perms_wf_map(krnl.prc_mp); krnl.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), process_ptr);
        krnl.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr);
        krnl.ctn_mp.typed_lock_map_aligned_held_in_dom(lctx.container_lock_map(), lctx.thread_id());
    }
    kill_container_pages(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, owner_ptr, Tracked(cpu_perm), Tracked(process_perm),
        Tracked(thread_perm), Tracked(&container_perm), Tracked(owner_perm), Ghost(start), Ghost(pre), Ghost(ctx));
    if parent == owner_ptr {
        kill_container_retire(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, parent, owner_ptr, cpu_set_ptr, Tracked(cpu_perm),
            Tracked(process_perm), Tracked(thread_perm), Tracked(container_perm), Tracked(owner_perm), Tracked(owner_perm), Tracked(cpu_set_perm), Ghost(start), Ghost(pre),
            Ghost(ctx));
    } else {
        let tracked parent_perm = chain_perms.tracked_borrow(parent);
        kill_container_retire(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, parent, owner_ptr, cpu_set_ptr, Tracked(cpu_perm),
            Tracked(process_perm), Tracked(thread_perm), Tracked(container_perm), Tracked(parent_perm), Tracked(owner_perm), Tracked(cpu_set_perm), Ghost(start), Ghost(pre),
            Ghost(ctx));
    }
    proof {
        vstd::set::lemma_set_remove_len(entry_k.ctn_mp.spec_index(owner_ptr).view_ghost().subtree_set.view(), target);
        assert(kill_container_walk_state(*krnl, *lctx, cpu_id, process_ptr, thread_ptr, owner_ptr, killer_info, chain.drop_last(), *cpu_perm, *process_perm, *thread_perm, *owner_perm,
            *chain_perms)) by {
            process_perms_wf_map(krnl.prc_mp); reveal(LockedMap::typed_lock_map_aligned);
        };
    }
    parent
}
} // verus!
