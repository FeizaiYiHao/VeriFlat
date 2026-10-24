use vstd::prelude::*;
use crate::*;
use super::syscall_kill_process_spec::*;
use super::syscall_kill_process_trace::*;
use super::syscall_kill_process_victim::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_victim_spec::*;

verus! {
/// What a kill reaches: the subtree below the killer's process `process`, or every process of the victim container
/// `container`.
pub ghost enum KillScope { Subtree { process: RwLockProcessPtr }, Container { container: RwLockContainerPtr } }

/// The killer's progress after moving to `process` at `stage` in `scope`: a process kill below its process, or a
/// container kill working on a process of the victim container.
pub open spec fn kill_scope_progress(scope: KillScope, process: RwLockProcessPtr, stage: KillStage) -> Option<SyscallProgress> {
    match scope {
        KillScope::Subtree { .. } => kill_progress(process, stage),
        KillScope::Container { container } => Some(SyscallProgress::KillContainer { container, stage: ContainerKillStage::Process { process, stage } }),
    }
}

/// The killer `thread_ptr` of process `process_ptr`, running on `cpu_id`, walks `chain`, the marked processes of `scope`
/// from its first marked process down to the target, at `stage`. It write-holds its cpu, its process, and itself with
/// `cpu_perm`, `process_perm`, and `thread_perm`, every process on the chain with `chain_perms`, the marked `victim` if
/// any, and the containers of `scope`, and no other lock.
pub open spec fn kill_walk_state(
    k: KernelK, lctx: LocalContext, cpu_id: CpuId, scope: KillScope, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, chain: Seq<RwLockProcessPtr>,
    victim: Option<RwLockThreadPtr>, stage: KillStage, cpu_perm: LockPerm, process_perm: LockPerm, thread_perm: LockPerm, chain_perms: Map<RwLockProcessPtr, LockPerm>,
) -> bool {
    &&& killer_held_context(k, lctx, process_ptr, thread_ptr, lctx.container_lock_map().dom())
    &&& forall|t: RwLockThreadPtr| #![trigger lctx.thread_lock_map().dom().contains(t)] lctx.thread_lock_map().dom().contains(t) <==> (t == thread_ptr || Some(t) == victim)
    &&& k.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean()
    &&& kill_chain_state(k, lctx, cpu_id, scope, process_ptr, thread_ptr, chain, stage, cpu_perm, process_perm, thread_perm, chain_perms)
}

/// The killer `thread_ptr` of process `process_ptr`, running on `cpu_id`, works at `stage` on `chain`, the marked
/// processes of `scope` from its first marked process down to the target. It write-holds its cpu, its process, and
/// itself with `cpu_perm`, `process_perm`, and `thread_perm`, and every process on the chain with `chain_perms`, and no cpu
/// set. A held process other than the killer's sits on the chain at its depth below the chain's base depth: the depth
/// below the subtree's process, or the root depth of the victim container. The killer's process is running; every chain process
/// lies in the subtree of the scope's process or is owned by the victim container, is being killed or a zombie, and the
/// target may also have emptied tables at stage `Zombie`. The chain starts at a child of the scope's process or at the
/// victim container's root process. A subtree hangs below the killer's process, which lies in its cpu's container; a
/// victim container is marked, write-held, and below the killer's cpu's container, which the killer write-holds too, and
/// every other container the killer holds is marked, by the killer's process.
pub open spec fn kill_chain_state(
    k: KernelK, lctx: LocalContext, cpu_id: CpuId, scope: KillScope, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, chain: Seq<RwLockProcessPtr>,
    stage: KillStage, cpu_perm: LockPerm, process_perm: LockPerm, thread_perm: LockPerm, chain_perms: Map<RwLockProcessPtr, LockPerm>,
) -> bool {
    let cpu = k.cpu_arr.spec_index(cpu_id).view().view().view();
    let process = k.prc_mp.spec_index(process_ptr);
    let thread = k.thr_mp.spec_index(thread_ptr);
    let depth = process.view_rodata().view().depth;
    let base = match scope { KillScope::Subtree { process: root } => k.prc_mp.spec_index(root).view_rodata().view().depth + 1, KillScope::Container { .. } => 0int };
    let container_ptr = match scope { KillScope::Subtree { .. } => process.view_rodata().view().owning_container, KillScope::Container { container } => container };
    &&& cpu_id == lctx.cpu_id()
    &&& lctx.cpu_set_lock_map().dom().is_empty()
    &&& k.prc_mp.dom().contains(process_ptr)
    &&& k.thr_mp.dom().contains(thread_ptr)
    &&& k.cpu_published[cpu_id as int].view() == (cpu.current_cr3, cpu.current_pcid)
    &&& cpu.process_depth == depth
    &&& cpu.container_depth == process.view_rodata().view().container_depth
    &&& !k.cpu_arr.spec_index(cpu_id).view().being_killed()
    &&& !process.being_killed()
    &&& process.view().state.view() is Running
    &&& !thread.being_killed()
    &&& thread.view().state == (ThreadState::RUNNING { cpu_id })
    &&& thread.view().owning_proc == process_ptr
    &&& thread.view().temp_alloc_clean()
    &&& thread.view().syscall_progress.view() == kill_scope_progress(scope, if chain.len() == 0 { process_ptr } else { chain[chain.len() - 1] }, stage)
    &&& !thread.view_ghost().exited
    &&& match scope {
        KillScope::Subtree { process: root } => root == process_ptr && lctx.container_lock_map().dom().is_empty() && process.view_rodata().view().owning_container == cpu.owning_container,
        KillScope::Container { container } => {
            &&& k.ctn_mp.dom().contains(container)
            &&& k.ctn_mp.spec_index(container).being_killed()
            &&& container != cpu.owning_container
            &&& k.ctn_mp.spec_index(container).view_ghost().uppertree_seq.view().contains(cpu.owning_container)
            &&& typed_lock_map_contains_mode(lctx.container_lock_map(), container, TypedLockMode::Write)
            &&& typed_lock_map_contains_mode(lctx.container_lock_map(), cpu.owning_container, TypedLockMode::Write)
            &&& forall|c: RwLockContainerPtr| #![trigger lctx.container_lock_map().dom().contains(c)] lctx.container_lock_map().dom().contains(c) ==> {
                &&& c != cpu.owning_container ==> k.ctn_mp.spec_index(c).being_killed()
                &&& k.ctn_mp.spec_index(c).killer_info() is Some ==> k.ctn_mp.spec_index(c).killer_info()->Some_0.process == process_ptr
            }
        },
    }
    &&& cpu_perm.state() is WriteLock
    &&& cpu_perm.thread_id() == lctx.thread_id()
    &&& cpu_perm.lock_id() == k.cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id
    &&& process_perm.state() is WriteLock
    &&& process_perm.thread_id() == lctx.thread_id()
    &&& process_perm.lock_id() == process.locking_thread()->Write_lock_id
    &&& thread_perm.state() is WriteLock
    &&& thread_perm.thread_id() == lctx.thread_id()
    &&& thread_perm.lock_id() == thread.locking_thread()->Write_lock_id
    &&& forall|p: RwLockProcessPtr| #![trigger lctx.process_lock_map().dom().contains(p)] lctx.process_lock_map().dom().contains(p) && p != process_ptr ==> {
        let index = k.prc_mp.spec_index(p).view_rodata().view().depth - base;
        &&& 0 <= index < chain.len()
        &&& chain[index] == p
    }
    &&& forall|i: int| #![trigger chain[i]] 0 <= i < chain.len() ==> {
        let p = k.prc_mp.spec_index(chain[i]);
        &&& k.prc_mp.dom().contains(chain[i])
        &&& p.being_killed()
        &&& p.killer_info()->Some_0.process == process_ptr
        &&& p.view().state.view() is Killing || p.view().state.view() is Zombie || stage is Zombie && i == chain.len() - 1 && p.view().state.view() is TablesEmptied
        &&& typed_lock_map_contains_mode(lctx.process_lock_map(), chain[i], TypedLockMode::Write)
        &&& p.view_rodata().view().owning_container == container_ptr
        &&& p.view_rodata().view().depth == base + i
        &&& chain_perms.dom().contains(chain[i])
        &&& chain_perms[chain[i]].state() is WriteLock
        &&& chain_perms[chain[i]].thread_id() == lctx.thread_id()
        &&& chain_perms[chain[i]].lock_id() == p.locking_thread()->Write_lock_id
    }
    &&& scope is Subtree ==> forall|i: int| #![trigger chain[i]] 0 <= i < chain.len() ==> {
        &&& k.prc_mp.spec_index(scope->Subtree_process).view_ghost().subtree_set.view().contains(chain[i])
        &&& i == 0 ==> k.prc_mp.spec_index(chain[i]).view_rodata().view().parent == Some(scope->Subtree_process)
    }
    &&& scope is Container ==> forall|i: int| #![trigger chain[i]] 0 <= i < chain.len() ==> {
        &&& cpu.container_depth < k.prc_mp.spec_index(chain[i]).view_rodata().view().container_depth
        &&& i == 0 ==> chain[i] == k.ctn_mp.spec_index(scope->Container_container).view().root_process
    }
    &&& forall|i: int, j: int| #![trigger chain[i], chain[j]] 0 <= i && j == i + 1 && j < chain.len() ==> k.prc_mp.spec_index(chain[j]).view_rodata().view().parent == Some(chain[i])
}

/// Descend from the target into its first child: mark and write-lock the child and record its walk. The child of the
/// write-held target carries no mark of another killer.
pub(crate) fn kill_mark_child(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, killer_info: KillerInfo, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>,
    Tracked(chain_perms): Tracked<&mut Map<RwLockProcessPtr, LockPerm>>, Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>,
    Tracked(thread_perm): Tracked<&LockPerm>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
) -> (ret: RwLockProcessPtr)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        kill_walk_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, None, KillStage::Walk, *cpu_perm, *process_perm, *thread_perm, *old(chain_perms)),
        0 < chain.len(),
        target == chain[chain.len() - 1],
        0 < old(krnl).prc_mp.spec_index(target).view().children.view().len(),
        killer_info.process == process_ptr,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_walk_state(*final(krnl), *final(lctx), cpu_id, scope, process_ptr, thread_ptr, chain.push(ret), None, KillStage::Walk, *cpu_perm, *process_perm, *thread_perm, *final(chain_perms)),
        final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
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
        scope is Container ==> final(krnl).ctn_mp.spec_index(scope->Container_container).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(scope->Container_container).view_ghost().owned_processes,
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
{
    let ghost before = *krnl;
    let ghost before_lctx = *lctx;
    let ghost before_steps = steps.view();
    proof { process_perms_wf_map(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, target); krnl.prc_mp.spec_index(target).view().children.lemma_len_view(); }
    let child_ptr = {
        let tracked target_perm = chain_perms.tracked_borrow(target);
        krnl.prc_mp.borrow_typed(target, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(target_perm)).children.get(0)
    };
    proof {
        let target_ro = krnl.prc_mp.spec_index(target).view_rodata().view();
        assert({
            let child_ro = krnl.prc_mp.spec_index(child_ptr).view_rodata().view();
            &&& krnl.prc_mp.dom().contains(child_ptr)
            &&& child_ro.parent == Some(target)
            &&& child_ro.depth == target_ro.depth + 1
            &&& child_ro.owning_container == target_ro.owning_container
            &&& child_ro.container_depth == target_ro.container_depth
        }) by {
            let tree = krnl.ctn_mp.spec_index(target_ro.owning_container).view_ghost().owned_processes.view();
            let root = krnl.ctn_mp.spec_index(target_ro.owning_container).view().root_process;
            container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, target); per_container_process_tree_wf_at(krnl.ctn_mp, krnl.prc_mp, target_ro.owning_container);
            process_children_parent_wf_at(root, tree, krnl.prc_mp, target, child_ptr); process_root_wf_at(root, tree, krnl.prc_mp, child_ptr);
            container_process_wf_container_at(krnl.ctn_mp, krnl.prc_mp, target_ro.owning_container, child_ptr); container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, child_ptr);
        };
        assert(!krnl.prc_mp.spec_index(child_ptr).wlocked_by_thread(lctx.thread_id())) by { krnl.prc_mp.typed_lock_map_aligned_locked_at(lctx.process_lock_map(), lctx.thread_id(), child_ptr); };
        if scope is Subtree {
            assert(krnl.prc_mp.spec_index(process_ptr).view_ghost().subtree_set.view().contains(child_ptr)) by {
                let uppers = krnl.prc_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view();
                let tree = krnl.ctn_mp.spec_index(target_ro.owning_container).view_ghost().owned_processes.view();
                let root = krnl.ctn_mp.spec_index(target_ro.owning_container).view().root_process;
                process_perms_wf_at(krnl.prc_mp, child_ptr); container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, child_ptr); container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, process_ptr);
                per_container_process_tree_wf_at(krnl.ctn_mp, krnl.prc_mp, target_ro.owning_container); process_root_wf_at(root, tree, krnl.prc_mp, child_ptr);
                process_uppertree_seq_wf_at(root, tree, krnl.prc_mp, child_ptr, target); process_uppertree_seq_wf_at(root, tree, krnl.prc_mp, child_ptr, process_ptr);
                assert(uppers.contains(target)) by { process_children_depth_wf_at(root, tree, krnl.prc_mp, child_ptr); };
                assert(uppers.contains(process_ptr)) by { process_subtree_set_wf_at(root, tree, krnl.prc_mp, process_ptr, target); };
            };
        } else { container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, child_ptr); }
        assert(!krnl.prc_mp.spec_index(child_ptr).being_killed()) by { process_kill_mark_wf_at(krnl.ctn_mp, krnl.prc_mp, child_ptr); krnl.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), target); };
    }
    let Tracked(child_perm) = krnl.try_wlock_process_and_mark_kill(child_ptr, process_ptr, thread_ptr, killer_info, Tracked(&mut *lctx)).unwrap();
    let ghost marked_k = *krnl;
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(kill_scope_progress(scope, child_ptr, KillStage::Walk)), Tracked(&*lctx), Tracked(thread_perm));
    let ghost entered_k = *krnl;
    proof {
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        let before_u = kernel_k_to_kernel_u(before);
        kill_step_pre_from_k(&before, &before_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Walk, scope); kill_mark_child_pre_from_k(&before, target, child_ptr);
        kernel_process_locked_and_marked_implies_u_step(&before, &marked_k, child_ptr);
        kernel_thread_syscall_progress_changed_implies_u_step(&marked_k, &entered_k, thread_ptr);
        kill_mark_child_step_from_u(before_u, kernel_k_to_kernel_u(marked_k), kernel_k_to_kernel_u(entered_k), cpu_id, thread_ptr, target, child_ptr, scope);
        kill_trace_push(&*steps, before_steps, start, pre, before_u, kernel_k_to_kernel_u(entered_k), cpu_id, ctx);
        chain_perms.tracked_insert(child_ptr, child_perm);
    }
    child_ptr
}

/// Work on the first thread of the childless target. A thread waiting for a reply leaves the target as an unlocked
/// dangling thread. Any other thread is marked, taken off the scheduler shard, endpoint queue, or remote cpu it occupies, releases
/// its caller, is unlinked from the target, and is reclaimed.
pub(crate) fn kill_first_thread(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, killer_info: KillerInfo, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>,
    Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>, Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>,
    Tracked(thread_perm): Tracked<&LockPerm>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        kill_walk_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, None, KillStage::Walk, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
        0 < chain.len(),
        target == chain[chain.len() - 1],
        old(krnl).prc_mp.spec_index(target).view().children.view().len() == 0,
        0 < old(krnl).prc_mp.spec_index(target).view().owned_threads.view().len(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_walk_state(*final(krnl), *final(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, None, KillStage::Walk, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
        final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
        final(krnl).prc_mp.spec_index(target).view().owned_threads.view().len() < old(krnl).prc_mp.spec_index(target).view().owned_threads.view().len(),
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
        scope is Container ==> final(krnl).ctn_mp.spec_index(scope->Container_container).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(scope->Container_container).view_ghost().owned_processes,
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
{
    let ghost before = *krnl;
    let ghost before_lctx = *lctx;
    let ghost before_steps = steps.view();
    let tracked target_perm = chain_perms.tracked_borrow(target);
    proof { process_perms_wf_map(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, target); krnl.prc_mp.spec_index(target).view().owned_threads.lemma_len_view(); }
    let victim_ptr = krnl.prc_mp.borrow_typed(target, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(target_perm)).owned_threads.get(0);
    proof {
        let target_ro = krnl.prc_mp.spec_index(target).view_rodata().view();
        assert({
            let victim = krnl.thr_mp.spec_index(victim_ptr).view();
            &&& krnl.thr_mp.dom().contains(victim_ptr)
            &&& victim.owning_proc == target
            &&& victim.owning_container == target_ro.owning_container
            &&& victim.container_depth == target_ro.container_depth
            &&& victim.process_depth == target_ro.depth
            &&& !victim.proc_linkedlist_node.is_init()
        }) by { process_thread_wf_process_at(krnl.prc_mp, krnl.thr_mp, target, victim_ptr); };
        container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, target); container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, process_ptr);
        assert(!krnl.thr_mp.spec_index(victim_ptr).being_killed()) by {
            assert(!krnl.thr_mp.spec_index(victim_ptr).wlocked_by_thread(lctx.thread_id())) by { krnl.thr_mp.typed_lock_map_aligned_locked_at(lctx.thread_lock_map(), lctx.thread_id(), victim_ptr); };
            krnl.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), target); process_thread_wf_killed_thread_at(krnl.prc_mp, krnl.thr_mp, victim_ptr);
        };
    }
    let Tracked(victim_perm) = krnl.wlock_kill_victim_thread(victim_ptr, Tracked(&mut *lctx)).unwrap();
    proof {
        thread_perms_wf_at(krnl.thr_mp, victim_ptr); thread_caller_callee_wf_at(krnl.thr_mp, victim_ptr);
        assert(!(before.thr_mp.spec_index(victim_ptr).view().state is IPC_TRANSIT || before.thr_mp.spec_index(victim_ptr).view().state is KILLED)) by {
            thread_killed_only_when_wlocked_at(before.thr_mp, victim_ptr); thread_ipc_transit_wf_at(before.thr_mp, victim_ptr);
        };
    }
    let waiting_reply = match krnl.thr_mp.borrow_typed(victim_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&victim_perm)).state {
        ThreadState::WAITING_REPLY => true,
        _ => false,
    };
    proof { enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); }
    if waiting_reply {
        kill_leave_process(krnl, Tracked(&*lctx), target, victim_ptr, Tracked(target_perm), Tracked(&victim_perm));
        proof {
            reveal(kill_leave_process_eof_transition_framing);
            assert(krnl.prc_mp.spec_index(target).view().owned_threads.view().len() < before.prc_mp.spec_index(target).view().owned_threads.view().len()) by {
                before.prc_mp.spec_index(target).view().owned_threads.view().index_of_first_ensures(victim_ptr);
            };
        }
        krnl.wunlock_thread(victim_ptr, Tracked(&mut *lctx), Tracked(victim_perm));
        let ghost dangling_k = *krnl;
        proof {
            kernel_thread_left_process_implies_u_step(&before, &dangling_k, target, victim_ptr);
            krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
            let before_u = kernel_k_to_kernel_u(before);
            kill_step_pre_from_k(&before, &before_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Walk, scope); kill_dangling_pre_from_k(&before, target, victim_ptr);
            kill_dangling_step_from_u(before_u, kernel_k_to_kernel_u(dangling_k), cpu_id, target, victim_ptr);
            kill_trace_push(&*steps, before_steps, start, pre, before_u, kernel_k_to_kernel_u(dangling_k), cpu_id, ctx);
        }
    } else {
        krnl.mark_thread_kill(victim_ptr, target, killer_info, Tracked(&mut *lctx));
        let ghost marked_k = *krnl;
        krnl.set_thread_syscall_progress(thread_ptr, Ghost(kill_scope_progress(scope, target, KillStage::Thread { thread: victim_ptr })), Tracked(&*lctx), Tracked(thread_perm));
        let ghost entered_k = *krnl;
        proof {
            krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
            let before_u = kernel_k_to_kernel_u(before);
            kill_step_pre_from_k(&before, &before_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Walk, scope); kill_mark_thread_pre_from_k(&before, target, victim_ptr);
            kernel_thread_locked_and_marked_implies_u_step(&before, &marked_k, victim_ptr);
            kernel_thread_syscall_progress_changed_implies_u_step(&marked_k, &entered_k, thread_ptr);
            kill_mark_thread_step_from_u(before_u, kernel_k_to_kernel_u(marked_k), kernel_k_to_kernel_u(entered_k), cpu_id, thread_ptr, target, victim_ptr, scope);
            kill_trace_push(&*steps, before_steps, start, pre, before_u, kernel_k_to_kernel_u(entered_k), cpu_id, ctx);
        }
        kill_finish_marked_victim(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, victim_ptr, killer_info, Ghost(chain), Tracked(chain_perms),
            Tracked(cpu_perm), Tracked(process_perm), Tracked(thread_perm), Tracked(victim_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    }
}

/// Kill the marked first thread `victim_ptr` of the target, release its caller, unlink it from the target, and reclaim it.
pub(crate) fn kill_finish_marked_victim(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, victim_ptr: RwLockThreadPtr, killer_info: KillerInfo, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>,
    Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>, Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>,
    Tracked(thread_perm): Tracked<&LockPerm>, Tracked(victim_perm): Tracked<LockPerm>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        kill_walk_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, Some(victim_ptr), KillStage::Thread { thread: victim_ptr }, *cpu_perm, *process_perm,
            *thread_perm, *chain_perms),
        0 < chain.len(),
        target == chain[chain.len() - 1],
        old(krnl).prc_mp.spec_index(target).view().owned_threads.view().contains(victim_ptr),
        old(krnl).thr_mp.dom().contains(victim_ptr),
        old(krnl).thr_mp.spec_index(victim_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(victim_ptr).view().syscall_progress.view() is None,
        old(krnl).thr_mp.spec_index(victim_ptr).view().owning_container == old(krnl).prc_mp.spec_index(target).view_rodata().view().owning_container,
        old(krnl).thr_mp.spec_index(victim_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(victim_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(victim_ptr).view().callee is None,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), victim_ptr, TypedLockMode::Write),
        victim_perm.state() is WriteLock,
        victim_perm.thread_id() == old(lctx).thread_id(),
        victim_perm.lock_id() == old(krnl).thr_mp.spec_index(victim_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(victim_ptr).view().container_depth == old(krnl).prc_mp.spec_index(target).view_rodata().view().container_depth,
        old(krnl).thr_mp.spec_index(victim_ptr).view().process_depth == old(krnl).prc_mp.spec_index(target).view_rodata().view().depth,
        ({
            let state = old(krnl).thr_mp.spec_index(victim_ptr).view().state;
            state is SCHEDULED || state.is_endpoint_waiting() || state is RUNNING
        }),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_walk_state(*final(krnl), *final(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, None, KillStage::Walk, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
        final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
        final(krnl).prc_mp.spec_index(target).view().owned_threads.view().len() < old(krnl).prc_mp.spec_index(target).view().owned_threads.view().len(),
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
    kill_victim_off_cpu_or_queue(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, victim_ptr, killer_info, Ghost(chain), Tracked(chain_perms),
        Tracked(cpu_perm), Tracked(process_perm), Tracked(thread_perm), Tracked(&victim_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    kill_release_victim_caller(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, victim_ptr, Ghost(chain), Tracked(chain_perms),
        Tracked(cpu_perm), Tracked(process_perm), Tracked(thread_perm), Tracked(&victim_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    kill_unlink_victim(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, victim_ptr, Ghost(chain), Tracked(chain_perms),
        Tracked(cpu_perm), Tracked(process_perm), Tracked(thread_perm), Tracked(&victim_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    kill_reclaim_victim(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, victim_ptr, Ghost(chain), Tracked(chain_perms),
        Tracked(cpu_perm), Tracked(process_perm), Tracked(thread_perm), Tracked(victim_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
}

/// Take the marked first thread `victim_ptr` of the target off the scheduler shard or endpoint queue it waits in, or
/// evict it from the remote cpu it runs on, and kill it.
pub(crate) fn kill_victim_off_cpu_or_queue(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, victim_ptr: RwLockThreadPtr, killer_info: KillerInfo, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>,
    Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>, Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>,
    Tracked(thread_perm): Tracked<&LockPerm>, Tracked(victim_perm): Tracked<&LockPerm>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        kill_walk_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, Some(victim_ptr), KillStage::Thread { thread: victim_ptr }, *cpu_perm, *process_perm,
            *thread_perm, *chain_perms),
        0 < chain.len(),
        target == chain[chain.len() - 1],
        old(krnl).prc_mp.spec_index(target).view().owned_threads.view().contains(victim_ptr),
        old(krnl).thr_mp.dom().contains(victim_ptr),
        old(krnl).thr_mp.spec_index(victim_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(victim_ptr).view().syscall_progress.view() is None,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), victim_ptr, TypedLockMode::Write),
        victim_perm.state() is WriteLock,
        victim_perm.thread_id() == old(lctx).thread_id(),
        victim_perm.lock_id() == old(krnl).thr_mp.spec_index(victim_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(victim_ptr).view().container_depth == old(krnl).prc_mp.spec_index(target).view_rodata().view().container_depth,
        old(krnl).thr_mp.spec_index(victim_ptr).view().process_depth == old(krnl).prc_mp.spec_index(target).view_rodata().view().depth,
        ({
            let state = old(krnl).thr_mp.spec_index(victim_ptr).view().state;
            state is SCHEDULED || state.is_endpoint_waiting() || state is RUNNING
        }),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_walk_state(*final(krnl), *final(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, Some(victim_ptr), KillStage::Thread { thread: victim_ptr }, *cpu_perm, *process_perm,
            *thread_perm, *chain_perms),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(krnl).prc_mp.spec_index(target) == old(krnl).prc_mp.spec_index(target),
        final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
        final(krnl).thr_mp.dom().contains(victim_ptr),
        final(krnl).thr_mp.spec_index(victim_ptr).view() == (Thread {
            state: ThreadState::KILLED, error_code: final(krnl).thr_mp.spec_index(victim_ptr).view().error_code,
            blocking_endpoint_ptr: final(krnl).thr_mp.spec_index(victim_ptr).view().blocking_endpoint_ptr,
            blocking_endpoint_index: final(krnl).thr_mp.spec_index(victim_ptr).view().blocking_endpoint_index,
            scheduler_linkedlist_node: final(krnl).thr_mp.spec_index(victim_ptr).view().scheduler_linkedlist_node,
            endpoint_linkedlist_node: final(krnl).thr_mp.spec_index(victim_ptr).view().endpoint_linkedlist_node, ..old(krnl).thr_mp.spec_index(victim_ptr).view()
        }),
        final(krnl).thr_mp.spec_index(victim_ptr).locking_thread() == old(krnl).thr_mp.spec_index(victim_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(victim_ptr).being_killed(),
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
    let ghost before = *krnl;
    let ghost before_lctx = *lctx;
    let ghost before_steps = steps.view();
    proof { thread_perms_wf_map(krnl.thr_mp); thread_perms_wf_at(krnl.thr_mp, victim_ptr); }
    let (scheduled, running) = match krnl.thr_mp.borrow_typed(victim_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(victim_perm)).state {
        ThreadState::SCHEDULED { .. } => (true, false),
        ThreadState::RUNNING { .. } => (false, true),
        _ => (false, false),
    };
    proof {
        let victim = before.thr_mp.spec_index(victim_ptr).view();
        kill_step_pre_from_k(&before, &before_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Thread { thread: victim_ptr }, scope);
        kill_victim_pre_from_k(&before, &before_lctx, cpu_id, target, victim_ptr, victim.state, victim.owning_container, victim.blocking_endpoint_ptr);
    }
    if scheduled {
        kill_dequeue_scheduled_victim(krnl, Tracked(&mut *lctx), victim_ptr, Tracked(victim_perm));
        let ghost killed_k = *krnl;
        proof {
            let victim = before.thr_mp.spec_index(victim_ptr).view();
            let container_ptr = victim.owning_container;
            let shard = victim.state->SCHEDULED_cpu_id;
            kernel_scheduled_thread_killed_implies_u_step(&before, &killed_k, victim_ptr, container_ptr, before.ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler, shard);
            krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
            kill_dequeue_scheduled_step_from_u(kernel_k_to_kernel_u(before), kernel_k_to_kernel_u(killed_k), cpu_id, victim_ptr, container_ptr, shard);
            kill_trace_push(&*steps, before_steps, start, pre, kernel_k_to_kernel_u(before), kernel_k_to_kernel_u(killed_k), cpu_id, ctx);
        }
    } else if running {
        proof { container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, target); container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, process_ptr); }
        kill_evict_running_victim(krnl, Tracked(&mut *lctx), victim_ptr, killer_info, Tracked(victim_perm));
        let ghost killed_k = *krnl;
        proof {
            let remote = before.thr_mp.spec_index(victim_ptr).view().state->RUNNING_cpu_id;
            kernel_running_thread_evicted_implies_u_step(&before, &killed_k, victim_ptr, remote);
            krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
            kill_evict_step_from_u(kernel_k_to_kernel_u(before), kernel_k_to_kernel_u(killed_k), cpu_id, victim_ptr, remote);
            kill_trace_push(&*steps, before_steps, start, pre, kernel_k_to_kernel_u(before), kernel_k_to_kernel_u(killed_k), cpu_id, ctx);
        }
    } else {
        kill_dequeue_endpoint_victim(krnl, Tracked(&mut *lctx), victim_ptr, Tracked(victim_perm));
        let ghost killed_k = *krnl;
        proof {
            let endpoint_ptr = before.thr_mp.spec_index(victim_ptr).view().blocking_endpoint_ptr->Some_0;
            kernel_endpoint_waiter_killed_implies_u_step(&before, &killed_k, victim_ptr, endpoint_ptr);
            krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
            kill_dequeue_endpoint_step_from_u(kernel_k_to_kernel_u(before), kernel_k_to_kernel_u(killed_k), cpu_id, victim_ptr, endpoint_ptr);
            kill_trace_push(&*steps, before_steps, start, pre, kernel_k_to_kernel_u(before), kernel_k_to_kernel_u(killed_k), cpu_id, ctx);
        }
    }
}

/// Release the caller of the killed first thread `victim_ptr`, still linked to the target: wake a caller waiting for the reply, or
/// take over the dangling thread of a killed caller and reclaim it with the dangling threads it serves.
pub(crate) fn kill_release_victim_caller(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, victim_ptr: RwLockThreadPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>,
    Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>, Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>,
    Tracked(thread_perm): Tracked<&LockPerm>, Tracked(victim_perm): Tracked<&LockPerm>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        kill_walk_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, Some(victim_ptr), KillStage::Thread { thread: victim_ptr }, *cpu_perm, *process_perm,
            *thread_perm, *chain_perms),
        0 < chain.len(),
        target == chain[chain.len() - 1],
        old(krnl).thr_mp.dom().contains(victim_ptr),
        old(krnl).thr_mp.spec_index(victim_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(victim_ptr).view().owning_container == old(krnl).prc_mp.spec_index(target).view_rodata().view().owning_container,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), victim_ptr, TypedLockMode::Write),
        victim_perm.state() is WriteLock,
        victim_perm.thread_id() == old(lctx).thread_id(),
        victim_perm.lock_id() == old(krnl).thr_mp.spec_index(victim_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(victim_ptr).view().state is KILLED,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_walk_state(*final(krnl), *final(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, Some(victim_ptr), KillStage::Thread { thread: victim_ptr }, *cpu_perm, *process_perm,
            *thread_perm, *chain_perms),
        final(krnl).prc_mp.spec_index(target) == old(krnl).prc_mp.spec_index(target),
        final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
        final(krnl).thr_mp.dom().contains(victim_ptr),
        final(krnl).thr_mp.spec_index(victim_ptr).view() == (Thread { caller: None, ..old(krnl).thr_mp.spec_index(victim_ptr).view() }),
        final(krnl).thr_mp.spec_index(victim_ptr).locking_thread() == old(krnl).thr_mp.spec_index(victim_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(victim_ptr).being_killed(),
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
    let ghost before = *krnl;
    let ghost before_lctx = *lctx;
    let ghost before_steps = steps.view();
    proof { assert(kernel_steps_prefix_unchanged(before_steps, before_steps)) by { reveal(kernel_steps_prefix_unchanged); }; }
    let (next, Tracked(next_perm)) = release_killed_thread_caller(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, victim_ptr, Tracked(victim_perm));
    proof {
        let victim_container = before.thr_mp.spec_index(victim_ptr).view().owning_container;
        kill_step_pre_from_k(&before, &before_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Thread { thread: victim_ptr }, scope); kill_refund_pre_from_k(&before, target, victim_container);
        kill_trace_from_killed_thread_reclaim(&*steps, before_steps, start, pre, kernel_k_to_kernel_u(before), cpu_id, ctx, process_ptr, target, victim_container, KillStage::Thread { thread: victim_ptr }, scope);
    }
    if let Some(caller_ptr) = next {
        let ghost reclaim_k = *krnl;
        let ghost reclaim_lctx = *lctx;
        let ghost reclaim_before = steps.view();
        let tracked caller_perm = next_perm.tracked_unwrap();
        proof { assert(kernel_steps_prefix_unchanged(reclaim_before, reclaim_before)) by { reveal(kernel_steps_prefix_unchanged); }; }
        reclaim_killed_thread_chain(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, caller_ptr, Tracked(caller_perm));
        proof {
            let victim_container = reclaim_k.thr_mp.spec_index(caller_ptr).view().owning_container;
            kill_step_pre_from_k(&reclaim_k, &reclaim_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Thread { thread: victim_ptr }, scope); kill_refund_pre_from_k(&reclaim_k, target, victim_container);
            kill_trace_from_killed_thread_reclaim(&*steps, reclaim_before, start, pre, kernel_k_to_kernel_u(reclaim_k), cpu_id, ctx, process_ptr, target, victim_container, KillStage::Thread { thread: victim_ptr }, scope);
            assert(lctx.thread_lock_map() =~= old(lctx).thread_lock_map());
        }
    }
}

/// Unlink the killed first thread `victim_ptr` from the target, which absorbs its quota, and walk the target again.
pub(crate) fn kill_unlink_victim(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, victim_ptr: RwLockThreadPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>,
    Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>, Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>,
    Tracked(thread_perm): Tracked<&LockPerm>, Tracked(victim_perm): Tracked<&LockPerm>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        kill_walk_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, Some(victim_ptr), KillStage::Thread { thread: victim_ptr }, *cpu_perm, *process_perm,
            *thread_perm, *chain_perms),
        0 < chain.len(),
        target == chain[chain.len() - 1],
        old(krnl).prc_mp.spec_index(target).view().owned_threads.view().contains(victim_ptr),
        old(krnl).thr_mp.dom().contains(victim_ptr),
        old(krnl).thr_mp.spec_index(victim_ptr).being_killed(),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), victim_ptr, TypedLockMode::Write),
        victim_perm.state() is WriteLock,
        victim_perm.thread_id() == old(lctx).thread_id(),
        victim_perm.lock_id() == old(krnl).thr_mp.spec_index(victim_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(victim_ptr).view().state is KILLED,
        old(krnl).thr_mp.spec_index(victim_ptr).view().caller is None,
        old(krnl).thr_mp.spec_index(victim_ptr).view().temp_alloc_clean(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_walk_state(*final(krnl), *final(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, Some(victim_ptr), KillStage::Walk, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
        final(krnl).thr_mp.dom().contains(victim_ptr),
        final(krnl).thr_mp.spec_index(victim_ptr).view() == (Thread {
            quota_4k: 0, quota_2m: 0, quota_1g: 0, proc_linkedlist_node: final(krnl).thr_mp.spec_index(victim_ptr).view().proc_linkedlist_node, ..old(krnl).thr_mp.spec_index(victim_ptr).view()
        }),
        final(krnl).thr_mp.spec_index(victim_ptr).view().proc_linkedlist_node.is_init(),
        final(krnl).thr_mp.spec_index(victim_ptr).locking_thread() == old(krnl).thr_mp.spec_index(victim_ptr).locking_thread(),
        final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
        final(krnl).prc_mp.spec_index(target).view().owned_threads.view().len() < old(krnl).prc_mp.spec_index(target).view().owned_threads.view().len(),
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
    let ghost before = *krnl;
    let ghost before_lctx = *lctx;
    let ghost before_steps = steps.view();
    let tracked target_perm = chain_perms.tracked_borrow(target);
    proof {
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        assert(krnl.prc_mp.spec_index(target).view().state.view() is Killing) by { process_perms_wf_at(krnl.prc_mp, target); };
    }
    kill_leave_process(krnl, Tracked(&*lctx), target, victim_ptr, Tracked(target_perm), Tracked(victim_perm));
    let ghost left_k = *krnl;
    proof {
        reveal(kill_leave_process_eof_transition_framing);
        assert(krnl.prc_mp.spec_index(target).view().owned_threads.view().len() < before.prc_mp.spec_index(target).view().owned_threads.view().len()) by {
            before.prc_mp.spec_index(target).view().owned_threads.view().index_of_first_ensures(victim_ptr);
        };
    }
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(kill_scope_progress(scope, target, KillStage::Walk)), Tracked(&*lctx), Tracked(thread_perm));
    let ghost entered_k = *krnl;
    proof {
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        let before_u = kernel_k_to_kernel_u(before);
        let victim = before.thr_mp.spec_index(victim_ptr).view();
        kill_step_pre_from_k(&before, &before_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Thread { thread: victim_ptr }, scope);
        kill_victim_pre_from_k(&before, &before_lctx, cpu_id, target, victim_ptr, victim.state, victim.owning_container, victim.blocking_endpoint_ptr);
        kernel_thread_left_process_implies_u_step(&before, &left_k, target, victim_ptr);
        kernel_thread_syscall_progress_changed_implies_u_step(&left_k, &entered_k, thread_ptr);
        kill_unlink_step_from_u(before_u, kernel_k_to_kernel_u(left_k), kernel_k_to_kernel_u(entered_k), cpu_id, thread_ptr, target, victim_ptr, scope);
        kill_trace_push(&*steps, before_steps, start, pre, before_u, kernel_k_to_kernel_u(entered_k), cpu_id, ctx);
    }
}

/// Reclaim the killed first thread `victim_ptr`, unlinked from the target, and the dangling threads it serves.
pub(crate) fn kill_reclaim_victim(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, victim_ptr: RwLockThreadPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>,
    Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>, Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>,
    Tracked(thread_perm): Tracked<&LockPerm>, Tracked(victim_perm): Tracked<LockPerm>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        kill_walk_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, Some(victim_ptr), KillStage::Walk, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
        0 < chain.len(),
        target == chain[chain.len() - 1],
        old(krnl).thr_mp.dom().contains(victim_ptr),
        old(krnl).thr_mp.spec_index(victim_ptr).view().owning_container == old(krnl).prc_mp.spec_index(target).view_rodata().view().owning_container,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), victim_ptr, TypedLockMode::Write),
        victim_perm.state() is WriteLock,
        victim_perm.thread_id() == old(lctx).thread_id(),
        victim_perm.lock_id() == old(krnl).thr_mp.spec_index(victim_ptr).locking_thread()->Write_lock_id,
        ({
            let victim = old(krnl).thr_mp.spec_index(victim_ptr).view();
            &&& victim.state is KILLED
            &&& victim.callee is None
            &&& victim.proc_linkedlist_node.is_init()
            &&& victim.temp_alloc_clean()
            &&& victim.free_quota_pending_clean()
            &&& victim.quota_4k == 0
            &&& victim.quota_2m == 0
            &&& victim.quota_1g == 0
        }),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_walk_state(*final(krnl), *final(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, None, KillStage::Walk, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
        final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
        final(krnl).prc_mp.spec_index(target) == old(krnl).prc_mp.spec_index(target),
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
    let ghost reclaim_k = *krnl;
    let ghost reclaim_lctx = *lctx;
    let ghost reclaim_before = steps.view();
    proof { assert(kernel_steps_prefix_unchanged(reclaim_before, reclaim_before)) by { reveal(kernel_steps_prefix_unchanged); }; }
    reclaim_killed_thread_chain(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, victim_ptr, Tracked(victim_perm));
    proof {
        let victim_container = reclaim_k.thr_mp.spec_index(victim_ptr).view().owning_container;
        kill_step_pre_from_k(&reclaim_k, &reclaim_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Walk, scope); kill_refund_pre_from_k(&reclaim_k, target, victim_container);
        kill_trace_from_killed_thread_reclaim(&*steps, reclaim_before, start, pre, kernel_k_to_kernel_u(reclaim_k), cpu_id, ctx, process_ptr, target, victim_container, KillStage::Walk, scope);
    }
}
} // verus!
