use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_spec::kill_progress;

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

/// The killer `thrd_ptr` of process `prc_ptr`, running on `cpu_id`, walks `chain`, the marked processes of `scope`
/// from its first marked process down to the target, at `stage`. It write-holds its cpu, its process, and itself with
/// `cpu_perm`, `process_perm`, and `thread_perm`, every process on the chain with `chain_perms`, the marked `victim` if
/// any, and the containers of `scope`, and no other lock.
pub open spec fn kill_walk_state(
    k: KernelK, lctx: LocalContext, cpu_id: CpuId, scope: KillScope, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, chain: Seq<RwLockProcessPtr>,
    victim: Option<RwLockThreadPtr>, stage: KillStage, cpu_perm: LockPerm, process_perm: LockPerm, thread_perm: LockPerm, chain_perms: Map<RwLockProcessPtr, LockPerm>,
) -> bool {
    &&& killer_held_context(k, lctx, prc_ptr, thrd_ptr, lctx.container_lock_map().dom())
    &&& forall|t: RwLockThreadPtr| #![trigger lctx.thread_lock_map().dom().contains(t)] lctx.thread_lock_map().dom().contains(t) <==> (t == thrd_ptr || Some(t) == victim)
    &&& k.thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean()
    &&& kill_chain_state(k, lctx, cpu_id, scope, prc_ptr, thrd_ptr, chain, stage, cpu_perm, process_perm, thread_perm, chain_perms)
}

/// The killer `thrd_ptr` of process `prc_ptr`, running on `cpu_id`, works at `stage` on `chain`, the marked
/// processes of `scope` from its first marked process down to the target. It write-holds its cpu, inside its kernel
/// step, its process, and itself with `cpu_perm`, `process_perm`, and `thread_perm`, and every process on the chain
/// with `chain_perms`, and no cpu set. A held process other than the killer's sits on the chain at its depth below the
/// chain's base depth: the depth below the subtree's process, or the root depth of the victim container. The killer's
/// process is running; every chain process lies in the subtree of the scope's process or is owned by the victim
/// container, is being killed or a zombie, and the target may also have emptied tables at stage `Zombie`. The chain
/// starts at a child of the scope's process or at the victim container's root process. A subtree hangs below the
/// killer's process, which lies in its cpu's container; a victim container is marked, write-held, and below the
/// killer's cpu's container, which the killer write-holds too, and every other container the killer holds is marked, by
/// the killer's process.
pub open spec fn kill_chain_state(
    k: KernelK, lctx: LocalContext, cpu_id: CpuId, scope: KillScope, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, chain: Seq<RwLockProcessPtr>,
    stage: KillStage, cpu_perm: LockPerm, process_perm: LockPerm, thread_perm: LockPerm, chain_perms: Map<RwLockProcessPtr, LockPerm>,
) -> bool {
    let cpu = k.cpu_arr.spec_index(cpu_id).view().view().view();
    let process = k.prc_mp.spec_index(prc_ptr);
    let thread = k.thrd_mp.spec_index(thrd_ptr);
    let depth = process.view_rodata().view().depth;
    let base = match scope { KillScope::Subtree { process: root } => k.prc_mp.spec_index(root).view_rodata().view().depth + 1, KillScope::Container { .. } => 0int };
    let ctn_ptr = match scope { KillScope::Subtree { .. } => process.view_rodata().view().owning_container, KillScope::Container { container } => container };
    &&& cpu_id == lctx.cpu_id()
    &&& lctx.cpu_set_lock_map().dom().is_empty()
    &&& k.prc_mp.dom().contains(prc_ptr)
    &&& k.thrd_mp.dom().contains(thrd_ptr)
    &&& k.cpu_hw_cr3_pcid[cpu_id as int].view() == (cpu.current_cr3, cpu.current_pcid)
    &&& k.cpu_arr.spec_index(cpu_id).view().view().kernel_call_perm() is None
    &&& cpu.process_depth == depth
    &&& cpu.container_depth == process.view_rodata().view().container_depth
    &&& !k.cpu_arr.spec_index(cpu_id).view().being_killed()
    &&& !process.being_killed()
    &&& process.view().state.view() is Running
    &&& !thread.being_killed()
    &&& thread.view().state == (ThreadState::RUNNING { cpu_id })
    &&& thread.view().owning_proc == prc_ptr
    &&& thread.view().temp_alloc_clean()
    &&& thread.view().syscall_progress.view() == kill_scope_progress(scope, if chain.len() == 0 { prc_ptr } else { chain[chain.len() - 1] }, stage)
    &&& !thread.view_ghost().exited
    &&& match scope {
        KillScope::Subtree { process: root } => root == prc_ptr && lctx.container_lock_map().dom().is_empty() && process.view_rodata().view().owning_container == cpu.owning_container,
        KillScope::Container { container } => {
            &&& k.ctn_mp.dom().contains(container)
            &&& k.ctn_mp.spec_index(container).being_killed()
            &&& container != cpu.owning_container
            &&& k.ctn_mp.spec_index(container).view_ghost().uppertree_seq.view().contains(cpu.owning_container)
            &&& typed_lock_map_contains_mode(lctx.container_lock_map(), container, TypedLockMode::Write)
            &&& typed_lock_map_contains_mode(lctx.container_lock_map(), cpu.owning_container, TypedLockMode::Write)
            &&& forall|c: RwLockContainerPtr| #![trigger lctx.container_lock_map().dom().contains(c)] lctx.container_lock_map().dom().contains(c) ==> {
                &&& c != cpu.owning_container ==> k.ctn_mp.spec_index(c).being_killed()
                &&& k.ctn_mp.spec_index(c).killer_info() is Some ==> k.ctn_mp.spec_index(c).killer_info()->Some_0.process == prc_ptr
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
    &&& forall|p: RwLockProcessPtr| #![trigger lctx.process_lock_map().dom().contains(p)] lctx.process_lock_map().dom().contains(p) && p != prc_ptr ==> {
        let index = k.prc_mp.spec_index(p).view_rodata().view().depth - base;
        &&& 0 <= index < chain.len()
        &&& chain[index] == p
    }
    &&& forall|i: int| #![trigger chain[i]] 0 <= i < chain.len() ==> {
        let p = k.prc_mp.spec_index(chain[i]);
        &&& k.prc_mp.dom().contains(chain[i])
        &&& p.being_killed()
        &&& p.killer_info()->Some_0.process == prc_ptr
        &&& p.view().state.view() is Killing || p.view().state.view() is Zombie || stage is Zombie && i == chain.len() - 1 && p.view().state.view() is TablesEmptied
        &&& typed_lock_map_contains_mode(lctx.process_lock_map(), chain[i], TypedLockMode::Write)
        &&& p.view_rodata().view().owning_container == ctn_ptr
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
} // verus!
