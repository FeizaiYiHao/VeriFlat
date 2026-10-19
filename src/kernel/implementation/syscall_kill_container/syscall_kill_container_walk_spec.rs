use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_spec::kill_container_progress;

verus! {
/// The killer `thread_ptr` of process `process_ptr`, running on `cpu_id` in its container `owner_ptr`, walks `chain`,
/// the containers it marked with `killer_info` from a child of its container down to the target, and works on the
/// target, or on its own container once the chain is empty, at stage `Walk`. It write-holds its cpu, its process,
/// itself, and its container with `cpu_perm`, `process_perm`, `thread_perm`, and `owner_perm`, every container on the
/// chain with `chain_perms`, and no other lock. A held container other than its own sits on the chain at its depth
/// below its own container; every chain container is the child of the one before it, lies below the killer's
/// container, and, except the target, still owns processes.
pub open spec fn kill_container_walk_state(
    k: KernelK, lctx: LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, owner_ptr: RwLockContainerPtr, killer_info: KillerInfo,
    chain: Seq<RwLockContainerPtr>, cpu_perm: LockPerm, process_perm: LockPerm, thread_perm: LockPerm, owner_perm: LockPerm, chain_perms: Map<RwLockContainerPtr, LockPerm>,
) -> bool {
    let cpu = k.cpu_arr.spec_index(cpu_id).view().view().view();
    let process = k.prc_mp.spec_index(process_ptr);
    let thread = k.thr_mp.spec_index(thread_ptr);
    let owner = k.ctn_mp.spec_index(owner_ptr);
    let base = owner.view_rodata().view().depth + 1;
    &&& cpu_id == lctx.cpu_id()
    &&& killer_held_context(k, lctx, process_ptr, thread_ptr, lctx.container_lock_map().dom())
    &&& lctx.thread_lock_map().dom() =~= set![thread_ptr]
    &&& lctx.process_lock_map().dom() =~= set![process_ptr]
    &&& lctx.cpu_set_lock_map().dom().is_empty()
    &&& k.prc_mp.dom().contains(process_ptr)
    &&& k.thr_mp.dom().contains(thread_ptr)
    &&& k.cpu_published[cpu_id as int].view() == (cpu.current_cr3, cpu.current_pcid)
    &&& cpu.owning_container == owner_ptr
    &&& cpu.process_depth == process.view_rodata().view().depth
    &&& cpu.container_depth == process.view_rodata().view().container_depth
    &&& !k.cpu_arr.spec_index(cpu_id).view().being_killed()
    &&& !process.being_killed()
    &&& process.view().state.view() is Running
    &&& !thread.being_killed()
    &&& thread.view().state == (ThreadState::RUNNING { cpu_id })
    &&& thread.view().owning_proc == process_ptr
    &&& thread.view().temp_alloc_clean()
    &&& thread.view().free_quota_pending_clean()
    &&& thread.view().syscall_progress.view() == kill_container_progress(if chain.len() == 0 { owner_ptr } else { chain[chain.len() - 1] }, ContainerKillStage::Walk)
    &&& !thread.view_ghost().exited
    &&& killer_info.process == process_ptr
    &&& k.ctn_mp.dom().contains(owner_ptr)
    &&& !owner.being_killed()
    &&& owner.view_rodata().view().depth == cpu.container_depth
    &&& typed_lock_map_contains_mode(lctx.container_lock_map(), owner_ptr, TypedLockMode::Write)
    &&& cpu_perm.state() is WriteLock && cpu_perm.thread_id() == lctx.thread_id() && cpu_perm.lock_id() == k.cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id
    &&& process_perm.state() is WriteLock && process_perm.thread_id() == lctx.thread_id() && process_perm.lock_id() == process.locking_thread()->Write_lock_id
    &&& thread_perm.state() is WriteLock && thread_perm.thread_id() == lctx.thread_id() && thread_perm.lock_id() == thread.locking_thread()->Write_lock_id
    &&& owner_perm.state() is WriteLock && owner_perm.thread_id() == lctx.thread_id() && owner_perm.lock_id() == owner.locking_thread()->Write_lock_id
    &&& forall|c: RwLockContainerPtr| #![trigger lctx.container_lock_map().dom().contains(c)] lctx.container_lock_map().dom().contains(c) && c != owner_ptr ==> {
        let index = k.ctn_mp.spec_index(c).view_rodata().view().depth - base;
        &&& 0 <= index < chain.len()
        &&& chain[index] == c
    }
    &&& forall|i: int| #![trigger chain[i]] 0 <= i < chain.len() ==> {
        let c = k.ctn_mp.spec_index(chain[i]);
        &&& k.ctn_mp.dom().contains(chain[i])
        &&& c.killer_info() == Some(killer_info)
        &&& typed_lock_map_contains_mode(lctx.container_lock_map(), chain[i], TypedLockMode::Write)
        &&& c.view_rodata().view().depth == base + i
        &&& c.view_ghost().uppertree_seq.view().contains(owner_ptr)
        &&& i == 0 ==> c.view_rodata().view().parent == Some(owner_ptr)
        &&& i < chain.len() - 1 ==> !c.view_ghost().owned_processes.view().is_empty()
        &&& chain_perms.dom().contains(chain[i])
        &&& chain_perms[chain[i]].state() is WriteLock
        &&& chain_perms[chain[i]].thread_id() == lctx.thread_id()
        &&& chain_perms[chain[i]].lock_id() == c.locking_thread()->Write_lock_id
    }
    &&& forall|i: int, j: int| #![trigger chain[i], chain[j]] 0 <= i && j == i + 1 && j < chain.len() ==> k.ctn_mp.spec_index(chain[j]).view_rodata().view().parent == Some(chain[i])
}
} // verus!
