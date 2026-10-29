use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_walk::{KillScope, kill_walk_state};

verus! {
/// `kill_walk_state` survives a step from `pre` to `post` that keeps the typed lock maps, the containers, processes, and
/// threads `pre_lctx` holds, and the killer's cpu with its hardware cr3/pcid word.
pub(crate) proof fn kill_walk_state_preserved_for_held_objects_unchanged(
    pre: KernelK, post: KernelK, pre_lctx: LocalContext, post_lctx: LocalContext, cpu_id: CpuId, scope: KillScope, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    chain: Seq<RwLockProcessPtr>, victim: Option<RwLockThreadPtr>, stage: KillStage, cpu_perm: LockPerm, process_perm: LockPerm, thread_perm: LockPerm,
    chain_perms: Map<RwLockProcessPtr, LockPerm>,
)
    requires
        kill_walk_state(pre, pre_lctx, cpu_id, scope, process_ptr, thread_ptr, chain, victim, stage, cpu_perm, process_perm, thread_perm, chain_perms),
        typed_lock_maps_unchanged(&pre_lctx, &post_lctx),
        post_lctx.thread_id() == pre_lctx.thread_id(),
        post_lctx.cpu_id() == pre_lctx.cpu_id(),
        held_containers_unchanged(pre.ctn_mp, post.ctn_mp, &pre_lctx),
        held_processes_unchanged(pre.prc_mp, post.prc_mp, &pre_lctx),
        held_threads_unchanged(pre.thr_mp, post.thr_mp, &pre_lctx),
        post.cpu_arr.spec_index(cpu_id).view() == pre.cpu_arr.spec_index(cpu_id).view(),
        post.cpu_hw_cr3_pcid[cpu_id as int].view() == pre.cpu_hw_cr3_pcid[cpu_id as int].view(),
    ensures
        kill_walk_state(post, post_lctx, cpu_id, scope, process_ptr, thread_ptr, chain, victim, stage, cpu_perm, process_perm, thread_perm, chain_perms),
{}
}
