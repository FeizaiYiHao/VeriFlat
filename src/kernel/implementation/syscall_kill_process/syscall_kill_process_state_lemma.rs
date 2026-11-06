use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_walk_spec::{KillScope, kill_walk_state};

verus! {
/// Every user 1G L3 entry of the table `pt_ptr` with the kernel_present and PS bits set, and every present 1G mapping of it, names a Mapped1g page that lists `pt_ptr` at that VA.
pub(crate) proof fn mapped_1g_page_pagetable_wf_table_at(pt_mp: PageTableLockedMap, pt_lower: PageTableLowerMap, pg_arr: PageLockedArray, pt_ptr: RwLockPageTableRoot)
    requires
        mapped_1g_page_pagetable_wf(pt_mp, pt_lower, pg_arr),
        pt_mp.dom().contains(pt_ptr),
    ensures
        forall|l4i: L4Index, l3i: L3Index| #![trigger whole_pagetable(pt_mp, pt_lower, pt_ptr).spec_held_1g_l3(l4i, l3i)]
            whole_pagetable(pt_mp, pt_lower, pt_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && whole_pagetable(pt_mp, pt_lower, pt_ptr).spec_held_1g_l3(l4i, l3i) is Some ==> {
                let pg_idx = page_ptr2page_index(whole_pagetable(pt_mp, pt_lower, pt_ptr).spec_held_1g_l3(l4i, l3i)->0.addr);
                &&& index_valid(NUM_PAGES, pg_idx)
                &&& pg_arr.spec_index(pg_idx).view().view().state == PageState::Mapped1g
                &&& pg_arr.spec_index(pg_idx).view().view().mappings().contains((pt_ptr, spec_index2va((l4i, l3i, 0, 0))))
            },
        forall|va: VAddr| #![trigger whole_pagetable(pt_mp, pt_lower, pt_ptr).mapping_1g().contains_key(va)]
            whole_pagetable(pt_mp, pt_lower, pt_ptr).mapping_1g().contains_key(va) ==> {
                let page = pg_arr.spec_index(page_ptr2page_index(whole_pagetable(pt_mp, pt_lower, pt_ptr).mapping_1g().spec_index(va).addr)).view().view();
                &&& page.state == PageState::Mapped1g
                &&& page.mappings().contains((pt_ptr, va))
            },
{ reveal(mapped_1g_page_pagetable_wf); }

/// `kill_walk_state` survives a step from `pre` to `post` that keeps the typed lock maps, the containers, processes, and
/// threads `pre_lctx` holds, and the killer's cpu with its hardware cr3/pcid word.
pub(crate) proof fn kill_walk_state_preserved_for_held_objects_unchanged(
    pre: KernelK, post: KernelK, pre_lctx: LocalContext, post_lctx: LocalContext, cpu_id: CpuId, scope: KillScope, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    chain: Seq<RwLockProcessPtr>, victim: Option<RwLockThreadPtr>, stage: KillStage, cpu_perm: LockPerm, process_perm: LockPerm, thread_perm: LockPerm,
    chain_perms: Map<RwLockProcessPtr, LockPerm>,
)
    requires
        kill_walk_state(pre, pre_lctx, cpu_id, scope, prc_ptr, thrd_ptr, chain, victim, stage, cpu_perm, process_perm, thread_perm, chain_perms),
        typed_lock_maps_unchanged(&pre_lctx, &post_lctx),
        post_lctx.thread_id() == pre_lctx.thread_id(),
        post_lctx.cpu_id() == pre_lctx.cpu_id(),
        held_containers_unchanged(pre.ctn_mp, post.ctn_mp, &pre_lctx),
        held_processes_unchanged(pre.prc_mp, post.prc_mp, &pre_lctx),
        held_threads_unchanged(pre.thrd_mp, post.thrd_mp, &pre_lctx),
        post.cpu_arr.spec_index(cpu_id).view() == pre.cpu_arr.spec_index(cpu_id).view(),
        post.cpu_hw_cr3_pcid[cpu_id as int].view() == pre.cpu_hw_cr3_pcid[cpu_id as int].view(),
    ensures
        kill_walk_state(post, post_lctx, cpu_id, scope, prc_ptr, thrd_ptr, chain, victim, stage, cpu_perm, process_perm, thread_perm, chain_perms),
{}
}
