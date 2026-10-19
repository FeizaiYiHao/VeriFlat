use vstd::prelude::*;
use crate::*;

verus! {
/// One cpu move of the container kill: the cpu `moved` leaves the target's cpu set `source_set` and joins the killer
/// container's cpu set `target_set` (closed when `closed`), takes the killer's container `target` at `depth` as its
/// owner, and its request cell in the target's table `flags_ptr` clears; the cpu, both sets, and the cell keep their
/// locks and marks, and nothing else changes.
#[verifier::opaque]
pub(crate) open spec fn kill_container_cpus_eof_transition_framing(
    pre: KernelK, post: KernelK, source_set: RwLockCpuSetPtr, target_set: RwLockCpuSetPtr, flags_ptr: RwLockCpuOfflineFlagsPtr, moved: CpuId, target: RwLockContainerPtr,
    depth: usize, closed: bool,
) -> bool {
    let old_table = pre.cpu_offline_mp.spec_index(flags_ptr);
    let new_table = post.cpu_offline_mp.spec_index(flags_ptr);
    let old_cell = old_table.flags.spec_index(moved).view();
    let new_cell = new_table.flags.spec_index(moved).view();
    &&& post == (KernelK { cpu_arr: post.cpu_arr, cpu_set_mp: post.cpu_set_mp, cpu_offline_mp: post.cpu_offline_mp, ..pre })
    &&& post.cpu_arr.view().len() == pre.cpu_arr.view().len()
    &&& forall|cpu_i: CpuId| #![trigger pre.cpu_arr.spec_index(cpu_i)] #![trigger post.cpu_arr.spec_index(cpu_i)]
        index_valid(NUM_CPUS, cpu_i) && cpu_i != moved ==> post.cpu_arr.spec_index(cpu_i) == pre.cpu_arr.spec_index(cpu_i)
    &&& {
        let before = pre.cpu_arr.spec_index(moved).view();
        let after = post.cpu_arr.spec_index(moved).view();
        &&& after.is_init() == before.is_init()
        &&& after.view_rodata() == before.view_rodata()
        &&& after.view_ghost() == before.view_ghost()
        &&& after.being_killed() == before.being_killed()
        &&& after.locking_thread() == before.locking_thread()
        &&& after.view().view() == (CpuView { owning_container: target, container_depth: depth, ..before.view().view() })
        &&& after.view().wf()
    }
    &&& post.cpu_set_mp.dom() == pre.cpu_set_mp.dom()
    &&& forall|key: RwLockCpuSetPtr| #![trigger pre.cpu_set_mp.spec_index(key)] #![trigger post.cpu_set_mp.spec_index(key)]
        pre.cpu_set_mp.dom().contains(key) ==> {
            let before = pre.cpu_set_mp.spec_index(key);
            let after = post.cpu_set_mp.spec_index(key);
            &&& !(key == source_set || key == target_set) ==> after == before
            &&& (key == source_set || key == target_set) ==> {
                &&& after.is_init() == before.is_init()
                &&& after.view_rodata() == before.view_rodata()
                &&& after.view_ghost() == before.view_ghost()
                &&& after.being_killed() == before.being_killed()
                &&& after.killer_info() == before.killer_info()
                &&& after.locking_thread() == before.locking_thread()
                &&& after.view().owning_container == before.view().owning_container
                &&& after.view().container_depth == before.view().container_depth
                &&& after.view().owned_cpus.view() == if key == source_set { before.view().owned_cpus.view().remove(moved) } else { before.view().owned_cpus.view().insert(moved) }
                &&& after.view().owned_cpus.closed_view() == if key == source_set { before.view().owned_cpus.closed_view().remove(moved) }
                    else if closed { before.view().owned_cpus.closed_view().insert(moved) } else { before.view().owned_cpus.closed_view() }
            }
        }
    &&& post.cpu_offline_mp.unchanged_except(&pre.cpu_offline_mp, flags_ptr)
    &&& new_table.owning_container == old_table.owning_container
    &&& new_table.container_depth == old_table.container_depth
    &&& new_table.flags.entries_unchanged_except(&old_table.flags, moved)
    &&& !new_cell.view().requested
    &&& new_cell.view().index() == old_cell.view().index()
    &&& new_cell.is_init()
    &&& new_cell.view_rodata() == old_cell.view_rodata()
    &&& new_cell.view_ghost() == old_cell.view_ghost()
    &&& new_cell.locking_thread() == old_cell.locking_thread()
    &&& new_cell.being_killed() == old_cell.being_killed()
    &&& new_table.flags.lock_id_by_index(moved) == old_table.flags.lock_id_by_index(moved)
    &&& cpu_offline_requests_of(new_table) == cpu_offline_requests_of(old_table).update(moved as int, false)
}

/// Closes every kernel invariant after one cpu move of the container kill from the entry invariants, the summary, and
/// the representation facts the set, cell, and cpu updates guarantee.
pub(crate) proof fn kill_container_cpus_eof(
    pre: KernelK, post: KernelK, source: RwLockContainerPtr, target: RwLockContainerPtr, source_set: RwLockCpuSetPtr, target_set: RwLockCpuSetPtr,
    flags_ptr: RwLockCpuOfflineFlagsPtr, moved: CpuId, depth: usize, closed: bool,
)
    requires
        pre.inv(),
        kill_container_cpus_eof_transition_framing(pre, post, source_set, target_set, flags_ptr, moved, target, depth, closed),
        index_valid(NUM_CPUS, moved),
        source != target,
        source_set != target_set,
        pre.ctn_mp.dom().contains(source),
        pre.ctn_mp.dom().contains(target),
        pre.ctn_mp.spec_index(source).view_rodata().view().cpu_set == source_set,
        pre.ctn_mp.spec_index(target).view_rodata().view().cpu_set == target_set,
        pre.ctn_mp.spec_index(target).view_rodata().view().depth == depth,
        pre.ctn_mp.spec_index(source).view_ghost().owned_processes.view().is_empty(),
        pre.cpu_set_mp.dom().contains(source_set),
        pre.cpu_set_mp.dom().contains(target_set),
        pre.cpu_set_mp.spec_index(source_set).view().owned_cpus.view().contains(moved),
        closed == pre.cpu_set_mp.spec_index(source_set).view().owned_cpus.closed_view().contains(moved),
        !pre.cpu_set_mp.spec_index(target_set).view().owned_cpus.view().contains(moved),
        pre.cpu_arr.spec_index(moved).view().view().view().owning_container == source,
        closed == pre.cpu_arr.spec_index(moved).view().view().view().state is Off,
        !(pre.cpu_arr.spec_index(moved).view().view().view().state is Running),
        flags_ptr == cpu_offline_flags_ptr(source),
        pre.cpu_offline_mp.dom().contains(flags_ptr),
        post.cpu_arr.inv(),
        post.cpu_set_mp.perms_wf(),
        post.cpu_set_mp.spec_index(source_set).view().owned_cpus.wf(),
        post.cpu_set_mp.spec_index(target_set).view().owned_cpus.wf(),
        post.cpu_offline_mp.perms_wf(),
        post.cpu_offline_mp.spec_index(flags_ptr).inv(),
    ensures
        post.inv(),
{
    reveal(kill_container_cpus_eof_transition_framing);
    assert(post.cpu_arr.spec_index(moved).view().view().tlb_dirty_bitmap() == pre.cpu_arr.spec_index(moved).view().view().tlb_dirty_bitmap());
    assert(post.subsystems_inv()) by {
        reveal(cpu_set_perms_wf); reveal(cpu_array_wf); reveal(cpu_published_wf); reveal(cpu_offline_flags_wf); reveal(container_cpu_offline_flags_wf); reveal(KernelK::default_pagetable_wf);
    };
    assert(post.memory_management_inv()) by { assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); }; };
    assert(post.process_management_inv()) by {
        assert(container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
        assert(container_cpu_offline_flags_wf(post.ctn_mp, post.cpu_offline_mp)) by { reveal(container_cpu_offline_flags_wf); };
        assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); };
        assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by { reveal(container_cpu_wf); reveal(container_cpu_set_wf); reveal(cpu_set_perms_wf); };
        assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { reveal(process_cpu_wf); };
        assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { reveal(thread_cpu_wf); };
    };
    assert(post.inv()) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match);
        reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(tlb_wf_spec);
    };
}
} // verus!
