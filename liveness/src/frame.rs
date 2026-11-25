//! Round 5: what one step of cpu `d` leaves alone, stated once for every family of the world. A family proves these
//! frames for its own labels; `world` combines them into the invariants of the whole world.
use vstd::prelude::*;
use crate::*;
use crate::pagetable_locks::*;

verus! {
/// Cpu `x` keeps its entry, the syscall progress of its running thread, and, when that thread records progress or `x`
/// write-holds it, the whole thread, unless `x` is write-locked on neither side; every cpu inside a syscall is
/// write-locked and holds its thread, so this keeps every cpu inside. A cpu in its offline-check window holds no thread,
/// which other cpus may lock and mark.
pub open spec fn cpu_kept(u: KernelU, u2: KernelU, x: CpuId) -> bool {
    (u.cpu_array[x as int].lock_state is WriteLocked || u2.cpu_array[x as int].lock_state is WriteLocked) ==> {
        &&& u2.cpu_array[x as int] == u.cpu_array[x as int]
        &&& u.cpu_array[x as int].current_thread is Some ==> cur_thread(u2, x).syscall_progress == cur_thread(u, x).syscall_progress
        &&& u.cpu_array[x as int].current_thread is Some && (cur_thread(u, x).syscall_progress is Some || cur_thread(u, x).lock_state == (LockStateU::WriteLocked { writer: x }))
            ==> cur_thread(u2, x) == cur_thread(u, x)
        &&& u.cpu_array[x as int].current_thread is Some && cur_thread(u2, x).lock_state == (LockStateU::WriteLocked { writer: x })
            ==> cur_thread(u, x).lock_state == (LockStateU::WriteLocked { writer: x })
    }
}

/// `c` is write-locked but holds no running thread: between the hold step of `cpu_offline_check` and its release or offline
/// step, the only stretch in which a write-locked cpu does not write-hold its running thread.
pub open spec fn cpu_unbound(u: KernelU, c: CpuId) -> bool {
    &&& index_valid(NUM_CPUS, c)
    &&& u.cpu_array[c as int].lock_state is WriteLocked
    &&& u.cpu_array[c as int].current_thread is None || cur_thread(u, c).lock_state != (LockStateU::WriteLocked { writer: c })
}

/// Every cpu but `d` is kept.
pub open spec fn others_kept(u: KernelU, u2: KernelU, d: CpuId) -> bool {
    forall|x: CpuId| #![trigger cpu_kept(u, u2, x)] index_valid(NUM_CPUS, x) && x != d ==> cpu_kept(u, u2, x)
}

/// `c` is not write-locked, so it is inside no syscall.
pub open spec fn cpu_outside(u: KernelU, c: CpuId) -> bool { !(u.cpu_array[c as int].lock_state is WriteLocked) }

/// A container, process, or endpoint that a cpu other than `d` write-holds keeps its lock, and a PCID allocator that a cpu
/// other than `d` write-holds keeps its lock and its free PCIDs.
pub open spec fn foreign_holds_kept(u: KernelU, u2: KernelU, d: CpuId) -> bool {
    &&& forall|ctn: RwLockContainerPtr| #![trigger u2.container_map[ctn]] u.container_map.dom().contains(ctn) && u.container_map[ctn].pcid_allocator_lock is WriteLocked
        && u.container_map[ctn].pcid_allocator_lock->WriteLocked_writer != d ==> u2.container_map[ctn].pcid_allocator_lock == u.container_map[ctn].pcid_allocator_lock
            && u2.container_map[ctn].free_pcids == u.container_map[ctn].free_pcids
    &&& forall|ctn: RwLockContainerPtr| #![trigger u2.container_map[ctn]] u.container_map.dom().contains(ctn) && u.container_map[ctn].lock_state is WriteLocked
        && u.container_map[ctn].lock_state->WriteLocked_writer != d ==> u2.container_map[ctn].lock_state == u.container_map[ctn].lock_state
    &&& forall|prc: RwLockProcessPtr| #![trigger u2.process_map[prc]] u.process_map.dom().contains(prc) && u.process_map[prc].lock_state is WriteLocked
        && u.process_map[prc].lock_state->WriteLocked_writer != d ==> u2.process_map[prc].lock_state == u.process_map[prc].lock_state
    &&& forall|ep: RwLockEndpointPtr| #![trigger u2.endpoint_map[ep]] u.endpoint_map.dom().contains(ep) && u.endpoint_map[ep].lock_state is WriteLocked
        && u.endpoint_map[ep].lock_state->WriteLocked_writer != d ==> u2.endpoint_map[ep].lock_state == u.endpoint_map[ep].lock_state
}

/// The step changes no container, process, endpoint, or PCID allocator lock, and no free PCID.
pub open spec fn object_locks_same(u: KernelU, u2: KernelU) -> bool {
    &&& forall|ctn: RwLockContainerPtr| #![trigger u2.container_map[ctn]] u.container_map.dom().contains(ctn) ==> u2.container_map[ctn].lock_state == u.container_map[ctn].lock_state
        && u2.container_map[ctn].pcid_allocator_lock == u.container_map[ctn].pcid_allocator_lock && u2.container_map[ctn].free_pcids == u.container_map[ctn].free_pcids
    &&& forall|prc: RwLockProcessPtr| #![trigger u2.process_map[prc]] u.process_map.dom().contains(prc) ==> u2.process_map[prc].lock_state == u.process_map[prc].lock_state
    &&& forall|ep: RwLockEndpointPtr| #![trigger u2.endpoint_map[ep]] u.endpoint_map.dom().contains(ep) ==> u2.endpoint_map[ep].lock_state == u.endpoint_map[ep].lock_state
}

/// The step changes no pagetable lock, window lock, or 4K mapping, and creates or removes no pagetable.
pub open spec fn tables_kept(u: KernelU, u2: KernelU) -> bool {
    &&& forall|p: RwLockProcessPtr| #![trigger table_view(u2, p)] table_view(u2, p) == table_view(u, p)
    &&& forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] u2.process_map[p].pagetable->Some_0.mapping_4k == u.process_map[p].pagetable->Some_0.mapping_4k
}

/// The frame of a one-step syscall of `d`: every other cpu, every lock, and every pagetable are kept, and `d` is outside
/// every syscall before and after.
pub open spec fn single_step_frame(u: KernelU, u2: KernelU, d: CpuId) -> bool {
    &&& others_kept(u, u2, d)
    &&& cpu_outside(u, d) && cpu_outside(u2, d)
    &&& object_locks_same(u, u2)
    &&& tables_kept(u, u2)
    &&& !table_op(u, d) && !table_op(u2, d)
}

/// After the step `d` is outside, or runs inside its kernel step, or kept the mode it had inside.
pub open spec fn op_in_step_kept(u: KernelU, u2: KernelU, d: CpuId) -> bool {
    !cpu_outside(u2, d) ==> u2.cpu_array[d as int].op is InStep || (!cpu_outside(u, d) && u2.cpu_array[d as int].op == u.cpu_array[d as int].op)
}

/// A step that changes no lock gives up no foreign hold.
pub proof fn object_locks_same_implies_foreign_holds_kept(u: KernelU, u2: KernelU, d: CpuId)
    requires object_locks_same(u, u2),
    ensures foreign_holds_kept(u, u2, d),
{}

/// A step of `d` that keeps every other cpu, every lock read of the pagetables, and every 4K mapping, while `d` is outside
/// `mmap_4k` and `unmap_4k` before and after and keeps whether and where it reclaims a table, keeps pagetable lock
/// consistency and VA progress.
pub proof fn tables_kept_implies_table_invariants_kept(u: KernelU, u2: KernelU, d: CpuId)
    requires
        pagetable_locks_consistent(u), table_ops_vas(u), others_kept(u, u2, d), tables_kept(u, u2), !table_op(u, d), !table_op(u2, d), !table_sharer(u, d), !table_sharer(u2, d),
        table_killer(u2, d) == table_killer(u, d), table_killer(u, d) ==> table_killer_proc(u2, d) == table_killer_proc(u, d),
    ensures pagetable_locks_consistent(u2), table_ops_vas(u2),
{
    assert forall|x: CpuId| #![trigger other_cpu_unchanged(u, u2, x)] x != d implies other_cpu_unchanged(u, u2, x) by { if index_valid(NUM_CPUS, x) { assert(cpu_kept(u, u2, x)); } };
    table_views_same_implies_locks_consistent_kept(u, u2, d);
    assert forall|c: CpuId| #![trigger table_op(u2, c)] table_op(u2, c) implies table_op_vas(u2, c) by {
        assert(cpu_kept(u, u2, c));
        assert(table_op(u, c));
        assert(table_op_vas(u, c));
        assert(u2.process_map[table_proc(u, c)].pagetable->Some_0.mapping_4k == u.process_map[table_proc(u, c)].pagetable->Some_0.mapping_4k);
    };
    assert forall|c: CpuId| #![trigger table_sharer(u2, c)] table_sharer(u2, c) implies sharer_vas(u2, c) by {
        assert(cpu_kept(u, u2, c));
        assert(table_sharer(u, c) && sharer_vas(u, c));
        assert(u2.process_map[table_proc(u, c)].pagetable->Some_0.mapping_4k == u.process_map[table_proc(u, c)].pagetable->Some_0.mapping_4k);
        if sharer_child(u, c) is Some {
            let ch = sharer_child(u, c)->Some_0;
            assert(u2.process_map[ch].pagetable->Some_0.mapping_4k == u.process_map[ch].pagetable->Some_0.mapping_4k);
        }
    };
}

/// A set of addresses that holds `x` has a least member: descend through smaller members, which cannot go on forever.
pub proof fn vaddr_set_member_implies_least_member_exists(s: Set<VAddr>, x: VAddr)
    requires s.contains(x),
    ensures exists|y: VAddr| s.contains(y) && forall|z: VAddr| #[trigger] s.contains(z) ==> y <= z,
    decreases x,
{
    if exists|z: VAddr| s.contains(z) && z < x {
        let z = choose|z: VAddr| s.contains(z) && z < x;
        vaddr_set_member_implies_least_member_exists(s, z);
    } else {
        assert(forall|z: VAddr| #[trigger] s.contains(z) ==> x <= z);
    }
}
} // verus!
