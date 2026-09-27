use vstd::prelude::*;
use crate::*;

verus! {
#[verifier::opaque]
/// Moves one Off CPU owned by the parent container into the new child container's
/// CPU set. Every other kernel object is unchanged.
pub open spec fn new_container_cpu_transfer_transition(
    pre: KernelK, post: KernelK, parent_container: RwLockContainerPtr, child_container: RwLockContainerPtr,
    parent_cpu_set: RwLockCpuSetPtr, child_cpu_set: RwLockCpuSetPtr, transfer_cpu_id: CpuId, thread_id: LockThreadId,
) -> bool {
    &&& index_valid(NUM_CPUS, transfer_cpu_id)
    &&& parent_container != child_container
    &&& parent_cpu_set != child_cpu_set
    &&& pre.ctn_mp.dom().contains(parent_container)
    &&& pre.ctn_mp.dom().contains(child_container)
    &&& pre.cpu_set_mp.dom().contains(parent_cpu_set)
    &&& pre.cpu_set_mp.dom().contains(child_cpu_set)
    &&& pre.ctn_mp.spec_index(parent_container).view_rodata().view().cpu_set == parent_cpu_set
    &&& pre.ctn_mp.spec_index(child_container).view_rodata().view().cpu_set == child_cpu_set
    &&& pre.cpu_set_mp.spec_index(parent_cpu_set).view().owned_cpus.view().contains(transfer_cpu_id)
    &&& pre.cpu_set_mp.spec_index(parent_cpu_set).view().owned_cpus.closed_view().contains(transfer_cpu_id)
    &&& !pre.cpu_set_mp.spec_index(child_cpu_set).view().owned_cpus.view().contains(transfer_cpu_id)
    &&& pre.cpu_arr.spec_index(transfer_cpu_id).view().view().view().state is Off
    &&& pre.cpu_arr.spec_index(transfer_cpu_id).view().view().view().owning_container == parent_container
    &&& post == (KernelK { cpu_arr: post.cpu_arr, cpu_set_mp: post.cpu_set_mp, ..pre })
    &&& post.cpu_arr.view().len() == pre.cpu_arr.view().len()
    &&& forall|cpu_i: CpuId|
        #![trigger pre.cpu_arr.spec_index(cpu_i)]
        #![trigger post.cpu_arr.spec_index(cpu_i)]
        index_valid(NUM_CPUS, cpu_i) && cpu_i != transfer_cpu_id ==> post.cpu_arr.spec_index(cpu_i) == pre.cpu_arr.spec_index(cpu_i)
    &&& {
        let before = pre.cpu_arr.spec_index(transfer_cpu_id).view();
        let after = post.cpu_arr.spec_index(transfer_cpu_id).view();
        &&& after.is_init() == before.is_init()
        &&& after.view_rodata() == before.view_rodata()
        &&& after.view_ghost() == before.view_ghost()
        &&& after.being_killed() == before.being_killed()
        &&& after.locking_thread() is Write
        &&& after.locking_thread()->Write_thread_id == thread_id
        &&& after.view().view() == CpuView { owning_container: child_container, container_depth: pre.ctn_mp.spec_index(child_container).view_rodata().view().depth, ..before.view().view() }
    }
    &&& post.cpu_set_mp.dom() == pre.cpu_set_mp.dom()
    &&& forall|key: RwLockCpuSetPtr|
        #![trigger pre.cpu_set_mp.spec_index(key)]
        #![trigger post.cpu_set_mp.spec_index(key)]
        pre.cpu_set_mp.dom().contains(key) ==> {
            let before = pre.cpu_set_mp.spec_index(key);
            let after = post.cpu_set_mp.spec_index(key);
            &&& post.cpu_set_mp.view().spec_index(key).is_init() == pre.cpu_set_mp.view().spec_index(key).is_init()
            &&& post.cpu_set_mp.view().spec_index(key).addr() == pre.cpu_set_mp.view().spec_index(key).addr()
            &&& !(key == parent_cpu_set || key == child_cpu_set) ==> after == before
            &&& (key == parent_cpu_set || key == child_cpu_set) ==> {
                &&& after.is_init() == before.is_init()
                &&& after.view_rodata() == before.view_rodata()
                &&& after.view_ghost() == before.view_ghost()
                &&& after.being_killed() == before.being_killed()
                &&& after.locking_thread() is Write
                &&& after.locking_thread()->Write_thread_id == thread_id
                &&& after.view().owning_container == before.view().owning_container
                &&& after.view().container_depth == before.view().container_depth
                &&& after.view().owned_cpus.view() == if key == parent_cpu_set { before.view().owned_cpus.view().remove(transfer_cpu_id) } else { before.view().owned_cpus.view().insert(transfer_cpu_id) }
                &&& after.view().owned_cpus.closed_view() == if key == parent_cpu_set { before.view().owned_cpus.closed_view().remove(transfer_cpu_id) } else { before.view().owned_cpus.closed_view().insert(transfer_cpu_id) }
                &&& after.view().owned_cpus.data.view() == before.view().owned_cpus.data.view().update(transfer_cpu_id as int, key == child_cpu_set)
                &&& after.view().owned_cpus.closed.view() == before.view().owned_cpus.closed.view().update(transfer_cpu_id as int, key == child_cpu_set)
                &&& after.view().owned_cpus.len as int == before.view().owned_cpus.len as int + if key == parent_cpu_set { -1int } else { 1int }
            }
        }
}
}
