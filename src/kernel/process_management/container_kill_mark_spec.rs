use vstd::prelude::*;
use crate::*;

verus! {
/// A marked container and its parent stay write-held by the thread that holds its killer's process.
#[verifier::opaque]
pub open spec fn container_kill_mark_wf(container_map: ContainerLockedMap, process_map: ProcessLockedMap) -> bool {
    forall|c: RwLockContainerPtr|
        #![trigger container_map.spec_index(c).killer_info()]
        container_map.dom().contains(c) && container_map.spec_index(c).killer_info() is Some ==> {
            let killer_process = container_map.spec_index(c).killer_info()->Some_0.process;
            let killer_tid = process_map.spec_index(killer_process).locking_thread()->Write_thread_id;
            let parent = container_map.spec_index(c).view_rodata().view().parent;
            &&& process_map.dom().contains(killer_process)
            &&& process_map.spec_index(killer_process).locking_thread() is Write
            &&& container_map.spec_index(c).wlocked_by_thread(killer_tid)
            &&& parent is Some
            &&& container_map.dom().contains(parent->Some_0)
            &&& container_map.spec_index(parent->Some_0).wlocked_by_thread(killer_tid)
        }
}

pub proof fn container_kill_mark_wf_at(container_map: ContainerLockedMap, process_map: ProcessLockedMap, c: RwLockContainerPtr)
    requires
        container_kill_mark_wf(container_map, process_map),
    ensures
        container_map.dom().contains(c) && container_map.spec_index(c).killer_info() is Some ==> ({
            let killer_process = container_map.spec_index(c).killer_info()->Some_0.process;
            let killer_tid = process_map.spec_index(killer_process).locking_thread()->Write_thread_id;
            let parent = container_map.spec_index(c).view_rodata().view().parent;
            &&& process_map.dom().contains(killer_process)
            &&& process_map.spec_index(killer_process).locking_thread() is Write
            &&& container_map.spec_index(c).wlocked_by_thread(killer_tid)
            &&& parent is Some
            &&& container_map.dom().contains(parent->Some_0)
            &&& container_map.spec_index(parent->Some_0).wlocked_by_thread(killer_tid)
        }),
{ reveal(container_kill_mark_wf); }
}
