use vstd::prelude::*;
use crate::*;

verus! {
/// A marked process and its parent stay write-held by the thread that holds its killer's process, so a process a walker
/// write-holds carries no foreign mark on any process it killed and no foreign mark on any of its children.
// Proof dependencies (confirmed): container_process_wf, per_container_process_tree_wf, process_children_parent_wf.
#[verifier::opaque]
pub open spec fn process_kill_mark_wf(process_map: ProcessLockedMap) -> bool {
    forall|d: RwLockProcessPtr|
        #![trigger process_map.spec_index(d).killer_info()]
        process_map.dom().contains(d) && process_map.spec_index(d).killer_info() is Some ==> {
            let killer_process = process_map.spec_index(d).killer_info()->Some_0.process;
            let parent = process_map.spec_index(d).view_rodata().view().parent->Some_0;
            &&& process_map.dom().contains(killer_process)
            &&& process_map.spec_index(killer_process).locking_thread() is Write
            &&& process_map.spec_index(d).wlocked_by_thread(process_map.spec_index(killer_process).locking_thread()->Write_thread_id)
            &&& process_map.spec_index(d).view_rodata().view().parent is Some
            &&& process_map.dom().contains(parent)
            &&& process_map.spec_index(parent).wlocked_by_thread(process_map.spec_index(killer_process).locking_thread()->Write_thread_id)
        }
}

pub proof fn process_kill_mark_wf_at(process_map: ProcessLockedMap, d: RwLockProcessPtr)
    requires
        process_kill_mark_wf(process_map),
    ensures
        process_map.dom().contains(d) && process_map.spec_index(d).killer_info() is Some ==> ({
            let killer_process = process_map.spec_index(d).killer_info()->Some_0.process;
            let parent = process_map.spec_index(d).view_rodata().view().parent->Some_0;
            &&& process_map.dom().contains(killer_process)
            &&& process_map.spec_index(killer_process).locking_thread() is Write
            &&& process_map.spec_index(d).wlocked_by_thread(process_map.spec_index(killer_process).locking_thread()->Write_thread_id)
            &&& process_map.spec_index(d).view_rodata().view().parent is Some
            &&& process_map.dom().contains(parent)
            &&& process_map.spec_index(parent).wlocked_by_thread(process_map.spec_index(killer_process).locking_thread()->Write_thread_id)
        }),
{ reveal(process_kill_mark_wf); }
}
