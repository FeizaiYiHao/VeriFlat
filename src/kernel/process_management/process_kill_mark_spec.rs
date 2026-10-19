use vstd::prelude::*;
use crate::*;

verus! {
/// A marked process and its parent stay write-held by the thread that holds its killer's process, so a process a walker
/// write-holds carries no foreign mark on any process it killed and no foreign mark on any of its children. A marked
/// container root has no parent: its container carries the same mark and stays write-held by that thread instead.
// Proof dependencies (confirmed): container_process_wf, per_container_process_tree_wf, process_children_parent_wf.
#[verifier::opaque]
pub open spec fn process_kill_mark_wf(container_map: ContainerLockedMap, process_map: ProcessLockedMap) -> bool {
    forall|d: RwLockProcessPtr|
        #![trigger process_map.spec_index(d).killer_info()]
        process_map.dom().contains(d) && process_map.spec_index(d).killer_info() is Some ==> {
            let killer_process = process_map.spec_index(d).killer_info()->Some_0.process;
            let killer_tid = process_map.spec_index(killer_process).locking_thread()->Write_thread_id;
            let ro = process_map.spec_index(d).view_rodata().view();
            &&& process_map.dom().contains(killer_process)
            &&& process_map.spec_index(killer_process).locking_thread() is Write
            &&& process_map.spec_index(d).wlocked_by_thread(killer_tid)
            &&& ro.parent is Some ==> process_map.dom().contains(ro.parent->Some_0) && process_map.spec_index(ro.parent->Some_0).wlocked_by_thread(killer_tid)
            &&& ro.parent is None ==> {
                &&& container_map.dom().contains(ro.owning_container)
                &&& container_map.spec_index(ro.owning_container).view().root_process == d
                &&& container_map.spec_index(ro.owning_container).killer_info() == process_map.spec_index(d).killer_info()
                &&& container_map.spec_index(ro.owning_container).wlocked_by_thread(killer_tid)
            }
        }
}

pub proof fn process_kill_mark_wf_at(container_map: ContainerLockedMap, process_map: ProcessLockedMap, d: RwLockProcessPtr)
    requires
        process_kill_mark_wf(container_map, process_map),
    ensures
        process_map.dom().contains(d) && process_map.spec_index(d).killer_info() is Some ==> ({
            let killer_process = process_map.spec_index(d).killer_info()->Some_0.process;
            let killer_tid = process_map.spec_index(killer_process).locking_thread()->Write_thread_id;
            let ro = process_map.spec_index(d).view_rodata().view();
            &&& process_map.dom().contains(killer_process)
            &&& process_map.spec_index(killer_process).locking_thread() is Write
            &&& process_map.spec_index(d).wlocked_by_thread(killer_tid)
            &&& ro.parent is Some ==> process_map.dom().contains(ro.parent->Some_0) && process_map.spec_index(ro.parent->Some_0).wlocked_by_thread(killer_tid)
            &&& ro.parent is None ==> {
                &&& container_map.dom().contains(ro.owning_container)
                &&& container_map.spec_index(ro.owning_container).view().root_process == d
                &&& container_map.spec_index(ro.owning_container).killer_info() == process_map.spec_index(d).killer_info()
                &&& container_map.spec_index(ro.owning_container).wlocked_by_thread(killer_tid)
            }
        }),
{ reveal(process_kill_mark_wf); }
}
