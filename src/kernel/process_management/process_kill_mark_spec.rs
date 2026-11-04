use vstd::prelude::*;
use crate::*;

verus! {
/// A marked process and its parent stay write-held by the thread that holds its killer's process. A marked container
/// root has no parent: its container carries the same mark and stays write-held by that thread instead.
// Proof dependencies (confirmed): container_process_wf, per_container_process_tree_wf, process_children_parent_wf.
#[verifier::opaque]
pub open spec fn process_kill_mark_wf(ctn_mp: ContainerLockedMap, prc_mp: ProcessLockedMap) -> bool {
    forall|p: RwLockProcessPtr|
        #![trigger prc_mp.spec_index(p).killer_info()]
        prc_mp.dom().contains(p) && prc_mp.spec_index(p).killer_info() is Some ==> {
            let killer_process = prc_mp.spec_index(p).killer_info()->Some_0.process;
            let killer_tid = prc_mp.spec_index(killer_process).locking_thread()->Write_thread_id;
            let ro = prc_mp.spec_index(p).view_rodata().view();
            &&& prc_mp.dom().contains(killer_process)
            &&& prc_mp.spec_index(killer_process).locking_thread() is Write
            &&& prc_mp.spec_index(p).wlocked_by_thread(killer_tid)
            &&& ro.parent is Some ==> {
                &&& prc_mp.dom().contains(ro.parent->Some_0)
                &&& prc_mp.spec_index(ro.parent->Some_0).wlocked_by_thread(killer_tid)
            }
            &&& ro.parent is None ==> {
                &&& ctn_mp.dom().contains(ro.owning_container)
                &&& ctn_mp.spec_index(ro.owning_container).view().root_process == p
                &&& ctn_mp.spec_index(ro.owning_container).killer_info() == prc_mp.spec_index(p).killer_info()
                &&& ctn_mp.spec_index(ro.owning_container).wlocked_by_thread(killer_tid)
            }
        }
}

pub proof fn process_kill_mark_wf_at(ctn_mp: ContainerLockedMap, prc_mp: ProcessLockedMap, prc_ptr: RwLockProcessPtr)
    requires
        process_kill_mark_wf(ctn_mp, prc_mp),
    ensures
        prc_mp.dom().contains(prc_ptr) && prc_mp.spec_index(prc_ptr).killer_info() is Some ==> ({
            let killer_process = prc_mp.spec_index(prc_ptr).killer_info()->Some_0.process;
            let killer_tid = prc_mp.spec_index(killer_process).locking_thread()->Write_thread_id;
            let ro = prc_mp.spec_index(prc_ptr).view_rodata().view();
            &&& prc_mp.dom().contains(killer_process)
            &&& prc_mp.spec_index(killer_process).locking_thread() is Write
            &&& prc_mp.spec_index(prc_ptr).wlocked_by_thread(killer_tid)
            &&& ro.parent is Some ==> {
                &&& prc_mp.dom().contains(ro.parent->Some_0)
                &&& prc_mp.spec_index(ro.parent->Some_0).wlocked_by_thread(killer_tid)
            }
            &&& ro.parent is None ==> {
                &&& ctn_mp.dom().contains(ro.owning_container)
                &&& ctn_mp.spec_index(ro.owning_container).view().root_process == prc_ptr
                &&& ctn_mp.spec_index(ro.owning_container).killer_info() == prc_mp.spec_index(prc_ptr).killer_info()
                &&& ctn_mp.spec_index(ro.owning_container).wlocked_by_thread(killer_tid)
            }
        }),
{ reveal(process_kill_mark_wf); }
}
