use vstd::prelude::*;
use crate::*;

verus! {
/// A marked container and its parent stay write-held by the thread that holds its killer's process.
#[verifier::opaque]
pub open spec fn container_kill_mark_wf(ctn_mp: ContainerLockedMap, prc_mp: ProcessLockedMap) -> bool {
    forall|c: RwLockContainerPtr|
        #![trigger ctn_mp.spec_index(c).killer_info()]
        ctn_mp.dom().contains(c) && ctn_mp.spec_index(c).killer_info() is Some ==> {
            let killer_process = ctn_mp.spec_index(c).killer_info()->Some_0.process;
            let killer_tid = prc_mp.spec_index(killer_process).locking_thread()->Write_thread_id;
            let parent = ctn_mp.spec_index(c).view_rodata().view().parent;
            &&& prc_mp.dom().contains(killer_process)
            &&& prc_mp.spec_index(killer_process).locking_thread() is Write
            &&& ctn_mp.spec_index(c).wlocked_by_thread(killer_tid)
            &&& parent is Some
            &&& ctn_mp.dom().contains(parent->Some_0)
            &&& ctn_mp.spec_index(parent->Some_0).wlocked_by_thread(killer_tid)
        }
}

pub proof fn container_kill_mark_wf_at(ctn_mp: ContainerLockedMap, prc_mp: ProcessLockedMap, ctn_ptr: RwLockContainerPtr)
    requires
        container_kill_mark_wf(ctn_mp, prc_mp),
    ensures
        ctn_mp.dom().contains(ctn_ptr) && ctn_mp.spec_index(ctn_ptr).killer_info() is Some ==> ({
            let killer_process = ctn_mp.spec_index(ctn_ptr).killer_info()->Some_0.process;
            let killer_tid = prc_mp.spec_index(killer_process).locking_thread()->Write_thread_id;
            let parent = ctn_mp.spec_index(ctn_ptr).view_rodata().view().parent;
            &&& prc_mp.dom().contains(killer_process)
            &&& prc_mp.spec_index(killer_process).locking_thread() is Write
            &&& ctn_mp.spec_index(ctn_ptr).wlocked_by_thread(killer_tid)
            &&& parent is Some
            &&& ctn_mp.dom().contains(parent->Some_0)
            &&& ctn_mp.spec_index(parent->Some_0).wlocked_by_thread(killer_tid)
        }),
{ reveal(container_kill_mark_wf); }
}
