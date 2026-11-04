use vstd::prelude::*;
use crate::*;

verus! {
/// Container owned_threads and thread owning_container agree, and a container's indirect threads are exactly the
/// threads that list it among their upper containers.
#[verifier::opaque]
pub open spec fn container_thread_wf(ctn_mp: ContainerLockedMap, thrd_mp: ThreadLockedMap) -> bool {
    // Container -> owned threads.
    &&& forall|c: RwLockContainerPtr, t: RwLockThreadPtr|
        #![trigger ctn_mp.spec_index(c).view_ghost().owned_threads.view().contains(t)]
        ctn_mp.dom().contains(c) && ctn_mp.spec_index(c).view_ghost().owned_threads.view().contains(t) ==> {
            &&& thrd_mp.dom().contains(t)
            &&& thrd_mp.spec_index(t).view().owning_container == c
            &&& thrd_mp.spec_index(t).view().container_depth == ctn_mp.spec_index(c).view_rodata().view().depth
            &&& thrd_mp.spec_index(t).view().upper_container_seq == ctn_mp.spec_index(c).view_ghost().uppertree_seq
        }
    // Thread -> container.
    &&& forall|t: RwLockThreadPtr|
        #![trigger thrd_mp.dom().contains(t)]
        thrd_mp.dom().contains(t) ==> {
            let ctn_ptr = thrd_mp.spec_index(t).view().owning_container;
            &&& ctn_mp.dom().contains(ctn_ptr)
            &&& ctn_mp.spec_index(ctn_ptr).view_ghost().owned_threads.view().contains(t)
        }
    // Indirect threads <-> upper containers.
    &&& forall|c: RwLockContainerPtr, t: RwLockThreadPtr|
        #![trigger ctn_mp.spec_index(c).view_ghost().owned_indirect_threads.view().contains(t)]
        #![trigger ctn_mp.dom().contains(c), thrd_mp.dom().contains(t)]
        #![trigger ctn_mp.spec_index(c), thrd_mp.spec_index(t)]
        ctn_mp.dom().contains(c) && ctn_mp.spec_index(c).view_ghost().owned_indirect_threads.view().contains(t) ==> {
            &&& thrd_mp.dom().contains(t)
            &&& thrd_mp.spec_index(t).view().upper_container_seq.view().contains(c)
        }
    &&& forall|c: RwLockContainerPtr, t: RwLockThreadPtr|
        #![trigger thrd_mp.spec_index(t).view().upper_container_seq.view().contains(c)]
        #![trigger ctn_mp.dom().contains(c), thrd_mp.dom().contains(t)]
        #![trigger ctn_mp.spec_index(c), thrd_mp.spec_index(t)]
        thrd_mp.dom().contains(t) && thrd_mp.spec_index(t).view().upper_container_seq.view().contains(c) ==> {
            &&& ctn_mp.dom().contains(c)
            &&& ctn_mp.spec_index(c).view_ghost().owned_indirect_threads.view().contains(t)
        }
}

/// Thread `thrd_ptr` owned by container `ctn_ptr` is in the thread map at `ctn_ptr`'s depth and shares `ctn_ptr`'s upper-tree sequence.
pub proof fn container_thread_wf_owned_thread_at(ctn_mp: ContainerLockedMap, thrd_mp: ThreadLockedMap, ctn_ptr: RwLockContainerPtr, thrd_ptr: RwLockThreadPtr)
    requires
        container_thread_wf(ctn_mp, thrd_mp),
        ctn_mp.dom().contains(ctn_ptr),
    ensures
        ctn_mp.spec_index(ctn_ptr).view_ghost().owned_threads.view().contains(thrd_ptr) ==> {
            &&& thrd_mp.dom().contains(thrd_ptr)
            &&& thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr
            &&& thrd_mp.spec_index(thrd_ptr).view().container_depth == ctn_mp.spec_index(ctn_ptr).view_rodata().view().depth
            &&& thrd_mp.spec_index(thrd_ptr).view().upper_container_seq == ctn_mp.spec_index(ctn_ptr).view_ghost().uppertree_seq
        },
{ reveal(container_thread_wf); }

pub proof fn container_thread_wf_thread_at(ctn_mp: ContainerLockedMap, thrd_mp: ThreadLockedMap, thrd_ptr: RwLockThreadPtr)
    requires
        container_thread_wf(ctn_mp, thrd_mp),
        thrd_mp.dom().contains(thrd_ptr),
    ensures
        ({
            let ctn_ptr = thrd_mp.spec_index(thrd_ptr).view().owning_container;
            &&& ctn_mp.dom().contains(ctn_ptr)
            &&& ctn_mp.spec_index(ctn_ptr).view_ghost().owned_threads.view().contains(thrd_ptr)
            &&& thrd_mp.spec_index(thrd_ptr).view().container_depth == ctn_mp.spec_index(ctn_ptr).view_rodata().view().depth
        }),
{ reveal(container_thread_wf); }

/// Indirect thread `thrd_ptr` of container `ctn_ptr` is in the thread map and has `ctn_ptr` among its upper containers.
pub proof fn container_thread_wf_indirect_thread_at(ctn_mp: ContainerLockedMap, thrd_mp: ThreadLockedMap, ctn_ptr: RwLockContainerPtr, thrd_ptr: RwLockThreadPtr)
    requires
        container_thread_wf(ctn_mp, thrd_mp),
        ctn_mp.dom().contains(ctn_ptr),
    ensures
        ctn_mp.spec_index(ctn_ptr).view_ghost().owned_indirect_threads.view().contains(thrd_ptr)
            ==> thrd_mp.dom().contains(thrd_ptr) && thrd_mp.spec_index(thrd_ptr).view().upper_container_seq.view().contains(ctn_ptr),
{ reveal(container_thread_wf); }

/// Thread `thrd_ptr`'s owning container exists and its uppertree is the thread's recorded upper-container sequence.
pub proof fn container_thread_wf_uppertree_at(ctn_mp: ContainerLockedMap, thrd_mp: ThreadLockedMap, thrd_ptr: RwLockThreadPtr)
    requires
        container_thread_wf(ctn_mp, thrd_mp),
        thrd_mp.dom().contains(thrd_ptr),
    ensures
        ({
            let ctn_ptr = thrd_mp.spec_index(thrd_ptr).view().owning_container;
            &&& ctn_mp.dom().contains(ctn_ptr)
            &&& ctn_mp.spec_index(ctn_ptr).view_ghost().uppertree_seq == thrd_mp.spec_index(thrd_ptr).view().upper_container_seq
        }),
{ reveal(container_thread_wf); }
}
