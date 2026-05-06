use std::os::unix::thread;

use vstd::prelude::*;
use crate::*;

verus! {
   pub proof fn process_thread_wf_proof()
        ensures
            forall|process_map: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, PROCESS_HAS_KILL_STATE>, thread_map: LockedMap<RwLockThreadPtr, Thread, (), THREAD_HAS_KILL_STATE>|
                process_thread_wf(process_map, thread_map) <==> process_thread_wf_inner(process_map, thread_map)
    {}

    pub closed spec fn process_thread_wf(process_map: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, PROCESS_HAS_KILL_STATE>, thread_map: LockedMap<RwLockThreadPtr, Thread, (), THREAD_HAS_KILL_STATE>) -> bool {
        process_thread_wf_inner(process_map, thread_map)
    }
    pub open spec fn process_thread_wf_inner(process_map: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, PROCESS_HAS_KILL_STATE>, 
            thread_map: LockedMap<RwLockThreadPtr, Thread, (), THREAD_HAS_KILL_STATE>) -> bool {
        &&&
        forall|p_ptr:RwLockProcessPtr, t_ptr:RwLockThreadPtr|
            #![trigger process_map.spec_index(p_ptr).view(), thread_map.spec_index(t_ptr).view()]
            process_map.dom().contains(p_ptr) && process_map.spec_index(p_ptr).view().owned_threads.view().contains(t_ptr)
            ==>
            thread_map.dom().contains(t_ptr) && thread_map.spec_index(t_ptr).view().owning_proc == p_ptr
            &&
            thread_map.spec_index(t_ptr).view().proc_pagetable_ptr == process_map.spec_index(p_ptr).view().pagetable
            &&
            process_map.spec_index(p_ptr).view().owned_threads.map().spec_index(t_ptr) 
                == thread_map.spec_index(t_ptr).view().proc_linkedlist_node.addr()
        &&&
        forall|t_ptr:RwLockThreadPtr|
            #![trigger process_map.dom().contains(thread_map.spec_index(t_ptr).view().owning_proc)]
            thread_map.dom().contains(t_ptr)
            ==>
            process_map.dom().contains(thread_map.spec_index(t_ptr).view().owning_proc)
            &&
            process_map.spec_index(thread_map.spec_index(t_ptr).view().owning_proc).view().owned_threads.view().contains(t_ptr)
    }

}