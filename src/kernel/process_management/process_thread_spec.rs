use std::os::unix::thread;

use vstd::prelude::*;
use crate::*;

verus! {
    #[verifier::opaque]
    pub open spec fn process_thread_wf(process_map: ProcessLockedMap, 
            thread_map: ThreadLockedMap) -> bool {
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
