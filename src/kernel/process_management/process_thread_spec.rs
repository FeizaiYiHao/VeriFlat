use std::os::unix::thread;

use vstd::prelude::*;
use crate::*;

verus! {
    #[verifier::opaque]
    pub open spec fn process_empty_lists_wlocked(process_map: ProcessLockedMap) -> bool {
        forall|p_ptr:RwLockProcessPtr|
            #![trigger process_map.dom().contains(p_ptr)]
            process_map.dom().contains(p_ptr) && (if process_map.spec_index(p_ptr).view().zombie {
                process_map.spec_index(p_ptr).view().children.view().len() == 0
            } else {
                process_map.spec_index(p_ptr).view().owned_threads.view().len() == 0
            }) ==> process_map.spec_index(p_ptr).wlocked()
    }

    // Proof dependencies (confirmed): process_empty_lists_wlocked.
    #[verifier::opaque]
    pub open spec fn process_thread_wf(process_map: ProcessLockedMap,
            thread_map: ThreadLockedMap) -> bool {
        &&&
        process_empty_lists_wlocked(process_map)
        &&&
        forall|p_ptr:RwLockProcessPtr, t_ptr:RwLockThreadPtr|
            #![trigger process_map.spec_index(p_ptr), thread_map.spec_index(t_ptr)]
            #![trigger process_map.spec_index(p_ptr).view().owned_threads.view().contains(t_ptr)]
            process_map.dom().contains(p_ptr) && process_map.spec_index(p_ptr).view().owned_threads.view().contains(t_ptr) ==>
            thread_map.dom().contains(t_ptr) && thread_map.spec_index(t_ptr).view().owning_proc == p_ptr
            && thread_map.spec_index(t_ptr).view().owning_container == process_map.spec_index(p_ptr).view_rodata().view().owning_container
            && thread_map.spec_index(t_ptr).view().container_depth == process_map.spec_index(p_ptr).view_rodata().view().container_depth
            && thread_map.spec_index(t_ptr).view().process_depth == process_map.spec_index(p_ptr).view_rodata().view().depth
            && thread_map.spec_index(t_ptr).view().proc_pagetable_ptr == process_map.spec_index(p_ptr).view().pagetable
            && process_map.spec_index(p_ptr).view().owned_threads.map().dom().contains(thread_map.spec_index(t_ptr).view().proc_linkedlist_node.addr())
            && process_map.spec_index(p_ptr).view().owned_threads.map().spec_index(thread_map.spec_index(t_ptr).view().proc_linkedlist_node.addr()) == t_ptr
        &&&
        forall|t_ptr:RwLockThreadPtr|
            #![trigger
                thread_map.dom().contains(t_ptr),
                thread_map.spec_index(t_ptr).view().owning_proc
            ]
            thread_map.dom().contains(t_ptr) ==>
            process_map.dom().contains(thread_map.spec_index(t_ptr).view().owning_proc) && !process_map.spec_index(thread_map.spec_index(t_ptr).view().owning_proc).view().zombie
            && process_map.spec_index(thread_map.spec_index(t_ptr).view().owning_proc).view().owned_threads.view().contains(t_ptr)
    }

    pub proof fn process_thread_wf_at(process_map: ProcessLockedMap, thread_map: ThreadLockedMap, thread_ptr: RwLockThreadPtr)
        requires
            process_thread_wf(process_map, thread_map),
            thread_map.dom().contains(thread_ptr),
        ensures
            ({
                let thread = thread_map.spec_index(thread_ptr).view();
                let process = process_map.spec_index(thread.owning_proc);
                &&& process_map.dom().contains(thread.owning_proc)
                &&& !process.view().zombie
                &&& process.view().owned_threads.view().contains(thread_ptr)
                &&& thread.owning_container == process.view_rodata().view().owning_container
                &&& thread.container_depth == process.view_rodata().view().container_depth
                &&& thread.process_depth == process.view_rodata().view().depth
                &&& thread.proc_pagetable_ptr == process.view().pagetable
                &&& process.view().owned_threads.map().dom().contains(thread.proc_linkedlist_node.addr())
                &&& process.view().owned_threads.map().spec_index(thread.proc_linkedlist_node.addr()) == thread_ptr
            }),
    {
        reveal(process_thread_wf);
    }
}
