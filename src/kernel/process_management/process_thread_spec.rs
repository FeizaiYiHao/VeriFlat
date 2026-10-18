use vstd::prelude::*;
use crate::*;

verus! {
    #[verifier::opaque]
    pub open spec fn process_thread_wf(process_map: ProcessLockedMap, thread_map: ThreadLockedMap) -> bool {
        &&& forall|p_ptr:RwLockProcessPtr, t_ptr:RwLockThreadPtr|
            #![trigger process_map.spec_index(p_ptr).view().owned_threads.view().contains(t_ptr)]
            process_map.dom().contains(p_ptr) && process_map.spec_index(p_ptr).view().owned_threads.view().contains(t_ptr)
                ==> thread_map.dom().contains(t_ptr) && thread_map.spec_index(t_ptr).view().owning_proc == p_ptr
                && thread_map.spec_index(t_ptr).view().owning_container == process_map.spec_index(p_ptr).view_rodata().view().owning_container
                && thread_map.spec_index(t_ptr).view().container_depth == process_map.spec_index(p_ptr).view_rodata().view().container_depth
                && thread_map.spec_index(t_ptr).view().process_depth == process_map.spec_index(p_ptr).view_rodata().view().depth
                && thread_map.spec_index(t_ptr).view().proc_pagetable_ptr == process_map.spec_index(p_ptr).view().pagetable
                && process_map.spec_index(p_ptr).view().owned_threads.map().dom().contains(thread_map.spec_index(t_ptr).view().proc_linkedlist_node.addr())
                && process_map.spec_index(p_ptr).view().owned_threads.map().spec_index(thread_map.spec_index(t_ptr).view().proc_linkedlist_node.addr()) == t_ptr
                && !thread_map.spec_index(t_ptr).view().proc_linkedlist_node.is_init()
        // A dangling thread has left its process, which may already be gone.
        &&& forall|t_ptr:RwLockThreadPtr|
            #![trigger thread_map.dom().contains(t_ptr), thread_map.spec_index(t_ptr).view().owning_proc]
            thread_map.dom().contains(t_ptr) && !thread_is_dangling(thread_map.spec_index(t_ptr))
                ==> process_map.dom().contains(thread_map.spec_index(t_ptr).view().owning_proc) && !process_map.spec_index(thread_map.spec_index(t_ptr).view().owning_proc).view().zombie
                && process_map.spec_index(thread_map.spec_index(t_ptr).view().owning_proc).view().owned_threads.view().contains(t_ptr)
        // A thread being killed is write-held and never waits for a reply; unless it is already a dangling thread, its process is
        // being killed and the same killer write-holds both.
        &&& forall|t_ptr: RwLockThreadPtr|
            #![trigger thread_map.spec_index(t_ptr).being_killed()]
            thread_map.dom().contains(t_ptr) && thread_map.spec_index(t_ptr).being_killed() ==> {
                let process = process_map.spec_index(thread_map.spec_index(t_ptr).view().owning_proc);
                &&& thread_map.spec_index(t_ptr).locking_thread() is Write
                &&& !thread_map.spec_index(t_ptr).view().state.is_reply_waiting()
                &&& !thread_is_dangling(thread_map.spec_index(t_ptr)) ==> {
                    &&& process.being_killed()
                    &&& process.locking_thread() is Write
                    &&& thread_map.spec_index(t_ptr).locking_thread()->Write_thread_id == process.locking_thread()->Write_thread_id
                }
            }
    }

    /// Thread `t_ptr` owned by process `p_ptr` is a live thread of `p_ptr` that mirrors the process's container, depths, and page table.
    pub proof fn process_thread_wf_process_at(process_map: ProcessLockedMap, thread_map: ThreadLockedMap, p_ptr: RwLockProcessPtr, t_ptr: RwLockThreadPtr)
        requires
            process_thread_wf(process_map, thread_map),
            process_map.dom().contains(p_ptr),
        ensures
            process_map.spec_index(p_ptr).view().owned_threads.view().contains(t_ptr) ==> {
                let thread = thread_map.spec_index(t_ptr).view();
                let process = process_map.spec_index(p_ptr);
                &&& thread_map.dom().contains(t_ptr)
                &&& thread.owning_proc == p_ptr
                &&& thread.owning_container == process.view_rodata().view().owning_container
                &&& thread.container_depth == process.view_rodata().view().container_depth
                &&& thread.process_depth == process.view_rodata().view().depth
                &&& thread.proc_pagetable_ptr == process.view().pagetable
                &&& process.view().owned_threads.map().dom().contains(thread.proc_linkedlist_node.addr())
                &&& process.view().owned_threads.map().spec_index(thread.proc_linkedlist_node.addr()) == t_ptr
                &&& !thread.proc_linkedlist_node.is_init()
            },
    { reveal(process_thread_wf); }

    /// Every thread owned by process `p_ptr` is in the thread map.
    pub proof fn process_thread_wf_owned_threads_dom_at(process_map: ProcessLockedMap, thread_map: ThreadLockedMap, p_ptr: RwLockProcessPtr)
        requires
            process_thread_wf(process_map, thread_map),
            process_map.dom().contains(p_ptr),
        ensures forall|t_ptr: RwLockThreadPtr| #[trigger] process_map.spec_index(p_ptr).view().owned_threads.view().contains(t_ptr) ==> thread_map.dom().contains(t_ptr),
    { reveal(process_thread_wf); }

    pub proof fn process_thread_wf_at(process_map: ProcessLockedMap, thread_map: ThreadLockedMap, thread_ptr: RwLockThreadPtr)
        requires
            process_thread_wf(process_map, thread_map),
            thread_map.dom().contains(thread_ptr),
            !thread_is_dangling(thread_map.spec_index(thread_ptr)),
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
    { reveal(process_thread_wf); }
}
