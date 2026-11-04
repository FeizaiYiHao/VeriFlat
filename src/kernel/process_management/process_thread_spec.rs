use vstd::prelude::*;
use crate::*;

verus! {
/// Process owned_threads and thread owning_proc agree for every thread that is not dangling, and a thread being killed is
/// write-held together with its process by the same killer.
#[verifier::opaque]
pub open spec fn process_thread_wf(prc_mp: ProcessLockedMap, thrd_mp: ThreadLockedMap) -> bool {
    // Process -> owned threads.
    &&& forall|p: RwLockProcessPtr, t: RwLockThreadPtr|
        #![trigger prc_mp.spec_index(p).view().owned_threads.view().contains(t)]
        prc_mp.dom().contains(p) && prc_mp.spec_index(p).view().owned_threads.view().contains(t) ==> {
            let thread = thrd_mp.spec_index(t).view();
            let process = prc_mp.spec_index(p);
            &&& thrd_mp.dom().contains(t)
            &&& thread.owning_proc == p
            &&& thread.owning_container == process.view_rodata().view().owning_container
            &&& thread.container_depth == process.view_rodata().view().container_depth
            &&& thread.process_depth == process.view_rodata().view().depth
            &&& thread.proc_pagetable_ptr == process.view().pagetable
            &&& process.view().owned_threads.map().dom().contains(thread.proc_linkedlist_node.addr())
            &&& process.view().owned_threads.map().spec_index(thread.proc_linkedlist_node.addr()) == t
            &&& !thread.proc_linkedlist_node.is_init()
        }
    // A thread that is not dangling is owned by its live process.
    &&& forall|t: RwLockThreadPtr|
        #![trigger thrd_mp.dom().contains(t), thrd_mp.spec_index(t).view().owning_proc]
        thrd_mp.dom().contains(t) && !thread_is_dangling(thrd_mp.spec_index(t)) ==> {
            let prc_ptr = thrd_mp.spec_index(t).view().owning_proc;
            &&& prc_mp.dom().contains(prc_ptr)
            &&& !prc_mp.spec_index(prc_ptr).view().zombie
            &&& prc_mp.spec_index(prc_ptr).view().owned_threads.view().contains(t)
        }
    // A thread being killed is write-held and never waits for a reply; its process, in the thread's container, is being
    // killed and the same killer write-holds both, also after the thread left the process.
    &&& forall|t: RwLockThreadPtr|
        #![trigger thrd_mp.spec_index(t).being_killed()]
        thrd_mp.dom().contains(t) && thrd_mp.spec_index(t).being_killed() ==> {
            let process = prc_mp.spec_index(thrd_mp.spec_index(t).view().owning_proc);
            &&& thrd_mp.spec_index(t).locking_thread() is Write
            &&& !thrd_mp.spec_index(t).view().state.is_reply_waiting()
            &&& prc_mp.dom().contains(thrd_mp.spec_index(t).view().owning_proc)
            &&& process.being_killed()
            &&& process.locking_thread() is Write
            &&& thrd_mp.spec_index(t).locking_thread()->Write_thread_id == process.locking_thread()->Write_thread_id
            &&& thrd_mp.spec_index(t).view().owning_container == process.view_rodata().view().owning_container
        }
}

/// Thread `thrd_ptr` owned by process `prc_ptr` is a live thread of `prc_ptr` that mirrors the process's container, depths, and page table.
pub proof fn process_thread_wf_process_at(prc_mp: ProcessLockedMap, thrd_mp: ThreadLockedMap, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr)
    requires
        process_thread_wf(prc_mp, thrd_mp),
        prc_mp.dom().contains(prc_ptr),
    ensures
        prc_mp.spec_index(prc_ptr).view().owned_threads.view().contains(thrd_ptr) ==> {
            let thread = thrd_mp.spec_index(thrd_ptr).view();
            let process = prc_mp.spec_index(prc_ptr);
            &&& thrd_mp.dom().contains(thrd_ptr)
            &&& thread.owning_proc == prc_ptr
            &&& thread.owning_container == process.view_rodata().view().owning_container
            &&& thread.container_depth == process.view_rodata().view().container_depth
            &&& thread.process_depth == process.view_rodata().view().depth
            &&& thread.proc_pagetable_ptr == process.view().pagetable
            &&& process.view().owned_threads.map().dom().contains(thread.proc_linkedlist_node.addr())
            &&& process.view().owned_threads.map().spec_index(thread.proc_linkedlist_node.addr()) == thrd_ptr
            &&& !thread.proc_linkedlist_node.is_init()
        },
{ reveal(process_thread_wf); }

/// Every thread owned by process `prc_ptr` is in the thread map.
pub proof fn process_thread_wf_implies_owned_threads_in_map(prc_mp: ProcessLockedMap, thrd_mp: ThreadLockedMap, prc_ptr: RwLockProcessPtr)
    requires
        process_thread_wf(prc_mp, thrd_mp),
        prc_mp.dom().contains(prc_ptr),
    ensures forall|t: RwLockThreadPtr| #[trigger] prc_mp.spec_index(prc_ptr).view().owned_threads.view().contains(t) ==> thrd_mp.dom().contains(t),
{ reveal(process_thread_wf); }

pub proof fn process_thread_wf_thread_at(prc_mp: ProcessLockedMap, thrd_mp: ThreadLockedMap, thrd_ptr: RwLockThreadPtr)
    requires
        process_thread_wf(prc_mp, thrd_mp),
        thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(thrd_mp.spec_index(thrd_ptr)),
    ensures
        ({
            let thread = thrd_mp.spec_index(thrd_ptr).view();
            let process = prc_mp.spec_index(thread.owning_proc);
            &&& prc_mp.dom().contains(thread.owning_proc)
            &&& !process.view().zombie
            &&& process.view().owned_threads.view().contains(thrd_ptr)
            &&& thread.owning_container == process.view_rodata().view().owning_container
            &&& thread.container_depth == process.view_rodata().view().container_depth
            &&& thread.process_depth == process.view_rodata().view().depth
            &&& thread.proc_pagetable_ptr == process.view().pagetable
            &&& process.view().owned_threads.map().dom().contains(thread.proc_linkedlist_node.addr())
            &&& process.view().owned_threads.map().spec_index(thread.proc_linkedlist_node.addr()) == thrd_ptr
        }),
{ reveal(process_thread_wf); }

/// A thread `thrd_ptr` being killed is write-held and not reply-waiting, and its killer also write-holds its process in the thread's
/// container.
pub proof fn process_thread_wf_killed_thread_at(prc_mp: ProcessLockedMap, thrd_mp: ThreadLockedMap, thrd_ptr: RwLockThreadPtr)
    requires
        process_thread_wf(prc_mp, thrd_mp),
        thrd_mp.dom().contains(thrd_ptr),
    ensures
        thrd_mp.spec_index(thrd_ptr).being_killed() ==> {
            let process = prc_mp.spec_index(thrd_mp.spec_index(thrd_ptr).view().owning_proc);
            &&& thrd_mp.spec_index(thrd_ptr).locking_thread() is Write
            &&& !thrd_mp.spec_index(thrd_ptr).view().state.is_reply_waiting()
            &&& prc_mp.dom().contains(thrd_mp.spec_index(thrd_ptr).view().owning_proc)
            &&& process.being_killed()
            &&& process.locking_thread() is Write
            &&& thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_thread_id == process.locking_thread()->Write_thread_id
            &&& thrd_mp.spec_index(thrd_ptr).view().owning_container == process.view_rodata().view().owning_container
        },
{ reveal(process_thread_wf); }
}
