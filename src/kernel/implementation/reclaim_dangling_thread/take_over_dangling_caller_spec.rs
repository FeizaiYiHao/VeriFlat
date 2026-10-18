use vstd::prelude::*;
use crate::*;

verus! {
/// The thread `thread_ptr` drops its caller link to the dangling thread `dangling_ptr` of its killed caller, and the dangling thread
/// becomes killed and drops its callee link.
#[verifier::opaque]
pub open spec fn take_over_dangling_caller_eof_transition_framing(pre: KernelK, post: KernelK, thread_ptr: RwLockThreadPtr, dangling_ptr: RwLockThreadPtr) -> bool {
    &&& post == (KernelK { thr_mp: post.thr_mp, ..pre })
    &&& post.thr_mp.dom() == pre.thr_mp.dom()
    &&& forall|key: RwLockThreadPtr| #![trigger pre.thr_mp.spec_index(key)] #![trigger post.thr_mp.spec_index(key)]
        #![trigger pre.thr_mp.spec_index(key).view().temp_alloc_cache_2m] #![trigger post.thr_mp.spec_index(key).view().temp_alloc_cache_2m]
        #![trigger pre.thr_mp.spec_index(key).view().temp_alloc_cache_1g] #![trigger post.thr_mp.spec_index(key).view().temp_alloc_cache_1g]
        pre.thr_mp.dom().contains(key) ==> {
            let before = pre.thr_mp.spec_index(key);
            let after = post.thr_mp.spec_index(key);
            &&& after.view().temp_alloc_cache_2m == before.view().temp_alloc_cache_2m
            &&& after.view().temp_alloc_cache_1g == before.view().temp_alloc_cache_1g
            &&& !(key == thread_ptr || key == dangling_ptr) ==> after == before
        }
    &&& {
        let before = pre.thr_mp.spec_index(thread_ptr);
        let after = post.thr_mp.spec_index(thread_ptr);
        &&& after.is_init() == before.is_init()
        &&& after.view_rodata() == before.view_rodata()
        &&& after.view_ghost() == before.view_ghost()
        &&& after.being_killed() == before.being_killed()
        &&& after.killer_info() == before.killer_info()
        &&& after.locking_thread() == before.locking_thread()
        &&& after.view() == (Thread { caller: None, ..before.view() })
    }
    &&& {
        let before = pre.thr_mp.spec_index(dangling_ptr);
        let after = post.thr_mp.spec_index(dangling_ptr);
        &&& after.is_init() == before.is_init()
        &&& after.view_rodata() == before.view_rodata()
        &&& after.view_ghost() == before.view_ghost()
        &&& after.being_killed() == before.being_killed()
        &&& after.killer_info() == before.killer_info()
        &&& after.locking_thread() == before.locking_thread()
        &&& after.view() == (Thread { state: ThreadState::KILLED, callee: None, ..before.view() })
    }
}
} // verus!
