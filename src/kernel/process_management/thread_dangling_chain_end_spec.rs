use vstd::prelude::*;
use crate::*;

verus! {
/// A dangling thread names the end of its call chain: the live thread of its own container that still owes the chain a reply.
#[verifier::opaque]
pub open spec fn thread_dangling_chain_end_wf(thrd_mp: ThreadLockedMap) -> bool {
    // A dangling thread its killer holds has no caller.
    &&& forall|t: RwLockThreadPtr|
        #![trigger thrd_mp.spec_index(t).view().caller]
        thrd_mp.dom().contains(t)
            && thread_is_dangling(thrd_mp.spec_index(t))
            && thrd_mp.spec_index(t).being_killed()
            ==> thrd_mp.spec_index(t).view().caller is None
    // Any other dangling thread has a live chain end in its container, deeper in the call chain.
    &&& forall|t: RwLockThreadPtr|
        #![trigger thrd_mp.spec_index(t).view_ghost()]
        thrd_mp.dom().contains(t)
            && thread_is_dangling(thrd_mp.spec_index(t))
            && !thrd_mp.spec_index(t).being_killed()
            ==> {
                let thread = thrd_mp.spec_index(t);
                let end_ptr = thread.view_ghost().chain_end.unwrap();
                let end = thrd_mp.spec_index(end_ptr);
                &&& thread.view_ghost().chain_end is Some
                &&& thrd_mp.dom().contains(end_ptr)
                &&& !thread_is_dangling(end)
                &&& end.view().owning_container == thread.view().owning_container
                &&& thread.view().call_depth.view() < end.view().call_depth.view()
                // a dangling callee that no killer holds shares the end; otherwise the callee is the end
                &&& thread.view().callee is Some ==> {
                    let callee = thrd_mp.spec_index(thread.view().callee.unwrap());
                    let callee_dangling = thread_is_dangling(callee) && !callee.being_killed();
                    &&& thrd_mp.dom().contains(thread.view().callee.unwrap())
                    &&& callee_dangling ==> callee.view_ghost().chain_end == thread.view_ghost().chain_end
                    &&& !callee_dangling ==> thread.view().callee == thread.view_ghost().chain_end
                }
                // taken over for reclamation: it and its end are write-held by one thread
                &&& thread.view().callee is None ==> {
                    &&& thread.locking_thread() is Write
                    &&& end.locking_thread() is Write
                    &&& thread.locking_thread()->Write_thread_id == end.locking_thread()->Write_thread_id
                }
            }
}

/// The chain end of dangling thread `thrd_ptr`, which no killer holds, is a live thread of `thrd_ptr`'s container.
pub proof fn thread_dangling_chain_end_wf_at(thrd_mp: ThreadLockedMap, thrd_ptr: RwLockThreadPtr)
    requires
        thread_dangling_chain_end_wf(thrd_mp),
        thrd_mp.dom().contains(thrd_ptr),
        thread_is_dangling(thrd_mp.spec_index(thrd_ptr)),
        !thrd_mp.spec_index(thrd_ptr).being_killed(),
    ensures
        ({
            let thread = thrd_mp.spec_index(thrd_ptr);
            let end_ptr = thread.view_ghost().chain_end.unwrap();
            let end = thrd_mp.spec_index(end_ptr);
            &&& thread.view_ghost().chain_end is Some
            &&& thrd_mp.dom().contains(end_ptr)
            &&& !thread_is_dangling(end)
            &&& end.view().owning_container == thread.view().owning_container
            &&& thread.view().call_depth.view() < end.view().call_depth.view()
            &&& thread.view().callee is Some ==> {
                let callee = thrd_mp.spec_index(thread.view().callee.unwrap());
                let callee_dangling = thread_is_dangling(callee) && !callee.being_killed();
                &&& thrd_mp.dom().contains(thread.view().callee.unwrap())
                &&& callee_dangling ==> callee.view_ghost().chain_end == thread.view_ghost().chain_end
                &&& !callee_dangling ==> thread.view().callee == thread.view_ghost().chain_end
            }
            &&& thread.view().callee is None ==> {
                &&& thread.locking_thread() is Write
                &&& end.locking_thread() is Write
                &&& thread.locking_thread()->Write_thread_id == end.locking_thread()->Write_thread_id
            }
        }),
{ reveal(thread_dangling_chain_end_wf); }

/// A dangling thread `thrd_ptr` its killer holds has no caller.
pub proof fn thread_dangling_chain_end_wf_killed_at(thrd_mp: ThreadLockedMap, thrd_ptr: RwLockThreadPtr)
    requires
        thread_dangling_chain_end_wf(thrd_mp),
        thrd_mp.dom().contains(thrd_ptr),
        thread_is_dangling(thrd_mp.spec_index(thrd_ptr)),
        thrd_mp.spec_index(thrd_ptr).being_killed(),
    ensures
        thrd_mp.spec_index(thrd_ptr).view().caller is None,
{ reveal(thread_dangling_chain_end_wf); }

/// Every dangling thread that no killer holds, whose chain ends at `x` at most `gap` call levels below `x`, lies on `x`'s caller
/// chain: it is in every set `chain` that holds `x`'s dangling caller and the dangling caller of each of its members, unless a
/// dangling thread taken over for reclamation is write-held by the thread that write-holds `x`.
pub proof fn thread_dangling_chain_end_on_caller_chain(thrd_mp: ThreadLockedMap, x: RwLockThreadPtr, chain: Set<RwLockThreadPtr>, gap: nat)
    requires
        thread_dangling_chain_end_wf(thrd_mp),
        thread_caller_callee_wf(thrd_mp),
        thrd_mp.dom().contains(x),
        thrd_mp.spec_index(x).view().caller is Some && thread_is_dangling(thrd_mp.spec_index(thrd_mp.spec_index(x).view().caller.unwrap()))
            ==> chain.contains(thrd_mp.spec_index(x).view().caller.unwrap()),
        forall|v: RwLockThreadPtr| #![trigger chain.contains(v)]
            chain.contains(v) && thrd_mp.dom().contains(v) && thrd_mp.spec_index(v).view().caller is Some
                && thread_is_dangling(thrd_mp.spec_index(thrd_mp.spec_index(v).view().caller.unwrap())) ==> chain.contains(thrd_mp.spec_index(v).view().caller.unwrap()),
        forall|u: RwLockThreadPtr| #![trigger thrd_mp.spec_index(u).locking_thread()]
            thrd_mp.dom().contains(u) && thread_is_dangling(thrd_mp.spec_index(u)) && !thrd_mp.spec_index(u).being_killed() && thrd_mp.spec_index(u).view().callee is None
                && thrd_mp.spec_index(x).locking_thread() is Write && thrd_mp.spec_index(u).locking_thread() is Write
                ==> thrd_mp.spec_index(u).locking_thread()->Write_thread_id != thrd_mp.spec_index(x).locking_thread()->Write_thread_id,
    ensures
        forall|t: RwLockThreadPtr| #![trigger thrd_mp.spec_index(t).view_ghost()]
            thrd_mp.dom().contains(t) && thread_is_dangling(thrd_mp.spec_index(t)) && !thrd_mp.spec_index(t).being_killed()
                && thrd_mp.spec_index(t).view_ghost().chain_end == Some(x)
                && thrd_mp.spec_index(x).view().call_depth.view() <= thrd_mp.spec_index(t).view().call_depth.view() + gap ==> chain.contains(t),
    decreases gap,
{
    reveal(thread_dangling_chain_end_wf); reveal(thread_caller_callee_wf);
    if gap > 0 { thread_dangling_chain_end_on_caller_chain(thrd_mp, x, chain, (gap - 1) as nat); }
}

/// Set `end` as the chain end of `cur` and of each dangling caller above it, keeping every lock holder, and return the threads
/// updated: `cur` and its dangling callers, each of them in `cur`'s container, the caller of an updated thread, and below `cur`'s
/// call depth.
pub proof fn thread_map_set_chain_end_along_dangling_caller_chain(tracked thrd_mp: &mut ThreadLockedMap, cur: RwLockThreadPtr, end: RwLockThreadPtr) -> (chain: Set<RwLockThreadPtr>)
    requires
        old(thrd_mp).perms_wf(),
        thread_caller_callee_wf(*old(thrd_mp)),
        old(thrd_mp).dom().contains(cur),
    ensures
        final(thrd_mp).perms_wf(),
        final(thrd_mp).dom() == old(thrd_mp).dom(),
        chain.contains(cur),
        forall|t: RwLockThreadPtr| #![trigger final(thrd_mp).spec_index(t)]
            old(thrd_mp).dom().contains(t) && !chain.contains(t) ==> final(thrd_mp).spec_index(t) == old(thrd_mp).spec_index(t),
        forall|t: RwLockThreadPtr| #![trigger final(thrd_mp).spec_index(t)]
            chain.contains(t) ==> update_ghost_ensures(old(thrd_mp).spec_index(t), final(thrd_mp).spec_index(t), ThreadGhost { chain_end: Some(end), ..old(thrd_mp).spec_index(t).view_ghost() }),
        forall|t: RwLockThreadPtr, thread_id: LockThreadId| #![trigger final(thrd_mp).spec_index(t).locked_by_thread(thread_id)]
            old(thrd_mp).dom().contains(t) ==> final(thrd_mp).spec_index(t).locked_by_thread(thread_id) == old(thrd_mp).spec_index(t).locked_by_thread(thread_id),
        forall|t: RwLockThreadPtr, thread_id: LockThreadId| #![trigger final(thrd_mp).spec_index(t).rlocked_by_thread(thread_id)]
            old(thrd_mp).dom().contains(t) ==> final(thrd_mp).spec_index(t).rlocked_by_thread(thread_id) == old(thrd_mp).spec_index(t).rlocked_by_thread(thread_id),
        forall|t: RwLockThreadPtr, thread_id: LockThreadId| #![trigger final(thrd_mp).spec_index(t).wlocked_by_thread(thread_id)]
            old(thrd_mp).dom().contains(t) ==> final(thrd_mp).spec_index(t).wlocked_by_thread(thread_id) == old(thrd_mp).spec_index(t).wlocked_by_thread(thread_id),
        forall|t: RwLockThreadPtr| #![trigger final(thrd_mp).lock_id_by_key(t)]
            old(thrd_mp).dom().contains(t) ==> final(thrd_mp).lock_id_by_key(t) == old(thrd_mp).lock_id_by_key(t),
        forall|v: RwLockThreadPtr| #![trigger chain.contains(v)]
            chain.contains(v) ==> {
                let thread = old(thrd_mp).spec_index(v).view();
                &&& old(thrd_mp).dom().contains(v)
                &&& thread.owning_container == old(thrd_mp).spec_index(cur).view().owning_container
                &&& thread.caller is Some && thread_is_dangling(old(thrd_mp).spec_index(thread.caller.unwrap())) ==> chain.contains(thread.caller.unwrap())
                &&& v != cur ==> {
                    &&& thread_is_dangling(old(thrd_mp).spec_index(v))
                    &&& thread.callee is Some
                    &&& chain.contains(thread.callee.unwrap())
                    &&& thread.call_depth.view() < old(thrd_mp).spec_index(cur).view().call_depth.view()
                }
            },
    decreases old(thrd_mp).spec_index(cur).view().call_depth.view(),
{
    let ghost pre = *thrd_mp;
    thread_caller_callee_wf_at(pre, cur);
    thrd_mp.update_ghost(cur, ThreadGhost { chain_end: Some(end), ..pre.spec_index(cur).view_ghost() });
    let caller = pre.spec_index(cur).view().caller;
    if caller is Some && thread_is_dangling(pre.spec_index(caller.unwrap())) {
        thread_caller_callee_wf_preserved_for_call_link_eq(pre, *thrd_mp); reveal(thread_caller_callee_wf);
        let rest = thread_map_set_chain_end_along_dangling_caller_chain(thrd_mp, caller.unwrap(), end);
        rest.insert(cur)
    } else {
        set![cur]
    }
}

/// `thread_dangling_chain_end_wf` survives a step that keeps every old thread with its dangling status, container, call depth,
/// and write holder, every dangling thread with its kill mark, chain end, callee, and caller, and adds only live threads.
pub proof fn thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre: ThreadLockedMap, post: ThreadLockedMap)
    requires
        thread_dangling_chain_end_wf(pre),
        forall|u: RwLockThreadPtr| #![trigger post.spec_index(u)]
            pre.dom().contains(u) ==> {
                &&& post.dom().contains(u)
                &&& thread_is_dangling(post.spec_index(u)) == thread_is_dangling(pre.spec_index(u))
                &&& post.spec_index(u).view().owning_container == pre.spec_index(u).view().owning_container
                &&& post.spec_index(u).view().call_depth == pre.spec_index(u).view().call_depth
                &&& thread_is_dangling(pre.spec_index(u)) ==> {
                    &&& post.spec_index(u).being_killed() == pre.spec_index(u).being_killed()
                    &&& post.spec_index(u).view_ghost() == pre.spec_index(u).view_ghost()
                    &&& post.spec_index(u).view().callee == pre.spec_index(u).view().callee
                    &&& post.spec_index(u).view().caller == pre.spec_index(u).view().caller
                }
                &&& pre.spec_index(u).locking_thread() is Write ==> post.spec_index(u).locking_thread() is Write
                    && post.spec_index(u).locking_thread()->Write_thread_id == pre.spec_index(u).locking_thread()->Write_thread_id
            },
        forall|u: RwLockThreadPtr| #![trigger post.spec_index(u)] post.dom().contains(u) && !pre.dom().contains(u) ==> !thread_is_dangling(post.spec_index(u)),
    ensures
        thread_dangling_chain_end_wf(post),
{ reveal(thread_dangling_chain_end_wf); }
} // verus!
