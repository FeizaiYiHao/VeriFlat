use vstd::prelude::*;
use crate::*;

verus! {
/// Every dangling thread that no killer holds records the live thread of its own container at the end of its call chain, which
/// still owes the chain a reply and sits deeper in the call chain. A waiting dangling thread shares its end with a waiting
/// dangling callee and is the caller of its end otherwise; a dangling thread taken over for reclamation is write-held together
/// with its end by the same thread. A dangling thread its killer holds has no caller.
#[verifier::opaque]
pub open spec fn thread_dangling_chain_end_wf(thread_map: ThreadLockedMap) -> bool {
    &&& forall|t: RwLockThreadPtr| #![trigger thread_map.spec_index(t).view().caller]
        thread_map.dom().contains(t) && thread_is_dangling(thread_map.spec_index(t)) && thread_map.spec_index(t).being_killed() ==> thread_map.spec_index(t).view().caller is None
    &&& forall|t: RwLockThreadPtr| #![trigger thread_map.spec_index(t).view_ghost()]
        thread_map.dom().contains(t) && thread_is_dangling(thread_map.spec_index(t)) && !thread_map.spec_index(t).being_killed() ==> {
            let thread = thread_map.spec_index(t);
            let end = thread_map.spec_index(thread.view_ghost().chain_end.unwrap());
            &&& thread.view_ghost().chain_end is Some
            &&& thread_map.dom().contains(thread.view_ghost().chain_end.unwrap())
            &&& !thread_is_dangling(end)
            &&& end.view().owning_container == thread.view().owning_container
            &&& thread.view().call_depth.view() < end.view().call_depth.view()
            &&& thread.view().callee is Some ==> {
                let callee = thread_map.spec_index(thread.view().callee.unwrap());
                &&& thread_map.dom().contains(thread.view().callee.unwrap())
                &&& thread_is_dangling(callee) && !callee.being_killed() ==> callee.view_ghost().chain_end == thread.view_ghost().chain_end
                &&& !(thread_is_dangling(callee) && !callee.being_killed()) ==> thread.view().callee == thread.view_ghost().chain_end
            }
            &&& thread.view().callee is None ==> {
                &&& thread.locking_thread() is Write
                &&& end.locking_thread() is Write
                &&& thread.locking_thread()->Write_thread_id == end.locking_thread()->Write_thread_id
            }
        }
}

/// The chain end of dangling thread `t`, which no killer holds, is a live thread of `t`'s container.
pub proof fn thread_dangling_chain_end_wf_at(thread_map: ThreadLockedMap, t: RwLockThreadPtr)
    requires
        thread_dangling_chain_end_wf(thread_map),
        thread_map.dom().contains(t),
        thread_is_dangling(thread_map.spec_index(t)),
        !thread_map.spec_index(t).being_killed(),
    ensures
        ({
            let thread = thread_map.spec_index(t);
            let end = thread_map.spec_index(thread.view_ghost().chain_end.unwrap());
            &&& thread.view_ghost().chain_end is Some
            &&& thread_map.dom().contains(thread.view_ghost().chain_end.unwrap())
            &&& !thread_is_dangling(end)
            &&& end.view().owning_container == thread.view().owning_container
            &&& thread.view().call_depth.view() < end.view().call_depth.view()
            &&& thread.view().callee is Some ==> {
                let callee = thread_map.spec_index(thread.view().callee.unwrap());
                &&& thread_map.dom().contains(thread.view().callee.unwrap())
                &&& thread_is_dangling(callee) && !callee.being_killed() ==> callee.view_ghost().chain_end == thread.view_ghost().chain_end
                &&& !(thread_is_dangling(callee) && !callee.being_killed()) ==> thread.view().callee == thread.view_ghost().chain_end
            }
            &&& thread.view().callee is None ==> {
                &&& thread.locking_thread() is Write
                &&& end.locking_thread() is Write
                &&& thread.locking_thread()->Write_thread_id == end.locking_thread()->Write_thread_id
            }
        }),
{ reveal(thread_dangling_chain_end_wf); }

/// A dangling thread `t` its killer holds has no caller.
pub proof fn thread_dangling_chain_end_wf_killed_at(thread_map: ThreadLockedMap, t: RwLockThreadPtr)
    requires
        thread_dangling_chain_end_wf(thread_map),
        thread_map.dom().contains(t),
        thread_is_dangling(thread_map.spec_index(t)),
        thread_map.spec_index(t).being_killed(),
    ensures
        thread_map.spec_index(t).view().caller is None,
{ reveal(thread_dangling_chain_end_wf); }

/// Every dangling thread that no killer holds, whose chain ends at `x` at most `gap` call levels below `x`, lies on `x`'s caller
/// chain: it is in every set `chain` that holds `x`'s dangling caller and the dangling caller of each of its members, unless a
/// dangling thread taken over for reclamation is write-held by the thread that write-holds `x`.
pub proof fn thread_dangling_chain_end_on_caller_chain(thread_map: ThreadLockedMap, x: RwLockThreadPtr, chain: Set<RwLockThreadPtr>, gap: nat)
    requires
        thread_dangling_chain_end_wf(thread_map),
        thread_caller_callee_wf(thread_map),
        thread_map.dom().contains(x),
        thread_map.spec_index(x).view().caller is Some && thread_is_dangling(thread_map.spec_index(thread_map.spec_index(x).view().caller.unwrap()))
            ==> chain.contains(thread_map.spec_index(x).view().caller.unwrap()),
        forall|v: RwLockThreadPtr| #![trigger chain.contains(v)]
            chain.contains(v) && thread_map.dom().contains(v) && thread_map.spec_index(v).view().caller is Some
                && thread_is_dangling(thread_map.spec_index(thread_map.spec_index(v).view().caller.unwrap())) ==> chain.contains(thread_map.spec_index(v).view().caller.unwrap()),
        forall|u: RwLockThreadPtr| #![trigger thread_map.spec_index(u).locking_thread()]
            thread_map.dom().contains(u) && thread_is_dangling(thread_map.spec_index(u)) && !thread_map.spec_index(u).being_killed() && thread_map.spec_index(u).view().callee is None
                && thread_map.spec_index(x).locking_thread() is Write && thread_map.spec_index(u).locking_thread() is Write
                ==> thread_map.spec_index(u).locking_thread()->Write_thread_id != thread_map.spec_index(x).locking_thread()->Write_thread_id,
    ensures
        forall|t: RwLockThreadPtr| #![trigger thread_map.spec_index(t).view_ghost()]
            thread_map.dom().contains(t) && thread_is_dangling(thread_map.spec_index(t)) && !thread_map.spec_index(t).being_killed()
                && thread_map.spec_index(t).view_ghost().chain_end == Some(x)
                && thread_map.spec_index(x).view().call_depth.view() <= thread_map.spec_index(t).view().call_depth.view() + gap ==> chain.contains(t),
    decreases gap,
{
    reveal(thread_dangling_chain_end_wf); reveal(thread_caller_callee_wf);
    if gap > 0 { thread_dangling_chain_end_on_caller_chain(thread_map, x, chain, (gap - 1) as nat); }
}

/// Record `end` as the chain end of `cur` and of each dangling caller above it, keeping every lock holder, and return the threads
/// updated: `cur` and its dangling callers, each of them in `cur`'s container, the caller of an updated thread, and below `cur`'s
/// call depth.
pub proof fn thread_map_set_chain_end_up_dangling_callers(tracked thread_map: &mut ThreadLockedMap, cur: RwLockThreadPtr, end: RwLockThreadPtr)
    -> (chain: Set<RwLockThreadPtr>)
    requires
        old(thread_map).perms_wf(),
        thread_caller_callee_wf(*old(thread_map)),
        old(thread_map).dom().contains(cur),
    ensures
        final(thread_map).perms_wf(),
        final(thread_map).dom() == old(thread_map).dom(),
        chain.contains(cur),
        forall|t: RwLockThreadPtr| #![trigger final(thread_map).spec_index(t)]
            old(thread_map).dom().contains(t) && !chain.contains(t) ==> final(thread_map).spec_index(t) == old(thread_map).spec_index(t),
        forall|t: RwLockThreadPtr| #![trigger final(thread_map).spec_index(t)]
            chain.contains(t) ==> update_ghost_ensures(old(thread_map).spec_index(t), final(thread_map).spec_index(t), ThreadGhost { chain_end: Some(end), ..old(thread_map).spec_index(t).view_ghost() }),
        forall|t: RwLockThreadPtr, thread_id: LockThreadId| #![trigger final(thread_map).spec_index(t).locked_by_thread(thread_id)]
            old(thread_map).dom().contains(t) ==> final(thread_map).spec_index(t).locked_by_thread(thread_id) == old(thread_map).spec_index(t).locked_by_thread(thread_id),
        forall|t: RwLockThreadPtr, thread_id: LockThreadId| #![trigger final(thread_map).spec_index(t).rlocked_by_thread(thread_id)]
            old(thread_map).dom().contains(t) ==> final(thread_map).spec_index(t).rlocked_by_thread(thread_id) == old(thread_map).spec_index(t).rlocked_by_thread(thread_id),
        forall|t: RwLockThreadPtr, thread_id: LockThreadId| #![trigger final(thread_map).spec_index(t).wlocked_by_thread(thread_id)]
            old(thread_map).dom().contains(t) ==> final(thread_map).spec_index(t).wlocked_by_thread(thread_id) == old(thread_map).spec_index(t).wlocked_by_thread(thread_id),
        forall|t: RwLockThreadPtr| #![trigger final(thread_map).lock_id_by_key(t)]
            old(thread_map).dom().contains(t) ==> final(thread_map).lock_id_by_key(t) == old(thread_map).lock_id_by_key(t),
        forall|v: RwLockThreadPtr| #![trigger chain.contains(v)]
            chain.contains(v) ==> {
                let thread = old(thread_map).spec_index(v).view();
                &&& old(thread_map).dom().contains(v)
                &&& thread.owning_container == old(thread_map).spec_index(cur).view().owning_container
                &&& thread.caller is Some && thread_is_dangling(old(thread_map).spec_index(thread.caller.unwrap())) ==> chain.contains(thread.caller.unwrap())
                &&& v != cur ==> {
                    &&& thread_is_dangling(old(thread_map).spec_index(v))
                    &&& thread.callee is Some
                    &&& chain.contains(thread.callee.unwrap())
                    &&& thread.call_depth.view() < old(thread_map).spec_index(cur).view().call_depth.view()
                }
            },
    decreases old(thread_map).spec_index(cur).view().call_depth.view(),
{
    let ghost pre = *thread_map;
    thread_caller_callee_wf_at(pre, cur);
    thread_map.update_ghost(cur, ThreadGhost { chain_end: Some(end), ..pre.spec_index(cur).view_ghost() });
    let caller = pre.spec_index(cur).view().caller;
    if caller is Some && thread_is_dangling(pre.spec_index(caller.unwrap())) {
        thread_caller_callee_wf_preserved_for_call_link_eq(pre, *thread_map); reveal(thread_caller_callee_wf);
        let rest = thread_map_set_chain_end_up_dangling_callers(thread_map, caller.unwrap(), end);
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
