use super::*;
use vstd::prelude::*;
use crate::*;

verus! {
impl<T, const MAJOR: LockMajorId> LinkedList<T, MAJOR> {
    /// EOF closure of `remove_helper`: membership, list, endpoint, map, and uniqueness leaves.
    pub(super) proof fn remove_helper_eof_lists(pre: Self, post: Self, addr: usize, idx: int, prev: usize, next: usize)
        requires
            pre.wf(),
            pre.dom().contains(addr),
            0 < idx,
            idx + 1 < pre.length,
            pre.addr_list.view().len() == pre.length,
            pre.value_list.view().len() == pre.length,
            pre.addr_list.view().spec_index(idx) == addr,
            prev == pre.addr_list.view().spec_index(idx - 1),
            next == pre.addr_list.view().spec_index(idx + 1),
            prev != addr && next != addr && prev != next,
            pre.perms.view().dom().contains(prev) && pre.perms.view().dom().contains(next),
            post == (Self { perms: post.perms, addr_list: post.addr_list, value_list: post.value_list, map: post.map, length: post.length, ..pre }),
            post.length == pre.length - 1,
            post.addr_list.view() == pre.addr_list.view().subrange(0, idx).add(pre.addr_list.view().subrange(idx + 1, pre.length as int)),
            post.value_list.view() == pre.value_list.view().subrange(0, idx).add(pre.value_list.view().subrange(idx + 1, pre.length as int)),
            post.map.view() == pre.map.view().remove(addr),
            post.perms.view() =~= pre.perms.view().remove(addr).insert(prev, post.perms.view().spec_index(prev)).insert(next, post.perms.view().spec_index(next)),
            post.perms.view().spec_index(prev).is_init() && post.perms.view().spec_index(prev).addr() == prev,
            post.perms.view().spec_index(prev).value().view() == pre.perms.view().spec_index(prev).value().view(),
            post.perms.view().spec_index(prev).value().prev == pre.perms.view().spec_index(prev).value().prev,
            post.perms.view().spec_index(prev).value().next == Some(next),
            post.perms.view().spec_index(next).is_init() && post.perms.view().spec_index(next).addr() == next,
            post.perms.view().spec_index(next).value().view() == pre.perms.view().spec_index(next).value().view(),
            post.perms.view().spec_index(next).value().prev == Some(prev),
            post.perms.view().spec_index(next).value().next == pre.perms.view().spec_index(next).value().next,
        ensures
            post.wf_perms(), post.wf_addr_list(), post.wf_value_list(), post.wf_head(), post.wf_tail(), post.wf_map(), post.value_list_unique(),
    {
        assert(post.wf_perms()) by { seq_remove_lemma::<usize>(); reveal(LinkedList::wf_perms); reveal(LinkedList::wf_addr_list); };
        assert(post.wf_addr_list()) by { reveal(LinkedList::wf_addr_list); };
        assert(post.wf_value_list()) by { reveal(LinkedList::wf_addr_list); reveal(LinkedList::wf_value_list); };
        assert(post.wf_head()) by { reveal(LinkedList::wf_addr_list); reveal(LinkedList::wf_head); };
        assert(post.wf_tail()) by { reveal(LinkedList::wf_addr_list); reveal(LinkedList::wf_tail); };
        assert(post.map().dom() =~= post.perms.view().dom()) by { reveal(LinkedList::wf_map); };
        assert(post.wf_map()) by { reveal(LinkedList::wf_map); };
        assert(post.value_list_unique()) by { reveal(LinkedList::value_list_unique); pre.value_list.view().remove_ensures(idx); };
    }

    /// EOF closure of `remove_helper`: backward links.
    pub(super) proof fn remove_helper_eof_prev(pre: Self, post: Self, addr: usize, idx: int, prev: usize, next: usize)
        requires
            pre.wf(),
            pre.dom().contains(addr),
            0 < idx,
            idx + 1 < pre.length,
            pre.addr_list.view().spec_index(idx) == addr,
            prev == pre.addr_list.view().spec_index(idx - 1),
            next == pre.addr_list.view().spec_index(idx + 1),
            post == (Self { perms: post.perms, addr_list: post.addr_list, value_list: post.value_list, map: post.map, length: post.length, ..pre }),
            post.length == pre.length - 1,
            post.addr_list.view() == pre.addr_list.view().subrange(0, idx).add(pre.addr_list.view().subrange(idx + 1, pre.length as int)),
            post.value_list.view() == pre.value_list.view().subrange(0, idx).add(pre.value_list.view().subrange(idx + 1, pre.length as int)),
            post.map.view() == pre.map.view().remove(addr),
            post.perms.view() =~= pre.perms.view().remove(addr).insert(prev, post.perms.view().spec_index(prev)).insert(next, post.perms.view().spec_index(next)),
            post.perms.view().spec_index(prev).is_init() && post.perms.view().spec_index(prev).addr() == prev,
            post.perms.view().spec_index(prev).value().view() == pre.perms.view().spec_index(prev).value().view(),
            post.perms.view().spec_index(prev).value().prev == pre.perms.view().spec_index(prev).value().prev,
            post.perms.view().spec_index(prev).value().next == Some(next),
            post.perms.view().spec_index(next).is_init() && post.perms.view().spec_index(next).addr() == next,
            post.perms.view().spec_index(next).value().view() == pre.perms.view().spec_index(next).value().view(),
            post.perms.view().spec_index(next).value().prev == Some(prev),
            post.perms.view().spec_index(next).value().next == pre.perms.view().spec_index(next).value().next,
        ensures
            post.wf_prev(),
    {
        assert(post.wf_prev()) by { reveal(LinkedList::wf_addr_list); reveal(LinkedList::wf_prev); };
    }

    /// EOF closure of `remove_helper`: forward links.
    pub(super) proof fn remove_helper_eof_next(pre: Self, post: Self, addr: usize, idx: int, prev: usize, next: usize)
        requires
            pre.wf(),
            pre.dom().contains(addr),
            0 < idx,
            idx + 1 < pre.length,
            pre.addr_list.view().spec_index(idx) == addr,
            prev == pre.addr_list.view().spec_index(idx - 1),
            next == pre.addr_list.view().spec_index(idx + 1),
            post == (Self { perms: post.perms, addr_list: post.addr_list, value_list: post.value_list, map: post.map, length: post.length, ..pre }),
            post.length == pre.length - 1,
            post.addr_list.view() == pre.addr_list.view().subrange(0, idx).add(pre.addr_list.view().subrange(idx + 1, pre.length as int)),
            post.value_list.view() == pre.value_list.view().subrange(0, idx).add(pre.value_list.view().subrange(idx + 1, pre.length as int)),
            post.map.view() == pre.map.view().remove(addr),
            post.perms.view() =~= pre.perms.view().remove(addr).insert(prev, post.perms.view().spec_index(prev)).insert(next, post.perms.view().spec_index(next)),
            post.perms.view().spec_index(prev).is_init() && post.perms.view().spec_index(prev).addr() == prev,
            post.perms.view().spec_index(prev).value().view() == pre.perms.view().spec_index(prev).value().view(),
            post.perms.view().spec_index(prev).value().prev == pre.perms.view().spec_index(prev).value().prev,
            post.perms.view().spec_index(prev).value().next == Some(next),
            post.perms.view().spec_index(next).is_init() && post.perms.view().spec_index(next).addr() == next,
            post.perms.view().spec_index(next).value().view() == pre.perms.view().spec_index(next).value().view(),
            post.perms.view().spec_index(next).value().prev == Some(prev),
            post.perms.view().spec_index(next).value().next == pre.perms.view().spec_index(next).value().next,
        ensures
            post.wf_next(),
    {
        assert(post.wf_next()) by { reveal(LinkedList::wf_addr_list); reveal(LinkedList::wf_next); };
    }
}
} // verus!
