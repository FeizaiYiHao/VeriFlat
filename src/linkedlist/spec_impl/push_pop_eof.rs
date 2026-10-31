use super::*;
use vstd::prelude::*;
use crate::*;

verus! {
impl<T, const MAJOR: LockMajorId> LinkedList<T, MAJOR> {
    /// EOF closure of `push_head` on a non-empty list: node `addr` became the head, linked in front of `old_head`.
    pub(super) proof fn push_head_eof_wf(pre: Self, post: Self, addr: usize, old_head: usize)
        requires
            pre.wf(),
            pre.length != 0,
            pre.length != usize::MAX,
            pre.head == Some(old_head),
            !pre.dom().contains(addr),
            !pre.view().contains(post.perms.view().spec_index(addr).value().view()),
            post == (Self { perms: post.perms, addr_list: post.addr_list, value_list: post.value_list, length: post.length, head: post.head, map: post.map, ..pre }),
            post.length == pre.length + 1,
            post.head == Some(addr),
            post.addr_list.view() == pre.addr_list.view().insert(0, addr),
            post.value_list.view() == pre.value_list.view().insert(0, post.perms.view().spec_index(addr).value().view()),
            post.map.view() == pre.map.view().insert(addr, post.perms.view().spec_index(addr).value().view()),
            post.perms.view() == pre.perms.view().remove(old_head).insert(old_head, post.perms.view().spec_index(old_head)).insert(addr, post.perms.view().spec_index(addr)),
            post.perms.view().spec_index(addr).is_init() && post.perms.view().spec_index(addr).addr() == addr,
            post.perms.view().spec_index(addr).value().prev is None,
            post.perms.view().spec_index(addr).value().next == Some(old_head),
            post.perms.view().spec_index(old_head).is_init() && post.perms.view().spec_index(old_head).addr() == old_head,
            post.perms.view().spec_index(old_head).value().view() == pre.perms.view().spec_index(old_head).value().view(),
            post.perms.view().spec_index(old_head).value().prev == Some(addr),
            post.perms.view().spec_index(old_head).value().next == pre.perms.view().spec_index(old_head).value().next,
        ensures
            post.wf(),
    {
        reveal(LinkedList::wf_perms); reveal(LinkedList::wf_addr_list); reveal(LinkedList::wf_value_list); reveal(LinkedList::wf_head); reveal(LinkedList::wf_map);
        seq_push_head_lemma::<usize>(); seq_push_head_lemma::<T>(); seq_push_head_unique_lemma::<usize>();
        assert({
            &&& !pre.addr_list.view().contains(addr)
            &&& post.addr_list.view().spec_index(post.length - 1) == post.tail.unwrap()
            &&& post.perms.view().spec_index(post.tail.unwrap()).value().next is None
        }) by { reveal(LinkedList::wf_tail); };
        reveal(LinkedList::wf_tail); reveal(LinkedList::wf_prev); reveal(LinkedList::wf_next); reveal(LinkedList::value_list_unique);
    }

    /// EOF closure of `pop_head` on a list of at least two nodes: head `old_head` was unlinked and `new_head` lost its `prev`.
    pub(super) proof fn pop_head_eof_wf(pre: Self, post: Self, old_head: usize, new_head: usize)
        requires
            pre.wf(),
            pre.length != 0,
            pre.length != 1,
            pre.head == Some(old_head),
            pre.perms.view().spec_index(old_head).value().next == Some(new_head),
            post == (Self { perms: post.perms, addr_list: post.addr_list, value_list: post.value_list, length: post.length, head: post.head, map: post.map, ..pre }),
            post.length == pre.length - 1,
            post.head == Some(new_head),
            post.addr_list.view() == pre.addr_list.view().skip(1),
            post.value_list.view() == pre.value_list.view().skip(1),
            post.map.view() == pre.map.view().remove(old_head),
            post.perms.view() == pre.perms.view().remove(old_head).remove(new_head).insert(new_head, post.perms.view().spec_index(new_head)),
            post.perms.view().spec_index(new_head).is_init() && post.perms.view().spec_index(new_head).addr() == new_head,
            post.perms.view().spec_index(new_head).value().view() == pre.perms.view().spec_index(new_head).value().view(),
            post.perms.view().spec_index(new_head).value().prev is None,
            post.perms.view().spec_index(new_head).value().next == pre.perms.view().spec_index(new_head).value().next,
        ensures
            post.wf(),
    {
        reveal(LinkedList::wf_perms); reveal(LinkedList::wf_addr_list); reveal(LinkedList::wf_value_list); reveal(LinkedList::wf_head); reveal(LinkedList::wf_next); reveal(LinkedList::wf_map);
        seq_skip_lemma::<usize>(); seq_skip_lemma::<T>(); seq_skip_index_of_lemma::<usize>(); seq_skip_index_of_lemma::<T>();
        reveal(LinkedList::wf_tail); reveal(LinkedList::wf_prev); reveal(LinkedList::value_list_unique);
    }
}
} // verus!
