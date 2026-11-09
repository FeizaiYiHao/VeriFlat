use super::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;

verus! {
impl<const MAJOR: LockMajorId> LinkedList<usize, MAJOR> {
    pub proof fn take_sort_run_eof_implies_sorted_runs(pre: Self, post: Self, run: Self, count: usize, width: usize)
        requires
            Self::take_sort_run_eof_transition_framing(pre, post, run, count),
            Self::runs_sorted(pre.view(), width as int),
            count == if pre.length < width { pre.length } else { width },
            pre.view().len() == pre.length,
        ensures
            Self::values_sorted(run.view()),
            Self::runs_sorted(post.view(), width as int),
    {
        broadcast use lemma_basic_div, add_divisor_implies_quotient_plus_one;
    }

    pub proof fn append_sort_run_eof_implies_sorted_runs(pre: Self, input: Self, post: Self, remaining: Self, width: int)
        requires
            Self::append_sort_run_eof_transition_framing(pre, input, post, remaining),
            Self::runs_sorted(pre.view(), width),
            (pre.length as int) % width == 0,
            Self::values_sorted(input.view()),
            input.length <= width,
            pre.view().len() == pre.length,
            input.view().len() == input.length,
        ensures
            Self::runs_sorted(post.view(), width),
    {
        broadcast use lemma_div_by_multiple_is_strongly_ordered, lemma_div_is_ordered;
        lemma_fundamental_div_mod(pre.length as int, width); vstd::arithmetic::mul::lemma_mul_is_commutative(width, pre.length as int / width);
    }

    pub proof fn sort_page_ptrs_eof_implies_sorted_single_run(pre: Self, post: Self, width: int)
        requires
            Self::sort_page_ptrs_eof_transition_framing(pre, post, width),
            post.length <= width,
        ensures
            Self::values_sorted(post.view()),
    {
        broadcast use lemma_basic_div;
    }

    pub proof fn sort_page_ptrs_pass_empty_output_eof_implies_wf(list: &Self)
        requires
            list.perms.view().dom() == Set::<usize>::empty(),
            list.addr_list.view() == Seq::<usize>::empty(),
            list.value_list.view() == Seq::<usize>::empty(),
            list.map() == Map::<usize, usize>::empty(),
            list.length == 0,
            list.head is None,
            list.tail is None,
        ensures
            list.wf(),
    {
        reveal(LinkedList::wf_perms); reveal(LinkedList::wf_addr_list); reveal(LinkedList::wf_value_list);
        reveal(LinkedList::wf_head); reveal(LinkedList::wf_tail); reveal(LinkedList::wf_prev);
        reveal(LinkedList::wf_next); reveal(LinkedList::wf_map); reveal(LinkedList::value_list_unique);
    }

}
}
