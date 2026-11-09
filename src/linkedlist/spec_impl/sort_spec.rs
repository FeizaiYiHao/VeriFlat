use super::*;

verus! {
impl<const MAJOR: LockMajorId> LinkedList<usize, MAJOR> {
    pub open spec fn take_sort_run_eof_transition_framing(pre: Self, post: Self, run: Self, count: usize) -> bool {
        &&& run.length == count
        &&& post.length == pre.length - count
        &&& run.view() == pre.view().take(count as int)
        &&& post.view() == pre.view().skip(count as int)
        &&& run.view().len() == run.length
        &&& post.view().len() == post.length
        &&& run.dom().disjoint(post.dom())
        &&& run.dom().union(post.dom()) == pre.dom()
        &&& run.view().to_set().disjoint(post.view().to_set())
        &&& run.view().to_set().union(post.view().to_set()) == pre.view().to_set()
        &&& run.map().union_prefer_right(post.map()) == pre.map()
        &&& post.container_depth == pre.container_depth
        &&& post.minor == pre.minor
    }

    pub open spec fn append_sort_run_eof_transition_framing(pre: Self, input: Self, post: Self, remaining: Self) -> bool {
        &&& remaining.length == 0
        &&& remaining.dom() == Set::<usize>::empty()
        &&& remaining.map() == Map::<usize, usize>::empty()
        &&& post.length == pre.length + input.length
        &&& post.view() == pre.view().add(input.view())
        &&& post.view().len() == post.length
        &&& post.map() == pre.map().union_prefer_right(input.map())
        &&& post.dom() == pre.dom().union(input.dom())
        &&& post.view().to_set() == pre.view().to_set().union(input.view().to_set())
        &&& post.container_depth == pre.container_depth
        &&& post.minor == pre.minor
    }

    pub open spec fn sort_page_ptrs_eof_transition_framing(pre: Self, post: Self, width: int) -> bool {
        &&& post.length == pre.length
        &&& post.map() == pre.map()
        &&& post.dom() == pre.dom()
        &&& post.view().to_set() == pre.view().to_set()
        &&& post.container_depth == pre.container_depth
        &&& post.minor == pre.minor
        &&& post.view().len() == post.length
        &&& Self::runs_sorted(post.view(), width)
    }
}
}
