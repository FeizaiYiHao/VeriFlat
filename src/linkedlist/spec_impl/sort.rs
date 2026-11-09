use super::*;
#[cfg(verus_keep_ghost)]
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_sets_equal};
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;

verus! {
impl<const MAJOR: LockMajorId> LinkedList<usize, MAJOR> {
    pub open spec fn values_sorted(values: Seq<usize>) -> bool {
        forall|i: int, j: int| #![trigger values.spec_index(i), values.spec_index(j)]
            0 <= i <= j < values.len() ==> values.spec_index(i) <= values.spec_index(j)
    }

    pub open spec fn runs_sorted(values: Seq<usize>, width: int) -> bool {
        width > 0 && forall|i: int, j: int| #![trigger values.spec_index(i), values.spec_index(j)]
            0 <= i <= j < values.len() && i / width == j / width ==> values.spec_index(i) <= values.spec_index(j)
    }

    fn take_sort_run(&mut self, count: usize, _width: Ghost<usize>) -> (ret: Self)
        requires
            old(self).wf(),
            count <= old(self).length,
            0 < _width.view(),
            count == if old(self).length < _width.view() { old(self).length } else { _width.view() },
            Self::runs_sorted(old(self).view(), _width.view() as int),
        ensures
            final(self).wf(),
            ret.wf(),
            ret.length == count,
            final(self).length == old(self).length - count,
            ret.view().len() == ret.length,
            final(self).view().len() == final(self).length,
            ret.view() == old(self).view().take(count as int),
            final(self).view() == old(self).view().skip(count as int),
            ret.dom().disjoint(final(self).dom()),
            ret.dom().union(final(self).dom()) == old(self).dom(),
            ret.view().to_set().disjoint(final(self).view().to_set()),
            ret.view().to_set().union(final(self).view().to_set()) == old(self).view().to_set(),
            ret.map().union_prefer_right(final(self).map()) == old(self).map(),
            final(self).container_depth == old(self).container_depth,
            final(self).minor == old(self).minor,
            ret.map().dom() == ret.dom(),
            final(self).map().dom() == final(self).dom(),
            forall|value: usize| #![trigger old(self).view().contains(value)] #![trigger ret.view().contains(value)] #![trigger final(self).view().contains(value)]
                old(self).view().contains(value) == (ret.view().contains(value) || final(self).view().contains(value)),
            Self::values_sorted(ret.view()),
            Self::runs_sorted(final(self).view(), _width.view() as int),
    {
        broadcast use Seq::to_set_ensures, Seq::lemma_seq_skip_skip;
        let mut ret = Self::new(None, None);
        let mut moved = 0usize;
        proof { self.wf_implies_view_len_eq_len(); }
        while moved < count
            invariant
                self.wf(),
                ret.wf(),
                count <= old(self).length,
                moved <= count,
                ret.length == moved,
                self.length == old(self).length - moved,
                self.view().len() == self.length,
                ret.view().len() == ret.length,
                old(self).view().len() == old(self).length,
                Self::runs_sorted(old(self).view(), _width.view() as int),
                0 < _width.view(),
                count == if old(self).length < _width.view() { old(self).length } else { _width.view() },
                ret.view() == old(self).view().take(moved as int),
                self.view() == old(self).view().skip(moved as int),
                ret.dom().disjoint(self.dom()),
                ret.dom().union(self.dom()) == old(self).dom(),
                ret.view().to_set().disjoint(self.view().to_set()),
                ret.view().to_set().union(self.view().to_set()) == old(self).view().to_set(),
                ret.map().union_prefer_right(self.map()) == old(self).map(),
                forall|value: usize| #![trigger old(self).view().contains(value)] #![trigger ret.view().contains(value)] #![trigger self.view().contains(value)]
                    old(self).view().contains(value) == (ret.view().contains(value) || self.view().contains(value)),
                ret.map().dom() == ret.dom(),
                self.map().dom() == self.dom(),
                self.container_depth == old(self).container_depth,
                self.minor == old(self).minor,
            decreases count - moved,
        {
            let ghost value = self.view().spec_index(0);
            assert(!ret.view().to_set().contains(value) && !ret.view().contains(value)) by { ret.view().to_set_ensures(); self.view().to_set_ensures(); }
            let (addr, perm) = self.pop_head();
            proof { ret.wf_map_at(addr); }
            ret.push_tail(addr, perm);
            moved = moved + 1;
            assert(ret.view() == old(self).view().take(moved as int)) by { Seq::lemma_take_succ(old(self).view(), moved as int - 1); };
            proof {
                assert_maps_equal!(ret.map().union_prefer_right(self.map()), old(self).map());
                self.wf_implies_view_len_eq_len(); ret.wf_implies_view_len_eq_len();
                seq_push_implies_contains::<usize>(); seq_skip_one_implies_contains_and_index_shift::<usize>();
            }
            assert(ret.view().to_set().disjoint(self.view().to_set())) by {
                broadcast use Seq::lemma_push_to_set_commute;
                seq_push_implies_contains::<usize>(); seq_skip_one_implies_contains_and_index_shift::<usize>();
            }
            assert(ret.view().to_set().union(self.view().to_set()) == old(self).view().to_set()) by {
                seq_push_implies_contains::<usize>(); seq_skip_one_implies_contains_and_index_shift::<usize>();
                assert_sets_equal!(ret.view().to_set().union(self.view().to_set()), old(self).view().to_set());
            }
        }
        proof { Self::take_sort_run_eof_implies_sorted_runs(*old(self), *self, ret, count, _width.view()); }
        ret
    }

    fn merge_sort_runs(left: &mut Self, right: &mut Self) -> (ret: Self)
        requires
            old(left).wf(),
            old(right).wf(),
            Self::values_sorted(old(left).view()),
            Self::values_sorted(old(right).view()),
            old(left).length + old(right).length <= usize::MAX,
            old(left).dom().disjoint(old(right).dom()),
            old(left).view().to_set().disjoint(old(right).view().to_set()),
        ensures
            final(left).wf(),
            final(right).wf(),
            ret.wf(),
            final(left).length == 0,
            final(right).length == 0,
            ret.length == old(left).length + old(right).length,
            ret.view().len() == ret.length,
            Self::values_sorted(ret.view()),
            ret.map() == old(left).map().union_prefer_right(old(right).map()),
            ret.dom() == old(left).dom().union(old(right).dom()),
            ret.view().to_set() == old(left).view().to_set().union(old(right).view().to_set()),
            forall|value: usize| #![trigger ret.view().contains(value)] #![trigger old(left).view().contains(value)] #![trigger old(right).view().contains(value)]
                ret.view().contains(value) == (old(left).view().contains(value) || old(right).view().contains(value)),
            ret.map().dom() == ret.dom(),
    {
        broadcast use Seq::to_set_ensures;
        let mut ret = Self::new(None, None);
        proof { left.wf_implies_view_len_eq_len(); right.wf_implies_view_len_eq_len(); }
        while left.length != 0 || right.length != 0
            invariant
                left.wf(),
                right.wf(),
                ret.wf(),
                Self::values_sorted(left.view()),
                Self::values_sorted(right.view()),
                Self::values_sorted(ret.view()),
                ret.length + left.length + right.length == old(left).length + old(right).length <= usize::MAX,
                left.view().len() == left.length,
                right.view().len() == right.length,
                ret.view().len() == ret.length,
                ret.dom().disjoint(left.dom()),
                ret.dom().disjoint(right.dom()),
                left.dom().disjoint(right.dom()),
                ret.view().to_set().disjoint(left.view().to_set()),
                ret.view().to_set().disjoint(right.view().to_set()),
                left.view().to_set().disjoint(right.view().to_set()),
                ret.map().union_prefer_right(left.map()).union_prefer_right(right.map()) == old(left).map().union_prefer_right(old(right).map()),
                ret.dom().union(left.dom()).union(right.dom()) == old(left).dom().union(old(right).dom()),
                ret.map().dom() == ret.dom(),
                left.map().dom() == left.dom(),
                right.map().dom() == right.dom(),
                ret.view().to_set().union(left.view().to_set()).union(right.view().to_set()) == old(left).view().to_set().union(old(right).view().to_set()),
                forall|value: usize| #![trigger ret.view().contains(value)] #![trigger left.view().contains(value)] #![trigger right.view().contains(value)]
                    #![trigger old(left).view().contains(value)] #![trigger old(right).view().contains(value)]
                    (ret.view().contains(value) || left.view().contains(value) || right.view().contains(value)) == (old(left).view().contains(value) || old(right).view().contains(value)),
                forall|i: int, j: int| #![trigger ret.view().spec_index(i), left.view().spec_index(j)]
                    0 <= i < ret.length && 0 <= j < left.length ==> ret.view().spec_index(i) <= left.view().spec_index(j),
                forall|i: int, j: int| #![trigger ret.view().spec_index(i), right.view().spec_index(j)]
                    0 <= i < ret.length && 0 <= j < right.length ==> ret.view().spec_index(i) <= right.view().spec_index(j),
            decreases left.length + right.length,
        {
            let take_left = if left.length == 0 { false }
                else if right.length == 0 { true }
                else { left.peek_head().1 <= right.peek_head().1 };
            if take_left {
                let ghost value = left.view().spec_index(0);
                assert(!ret.view().to_set().contains(value) && !ret.view().contains(value)) by { ret.view().to_set_ensures(); left.view().to_set_ensures(); }
                let (addr, perm) = left.pop_head();
                proof { ret.wf_map_at(addr); }
                ret.push_tail(addr, perm);
            } else {
                let ghost value = right.view().spec_index(0);
                assert(!ret.view().to_set().contains(value) && !ret.view().contains(value)) by { ret.view().to_set_ensures(); right.view().to_set_ensures(); }
                let (addr, perm) = right.pop_head();
                proof { ret.wf_map_at(addr); left.wf_map_at(addr); }
                ret.push_tail(addr, perm);
            }
            proof {
                assert_maps_equal!(ret.map().union_prefer_right(left.map()).union_prefer_right(right.map()),
                    old(left).map().union_prefer_right(old(right).map()));
                ret.wf_implies_view_len_eq_len(); left.wf_implies_view_len_eq_len(); right.wf_implies_view_len_eq_len();
                seq_push_implies_contains::<usize>(); seq_skip_one_implies_contains_and_index_shift::<usize>();
            }
            assert(ret.view().to_set().union(left.view().to_set()).union(right.view().to_set()) == old(left).view().to_set().union(old(right).view().to_set())) by {
                seq_push_implies_contains::<usize>(); seq_skip_one_implies_contains_and_index_shift::<usize>();
                assert_sets_equal!(ret.view().to_set().union(left.view().to_set()).union(right.view().to_set()), old(left).view().to_set().union(old(right).view().to_set()));
            }
        }
        proof { left.wf_implies_view_len_eq_len(); right.wf_implies_view_len_eq_len(); }
        ret
    }

    fn append_sort_run(&mut self, run: &mut Self, _width: Ghost<int>)
        requires
            old(self).wf(),
            old(run).wf(),
            old(self).length + old(run).length <= usize::MAX,
            old(self).dom().disjoint(old(run).dom()),
            old(self).view().to_set().disjoint(old(run).view().to_set()),
            Self::runs_sorted(old(self).view(), _width.view()),
            (old(self).length as int) % _width.view() == 0,
            Self::values_sorted(old(run).view()),
            old(run).length <= _width.view(),
        ensures
            final(self).wf(),
            final(run).wf(),
            final(run).length == 0,
            final(self).length == old(self).length + old(run).length,
            final(self).view() == old(self).view().add(old(run).view()),
            final(self).view().len() == final(self).length,
            final(self).map() == old(self).map().union_prefer_right(old(run).map()),
            final(self).dom() == old(self).dom().union(old(run).dom()),
            final(self).view().to_set() == old(self).view().to_set().union(old(run).view().to_set()),
            forall|value: usize| #![trigger final(self).view().contains(value)] #![trigger old(self).view().contains(value)] #![trigger old(run).view().contains(value)]
                final(self).view().contains(value) == (old(self).view().contains(value) || old(run).view().contains(value)),
            final(self).container_depth == old(self).container_depth,
            final(self).minor == old(self).minor,
            final(self).map().dom() == final(self).dom(),
            Self::runs_sorted(final(self).view(), _width.view()),
    {
        broadcast use Seq::to_set_ensures, Seq::lemma_seq_skip_skip, Seq::push_distributes_over_add;
        let mut moved = 0usize;
        proof { self.wf_implies_view_len_eq_len(); run.wf_implies_view_len_eq_len(); }
        while run.length != 0
            invariant
                self.wf(),
                run.wf(),
                self.length + run.length == old(self).length + old(run).length <= usize::MAX,
                self.view().len() == self.length,
                run.view().len() == run.length,
                old(run).view().len() == old(run).length,
                old(self).view().len() == old(self).length,
                moved <= old(run).length,
                self.view() == old(self).view().add(old(run).view().take(moved as int)),
                run.view() == old(run).view().skip(moved as int),
                run.length == old(run).length - moved,
                self.dom().disjoint(run.dom()),
                self.view().to_set().disjoint(run.view().to_set()),
                self.map().union_prefer_right(run.map()) == old(self).map().union_prefer_right(old(run).map()),
                self.dom().union(run.dom()) == old(self).dom().union(old(run).dom()),
                self.view().to_set().union(run.view().to_set()) == old(self).view().to_set().union(old(run).view().to_set()),
                forall|value: usize| #![trigger self.view().contains(value)] #![trigger run.view().contains(value)]
                    #![trigger old(self).view().contains(value)] #![trigger old(run).view().contains(value)]
                    (self.view().contains(value) || run.view().contains(value)) == (old(self).view().contains(value) || old(run).view().contains(value)),
                self.map().dom() == self.dom(),
                run.map().dom() == run.dom(),
                self.container_depth == old(self).container_depth,
                self.minor == old(self).minor,
                Self::runs_sorted(old(self).view(), _width.view()),
                (old(self).length as int) % _width.view() == 0,
                Self::values_sorted(old(run).view()),
                old(run).length <= _width.view(),
            decreases run.length,
        {
            let ghost value = run.view().spec_index(0);
            assert(!self.view().to_set().contains(value) && !self.view().contains(value)) by { self.view().to_set_ensures(); run.view().to_set_ensures(); }
            let (addr, perm) = run.pop_head();
            self.push_tail(addr, perm);
            moved = moved + 1;
            proof {
                Seq::lemma_take_succ(old(run).view(), moved as int - 1);
                assert_maps_equal!(self.map().union_prefer_right(run.map()), old(self).map().union_prefer_right(old(run).map()));
                self.wf_implies_view_len_eq_len(); run.wf_implies_view_len_eq_len();
                seq_push_implies_contains::<usize>(); seq_skip_one_implies_contains_and_index_shift::<usize>();
            }
            assert(self.view().to_set().disjoint(run.view().to_set())) by {
                broadcast use Seq::lemma_push_to_set_commute;
                seq_push_implies_contains::<usize>(); seq_skip_one_implies_contains_and_index_shift::<usize>();
            }
            assert(self.view().to_set().union(run.view().to_set()) == old(self).view().to_set().union(old(run).view().to_set())) by {
                seq_push_implies_contains::<usize>(); seq_skip_one_implies_contains_and_index_shift::<usize>();
                assert_sets_equal!(self.view().to_set().union(run.view().to_set()), old(self).view().to_set().union(old(run).view().to_set()));
            }
        }
        proof { run.wf_implies_view_len_eq_len(); }
        assert(Self::append_sort_run_eof_transition_framing(*old(self), *old(run), *self, *run)) by {
            old(run).view().lemma_take_len();
            assert_maps_equal!(self.map(), old(self).map().union_prefer_right(old(run).map()));
            assert_sets_equal!(self.dom(), old(self).dom().union(old(run).dom()));
            assert_sets_equal!(self.view().to_set(), old(self).view().to_set().union(old(run).view().to_set()));
        };
        proof { Self::append_sort_run_eof_implies_sorted_runs(*old(self), *old(run), *self, *run, _width.view()); }
    }

    fn sort_page_ptrs_pass(&mut self, width: usize)
        requires
            old(self).wf(),
            0 < width <= old(self).length,
            Self::runs_sorted(old(self).view(), width as int),
        ensures
            final(self).wf(),
            final(self).length == old(self).length,
            final(self).view().len() == old(self).view().len(),
            final(self).map() == old(self).map(),
            final(self).dom() == old(self).dom(),
            final(self).view().to_set() == old(self).view().to_set(),
            forall|value: usize| #![trigger final(self).view().contains(value)] #![trigger old(self).view().contains(value)]
                final(self).view().contains(value) == old(self).view().contains(value),
            final(self).container_depth == old(self).container_depth,
            final(self).minor == old(self).minor,
            Self::runs_sorted(final(self).view(), 2 * width),
    {
        broadcast use Seq::to_set_ensures;
        let mut output = Self {
            perms: Tracked(Map::tracked_empty()), addr_list: Ghost(Seq::empty()), value_list: Ghost(Seq::empty()),
            length: 0, head: None, tail: None, map: Ghost(Map::empty()),
            container_depth: self.container_depth, minor: self.minor,
        };
        proof { Self::sort_page_ptrs_pass_empty_output_eof_implies_wf(&output); }
        proof { self.wf_implies_view_len_eq_len(); }
        while self.length != 0
            invariant
                self.wf(),
                output.wf(),
                self.length + output.length == old(self).length,
                self.view().len() == self.length,
                output.view().len() == output.length,
                old(self).view().len() == old(self).length,
                self.dom().disjoint(output.dom()),
                self.view().to_set().disjoint(output.view().to_set()),
                self.view().to_set().union(output.view().to_set()) == old(self).view().to_set(),
                forall|value: usize| #![trigger self.view().contains(value)] #![trigger output.view().contains(value)] #![trigger old(self).view().contains(value)]
                    (self.view().contains(value) || output.view().contains(value)) == old(self).view().contains(value),
                self.map().union_prefer_right(output.map()) == old(self).map(),
                self.dom().union(output.dom()) == old(self).dom(),
                self.map().dom() == self.dom(),
                output.map().dom() == output.dom(),
                0 < width <= old(self).length,
                Self::runs_sorted(self.view(), width as int),
                Self::runs_sorted(output.view(), 2 * width),
                self.length != 0 ==> (output.length as int) % (2 * width) == 0,
                self.container_depth == old(self).container_depth,
                self.minor == old(self).minor,
                output.container_depth == old(self).container_depth,
                output.minor == old(self).minor,
            decreases self.length,
        {
            let left_count = if self.length < width { self.length } else { width };
            let mut left = self.take_sort_run(left_count, Ghost(width));
            let right_count = if self.length < width { self.length } else { width };
            let mut right = self.take_sort_run(right_count, Ghost(width));
            let mut merged = Self::merge_sort_runs(&mut left, &mut right);
            output.append_sort_run(&mut merged, Ghost(2 * width));
            proof {
                lemma_mod_add_multiples_vanish(output.length as int - 2 * width, 2 * width);
                assert_sets_equal!(self.view().to_set().union(output.view().to_set()), old(self).view().to_set());
            }
        }
        proof {
            self.wf_implies_view_len_eq_len();
            assert_maps_equal!(output.map(), old(self).map());
            assert_sets_equal!(output.view().to_set(), old(self).view().to_set());
        }
        *self = output;
    }

    pub fn sort_page_ptrs(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).length == old(self).length,
            final(self).view().len() == old(self).view().len(),
            final(self).map() == old(self).map(),
            final(self).dom() == old(self).dom(),
            final(self).view().to_set() == old(self).view().to_set(),
            forall|value: usize| #![trigger final(self).view().contains(value)] #![trigger old(self).view().contains(value)]
                final(self).view().contains(value) == old(self).view().contains(value),
            final(self).container_depth == old(self).container_depth,
            final(self).minor == old(self).minor,
            Self::values_sorted(final(self).view()),
    {
        broadcast use Seq::to_set_ensures;
        let mut width = 1usize;
        proof { self.wf_implies_view_len_eq_len(); }
        while width < self.length
            invariant
                self.wf(),
                self.length == old(self).length,
                self.view().len() == self.length,
                old(self).view().len() == old(self).length,
                self.map() == old(self).map(),
                self.dom() == old(self).dom(),
                self.view().to_set() == old(self).view().to_set(),
                forall|value: usize| #![trigger self.view().contains(value)] #![trigger old(self).view().contains(value)]
                    self.view().contains(value) == old(self).view().contains(value),
                self.container_depth == old(self).container_depth,
                self.minor == old(self).minor,
                0 < width,
                Self::runs_sorted(self.view(), width as int),
            decreases self.length - width,
        {
            self.sort_page_ptrs_pass(width);
            if width <= self.length / 2 { width = width * 2; }
            else {
                proof { Self::sort_page_ptrs_eof_implies_sorted_single_run(*old(self), *self, 2 * width); }
                width = self.length;
            }
        }
        proof { Self::sort_page_ptrs_eof_implies_sorted_single_run(*old(self), *self, width as int); }
    }
}
}
