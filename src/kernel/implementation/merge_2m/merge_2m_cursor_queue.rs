#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_cursor_queue_folds::*;

verus! {
#[derive(Clone, Copy)]
pub struct Merge2mCursor {
    pub page: PagePtr,
    pub node: Option<usize>,
    pub source: usize,
}

impl Merge2mCursor {
    pub open spec fn source_value() -> spec_fn(Merge2mCursor) -> usize { |cursor: Merge2mCursor| cursor.source }

    pub open spec fn wf(self) -> bool {
        &&& self.source <= NUM_CPUS
        &&& self.node is None ==> self.page == usize::MAX
        &&& self.node is Some ==> page_ptr_valid(self.page)
    }
}

pub struct Merge2mCursorQueue {
    pub cursors: Array<Merge2mCursor, { NUM_CPUS + 1 }>,
}

impl Merge2mCursorQueue {
    pub open spec fn cursors_wf(&self) -> bool {
        &&& self.cursors.wf()
        &&& forall|i: int| #![trigger self.cursors.view().spec_index(i)] 0 <= i < NUM_CPUS + 1 ==> self.cursors.view().spec_index(i).wf()
    }

    pub open spec fn ordered_from(&self, first: usize) -> bool {
        forall|i: int| #![trigger self.cursors.view().spec_index(i)] 1 <= i < NUM_CPUS + 1 && (i - 1) / 2 >= first ==>
            self.cursors.view().spec_index((i - 1) / 2).page <= self.cursors.view().spec_index(i).page
    }

    pub open spec fn wf(&self) -> bool { self.cursors_wf() && self.ordered_from(0) }

    fn swap_cursors(&mut self, left: usize, right: usize)
        requires
            old(self).cursors_wf(),
            left < NUM_CPUS + 1,
            right < NUM_CPUS + 1,
            left != right,
        ensures
            final(self).cursors_wf(),
            final(self).cursors.view() == old(self).cursors.view().update(left as int, old(self).cursors.view().spec_index(right as int))
                .update(right as int, old(self).cursors.view().spec_index(left as int)),
            final(self).cursors.view().to_multiset() == old(self).cursors.view().to_multiset(),
    {
        let left_cursor = *self.cursors.get(left);
        let right_cursor = *self.cursors.get(right);
        self.cursors.set(left, right_cursor);
        self.cursors.set(right, left_cursor);
        assert(self.cursors.view().to_multiset() == old(self).cursors.view().to_multiset()) by {
            sequence_swap_implies_same_multiset(old(self).cursors.view(), left as int, right as int);
        };
    }

    fn sift_down(&mut self, first: usize)
        requires
            old(self).cursors_wf(),
            first < NUM_CPUS + 1,
            old(self).ordered_from((first + 1) as usize),
        ensures
            final(self).cursors_wf(),
            final(self).ordered_from(first),
            final(self).cursors.view().to_multiset() == old(self).cursors.view().to_multiset(),
            forall|i: int| #![trigger final(self).cursors.view().spec_index(i)] 0 <= i < first ==>
                final(self).cursors.view().spec_index(i) == old(self).cursors.view().spec_index(i),
    {
        let mut hole = first;
        while hole < (NUM_CPUS + 1) / 2
            invariant
                self.cursors_wf(),
                first <= hole < NUM_CPUS + 1,
                self.cursors.view().to_multiset() == old(self).cursors.view().to_multiset(),
                forall|i: int| #![trigger self.cursors.view().spec_index(i)]
                    1 <= i < NUM_CPUS + 1 && (i - 1) / 2 >= first && (i - 1) / 2 != hole ==>
                        self.cursors.view().spec_index((i - 1) / 2).page <= self.cursors.view().spec_index(i).page,
                forall|i: int| #![trigger self.cursors.view().spec_index(i)]
                    1 <= i < NUM_CPUS + 1 && (i - 1) / 2 == hole && hole > first ==>
                        self.cursors.view().spec_index((hole - 1) / 2).page <= self.cursors.view().spec_index(i).page,
                forall|i: int| #![trigger self.cursors.view().spec_index(i)] 0 <= i < first ==>
                    self.cursors.view().spec_index(i) == old(self).cursors.view().spec_index(i),
            decreases NUM_CPUS + 1 - hole,
        {
            let left = 2 * hole + 1;
            let right = left + 1;
            let mut child = left;
            let left_cursor = *self.cursors.get(left);
            if right < NUM_CPUS + 1 {
                let right_cursor = *self.cursors.get(right);
                if right_cursor.page < left_cursor.page { child = right; }
            }
            let child_cursor = *self.cursors.get(child);
            let hole_cursor = *self.cursors.get(hole);
            if hole_cursor.page <= child_cursor.page {
                assert(self.ordered_from(first)) by { broadcast use vstd::arithmetic::div_mod::lemma_fundamental_div_mod; };
                return;
            }
            assert((left as int - 1) / 2 == hole as int && (right as int - 1) / 2 == hole as int) by (nonlinear_arith) requires left == 2 * hole + 1, right == left + 1;
            self.swap_cursors(hole, child);
            hole = child;
        }
    }

    pub fn new(cursors: Array<Merge2mCursor, { NUM_CPUS + 1 }>) -> (ret: Self)
        requires
            cursors.wf(),
            forall|i: int| #![trigger cursors.view().spec_index(i)] 0 <= i < NUM_CPUS + 1 ==> cursors.view().spec_index(i).wf(),
        ensures
            ret.wf(),
            ret.cursors.view().to_multiset() == cursors.view().to_multiset(),
    {
        let mut ret = Merge2mCursorQueue { cursors };
        let mut first = (NUM_CPUS + 1) / 2;
        while first > 0
            invariant
                ret.cursors_wf(),
                ret.cursors.view().to_multiset() == cursors.view().to_multiset(),
                first <= (NUM_CPUS + 1) / 2,
                ret.ordered_from(first),
            decreases first,
        {
            first = first - 1;
            ret.sift_down(first);
        }
        ret
    }

    pub fn peek_min(&self) -> (ret: Merge2mCursor)
        requires
            self.wf(),
        ensures
            ret == self.cursors.view().spec_index(0),
            ret.wf(),
            ret.node is None ==> forall|i: int| #![trigger self.cursors.view().spec_index(i)] 0 <= i < NUM_CPUS + 1 ==>
                self.cursors.view().spec_index(i).node is None,
            forall|i: int| #![trigger self.cursors.view().spec_index(i)] 0 <= i < NUM_CPUS + 1 ==> ret.page <= self.cursors.view().spec_index(i).page,
    {
        *self.cursors.get(0)
    }

    pub fn advance_min(&mut self, page: PagePtr, node: Option<usize>)
        requires
            old(self).wf(),
            node is None ==> page == usize::MAX,
            node is Some ==> page_ptr_valid(page),
        ensures
            final(self).wf(),
            final(self).cursors.view().to_multiset() == old(self).cursors.view().update(0,
                Merge2mCursor { page, node, source: old(self).cursors.view().spec_index(0).source }).to_multiset(),
    {
        let old_min = *self.cursors.get(0);
        self.cursors.set(0, Merge2mCursor { page, node, source: old_min.source });
        self.sift_down(0);
    }
}
}
