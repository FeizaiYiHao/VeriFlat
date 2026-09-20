use vstd::prelude::*;
verus! {
use crate::*;
use vstd::set_lib::*;


/// A set of integers from 0 to N - 1.
pub struct ArraySet<const N: usize> {
    pub data: Array<bool, N>,
    pub closed: Array<bool, N>,
    pub len: usize,
    pub set: Ghost<Set<usize>>,
    pub closed_set: Ghost<Set<usize>>,
}

impl <const N: usize> ArraySet<N> {

    pub fn new() -> (ret:Self)
        ensures
            ret.wf(),
            ret.view() == Set::<usize>::empty(),
            ret.closed_view() == Set::<usize>::empty(),
    {
        let mut ret = Self {
            data: Array::new(),
            closed: Array::new(),
            len: 0,
            set: Ghost(Set::<usize>::empty()),
            closed_set: Ghost(Set::<usize>::empty()),
        };
        for i in 0..N
            invariant
                0<=i<=N,
                ret.data.wf(),
                ret.closed.wf(),
                ret.len == 0,
                ret.set.view() == Set::<usize>::empty(),
                ret.closed_set.view() == Set::<usize>::empty(),
                forall|j:int| 0<=j<i ==> ret.data.view().spec_index(j) == false,
                forall|j:int| 0<=j<i ==> ret.closed.view().spec_index(j) == false,
        {
            ret.data.set(i, false);
            ret.closed.set(i, false);
        }
        ret
    }

    pub fn init(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).view() == Set::<usize>::empty(),
            final(self).closed_view() == Set::<usize>::empty(),
    {
        self.len = 0;
        self.set = Ghost(Set::<usize>::empty());
        self.closed_set = Ghost(Set::<usize>::empty());
        for i in 0..N
            invariant
                0<=i<=N,
                self.data.wf(),
                self.closed.wf(),
                self.len == 0,
                self.set.view() == Set::<usize>::empty(),
                self.closed_set.view() == Set::<usize>::empty(),
                forall|j:int| 0<=j<i ==> self.data.view().spec_index(j) == false,
                forall|j:int| 0<=j<i ==> self.closed.view().spec_index(j) == false,
        {
            self.data.set(i, false);
            self.closed.set(i, false);
        }
    }

    pub closed spec fn view(&self) -> Set<usize>{
        self.set.view()
    }

    pub closed spec fn closed_view(&self) -> Set<usize> {
        self.closed_set.view()
    }

    pub fn contains(&self, v: usize) -> (ret: bool)
        requires
            self.wf(),
            0 <= v < N,
        ensures
            ret == self.view().contains(v),
    {
        *self.data.get(v)
    }

    pub fn is_closed(&self, v: usize) -> (ret: bool)
        requires
            self.wf(),
            0 <= v < N,
        ensures
            ret == self.closed_view().contains(v),
    {
        *self.closed.get(v)
    }

    #[verifier(when_used_as_spec(spec_len))]
    pub fn len(&self) -> (ret:usize)
        requires
            self.wf(),
        ensures
            ret == self.set.view().len(),
    {
        self.len
    }

    pub closed spec fn spec_len(&self) -> usize{
        self.set.view().len() as usize
    }

    pub open spec fn wf(&self) -> bool{
        &&&
        self.elements_in_range()
        &&&
        self.internal_wf()
        &&& self.closed_view().subset_of(self.view())
    }

    pub open spec fn elements_in_range(&self) -> bool{
        &&&
        forall|i:usize| 
            #![trigger self.view().contains(i)]
            self.view().contains(i) ==> 0 <= i < N
    }

    pub closed spec fn internal_wf(&self) -> bool{
        &&&
        self.data.wf()
        &&&
        self.closed.wf()
        &&&
        0 <= self.len <= N
        &&&
        forall|i:usize| 
            #![trigger self.data.view().spec_index(i as int)]
            #![trigger self.set.view().contains(i)]
            0 <= i < N && self.data.view().spec_index(i as int) ==> self.set.view().contains(i)
        &&&
        forall|i:usize| 
            #![trigger self.data.view().spec_index(i as int)]
            #![trigger self.set.view().contains(i)]
            self.set.view().contains(i) ==> 0 <= i < N && self.data.view().spec_index(i as int)
        &&&
        forall|i:usize|
            #![trigger self.closed.view().spec_index(i as int)]
            #![trigger self.closed_set.view().contains(i)]
            0 <= i < N && self.closed.view().spec_index(i as int) ==> self.closed_set.view().contains(i)
        &&&
        forall|i:usize|
            #![trigger self.closed.view().spec_index(i as int)]
            #![trigger self.closed_set.view().contains(i)]
            self.closed_set.view().contains(i) ==> 0 <= i < N && self.closed.view().spec_index(i as int)
        &&&
        self.closed_set.view().subset_of(self.set.view())
        &&&
        self.len == self.set.view().len()
    }

    pub fn insert(&mut self, v:usize)
        requires
            old(self).wf(),
            old(self).view().contains(v) == false,
            0 <= v < N,
        ensures
            final(self).wf(),
            final(self).view() == old(self).view().insert(v),
            final(self).closed_view() == old(self).closed_view(),
    {
        proof { Self::lemma_set_missing_element_size(self.set.view(), v, N); }

        self.data.set(v, true);
        self.closed.set(v, false);
        self.set = Ghost(self.set.view().insert(v));
        self.len = self.len + 1;
    }

    pub fn insert_closed(&mut self, v: usize)
        requires
            old(self).wf(),
            old(self).view().contains(v) == false,
            0 <= v < N,
        ensures
            final(self).wf(),
            final(self).view() == old(self).view().insert(v),
            final(self).closed_view() == old(self).closed_view().insert(v),
            final(self).data.view() == old(self).data.view().update(v as int, true),
            final(self).closed.view() == old(self).closed.view().update(v as int, true),
            final(self).len as int == old(self).len as int + 1,
    {
        proof { Self::lemma_set_missing_element_size(self.set.view(), v, N); }
        self.data.set(v, true);
        self.closed.set(v, true);
        self.set = Ghost(self.set.view().insert(v));
        self.closed_set = Ghost(self.closed_set.view().insert(v));
        self.len = self.len + 1;
    }

    pub fn remove(&mut self, v:usize)
        requires
            old(self).wf(),
            old(self).view().contains(v) == true,
        ensures
            final(self).wf(),
            final(self).view() == old(self).view().remove(v),
            final(self).closed_view() == old(self).closed_view().remove(v),
            final(self).data.view() == old(self).data.view().update(v as int, false),
            final(self).closed.view() == old(self).closed.view().update(v as int, false),
            final(self).len as int == old(self).len as int - 1,
    {
        self.data.set(v, false);
        self.closed.set(v, false);
        self.len = self.len - 1;
        self.set = Ghost(self.set.view().remove(v));
        self.closed_set = Ghost(self.closed_set.view().remove(v));
    }

    pub fn mark_closed(&mut self, v: usize)
        requires
            old(self).wf(),
            old(self).view().contains(v),
            !old(self).closed_view().contains(v),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            final(self).closed_view() == old(self).closed_view().insert(v),
    {
        self.closed.set(v, true);
        self.closed_set = Ghost(self.closed_set.view().insert(v));
    }

    pub fn mark_open(&mut self, v: usize)
        requires
            old(self).wf(),
            old(self).closed_view().contains(v),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            final(self).closed_view() == old(self).closed_view().remove(v),
    {
        self.closed.set(v, false);
        self.closed_set = Ghost(self.closed_set.view().remove(v));
    }
    proof fn lemma_finite_set_bounded_size(s: Set<usize>, m: usize)
        requires
            forall|i: usize| #[trigger] s.contains(i) ==> 0 <= i < m,
        ensures
            s.len() <= m,
    {
        lemma_len_subset(s, Set::<usize>::range(0, m));
    }

    proof fn lemma_set_missing_element_size(s: Set<usize>, v: usize, n: usize)
        requires
            forall|i: usize| #[trigger] s.contains(i) ==> 0 <= i < n,
            0 <= v < n,
            !s.contains(v),
            n > 0,
        ensures
            s.len() < n,
    {
        Self::lemma_finite_set_bounded_size(s.insert(v), n);
    }
}

}
