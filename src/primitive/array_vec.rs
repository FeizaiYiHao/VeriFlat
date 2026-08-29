use vstd::prelude::*;
verus! {
use crate::*;



/// A preallocated vector.
pub struct ArrayVec<T, const N: usize> {
    pub data: Array<T, N>,
    pub len: usize,
}

impl<T: Copy, const N: usize> ArrayVec<T, N> {
    pub fn new() -> (ret: Self)
        requires
            0 <= N <= usize::MAX, // Verus doesn't know
        ensures
            ret.wf(),
            ret.len() == 0,
            ret.capacity() == N,
    {
        let ret = Self {
            data: Array::new(),
            len: 0,
        };

        ret
    }

    #[verifier(when_used_as_spec(spec_len))]
    pub fn len(&self) -> (ret: usize)
        requires
            self.wf(),
        ensures
            ret == self.len(),
    {
        self.len
    }

    pub open spec fn spec_len(&self) -> usize {
        self.len
    }

    #[verifier(when_used_as_spec(spec_capacity))]
    pub const fn capacity(&self) -> (ret: usize)
        ensures
            ret == self.spec_capacity(),
    {
        N
    }

    pub open spec fn spec_capacity(&self) -> usize {
        N
    }

    pub closed spec fn view(&self) -> Seq<T>
    {
        self.data.view().subrange(0, self.len as int)
    }


    pub open spec fn wf(&self) -> bool {
        &&& self.len() == self.view().len()
        &&& self.len() <= self.capacity()
        &&& self.data.wf()
    }

    pub open spec fn spec_index(&self, index: int) -> (ret: T) {
        self.view().spec_index(index)
    }

    pub fn get(&self, index: usize) -> (ret: &T)
        requires
            self.wf(),
            index < self.len(),
        ensures
            *ret == self.view().spec_index(index as int),
    {
        self.data.get(index)
    }

    pub fn push(&mut self, value: T)
        requires
            old(self).wf(),
            old(self).len() < old(self).capacity(),
        ensures
            final(self).wf(),
            final(self).view() =~= old(self).view().push(value),
            final(self).len() == old(self).len() + 1,
    {
        let index = self.len;
        self.data.set(index, value);

        self.len = self.len + 1;
    }

    pub fn push_unique(&mut self, value: T)
    requires
        old(self).wf(),
        old(self).len() < old(self).capacity(),
        old(self).view().no_duplicates(),
        old(self).view().contains(value) == false,
    ensures
        final(self).wf(),
        final(self).view() =~= old(self).view().push(value),
        final(self).len() == old(self).len() + 1,
        final(self).view().no_duplicates(),
    {
        let index = self.len;
        let ret = self.data.set(index, value);

        self.len = self.len + 1;

        assert(self.view() =~= old(self).view().push(value));

        assert(forall|t:T| #![auto] !( t =~= value) ==> self.view().contains(t) ==> old(self).view().contains(t));
        assert(forall|t:T| #![auto] !( t =~= value) ==> old(self).view().contains(t) ==> self.view().spec_index(old(self).view().index_of(t)) =~= t);
        assert(forall|t:T| #![auto] !( t =~= value) ==> old(self).view().contains(t) ==> self.view().contains(t));
        assert(forall|i:int| #![auto] 0<=i<old(self).len() ==> ! (self.view().spec_index(i) =~= value));
        assert(self.view().spec_index(self.len - 1) =~= value);
    }

    pub fn pop(&mut self) -> (ret: T)
        requires
            old(self).wf(),
            old(self).len() > 0,
        ensures
            final(self).wf(),
            final(self).len() == old(self).len() - 1,
            ret == old(self).view().spec_index(old(self).len() - 1),
            final(self).view() =~= old(self).view().drop_last(),
    {
        let index = self.len() - 1;
        let ret = *self.data.get(index);

        self.len = self.len - 1;

        ret
    }

    pub fn pop_unique(&mut self) -> (ret: &T)
        requires
            old(self).wf(),
            old(self).view().len() > 0,
            old(self).view().no_duplicates(),
        ensures
            final(self).wf(),
            final(self).view().len() == old(self).view().len() - 1,
            ret == old(self).view().spec_index(old(self).len() - 1),
            final(self).view() =~= old(self).view().drop_last(),
            final(self).view().no_duplicates(),
    {
        let index = self.len() - 1;
        let ret = self.data.get(index);

        self.len = self.len - 1;

        ret
    }

    pub fn set(&mut self, index: usize, value: T)
        requires
            old(self).wf(),
            index < old(self).len(),
        ensures
            final(self).wf(),
            final(self).view() =~= old(self).view().update(index as int, value),
    {
        self.data.set(index, value);
    }

}

fn test<const N: usize>(ar: &mut ArrayVec<u64, N>)
requires
    old(ar).wf(),
    old(ar).len() == 1,
    old(ar).view().spec_index(0) == 0,
    N == 2,

{
    let v_0 = ar.pop();
    assert(ar.view() == Seq::<u64>::empty());
    assert(v_0 == 0);
}

}