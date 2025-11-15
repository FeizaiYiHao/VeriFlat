use vstd::prelude::*;
verus! {
use core::mem::MaybeUninit;

pub struct Array<A, const N: usize>{
    pub seq: Ghost<Seq<A>>,
    pub ar: [A;N]
}

impl<A, const N: usize> Array<A, N> {
    #[verifier(external_body)]
    pub const fn new() -> (ret: Self)
        ensures
            ret.wf(),
    {
        unsafe{
        let ret = Self {
            ar: MaybeUninit::uninit().assume_init(),
            seq: Ghost(Seq::empty()),
        };
        ret
        }
    }

    #[verifier(external_body)]
    pub fn get(&self, i: usize) -> (out: &A)
        requires
            0 <= i < N,
            self.wf(),
        ensures
            *out == self.seq@[i as int],
    {
        &self.ar[i]
    }

    #[verifier(inline)]
    pub open spec fn spec_index(self, i: usize) -> A
        recommends self.seq@.len() == N,
            0 <= i < N,
    {
        self.seq@[i as int]
    }

    #[verifier(inline)]
    pub open spec fn view(&self) -> Seq<A>{
        self.seq@
    }

    pub open spec fn wf(&self) -> bool{
        self.seq@.len() == N
    }

}

impl<A, const N: usize> Array<A, N> {
    #[verifier(external_body)]
    pub fn set(&mut self, i: usize, out: A)
        requires
            0 <= i < N,
            old(self).wf(),
        ensures
            self.seq@ =~= old(self).seq@.update(i as int, out),
            self.wf(),
    {
        self.ar[i] = out;
    }
}

impl<const N: usize> Array<u8, N> {

    pub fn init2zero(&mut self)
        requires
            old(self).wf(),
            N <= usize::MAX,
        ensures
            forall|index:int| 0<= index < N ==> #[trigger] self@[index] == 0,
            self.wf(),
    {
        let mut i = 0;
        for i in 0..N
            invariant
                N <= usize::MAX,
                0<=i<=N,
                self.wf(),
                forall|j:int| #![auto] 0<=j<i ==> self@[j] == 0,
        {
            let tmp:Ghost<Seq<u8>> = Ghost(self@);
            assert(forall|j:int| #![auto] 0<=j<i ==> self@[j] == 0);
            self.set(i,0);
            assert(self@ =~= tmp@.update(i as int,0));
            assert(forall|j:int| #![auto] 0<=j<i ==> self@[j] == 0);
        }
    }
}

impl<const N: usize> Array<usize, N> {

    pub fn init2zero(&mut self)
        requires
            old(self).wf(),
            N <= usize::MAX,
        ensures
            forall|index:int| 0<= index < N ==> #[trigger] self@[index] == 0,
            self.wf(),
    {
        let mut i = 0;
        for i in 0..N
            invariant
                N <= usize::MAX,
                0<=i<=N,
                self.wf(),
                forall|j:int| #![auto] 0<=j<i ==> self@[j] == 0,
        {
            let tmp:Ghost<Seq<usize>> = Ghost(self@);
            assert(forall|j:int| #![auto] 0<=j<i ==> self@[j] == 0);
            self.set(i,0);
            assert(self@ =~= tmp@.update(i as int,0));
            assert(forall|j:int| #![auto] 0<=j<i ==> self@[j] == 0);
        }
    }
}

impl<T: Copy, const N: usize> Array<Option<T>, N> {

    pub fn init2none(&mut self)
        requires
            old(self).wf(),
            N <= usize::MAX,
        ensures
            forall|index:int| 0<= index < N ==> #[trigger] self@[index] is None,
            self.wf(),
    {
        let mut i = 0;
        for i in 0..N
            invariant
                N <= usize::MAX,
                0<=i<=N,
                self.wf(),
                forall|j:int| #![auto] 0<=j<i ==> self@[j] is None,
        {
            let tmp:Ghost<Seq<Option<T>>> = Ghost(self@);
            assert(forall|j:int| #![auto] 0<=j<i ==> self@[j] is None);
            self.set(i,None);
            assert(self@ =~= tmp@.update(i as int,None));
            assert(forall|j:int| #![auto] 0<=j<i ==> self@[j] is None);
        }
    }
}


fn test<const N: usize>(ar: &mut Array<u64, N>)
    requires
        old(ar).wf(),
        old(ar)[1] == 0,
        N == 2,

    {
    let v_1 = ar.get(1);
    assert(v_1 == 0);
    ar.set(0,1);
    let v_0 = ar.get(0);
    assert(v_0 == 1);
    let v_1_new = ar.get(1);
    // assert(v_1_new != 0); // this should fail
    }

}
