use vstd::prelude::*;
verus! {
use core::mem::MaybeUninit;

/// A fixed-size array whose spec view is its own elements, so no ghost copy can disagree with them; `ar` stays public for
/// the raw-pointer TCB accessors and the inline view.
#[repr(C)]
pub struct Array<A, const N: usize> {
    pub ar: [A; N],
}

impl<A, const N: usize> Array<A, N> {
    pub fn get(&self, i: usize) -> (out: &A)
        requires
            0 <= i < N,
            self.wf(),
        ensures
            *out == self.view().spec_index(i as int),
    {
        &self.ar[i]
    }

    #[verifier(inline)]
    pub open spec fn spec_index(self, i: usize) -> A
        recommends
            self.view().len() == N,
            0 <= i < N,
    {
        self.view().spec_index(i as int)
    }

    #[verifier(inline)]
    pub open spec fn view(&self) -> Seq<A> { self.ar.view() }
    pub open spec fn wf(&self) -> bool { self.view().len() == N }

    pub fn set(&mut self, i: usize, out: A)
        requires
            0 <= i < N,
            old(self).wf(),
        ensures
            final(self).view() =~= old(self).view().update(i as int, out),
            final(self).wf(),
    {
        self.ar[i] = out;
    }
}

impl<A: Copy, const N: usize> Array<A, N> {
    pub fn new_with_init_value(v: A) -> (ret: Self)
        ensures
            ret.wf(),
            ret.view() == Seq::new(N as nat, |i: int| { v }),
    {
        let ret = Self { ar: [v; N] };
        assert(ret.view() =~= Seq::new(N as nat, |i: int| { v }));
        ret
    }
}

/// An array filled in index order, for elements that are not `Copy`; `finish` yields the `Array` once all `N` are pushed.
#[verifier::external_body]
#[verifier::reject_recursive_types(A)]
pub struct ArrayBuilder<A, const N: usize> {
    buf: [MaybeUninit<A>; N],
    len: usize,
}

impl<A, const N: usize> ArrayBuilder<A, N> {
    /// The elements pushed so far, in order.
    pub uninterp spec fn view(&self) -> Seq<A>;

    /// TCB: an empty builder; no element is initialized and `len` is 0.
    #[verifier::external_body]
    pub fn new() -> (ret: Self)
        ensures
            ret.view() == Seq::<A>::empty(),
    {
        Self { buf: unsafe { MaybeUninit::<[MaybeUninit<A>; N]>::uninit().assume_init() }, len: 0 }
    }

    /// TCB: initializes element `len` (`len == view().len()` is kept by these three functions only).
    #[verifier::external_body]
    pub fn push(&mut self, v: A)
        requires
            old(self).view().len() < N,
        ensures
            final(self).view() == old(self).view().push(v),
    {
        self.buf[self.len].write(v);
        self.len = self.len + 1;
    }

    /// TCB: all `N` elements are initialized, so the buffer is read out as `[A; N]`.
    #[verifier::external_body]
    pub fn finish(self) -> (ret: Array<A, N>)
        requires
            self.view().len() == N,
        ensures
            ret.wf(),
            ret.view() == self.view(),
    {
        Array { ar: unsafe { (&self.buf as *const [MaybeUninit<A>; N] as *const [A; N]).read() } }
    }
}
}
