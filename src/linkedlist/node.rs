use core::mem::MaybeUninit;

use vstd::prelude::*;
use vstd::simple_pptr::*;
verus! {
pub struct Node<T> {
    pub value: T,
    pub next: Option<usize>,
    pub prev: Option<usize>,
}

/// A list-node slot: the node lives at `addr` outside the value, and `perm` parks its permission while the node is unlinked.
pub struct ExternalNode<T> {
    addr: usize,
    perm: Tracked<Option<PointsTo<Node<T>>>>,
}

impl<T> Node<T> {
    pub open spec fn view(&self) -> T { self.value }
}

impl<T> ExternalNode<T> {
    pub closed spec fn spec_addr(&self) -> usize { self.addr }
    pub closed spec fn is_init(&self) -> bool {
        &&& self.perm.view() is Some
        &&& self.perm.view()->Some_0.addr() == self.addr
        &&& self.perm.view()->Some_0.is_init()
    }

    /// Park the permission of the initialized node at `addr`.
    pub fn new_parked(addr: usize, Tracked(perm): Tracked<PointsTo<Node<T>>>) -> (ret: Self)
        requires
            perm.addr() == addr,
            perm.is_init(),
        ensures
            ret.is_init(),
            ret.addr() == addr,
    {
        Self { addr, perm: Tracked(Some(perm)) }
    }

    #[verifier(when_used_as_spec(spec_addr))]
    pub fn addr(&self) -> (ret: usize)
        ensures
            ret == self.addr()
    {
        self.addr
    }

    pub fn take(&mut self) -> (ret: (usize, Tracked<PointsTo<Node<T>>>))
        requires
            old(self).is_init(),
        ensures
            final(self).is_init() == false,
            final(self).addr() == old(self).addr(),
            final(self).addr() == ret.0,
            ret.1.view().is_init(),
            ret.1.view().addr() == final(self).addr(),
    {
        let tracked perm = self.perm.borrow_mut().tracked_take();
        (self.addr, Tracked(perm))
    }

    pub fn put(&mut self, perm: Tracked<PointsTo<Node<T>>>)
        requires
            old(self).is_init() == false,
            old(self).addr() == perm.view().addr(),
            perm.view().is_init(),
        ensures
            final(self).is_init() == true,
            final(self).addr() == old(self).addr(),
    {
        let Tracked(perm) = perm;
        self.perm = Tracked(Some(perm));
    }
}

#[verifier(external_body)]
pub proof fn node_perm_disjoint<T, K, V>(tracked this: &mut PointsTo<Node<T>>, tracked others: &Map<K, PointsTo<Node<V>>>)
    ensures
        forall|k: K| #![trigger others.spec_index(k).addr()] others.dom().contains(k) ==> final(this).addr() != others.spec_index(k).addr(),
        *final(this) == *old(this),
{
}

#[verifier(external_body)]
pub fn node_update_value<T>(addr: usize, perm: &mut Tracked<PointsTo<Node<T>>>, value: T)
    requires
        old(perm).view().addr() == addr,
        old(perm).view().is_init(),
    ensures
        final(perm).view().is_init(),
        final(perm).view().addr() == old(perm).view().addr(),
        final(perm).view().value().view() == value,
        final(perm).view().value().prev == old(perm).view().value().prev,
        final(perm).view().value().next == old(perm).view().value().next,
{
    unsafe {
        let uptr = addr as *mut MaybeUninit<Node<T>>;
        (*uptr).assume_init_mut().value = value;
    }
}

#[verifier(external_body)]
pub fn node_update_prev<T>(addr: usize, perm: &mut Tracked<PointsTo<Node<T>>>, prev: Option<usize>)
    requires
        old(perm).view().addr() == addr,
        old(perm).view().is_init(),
    ensures
        final(perm).view().is_init(),
        final(perm).view().addr() == old(perm).view().addr(),
        final(perm).view().value().view() == old(perm).view().value().view(),
        final(perm).view().value().prev == prev,
        final(perm).view().value().next == old(perm).view().value().next,
{
    unsafe {
        let uptr = addr as *mut MaybeUninit<Node<T>>;
        (*uptr).assume_init_mut().prev = prev;
    }
}

#[verifier(external_body)]
pub fn node_update_next<T>(addr: usize, perm: &mut Tracked<PointsTo<Node<T>>>, next: Option<usize>)
    requires
        old(perm).view().addr() == addr,
        old(perm).view().is_init(),
    ensures
        final(perm).view().is_init(),
        final(perm).view().addr() == old(perm).view().addr(),
        final(perm).view().value().view() == old(perm).view().value().view(),
        final(perm).view().value().prev == old(perm).view().value().prev,
        final(perm).view().value().next == next,
{
    unsafe {
        let uptr = addr as *mut MaybeUninit<Node<T>>;
        (*uptr).assume_init_mut().next = next;
    }
}
}
