use core::mem::MaybeUninit;

use vstd::prelude::*;
use vstd::simple_pptr::*;
verus! {

pub struct Node<T>{
    pub value: T,
    pub next: Option<usize>,
    pub prev: Option<usize>,
}

pub struct ExternalNode<T>{
    storage: Node<T>,
    is_init: Ghost<bool>,
    addr: Ghost<usize>,
}

impl<T> Node<T>{
    pub open spec fn view(&self) -> T {
        self.value
    }
}

impl<T> ExternalNode<T>{
    pub closed spec fn spec_addr(&self) -> usize {
        self.addr@
    }
    pub closed spec fn is_init(&self) -> bool {
        self.is_init@
    }

    #[verifier(when_used_as_spec(spec_addr))]
    #[verifier(external_body)]
    pub fn addr(&self) -> (ret:usize)
        ensures
            ret == self.addr()
    {
        &self.storage as *const Node<T> as usize
    }

    #[verifier(external_body)]
    pub fn take(&mut self) -> (ret:(usize, Tracked<PointsTo<Node<T>>>))
        requires
            old(self).is_init(),
        ensures
            self.is_init() == false,
            self.addr() == old(self).addr(),
            self.addr() == ret.0,
            ret.1@.is_init(),
            ret.1@.addr() == self.addr(),
    {
        (&self.storage as *const Node<T> as usize, Tracked::assume_new())
    }
    #[verifier(external_body)]
    pub fn put(&mut self, perm: Tracked<PointsTo<Node<T>>>)
        requires
            old(self).is_init() == false,
            old(self).addr() == perm@.addr(),
            perm@.is_init(),
        ensures
            self.is_init() == true,
            self.addr() == old(self).addr(),
    {
    }
}

#[verifier(external_body)]
pub broadcast proof fn node_has_size<T>()
    ensures
        #![trigger size_of::<Node<T>>()]
        size_of::<Node<T>>() != 0,
{
}
#[verifier(external_body)]
pub proof fn node_perm_disjoint<T,K,V>(tracked this: &mut PointsTo<Node<T>>, tracked others: &Map<K, PointsTo<Node<V>>>)
    ensures 
        forall|k:K| 
            #![trigger others[k].addr()] 
            others.dom().contains(k) 
            ==> 
            this.addr() != others[k].addr(),
        *this == *old(this),
{
}

#[verifier(external_body)]
pub fn node_update_value<T>(addr:usize, perm: &mut Tracked<PointsTo<Node<T>>>, value: T)
    requires
        old(perm)@.addr() == addr,
        old(perm)@.is_init(),
    ensures
        perm@.is_init(),
        perm@.addr() == old(perm)@.addr(),
        perm@.value()@ == value,
        perm@.value().prev == old(perm)@.value().prev,
        perm@.value().next == old(perm)@.value().next,
{
    unsafe {
        let uptr = addr as *mut MaybeUninit<Node<T>>;
        (*uptr).assume_init_mut().value = value;
    }
}

#[verifier(external_body)]
pub fn node_update_prev<T>(addr:usize, perm: &mut Tracked<PointsTo<Node<T>>>, prev: Option<usize>)
    requires
        old(perm)@.addr() == addr,
        old(perm)@.is_init(),
    ensures
        perm@.is_init(),
        perm@.addr() == old(perm)@.addr(),
        perm@.value()@ == old(perm)@.value()@,
        perm@.value().prev == prev,
        perm@.value().next == old(perm)@.value().next,
{
    unsafe {
        let uptr = addr as *mut MaybeUninit<Node<T>>;
        (*uptr).assume_init_mut().prev = prev;
    }
}

#[verifier(external_body)]
pub fn node_update_next<T>(addr:usize, perm: &mut Tracked<PointsTo<Node<T>>>, next: Option<usize>)
    requires
        old(perm)@.addr() == addr,
        old(perm)@.is_init(),
    ensures
        perm@.is_init(),
        perm@.addr() == old(perm)@.addr(),
        perm@.value()@ == old(perm)@.value()@,
        perm@.value().prev == old(perm)@.value().prev,
        perm@.value().next == next,
{
    unsafe {
        let uptr = addr as *mut MaybeUninit<Node<T>>;
        (*uptr).assume_init_mut().next = next;
    }
}

}