use core::mem::MaybeUninit;

use vstd::prelude::*;
use vstd::simple_pptr::PointsTo;

use crate::*;

verus! {

pub struct ReadOnlyNode<V>{
    value: V, 
    owner_ptr: Ghost<usize>
}

pub struct ExternalReadOnlyNode<V>{
    storage: ReadOnlyNode<V>,
    is_init: Ghost<bool>,
    addr: Ghost<usize>,
}

impl<V> ReadOnlyNode<V>{
    pub closed spec fn view(&self) -> V {
        self.value
    }
    pub closed spec fn owner_addr(&self) -> usize{
        self.owner_ptr.view()
    }
    #[verifier(external_body)]
    pub fn new(v: V, owner_addr: Ghost<usize>) -> (ret :Self)
        ensures 
            ret.view() == v,
            ret.owner_addr() == owner_addr.view()
    {
        Self{
            value: v,
            owner_ptr: owner_addr
        }
    }
    #[verifier(external_body)]
    pub fn borrow(&self) -> (ret: &V)
        ensures
            ret == self.view()
    {
        &self.value
    }
}

impl<T> ExternalReadOnlyNode<T>{
    pub closed spec fn spec_addr(&self) -> usize {
        self.addr.view()
    }
    pub closed spec fn is_init(&self) -> bool {
        self.is_init.view()
    }

    #[verifier(when_used_as_spec(spec_addr))]
    #[verifier(external_body)]
    pub fn addr(&self) -> (ret:usize)
        ensures
            ret == self.addr()
    {
        &self.storage as *const ReadOnlyNode<T> as usize
    }

    #[verifier(external_body)]
    pub fn take(&mut self) -> (ret:(usize, Tracked<PointsTo<ReadOnlyNode<T>>>))
        requires
            old(self).is_init(),
        ensures
            final(self).is_init() == false,
            final(self).addr() == old(self).addr(),
            final(self).addr() == ret.0,
            ret.1.view().is_init(),
            ret.1.view().addr() == final(self).addr(),
    {
        (&self.storage as *const ReadOnlyNode<T> as usize, Tracked::assume_new())
    }
    #[verifier(external_body)]
    pub fn put(&mut self, perm: Tracked<PointsTo<ReadOnlyNode<T>>>)
        requires
            old(self).is_init() == false,
            old(self).addr() == perm.view().addr(),
            perm.view().is_init(),
        ensures
            final(self).is_init() == true,
            final(self).addr() == old(self).addr(),
    {
    }

}

impl<V: LockOwnerIdTrait> LockOwnerIdTrait for ReadOnlyNode<V>{
    open spec fn container_depth(&self) -> LockOwnerId {
        self.view().container_depth()
    }

    open spec fn process_depth(&self) -> LockOwnerId {
        self.view().process_depth()
    }
}

}
