use vstd::prelude::*;

use crate::*;

verus! {
pub struct ReadOnlyNode<V> { value: V }

impl<V> ReadOnlyNode<V> {
    pub closed spec fn view(&self) -> V { self.value }
    pub fn new(v: V) -> (ret: Self)
        ensures
            ret.view() == v
    {
        Self { value: v }
    }
    pub fn borrow(&self) -> (ret: &V)
        ensures
            ret == self.view()
    {
        &self.value
    }
}

impl<V: LockOwnerIdTrait> LockOwnerIdTrait for ReadOnlyNode<V> {
    open spec fn container_depth(&self) -> LockOwnerId { self.view().container_depth() }
    open spec fn process_depth(&self) -> LockOwnerId { self.view().process_depth() }
    open spec fn container_source(&self) -> OwnerSource { self.view().container_source() }
    open spec fn process_source(&self) -> OwnerSource { self.view().process_source() }
}
}
