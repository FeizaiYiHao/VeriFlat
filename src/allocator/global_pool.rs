use vstd::prelude::*;
use vstd::simple_pptr::*;

use crate::*;
verus! {
pub struct GlobalPool<const SIZE: usize> {
    pub linked_list: LinkedList<PagePtr, 233>,
}

impl<const SIZE: usize> LockOwnerIdTrait for GlobalPool<SIZE> {
    open spec fn container_depth(&self) -> LockOwnerId { LockOwnerId::None }
    open spec fn process_depth(&self) -> LockOwnerId { LockOwnerId::None }
}

impl<const SIZE: usize> LockInvTrait for GlobalPool<SIZE> {
    open spec fn inv(&self) -> bool { self.wf() }
}

impl<const SIZE: usize> LockMajorTrait for GlobalPool<SIZE> {
    open spec fn lock_major_1(&self) -> LockMajorId { allocator_global_pool_major(SIZE) }
    open spec fn lock_major_2(&self) -> LockMajorId { 233 }
    open spec fn lock_major_3(&self) -> LockMajorId { 233 }
    open spec fn lock_major_default(&self) -> LockMajorId { 233 }
    open spec fn lock_major_1_predicate(&self) -> bool { true }
    open spec fn lock_major_2_predicate(&self) -> bool { false }
    open spec fn lock_major_3_predicate(&self) -> bool { false }
    open spec fn lock_major_default_predicate(&self) -> bool { false }
}

impl<const SIZE: usize> LockMinorTrait for GlobalPool<SIZE> {
    open spec fn lock_minor(&self) -> LockMinorId { self.linked_list.lock_minor() }
}

impl<const SIZE: usize> LockIdTrait for GlobalPool<SIZE> {
    open spec fn lock_id(&self) -> LockId {
        LockId { container: self.container_depth(), process: self.process_depth(), major: self.current_lock_major(), minor: self.lock_minor() }
    }
}

impl<const SIZE: usize> GlobalPool<SIZE> {
    pub open spec fn wf(&self) -> bool {
        &&& self.linked_list.wf()
    }

    pub open spec fn view(&self) -> Seq<PagePtr> { self.linked_list.view() }
    pub open spec fn dom(&self) -> Set<PagePtr> { self.linked_list.dom() }
    pub open spec fn map(&self) -> Map<usize, PagePtr> { self.linked_list.map() }
    pub open spec fn spec_len(&self) -> usize { self.linked_list.view().len() as usize }

    #[verifier(when_used_as_spec(spec_len))]
    pub fn len(&self) -> (ret: usize)
        requires
            self.linked_list.wf(),
        ensures
            ret == self.linked_list.len(),
    { self.linked_list.len() }

    pub fn peek_head(&self) -> (ret: (usize, PagePtr))
        where PagePtr: Copy
        requires
            self.linked_list.wf(),
            self.linked_list.len() != 0,
        ensures
            self.linked_list.dom().contains(ret.0),
            self.linked_list.map().dom().contains(ret.0),
            ret.1 == self.linked_list.view().spec_index(0),
            ret.1 == self.linked_list.map().spec_index(ret.0),
    { self.linked_list.peek_head() }

    pub fn get(&self, index: usize) -> (ret: PagePtr)
        requires
            self.linked_list.wf(),
            index < self.linked_list.len(),
        ensures
            ret == self.linked_list.view().spec_index(index as int),
    { self.linked_list.get(index) }

    pub proof fn lemma_len_view(&self)
        requires
            self.linked_list.wf(),
        ensures
            self.linked_list.view().len() == self.linked_list.len(),
    { self.linked_list.lemma_len_view(); }
}
} // verus!
