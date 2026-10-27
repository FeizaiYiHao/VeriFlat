use vstd::prelude::*;
use crate::*;
use vstd::simple_pptr::*;
verus! {
pub struct AllocatorCache<const SIZE: usize> {
    pub linked_list: LinkedList<PagePtr, 233>,
}

impl<const SIZE: usize> LockOwnerIdTrait for AllocatorCache<SIZE> {
    open spec fn container_depth(&self) -> LockOwnerId { LockOwnerId::None }
    open spec fn process_depth(&self) -> LockOwnerId { LockOwnerId::None }
}

impl<const SIZE: usize> LockInvTrait for AllocatorCache<SIZE> {
    open spec fn inv(&self) -> bool { self.wf() }
}

impl<const SIZE: usize> LockMajorTrait for AllocatorCache<SIZE> {
    open spec fn lock_major_1(&self) -> LockMajorId { allocator_cache_major(SIZE) }
    open spec fn lock_major_2(&self) -> LockMajorId { 233 }
    open spec fn lock_major_3(&self) -> LockMajorId { 233 }
    open spec fn lock_major_default(&self) -> LockMajorId { 233 }
    open spec fn lock_major_1_predicate(&self) -> bool { true }
    open spec fn lock_major_2_predicate(&self) -> bool { false }
    open spec fn lock_major_3_predicate(&self) -> bool { false }
    open spec fn lock_major_default_predicate(&self) -> bool { false }
}

impl<const SIZE: usize> AllocatorCache<SIZE> {
    pub open spec fn wf(&self) -> bool {
        &&& self.linked_list.wf()
        &&& self.watermark_wf()
    }

    pub open spec fn view(&self) -> Seq<PagePtr> { self.linked_list.view() }
    pub open spec fn dom(&self) -> Set<PagePtr> { self.linked_list.dom() }
    pub open spec fn map(&self) -> Map<usize, PagePtr> { self.linked_list.map() }
    pub open spec fn watermark_wf(&self) -> bool { ALLOCATOR_MIN_WATERMARK <= self.linked_list.view().len() <= ALLOCATOR_MAX_WATERMARK }
}
}
