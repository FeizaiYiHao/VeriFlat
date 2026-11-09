#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::*;

verus! {
pub proof fn container_allocator_2m_forward_wf_at(containers: ContainerLockedMap,
    allocators_4k: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_4K>, allocators_2m: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_2M>,
    allocators_1g: PageAllocatorUnLockedMap<ALLOCATOR_SIZE_1G>, allocator: RwLockPageAllocatorPtr)
    requires
        container_allocator_wf(containers, allocators_4k, allocators_2m, allocators_1g),
        allocators_2m.dom().contains(allocator),
    ensures
        containers.dom().contains(allocators_2m.spec_index(allocator).owning_container),
        containers.spec_index(allocators_2m.spec_index(allocator).owning_container).view_rodata().view().allocator_ptr_2m == allocator,
{ reveal(container_allocator_wf); }
}
