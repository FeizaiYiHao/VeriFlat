use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::*;

verus! {
pub fn remove_shared_4k_mapping(page: &mut Page, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires
        old(page).inv(),
        old(page).state is Mapped4k,
        old(page).mappings().contains((pagetable_ptr, va)),
        old(page).ref_count > 1,
    ensures
        final(page).inv(),
        final(page).mappings() == old(page).mappings().remove((pagetable_ptr, va)),
        final(page).ref_count == old(page).ref_count - 1,
        *final(page) == (Page { mappings: final(page).mappings, ref_count: final(page).ref_count, ..*old(page) }),
{
    page.mappings = Ghost(page.mappings().remove((pagetable_ptr, va)));
    page.ref_count = page.ref_count - 1;
    proof { reveal(Page::mappings_va_valid); assert(page.iommu_mappings() == old(page).iommu_mappings()); }
}

pub fn remove_last_4k_mapping_to_cache(page: &mut Page, pagetable_ptr: RwLockPageTableRoot, va: VAddr, allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId) -> (ret: (usize, Tracked<PointsTo<Node<PagePtr>>>))
    requires
        old(page).inv(),
        old(page).state is Mapped4k,
        !old(page).is_io_page,
        old(page).mappings().contains((pagetable_ptr, va)),
        old(page).ref_count == 1,
        index_valid(NUM_CPUS, cpu_id),
    ensures
        final(page).inv(),
        final(page).state == (PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } }),
        final(page).mappings() == Set::<(RwLockPageTableRoot, VAddr)>::empty(),
        final(page).mappings() == old(page).mappings().remove((pagetable_ptr, va)),
        final(page).ref_count == 0,
        ret.0 == old(page).free_list_node_storage.addr(),
        ret.1.view().is_init(),
        ret.1.view().addr() == ret.0,
        ret.1.view().value().view() == old(page).addr,
        final(page).free_list_node_storage.addr() == old(page).free_list_node_storage.addr(),
        *final(page) == (Page { state: final(page).state, mappings: final(page).mappings, ref_count: 0, free_list_node_storage: final(page).free_list_node_storage, ..*old(page) }),
{
    proof { reveal(Page::mappings_va_valid); }
    let (node_addr, mut node_perm) = page.free_list_node_storage.take();
    node_update_value(node_addr, &mut node_perm, page.addr);
    page.mappings = Ghost(Set::empty());
    page.ref_count = 0;
    page.state = PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } };
    (node_addr, node_perm)
}

pub fn remove_last_4k_io_mapping(page: &mut Page, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires
        old(page).inv(),
        old(page).state is Mapped4k,
        old(page).is_io_page,
        old(page).mappings().contains((pagetable_ptr, va)),
        old(page).ref_count == 1,
    ensures
        final(page).inv(),
        final(page).state is Unavailable,
        final(page).mappings() == Set::<(RwLockPageTableRoot, VAddr)>::empty(),
        final(page).mappings() == old(page).mappings().remove((pagetable_ptr, va)),
        final(page).ref_count == 0,
        final(page).perm_4k.view() is None,
        *final(page) == (Page { state: PageState::Unavailable, mappings: final(page).mappings, ref_count: 0, perm_4k: final(page).perm_4k, ..*old(page) }),
{
    proof {
        reveal(Page::mappings_va_valid);
        let tracked _retired_perm = page.perm_4k.borrow_mut().tracked_take();
    }
    page.mappings = Ghost(Set::empty());
    page.ref_count = 0;
    page.state = PageState::Unavailable;
}
}

verus! {
pub fn remove_shared_4k_iommu_mapping(page: &mut Page, iommu_table_ptr: RwLockPageTableRoot, iova: VAddr)
    requires
        old(page).inv(),
        old(page).state is Mapped4k,
        old(page).iommu_mappings().contains((iommu_table_ptr, iova)),
        old(page).ref_count > 1,
    ensures
        final(page).inv(),
        final(page).iommu_mappings() == old(page).iommu_mappings().remove((iommu_table_ptr, iova)),
        final(page).ref_count == old(page).ref_count - 1,
        *final(page) == (Page { iommu_mappings: final(page).iommu_mappings, ref_count: final(page).ref_count, ..*old(page) }),
{
    page.iommu_mappings = Ghost(page.iommu_mappings().remove((iommu_table_ptr, iova)));
    page.ref_count = page.ref_count - 1;
    proof { reveal(Page::mappings_va_valid); assert(page.mappings() == old(page).mappings()); }
}

pub fn remove_last_4k_iommu_mapping_to_cache(page: &mut Page, iommu_table_ptr: RwLockPageTableRoot, iova: VAddr, allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId) -> (ret: (usize, Tracked<PointsTo<Node<PagePtr>>>))
    requires
        old(page).inv(),
        old(page).state is Mapped4k,
        !old(page).is_io_page,
        old(page).iommu_mappings().contains((iommu_table_ptr, iova)),
        old(page).ref_count == 1,
        index_valid(NUM_CPUS, cpu_id),
    ensures
        final(page).inv(),
        final(page).state == (PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } }),
        final(page).iommu_mappings() == Set::<(RwLockPageTableRoot, VAddr)>::empty(),
        final(page).iommu_mappings() == old(page).iommu_mappings().remove((iommu_table_ptr, iova)),
        final(page).mappings() == Set::<(RwLockPageTableRoot, VAddr)>::empty(),
        final(page).ref_count == 0,
        ret.0 == old(page).free_list_node_storage.addr(),
        ret.1.view().is_init(),
        ret.1.view().addr() == ret.0,
        ret.1.view().value().view() == old(page).addr,
        final(page).free_list_node_storage.addr() == old(page).free_list_node_storage.addr(),
        *final(page) == (Page { state: final(page).state, iommu_mappings: final(page).iommu_mappings, ref_count: 0, free_list_node_storage: final(page).free_list_node_storage, ..*old(page) }),
{
    proof { reveal(Page::mappings_va_valid); }
    let (node_addr, mut node_perm) = page.free_list_node_storage.take();
    node_update_value(node_addr, &mut node_perm, page.addr);
    page.iommu_mappings = Ghost(Set::empty());
    page.ref_count = 0;
    page.state = PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } };
    (node_addr, node_perm)
}

pub fn remove_last_4k_iommu_io_mapping(page: &mut Page, iommu_table_ptr: RwLockPageTableRoot, iova: VAddr)
    requires
        old(page).inv(),
        old(page).state is Mapped4k,
        old(page).is_io_page,
        old(page).iommu_mappings().contains((iommu_table_ptr, iova)),
        old(page).ref_count == 1,
    ensures
        final(page).inv(),
        final(page).state is Unavailable,
        final(page).iommu_mappings() == Set::<(RwLockPageTableRoot, VAddr)>::empty(),
        final(page).iommu_mappings() == old(page).iommu_mappings().remove((iommu_table_ptr, iova)),
        final(page).ref_count == 0,
        final(page).perm_4k.view() is None,
        *final(page) == (Page { state: PageState::Unavailable, iommu_mappings: final(page).iommu_mappings, ref_count: 0, perm_4k: final(page).perm_4k, ..*old(page) }),
{
    proof {
        reveal(Page::mappings_va_valid);
        let tracked _retired_perm = page.perm_4k.borrow_mut().tracked_take();
    }
    page.iommu_mappings = Ghost(Set::empty());
    page.ref_count = 0;
    page.state = PageState::Unavailable;
}
}
