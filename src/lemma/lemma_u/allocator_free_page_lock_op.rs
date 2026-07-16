use vstd::prelude::*;
use crate::*;
use crate::kernel::*;
verus! {

pub proof fn lemma_container_allocator_free_4k_page_wf_preserved_for_lock_op(
    pre: KernelK,
    post: KernelK,
)
    requires
        container_allocator_free_4k_page_wf(pre.container_map, pre.allocator_4k_map, pre.page_array),
        container_page_owner_wf(pre.container_map, pre.page_array),
        container_allocator_wf(pre.container_map, pre.allocator_4k_map, pre.allocator_2m_map, pre.allocator_1g_map),
        page_array_wf(pre.page_array),
        post.page_array == pre.page_array,
        post.container_map.dom() == pre.container_map.dom(),
        forall|c: RwLockContainerPtr|
            #![trigger post.container_map.spec_index(c).view_rodata()]
            post.container_map.dom().contains(c) ==>
                post.container_map.spec_index(c).view_rodata() == pre.container_map.spec_index(c).view_rodata(),
        post.allocator_4k_map.dom() == pre.allocator_4k_map.dom(),
        forall|a: RwLockPageAllocatorPtr|
            #![trigger post.allocator_4k_map.spec_index(a).owning_container]
            post.allocator_4k_map.dom().contains(a) ==>
                post.allocator_4k_map.spec_index(a).owning_container == pre.allocator_4k_map.spec_index(a).owning_container
                && post.allocator_4k_map.spec_index(a).global_pool.view() == pre.allocator_4k_map.spec_index(a).global_pool.view(),
        forall|a: RwLockPageAllocatorPtr, i: CpuId|
            #![trigger post.allocator_4k_map.spec_index(a).cpu_caches.spec_index(i).view().view()]
            post.allocator_4k_map.dom().contains(a) && cpu_id_valid(i) ==>
                post.allocator_4k_map.spec_index(a).cpu_caches.spec_index(i).view().view()
                    == pre.allocator_4k_map.spec_index(a).cpu_caches.spec_index(i).view().view(),
    ensures
        container_allocator_free_4k_page_wf(post.container_map, post.allocator_4k_map, post.page_array),
{
    reveal(container_allocator_free_4k_page_wf);
    reveal(container_page_owner_wf);
    reveal(container_allocator_wf);
    reveal(page_array_wf);

    assert forall|page_index: PageIndex|
        #![trigger post.page_array.spec_index(page_index).view().view().state]
        page_index_wf(page_index)
    implies {
        let owner = post.page_array.spec_index(page_index).view().view().owning_container;
        let alloc = post.container_map.spec_index(owner).view_rodata().view().allocator_ptr_4k;
        &&& post.page_array.spec_index(page_index).view().view().state matches PageState::Free4k { state: FreePageAllocatorState::GlobalList }
            ==> post.allocator_4k_map.spec_index(alloc).global_pool.view().view().contains(page_index2page_ptr(page_index))
                && post.allocator_4k_map.spec_index(alloc).global_pool.view().map().spec_index(post.page_array.spec_index(page_index).view().view().free_list_node_storage.addr())
                    == page_index2page_ptr(page_index)
                && post.allocator_4k_map.spec_index(alloc).owning_container == post.page_array.spec_index(page_index).view().view().owning_container
        &&& post.page_array.spec_index(page_index).view().view().state matches PageState::Free4k { state: FreePageAllocatorState::PreCpuCache { cpu_id } }
            ==> post.allocator_4k_map.dom().contains(alloc)
                && post.allocator_4k_map.spec_index(alloc).cpu_caches.spec_index(cpu_id).view().view().view().contains(page_index2page_ptr(page_index))
                && post.allocator_4k_map.spec_index(alloc).cpu_caches.spec_index(cpu_id).view().view().map().spec_index(post.page_array.spec_index(page_index).view().view().free_list_node_storage.addr())
                    == page_index2page_ptr(page_index)
                && post.allocator_4k_map.spec_index(alloc).owning_container == post.page_array.spec_index(page_index).view().view().owning_container
    } by {
        assert(post.page_array.spec_index(page_index) == pre.page_array.spec_index(page_index));
        assert(pre.page_array.spec_index(page_index).view().view().state
            == post.page_array.spec_index(page_index).view().view().state);
        let owner = pre.page_array.spec_index(page_index).view().view().owning_container;
        assert(page_index_valid(page_index));
        assert(pre.container_map.dom().contains(owner));
        assert(post.container_map.spec_index(owner).view_rodata() == pre.container_map.spec_index(owner).view_rodata());
        let alloc = pre.container_map.spec_index(owner).view_rodata().view().allocator_ptr_4k;
        assert(pre.allocator_4k_map.dom().contains(alloc));
        assert(post.allocator_4k_map.spec_index(alloc).owning_container == pre.allocator_4k_map.spec_index(alloc).owning_container);
        assert(post.allocator_4k_map.spec_index(alloc).global_pool.view() == pre.allocator_4k_map.spec_index(alloc).global_pool.view());
        assert(pre.page_array.spec_index(page_index)@@.inv());
        assert forall|i: CpuId| #![trigger post.allocator_4k_map.spec_index(alloc).cpu_caches.spec_index(i)] cpu_id_valid(i) implies
            post.allocator_4k_map.spec_index(alloc).cpu_caches.spec_index(i).view().view()
                == pre.allocator_4k_map.spec_index(alloc).cpu_caches.spec_index(i).view().view() by {};
    };

    assert forall|alloc_ptr: RwLockPageAllocatorPtr, page_ptr: PagePtr|
        #![trigger post.allocator_4k_map.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr)]
        post.allocator_4k_map.dom().contains(alloc_ptr) && post.allocator_4k_map.spec_index(alloc_ptr).global_pool.view().view().contains(page_ptr)
    implies
        (post.page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state matches PageState::Free4k { state: FreePageAllocatorState::GlobalList })
        && post.page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == post.allocator_4k_map.spec_index(alloc_ptr).owning_container
    by {
        assert(pre.allocator_4k_map.dom().contains(alloc_ptr));
        assert(post.allocator_4k_map.spec_index(alloc_ptr).owning_container == pre.allocator_4k_map.spec_index(alloc_ptr).owning_container);
        assert(pre.allocator_4k_map.spec_index(alloc_ptr).global_pool.view() == post.allocator_4k_map.spec_index(alloc_ptr).global_pool.view());
        assert(post.page_array.spec_index(page_ptr2page_index(page_ptr)) == pre.page_array.spec_index(page_ptr2page_index(page_ptr)));
    };

    assert forall|alloc_ptr: RwLockPageAllocatorPtr, cpu_i: CpuId, page_ptr: PagePtr|
        #![trigger post.allocator_4k_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)]
        post.allocator_4k_map.dom().contains(alloc_ptr) && cpu_id_valid(cpu_i)
        && post.allocator_4k_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view().view().contains(page_ptr)
    implies
        (post.page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state matches PageState::Free4k { state: FreePageAllocatorState::PreCpuCache { cpu_id }})
        && post.page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == post.allocator_4k_map.spec_index(alloc_ptr).owning_container
    by {
        assert(pre.allocator_4k_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view()
            == post.allocator_4k_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().view());
        assert(post.allocator_4k_map.spec_index(alloc_ptr).owning_container == pre.allocator_4k_map.spec_index(alloc_ptr).owning_container);
        assert(post.page_array.spec_index(page_ptr2page_index(page_ptr)) == pre.page_array.spec_index(page_ptr2page_index(page_ptr)));
    };
}

}
