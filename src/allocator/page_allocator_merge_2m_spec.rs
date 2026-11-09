#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::simple_pptr::*;
use crate::*;

verus! {
impl<const SIZE: usize> PageAllocator<SIZE> {
    pub open spec fn merge_2m_source_list(&self, source: usize) -> LinkedList<PagePtr, 233> {
        if source < NUM_CPUS { self.cpu_caches.spec_index(source).view().view().linked_list }
        else { self.global_pool.view().linked_list }
    }
}

impl<const SIZE: usize> UnLockedMap<usize, PageAllocator<SIZE>> {
    pub open spec fn merge_2m_sort_source_eof_transition_framing(pre: Self, post: Self,
        allocator: RwLockPageAllocatorPtr, source: u8) -> bool {
        let before = pre.spec_index(allocator);
        let after = post.spec_index(allocator);
        let before_list = before.merge_2m_source_list(source as usize);
        let after_list = after.merge_2m_source_list(source as usize);
        &&& post.view() == pre.view().insert(allocator, post.view().spec_index(allocator))
        &&& post.view().spec_index(allocator).is_init()
        &&& post.view().spec_index(allocator).addr() == allocator
        &&& after.quota == before.quota
        &&& after.owning_container == before.owning_container
        &&& after.total_free_pages == before.total_free_pages
        &&& after_list.length == before_list.length
        &&& after_list.view().len() == before_list.view().len()
        &&& after_list.map() == before_list.map()
        &&& after_list.dom() == before_list.dom()
        &&& after_list.view().to_set() == before_list.view().to_set()
        &&& after_list.container_depth == before_list.container_depth
        &&& after_list.minor == before_list.minor
        &&& LinkedList::<PagePtr, 233>::values_sorted(after_list.view())
        &&& forall|value: PagePtr| #![trigger after_list.view().contains(value)] #![trigger before_list.view().contains(value)]
            after_list.view().contains(value) == before_list.view().contains(value)
        &&& if (source as usize) < NUM_CPUS {
            let old_cache = before.cpu_caches.spec_index(source as usize).view();
            let new_cache = after.cpu_caches.spec_index(source as usize).view();
            &&& after.cpu_caches.entries_unchanged_except(&before.cpu_caches, source as usize)
            &&& after.global_pool == before.global_pool
            &&& new_cache.is_init() == old_cache.is_init()
            &&& new_cache.view_rodata() == old_cache.view_rodata()
            &&& new_cache.view_ghost() == old_cache.view_ghost()
            &&& new_cache.locking_thread() == old_cache.locking_thread()
            &&& new_cache.control() == old_cache.control()
            &&& new_cache.view().line_pad == old_cache.view().line_pad
        } else {
            &&& after.cpu_caches == before.cpu_caches
            &&& after.global_pool.is_init() == before.global_pool.is_init()
            &&& after.global_pool.view_rodata() == before.global_pool.view_rodata()
            &&& after.global_pool.view_ghost() == before.global_pool.view_ghost()
            &&& after.global_pool.locking_thread() == before.global_pool.locking_thread()
            &&& after.global_pool.control() == before.global_pool.control()
            &&& after.global_pool.view().line_pad == before.global_pool.view().line_pad
        }
    }

    pub open spec fn merge_2m_remove_source_eof_transition_framing(pre: Self, post: Self,
        allocator: RwLockPageAllocatorPtr, source: u8, node: usize, node_perm: PointsTo<Node<PagePtr>>) -> bool {
        let before = pre.spec_index(allocator);
        let after = post.spec_index(allocator);
        let before_list = before.merge_2m_source_list(source as usize);
        let after_list = after.merge_2m_source_list(source as usize);
        &&& post.view() == pre.view().insert(allocator, post.view().spec_index(allocator))
        &&& post.view().spec_index(allocator).is_init()
        &&& post.view().spec_index(allocator).addr() == allocator
        &&& after.quota == before.quota
        &&& after.owning_container == before.owning_container
        &&& after.total_free_pages.view() == before.total_free_pages.view() - 1
        &&& after_list.length == before_list.length - 1
        &&& after_list.view() == before_list.view().remove_value(before_list.map().spec_index(node))
        &&& after_list.map() == before_list.map().remove(node)
        &&& after_list.dom() == before_list.dom().remove(node)
        &&& after_list.container_depth == before_list.container_depth
        &&& after_list.minor == before_list.minor
        &&& node_perm.is_init()
        &&& node_perm.addr() == node
        &&& node_perm.value().view() == before_list.map().spec_index(node)
        &&& if (source as usize) < NUM_CPUS {
            let old_cache = before.cpu_caches.spec_index(source as usize).view();
            let new_cache = after.cpu_caches.spec_index(source as usize).view();
            &&& after.cpu_caches.entries_unchanged_except(&before.cpu_caches, source as usize)
            &&& after.global_pool == before.global_pool
            &&& new_cache.is_init() == old_cache.is_init()
            &&& new_cache.view_rodata() == old_cache.view_rodata()
            &&& new_cache.view_ghost() == old_cache.view_ghost()
            &&& new_cache.locking_thread() == old_cache.locking_thread()
            &&& new_cache.control() == old_cache.control()
            &&& new_cache.view().line_pad == old_cache.view().line_pad
        } else {
            &&& after.cpu_caches == before.cpu_caches
            &&& after.global_pool.is_init() == before.global_pool.is_init()
            &&& after.global_pool.view_rodata() == before.global_pool.view_rodata()
            &&& after.global_pool.view_ghost() == before.global_pool.view_ghost()
            &&& after.global_pool.locking_thread() == before.global_pool.locking_thread()
            &&& after.global_pool.control() == before.global_pool.control()
            &&& after.global_pool.view().line_pad == before.global_pool.view().line_pad
        }
    }
}
}
