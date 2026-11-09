#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::simple_pptr::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use vstd::{assert_sets_equal, assert_sets_equal_internal, assert_maps_equal, assert_maps_equal_internal};

verus! {
impl<const SIZE: usize> UnLockedMap<usize, PageAllocator<SIZE>> {
    pub proof fn merge_2m_sort_source_eof_implies_wf_and_alignment(pre: Self, post: Self,
        allocator: RwLockPageAllocatorPtr, source: u8, quota_locks: Map<RwLockPageAllocatorPtr, TypedHeldLock>,
        cache_locks: Map<(RwLockPageAllocatorPtr, CpuId), TypedHeldLock>, pool_locks: Map<RwLockPageAllocatorPtr, TypedHeldLock>, thread: LockThreadId)
        requires
            pre.perms_wf(),
            pre.dom().contains(allocator),
            pre.spec_index(allocator).wf(),
            (source as usize) <= NUM_CPUS,
            pre.typed_quota_lock_map_aligned(quota_locks, thread),
            pre.typed_cache_lock_map_aligned(cache_locks, thread),
            pre.typed_global_pool_lock_map_aligned(pool_locks, thread),
            Self::merge_2m_sort_source_eof_transition_framing(pre, post, allocator, source),
            post.spec_index(allocator).cpu_caches.inv(),
            post.spec_index(allocator).merge_2m_source_list(source as usize).wf(),
        ensures
            post.perms_wf(),
            post.unchanged_except(&pre, allocator),
            post.spec_index(allocator).wf(),
            post.typed_quota_lock_map_aligned(quota_locks, thread),
            post.typed_cache_lock_map_aligned(cache_locks, thread),
            post.typed_global_pool_lock_map_aligned(pool_locks, thread),
    {
        let before = pre.spec_index(allocator);
        let after = post.spec_index(allocator);
        assert(post.dom() == pre.dom()) by { assert_sets_equal!(post.dom(), pre.dom()); }
        if (source as usize) < NUM_CPUS {
            assert(after.total_free_pages_wf()) by {
                before.cpu_caches.view_index_eq_element_value(); after.cpu_caches.view_index_eq_element_value();
                lemma_cache_len_fold_congruence(before.cpu_caches.view(), after.cpu_caches.view());
            };
        }
        assert(post.typed_quota_lock_map_aligned(quota_locks, thread)
            && post.typed_cache_lock_map_aligned(cache_locks, thread)
            && post.typed_global_pool_lock_map_aligned(pool_locks, thread)) by {
            reveal(UnLockedMap::typed_quota_lock_map_aligned);
            reveal(UnLockedMap::typed_cache_lock_map_aligned);
            reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
        };
    }

    pub proof fn typed_cache_lock_map_aligned_wf_at(&self,
        held: Map<(RwLockPageAllocatorPtr, CpuId), TypedHeldLock>, thread: LockThreadId, allocator: RwLockPageAllocatorPtr, cpu: CpuId)
        requires
            self.typed_cache_lock_map_aligned(held, thread),
        ensures
            typed_lock_map_contains_mode(held, (allocator, cpu), TypedLockMode::Write) == {
                &&& self.dom().contains(allocator)
                &&& index_valid(NUM_CPUS, cpu)
                &&& self.spec_index(allocator).cpu_caches.spec_index(cpu).view().wlocked_by_thread(thread)
            },
    { reveal(UnLockedMap::typed_cache_lock_map_aligned); }

    pub proof fn typed_global_pool_lock_map_aligned_wf_at(&self,
        held: Map<RwLockPageAllocatorPtr, TypedHeldLock>, thread: LockThreadId, allocator: RwLockPageAllocatorPtr)
        requires
            self.typed_global_pool_lock_map_aligned(held, thread),
        ensures
            typed_lock_map_contains_mode(held, allocator, TypedLockMode::Write) == {
                &&& self.dom().contains(allocator)
                &&& self.spec_index(allocator).global_pool.wlocked_by_thread(thread)
            },
    { reveal(UnLockedMap::typed_global_pool_lock_map_aligned); }

    pub proof fn merge_2m_remove_source_eof_implies_wf_and_alignment(pre: Self, post: Self,
        allocator: RwLockPageAllocatorPtr, source: u8, node: usize, node_perm: PointsTo<Node<PagePtr>>,
        quota_locks: Map<RwLockPageAllocatorPtr, TypedHeldLock>, cache_locks: Map<(RwLockPageAllocatorPtr, CpuId), TypedHeldLock>,
        pool_locks: Map<RwLockPageAllocatorPtr, TypedHeldLock>, thread: LockThreadId)
        requires
            pre.perms_wf(),
            pre.dom().contains(allocator),
            pre.spec_index(allocator).wf(),
            (source as usize) <= NUM_CPUS,
            pre.spec_index(allocator).merge_2m_source_list(source as usize).dom().contains(node),
            pre.typed_quota_lock_map_aligned(quota_locks, thread),
            pre.typed_cache_lock_map_aligned(cache_locks, thread),
            pre.typed_global_pool_lock_map_aligned(pool_locks, thread),
            Self::merge_2m_remove_source_eof_transition_framing(pre, post, allocator, source, node, node_perm),
            post.spec_index(allocator).cpu_caches.inv(),
            post.spec_index(allocator).merge_2m_source_list(source as usize).wf(),
        ensures
            post.perms_wf(),
            post.unchanged_except(&pre, allocator),
            post.spec_index(allocator).wf(),
            post.spec_index(allocator).merge_2m_source_list(source as usize).map()
                == pre.spec_index(allocator).merge_2m_source_list(source as usize).map().filter_keys(|key: usize|
                    pre.spec_index(allocator).merge_2m_source_list(source as usize).map().spec_index(key) != node_perm.value().view()),
            forall|value: PagePtr| #![trigger post.spec_index(allocator).merge_2m_source_list(source as usize).view().contains(value)]
                #![trigger pre.spec_index(allocator).merge_2m_source_list(source as usize).view().contains(value)]
                post.spec_index(allocator).merge_2m_source_list(source as usize).view().contains(value)
                    == (pre.spec_index(allocator).merge_2m_source_list(source as usize).view().contains(value) && value != node_perm.value().view()),
            LinkedList::<PagePtr, 233>::values_sorted(pre.spec_index(allocator).merge_2m_source_list(source as usize).view())
                ==> LinkedList::<PagePtr, 233>::values_sorted(post.spec_index(allocator).merge_2m_source_list(source as usize).view()),
            post.typed_quota_lock_map_aligned(quota_locks, thread),
            post.typed_cache_lock_map_aligned(cache_locks, thread),
            post.typed_global_pool_lock_map_aligned(pool_locks, thread),
    {
        let before = pre.spec_index(allocator);
        let after = post.spec_index(allocator);
        assert(post.dom() == pre.dom()) by { assert_sets_equal!(post.dom(), pre.dom()); }
        before.merge_2m_source_list(source as usize).wf_implies_view_len_eq_len();
        after.merge_2m_source_list(source as usize).wf_implies_view_len_eq_len();
        let value = node_perm.value().view();
        assert_maps_equal!(after.merge_2m_source_list(source as usize).map(), before.merge_2m_source_list(source as usize).map().filter_keys(|key: usize|
            before.merge_2m_source_list(source as usize).map().spec_index(key) != value), key => {
            if before.merge_2m_source_list(source as usize).map().dom().contains(key)
                && before.merge_2m_source_list(source as usize).map().spec_index(key) == value {
                before.merge_2m_source_list(source as usize).wf_and_equal_values_implies_equal_addrs(key, node);
            }
        });
        lemma_seq_remove_value_membership::<PagePtr>();
        if (source as usize) < NUM_CPUS {
            assert(after.total_free_pages_wf()) by { lemma_cache_len_fold_change_one_array(before.cpu_caches, after.cpu_caches, source as usize); };
        }
        if LinkedList::<PagePtr, 233>::values_sorted(before.merge_2m_source_list(source as usize).view()) {
            assert(LinkedList::<PagePtr, 233>::values_sorted(after.merge_2m_source_list(source as usize).view())) by {
                let values = before.merge_2m_source_list(source as usize).view();
                let value = before.merge_2m_source_list(source as usize).map().spec_index(node);
                values.index_of_first_ensures(value);
                if values.index_of_first(value) is Some { values.remove_ensures(values.index_of_first(value).unwrap()); }
            };
        }
        assert(post.typed_quota_lock_map_aligned(quota_locks, thread)
            && post.typed_cache_lock_map_aligned(cache_locks, thread)
            && post.typed_global_pool_lock_map_aligned(pool_locks, thread)) by {
            reveal(UnLockedMap::typed_quota_lock_map_aligned);
            reveal(UnLockedMap::typed_cache_lock_map_aligned);
            reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
        };
    }
}
}
