#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::*;

verus! {
impl<const SIZE: usize> UnLockedMap<usize, PageAllocator<SIZE>> {
    pub fn merge_2m_sort_source(&mut self, allocator: RwLockPageAllocatorPtr, source: u8,
        Ghost(quota_locks): Ghost<Map<RwLockPageAllocatorPtr, TypedHeldLock>>,
        Ghost(cache_locks): Ghost<Map<(RwLockPageAllocatorPtr, CpuId), TypedHeldLock>>,
        Ghost(pool_locks): Ghost<Map<RwLockPageAllocatorPtr, TypedHeldLock>>, Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&LockPerm>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(allocator),
            old(self).spec_index(allocator).wf(),
            (source as usize) <= NUM_CPUS,
            old(self).typed_quota_lock_map_aligned(quota_locks, lctx.thread_id()),
            old(self).typed_cache_lock_map_aligned(cache_locks, lctx.thread_id()),
            old(self).typed_global_pool_lock_map_aligned(pool_locks, lctx.thread_id()),
            lp.view().state() is WriteLock,
            lp.view().thread_id() == lctx.thread_id(),
            (source as usize) < NUM_CPUS ==> typed_lock_map_contains_mode(cache_locks, (allocator, source as usize), TypedLockMode::Write),
            (source as usize) < NUM_CPUS ==> lp.view().lock_id() == old(self).spec_index(allocator).cpu_caches.spec_index(source as usize).view().locking_thread()->Write_lock_id,
            source as usize == NUM_CPUS ==> typed_lock_map_contains_mode(pool_locks, allocator, TypedLockMode::Write),
            source as usize == NUM_CPUS ==> lp.view().lock_id() == old(self).spec_index(allocator).global_pool.locking_thread()->Write_lock_id,
        ensures
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), allocator),
            final(self).spec_index(allocator).wf(),
            final(self).spec_index(allocator).merge_2m_source_list(source as usize).map() == old(self).spec_index(allocator).merge_2m_source_list(source as usize).map(),
            final(self).spec_index(allocator).merge_2m_source_list(source as usize).dom() == old(self).spec_index(allocator).merge_2m_source_list(source as usize).dom(),
            final(self).spec_index(allocator).merge_2m_source_list(source as usize).length == old(self).spec_index(allocator).merge_2m_source_list(source as usize).length,
            final(self).spec_index(allocator).merge_2m_source_list(source as usize).view().len() == old(self).spec_index(allocator).merge_2m_source_list(source as usize).view().len(),
            final(self).spec_index(allocator).merge_2m_source_list(source as usize).view().to_set() == old(self).spec_index(allocator).merge_2m_source_list(source as usize).view().to_set(),
            forall|value: PagePtr| #![trigger final(self).spec_index(allocator).merge_2m_source_list(source as usize).view().contains(value)]
                #![trigger old(self).spec_index(allocator).merge_2m_source_list(source as usize).view().contains(value)]
                final(self).spec_index(allocator).merge_2m_source_list(source as usize).view().contains(value) == old(self).spec_index(allocator).merge_2m_source_list(source as usize).view().contains(value),
            LinkedList::<PagePtr, 233>::values_sorted(final(self).spec_index(allocator).merge_2m_source_list(source as usize).view()),
            final(self).spec_index(allocator).total_free_pages == old(self).spec_index(allocator).total_free_pages,
            final(self).spec_index(allocator).quota == old(self).spec_index(allocator).quota,
            final(self).spec_index(allocator).owning_container == old(self).spec_index(allocator).owning_container,
            Self::merge_2m_sort_source_eof_transition_framing(*old(self), *final(self), allocator, source),
            final(self).typed_quota_lock_map_aligned(quota_locks, lctx.thread_id()),
            final(self).typed_cache_lock_map_aligned(cache_locks, lctx.thread_id()),
            final(self).typed_global_pool_lock_map_aligned(pool_locks, lctx.thread_id()),
    {
        proof {
            if (source as usize) < NUM_CPUS {
                self.typed_cache_lock_map_aligned_wf_at(cache_locks, lctx.thread_id(), allocator, source as usize);
            } else { self.typed_global_pool_lock_map_aligned_wf_at(pool_locks, lctx.thread_id(), allocator); }
        }
        {
            let Tracked(perm) = self.borrow_perm_mut(allocator);
            let pptr = PPtr::<PageAllocator<SIZE>>::from_usize(allocator);
            if (source as usize) < NUM_CPUS {
                let cache = borrow_mut_cache(&pptr, Tracked(&mut *perm), source as usize, Tracked(lctx), lp);
                cache.linked_list.sort_page_ptrs();
            } else {
                let pool = borrow_mut_global_pool(&pptr, Tracked(&mut *perm), Tracked(lctx), lp);
                pool.linked_list.sort_page_ptrs();
            }
        }
        proof {
            Self::merge_2m_sort_source_eof_implies_wf_and_alignment(*old(self), *self, allocator, source,
                quota_locks, cache_locks, pool_locks, lctx.thread_id());
        }
    }

    pub fn merge_2m_remove_source(&mut self, allocator: RwLockPageAllocatorPtr, source: u8, node: usize,
        Ghost(quota_locks): Ghost<Map<RwLockPageAllocatorPtr, TypedHeldLock>>,
        Ghost(cache_locks): Ghost<Map<(RwLockPageAllocatorPtr, CpuId), TypedHeldLock>>,
        Ghost(pool_locks): Ghost<Map<RwLockPageAllocatorPtr, TypedHeldLock>>, Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&LockPerm>)
        -> (ret: (usize, Tracked<PointsTo<Node<PagePtr>>>))
        requires
            old(self).perms_wf(),
            old(self).dom().contains(allocator),
            old(self).spec_index(allocator).wf(),
            (source as usize) <= NUM_CPUS,
            old(self).spec_index(allocator).merge_2m_source_list(source as usize).dom().contains(node),
            old(self).typed_quota_lock_map_aligned(quota_locks, lctx.thread_id()),
            old(self).typed_cache_lock_map_aligned(cache_locks, lctx.thread_id()),
            old(self).typed_global_pool_lock_map_aligned(pool_locks, lctx.thread_id()),
            lp.view().state() is WriteLock,
            lp.view().thread_id() == lctx.thread_id(),
            (source as usize) < NUM_CPUS ==> typed_lock_map_contains_mode(cache_locks, (allocator, source as usize), TypedLockMode::Write),
            (source as usize) < NUM_CPUS ==> lp.view().lock_id() == old(self).spec_index(allocator).cpu_caches.spec_index(source as usize).view().locking_thread()->Write_lock_id,
            source as usize == NUM_CPUS ==> typed_lock_map_contains_mode(pool_locks, allocator, TypedLockMode::Write),
            source as usize == NUM_CPUS ==> lp.view().lock_id() == old(self).spec_index(allocator).global_pool.locking_thread()->Write_lock_id,
        ensures
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), allocator),
            final(self).spec_index(allocator).wf(),
            ret.0 == node,
            ret.1.view().is_init(),
            ret.1.view().addr() == node,
            ret.1.view().value().view() == old(self).spec_index(allocator).merge_2m_source_list(source as usize).map().spec_index(node),
            final(self).spec_index(allocator).merge_2m_source_list(source as usize).map() == old(self).spec_index(allocator).merge_2m_source_list(source as usize).map().remove(node),
            final(self).spec_index(allocator).merge_2m_source_list(source as usize).dom() == old(self).spec_index(allocator).merge_2m_source_list(source as usize).dom().remove(node),
            final(self).spec_index(allocator).merge_2m_source_list(source as usize).view() == old(self).spec_index(allocator).merge_2m_source_list(source as usize).view().remove_value(ret.1.view().value().view()),
            final(self).spec_index(allocator).merge_2m_source_list(source as usize).length == old(self).spec_index(allocator).merge_2m_source_list(source as usize).length - 1,
            final(self).spec_index(allocator).merge_2m_source_list(source as usize).wf(),
            forall|other: usize, key: usize| #![trigger final(self).spec_index(allocator).merge_2m_source_list(other).map().dom().contains(key)]
                #![trigger old(self).spec_index(allocator).merge_2m_source_list(other).map().dom().contains(key)] other <= NUM_CPUS ==> {
                let before = old(self).spec_index(allocator).merge_2m_source_list(other).map();
                let after = final(self).spec_index(allocator).merge_2m_source_list(other).map();
                &&& after.dom().contains(key) == (before.dom().contains(key) && (other != source as usize || before.spec_index(key) != ret.1.view().value().view()))
                &&& after.dom().contains(key) ==> after.spec_index(key) == before.spec_index(key)
            },
            forall|other: usize| #![trigger final(self).spec_index(allocator).merge_2m_source_list(other)] other <= NUM_CPUS ==>
                final(self).spec_index(allocator).merge_2m_source_list(other).map() == if other == source as usize {
                    old(self).spec_index(allocator).merge_2m_source_list(other).map().remove(node)
                } else { old(self).spec_index(allocator).merge_2m_source_list(other).map() },
            forall|other: usize, value: PagePtr| #![trigger final(self).spec_index(allocator).merge_2m_source_list(other).view().contains(value)]
                #![trigger old(self).spec_index(allocator).merge_2m_source_list(other).view().contains(value)] other <= NUM_CPUS ==>
                final(self).spec_index(allocator).merge_2m_source_list(other).view().contains(value)
                    == (old(self).spec_index(allocator).merge_2m_source_list(other).view().contains(value) && (other != source as usize || value != ret.1.view().value().view())),
            forall|other: usize| #![trigger final(self).spec_index(allocator).merge_2m_source_list(other)] other <= NUM_CPUS
                && LinkedList::<PagePtr, 233>::values_sorted(old(self).spec_index(allocator).merge_2m_source_list(other).view()) ==>
                    LinkedList::<PagePtr, 233>::values_sorted(final(self).spec_index(allocator).merge_2m_source_list(other).view()),
            forall|other: usize| #![trigger final(self).spec_index(allocator).merge_2m_source_list(other)] other <= NUM_CPUS && other != source as usize ==>
                final(self).spec_index(allocator).merge_2m_source_list(other) == old(self).spec_index(allocator).merge_2m_source_list(other),
            forall|value: PagePtr| #![trigger final(self).spec_index(allocator).merge_2m_source_list(source as usize).view().contains(value)]
                #![trigger old(self).spec_index(allocator).merge_2m_source_list(source as usize).view().contains(value)]
                final(self).spec_index(allocator).merge_2m_source_list(source as usize).view().contains(value)
                    == (old(self).spec_index(allocator).merge_2m_source_list(source as usize).view().contains(value) && value != ret.1.view().value().view()),
            LinkedList::<PagePtr, 233>::values_sorted(old(self).spec_index(allocator).merge_2m_source_list(source as usize).view())
                ==> LinkedList::<PagePtr, 233>::values_sorted(final(self).spec_index(allocator).merge_2m_source_list(source as usize).view()),
            final(self).spec_index(allocator).total_free_pages.view() == old(self).spec_index(allocator).total_free_pages.view() - 1,
            final(self).spec_index(allocator).quota == old(self).spec_index(allocator).quota,
            final(self).spec_index(allocator).owning_container == old(self).spec_index(allocator).owning_container,
            final(self).spec_index(allocator).merge_2m_source_list(source as usize).container_depth == old(self).spec_index(allocator).merge_2m_source_list(source as usize).container_depth,
            final(self).spec_index(allocator).merge_2m_source_list(source as usize).minor == old(self).spec_index(allocator).merge_2m_source_list(source as usize).minor,
            (source as usize) < NUM_CPUS ==> final(self).spec_index(allocator).global_pool == old(self).spec_index(allocator).global_pool,
            source as usize == NUM_CPUS ==> final(self).spec_index(allocator).cpu_caches == old(self).spec_index(allocator).cpu_caches,
            (source as usize) < NUM_CPUS ==> final(self).spec_index(allocator).cpu_caches.entries_unchanged_except(&old(self).spec_index(allocator).cpu_caches, source as usize),
            (source as usize) < NUM_CPUS ==> final(self).spec_index(allocator).cpu_caches.spec_index(source as usize).view().locking_thread() == old(self).spec_index(allocator).cpu_caches.spec_index(source as usize).view().locking_thread(),
            (source as usize) < NUM_CPUS ==> final(self).spec_index(allocator).cpu_caches.spec_index(source as usize).view().control() == old(self).spec_index(allocator).cpu_caches.spec_index(source as usize).view().control(),
            source as usize == NUM_CPUS ==> final(self).spec_index(allocator).global_pool.locking_thread() == old(self).spec_index(allocator).global_pool.locking_thread(),
            source as usize == NUM_CPUS ==> final(self).spec_index(allocator).global_pool.control() == old(self).spec_index(allocator).global_pool.control(),
            Self::merge_2m_remove_source_eof_transition_framing(*old(self), *final(self), allocator, source, node, ret.1.view()),
            final(self).typed_quota_lock_map_aligned(quota_locks, lctx.thread_id()),
            final(self).typed_cache_lock_map_aligned(cache_locks, lctx.thread_id()),
            final(self).typed_global_pool_lock_map_aligned(pool_locks, lctx.thread_id()),
    {
        proof {
            if (source as usize) < NUM_CPUS {
                self.typed_cache_lock_map_aligned_wf_at(cache_locks, lctx.thread_id(), allocator, source as usize);
                lemma_cache_len_fold_ge_elem(self.spec_index(allocator).cpu_caches.view(), source as int);
            } else {
                self.typed_global_pool_lock_map_aligned_wf_at(pool_locks, lctx.thread_id(), allocator);
                lemma_cache_len_fold_nonneg(self.spec_index(allocator).cpu_caches.view());
            }
            self.spec_index(allocator).merge_2m_source_list(source as usize).wf_implies_view_len_eq_len();
        }
        let ret = {
            let Tracked(perm) = self.borrow_perm_mut(allocator);
            let pptr = PPtr::<PageAllocator<SIZE>>::from_usize(allocator);
            let ret = if (source as usize) < NUM_CPUS {
                let cache = borrow_mut_cache(&pptr, Tracked(&mut *perm), source as usize, Tracked(lctx), lp);
                cache.linked_list.remove(node)
            } else {
                let pool = borrow_mut_global_pool(&pptr, Tracked(&mut *perm), Tracked(lctx), lp);
                pool.linked_list.remove(node)
            };
            proof { set_total_free_pages_ghost(perm, (perm.value().total_free_pages.view() - 1) as usize); }
            ret
        };
        proof {
            Self::merge_2m_remove_source_eof_implies_wf_and_alignment(*old(self), *self, allocator, source, node, ret.1.view(),
                quota_locks, cache_locks, pool_locks, lctx.thread_id());
        }
        ret
    }
}
}
