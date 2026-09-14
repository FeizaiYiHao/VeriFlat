use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
        pub fn wlock_allocator_cache_2m(
            &mut self,
            alloc_ptr_2m: RwLockPageAllocatorPtr,
            cache_cpu: CpuId,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Tracked<LockPerm>)
            requires
                old(self).inv(),
                old(self).allc_2m_mp.dom().contains(alloc_ptr_2m),
                old(self).allc_2m_mp.spec_index(alloc_ptr_2m).wf(),
                index_valid(NUM_CPUS, cache_cpu),
                !typed_lock_map_contains_mode(old(lctx).allocator_cache_2m_lock_map(), (alloc_ptr_2m, cache_cpu), TypedLockMode::Write),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).lock_id_acyclic(LockId{ container: old(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cache_cpu).container_depth(), process: old(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cache_cpu).process_depth(), major: old(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cache_cpu).view().view().current_lock_major(), minor: old(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cache_cpu).lock_minor(), }),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                final(self).pt_mp     == old(self).pt_mp,
                final(self).it_mp     == old(self).it_mp,
                final(self).irt     == old(self).irt,
                final(self).pg_arr        == old(self).pg_arr,
                final(self).cpu_arr         == old(self).cpu_arr,
                final(self).pcid_needflush == old(self).pcid_needflush,
                final(self).cpu_published == old(self).cpu_published,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).iommu_tlb           == old(self).iommu_tlb,
                final(self).rt_ctn    == old(self).rt_ctn,
                final(self).ctn_mp     == old(self).ctn_mp,
                final(self).sched_mp     == old(self).sched_mp,
                final(self).pcid_allc_mp == old(self).pcid_allc_mp,
                final(self).cpu_set_mp == old(self).cpu_set_mp,
                final(self).prc_mp       == old(self).prc_mp,
                final(self).thr_mp        == old(self).thr_mp,
                final(self).ep_mp      == old(self).ep_mp,
                final(self).allc_4k_mp  == old(self).allc_4k_mp,
                final(self).allc_1g_mp  == old(self).allc_1g_mp,
                final(self).dflt_pt == old(self).dflt_pt,
                final(self).allc_2m_mp.dom() == old(self).allc_2m_mp.dom(),
                final(self).allc_2m_mp.unchanged_except(&old(self).allc_2m_mp, alloc_ptr_2m),
                final(self).allc_2m_mp.perms_wf(),
                final(self).allc_2m_mp.spec_index(alloc_ptr_2m).wf(),
                final(self).allc_2m_mp.spec_index(alloc_ptr_2m).quota == old(self).allc_2m_mp.spec_index(alloc_ptr_2m).quota,
                final(self).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool == old(self).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool,
                final(self).allc_2m_mp.spec_index(alloc_ptr_2m).owning_container == old(self).allc_2m_mp.spec_index(alloc_ptr_2m).owning_container,
                final(self).allc_2m_mp.spec_index(alloc_ptr_2m).total_free_pages == old(self).allc_2m_mp.spec_index(alloc_ptr_2m).total_free_pages,
                final(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.unchanged_except(&old(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches, cache_cpu),
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                wlock_ensures(old(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cache_cpu).view(), final(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cache_cpu).view(), LockId{ container: old(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cache_cpu).container_depth(), process: old(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cache_cpu).process_depth(), major: old(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cache_cpu).view().view().current_lock_major(), minor: old(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cache_cpu).lock_minor(), }, final(lctx), ret.view()),
                final(lctx).allocator_cache_2m_lock_map().dom().contains((alloc_ptr_2m, cache_cpu)),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.lock_id_by_index(cache_cpu), KernelObjId::AllocatorCache(PageSize::SZ2m, alloc_ptr_2m, cache_cpu))),
                typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::AllocatorCache(PageSize::SZ2m, alloc_ptr_2m, cache_cpu), TypedHeldLock { lock_id: final(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.lock_id_by_index(cache_cpu), mode: TypedLockMode::Write }),
        {
            hide(kernel_k_to_kernel_u);
            proof {
                assert(
                    {
                        &&& old(self).allc_2m_mp.perms_wf()
                        &&& old(self).allc_2m_mp.spec_index(alloc_ptr_2m).wf()
                    }
                ) by { reveal(allocator_perms_wf); };
                assert(wlock_requires(self.allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cache_cpu).view(), &*lctx)) by { reveal(UnLockedMap::typed_cache_lock_map_aligned); };
            }
            let ret = self.allc_2m_mp.wlock_cache(alloc_ptr_2m, cache_cpu, Tracked(&mut *lctx), Ghost(PageSize::SZ2m));

            proof {
                assert(allocator_perms_wf(self.allc_2m_mp)) by { reveal(allocator_perms_wf); };
                assert(allocator_invariant_fields_unchanged(old(self).allc_2m_mp, self.allc_2m_mp)) by { allocator_cache_lock_op_preserves_invariant_fields(old(self).allc_2m_mp, self.allc_2m_mp, alloc_ptr_2m, cache_cpu); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.memory_management_inv()) by {
                    assert(allocator_pages_wf(self.pg_arr, self.allc_4k_mp, self.allc_2m_mp, self.allc_1g_mp)) by { reveal(allocator_2m_pages_wf); };
                    assert(container_process_allocator_quota_2m_wf(self.ctn_mp, self.prc_mp, self.thr_mp, self.allc_2m_mp)) by { reveal(container_process_allocator_quota_2m_wf); reveal(container_allocator_wf); };
                    assert(container_allocator_wf(self.ctn_mp, self.allc_4k_mp, self.allc_2m_mp, self.allc_1g_mp)) by { reveal(container_allocator_wf); reveal(allocator_invariant_fields_unchanged); };
                    assert(allocator_free_page_ptrs_wf(self.allc_2m_mp)) by { lemma_no_change_imply_allocator_free_page_ptrs_wf_forall(); };
                    assert(container_allocator_free_2m_page_wf(self.allc_2m_mp, self.pg_arr)) by { lemma_container_allocator_free_2m_page_wf_preserved_for_lock_op(*old(self), *self); };
                };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
            }
            ret
        }

        pub fn wunlock_allocator_cache_2m(
            &mut self,
            alloc_ptr_2m: RwLockPageAllocatorPtr,
            cache_cpu: CpuId,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                old(self).allc_2m_mp.dom().contains(alloc_ptr_2m),
                index_valid(NUM_CPUS, cache_cpu),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id() == old(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cache_cpu).view().locking_thread()->Write_lock_id,
                typed_lock_map_contains_mode(old(lctx).allocator_cache_2m_lock_map(), (alloc_ptr_2m, cache_cpu), TypedLockMode::Write),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                final(self).pt_mp     == old(self).pt_mp,
                final(self).it_mp     == old(self).it_mp,
                final(self).irt     == old(self).irt,
                final(self).pg_arr        == old(self).pg_arr,
                final(self).cpu_arr         == old(self).cpu_arr,
                final(self).pcid_needflush == old(self).pcid_needflush,
                final(self).cpu_published == old(self).cpu_published,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).iommu_tlb           == old(self).iommu_tlb,
                final(self).rt_ctn    == old(self).rt_ctn,
                final(self).ctn_mp     == old(self).ctn_mp,
                final(self).sched_mp     == old(self).sched_mp,
                final(self).pcid_allc_mp == old(self).pcid_allc_mp,
                final(self).cpu_set_mp == old(self).cpu_set_mp,
                final(self).prc_mp       == old(self).prc_mp,
                final(self).thr_mp        == old(self).thr_mp,
                final(self).ep_mp      == old(self).ep_mp,
                final(self).allc_4k_mp  == old(self).allc_4k_mp,
                final(self).allc_1g_mp  == old(self).allc_1g_mp,
                final(self).dflt_pt == old(self).dflt_pt,
                final(self).allc_2m_mp.dom() == old(self).allc_2m_mp.dom(),
                final(self).allc_2m_mp.unchanged_except(&old(self).allc_2m_mp, alloc_ptr_2m),
                final(self).allc_2m_mp.perms_wf(),
                final(self).allc_2m_mp.spec_index(alloc_ptr_2m).wf(),
                final(self).allc_2m_mp.spec_index(alloc_ptr_2m).quota == old(self).allc_2m_mp.spec_index(alloc_ptr_2m).quota,
                final(self).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool == old(self).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool,
                final(self).allc_2m_mp.spec_index(alloc_ptr_2m).owning_container == old(self).allc_2m_mp.spec_index(alloc_ptr_2m).owning_container,
                final(self).allc_2m_mp.spec_index(alloc_ptr_2m).total_free_pages == old(self).allc_2m_mp.spec_index(alloc_ptr_2m).total_free_pages,
                final(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.unchanged_except(&old(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches, cache_cpu),
                // `unlock_ensures` owns the Acquire -> Release phase transition.
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,
                final(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cache_cpu).lock_id() == old(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cache_cpu).lock_id(),
                !typed_lock_map_contains_mode(final(lctx).allocator_cache_2m_lock_map(), (alloc_ptr_2m, cache_cpu), TypedLockMode::Write),
                !final(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cache_cpu).view().locked(),
                wunlock_ensures(old(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cache_cpu).view(), final(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cache_cpu).view()),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().remove((old(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cache_cpu).lock_id(), KernelObjId::AllocatorCache(PageSize::SZ2m, alloc_ptr_2m, cache_cpu))),
                typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::AllocatorCache(PageSize::SZ2m, alloc_ptr_2m, cache_cpu)),
                unlock_ensures(old(lctx), final(lctx), KernelObjId::AllocatorCache(PageSize::SZ2m, alloc_ptr_2m, cache_cpu), old(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cache_cpu).lock_id()),
        {
            hide(kernel_k_to_kernel_u);
            proof {
                assert(
                    {
                        &&& old(self).allc_2m_mp.perms_wf()
                        &&& old(self).allc_2m_mp.spec_index(alloc_ptr_2m).wf()
                    }
                ) by { reveal(allocator_perms_wf); };
                assert(old(lctx).lock_entry_contains(old(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.lock_id_by_index(cache_cpu), KernelObjId::AllocatorCache(PageSize::SZ2m, alloc_ptr_2m, cache_cpu))) by { reveal(UnLockedMap::typed_cache_lock_map_aligned); };
                assert(old(lctx).lock_id_set().contains((old(self).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.lock_id_by_index(cache_cpu), KernelObjId::AllocatorCache(PageSize::SZ2m, alloc_ptr_2m, cache_cpu)))) by { reveal(lock_id_set_aligned); };
            }
            assert(self.allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cache_cpu).view().wlocked_by(&*lctx)) by { reveal(UnLockedMap::typed_cache_lock_map_aligned); };
            self.allc_2m_mp.wunlock_cache(alloc_ptr_2m, cache_cpu, Tracked(&mut *lctx), lock_perm, Ghost(PageSize::SZ2m));

            proof {
                assert(allocator_perms_wf(self.allc_2m_mp)) by { reveal(allocator_perms_wf); };
                assert(allocator_invariant_fields_unchanged(old(self).allc_2m_mp, self.allc_2m_mp)) by { allocator_cache_lock_op_preserves_invariant_fields(old(self).allc_2m_mp, self.allc_2m_mp, alloc_ptr_2m, cache_cpu); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.memory_management_inv()) by {
                    assert(allocator_pages_wf(self.pg_arr, self.allc_4k_mp, self.allc_2m_mp, self.allc_1g_mp)) by { reveal(allocator_2m_pages_wf); };
                    assert(container_process_allocator_quota_2m_wf(self.ctn_mp, self.prc_mp, self.thr_mp, self.allc_2m_mp)) by { reveal(container_process_allocator_quota_2m_wf); reveal(container_allocator_wf); };
                    assert(container_allocator_wf(self.ctn_mp, self.allc_4k_mp, self.allc_2m_mp, self.allc_1g_mp)) by { reveal(container_allocator_wf); reveal(allocator_invariant_fields_unchanged); };
                    assert(allocator_free_page_ptrs_wf(self.allc_2m_mp)) by { lemma_no_change_imply_allocator_free_page_ptrs_wf_forall(); };
                    assert(container_allocator_free_2m_page_wf(self.allc_2m_mp, self.pg_arr)) by { lemma_container_allocator_free_2m_page_wf_preserved_for_lock_op(*old(self), *self); };
                };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
            }
        }
}
} // verus!
