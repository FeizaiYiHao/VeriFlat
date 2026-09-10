use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
        pub fn wlock_quota_4k(
            &mut self,
            alloc_ptr_4k: RwLockPageAllocatorPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Tracked<LockPerm>)
            requires
                old(self).inv(),
                old(self).allc_4k_mp.dom().contains(alloc_ptr_4k),
                old(self).allc_4k_mp.spec_index(alloc_ptr_4k).wf(),
                wlock_requires(old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota, old(lctx)),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).page_lock_map().dom().is_empty(),
                old(lctx).container_lock_map().dom() =~= set![old(self).allc_4k_mp.spec_index(
                        alloc_ptr_4k,
                    ).owning_container],
                old(lctx).process_lock_map().dom().is_empty(),
                old(lctx).thread_lock_map().dom().is_empty(),
                old(lctx).endpoint_lock_map().dom().is_empty(),
                old(lctx).scheduler_lock_map().dom().is_empty(),
                old(lctx).pcid_allocator_lock_map().dom().is_empty(),
                old(lctx).cpu_set_lock_map().dom().is_empty(),
                old(lctx).pagetable_lock_map().dom().is_empty(),
                old(lctx).iommu_table_lock_map().dom().is_empty(),
                old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
                old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
                old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
                old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
                old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
                old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
                old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
                old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
                old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
                !old(lctx).cpu_lock_map().dom().is_empty(),
                (forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> ((index_valid(NUM_CPUS, held_cpu_id)) && (old(self).cpu_arr.spec_index(held_cpu_id).view().view().owning_container == old(self).allc_4k_mp.spec_index(
                        alloc_ptr_4k,
                    ).owning_container))),
                (forall|held_cpu_id: CpuId|
                    #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)]
                    old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> {
                        &&& index_valid(NUM_CPUS, held_cpu_id)
                        &&& !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().state is Off)
                    }),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                final(self).inv(),
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                final(self).pt_mp     == old(self).pt_mp,
                final(self).it_mp     == old(self).it_mp,
                final(self).irt     == old(self).irt,
                final(self).pg_arr        == old(self).pg_arr,
                final(self).cpu_arr         == old(self).cpu_arr,
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
                final(self).allc_2m_mp  == old(self).allc_2m_mp,
                final(self).allc_1g_mp  == old(self).allc_1g_mp,
                final(self).dflt_pt == old(self).dflt_pt,
                final(self).allc_4k_mp.dom() == old(self).allc_4k_mp.dom(),
                final(self).allc_4k_mp.unchanged_except(&old(self).allc_4k_mp, alloc_ptr_4k),
                final(self).allc_4k_mp.perms_wf(),
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).wf(),
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches,
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool,
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).owning_container == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).owning_container,
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).total_free_pages == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).total_free_pages,
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                wlock_ensures(old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota, final(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota, old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.lock_id(), final(lctx), ret.view()),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.lock_id(), KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k))),
                typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k), TypedHeldLock { lock_id: final(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.lock_id(), mode: TypedLockMode::Write }),
        {
            proof {
                assert(old(self).allc_4k_mp.perms_wf()) by { reveal(allocator_perms_wf); };
                assert(old(lctx).lock_id_acyclic(old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.lock_id())) by {    reveal(lock_id_set_aligned);  reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned); reveal(container_cpu_wf); reveal(container_allocator_wf); reveal(container_perms_wf); reveal(allocator_perms_wf); };
            }
            let ret = self.allc_4k_mp.wlock_quota(alloc_ptr_4k, Tracked(&mut *lctx), Ghost(PageSize::SZ4k));

            proof {
                assert(allocator_perms_wf(self.allc_4k_mp)) by { reveal(allocator_perms_wf); };
                assert(allocator_invariant_fields_unchanged(old(self).allc_4k_mp, self.allc_4k_mp)) by { allocator_quota_lock_op_preserves_invariant_fields(old(self).allc_4k_mp, self.allc_4k_mp, alloc_ptr_4k); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.memory_management_inv()) by {
                    assert(allocator_pages_wf(self.pg_arr, self.allc_4k_mp, self.allc_2m_mp, self.allc_1g_mp)) by { lemma_no_change_imply_allocator_pages_wf_forall(); };
                    assert(container_process_allocator_quota_4k_wf(self.ctn_mp, self.prc_mp, self.thr_mp, self.allc_4k_mp)) by { reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf); };
                    assert(container_allocator_wf(self.ctn_mp, self.allc_4k_mp, self.allc_2m_mp, self.allc_1g_mp)) by { lemma_no_change_imply_container_allocator_wf_forall(); };
                    assert(allocator_free_page_ptrs_wf(self.allc_4k_mp)) by { lemma_no_change_imply_allocator_free_page_ptrs_wf_forall(); };
                    assert(container_allocator_free_4k_page_wf(self.allc_4k_mp, self.pg_arr)) by { lemma_container_allocator_free_4k_page_wf_preserved_for_lock_op(*old(self), *self); };
                };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
            }
            ret
        }

        pub fn wunlock_quota_4k(
            &mut self,
            alloc_ptr_4k: RwLockPageAllocatorPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                old(self).allc_4k_mp.dom().contains(alloc_ptr_4k),
                old(self).allc_4k_mp.spec_index(alloc_ptr_4k).wf(),
                old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.inv(),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id() == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.locking_thread()->Write_lock_id,
                old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.wlocked_by(old(lctx)),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                final(self).inv(),
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                final(self).pt_mp     == old(self).pt_mp,
                final(self).it_mp     == old(self).it_mp,
                final(self).irt     == old(self).irt,
                final(self).pg_arr        == old(self).pg_arr,
                final(self).cpu_arr         == old(self).cpu_arr,
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
                final(self).allc_2m_mp  == old(self).allc_2m_mp,
                final(self).allc_1g_mp  == old(self).allc_1g_mp,
                final(self).dflt_pt == old(self).dflt_pt,
                final(self).allc_4k_mp.dom() == old(self).allc_4k_mp.dom(),
                final(self).allc_4k_mp.unchanged_except(&old(self).allc_4k_mp, alloc_ptr_4k),
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).wf(),
                !final(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.locked_by_thread(final(lctx).thread_id()),
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches,
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool,
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).owning_container == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).owning_container,
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).total_free_pages == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).total_free_pages,
                // `unlock_ensures` owns the Acquire -> Release phase transition.
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,
                final(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.lock_id() == old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.lock_id(),
                wunlock_ensures(old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota, final(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().remove((old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.lock_id(), KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k))),
                typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k)),
        {
            proof {
                assert(old(self).allc_4k_mp.perms_wf()) by { reveal(allocator_perms_wf); };
                assert(old(lctx).lock_entry_contains(old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.lock_id(), KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k))) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); };
                assert(old(lctx).lock_id_set().contains((old(self).allc_4k_mp.spec_index(alloc_ptr_4k).quota.lock_id(), KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k)))) by { reveal(lock_id_set_aligned); };
            }
            self.allc_4k_mp.wunlock_quota(alloc_ptr_4k, Tracked(&mut *lctx), lock_perm, Ghost(PageSize::SZ4k));

            proof {
                assert(allocator_perms_wf(self.allc_4k_mp)) by { reveal(allocator_perms_wf); };
                assert(allocator_invariant_fields_unchanged(old(self).allc_4k_mp, self.allc_4k_mp)) by { allocator_quota_lock_op_preserves_invariant_fields(old(self).allc_4k_mp, self.allc_4k_mp, alloc_ptr_4k); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.memory_management_inv()) by {
                    assert(allocator_pages_wf(self.pg_arr, self.allc_4k_mp, self.allc_2m_mp, self.allc_1g_mp)) by { lemma_no_change_imply_allocator_pages_wf_forall(); };
                    assert(container_process_allocator_quota_4k_wf(self.ctn_mp, self.prc_mp, self.thr_mp, self.allc_4k_mp)) by { reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf); };
                    assert(container_allocator_wf(self.ctn_mp, self.allc_4k_mp, self.allc_2m_mp, self.allc_1g_mp)) by { lemma_no_change_imply_container_allocator_wf_forall(); };
                    assert(allocator_free_page_ptrs_wf(self.allc_4k_mp)) by { lemma_no_change_imply_allocator_free_page_ptrs_wf_forall(); };
                    assert(container_allocator_free_4k_page_wf(self.allc_4k_mp, self.pg_arr)) by { lemma_container_allocator_free_4k_page_wf_preserved_for_lock_op(*old(self), *self); };
                };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
            }
        }
}
} // verus!
