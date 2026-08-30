use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
        pub fn wlock_endpoint(
            &mut self,
            endpoint_ptr: RwLockEndpointPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Tracked<LockPerm>)
            requires
                old(self).inv(),
                old(self).endpoint_map.dom().contains(endpoint_ptr),
                !old(lctx).endpoint_lock_map().dom().contains(endpoint_ptr),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).lock_id_acyclic(old(self).endpoint_map.lock_id_by_key(endpoint_ptr)),
                typed_lock_maps_aligned(old(self), old(lctx)),
            ensures
                final(self).inv(),
                typed_lock_maps_aligned(final(self), final(lctx)),
                final(self).pagetable_map == old(self).pagetable_map,
                final(self).iommu_table_map == old(self).iommu_table_map,
                final(self).iommu_root_table == old(self).iommu_root_table,
                final(self).page_array == old(self).page_array,
                final(self).cpu_array == old(self).cpu_array,
                final(self).cpu_tlb == old(self).cpu_tlb,
                final(self).iommu_tlb == old(self).iommu_tlb,
                final(self).root_container == old(self).root_container,
                final(self).container_map == old(self).container_map,
                final(self).scheduler_map == old(self).scheduler_map,
                final(self).pcid_allocator_map == old(self).pcid_allocator_map,
                final(self).process_map == old(self).process_map,
                final(self).thread_map == old(self).thread_map,
                final(self).allocator_4k_map == old(self).allocator_4k_map,
                final(self).allocator_2m_map == old(self).allocator_2m_map,
                final(self).allocator_1g_map == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,
                final(self).endpoint_map.dom() == old(self).endpoint_map.dom(),
                final(self).endpoint_map.unchanged_except(&old(self).endpoint_map, endpoint_ptr),
                typed_lock_maps_inserted(
                    old(lctx), final(lctx), KernelObjId::Endpoint(endpoint_ptr),
                    TypedHeldLock {
                        lock_id: final(self).endpoint_map.lock_id_by_key(endpoint_ptr),
                        mode: TypedLockMode::Write,
                    }),
                final(lctx).endpoint_lock_map().contains_pair(endpoint_ptr, TypedHeldLock {
                        lock_id: final(self).endpoint_map.lock_id_by_key(endpoint_ptr),
                        mode: TypedLockMode::Write,
                    }),
                ret.view().ordering_lock_id()
                    == final(self).endpoint_map.lock_id_by_key(endpoint_ptr),
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
                final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                wlock_ensures(
                    old(self).endpoint_map.spec_index(endpoint_ptr),
                    final(self).endpoint_map.spec_index(endpoint_ptr),
                    old(self).endpoint_map.lock_id_by_key(endpoint_ptr),
                    final(lctx),
                    ret.view(),
                ),
        {
            proof {
                assert(old(self).endpoint_map.perms_wf()) by { reveal(endpoint_perms_wf); };
                assert(wlock_requires(
                    old(self).endpoint_map.spec_index(endpoint_ptr), old(lctx))) by {
                    reveal(LockedMap::typed_lock_map_aligned);
                };
            }
            let ret = self.endpoint_map.wlock(
                endpoint_ptr,
                Tracked(&mut *lctx),
                Ghost(KernelObjId::Endpoint(endpoint_ptr)),
            );
            proof {
                assert(endpoint_invariant_fields_unchanged(old(self).endpoint_map, self.endpoint_map)) by { endpoint_lock_op_preserves_invariant_fields(old(self).endpoint_map, self.endpoint_map, endpoint_ptr); };
                assert(self.subsystems_inv()) by {
                    reveal(KernelK::default_pagetable_wf);
                    assert(endpoint_perms_wf(self.endpoint_map)) by { reveal(endpoint_perms_wf); reveal(endpoints_inv); reveal(endpoint_invariant_fields_unchanged); };
                };
                assert(self.memory_management_inv()) by {
                    assert(endpoint_pages_wf(self.endpoint_map, self.page_array)) by { reveal(endpoint_invariant_fields_unchanged); reveal(endpoint_pages_wf); };
                };
                assert(self.process_management_inv()) by {
                    assert(container_endpoint_wf(self.container_map, self.endpoint_map)) by { reveal(endpoint_invariant_fields_unchanged); reveal(container_endpoint_wf); };
                    assert(thread_endpoint_ref_counter_wf(self.thread_map, self.endpoint_map)) by { reveal(endpoint_invariant_fields_unchanged); reveal(thread_endpoint_ref_counter_wf); };
                    assert(thread_endpoint_queue_wf(self.thread_map, self.endpoint_map)) by { thread_endpoint_queue_wf_preserved_for_endpoint_invariant_fields(self.thread_map, old(self).endpoint_map, self.endpoint_map); };
                    assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by { container_thread_endpoint_wf_preserved_for_endpoint_invariant_fields(self.container_map, self.thread_map, old(self).endpoint_map, self.endpoint_map); };
                };
                assert(typed_lock_maps_aligned(self, &*lctx)) by {
                    reveal(LockedMap::typed_lock_map_aligned);

                };
            }
            ret
        }

        pub fn wunlock_endpoint(
            &mut self,
            endpoint_ptr: RwLockEndpointPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                old(self).endpoint_map.dom().contains(endpoint_ptr),
                typed_lock_map_contains_mode(
                    old(lctx).endpoint_lock_map(), endpoint_ptr,
                    TypedLockMode::Write),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id()
                    == old(self).endpoint_map.spec_index(endpoint_ptr)
                        .locking_thread()->Write_lock_id,
                typed_lock_maps_aligned(old(self), old(lctx)),
            ensures
                final(self).inv(),
                typed_lock_maps_aligned(final(self), final(lctx)),
                final(self).pagetable_map == old(self).pagetable_map,
                final(self).iommu_table_map == old(self).iommu_table_map,
                final(self).iommu_root_table == old(self).iommu_root_table,
                final(self).page_array == old(self).page_array,
                final(self).cpu_array == old(self).cpu_array,
                final(self).cpu_tlb == old(self).cpu_tlb,
                final(self).iommu_tlb == old(self).iommu_tlb,
                final(self).root_container == old(self).root_container,
                final(self).container_map == old(self).container_map,
                final(self).scheduler_map == old(self).scheduler_map,
                final(self).pcid_allocator_map == old(self).pcid_allocator_map,
                final(self).process_map == old(self).process_map,
                final(self).thread_map == old(self).thread_map,
                final(self).allocator_4k_map == old(self).allocator_4k_map,
                final(self).allocator_2m_map == old(self).allocator_2m_map,
                final(self).allocator_1g_map == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,
                final(self).endpoint_map.dom() == old(self).endpoint_map.dom(),
                final(self).endpoint_map.unchanged_except(&old(self).endpoint_map, endpoint_ptr),
                final(self).endpoint_map.spec_index(endpoint_ptr).locking_thread() is None,
                final(self).endpoint_map.lock_id_by_key(endpoint_ptr)
                    == old(self).endpoint_map.lock_id_by_key(endpoint_ptr),
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
                final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
                final(lctx).kernel_view_locking_state() is Release,
                wunlock_ensures(
                    old(self).endpoint_map.spec_index(endpoint_ptr),
                    final(self).endpoint_map.spec_index(endpoint_ptr),
                ),
                typed_lock_maps_removed(
                    old(lctx), final(lctx), KernelObjId::Endpoint(endpoint_ptr)),
                !final(lctx).endpoint_lock_map().dom().contains(endpoint_ptr),
        {
            proof {
                assert({
                    &&& old(self).endpoint_map.perms_wf()
                    &&& old(self).endpoint_map.spec_index(endpoint_ptr).inv()
                }) by { reveal(endpoint_perms_wf); reveal(endpoints_inv); };
                assert(old(self).endpoint_map.spec_index(endpoint_ptr)
                    .wlocked_by(old(lctx))) by {
                    reveal(LockedMap::typed_lock_map_aligned);
                };
                assert(old(lctx).lock_entry_contains(
                    old(self).endpoint_map.lock_id_by_key(endpoint_ptr),
                    KernelObjId::Endpoint(endpoint_ptr),
                )) by {
                    reveal(LockedMap::typed_lock_map_aligned);
                };
            }
            self.endpoint_map.wunlock(
                endpoint_ptr,
                Tracked(&mut *lctx),
                lock_perm,
                Ghost(KernelObjId::Endpoint(endpoint_ptr)),
            );
            proof {
                assert(endpoint_invariant_fields_unchanged(old(self).endpoint_map, self.endpoint_map)) by { endpoint_lock_op_preserves_invariant_fields(old(self).endpoint_map, self.endpoint_map, endpoint_ptr); };
                assert(self.subsystems_inv()) by {
                    reveal(KernelK::default_pagetable_wf);
                    assert(endpoint_perms_wf(self.endpoint_map)) by { reveal(endpoint_perms_wf); reveal(endpoints_inv); reveal(endpoint_invariant_fields_unchanged); };
                };
                assert(self.memory_management_inv()) by {
                    assert(endpoint_pages_wf(self.endpoint_map, self.page_array)) by { reveal(endpoint_invariant_fields_unchanged); reveal(endpoint_pages_wf); };
                };
                assert(self.process_management_inv()) by {
                    assert(container_endpoint_wf(self.container_map, self.endpoint_map)) by { reveal(endpoint_invariant_fields_unchanged); reveal(container_endpoint_wf); };
                    assert(thread_endpoint_ref_counter_wf(self.thread_map, self.endpoint_map)) by { reveal(endpoint_invariant_fields_unchanged); reveal(thread_endpoint_ref_counter_wf); };
                    assert(thread_endpoint_queue_wf(self.thread_map, self.endpoint_map)) by { thread_endpoint_queue_wf_preserved_for_endpoint_invariant_fields(self.thread_map, old(self).endpoint_map, self.endpoint_map); };
                    assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by { container_thread_endpoint_wf_preserved_for_endpoint_invariant_fields(self.container_map, self.thread_map, old(self).endpoint_map, self.endpoint_map); };
                };
                assert(typed_lock_maps_aligned(self, &*lctx)) by {
                    reveal(LockedMap::typed_lock_map_aligned);

                };
            }
        }

}
} // verus!
