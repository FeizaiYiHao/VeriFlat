use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
        pub fn wlock_pagetable(
            &mut self,
            pagetable_ptr: RwLockPageTableRoot,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Tracked<LockPerm>)
            requires
                old(self).inv(),
                old(self).pagetable_map.dom().contains(pagetable_ptr),
                !old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).lock_id_acyclic(
                    old(self).pagetable_map.lock_id_by_key(pagetable_ptr),
                ),
                typed_lock_maps_aligned(old(self), old(lctx)),
            ensures
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                typed_lock_maps_aligned(final(self), final(lctx)),

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
                final(self).endpoint_map == old(self).endpoint_map,
                final(self).allocator_4k_map == old(self).allocator_4k_map,
                final(self).allocator_2m_map == old(self).allocator_2m_map,
                final(self).allocator_1g_map == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                final(self).pagetable_map.unchanged_except(
                    &old(self).pagetable_map,
                    pagetable_ptr,
                ),
                typed_lock_maps_inserted(
                    old(lctx), final(lctx), KernelObjId::PageTable(pagetable_ptr),
                    TypedHeldLock {
                        lock_id: final(self).pagetable_map.lock_id_by_key(pagetable_ptr),
                        mode: TypedLockMode::Write,
                    }),
                final(lctx).pagetable_lock_map().contains_pair(pagetable_ptr, TypedHeldLock {
                        lock_id: final(self).pagetable_map.lock_id_by_key(pagetable_ptr),
                        mode: TypedLockMode::Write,
                    }),

                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state()
                    == old(lctx).kernel_view_locking_state(),
                wlock_ensures(
                    old(self).pagetable_map.spec_index(pagetable_ptr),
                    final(self).pagetable_map.spec_index(pagetable_ptr),
                    old(self).pagetable_map.lock_id_by_key(pagetable_ptr),
                    final(lctx),
                    ret.view(),
                ),
                forall|other_pagetable: RwLockPageTableRoot|
                    #![trigger final(lctx).lock_entry_contains(
                        final(self).pagetable_map.lock_id_by_key(other_pagetable),
                        KernelObjId::PageTable(other_pagetable),
                    )]
                    old(self).pagetable_map.dom().contains(other_pagetable)
                        && other_pagetable != pagetable_ptr
                    ==> final(lctx).lock_entry_contains(
                            final(self).pagetable_map.lock_id_by_key(other_pagetable),
                            KernelObjId::PageTable(other_pagetable),
                        ) == old(lctx).lock_entry_contains(
                            old(self).pagetable_map.lock_id_by_key(other_pagetable),
                            KernelObjId::PageTable(other_pagetable),
                        ),
        {
            proof {
                assert(old(self).pagetable_map.perms_wf()) by { reveal(pagetable_perms_wf); };
                assert(wlock_requires(
                    old(self).pagetable_map.spec_index(pagetable_ptr), old(lctx))) by {
                    reveal(LockedMap::typed_lock_map_aligned);
                };
            }
            let ret = self.pagetable_map.wlock(
                pagetable_ptr,
                Tracked(&mut *lctx),
                Ghost(KernelObjId::PageTable(pagetable_ptr)),
            );
            proof {
                assert(self.subsystems_inv()) by {
                    assert(pagetable_perms_wf(self.pagetable_map)) by {
                        reveal(pagetable_perms_wf);

                    };
                    reveal(KernelK::default_pagetable_wf);
                };
                assert(self.memory_management_inv()) by {
                    assert(process_pagetable_match(
                        self.process_map,
                        self.pagetable_map,
                    )) by { reveal(process_pagetable_match); };
                    assert(page_pagetable_wf(
                        self.pagetable_map,
                        self.page_array,
                    )) by {
                        reveal(mapped_4k_page_pagetable_wf);
                        reveal(mapped_2m_page_pagetable_wf);
                        reveal(mapped_1g_page_pagetable_wf);
                    };
                    assert(container_process_page_pagetable_wf(
                        self.container_map,
                        self.process_map,
                        self.pagetable_map,
                        self.page_array,
                    )) by {
                        reveal(container_process_page_pagetable_wf);
                        reveal(process_pagetable_match);
                        reveal(container_page_owner_wf);
                        reveal(mapped_4k_page_pagetable_wf);
                        reveal(mapped_2m_page_pagetable_wf);
                        reveal(mapped_1g_page_pagetable_wf);
                    };
                    assert(pagetable_pages_wf(
                        self.pagetable_map,
                        self.page_array,
                    )) by { reveal(pagetable_pages_wf); };
                };
                assert(cpu_dirty_map_wf(
                    self.container_map,
                    self.process_map,
                    self.cpu_array,
                    self.cpu_tlb,
                    self.pagetable_map,
                )) by { reveal(cpu_dirty_map_contains_pagetable_pcid_match); };
                assert(tlb_wf_spec(
                    self.cpu_tlb,
                    self.pagetable_map,
                    self.cpu_array,
                )) by { reveal(tlb_wf_spec); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by {
                    reveal(LockedMap::typed_lock_map_aligned);

                };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                };
            }
            ret
        }

        pub fn wunlock_pagetable(
            &mut self,
            pagetable_ptr: RwLockPageTableRoot,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                old(self).pagetable_map.dom().contains(pagetable_ptr),
                typed_lock_map_contains_mode(
                    old(lctx).pagetable_lock_map(),
                    pagetable_ptr, TypedLockMode::Write),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id()
                    == old(self).pagetable_map.spec_index(pagetable_ptr)
                        .locking_thread()->Write_lock_id,
                typed_lock_maps_aligned(old(self), old(lctx)),
            ensures
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                typed_lock_maps_aligned(final(self), final(lctx)),

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
                final(self).endpoint_map == old(self).endpoint_map,
                final(self).allocator_4k_map == old(self).allocator_4k_map,
                final(self).allocator_2m_map == old(self).allocator_2m_map,
                final(self).allocator_1g_map == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                final(self).pagetable_map.unchanged_except(
                    &old(self).pagetable_map,
                    pagetable_ptr,
                ),
                final(self).pagetable_map.lock_id_by_key(pagetable_ptr)
                    == old(self).pagetable_map.lock_id_by_key(pagetable_ptr),

                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,
                wunlock_ensures(
                    old(self).pagetable_map.spec_index(pagetable_ptr),
                    final(self).pagetable_map.spec_index(pagetable_ptr),
                ),
                typed_lock_maps_removed(
                    old(lctx), final(lctx), KernelObjId::PageTable(pagetable_ptr)),
                !final(lctx).pagetable_lock_map().dom().contains(pagetable_ptr),
                forall|other_pagetable: RwLockPageTableRoot|
                    #![trigger final(lctx).lock_entry_contains(
                        final(self).pagetable_map.lock_id_by_key(other_pagetable),
                        KernelObjId::PageTable(other_pagetable),
                    )]
                    old(self).pagetable_map.dom().contains(other_pagetable)
                        && other_pagetable != pagetable_ptr
                    ==> final(lctx).lock_entry_contains(
                            final(self).pagetable_map.lock_id_by_key(other_pagetable),
                            KernelObjId::PageTable(other_pagetable),
                        ) == old(lctx).lock_entry_contains(
                            old(self).pagetable_map.lock_id_by_key(other_pagetable),
                            KernelObjId::PageTable(other_pagetable),
                        ),
        {
            proof {
                assert({
                    &&& old(self).pagetable_map.perms_wf()
                    &&& old(self).pagetable_map.spec_index(pagetable_ptr).inv()
                }) by {
                    reveal(pagetable_perms_wf);

                };
                assert(old(self).pagetable_map.spec_index(pagetable_ptr)
                    .wlocked_by(old(lctx))) by {
                    reveal(LockedMap::typed_lock_map_aligned);
                };
                assert(old(lctx).lock_entry_contains(
                    old(self).pagetable_map.lock_id_by_key(pagetable_ptr),
                    KernelObjId::PageTable(pagetable_ptr),
                )) by {
                    reveal(LockedMap::typed_lock_map_aligned);
                };
            }
            self.pagetable_map.wunlock(
                pagetable_ptr,
                Tracked(&mut *lctx),
                lock_perm,
                Ghost(KernelObjId::PageTable(pagetable_ptr)),
            );
            proof {
                assert(self.subsystems_inv()) by {
                    assert(pagetable_perms_wf(self.pagetable_map)) by {
                        reveal(pagetable_perms_wf);

                    };
                    reveal(KernelK::default_pagetable_wf);
                };
                assert(self.memory_management_inv()) by {
                    assert(process_pagetable_match(
                        self.process_map,
                        self.pagetable_map,
                    )) by { reveal(process_pagetable_match); };
                    assert(page_pagetable_wf(
                        self.pagetable_map,
                        self.page_array,
                    )) by {
                        reveal(mapped_4k_page_pagetable_wf);
                        reveal(mapped_2m_page_pagetable_wf);
                        reveal(mapped_1g_page_pagetable_wf);
                    };
                    assert(container_process_page_pagetable_wf(
                        self.container_map,
                        self.process_map,
                        self.pagetable_map,
                        self.page_array,
                    )) by {
                        reveal(container_process_page_pagetable_wf);
                        reveal(process_pagetable_match);
                        reveal(container_page_owner_wf);
                        reveal(mapped_4k_page_pagetable_wf);
                        reveal(mapped_2m_page_pagetable_wf);
                        reveal(mapped_1g_page_pagetable_wf);
                    };
                    assert(pagetable_pages_wf(
                        self.pagetable_map,
                        self.page_array,
                    )) by { reveal(pagetable_pages_wf); };
                };
                assert(cpu_dirty_map_wf(
                    self.container_map,
                    self.process_map,
                    self.cpu_array,
                    self.cpu_tlb,
                    self.pagetable_map,
                )) by { reveal(cpu_dirty_map_contains_pagetable_pcid_match); };
                assert(tlb_wf_spec(
                    self.cpu_tlb,
                    self.pagetable_map,
                    self.cpu_array,
                )) by { reveal(tlb_wf_spec); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by {
                    reveal(LockedMap::typed_lock_map_aligned);

                };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                };
            }
        }
}
} // verus!
