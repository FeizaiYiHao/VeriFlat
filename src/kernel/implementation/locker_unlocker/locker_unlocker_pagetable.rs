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
                wlock_requires(
                    old(self).pagetable_map.spec_index(pagetable_ptr), old(lctx)),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).lock_id_acyclic(
                    old(self).pagetable_map.lock_id_by_key(pagetable_ptr),
                ),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                lock_id_aligned(final(self), final(lctx)),

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
                pagetable_objects_unlocked(
                    old(self).pagetable_map, old(lctx).thread_id(),
                ) ==> pagetable_objects_unlocked_except(
                    final(self).pagetable_map, final(lctx).thread_id(), set![pagetable_ptr]),

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
                final(lctx).lock_id_set() == old(lctx).lock_id_set().insert(
                    (
                        final(self).pagetable_map.lock_id_by_key(pagetable_ptr),
                        KernelObjId::PageTable(pagetable_ptr),
                    ),
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
            }
            let ret = self.pagetable_map.wlock(
                pagetable_ptr,
                Tracked(&mut *lctx),
                Ghost(KernelObjId::PageTable(pagetable_ptr)),
            );
            proof {
                assert(pagetable_invariant_fields_unchanged(
                    old(self).pagetable_map,
                    self.pagetable_map,
                )) by {
                    pagetable_lock_op_preserves_invariant_fields(
                        old(self).pagetable_map,
                        self.pagetable_map,
                        pagetable_ptr,
                    );
                };
                assert(self.subsystems_inv()) by {
                    assert(pagetable_perms_wf(self.pagetable_map)) by {
                        lemma_no_change_imply_pagetable_perms_wf_forall();
                    };
                    reveal(KernelK::default_pagetable_wf);
                };
                assert(self.memory_management_inv()) by {
                    assert(process_pagetable_match(
                        self.process_map,
                        self.pagetable_map,
                    )) by {
                        lemma_no_change_imply_process_pagetable_match_for_pagetable_fields_forall();
                    };
                    assert(page_pagetable_wf(
                        self.pagetable_map,
                        self.page_array,
                    )) by {
                        lemma_no_change_imply_page_pagetable_wf_for_pagetable_fields_forall();
                    };
                    assert(container_process_page_pagetable_wf(
                        self.container_map,
                        self.process_map,
                        self.pagetable_map,
                        self.page_array,
                    )) by {
                        lemma_no_change_imply_container_process_page_pagetable_wf_for_pagetable_fields_forall();
                    };
                    assert(pagetable_pages_wf(
                        self.pagetable_map,
                        self.page_array,
                    )) by {
                        lemma_no_change_imply_pagetable_pages_wf_for_pagetable_fields_forall();
                    };
                };
                assert(cpu_dirty_map_wf(
                    self.container_map,
                    self.process_map,
                    self.cpu_array,
                    self.cpu_tlb,
                    self.pagetable_map,
                )) by {
                    lemma_no_change_imply_cpu_dirty_map_wf_for_pagetable_fields_forall();
                };
                assert(tlb_wf_spec(
                    self.cpu_tlb,
                    self.pagetable_map,
                    self.cpu_array,
                )) by {
                    lemma_no_change_imply_tlb_wf_spec_for_pagetable_fields_forall();
                };
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);

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
                old(self).pagetable_map.spec_index(pagetable_ptr)
                    .wlocked_by(old(lctx)),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id()
                    == old(self).pagetable_map.spec_index(pagetable_ptr)
                        .locking_thread()->Write_lock_id,
                old(lctx).lock_entry_contains(
                    old(self).pagetable_map.lock_id_by_key(pagetable_ptr),
                    KernelObjId::PageTable(pagetable_ptr)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                lock_id_aligned(final(self), final(lctx)),

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
                pagetable_objects_unlocked_except(
                    old(self).pagetable_map, old(lctx).thread_id(), set![pagetable_ptr],
                ) ==> pagetable_objects_unlocked(
                    final(self).pagetable_map, final(lctx).thread_id()),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().remove(
                    (
                        old(self).pagetable_map.lock_id_by_key(pagetable_ptr),
                        KernelObjId::PageTable(pagetable_ptr),
                    ),
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
                assert({
                    &&& old(self).pagetable_map.perms_wf()
                    &&& old(self).pagetable_map.spec_index(pagetable_ptr).inv()
                }) by {
                    reveal(pagetable_perms_wf);

                };
            }
            self.pagetable_map.wunlock(
                pagetable_ptr,
                Tracked(&mut *lctx),
                lock_perm,
                Ghost(KernelObjId::PageTable(pagetable_ptr)),
            );
            proof {
                assert(pagetable_invariant_fields_unchanged(
                    old(self).pagetable_map,
                    self.pagetable_map,
                )) by {
                    pagetable_lock_op_preserves_invariant_fields(
                        old(self).pagetable_map,
                        self.pagetable_map,
                        pagetable_ptr,
                    );
                };
                assert(self.subsystems_inv()) by {
                    assert(pagetable_perms_wf(self.pagetable_map)) by {
                        lemma_no_change_imply_pagetable_perms_wf_forall();
                    };
                    reveal(KernelK::default_pagetable_wf);
                };
                assert(self.memory_management_inv()) by {
                    assert(process_pagetable_match(
                        self.process_map,
                        self.pagetable_map,
                    )) by {
                        lemma_no_change_imply_process_pagetable_match_for_pagetable_fields_forall();
                    };
                    assert(page_pagetable_wf(
                        self.pagetable_map,
                        self.page_array,
                    )) by {
                        lemma_no_change_imply_page_pagetable_wf_for_pagetable_fields_forall();
                    };
                    assert(container_process_page_pagetable_wf(
                        self.container_map,
                        self.process_map,
                        self.pagetable_map,
                        self.page_array,
                    )) by {
                        lemma_no_change_imply_container_process_page_pagetable_wf_for_pagetable_fields_forall();
                    };
                    assert(pagetable_pages_wf(
                        self.pagetable_map,
                        self.page_array,
                    )) by {
                        lemma_no_change_imply_pagetable_pages_wf_for_pagetable_fields_forall();
                    };
                };
                assert(cpu_dirty_map_wf(
                    self.container_map,
                    self.process_map,
                    self.cpu_array,
                    self.cpu_tlb,
                    self.pagetable_map,
                )) by {
                    lemma_no_change_imply_cpu_dirty_map_wf_for_pagetable_fields_forall();
                };
                assert(tlb_wf_spec(
                    self.cpu_tlb,
                    self.pagetable_map,
                    self.cpu_array,
                )) by {
                    lemma_no_change_imply_tlb_wf_spec_for_pagetable_fields_forall();
                };
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);

                };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                };
            }
        }
}
} // verus!
