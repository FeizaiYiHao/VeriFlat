use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
        #[verifier::spinoff_prover]
        pub fn wlock_page(
            &mut self,
            page_index: PageIndex,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Tracked<LockPerm>)
            requires
                old(self).inv(),
                index_valid(NUM_PAGES, page_index),
                old(lctx).kernel_view_locking_state() is Acquire,
                !old(self).page_array.spec_index(page_index).view()
                    .locked_by_thread(old(lctx).thread_id()),
                old(lctx).lock_id_acyclic(old(self).page_array.lock_id_by_index(page_index)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self))
                    == kernel_k_to_kernel_u(*old(self)),

                // ---- Every held lock still matches lctx (page slot now locked) ----
                lock_id_aligned(final(self), final(lctx)),

                // ---- Field framing: only page_array's slot lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).iommu_table_map     == old(self).iommu_table_map,
                final(self).iommu_root_table     == old(self).iommu_root_table,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).iommu_tlb           == old(self).iommu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).scheduler_map     == old(self).scheduler_map,
                final(self).pcid_allocator_map == old(self).pcid_allocator_map,
                final(self).process_map       == old(self).process_map,
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_4k_map  == old(self).allocator_4k_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- page_array: only the targeted slot's lock state changed ----
                final(self).page_array.unchanged_except(&old(self).page_array, page_index),
                page_objects_unlocked(
                    old(self).page_array, old(lctx).thread_id(),
                ) ==> page_objects_unlocked_except(
                    final(self).page_array, final(lctx).thread_id(), set![page_index],
                ),

                // ---- LocalContext: phases preserved ----
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),

                // ---- The lock perm + lock ensures (forwarded from LockedArray::wlock) ----
                wlock_ensures(
                    old(self).page_array.spec_index(page_index).view(),
                    final(self).page_array.spec_index(page_index).view(),
                    old(self).page_array.lock_id_by_index(page_index),
                    final(lctx),
                    ret.view(),
                ),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().insert(
                    (
                        final(self).page_array.lock_id_by_index(page_index),
                        KernelObjId::Page(page_index),
                    ),
                ),
        {
            proof {
                assert(old(self).page_array.inv()) by {
                    reveal(page_array_wf);
                };
            }
            let ret = self.page_array.wlock(page_index, Tracked(&mut *lctx), Ghost(KernelObjId::Page(page_index)));
            proof {
                    assert(page_array_wf(self.page_array)) by {

                        reveal(page_array_wf);
                    };
                    assert(self.subsystems_inv()) by {
                        reveal(KernelK::default_pagetable_wf);
                    };
                    assert(self.memory_management_inv()) by {
                        assert(allocator_pages_wf(
                            self.page_array,
                            self.allocator_4k_map,
                            self.allocator_2m_map,
                            self.allocator_1g_map,
                        )) by {

                            reveal(allocator_4k_pages_wf);
                            reveal(allocator_2m_pages_wf);
                            reveal(allocator_1g_pages_wf);
                        };
                        assert(container_page_owner_wf(
                            self.container_map,
                            self.page_array,
                        )) by {

                            reveal(container_page_owner_wf);
                        };
                        assert(container_process_page_pagetable_wf(
                            self.container_map,
                            self.process_map,
                            self.pagetable_map,
                            self.page_array,
                        )) by {

                            reveal(container_process_page_pagetable_wf);
                        };
                        assert(container_pages_wf(
                            self.page_array,
                            self.container_map,
                        )) by {

                            reveal(container_pages_wf);
                        };
                        assert(process_pages_wf(
                            self.page_array,
                            self.process_map,
                        )) by {

                            reveal(process_pages_wf);
                        };
                        assert(hugepage_2m_wf(self.page_array)) by {

                            reveal(hugepage_2m_wf);
                        };
                        assert(hugepage_1g_wf(self.page_array)) by {

                            reveal(hugepage_1g_wf);
                        };
                        assert(mapped_4k_page_pagetable_wf(
                            self.pagetable_map,
                            self.page_array,
                        )) by {
                            reveal(pagetable_perms_wf);
                            reveal(mapped_4k_page_pagetable_wf);
                        };
                        assert(mapped_2m_page_pagetable_wf(
                            self.pagetable_map,
                            self.page_array,
                        )) by {
                            reveal(pagetable_perms_wf);
                            reveal(mapped_2m_page_pagetable_wf);
                        };
                        assert(mapped_1g_page_pagetable_wf(
                            self.pagetable_map,
                            self.page_array,
                        )) by {
                            reveal(pagetable_perms_wf);
                            reveal(mapped_1g_page_pagetable_wf);
                        };
                        assert(pagetable_pages_wf(
                            self.pagetable_map,
                            self.page_array,
                        )) by {

                            reveal(pagetable_pages_wf);
                        };
                        assert(iommu_table_pages_wf(
                            self.iommu_table_map,
                            self.page_array,
                        )) by {

                            reveal(iommu_table_pages_wf);
                        };
                        assert(pcid_allocator_pages_wf(
                            self.page_array,
                            self.pcid_allocator_map,
                        )) by {
                            pcid_allocator_pages_wf_preserved_for_page_lock_change(
                                old(self).page_array,
                                self.page_array,
                                self.pcid_allocator_map,
                                page_index,
                            );
                        };
                        assert(thread_pages_wf(
                            self.thread_map,
                            self.page_array,
                        )) by {

                            reveal(thread_pages_wf);
                        };
                        assert(thread_staged_pages_4k_wf(
                            self.thread_map,
                            self.page_array,
                        )) by {
                            reveal(thread_staged_pages_4k_wf);
                        };
                        assert(thread_staged_pages_2m_wf(
                            self.thread_map,
                            self.page_array,
                        )) by {
                            reveal(thread_staged_pages_2m_wf);
                        };
                        assert(thread_staged_pages_1g_wf(
                            self.thread_map,
                            self.page_array,
                        )) by {
                            reveal(thread_staged_pages_1g_wf);
                        };
                        assert(endpoint_pages_wf(
                            self.endpoint_map,
                            self.page_array,
                        )) by {

                            reveal(endpoint_pages_wf);
                        };
                        assert(container_allocator_global_free_4k_page_wf(
                            self.allocator_4k_map,
                            self.page_array,
                        )) by {
                            reveal(allocator_free_page_ptrs_wf);

                            reveal(container_allocator_free_4k_page_wf);
                            reveal(container_allocator_global_free_4k_page_wf);
                        };
                        assert(container_allocator_cpu_cache_free_4k_page_wf(
                            self.allocator_4k_map,
                            self.page_array,
                        )) by {
                            reveal(allocator_free_page_ptrs_wf);

                            reveal(container_allocator_free_4k_page_wf);
                            reveal(container_allocator_cpu_cache_free_4k_page_wf);
                        };
                        assert(container_allocator_free_4k_page_wf(
                            self.allocator_4k_map,
                            self.page_array,
                        )) by {
                            reveal(container_allocator_free_4k_page_wf);
                        };
                        assert(container_allocator_global_free_2m_page_wf(
                            self.allocator_2m_map,
                            self.page_array,
                        )) by {
                            reveal(allocator_free_page_ptrs_wf);

                            reveal(container_allocator_free_2m_page_wf);
                            reveal(container_allocator_global_free_2m_page_wf);
                        };
                        assert(container_allocator_cpu_cache_free_2m_page_wf(
                            self.allocator_2m_map,
                            self.page_array,
                        )) by {
                            reveal(allocator_free_page_ptrs_wf);

                            reveal(container_allocator_free_2m_page_wf);
                            reveal(container_allocator_cpu_cache_free_2m_page_wf);
                        };
                        assert(container_allocator_free_2m_page_wf(
                            self.allocator_2m_map,
                            self.page_array,
                        )) by {
                            reveal(container_allocator_free_2m_page_wf);
                        };
                        assert(container_allocator_global_free_1g_page_wf(
                            self.allocator_1g_map,
                            self.page_array,
                        )) by {
                            reveal(allocator_free_page_ptrs_wf);
                            reveal(container_allocator_free_1g_page_wf);
                            reveal(container_allocator_global_free_1g_page_wf);
                        };
                        assert(container_allocator_cpu_cache_free_1g_page_wf(
                            self.allocator_1g_map,
                            self.page_array,
                        )) by {
                            reveal(allocator_free_page_ptrs_wf);

                            reveal(container_allocator_free_1g_page_wf);
                            reveal(container_allocator_cpu_cache_free_1g_page_wf);
                        };
                        assert(container_allocator_free_1g_page_wf(
                            self.allocator_1g_map,
                            self.page_array,
                        )) by {
                            reveal(container_allocator_free_1g_page_wf);
                        };
                    };
                assert(lock_id_aligned(self, &*lctx)) by {

                    reveal(lock_id_aligned);

                };
                assert(page_objects_unlocked(
                    old(self).page_array, old(lctx).thread_id(),
                ) ==> page_objects_unlocked_except(
                    self.page_array, lctx.thread_id(), set![page_index],
                )) by {
                    reveal(page_objects_unlocked_except);
                };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                };
            }
            ret
        }

        #[verifier::spinoff_prover]
        pub fn wunlock_page(
            &mut self,
            page_index: PageIndex,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                index_valid(NUM_PAGES, page_index),
                old(self).page_array.spec_index(page_index).view().being_killed() == false,
                old(self).page_array.spec_index(page_index).view().wlocked_by(old(lctx)),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id()
                    == old(self).page_array.spec_index(page_index).view().locking_thread()->Write_lock_id,
                old(lctx).lock_entry_contains(
                    old(self).page_array.lock_id_by_index(page_index),
                    KernelObjId::Page(page_index)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self))
                    == kernel_k_to_kernel_u(*old(self)),

                // ---- Every held lock still matches lctx (page slot now released) ----
                lock_id_aligned(final(self), final(lctx)),

                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).iommu_table_map     == old(self).iommu_table_map,
                final(self).iommu_root_table     == old(self).iommu_root_table,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).iommu_tlb           == old(self).iommu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).scheduler_map     == old(self).scheduler_map,
                final(self).pcid_allocator_map == old(self).pcid_allocator_map,
                final(self).process_map       == old(self).process_map,
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_4k_map  == old(self).allocator_4k_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- page_array: only the targeted slot's lock state changed (now unlocked) ----
                final(self).page_array.unchanged_except(&old(self).page_array, page_index),
                final(self).page_array.lock_id_by_index(page_index)
                    == old(self).page_array.lock_id_by_index(page_index),

                // ---- LocalContext: lock dropped; thread preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` flips it Acquire → Release (same trap as the
                // `LockedArray::wunlock` NOTE).
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,

                // ---- wunlock ensures (forwarded from LockedArray::wunlock) ----
                wunlock_ensures(old(self).page_array.spec_index(page_index).view(), final(self).page_array.spec_index(page_index).view()),
                page_objects_unlocked_except(
                    old(self).page_array, old(lctx).thread_id(), set![page_index],
                ) ==> page_objects_unlocked(
                    final(self).page_array, final(lctx).thread_id()),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().remove(
                    (
                        old(self).page_array.lock_id_by_index(page_index),
                        KernelObjId::Page(page_index),
                    ),
                ),
                unlock_ensures(
                    old(lctx),
                    final(lctx),
                    (),
                    lock_perm.view().lock_id(),
                    KernelObjId::Page(page_index),
                    old(self).page_array.lock_id_by_index(page_index),
                ),
        {
            assert(self.page_array.inv()) by {
                reveal(page_array_wf);
            };
            self.page_array.wunlock(page_index, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::Page(page_index)));
            proof {
                    assert(page_array_wf(self.page_array)) by {

                        reveal(page_array_wf);
                    };
                    assert(self.subsystems_inv()) by {
                        reveal(KernelK::default_pagetable_wf);
                    };
                    assert(self.memory_management_inv()) by {
                        assert(allocator_pages_wf(
                            self.page_array,
                            self.allocator_4k_map,
                            self.allocator_2m_map,
                            self.allocator_1g_map,
                        )) by {

                            reveal(allocator_4k_pages_wf);
                            reveal(allocator_2m_pages_wf);
                            reveal(allocator_1g_pages_wf);
                        };
                        assert(container_page_owner_wf(
                            self.container_map,
                            self.page_array,
                        )) by {

                            reveal(container_page_owner_wf);
                        };
                        assert(container_process_page_pagetable_wf(
                            self.container_map,
                            self.process_map,
                            self.pagetable_map,
                            self.page_array,
                        )) by {

                            reveal(container_process_page_pagetable_wf);
                        };
                        assert(container_pages_wf(
                            self.page_array,
                            self.container_map,
                        )) by {

                            reveal(container_pages_wf);
                        };
                        assert(process_pages_wf(
                            self.page_array,
                            self.process_map,
                        )) by {

                            reveal(process_pages_wf);
                        };
                        assert(hugepage_2m_wf(self.page_array)) by {

                            reveal(hugepage_2m_wf);
                        };
                        assert(hugepage_1g_wf(self.page_array)) by {

                            reveal(hugepage_1g_wf);
                        };
                        assert(mapped_4k_page_pagetable_wf(
                            self.pagetable_map,
                            self.page_array,
                        )) by {
                            reveal(pagetable_perms_wf);
                            reveal(mapped_4k_page_pagetable_wf);
                        };
                        assert(mapped_2m_page_pagetable_wf(
                            self.pagetable_map,
                            self.page_array,
                        )) by {
                            reveal(pagetable_perms_wf);
                            reveal(mapped_2m_page_pagetable_wf);
                        };
                        assert(mapped_1g_page_pagetable_wf(
                            self.pagetable_map,
                            self.page_array,
                        )) by {
                            reveal(pagetable_perms_wf);
                            reveal(mapped_1g_page_pagetable_wf);
                        };
                        assert(pagetable_pages_wf(
                            self.pagetable_map,
                            self.page_array,
                        )) by {

                            reveal(pagetable_pages_wf);
                        };
                        assert(iommu_table_pages_wf(
                            self.iommu_table_map,
                            self.page_array,
                        )) by {

                            reveal(iommu_table_pages_wf);
                        };
                        assert(pcid_allocator_pages_wf(
                            self.page_array,
                            self.pcid_allocator_map,
                        )) by {
                            pcid_allocator_pages_wf_preserved_for_page_lock_change(
                                old(self).page_array,
                                self.page_array,
                                self.pcid_allocator_map,
                                page_index,
                            );
                        };
                        assert(thread_pages_wf(
                            self.thread_map,
                            self.page_array,
                        )) by {

                            reveal(thread_pages_wf);
                        };
                        assert(thread_staged_pages_4k_wf(
                            self.thread_map,
                            self.page_array,
                        )) by {
                            reveal(thread_staged_pages_4k_wf);
                        };
                        assert(thread_staged_pages_2m_wf(
                            self.thread_map,
                            self.page_array,
                        )) by {
                            reveal(thread_staged_pages_2m_wf);
                        };
                        assert(thread_staged_pages_1g_wf(
                            self.thread_map,
                            self.page_array,
                        )) by {
                            reveal(thread_staged_pages_1g_wf);
                        };
                        assert(endpoint_pages_wf(
                            self.endpoint_map,
                            self.page_array,
                        )) by {

                            reveal(endpoint_pages_wf);
                        };
                        assert(container_allocator_global_free_4k_page_wf(
                            self.allocator_4k_map,
                            self.page_array,
                        )) by {
                            reveal(allocator_free_page_ptrs_wf);

                            reveal(container_allocator_free_4k_page_wf);
                            reveal(container_allocator_global_free_4k_page_wf);
                        };
                        assert(container_allocator_cpu_cache_free_4k_page_wf(
                            self.allocator_4k_map,
                            self.page_array,
                        )) by {
                            reveal(allocator_free_page_ptrs_wf);

                            reveal(container_allocator_free_4k_page_wf);
                            reveal(container_allocator_cpu_cache_free_4k_page_wf);
                        };
                        assert(container_allocator_free_4k_page_wf(
                            self.allocator_4k_map,
                            self.page_array,
                        )) by {
                            reveal(container_allocator_free_4k_page_wf);
                        };
                        assert(container_allocator_global_free_2m_page_wf(
                            self.allocator_2m_map,
                            self.page_array,
                        )) by {
                            reveal(allocator_free_page_ptrs_wf);

                            reveal(container_allocator_free_2m_page_wf);
                            reveal(container_allocator_global_free_2m_page_wf);
                        };
                        assert(container_allocator_cpu_cache_free_2m_page_wf(
                            self.allocator_2m_map,
                            self.page_array,
                        )) by {
                            reveal(allocator_free_page_ptrs_wf);

                            reveal(container_allocator_free_2m_page_wf);
                            reveal(container_allocator_cpu_cache_free_2m_page_wf);
                        };
                        assert(container_allocator_free_2m_page_wf(
                            self.allocator_2m_map,
                            self.page_array,
                        )) by {
                            reveal(container_allocator_free_2m_page_wf);
                        };
                        assert(container_allocator_global_free_1g_page_wf(
                            self.allocator_1g_map,
                            self.page_array,
                        )) by {
                            reveal(allocator_free_page_ptrs_wf);

                            reveal(container_allocator_free_1g_page_wf);
                            reveal(container_allocator_global_free_1g_page_wf);
                        };
                        assert(container_allocator_cpu_cache_free_1g_page_wf(
                            self.allocator_1g_map,
                            self.page_array,
                        )) by {
                            reveal(allocator_free_page_ptrs_wf);

                            reveal(container_allocator_free_1g_page_wf);
                            reveal(container_allocator_cpu_cache_free_1g_page_wf);
                        };
                        assert(container_allocator_free_1g_page_wf(
                            self.allocator_1g_map,
                            self.page_array,
                        )) by {
                            reveal(container_allocator_free_1g_page_wf);
                        };
                    };
                assert(lock_id_aligned(self, &*lctx)) by {

                    reveal(lock_id_aligned);

                };
                assert(page_objects_unlocked_except(
                    old(self).page_array, old(lctx).thread_id(), set![page_index],
                ) ==> page_objects_unlocked(
                    self.page_array, lctx.thread_id(),
                )) by {

                    reveal(page_objects_unlocked_except);
                };
            }
        }

}
} // verus!
