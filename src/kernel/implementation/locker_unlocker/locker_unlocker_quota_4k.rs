use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
        #[verifier::spinoff_prover]
        pub fn wlock_quota_4k(
            &mut self,
            alloc_ptr_4k: RwLockPageAllocatorPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Tracked<LockPerm>)
            requires
                old(self).inv(),
                old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
                wlock_requires(
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
                    old(lctx),
                ),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).lock_id_acyclic(old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.lock_id()),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Every held lock still matches lctx (quota now locked) ----

                // ---- Dynamic lock ids remain aligned ----
                lock_id_aligned(final(self), final(lctx)),

                // ---- Field framing: only allocator_4k_map's quota lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).iommu_table_map     == old(self).iommu_table_map,
                final(self).iommu_root_table     == old(self).iommu_root_table,
                final(self).page_array        == old(self).page_array,
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
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- allocator_4k_map: dom unchanged; only the targeted entry's quota lock state changed ----
                final(self).allocator_4k_map.dom() == old(self).allocator_4k_map.dom(),
                final(self).allocator_4k_map.perms_wf(),
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).owning_container == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).owning_container,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages,
                forall|k: usize| #![auto] old(self).allocator_4k_map.dom().contains(k) && k != alloc_ptr_4k ==>
                    final(self).allocator_4k_map.spec_index(k) == old(self).allocator_4k_map.spec_index(k),

                // ---- LocalContext: phases preserved ----
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),

                // ---- The lock perm + lock ensures (forwarded from UnLockedMap::wlock_quota) ----
                wlock_ensures(
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
                    final(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.lock_id(),
                    final(lctx),
                    ret.view(),
                ),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().insert(
                    (
                        final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                            .quota.lock_id(),
                        KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k),
                    ),
                ),
        {
            proof {
                assert(old(self).allocator_4k_map.perms_wf()) by {
                    reveal(allocator_perms_wf);
                };
            }
            let ret = self.allocator_4k_map.wlock_quota(alloc_ptr_4k, Tracked(&mut *lctx), Ghost(PageSize::SZ4k));

            proof {
                    assert(allocator_perms_wf(
                        self.allocator_4k_map,
                    )) by {
                        reveal(allocator_perms_wf);
                    };
                    assert(allocator_4k_invariant_fields_unchanged(
                        old(self).allocator_4k_map,
                        self.allocator_4k_map,
                    )) by {
                        allocator_4k_quota_lock_op_preserves_invariant_fields(
                            old(self).allocator_4k_map,
                            self.allocator_4k_map,
                            alloc_ptr_4k,
                        );
                    };
                    assert(allocator_quota_value_framed_fields_unchanged(
                        old(self).allocator_4k_map,
                        self.allocator_4k_map,
                    )) by {
                        reveal(allocator_4k_invariant_fields_unchanged);
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
                            lemma_no_change_imply_allocator_pages_wf_forall();
                        };
                        assert(container_process_allocator_quota_4k_wf(
                            self.container_map,
                            self.process_map,
                            self.thread_map,
                            self.allocator_4k_map,
                        )) by {
                            assert forall|c_ptr: RwLockContainerPtr|
                                #![trigger self.container_map.spec_index(c_ptr)
                                    .view_rodata().view().allocator_ptr_4k]
                                self.container_map.dom().contains(c_ptr)
                            implies {
                                let alloc_ptr = self.container_map.spec_index(c_ptr)
                                    .view_rodata().view().allocator_ptr_4k;
                                &&& self.allocator_4k_map.spec_index(alloc_ptr).quota.view()
                                    == old(self).allocator_4k_map.spec_index(alloc_ptr).quota.view()
                                &&& self.allocator_4k_map.spec_index(alloc_ptr).total_free_pages
                                    == old(self).allocator_4k_map.spec_index(alloc_ptr).total_free_pages
                            } by {
                                assert(old(self).allocator_4k_map.dom().contains(
                                    self.container_map.spec_index(c_ptr)
                                        .view_rodata().view().allocator_ptr_4k,
                                )) by {
                                    reveal(container_allocator_wf);
                                };
                                assert(self.allocator_4k_map.spec_index(
                                    self.container_map.spec_index(c_ptr)
                                        .view_rodata().view().allocator_ptr_4k,
                                ).owning_container
                                    == old(self).allocator_4k_map.spec_index(
                                        self.container_map.spec_index(c_ptr)
                                            .view_rodata().view().allocator_ptr_4k,
                                    ).owning_container) by {
                                    reveal(allocator_4k_invariant_fields_unchanged);
                                };
                                reveal(allocator_4k_invariant_fields_unchanged);
                            };
                            reveal(allocator_4k_invariant_fields_unchanged);
                            reveal(container_process_allocator_quota_4k_wf);
                            reveal(container_allocator_wf);
                        };
                        assert(container_allocator_wf(
                            self.container_map,
                            self.allocator_4k_map,
                            self.allocator_2m_map,
                            self.allocator_1g_map,
                        )) by {
                            lemma_no_change_imply_container_allocator_wf_forall();
                        };
                        assert(allocator_free_page_ptrs_wf(
                            self.allocator_4k_map,
                        )) by {
                            lemma_no_change_imply_allocator_free_page_ptrs_wf_forall();
                        };
                        assert(container_allocator_free_4k_page_wf(
                            self.allocator_4k_map,
                            self.page_array,
                        )) by {
                            assert forall|a_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId|
                                #![trigger self.allocator_4k_map.spec_index(a_ptr)
                                    .cpu_caches.spec_index(cpu_id).view().view()]
                                self.allocator_4k_map.dom().contains(a_ptr)
                                    && index_valid(NUM_CPUS, cpu_id)
                            implies
                                self.allocator_4k_map.spec_index(a_ptr).cpu_caches
                                    .spec_index(cpu_id).view().view()
                                == old(self).allocator_4k_map.spec_index(a_ptr).cpu_caches
                                    .spec_index(cpu_id).view().view()
                            by {
                                assert(self.allocator_4k_map.spec_index(a_ptr).owning_container
                                    == old(self).allocator_4k_map.spec_index(a_ptr).owning_container) by {
                                    reveal(allocator_4k_invariant_fields_unchanged);
                                };
                                reveal(allocator_4k_invariant_fields_unchanged);
                            };
                            reveal(allocator_4k_invariant_fields_unchanged);
                            lemma_no_change_imply_container_allocator_free_4k_page_wf_forall();
                        };
                    };
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);
                };
            }
            ret
        }

        /// Companion of `wlock_quota_4k` for the unlock side. Wraps
        /// `UnLockedMap::wunlock_quota` for `allocator_4k_map` and
        /// re-establishes `inv()` immediately afterwards. Same template as
        /// `wlock_quota_4k`; the quota's `view()` is preserved by
        /// `wunlock_ensures`, so the fold conjunct holds via the same set-fold
        /// axioms.
        #[verifier::spinoff_prover]
        pub fn wunlock_quota_4k(
            &mut self,
            alloc_ptr_4k: RwLockPageAllocatorPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.inv(),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id()
                    == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota
                        .locking_thread()->Write_lock_id,
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota
                    .wlocked_by(old(lctx)),
                old(lctx).lock_entry_contains(
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .quota.lock_id(),
                    KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Every held lock still matches lctx (quota now released) ----

                // ---- Dynamic lock ids remain aligned ----
                lock_id_aligned(final(self), final(lctx)),

                // ---- Field framing: only allocator_4k_map's quota lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).iommu_table_map     == old(self).iommu_table_map,
                final(self).iommu_root_table     == old(self).iommu_root_table,
                final(self).page_array        == old(self).page_array,
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
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- allocator_4k_map: dom unchanged; only the targeted entry's quota lock state changed (now unlocked) ----
                final(self).allocator_4k_map.dom() == old(self).allocator_4k_map.dom(),
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).owning_container == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).owning_container,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages,
                forall|k: usize| #![auto] old(self).allocator_4k_map.dom().contains(k) && k != alloc_ptr_4k ==>
                    final(self).allocator_4k_map.spec_index(k) == old(self).allocator_4k_map.spec_index(k),

                // ---- LocalContext: lock dropped; thread preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` transitions it Acquire -> Release, so restating
                // `== old` would contradict it and make the postcondition `false`
                // in an Acquire section. `unlock_ensures` is the source of truth
                // for the phase transition (same trap as the NOTE on
                // `LockedArray::wunlock`). user_view is separately preserved.
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,

                // ---- wunlock ensures (forwarded from UnLockedMap::wunlock_quota) ----
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .quota.lock_id()
                    == old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .quota.lock_id(),
                wunlock_ensures(
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
                    final(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
                ),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().remove(
                    (
                        old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                            .quota.lock_id(),
                        KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k),
                    ),
                ),
        {
            proof {
                assert(old(self).allocator_4k_map.perms_wf()) by {
                    reveal(allocator_perms_wf);
                };
            }
            self.allocator_4k_map.wunlock_quota(alloc_ptr_4k, Tracked(&mut *lctx), lock_perm, Ghost(PageSize::SZ4k));

            proof {
                    assert(allocator_perms_wf(
                        self.allocator_4k_map,
                    )) by {
                        reveal(allocator_perms_wf);
                    };
                    assert(allocator_4k_invariant_fields_unchanged(
                        old(self).allocator_4k_map,
                        self.allocator_4k_map,
                    )) by {
                        allocator_4k_quota_lock_op_preserves_invariant_fields(
                            old(self).allocator_4k_map,
                            self.allocator_4k_map,
                            alloc_ptr_4k,
                        );
                    };
                    assert(allocator_quota_value_framed_fields_unchanged(
                        old(self).allocator_4k_map,
                        self.allocator_4k_map,
                    )) by {
                        reveal(allocator_4k_invariant_fields_unchanged);
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
                            lemma_no_change_imply_allocator_pages_wf_forall();
                        };
                        assert(container_process_allocator_quota_4k_wf(
                            self.container_map,
                            self.process_map,
                            self.thread_map,
                            self.allocator_4k_map,
                        )) by {
                            assert forall|c_ptr: RwLockContainerPtr|
                                #![trigger self.container_map.spec_index(c_ptr)
                                    .view_rodata().view().allocator_ptr_4k]
                                self.container_map.dom().contains(c_ptr)
                            implies {
                                let alloc_ptr = self.container_map.spec_index(c_ptr)
                                    .view_rodata().view().allocator_ptr_4k;
                                &&& self.allocator_4k_map.spec_index(alloc_ptr).quota.view()
                                    == old(self).allocator_4k_map.spec_index(alloc_ptr).quota.view()
                                &&& self.allocator_4k_map.spec_index(alloc_ptr).total_free_pages
                                    == old(self).allocator_4k_map.spec_index(alloc_ptr).total_free_pages
                            } by {
                                assert(old(self).allocator_4k_map.dom().contains(
                                    self.container_map.spec_index(c_ptr)
                                        .view_rodata().view().allocator_ptr_4k,
                                )) by {
                                    reveal(container_allocator_wf);
                                };
                                assert(self.allocator_4k_map.spec_index(
                                    self.container_map.spec_index(c_ptr)
                                        .view_rodata().view().allocator_ptr_4k,
                                ).owning_container
                                    == old(self).allocator_4k_map.spec_index(
                                        self.container_map.spec_index(c_ptr)
                                            .view_rodata().view().allocator_ptr_4k,
                                    ).owning_container) by {
                                    reveal(allocator_4k_invariant_fields_unchanged);
                                };
                                reveal(allocator_4k_invariant_fields_unchanged);
                            };
                            reveal(allocator_4k_invariant_fields_unchanged);
                            reveal(container_process_allocator_quota_4k_wf);
                            reveal(container_allocator_wf);
                        };
                        assert(container_allocator_wf(
                            self.container_map,
                            self.allocator_4k_map,
                            self.allocator_2m_map,
                            self.allocator_1g_map,
                        )) by {
                            lemma_no_change_imply_container_allocator_wf_forall();
                        };
                        assert(allocator_free_page_ptrs_wf(
                            self.allocator_4k_map,
                        )) by {
                            lemma_no_change_imply_allocator_free_page_ptrs_wf_forall();
                        };
                        assert(container_allocator_free_4k_page_wf(
                            self.allocator_4k_map,
                            self.page_array,
                        )) by {
                            assert forall|a_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId|
                                #![trigger self.allocator_4k_map.spec_index(a_ptr)
                                    .cpu_caches.spec_index(cpu_id).view().view()]
                                self.allocator_4k_map.dom().contains(a_ptr)
                                    && index_valid(NUM_CPUS, cpu_id)
                            implies
                                self.allocator_4k_map.spec_index(a_ptr).cpu_caches
                                    .spec_index(cpu_id).view().view()
                                == old(self).allocator_4k_map.spec_index(a_ptr).cpu_caches
                                    .spec_index(cpu_id).view().view()
                            by {
                                assert(self.allocator_4k_map.spec_index(a_ptr).owning_container
                                    == old(self).allocator_4k_map.spec_index(a_ptr).owning_container) by {
                                    reveal(allocator_4k_invariant_fields_unchanged);
                                };
                                reveal(allocator_4k_invariant_fields_unchanged);
                            };
                            reveal(allocator_4k_invariant_fields_unchanged);
                            lemma_no_change_imply_container_allocator_free_4k_page_wf_forall();
                        };
                    };
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);
                };
            }
        }
}
} // verus!
