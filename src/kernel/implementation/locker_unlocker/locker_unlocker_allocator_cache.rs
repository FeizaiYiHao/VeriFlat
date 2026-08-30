use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
        #[verifier::spinoff_prover]
        pub fn wlock_allocator_cache(
            &mut self,
            alloc_ptr_4k: RwLockPageAllocatorPtr,
            cache_cpu: CpuId,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Tracked<LockPerm>)
            requires
                old(self).inv(),
                old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
                index_valid(NUM_CPUS, cache_cpu),
                !old(lctx).allocator_cache_4k_lock_map().dom().contains(
                    (alloc_ptr_4k, cache_cpu)),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).lock_id_acyclic(LockId{
                    container: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).container_depth(),
                    process: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).process_depth(),
                    major: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).view().view().current_lock_major(),
                    minor: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).lock_minor(),
                }),
                typed_lock_maps_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),

                // ---- Every held lock still matches lctx (cache now locked) ----
                typed_lock_maps_aligned(final(self), final(lctx)),

                // ---- Field framing: only allocator_4k_map's cache lock state moves ----
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

                // ---- allocator_4k_map: dom unchanged; only the targeted entry's cache lock state changed ----
                final(self).allocator_4k_map.dom() == old(self).allocator_4k_map.dom(),
                final(self).allocator_4k_map.perms_wf(),
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).owning_container == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).owning_container,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.unchanged_except(&old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches, cache_cpu),
                forall|k: usize| #![auto] old(self).allocator_4k_map.dom().contains(k) && k != alloc_ptr_4k ==>
                    final(self).allocator_4k_map.spec_index(k) == old(self).allocator_4k_map.spec_index(k),

                // ---- LocalContext: phases preserved ----
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),

                // ---- The lock perm + lock ensures (forwarded from UnLockedMap::wlock_cache) ----
                wlock_ensures(
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).view(),
                    final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).view(),
                    LockId{
                        container: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).container_depth(),
                        process: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).process_depth(),
                        major: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).view().view().current_lock_major(),
                        minor: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).lock_minor(),
                    },
                    final(lctx),
                    ret.view(),
                ),
                typed_lock_maps_inserted(
                    old(lctx), final(lctx),
                    KernelObjId::AllocatorCache(
                        PageSize::SZ4k, alloc_ptr_4k, cache_cpu),
                    TypedHeldLock {
                        lock_id: final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                            .cpu_caches.lock_id_by_index(cache_cpu),
                        mode: TypedLockMode::Write,
                    }),
                final(lctx).allocator_cache_4k_lock_map().contains_pair((alloc_ptr_4k, cache_cpu), TypedHeldLock {
                        lock_id: final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                            .cpu_caches.lock_id_by_index(cache_cpu),
                        mode: TypedLockMode::Write,
                    }),
                ret.view().ordering_lock_id()
                    == final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.lock_id_by_index(cache_cpu),
        {
            proof {
                assert(
                    {
                        &&& old(self).allocator_4k_map.perms_wf()
                        &&& old(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf()
                    }
                ) by {
                    reveal(allocator_perms_wf);
                };
                assert(wlock_requires(
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(cache_cpu).view(),
                    old(lctx),
                )) by {
                    reveal(UnLockedMap::typed_cache_lock_map_aligned);
                };
            }
            let ret = self.allocator_4k_map.wlock_cache(alloc_ptr_4k, cache_cpu, Tracked(&mut *lctx), Ghost(PageSize::SZ4k));

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
                        allocator_4k_cache_lock_op_preserves_invariant_fields(
                            old(self).allocator_4k_map,
                            self.allocator_4k_map,
                            alloc_ptr_4k,
                            cache_cpu,
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
                assert(typed_lock_maps_aligned(self, &*lctx)) by {
                    reveal(UnLockedMap::typed_cache_lock_map_aligned);
                    reveal(UnLockedMap::typed_quota_lock_map_aligned);
                    reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
                };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                };
            }
            ret
        }

        #[verifier::spinoff_prover]
        pub fn wunlock_allocator_cache(
            &mut self,
            alloc_ptr_4k: RwLockPageAllocatorPtr,
            cache_cpu: CpuId,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
                index_valid(NUM_CPUS, cache_cpu),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id()
                    == old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(cache_cpu).view().locking_thread()->Write_lock_id,
                typed_lock_map_contains_mode(
                    old(lctx).allocator_cache_4k_lock_map(),
                    (alloc_ptr_4k, cache_cpu), TypedLockMode::Write),
                typed_lock_maps_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),

                // ---- Every held lock still matches lctx (cache now released) ----
                typed_lock_maps_aligned(final(self), final(lctx)),

                // ---- Field framing: only allocator_4k_map's cache lock state moves ----
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

                // ---- allocator_4k_map: dom unchanged; only the targeted entry's cache lock state changed (now unlocked) ----
                final(self).allocator_4k_map.dom() == old(self).allocator_4k_map.dom(),
                final(self).allocator_4k_map.perms_wf(),
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).owning_container == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).owning_container,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.unchanged_except(&old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches, cache_cpu),
                forall|k: usize| #![auto] old(self).allocator_4k_map.dom().contains(k) && k != alloc_ptr_4k ==>
                    final(self).allocator_4k_map.spec_index(k) == old(self).allocator_4k_map.spec_index(k),

                // ---- LocalContext: lock dropped; thread preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` transitions it Acquire -> Release, so restating
                // `== old` would contradict it and make the postcondition `false`
                // in an Acquire section (same trap as the NOTE on
                // `LockedArray::wunlock`). user_view is separately preserved.
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,

                // ---- wunlock ensures (forwarded from UnLockedMap::wunlock_cache) ----
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches.spec_index(cache_cpu).lock_id()
                    == old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(cache_cpu).lock_id(),
                !final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches.spec_index(cache_cpu).view()
                    .wlocked_by_thread(final(lctx).thread_id()),
                !final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches.spec_index(cache_cpu).view().locked(),
                wunlock_ensures(
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).view(),
                    final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).view(),
                ),
                typed_lock_maps_removed(
                    old(lctx), final(lctx),
                    KernelObjId::AllocatorCache(
                        PageSize::SZ4k, alloc_ptr_4k, cache_cpu)),
                !final(lctx).allocator_cache_4k_lock_map().dom().contains(
                    (alloc_ptr_4k, cache_cpu)),
                unlock_ensures(
                    old(lctx),
                    final(lctx),
                    (),
                    lock_perm.view().lock_id(),
                    KernelObjId::AllocatorCache(
                        PageSize::SZ4k, alloc_ptr_4k, cache_cpu,
                    ),
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(cache_cpu).lock_id(),
                ),
        {
            proof {
                assert(
                    {
                        &&& old(self).allocator_4k_map.perms_wf()
                        &&& old(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf()
                    }
                ) by {
                    reveal(allocator_perms_wf);
                };
                assert(old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches.spec_index(cache_cpu).view()
                    .wlocked_by(old(lctx))) by {
                    reveal(UnLockedMap::typed_cache_lock_map_aligned);
                };
                assert(old(lctx).lock_entry_contains(
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.lock_id_by_index(cache_cpu),
                    KernelObjId::AllocatorCache(
                        PageSize::SZ4k, alloc_ptr_4k, cache_cpu,
                    ),
                )) by {
                    reveal(UnLockedMap::typed_cache_lock_map_aligned);
                };
            }
            self.allocator_4k_map.wunlock_cache(alloc_ptr_4k, cache_cpu, Tracked(&mut *lctx), lock_perm, Ghost(PageSize::SZ4k));

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
                        allocator_4k_cache_lock_op_preserves_invariant_fields(
                            old(self).allocator_4k_map,
                            self.allocator_4k_map,
                            alloc_ptr_4k,
                            cache_cpu,
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
                assert(typed_lock_maps_aligned(self, &*lctx)) by {
                    reveal(UnLockedMap::typed_cache_lock_map_aligned);
                    reveal(UnLockedMap::typed_quota_lock_map_aligned);
                    reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
                };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                };
            }
        }
}
} // verus!
