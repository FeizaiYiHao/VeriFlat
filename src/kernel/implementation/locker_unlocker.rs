use vstd::prelude::*;
use crate::*;
verus! {
    impl KernelK{
        pub fn wlock_cpu(
            &mut self,
            cpu_id: CpuId,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Tracked<LockPerm>)
            requires
                old(self).inv(),
                old(lctx).wf(),
                cpu_id_valid(cpu_id),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).lock_id_acyclic(old(self).cpu_array.lock_id_by_index(cpu_id)),
                old(self).locked_objects_match_lctx(old(lctx)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                final(lctx).wf(),

                // ---- Every held lock still matches lctx (cpu now locked) ----
                final(self).locked_objects_match_lctx(final(lctx)),

                // ---- Dynamic lock ids remain aligned ----
                lock_id_aligned(final(self), final(lctx)),

                // ---- Field framing: only cpu_array's lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).iommu_table_map     == old(self).iommu_table_map,
                final(self).iommu_root_table     == old(self).iommu_root_table,
                final(self).page_array        == old(self).page_array,
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

                // ---- cpu_array: only the targeted slot's lock state changed ----
                final(self).cpu_array.unchanged_except(&old(self).cpu_array, cpu_id),
                final(self).cpu_array.inv(),

                // ---- LocalContext: phases preserved ----
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),

                // ---- The lock perm + lock ensures (forwarded from LockedArray::wlock) ----
                wlock_ensures(
                    old(self).cpu_array.spec_index(cpu_id).view(),
                    final(self).cpu_array.spec_index(cpu_id).view(),
                    old(self).cpu_array.lock_id_by_index(cpu_id),
                    final(lctx).thread_id(),
                    ret.view(),
                ),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().insert(
                    final(self).cpu_array.lock_id_by_index(cpu_id),
                ),
        {
            proof {
                assert(old(self).cpu_array.inv()) by {
                    reveal(cpu_array_wf);
                };
                assert(old(lctx).obj_id_fresh(KernelObjId::Cpu(cpu_id))) by {
                    reveal(LocalContext::wf);
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(cpu_locked_match_lctx);
                    reveal(LocalContext::obj_id_fresh);
                    reveal(LocalContext::lock_map_contains);
                };
                assert(wlock_requires(old(self).cpu_array.spec_index(cpu_id).view(), old(lctx))) by {
                    reveal(wlock_requires);
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(cpu_locked_match_lctx);
                    reveal(LocalContext::obj_id_fresh);
                    reveal(LocalContext::lock_map_contains);
                };
            }
            let ret = self.cpu_array.wlock(cpu_id, Tracked(&mut *lctx), Ghost(KernelObjId::Cpu(cpu_id)));
            proof {
                assert(self.inv()) by {
                    assert(cpu_array_wf(
                        self.cpu_array,
                        self.default_pagetable.view(),
                    )) by {
                        reveal(cpu_array_wf);
                    };
                    assert(self.subsystems_inv()) by {
                        reveal(KernelK::default_pagetable_wf);
                    };
                    assert(self.process_management_inv()) by {
                        assert(container_cpu_wf(
                            self.container_map,
                            self.cpu_array,
                        )) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(container_perms_wf);
                            reveal(container_cpu_wf);
                        };
                        assert(process_cpu_wf(
                            self.process_map,
                            self.cpu_array,
                        )) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(process_cpu_wf);
                        };
                        assert(thread_cpu_wf(
                            self.thread_map,
                            self.cpu_array,
                        )) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(thread_cpu_wf);
                        };
                    };
                    assert(cpu_dirty_map_wf(
                        self.container_map,
                        self.process_map,
                        self.cpu_array,
                        self.cpu_tlb,
                        self.pagetable_map,
                    )) by {
                        reveal(LockedArray::payloads_unchanged);
                        reveal(cpu_dirty_map_contains_container_processes);
                        reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                        reveal(cpu_dirty_map_proc_pcid_match);
                        reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                        reveal(container_cpu_wf);
                    };
                    assert(tlb_wf_spec(
                        self.cpu_tlb,
                        self.pagetable_map,
                        self.cpu_array,
                    )) by {
                        reveal(LockedArray::payloads_unchanged);
                        reveal(tlb_wf_spec);
                    };
                    reveal(KernelK::inv);
                };
                // ---- locked_objects_match_lctx: cpu slot gained, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(cpu_locked_match_lctx);
                };
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);
                    reveal(page_lock_id_aligned);
                    reveal(lock_ensures);
                    reveal(LocalContext::lock_maps_inserted);
                };
            }
            ret
        }

        pub fn wunlock_cpu(
            &mut self,
            cpu_id: CpuId,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                old(lctx).wf(),
                cpu_id_valid(cpu_id),
                old(self).cpu_array.spec_index(cpu_id).view().being_killed() == false,
                old(self).cpu_array.spec_index(cpu_id).view().wlocked_by(old(lctx)),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id()
                    == old(self).cpu_array.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
                old(self).locked_objects_match_lctx(old(lctx)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                final(lctx).wf(),

                // ---- Every held lock still matches lctx (cpu now released) ----
                final(self).locked_objects_match_lctx(final(lctx)),

                // ---- Dynamic lock ids remain aligned ----
                lock_id_aligned(final(self), final(lctx)),

                // ---- Field framing: only cpu_array's lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).iommu_table_map     == old(self).iommu_table_map,
                final(self).iommu_root_table     == old(self).iommu_root_table,
                final(self).page_array        == old(self).page_array,
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

                // ---- cpu_array: only the targeted slot's lock state changed (now unlocked) ----
                final(self).cpu_array.unchanged_except(&old(self).cpu_array, cpu_id),
                final(self).cpu_array.inv(),
                final(self).cpu_array.spec_index(cpu_id).view().locking_thread() is None,
                wunlock_ensures(
                    old(self).cpu_array.spec_index(cpu_id).view(),
                    final(self).cpu_array.spec_index(cpu_id).view(),
                ),

                // ---- LocalContext: lock dropped; thread preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` transitions it Acquire -> Release, so restating
                // `== old` would contradict it and make the postcondition `false`
                // in an Acquire section. `unlock_ensures` is the source of truth
                // for the phase transition (same trap as the NOTE on
                // `LockedArray::wunlock`). user_view is separately preserved.
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,

                final(lctx).lock_id_set() == old(lctx).lock_id_set().remove(
                    old(self).cpu_array.lock_id_by_index(cpu_id),
                ),
        {
            proof {
                assert({
                    &&& old(self).cpu_array.inv()
                    &&& old(lctx).cpu_lock_map().dom().contains(cpu_id)
                    &&& old(lctx).cpu_lock_map().spec_index(cpu_id)
                        == old(self).cpu_array.lock_id_by_index(cpu_id)
                }) by {
                    reveal(cpu_array_wf);
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(cpu_locked_match_lctx);
                    reveal(LocalContext::lock_map_contains);
                };
            }
            self.cpu_array.wunlock(cpu_id, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::Cpu(cpu_id)));
            // Re-establish inv(). Only `cpu_array[cpu_id]`'s lock state moved
            // (now unlocked); every payload view, every other slot, and every
            // other KernelK field is unchanged. Same template as wlock_cpu.
            proof {
                assert(self.inv()) by {
                    assert(cpu_array_wf(
                        self.cpu_array,
                        self.default_pagetable.view(),
                    )) by {
                        reveal(cpu_array_wf);
                    };
                    assert(self.subsystems_inv()) by {
                        reveal(KernelK::default_pagetable_wf);
                    };
                    assert(self.process_management_inv()) by {
                        assert(container_cpu_wf(
                            self.container_map,
                            self.cpu_array,
                        )) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(container_perms_wf);
                            reveal(container_cpu_wf);
                        };
                        assert(process_cpu_wf(
                            self.process_map,
                            self.cpu_array,
                        )) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(process_cpu_wf);
                        };
                        assert(thread_cpu_wf(
                            self.thread_map,
                            self.cpu_array,
                        )) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(thread_cpu_wf);
                        };
                    };
                    assert(cpu_dirty_map_wf(
                        self.container_map,
                        self.process_map,
                        self.cpu_array,
                        self.cpu_tlb,
                        self.pagetable_map,
                    )) by {
                        reveal(LockedArray::payloads_unchanged);
                        reveal(cpu_dirty_map_contains_container_processes);
                        reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                        reveal(cpu_dirty_map_proc_pcid_match);
                        reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                        reveal(container_cpu_wf);
                    };
                    assert(tlb_wf_spec(
                        self.cpu_tlb,
                        self.pagetable_map,
                        self.cpu_array,
                    )) by {
                        reveal(LockedArray::payloads_unchanged);
                        reveal(tlb_wf_spec);
                    };
                    reveal(KernelK::inv);
                };
                // ---- locked_objects_match_lctx: cpu slot released, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(cpu_locked_match_lctx);
                };
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);
                    reveal(page_lock_id_aligned);
                    reveal(unlock_ensures);
                    reveal(LocalContext::lock_maps_removed);
                };
            }
        }


        pub fn wlock_container_unless_killed(
            &mut self,
            container_ptr: RwLockContainerPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: (bool, Option<Tracked<LockPerm>>))
            requires
                old(self).inv(),
                old(lctx).wf(),
                old(self).container_map.dom().contains(container_ptr),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).lock_id_acyclic(old(self).container_map.lock_id_by_key(container_ptr)),
                old(self).locked_objects_match_lctx(old(lctx)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                final(lctx).wf(),

                // ---- Every held lock still matches lctx (success: container locked; failure: no-op) ----
                final(self).locked_objects_match_lctx(final(lctx)),

                // ---- Dynamic lock ids remain aligned ----
                lock_id_aligned(final(self), final(lctx)),

                // ---- Field framing: only container_map's lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).iommu_table_map     == old(self).iommu_table_map,
                final(self).iommu_root_table     == old(self).iommu_root_table,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).iommu_tlb           == old(self).iommu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).scheduler_map     == old(self).scheduler_map,
                final(self).pcid_allocator_map == old(self).pcid_allocator_map,
                final(self).process_map       == old(self).process_map,
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_4k_map  == old(self).allocator_4k_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- container_map: only the targeted entry's lock state
                // ---- (success) or nothing at all (failure) changed.
                final(self).container_map.unchanged_except(&old(self).container_map, container_ptr),
                final(self).container_map.perms_wf(),

                // ---- LocalContext phase preservation ----
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),

                // ---- Failure: container is being killed; complete no-op ----
                ret.0 == false ==>
                {
                    &&& old(self).container_map.spec_index(container_ptr).being_killed() == true
                    &&& final(self).container_map.spec_index(container_ptr) == old(self).container_map.spec_index(container_ptr)
                    &&& ret.1 is None
                    &&& final(lctx).lock_id_set() =~= old(lctx).lock_id_set()
                },

                // ---- Success: container locked by us, perm returned ----
                ret.0 == true ==>
                {
                    &&& old(self).container_map.spec_index(container_ptr).being_killed() == false
                    &&& ret.1 is Some
                    &&& wlock_ensures(
                        old(self).container_map.spec_index(container_ptr),
                        final(self).container_map.spec_index(container_ptr),
                        old(self).container_map.lock_id_by_key(container_ptr),
                        final(lctx).thread_id(),
                        ret.1.unwrap().view(),
                    )
                    &&& final(lctx).lock_id_set() == old(lctx).lock_id_set().insert(
                        final(self).container_map.lock_id_by_key(container_ptr),
                    )
                },
        {
            proof {
                assert(old(self).container_map.perms_wf()) by {
                    reveal(container_perms_wf);
                };
                assert(old(lctx).obj_id_fresh(
                    KernelObjId::Container(container_ptr)
                )) by {
                    reveal(LocalContext::wf);
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(container_locked_match_lctx);
                    reveal(LocalContext::obj_id_fresh);
                    reveal(LocalContext::lock_map_contains);
                };
                assert(
                    old(self).container_map.spec_index(container_ptr)
                        .locked_by(old(lctx)) == false
                ) by {
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(container_locked_match_lctx);
                    reveal(LocalContext::obj_id_fresh);
                    reveal(LocalContext::lock_map_contains);
                };
            }
            let res = self.container_map.wlock_unless_killed(
                container_ptr,
                Tracked(&mut *lctx),
                Ghost(KernelObjId::Container(container_ptr)),
            );
            proof {
                assert(self.inv()) by {
                    assert(container_perms_wf(self.container_map)) by {
                        reveal(container_perms_wf);
                        reveal(container_tree_fields_wf);
                    };
                    assert(container_invariant_fields_unchanged(
                        old(self).container_map,
                        self.container_map,
                    )) by {
                        container_lock_op_preserves_invariant_fields(
                            old(self).container_map,
                            self.container_map,
                            container_ptr,
                        );
                    };
                    assert(self.subsystems_inv()) by {
                        reveal(KernelK::default_pagetable_wf);
                    };
                    assert(self.memory_management_inv()) by {
                        assert(container_page_owner_wf(
                            self.container_map,
                            self.page_array,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_page_owner_wf);
                        };
                        assert(container_process_page_pagetable_wf(
                            self.container_map,
                            self.process_map,
                            self.pagetable_map,
                            self.page_array,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_process_page_pagetable_wf);
                            reveal(container_process_wf);
                            reveal(process_pagetable_match);
                            reveal(container_page_owner_wf);
                        };
                        assert(container_pages_wf(
                            self.page_array,
                            self.container_map,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_pages_wf);
                        };
                        assert(container_process_allocator_quota_wf(
                            self.container_map,
                            self.process_map,
                            self.thread_map,
                            self.allocator_4k_map,
                            self.allocator_2m_map,
                            self.allocator_1g_map,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_process_allocator_quota_4k_wf);
                            reveal(container_process_allocator_quota_2m_wf);
                            reveal(container_process_allocator_quota_1g_wf);
                        };
                        assert(container_allocator_wf(
                            self.container_map,
                            self.allocator_4k_map,
                            self.allocator_2m_map,
                            self.allocator_1g_map,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_allocator_wf);
                        };
                        assert(container_allocator_free_4k_page_wf(
                            self.container_map,
                            self.allocator_4k_map,
                            self.page_array,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_allocator_free_4k_page_wf);
                            reveal(container_allocator_wf);
                            reveal(container_page_owner_wf);
                        };
                        assert(container_allocator_free_2m_page_wf(
                            self.container_map,
                            self.allocator_2m_map,
                            self.page_array,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_allocator_free_2m_page_wf);
                            reveal(container_allocator_wf);
                            reveal(container_page_owner_wf);
                        };
                        assert(container_allocator_free_1g_page_wf(
                            self.container_map,
                            self.allocator_1g_map,
                            self.page_array,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_allocator_free_1g_page_wf);
                            reveal(container_allocator_wf);
                            reveal(container_page_owner_wf);
                        };
                    };
                    assert(self.process_management_inv()) by {
                        assert(container_pcid_allocator_wf(self.container_map, self.pcid_allocator_map)) by { lemma_no_change_imply_container_pcid_allocator_wf_forall(); };
                        assert(process_pcid_allocator_wf(self.container_map, self.process_map, self.pcid_allocator_map)) by { lemma_no_change_imply_process_pcid_allocator_wf_for_container_fields_forall(); };
                        assert(container_tree_wf(
                            self.root_container,
                            self.container_map,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            container_no_change_to_tree_fields_imply_wf(old(self).root_container, old(self).container_map, self.container_map);
                        };
                        assert(container_process_wf(
                            self.container_map,
                            self.process_map,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_process_wf);
                        };
                        assert(per_container_process_tree_wf(
                            self.container_map,
                            self.process_map,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(per_container_process_tree_wf);
                        };
                        assert(container_cpu_wf(
                            self.container_map,
                            self.cpu_array,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_cpu_wf);
                        };
                        assert(container_thread_endpoint_wf(
                            self.container_map,
                            self.thread_map,
                            self.endpoint_map,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_endpoint_wf);
                            reveal(thread_endpoint_ref_counter_wf);
                            reveal(thread_endpoint_queue_wf);
                            reveal(container_thread_endpoint_wf);
                        };
                        assert(container_thread_scheduler_wf(
                            self.container_map,
                            self.thread_map,
                            self.scheduler_map,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_thread_wf);
                            reveal(container_scheduler_wf);
                            reveal(container_thread_scheduler_wf);
                        };
                        assert(container_endpoint_wf(
                            self.container_map,
                            self.endpoint_map,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_endpoint_wf);
                        };
                        assert(container_scheduler_wf(
                            self.container_map,
                            self.scheduler_map,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_scheduler_wf);
                        };
                        assert(container_thread_wf(
                            self.container_map,
                            self.thread_map,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_thread_wf);
                        };
                    };
                    assert(cpu_dirty_map_wf(
                        self.container_map,
                        self.process_map,
                        self.cpu_array,
                        self.cpu_tlb,
                        self.pagetable_map,
                    )) by {
                        reveal(container_invariant_fields_unchanged);
                        reveal(cpu_dirty_map_contains_container_processes);
                        reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                        reveal(cpu_dirty_map_proc_pcid_match);
                        reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                        reveal(container_cpu_wf);
                    };
                    reveal(KernelK::inv);
                };
                // ---- locked_objects_match_lctx: success locks container, failure is a no-op ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(container_locked_match_lctx);
                };
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);
                    reveal(page_lock_id_aligned);
                    reveal(lock_ensures);
                    reveal(LocalContext::lock_maps_inserted);
                };
            }
            res
        }

        /// Companion of `wlock_container_unless_killed` for the unlock side.
        /// Wraps `LockedMap::wunlock` for `container_map` and re-establishes
        /// `inv()` immediately afterwards. Unlocking has no killed-branch — the
        /// caller already holds the write lock, so this is unconditional.
        ///
        /// What changes in this lock phase:
        ///  * `container_map[container_ptr]`'s `locking_thread()` becomes
        ///    `None`; its payload view, rodata, and ghost state are all
        ///    preserved (`wunlock_ensures`).
        ///  * Every other entry of `container_map` is byte-equal pre/post
        ///    (`unchanged_except`).
        ///  * Every other `KernelK` field is byte-equal pre/post.
        ///  * `lctx.lock_map` loses the `KernelObjId::Container(container_ptr)`
        ///    entry (encapsulated by `unlock_ensures`).
        #[verifier::spinoff_prover]
        pub fn wunlock_container(
            &mut self,
            container_ptr: RwLockContainerPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                old(lctx).wf(),
                old(self).container_map.dom().contains(container_ptr),
                old(self).container_map.spec_index(container_ptr).being_killed() == false,
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id()
                    == old(self).container_map.spec_index(container_ptr)
                        .locking_thread()->Write_lock_id,
                old(self).container_map.spec_index(container_ptr).wlocked_by(old(lctx)),
                old(self).locked_objects_match_lctx(old(lctx)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                final(lctx).wf(),

                // ---- Every held lock still matches lctx (container now released) ----
                final(self).locked_objects_match_lctx(final(lctx)),

                // ---- Dynamic lock ids remain aligned ----
                lock_id_aligned(final(self), final(lctx)),

                // ---- Field framing: only container_map's lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).iommu_table_map     == old(self).iommu_table_map,
                final(self).iommu_root_table     == old(self).iommu_root_table,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).iommu_tlb           == old(self).iommu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).scheduler_map     == old(self).scheduler_map,
                final(self).pcid_allocator_map == old(self).pcid_allocator_map,
                final(self).process_map       == old(self).process_map,
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_4k_map  == old(self).allocator_4k_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- container_map: only the targeted entry's lock state changed (now unlocked) ----
                final(self).container_map.unchanged_except(&old(self).container_map, container_ptr),
                final(self).container_map.perms_wf(),
                final(self).container_map.spec_index(container_ptr).locking_thread() is None,
                wunlock_ensures(
                    old(self).container_map.spec_index(container_ptr),
                    final(self).container_map.spec_index(container_ptr),
                ),

                // ---- LocalContext: lock dropped; thread preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` transitions it Acquire -> Release, so restating
                // `== old` would contradict it and make the postcondition `false`
                // in an Acquire section. `unlock_ensures` is the source of truth
                // for the phase transition (same trap as the NOTE on
                // `LockedArray::wunlock`). user_view is separately preserved.
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,

                final(lctx).lock_id_set() == old(lctx).lock_id_set().remove(
                    old(self).container_map.lock_id_by_key(container_ptr),
                ),
        {
            proof {
                assert({
                    &&& old(self).container_map.perms_wf()
                    &&& old(self).container_map.spec_index(container_ptr).inv()
                }) by {
                    reveal(container_perms_wf);
                };
                assert({
                    &&& old(lctx).container_lock_map().dom().contains(
                        container_ptr,
                    )
                    &&& old(lctx).container_lock_map().spec_index(container_ptr)
                        == old(self).container_map.lock_id_by_key(container_ptr)
                }) by {
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(container_locked_match_lctx);
                };
            }
            self.container_map.wunlock(
                container_ptr,
                Tracked(&mut *lctx),
                lock_perm,
                Ghost(KernelObjId::Container(container_ptr)),
            );
            // Re-establish inv(). The only change to `self` since entry is
            // *lock state on container_map[container_ptr]*: it went from
            // WriteLock(us) to None. Every payload view, every rodata, every
            // other LockedMap entry, and every other KernelK field is
            // unchanged. Same proof template as wlock_container_unless_killed.
            proof {
                assert(self.inv()) by {
                    assert(container_perms_wf(self.container_map)) by {
                        reveal(container_perms_wf);
                        reveal(container_tree_fields_wf);
                    };
                    assert(container_invariant_fields_unchanged(
                        old(self).container_map,
                        self.container_map,
                    )) by {
                        container_lock_op_preserves_invariant_fields(
                            old(self).container_map,
                            self.container_map,
                            container_ptr,
                        );
                    };
                    assert(self.subsystems_inv()) by {
                        reveal(KernelK::default_pagetable_wf);
                    };
                    assert(self.memory_management_inv()) by {
                        assert(container_page_owner_wf(
                            self.container_map,
                            self.page_array,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_page_owner_wf);
                        };
                        assert(container_process_page_pagetable_wf(
                            self.container_map,
                            self.process_map,
                            self.pagetable_map,
                            self.page_array,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_process_page_pagetable_wf);
                            reveal(container_process_wf);
                            reveal(process_pagetable_match);
                            reveal(container_page_owner_wf);
                        };
                        assert(container_pages_wf(
                            self.page_array,
                            self.container_map,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_pages_wf);
                        };
                        assert(container_process_allocator_quota_wf(
                            self.container_map,
                            self.process_map,
                            self.thread_map,
                            self.allocator_4k_map,
                            self.allocator_2m_map,
                            self.allocator_1g_map,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_process_allocator_quota_4k_wf);
                            reveal(container_process_allocator_quota_2m_wf);
                            reveal(container_process_allocator_quota_1g_wf);
                        };
                        assert(container_allocator_wf(
                            self.container_map,
                            self.allocator_4k_map,
                            self.allocator_2m_map,
                            self.allocator_1g_map,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_allocator_wf);
                        };
                        assert(container_allocator_free_4k_page_wf(
                            self.container_map,
                            self.allocator_4k_map,
                            self.page_array,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_allocator_free_4k_page_wf);
                            reveal(container_allocator_wf);
                            reveal(container_page_owner_wf);
                        };
                        assert(container_allocator_free_2m_page_wf(
                            self.container_map,
                            self.allocator_2m_map,
                            self.page_array,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_allocator_free_2m_page_wf);
                            reveal(container_allocator_wf);
                            reveal(container_page_owner_wf);
                        };
                        assert(container_allocator_free_1g_page_wf(
                            self.container_map,
                            self.allocator_1g_map,
                            self.page_array,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_allocator_free_1g_page_wf);
                            reveal(container_allocator_wf);
                            reveal(container_page_owner_wf);
                        };
                    };
                    assert(self.process_management_inv()) by {
                        assert(container_pcid_allocator_wf(self.container_map, self.pcid_allocator_map)) by { lemma_no_change_imply_container_pcid_allocator_wf_forall(); };
                        assert(process_pcid_allocator_wf(self.container_map, self.process_map, self.pcid_allocator_map)) by { lemma_no_change_imply_process_pcid_allocator_wf_for_container_fields_forall(); };
                        assert(container_tree_wf(
                            self.root_container,
                            self.container_map,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            container_no_change_to_tree_fields_imply_wf(old(self).root_container, old(self).container_map, self.container_map);
                        };
                        assert(container_process_wf(
                            self.container_map,
                            self.process_map,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_process_wf);
                        };
                        assert(per_container_process_tree_wf(
                            self.container_map,
                            self.process_map,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(per_container_process_tree_wf);
                        };
                        assert(container_cpu_wf(
                            self.container_map,
                            self.cpu_array,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_cpu_wf);
                        };
                        assert(container_thread_endpoint_wf(
                            self.container_map,
                            self.thread_map,
                            self.endpoint_map,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_endpoint_wf);
                            reveal(thread_endpoint_ref_counter_wf);
                            reveal(thread_endpoint_queue_wf);
                            reveal(container_thread_endpoint_wf);
                        };
                        assert(container_thread_scheduler_wf(
                            self.container_map,
                            self.thread_map,
                            self.scheduler_map,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_thread_wf);
                            reveal(container_scheduler_wf);
                            reveal(container_thread_scheduler_wf);
                        };
                        assert(container_endpoint_wf(
                            self.container_map,
                            self.endpoint_map,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_endpoint_wf);
                        };
                        assert(container_scheduler_wf(
                            self.container_map,
                            self.scheduler_map,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_scheduler_wf);
                        };
                        assert(container_thread_wf(
                            self.container_map,
                            self.thread_map,
                        )) by {
                            reveal(container_invariant_fields_unchanged);
                            reveal(container_thread_wf);
                        };
                    };
                    assert(cpu_dirty_map_wf(
                        self.container_map,
                        self.process_map,
                        self.cpu_array,
                        self.cpu_tlb,
                        self.pagetable_map,
                    )) by {
                        reveal(container_invariant_fields_unchanged);
                        reveal(cpu_dirty_map_contains_container_processes);
                        reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                        reveal(cpu_dirty_map_proc_pcid_match);
                        reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                        reveal(container_cpu_wf);
                    };
                    reveal(KernelK::inv);
                };
                // ---- locked_objects_match_lctx: container slot released, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(container_locked_match_lctx);
                };
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);
                    reveal(page_lock_id_aligned);
                    reveal(unlock_ensures);
                    reveal(LocalContext::lock_maps_removed);
                };
            }
        }

        #[verifier::spinoff_prover]
        pub fn wlock_quota_4k(
            &mut self,
            alloc_ptr_4k: RwLockPageAllocatorPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Tracked<LockPerm>)
            requires
                old(self).inv(),
                old(lctx).wf(),
                old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).lock_id_acyclic(old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.lock_id()),
                old(self).locked_objects_match_lctx(old(lctx)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                final(lctx).wf(),

                // ---- Every held lock still matches lctx (quota now locked) ----
                final(self).locked_objects_match_lctx(final(lctx)),

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
                    final(lctx).thread_id(),
                    ret.view(),
                ),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().insert(
                    final(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.lock_id(),
                ),
        {
            proof {
                assert(old(self).allocator_4k_map.perms_wf()) by {
                    reveal(allocator_perms_wf);
                };
                assert(old(lctx).obj_id_fresh(
                    KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k)
                )) by {
                    reveal(LocalContext::wf);
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(allocator_4k_locked_match_lctx);
                    reveal(LocalContext::obj_id_fresh);
                    reveal(LocalContext::lock_map_contains);
                };
                assert(wlock_requires(
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
                    old(lctx),
                )) by {
                    reveal(wlock_requires);
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(allocator_4k_locked_match_lctx);
                    reveal(LocalContext::obj_id_fresh);
                    reveal(LocalContext::lock_map_contains);
                };
            }
            let ret = self.allocator_4k_map.wlock_quota(alloc_ptr_4k, Tracked(&mut *lctx), Ghost(PageSize::SZ4k));

            proof {
                assert(self.inv()) by {
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
                            self.container_map,
                            self.allocator_4k_map,
                            self.page_array,
                        )) by {
                            assert forall|a_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId|
                                #![trigger self.allocator_4k_map.spec_index(a_ptr)
                                    .cpu_caches.spec_index(cpu_id).view().view()]
                                self.allocator_4k_map.dom().contains(a_ptr)
                                    && cpu_id_valid(cpu_id)
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
                    reveal(KernelK::inv);
                };
                // ---- locked_objects_match_lctx: quota slot gained, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(allocator_4k_locked_match_lctx);
                };
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);
                    reveal(page_lock_id_aligned);
                    reveal(lock_ensures);
                    reveal(LocalContext::lock_maps_inserted);
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
                old(lctx).wf(),
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
                old(self).locked_objects_match_lctx(old(lctx)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                final(lctx).wf(),

                // ---- Every held lock still matches lctx (quota now released) ----
                final(self).locked_objects_match_lctx(final(lctx)),

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
                wunlock_ensures(
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
                    final(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
                ),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().remove(
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.lock_id(),
                ),
        {
            proof {
                assert({
                    &&& old(self).allocator_4k_map.perms_wf()
                    &&& old(lctx).allocator_4k_lock_map().dom().contains(
                        AllocatorLockObjId::Quota(alloc_ptr_4k),
                    )
                    &&& old(lctx).allocator_4k_lock_map().spec_index(
                        AllocatorLockObjId::Quota(alloc_ptr_4k)
                    ) == old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .quota.lock_id()
                }) by {
                    reveal(allocator_perms_wf);
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(allocator_4k_locked_match_lctx);
                };
            }
            self.allocator_4k_map.wunlock_quota(alloc_ptr_4k, Tracked(&mut *lctx), lock_perm, Ghost(PageSize::SZ4k));

            proof {
                assert(self.inv()) by {
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
                            self.container_map,
                            self.allocator_4k_map,
                            self.page_array,
                        )) by {
                            assert forall|a_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId|
                                #![trigger self.allocator_4k_map.spec_index(a_ptr)
                                    .cpu_caches.spec_index(cpu_id).view().view()]
                                self.allocator_4k_map.dom().contains(a_ptr)
                                    && cpu_id_valid(cpu_id)
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
                    reveal(KernelK::inv);
                };
                // ---- locked_objects_match_lctx: quota slot released, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(allocator_4k_locked_match_lctx);
                };
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);
                    reveal(page_lock_id_aligned);
                    reveal(unlock_ensures);
                    reveal(LocalContext::lock_maps_removed);
                };
            }
        }

        /// Wrapper around `LockedMap::wlock_unless_killed` for `process_map`
        /// that re-establishes `inv()` after the lock attempt. Same shape as
        /// `wlock_container_unless_killed`, but for the process map, which is
        /// touched by the conservation-fold conjunct
        /// `container_process_allocator_quota_wf` — so that piece is discharged
        /// via the per-process set-fold axioms (the lock only moves lock state,
        /// so each process's `process_effective_quota_*` is unchanged ==> the
        /// folded sum is unchanged).
        ///
        #[verifier::spinoff_prover]
        pub fn wlock_process_unless_killed(
            &mut self,
            process_ptr: RwLockProcessPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: (bool, Option<Tracked<LockPerm>>))
            requires
                old(self).inv(),
                old(lctx).wf(),
                old(self).process_map.dom().contains(process_ptr),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).lock_id_acyclic(old(self).process_map.lock_id_by_key(process_ptr)),
                old(self).locked_objects_match_lctx(old(lctx)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                final(lctx).wf(),

                // ---- Every held lock still matches lctx (success: process locked; failure: no-op) ----
                final(self).locked_objects_match_lctx(final(lctx)),

                // ---- Dynamic lock ids remain aligned ----
                lock_id_aligned(final(self), final(lctx)),

                // ---- Field framing: only process_map's lock state moves ----
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
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_4k_map  == old(self).allocator_4k_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- process_map: only the targeted entry's lock state
                // ---- (success) or nothing at all (failure) changed.
                final(self).process_map.unchanged_except(&old(self).process_map, process_ptr),
                final(self).process_map.perms_wf(),

                // ---- LocalContext phase preservation ----
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),

                // ---- Failure: process is being killed; complete no-op ----
                ret.0 == false ==>
                {
                    &&& old(self).process_map.spec_index(process_ptr).being_killed() == true
                    &&& final(self).process_map.spec_index(process_ptr) == old(self).process_map.spec_index(process_ptr)
                    &&& ret.1 is None
                    &&& final(lctx).lock_id_set() =~= old(lctx).lock_id_set()
                },

                // ---- Success: process locked by us, perm returned ----
                ret.0 == true ==>
                {
                    &&& old(self).process_map.spec_index(process_ptr).being_killed() == false
                    &&& ret.1 is Some
                    &&& wlock_ensures(
                        old(self).process_map.spec_index(process_ptr),
                        final(self).process_map.spec_index(process_ptr),
                        old(self).process_map.lock_id_by_key(process_ptr),
                        final(lctx).thread_id(),
                        ret.1.unwrap().view(),
                    )
                    &&& final(lctx).lock_id_set() == old(lctx).lock_id_set().insert(
                        final(self).process_map.lock_id_by_key(process_ptr),
                    )
                },
        {
            proof {
                assert(old(self).process_map.perms_wf()) by {
                    reveal(process_perms_wf);
                };
                assert(old(lctx).obj_id_fresh(
                    KernelObjId::Process(process_ptr),
                )) by {
                    reveal(LocalContext::wf);
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(process_locked_match_lctx);
                    reveal(LocalContext::obj_id_fresh);
                    reveal(LocalContext::lock_map_contains);
                };
                assert(
                    old(self).process_map.spec_index(process_ptr)
                        .locked_by(old(lctx)) == false
                ) by {
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(process_locked_match_lctx);
                    reveal(LocalContext::obj_id_fresh);
                    reveal(LocalContext::lock_map_contains);
                };
            }
            let res = self.process_map.wlock_unless_killed(
                process_ptr,
                Tracked(&mut *lctx),
                Ghost(KernelObjId::Process(process_ptr)),
            );

            proof {
                assert(self.inv()) by {
                    assert(process_perms_wf(self.process_map)) by {
                        reveal(process_perms_wf);
                    };
                    assert(process_invariant_fields_unchanged(
                        old(self).process_map,
                        self.process_map,
                    )) by {
                        process_lock_op_preserves_invariant_fields(
                            old(self).process_map,
                            self.process_map,
                            process_ptr,
                        );
                    };
                    assert(process_quota_4k_framed_fields_unchanged(
                        old(self).process_map,
                        self.process_map,
                    )) by {
                        reveal(process_invariant_fields_unchanged);
                    };
                    assert(self.subsystems_inv()) by {
                        reveal(KernelK::default_pagetable_wf);
                    };
                    assert(self.memory_management_inv()) by {
                        assert(container_process_page_pagetable_wf(
                            self.container_map,
                            self.process_map,
                            self.pagetable_map,
                            self.page_array,
                        )) by {
                            lemma_no_change_imply_container_process_page_pagetable_wf_forall();
                        };
                        assert(process_pages_wf(
                            self.page_array,
                            self.process_map,
                        )) by {
                            lemma_no_change_imply_process_pages_wf_forall();
                        };
                        assert(container_process_allocator_quota_4k_wf(
                            self.container_map,
                            self.process_map,
                            self.thread_map,
                            self.allocator_4k_map,
                        )) by {
                            reveal(process_invariant_fields_unchanged);
                            reveal(container_process_allocator_quota_4k_wf);
                            assert forall|c_ptr: RwLockContainerPtr|
                                #![trigger self.container_map.spec_index(c_ptr)
                                    .view_rodata().view().allocator_ptr_4k]
                                self.container_map.dom().contains(c_ptr)
                            implies
                                self.container_map.spec_index(c_ptr).view()
                                    .owned_processes.view().fold(
                                        0,
                                        |sum: int, p_ptr: RwLockProcessPtr|
                                            sum + process_effective_quota_4k(
                                                self.process_map.spec_index(p_ptr),
                                            ),
                                    )
                                    == old(self).container_map.spec_index(c_ptr).view()
                                        .owned_processes.view().fold(
                                            0,
                                            |sum: int, p_ptr: RwLockProcessPtr|
                                                sum + process_effective_quota_4k(
                                                    old(self).process_map.spec_index(p_ptr),
                                                ),
                                        )
                            by {
                                assert(self.container_map.spec_index(c_ptr).view()
                                    .owned_processes.view().subset_of(
                                        old(self).process_map.dom(),
                                    )) by {
                                    reveal(container_process_wf);
                                };
                                lemma_process_effective_quota_4k_fold_eq(
                                    self.container_map.spec_index(c_ptr).view()
                                        .owned_processes.view(),
                                    old(self).process_map,
                                    self.process_map,
                                );
                            };
                        };
                        assert(container_process_allocator_quota_2m_wf(
                            self.container_map,
                            self.process_map,
                            self.thread_map,
                            self.allocator_2m_map,
                        )) by {
                            reveal(process_invariant_fields_unchanged);
                            reveal(container_process_allocator_quota_2m_wf);
                            assert forall|c_ptr: RwLockContainerPtr|
                                #![trigger self.container_map.spec_index(c_ptr)
                                    .view_rodata().view().allocator_ptr_2m]
                                self.container_map.dom().contains(c_ptr)
                            implies
                                self.container_map.spec_index(c_ptr).view()
                                    .owned_processes.view().fold(
                                        0,
                                        |sum: int, p_ptr: RwLockProcessPtr|
                                            sum + process_effective_quota_2m(
                                                self.process_map.spec_index(p_ptr),
                                            ),
                                    )
                                    == old(self).container_map.spec_index(c_ptr).view()
                                        .owned_processes.view().fold(
                                            0,
                                            |sum: int, p_ptr: RwLockProcessPtr|
                                                sum + process_effective_quota_2m(
                                                    old(self).process_map.spec_index(p_ptr),
                                                ),
                                        )
                            by {
                                assert(self.container_map.spec_index(c_ptr).view()
                                    .owned_processes.view().subset_of(
                                        old(self).process_map.dom(),
                                    )) by {
                                    reveal(container_process_wf);
                                };
                                lemma_process_effective_quota_2m_fold_eq(
                                    self.container_map.spec_index(c_ptr).view()
                                        .owned_processes.view(),
                                    old(self).process_map,
                                    self.process_map,
                                );
                            };
                        };
                        assert(container_process_allocator_quota_1g_wf(
                            self.container_map,
                            self.process_map,
                            self.thread_map,
                            self.allocator_1g_map,
                        )) by {
                            reveal(process_invariant_fields_unchanged);
                            reveal(container_process_allocator_quota_1g_wf);
                            assert forall|c_ptr: RwLockContainerPtr|
                                #![trigger self.container_map.spec_index(c_ptr)
                                    .view_rodata().view().allocator_ptr_1g]
                                self.container_map.dom().contains(c_ptr)
                            implies
                                self.container_map.spec_index(c_ptr).view()
                                    .owned_processes.view().fold(
                                        0,
                                        |sum: int, p_ptr: RwLockProcessPtr|
                                            sum + process_effective_quota_1g(
                                                self.process_map.spec_index(p_ptr),
                                            ),
                                    )
                                    == old(self).container_map.spec_index(c_ptr).view()
                                        .owned_processes.view().fold(
                                            0,
                                            |sum: int, p_ptr: RwLockProcessPtr|
                                                sum + process_effective_quota_1g(
                                                    old(self).process_map.spec_index(p_ptr),
                                                ),
                                        )
                            by {
                                assert(self.container_map.spec_index(c_ptr).view()
                                    .owned_processes.view().subset_of(
                                        old(self).process_map.dom(),
                                    )) by {
                                    reveal(container_process_wf);
                                };
                                lemma_process_effective_quota_1g_fold_eq(
                                    self.container_map.spec_index(c_ptr).view()
                                        .owned_processes.view(),
                                    old(self).process_map,
                                    self.process_map,
                                );
                            };
                        };
                        assert(process_pagetable_match(
                            self.process_map,
                            self.pagetable_map,
                        )) by {
                            lemma_no_change_imply_process_pagetable_match_forall();
                        };
                        assert(process_iommu_table_match(self.process_map, self.iommu_table_map)) by { lemma_no_change_imply_process_iommu_table_match_forall(); };
                    };
                    assert(self.process_management_inv()) by {
                        assert(process_pcid_allocator_wf(self.container_map, self.process_map, self.pcid_allocator_map)) by { lemma_no_change_imply_process_pcid_allocator_wf_forall(); };
                        assert(container_process_wf(
                            self.container_map,
                            self.process_map,
                        )) by {
                            lemma_no_change_imply_container_process_wf_forall();
                        };
                        assert(per_container_process_tree_wf(
                            self.container_map,
                            self.process_map,
                        )) by {
                            lemma_no_change_imply_per_container_process_tree_wf_forall();
                        };
                        assert(process_cpu_wf(
                            self.process_map,
                            self.cpu_array,
                        )) by {
                            lemma_no_change_imply_process_cpu_wf_forall();
                        };
                        assert(process_thread_wf(
                            self.process_map,
                            self.thread_map,
                        )) by {
                            lemma_no_change_imply_process_thread_wf_forall();
                        };
                    };
                    assert(iommu_root_table_process_wf(&self.iommu_root_table, self.process_map, self.iommu_table_map)) by { lemma_no_change_imply_iommu_root_table_process_wf_forall(); };
                    assert(process_pci_function_ownership_wf(&self.iommu_root_table, self.process_map)) by { lemma_no_change_imply_process_pci_function_ownership_wf_forall(); };
                    assert(iommu_tlb_wf_spec(self.iommu_tlb, &self.iommu_root_table, self.process_map, self.iommu_table_map)) by { lemma_no_change_imply_iommu_tlb_wf_spec_forall(); };
                    assert(cpu_dirty_map_wf(
                        self.container_map,
                        self.process_map,
                        self.cpu_array,
                        self.cpu_tlb,
                        self.pagetable_map,
                    )) by {
                        lemma_no_change_imply_cpu_dirty_map_wf_forall();
                    };
                    reveal(KernelK::inv);
                };
                // ---- locked_objects_match_lctx: success locks process, failure is a no-op ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(process_locked_match_lctx);
                };
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);
                    reveal(page_lock_id_aligned);
                    reveal(lock_ensures);
                    reveal(LocalContext::lock_maps_inserted);
                };
            }
            res
        }

        /// Companion of `wlock_process_unless_killed` for the unlock side.
        /// Wraps `LockedMap::wunlock` for `process_map` and re-establishes
        /// `inv()` immediately afterwards. Unlocking has no killed-branch — the
        /// caller already holds the write lock, so this is unconditional.
        #[verifier::spinoff_prover]
        pub fn wunlock_process(
            &mut self,
            process_ptr: RwLockProcessPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                old(lctx).wf(),
                old(self).process_map.dom().contains(process_ptr),
                old(self).process_map.spec_index(process_ptr).being_killed() == false,
                old(self).process_map.spec_index(process_ptr)
                    .wlocked_by(old(lctx)),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id()
                    == old(self).process_map.spec_index(process_ptr)
                        .locking_thread()->Write_lock_id,
                old(self).locked_objects_match_lctx(old(lctx)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                final(lctx).wf(),

                // ---- Every held lock still matches lctx (process now released) ----
                final(self).locked_objects_match_lctx(final(lctx)),

                // ---- Dynamic lock ids remain aligned ----
                lock_id_aligned(final(self), final(lctx)),

                // ---- Field framing: only process_map's lock state moves ----
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
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_4k_map  == old(self).allocator_4k_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- process_map: only the targeted entry's lock state changed (now unlocked) ----
                final(self).process_map.unchanged_except(&old(self).process_map, process_ptr),
                final(self).process_map.perms_wf(),
                final(self).process_map.spec_index(process_ptr).locking_thread() is None,
                wunlock_ensures(
                    old(self).process_map.spec_index(process_ptr),
                    final(self).process_map.spec_index(process_ptr),
                ),

                // ---- LocalContext: lock dropped; thread preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` transitions it Acquire -> Release, so restating
                // `== old` would contradict it and make the postcondition `false`
                // in an Acquire section. `unlock_ensures` is the source of truth
                // for the phase transition (same trap as the NOTE on
                // `LockedArray::wunlock`). user_view is separately preserved.
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,

                final(lctx).lock_id_set() == old(lctx).lock_id_set().remove(
                    old(self).process_map.lock_id_by_key(process_ptr),
                ),
        {
            proof {
                assert({
                    &&& old(self).process_map.perms_wf()
                    &&& old(self).process_map.spec_index(process_ptr).inv()
                }) by {
                    reveal(process_perms_wf);
                };
                assert({
                    &&& old(lctx).process_lock_map().dom().contains(
                        process_ptr,
                    )
                    &&& old(lctx).process_lock_map().spec_index(process_ptr)
                        == old(self).process_map.lock_id_by_key(process_ptr)
                }) by {
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(process_locked_match_lctx);
                };
            }
            self.process_map.wunlock(
                process_ptr,
                Tracked(&mut *lctx),
                lock_perm,
                Ghost(KernelObjId::Process(process_ptr)),
            );
            // Re-establish inv(). Only `process_map[process_ptr]`'s lock state
            // moved; every process payload view, every other entry, and every
            // other KernelK field is byte-equal pre/post. Same template as
            // wlock_process_unless_killed.
            proof {
                assert(self.inv()) by {
                    assert(process_perms_wf(self.process_map)) by {
                        reveal(process_perms_wf);
                    };
                    assert(process_invariant_fields_unchanged(
                        old(self).process_map,
                        self.process_map,
                    )) by {
                        process_lock_op_preserves_invariant_fields(
                            old(self).process_map,
                            self.process_map,
                            process_ptr,
                        );
                    };
                    assert(process_quota_4k_framed_fields_unchanged(
                        old(self).process_map,
                        self.process_map,
                    )) by {
                        reveal(process_invariant_fields_unchanged);
                    };
                    assert(self.subsystems_inv()) by {
                        reveal(KernelK::default_pagetable_wf);
                    };
                    assert(self.memory_management_inv()) by {
                        assert(container_process_page_pagetable_wf(
                            self.container_map,
                            self.process_map,
                            self.pagetable_map,
                            self.page_array,
                        )) by {
                            lemma_no_change_imply_container_process_page_pagetable_wf_forall();
                        };
                        assert(process_pages_wf(
                            self.page_array,
                            self.process_map,
                        )) by {
                            lemma_no_change_imply_process_pages_wf_forall();
                        };
                        assert(container_process_allocator_quota_4k_wf(
                            self.container_map,
                            self.process_map,
                            self.thread_map,
                            self.allocator_4k_map,
                        )) by {
                            reveal(process_invariant_fields_unchanged);
                            reveal(container_process_allocator_quota_4k_wf);
                            assert forall|c_ptr: RwLockContainerPtr|
                                #![trigger self.container_map.spec_index(c_ptr)
                                    .view_rodata().view().allocator_ptr_4k]
                                self.container_map.dom().contains(c_ptr)
                            implies
                                self.container_map.spec_index(c_ptr).view()
                                    .owned_processes.view().fold(
                                        0,
                                        |sum: int, p_ptr: RwLockProcessPtr|
                                            sum + process_effective_quota_4k(
                                                self.process_map.spec_index(p_ptr),
                                            ),
                                    )
                                    == old(self).container_map.spec_index(c_ptr).view()
                                        .owned_processes.view().fold(
                                            0,
                                            |sum: int, p_ptr: RwLockProcessPtr|
                                                sum + process_effective_quota_4k(
                                                    old(self).process_map.spec_index(p_ptr),
                                                ),
                                        )
                            by {
                                assert(self.container_map.spec_index(c_ptr).view()
                                    .owned_processes.view().subset_of(
                                        old(self).process_map.dom(),
                                    )) by {
                                    reveal(container_process_wf);
                                };
                                lemma_process_effective_quota_4k_fold_eq(
                                    self.container_map.spec_index(c_ptr).view()
                                        .owned_processes.view(),
                                    old(self).process_map,
                                    self.process_map,
                                );
                            };
                        };
                        assert(container_process_allocator_quota_2m_wf(
                            self.container_map,
                            self.process_map,
                            self.thread_map,
                            self.allocator_2m_map,
                        )) by {
                            reveal(process_invariant_fields_unchanged);
                            reveal(container_process_allocator_quota_2m_wf);
                            assert forall|c_ptr: RwLockContainerPtr|
                                #![trigger self.container_map.spec_index(c_ptr)
                                    .view_rodata().view().allocator_ptr_2m]
                                self.container_map.dom().contains(c_ptr)
                            implies
                                self.container_map.spec_index(c_ptr).view()
                                    .owned_processes.view().fold(
                                        0,
                                        |sum: int, p_ptr: RwLockProcessPtr|
                                            sum + process_effective_quota_2m(
                                                self.process_map.spec_index(p_ptr),
                                            ),
                                    )
                                    == old(self).container_map.spec_index(c_ptr).view()
                                        .owned_processes.view().fold(
                                            0,
                                            |sum: int, p_ptr: RwLockProcessPtr|
                                                sum + process_effective_quota_2m(
                                                    old(self).process_map.spec_index(p_ptr),
                                                ),
                                        )
                            by {
                                assert(self.container_map.spec_index(c_ptr).view()
                                    .owned_processes.view().subset_of(
                                        old(self).process_map.dom(),
                                    )) by {
                                    reveal(container_process_wf);
                                };
                                lemma_process_effective_quota_2m_fold_eq(
                                    self.container_map.spec_index(c_ptr).view()
                                        .owned_processes.view(),
                                    old(self).process_map,
                                    self.process_map,
                                );
                            };
                        };
                        assert(container_process_allocator_quota_1g_wf(
                            self.container_map,
                            self.process_map,
                            self.thread_map,
                            self.allocator_1g_map,
                        )) by {
                            reveal(process_invariant_fields_unchanged);
                            reveal(container_process_allocator_quota_1g_wf);
                            assert forall|c_ptr: RwLockContainerPtr|
                                #![trigger self.container_map.spec_index(c_ptr)
                                    .view_rodata().view().allocator_ptr_1g]
                                self.container_map.dom().contains(c_ptr)
                            implies
                                self.container_map.spec_index(c_ptr).view()
                                    .owned_processes.view().fold(
                                        0,
                                        |sum: int, p_ptr: RwLockProcessPtr|
                                            sum + process_effective_quota_1g(
                                                self.process_map.spec_index(p_ptr),
                                            ),
                                    )
                                    == old(self).container_map.spec_index(c_ptr).view()
                                        .owned_processes.view().fold(
                                            0,
                                            |sum: int, p_ptr: RwLockProcessPtr|
                                                sum + process_effective_quota_1g(
                                                    old(self).process_map.spec_index(p_ptr),
                                                ),
                                        )
                            by {
                                assert(self.container_map.spec_index(c_ptr).view()
                                    .owned_processes.view().subset_of(
                                        old(self).process_map.dom(),
                                    )) by {
                                    reveal(container_process_wf);
                                };
                                lemma_process_effective_quota_1g_fold_eq(
                                    self.container_map.spec_index(c_ptr).view()
                                        .owned_processes.view(),
                                    old(self).process_map,
                                    self.process_map,
                                );
                            };
                        };
                        assert(process_pagetable_match(
                            self.process_map,
                            self.pagetable_map,
                        )) by {
                            lemma_no_change_imply_process_pagetable_match_forall();
                        };
                        assert(process_iommu_table_match(self.process_map, self.iommu_table_map)) by { lemma_no_change_imply_process_iommu_table_match_forall(); };
                    };
                    assert(self.process_management_inv()) by {
                        assert(process_pcid_allocator_wf(self.container_map, self.process_map, self.pcid_allocator_map)) by { lemma_no_change_imply_process_pcid_allocator_wf_forall(); };
                        assert(container_process_wf(
                            self.container_map,
                            self.process_map,
                        )) by {
                            lemma_no_change_imply_container_process_wf_forall();
                        };
                        assert(per_container_process_tree_wf(
                            self.container_map,
                            self.process_map,
                        )) by {
                            lemma_no_change_imply_per_container_process_tree_wf_forall();
                        };
                        assert(process_cpu_wf(
                            self.process_map,
                            self.cpu_array,
                        )) by {
                            lemma_no_change_imply_process_cpu_wf_forall();
                        };
                        assert(process_thread_wf(
                            self.process_map,
                            self.thread_map,
                        )) by {
                            lemma_no_change_imply_process_thread_wf_forall();
                        };
                    };
                    assert(iommu_root_table_process_wf(&self.iommu_root_table, self.process_map, self.iommu_table_map)) by { lemma_no_change_imply_iommu_root_table_process_wf_forall(); };
                    assert(process_pci_function_ownership_wf(&self.iommu_root_table, self.process_map)) by { lemma_no_change_imply_process_pci_function_ownership_wf_forall(); };
                    assert(iommu_tlb_wf_spec(self.iommu_tlb, &self.iommu_root_table, self.process_map, self.iommu_table_map)) by { lemma_no_change_imply_iommu_tlb_wf_spec_forall(); };
                    assert(cpu_dirty_map_wf(
                        self.container_map,
                        self.process_map,
                        self.cpu_array,
                        self.cpu_tlb,
                        self.pagetable_map,
                    )) by {
                        lemma_no_change_imply_cpu_dirty_map_wf_forall();
                    };
                    reveal(KernelK::inv);
                };
                // ---- locked_objects_match_lctx: process slot released, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(process_locked_match_lctx);
                };
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);
                    reveal(page_lock_id_aligned);
                    reveal(unlock_ensures);
                    reveal(LocalContext::lock_maps_removed);
                };
            }
        }

        #[verifier::spinoff_prover]
        pub fn wlock_thread_unless_killed(
            &mut self,
            thread_ptr: RwLockThreadPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: (bool, Option<Tracked<LockPerm>>))
            requires
                old(self).inv(),
                old(lctx).wf(),
                old(self).thread_map.dom().contains(thread_ptr),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).lock_id_acyclic(old(self).thread_map.lock_id_by_key(thread_ptr)),
                old(self).locked_objects_match_lctx(old(lctx)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                final(self).inv(),
                final(lctx).wf(),
                final(self).locked_objects_match_lctx(final(lctx)),
                lock_id_aligned(final(self), final(lctx)),
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
                final(self).endpoint_map == old(self).endpoint_map,
                final(self).allocator_4k_map == old(self).allocator_4k_map,
                final(self).allocator_2m_map == old(self).allocator_2m_map,
                final(self).allocator_1g_map == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,
                final(self).thread_map.unchanged_except(&old(self).thread_map, thread_ptr),
                final(self).thread_map.perms_wf(),
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                ret.0 == false ==> {
                    &&& old(self).thread_map.spec_index(thread_ptr).being_killed()
                    &&& final(self).thread_map.spec_index(thread_ptr)
                        == old(self).thread_map.spec_index(thread_ptr)
                    &&& ret.1 is None
                    &&& final(lctx).lock_id_set() =~= old(lctx).lock_id_set()
                },
                ret.0 == true ==> {
                    &&& old(self).thread_map.spec_index(thread_ptr).being_killed() == false
                    &&& ret.1 is Some
                    &&& wlock_ensures(
                        old(self).thread_map.spec_index(thread_ptr),
                        final(self).thread_map.spec_index(thread_ptr),
                        old(self).thread_map.lock_id_by_key(thread_ptr),
                        final(lctx).thread_id(),
                        ret.1.unwrap().view(),
                    )
                    &&& final(self).thread_map.spec_index(thread_ptr).view()
                        .free_quota_pending_clean()
                    &&& final(self).thread_map.spec_index(thread_ptr).view()
                        .temp_alloc_clean()
                    &&& final(lctx).lock_id_set() == old(lctx).lock_id_set().insert(
                        final(self).thread_map.lock_id_by_key(thread_ptr),
                    )
                },
        {
            proof {
                assert(old(self).thread_map.perms_wf()) by {
                    reveal(thread_perms_wf);
                };
                assert(old(lctx).obj_id_fresh(KernelObjId::Thread(thread_ptr))) by {
                    reveal(LocalContext::wf);
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(thread_locked_match_lctx);
                    reveal(LocalContext::obj_id_fresh);
                    reveal(LocalContext::lock_map_contains);
                };
                assert(old(self).thread_map.spec_index(thread_ptr).locked_by(old(lctx)) == false) by {
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(thread_locked_match_lctx);
                    reveal(LocalContext::obj_id_fresh);
                    reveal(LocalContext::lock_map_contains);
                };
            }
            let res = self.thread_map.wlock_unless_killed(
                thread_ptr,
                Tracked(&mut *lctx),
                Ghost(KernelObjId::Thread(thread_ptr)),
            );
            proof {
                assert(self.inv()) by {
                    assert(thread_perms_wf(self.thread_map)) by {
                        reveal(thread_perms_wf);
                        reveal(threads_inv);
                        reveal(thread_free_quota_pending_empty_unless_wlocked);
                        reveal(thread_temp_alloc_empty_unless_wlocked);
                    };
                    assert(thread_invariant_fields_unchanged(
                        old(self).thread_map,
                        self.thread_map,
                    )) by {
                        thread_lock_op_preserves_invariant_fields(
                            old(self).thread_map,
                            self.thread_map,
                            thread_ptr,
                        );
                    };
                    assert(self.subsystems_inv()) by {
                        reveal(KernelK::default_pagetable_wf);
                    };
                    assert(self.memory_management_inv()) by {
                        assert(container_process_allocator_quota_4k_wf(
                            self.container_map,
                            self.process_map,
                            self.thread_map,
                            self.allocator_4k_map,
                        )) by {
                            container_process_allocator_quota_4k_wf_preserved_for_thread_fields_forall();
                        };
                        assert(container_process_allocator_quota_2m_wf(
                            self.container_map,
                            self.process_map,
                            self.thread_map,
                            self.allocator_2m_map,
                        )) by {
                            container_process_allocator_quota_2m_wf_preserved_for_thread_fields_forall();
                        };
                        assert(container_process_allocator_quota_1g_wf(
                            self.container_map,
                            self.process_map,
                            self.thread_map,
                            self.allocator_1g_map,
                        )) by {
                            container_process_allocator_quota_1g_wf_preserved_for_thread_fields_forall();
                        };
                        assert(thread_pages_wf(self.thread_map, self.page_array)) by {
                            reveal(thread_invariant_fields_unchanged);
                            reveal(thread_pages_wf);
                        };
                        assert(thread_staged_pages_wf(self.thread_map, self.page_array)) by {
                            lemma_no_change_imply_thread_staged_pages_wf_forall();
                        };
                    };
                    assert(self.process_management_inv()) by {
                        assert(thread_endpoint_ref_counter_wf(self.thread_map, self.endpoint_map)) by {
                            reveal(thread_invariant_fields_unchanged);
                            reveal(thread_endpoint_ref_counter_wf);
                        };
                        assert(thread_endpoint_queue_wf(self.thread_map, self.endpoint_map)) by {
                            reveal(thread_invariant_fields_unchanged);
                            reveal(thread_endpoint_queue_wf);
                        };
                        assert(container_thread_endpoint_wf(
                            self.container_map, self.thread_map, self.endpoint_map,
                        )) by {
                            reveal(thread_invariant_fields_unchanged);
                            reveal(container_endpoint_wf);
                            reveal(thread_endpoint_ref_counter_wf);
                            reveal(thread_endpoint_queue_wf);
                            reveal(container_thread_endpoint_wf);
                        };
                        assert(container_thread_scheduler_wf(
                            self.container_map, self.thread_map, self.scheduler_map,
                        )) by {
                            reveal(thread_invariant_fields_unchanged);
                            reveal(container_thread_wf);
                            reveal(container_scheduler_wf);
                            reveal(container_thread_scheduler_wf);
                        };
                        assert(container_thread_wf(self.container_map, self.thread_map)) by {
                            reveal(thread_invariant_fields_unchanged);
                            reveal(container_thread_wf);
                        };
                        assert(process_thread_wf(self.process_map, self.thread_map)) by {
                            reveal(thread_invariant_fields_unchanged);
                            reveal(process_thread_wf);
                        };
                        assert(thread_cpu_wf(self.thread_map, self.cpu_array)) by {
                            reveal(thread_invariant_fields_unchanged);
                            reveal(thread_cpu_wf);
                        };
                    };
                    reveal(KernelK::inv);
                };
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(thread_locked_match_lctx);
                };
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);
                    reveal(page_lock_id_aligned);
                    reveal(lock_ensures);
                    reveal(LocalContext::lock_maps_inserted);
                };
                if res.0 {
                    assert(
                        self.thread_map.spec_index(thread_ptr).view()
                            .free_quota_pending_clean()
                        && self.thread_map.spec_index(thread_ptr).view()
                            .temp_alloc_clean()
                    ) by {
                        reveal(thread_perms_wf);
                        reveal(thread_free_quota_pending_empty_unless_wlocked);
                        reveal(thread_temp_alloc_empty_unless_wlocked);
                        reveal(wlock_ensures);
                    };
                }
            }
            res
        }

        /// Companion of the thread write-lock for the unlock side. Wraps
        /// `LockedMap::wunlock` for `thread_map` and re-establishes `inv()`. Only
        /// the targeted `thread_map` entry's lock state moves; every thread
        /// payload view, every other entry, and every other KernelK field is
        /// byte-equal pre/post — so the conservation folds transport by
        /// byte-equality (thread payloads unchanged).
        ///
        /// The pending-clean protocol: the thread must be `free_quota_pending_clean`
        /// before releasing the write lock, because once unlocked the global
        /// invariant `thread_free_quota_pending_empty_unless_wlocked` demands it.
        /// A freshly-created thread satisfies this (its pendings are all zero).
        #[verifier::spinoff_prover]
        pub fn wunlock_thread(
            &mut self,
            thread_ptr: RwLockThreadPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                old(lctx).wf(),
                old(self).thread_map.dom().contains(thread_ptr),
                old(self).thread_map.spec_index(thread_ptr).being_killed() == false,
                old(self).thread_map.spec_index(thread_ptr)
                    .wlocked_by(old(lctx)),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id()
                    == old(self).thread_map.spec_index(thread_ptr)
                        .locking_thread()->Write_lock_id,
                // The pending-clean protocol: pendings must be flushed before
                // releasing the write lock (see doc comment above).
                old(self).thread_map.spec_index(thread_ptr).view().free_quota_pending_clean(),
                old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
                old(self).locked_objects_match_lctx(old(lctx)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                final(lctx).wf(),

                // ---- Every held lock still matches lctx (thread now released) ----
                final(self).locked_objects_match_lctx(final(lctx)),
                lock_id_aligned(final(self), final(lctx)),

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
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_4k_map  == old(self).allocator_4k_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- thread_map: only the targeted entry's lock state changed (now unlocked) ----
                final(self).thread_map.unchanged_except(&old(self).thread_map, thread_ptr),
                final(self).thread_map.perms_wf(),
                final(self).thread_map.spec_index(thread_ptr).locking_thread() is None,
                wunlock_ensures(
                    old(self).thread_map.spec_index(thread_ptr),
                    final(self).thread_map.spec_index(thread_ptr),
                ),
                forall|held_thread: RwLockThreadPtr|
                    #![trigger old(self).thread_map.spec_index(held_thread).wlocked_by(old(lctx))]
                    old(self).thread_map.dom().contains(held_thread)
                        && held_thread != thread_ptr
                        && old(self).thread_map.spec_index(held_thread).wlocked_by(old(lctx))
                    ==> final(self).thread_map.dom().contains(held_thread)
                        && final(self).thread_map.spec_index(held_thread).wlocked_by(final(lctx))
                        && final(self).thread_map.lock_id_by_key(held_thread)
                            == old(self).thread_map.lock_id_by_key(held_thread),

                // ---- LocalContext: lock dropped; thread preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` transitions it Acquire -> Release (same trap as
                // the NOTE on wunlock_process / LockedArray::wunlock).
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,

                final(lctx).lock_id_set() == old(lctx).lock_id_set().remove(
                    old(self).thread_map.lock_id_by_key(thread_ptr),
                ),
        {
            proof {
                assert({
                    &&& old(self).thread_map.perms_wf()
                    &&& old(self).thread_map.spec_index(thread_ptr).inv()
                }) by {
                    reveal(thread_perms_wf);
                };
                assert({
                    &&& old(lctx).thread_lock_map().dom().contains(
                        thread_ptr,
                    )
                    &&& old(lctx).thread_lock_map().spec_index(thread_ptr)
                        == old(self).thread_map.lock_id_by_key(thread_ptr)
                }) by {
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(thread_locked_match_lctx);
                };
            }
            self.thread_map.wunlock(
                thread_ptr,
                Tracked(&mut *lctx),
                lock_perm,
                Ghost(KernelObjId::Thread(thread_ptr)),
            );
            proof {
                assert(self.inv()) by {
                    assert(thread_perms_wf(self.thread_map)) by {
                        reveal(thread_perms_wf);
                        reveal(threads_inv);
                        reveal(thread_free_quota_pending_empty_unless_wlocked);
                        reveal(thread_temp_alloc_empty_unless_wlocked);
                    };
                    assert(thread_invariant_fields_unchanged(
                        old(self).thread_map,
                        self.thread_map,
                    )) by {
                        thread_lock_op_preserves_invariant_fields(
                            old(self).thread_map,
                            self.thread_map,
                            thread_ptr,
                        );
                    };
                    assert(self.subsystems_inv()) by {
                        reveal(KernelK::default_pagetable_wf);
                    };
                    assert(self.memory_management_inv()) by {
                        assert(container_process_allocator_quota_4k_wf(
                            self.container_map,
                            self.process_map,
                            self.thread_map,
                            self.allocator_4k_map,
                        )) by {
                            container_process_allocator_quota_4k_wf_preserved_for_thread_fields_forall();
                        };
                        assert(container_process_allocator_quota_2m_wf(
                            self.container_map,
                            self.process_map,
                            self.thread_map,
                            self.allocator_2m_map,
                        )) by {
                            container_process_allocator_quota_2m_wf_preserved_for_thread_fields_forall();
                        };
                        assert(container_process_allocator_quota_1g_wf(
                            self.container_map,
                            self.process_map,
                            self.thread_map,
                            self.allocator_1g_map,
                        )) by {
                            container_process_allocator_quota_1g_wf_preserved_for_thread_fields_forall();
                        };
                        assert(thread_pages_wf(
                            self.thread_map,
                            self.page_array,
                        )) by {
                            reveal(thread_invariant_fields_unchanged);
                            reveal(thread_pages_wf);
                        };
                        assert(thread_staged_pages_wf(
                            self.thread_map,
                            self.page_array,
                        )) by {
                            lemma_no_change_imply_thread_staged_pages_wf_forall();
                        };
                    };
                    assert(self.process_management_inv()) by {
                        assert(thread_endpoint_ref_counter_wf(
                            self.thread_map,
                            self.endpoint_map,
                        )) by {
                            reveal(thread_invariant_fields_unchanged);
                            reveal(thread_endpoint_ref_counter_wf);
                        };
                        assert(thread_endpoint_queue_wf(
                            self.thread_map,
                            self.endpoint_map,
                        )) by {
                            reveal(thread_invariant_fields_unchanged);
                            reveal(thread_endpoint_queue_wf);
                        };
                        assert(container_thread_endpoint_wf(
                            self.container_map,
                            self.thread_map,
                            self.endpoint_map,
                        )) by {
                            reveal(thread_invariant_fields_unchanged);
                            reveal(container_endpoint_wf);
                            reveal(thread_endpoint_ref_counter_wf);
                            reveal(thread_endpoint_queue_wf);
                            reveal(container_thread_endpoint_wf);
                        };
                        assert(container_thread_scheduler_wf(
                            self.container_map,
                            self.thread_map,
                            self.scheduler_map,
                        )) by {
                            reveal(thread_invariant_fields_unchanged);
                            reveal(container_thread_wf);
                            reveal(container_scheduler_wf);
                            reveal(container_thread_scheduler_wf);
                        };
                        assert(container_thread_wf(
                            self.container_map,
                            self.thread_map,
                        )) by {
                            reveal(thread_invariant_fields_unchanged);
                            reveal(container_thread_wf);
                        };
                        assert(process_thread_wf(
                            self.process_map,
                            self.thread_map,
                        )) by {
                            reveal(thread_invariant_fields_unchanged);
                            reveal(process_thread_wf);
                        };
                        assert(thread_cpu_wf(
                            self.thread_map,
                            self.cpu_array,
                        )) by {
                            reveal(thread_invariant_fields_unchanged);
                            reveal(thread_cpu_wf);
                        };
                    };
                    reveal(KernelK::inv);
                };
                // ---- locked_objects_match_lctx: thread slot released, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(thread_locked_match_lctx);
                };
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);
                    reveal(page_lock_id_aligned);
                    reveal(unlock_ensures);
                    reveal(LocalContext::lock_maps_removed);
                };
            }
        }

        #[verifier::spinoff_prover]
        pub fn wlock_allocator_cache(
            &mut self,
            alloc_ptr_4k: RwLockPageAllocatorPtr,
            cache_cpu: CpuId,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Tracked<LockPerm>)
            requires
                old(self).inv(),
                old(lctx).wf(),
                old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
                cpu_id_valid(cache_cpu),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).lock_id_acyclic(LockId{
                    container: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).container_depth(),
                    process: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).process_depth(),
                    major: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).view().view().current_lock_major(),
                    minor: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).lock_minor(),
                }),
                old(self).locked_objects_match_lctx(old(lctx)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                final(lctx).wf(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),

                // ---- Every held lock still matches lctx (cache now locked) ----
                final(self).locked_objects_match_lctx(final(lctx)),
                lock_id_aligned(final(self), final(lctx)),
                forall|page_index: PageIndex|
                    #![trigger old(self).page_array.spec_index(page_index).view().wlocked_by(old(lctx))]
                    page_index_wf(page_index)
                        && old(self).page_array.spec_index(page_index).view().wlocked_by(old(lctx))
                    ==> final(self).page_array.spec_index(page_index).view().wlocked_by(final(lctx))
                        && final(self).page_array.spec_index(page_index).view().locked_by(final(lctx)),
                forall|process_ptr: RwLockProcessPtr|
                    #![trigger old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx))]
                    old(self).process_map.dom().contains(process_ptr)
                        && old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx))
                    ==> final(self).process_map.dom().contains(process_ptr)
                        && final(self).process_map.spec_index(process_ptr).wlocked_by(final(lctx))
                        && final(self).process_map.spec_index(process_ptr).locked_by(final(lctx)),

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
                    final(lctx).thread_id(),
                    ret.view(),
                ),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().insert(
                    final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(cache_cpu).lock_id(),
                ),
                final(lctx).lock_maps_inserted(
                    old(lctx),
                    KernelObjId::AllocatorCache(
                        PageSize::SZ4k, alloc_ptr_4k, cache_cpu,
                    ),
                    final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
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
                assert({
                    &&& old(lctx).obj_id_fresh(
                            KernelObjId::AllocatorCache(
                                PageSize::SZ4k,
                                alloc_ptr_4k,
                                cache_cpu,
                            ),
                        )
                    &&& wlock_requires(
                        old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                            .cpu_caches.spec_index(cache_cpu).view(),
                        old(lctx),
                    )
                }) by {
                    reveal(LocalContext::wf);
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(allocator_4k_locked_match_lctx);
                    reveal(LocalContext::obj_id_fresh);
                    reveal(LocalContext::lock_map_contains);
                    reveal(wlock_requires);
                };
            }
            let ret = self.allocator_4k_map.wlock_cache(alloc_ptr_4k, cache_cpu, Tracked(&mut *lctx), Ghost(PageSize::SZ4k));

            proof {
                assert(self.inv()) by {
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
                            self.container_map,
                            self.allocator_4k_map,
                            self.page_array,
                        )) by {
                            assert forall|a_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId|
                                #![trigger self.allocator_4k_map.spec_index(a_ptr)
                                    .cpu_caches.spec_index(cpu_id).view().view()]
                                self.allocator_4k_map.dom().contains(a_ptr)
                                    && cpu_id_valid(cpu_id)
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
                    reveal(KernelK::inv);
                };
                // ---- locked_objects_match_lctx: cache slot gained, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(allocator_4k_locked_match_lctx);
                };
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(page_lock_id_aligned);
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
                old(lctx).wf(),
                old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
                cpu_id_valid(cache_cpu),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id()
                    == old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(cache_cpu).view().locking_thread()->Write_lock_id,
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches.spec_index(cache_cpu).view().wlocked_by(old(lctx)),
                old(self).locked_objects_match_lctx(old(lctx)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                final(lctx).wf(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),

                // ---- Every held lock still matches lctx (cache now released) ----
                final(self).locked_objects_match_lctx(final(lctx)),
                lock_id_aligned(final(self), final(lctx)),
                forall|page_index: PageIndex|
                    #![trigger old(self).page_array.spec_index(page_index).view().wlocked_by(old(lctx))]
                    page_index_wf(page_index)
                        && old(self).page_array.spec_index(page_index).view().wlocked_by(old(lctx))
                    ==> final(self).page_array.spec_index(page_index).view().wlocked_by(final(lctx))
                        && final(self).page_array.spec_index(page_index).view().locked_by(final(lctx)),
                forall|process_ptr: RwLockProcessPtr|
                    #![trigger old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx))]
                    old(self).process_map.dom().contains(process_ptr)
                        && old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx))
                    ==> final(self).process_map.dom().contains(process_ptr)
                        && final(self).process_map.spec_index(process_ptr).wlocked_by(final(lctx))
                        && final(self).process_map.spec_index(process_ptr).locked_by(final(lctx)),

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
                wunlock_ensures(
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).view(),
                    final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cache_cpu).view(),
                ),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().remove(
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(cache_cpu).lock_id(),
                ),
                final(lctx).lock_maps_removed(
                    old(lctx),
                    KernelObjId::AllocatorCache(
                        PageSize::SZ4k, alloc_ptr_4k, cache_cpu,
                    ),
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
                assert({
                    &&& old(lctx).allocator_4k_lock_map().dom().contains(
                            AllocatorLockObjId::Cache(alloc_ptr_4k, cache_cpu),
                        )
                    &&& old(lctx).allocator_4k_lock_map().spec_index(
                        AllocatorLockObjId::Cache(alloc_ptr_4k, cache_cpu)
                    ) == old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .cpu_caches.lock_id_by_index(cache_cpu)
                }) by {
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(allocator_4k_locked_match_lctx);
                };
            }
            self.allocator_4k_map.wunlock_cache(alloc_ptr_4k, cache_cpu, Tracked(&mut *lctx), lock_perm, Ghost(PageSize::SZ4k));

            proof {
                assert(self.inv()) by {
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
                            self.container_map,
                            self.allocator_4k_map,
                            self.page_array,
                        )) by {
                            assert forall|a_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId|
                                #![trigger self.allocator_4k_map.spec_index(a_ptr)
                                    .cpu_caches.spec_index(cpu_id).view().view()]
                                self.allocator_4k_map.dom().contains(a_ptr)
                                    && cpu_id_valid(cpu_id)
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
                    reveal(KernelK::inv);
                };
                // ---- locked_objects_match_lctx: cache slot released, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(allocator_4k_locked_match_lctx);
                };
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(page_lock_id_aligned);
                };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                };
            }
        }

        #[verifier::spinoff_prover]
        pub fn wlock_allocator_global_pool(
            &mut self,
            alloc_ptr_4k: RwLockPageAllocatorPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Tracked<LockPerm>)
            requires
                old(self).inv(),
                old(lctx).wf(),
                old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).lock_id_acyclic(LockId{
                    container: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().container_depth(),
                    process: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().process_depth(),
                    major: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().current_lock_major(),
                    minor: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().lock_minor(),
                }),
                old(self).locked_objects_match_lctx(old(lctx)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                final(lctx).wf(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),

                // ---- Every held lock still matches lctx (global pool now locked) ----
                final(self).locked_objects_match_lctx(final(lctx)),
                lock_id_aligned(final(self), final(lctx)),
                forall|page_index: PageIndex|
                    #![trigger old(self).page_array.spec_index(page_index).view().wlocked_by(old(lctx))]
                    page_index_wf(page_index)
                        && old(self).page_array.spec_index(page_index).view().wlocked_by(old(lctx))
                    ==> final(self).page_array.spec_index(page_index).view().wlocked_by(final(lctx))
                        && final(self).page_array.spec_index(page_index).view().locked_by(final(lctx)),
                forall|process_ptr: RwLockProcessPtr|
                    #![trigger old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx))]
                    old(self).process_map.dom().contains(process_ptr)
                        && old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx))
                    ==> final(self).process_map.dom().contains(process_ptr)
                        && final(self).process_map.spec_index(process_ptr).wlocked_by(final(lctx))
                        && final(self).process_map.spec_index(process_ptr).locked_by(final(lctx)),

                // ---- Field framing: only allocator_4k_map's global_pool lock state moves ----
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

                // ---- allocator_4k_map: dom unchanged; only the targeted entry's global_pool lock state changed ----
                final(self).allocator_4k_map.dom() == old(self).allocator_4k_map.dom(),
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).owning_container == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).owning_container,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages,
                forall|k: usize| #![auto] old(self).allocator_4k_map.dom().contains(k) && k != alloc_ptr_4k ==>
                    final(self).allocator_4k_map.spec_index(k) == old(self).allocator_4k_map.spec_index(k),

                // ---- LocalContext: phases preserved ----
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),

                // ---- The lock perm + lock ensures (forwarded from UnLockedMap::wlock_global_pool) ----
                wlock_ensures(
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool,
                    final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool,
                    LockId{
                        container: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().container_depth(),
                        process: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().process_depth(),
                        major: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().current_lock_major(),
                        minor: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().lock_minor(),
                    },
                    final(lctx).thread_id(),
                    ret.view(),
                ),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().insert(
                    final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .global_pool.lock_id(),
                ),
                final(lctx).lock_maps_inserted(
                    old(lctx),
                    KernelObjId::AllocatorGlobalPoll(
                        PageSize::SZ4k, alloc_ptr_4k,
                    ),
                    final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .global_pool.lock_id(),
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
                assert({
                    &&& old(lctx).obj_id_fresh(
                            KernelObjId::AllocatorGlobalPoll(
                                PageSize::SZ4k,
                                alloc_ptr_4k,
                            ),
                        )
                    &&& wlock_requires(
                        old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                            .global_pool,
                        old(lctx),
                    )
                }) by {
                    reveal(LocalContext::wf);
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(allocator_4k_locked_match_lctx);
                    reveal(LocalContext::obj_id_fresh);
                    reveal(LocalContext::lock_map_contains);
                    reveal(wlock_requires);
                };
            }
            let ret = self.allocator_4k_map.wlock_global_pool(alloc_ptr_4k, Tracked(&mut *lctx), Ghost(PageSize::SZ4k));

            proof {
                assert(self.inv()) by {
                    assert(allocator_perms_wf(
                        self.allocator_4k_map,
                    )) by {
                        reveal(allocator_perms_wf);
                    };
                    assert(allocator_4k_invariant_fields_unchanged(
                        old(self).allocator_4k_map,
                        self.allocator_4k_map,
                    )) by {
                        allocator_4k_global_pool_lock_op_preserves_invariant_fields(
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
                            self.container_map,
                            self.allocator_4k_map,
                            self.page_array,
                        )) by {
                            assert forall|a_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId|
                                #![trigger self.allocator_4k_map.spec_index(a_ptr)
                                    .cpu_caches.spec_index(cpu_id).view().view()]
                                self.allocator_4k_map.dom().contains(a_ptr)
                                    && cpu_id_valid(cpu_id)
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
                    reveal(KernelK::inv);
                };
                // ---- locked_objects_match_lctx: global pool slot gained, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(allocator_4k_locked_match_lctx);
                };
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(page_lock_id_aligned);
                };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                };
            }
            ret
        }

        #[verifier::spinoff_prover]
        pub fn wunlock_allocator_global_pool(
            &mut self,
            alloc_ptr_4k: RwLockPageAllocatorPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                old(lctx).wf(),
                old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id()
                    == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool
                        .locking_thread()->Write_lock_id,
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.wlocked_by(old(lctx)),
                old(self).locked_objects_match_lctx(old(lctx)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                final(lctx).wf(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),

                // ---- Every held lock still matches lctx (global pool now released) ----
                final(self).locked_objects_match_lctx(final(lctx)),
                forall|page_index: PageIndex|
                    #![trigger old(self).page_array.spec_index(page_index).view().wlocked_by(old(lctx))]
                    page_index_wf(page_index)
                        && old(self).page_array.spec_index(page_index).view().wlocked_by(old(lctx))
                    ==> final(self).page_array.spec_index(page_index).view().wlocked_by(final(lctx))
                        && final(self).page_array.spec_index(page_index).view().locked_by(final(lctx)),
                forall|process_ptr: RwLockProcessPtr|
                    #![trigger old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx))]
                    old(self).process_map.dom().contains(process_ptr)
                        && old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx))
                    ==> final(self).process_map.dom().contains(process_ptr)
                        && final(self).process_map.spec_index(process_ptr).wlocked_by(final(lctx))
                        && final(self).process_map.spec_index(process_ptr).locked_by(final(lctx)),

                // ---- Dynamic lock ids remain aligned ----
                lock_id_aligned(final(self), final(lctx)),

                // ---- Field framing: only allocator_4k_map's global_pool lock state moves ----
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

                // ---- allocator_4k_map: dom unchanged; only the targeted entry's global_pool lock state changed (now unlocked) ----
                final(self).allocator_4k_map.dom() == old(self).allocator_4k_map.dom(),
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).owning_container == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).owning_container,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages,
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

                // ---- wunlock ensures (forwarded from UnLockedMap::wunlock_global_pool) ----
                wunlock_ensures(
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool,
                    final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool,
                ),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().remove(
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .global_pool.lock_id(),
                ),
                final(lctx).lock_maps_removed(
                    old(lctx),
                    KernelObjId::AllocatorGlobalPoll(
                        PageSize::SZ4k, alloc_ptr_4k,
                    ),
                ),
        {
            proof {
                assert(
                    {
                        &&& old(self).allocator_4k_map.perms_wf()
                        &&& old(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf()
                        &&& old(lctx).allocator_4k_lock_map().dom().contains(
                            AllocatorLockObjId::GlobalPool(alloc_ptr_4k),
                        )
                        &&& old(lctx).allocator_4k_lock_map().spec_index(
                            AllocatorLockObjId::GlobalPool(alloc_ptr_4k)
                        ) == old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                            .global_pool.lock_id()
                    }
                ) by {
                    reveal(allocator_perms_wf);
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(allocator_4k_locked_match_lctx);
                };
            }
            self.allocator_4k_map.wunlock_global_pool(alloc_ptr_4k, Tracked(&mut *lctx), lock_perm, Ghost(PageSize::SZ4k));

            proof {
                assert(self.inv()) by {
                    assert(allocator_perms_wf(
                        self.allocator_4k_map,
                    )) by {
                        reveal(allocator_perms_wf);
                    };
                    assert(allocator_4k_invariant_fields_unchanged(
                        old(self).allocator_4k_map,
                        self.allocator_4k_map,
                    )) by {
                        allocator_4k_global_pool_lock_op_preserves_invariant_fields(
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
                            self.container_map,
                            self.allocator_4k_map,
                            self.page_array,
                        )) by {
                            assert forall|a_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId|
                                #![trigger self.allocator_4k_map.spec_index(a_ptr)
                                    .cpu_caches.spec_index(cpu_id).view().view()]
                                self.allocator_4k_map.dom().contains(a_ptr)
                                    && cpu_id_valid(cpu_id)
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
                    reveal(KernelK::inv);
                };
                // ---- locked_objects_match_lctx: global pool slot released, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(allocator_4k_locked_match_lctx);
                };
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(page_lock_id_aligned);
                };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                };
            }
        }

        #[verifier::spinoff_prover]
        pub fn wlock_page(
            &mut self,
            page_index: PageIndex,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Tracked<LockPerm>)
            requires
                old(self).inv(),
                old(lctx).wf(),
                page_index_wf(page_index),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).lock_id_acyclic(old(self).page_array.lock_id_by_index(page_index)),
                old(self).locked_objects_match_lctx(old(lctx)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                final(lctx).wf(),

                // ---- Every held lock still matches lctx (page slot now locked) ----
                final(self).locked_objects_match_lctx(final(lctx)),
                lock_id_aligned(final(self), final(lctx)),
                final(self).page_array.spec_index(page_index).view().wlocked_by(final(lctx)),

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
                final(self).page_array.view().len() == old(self).page_array.view().len(),
                final(self).page_array.unchanged_except(&old(self).page_array, page_index),

                // ---- LocalContext: phases preserved ----
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),

                // ---- The lock perm + lock ensures (forwarded from LockedArray::wlock) ----
                wlock_ensures(
                    old(self).page_array.spec_index(page_index).view(),
                    final(self).page_array.spec_index(page_index).view(),
                    old(self).page_array.lock_id_by_index(page_index),
                    final(lctx).thread_id(),
                    ret.view(),
                ),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().insert(
                    final(self).page_array.lock_id_by_index(page_index),
                ),
                final(lctx).lock_maps_inserted(
                    old(lctx),
                    KernelObjId::Page(page_index),
                    final(self).page_array.lock_id_by_index(page_index),
                ),
        {
            proof {
                assert(old(self).page_array.inv()) by {
                    reveal(page_array_wf);
                };
                assert({
                    &&& old(lctx).obj_id_fresh(
                        KernelObjId::Page(page_index),
                    )
                    &&& wlock_requires(
                        old(self).page_array.spec_index(page_index).view(),
                        old(lctx),
                    )
                }) by {
                    reveal(LocalContext::wf);
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(LocalContext::obj_id_fresh);
                    reveal(LocalContext::lock_map_contains);
                    reveal(wlock_requires);
                };
            }
            let ret = self.page_array.wlock(page_index, Tracked(&mut *lctx), Ghost(KernelObjId::Page(page_index)));
            proof {
                assert(self.inv()) by {
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
                            reveal(LockedArray::payloads_unchanged);
                            reveal(allocator_4k_pages_wf);
                            reveal(allocator_2m_pages_wf);
                            reveal(allocator_1g_pages_wf);
                        };
                        assert(container_page_owner_wf(
                            self.container_map,
                            self.page_array,
                        )) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(container_page_owner_wf);
                        };
                        assert(container_process_page_pagetable_wf(
                            self.container_map,
                            self.process_map,
                            self.pagetable_map,
                            self.page_array,
                        )) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(container_process_page_pagetable_wf);
                        };
                        assert(container_pages_wf(
                            self.page_array,
                            self.container_map,
                        )) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(container_pages_wf);
                        };
                        assert(process_pages_wf(
                            self.page_array,
                            self.process_map,
                        )) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(process_pages_wf);
                        };
                        assert(hugepage_2m_wf(self.page_array)) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(hugepage_2m_wf);
                        };
                        assert(hugepage_1g_wf(self.page_array)) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(hugepage_1g_wf);
                        };
                        assert(page_pagetable_wf(
                            self.pagetable_map,
                            self.page_array,
                        )) by {
                            page_pagetable_wf_preserved_for_page_payloads_unchanged(old(self).pagetable_map, self.pagetable_map, old(self).page_array, self.page_array);
                        };
                        assert(pagetable_pages_wf(
                            self.pagetable_map,
                            self.page_array,
                        )) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(pagetable_pages_wf);
                        };
                        assert(iommu_table_pages_wf(
                            self.iommu_table_map,
                            self.page_array,
                        )) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(iommu_table_pages_wf);
                        };
                        assert(pcid_allocator_pages_wf(
                            self.page_array,
                            self.pcid_allocator_map,
                        )) by {
                            pcid_allocator_pages_wf_preserved_for_page_payloads_unchanged(old(self).page_array, self.page_array, self.pcid_allocator_map);
                        };
                        assert(thread_pages_wf(
                            self.thread_map,
                            self.page_array,
                        )) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(thread_pages_wf);
                        };
                        assert(thread_staged_pages_4k_wf(self.thread_map, self.page_array)) by { reveal(LockedArray::payloads_unchanged); reveal(thread_staged_pages_4k_wf); };
                        assert(thread_staged_pages_2m_wf(self.thread_map, self.page_array)) by { reveal(LockedArray::payloads_unchanged); reveal(thread_staged_pages_2m_wf); };
                        assert(thread_staged_pages_1g_wf(self.thread_map, self.page_array)) by { reveal(LockedArray::payloads_unchanged); reveal(thread_staged_pages_1g_wf); };
                        assert(endpoint_pages_wf(
                            self.endpoint_map,
                            self.page_array,
                        )) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(endpoint_pages_wf);
                        };
                        assert(container_allocator_free_4k_page_wf(
                            self.container_map,
                            self.allocator_4k_map,
                            self.page_array,
                        )) by {
                            page_ptr_lemma1();
                            reveal(LockedArray::payloads_unchanged);
                            reveal(container_allocator_free_4k_page_wf);
                            reveal(allocator_free_page_ptrs_wf);
                            reveal(container_allocator_wf);
                            reveal(container_page_owner_wf);
                        };
                        assert(container_allocator_free_2m_page_wf(
                            self.container_map,
                            self.allocator_2m_map,
                            self.page_array,
                        )) by {
                            page_ptr_lemma1();
                            reveal(LockedArray::payloads_unchanged);
                            reveal(container_allocator_free_2m_page_wf);
                            reveal(allocator_free_page_ptrs_wf);
                            reveal(container_allocator_wf);
                            reveal(container_page_owner_wf);
                        };
                        assert(container_allocator_free_1g_page_wf(
                            self.container_map,
                            self.allocator_1g_map,
                            self.page_array,
                        )) by {
                            page_ptr_lemma1();
                            reveal(LockedArray::payloads_unchanged);
                            reveal(container_allocator_free_1g_page_wf);
                            reveal(allocator_free_page_ptrs_wf);
                            reveal(container_allocator_wf);
                            reveal(container_page_owner_wf);
                        };
                    };
                    reveal(KernelK::inv);
                };
                // ---- locked_objects_match_lctx: page slot gained, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(page_locked_match_lctx);
                };
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);
                    reveal(page_lock_id_aligned);
                    reveal(lock_ensures);
                    reveal(LocalContext::lock_maps_inserted);
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
                old(lctx).wf(),
                page_index_wf(page_index),
                old(self).page_array.spec_index(page_index).view().being_killed() == false,
                old(self).page_array.spec_index(page_index).view().wlocked_by(old(lctx)),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id()
                    == old(self).page_array.spec_index(page_index).view().locking_thread()->Write_lock_id,
                old(self).locked_objects_match_lctx(old(lctx)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                final(lctx).wf(),

                // ---- Every held lock still matches lctx (page slot now released) ----
                final(self).locked_objects_match_lctx(final(lctx)),
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
                final(self).page_array.view().len() == old(self).page_array.view().len(),
                final(self).page_array.unchanged_except(&old(self).page_array, page_index),
                final(self).page_array.spec_index(page_index).view().locking_thread() is None,

                // ---- LocalContext: lock dropped; thread preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` flips it Acquire → Release (same trap as the
                // `LockedArray::wunlock` NOTE).
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,

                // ---- wunlock ensures (forwarded from LockedArray::wunlock) ----
                wunlock_ensures(old(self).page_array.spec_index(page_index).view(), final(self).page_array.spec_index(page_index).view()),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().remove(
                    old(self).page_array.lock_id_by_index(page_index),
                ),
                final(lctx).lock_maps_removed(
                    old(lctx), KernelObjId::Page(page_index),
                ),
        {
            assert({
                &&& self.page_array.inv()
                &&& lctx.page_lock_map().dom().contains(page_index)
                &&& lctx.page_lock_map().spec_index(page_index)
                    == self.page_array.lock_id_by_index(page_index)
            }) by {
                reveal(page_array_wf);
                reveal(KernelK::locked_objects_match_lctx);
                reveal(page_locked_match_lctx);
            };
            self.page_array.wunlock(page_index, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::Page(page_index)));
            proof {
                assert(self.inv()) by {
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
                            reveal(LockedArray::payloads_unchanged);
                            reveal(allocator_4k_pages_wf);
                            reveal(allocator_2m_pages_wf);
                            reveal(allocator_1g_pages_wf);
                        };
                        assert(container_page_owner_wf(
                            self.container_map,
                            self.page_array,
                        )) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(container_page_owner_wf);
                        };
                        assert(container_process_page_pagetable_wf(
                            self.container_map,
                            self.process_map,
                            self.pagetable_map,
                            self.page_array,
                        )) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(container_process_page_pagetable_wf);
                        };
                        assert(container_pages_wf(
                            self.page_array,
                            self.container_map,
                        )) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(container_pages_wf);
                        };
                        assert(process_pages_wf(
                            self.page_array,
                            self.process_map,
                        )) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(process_pages_wf);
                        };
                        assert(hugepage_2m_wf(self.page_array)) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(hugepage_2m_wf);
                        };
                        assert(hugepage_1g_wf(self.page_array)) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(hugepage_1g_wf);
                        };
                        assert(page_pagetable_wf(
                            self.pagetable_map,
                            self.page_array,
                        )) by {
                            page_pagetable_wf_preserved_for_page_payloads_unchanged(old(self).pagetable_map, self.pagetable_map, old(self).page_array, self.page_array);
                        };
                        assert(pagetable_pages_wf(
                            self.pagetable_map,
                            self.page_array,
                        )) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(pagetable_pages_wf);
                        };
                        assert(iommu_table_pages_wf(
                            self.iommu_table_map,
                            self.page_array,
                        )) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(iommu_table_pages_wf);
                        };
                        assert(pcid_allocator_pages_wf(
                            self.page_array,
                            self.pcid_allocator_map,
                        )) by {
                            pcid_allocator_pages_wf_preserved_for_page_payloads_unchanged(old(self).page_array, self.page_array, self.pcid_allocator_map);
                        };
                        assert(thread_pages_wf(
                            self.thread_map,
                            self.page_array,
                        )) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(thread_pages_wf);
                        };
                        assert(thread_staged_pages_wf(
                            self.thread_map,
                            self.page_array,
                        )) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(thread_staged_pages_4k_wf);
                            reveal(thread_staged_pages_2m_wf);
                            reveal(thread_staged_pages_1g_wf);
                        };
                        assert(endpoint_pages_wf(
                            self.endpoint_map,
                            self.page_array,
                        )) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(endpoint_pages_wf);
                        };
                        assert(container_allocator_free_4k_page_wf(
                            self.container_map,
                            self.allocator_4k_map,
                            self.page_array,
                        )) by {
                            page_ptr_lemma1();
                            reveal(LockedArray::payloads_unchanged);
                            reveal(container_allocator_free_4k_page_wf);
                            reveal(allocator_free_page_ptrs_wf);
                            reveal(container_allocator_wf);
                            reveal(container_page_owner_wf);
                        };
                        assert(container_allocator_free_2m_page_wf(
                            self.container_map,
                            self.allocator_2m_map,
                            self.page_array,
                        )) by {
                            page_ptr_lemma1();
                            reveal(LockedArray::payloads_unchanged);
                            reveal(container_allocator_free_2m_page_wf);
                            reveal(allocator_free_page_ptrs_wf);
                            reveal(container_allocator_wf);
                            reveal(container_page_owner_wf);
                        };
                        assert(container_allocator_free_1g_page_wf(
                            self.container_map,
                            self.allocator_1g_map,
                            self.page_array,
                        )) by {
                            page_ptr_lemma1();
                            reveal(LockedArray::payloads_unchanged);
                            reveal(container_allocator_free_1g_page_wf);
                            reveal(allocator_free_page_ptrs_wf);
                            reveal(container_allocator_wf);
                            reveal(container_page_owner_wf);
                        };
                    };
                    reveal(KernelK::inv);
                };
                // ---- locked_objects_match_lctx: page slot released, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(page_locked_match_lctx);
                };
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);
                    reveal(page_lock_id_aligned);
                    reveal(unlock_ensures);
                    reveal(LocalContext::lock_maps_removed);
                };
            }
        }

        pub fn wlock_scheduler(
            &mut self,
            scheduler_ptr: RwLockSchedulerPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Tracked<LockPerm>)
            requires
                old(self).inv(),
                old(lctx).wf(),
                old(self).scheduler_map.dom().contains(scheduler_ptr),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).lock_id_acyclic(LockId{
                    container: old(self).scheduler_map.spec_index(scheduler_ptr).container_depth(),
                    process: old(self).scheduler_map.spec_index(scheduler_ptr).process_depth(),
                    major: old(self).scheduler_map.spec_index(scheduler_ptr).view().current_lock_major(),
                    minor: scheduler_ptr,
                }),
                old(self).locked_objects_match_lctx(old(lctx)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                final(lctx).wf(),

                // ---- Every held lock still matches lctx (scheduler now locked) ----
                final(self).locked_objects_match_lctx(final(lctx)),

                // ---- Dynamic lock ids remain aligned ----
                lock_id_aligned(final(self), final(lctx)),

                // ---- Field framing: only scheduler_map's lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).iommu_table_map     == old(self).iommu_table_map,
                final(self).iommu_root_table     == old(self).iommu_root_table,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).iommu_tlb           == old(self).iommu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).pcid_allocator_map == old(self).pcid_allocator_map,
                final(self).process_map       == old(self).process_map,
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_4k_map  == old(self).allocator_4k_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- scheduler_map: dom unchanged; only the targeted entry's lock state changed ----
                final(self).scheduler_map.dom() == old(self).scheduler_map.dom(),
                final(self).scheduler_map.unchanged_except(&old(self).scheduler_map, scheduler_ptr),

                // ---- LocalContext: phases preserved ----
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),

                // ---- The lock perm + lock ensures (forwarded from LockedMap::wlock) ----
                wlock_ensures(
                    old(self).scheduler_map.spec_index(scheduler_ptr),
                    final(self).scheduler_map.spec_index(scheduler_ptr),
                    LockId{
                        container: old(self).scheduler_map.spec_index(scheduler_ptr).container_depth(),
                        process: old(self).scheduler_map.spec_index(scheduler_ptr).process_depth(),
                        major: old(self).scheduler_map.spec_index(scheduler_ptr).view().current_lock_major(),
                        minor: scheduler_ptr,
                    },
                    final(lctx).thread_id(),
                    ret.view(),
                ),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().insert(
                    final(self).scheduler_map.lock_id_by_key(scheduler_ptr),
                ),
        {
            proof {
                assert(old(self).scheduler_map.perms_wf()) by {
                    reveal(scheduler_perms_wf);
                };
                assert({
                    &&& old(lctx).obj_id_fresh(
                        KernelObjId::Scheduler(scheduler_ptr),
                    )
                    &&& wlock_requires(
                        old(self).scheduler_map.spec_index(scheduler_ptr),
                        old(lctx),
                    )
                }) by {
                    reveal(LocalContext::wf);
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(scheduler_locked_match_lctx);
                    reveal(LocalContext::obj_id_fresh);
                    reveal(LocalContext::lock_map_contains);
                    reveal(wlock_requires);
                };
            }
            let ret = self.scheduler_map.wlock(scheduler_ptr, Tracked(&mut *lctx), Ghost(KernelObjId::Scheduler(scheduler_ptr)));
            proof {
                assert(self.inv()) by {
                    assert(scheduler_perms_wf(
                        self.scheduler_map,
                    )) by {
                        reveal(scheduler_perms_wf);
                    };
                    assert(scheduler_invariant_fields_unchanged(
                        old(self).scheduler_map,
                        self.scheduler_map,
                    )) by {
                        scheduler_lock_op_preserves_invariant_fields(
                            old(self).scheduler_map,
                            self.scheduler_map,
                            scheduler_ptr,
                        );
                    };
                    assert(self.subsystems_inv()) by {
                        reveal(KernelK::default_pagetable_wf);
                    };
                    assert(self.process_management_inv()) by {
                        assert(container_scheduler_wf(
                            self.container_map,
                            self.scheduler_map,
                        )) by {
                            reveal(scheduler_invariant_fields_unchanged);
                            reveal(container_scheduler_wf);
                        };
                        assert(container_thread_scheduler_wf(
                            self.container_map,
                            self.thread_map,
                            self.scheduler_map,
                        )) by {
                            reveal(scheduler_invariant_fields_unchanged);
                            reveal(container_thread_wf);
                            reveal(container_scheduler_wf);
                            reveal(container_thread_scheduler_wf);
                        };
                    };
                    reveal(KernelK::inv);
                };
                // ---- locked_objects_match_lctx: scheduler slot gained, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(scheduler_locked_match_lctx);
                };
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);
                    reveal(page_lock_id_aligned);
                    reveal(lock_ensures);
                    reveal(LocalContext::lock_maps_inserted);
                };
            }
            ret
        }

        pub fn wunlock_scheduler(
            &mut self,
            scheduler_ptr: RwLockSchedulerPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                old(lctx).wf(),
                old(self).scheduler_map.dom().contains(scheduler_ptr),
                old(self).scheduler_map.spec_index(scheduler_ptr)
                    .wlocked_by(old(lctx)),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id()
                    == old(self).scheduler_map.spec_index(scheduler_ptr)
                        .locking_thread()->Write_lock_id,
                old(self).locked_objects_match_lctx(old(lctx)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                final(lctx).wf(),

                // ---- Every held lock still matches lctx (scheduler now released) ----
                final(self).locked_objects_match_lctx(final(lctx)),

                // ---- Dynamic lock ids remain aligned ----
                lock_id_aligned(final(self), final(lctx)),

                // ---- Field framing: only scheduler_map's lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).iommu_table_map     == old(self).iommu_table_map,
                final(self).iommu_root_table     == old(self).iommu_root_table,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).iommu_tlb           == old(self).iommu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).pcid_allocator_map == old(self).pcid_allocator_map,
                final(self).process_map       == old(self).process_map,
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_4k_map  == old(self).allocator_4k_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- scheduler_map: dom unchanged; only the targeted entry's lock state changed (now unlocked) ----
                final(self).scheduler_map.dom() == old(self).scheduler_map.dom(),
                final(self).scheduler_map.unchanged_except(&old(self).scheduler_map, scheduler_ptr),
                final(self).scheduler_map.spec_index(scheduler_ptr).locking_thread() is None,

                // ---- LocalContext: lock dropped; thread preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` flips it Acquire → Release (same trap as the
                // `LockedArray::wunlock` NOTE).
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,

                // ---- wunlock ensures (forwarded from LockedMap::wunlock) ----
                wunlock_ensures(
                    old(self).scheduler_map.spec_index(scheduler_ptr),
                    final(self).scheduler_map.spec_index(scheduler_ptr),
                ),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().remove(
                    old(self).scheduler_map.lock_id_by_key(scheduler_ptr),
                ),
        {
            proof {
                assert({
                    &&& old(self).scheduler_map.perms_wf()
                    &&& old(self).scheduler_map.spec_index(scheduler_ptr).inv()
                }) by {
                    reveal(scheduler_perms_wf);
                };
                assert({
                    &&& old(lctx).scheduler_lock_map().dom().contains(
                        scheduler_ptr,
                    )
                    &&& old(lctx).scheduler_lock_map().spec_index(scheduler_ptr)
                        == old(self).scheduler_map.lock_id_by_key(scheduler_ptr)
                }) by {
                    reveal(KernelK::locked_objects_match_lctx);
                    reveal(scheduler_locked_match_lctx);
                };
            }
            self.scheduler_map.wunlock(scheduler_ptr, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::Scheduler(scheduler_ptr)));
            proof {
                assert(self.inv()) by {
                    assert(scheduler_perms_wf(
                        self.scheduler_map,
                    )) by {
                        reveal(scheduler_perms_wf);
                    };
                    assert(scheduler_invariant_fields_unchanged(
                        old(self).scheduler_map,
                        self.scheduler_map,
                    )) by {
                        scheduler_lock_op_preserves_invariant_fields(
                            old(self).scheduler_map,
                            self.scheduler_map,
                            scheduler_ptr,
                        );
                    };
                    assert(self.subsystems_inv()) by {
                        reveal(KernelK::default_pagetable_wf);
                    };
                    assert(self.process_management_inv()) by {
                        assert(container_scheduler_wf(
                            self.container_map,
                            self.scheduler_map,
                        )) by {
                            reveal(scheduler_invariant_fields_unchanged);
                            reveal(container_scheduler_wf);
                        };
                        assert(container_thread_scheduler_wf(
                            self.container_map,
                            self.thread_map,
                            self.scheduler_map,
                        )) by {
                            reveal(scheduler_invariant_fields_unchanged);
                            reveal(container_thread_wf);
                            reveal(container_scheduler_wf);
                            reveal(container_thread_scheduler_wf);
                        };
                    };
                    reveal(KernelK::inv);
                };
                // ---- locked_objects_match_lctx: scheduler slot released, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(scheduler_locked_match_lctx);
                };
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);
                    reveal(page_lock_id_aligned);
                    reveal(unlock_ensures);
                    reveal(LocalContext::lock_maps_removed);
                };
            }
        }

        pub fn wlock_endpoint(
            &mut self,
            endpoint_ptr: RwLockEndpointPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Tracked<LockPerm>)
            requires
                old(self).inv(),
                old(lctx).wf(),
                old(self).endpoint_map.dom().contains(endpoint_ptr),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).lock_id_acyclic(old(self).endpoint_map.lock_id_by_key(endpoint_ptr)),
                old(self).locked_objects_match_lctx(old(lctx)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                final(self).inv(),
                final(lctx).wf(),
                final(self).locked_objects_match_lctx(final(lctx)),
                lock_id_aligned(final(self), final(lctx)),
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
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                wlock_ensures(
                    old(self).endpoint_map.spec_index(endpoint_ptr),
                    final(self).endpoint_map.spec_index(endpoint_ptr),
                    old(self).endpoint_map.lock_id_by_key(endpoint_ptr),
                    final(lctx).thread_id(),
                    ret.view(),
                ),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().insert(
                    final(self).endpoint_map.lock_id_by_key(endpoint_ptr),
                ),
        {
            proof {
                assert(old(self).endpoint_map.perms_wf()) by { reveal(endpoint_perms_wf); };
                assert({
                    &&& old(lctx).obj_id_fresh(KernelObjId::Endpoint(endpoint_ptr))
                    &&& wlock_requires(
                        old(self).endpoint_map.spec_index(endpoint_ptr),
                        old(lctx),
                    )
                }) by { reveal(LocalContext::wf); reveal(KernelK::locked_objects_match_lctx); reveal(endpoint_locked_match_lctx); reveal(LocalContext::obj_id_fresh); reveal(LocalContext::lock_map_contains); reveal(wlock_requires); };
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
                assert(self.locked_objects_match_lctx(&*lctx)) by { reveal(endpoint_locked_match_lctx); };
                assert(lock_id_aligned(self, &*lctx)) by { reveal(lock_id_aligned); reveal(page_lock_id_aligned); reveal(LocalContext::lock_maps_inserted); };
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
                old(lctx).wf(),
                old(self).endpoint_map.dom().contains(endpoint_ptr),
                old(self).endpoint_map.spec_index(endpoint_ptr).wlocked_by(old(lctx)),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id()
                    == old(self).endpoint_map.spec_index(endpoint_ptr)
                        .locking_thread()->Write_lock_id,
                old(self).locked_objects_match_lctx(old(lctx)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                final(self).inv(),
                final(lctx).wf(),
                final(self).locked_objects_match_lctx(final(lctx)),
                lock_id_aligned(final(self), final(lctx)),
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
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,
                wunlock_ensures(
                    old(self).endpoint_map.spec_index(endpoint_ptr),
                    final(self).endpoint_map.spec_index(endpoint_ptr),
                ),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().remove(
                    old(self).endpoint_map.lock_id_by_key(endpoint_ptr),
                ),
        {
            proof {
                assert({
                    &&& old(self).endpoint_map.perms_wf()
                    &&& old(self).endpoint_map.spec_index(endpoint_ptr).inv()
                }) by { reveal(endpoint_perms_wf); reveal(endpoints_inv); };
                assert({
                    &&& old(lctx).endpoint_lock_map().dom().contains(endpoint_ptr)
                    &&& old(lctx).endpoint_lock_map().spec_index(endpoint_ptr)
                        == old(self).endpoint_map.lock_id_by_key(endpoint_ptr)
                }) by { reveal(KernelK::locked_objects_match_lctx); reveal(endpoint_locked_match_lctx); };
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
                assert(self.locked_objects_match_lctx(&*lctx)) by { reveal(endpoint_locked_match_lctx); };
                assert(lock_id_aligned(self, &*lctx)) by { reveal(lock_id_aligned); reveal(page_lock_id_aligned); reveal(LocalContext::lock_maps_removed); };
            }
        }

    }
}
