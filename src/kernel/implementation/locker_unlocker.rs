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
                cpu_id_valid(cpu_id),
                wlock_requires(old(self).cpu_array[cpu_id]@, old(lctx)),
                old(lctx).lock_id_acyclic(old(self).cpu_array.lock_id_by_index(cpu_id)),
                old(lctx).obj_id_fresh(KernelObjId::Cpu(cpu_id)),
                old(self).locked_objects_match_lctx(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Every held lock still matches lctx (cpu now locked) ----
                final(self).locked_objects_match_lctx(final(lctx)),

                // ---- Field framing: only cpu_array's lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).scheduler_map     == old(self).scheduler_map,
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
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),

                // ---- The lock perm + lock ensures (forwarded from LockedArray::wlock) ----
                wlock_ensures(
                    old(self).cpu_array[cpu_id]@,
                    final(self).cpu_array[cpu_id]@,
                    old(self).cpu_array.lock_id_by_index(cpu_id),
                    final(lctx).thread_id(),
                    ret@,
                ),
                lock_ensures(
                    old(lctx),
                    final(lctx),
                    final(self).cpu_array[cpu_id]@@,
                    old(self).cpu_array.lock_id_by_index(cpu_id),
                    KernelObjId::Cpu(cpu_id),
                ),
        {
            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
            }
            let ret = self.cpu_array.wlock(cpu_id, Tracked(&mut *lctx), Ghost(KernelObjId::Cpu(cpu_id)));
            proof {
                // ---- subsystems_inv ----
                assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
                assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
                assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
                assert(thread_perms_wf(self.thread_map)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                // ---- memory_management_inv ----
                assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf);
                };
                assert(container_page_owner_wf(self.container_map, self.page_array)) by {
                    reveal(container_page_owner_wf);
                };
                assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by {
                    reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
                };
                assert(container_pages_wf(self.page_array, self.container_map)) by {
                    reveal(container_pages_wf);
                };
                assert(process_pages_wf(self.page_array, self.process_map)) by {
                    reveal(process_pages_wf);
                };
                assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    reveal(container_process_allocator_quota_4k_wf);
                    reveal(container_process_allocator_quota_2m_wf);
                    reveal(container_process_allocator_quota_1g_wf); reveal(container_allocator_wf); reveal(container_process_wf); reveal(container_thread_wf);
                };
                assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    reveal(container_allocator_wf);
                };
                assert(self.allocator_free_pages_wf());
                assert(self.memory_management_inv());
                // ---- process_management_inv ----
                assert(container_tree_wf(self.root_container, self.container_map));
                assert(container_process_wf(self.container_map, self.process_map)) by {
                    reveal(container_process_wf);
                };
                assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                    reveal(container_process_wf); reveal(per_container_process_tree_wf);
                };
                assert(container_cpu_wf(self.container_map, self.cpu_array)) by {
                    reveal(container_cpu_wf);
                };
                assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
                    reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
                    reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf);
                };
                assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
                    reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
                };
                assert(process_cpu_wf(self.process_map, self.cpu_array)) by {
                    reveal(process_cpu_wf);
                };
                assert(thread_cpu_wf(self.thread_map, self.cpu_array)) by {
                    reveal(thread_cpu_wf);
                };
                assert(self.process_management_inv());
                // ---- inv() direct conjuncts ----
                assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
                    reveal(cpu_dirty_map_contains_container_processes);
                    reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                    reveal(cpu_dirty_map_proc_pcid_match);
                    reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                    reveal(container_cpu_wf);
                };
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
                assert(self.inv());
                // ---- locked_objects_match_lctx: cpu slot gained, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(container_locked_match_lctx);
                    reveal(process_locked_match_lctx);
                    reveal(thread_locked_match_lctx);
                    reveal(endpoint_locked_match_lctx);
                    reveal(scheduler_locked_match_lctx);
                    reveal(pagetable_locked_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(cpu_locked_match_lctx);
                    reveal(allocator_locked_match_lctx);
                }
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
                cpu_id_valid(cpu_id),
                old(self).cpu_array[cpu_id]@.being_killed() == false,
                unlock_requires::<Cpu>(old(lctx)),
                lock_perm@.state() is WriteLock,
                lock_perm@.thread_id() == old(lctx).thread_id(),
                old(lctx).cpu_lock_map().dom().contains(cpu_id),
                old(lctx).cpu_lock_map()[cpu_id] == old(self).cpu_array.lock_id_by_index(cpu_id),
                lock_perm@.lock_id() == old(self).cpu_array[cpu_id]@.locking_thread()->Write_lock_id,
                old(self).locked_objects_match_lctx(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Every held lock still matches lctx (cpu now released) ----
                final(self).locked_objects_match_lctx(final(lctx)),

                // ---- Field framing: only cpu_array's lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).scheduler_map     == old(self).scheduler_map,
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
                final(self).cpu_array[cpu_id]@.locking_thread() is None,
                wunlock_ensures(
                    old(self).cpu_array[cpu_id]@,
                    final(self).cpu_array[cpu_id]@,
                ),

                // ---- LocalContext: lock dropped; thread + user-view phase preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` transitions it Acquire -> Release, so restating
                // `== old` would contradict it and make the postcondition `false`
                // in an Acquire section. `unlock_ensures` is the source of truth
                // for the phase transition (same trap as the NOTE on
                // `LockedArray::wunlock`). user_view is separately preserved.
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),

                // ---- wunlock ensures (forwarded from LockedArray::wunlock) ----
                unlock_ensures(
                    old(lctx),
                    final(lctx),
                    final(self).cpu_array[cpu_id]@@,
                    lock_perm@.lock_id(),
                    KernelObjId::Cpu(cpu_id),
                ),
                final(lctx).lock_maps_removed(old(lctx), KernelObjId::Cpu(cpu_id)),
        {
            proof {
                reveal(KernelK::locked_objects_match_lctx);
                reveal(cpu_locked_match_lctx);
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
            }
            self.cpu_array.wunlock(cpu_id, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::Cpu(cpu_id)));
            // Re-establish inv(). Only `cpu_array[cpu_id]`'s lock state moved
            // (now unlocked); every payload view, every other slot, and every
            // other KernelK field is unchanged. Same template as wlock_cpu.
            proof {
                // ---- subsystems_inv ----
                assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
                assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
                assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
                assert(thread_perms_wf(self.thread_map)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                // ---- memory_management_inv ----
                assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf);
                };
                assert(container_page_owner_wf(self.container_map, self.page_array)) by {
                    reveal(container_page_owner_wf);
                };
                assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by {
                    reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
                };
                assert(container_pages_wf(self.page_array, self.container_map)) by {
                    reveal(container_pages_wf);
                };
                assert(process_pages_wf(self.page_array, self.process_map)) by {
                    reveal(process_pages_wf);
                };
                assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    reveal(container_process_allocator_quota_4k_wf);
                    reveal(container_process_allocator_quota_2m_wf);
                    reveal(container_process_allocator_quota_1g_wf); reveal(container_allocator_wf); reveal(container_process_wf); reveal(container_thread_wf);
                };
                assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    reveal(container_allocator_wf);
                };
                assert(self.allocator_free_pages_wf());
                assert(self.memory_management_inv());
                // ---- process_management_inv ----
                assert(container_tree_wf(self.root_container, self.container_map));
                assert(container_process_wf(self.container_map, self.process_map)) by {
                    reveal(container_process_wf);
                };
                assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                    reveal(container_process_wf); reveal(per_container_process_tree_wf);
                };
                assert(container_cpu_wf(self.container_map, self.cpu_array)) by {
                    reveal(container_cpu_wf);
                };
                assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
                    reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
                    reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf);
                };
                assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
                    reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
                };
                assert(process_cpu_wf(self.process_map, self.cpu_array)) by {
                    reveal(process_cpu_wf);
                };
                assert(thread_cpu_wf(self.thread_map, self.cpu_array)) by {
                    reveal(thread_cpu_wf);
                };
                assert(self.process_management_inv());
                // ---- inv() direct conjuncts ----
                assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
                    reveal(cpu_dirty_map_contains_container_processes);
                    reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                    reveal(cpu_dirty_map_proc_pcid_match);
                    reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                    reveal(container_cpu_wf);
                };
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
                assert(self.inv());
                // ---- locked_objects_match_lctx: cpu slot released, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(container_locked_match_lctx);
                    reveal(process_locked_match_lctx);
                    reveal(thread_locked_match_lctx);
                    reveal(endpoint_locked_match_lctx);
                    reveal(scheduler_locked_match_lctx);
                    reveal(pagetable_locked_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(cpu_locked_match_lctx);
                    reveal(allocator_locked_match_lctx);
                }
            }
        }


        pub fn wlock_container_unless_killed(
            &mut self,
            container_ptr: RwLockContainerPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: (bool, Option<Tracked<LockPerm>>))
            requires
                old(self).inv(),
                old(self).container_map.dom().contains(container_ptr),
                old(self).container_map.spec_index(container_ptr).locked_by(old(lctx)) == false,
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).user_view_locking_state() is Acquire,
                old(lctx).lock_id_acyclic(old(self).container_map.lock_id_by_key(container_ptr)),
                old(lctx).obj_id_fresh(KernelObjId::Container(container_ptr)),
                old(self).locked_objects_match_lctx(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Every held lock still matches lctx (success: container locked; failure: no-op) ----
                final(self).locked_objects_match_lctx(final(lctx)),

                // ---- Field framing: only container_map's lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).scheduler_map     == old(self).scheduler_map,
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
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),

                // ---- Failure: container is being killed; complete no-op ----
                ret.0 == false ==>
                {
                    &&& old(self).container_map.spec_index(container_ptr).being_killed() == true
                    &&& final(self).container_map.spec_index(container_ptr) == old(self).container_map.spec_index(container_ptr)
                    &&& ret.1 is None
                    &&& final(lctx).lock_maps_equal(old(lctx))
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
                        ret.1.unwrap()@,
                    )
                    &&& lock_ensures(
                        old(lctx),
                        final(lctx),
                        old(self).container_map.spec_index(container_ptr).view(),
                        old(self).container_map.lock_id_by_key(container_ptr),
                        KernelObjId::Container(container_ptr),
                    )
                },
        {
            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
            }
            let res = self.container_map.wlock_unless_killed(
                container_ptr,
                Tracked(&mut *lctx),
                Ghost(KernelObjId::Container(container_ptr)),
            );
            proof {
                // ---- subsystems_inv ----
                assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
                assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
                assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
                assert(thread_perms_wf(self.thread_map)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                // ---- memory_management_inv ----
                assert(self.memory_management_inv()) by {
                    assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf);
                    };
                    assert(container_page_owner_wf(self.container_map, self.page_array)) by {
                        container_page_owner_wf_preserved_for_owning_container_eq(old(self).container_map, self.container_map, old(self).page_array, self.page_array);
                    };
                    assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by {
                        reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
                    };
                    assert(container_pages_wf(self.page_array, self.container_map)) by {
                        reveal(container_pages_wf);
                    };
                    assert(process_pages_wf(self.page_array, self.process_map)) by {
                        reveal(process_pages_wf);
                    };
                    assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(container_process_allocator_quota_4k_wf);
                        reveal(container_process_allocator_quota_2m_wf);
                        reveal(container_process_allocator_quota_1g_wf); reveal(container_allocator_wf); reveal(container_process_wf); reveal(container_thread_wf);
                    };
                    assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(container_allocator_wf);
                    };
                    assert(self.allocator_free_pages_wf());
                    assert(container_allocator_free_4k_page_wf(self.container_map, self.allocator_4k_map, self.page_array)) by {
                        reveal(container_allocator_free_4k_page_wf);
                        reveal(container_allocator_wf);
                        reveal(container_page_owner_wf);
                    };
                    assert(container_allocator_free_2m_page_wf(self.container_map, self.allocator_2m_map, self.page_array)) by {
                        reveal(container_allocator_free_2m_page_wf);
                        reveal(container_allocator_wf);
                        reveal(container_page_owner_wf);
                    };
                    assert(container_allocator_free_1g_page_wf(self.container_map, self.allocator_1g_map, self.page_array)) by {
                        reveal(container_allocator_free_1g_page_wf);
                        reveal(container_allocator_wf);
                        reveal(container_page_owner_wf);
                    };
                };
                // ---- process_management_inv ----
                assert(self.process_management_inv()) by {
                    assert(container_tree_wf(self.root_container, self.container_map)) by {
                        container_no_change_to_tree_fields_imply_wf(self.root_container, old(self).container_map, self.container_map);
                    };
                    assert(container_process_wf(self.container_map, self.process_map)) by {
                        reveal(container_process_wf);
                    };
                    assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                        reveal(container_process_wf); reveal(per_container_process_tree_wf);
                    };
                    assert(container_cpu_wf(self.container_map, self.cpu_array)) by {
                        reveal(container_cpu_wf);
                    };
                    assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
                        reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
                        reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf);
                    };
                    assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
                        reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
                    };
                    assert(process_cpu_wf(self.process_map, self.cpu_array)) by {
                        reveal(process_cpu_wf);
                    };
                    assert(container_endpoint_wf(self.container_map, self.endpoint_map)) by {
                        reveal(container_endpoint_wf);
                    };
                    assert(container_scheduler_wf(self.container_map, self.scheduler_map)) by {
                        reveal(container_scheduler_wf);
                    };
                    assert(container_thread_wf(self.container_map, self.thread_map)) by {
                        reveal(container_thread_wf);
                    };
                };
                // ---- inv() direct conjuncts ----
                assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
                    reveal(cpu_dirty_map_contains_container_processes);
                    reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                    reveal(cpu_dirty_map_proc_pcid_match);
                    reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                    reveal(container_cpu_wf);
                };
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
                assert(self.inv());
                // ---- locked_objects_match_lctx: success locks container, failure is a no-op ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(container_locked_match_lctx);
                    reveal(process_locked_match_lctx);
                    reveal(thread_locked_match_lctx);
                    reveal(endpoint_locked_match_lctx);
                    reveal(scheduler_locked_match_lctx);
                    reveal(pagetable_locked_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(cpu_locked_match_lctx);
                    reveal(allocator_locked_match_lctx);
                }
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
        ///  * The caller must ALREADY have flipped `user_view_locking_state`
        ///    to Release (the standard linearization-point precondition for
        ///    unlocking a user-visible object), enforced via `unlock_requires`.
        #[verifier::spinoff_prover]
        pub fn wunlock_container(
            &mut self,
            container_ptr: RwLockContainerPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                old(self).container_map.dom().contains(container_ptr),
                old(self).container_map.spec_index(container_ptr).wlocked_by(old(lctx)),
                old(self).container_map.spec_index(container_ptr).being_killed() == false,
                unlock_requires::<Container>(old(lctx)),
                lock_perm@.state() is WriteLock,
                lock_perm@.thread_id() == old(lctx).thread_id(),
                lock_perm@.lock_id() == old(self).container_map.spec_index(container_ptr).locking_thread()->Write_lock_id,
                old(lctx).container_lock_map().dom().contains(container_ptr),
                old(lctx).container_lock_map()[container_ptr] == old(self).container_map.lock_id_by_key(container_ptr),
                old(self).locked_objects_match_lctx(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Every held lock still matches lctx (container now released) ----
                final(self).locked_objects_match_lctx(final(lctx)),

                // ---- Field framing: only container_map's lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).scheduler_map     == old(self).scheduler_map,
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

                // ---- LocalContext: lock dropped; thread + user-view phase preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` transitions it Acquire -> Release, so restating
                // `== old` would contradict it and make the postcondition `false`
                // in an Acquire section. `unlock_ensures` is the source of truth
                // for the phase transition (same trap as the NOTE on
                // `LockedArray::wunlock`). user_view is separately preserved.
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),

                // ---- wunlock ensures (forwarded from LockedMap::wunlock) ----
                unlock_ensures(
                    old(lctx),
                    final(lctx),
                    final(self).container_map.spec_index(container_ptr).view(),
                    lock_perm@.lock_id(),
                    KernelObjId::Container(container_ptr),
                ),
        {
            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
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
                // ---- subsystems_inv ----
                assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
                assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
                assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
                assert(thread_perms_wf(self.thread_map)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                // ---- memory_management_inv ----
                assert(self.memory_management_inv()) by {
                    assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf);
                    };
                    assert(container_page_owner_wf(self.container_map, self.page_array)) by {
                        reveal(container_page_owner_wf);
                    };
                    assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by {
                        reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
                    };
                    assert(container_pages_wf(self.page_array, self.container_map)) by {
                        reveal(container_pages_wf);
                    };
                    assert(process_pages_wf(self.page_array, self.process_map)) by {
                        reveal(process_pages_wf);
                    };
                    assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(container_process_allocator_quota_4k_wf);
                        reveal(container_process_allocator_quota_2m_wf);
                        reveal(container_process_allocator_quota_1g_wf); reveal(container_allocator_wf); reveal(container_process_wf); reveal(container_thread_wf);
                    };
                    assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(container_allocator_wf);
                    };
                    assert(self.allocator_free_pages_wf());
                    assert(container_allocator_free_4k_page_wf(self.container_map, self.allocator_4k_map, self.page_array)) by {
                        reveal(container_allocator_free_4k_page_wf);
                        reveal(container_allocator_wf);
                        reveal(container_page_owner_wf);
                    };
                    assert(container_allocator_free_2m_page_wf(self.container_map, self.allocator_2m_map, self.page_array)) by {
                        reveal(container_allocator_free_2m_page_wf);
                        reveal(container_allocator_wf);
                        reveal(container_page_owner_wf);
                    };
                    assert(container_allocator_free_1g_page_wf(self.container_map, self.allocator_1g_map, self.page_array)) by {
                        reveal(container_allocator_free_1g_page_wf);
                        reveal(container_allocator_wf);
                        reveal(container_page_owner_wf);
                    };
                };
                // ---- process_management_inv ----
                assert(self.process_management_inv()) by {
                    assert(container_tree_wf(self.root_container, self.container_map)) by {
                        container_no_change_to_tree_fields_imply_wf(self.root_container, old(self).container_map, self.container_map);
                    };
                    assert(container_process_wf(self.container_map, self.process_map)) by {
                        reveal(container_process_wf);
                    };
                    assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                        reveal(container_process_wf); reveal(per_container_process_tree_wf);
                    };
                    assert(container_cpu_wf(self.container_map, self.cpu_array)) by {
                        reveal(container_cpu_wf);
                    };
                    assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
                        reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
                        reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf);
                    };
                    assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
                        reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
                    };
                    assert(process_cpu_wf(self.process_map, self.cpu_array)) by {
                        reveal(process_cpu_wf);
                    };
                    assert(container_endpoint_wf(self.container_map, self.endpoint_map)) by {
                        reveal(container_endpoint_wf);
                    };
                    assert(container_scheduler_wf(self.container_map, self.scheduler_map)) by {
                        reveal(container_scheduler_wf);
                    };
                    assert(container_thread_wf(self.container_map, self.thread_map)) by {
                        reveal(container_thread_wf);
                        assert(forall|c_ptr:RwLockContainerPtr, t_ptr:RwLockThreadPtr|
                                #![trigger self.container_map.dom().contains(c_ptr), self.thread_map.dom().contains(t_ptr)]
                                self.container_map.dom().contains(c_ptr) && self.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().contains(t_ptr)
                                ==>
                                self.thread_map.dom().contains(t_ptr) && self.thread_map.spec_index(t_ptr).view().owning_container == c_ptr
                                &&
                                self.thread_map.spec_index(t_ptr).view().container_depth == self.container_map.spec_index(c_ptr).view_rodata().view().depth
                                &&
                                self.thread_map.spec_index(t_ptr).view().upper_container_seq == self.container_map.spec_index(c_ptr).view().uppertree_seq);
                        assert(forall|t_ptr:RwLockThreadPtr|
                                #![trigger self.thread_map.spec_index(t_ptr).view().owning_container]
                                self.thread_map.dom().contains(t_ptr)
                                ==>
                                self.container_map.dom().contains(self.thread_map.spec_index(t_ptr).view().owning_container)
                                &&
                                self.container_map.spec_index(self.thread_map.spec_index(t_ptr).view().owning_container).view_user_ghost().owned_threads.view().contains(t_ptr));
                        assert(forall|c_ptr:RwLockContainerPtr, t_ptr:RwLockThreadPtr|
                                #![trigger self.container_map.dom().contains(c_ptr), self.thread_map.dom().contains(t_ptr)]
                                self.container_map.dom().contains(c_ptr) && self.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().contains(t_ptr)
                                ==>
                                self.thread_map.dom().contains(t_ptr) );
                        assert(forall|t_ptr:RwLockThreadPtr, c_ptr:RwLockContainerPtr,|
                                #![trigger self.thread_map.spec_index(t_ptr).view().upper_container_seq.view().contains(c_ptr)]
                                self.thread_map.dom().contains(t_ptr) && self.thread_map.spec_index(t_ptr).view().upper_container_seq.view().contains(c_ptr)
                                ==>
                                self.container_map.dom().contains(c_ptr)
                                &&
                                self.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().contains(t_ptr));
                    };
                };
                // ---- inv() direct conjuncts ----
                assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
                    reveal(cpu_dirty_map_contains_container_processes);
                    reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                    reveal(cpu_dirty_map_proc_pcid_match);
                    reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                    reveal(container_cpu_wf);
                };
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
                assert(self.inv());
                // ---- locked_objects_match_lctx: container slot released, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(container_locked_match_lctx);
                    reveal(process_locked_match_lctx);
                    reveal(thread_locked_match_lctx);
                    reveal(endpoint_locked_match_lctx);
                    reveal(scheduler_locked_match_lctx);
                    reveal(pagetable_locked_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(cpu_locked_match_lctx);
                    reveal(allocator_locked_match_lctx);
                }
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
                old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
                wlock_requires(old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota, old(lctx)),
                old(lctx).lock_id_acyclic(old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.lock_id()),
                old(lctx).obj_id_fresh(KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k)),
                old(self).locked_objects_match_lctx(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Every held lock still matches lctx (quota now locked) ----
                final(self).locked_objects_match_lctx(final(lctx)),

                // ---- Field framing: only allocator_4k_map's quota lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).scheduler_map     == old(self).scheduler_map,
                final(self).process_map       == old(self).process_map,
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- allocator_4k_map: dom unchanged; only the targeted entry's quota lock state changed ----
                final(self).allocator_4k_map.dom() == old(self).allocator_4k_map.dom(),
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
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),

                // ---- The lock perm + lock ensures (forwarded from UnLockedMap::wlock_quota) ----
                wlock_ensures(
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
                    final(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.lock_id(),
                    final(lctx).thread_id(),
                    ret@,
                ),
                lock_ensures(
                    old(lctx),
                    final(lctx),
                    final(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.view(),
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.lock_id(),
                    KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k),
                ),
        {
            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
                reveal(process_perms_wf);
            }
            let ret = self.allocator_4k_map.wlock_quota(alloc_ptr_4k, Tracked(&mut *lctx), Ghost(PageSize::SZ4k));

            proof {
                assert forall|aptr: RwLockPageAllocatorPtr|
                    #![trigger self.allocator_4k_map.spec_index(aptr)]
                    self.allocator_4k_map.dom().contains(aptr)
                implies
                    self.allocator_4k_map.spec_index(aptr).global_pool == old(self).allocator_4k_map.spec_index(aptr).global_pool
                    && self.allocator_4k_map.spec_index(aptr).cpu_caches == old(self).allocator_4k_map.spec_index(aptr).cpu_caches
                    && self.allocator_4k_map.spec_index(aptr).quota.view() == old(self).allocator_4k_map.spec_index(aptr).quota.view()
                    && self.allocator_4k_map.spec_index(aptr).total_free_pages == old(self).allocator_4k_map.spec_index(aptr).total_free_pages
                by {
                    if aptr != alloc_ptr_4k {
                        assert(self.allocator_4k_map.spec_index(aptr) == old(self).allocator_4k_map.spec_index(aptr));
                    }
                };
                // ---- subsystems_inv ----
                assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
                assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
                assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
                assert(process_perms_wf(self.process_map)) by { reveal(process_perms_wf); reveal(process_temp_alloc_empty_unless_wlocked); };
                assert(thread_perms_wf(self.thread_map)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                // ---- memory_management_inv ----
                assert(self.memory_management_inv()) by {
                    assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf);
                    };
                    assert(container_page_owner_wf(self.container_map, self.page_array)) by {
                        reveal(container_page_owner_wf);
                    };
                    assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by {
                        reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
                    };
                    assert(container_pages_wf(self.page_array, self.container_map)) by {
                        reveal(container_pages_wf);
                    };
                    assert(process_pages_wf(self.page_array, self.process_map)) by {
                        reveal(process_pages_wf);
                    };
                    assert(container_process_allocator_quota_4k_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map)) by {
                        reveal(container_process_allocator_quota_4k_wf);
                        assert forall|c_ptr: RwLockContainerPtr|
                            #![trigger self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k]
                            self.container_map.dom().contains(c_ptr)
                        implies
                            self.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| {sum + process_effective_quota_4k(self.process_map.spec_index(p_ptr))})
                                + self.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_4k.view()})
                                + self.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_4k.view().spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                                + self.allocator_4k_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).quota.view().view()
                                == self.allocator_4k_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).total_free_pages.view()
                        by {
                            let aptr = self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k;
                            let depth = self.container_map.spec_index(c_ptr).view_rodata().view().depth as int;
                            lemma_process_effective_quota_4k_fold_eq(
                                self.container_map.spec_index(c_ptr).view().owned_processes.view(),
                                old(self).process_map, self.process_map);
                            lemma_thread_direct_pending_4k_fold_eq(
                                self.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view(),
                                old(self).thread_map, self.thread_map);
                            lemma_thread_indirect_pending_4k_fold_eq_at_depth(
                                self.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view(),
                                old(self).thread_map, self.thread_map, depth);
                            assert(self.allocator_4k_map.dom().contains(aptr)) by {
                                reveal(container_allocator_wf);
                            };
                            assert(old(self).container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| {sum + process_effective_quota_4k(old(self).process_map.spec_index(p_ptr))})
                                + old(self).container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + old(self).thread_map.spec_index(t_ptr).view().direct_free_quota_pending_4k.view()})
                                + old(self).container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + old(self).thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_4k.view().spec_index(old(self).container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                                + old(self).allocator_4k_map.spec_index(aptr).quota.view().view()
                                == old(self).allocator_4k_map.spec_index(aptr).total_free_pages.view()) by {
                                reveal(container_process_allocator_quota_4k_wf);
                            };
                        };
                    };
                    assert(container_process_allocator_quota_2m_wf(self.container_map, self.process_map, self.thread_map, self.allocator_2m_map));
                    assert(container_process_allocator_quota_1g_wf(self.container_map, self.process_map, self.thread_map, self.allocator_1g_map));
                    assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map));
                    assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(container_allocator_wf);
                    };
                    assert(allocator_free_page_ptrs_wf(self.allocator_4k_map)) by {
                        reveal(allocator_free_page_ptrs_wf);
                    };
                    assert(self.allocator_free_pages_wf());
                    assert(process_pagetable_match(self.process_map, self.pagetable_map)) by { reveal(process_pagetable_match); };
                    assert(hugepage_2m_wf(self.page_array));
                    assert(hugepage_1g_wf(self.page_array));
                    assert(page_pagetable_wf(self.pagetable_map, self.page_array));
                    assert(pagetable_pages_wf(self.pagetable_map, self.page_array));
                    assert(thread_pages_wf(self.thread_map, self.page_array));
                    assert(process_staged_pages_wf(self.process_map, self.page_array));
                    assert(endpoint_pages_wf(self.endpoint_map, self.page_array));
                    assert(container_allocator_free_4k_page_wf(self.container_map, self.allocator_4k_map, self.page_array)) by {
                        reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                    };
                    assert(container_allocator_free_2m_page_wf(self.container_map, self.allocator_2m_map, self.page_array)) by {
                        reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                    };
                    assert(container_allocator_free_1g_page_wf(self.container_map, self.allocator_1g_map, self.page_array)) by {
                        reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                    };
                };
                // ---- process_management_inv: container_map, process_map, etc. all byte-equal ----
                assert(self.process_management_inv()) by {
                    assert(container_tree_wf(self.root_container, self.container_map));
                    assert(container_process_wf(self.container_map, self.process_map)) by { reveal(container_process_wf); };
                    assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                        reveal(container_process_wf); reveal(per_container_process_tree_wf);
                    };
                    assert(container_endpoint_wf(self.container_map, self.endpoint_map)) by { reveal(container_endpoint_wf); };
                    assert(container_cpu_wf(self.container_map, self.cpu_array)) by { reveal(container_cpu_wf); };
                    assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
                        reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
                        reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf);
                    };
                    assert(container_scheduler_wf(self.container_map, self.scheduler_map)) by { reveal(container_scheduler_wf); };
                    assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
                        reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
                    };
                    assert(container_thread_wf(self.container_map, self.thread_map)) by { reveal(container_thread_wf); };
                    assert(process_cpu_wf(self.process_map, self.cpu_array)) by { reveal(process_cpu_wf); };
                    assert(process_thread_wf(self.process_map, self.thread_map)) by { reveal(process_thread_wf); };
                };
                // ---- inv() direct conjuncts ----
                assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
                    reveal(cpu_dirty_map_contains_container_processes);
                    reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                    reveal(cpu_dirty_map_proc_pcid_match);
                    reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                    reveal(container_cpu_wf);
                };
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
                assert(self.inv());
                // ---- locked_objects_match_lctx: quota slot gained, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(container_locked_match_lctx);
                    reveal(process_locked_match_lctx);
                    reveal(thread_locked_match_lctx);
                    reveal(endpoint_locked_match_lctx);
                    reveal(scheduler_locked_match_lctx);
                    reveal(pagetable_locked_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(cpu_locked_match_lctx);
                    reveal(allocator_locked_match_lctx);
                }
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
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.wlocked_by(old(lctx)),
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.inv(),
                unlock_requires::<crate::allocator::allocator_quota::AllocatorQuota>(old(lctx)),
                lock_perm@.state() is WriteLock,
                lock_perm@.thread_id() == old(lctx).thread_id(),
                lock_perm@.lock_id() == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.locking_thread()->Write_lock_id,
                old(lctx).allocator_4k_lock_map().dom().contains(AllocatorLockObjId::Quota(alloc_ptr_4k)),
                old(lctx).allocator_4k_lock_map()[AllocatorLockObjId::Quota(alloc_ptr_4k)] == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.lock_id(),
                old(self).locked_objects_match_lctx(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Every held lock still matches lctx (quota now released) ----
                final(self).locked_objects_match_lctx(final(lctx)),

                // ---- Field framing: only allocator_4k_map's quota lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).scheduler_map     == old(self).scheduler_map,
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

                // ---- LocalContext: lock dropped; thread + user-view phase preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` transitions it Acquire -> Release, so restating
                // `== old` would contradict it and make the postcondition `false`
                // in an Acquire section. `unlock_ensures` is the source of truth
                // for the phase transition (same trap as the NOTE on
                // `LockedArray::wunlock`). user_view is separately preserved.
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),

                // ---- wunlock ensures (forwarded from UnLockedMap::wunlock_quota) ----
                wunlock_ensures(
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
                    final(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
                ),
                unlock_ensures(
                    old(lctx),
                    final(lctx),
                    final(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.view(),
                    lock_perm@.lock_id(),
                    KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k),
                ),
        {
            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
                reveal(process_perms_wf);
            }
            self.allocator_4k_map.wunlock_quota(alloc_ptr_4k, Tracked(&mut *lctx), lock_perm, Ghost(PageSize::SZ4k));

            proof {
                // ---- subsystems_inv ----
                assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
                assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
                assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
                assert(process_perms_wf(self.process_map)) by { reveal(process_perms_wf); reveal(process_temp_alloc_empty_unless_wlocked); };
                assert(thread_perms_wf(self.thread_map)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                // ---- memory_management_inv ----
                assert(self.memory_management_inv()) by {
                    assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf);
                    };
                    assert(container_page_owner_wf(self.container_map, self.page_array)) by {
                        reveal(container_page_owner_wf);
                    };
                    assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by {
                        reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
                    };
                    assert(container_pages_wf(self.page_array, self.container_map)) by {
                        reveal(container_pages_wf);
                    };
                    assert(process_pages_wf(self.page_array, self.process_map)) by {
                        reveal(process_pages_wf);
                    };
                    assert(container_process_allocator_quota_4k_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map)) by {
                        reveal(container_process_allocator_quota_4k_wf);
                        assert forall|c_ptr: RwLockContainerPtr|
                            #![trigger self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k]
                            self.container_map.dom().contains(c_ptr)
                        implies
                            self.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| {sum + process_effective_quota_4k(self.process_map.spec_index(p_ptr))})
                                + self.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_4k.view()})
                                + self.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_4k.view().spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                                + self.allocator_4k_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).quota.view().view()
                                == self.allocator_4k_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).total_free_pages.view()
                        by {
                            let aptr = self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k;
                            let depth = self.container_map.spec_index(c_ptr).view_rodata().view().depth as int;
                            lemma_process_effective_quota_4k_fold_eq(
                                self.container_map.spec_index(c_ptr).view().owned_processes.view(),
                                old(self).process_map, self.process_map);
                            lemma_thread_direct_pending_4k_fold_eq(
                                self.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view(),
                                old(self).thread_map, self.thread_map);
                            lemma_thread_indirect_pending_4k_fold_eq_at_depth(
                                self.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view(),
                                old(self).thread_map, self.thread_map, depth);
                            assert(self.allocator_4k_map.dom().contains(aptr)) by {
                                reveal(container_allocator_wf);
                            };
                            assert(old(self).container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| {sum + process_effective_quota_4k(old(self).process_map.spec_index(p_ptr))})
                                + old(self).container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + old(self).thread_map.spec_index(t_ptr).view().direct_free_quota_pending_4k.view()})
                                + old(self).container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + old(self).thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_4k.view().spec_index(old(self).container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                                + old(self).allocator_4k_map.spec_index(aptr).quota.view().view()
                                == old(self).allocator_4k_map.spec_index(aptr).total_free_pages.view()) by {
                                reveal(container_process_allocator_quota_4k_wf);
                            };
                        };
                    };
                    assert(container_process_allocator_quota_2m_wf(self.container_map, self.process_map, self.thread_map, self.allocator_2m_map));
                    assert(container_process_allocator_quota_1g_wf(self.container_map, self.process_map, self.thread_map, self.allocator_1g_map));
                    assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map));
                    assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(container_allocator_wf);
                    };
                    assert(allocator_free_page_ptrs_wf(self.allocator_4k_map)) by {
                        reveal(allocator_free_page_ptrs_wf);
                    };
                    assert(self.allocator_free_pages_wf());
                    assert(process_pagetable_match(self.process_map, self.pagetable_map)) by { reveal(process_pagetable_match); };
                    assert(hugepage_2m_wf(self.page_array));
                    assert(hugepage_1g_wf(self.page_array));
                    assert(page_pagetable_wf(self.pagetable_map, self.page_array));
                    assert(pagetable_pages_wf(self.pagetable_map, self.page_array));
                    assert(thread_pages_wf(self.thread_map, self.page_array));
                    assert(process_staged_pages_wf(self.process_map, self.page_array));
                    assert(endpoint_pages_wf(self.endpoint_map, self.page_array));
                    assert(container_allocator_free_4k_page_wf(self.container_map, self.allocator_4k_map, self.page_array)) by {
                        reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                    };
                    assert(container_allocator_free_2m_page_wf(self.container_map, self.allocator_2m_map, self.page_array)) by {
                        reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                    };
                    assert(container_allocator_free_1g_page_wf(self.container_map, self.allocator_1g_map, self.page_array)) by {
                        reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                    };
                };
                // ---- process_management_inv: container_map, process_map, etc. all byte-equal ----
                assert(self.process_management_inv()) by {
                    assert(container_tree_wf(self.root_container, self.container_map));
                    assert(container_process_wf(self.container_map, self.process_map)) by { reveal(container_process_wf); };
                    assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                        reveal(container_process_wf); reveal(per_container_process_tree_wf);
                    };
                    assert(container_endpoint_wf(self.container_map, self.endpoint_map)) by { reveal(container_endpoint_wf); };
                    assert(container_cpu_wf(self.container_map, self.cpu_array)) by { reveal(container_cpu_wf); };
                    assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
                        reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
                        reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf);
                    };
                    assert(container_scheduler_wf(self.container_map, self.scheduler_map)) by { reveal(container_scheduler_wf); };
                    assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
                        reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
                    };
                    assert(container_thread_wf(self.container_map, self.thread_map)) by { reveal(container_thread_wf); };
                    assert(process_cpu_wf(self.process_map, self.cpu_array)) by { reveal(process_cpu_wf); };
                    assert(process_thread_wf(self.process_map, self.thread_map)) by { reveal(process_thread_wf); };
                };
                // ---- inv() direct conjuncts ----
                assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
                    reveal(cpu_dirty_map_contains_container_processes);
                    reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                    reveal(cpu_dirty_map_proc_pcid_match);
                    reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                    reveal(container_cpu_wf);
                };
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
                assert(self.inv());
                // ---- locked_objects_match_lctx: quota slot released, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(container_locked_match_lctx);
                    reveal(process_locked_match_lctx);
                    reveal(thread_locked_match_lctx);
                    reveal(endpoint_locked_match_lctx);
                    reveal(scheduler_locked_match_lctx);
                    reveal(pagetable_locked_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(cpu_locked_match_lctx);
                    reveal(allocator_locked_match_lctx);
                }
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
        /// Success path additionally proves the just-locked process has a clean
        /// temp-alloc cache: a successful wlock proves the lock was previously
        /// free (`wlock_ensures` gives `old.locked() == false`), and the entry
        /// invariant `process_temp_alloc_empty_unless_wlocked` then forces
        /// cleanliness; `wlock_ensures` preserves the payload, so it carries to
        /// the post-lock view. Callers need this to discharge `wunlock_process`'s
        /// temp-alloc precondition for syscalls that never stage pages.
        #[verifier::spinoff_prover]
        pub fn wlock_process_unless_killed(
            &mut self,
            process_ptr: RwLockProcessPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: (bool, Option<Tracked<LockPerm>>))
            requires
                old(self).inv(),
                old(self).process_map.dom().contains(process_ptr),
                old(self).process_map.spec_index(process_ptr).locked_by(old(lctx)) == false,
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).user_view_locking_state() is Acquire,
                old(lctx).lock_id_acyclic(old(self).process_map.lock_id_by_key(process_ptr)),
                old(lctx).obj_id_fresh(KernelObjId::Process(process_ptr)),
                old(self).locked_objects_match_lctx(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Every held lock still matches lctx (success: process locked; failure: no-op) ----
                final(self).locked_objects_match_lctx(final(lctx)),

                // ---- Field framing: only process_map's lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).scheduler_map     == old(self).scheduler_map,
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
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),

                // ---- Failure: process is being killed; complete no-op ----
                ret.0 == false ==>
                {
                    &&& old(self).process_map.spec_index(process_ptr).being_killed() == true
                    &&& final(self).process_map.spec_index(process_ptr) == old(self).process_map.spec_index(process_ptr)
                    &&& ret.1 is None
                    &&& final(lctx).lock_maps_equal(old(lctx))
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
                        ret.1.unwrap()@,
                    )
                    &&& lock_ensures(
                        old(lctx),
                        final(lctx),
                        old(self).process_map.spec_index(process_ptr).view(),
                        old(self).process_map.lock_id_by_key(process_ptr),
                        KernelObjId::Process(process_ptr),
                    )
                    // The just-locked process has a clean temp-alloc cache (the
                    // "flushed before wunlock" protocol — see `wunlock_process`).
                    &&& final(self).process_map.spec_index(process_ptr).view().temp_alloc_clean()
                },
        {
            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
                reveal(process_perms_wf);
            }
            let res = self.process_map.wlock_unless_killed(
                process_ptr,
                Tracked(&mut *lctx),
                Ghost(KernelObjId::Process(process_ptr)),
            );

            proof {
                // ---- subsystems_inv ----
                assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
                assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
                assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
                assert(process_perms_wf(self.process_map)) by {
                    reveal(process_perms_wf);
                    reveal(process_temp_alloc_empty_unless_wlocked);
                };
                assert(thread_perms_wf(self.thread_map)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                // ---- memory_management_inv ----
                assert(self.memory_management_inv()) by {
                    assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf);
                    };
                    assert(container_page_owner_wf(self.container_map, self.page_array)) by {
                        reveal(container_page_owner_wf);
                    };
                    assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by {
                        reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
                        reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
                    };
                    assert(container_pages_wf(self.page_array, self.container_map)) by {
                        reveal(container_pages_wf);
                    };
                    assert(process_pages_wf(self.page_array, self.process_map)) by {
                        reveal(process_pages_wf);
                    };
                    assert(container_process_allocator_quota_4k_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map)) by {
                        reveal(container_process_allocator_quota_4k_wf);
                        assert forall|c_ptr: RwLockContainerPtr|
                            #![trigger self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k]
                            self.container_map.dom().contains(c_ptr)
                        implies
                            self.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| {sum + process_effective_quota_4k(self.process_map.spec_index(p_ptr))})
                                + self.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_4k.view()})
                                + self.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_4k.view().spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                                + self.allocator_4k_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).quota.view().view()
                                == self.allocator_4k_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).total_free_pages.view()
                        by {
                            assert(self.container_map.spec_index(c_ptr).view().owned_processes.view().subset_of(self.process_map.dom())) by {
                                reveal(container_process_wf);
                            };
                            lemma_process_effective_quota_4k_fold_eq(
                                self.container_map.spec_index(c_ptr).view().owned_processes.view(),
                                old(self).process_map, self.process_map);
                        };
                    };
                    assert(container_process_allocator_quota_2m_wf(self.container_map, self.process_map, self.thread_map, self.allocator_2m_map)) by {
                        reveal(container_process_allocator_quota_2m_wf);
                        assert forall|c_ptr: RwLockContainerPtr|
                            #![trigger self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m]
                            self.container_map.dom().contains(c_ptr)
                        implies
                            self.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| {sum + process_effective_quota_2m(self.process_map.spec_index(p_ptr))})
                                + self.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_2m.view()})
                                + self.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_2m.view().spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                                + self.allocator_2m_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).quota.view().view()
                                == self.allocator_2m_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).total_free_pages.view()
                        by {
                            assert(self.container_map.spec_index(c_ptr).view().owned_processes.view().subset_of(self.process_map.dom())) by {
                                reveal(container_process_wf);
                            };
                            lemma_process_effective_quota_2m_fold_eq(
                                self.container_map.spec_index(c_ptr).view().owned_processes.view(),
                                old(self).process_map, self.process_map);
                        };
                    };
                    assert(container_process_allocator_quota_1g_wf(self.container_map, self.process_map, self.thread_map, self.allocator_1g_map)) by {
                        reveal(container_process_allocator_quota_1g_wf);
                        assert forall|c_ptr: RwLockContainerPtr|
                            #![trigger self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g]
                            self.container_map.dom().contains(c_ptr)
                        implies
                            self.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| {sum + process_effective_quota_1g(self.process_map.spec_index(p_ptr))})
                                + self.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_1g.view()})
                                + self.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_1g.view().spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                                + self.allocator_1g_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).quota.view().view()
                                == self.allocator_1g_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).total_free_pages.view()
                        by {
                            assert(self.container_map.spec_index(c_ptr).view().owned_processes.view().subset_of(self.process_map.dom())) by {
                                reveal(container_process_wf);
                            };
                            lemma_process_effective_quota_1g_fold_eq(
                                self.container_map.spec_index(c_ptr).view().owned_processes.view(),
                                old(self).process_map, self.process_map);

                        };
                    };
                    assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map));
                    assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(container_allocator_wf);
                    };
                    assert(self.allocator_free_pages_wf());
                    assert(process_pagetable_match(self.process_map, self.pagetable_map)) by {
                        reveal(process_pagetable_match);
                    };
                    // process_staged_pages_wf reads per-process temp-alloc caches
                    // (process view()) + page_array; both preserved here, so lift it
                    // via the view-equality preservation lemma.
                    assert(process_staged_pages_wf(self.process_map, self.page_array)) by {
                        reveal(process_staged_pages_4k_wf);
                        reveal(process_staged_pages_2m_wf);
                        reveal(process_staged_pages_1g_wf);
                    };
                    assert(hugepage_2m_wf(self.page_array));
                    assert(hugepage_1g_wf(self.page_array));
                    assert(page_pagetable_wf(self.pagetable_map, self.page_array));
                    assert(pagetable_pages_wf(self.pagetable_map, self.page_array));
                    assert(thread_pages_wf(self.thread_map, self.page_array));
                    assert(endpoint_pages_wf(self.endpoint_map, self.page_array));
                    assert(container_allocator_free_4k_page_wf(self.container_map, self.allocator_4k_map, self.page_array)) by {
                        reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                    };
                    assert(container_allocator_free_2m_page_wf(self.container_map, self.allocator_2m_map, self.page_array)) by {
                        reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                    };
                    assert(container_allocator_free_1g_page_wf(self.container_map, self.allocator_1g_map, self.page_array)) by {
                        reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                    };
                };
                // ---- process_management_inv ----
                assert(self.process_management_inv()) by {
                    assert(container_tree_wf(self.root_container, self.container_map));
                    assert(container_process_wf(self.container_map, self.process_map)) by {
                        reveal(container_process_wf);
                    };
                    // per_container_process_tree_wf: process_map's tree-fields
                    // (view/view_rodata) are preserved per process, so each
                    // container's process tree carries over via the lemma.
                    assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                        reveal(container_process_wf); reveal(per_container_process_tree_wf);
                        assert(per_container_process_tree_wf(old(self).container_map, old(self).process_map));
                        assert forall|c_ptr: RwLockContainerPtr| #![auto]
                            self.container_map.dom().contains(c_ptr)
                        implies
                            process_tree_wf(
                                self.container_map.spec_index(c_ptr).view().root_process,
                                self.container_map.spec_index(c_ptr).view().owned_processes@,
                                self.process_map,
                            )
                        by {
                            process_no_change_to_tree_fields_imply_wf(
                                self.container_map.spec_index(c_ptr).view().root_process,
                                self.container_map.spec_index(c_ptr).view().owned_processes@,
                                old(self).process_map, self.process_map,
                            );
                        };
                    };
                    assert(container_endpoint_wf(self.container_map, self.endpoint_map)) by {
                        reveal(container_endpoint_wf);
                    };
                    assert(container_cpu_wf(self.container_map, self.cpu_array)) by {
                        reveal(container_cpu_wf);
                    };
                    assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
                        reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
                        reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf);
                    };
                    assert(container_scheduler_wf(self.container_map, self.scheduler_map)) by {
                        reveal(container_scheduler_wf);
                    };
                    assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
                        reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
                    };
                    assert(container_thread_wf(self.container_map, self.thread_map)) by {
                        reveal(container_thread_wf);
                    };
                    assert(process_cpu_wf(self.process_map, self.cpu_array)) by {
                        reveal(process_cpu_wf);
                    };
                    assert(process_thread_wf(self.process_map, self.thread_map)) by {
                        reveal(process_thread_wf);
                    };
                };
                // ---- inv() direct conjuncts ----
                assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
                    reveal(cpu_dirty_map_contains_container_processes);
                    reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                    reveal(cpu_dirty_map_proc_pcid_match);
                    reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                    reveal(container_cpu_wf);
                };
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
                assert(self.inv());
                // ---- locked_objects_match_lctx: success locks process, failure is a no-op ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(container_locked_match_lctx);
                    reveal(process_locked_match_lctx);
                    reveal(thread_locked_match_lctx);
                    reveal(endpoint_locked_match_lctx);
                    reveal(scheduler_locked_match_lctx);
                    reveal(pagetable_locked_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(cpu_locked_match_lctx);
                    reveal(allocator_locked_match_lctx);
                }
            }
            // Success-only ensures: the just-locked process has a clean
            // temp-alloc cache. From `old(self).inv()` the entry-pre invariant
            // `process_temp_alloc_empty_unless_wlocked` holds; the pre-lock
            // process was NOT write-locked (a successful wlock requires
            // `old.locked() == false`), so the clause forces `temp_alloc_clean`
            // pre-lock; `wlock_ensures` preserves the payload, so it carries to
            // the post-lock view.
            proof {
                if res.0 == true {
                    reveal(process_perms_wf);
                    reveal(process_temp_alloc_empty_unless_wlocked);
                    assert(old(self).process_map.spec_index(process_ptr).locking_thread() is Write == false);
                    assert(old(self).process_map.spec_index(process_ptr).view().temp_alloc_clean());
                }
            }
            res
        }

        /// Companion of `wlock_process_unless_killed` for the unlock side.
        /// Wraps `LockedMap::wunlock` for `process_map` and re-establishes
        /// `inv()` immediately afterwards. Unlocking has no killed-branch — the
        /// caller already holds the write lock, so this is unconditional.
        ///
        /// The "flushed before wunlock" protocol: the caller must have drained
        /// the process's temp-alloc cache before releasing the write lock,
        /// because once unlocked the global invariant
        /// `process_temp_alloc_empty_unless_wlocked` demands the cache be clean.
        /// The process write-lock is the only thing that licenses a non-empty
        /// cache, and dropping it requires emptiness — enforced via the
        /// `temp_alloc_clean` precondition. Syscalls that never stage pages get
        /// this for free from `wlock_process_unless_killed`'s success ensures.
        #[verifier::spinoff_prover]
        pub fn wunlock_process(
            &mut self,
            process_ptr: RwLockProcessPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                old(self).process_map.spec_index(process_ptr).being_killed() == false,
                unlock_requires::<Process>(old(lctx)),
                lock_perm@.state() is WriteLock,
                lock_perm@.thread_id() == old(lctx).thread_id(),
                old(lctx).process_lock_map().dom().contains(process_ptr),
                old(lctx).process_lock_map()[process_ptr] == old(self).process_map.lock_id_by_key(process_ptr),
                lock_perm@.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
                // The "flushed before wunlock" protocol: the cache must be empty
                // before releasing the write lock (see doc comment above).
                old(self).process_map.spec_index(process_ptr).view().temp_alloc_clean(),
                old(self).locked_objects_match_lctx(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Every held lock still matches lctx (process now released) ----
                final(self).locked_objects_match_lctx(final(lctx)),

                // ---- Field framing: only process_map's lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).scheduler_map     == old(self).scheduler_map,
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

                // ---- LocalContext: lock dropped; thread + user-view phase preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` transitions it Acquire -> Release, so restating
                // `== old` would contradict it and make the postcondition `false`
                // in an Acquire section. `unlock_ensures` is the source of truth
                // for the phase transition (same trap as the NOTE on
                // `LockedArray::wunlock`). user_view is separately preserved.
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),

                // ---- wunlock ensures (forwarded from LockedMap::wunlock) ----
                unlock_ensures(
                    old(lctx),
                    final(lctx),
                    final(self).process_map.spec_index(process_ptr).view(),
                    lock_perm@.lock_id(),
                    KernelObjId::Process(process_ptr),
                ),
                final(lctx).lock_maps_removed(old(lctx), KernelObjId::Process(process_ptr)),
        {
            proof {
                reveal(KernelK::locked_objects_match_lctx);
                reveal(process_locked_match_lctx);
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
                reveal(process_perms_wf);
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
                // ---- subsystems_inv ----
                assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
                assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
                assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
                assert(process_perms_wf(self.process_map)) by {
                    reveal(process_perms_wf);
                    reveal(process_temp_alloc_empty_unless_wlocked);
                };
                assert(thread_perms_wf(self.thread_map)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                // ---- memory_management_inv ----
                assert(self.memory_management_inv()) by {
                    assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf);
                    };
                    assert(container_page_owner_wf(self.container_map, self.page_array)) by {
                        reveal(container_page_owner_wf);
                    };
                    assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by {
                        reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
                        reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
                    };
                    assert(container_pages_wf(self.page_array, self.container_map)) by {
                        reveal(container_pages_wf);
                    };
                    assert(process_pages_wf(self.page_array, self.process_map)) by {
                        reveal(process_pages_wf);
                    };
                    assert(container_process_allocator_quota_4k_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map)) by {
                        reveal(container_process_allocator_quota_4k_wf);
                        assert forall|c_ptr: RwLockContainerPtr|
                            #![trigger self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k]
                            self.container_map.dom().contains(c_ptr)
                        implies
                            self.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| {sum + process_effective_quota_4k(self.process_map.spec_index(p_ptr))})
                                + self.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_4k.view()})
                                + self.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_4k.view().spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                                + self.allocator_4k_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).quota.view().view()
                                == self.allocator_4k_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).total_free_pages.view()
                        by {
                            assert(self.container_map.spec_index(c_ptr).view().owned_processes.view().subset_of(self.process_map.dom())) by {
                                reveal(container_process_wf);
                            };
                            lemma_process_effective_quota_4k_fold_eq(
                                self.container_map.spec_index(c_ptr).view().owned_processes.view(),
                                old(self).process_map, self.process_map);
                        };
                    };
                    assert(container_process_allocator_quota_2m_wf(self.container_map, self.process_map, self.thread_map, self.allocator_2m_map)) by {
                        reveal(container_process_allocator_quota_2m_wf);
                        assert forall|c_ptr: RwLockContainerPtr|
                            #![trigger self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m]
                            self.container_map.dom().contains(c_ptr)
                        implies
                            self.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| {sum + process_effective_quota_2m(self.process_map.spec_index(p_ptr))})
                                + self.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_2m.view()})
                                + self.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_2m.view().spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                                + self.allocator_2m_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).quota.view().view()
                                == self.allocator_2m_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).total_free_pages.view()
                        by {
                            assert(self.container_map.spec_index(c_ptr).view().owned_processes.view().subset_of(self.process_map.dom())) by {
                                reveal(container_process_wf);
                            };
                            lemma_process_effective_quota_2m_fold_eq(
                                self.container_map.spec_index(c_ptr).view().owned_processes.view(),
                                old(self).process_map, self.process_map);
                        };
                    };
                    assert(container_process_allocator_quota_1g_wf(self.container_map, self.process_map, self.thread_map, self.allocator_1g_map)) by {
                        reveal(container_process_allocator_quota_1g_wf);
                        assert forall|c_ptr: RwLockContainerPtr|
                            #![trigger self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g]
                            self.container_map.dom().contains(c_ptr)
                        implies
                            self.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| {sum + process_effective_quota_1g(self.process_map.spec_index(p_ptr))})
                                + self.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_1g.view()})
                                + self.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_1g.view().spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                                + self.allocator_1g_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).quota.view().view()
                                == self.allocator_1g_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).total_free_pages.view()
                        by {
                            assert(self.container_map.spec_index(c_ptr).view().owned_processes.view().subset_of(self.process_map.dom())) by {
                                reveal(container_process_wf);
                            };
                            lemma_process_effective_quota_1g_fold_eq(
                                self.container_map.spec_index(c_ptr).view().owned_processes.view(),
                                old(self).process_map, self.process_map);
                        };
                    };
                    assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map));
                    assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(container_allocator_wf);
                    };
                    assert(self.allocator_free_pages_wf());
                    assert(process_pagetable_match(self.process_map, self.pagetable_map)) by {
                        reveal(process_pagetable_match);
                    };
                    assert(process_staged_pages_wf(self.process_map, self.page_array)) by {
                        reveal(process_staged_pages_4k_wf);
                        reveal(process_staged_pages_2m_wf);
                        reveal(process_staged_pages_1g_wf);
                    };
                    assert(hugepage_2m_wf(self.page_array));
                    assert(hugepage_1g_wf(self.page_array));
                    assert(page_pagetable_wf(self.pagetable_map, self.page_array));
                    assert(pagetable_pages_wf(self.pagetable_map, self.page_array));
                    assert(thread_pages_wf(self.thread_map, self.page_array));
                    assert(endpoint_pages_wf(self.endpoint_map, self.page_array));
                    assert(container_allocator_free_4k_page_wf(self.container_map, self.allocator_4k_map, self.page_array)) by {
                        reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                    };
                    assert(container_allocator_free_2m_page_wf(self.container_map, self.allocator_2m_map, self.page_array)) by {
                        reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                    };
                    assert(container_allocator_free_1g_page_wf(self.container_map, self.allocator_1g_map, self.page_array)) by {
                        reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                    };
                };
                // ---- process_management_inv ----
                assert(self.process_management_inv()) by {
                    assert(container_tree_wf(self.root_container, self.container_map));
                    assert(container_process_wf(self.container_map, self.process_map)) by {
                        reveal(container_process_wf);
                    };
                    // per_container_process_tree_wf: process_map's tree-fields
                    // (view/view_rodata) are preserved per process, so each
                    // container's process tree carries over via the lemma.
                    assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                        reveal(container_process_wf); reveal(per_container_process_tree_wf);
                        assert(per_container_process_tree_wf(old(self).container_map, old(self).process_map));
                        assert forall|c_ptr: RwLockContainerPtr| #![auto]
                            self.container_map.dom().contains(c_ptr)
                        implies
                            process_tree_wf(
                                self.container_map.spec_index(c_ptr).view().root_process,
                                self.container_map.spec_index(c_ptr).view().owned_processes@,
                                self.process_map,
                            )
                        by {
                            process_no_change_to_tree_fields_imply_wf(
                                self.container_map.spec_index(c_ptr).view().root_process,
                                self.container_map.spec_index(c_ptr).view().owned_processes@,
                                old(self).process_map, self.process_map,
                            );
                        };
                    };
                    assert(container_endpoint_wf(self.container_map, self.endpoint_map)) by {
                        reveal(container_endpoint_wf);
                    };
                    assert(container_cpu_wf(self.container_map, self.cpu_array)) by {
                        reveal(container_cpu_wf);
                    };
                    assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
                        reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
                        reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf);
                    };
                    assert(container_scheduler_wf(self.container_map, self.scheduler_map)) by {
                        reveal(container_scheduler_wf);
                    };
                    assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
                        reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
                    };
                    assert(container_thread_wf(self.container_map, self.thread_map)) by {
                        reveal(container_thread_wf);
                    };
                    assert(process_cpu_wf(self.process_map, self.cpu_array)) by {
                        reveal(process_cpu_wf);
                    };
                    assert(process_thread_wf(self.process_map, self.thread_map)) by {
                        reveal(process_thread_wf);
                    };
                };
                // ---- inv() direct conjuncts ----
                assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
                    reveal(cpu_dirty_map_contains_container_processes);
                    reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                    reveal(cpu_dirty_map_proc_pcid_match);
                    reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                    reveal(container_cpu_wf);
                };
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
                assert(self.inv());
                // ---- locked_objects_match_lctx: process slot released, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(container_locked_match_lctx);
                    reveal(process_locked_match_lctx);
                    reveal(thread_locked_match_lctx);
                    reveal(endpoint_locked_match_lctx);
                    reveal(scheduler_locked_match_lctx);
                    reveal(pagetable_locked_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(cpu_locked_match_lctx);
                    reveal(allocator_locked_match_lctx);
                }
            }
        }

        /// Companion of the thread-creation write-lock for the unlock side. Wraps
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
                old(self).thread_map.spec_index(thread_ptr).being_killed() == false,
                unlock_requires::<Thread>(old(lctx)),
                lock_perm@.state() is WriteLock,
                lock_perm@.thread_id() == old(lctx).thread_id(),
                old(lctx).thread_lock_map().dom().contains(thread_ptr),
                old(lctx).thread_lock_map()[thread_ptr] == old(self).thread_map.lock_id_by_key(thread_ptr),
                lock_perm@.lock_id() == old(self).thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id,
                // The pending-clean protocol: pendings must be flushed before
                // releasing the write lock (see doc comment above).
                old(self).thread_map.spec_index(thread_ptr).view().free_quota_pending_clean(),
                old(self).locked_objects_match_lctx(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Every held lock still matches lctx (thread now released) ----
                final(self).locked_objects_match_lctx(final(lctx)),

                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).scheduler_map     == old(self).scheduler_map,
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

                // ---- LocalContext: lock dropped; thread + user-view phase preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` transitions it Acquire -> Release (same trap as
                // the NOTE on wunlock_process / LockedArray::wunlock).
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),

                // ---- wunlock ensures (forwarded from LockedMap::wunlock) ----
                unlock_ensures(
                    old(lctx),
                    final(lctx),
                    final(self).thread_map.spec_index(thread_ptr).view(),
                    lock_perm@.lock_id(),
                    KernelObjId::Thread(thread_ptr),
                ),
                final(lctx).lock_maps_removed(old(lctx), KernelObjId::Thread(thread_ptr)),
        {
            proof {
                reveal(KernelK::locked_objects_match_lctx);
                reveal(thread_locked_match_lctx);
                reveal(scheduler_locked_match_lctx);
                reveal(process_locked_match_lctx);
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
                reveal(thread_perms_wf);
                reveal(scheduler_perms_wf);
                reveal(process_perms_wf);
            }
            self.thread_map.wunlock(
                thread_ptr,
                Tracked(&mut *lctx),
                lock_perm,
                Ghost(KernelObjId::Thread(thread_ptr)),
            );
            // Only thread_ptr's lock state moved; every thread's payload view is
            // byte-equal pre/post (other entries via unchanged_except, thread_ptr
            // via wunlock_ensures' `new@ == old@`) — the frame every thread-coupled
            // conjunct + conservation fold reads.
            assert forall|t: RwLockThreadPtr| #![auto]
                self.thread_map.dom().contains(t)
                implies self.thread_map.spec_index(t).view() == old(self).thread_map.spec_index(t).view() by {
                if t != thread_ptr {
                    assert(self.thread_map.spec_index(t) == old(self).thread_map.spec_index(t));
                }
            };
            proof {
                // ---- subsystems_inv ----
                assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
                assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
                assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
                assert(process_perms_wf(self.process_map)) by { reveal(process_perms_wf); reveal(process_temp_alloc_empty_unless_wlocked); };
                assert(thread_perms_wf(self.thread_map)) by {
                    reveal(thread_perms_wf);
                    reveal(threads_inv);
                    reveal(thread_free_quota_pending_empty_unless_wlocked);
                };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(scheduler_perms_wf); };
                // ---- memory_management_inv ----
                assert(self.memory_management_inv()) by {
                    assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf);
                    };
                    assert(container_page_owner_wf(self.container_map, self.page_array)) by { reveal(container_page_owner_wf); };
                    assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by {
                        reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
                        reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
                    };
                    assert(container_pages_wf(self.page_array, self.container_map)) by { reveal(container_pages_wf); };
                    assert(process_pages_wf(self.page_array, self.process_map)) by { reveal(process_pages_wf); };
                    assert(container_process_allocator_quota_4k_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map)) by {
                        reveal(container_process_allocator_quota_4k_wf);
                        assert forall|c_ptr: RwLockContainerPtr|
                            #![trigger self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k]
                            self.container_map.dom().contains(c_ptr)
                        implies
                            self.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| {sum + process_effective_quota_4k(self.process_map.spec_index(p_ptr))})
                                + self.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_4k.view()})
                                + self.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_4k.view().spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                                + self.allocator_4k_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).quota.view().view()
                                == self.allocator_4k_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).total_free_pages.view()
                        by {
                            assert(self.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().subset_of(self.thread_map.dom())) by {
                                reveal(container_thread_wf);
                            };
                            assert(self.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().subset_of(self.thread_map.dom())) by {
                                reveal(container_thread_wf);
                            };
                            lemma_thread_direct_pending_4k_fold_eq(
                                self.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view(),
                                old(self).thread_map, self.thread_map);
                            lemma_thread_indirect_pending_4k_fold_eq_at_depth(
                                self.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view(),
                                old(self).thread_map, self.thread_map, self.container_map.spec_index(c_ptr).view_rodata().view().depth as int);
                        };
                    };
                    assert(container_process_allocator_quota_2m_wf(self.container_map, self.process_map, self.thread_map, self.allocator_2m_map)) by {
                        reveal(container_process_allocator_quota_2m_wf);
                        assert forall|c_ptr: RwLockContainerPtr|
                            #![trigger self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m]
                            self.container_map.dom().contains(c_ptr)
                        implies
                            self.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| {sum + process_effective_quota_2m(self.process_map.spec_index(p_ptr))})
                                + self.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_2m.view()})
                                + self.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_2m.view().spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                                + self.allocator_2m_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).quota.view().view()
                                == self.allocator_2m_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_2m).total_free_pages.view()
                        by {
                            assert(self.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().subset_of(self.thread_map.dom())) by {
                                reveal(container_thread_wf);
                            };
                            assert(self.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().subset_of(self.thread_map.dom())) by {
                                reveal(container_thread_wf);
                            };
                            lemma_thread_direct_pending_2m_fold_eq(
                                self.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view(),
                                old(self).thread_map, self.thread_map);
                            lemma_thread_indirect_pending_2m_fold_eq_at_depth(
                                self.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view(),
                                old(self).thread_map, self.thread_map, self.container_map.spec_index(c_ptr).view_rodata().view().depth as int);
                        };
                    };
                    assert(container_process_allocator_quota_1g_wf(self.container_map, self.process_map, self.thread_map, self.allocator_1g_map)) by {
                        reveal(container_process_allocator_quota_1g_wf);
                        assert forall|c_ptr: RwLockContainerPtr|
                            #![trigger self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g]
                            self.container_map.dom().contains(c_ptr)
                        implies
                            self.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| {sum + process_effective_quota_1g(self.process_map.spec_index(p_ptr))})
                                + self.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_1g.view()})
                                + self.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_1g.view().spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                                + self.allocator_1g_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).quota.view().view()
                                == self.allocator_1g_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_1g).total_free_pages.view()
                        by {
                            assert(self.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().subset_of(self.thread_map.dom())) by {
                                reveal(container_thread_wf);
                            };
                            assert(self.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().subset_of(self.thread_map.dom())) by {
                                reveal(container_thread_wf);
                            };
                            lemma_thread_direct_pending_1g_fold_eq(
                                self.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view(),
                                old(self).thread_map, self.thread_map);
                            lemma_thread_indirect_pending_1g_fold_eq_at_depth(
                                self.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view(),
                                old(self).thread_map, self.thread_map, self.container_map.spec_index(c_ptr).view_rodata().view().depth as int);
                        };
                    };
                    assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map));
                    assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by { reveal(container_allocator_wf); };
                    assert(self.allocator_free_pages_wf());
                    assert(process_pagetable_match(self.process_map, self.pagetable_map)) by { reveal(process_pagetable_match); };
                    assert(process_staged_pages_wf(self.process_map, self.page_array)) by {
                        reveal(process_staged_pages_4k_wf); reveal(process_staged_pages_2m_wf); reveal(process_staged_pages_1g_wf);
                    };
                    assert(hugepage_2m_wf(self.page_array));
                    assert(hugepage_1g_wf(self.page_array));
                    assert(page_pagetable_wf(self.pagetable_map, self.page_array));
                    assert(pagetable_pages_wf(self.pagetable_map, self.page_array));
                    assert(thread_pages_wf(self.thread_map, self.page_array)) by { reveal(thread_pages_wf); };
                    assert(endpoint_pages_wf(self.endpoint_map, self.page_array));
                    assert(container_allocator_free_4k_page_wf(self.container_map, self.allocator_4k_map, self.page_array)) by {
                        reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                    };
                    assert(container_allocator_free_2m_page_wf(self.container_map, self.allocator_2m_map, self.page_array)) by {
                        reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                    };
                    assert(container_allocator_free_1g_page_wf(self.container_map, self.allocator_1g_map, self.page_array)) by {
                        reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                    };
                };
                // ---- process_management_inv ----
                assert(self.process_management_inv()) by {
                    assert(container_tree_wf(self.root_container, self.container_map));
                    assert(container_process_wf(self.container_map, self.process_map)) by { reveal(container_process_wf); };
                    assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                        reveal(container_process_wf); reveal(per_container_process_tree_wf);
                    };
                    assert(container_endpoint_wf(self.container_map, self.endpoint_map)) by { reveal(container_endpoint_wf); };
                    assert(container_cpu_wf(self.container_map, self.cpu_array)) by { reveal(container_cpu_wf); };
                    assert(thread_endpoint_ref_counter_wf(self.thread_map, self.endpoint_map)) by { reveal(thread_endpoint_ref_counter_wf); };
                    assert(thread_endpoint_queue_wf(self.thread_map, self.endpoint_map)) by { reveal(thread_endpoint_queue_wf); };
                    assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
                        reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
                        reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf);
                    };
                    assert(container_scheduler_wf(self.container_map, self.scheduler_map)) by { reveal(container_scheduler_wf); };
                    assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
                        reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
                    };
                    assert(container_thread_wf(self.container_map, self.thread_map)) by { reveal(container_thread_wf); };
                    assert(process_cpu_wf(self.process_map, self.cpu_array)) by { reveal(process_cpu_wf); };
                    assert(process_thread_wf(self.process_map, self.thread_map)) by {
                        reveal(process_thread_wf);
                        assert forall|p2: RwLockProcessPtr, t2: RwLockThreadPtr|
                            #![trigger self.process_map.spec_index(p2).view(), self.thread_map.spec_index(t2).view()]
                            self.process_map.dom().contains(p2) && self.process_map.spec_index(p2).view().owned_threads.view().contains(t2)
                            implies
                                self.thread_map.dom().contains(t2) && self.thread_map.spec_index(t2).view().owning_proc == p2
                                && self.thread_map.spec_index(t2).view().proc_pagetable_ptr == self.process_map.spec_index(p2).view().pagetable
                                && self.process_map.spec_index(p2).view().owned_threads.map().dom().contains(self.thread_map.spec_index(t2).view().proc_linkedlist_node.addr())
                                && self.process_map.spec_index(p2).view().owned_threads.map().spec_index(self.thread_map.spec_index(t2).view().proc_linkedlist_node.addr()) == t2
                        by {
                            assert(old(self).process_map.spec_index(p2).view().owned_threads.view().contains(t2));
                            assert(self.thread_map.spec_index(t2).view() == old(self).thread_map.spec_index(t2).view());
                        };
                        assert forall|t2: RwLockThreadPtr|
                            #![trigger self.thread_map.spec_index(t2).view().owning_proc]
                            self.thread_map.dom().contains(t2)
                            implies
                                self.process_map.dom().contains(self.thread_map.spec_index(t2).view().owning_proc)
                                && self.process_map.spec_index(self.thread_map.spec_index(t2).view().owning_proc).view().owned_threads.view().contains(t2)
                        by {
                            assert(old(self).thread_map.dom().contains(t2));
                            assert(self.thread_map.spec_index(t2).view() == old(self).thread_map.spec_index(t2).view());
                        };
                    };
                    assert(thread_cpu_wf(self.thread_map, self.cpu_array)) by {
                        reveal(thread_cpu_wf);
                    };
                };
                // ---- inv() direct conjuncts ----
                assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
                    reveal(cpu_dirty_map_contains_container_processes);
                    reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                    reveal(cpu_dirty_map_proc_pcid_match);
                    reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                    reveal(container_cpu_wf);
                };
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
                assert(self.inv());
                // ---- locked_objects_match_lctx: thread slot released, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(container_locked_match_lctx);
                    reveal(process_locked_match_lctx);
                    reveal(thread_locked_match_lctx);
                    reveal(endpoint_locked_match_lctx);
                    reveal(scheduler_locked_match_lctx);
                    reveal(pagetable_locked_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(cpu_locked_match_lctx);
                    reveal(allocator_locked_match_lctx);
                }
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
                old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
                cpu_id_valid(cache_cpu),
                wlock_requires(old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu]@, old(lctx)),
                old(lctx).lock_id_acyclic(LockId{
                    container: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu].container_depth(),
                    process: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu].process_depth(),
                    major: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu]@@.current_lock_major(),
                    minor: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu].lock_minor(),
                }),
                old(lctx).obj_id_fresh(KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cache_cpu)),
                old(self).locked_objects_match_lctx(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Every held lock still matches lctx (cache now locked) ----
                final(self).locked_objects_match_lctx(final(lctx)),

                // ---- Field framing: only allocator_4k_map's cache lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).scheduler_map     == old(self).scheduler_map,
                final(self).process_map       == old(self).process_map,
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- allocator_4k_map: dom unchanged; only the targeted entry's cache lock state changed ----
                final(self).allocator_4k_map.dom() == old(self).allocator_4k_map.dom(),
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
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),

                // ---- The lock perm + lock ensures (forwarded from UnLockedMap::wlock_cache) ----
                wlock_ensures(
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu]@,
                    final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu]@,
                    LockId{
                        container: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu].container_depth(),
                        process: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu].process_depth(),
                        major: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu]@@.current_lock_major(),
                        minor: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu].lock_minor(),
                    },
                    final(lctx).thread_id(),
                    ret@,
                ),
                lock_ensures(
                    old(lctx), final(lctx),
                    final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu]@@,
                    LockId{
                        container: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu].container_depth(),
                        process: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu].process_depth(),
                        major: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu]@@.current_lock_major(),
                        minor: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu].lock_minor(),
                    },
                    KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cache_cpu),
                ),
        {
            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
                reveal(process_perms_wf);
            }
            let ret = self.allocator_4k_map.wlock_cache(alloc_ptr_4k, cache_cpu, Tracked(&mut *lctx), Ghost(PageSize::SZ4k));

            proof {
                // ---- subsystems_inv ----
                assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
                assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
                assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
                assert(process_perms_wf(self.process_map)) by { reveal(process_perms_wf); reveal(process_temp_alloc_empty_unless_wlocked); };
                assert(thread_perms_wf(self.thread_map)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                // ---- memory_management_inv ----
                assert(self.memory_management_inv()) by {
                    assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf);
                    };
                    assert(container_page_owner_wf(self.container_map, self.page_array)) by {
                        reveal(container_page_owner_wf);
                    };
                    assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by {
                        reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
                    };
                    assert(container_pages_wf(self.page_array, self.container_map)) by {
                        reveal(container_pages_wf);
                    };
                    assert(process_pages_wf(self.page_array, self.process_map)) by {
                        reveal(process_pages_wf);
                    };
                    assert(container_process_allocator_quota_4k_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map)) by {
                        reveal(container_process_allocator_quota_4k_wf);
                        reveal(container_allocator_wf);
                        // assert forall|c_ptr: RwLockContainerPtr|
                        //     #![trigger self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k]
                        //     self.container_map.dom().contains(c_ptr)
                        // implies
                        //     self.container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| {sum + process_effective_quota_4k(self.process_map.spec_index(p_ptr))})
                        //         + self.container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_4k.view()})
                        //         + self.container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_4k.view().spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                        //         + self.allocator_4k_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).quota.view().view()
                        //         == self.allocator_4k_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).total_free_pages.view()
                        // by {
                        //     let aptr = self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k;
                        //     let depth = self.container_map.spec_index(c_ptr).view_rodata().view().depth as int;
                        //     assert(self.allocator_4k_map.dom().contains(aptr)) by {
                        //         reveal(container_allocator_wf);
                        //     };
                            // assert(old(self).container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| {sum + process_effective_quota_4k(old(self).process_map.spec_index(p_ptr))})
                            //     + old(self).container_map.spec_index(c_ptr).view_user_ghost().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + old(self).thread_map.spec_index(t_ptr).view().direct_free_quota_pending_4k.view()})
                            //     + old(self).container_map.spec_index(c_ptr).view_kernel_ghost().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + old(self).thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_4k.view().spec_index(old(self).container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                            //     + old(self).allocator_4k_map.spec_index(aptr).quota.view().view()
                            //     == old(self).allocator_4k_map.spec_index(aptr).total_free_pages.view()) by {
                            //     reveal(container_process_allocator_quota_4k_wf);
                            // };
                        // };
                    };
                    assert(container_process_allocator_quota_2m_wf(self.container_map, self.process_map, self.thread_map, self.allocator_2m_map));
                    assert(container_process_allocator_quota_1g_wf(self.container_map, self.process_map, self.thread_map, self.allocator_1g_map));
                    assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map));
                    assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(container_allocator_wf);
                    };
                    assert(allocator_free_page_ptrs_wf(self.allocator_4k_map)) by {
                        reveal(allocator_free_page_ptrs_wf);
                    };
                    assert(self.allocator_free_pages_wf());
                    assert(process_pagetable_match(self.process_map, self.pagetable_map)) by { reveal(process_pagetable_match); };
                    assert(hugepage_2m_wf(self.page_array));
                    assert(hugepage_1g_wf(self.page_array));
                    assert(page_pagetable_wf(self.pagetable_map, self.page_array));
                    assert(pagetable_pages_wf(self.pagetable_map, self.page_array));
                    assert(thread_pages_wf(self.thread_map, self.page_array));
                    assert(process_staged_pages_wf(self.process_map, self.page_array));
                    assert(endpoint_pages_wf(self.endpoint_map, self.page_array));
                    lemma_container_allocator_free_4k_page_wf_preserved_for_lock_op(*old(self), *self);
                    assert(container_allocator_free_2m_page_wf(self.container_map, self.allocator_2m_map, self.page_array)) by {
                        reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                    };
                    assert(container_allocator_free_1g_page_wf(self.container_map, self.allocator_1g_map, self.page_array)) by {
                        reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                    };
                };
                // ---- process_management_inv: container_map, process_map, etc. all byte-equal ----
                assert(self.process_management_inv()) by {
                    assert(container_tree_wf(self.root_container, self.container_map));
                    assert(container_process_wf(self.container_map, self.process_map)) by { reveal(container_process_wf); };
                    assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                        reveal(container_process_wf); reveal(per_container_process_tree_wf);
                    };
                    assert(container_endpoint_wf(self.container_map, self.endpoint_map)) by { reveal(container_endpoint_wf); };
                    assert(container_cpu_wf(self.container_map, self.cpu_array)) by { reveal(container_cpu_wf); };
                    assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
                        reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
                        reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf);
                    };
                    assert(container_scheduler_wf(self.container_map, self.scheduler_map)) by { reveal(container_scheduler_wf); };
                    assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
                        reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
                    };
                    assert(container_thread_wf(self.container_map, self.thread_map)) by { reveal(container_thread_wf); };
                    assert(process_cpu_wf(self.process_map, self.cpu_array)) by { reveal(process_cpu_wf); };
                    assert(process_thread_wf(self.process_map, self.thread_map)) by { reveal(process_thread_wf); };
                };
                // ---- inv() direct conjuncts ----
                assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
                    reveal(cpu_dirty_map_contains_container_processes);
                    reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                    reveal(cpu_dirty_map_proc_pcid_match);
                    reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                    reveal(container_cpu_wf);
                };
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
                assert(self.inv());
                // ---- locked_objects_match_lctx: cache slot gained, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(container_locked_match_lctx);
                    reveal(process_locked_match_lctx);
                    reveal(thread_locked_match_lctx);
                    reveal(endpoint_locked_match_lctx);
                    reveal(scheduler_locked_match_lctx);
                    reveal(pagetable_locked_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(cpu_locked_match_lctx);
                    reveal(allocator_locked_match_lctx);
                }
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
                cpu_id_valid(cache_cpu),
                lock_perm@.state() is WriteLock,
                lock_perm@.thread_id() == old(lctx).thread_id(),
                lock_perm@.lock_id() == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu]@.locking_thread()->Write_lock_id,
                old(lctx).allocator_4k_lock_map().dom().contains(AllocatorLockObjId::Cache(alloc_ptr_4k, cache_cpu)),
                old(lctx).allocator_4k_lock_map()[AllocatorLockObjId::Cache(alloc_ptr_4k, cache_cpu)] == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu].lock_id(),
                old(self).locked_objects_match_lctx(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Every held lock still matches lctx (cache now released) ----
                final(self).locked_objects_match_lctx(final(lctx)),

                // ---- Field framing: only allocator_4k_map's cache lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).scheduler_map     == old(self).scheduler_map,
                final(self).process_map       == old(self).process_map,
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- allocator_4k_map: dom unchanged; only the targeted entry's cache lock state changed (now unlocked) ----
                final(self).allocator_4k_map.dom() == old(self).allocator_4k_map.dom(),
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).owning_container == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).owning_container,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.unchanged_except(&old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches, cache_cpu),
                forall|k: usize| #![auto] old(self).allocator_4k_map.dom().contains(k) && k != alloc_ptr_4k ==>
                    final(self).allocator_4k_map.spec_index(k) == old(self).allocator_4k_map.spec_index(k),

                // ---- LocalContext: lock dropped; thread + user-view phase preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` transitions it Acquire -> Release, so restating
                // `== old` would contradict it and make the postcondition `false`
                // in an Acquire section (same trap as the NOTE on
                // `LockedArray::wunlock`). user_view is separately preserved.
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),

                // ---- wunlock ensures (forwarded from UnLockedMap::wunlock_cache) ----
                wunlock_ensures(
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu]@,
                    final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu]@,
                ),
                unlock_ensures(
                    old(lctx),
                    final(lctx),
                    final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches[cache_cpu]@@,
                    lock_perm@.lock_id(),
                    KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr_4k, cache_cpu),
                ),
        {
            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
                reveal(allocator_locked_match_lctx);
                reveal(process_perms_wf);
            }
            self.allocator_4k_map.wunlock_cache(alloc_ptr_4k, cache_cpu, Tracked(&mut *lctx), lock_perm, Ghost(PageSize::SZ4k));

            proof {
                // ---- subsystems_inv ----
                assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
                assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
                assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
                assert(process_perms_wf(self.process_map)) by { reveal(process_perms_wf); reveal(process_temp_alloc_empty_unless_wlocked); };
                assert(thread_perms_wf(self.thread_map)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                // ---- memory_management_inv ----
                assert(self.memory_management_inv()) by {
                    assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf);
                    };
                    assert(container_page_owner_wf(self.container_map, self.page_array)) by {
                        reveal(container_page_owner_wf);
                    };
                    assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by {
                        reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
                    };
                    assert(container_pages_wf(self.page_array, self.container_map)) by {
                        reveal(container_pages_wf);
                    };
                    assert(process_pages_wf(self.page_array, self.process_map)) by {
                        reveal(process_pages_wf);
                    };
                    assert(container_process_allocator_quota_4k_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map)) by {
                        reveal(container_process_allocator_quota_4k_wf);
                        reveal(container_allocator_wf);
                    };
                    assert(container_process_allocator_quota_2m_wf(self.container_map, self.process_map, self.thread_map, self.allocator_2m_map));
                    assert(container_process_allocator_quota_1g_wf(self.container_map, self.process_map, self.thread_map, self.allocator_1g_map));
                    assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map));
                    assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(container_allocator_wf);
                    };
                    assert(allocator_free_page_ptrs_wf(self.allocator_4k_map)) by {
                        reveal(allocator_free_page_ptrs_wf);
                    };
                    assert(self.allocator_free_pages_wf());
                    assert(process_pagetable_match(self.process_map, self.pagetable_map)) by { reveal(process_pagetable_match); };
                    assert(hugepage_2m_wf(self.page_array));
                    assert(hugepage_1g_wf(self.page_array));
                    assert(page_pagetable_wf(self.pagetable_map, self.page_array));
                    assert(pagetable_pages_wf(self.pagetable_map, self.page_array));
                    assert(thread_pages_wf(self.thread_map, self.page_array));
                    assert(process_staged_pages_wf(self.process_map, self.page_array));
                    assert(endpoint_pages_wf(self.endpoint_map, self.page_array));
                    lemma_container_allocator_free_4k_page_wf_preserved_for_lock_op(*old(self), *self);
                    assert(container_allocator_free_2m_page_wf(self.container_map, self.allocator_2m_map, self.page_array)) by {
                        reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                    };
                    assert(container_allocator_free_1g_page_wf(self.container_map, self.allocator_1g_map, self.page_array)) by {
                        reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                    };
                };
                // ---- process_management_inv: container_map, process_map, etc. all byte-equal ----
                assert(self.process_management_inv()) by {
                    assert(container_tree_wf(self.root_container, self.container_map));
                    assert(container_process_wf(self.container_map, self.process_map)) by { reveal(container_process_wf); };
                    assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                        reveal(container_process_wf); reveal(per_container_process_tree_wf);
                    };
                    assert(container_endpoint_wf(self.container_map, self.endpoint_map)) by { reveal(container_endpoint_wf); };
                    assert(container_cpu_wf(self.container_map, self.cpu_array)) by { reveal(container_cpu_wf); };
                    assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
                        reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
                        reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf);
                    };
                    assert(container_scheduler_wf(self.container_map, self.scheduler_map)) by { reveal(container_scheduler_wf); };
                    assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
                        reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
                    };
                    assert(container_thread_wf(self.container_map, self.thread_map)) by { reveal(container_thread_wf); };
                    assert(process_cpu_wf(self.process_map, self.cpu_array)) by { reveal(process_cpu_wf); };
                    assert(process_thread_wf(self.process_map, self.thread_map)) by { reveal(process_thread_wf); };
                };
                // ---- inv() direct conjuncts ----
                assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
                    reveal(cpu_dirty_map_contains_container_processes);
                    reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                    reveal(cpu_dirty_map_proc_pcid_match);
                    reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                    reveal(container_cpu_wf);
                };
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
                assert(self.inv());
                // ---- locked_objects_match_lctx: cache slot released, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(container_locked_match_lctx);
                    reveal(process_locked_match_lctx);
                    reveal(thread_locked_match_lctx);
                    reveal(endpoint_locked_match_lctx);
                    reveal(scheduler_locked_match_lctx);
                    reveal(pagetable_locked_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(cpu_locked_match_lctx);
                    reveal(allocator_locked_match_lctx);
                }
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
                old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
                wlock_requires(old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool, old(lctx)),
                old(lctx).lock_id_acyclic(LockId{
                    container: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool@.container_depth(),
                    process: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool@.process_depth(),
                    major: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool@.current_lock_major(),
                    minor: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool@.lock_minor(),
                }),
                old(lctx).obj_id_fresh(KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, alloc_ptr_4k)),
                old(self).locked_objects_match_lctx(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Every held lock still matches lctx (global pool now locked) ----
                final(self).locked_objects_match_lctx(final(lctx)),

                // ---- Field framing: only allocator_4k_map's global_pool lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).scheduler_map     == old(self).scheduler_map,
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
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),

                // ---- The lock perm + lock ensures (forwarded from UnLockedMap::wlock_global_pool) ----
                wlock_ensures(
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool,
                    final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool,
                    LockId{
                        container: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool@.container_depth(),
                        process: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool@.process_depth(),
                        major: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool@.current_lock_major(),
                        minor: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool@.lock_minor(),
                    },
                    final(lctx).thread_id(),
                    ret@,
                ),
                lock_ensures(
                    old(lctx), final(lctx),
                    final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view(),
                    LockId{
                        container: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool@.container_depth(),
                        process: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool@.process_depth(),
                        major: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool@.current_lock_major(),
                        minor: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool@.lock_minor(),
                    },
                    KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, alloc_ptr_4k),
                ),
        {
            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
                reveal(process_perms_wf);
            }
            let ret = self.allocator_4k_map.wlock_global_pool(alloc_ptr_4k, Tracked(&mut *lctx), Ghost(PageSize::SZ4k));

            proof {
                // ---- subsystems_inv ----
                assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
                assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
                assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
                assert(process_perms_wf(self.process_map)) by { reveal(process_perms_wf); reveal(process_temp_alloc_empty_unless_wlocked); };
                assert(thread_perms_wf(self.thread_map)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                // ---- memory_management_inv ----
                assert(self.memory_management_inv()) by {
                    assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf);
                    };
                    assert(container_page_owner_wf(self.container_map, self.page_array)) by {
                        reveal(container_page_owner_wf);
                    };
                    assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by {
                        reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
                    };
                    assert(container_pages_wf(self.page_array, self.container_map)) by {
                        reveal(container_pages_wf);
                    };
                    assert(process_pages_wf(self.page_array, self.process_map)) by {
                        reveal(process_pages_wf);
                    };
                    assert(container_process_allocator_quota_4k_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map)) by {
                        reveal(container_process_allocator_quota_4k_wf);
                        reveal(container_allocator_wf);
                    };
                    assert(container_process_allocator_quota_2m_wf(self.container_map, self.process_map, self.thread_map, self.allocator_2m_map));
                    assert(container_process_allocator_quota_1g_wf(self.container_map, self.process_map, self.thread_map, self.allocator_1g_map));
                    assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map));
                    assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(container_allocator_wf);
                    };
                    assert(allocator_free_page_ptrs_wf(self.allocator_4k_map)) by {
                        reveal(allocator_free_page_ptrs_wf);
                    };
                    assert(self.allocator_free_pages_wf());
                    assert(process_pagetable_match(self.process_map, self.pagetable_map)) by { reveal(process_pagetable_match); };
                    assert(hugepage_2m_wf(self.page_array));
                    assert(hugepage_1g_wf(self.page_array));
                    assert(page_pagetable_wf(self.pagetable_map, self.page_array));
                    assert(pagetable_pages_wf(self.pagetable_map, self.page_array));
                    assert(thread_pages_wf(self.thread_map, self.page_array));
                    assert(process_staged_pages_wf(self.process_map, self.page_array));
                    assert(endpoint_pages_wf(self.endpoint_map, self.page_array));
                    lemma_container_allocator_free_4k_page_wf_preserved_for_lock_op(*old(self), *self);
                    assert(container_allocator_free_2m_page_wf(self.container_map, self.allocator_2m_map, self.page_array)) by {
                        reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                    };
                    assert(container_allocator_free_1g_page_wf(self.container_map, self.allocator_1g_map, self.page_array)) by {
                        reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                    };
                };
                // ---- process_management_inv: container_map, process_map, etc. all byte-equal ----
                assert(self.process_management_inv()) by {
                    assert(container_tree_wf(self.root_container, self.container_map));
                    assert(container_process_wf(self.container_map, self.process_map)) by { reveal(container_process_wf); };
                    assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                        reveal(container_process_wf); reveal(per_container_process_tree_wf);
                    };
                    assert(container_endpoint_wf(self.container_map, self.endpoint_map)) by { reveal(container_endpoint_wf); };
                    assert(container_cpu_wf(self.container_map, self.cpu_array)) by { reveal(container_cpu_wf); };
                    assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
                        reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
                        reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf);
                    };
                    assert(container_scheduler_wf(self.container_map, self.scheduler_map)) by { reveal(container_scheduler_wf); };
                    assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
                        reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
                    };
                    assert(container_thread_wf(self.container_map, self.thread_map)) by { reveal(container_thread_wf); };
                    assert(process_cpu_wf(self.process_map, self.cpu_array)) by { reveal(process_cpu_wf); };
                    assert(process_thread_wf(self.process_map, self.thread_map)) by { reveal(process_thread_wf); };
                };
                // ---- inv() direct conjuncts ----
                assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
                    reveal(cpu_dirty_map_contains_container_processes);
                    reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                    reveal(cpu_dirty_map_proc_pcid_match);
                    reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                    reveal(container_cpu_wf);
                };
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
                assert(self.inv());
                // ---- locked_objects_match_lctx: global pool slot gained, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(container_locked_match_lctx);
                    reveal(process_locked_match_lctx);
                    reveal(thread_locked_match_lctx);
                    reveal(endpoint_locked_match_lctx);
                    reveal(scheduler_locked_match_lctx);
                    reveal(pagetable_locked_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(cpu_locked_match_lctx);
                    reveal(allocator_locked_match_lctx);
                }
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
                unlock_requires::<GlobalPool>(old(lctx)),
                lock_perm@.state() is WriteLock,
                lock_perm@.thread_id() == old(lctx).thread_id(),
                lock_perm@.lock_id() == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.locking_thread()->Write_lock_id,
                old(lctx).allocator_4k_lock_map().dom().contains(AllocatorLockObjId::GlobalPool(alloc_ptr_4k)),
                old(lctx).allocator_4k_lock_map()[AllocatorLockObjId::GlobalPool(alloc_ptr_4k)] == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.lock_id(),
                old(self).locked_objects_match_lctx(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Every held lock still matches lctx (global pool now released) ----
                final(self).locked_objects_match_lctx(final(lctx)),

                // ---- Field framing: only allocator_4k_map's global_pool lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).scheduler_map     == old(self).scheduler_map,
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

                // ---- LocalContext: lock dropped; thread + user-view phase preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` transitions it Acquire -> Release, so restating
                // `== old` would contradict it and make the postcondition `false`
                // in an Acquire section (same trap as the NOTE on
                // `LockedArray::wunlock`). user_view is separately preserved.
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),

                // ---- wunlock ensures (forwarded from UnLockedMap::wunlock_global_pool) ----
                wunlock_ensures(
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool,
                    final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool,
                ),
                unlock_ensures(
                    old(lctx),
                    final(lctx),
                    final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view(),
                    lock_perm@.lock_id(),
                    KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, alloc_ptr_4k),
                ),
        {
            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
                reveal(allocator_locked_match_lctx);
                reveal(process_perms_wf);
            }
            self.allocator_4k_map.wunlock_global_pool(alloc_ptr_4k, Tracked(&mut *lctx), lock_perm, Ghost(PageSize::SZ4k));

            proof {
                // ---- subsystems_inv ----
                assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
                assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
                assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
                assert(process_perms_wf(self.process_map)) by { reveal(process_perms_wf); reveal(process_temp_alloc_empty_unless_wlocked); };
                assert(thread_perms_wf(self.thread_map)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                // ---- memory_management_inv ----
                assert(self.memory_management_inv()) by {
                    assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf);
                    };
                    assert(container_page_owner_wf(self.container_map, self.page_array)) by {
                        reveal(container_page_owner_wf);
                    };
                    assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by {
                        reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
                    };
                    assert(container_pages_wf(self.page_array, self.container_map)) by {
                        reveal(container_pages_wf);
                    };
                    assert(process_pages_wf(self.page_array, self.process_map)) by {
                        reveal(process_pages_wf);
                    };
                    assert(container_process_allocator_quota_4k_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map)) by {
                        reveal(container_process_allocator_quota_4k_wf);
                        reveal(container_allocator_wf);
                    };
                    assert(container_process_allocator_quota_2m_wf(self.container_map, self.process_map, self.thread_map, self.allocator_2m_map));
                    assert(container_process_allocator_quota_1g_wf(self.container_map, self.process_map, self.thread_map, self.allocator_1g_map));
                    assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map));
                    assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(container_allocator_wf);
                    };
                    assert(allocator_free_page_ptrs_wf(self.allocator_4k_map)) by {
                        reveal(allocator_free_page_ptrs_wf);
                    };
                    assert(self.allocator_free_pages_wf());
                    assert(process_pagetable_match(self.process_map, self.pagetable_map)) by { reveal(process_pagetable_match); };
                    assert(hugepage_2m_wf(self.page_array));
                    assert(hugepage_1g_wf(self.page_array));
                    assert(page_pagetable_wf(self.pagetable_map, self.page_array));
                    assert(pagetable_pages_wf(self.pagetable_map, self.page_array));
                    assert(thread_pages_wf(self.thread_map, self.page_array));
                    assert(process_staged_pages_wf(self.process_map, self.page_array));
                    assert(endpoint_pages_wf(self.endpoint_map, self.page_array));
                    lemma_container_allocator_free_4k_page_wf_preserved_for_lock_op(*old(self), *self);
                    assert(container_allocator_free_2m_page_wf(self.container_map, self.allocator_2m_map, self.page_array)) by {
                        reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                    };
                    assert(container_allocator_free_1g_page_wf(self.container_map, self.allocator_1g_map, self.page_array)) by {
                        reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                    };
                };
                // ---- process_management_inv: container_map, process_map, etc. all byte-equal ----
                assert(self.process_management_inv()) by {
                    assert(container_tree_wf(self.root_container, self.container_map));
                    assert(container_process_wf(self.container_map, self.process_map)) by { reveal(container_process_wf); };
                    assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                        reveal(container_process_wf); reveal(per_container_process_tree_wf);
                    };
                    assert(container_endpoint_wf(self.container_map, self.endpoint_map)) by { reveal(container_endpoint_wf); };
                    assert(container_cpu_wf(self.container_map, self.cpu_array)) by { reveal(container_cpu_wf); };
                    assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
                        reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
                        reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf);
                    };
                    assert(container_scheduler_wf(self.container_map, self.scheduler_map)) by { reveal(container_scheduler_wf); };
                    assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
                        reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
                    };
                    assert(container_thread_wf(self.container_map, self.thread_map)) by { reveal(container_thread_wf); };
                    assert(process_cpu_wf(self.process_map, self.cpu_array)) by { reveal(process_cpu_wf); };
                    assert(process_thread_wf(self.process_map, self.thread_map)) by { reveal(process_thread_wf); };
                };
                // ---- inv() direct conjuncts ----
                assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
                    reveal(cpu_dirty_map_contains_container_processes);
                    reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                    reveal(cpu_dirty_map_proc_pcid_match);
                    reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                    reveal(container_cpu_wf);
                };
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
                assert(self.inv());
                // ---- locked_objects_match_lctx: global pool slot released, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(container_locked_match_lctx);
                    reveal(process_locked_match_lctx);
                    reveal(thread_locked_match_lctx);
                    reveal(endpoint_locked_match_lctx);
                    reveal(scheduler_locked_match_lctx);
                    reveal(pagetable_locked_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(cpu_locked_match_lctx);
                    reveal(allocator_locked_match_lctx);
                }
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
                page_index_wf(page_index),
                wlock_requires(old(self).page_array[page_index]@, old(lctx)),
                old(lctx).lock_id_acyclic(old(self).page_array.lock_id_by_index(page_index)),
                old(lctx).obj_id_fresh(KernelObjId::Page(page_index)),
                old(self).locked_objects_match_lctx(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Every held lock still matches lctx (page slot now locked) ----
                final(self).locked_objects_match_lctx(final(lctx)),

                // ---- Field framing: only page_array's slot lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).scheduler_map     == old(self).scheduler_map,
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
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),

                // ---- The lock perm + lock ensures (forwarded from LockedArray::wlock) ----
                wlock_ensures(
                    old(self).page_array[page_index]@,
                    final(self).page_array[page_index]@,
                    old(self).page_array.lock_id_by_index(page_index),
                    final(lctx).thread_id(),
                    ret@,
                ),
                lock_ensures(
                    old(lctx), final(lctx),
                    final(self).page_array[page_index]@@,
                    old(self).page_array.lock_id_by_index(page_index),
                    KernelObjId::Page(page_index),
                ),
        {
            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
                reveal(process_perms_wf);
                reveal(page_array_wf);
            }
            let ghost pre = *self;
            let ret = self.page_array.wlock(page_index, Tracked(&mut *lctx), Ghost(KernelObjId::Page(page_index)));
            proof {
                reveal(page_array_wf);
                // ---- subsystems_inv ----
                assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
                assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
                assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
                assert(process_perms_wf(self.process_map)) by { reveal(process_perms_wf); reveal(process_temp_alloc_empty_unless_wlocked); };
                assert(thread_perms_wf(self.thread_map)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                // ---- memory_management_inv ----
                assert(self.memory_management_inv()) by {
                    assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf);
                    };
                    assert(container_page_owner_wf(self.container_map, self.page_array)) by { reveal(container_page_owner_wf); };
                    assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by {
                        reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
                        reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
                    };
                    assert(container_pages_wf(self.page_array, self.container_map)) by { reveal(container_pages_wf); };
                    assert(process_pages_wf(self.page_array, self.process_map)) by { reveal(process_pages_wf); };
                    assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(container_process_allocator_quota_4k_wf); reveal(container_process_allocator_quota_2m_wf); reveal(container_process_allocator_quota_1g_wf);
                    };
                    assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by { reveal(container_allocator_wf); };
                    assert(self.allocator_free_pages_wf());
                    assert(process_pagetable_match(self.process_map, self.pagetable_map)) by { reveal(process_pagetable_match); };
                    assert(hugepage_2m_wf(self.page_array)) by { reveal(hugepage_2m_wf); };
                    assert(hugepage_1g_wf(self.page_array)) by { reveal(hugepage_1g_wf); };
                    assert(page_pagetable_wf(self.pagetable_map, self.page_array)) by {
                        reveal(page_pagetable_wf);
                        reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
                        reveal(pagetable_perms_wf); reveal(pagetables_inv);
                        page_ptr_lemma1();
                    };
                    assert(pagetable_pages_wf(self.pagetable_map, self.page_array)) by { reveal(pagetable_pages_wf); };
                    assert(thread_pages_wf(self.thread_map, self.page_array)) by { reveal(thread_pages_wf); };
                    assert(process_staged_pages_wf(self.process_map, self.page_array)) by {
                        reveal(process_staged_pages_wf); reveal(process_staged_pages_4k_wf); reveal(process_staged_pages_2m_wf); reveal(process_staged_pages_1g_wf);
                    };
                    assert(endpoint_pages_wf(self.endpoint_map, self.page_array)) by { reveal(endpoint_pages_wf); };
                    assert(container_allocator_free_4k_page_wf(self.container_map, self.allocator_4k_map, self.page_array)) by {
                        reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                        reveal(allocator_free_page_ptrs_wf); page_ptr_lemma1();
                    };
                    assert(container_allocator_free_2m_page_wf(self.container_map, self.allocator_2m_map, self.page_array)) by {
                        reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                        reveal(allocator_free_page_ptrs_wf); page_ptr_lemma1();
                    };
                    assert(container_allocator_free_1g_page_wf(self.container_map, self.allocator_1g_map, self.page_array)) by {
                        reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                        reveal(allocator_free_page_ptrs_wf); page_ptr_lemma1();
                    };
                };
                // ---- process_management_inv: all byte-equal maps ----
                assert(self.process_management_inv()) by {
                    reveal(container_process_wf); reveal(per_container_process_tree_wf);
                    reveal(container_endpoint_wf); reveal(container_cpu_wf);
                    reveal(thread_endpoint_ref_counter_wf); reveal(thread_endpoint_queue_wf);
                    reveal(container_thread_endpoint_wf); reveal(container_scheduler_wf);
                    reveal(container_thread_scheduler_wf); reveal(container_thread_wf);
                    reveal(process_cpu_wf); reveal(process_thread_wf);
                };
                // ---- inv() direct conjuncts ----
                assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
                    reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                    reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(container_cpu_wf);
                };
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
                assert(self.inv());
                // ---- locked_objects_match_lctx: page slot gained, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(container_locked_match_lctx);
                    reveal(process_locked_match_lctx);
                    reveal(thread_locked_match_lctx);
                    reveal(endpoint_locked_match_lctx);
                    reveal(scheduler_locked_match_lctx);
                    reveal(pagetable_locked_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(cpu_locked_match_lctx);
                    reveal(allocator_locked_match_lctx);
                }
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
                page_index_wf(page_index),
                old(self).page_array[page_index]@.being_killed() == false,
                lock_perm@.state() is WriteLock,
                lock_perm@.thread_id() == old(lctx).thread_id(),
                old(lctx).page_lock_map().dom().contains(page_index),
                old(lctx).page_lock_map()[page_index] == old(self).page_array.lock_id_by_index(page_index),
                lock_perm@.lock_id() == old(self).page_array[page_index]@.locking_thread()->Write_lock_id,
                old(self).locked_objects_match_lctx(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Every held lock still matches lctx (page slot now released) ----
                final(self).locked_objects_match_lctx(final(lctx)),

                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).scheduler_map     == old(self).scheduler_map,
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
                final(self).page_array[page_index]@.locking_thread() is None,

                // ---- LocalContext: lock dropped; thread + user-view phase preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` flips it Acquire → Release (same trap as the
                // `LockedArray::wunlock` NOTE).
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),

                // ---- wunlock ensures (forwarded from LockedArray::wunlock) ----
                wunlock_ensures(old(self).page_array[page_index]@, final(self).page_array[page_index]@),
                unlock_ensures(
                    old(lctx), final(lctx),
                    final(self).page_array[page_index]@@,
                    lock_perm@.lock_id(),
                    KernelObjId::Page(page_index),
                ),
                final(lctx).lock_maps_removed(old(lctx), KernelObjId::Page(page_index)),
        {
            proof {
                reveal(KernelK::locked_objects_match_lctx);
                reveal(scheduler_locked_match_lctx);
                reveal(process_locked_match_lctx);
                reveal(scheduler_perms_wf);
                reveal(process_perms_wf);
            }
            // proof {
            //     reveal(cpu_array_wf);
            //     reveal(container_perms_wf);
            //     reveal(allocator_perms_wf);
            //     reveal(process_perms_wf);
                // reveal(page_array_wf);
            // }
            // let ghost pre = *self;
            // assert(unlock_requires::<Page>(&*lctx)) by { assert(!Page::is_user_visible()); };
            assert(self.page_array.inv()) by {reveal(page_array_wf);};
            assert(self.page_array[page_index]@.wlocked_by(&*lctx)) by {
                reveal(KernelK::locked_objects_match_lctx);
                reveal(page_locked_match_lctx);
            }
            self.page_array.wunlock(page_index, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::Page(page_index)));
            proof {
                // ---- subsystems_inv ----
                assert(page_array_wf(self.page_array)) by {reveal(page_array_wf);};
                assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
                assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
                assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
                assert(process_perms_wf(self.process_map)) by { reveal(process_perms_wf); reveal(process_temp_alloc_empty_unless_wlocked); };
                assert(thread_perms_wf(self.thread_map)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                // ---- memory_management_inv ----
                assert(self.memory_management_inv()) by {
                    assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf);
                    };
                    assert(container_page_owner_wf(self.container_map, self.page_array)) by { reveal(container_page_owner_wf); };
                    assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by {
                        reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
                        reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
                    };
                    assert(container_pages_wf(self.page_array, self.container_map)) by { reveal(container_pages_wf); };
                    assert(process_pages_wf(self.page_array, self.process_map)) by { reveal(process_pages_wf); };
                    assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(container_process_allocator_quota_4k_wf); reveal(container_process_allocator_quota_2m_wf); reveal(container_process_allocator_quota_1g_wf);
                    };
                    assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by { reveal(container_allocator_wf); };
                    assert(self.allocator_free_pages_wf());
                    assert(process_pagetable_match(self.process_map, self.pagetable_map)) by { reveal(process_pagetable_match); };
                    assert(hugepage_2m_wf(self.page_array)) by { reveal(hugepage_2m_wf); };
                    assert(hugepage_1g_wf(self.page_array)) by { reveal(hugepage_1g_wf); };
                    assert(page_pagetable_wf(self.pagetable_map, self.page_array)) by {
                        reveal(page_pagetable_wf);
                        reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
                        reveal(pagetable_perms_wf); reveal(pagetables_inv);
                        page_ptr_lemma1();
                    };
                    assert(pagetable_pages_wf(self.pagetable_map, self.page_array)) by { reveal(pagetable_pages_wf); };
                    assert(thread_pages_wf(self.thread_map, self.page_array)) by { reveal(thread_pages_wf); };
                    assert(process_staged_pages_wf(self.process_map, self.page_array)) by {
                        reveal(process_staged_pages_wf); reveal(process_staged_pages_4k_wf); reveal(process_staged_pages_2m_wf); reveal(process_staged_pages_1g_wf);
                    };
                    assert(endpoint_pages_wf(self.endpoint_map, self.page_array)) by { reveal(endpoint_pages_wf); };
                    assert(container_allocator_free_4k_page_wf(self.container_map, self.allocator_4k_map, self.page_array)) by {
                        reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                        reveal(allocator_free_page_ptrs_wf); page_ptr_lemma1();
                    };
                    assert(container_allocator_free_2m_page_wf(self.container_map, self.allocator_2m_map, self.page_array)) by {
                        reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                        reveal(allocator_free_page_ptrs_wf); page_ptr_lemma1();
                    };
                    assert(container_allocator_free_1g_page_wf(self.container_map, self.allocator_1g_map, self.page_array)) by {
                        reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_wf); reveal(container_page_owner_wf);
                        reveal(allocator_free_page_ptrs_wf); page_ptr_lemma1();
                    };
                };
                // ---- process_management_inv: all byte-equal maps ----
                assert(self.process_management_inv()) by {
                    reveal(container_process_wf); reveal(per_container_process_tree_wf);
                    reveal(container_endpoint_wf); reveal(container_cpu_wf);
                    reveal(thread_endpoint_ref_counter_wf); reveal(thread_endpoint_queue_wf);
                    reveal(container_thread_endpoint_wf); reveal(container_scheduler_wf);
                    reveal(container_thread_scheduler_wf); reveal(container_thread_wf);
                    reveal(process_cpu_wf); reveal(process_thread_wf);
                };
                // ---- inv() direct conjuncts ----
                assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
                    reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                    reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(container_cpu_wf);
                };
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
                assert(self.inv());
                // ---- locked_objects_match_lctx: page slot released, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(container_locked_match_lctx);
                    reveal(process_locked_match_lctx);
                    reveal(thread_locked_match_lctx);
                    reveal(endpoint_locked_match_lctx);
                    reveal(scheduler_locked_match_lctx);
                    reveal(pagetable_locked_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(cpu_locked_match_lctx);
                    reveal(allocator_locked_match_lctx);
                }
            }
        }

        pub fn wlock_scheduler(
            &mut self,
            scheduler_ptr: RwLockSchedulerPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Tracked<LockPerm>)
            requires
                old(self).inv(),
                old(self).scheduler_map.dom().contains(scheduler_ptr),
                wlock_requires(old(self).scheduler_map.spec_index(scheduler_ptr), old(lctx)),
                old(lctx).lock_id_acyclic(LockId{
                    container: old(self).scheduler_map.spec_index(scheduler_ptr).container_depth(),
                    process: old(self).scheduler_map.spec_index(scheduler_ptr).process_depth(),
                    major: old(self).scheduler_map.spec_index(scheduler_ptr).view().current_lock_major(),
                    minor: scheduler_ptr,
                }),
                old(lctx).obj_id_fresh(KernelObjId::Scheduler(scheduler_ptr)),
                old(self).locked_objects_match_lctx(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Every held lock still matches lctx (scheduler now locked) ----
                final(self).locked_objects_match_lctx(final(lctx)),

                // ---- Field framing: only scheduler_map's lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
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
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),

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
                    ret@,
                ),
                lock_ensures(
                    old(lctx), final(lctx),
                    final(self).scheduler_map.spec_index(scheduler_ptr).view(),
                    LockId{
                        container: old(self).scheduler_map.spec_index(scheduler_ptr).container_depth(),
                        process: old(self).scheduler_map.spec_index(scheduler_ptr).process_depth(),
                        major: old(self).scheduler_map.spec_index(scheduler_ptr).view().current_lock_major(),
                        minor: scheduler_ptr,
                    },
                    KernelObjId::Scheduler(scheduler_ptr),
                ),
                final(lctx).lock_maps_inserted(old(lctx), KernelObjId::Scheduler(scheduler_ptr), final(self).scheduler_map.lock_id_by_key(scheduler_ptr)),
        {
            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
                reveal(process_perms_wf);
                reveal(scheduler_perms_wf);
            }
            let ret = self.scheduler_map.wlock(scheduler_ptr, Tracked(&mut *lctx), Ghost(KernelObjId::Scheduler(scheduler_ptr)));
            proof {
                // ---- subsystems_inv ----
                assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
                assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
                assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
                assert(process_perms_wf(self.process_map)) by { reveal(process_perms_wf); reveal(process_temp_alloc_empty_unless_wlocked); };
                assert(thread_perms_wf(self.thread_map)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                // ---- memory_management_inv: scheduler_map absent from every memory conjunct ----
                assert(self.memory_management_inv());
                // ---- process_management_inv: only scheduler_map's lock state moved; its view() is framed ----
                assert(self.process_management_inv()) by {
                    reveal(container_process_wf); reveal(per_container_process_tree_wf);
                    reveal(container_endpoint_wf); reveal(container_cpu_wf);
                    reveal(thread_endpoint_ref_counter_wf); reveal(thread_endpoint_queue_wf);
                    reveal(container_thread_endpoint_wf); reveal(container_scheduler_wf);
                    reveal(container_thread_scheduler_wf); reveal(container_thread_wf);
                    reveal(process_cpu_wf); reveal(process_thread_wf);
                };
                // ---- inv() direct conjuncts ----
                assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
                    reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                    reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(container_cpu_wf);
                };
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
                assert(self.inv());
                // ---- locked_objects_match_lctx: scheduler slot gained, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(container_locked_match_lctx);
                    reveal(process_locked_match_lctx);
                    reveal(thread_locked_match_lctx);
                    reveal(endpoint_locked_match_lctx);
                    reveal(scheduler_locked_match_lctx);
                    reveal(pagetable_locked_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(cpu_locked_match_lctx);
                    reveal(allocator_locked_match_lctx);
                }
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
                unlock_requires::<Scheduler>(old(lctx)),
                lock_perm@.state() is WriteLock,
                lock_perm@.thread_id() == old(lctx).thread_id(),
                old(lctx).scheduler_lock_map().dom().contains(scheduler_ptr),
                old(lctx).scheduler_lock_map()[scheduler_ptr] == old(self).scheduler_map.lock_id_by_key(scheduler_ptr),
                lock_perm@.lock_id() == old(self).scheduler_map.spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
                old(self).locked_objects_match_lctx(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Every held lock still matches lctx (scheduler now released) ----
                final(self).locked_objects_match_lctx(final(lctx)),

                // ---- Field framing: only scheduler_map's lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
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

                // ---- LocalContext: lock dropped; thread + user-view phase preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` flips it Acquire → Release (same trap as the
                // `LockedArray::wunlock` NOTE).
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),

                // ---- wunlock ensures (forwarded from LockedMap::wunlock) ----
                wunlock_ensures(
                    old(self).scheduler_map.spec_index(scheduler_ptr),
                    final(self).scheduler_map.spec_index(scheduler_ptr),
                ),
                unlock_ensures(
                    old(lctx), final(lctx),
                    final(self).scheduler_map.spec_index(scheduler_ptr).view(),
                    lock_perm@.lock_id(),
                    KernelObjId::Scheduler(scheduler_ptr),
                ),
                final(lctx).lock_maps_removed(old(lctx), KernelObjId::Scheduler(scheduler_ptr)),
        {
            proof {
                reveal(KernelK::locked_objects_match_lctx);
                reveal(scheduler_locked_match_lctx);
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
                reveal(process_perms_wf);
                reveal(scheduler_perms_wf);
            }
            self.scheduler_map.wunlock(scheduler_ptr, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::Scheduler(scheduler_ptr)));
            proof {
                // ---- subsystems_inv ----
                assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
                assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
                assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
                assert(process_perms_wf(self.process_map)) by { reveal(process_perms_wf); reveal(process_temp_alloc_empty_unless_wlocked); };
                assert(thread_perms_wf(self.thread_map)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                // ---- memory_management_inv: scheduler_map absent from every memory conjunct ----
                assert(self.memory_management_inv());
                // ---- process_management_inv: only scheduler_map's lock state moved; its view() is framed ----
                assert(self.process_management_inv()) by {
                    reveal(container_process_wf); reveal(per_container_process_tree_wf);
                    reveal(container_endpoint_wf); reveal(container_cpu_wf);
                    reveal(thread_endpoint_ref_counter_wf); reveal(thread_endpoint_queue_wf);
                    reveal(container_thread_endpoint_wf); reveal(container_scheduler_wf);
                    reveal(container_thread_scheduler_wf); reveal(container_thread_wf);
                    reveal(process_cpu_wf); reveal(process_thread_wf);
                };
                // ---- inv() direct conjuncts ----
                assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
                    reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                    reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(container_cpu_wf);
                };
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
                assert(self.inv());
                // ---- locked_objects_match_lctx: scheduler slot released, all else framed ----
                assert(self.locked_objects_match_lctx(&*lctx)) by {
                    reveal(container_locked_match_lctx);
                    reveal(process_locked_match_lctx);
                    reveal(thread_locked_match_lctx);
                    reveal(endpoint_locked_match_lctx);
                    reveal(scheduler_locked_match_lctx);
                    reveal(pagetable_locked_match_lctx);
                    reveal(page_locked_match_lctx);
                    reveal(cpu_locked_match_lctx);
                    reveal(allocator_locked_match_lctx);
                }
            }
        }

    }
}
