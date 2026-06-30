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
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

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
                assert(self.thread_perms_wf()) by { reveal(KernelK::thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
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
                old(self).cpu_array[cpu_id]@.wlocked_by(old(lctx)),
                old(self).cpu_array[cpu_id]@.being_killed() == false,
                unlock_requires::<Cpu>(old(lctx)),
                lock_perm@.state() is WriteLock,
                lock_perm@.thread_id() == old(lctx).thread_id(),
                lock_perm@.lock_id() == old(self).cpu_array[cpu_id]@.locking_thread()->Write_lock_id,
                old(lctx).lock_map().dom().contains(KernelObjId::Cpu(cpu_id)),
                old(lctx).lock_map()[KernelObjId::Cpu(cpu_id)] == lock_perm@.lock_id(),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

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
        {
            proof {
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
                assert(self.thread_perms_wf()) by { reveal(KernelK::thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
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
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

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
                    &&& final(lctx).lock_map() =~= old(lctx).lock_map()
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
                assert(self.thread_perms_wf()) by { reveal(KernelK::thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
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
                old(lctx).lock_map().dom().contains(KernelObjId::Container(container_ptr)),
                old(lctx).lock_map()[KernelObjId::Container(container_ptr)] == lock_perm@.lock_id(),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

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
                assert(self.thread_perms_wf()) by { reveal(KernelK::thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
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
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

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
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll,
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
                    self.allocator_4k_map.spec_index(aptr).global_poll == old(self).allocator_4k_map.spec_index(aptr).global_poll
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
                assert(self.thread_perms_wf()) by { reveal(KernelK::thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
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
                                + self.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_4k.view()})
                                + self.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_4k.view().spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                                + self.allocator_4k_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).quota.view().view()
                                == self.allocator_4k_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).total_free_pages.view()
                        by {
                            let aptr = self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k;
                            let depth = self.container_map.spec_index(c_ptr).view_rodata().view().depth as int;
                            lemma_process_effective_quota_4k_fold_eq(
                                self.container_map.spec_index(c_ptr).view().owned_processes.view(),
                                old(self).process_map, self.process_map);
                            lemma_thread_direct_pending_4k_fold_eq(
                                self.container_map.spec_index(c_ptr).view().owned_threads.view(),
                                old(self).thread_map, self.thread_map);
                            lemma_thread_indirect_pending_4k_fold_eq_at_depth(
                                self.container_map.spec_index(c_ptr).view().owned_indirect_threads.view(),
                                old(self).thread_map, self.thread_map, depth);
                            assert(self.allocator_4k_map.dom().contains(aptr)) by {
                                reveal(container_allocator_wf);
                            };
                            assert(old(self).container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| {sum + process_effective_quota_4k(old(self).process_map.spec_index(p_ptr))})
                                + old(self).container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + old(self).thread_map.spec_index(t_ptr).view().direct_free_quota_pending_4k.view()})
                                + old(self).container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + old(self).thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_4k.view().spec_index(old(self).container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
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
                old(lctx).lock_map().dom().contains(KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k)),
                old(lctx).lock_map()[KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k)] == lock_perm@.lock_id(),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

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
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll,
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
                assert(self.thread_perms_wf()) by { reveal(KernelK::thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
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
                                + self.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_4k.view()})
                                + self.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_4k.view().spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
                                + self.allocator_4k_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).quota.view().view()
                                == self.allocator_4k_map.spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k).total_free_pages.view()
                        by {
                            let aptr = self.container_map.spec_index(c_ptr).view_rodata().view().allocator_ptr_4k;
                            let depth = self.container_map.spec_index(c_ptr).view_rodata().view().depth as int;
                            lemma_process_effective_quota_4k_fold_eq(
                                self.container_map.spec_index(c_ptr).view().owned_processes.view(),
                                old(self).process_map, self.process_map);
                            lemma_thread_direct_pending_4k_fold_eq(
                                self.container_map.spec_index(c_ptr).view().owned_threads.view(),
                                old(self).thread_map, self.thread_map);
                            lemma_thread_indirect_pending_4k_fold_eq_at_depth(
                                self.container_map.spec_index(c_ptr).view().owned_indirect_threads.view(),
                                old(self).thread_map, self.thread_map, depth);
                            assert(self.allocator_4k_map.dom().contains(aptr)) by {
                                reveal(container_allocator_wf);
                            };
                            assert(old(self).container_map.spec_index(c_ptr).view().owned_processes.view().fold(0, |sum: int, p_ptr: RwLockProcessPtr| {sum + process_effective_quota_4k(old(self).process_map.spec_index(p_ptr))})
                                + old(self).container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + old(self).thread_map.spec_index(t_ptr).view().direct_free_quota_pending_4k.view()})
                                + old(self).container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + old(self).thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_4k.view().spec_index(old(self).container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
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
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

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
                    &&& final(lctx).lock_map() =~= old(lctx).lock_map()
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
                assert(self.thread_perms_wf()) by { reveal(KernelK::thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
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
                                + self.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_4k.view()})
                                + self.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_4k.view().spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
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
                                + self.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_2m.view()})
                                + self.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_2m.view().spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
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
                                + self.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_1g.view()})
                                + self.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_1g.view().spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
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
                old(self).process_map.dom().contains(process_ptr),
                old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
                old(self).process_map.spec_index(process_ptr).being_killed() == false,
                unlock_requires::<Process>(old(lctx)),
                lock_perm@.state() is WriteLock,
                lock_perm@.thread_id() == old(lctx).thread_id(),
                lock_perm@.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
                old(lctx).lock_map().dom().contains(KernelObjId::Process(process_ptr)),
                old(lctx).lock_map()[KernelObjId::Process(process_ptr)] == lock_perm@.lock_id(),
                // The "flushed before wunlock" protocol: the cache must be empty
                // before releasing the write lock (see doc comment above).
                old(self).process_map.spec_index(process_ptr).view().temp_alloc_clean(),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

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
        {
            proof {
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
                assert(self.thread_perms_wf()) by { reveal(KernelK::thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
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
                                + self.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_4k.view()})
                                + self.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_4k.view().spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
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
                                + self.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_2m.view()})
                                + self.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_2m.view().spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
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
                                + self.container_map.spec_index(c_ptr).view().owned_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().direct_free_quota_pending_1g.view()})
                                + self.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().fold(0, |sum: int, t_ptr: RwLockThreadPtr| {sum + self.thread_map.spec_index(t_ptr).view().indirect_free_quota_pending_1g.view().spec_index(self.container_map.spec_index(c_ptr).view_rodata().view().depth as int)})
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
            }
        }

    }
}