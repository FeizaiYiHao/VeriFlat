use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
        #[verifier::spinoff_prover]
        pub fn wlock_thread_unless_killed(
            &mut self,
            thread_ptr: RwLockThreadPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Option<Tracked<LockPerm>>)
            requires
                old(self).inv(),
                old(self).thr_mp.dom().contains(thread_ptr),
                !typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
                old(lctx).kernel_view_locking_state() is Acquire,
                {
                    let cpus = old(lctx).cpu_lock_map().dom();
                    let thread = old(self).thr_mp.spec_index(thread_ptr).view();
                    &&& (forall|held_cpu_id: CpuId|
                        #![trigger cpus.contains(held_cpu_id)]
                        cpus.contains(held_cpu_id) ==> {
                            &&& index_valid(NUM_CPUS, held_cpu_id)
                            &&& !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off)
                        })
                    &&& match thread.state {
                        ThreadState::RUNNING { cpu_id } => {
                            let containers = old(lctx).container_lock_map().dom();
                            let pcid_allocators = old(lctx).pcid_allocator_lock_map().dom();
                            &&& cpus.contains(cpu_id)
                            &&& (forall|held_cpu_id: CpuId|
                                #![trigger cpus.contains(held_cpu_id)]
                                cpus.contains(held_cpu_id) ==> {
                                    &&& index_valid(NUM_CPUS, held_cpu_id)
                                    &&& old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().owning_container == thread.owning_container
                                    &&& old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().current_process is None || old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().current_process == Some(thread.owning_proc)
                                })
                            &&& old(lctx).page_lock_map().dom().is_empty()
                            &&& old(lctx).process_lock_map().dom() =~= set![thread.owning_proc]
                            &&& old(lctx).thread_lock_map().dom().is_empty()
                            &&& old(lctx).endpoint_lock_map().dom().is_empty()
                            &&& old(lctx).scheduler_lock_map().dom().is_empty()
                            &&& old(lctx).cpu_set_lock_map().dom().is_empty()
                            &&& old(lctx).pagetable_lock_map().dom().is_empty()
                            &&& old(lctx).iommu_table_lock_map().dom().is_empty()
                            &&& old(lctx).allocator_quota_4k_lock_map().dom().is_empty()
                            &&& old(lctx).allocator_cache_4k_lock_map().dom().is_empty()
                            &&& old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty()
                            &&& old(lctx).allocator_quota_2m_lock_map().dom().is_empty()
                            &&& old(lctx).allocator_cache_2m_lock_map().dom().is_empty()
                            &&& old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty()
                            &&& old(lctx).allocator_quota_1g_lock_map().dom().is_empty()
                            &&& old(lctx).allocator_cache_1g_lock_map().dom().is_empty()
                            &&& old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty()
                            &&& old(lctx).pcid_needflush_lock_map().dom().is_empty()
                            &&& containers.subset_of(set![thread.owning_container])
                            &&& pcid_allocators.subset_of(set![old(self).ctn_mp.spec_index(thread.owning_container).view_rodata().view().pcid_allocator])
                            &&& (!pcid_allocators.is_empty() ==> containers.contains(thread.owning_container))
                        },
                        ThreadState::SCHEDULED => {
                            let cpu_id = old(lctx).cpu_id();
                            let cpu = old(self).cpu_arr.spec_index(cpu_id).view().view().view();
                            let scheduler_ptr = old(self).ctn_mp.spec_index(thread.owning_container).view_rodata().view().scheduler;
                            &&& index_valid(NUM_CPUS, cpu_id)
                            &&& cpus =~= set![cpu_id]
                            &&& typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write)
                            &&& cpu.owning_container == thread.owning_container
                            &&& old(lctx).scheduler_lock_map().dom() =~= set![scheduler_ptr]
                            &&& typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), scheduler_ptr, TypedLockMode::Write)
                            &&& old(lctx).process_lock_map().dom() =~= match cpu.current_process { Some(ptr) => set![ptr], None => Set::empty() }
                            &&& old(lctx).thread_lock_map().dom() =~= match cpu.current_thread { Some(ptr) => set![ptr], None => Set::empty() }
                            &&& old(lctx).page_lock_map().dom().is_empty()
                            &&& old(lctx).container_lock_map().dom().is_empty()
                            &&& old(lctx).endpoint_lock_map().dom().is_empty()
                            &&& old(lctx).cpu_set_lock_map().dom().is_empty()
                            &&& old(lctx).pcid_allocator_lock_map().dom().is_empty()
                            &&& old(lctx).pagetable_lock_map().dom().is_empty()
                            &&& old(lctx).iommu_table_lock_map().dom().is_empty()
                            &&& old(lctx).allocator_quota_4k_lock_map().dom().is_empty()
                            &&& old(lctx).allocator_cache_4k_lock_map().dom().is_empty()
                            &&& old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty()
                            &&& old(lctx).allocator_quota_2m_lock_map().dom().is_empty()
                            &&& old(lctx).allocator_cache_2m_lock_map().dom().is_empty()
                            &&& old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty()
                            &&& old(lctx).allocator_quota_1g_lock_map().dom().is_empty()
                            &&& old(lctx).allocator_cache_1g_lock_map().dom().is_empty()
                            &&& old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty()
                            &&& old(lctx).pcid_needflush_lock_map().dom().is_empty()
                        },
                        _ => {
                            &&& thread.state.is_endpoint_waiting()
                            &&& thread.blocking_endpoint_ptr is Some
                            &&& old(lctx).process_lock_map().dom().len() == 1
                            &&& !old(lctx).thread_lock_map().dom().is_empty()
                            &&& forall|current_thread_ptr: RwLockThreadPtr|
                                #![trigger old(lctx).thread_lock_map().dom().contains(current_thread_ptr)]
                                old(lctx).thread_lock_map().dom().contains(current_thread_ptr) ==> {
                                    let current_thread = old(self).thr_mp.spec_index(current_thread_ptr).view();
                                    &&& current_thread_ptr != thread_ptr
                                    &&& current_thread.state is RUNNING
                                    &&& cpus.contains(current_thread.state->RUNNING_cpu_id)
                                    &&& (forall|held_cpu_id: CpuId|
                                        #![trigger cpus.contains(held_cpu_id)]
                                        cpus.contains(held_cpu_id) ==> {
                                            &&& index_valid(NUM_CPUS, held_cpu_id)
                                            &&& old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().owning_container == current_thread.owning_container
                                        })
                                    &&& old(lctx).page_lock_map().dom().is_empty()
                                    &&& old(lctx).container_lock_map().dom().is_empty()
                                    &&& old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr]
                                    &&& old(lctx).endpoint_lock_map().dom() =~= set![thread.blocking_endpoint_ptr->Some_0]
                                    &&& old(lctx).scheduler_lock_map().dom().is_empty()
                                    &&& old(lctx).pcid_allocator_lock_map().dom().is_empty()
                                    &&& old(lctx).cpu_set_lock_map().dom().is_empty()
                                    &&& old(lctx).pagetable_lock_map().dom().is_empty()
                                    &&& old(lctx).iommu_table_lock_map().dom().is_empty()
                                    &&& old(lctx).allocator_quota_4k_lock_map().dom().is_empty()
                                    &&& old(lctx).allocator_cache_4k_lock_map().dom().is_empty()
                                    &&& old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty()
                                    &&& old(lctx).allocator_quota_2m_lock_map().dom().is_empty()
                                    &&& old(lctx).allocator_cache_2m_lock_map().dom().is_empty()
                                    &&& old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty()
                                    &&& old(lctx).allocator_quota_1g_lock_map().dom().is_empty()
                                    &&& old(lctx).allocator_cache_1g_lock_map().dom().is_empty()
                                    &&& old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty()
                                    &&& old(lctx).pcid_needflush_lock_map().dom().is_empty()
                                }
                        },
                    }
                },
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                *final(self) == (KernelK { thr_mp: final(self).thr_mp, ..*old(self) }),
                final(self).thr_mp.unchanged_except(&old(self).thr_mp, thread_ptr),
                final(self).thr_mp.perms_wf(),
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                old(lctx).held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR) && old(self).thr_mp.lock_id_by_key(thread_ptr).major < PAGE_TABLE_LOCK_MAJOR ==> final(lctx).held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR),
                old(lctx).held_lock_majors_lt(PCID_NEEDFLUSH_LOCK_MAJOR) ==> final(lctx).held_lock_majors_lt(PCID_NEEDFLUSH_LOCK_MAJOR),
                old(lctx).held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR) && old(self).thr_mp.lock_id_by_key(thread_ptr).major < PAGE_TABLE_LOCK_MAJOR ==> final(lctx).held_lock_majors_lt(SCHEDULER_LOCK_MAJOR),
                ret is None ==> { &&& old(self).thr_mp.spec_index(thread_ptr).being_killed() &&& final(self).thr_mp.spec_index(thread_ptr) == old(self).thr_mp.spec_index(thread_ptr) &&& final(lctx).lock_id_set() =~= old(lctx).lock_id_set() &&& typed_lock_maps_unchanged(old(lctx), final(lctx)) },
                ret is Some ==> {
                    &&& old(self).thr_mp.spec_index(thread_ptr).being_killed() == false
                    &&& wlock_ensures(old(self).thr_mp.spec_index(thread_ptr), final(self).thr_mp.spec_index(thread_ptr), old(self).thr_mp.lock_id_by_key(thread_ptr), final(lctx), ret.unwrap().view())
                    &&& final(self).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean()
                    &&& final(self).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean()
                    &&& final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(self).thr_mp.lock_id_by_key(thread_ptr), KernelObjId::Thread(thread_ptr)))
                    &&& typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Thread(thread_ptr), TypedHeldLock { lock_id: final(self).thr_mp.lock_id_by_key(thread_ptr), mode: TypedLockMode::Write })
                },
        {
            proof {
                thread_perms_wf_at(old(self).thr_mp, thread_ptr);
                let target_thread =
                    old(self).thr_mp.spec_index(thread_ptr).view();
                match target_thread.state {
                    ThreadState::RUNNING { cpu_id } => {
                        assert(old(lctx).lock_id_acyclic(
                            old(self).thr_mp.lock_id_by_key(thread_ptr),
                        )) by {
                            reveal(lock_id_set_aligned);
                            reveal(LockedArray::typed_lock_map_aligned);
                            reveal(LockedMap::typed_lock_map_aligned);
                            reveal(container_cpu_wf);
                            reveal(process_cpu_wf);
                            reveal(container_process_wf);
                            reveal(container_pcid_allocator_wf);
                            reveal(process_thread_wf);
                        };
                    },
                    ThreadState::SCHEDULED => {
                        assert(old(self).thr_mp.lock_id_by_key(thread_ptr)
                            .major == THREAD_SCHEDULED_LOCK_MAJOR);
                        assert(old(self).thr_mp.lock_id_by_key(thread_ptr)
                            .process == LockOwnerId::NotApp);
                        assert(old(lctx).held_lock_majors_lt(
                            THREAD_SCHEDULED_LOCK_MAJOR,
                        )) by {
                            reveal(lock_id_set_aligned);
                            reveal(LockedArray::typed_lock_map_aligned);
                            reveal(LockedMap::typed_lock_map_aligned);
                            reveal(thread_cpu_wf);
                            reveal(cpu_array_wf);
                        };
                        assert(old(lctx).lock_id_acyclic(
                            old(self).thr_mp.lock_id_by_key(thread_ptr),
                        )) by {
                            reveal(lock_id_set_aligned);
                            reveal(LockedArray::typed_lock_map_aligned);
                            reveal(LockedMap::typed_lock_map_aligned);
                            reveal(container_cpu_wf);
                            reveal(container_process_wf);
                            reveal(thread_cpu_wf);
                            reveal(process_thread_wf);
                            reveal(cpu_array_wf);
                        };
                    },
                    _ => {
                        assert(old(lctx).lock_id_acyclic(
                            old(self).thr_mp.lock_id_by_key(thread_ptr),
                        )) by {
                            reveal(lock_id_set_aligned);
                            reveal(LockedArray::typed_lock_map_aligned);
                            reveal(LockedMap::typed_lock_map_aligned);
                        };
                    },
                }
            }
            proof {
                assert(!old(self).thr_mp.spec_index(thread_ptr)
                    .wlocked_by_thread(old(lctx).thread_id())) by {
                    if old(self).thr_mp.spec_index(thread_ptr)
                        .wlocked_by_thread(old(lctx).thread_id())
                    {
                        assert(typed_lock_map_contains_mode(
                            old(lctx).thread_lock_map(),
                            thread_ptr,
                            TypedLockMode::Write,
                        )) by {
                            reveal(LockedMap::typed_lock_map_aligned);
                        };
                    }
                };
                assert(!old(self).thr_mp.spec_index(thread_ptr)
                    .wlocked_by(&*old(lctx)));
            }
            assert(wlock_requires(self.thr_mp.spec_index(thread_ptr), &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            let res = self.thr_mp.wlock_unless_killed(thread_ptr, Tracked(&mut *lctx), Ghost(KernelObjId::Thread(thread_ptr)));
            proof {
                assert(thread_perms_wf(self.thr_mp)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); };
                assert(thread_invariant_fields_unchanged(old(self).thr_mp, self.thr_mp)) by { thread_lock_op_preserves_invariant_fields(old(self).thr_mp, self.thr_mp, thread_ptr); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.memory_management_inv()) by { memory_management_inv_preserved_for_thread_invariant_fields(*old(self), *self); };
                assert(self.process_management_inv()) by { process_management_inv_preserved_for_thread_invariant_fields(*old(self), *self); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
                assert(old(lctx).held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR) && old(self).thr_mp.lock_id_by_key(thread_ptr).major < PAGE_TABLE_LOCK_MAJOR ==> lctx.held_lock_majors_lt(SCHEDULER_LOCK_MAJOR)) by { assert(PAGE_TABLE_LOCK_MAJOR < SCHEDULER_LOCK_MAJOR) by (compute); };
                if res.is_some() {
                    assert(
                        self.thr_mp.spec_index(thread_ptr).view()
                            .free_quota_pending_clean()
                        && self.thr_mp.spec_index(thread_ptr).view()
                            .temp_alloc_clean()
                    ) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); };
                }
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                };
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
                old(self).thr_mp.dom().contains(thread_ptr),
                old(self).thr_mp.spec_index(thread_ptr).being_killed() == false,
                !(old(self).thr_mp.spec_index(thread_ptr).view().state is IPC_ENDPOINT_TRANSIT),
                typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id() == old(self).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
                // The pending-clean protocol: pendings must be flushed before
                // releasing the write lock (see doc comment above).
                old(self).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
                old(self).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                // ---- Every held lock still matches lctx (thread now released) ----
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                *final(self) == (KernelK { thr_mp: final(self).thr_mp, ..*old(self) }),
                // ---- thread_map: only the targeted entry's lock state changed (now unlocked) ----
                final(self).thr_mp.unchanged_except(&old(self).thr_mp, thread_ptr),
                final(self).thr_mp.perms_wf(),
                final(self).thr_mp.spec_index(thread_ptr).locking_thread() is None,
                !final(self).thr_mp.spec_index(thread_ptr).locked(),
                final(self).thr_mp.lock_id_by_key(thread_ptr) == old(self).thr_mp.lock_id_by_key(thread_ptr),
                wunlock_ensures(old(self).thr_mp.spec_index(thread_ptr), final(self).thr_mp.spec_index(thread_ptr)),
                // ---- LocalContext: lock dropped; thread preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` transitions it Acquire -> Release (same trap as
                // the NOTE on wunlock_process / LockedArray::wunlock).
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,
                final(lctx).lock_id_set() == old(lctx).lock_id_set().remove((old(self).thr_mp.lock_id_by_key(thread_ptr), KernelObjId::Thread(thread_ptr))),
                typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Thread(thread_ptr)),
                unlock_ensures(old(lctx), final(lctx), KernelObjId::Thread(thread_ptr), old(self).thr_mp.lock_id_by_key(thread_ptr)),
                forall|held: HeldLock|
                    #![trigger final(lctx).lock_id_set().contains((held.0, held.1))]
                    held.1 != KernelObjId::Thread(thread_ptr)
                    ==> final(lctx).lock_id_set().contains((held.0, held.1))
                        == old(lctx).lock_id_set().contains((held.0, held.1)),
        {
            proof {
                assert({
                    &&& old(self).thr_mp.perms_wf()
                    &&& old(self).thr_mp.spec_index(thread_ptr).inv()
                }) by { reveal(thread_perms_wf); };
                assert(old(lctx).lock_entry_contains(old(self).thr_mp.lock_id_by_key(thread_ptr), KernelObjId::Thread(thread_ptr))) by { reveal(LockedMap::typed_lock_map_aligned); };
                assert(old(lctx).lock_id_set().contains((old(self).thr_mp.lock_id_by_key(thread_ptr), KernelObjId::Thread(thread_ptr)))) by { reveal(lock_id_set_aligned); };
            }
            assert(self.thr_mp.spec_index(thread_ptr).wlocked_by(&*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            self.thr_mp.wunlock(thread_ptr, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::Thread(thread_ptr)));
            proof {
                assert(thread_perms_wf(self.thr_mp)) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); };
                assert(thread_invariant_fields_unchanged(old(self).thr_mp, self.thr_mp)) by { thread_lock_op_preserves_invariant_fields(old(self).thr_mp, self.thr_mp, thread_ptr); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.memory_management_inv()) by { memory_management_inv_preserved_for_thread_invariant_fields(*old(self), *self); };
                assert(self.process_management_inv()) by { process_management_inv_preserved_for_thread_invariant_fields(*old(self), *self); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                };
            }
        }
}
} // verus!
