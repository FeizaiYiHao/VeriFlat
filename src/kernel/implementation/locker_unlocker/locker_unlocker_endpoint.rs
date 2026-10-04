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
                old(self).ep_mp.dom().contains(endpoint_ptr),
                !old(lctx).endpoint_lock_map().dom().contains(endpoint_ptr),
                old(lctx).kernel_view_locking_state() is Acquire,
                {
                    let cpus = old(lctx).cpu_lock_map().dom();
                    let processes = old(lctx).process_lock_map().dom();
                    &&& !cpus.is_empty()
                    &&& (forall|held_cpu_id: CpuId|
                        #![trigger cpus.contains(held_cpu_id)]
                        cpus.contains(held_cpu_id) ==> {
                            &&& index_valid(NUM_CPUS, held_cpu_id)
                            &&& !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off)
                        })
                    &&& processes.len() == 1
                    &&& forall|cpu_id: CpuId|
                        #![trigger old(lctx).cpu_lock_map().dom().contains(cpu_id)]
                        cpus.contains(cpu_id) ==> {
                            let cpu = old(self).cpu_arr.spec_index(cpu_id).view().view();
                            let current_thread_ptr = cpu.current_thread()->Some_0;
                            let threads = old(lctx).thread_lock_map().dom();
                            &&& cpu.current_thread() is Some
                            &&& old(self).thr_mp.dom().contains(current_thread_ptr)
                            &&& old(self).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id })
                            &&& {
                                ||| {
                                    &&& old(lctx).page_lock_map().dom().is_empty()
                                    &&& old(lctx).cpu_lock_map().dom() =~= set![cpu_id]
                                    &&& old(lctx).container_lock_map().dom().is_empty()
                                    &&& old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr]
                                    &&& old(lctx).endpoint_lock_map().dom().is_empty()
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
                                ||| {
                                    &&& cpu.current_process() is Some
                                    &&& old(lctx).page_lock_map().dom().is_empty()
                                    &&& old(lctx).cpu_lock_map().dom() =~= set![cpu_id]
                                    &&& old(lctx).container_lock_map().dom().is_empty()
                                    &&& old(lctx).process_lock_map().dom() =~= set![cpu.current_process()->Some_0]
                                    &&& old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr]
                                    &&& old(lctx).endpoint_lock_map().dom().is_empty()
                                    &&& old(lctx).scheduler_lock_map().dom().is_empty()
                                    &&& old(lctx).pcid_allocator_lock_map().dom() =~= set![old(self).ctn_mp.spec_index(cpu.owning_container()).view_rodata().view().pcid_allocator]
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
                                ||| {
                                    &&& old(lctx).page_lock_map().dom().is_empty()
                                    &&& old(lctx).cpu_lock_map().dom() =~= set![cpu_id]
                                    &&& old(lctx).container_lock_map().dom().is_empty()
                                    &&& old(lctx).endpoint_lock_map().dom().is_empty()
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
                                    &&& threads.contains(current_thread_ptr)
                                    &&& threads.len() == 2
                                    &&& forall|peer_thread_ptr: RwLockThreadPtr|
                                        #![trigger old(lctx).thread_lock_map().dom().contains(peer_thread_ptr)]
                                        threads.contains(peer_thread_ptr) && peer_thread_ptr != current_thread_ptr
                                        ==> old(self).thr_mp.spec_index(peer_thread_ptr).view().state is IPC_ENDPOINT_TRANSIT
                                }
                            }
                        }
                },
                typed_lock_maps_aligned(old(self), old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                final(self).inv(),
                kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
                kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
                kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
                typed_lock_maps_aligned(final(self), final(lctx)),
                *final(self) == (KernelK { ep_mp: final(self).ep_mp, ..*old(self) }),
                final(self).ep_mp.unchanged_except(&old(self).ep_mp, endpoint_ptr),
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                wlock_ensures(old(self).ep_mp.spec_index(endpoint_ptr), final(self).ep_mp.spec_index(endpoint_ptr), old(self).ep_mp.lock_id_by_key(endpoint_ptr), final(lctx), ret.view()),
                typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Endpoint(endpoint_ptr), TypedHeldLock { lock_id: final(self).ep_mp.lock_id_by_key(endpoint_ptr), mode: TypedLockMode::Write }),
        {
            proof {
                endpoint_perms_wf_at(old(self).ep_mp, endpoint_ptr);
                assert(old(lctx).lock_id_acyclic(old(self).ep_mp.lock_id_by_key(endpoint_ptr))) by { reveal(LocalContext::lock_id_acyclic); reveal(UnLockedMap::typed_flag_lock_map_aligned); reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned); reveal(cpu_array_wf); reveal(container_perms_wf); reveal(pcid_allocator_perms_wf); reveal(process_perms_wf); reveal(thread_perms_wf); reveal(thread_cpu_wf); reveal(endpoint_perms_wf); };
                assert(!old(self).ep_mp.spec_index(endpoint_ptr).locked_by_thread(old(lctx).thread_id())) by {
                    if old(self).ep_mp.spec_index(endpoint_ptr).locked_by_thread(old(lctx).thread_id()) {
                        assert(old(lctx).endpoint_lock_map().dom().contains(endpoint_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
                    }
                };
            }
            assert(wlock_requires(self.ep_mp.spec_index(endpoint_ptr), &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            let ret = self.ep_mp.wlock(endpoint_ptr, Tracked(&mut *lctx), Ghost(KernelObjId::Endpoint(endpoint_ptr)));
            proof {
                assert(endpoint_invariant_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { endpoint_lock_op_preserves_invariant_fields(old(self).ep_mp, self.ep_mp, endpoint_ptr); };
                assert(self.subsystems_inv()) by {
                    reveal(KernelK::default_pagetable_wf);
                    lemma_endpoint_perms_wf_preserved_for_lock_op_forall();
                };
                assert(self.memory_management_inv()) by { lemma_endpoint_pages_wf_preserved_for_endpoint_invariant_fields_forall(); };
                assert(self.process_management_inv()) by {
                    lemma_container_endpoint_wf_preserved_for_endpoint_invariant_fields_forall();
                    lemma_thread_endpoint_ref_counter_wf_preserved_for_endpoint_invariant_fields_forall();
                    lemma_thread_endpoint_queue_wf_preserved_for_endpoint_invariant_fields_forall();
                    lemma_container_thread_endpoint_wf_preserved_for_endpoint_invariant_fields_forall();
                };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
                assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
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
                old(self).ep_mp.dom().contains(endpoint_ptr),
                typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id() == old(self).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
                typed_lock_maps_aligned(old(self), old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                final(self).inv(),
                kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
                kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
                kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
                typed_lock_maps_aligned(final(self), final(lctx)),
                *final(self) == (KernelK { ep_mp: final(self).ep_mp, ..*old(self) }),
                final(self).ep_mp.unchanged_except(&old(self).ep_mp, endpoint_ptr),
                final(self).ep_mp.lock_id_by_key(endpoint_ptr) == old(self).ep_mp.lock_id_by_key(endpoint_ptr),
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,
                wunlock_ensures(old(self).ep_mp.spec_index(endpoint_ptr), final(self).ep_mp.spec_index(endpoint_ptr)),
                typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Endpoint(endpoint_ptr)),
        {
            proof {
                assert({
                    &&& old(self).ep_mp.perms_wf()
                    &&& old(self).ep_mp.spec_index(endpoint_ptr).inv()
                }) by { reveal(endpoint_perms_wf); };
                assert(old(lctx).lock_entry_contains(old(self).ep_mp.lock_id_by_key(endpoint_ptr), KernelObjId::Endpoint(endpoint_ptr))) by { reveal(LockedMap::typed_lock_map_aligned); };
            }
            assert(self.ep_mp.spec_index(endpoint_ptr).wlocked_by(&*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            self.ep_mp.wunlock(endpoint_ptr, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::Endpoint(endpoint_ptr)));
            proof {
                assert(endpoint_invariant_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { endpoint_lock_op_preserves_invariant_fields(old(self).ep_mp, self.ep_mp, endpoint_ptr); };
                assert(self.subsystems_inv()) by {
                    reveal(KernelK::default_pagetable_wf);
                    lemma_endpoint_perms_wf_preserved_for_lock_op_forall();
                };
                assert(self.memory_management_inv()) by { lemma_endpoint_pages_wf_preserved_for_endpoint_invariant_fields_forall(); };
                assert(self.process_management_inv()) by {
                    lemma_container_endpoint_wf_preserved_for_endpoint_invariant_fields_forall();
                    lemma_thread_endpoint_ref_counter_wf_preserved_for_endpoint_invariant_fields_forall();
                    lemma_thread_endpoint_queue_wf_preserved_for_endpoint_invariant_fields_forall();
                    lemma_container_thread_endpoint_wf_preserved_for_endpoint_invariant_fields_forall();
                };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
                assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
            }
        }
}
} // verus!
