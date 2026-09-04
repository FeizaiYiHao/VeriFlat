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
                wlock_requires(old(self).ep_mp.spec_index(endpoint_ptr), old(lctx)),
                old(lctx).kernel_view_locking_state() is Acquire,
                endpoint_lock_acquire_scope(old(self), old(lctx)),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                final(self).inv(),
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                final(self).pt_mp == old(self).pt_mp,
                final(self).it_mp == old(self).it_mp,
                final(self).irt == old(self).irt,
                final(self).pg_arr == old(self).pg_arr,
                final(self).cpu_arr == old(self).cpu_arr,
                final(self).cpu_tlb == old(self).cpu_tlb,
                final(self).iommu_tlb == old(self).iommu_tlb,
                final(self).rt_ctn == old(self).rt_ctn,
                final(self).ctn_mp == old(self).ctn_mp,
                final(self).sched_mp == old(self).sched_mp,
                final(self).pcid_allc_mp == old(self).pcid_allc_mp,
                final(self).prc_mp == old(self).prc_mp,
                final(self).thr_mp == old(self).thr_mp,
                final(self).allc_4k_mp == old(self).allc_4k_mp,
                final(self).allc_2m_mp == old(self).allc_2m_mp,
                final(self).allc_1g_mp == old(self).allc_1g_mp,
                final(self).dflt_pt == old(self).dflt_pt,
                final(self).ep_mp.dom() == old(self).ep_mp.dom(),
                final(self).ep_mp.unchanged_except(&old(self).ep_mp, endpoint_ptr),
                endpoint_objects_unlocked(old(self).ep_mp, old(lctx).thread_id()) ==> endpoint_objects_unlocked_except(final(self).ep_mp, final(lctx).thread_id(), set![endpoint_ptr]),
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                wlock_ensures(old(self).ep_mp.spec_index(endpoint_ptr), final(self).ep_mp.spec_index(endpoint_ptr), old(self).ep_mp.lock_id_by_key(endpoint_ptr), final(lctx), ret.view()),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(self).ep_mp.lock_id_by_key(endpoint_ptr), KernelObjId::Endpoint(endpoint_ptr))),
                typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Endpoint(endpoint_ptr), TypedHeldLock { lock_id: final(self).ep_mp.lock_id_by_key(endpoint_ptr), mode: TypedLockMode::Write }),
                final(lctx).held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR),
                final(lctx).held_lock_majors_lt(SCHEDULER_LOCK_MAJOR),
                forall|cpus: Set<CpuId>, containers: Set<RwLockContainerPtr>, processes: Set<RwLockProcessPtr>, threads: Set<RwLockThreadPtr>, endpoints: Set<RwLockEndpointPtr>|
                    #![trigger old(lctx).base_lock_scope(cpus, containers, processes, threads, endpoints)]
                    old(lctx).base_lock_scope(cpus, containers, processes, threads, endpoints)
                    ==> final(lctx).base_lock_scope(cpus, containers, processes, threads, endpoints.insert(endpoint_ptr)),
        {
            proof {
                assert(old(self).ep_mp.perms_wf()) by { reveal(endpoint_perms_wf); };
                assert(old(lctx).held_lock_majors_lt(ENDPOINT_LOCK_MAJOR)) by { reveal(endpoint_lock_acquire_scope); reveal(LocalContext::base_lock_scope); reveal(LocalContext::object_lock_scope); reveal(LocalContext::held_lock_majors_lt); reveal(lock_id_set_aligned); reveal(typed_lock_maps_aligned); reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned); reveal(cpu_array_wf); reveal(container_perms_wf); reveal(pcid_allocator_perms_wf); reveal(process_perms_wf); reveal(thread_perms_wf); };
                assert(old(lctx).lock_id_acyclic(old(self).ep_mp.lock_id_by_key(endpoint_ptr))) by { reveal(LocalContext::lock_id_acyclic); reveal(LocalContext::held_lock_majors_lt); reveal(endpoint_perms_wf); };
            }
            let ret = self.ep_mp.wlock(endpoint_ptr, Tracked(&mut *lctx), Ghost(KernelObjId::Endpoint(endpoint_ptr)));
            proof {
                assert(endpoint_invariant_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { endpoint_lock_op_preserves_invariant_fields(old(self).ep_mp, self.ep_mp, endpoint_ptr); };
                assert(self.subsystems_inv()) by {
                    reveal(KernelK::default_pagetable_wf);
                    assert(endpoint_perms_wf(self.ep_mp)) by { lemma_no_change_imply_endpoint_perms_wf_forall(); };
                };
                assert(self.memory_management_inv()) by {
                    assert(endpoint_pages_wf(self.ep_mp, self.pg_arr)) by { lemma_no_change_imply_endpoint_pages_wf_forall(); };
                };
                assert(self.process_management_inv()) by {
                    assert(container_endpoint_wf(self.ctn_mp, self.ep_mp)) by { lemma_no_change_imply_container_endpoint_wf_forall(); };
                    assert(thread_endpoint_ref_counter_wf(self.thr_mp, self.ep_mp)) by { lemma_no_change_imply_thread_endpoint_ref_counter_wf_forall(); };
                    assert(thread_endpoint_queue_wf(self.thr_mp, self.ep_mp)) by { lemma_no_change_imply_thread_endpoint_queue_wf_forall(); };
                    assert(container_thread_endpoint_wf(self.ctn_mp, self.thr_mp, self.ep_mp)) by { lemma_no_change_imply_container_thread_endpoint_wf_forall(); };
                };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
                assert(lctx.held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR)) by { reveal(LocalContext::held_lock_majors_lt); reveal(endpoint_perms_wf); assert(ENDPOINT_LOCK_MAJOR < PAGE_TABLE_LOCK_MAJOR) by (compute); broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different; };
                assert(lctx.held_lock_majors_lt(SCHEDULER_LOCK_MAJOR)) by { reveal(LocalContext::held_lock_majors_lt); reveal(endpoint_perms_wf); assert(ENDPOINT_LOCK_MAJOR < SCHEDULER_LOCK_MAJOR) by (compute); broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different; };
                broadcast use vstd::map::lemma_map_insert_domain;
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
                old(self).ep_mp.spec_index(endpoint_ptr).wlocked_by(old(lctx)),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id() == old(self).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                final(self).inv(),
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                final(self).pt_mp == old(self).pt_mp,
                final(self).it_mp == old(self).it_mp,
                final(self).irt == old(self).irt,
                final(self).pg_arr == old(self).pg_arr,
                final(self).cpu_arr == old(self).cpu_arr,
                final(self).cpu_tlb == old(self).cpu_tlb,
                final(self).iommu_tlb == old(self).iommu_tlb,
                final(self).rt_ctn == old(self).rt_ctn,
                final(self).ctn_mp == old(self).ctn_mp,
                final(self).sched_mp == old(self).sched_mp,
                final(self).pcid_allc_mp == old(self).pcid_allc_mp,
                final(self).prc_mp == old(self).prc_mp,
                final(self).thr_mp == old(self).thr_mp,
                final(self).allc_4k_mp == old(self).allc_4k_mp,
                final(self).allc_2m_mp == old(self).allc_2m_mp,
                final(self).allc_1g_mp == old(self).allc_1g_mp,
                final(self).dflt_pt == old(self).dflt_pt,
                final(self).ep_mp.dom() == old(self).ep_mp.dom(),
                final(self).ep_mp.unchanged_except(&old(self).ep_mp, endpoint_ptr),
                final(self).ep_mp.spec_index(endpoint_ptr).locking_thread() is None,
                final(self).ep_mp.lock_id_by_key(endpoint_ptr) == old(self).ep_mp.lock_id_by_key(endpoint_ptr),
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,
                wunlock_ensures(old(self).ep_mp.spec_index(endpoint_ptr), final(self).ep_mp.spec_index(endpoint_ptr)),
                endpoint_objects_unlocked_except(old(self).ep_mp, old(lctx).thread_id(), set![endpoint_ptr]) ==> endpoint_objects_unlocked(final(self).ep_mp, final(lctx).thread_id()),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().remove((old(self).ep_mp.lock_id_by_key(endpoint_ptr), KernelObjId::Endpoint(endpoint_ptr))),
                typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Endpoint(endpoint_ptr)),
        {
            proof {
                assert({
                    &&& old(self).ep_mp.perms_wf()
                    &&& old(self).ep_mp.spec_index(endpoint_ptr).inv()
                }) by { reveal(endpoint_perms_wf); reveal(endpoints_inv); };
                assert(old(lctx).lock_entry_contains(old(self).ep_mp.lock_id_by_key(endpoint_ptr), KernelObjId::Endpoint(endpoint_ptr))) by { reveal(LockedMap::typed_lock_map_aligned); };
                assert(old(lctx).lock_id_set().contains((old(self).ep_mp.lock_id_by_key(endpoint_ptr), KernelObjId::Endpoint(endpoint_ptr)))) by { reveal(lock_id_set_aligned); };
            }
            self.ep_mp.wunlock(endpoint_ptr, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::Endpoint(endpoint_ptr)));
            proof {
                assert(endpoint_invariant_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { endpoint_lock_op_preserves_invariant_fields(old(self).ep_mp, self.ep_mp, endpoint_ptr); };
                assert(self.subsystems_inv()) by {
                    reveal(KernelK::default_pagetable_wf);
                    assert(endpoint_perms_wf(self.ep_mp)) by { lemma_no_change_imply_endpoint_perms_wf_forall(); };
                };
                assert(self.memory_management_inv()) by {
                    assert(endpoint_pages_wf(self.ep_mp, self.pg_arr)) by { lemma_no_change_imply_endpoint_pages_wf_forall(); };
                };
                assert(self.process_management_inv()) by {
                    assert(container_endpoint_wf(self.ctn_mp, self.ep_mp)) by { lemma_no_change_imply_container_endpoint_wf_forall(); };
                    assert(thread_endpoint_ref_counter_wf(self.thr_mp, self.ep_mp)) by { lemma_no_change_imply_thread_endpoint_ref_counter_wf_forall(); };
                    assert(thread_endpoint_queue_wf(self.thr_mp, self.ep_mp)) by { lemma_no_change_imply_thread_endpoint_queue_wf_forall(); };
                    assert(container_thread_endpoint_wf(self.ctn_mp, self.thr_mp, self.ep_mp)) by { lemma_no_change_imply_container_thread_endpoint_wf_forall(); };
                };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            }
        }

}
} // verus!
