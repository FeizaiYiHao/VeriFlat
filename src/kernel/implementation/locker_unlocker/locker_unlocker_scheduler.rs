use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
        pub fn wlock_scheduler(
            &mut self,
            scheduler_ptr: RwLockSchedulerPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Tracked<LockPerm>)
            requires
                old(self).inv(),
                old(self).sched_mp.dom().contains(scheduler_ptr),
                old(lctx).kernel_view_locking_state() is Acquire,
                wlock_requires(old(self).sched_mp.spec_index(scheduler_ptr), old(lctx)),
                old(lctx).held_lock_majors_lt(SCHEDULER_LOCK_MAJOR),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                // ---- Every held lock still matches lctx (scheduler now locked) ----
                // ---- Dynamic lock ids remain aligned ----
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                // ---- Field framing: only scheduler_map's lock state moves ----
                final(self).pt_mp     == old(self).pt_mp,
                final(self).it_mp     == old(self).it_mp,
                final(self).irt     == old(self).irt,
                final(self).pg_arr        == old(self).pg_arr,
                final(self).cpu_arr         == old(self).cpu_arr,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).iommu_tlb           == old(self).iommu_tlb,
                final(self).rt_ctn    == old(self).rt_ctn,
                final(self).ctn_mp     == old(self).ctn_mp,
                final(self).pcid_allc_mp == old(self).pcid_allc_mp,
                final(self).prc_mp       == old(self).prc_mp,
                final(self).thr_mp        == old(self).thr_mp,
                final(self).ep_mp      == old(self).ep_mp,
                final(self).allc_4k_mp  == old(self).allc_4k_mp,
                final(self).allc_2m_mp  == old(self).allc_2m_mp,
                final(self).allc_1g_mp  == old(self).allc_1g_mp,
                final(self).dflt_pt == old(self).dflt_pt,
                // ---- scheduler_map: dom unchanged; only the targeted entry's lock state changed ----
                final(self).sched_mp.dom() == old(self).sched_mp.dom(),
                final(self).sched_mp.unchanged_except(&old(self).sched_mp, scheduler_ptr),
                scheduler_objects_unlocked(old(self).sched_mp, old(lctx).thread_id()) ==> scheduler_objects_unlocked_except(final(self).sched_mp, final(lctx).thread_id(), set![scheduler_ptr]),
                // ---- LocalContext: phases preserved ----
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                // ---- The lock perm + lock ensures (forwarded from LockedMap::wlock) ----
                wlock_ensures(old(self).sched_mp.spec_index(scheduler_ptr), final(self).sched_mp.spec_index(scheduler_ptr), LockId{ container: old(self).sched_mp.spec_index(scheduler_ptr).container_depth(), process: old(self).sched_mp.spec_index(scheduler_ptr).process_depth(), major: old(self).sched_mp.spec_index(scheduler_ptr).view().current_lock_major(), minor: scheduler_ptr, }, final(lctx), ret.view()),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(self).sched_mp.lock_id_by_key(scheduler_ptr), KernelObjId::Scheduler(scheduler_ptr))),
                typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Scheduler(scheduler_ptr), TypedHeldLock { lock_id: final(self).sched_mp.lock_id_by_key(scheduler_ptr), mode: TypedLockMode::Write }),
                typed_lock_map_contains_mode(final(lctx).scheduler_lock_map(), scheduler_ptr, TypedLockMode::Write),
                final(lctx).lock_entry_contains(final(self).sched_mp.lock_id_by_key(scheduler_ptr), KernelObjId::Scheduler(scheduler_ptr)),
                final(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
                forall|pages: Set<PageIndex>, cpus: Set<CpuId>, containers: Set<RwLockContainerPtr>, processes: Set<RwLockProcessPtr>, threads: Set<RwLockThreadPtr>, endpoints: Set<RwLockEndpointPtr>, schedulers: Set<RwLockSchedulerPtr>, pcid_allocators: Set<RwLockPcidAllocatorPtr>, pagetables: Set<RwLockPageTableRoot>, iommu_tables: Set<RwLockPageTableRoot>|
                    #![trigger old(lctx).object_lock_scope(pages, cpus, containers, processes, threads, endpoints, schedulers, pcid_allocators, pagetables, iommu_tables)]
                    old(lctx).object_lock_scope(pages, cpus, containers, processes, threads, endpoints, schedulers, pcid_allocators, pagetables, iommu_tables)
                    ==> final(lctx).object_lock_scope(pages, cpus, containers, processes, threads, endpoints, schedulers.insert(scheduler_ptr), pcid_allocators, pagetables, iommu_tables),
                forall|cpus: Set<CpuId>, containers: Set<RwLockContainerPtr>, processes: Set<RwLockProcessPtr>, threads: Set<RwLockThreadPtr>, endpoints: Set<RwLockEndpointPtr>|
                    #![trigger old(lctx).base_lock_scope(cpus, containers, processes, threads, endpoints)]
                    old(lctx).base_lock_scope(cpus, containers, processes, threads, endpoints)
                    ==> final(lctx).object_lock_scope(Set::empty(), cpus, containers, processes, threads, endpoints, set![scheduler_ptr], Set::empty(), Set::empty(), Set::empty()),
        {
            proof {
                assert(old(self).sched_mp.perms_wf()) by { reveal(scheduler_perms_wf); };
                assert(old(lctx).lock_id_acyclic(LockId{ container: old(self).sched_mp.spec_index(scheduler_ptr).container_depth(), process: old(self).sched_mp.spec_index(scheduler_ptr).process_depth(), major: old(self).sched_mp.spec_index(scheduler_ptr).view().current_lock_major(), minor: scheduler_ptr, })) by { reveal(LocalContext::lock_id_acyclic); reveal(LocalContext::held_lock_majors_lt); reveal(scheduler_perms_wf); };
            }
            let ret = self.sched_mp.wlock(scheduler_ptr, Tracked(&mut *lctx), Ghost(KernelObjId::Scheduler(scheduler_ptr)));
            proof {
                assert(scheduler_perms_wf(self.sched_mp)) by { reveal(scheduler_perms_wf); };
                assert(scheduler_invariant_fields_unchanged(old(self).sched_mp, self.sched_mp)) by { scheduler_lock_op_preserves_invariant_fields(old(self).sched_mp, self.sched_mp, scheduler_ptr); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.process_management_inv()) by {
                    assert(container_scheduler_wf(self.ctn_mp, self.sched_mp)) by { reveal(container_scheduler_wf); };
                    assert(container_thread_scheduler_wf(self.ctn_mp, self.thr_mp, self.sched_mp)) by { reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf); };
                };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
                assert(lctx.lock_entry_contains(self.sched_mp.lock_id_by_key(scheduler_ptr), KernelObjId::Scheduler(scheduler_ptr))) by { reveal(typed_lock_maps_inserted); };
                assert(lctx.held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR)) by { reveal(LocalContext::held_lock_majors_lt); reveal(scheduler_perms_wf); assert(SCHEDULER_LOCK_MAJOR < ALLOCATOR_CACHE_MAJOR) by (compute); broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different; };
                reveal(LocalContext::base_lock_scope);
                reveal(LocalContext::object_lock_scope);
                broadcast use vstd::map::lemma_map_insert_domain;
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
                old(self).sched_mp.dom().contains(scheduler_ptr),
                old(self).sched_mp.spec_index(scheduler_ptr).wlocked_by(old(lctx)),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id() == old(self).sched_mp.spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
                typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), scheduler_ptr, TypedLockMode::Write),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                // ---- Every held lock still matches lctx (scheduler now released) ----
                // ---- Dynamic lock ids remain aligned ----
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                // ---- Field framing: only scheduler_map's lock state moves ----
                final(self).pt_mp     == old(self).pt_mp,
                final(self).it_mp     == old(self).it_mp,
                final(self).irt     == old(self).irt,
                final(self).pg_arr        == old(self).pg_arr,
                final(self).cpu_arr         == old(self).cpu_arr,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).iommu_tlb           == old(self).iommu_tlb,
                final(self).rt_ctn    == old(self).rt_ctn,
                final(self).ctn_mp     == old(self).ctn_mp,
                final(self).pcid_allc_mp == old(self).pcid_allc_mp,
                final(self).prc_mp       == old(self).prc_mp,
                final(self).thr_mp        == old(self).thr_mp,
                final(self).ep_mp      == old(self).ep_mp,
                final(self).allc_4k_mp  == old(self).allc_4k_mp,
                final(self).allc_2m_mp  == old(self).allc_2m_mp,
                final(self).allc_1g_mp  == old(self).allc_1g_mp,
                final(self).dflt_pt == old(self).dflt_pt,
                // ---- scheduler_map: dom unchanged; only the targeted entry's lock state changed (now unlocked) ----
                final(self).sched_mp.dom() == old(self).sched_mp.dom(),
                final(self).sched_mp.unchanged_except(&old(self).sched_mp, scheduler_ptr),
                final(self).sched_mp.spec_index(scheduler_ptr).locking_thread() is None,
                !final(self).sched_mp.spec_index(scheduler_ptr).locked(),
                final(self).sched_mp.lock_id_by_key(scheduler_ptr) == old(self).sched_mp.lock_id_by_key(scheduler_ptr),
                // ---- LocalContext: lock dropped; thread preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` flips it Acquire → Release (same trap as the
                // `LockedArray::wunlock` NOTE).
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,
                // ---- wunlock ensures (forwarded from LockedMap::wunlock) ----
                wunlock_ensures(old(self).sched_mp.spec_index(scheduler_ptr), final(self).sched_mp.spec_index(scheduler_ptr)),
                scheduler_objects_unlocked_except(old(self).sched_mp, old(lctx).thread_id(), set![scheduler_ptr]) ==> scheduler_objects_unlocked(final(self).sched_mp, final(lctx).thread_id()),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().remove((old(self).sched_mp.lock_id_by_key(scheduler_ptr), KernelObjId::Scheduler(scheduler_ptr))),
                typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Scheduler(scheduler_ptr)),
                forall|pages: Set<PageIndex>, cpus: Set<CpuId>, containers: Set<RwLockContainerPtr>, processes: Set<RwLockProcessPtr>, threads: Set<RwLockThreadPtr>, endpoints: Set<RwLockEndpointPtr>, schedulers: Set<RwLockSchedulerPtr>, pcid_allocators: Set<RwLockPcidAllocatorPtr>, pagetables: Set<RwLockPageTableRoot>, iommu_tables: Set<RwLockPageTableRoot>|
                    #![trigger old(lctx).object_lock_scope(pages, cpus, containers, processes, threads, endpoints, schedulers.insert(scheduler_ptr), pcid_allocators, pagetables, iommu_tables)]
                    !schedulers.contains(scheduler_ptr)
                    && old(lctx).object_lock_scope(pages, cpus, containers, processes, threads, endpoints, schedulers.insert(scheduler_ptr), pcid_allocators, pagetables, iommu_tables)
                    ==> final(lctx).object_lock_scope(pages, cpus, containers, processes, threads, endpoints, schedulers, pcid_allocators, pagetables, iommu_tables),
                unlock_ensures(old(lctx), final(lctx), (), lock_perm.view().lock_id(), KernelObjId::Scheduler(scheduler_ptr), old(self).sched_mp.lock_id_by_key(scheduler_ptr)),
        {
            proof {
                assert({
                    &&& old(self).sched_mp.perms_wf()
                    &&& old(self).sched_mp.spec_index(scheduler_ptr).inv()
                }) by { reveal(scheduler_perms_wf); };
                assert(old(lctx).lock_entry_contains(old(self).sched_mp.lock_id_by_key(scheduler_ptr), KernelObjId::Scheduler(scheduler_ptr))) by { reveal(LockedMap::typed_lock_map_aligned); };
                assert(old(lctx).lock_id_set().contains((old(self).sched_mp.lock_id_by_key(scheduler_ptr), KernelObjId::Scheduler(scheduler_ptr)))) by { reveal(lock_id_set_aligned); };
            }
            self.sched_mp.wunlock(scheduler_ptr, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::Scheduler(scheduler_ptr)));
            proof {
                assert(scheduler_perms_wf(self.sched_mp)) by { reveal(scheduler_perms_wf); };
                assert(scheduler_invariant_fields_unchanged(old(self).sched_mp, self.sched_mp)) by { scheduler_lock_op_preserves_invariant_fields(old(self).sched_mp, self.sched_mp, scheduler_ptr); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.process_management_inv()) by {
                    assert(container_scheduler_wf(self.ctn_mp, self.sched_mp)) by { reveal(container_scheduler_wf); };
                    assert(container_thread_scheduler_wf(self.ctn_mp, self.thr_mp, self.sched_mp)) by { reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf); };
                };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
                reveal(LocalContext::object_lock_scope);
                broadcast use vstd::map::lemma_map_remove_domain;
                broadcast use vstd::set::lemma_set_insert_same;
                broadcast use vstd::set::lemma_set_insert_different;
                broadcast use vstd::set::lemma_set_remove_same;
                broadcast use vstd::set::lemma_set_remove_different;
            }
        }

}
} // verus!
