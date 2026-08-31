use vstd::prelude::*;
use crate::*;

verus! {

pub open spec fn pagetable_pair_lock_acquire_scope(lctx: &LocalContext) -> bool {
    &&& lctx.held_lock_majors_lt(SCHEDULER_LOCK_MAJOR)
    &&& exists|cpus: Set<CpuId>, containers: Set<RwLockContainerPtr>, processes: Set<RwLockProcessPtr>, threads: Set<RwLockThreadPtr>, endpoints: Set<RwLockEndpointPtr>|
        lctx.base_lock_scope(cpus, containers, processes, threads, endpoints)
}

impl KernelK {
        fn wlock_pagetable_with_acyclic(
            &mut self,
            pagetable_ptr: RwLockPageTableRoot,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Tracked<LockPerm>)
            requires
                old(self).inv(),
                old(self).pt_mp.dom().contains(pagetable_ptr),
                wlock_requires(old(self).pt_mp.spec_index(pagetable_ptr), old(lctx)),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).lock_id_acyclic(old(self).pt_mp.lock_id_by_key(pagetable_ptr)),
                old(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
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
                final(self).ep_mp == old(self).ep_mp,
                final(self).allc_4k_mp == old(self).allc_4k_mp,
                final(self).allc_2m_mp == old(self).allc_2m_mp,
                final(self).allc_1g_mp == old(self).allc_1g_mp,
                final(self).dflt_pt == old(self).dflt_pt,
                final(self).pt_mp.unchanged_except(&old(self).pt_mp, pagetable_ptr),
                final(self).pt_mp.lock_id_by_key(pagetable_ptr) == old(self).pt_mp.lock_id_by_key(pagetable_ptr),
                forall|other_pagetable: RwLockPageTableRoot|
                    #![trigger final(self).pt_mp.lock_id_by_key(other_pagetable)]
                    other_pagetable != pagetable_ptr && old(self).pt_mp.dom().contains(other_pagetable)
                    ==> final(self).pt_mp.dom().contains(other_pagetable)
                        && final(self).pt_mp.lock_id_by_key(other_pagetable) == old(self).pt_mp.lock_id_by_key(other_pagetable),
                pagetable_objects_unlocked(old(self).pt_mp, old(lctx).thread_id()) ==> pagetable_objects_unlocked_except(final(self).pt_mp, final(lctx).thread_id(), set![pagetable_ptr]),
                forall|exceptions: Set<RwLockPageTableRoot>|
                    #![trigger pagetable_objects_unlocked_except(old(self).pt_mp, old(lctx).thread_id(), exceptions)]
                    pagetable_objects_unlocked_except(old(self).pt_mp, old(lctx).thread_id(), exceptions)
                    ==> pagetable_objects_unlocked_except(final(self).pt_mp, final(lctx).thread_id(), exceptions.insert(pagetable_ptr)),
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                wlock_ensures(old(self).pt_mp.spec_index(pagetable_ptr), final(self).pt_mp.spec_index(pagetable_ptr), old(self).pt_mp.lock_id_by_key(pagetable_ptr), final(lctx), ret.view()),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(self).pt_mp.lock_id_by_key(pagetable_ptr), KernelObjId::PageTable(pagetable_ptr))),
                typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::PageTable(pagetable_ptr), TypedHeldLock { lock_id: final(self).pt_mp.lock_id_by_key(pagetable_ptr), mode: TypedLockMode::Write }),
                final(lctx).pagetable_lock_map().contains_pair(pagetable_ptr, TypedHeldLock { lock_id: final(self).pt_mp.lock_id_by_key(pagetable_ptr), mode: TypedLockMode::Write }),
                final(lctx).lock_entry_contains(final(self).pt_mp.lock_id_by_key(pagetable_ptr), KernelObjId::PageTable(pagetable_ptr)),
                final(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
                final(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
                forall|pages: Set<PageIndex>, cpus: Set<CpuId>, containers: Set<RwLockContainerPtr>, processes: Set<RwLockProcessPtr>, threads: Set<RwLockThreadPtr>, endpoints: Set<RwLockEndpointPtr>, schedulers: Set<RwLockSchedulerPtr>, pcid_allocators: Set<RwLockPcidAllocatorPtr>, pagetables: Set<RwLockPageTableRoot>, iommu_tables: Set<RwLockPageTableRoot>|
                    #![trigger old(lctx).object_lock_scope(pages, cpus, containers, processes, threads, endpoints, schedulers, pcid_allocators, pagetables, iommu_tables)]
                    old(lctx).object_lock_scope(pages, cpus, containers, processes, threads, endpoints, schedulers, pcid_allocators, pagetables, iommu_tables)
                    ==> final(lctx).object_lock_scope(pages, cpus, containers, processes, threads, endpoints, schedulers, pcid_allocators, pagetables.insert(pagetable_ptr), iommu_tables),
                forall|cpus: Set<CpuId>, containers: Set<RwLockContainerPtr>, processes: Set<RwLockProcessPtr>, threads: Set<RwLockThreadPtr>, endpoints: Set<RwLockEndpointPtr>|
                    #![trigger old(lctx).base_lock_scope(cpus, containers, processes, threads, endpoints)]
                    old(lctx).base_lock_scope(cpus, containers, processes, threads, endpoints)
                    ==> final(lctx).object_lock_scope(Set::empty(), cpus, containers, processes, threads, endpoints, Set::empty(), Set::empty(), set![pagetable_ptr], Set::empty()),
                forall|other_pagetable: RwLockPageTableRoot|
                    #![trigger final(lctx).lock_id_set().contains((final(self).pt_mp.lock_id_by_key(other_pagetable), KernelObjId::PageTable(other_pagetable)))]
                    old(self).pt_mp.dom().contains(other_pagetable)
                        && other_pagetable != pagetable_ptr
                    ==> final(lctx).lock_id_set().contains((final(self).pt_mp.lock_id_by_key(other_pagetable), KernelObjId::PageTable(other_pagetable))) == old(lctx).lock_id_set().contains((old(self).pt_mp.lock_id_by_key(other_pagetable), KernelObjId::PageTable(other_pagetable))),
        {
            proof {
                assert(old(self).pt_mp.perms_wf()) by { reveal(pagetable_perms_wf); };
            }
            let ret = self.pt_mp.wlock(pagetable_ptr, Tracked(&mut *lctx), Ghost(KernelObjId::PageTable(pagetable_ptr)));
            proof {
                assert(pagetable_invariant_fields_unchanged(old(self).pt_mp, self.pt_mp)) by { pagetable_lock_op_preserves_invariant_fields(old(self).pt_mp, self.pt_mp, pagetable_ptr); };
                assert(self.subsystems_inv()) by {
                    assert(pagetable_perms_wf(self.pt_mp)) by { lemma_no_change_imply_pagetable_perms_wf_forall(); };
                    reveal(KernelK::default_pagetable_wf);
                };
                assert(self.memory_management_inv()) by {
                    assert(process_pagetable_match(self.prc_mp, self.pt_mp)) by { lemma_no_change_imply_process_pagetable_match_for_pagetable_fields_forall(); };
                    assert(page_pagetable_wf(self.pt_mp, self.pg_arr)) by { lemma_no_change_imply_page_pagetable_wf_for_pagetable_fields_forall(); };
                    assert(container_process_page_pagetable_wf(self.ctn_mp, self.prc_mp, self.pt_mp, self.pg_arr)) by { lemma_no_change_imply_container_process_page_pagetable_wf_for_pagetable_fields_forall(); };
                    assert(pagetable_pages_wf(self.pt_mp, self.pg_arr)) by { lemma_no_change_imply_pagetable_pages_wf_for_pagetable_fields_forall(); };
                };
                assert(cpu_dirty_map_wf(self.ctn_mp, self.prc_mp, self.cpu_arr, self.cpu_tlb, self.pt_mp)) by { lemma_no_change_imply_cpu_dirty_map_wf_for_pagetable_fields_forall(); };
                assert(tlb_wf_spec(self.cpu_tlb, self.pt_mp, self.cpu_arr)) by { lemma_no_change_imply_tlb_wf_spec_for_pagetable_fields_forall(); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
                assert(lctx.pagetable_lock_map().contains_pair(pagetable_ptr, TypedHeldLock { lock_id: self.pt_mp.lock_id_by_key(pagetable_ptr), mode: TypedLockMode::Write })) by { reveal(typed_lock_maps_inserted); };
                assert(lctx.lock_entry_contains(self.pt_mp.lock_id_by_key(pagetable_ptr), KernelObjId::PageTable(pagetable_ptr))) by { reveal(typed_lock_maps_inserted); };
                assert(lctx.held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR)) by { reveal(LocalContext::held_lock_majors_lt); reveal(pagetable_perms_wf); broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different; };
                assert(lctx.held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR)) by { reveal(LocalContext::held_lock_majors_lt); assert(MAPPED_PAGE_LOCK_MAJOR < ALLOCATOR_CACHE_MAJOR) by (compute); };
                assert(self.pt_mp.lock_id_by_key(pagetable_ptr) == old(self).pt_mp.lock_id_by_key(pagetable_ptr)) by { reveal(wlock_ensures); };
                reveal(LocalContext::base_lock_scope);
                reveal(LocalContext::object_lock_scope);
                reveal(pagetable_objects_unlocked_except);
                reveal(LockedMap::unchanged_except);
                broadcast use vstd::map::lemma_map_insert_domain;
                broadcast use vstd::set::lemma_set_insert_same;
                broadcast use vstd::set::lemma_set_insert_different;
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
            }
            ret
        }

        pub fn wlock_pagetable(
            &mut self,
            pagetable_ptr: RwLockPageTableRoot,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Tracked<LockPerm>)
            requires
                old(self).inv(),
                old(self).pt_mp.dom().contains(pagetable_ptr),
                wlock_requires(old(self).pt_mp.spec_index(pagetable_ptr), old(lctx)),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
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
                final(self).ep_mp == old(self).ep_mp,
                final(self).allc_4k_mp == old(self).allc_4k_mp,
                final(self).allc_2m_mp == old(self).allc_2m_mp,
                final(self).allc_1g_mp == old(self).allc_1g_mp,
                final(self).dflt_pt == old(self).dflt_pt,
                final(self).pt_mp.unchanged_except(&old(self).pt_mp, pagetable_ptr),
                final(self).pt_mp.lock_id_by_key(pagetable_ptr) == old(self).pt_mp.lock_id_by_key(pagetable_ptr),
                forall|other_pagetable: RwLockPageTableRoot|
                    #![trigger final(self).pt_mp.lock_id_by_key(other_pagetable)]
                    other_pagetable != pagetable_ptr && old(self).pt_mp.dom().contains(other_pagetable)
                    ==> final(self).pt_mp.dom().contains(other_pagetable)
                        && final(self).pt_mp.lock_id_by_key(other_pagetable) == old(self).pt_mp.lock_id_by_key(other_pagetable),
                pagetable_objects_unlocked(old(self).pt_mp, old(lctx).thread_id()) ==> pagetable_objects_unlocked_except(final(self).pt_mp, final(lctx).thread_id(), set![pagetable_ptr]),
                forall|exceptions: Set<RwLockPageTableRoot>|
                    #![trigger pagetable_objects_unlocked_except(old(self).pt_mp, old(lctx).thread_id(), exceptions)]
                    pagetable_objects_unlocked_except(old(self).pt_mp, old(lctx).thread_id(), exceptions)
                    ==> pagetable_objects_unlocked_except(final(self).pt_mp, final(lctx).thread_id(), exceptions.insert(pagetable_ptr)),
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                wlock_ensures(old(self).pt_mp.spec_index(pagetable_ptr), final(self).pt_mp.spec_index(pagetable_ptr), old(self).pt_mp.lock_id_by_key(pagetable_ptr), final(lctx), ret.view()),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(self).pt_mp.lock_id_by_key(pagetable_ptr), KernelObjId::PageTable(pagetable_ptr))),
                typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::PageTable(pagetable_ptr), TypedHeldLock { lock_id: final(self).pt_mp.lock_id_by_key(pagetable_ptr), mode: TypedLockMode::Write }),
                final(lctx).pagetable_lock_map().contains_pair(pagetable_ptr, TypedHeldLock { lock_id: final(self).pt_mp.lock_id_by_key(pagetable_ptr), mode: TypedLockMode::Write }),
                final(lctx).lock_entry_contains(final(self).pt_mp.lock_id_by_key(pagetable_ptr), KernelObjId::PageTable(pagetable_ptr)),
                final(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
                final(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
                forall|pages: Set<PageIndex>, cpus: Set<CpuId>, containers: Set<RwLockContainerPtr>, processes: Set<RwLockProcessPtr>, threads: Set<RwLockThreadPtr>, endpoints: Set<RwLockEndpointPtr>, schedulers: Set<RwLockSchedulerPtr>, pcid_allocators: Set<RwLockPcidAllocatorPtr>, pagetables: Set<RwLockPageTableRoot>, iommu_tables: Set<RwLockPageTableRoot>|
                    #![trigger old(lctx).object_lock_scope(pages, cpus, containers, processes, threads, endpoints, schedulers, pcid_allocators, pagetables, iommu_tables)]
                    old(lctx).object_lock_scope(pages, cpus, containers, processes, threads, endpoints, schedulers, pcid_allocators, pagetables, iommu_tables)
                    ==> final(lctx).object_lock_scope(pages, cpus, containers, processes, threads, endpoints, schedulers, pcid_allocators, pagetables.insert(pagetable_ptr), iommu_tables),
                forall|cpus: Set<CpuId>, containers: Set<RwLockContainerPtr>, processes: Set<RwLockProcessPtr>, threads: Set<RwLockThreadPtr>, endpoints: Set<RwLockEndpointPtr>|
                    #![trigger old(lctx).base_lock_scope(cpus, containers, processes, threads, endpoints)]
                    old(lctx).base_lock_scope(cpus, containers, processes, threads, endpoints)
                    ==> final(lctx).object_lock_scope(Set::empty(), cpus, containers, processes, threads, endpoints, Set::empty(), Set::empty(), set![pagetable_ptr], Set::empty()),
        {
            proof {
                assert(old(lctx).lock_id_acyclic(old(self).pt_mp.lock_id_by_key(pagetable_ptr))) by { reveal(LocalContext::lock_id_acyclic); reveal(LocalContext::held_lock_majors_lt); reveal(pagetable_perms_wf); };
            }
            self.wlock_pagetable_with_acyclic(pagetable_ptr, Tracked(&mut *lctx))
        }

        pub fn wlock_pagetable_pair(
            &mut self,
            source_pagetable: RwLockPageTableRoot,
            target_pagetable: RwLockPageTableRoot,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: (Tracked<LockPerm>, Tracked<LockPerm>))
            requires
                old(self).inv(),
                source_pagetable != target_pagetable,
                old(self).pt_mp.dom().contains(source_pagetable),
                old(self).pt_mp.dom().contains(target_pagetable),
                wlock_requires(old(self).pt_mp.spec_index(source_pagetable), old(lctx)),
                wlock_requires(old(self).pt_mp.spec_index(target_pagetable), old(lctx)),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR) || pagetable_pair_lock_acquire_scope(old(lctx)),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
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
                final(self).ep_mp == old(self).ep_mp,
                final(self).allc_4k_mp == old(self).allc_4k_mp,
                final(self).allc_2m_mp == old(self).allc_2m_mp,
                final(self).allc_1g_mp == old(self).allc_1g_mp,
                final(self).dflt_pt == old(self).dflt_pt,
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                final(lctx).page_lock_map() == old(lctx).page_lock_map(),
                final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
                final(lctx).container_lock_map() == old(lctx).container_lock_map(),
                final(lctx).process_lock_map() == old(lctx).process_lock_map(),
                final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
                final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
                final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
                final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
                final(lctx).pagetable_lock_map() == if source_pagetable < target_pagetable {
                    old(lctx).pagetable_lock_map()
                        .insert(source_pagetable, TypedHeldLock { lock_id: final(self).pt_mp.lock_id_by_key(source_pagetable), mode: TypedLockMode::Write })
                        .insert(target_pagetable, TypedHeldLock { lock_id: final(self).pt_mp.lock_id_by_key(target_pagetable), mode: TypedLockMode::Write })
                } else {
                    old(lctx).pagetable_lock_map()
                        .insert(target_pagetable, TypedHeldLock { lock_id: final(self).pt_mp.lock_id_by_key(target_pagetable), mode: TypedLockMode::Write })
                        .insert(source_pagetable, TypedHeldLock { lock_id: final(self).pt_mp.lock_id_by_key(source_pagetable), mode: TypedLockMode::Write })
                },
                final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
                final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
                final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
                final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
                final(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
                final(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
                final(self).pt_mp.spec_index(source_pagetable).wlocked_by(final(lctx)),
                final(self).pt_mp.spec_index(target_pagetable).wlocked_by(final(lctx)),
                ret.0.view().state() is WriteLock,
                ret.0.view().thread_id() == final(lctx).thread_id(),
                ret.0.view().lock_id() == final(self).pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
                ret.1.view().state() is WriteLock,
                ret.1.view().thread_id() == final(lctx).thread_id(),
                ret.1.view().lock_id() == final(self).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
                final(lctx).pagetable_lock_map().contains_pair(source_pagetable, TypedHeldLock { lock_id: final(self).pt_mp.lock_id_by_key(source_pagetable), mode: TypedLockMode::Write }),
                final(lctx).pagetable_lock_map().contains_pair(target_pagetable, TypedHeldLock { lock_id: final(self).pt_mp.lock_id_by_key(target_pagetable), mode: TypedLockMode::Write }),
                pagetable_objects_unlocked(old(self).pt_mp, old(lctx).thread_id()) ==> pagetable_objects_unlocked_except(final(self).pt_mp, final(lctx).thread_id(), set![source_pagetable, target_pagetable]),
        {
            proof {
                assert(old(lctx).held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR)) by {
                    reveal(pagetable_pair_lock_acquire_scope); reveal(LocalContext::base_lock_scope); reveal(LocalContext::object_lock_scope); reveal(LocalContext::held_lock_majors_lt); reveal(lock_id_set_aligned); reveal(typed_lock_maps_aligned); reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned); reveal(cpu_array_wf); reveal(container_perms_wf); reveal(process_perms_wf); reveal(thread_perms_wf); reveal(endpoint_perms_wf); reveal(pcid_allocator_perms_wf);
                };
            }
            if source_pagetable < target_pagetable {
                let Tracked(source_perm) = self.wlock_pagetable(source_pagetable, Tracked(&mut *lctx));
                proof {
                    assert(lctx.lock_id_acyclic(self.pt_mp.lock_id_by_key(target_pagetable))) by { reveal(LocalContext::lock_id_acyclic); reveal(LocalContext::held_lock_majors_lt); reveal(pagetable_perms_wf); broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different; };
                }
                let Tracked(target_perm) = self.wlock_pagetable_with_acyclic(target_pagetable, Tracked(&mut *lctx));
                proof {
                    assert(self.pt_mp.lock_id_by_key(source_pagetable) == old(self).pt_mp.lock_id_by_key(source_pagetable)) by { reveal(LockedMap::unchanged_except); };
                    assert(self.pt_mp.lock_id_by_key(target_pagetable) == old(self).pt_mp.lock_id_by_key(target_pagetable)) by { reveal(LockedMap::unchanged_except); };
                    assert(lctx.pagetable_lock_map() == old(lctx).pagetable_lock_map()
                        .insert(source_pagetable, TypedHeldLock { lock_id: self.pt_mp.lock_id_by_key(source_pagetable), mode: TypedLockMode::Write })
                        .insert(target_pagetable, TypedHeldLock { lock_id: self.pt_mp.lock_id_by_key(target_pagetable), mode: TypedLockMode::Write })) by { reveal(typed_lock_maps_inserted); };
                    assert(lctx.pagetable_lock_map().contains_pair(target_pagetable, TypedHeldLock { lock_id: self.pt_mp.lock_id_by_key(target_pagetable), mode: TypedLockMode::Write })) by { broadcast use vstd::map::lemma_map_insert_domain; };
                }
                (Tracked(source_perm), Tracked(target_perm))
            } else {
                let Tracked(target_perm) = self.wlock_pagetable(target_pagetable, Tracked(&mut *lctx));
                proof {
                    assert(lctx.lock_id_acyclic(self.pt_mp.lock_id_by_key(source_pagetable))) by { reveal(LocalContext::lock_id_acyclic); reveal(LocalContext::held_lock_majors_lt); reveal(pagetable_perms_wf); broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different; };
                }
                let Tracked(source_perm) = self.wlock_pagetable_with_acyclic(source_pagetable, Tracked(&mut *lctx));
                proof {
                    assert(self.pt_mp.lock_id_by_key(source_pagetable) == old(self).pt_mp.lock_id_by_key(source_pagetable)) by { reveal(LockedMap::unchanged_except); };
                    assert(self.pt_mp.lock_id_by_key(target_pagetable) == old(self).pt_mp.lock_id_by_key(target_pagetable)) by { reveal(LockedMap::unchanged_except); };
                    assert(lctx.pagetable_lock_map() == old(lctx).pagetable_lock_map()
                        .insert(target_pagetable, TypedHeldLock { lock_id: self.pt_mp.lock_id_by_key(target_pagetable), mode: TypedLockMode::Write })
                        .insert(source_pagetable, TypedHeldLock { lock_id: self.pt_mp.lock_id_by_key(source_pagetable), mode: TypedLockMode::Write })) by { reveal(typed_lock_maps_inserted); };
                    assert(lctx.pagetable_lock_map().contains_pair(target_pagetable, TypedHeldLock { lock_id: self.pt_mp.lock_id_by_key(target_pagetable), mode: TypedLockMode::Write })) by { broadcast use vstd::map::lemma_map_insert_domain; };
                }
                (Tracked(source_perm), Tracked(target_perm))
            }
        }

        pub fn wunlock_pagetable(
            &mut self,
            pagetable_ptr: RwLockPageTableRoot,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                old(self).pt_mp.dom().contains(pagetable_ptr),
                old(self).pt_mp.spec_index(pagetable_ptr).wlocked_by(old(lctx)),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id() == old(self).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
                typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
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
                final(self).ep_mp == old(self).ep_mp,
                final(self).allc_4k_mp == old(self).allc_4k_mp,
                final(self).allc_2m_mp == old(self).allc_2m_mp,
                final(self).allc_1g_mp == old(self).allc_1g_mp,
                final(self).dflt_pt == old(self).dflt_pt,
                final(self).pt_mp.unchanged_except(&old(self).pt_mp, pagetable_ptr),
                final(self).pt_mp.lock_id_by_key(pagetable_ptr) == old(self).pt_mp.lock_id_by_key(pagetable_ptr),
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,
                wunlock_ensures(old(self).pt_mp.spec_index(pagetable_ptr), final(self).pt_mp.spec_index(pagetable_ptr)),
                pagetable_objects_unlocked_except(old(self).pt_mp, old(lctx).thread_id(), set![pagetable_ptr]) ==> pagetable_objects_unlocked(final(self).pt_mp, final(lctx).thread_id()),
                forall|exceptions: Set<RwLockPageTableRoot>|
                    #![trigger pagetable_objects_unlocked_except(old(self).pt_mp, old(lctx).thread_id(), exceptions.insert(pagetable_ptr))]
                    !exceptions.contains(pagetable_ptr)
                    && pagetable_objects_unlocked_except(old(self).pt_mp, old(lctx).thread_id(), exceptions.insert(pagetable_ptr))
                    ==> pagetable_objects_unlocked_except(final(self).pt_mp, final(lctx).thread_id(), exceptions),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().remove((old(self).pt_mp.lock_id_by_key(pagetable_ptr), KernelObjId::PageTable(pagetable_ptr))),
                typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::PageTable(pagetable_ptr)),
                forall|pages: Set<PageIndex>, cpus: Set<CpuId>, containers: Set<RwLockContainerPtr>, processes: Set<RwLockProcessPtr>, threads: Set<RwLockThreadPtr>, endpoints: Set<RwLockEndpointPtr>, schedulers: Set<RwLockSchedulerPtr>, pcid_allocators: Set<RwLockPcidAllocatorPtr>, pagetables: Set<RwLockPageTableRoot>, iommu_tables: Set<RwLockPageTableRoot>|
                    #![trigger old(lctx).object_lock_scope(pages, cpus, containers, processes, threads, endpoints, schedulers, pcid_allocators, pagetables, iommu_tables)]
                    old(lctx).object_lock_scope(pages, cpus, containers, processes, threads, endpoints, schedulers, pcid_allocators, pagetables, iommu_tables)
                    ==> final(lctx).object_lock_scope(pages, cpus, containers, processes, threads, endpoints, schedulers, pcid_allocators, pagetables.remove(pagetable_ptr), iommu_tables),
                forall|pages: Set<PageIndex>, cpus: Set<CpuId>, containers: Set<RwLockContainerPtr>, processes: Set<RwLockProcessPtr>, threads: Set<RwLockThreadPtr>, endpoints: Set<RwLockEndpointPtr>, schedulers: Set<RwLockSchedulerPtr>, pcid_allocators: Set<RwLockPcidAllocatorPtr>, pagetables: Set<RwLockPageTableRoot>, iommu_tables: Set<RwLockPageTableRoot>|
                    #![trigger old(lctx).object_lock_scope(pages, cpus, containers, processes, threads, endpoints, schedulers, pcid_allocators, pagetables.insert(pagetable_ptr), iommu_tables)]
                    !pagetables.contains(pagetable_ptr)
                    && old(lctx).object_lock_scope(pages, cpus, containers, processes, threads, endpoints, schedulers, pcid_allocators, pagetables.insert(pagetable_ptr), iommu_tables)
                    ==> final(lctx).object_lock_scope(pages, cpus, containers, processes, threads, endpoints, schedulers, pcid_allocators, pagetables, iommu_tables),
                forall|other_pagetable: RwLockPageTableRoot|
                    #![trigger final(lctx).lock_id_set().contains((final(self).pt_mp.lock_id_by_key(other_pagetable), KernelObjId::PageTable(other_pagetable)))]
                    old(self).pt_mp.dom().contains(other_pagetable)
                        && other_pagetable != pagetable_ptr
                    ==> final(lctx).lock_id_set().contains((final(self).pt_mp.lock_id_by_key(other_pagetable), KernelObjId::PageTable(other_pagetable))) == old(lctx).lock_id_set().contains((old(self).pt_mp.lock_id_by_key(other_pagetable), KernelObjId::PageTable(other_pagetable))),
        {
            proof {
                assert({
                    &&& old(self).pt_mp.perms_wf()
                    &&& old(self).pt_mp.spec_index(pagetable_ptr).inv()
                }) by { reveal(pagetable_perms_wf); };
                assert(old(lctx).lock_entry_contains(old(self).pt_mp.lock_id_by_key(pagetable_ptr), KernelObjId::PageTable(pagetable_ptr))) by { reveal(LockedMap::typed_lock_map_aligned); };
                assert(old(lctx).lock_id_set().contains((old(self).pt_mp.lock_id_by_key(pagetable_ptr), KernelObjId::PageTable(pagetable_ptr)))) by { reveal(lock_id_set_aligned); };
            }
            self.pt_mp.wunlock(pagetable_ptr, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::PageTable(pagetable_ptr)));
            proof {
                assert(pagetable_invariant_fields_unchanged(old(self).pt_mp, self.pt_mp)) by { pagetable_lock_op_preserves_invariant_fields(old(self).pt_mp, self.pt_mp, pagetable_ptr); };
                assert(self.subsystems_inv()) by {
                    assert(pagetable_perms_wf(self.pt_mp)) by { lemma_no_change_imply_pagetable_perms_wf_forall(); };
                    reveal(KernelK::default_pagetable_wf);
                };
                assert(self.memory_management_inv()) by {
                    assert(process_pagetable_match(self.prc_mp, self.pt_mp)) by { lemma_no_change_imply_process_pagetable_match_for_pagetable_fields_forall(); };
                    assert(page_pagetable_wf(self.pt_mp, self.pg_arr)) by { lemma_no_change_imply_page_pagetable_wf_for_pagetable_fields_forall(); };
                    assert(container_process_page_pagetable_wf(self.ctn_mp, self.prc_mp, self.pt_mp, self.pg_arr)) by { lemma_no_change_imply_container_process_page_pagetable_wf_for_pagetable_fields_forall(); };
                    assert(pagetable_pages_wf(self.pt_mp, self.pg_arr)) by { lemma_no_change_imply_pagetable_pages_wf_for_pagetable_fields_forall(); };
                };
                assert(cpu_dirty_map_wf(self.ctn_mp, self.prc_mp, self.cpu_arr, self.cpu_tlb, self.pt_mp)) by { lemma_no_change_imply_cpu_dirty_map_wf_for_pagetable_fields_forall(); };
                assert(tlb_wf_spec(self.cpu_tlb, self.pt_mp, self.cpu_arr)) by { lemma_no_change_imply_tlb_wf_spec_for_pagetable_fields_forall(); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
                reveal(LocalContext::object_lock_scope);
                reveal(pagetable_objects_unlocked_except);
                reveal(LockedMap::unchanged_except);
                broadcast use vstd::map::lemma_map_remove_domain;
                broadcast use vstd::set::lemma_set_insert_same;
                broadcast use vstd::set::lemma_set_insert_different;
                broadcast use vstd::set::lemma_set_remove_same;
                broadcast use vstd::set::lemma_set_remove_different;
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
            }
        }
}
} // verus!
