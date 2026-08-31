use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
        /// Wrapper around `LockedMap::wlock_unless_killed` for `process_map`
        /// that re-establishes `inv()` after the lock attempt. Same shape as
        /// `wlock_container_unless_killed`, but for the process map, which is
        /// touched by the conservation-fold conjunct
        /// `container_process_allocator_quota_wf` — so that piece is discharged
        /// via the per-process set-fold axioms (the lock only moves lock state,
        /// so each process's `process_effective_quota_*` is unchanged ==> the
        /// folded sum is unchanged).
        ///
        pub fn wlock_process_unless_killed(
            &mut self,
            process_ptr: RwLockProcessPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: (bool, Option<Tracked<LockPerm>>))
            requires
                old(self).inv(),
                old(self).prc_mp.dom().contains(process_ptr),
                !old(self).prc_mp.spec_index(process_ptr).wlocked_by(old(lctx)),
                old(lctx).kernel_view_locking_state() is Acquire,
                process_lock_acquire_scope(old(self), old(lctx), process_ptr),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                // ---- Every held lock still matches lctx (success: process locked; failure: no-op) ----
                // ---- Dynamic lock ids remain aligned ----
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                // ---- Field framing: only process_map's lock state moves ----
                final(self).pt_mp     == old(self).pt_mp,
                final(self).it_mp     == old(self).it_mp,
                final(self).irt     == old(self).irt,
                final(self).pg_arr        == old(self).pg_arr,
                final(self).cpu_arr         == old(self).cpu_arr,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).iommu_tlb           == old(self).iommu_tlb,
                final(self).rt_ctn    == old(self).rt_ctn,
                final(self).ctn_mp     == old(self).ctn_mp,
                final(self).sched_mp     == old(self).sched_mp,
                final(self).pcid_allc_mp == old(self).pcid_allc_mp,
                final(self).thr_mp        == old(self).thr_mp,
                final(self).ep_mp      == old(self).ep_mp,
                final(self).allc_4k_mp  == old(self).allc_4k_mp,
                final(self).allc_2m_mp  == old(self).allc_2m_mp,
                final(self).allc_1g_mp  == old(self).allc_1g_mp,
                final(self).dflt_pt == old(self).dflt_pt,
                // ---- process_map: only the targeted entry's lock state
                // ---- (success) or nothing at all (failure) changed.
                final(self).prc_mp.unchanged_except(&old(self).prc_mp, process_ptr),
                final(self).prc_mp.perms_wf(),
                process_objects_unlocked(old(self).prc_mp, old(lctx).thread_id()) ==> process_objects_unlocked_except(final(self).prc_mp, final(lctx).thread_id(), set![process_ptr]),
                process_objects_unlocked(old(self).prc_mp, old(lctx).thread_id()) && !ret.0 ==> process_objects_unlocked(final(self).prc_mp, final(lctx).thread_id()),
                // ---- LocalContext phase preservation ----
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                old(lctx).held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR) ==> final(lctx).held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR),
                // ---- Failure: process is being killed; complete no-op ----
                ret.0 == false ==>
                {
                    &&& old(self).prc_mp.spec_index(process_ptr).being_killed() == true
                    &&& final(self).prc_mp.spec_index(process_ptr) == old(self).prc_mp.spec_index(process_ptr)
                    &&& ret.1 is None
                    &&& final(lctx).lock_id_set() =~= old(lctx).lock_id_set()
                    &&& typed_lock_maps_unchanged(old(lctx), final(lctx))
                },

                // ---- Success: process locked by us, perm returned ----
                ret.0 == true ==>
                {
                    &&& old(self).prc_mp.spec_index(process_ptr).being_killed() == false
                    &&& ret.1 is Some
                    &&& wlock_ensures(old(self).prc_mp.spec_index(process_ptr), final(self).prc_mp.spec_index(process_ptr), old(self).prc_mp.lock_id_by_key(process_ptr), final(lctx), ret.1.unwrap().view())
                    &&& final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(self).prc_mp.lock_id_by_key(process_ptr), KernelObjId::Process(process_ptr)))
                    &&& typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Process(process_ptr), TypedHeldLock { lock_id: final(self).prc_mp.lock_id_by_key(process_ptr), mode: TypedLockMode::Write })
                    &&& process_lock_held_scope(final(self), final(lctx), process_ptr)
                },
        {
            proof {
                assert(old(self).prc_mp.perms_wf()) by { reveal(process_perms_wf); };
                assert(old(lctx).lock_id_acyclic(old(self).prc_mp.lock_id_by_key(process_ptr))) by { reveal(process_lock_acquire_scope); reveal(LocalContext::base_lock_scope); reveal(LocalContext::base_quota_4k_lock_scope); reveal(lock_id_set_aligned); reveal(typed_lock_maps_aligned); reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned); reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(container_cpu_wf); reveal(process_cpu_wf); reveal(container_process_wf); reveal(container_allocator_wf); reveal(allocator_perms_wf); };
            }
            let res = self.prc_mp.wlock_unless_killed(process_ptr, Tracked(&mut *lctx), Ghost(KernelObjId::Process(process_ptr)));

            proof {
                assert(process_perms_wf(self.prc_mp)) by { reveal(process_perms_wf); };
                assert(process_invariant_fields_unchanged(old(self).prc_mp, self.prc_mp)) by { process_lock_op_preserves_invariant_fields(old(self).prc_mp, self.prc_mp, process_ptr); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.memory_management_inv()) by { process_no_change_imply_memory_management_inv(*old(self), *self); };
                assert(self.process_management_inv()) by { process_no_change_imply_process_management_inv(*old(self), *self); };
                assert(iommu_root_table_process_wf(&self.irt, self.prc_mp, self.it_mp)) by { lemma_no_change_imply_iommu_root_table_process_wf_forall(); };
                assert(process_pci_function_ownership_wf(&self.irt, self.prc_mp)) by { lemma_no_change_imply_process_pci_function_ownership_wf_forall(); };
                assert(iommu_tlb_wf_spec(self.iommu_tlb, &self.irt, self.prc_mp, self.it_mp)) by { lemma_no_change_imply_iommu_tlb_wf_spec_forall(); };
                assert(cpu_dirty_map_wf(self.ctn_mp, self.prc_mp, self.cpu_arr, self.cpu_tlb, self.pt_mp)) by { lemma_no_change_imply_cpu_dirty_map_wf_forall(); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
                assert(old(lctx).held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR) ==> lctx.held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR)) by { reveal(LocalContext::held_lock_majors_lt); reveal(process_perms_wf); broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different; };
                if res.0 {
                    reveal(process_lock_acquire_scope);
                    if exists|cpu_id: CpuId|
                        #![trigger old(self).cpu_arr.spec_index(cpu_id)]
                    {
                        &&& old(lctx).base_lock_scope(set![cpu_id], Set::empty(), Set::empty(), Set::empty(), Set::empty())
                        &&& index_valid(NUM_CPUS, cpu_id)
                        &&& old(self).cpu_arr.spec_index(cpu_id).view().view().current_process == Some(process_ptr)
                    } {
                        let cpu_id = choose|cpu_id: CpuId|
                            #![trigger old(self).cpu_arr.spec_index(cpu_id)]
                        {
                            &&& old(lctx).base_lock_scope(set![cpu_id], Set::empty(), Set::empty(), Set::empty(), Set::empty())
                            &&& index_valid(NUM_CPUS, cpu_id)
                            &&& old(self).cpu_arr.spec_index(cpu_id).view().view().current_process == Some(process_ptr)
                        };
                        assert({
                            &&& lctx.base_lock_scope(set![cpu_id], Set::empty(), set![process_ptr], Set::empty(), Set::empty())
                            &&& self.cpu_arr.spec_index(cpu_id).view().view().current_process == Some(process_ptr)
                        }) by { reveal(typed_lock_maps_inserted); reveal(LocalContext::base_lock_scope); broadcast use vstd::map::lemma_map_insert_domain; };
                        assert(process_lock_held_scope(self, lctx, process_ptr)) by { reveal(process_lock_held_scope); };
                    } else if exists|cpu_id: CpuId, container_ptr: RwLockContainerPtr|
                        #![trigger old(lctx).base_lock_scope(set![cpu_id], set![container_ptr], Set::empty(), Set::empty(), Set::empty())]
                    {
                        &&& old(lctx).base_lock_scope(set![cpu_id], set![container_ptr], Set::empty(), Set::empty(), Set::empty())
                        &&& index_valid(NUM_CPUS, cpu_id)
                        &&& old(self).cpu_arr.spec_index(cpu_id).view().view().current_process == Some(process_ptr)
                        &&& old(self).cpu_arr.spec_index(cpu_id).view().view().owning_container == container_ptr
                    } {
                        let cpu_id = choose|cpu_id: CpuId|
                            #![trigger old(self).cpu_arr.spec_index(cpu_id)]
                        exists|container_ptr: RwLockContainerPtr|
                            #![trigger old(lctx).base_lock_scope(set![cpu_id], set![container_ptr], Set::empty(), Set::empty(), Set::empty())]
                        {
                            &&& old(lctx).base_lock_scope(set![cpu_id], set![container_ptr], Set::empty(), Set::empty(), Set::empty())
                            &&& index_valid(NUM_CPUS, cpu_id)
                            &&& old(self).cpu_arr.spec_index(cpu_id).view().view().current_process == Some(process_ptr)
                            &&& old(self).cpu_arr.spec_index(cpu_id).view().view().owning_container == container_ptr
                        };
                        let container_ptr = choose|container_ptr: RwLockContainerPtr|
                            #![trigger old(lctx).base_lock_scope(set![cpu_id], set![container_ptr], Set::empty(), Set::empty(), Set::empty())]
                        {
                            &&& old(lctx).base_lock_scope(set![cpu_id], set![container_ptr], Set::empty(), Set::empty(), Set::empty())
                            &&& index_valid(NUM_CPUS, cpu_id)
                            &&& old(self).cpu_arr.spec_index(cpu_id).view().view().current_process == Some(process_ptr)
                            &&& old(self).cpu_arr.spec_index(cpu_id).view().view().owning_container == container_ptr
                        };
                        assert({
                            &&& lctx.base_lock_scope(set![cpu_id], set![container_ptr], set![process_ptr], Set::empty(), Set::empty())
                            &&& self.cpu_arr.spec_index(cpu_id).view().view().current_process == Some(process_ptr)
                            &&& self.cpu_arr.spec_index(cpu_id).view().view().owning_container == container_ptr
                        }) by { reveal(typed_lock_maps_inserted); reveal(LocalContext::base_lock_scope); broadcast use vstd::map::lemma_map_insert_domain; };
                        assert(process_lock_held_scope(self, lctx, process_ptr)) by { reveal(process_lock_held_scope); };
                    } else {
                        let cpu_id = choose|cpu_id: CpuId|
                            #![trigger old(self).cpu_arr.spec_index(cpu_id)]
                        exists|container_ptr: RwLockContainerPtr, alloc_ptr_4k: RwLockPageAllocatorPtr|
                            #![trigger old(lctx).base_quota_4k_lock_scope(set![cpu_id], set![container_ptr], Set::empty(), Set::empty(), Set::empty(), set![alloc_ptr_4k])]
                        {
                            &&& old(lctx).base_quota_4k_lock_scope(set![cpu_id], set![container_ptr], Set::empty(), Set::empty(), Set::empty(), set![alloc_ptr_4k])
                            &&& index_valid(NUM_CPUS, cpu_id)
                            &&& old(self).cpu_arr.spec_index(cpu_id).view().view().current_process == Some(process_ptr)
                            &&& old(self).cpu_arr.spec_index(cpu_id).view().view().owning_container == container_ptr
                            &&& old(self).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k
                        };
                        let container_ptr = choose|container_ptr: RwLockContainerPtr|
                            #![trigger old(self).ctn_mp.spec_index(container_ptr)]
                        exists|alloc_ptr_4k: RwLockPageAllocatorPtr|
                            #![trigger old(lctx).base_quota_4k_lock_scope(set![cpu_id], set![container_ptr], Set::empty(), Set::empty(), Set::empty(), set![alloc_ptr_4k])]
                        {
                            &&& old(lctx).base_quota_4k_lock_scope(set![cpu_id], set![container_ptr], Set::empty(), Set::empty(), Set::empty(), set![alloc_ptr_4k])
                            &&& index_valid(NUM_CPUS, cpu_id)
                            &&& old(self).cpu_arr.spec_index(cpu_id).view().view().current_process == Some(process_ptr)
                            &&& old(self).cpu_arr.spec_index(cpu_id).view().view().owning_container == container_ptr
                            &&& old(self).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k
                        };
                        let alloc_ptr_4k = choose|alloc_ptr_4k: RwLockPageAllocatorPtr|
                            #![trigger old(lctx).base_quota_4k_lock_scope(set![cpu_id], set![container_ptr], Set::empty(), Set::empty(), Set::empty(), set![alloc_ptr_4k])]
                        {
                            &&& old(lctx).base_quota_4k_lock_scope(set![cpu_id], set![container_ptr], Set::empty(), Set::empty(), Set::empty(), set![alloc_ptr_4k])
                            &&& index_valid(NUM_CPUS, cpu_id)
                            &&& old(self).cpu_arr.spec_index(cpu_id).view().view().current_process == Some(process_ptr)
                            &&& old(self).cpu_arr.spec_index(cpu_id).view().view().owning_container == container_ptr
                            &&& old(self).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k
                        };
                        assert({
                            &&& lctx.base_quota_4k_lock_scope(set![cpu_id], set![container_ptr], set![process_ptr], Set::empty(), Set::empty(), set![alloc_ptr_4k])
                            &&& self.cpu_arr.spec_index(cpu_id).view().view().current_process == Some(process_ptr)
                            &&& self.cpu_arr.spec_index(cpu_id).view().view().owning_container == container_ptr
                            &&& self.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k
                        }) by { reveal(typed_lock_maps_inserted); reveal(LocalContext::base_quota_4k_lock_scope); broadcast use vstd::map::lemma_map_insert_domain; };
                        assert(process_lock_held_scope(self, lctx, process_ptr)) by { reveal(process_lock_held_scope); };
                    }
                }
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
            }
            res
        }

        /// Companion of `wlock_process_unless_killed` for the unlock side.
        /// Wraps `LockedMap::wunlock` for `process_map` and re-establishes
        /// `inv()` immediately afterwards. Unlocking has no killed-branch — the
        /// caller already holds the write lock, so this is unconditional.
        pub fn wunlock_process(
            &mut self,
            process_ptr: RwLockProcessPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                old(self).prc_mp.dom().contains(process_ptr),
                old(self).prc_mp.spec_index(process_ptr).being_killed() == false,
                old(self).prc_mp.spec_index(process_ptr).wlocked_by(old(lctx)),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id() == old(self).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
                typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                // ---- Every held lock still matches lctx (process now released) ----
                // ---- Dynamic lock ids remain aligned ----
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                // ---- Field framing: only process_map's lock state moves ----
                final(self).pt_mp     == old(self).pt_mp,
                final(self).it_mp     == old(self).it_mp,
                final(self).irt     == old(self).irt,
                final(self).pg_arr        == old(self).pg_arr,
                final(self).cpu_arr         == old(self).cpu_arr,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).iommu_tlb           == old(self).iommu_tlb,
                final(self).rt_ctn    == old(self).rt_ctn,
                final(self).ctn_mp     == old(self).ctn_mp,
                final(self).sched_mp     == old(self).sched_mp,
                final(self).pcid_allc_mp == old(self).pcid_allc_mp,
                final(self).thr_mp        == old(self).thr_mp,
                final(self).ep_mp      == old(self).ep_mp,
                final(self).allc_4k_mp  == old(self).allc_4k_mp,
                final(self).allc_2m_mp  == old(self).allc_2m_mp,
                final(self).allc_1g_mp  == old(self).allc_1g_mp,
                final(self).dflt_pt == old(self).dflt_pt,
                // ---- process_map: only the targeted entry's lock state changed (now unlocked) ----
                final(self).prc_mp.unchanged_except(&old(self).prc_mp, process_ptr),
                final(self).prc_mp.perms_wf(),
                final(self).prc_mp.spec_index(process_ptr).locking_thread() is None,
                !final(self).prc_mp.spec_index(process_ptr).locked(),
                final(self).prc_mp.lock_id_by_key(process_ptr) == old(self).prc_mp.lock_id_by_key(process_ptr),
                wunlock_ensures(old(self).prc_mp.spec_index(process_ptr), final(self).prc_mp.spec_index(process_ptr)),
                process_objects_unlocked_except(old(self).prc_mp, old(lctx).thread_id(), set![process_ptr]) ==> process_objects_unlocked(final(self).prc_mp, final(lctx).thread_id()),
                // ---- LocalContext: lock dropped; thread preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` transitions it Acquire -> Release, so restating
                // `== old` would contradict it and make the postcondition `false`
                // in an Acquire section. `unlock_ensures` is the source of truth
                // for the phase transition (same trap as the NOTE on
                // `LockedArray::wunlock`). user_view is separately preserved.
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,
                final(lctx).lock_id_set() == old(lctx).lock_id_set().remove((old(self).prc_mp.lock_id_by_key(process_ptr), KernelObjId::Process(process_ptr))),
                typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Process(process_ptr)),
        {
            proof {
                assert({
                    &&& old(self).prc_mp.perms_wf()
                    &&& old(self).prc_mp.spec_index(process_ptr).inv()
                }) by { reveal(process_perms_wf); };
                assert(old(lctx).lock_entry_contains(old(self).prc_mp.lock_id_by_key(process_ptr), KernelObjId::Process(process_ptr))) by { reveal(LockedMap::typed_lock_map_aligned); };
                assert(old(lctx).lock_id_set().contains((old(self).prc_mp.lock_id_by_key(process_ptr), KernelObjId::Process(process_ptr)))) by { reveal(lock_id_set_aligned); };
            }
            self.prc_mp.wunlock(process_ptr, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::Process(process_ptr)));
            // Re-establish inv(). Only `process_map[process_ptr]`'s lock state
            // moved; every process payload view, every other entry, and every
            // other KernelK field is byte-equal pre/post. Same template as
            // wlock_process_unless_killed.
            proof {
                assert(process_perms_wf(self.prc_mp)) by { reveal(process_perms_wf); };
                assert(process_invariant_fields_unchanged(old(self).prc_mp, self.prc_mp)) by { process_lock_op_preserves_invariant_fields(old(self).prc_mp, self.prc_mp, process_ptr); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.memory_management_inv()) by { process_no_change_imply_memory_management_inv(*old(self), *self); };
                assert(self.process_management_inv()) by { process_no_change_imply_process_management_inv(*old(self), *self); };
                assert(iommu_root_table_process_wf(&self.irt, self.prc_mp, self.it_mp)) by { lemma_no_change_imply_iommu_root_table_process_wf_forall(); };
                assert(process_pci_function_ownership_wf(&self.irt, self.prc_mp)) by { lemma_no_change_imply_process_pci_function_ownership_wf_forall(); };
                assert(iommu_tlb_wf_spec(self.iommu_tlb, &self.irt, self.prc_mp, self.it_mp)) by { lemma_no_change_imply_iommu_tlb_wf_spec_forall(); };
                assert(cpu_dirty_map_wf(self.ctn_mp, self.prc_mp, self.cpu_arr, self.cpu_tlb, self.pt_mp)) by { lemma_no_change_imply_cpu_dirty_map_wf_forall(); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
            }
        }
}
} // verus!
