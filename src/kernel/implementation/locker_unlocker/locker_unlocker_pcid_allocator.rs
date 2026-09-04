use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
    pub fn wlock_pcid_allocator(
        &mut self,
        allocator_ptr: RwLockPcidAllocatorPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
    ) -> (ret: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).pcid_allc_mp.dom().contains(allocator_ptr),
            old(lctx).kernel_view_locking_state() is Acquire,
            wlock_requires(old(self).pcid_allc_mp.spec_index(allocator_ptr), old(lctx)),
            pcid_allocator_lock_acquire_scope(old(self), old(lctx), allocator_ptr),
            typed_lock_maps_aligned(old(self), old(lctx)),
            lock_id_set_aligned(old(lctx)),
        ensures
            final(self).inv(),
            kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
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
            final(self).prc_mp == old(self).prc_mp,
            final(self).thr_mp == old(self).thr_mp,
            final(self).ep_mp == old(self).ep_mp,
            final(self).allc_4k_mp == old(self).allc_4k_mp,
            final(self).allc_2m_mp == old(self).allc_2m_mp,
            final(self).allc_1g_mp == old(self).allc_1g_mp,
            final(self).dflt_pt == old(self).dflt_pt,
            final(self).pcid_allc_mp.unchanged_except(&old(self).pcid_allc_mp, allocator_ptr),
            final(self).pcid_allc_mp.perms_wf(),
            pcid_allocator_objects_unlocked(old(self).pcid_allc_mp, old(lctx).thread_id()) ==> pcid_allocator_objects_unlocked_except(final(self).pcid_allc_mp, final(lctx).thread_id(), set![allocator_ptr]),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            wlock_ensures(old(self).pcid_allc_mp.spec_index(allocator_ptr), final(self).pcid_allc_mp.spec_index(allocator_ptr), old(self).pcid_allc_mp.lock_id_by_key(allocator_ptr), final(lctx), ret.view()),
            final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(self).pcid_allc_mp.lock_id_by_key(allocator_ptr), KernelObjId::PcidAllocator(allocator_ptr))),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::PcidAllocator(allocator_ptr), TypedHeldLock { lock_id: final(self).pcid_allc_mp.lock_id_by_key(allocator_ptr), mode: TypedLockMode::Write }),
            pcid_allocator_lock_held_scope(final(self), final(lctx), allocator_ptr),
            final(lctx).held_lock_majors_lt(PROCESS_LOCK_MAJOR),
    {
        proof {
            assert(old(self).pcid_allc_mp.perms_wf()) by { reveal(pcid_allocator_perms_wf); };
            assert(old(lctx).held_lock_majors_lt(PCID_ALLOCATOR_LOCK_MAJOR)) by {     reveal(lock_id_set_aligned);  reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned); reveal(cpu_array_wf); reveal(container_perms_wf); };
            assert(old(lctx).lock_id_acyclic(old(self).pcid_allc_mp.lock_id_by_key(allocator_ptr))) by {    reveal(lock_id_set_aligned);  reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned); reveal(container_cpu_wf); reveal(container_pcid_allocator_wf); reveal(container_perms_wf); reveal(pcid_allocator_perms_wf); };
        }
        let ret = self.pcid_allc_mp.wlock(allocator_ptr, Tracked(&mut *lctx), Ghost(KernelObjId::PcidAllocator(allocator_ptr)));
        proof {
            assert(pcid_allocator_perms_wf(self.pcid_allc_mp)) by { reveal(pcid_allocator_perms_wf); };
            assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
            assert(self.memory_management_inv()) by { assert(pcid_allocator_pages_wf(self.pg_arr, self.pcid_allc_mp)) by { reveal(pcid_allocator_pages_wf); }; };
            assert(self.process_management_inv()) by { assert(container_pcid_allocator_wf(self.ctn_mp, self.pcid_allc_mp)) by { reveal(container_pcid_allocator_wf); }; assert(process_pcid_allocator_wf(self.ctn_mp, self.prc_mp, self.pcid_allc_mp)) by { reveal(process_pcid_allocator_wf);   }; };
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            let cpu_id = choose|cpu_id: CpuId|
                #![trigger old(self).cpu_arr.spec_index(cpu_id)]
                exists|container_ptr: RwLockContainerPtr|
                    #![trigger old(lctx).base_lock_scope(set![cpu_id], set![container_ptr], Set::empty(), Set::empty(), Set::empty())]
                {
                    &&& old(lctx).base_lock_scope(set![cpu_id], set![container_ptr], Set::empty(), Set::empty(), Set::empty())
                    &&& index_valid(NUM_CPUS, cpu_id)
                    &&& old(self).ctn_mp.dom().contains(container_ptr)
                    &&& old(self).cpu_arr.spec_index(cpu_id).view().view().owning_container == container_ptr
                    &&& old(self).ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator == allocator_ptr
                };
            let container_ptr = choose|container_ptr: RwLockContainerPtr|
                #![trigger old(lctx).base_lock_scope(set![cpu_id], set![container_ptr], Set::empty(), Set::empty(), Set::empty())]
            {
                &&& old(lctx).base_lock_scope(set![cpu_id], set![container_ptr], Set::empty(), Set::empty(), Set::empty())
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& old(self).ctn_mp.dom().contains(container_ptr)
                &&& old(self).cpu_arr.spec_index(cpu_id).view().view().owning_container == container_ptr
                &&& old(self).ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator == allocator_ptr
            };
            assert({
                &&& lctx.object_lock_scope(Set::empty(), set![cpu_id], set![container_ptr], Set::empty(), Set::empty(), Set::empty(), Set::empty(), set![allocator_ptr], Set::empty(), Set::empty())
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& self.ctn_mp.dom().contains(container_ptr)
                &&& self.cpu_arr.spec_index(cpu_id).view().view().owning_container == container_ptr
                &&& self.ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator == allocator_ptr
            }) by {    broadcast use vstd::map::lemma_map_insert_domain; };
            assert(lctx.held_lock_majors_lt(PROCESS_LOCK_MAJOR)) by {  reveal(pcid_allocator_perms_wf); assert(PCID_ALLOCATOR_LOCK_MAJOR < PROCESS_LOCK_MAJOR) by (compute); broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different; };
            assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
        }
        ret
    }

    pub fn wunlock_pcid_allocator(
        &mut self,
        allocator_ptr: RwLockPcidAllocatorPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
        lock_perm: Tracked<LockPerm>,
    )
        requires
            old(self).inv(),
            old(self).pcid_allc_mp.dom().contains(allocator_ptr),
            old(self).pcid_allc_mp.spec_index(allocator_ptr).wlocked_by(old(lctx)),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).pcid_allc_mp.spec_index(allocator_ptr).locking_thread()->Write_lock_id,
            typed_lock_maps_aligned(old(self), old(lctx)),
            lock_id_set_aligned(old(lctx)),
        ensures
            final(self).inv(),
            kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
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
            final(self).prc_mp == old(self).prc_mp,
            final(self).thr_mp == old(self).thr_mp,
            final(self).ep_mp == old(self).ep_mp,
            final(self).allc_4k_mp == old(self).allc_4k_mp,
            final(self).allc_2m_mp == old(self).allc_2m_mp,
            final(self).allc_1g_mp == old(self).allc_1g_mp,
            final(self).dflt_pt == old(self).dflt_pt,
            final(self).pcid_allc_mp.unchanged_except(&old(self).pcid_allc_mp, allocator_ptr),
            final(self).pcid_allc_mp.perms_wf(),
            final(self).pcid_allc_mp.spec_index(allocator_ptr).locking_thread() is None,
            !final(self).pcid_allc_mp.spec_index(allocator_ptr).locked(),
            final(self).pcid_allc_mp.lock_id_by_key(allocator_ptr) == old(self).pcid_allc_mp.lock_id_by_key(allocator_ptr),
            wunlock_ensures(old(self).pcid_allc_mp.spec_index(allocator_ptr), final(self).pcid_allc_mp.spec_index(allocator_ptr)),
            pcid_allocator_objects_unlocked_except(old(self).pcid_allc_mp, old(lctx).thread_id(), set![allocator_ptr]) ==> pcid_allocator_objects_unlocked(final(self).pcid_allc_mp, final(lctx).thread_id()),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).lock_id_set() == old(lctx).lock_id_set().remove((old(self).pcid_allc_mp.lock_id_by_key(allocator_ptr), KernelObjId::PcidAllocator(allocator_ptr))),
            typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::PcidAllocator(allocator_ptr)),
            unlock_ensures(old(lctx), final(lctx), (), lock_perm.view().lock_id(), KernelObjId::PcidAllocator(allocator_ptr), old(self).pcid_allc_mp.lock_id_by_key(allocator_ptr)),
    {
        proof {
            assert({ &&& old(self).pcid_allc_mp.perms_wf() &&& old(self).pcid_allc_mp.spec_index(allocator_ptr).inv() }) by { reveal(pcid_allocator_perms_wf); };
            assert(old(lctx).lock_entry_contains(old(self).pcid_allc_mp.lock_id_by_key(allocator_ptr), KernelObjId::PcidAllocator(allocator_ptr))) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(old(lctx).lock_id_set().contains((old(self).pcid_allc_mp.lock_id_by_key(allocator_ptr), KernelObjId::PcidAllocator(allocator_ptr)))) by { reveal(lock_id_set_aligned); };
        }
        self.pcid_allc_mp.wunlock(allocator_ptr, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::PcidAllocator(allocator_ptr)));
        proof {
            assert(pcid_allocator_perms_wf(self.pcid_allc_mp)) by { reveal(pcid_allocator_perms_wf); };
            assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
            assert(self.memory_management_inv()) by { assert(pcid_allocator_pages_wf(self.pg_arr, self.pcid_allc_mp)) by { reveal(pcid_allocator_pages_wf); }; };
            assert(self.process_management_inv()) by { assert(container_pcid_allocator_wf(self.ctn_mp, self.pcid_allc_mp)) by { reveal(container_pcid_allocator_wf); }; assert(process_pcid_allocator_wf(self.ctn_mp, self.prc_mp, self.pcid_allc_mp)) by { reveal(process_pcid_allocator_wf);   }; };
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
        }
    }
}
} // verus!
