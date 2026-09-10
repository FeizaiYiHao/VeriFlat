use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
    pub fn wlock_cpu_set(
        &mut self,
        cpu_set_ptr: RwLockCpuSetPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
    ) -> (ret: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).cpu_set_mp.dom().contains(cpu_set_ptr),
            old(lctx).kernel_view_locking_state() is Acquire,
            wlock_requires(old(self).cpu_set_mp.spec_index(cpu_set_ptr), old(lctx)),
            old(lctx).lock_id_acyclic(old(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr)),
            typed_lock_maps_aligned(old(self), old(lctx)),
            lock_id_set_aligned(old(lctx)),
        ensures
            final(self).inv(),
            forall|key: usize|
                #![trigger old(self).cpu_set_mp.view().spec_index(key)]
                #![trigger final(self).cpu_set_mp.view().spec_index(key)]
                old(self).cpu_set_mp.dom().contains(key) ==> {
                    &&& final(self).cpu_set_mp.view().spec_index(key).is_init() == old(self).cpu_set_mp.view().spec_index(key).is_init()
                    &&& final(self).cpu_set_mp.view().spec_index(key).addr() == old(self).cpu_set_mp.view().spec_index(key).addr()
                },
            final(self).cpu_set_mp.spec_index(cpu_set_ptr).is_init() == old(self).cpu_set_mp.spec_index(cpu_set_ptr).is_init(),
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
            final(self).pcid_allc_mp == old(self).pcid_allc_mp,
            final(self).prc_mp == old(self).prc_mp,
            final(self).thr_mp == old(self).thr_mp,
            final(self).ep_mp == old(self).ep_mp,
            final(self).allc_4k_mp == old(self).allc_4k_mp,
            final(self).allc_2m_mp == old(self).allc_2m_mp,
            final(self).allc_1g_mp == old(self).allc_1g_mp,
            final(self).dflt_pt == old(self).dflt_pt,
            final(self).cpu_set_mp.unchanged_except(&old(self).cpu_set_mp, cpu_set_ptr),
            final(self).cpu_set_mp.perms_wf(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            wlock_ensures(old(self).cpu_set_mp.spec_index(cpu_set_ptr), final(self).cpu_set_mp.spec_index(cpu_set_ptr), old(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr), final(lctx), ret.view()),
            final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr), KernelObjId::CpuSet(cpu_set_ptr))),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::CpuSet(cpu_set_ptr), TypedHeldLock { lock_id: final(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr), mode: TypedLockMode::Write }),
            final(lctx).held_lock_majors_lt(SCHEDULER_LOCK_MAJOR),
    {
        proof {
            assert(old(self).cpu_set_mp.perms_wf() && old(self).cpu_set_mp.spec_index(cpu_set_ptr).is_init()) by { reveal(cpu_set_perms_wf); };
        }
        let ret = self.cpu_set_mp.wlock(cpu_set_ptr, Tracked(&mut *lctx), Ghost(KernelObjId::CpuSet(cpu_set_ptr)));
        proof {
            assert(cpu_set_perms_wf(self.cpu_set_mp)) by { reveal(cpu_set_perms_wf); };
            assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
            assert(self.memory_management_inv()) by { reveal(cpu_set_pages_wf); };
            assert(self.process_management_inv()) by { reveal(container_cpu_wf); reveal(container_cpu_set_wf); };
            assert(self.inv()) by { reveal(cpu_dirty_map_contains_container_processes); };
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
        }
        ret
    }

    pub fn wunlock_cpu_set(
        &mut self,
        cpu_set_ptr: RwLockCpuSetPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
        lock_perm: Tracked<LockPerm>,
    )
        requires
            old(self).inv(),
            old(self).cpu_set_mp.dom().contains(cpu_set_ptr),
            old(self).cpu_set_mp.spec_index(cpu_set_ptr).wlocked_by(old(lctx)),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).cpu_set_mp.spec_index(cpu_set_ptr).locking_thread()->Write_lock_id,
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
            final(self).pcid_allc_mp == old(self).pcid_allc_mp,
            final(self).prc_mp == old(self).prc_mp,
            final(self).thr_mp == old(self).thr_mp,
            final(self).ep_mp == old(self).ep_mp,
            final(self).allc_4k_mp == old(self).allc_4k_mp,
            final(self).allc_2m_mp == old(self).allc_2m_mp,
            final(self).allc_1g_mp == old(self).allc_1g_mp,
            final(self).dflt_pt == old(self).dflt_pt,
            final(self).cpu_set_mp.unchanged_except(&old(self).cpu_set_mp, cpu_set_ptr),
            final(self).cpu_set_mp.perms_wf(),
            final(self).cpu_set_mp.spec_index(cpu_set_ptr).locking_thread() is None,
            !final(self).cpu_set_mp.spec_index(cpu_set_ptr).locked(),
            final(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr) == old(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr),
            wunlock_ensures(old(self).cpu_set_mp.spec_index(cpu_set_ptr), final(self).cpu_set_mp.spec_index(cpu_set_ptr)),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).lock_id_set() == old(lctx).lock_id_set().remove((old(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr), KernelObjId::CpuSet(cpu_set_ptr))),
            typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::CpuSet(cpu_set_ptr)),
            unlock_ensures(old(lctx), final(lctx), KernelObjId::CpuSet(cpu_set_ptr), old(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr)),
    {
        proof {
            assert({ &&& old(self).cpu_set_mp.perms_wf() &&& old(self).cpu_set_mp.spec_index(cpu_set_ptr).inv() }) by { reveal(cpu_set_perms_wf); };
            assert(old(lctx).lock_entry_contains(old(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr), KernelObjId::CpuSet(cpu_set_ptr))) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(old(lctx).lock_id_set().contains((old(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr), KernelObjId::CpuSet(cpu_set_ptr)))) by { reveal(lock_id_set_aligned); };
        }
        self.cpu_set_mp.wunlock(cpu_set_ptr, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::CpuSet(cpu_set_ptr)));
        proof {
            assert(cpu_set_perms_wf(self.cpu_set_mp)) by { reveal(cpu_set_perms_wf); };
            assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
            assert(self.memory_management_inv()) by { reveal(cpu_set_pages_wf); };
            assert(self.process_management_inv()) by { reveal(container_cpu_wf); reveal(container_cpu_set_wf); };
            assert(self.inv()) by { reveal(cpu_dirty_map_contains_container_processes); };
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
        }
    }
}
} // verus!
