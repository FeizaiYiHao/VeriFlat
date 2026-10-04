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
            !old(lctx).cpu_set_lock_map().dom().contains(cpu_set_ptr),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(self).pg_arr.lock_id_by_index(held_page).major < CPU_SET_LOCK_MAJOR,
            forall|held_thread: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(held_thread)] old(lctx).thread_lock_map().dom().contains(held_thread) ==> !(old(self).thr_mp.spec_index(held_thread).view().state is SCHEDULED),
            forall|held_cpu_set: RwLockCpuSetPtr| #![trigger old(lctx).cpu_set_lock_map().dom().contains(held_cpu_set)] old(lctx).cpu_set_lock_map().dom().contains(held_cpu_set) ==> held_cpu_set < cpu_set_ptr,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            forall|key: usize|
                #![trigger old(self).cpu_set_mp.view().spec_index(key)]
                #![trigger final(self).cpu_set_mp.view().spec_index(key)]
                old(self).cpu_set_mp.dom().contains(key) ==> {
                    &&& final(self).cpu_set_mp.view().spec_index(key).is_init() == old(self).cpu_set_mp.view().spec_index(key).is_init()
                    &&& final(self).cpu_set_mp.view().spec_index(key).addr() == old(self).cpu_set_mp.view().spec_index(key).addr()
                },
            final(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
            final(self).cpu_set_mp.spec_index(cpu_set_ptr).is_init() == old(self).cpu_set_mp.spec_index(cpu_set_ptr).is_init(),
            typed_lock_maps_aligned(final(self), final(lctx)),
            *final(self) == (KernelK { cpu_set_mp: final(self).cpu_set_mp, ..*old(self) }),
            final(self).cpu_set_mp.unchanged_except(&old(self).cpu_set_mp, cpu_set_ptr),
            final(self).cpu_set_mp.perms_wf(),
            wlock_ensures(old(self).cpu_set_mp.spec_index(cpu_set_ptr), final(self).cpu_set_mp.spec_index(cpu_set_ptr), old(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr), final(lctx), ret.view()),
            lock_ensures(old(lctx), final(lctx), old(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr), KernelObjId::CpuSet(cpu_set_ptr)),
    {
        assert(old(self).cpu_set_mp.perms_wf() && old(self).cpu_set_mp.spec_index(cpu_set_ptr).inv()) by { reveal(cpu_set_perms_wf); };
        assert(old(lctx).lock_id_acyclic(old(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr))) by {
            reveal(LocalContext::lock_id_acyclic); reveal(UnLockedMap::typed_flag_lock_map_aligned);
            reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned);
        };
        assert(!old(self).cpu_set_mp.spec_index(cpu_set_ptr).locked_by_thread(old(lctx).thread_id())) by {
            if old(self).cpu_set_mp.spec_index(cpu_set_ptr).locked_by_thread(old(lctx).thread_id()) {
                assert(old(lctx).cpu_set_lock_map().dom().contains(cpu_set_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
            }
        };
        assert(wlock_requires(self.cpu_set_mp.spec_index(cpu_set_ptr), &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
        let ret = self.cpu_set_mp.wlock(cpu_set_ptr, Tracked(&mut *lctx), Ghost(KernelObjId::CpuSet(cpu_set_ptr)));
        proof {
            assert(cpu_set_perms_wf(self.cpu_set_mp)) by { reveal(cpu_set_perms_wf); };
            assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
            assert(self.memory_management_inv()) by { reveal(cpu_set_pages_wf); };
            assert(self.process_management_inv()) by { reveal(container_cpu_wf); reveal(container_cpu_set_wf); };
            assert(self.inv()) by { reveal(cpu_dirty_map_contains_container_processes); };
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
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
            typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), cpu_set_ptr, TypedLockMode::Write),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).cpu_set_mp.spec_index(cpu_set_ptr).locking_thread()->Write_lock_id,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
            typed_lock_maps_aligned(final(self), final(lctx)),
            *final(self) == (KernelK { cpu_set_mp: final(self).cpu_set_mp, ..*old(self) }),
            final(self).cpu_set_mp.unchanged_except(&old(self).cpu_set_mp, cpu_set_ptr),
            final(self).cpu_set_mp.perms_wf(),
            final(self).cpu_set_mp.spec_index(cpu_set_ptr).locking_thread() is None,
            !final(self).cpu_set_mp.spec_index(cpu_set_ptr).locked(),
            final(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr) == old(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr),
            wunlock_ensures(old(self).cpu_set_mp.spec_index(cpu_set_ptr), final(self).cpu_set_mp.spec_index(cpu_set_ptr)),
            unlock_ensures(old(lctx), final(lctx), KernelObjId::CpuSet(cpu_set_ptr), old(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr)),
    {
        proof {
            assert({ &&& old(self).cpu_set_mp.perms_wf() &&& old(self).cpu_set_mp.spec_index(cpu_set_ptr).inv() }) by { reveal(cpu_set_perms_wf); };
            assert(old(lctx).lock_entry_contains(old(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr), KernelObjId::CpuSet(cpu_set_ptr))) by { reveal(LockedMap::typed_lock_map_aligned); };
        }
        assert(self.cpu_set_mp.spec_index(cpu_set_ptr).wlocked_by(&*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
        self.cpu_set_mp.wunlock(cpu_set_ptr, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::CpuSet(cpu_set_ptr)));
        proof {
            assert(cpu_set_perms_wf(self.cpu_set_mp)) by { reveal(cpu_set_perms_wf); };
            assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
            assert(cpu_set_pages_wf(self.cpu_set_mp, self.pg_arr)) by { reveal(cpu_set_pages_wf); };
            assert(container_cpu_set_wf(self.ctn_mp, self.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
            assert(container_cpu_wf(self.ctn_mp, self.cpu_set_mp, self.cpu_arr)) by { reveal(container_cpu_wf); reveal(container_cpu_set_wf); };
            assert(cpu_dirty_map_wf(self.ctn_mp, self.cpu_set_mp, self.prc_mp, self.cpu_arr, self.cpu_tlb, self.pt_mp, self.pcid_needflush)) by { reveal(cpu_dirty_map_contains_container_processes); };
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
        }
    }
}
} // verus!
