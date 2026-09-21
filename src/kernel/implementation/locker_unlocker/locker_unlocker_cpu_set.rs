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
            !typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), cpu_set_ptr, TypedLockMode::Write),
            old(lctx).lock_id_acyclic(old(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr)),
            typed_lock_maps_aligned(old(self), old(lctx)),
            lock_id_set_aligned(old(lctx)),
        ensures
            final(self).inv(),
            final(self).cpu_set_mp.spec_index(cpu_set_ptr).is_init() == old(self).cpu_set_mp.spec_index(cpu_set_ptr).is_init(),
            kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            *final(self) == (KernelK { cpu_set_mp: final(self).cpu_set_mp, ..*old(self) }),
            final(self).cpu_set_mp.unchanged_except(&old(self).cpu_set_mp, cpu_set_ptr),
            final(self).cpu_set_mp.perms_wf(),
            wlock_ensures(old(self).cpu_set_mp.spec_index(cpu_set_ptr), final(self).cpu_set_mp.spec_index(cpu_set_ptr), old(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr), final(lctx), ret.view()),
            lock_ensures(old(lctx), final(lctx), old(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr), KernelObjId::CpuSet(cpu_set_ptr)),
            final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr), KernelObjId::CpuSet(cpu_set_ptr))),
            final(lctx).held_lock_majors_lt(SCHEDULER_LOCK_MAJOR),
    {
        assert(old(self).cpu_set_mp.perms_wf() && old(self).cpu_set_mp.spec_index(cpu_set_ptr).inv()) by { reveal(cpu_set_perms_wf); };
        assert(!old(self).cpu_set_mp.spec_index(cpu_set_ptr)
            .wlocked_by_thread(old(lctx).thread_id())) by {
            if old(self).cpu_set_mp.spec_index(cpu_set_ptr)
                .wlocked_by_thread(old(lctx).thread_id())
            {
                assert(typed_lock_map_contains_mode(
                    old(lctx).cpu_set_lock_map(),
                    cpu_set_ptr,
                    TypedLockMode::Write,
                )) by {
                    reveal(LockedMap::typed_lock_map_aligned);
                };
            }
        };
        assert(!old(self).cpu_set_mp.spec_index(cpu_set_ptr)
            .wlocked_by(&*old(lctx)));
        assert(wlock_requires(self.cpu_set_mp.spec_index(cpu_set_ptr), &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
        let ret = self.cpu_set_mp.wlock(cpu_set_ptr, Tracked(&mut *lctx), Ghost(KernelObjId::CpuSet(cpu_set_ptr)));
        proof {
            assert(cpu_set_perms_wf(self.cpu_set_mp)) by { reveal(cpu_set_perms_wf); };
            assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
            assert(self.memory_management_inv()) by { reveal(cpu_set_pages_wf); };
            assert(self.process_management_inv()) by { reveal(container_cpu_wf); reveal(container_cpu_set_wf); };
            assert(self.inv()) by { reveal(cpu_dirty_map_contains_container_processes); };
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
            };
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
            lock_id_set_aligned(old(lctx)),
        ensures
            final(self).inv(),
            kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
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
            assert(old(lctx).lock_id_set().contains((old(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr), KernelObjId::CpuSet(cpu_set_ptr)))) by { reveal(lock_id_set_aligned); };
        }
        assert(self.cpu_set_mp.spec_index(cpu_set_ptr).wlocked_by(&*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
        self.cpu_set_mp.wunlock(cpu_set_ptr, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::CpuSet(cpu_set_ptr)));
        proof {
            assert(cpu_set_perms_wf(self.cpu_set_mp)) by { reveal(cpu_set_perms_wf); };
            assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
            assert(self.memory_management_inv()) by { reveal(cpu_set_pages_wf); };
            assert(self.process_management_inv()) by { reveal(container_cpu_wf); reveal(container_cpu_set_wf); };
            assert(self.inv()) by { reveal(cpu_dirty_map_contains_container_processes); };
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
            };
        }
    }
}
} // verus!
