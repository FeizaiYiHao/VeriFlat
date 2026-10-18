#[cfg(verus_keep_ghost)]
use super::locker_unlocker_cpu_set_eof::{cpu_set_lock_op_eof};
use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
    pub fn wlock_cpu_set(&mut self, cpu_set_ptr: RwLockCpuSetPtr, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).cpu_set_mp.dom().contains(cpu_set_ptr),
            old(lctx).kernel_view_locking_state() is Acquire,
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
            final(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
            final(self).cpu_set_mp.spec_index(cpu_set_ptr).is_init() == old(self).cpu_set_mp.spec_index(cpu_set_ptr).is_init(),
            typed_lock_maps_aligned(final(self), final(lctx)),
            *final(self) == (KernelK { cpu_set_mp: final(self).cpu_set_mp, ..*old(self) }),
            final(self).cpu_set_mp.unchanged_except(&old(self).cpu_set_mp, cpu_set_ptr),
            final(self).cpu_set_mp.perms_wf(),
            forall|c: RwLockContainerPtr| #![trigger final(self).cpu_set_mp.spec_index(final(self).ctn_mp.spec_index(c).view_rodata().view().cpu_set)]
                old(self).ctn_mp.dom().contains(c) && old(self).ctn_mp.spec_index(c).view_rodata().view().cpu_set != cpu_set_ptr
                    ==> final(self).cpu_set_mp.spec_index(final(self).ctn_mp.spec_index(c).view_rodata().view().cpu_set) == old(self).cpu_set_mp.spec_index(old(self).ctn_mp.spec_index(c).view_rodata().view().cpu_set),
            wlock_ensures(old(self).cpu_set_mp.spec_index(cpu_set_ptr), final(self).cpu_set_mp.spec_index(cpu_set_ptr), old(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr), final(lctx), ret.view()),
            lock_ensures(old(lctx), final(lctx), old(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr), KernelObjId::CpuSet(cpu_set_ptr)),
    {
        assert(old(self).cpu_set_mp.perms_wf() && old(self).cpu_set_mp.spec_index(cpu_set_ptr).inv()) by { cpu_set_perms_wf_map(old(self).cpu_set_mp); cpu_set_perms_wf_at(old(self).cpu_set_mp, cpu_set_ptr); };
        assert(old(lctx).lock_id_acyclic(old(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr))) by {
            reveal(LocalContext::lock_id_acyclic); reveal(UnLockedMap::typed_flag_lock_map_aligned); reveal(iommu_root_table_typed_lock_map_aligned);
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
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
            cpu_set_lock_op_eof(*old(self), *self, cpu_set_ptr);
        }
        ret
    }

    pub fn wunlock_cpu_set(&mut self, cpu_set_ptr: RwLockCpuSetPtr, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>)
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
            forall|c: RwLockContainerPtr| #![trigger final(self).cpu_set_mp.spec_index(final(self).ctn_mp.spec_index(c).view_rodata().view().cpu_set)]
                old(self).ctn_mp.dom().contains(c) && old(self).ctn_mp.spec_index(c).view_rodata().view().cpu_set != cpu_set_ptr
                    ==> final(self).cpu_set_mp.spec_index(final(self).ctn_mp.spec_index(c).view_rodata().view().cpu_set) == old(self).cpu_set_mp.spec_index(old(self).ctn_mp.spec_index(c).view_rodata().view().cpu_set),
            final(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr) == old(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr),
            wunlock_ensures(old(self).cpu_set_mp.spec_index(cpu_set_ptr), final(self).cpu_set_mp.spec_index(cpu_set_ptr)),
            unlock_ensures(old(lctx), final(lctx), KernelObjId::CpuSet(cpu_set_ptr), old(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr)),
    {
        proof {
            assert({ &&& old(self).cpu_set_mp.perms_wf() &&& old(self).cpu_set_mp.spec_index(cpu_set_ptr).inv() }) by { cpu_set_perms_wf_map(old(self).cpu_set_mp); cpu_set_perms_wf_at(old(self).cpu_set_mp, cpu_set_ptr); };
            assert(old(lctx).lock_entry_contains(old(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr), KernelObjId::CpuSet(cpu_set_ptr))) by { reveal(LockedMap::typed_lock_map_aligned); };
        }
        assert(self.cpu_set_mp.spec_index(cpu_set_ptr).wlocked_by(&*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
        self.cpu_set_mp.wunlock(cpu_set_ptr, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::CpuSet(cpu_set_ptr)));
        proof {
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
            cpu_set_lock_op_eof(*old(self), *self, cpu_set_ptr);
        }
    }
}
} // verus!
