#[cfg(verus_keep_ghost)]
use super::locker_unlocker_cpu_set_eof::{cpu_set_lock_op_eof, mark_kill_cpu_set_eof};
use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
    pub fn wlock_cpu_set(&mut self, cpu_set_ptr: RwLockCpuSetPtr, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).cpu_set_mp.dom().contains(cpu_set_ptr),
            !old(self).cpu_set_mp.spec_index(cpu_set_ptr).being_killed(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(self).pg_arr.spec_index(held_page).view().view().orders_below_allocator_locks(),
            forall|held_thread: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(held_thread)] old(lctx).thread_lock_map().dom().contains(held_thread) ==> !(old(self).thr_mp.spec_index(held_thread).view().state is SCHEDULED),
            forall|held_cpu_set: RwLockCpuSetPtr| #![trigger old(lctx).cpu_set_lock_map().dom().contains(held_cpu_set)] old(lctx).cpu_set_lock_map().dom().contains(held_cpu_set)
                ==> held_cpu_set < cpu_set_ptr || old(self).cpu_set_mp.spec_index(held_cpu_set).being_killed(),
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
            reveal(LocalContext::lock_id_acyclic); reveal(pagetable_window_typed_lock_map_aligned); reveal(UnLockedMap::typed_flag_lock_map_aligned); reveal(iommu_root_table_typed_lock_map_aligned);
            reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned);
        };
        assert(!old(self).cpu_set_mp.spec_index(cpu_set_ptr).locked_by_thread(old(lctx).thread_id())) by {
            if old(self).cpu_set_mp.spec_index(cpu_set_ptr).locked_by_thread(old(lctx).thread_id()) {
                assert(old(lctx).cpu_set_lock_map().dom().contains(cpu_set_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
            }
        };
        assert(wlock_requires(self.cpu_set_mp.spec_index(cpu_set_ptr), &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
        let ret = self.cpu_set_mp.wlock_unless_killed(cpu_set_ptr, Tracked(&mut *lctx), Ghost(KernelObjId::CpuSet(cpu_set_ptr))).unwrap();
        proof {
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
            cpu_set_lock_op_eof(*old(self), *self, cpu_set_ptr);
        }
        ret
    }

    /// Write-lock `cpu_set_ptr` unless its container's killer marked it; a marked set returns `None` and nothing changes.
    pub fn wlock_cpu_set_unless_killed(&mut self, cpu_set_ptr: RwLockCpuSetPtr, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Option<Tracked<LockPerm>>)
        requires
            old(self).inv(),
            old(self).cpu_set_mp.dom().contains(cpu_set_ptr),
            !old(lctx).cpu_set_lock_map().dom().contains(cpu_set_ptr),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(self).pg_arr.spec_index(held_page).view().view().orders_below_allocator_locks(),
            forall|held_thread: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(held_thread)] old(lctx).thread_lock_map().dom().contains(held_thread) ==> !(old(self).thr_mp.spec_index(held_thread).view().state is SCHEDULED),
            forall|held_cpu_set: RwLockCpuSetPtr| #![trigger old(lctx).cpu_set_lock_map().dom().contains(held_cpu_set)] old(lctx).cpu_set_lock_map().dom().contains(held_cpu_set)
                ==> held_cpu_set < cpu_set_ptr || old(self).cpu_set_mp.spec_index(held_cpu_set).being_killed(),
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
            (ret is None) == old(self).cpu_set_mp.spec_index(cpu_set_ptr).being_killed(),
            ret is None ==> final(self).cpu_set_mp.spec_index(cpu_set_ptr) == old(self).cpu_set_mp.spec_index(cpu_set_ptr) && *final(lctx) == *old(lctx),
            ret is Some ==> wlock_ensures(old(self).cpu_set_mp.spec_index(cpu_set_ptr), final(self).cpu_set_mp.spec_index(cpu_set_ptr), old(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr), final(lctx), ret->Some_0.view()),
            ret is Some ==> lock_ensures(old(lctx), final(lctx), old(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr), KernelObjId::CpuSet(cpu_set_ptr)),
    {
        assert(old(self).cpu_set_mp.perms_wf() && old(self).cpu_set_mp.spec_index(cpu_set_ptr).inv()) by { cpu_set_perms_wf_map(old(self).cpu_set_mp); cpu_set_perms_wf_at(old(self).cpu_set_mp, cpu_set_ptr); };
        proof {
            if !old(self).cpu_set_mp.spec_index(cpu_set_ptr).being_killed() {
                assert(old(lctx).lock_id_acyclic(old(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr))) by {
                    reveal(LocalContext::lock_id_acyclic); reveal(pagetable_window_typed_lock_map_aligned); reveal(UnLockedMap::typed_flag_lock_map_aligned); reveal(iommu_root_table_typed_lock_map_aligned);
                    reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned);
                };
            }
        }
        assert(!old(self).cpu_set_mp.spec_index(cpu_set_ptr).locked_by_thread(old(lctx).thread_id())) by {
            if old(self).cpu_set_mp.spec_index(cpu_set_ptr).locked_by_thread(old(lctx).thread_id()) {
                assert(old(lctx).cpu_set_lock_map().dom().contains(cpu_set_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
            }
        };
        assert(wlock_requires(self.cpu_set_mp.spec_index(cpu_set_ptr), &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
        let ret = self.cpu_set_mp.wlock_unless_killed(cpu_set_ptr, Tracked(&mut *lctx), Ghost(KernelObjId::CpuSet(cpu_set_ptr)));
        proof {
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
            cpu_set_lock_op_eof(*old(self), *self, cpu_set_ptr);
        }
        ret
    }

    /// Write-lock the cpu set `cpu_set_ptr` of the marked container `container_ptr`, which owns no process or thread, and
    /// mark the set for the same killer, whose process this thread write-holds. The held entry moves to the sunk id a
    /// marked object reports.
    pub fn wlock_cpu_set_and_mark_kill(&mut self, container_ptr: RwLockContainerPtr, cpu_set_ptr: RwLockCpuSetPtr, killer_info: KillerInfo, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).ctn_mp.dom().contains(container_ptr),
            old(self).ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set == cpu_set_ptr,
            old(self).ctn_mp.spec_index(container_ptr).killer_info() == Some(killer_info),
            old(self).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty(),
            old(self).ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().is_empty(),
            typed_lock_map_contains_mode(old(lctx).process_lock_map(), killer_info.process, TypedLockMode::Write),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(self).pg_arr.spec_index(held_page).view().view().orders_below_allocator_locks(),
            forall|held_thread: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(held_thread)] old(lctx).thread_lock_map().dom().contains(held_thread) ==> !(old(self).thr_mp.spec_index(held_thread).view().state is SCHEDULED),
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            final(self).inv(),
            typed_lock_maps_aligned(final(self), final(lctx)),
            *final(self) == (KernelK { cpu_set_mp: final(self).cpu_set_mp, ..*old(self) }),
            final(self).cpu_set_mp.unchanged_except(&old(self).cpu_set_mp, cpu_set_ptr),
            final(self).cpu_set_mp.perms_wf(),
            final(self).cpu_set_mp.spec_index(cpu_set_ptr).view() == old(self).cpu_set_mp.spec_index(cpu_set_ptr).view(),
            final(self).cpu_set_mp.spec_index(cpu_set_ptr).view_rodata() == old(self).cpu_set_mp.spec_index(cpu_set_ptr).view_rodata(),
            final(self).cpu_set_mp.spec_index(cpu_set_ptr).view_ghost() == old(self).cpu_set_mp.spec_index(cpu_set_ptr).view_ghost(),
            !old(self).cpu_set_mp.spec_index(cpu_set_ptr).being_killed(),
            final(self).cpu_set_mp.spec_index(cpu_set_ptr).being_killed(),
            final(self).cpu_set_mp.spec_index(cpu_set_ptr).killer_info() == Some(killer_info),
            final(self).cpu_set_mp.spec_index(cpu_set_ptr).locking_thread() == (RwLockState::Write { thread_id: final(lctx).thread_id(), lock_id: ret.view().lock_id() }),
            ret.view().state() is WriteLock,
            ret.view().thread_id() == final(lctx).thread_id(),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::CpuSet(cpu_set_ptr), TypedHeldLock { lock_id: final(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr), mode: TypedLockMode::Write }),
    {
        proof {
            container_cpu_set_wf_container_at(old(self).ctn_mp, old(self).cpu_set_mp, container_ptr);
            assert(old(self).cpu_set_mp.perms_wf() && old(self).cpu_set_mp.spec_index(cpu_set_ptr).inv()) by { cpu_set_perms_wf_map(old(self).cpu_set_mp); cpu_set_perms_wf_at(old(self).cpu_set_mp, cpu_set_ptr); };
            assert(!old(self).cpu_set_mp.spec_index(cpu_set_ptr).being_killed()) by {
                old(self).prc_mp.typed_lock_map_aligned_write_at(old(lctx).process_lock_map(), old(lctx).thread_id(), killer_info.process);
                cpu_set_kill_mark_wf_at(old(self).ctn_mp, old(self).cpu_set_mp, old(self).prc_mp, cpu_set_ptr);
                old(self).cpu_set_mp.typed_lock_map_aligned_locked_at(old(lctx).cpu_set_lock_map(), old(lctx).thread_id(), cpu_set_ptr);
            };
            assert(old(lctx).lock_id_acyclic(old(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr))) by {
                reveal(LocalContext::lock_id_acyclic); reveal(pagetable_window_typed_lock_map_aligned); reveal(UnLockedMap::typed_flag_lock_map_aligned); reveal(iommu_root_table_typed_lock_map_aligned);
                reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned);
            };
            assert(!old(self).cpu_set_mp.spec_index(cpu_set_ptr).locked_by_thread(old(lctx).thread_id())) by {
                old(self).cpu_set_mp.typed_lock_map_aligned_locked_at(old(lctx).cpu_set_lock_map(), old(lctx).thread_id(), cpu_set_ptr);
            };
        }
        assert(wlock_requires(self.cpu_set_mp.spec_index(cpu_set_ptr), &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
        let ret = self.cpu_set_mp.try_wlock_and_mark_kill(cpu_set_ptr, Tracked(&mut *lctx), Ghost(KernelObjId::CpuSet(cpu_set_ptr)), killer_info).unwrap();
        proof {
            let entry = TypedHeldLock { lock_id: old(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr), mode: TypedLockMode::Write };
            lctx.update_lock_id(KernelObjId::CpuSet(cpu_set_ptr), old(self).cpu_set_mp.lock_id_by_key(cpu_set_ptr), self.cpu_set_mp.lock_id_by_key(cpu_set_ptr));
            map_insert_overwrite_lemma(old(lctx).cpu_set_lock_map(), cpu_set_ptr, entry, TypedHeldLock { lock_id: self.cpu_set_mp.lock_id_by_key(cpu_set_ptr), mode: TypedLockMode::Write });
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            mark_kill_cpu_set_eof(*old(self), *self, *old(lctx), container_ptr, cpu_set_ptr, killer_info);
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
            !old(self).cpu_set_mp.spec_index(cpu_set_ptr).being_killed(),
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
