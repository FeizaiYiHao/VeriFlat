#[cfg(verus_keep_ghost)]
use super::locker_unlocker_container_eof::{wlock_container_eof, mark_kill_container_eof, wunlock_container_eof};
use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
    /// Dynamically write-lock the running context's container for the concrete process owner `requested`: the existing
    /// kill record, or a shallower live dynamic holder, is reported without any change.
    pub fn wlock_container_unless_killed(&mut self, container_ptr: RwLockContainerPtr, requested: LockOwnerId,
        Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: DynamicWLockResult)
        requires
            old(self).inv(),
            old(self).ctn_mp.dom().contains(container_ptr),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).container_lock_map().dom().is_empty(),
            old(lctx).process_lock_map().dom().is_empty(),
            old(lctx).thread_lock_map().dom().is_empty(),
            old(lctx).endpoint_lock_map().dom().is_empty(),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).pcid_allocator_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pagetable_lock_map().dom().is_empty(),
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).iommu_root_table_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
            !old(lctx).cpu_lock_map().dom().is_empty(),
            (forall|held_cpu_id: CpuId|
                #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)]
                old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> {
                    &&& index_valid(NUM_CPUS, held_cpu_id)
                    &&& old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().owning_container == container_ptr
                    &&& !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off)
                    &&& old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().container_depth == old(self).ctn_mp.spec_index(container_ptr).view_rodata().view().depth
                    &&& old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().current_process is Some
                    &&& requested == LockOwnerId::Some(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().process_depth)
                }),
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            // ---- Kernel-wide invariant re-established ----
            final(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
            // ---- Every held lock and its dynamic lock id still match lctx (success: container locked; failure: no-op) ----
            typed_lock_maps_aligned(final(self), final(lctx)),
            // ---- Field framing: only container_map's lock state moves ----
            *final(self) == (KernelK { ctn_mp: final(self).ctn_mp, ..*old(self) }),
            // ---- container_map: only the targeted entry's lock state (success) or nothing at all (failure) changed ----
            final(self).ctn_mp.unchanged_except(&old(self).ctn_mp, container_ptr),
            final(self).ctn_mp.perms_wf(),
            // ---- LocalContext phase preservation ----
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            // ---- Killed or depth conflict: complete no-op ----
            !(ret is Acquired) ==> {
                &&& final(self).ctn_mp.spec_index(container_ptr) == old(self).ctn_mp.spec_index(container_ptr)
                &&& *final(lctx) == *old(lctx)
            },
            ret is Killed ==> old(self).ctn_mp.spec_index(container_ptr).killer_info() == Some(ret->Killed_0),
            ret is DepthConflict ==> {
                &&& !old(self).ctn_mp.spec_index(container_ptr).being_killed()
                &&& old(self).ctn_mp.spec_index(container_ptr).lock_process_owner_u() == Some(ret->DepthConflict_observed_owner)
                &&& ret->DepthConflict_observed_owner < requested
            },
            // ---- Success: container locked by us under the requested candidate id ----
            ret is Acquired ==> {
                let new_c = final(self).ctn_mp.spec_index(container_ptr);
                let lock_id = dynamic_container_lock_id(container_ptr, old(self).ctn_mp.spec_index(container_ptr).view_rodata().view().depth, requested);
                &&& !old(self).ctn_mp.spec_index(container_ptr).being_killed()
                &&& !old(self).ctn_mp.spec_index(container_ptr).locked()
                &&& !old(self).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty()
                &&& new_c.locking_thread() == RwLockState::Write { thread_id: final(lctx).thread_id(), lock_id: ret->Acquired_0.view().lock_id() }
                &&& new_c.inv()
                &&& new_c.view() == old(self).ctn_mp.spec_index(container_ptr).view()
                &&& new_c.view_rodata() == old(self).ctn_mp.spec_index(container_ptr).view_rodata()
                &&& new_c.view_ghost() == old(self).ctn_mp.spec_index(container_ptr).view_ghost()
                &&& new_c.control() == LockControl::DynamicProcess(requested)
                &&& ret->Acquired_0.view().state() is WriteLock
                &&& ret->Acquired_0.view().ordering_lock_id() == lock_id
                &&& ret->Acquired_0.view().thread_id() == final(lctx).thread_id()
                &&& final(self).ctn_mp.lock_id_by_key(container_ptr) == lock_id
                &&& typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Container(container_ptr), TypedHeldLock { lock_id, mode: TypedLockMode::Write })
            },
    {
        proof {
            container_perms_wf_map(old(self).ctn_mp);
            container_perms_wf_at(old(self).ctn_mp, container_ptr);
            if !old(self).ctn_mp.spec_index(container_ptr).being_killed() {
                let lock_id = dynamic_container_lock_id(container_ptr, old(self).ctn_mp.spec_index(container_ptr).view_rodata().view().depth, requested);
                assert(old(lctx).lock_id_acyclic(lock_id)) by { reveal(LocalContext::lock_id_acyclic); reveal(pagetable_window_typed_lock_map_aligned); reveal(LockedArray::typed_lock_map_aligned); };
            }
            assert(!old(self).ctn_mp.spec_index(container_ptr).locked_by_thread(old(lctx).thread_id())) by {
                if old(self).ctn_mp.spec_index(container_ptr).locked_by_thread(old(lctx).thread_id()) {
                    assert(old(lctx).container_lock_map().dom().contains(container_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
                }
            };
        }
        let lock_id = Ghost(dynamic_container_lock_id(container_ptr, self.ctn_mp.spec_index(container_ptr).view_rodata().view().depth, requested));
        let res = self.ctn_mp.dynamic_wlock(container_ptr, Tracked(&mut *lctx), lock_id, Ghost(KernelObjId::Container(container_ptr)), requested);
        proof {
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
            wlock_container_eof(*old(self), *self, container_ptr, requested, res is Acquired);
        }
        res
    }

    /// Write-lock a child of a container the killer write-holds and mark it for the killer running on this cpu. A
    /// container another killer already marked is left untouched. On success the held entry moves to the sunk id a
    /// marked object reports. The acquisition requests the killer owner `High`, so it never reports a depth conflict.
    pub fn try_wlock_container_and_mark_kill(&mut self, container_ptr: RwLockContainerPtr, killer_info: KillerInfo, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Option<Tracked<LockPerm>>)
        requires
            old(self).inv(),
            old(self).ctn_mp.dom().contains(container_ptr),
            !old(lctx).container_lock_map().dom().contains(container_ptr),
            old(lctx).kernel_view_locking_state() is Acquire,
            ({
                let cpu = old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view();
                let container = old(self).ctn_mp.spec_index(container_ptr).view_rodata().view();
                &&& killer_held_context(*old(self), *old(lctx), cpu.current_process->Some_0, cpu.current_thread->Some_0, old(lctx).container_lock_map().dom())
                &&& killer_info.process == cpu.current_process->Some_0
                &&& container.parent is Some
                &&& typed_lock_map_contains_mode(old(lctx).container_lock_map(), container.parent->Some_0, TypedLockMode::Write)
                &&& container.depth > cpu.container_depth
            }),
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(self).inv(),
            typed_lock_maps_aligned(final(self), final(lctx)),
            *final(self) == (KernelK { ctn_mp: final(self).ctn_mp, ..*old(self) }),
            final(self).ctn_mp.unchanged_except(&old(self).ctn_mp, container_ptr),
            final(self).ctn_mp.perms_wf(),
            final(self).ctn_mp.spec_index(container_ptr).view() == old(self).ctn_mp.spec_index(container_ptr).view(),
            final(self).ctn_mp.spec_index(container_ptr).view_rodata() == old(self).ctn_mp.spec_index(container_ptr).view_rodata(),
            final(self).ctn_mp.spec_index(container_ptr).view_ghost() == old(self).ctn_mp.spec_index(container_ptr).view_ghost(),
            (ret is None) == old(self).ctn_mp.spec_index(container_ptr).being_killed(),
            ret is None ==> {
                &&& final(self).ctn_mp.spec_index(container_ptr) == old(self).ctn_mp.spec_index(container_ptr)
                &&& *final(lctx) == *old(lctx)
            },
            ret is Some ==> {
                &&& !old(self).ctn_mp.spec_index(container_ptr).locked()
                &&& !old(self).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty()
                &&& final(self).ctn_mp.spec_index(container_ptr).being_killed()
                &&& final(self).ctn_mp.spec_index(container_ptr).killer_info() == Some(killer_info)
                &&& final(self).ctn_mp.spec_index(container_ptr).locking_thread() == RwLockState::Write { thread_id: final(lctx).thread_id(), lock_id: ret.unwrap().view().lock_id() }
                &&& ret.unwrap().view().state() is WriteLock
                &&& ret.unwrap().view().thread_id() == final(lctx).thread_id()
                &&& final(lctx).kernel_view_locking_state() is Release
                &&& typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Container(container_ptr), TypedHeldLock { lock_id: final(self).ctn_mp.lock_id_by_key(container_ptr), mode: TypedLockMode::Write })
            },
    {
        proof {
            container_perms_wf_map(old(self).ctn_mp);
            container_perms_wf_at(old(self).ctn_mp, container_ptr);
            if !old(self).ctn_mp.spec_index(container_ptr).being_killed() {
                assert(old(lctx).lock_id_acyclic(dynamic_container_lock_id(container_ptr, old(self).ctn_mp.spec_index(container_ptr).view_rodata().view().depth, LockOwnerId::High))) by {
                    let cpu_id = old(lctx).cpu_id();
                    let cpu = old(self).cpu_arr.spec_index(cpu_id).view().view().view();
                    thread_cpu_wf_cpu_at(old(self).thr_mp, old(self).cpu_arr, cpu_id); process_cpu_wf_at(old(self).prc_mp, old(self).cpu_arr, cpu_id);
                    container_cpu_wf_cpu_at(old(self).ctn_mp, old(self).cpu_set_mp, old(self).cpu_arr, cpu_id);
                    thread_perms_wf_at(old(self).thr_mp, cpu.current_thread->Some_0); process_thread_wf_at(old(self).prc_mp, old(self).thr_mp, cpu.current_thread->Some_0);
                    container_process_wf_process_at(old(self).ctn_mp, old(self).prc_mp, cpu.current_process->Some_0);
                    reveal(LocalContext::lock_id_acyclic); reveal(pagetable_window_typed_lock_map_aligned); reveal(UnLockedMap::typed_flag_lock_map_aligned); reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned);
                };
            }
            assert(!old(self).ctn_mp.spec_index(container_ptr).locked_by_thread(old(lctx).thread_id())) by {
                if old(self).ctn_mp.spec_index(container_ptr).locked_by_thread(old(lctx).thread_id()) {
                    assert(old(lctx).container_lock_map().dom().contains(container_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
                }
            };
        }
        let lock_id = Ghost(dynamic_container_lock_id(container_ptr, self.ctn_mp.spec_index(container_ptr).view_rodata().view().depth, LockOwnerId::High));
        let res = self.ctn_mp.try_wlock_dynamic_and_mark_kill(container_ptr, Tracked(&mut *lctx), lock_id, Ghost(KernelObjId::Container(container_ptr)), Ghost(LockOwnerId::High), killer_info);
        proof {
            if res is Some {
                let entry = TypedHeldLock { lock_id: lock_id.view(), mode: TypedLockMode::Write };
                lctx.update_lock_id(KernelObjId::Container(container_ptr), lock_id.view(), self.ctn_mp.lock_id_by_key(container_ptr));
                map_insert_overwrite_lemma(old(lctx).container_lock_map(), container_ptr, entry, TypedHeldLock { lock_id: self.ctn_mp.lock_id_by_key(container_ptr), mode: TypedLockMode::Write });
            }
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            mark_kill_container_eof(*old(self), *self, *old(lctx), container_ptr, killer_info, res is Some);
        }
        res
    }

    /// Release this thread's live dynamic write acquisition of a live container through `LockedMap::dynamic_wunlock` and
    /// re-establish `inv()`. The entry becomes unlocked with a clear control word and unchanged payload, rodata, and
    /// ghost state (`dynamic_wunlock_ensures`); every other entry and `KernelK` field is unchanged, and the typed
    /// held-lock maps lose the container entry (`unlock_ensures`).
    pub fn wunlock_container(&mut self, container_ptr: RwLockContainerPtr, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).ctn_mp.dom().contains(container_ptr),
            old(self).ctn_mp.spec_index(container_ptr).being_killed() == false,
            forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) && old(self).ctn_mp.spec_index(c).killer_info() is Some
                ==> old(self).ctn_mp.spec_index(c).view_rodata().view().parent != Some(container_ptr),
            !old(self).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty(),
            forall|t: RwLockThreadPtr, i: PageIndex| #![trigger old(lctx).thread_lock_map().dom().contains(t), old(self).pg_arr.spec_index(i).view().view().state]
                old(lctx).thread_lock_map().dom().contains(t) && !old(self).thr_mp.spec_index(t).view().temp_alloc_clean() && index_valid(NUM_PAGES, i)
                && old(self).pg_arr.spec_index(i).view().view().owning_container == container_ptr && {
                    let state = old(self).pg_arr.spec_index(i).view().view().state;
                    state == (PageState::Owned4k { thread_ptr: t }) || state == (PageState::Owned2m { thread_ptr: t }) || state == (PageState::Owned1g { thread_ptr: t })
                } ==> old(self).thr_mp.spec_index(t).view().owning_container == container_ptr,
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            // ---- Kernel-wide invariant re-established ----
            final(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
            // ---- Every held lock and its dynamic lock id still match lctx (container now released) ----
            typed_lock_maps_aligned(final(self), final(lctx)),
            // ---- Field framing: only container_map's lock state moves ----
            *final(self) == (KernelK { ctn_mp: final(self).ctn_mp, ..*old(self) }),
            // ---- container_map: only the targeted entry's lock state changed (now unlocked) ----
            final(self).ctn_mp.unchanged_except(&old(self).ctn_mp, container_ptr),
            dynamic_wunlock_ensures(old(self).ctn_mp.spec_index(container_ptr), final(self).ctn_mp.spec_index(container_ptr)),
            unlock_ensures(old(lctx), final(lctx), KernelObjId::Container(container_ptr), old(self).ctn_mp.lock_id_by_key(container_ptr)),
    {
        proof {
            assert({ &&& old(self).ctn_mp.perms_wf() &&& old(self).ctn_mp.spec_index(container_ptr).inv() }) by { container_perms_wf_map(old(self).ctn_mp); container_perms_wf_at(old(self).ctn_mp, container_ptr); };
            assert(old(lctx).lock_entry_contains(old(self).ctn_mp.lock_id_by_key(container_ptr), KernelObjId::Container(container_ptr))) by { reveal(LockedMap::typed_lock_map_aligned); };
        }
        assert(self.ctn_mp.spec_index(container_ptr).wlocked_by(&*lctx)) by { old(self).ctn_mp.typed_lock_map_aligned_write_at(old(lctx).container_lock_map(), old(lctx).thread_id(), container_ptr); };
        self.ctn_mp.dynamic_wunlock(container_ptr, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::Container(container_ptr)));
        proof {
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
            assert(self.inv()) by { reveal(LockedMap::typed_lock_map_aligned); wunlock_container_eof(*old(self), *self, *old(lctx), container_ptr); };
        }
    }
}
} // verus!
