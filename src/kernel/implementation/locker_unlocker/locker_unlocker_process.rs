#[cfg(verus_keep_ghost)]
use super::locker_unlocker_process_eof::{wlock_process_eof, mark_kill_process_eof, wunlock_process_eof};
use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
    /// Wrapper around `LockedMap::wlock_unless_killed` for `process_map`
    /// that re-establishes `inv()` after the lock attempt. Same shape as
    /// `wlock_container_unless_killed`, but for the process map, which is
    /// touched by the conservation-fold conjunct
    /// `container_process_allocator_quota_wf` — so that piece is discharged
    /// via the per-process set-fold lemmas (the lock only moves lock state,
    /// so each process's `process_effective_quota_*` is unchanged ==> the
    /// folded sum is unchanged).
    pub fn wlock_process_unless_killed(&mut self, process_ptr: RwLockProcessPtr, Ghost(cpu_id): Ghost<CpuId>, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Option<Tracked<LockPerm>>)
        requires
            old(self).inv(),
            old(self).prc_mp.dom().contains(process_ptr),
            old(lctx).kernel_view_locking_state() is Acquire,
            {
                let cpus = old(lctx).cpu_lock_map().dom();
                let container_ptr = old(self).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container;
                let containers = old(lctx).container_lock_map().dom();
                let process = old(self).prc_mp.spec_index(process_ptr).view_rodata().view();
                &&& (forall|held_cpu_id: CpuId|
                    #![trigger cpus.contains(held_cpu_id)]
                    cpus.contains(held_cpu_id) ==> {
                        &&& index_valid(NUM_CPUS, held_cpu_id)
                        &&& old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().owning_container == container_ptr
                        &&& !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off)
                        &&& old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().current_process is None || old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().current_process == Some(process_ptr)
                        &&& old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().container_depth == process.container_depth
                        &&& old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().current_process is Some ==> old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().process_depth == process.depth
                    })
                &&& containers.contains(container_ptr) ==> old(self).ctn_mp.spec_index(container_ptr).view_rodata().view().depth == process.container_depth
                &&& cpus.contains(cpu_id)
                &&& old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr)
                &&& {
                    &&& old(lctx).page_lock_map().dom().is_empty()
                    &&& old(lctx).process_lock_map().dom().is_empty()
                    &&& old(lctx).thread_lock_map().dom().is_empty()
                    &&& old(lctx).endpoint_lock_map().dom().is_empty()
                    &&& old(lctx).scheduler_lock_map().dom().is_empty()
                    &&& old(lctx).cpu_set_lock_map().dom().is_empty()
                    &&& old(lctx).pagetable_lock_map().dom().is_empty()
                    &&& old(lctx).iommu_table_lock_map().dom().is_empty()
                    &&& old(lctx).iommu_root_table_lock_map().dom().is_empty()
                    &&& old(lctx).allocator_quota_4k_lock_map().dom().is_empty()
                    &&& old(lctx).allocator_cache_4k_lock_map().dom().is_empty()
                    &&& old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty()
                    &&& old(lctx).allocator_quota_2m_lock_map().dom().is_empty()
                    &&& old(lctx).allocator_cache_2m_lock_map().dom().is_empty()
                    &&& old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty()
                    &&& old(lctx).allocator_quota_1g_lock_map().dom().is_empty()
                    &&& old(lctx).allocator_cache_1g_lock_map().dom().is_empty()
                    &&& old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty()
                    &&& old(lctx).pcid_needflush_lock_map().dom().is_empty()
                    &&& containers.subset_of(set![container_ptr])
                    &&& old(lctx).pcid_allocator_lock_map().dom().is_empty()
                }
            },
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            // ---- Kernel-wide invariant re-established ----
            final(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
            // ---- Every held lock still matches lctx (success: process locked; failure: no-op) ----
            // ---- Dynamic lock ids remain aligned ----
            typed_lock_maps_aligned(final(self), final(lctx)),
            // ---- Field framing: only process_map's lock state moves ----
            *final(self) == (KernelK { prc_mp: final(self).prc_mp, ..*old(self) }),
            // ---- process_map: only the targeted entry's lock state
            // ---- (success) or nothing at all (failure) changed.
            final(self).prc_mp.unchanged_except(&old(self).prc_mp, process_ptr),
            final(self).prc_mp.perms_wf(),
            // ---- LocalContext phase preservation ----
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            // ---- Failure: process is being killed; complete no-op ----
            ret is None ==> {
                &&& old(self).prc_mp.spec_index(process_ptr).being_killed() == true
                &&& final(self).prc_mp.spec_index(process_ptr) == old(self).prc_mp.spec_index(process_ptr)
                &&& typed_lock_maps_unchanged(old(lctx), final(lctx))
            },
            // ---- Success: process locked by us, perm returned ----
            ret is Some ==> {
                &&& old(self).prc_mp.spec_index(process_ptr).being_killed() == false
                &&& wlock_ensures(old(self).prc_mp.spec_index(process_ptr), final(self).prc_mp.spec_index(process_ptr), old(self).prc_mp.lock_id_by_key(process_ptr), final(lctx), ret.unwrap().view())
                &&& typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Process(process_ptr), TypedHeldLock { lock_id: final(self).prc_mp.lock_id_by_key(process_ptr), mode: TypedLockMode::Write })
                &&& final(self).prc_mp.spec_index(process_ptr).view().state.view() is Running || final(self).prc_mp.spec_index(process_ptr).view().state.view() is Zombie
            },
    {
        proof {
            process_perms_wf_map(old(self).prc_mp);
            process_perms_wf_at(old(self).prc_mp, process_ptr);
            if !old(self).prc_mp.spec_index(process_ptr).being_killed() {
                assert(old(lctx).lock_id_acyclic(old(self).prc_mp.lock_id_by_key(process_ptr))) by { reveal(LocalContext::lock_id_acyclic); reveal(UnLockedMap::typed_flag_lock_map_aligned); reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned); };
            }
            assert(!old(self).prc_mp.spec_index(process_ptr).locked_by_thread(old(lctx).thread_id())) by {
                if old(self).prc_mp.spec_index(process_ptr).locked_by_thread(old(lctx).thread_id()) {
                    assert(old(lctx).process_lock_map().dom().contains(process_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
                }
            };
        }
        let res = self.prc_mp.wlock_unless_killed(process_ptr, Tracked(&mut *lctx), Ghost(KernelObjId::Process(process_ptr)));
        proof {
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by {
                broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged);
            };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
            wlock_process_eof(*old(self), *self, process_ptr, *lctx, res);
        }
        res
    }

    /// Write-lock a process below the killer's own and mark it for the killer: a child of a process the killer holds, or
    /// the root of a container the killer marked and holds. A process another killer already marked is left untouched.
    /// On success the held entry moves to the sunk id a marked object reports.
    pub fn try_wlock_process_and_mark_kill(&mut self, process_ptr: RwLockProcessPtr, killer_process: RwLockProcessPtr, killer_thread: RwLockThreadPtr, killer_info: KillerInfo, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Option<Tracked<LockPerm>>)
        requires
            old(self).inv(),
            old(self).prc_mp.dom().contains(process_ptr),
            old(self).prc_mp.dom().contains(killer_process),
            !old(lctx).process_lock_map().dom().contains(process_ptr),
            old(lctx).kernel_view_locking_state() is Acquire,
            killer_held_context(*old(self), *old(lctx), killer_process, killer_thread, old(lctx).container_lock_map().dom()),
            killer_info.process == killer_process,
            ({
                let process = old(self).prc_mp.spec_index(process_ptr).view_rodata().view();
                let killer = old(self).prc_mp.spec_index(killer_process).view_rodata().view();
                ||| {
                    &&& process.parent is Some
                    &&& typed_lock_map_contains_mode(old(lctx).process_lock_map(), process.parent->Some_0, TypedLockMode::Write)
                    &&& process.container_depth > killer.container_depth || (process.owning_container == killer.owning_container && process.depth > killer.depth)
                }
                ||| {
                    &&& process.parent is None
                    &&& old(self).ctn_mp.spec_index(process.owning_container).view().root_process == process_ptr
                    &&& old(self).ctn_mp.spec_index(process.owning_container).killer_info() == Some(killer_info)
                    &&& typed_lock_map_contains_mode(old(lctx).container_lock_map(), process.owning_container, TypedLockMode::Write)
                    &&& process.container_depth > killer.container_depth
                }
            }),
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(self).inv(),
            typed_lock_maps_aligned(final(self), final(lctx)),
            *final(self) == (KernelK { prc_mp: final(self).prc_mp, ..*old(self) }),
            final(self).prc_mp.unchanged_except(&old(self).prc_mp, process_ptr),
            final(self).prc_mp.perms_wf(),
            final(self).prc_mp.spec_index(process_ptr).view() == (Process { state: final(self).prc_mp.spec_index(process_ptr).view().state, ..old(self).prc_mp.spec_index(process_ptr).view() }),
            final(self).prc_mp.spec_index(process_ptr).view_rodata() == old(self).prc_mp.spec_index(process_ptr).view_rodata(),
            final(self).prc_mp.spec_index(process_ptr).view_ghost() == old(self).prc_mp.spec_index(process_ptr).view_ghost(),
            ret is None ==> {
                &&& old(self).prc_mp.spec_index(process_ptr).being_killed()
                &&& final(self).prc_mp.spec_index(process_ptr) == old(self).prc_mp.spec_index(process_ptr)
                &&& *final(lctx) == *old(lctx)
            },
            ret is Some ==> {
                &&& !old(self).prc_mp.spec_index(process_ptr).being_killed()
                &&& final(self).prc_mp.spec_index(process_ptr).being_killed()
                &&& final(self).prc_mp.spec_index(process_ptr).killer_info() == Some(killer_info)
                &&& final(self).prc_mp.spec_index(process_ptr).view().state.view() == if old(self).prc_mp.spec_index(process_ptr).view().zombie { ProcessState::Zombie } else { ProcessState::Killing }
                &&& final(self).prc_mp.spec_index(process_ptr).locking_thread() == RwLockState::Write { thread_id: final(lctx).thread_id(), lock_id: ret.unwrap().view().lock_id() }
                &&& ret.unwrap().view().state() is WriteLock
                &&& ret.unwrap().view().thread_id() == final(lctx).thread_id()
                &&& final(lctx).kernel_view_locking_state() is Release
                &&& typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Process(process_ptr), TypedHeldLock { lock_id: final(self).prc_mp.lock_id_by_key(process_ptr), mode: TypedLockMode::Write })
            },
    {
        proof {
            process_perms_wf_map(old(self).prc_mp);
            process_perms_wf_at(old(self).prc_mp, process_ptr);
            if !old(self).prc_mp.spec_index(process_ptr).being_killed() {
                assert(old(lctx).lock_id_acyclic(old(self).prc_mp.lock_id_by_key(process_ptr))) by {
                    thread_cpu_wf_cpu_at(old(self).thr_mp, old(self).cpu_arr, old(lctx).cpu_id()); process_cpu_wf_at(old(self).prc_mp, old(self).cpu_arr, old(lctx).cpu_id());
                    container_cpu_wf_cpu_at(old(self).ctn_mp, old(self).cpu_set_mp, old(self).cpu_arr, old(lctx).cpu_id());
                    thread_perms_wf_at(old(self).thr_mp, killer_thread); process_thread_wf_at(old(self).prc_mp, old(self).thr_mp, killer_thread);
                    container_process_wf_process_at(old(self).ctn_mp, old(self).prc_mp, killer_process); container_process_wf_process_at(old(self).ctn_mp, old(self).prc_mp, process_ptr);
                    reveal(LocalContext::lock_id_acyclic); reveal(UnLockedMap::typed_flag_lock_map_aligned); reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned);
                };
            }
            assert(!old(self).prc_mp.spec_index(process_ptr).locked_by_thread(old(lctx).thread_id())) by {
                if old(self).prc_mp.spec_index(process_ptr).locked_by_thread(old(lctx).thread_id()) {
                    assert(old(lctx).process_lock_map().dom().contains(process_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
                }
            };
        }
        let res = self.prc_mp.try_wlock_and_mark_kill(process_ptr, Tracked(&mut *lctx), Ghost(KernelObjId::Process(process_ptr)), killer_info);
        let res = if res.is_some() {
            let Tracked(lock_perm) = res.unwrap();
            let process = self.prc_mp.borrow_mut(process_ptr, Tracked(&*lctx), Tracked(&lock_perm));
            if !process.zombie { process.state = Ghost(ProcessState::Killing); }
            Some(Tracked(lock_perm))
        } else { None };
        proof {
            if res is Some {
                let entry = TypedHeldLock { lock_id: old(self).prc_mp.lock_id_by_key(process_ptr), mode: TypedLockMode::Write };
                lctx.update_lock_id(KernelObjId::Process(process_ptr), old(self).prc_mp.lock_id_by_key(process_ptr), self.prc_mp.lock_id_by_key(process_ptr));
                map_insert_overwrite_lemma(old(lctx).process_lock_map(), process_ptr, entry, TypedHeldLock { lock_id: self.prc_mp.lock_id_by_key(process_ptr), mode: TypedLockMode::Write });
            }
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            mark_kill_process_eof(*old(self), *self, *old(lctx), process_ptr, killer_process, killer_thread, killer_info, res is Some);
        }
        res
    }

    /// Companion of `wlock_process_unless_killed` for the unlock side.
    /// Wraps `LockedMap::wunlock` for `process_map` and re-establishes
    /// `inv()` immediately afterwards. Unlocking has no killed-branch — the
    /// caller already holds the write lock, so this is unconditional.
    pub fn wunlock_process(&mut self, process_ptr: RwLockProcessPtr, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).prc_mp.dom().contains(process_ptr),
            old(self).prc_mp.spec_index(process_ptr).being_killed() == false,
            forall|d: RwLockProcessPtr| #![trigger old(lctx).process_lock_map().dom().contains(d)] old(lctx).process_lock_map().dom().contains(d) && old(self).prc_mp.spec_index(d).killer_info() is Some
                ==> old(self).prc_mp.spec_index(d).killer_info()->Some_0.process != process_ptr && old(self).prc_mp.spec_index(d).view_rodata().view().parent != Some(process_ptr),
            forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) && old(self).ctn_mp.spec_index(c).killer_info() is Some
                ==> old(self).ctn_mp.spec_index(c).killer_info()->Some_0.process != process_ptr,
            old(self).prc_mp.spec_index(process_ptr).view().state.view() is Running || old(self).prc_mp.spec_index(process_ptr).view().state.view() is Zombie,
            old(self).prc_mp.spec_index(process_ptr).view().iommu_table is Some ==> !old(lctx).iommu_table_lock_map().dom().contains(old(self).prc_mp.spec_index(process_ptr).view().iommu_table->Some_0),
            typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            // ---- Kernel-wide invariant re-established ----
            final(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
            kernel_k_to_nonlock_kernel_u(*final(self)) == kernel_k_to_nonlock_kernel_u(*old(self)),
            // ---- Every held lock still matches lctx (process now released) ----
            // ---- Dynamic lock ids remain aligned ----
            typed_lock_maps_aligned(final(self), final(lctx)),
            // ---- Field framing: only process_map's lock state moves ----
            *final(self) == (KernelK { prc_mp: final(self).prc_mp, ..*old(self) }),
            // ---- process_map: only the targeted entry's lock state changed (now unlocked) ----
            final(self).prc_mp.unchanged_except(&old(self).prc_mp, process_ptr),
            final(self).prc_mp.perms_wf(),
            final(self).prc_mp.lock_id_by_key(process_ptr) == old(self).prc_mp.lock_id_by_key(process_ptr),
            wunlock_ensures(old(self).prc_mp.spec_index(process_ptr), final(self).prc_mp.spec_index(process_ptr)),
            // ---- LocalContext: lock dropped; thread preserved ----
            // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
            // `unlock_ensures` transitions it Acquire -> Release, so restating
            // `== old` would contradict it and make the postcondition `false`
            // in an Acquire section. `unlock_ensures` is the source of truth
            // for the phase transition (same trap as the NOTE on
            // `LockedArray::wunlock`). user_view is separately preserved.
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Process(process_ptr)),
    {
        proof {
            assert({ &&& old(self).prc_mp.perms_wf() &&& old(self).prc_mp.spec_index(process_ptr).inv() }) by { process_perms_wf_map(old(self).prc_mp); process_perms_wf_at(old(self).prc_mp, process_ptr); };
            assert(old(lctx).lock_entry_contains(old(self).prc_mp.lock_id_by_key(process_ptr), KernelObjId::Process(process_ptr))) by { reveal(LockedMap::typed_lock_map_aligned); };
        }
        assert(self.prc_mp.spec_index(process_ptr).wlocked_by(&*lctx)) by { old(self).prc_mp.typed_lock_map_aligned_write_at(old(lctx).process_lock_map(), old(lctx).thread_id(), process_ptr); };
        self.prc_mp.wunlock(process_ptr, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::Process(process_ptr)));
        proof {
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by {
                broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged);
            };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
            wunlock_process_eof(*old(self), *self, *old(lctx), process_ptr);
            assert(kernel_k_to_nonlock_kernel_u(*self) == kernel_k_to_nonlock_kernel_u(*old(self))) by { kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(old(self), self); };
        }
    }
}
} // verus!
