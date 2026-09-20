use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
        pub fn wlock_cpu(
            &mut self,
            cpu_id: CpuId,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Tracked<LockPerm>)
            requires
                old(self).inv(),
                index_valid(NUM_CPUS, cpu_id),
                old(self).cpu_arr.spec_index(cpu_id).view().view().view().state is Off ==> cpu_id == old(lctx).cpu_id(),
                old(lctx).kernel_view_locking_state() is Acquire,
                !old(lctx).cpu_lock_map().dom().contains(cpu_id),
                old(lctx).no_locks_held(),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                final(self).cpu_published[cpu_id as int].view() == (final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                // ---- Every held lock still matches lctx (cpu now locked) ----
                // ---- Dynamic lock ids remain aligned ----
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                // ---- Field framing: only cpu_array's lock state moves ----
                *final(self) == (KernelK { cpu_arr: final(self).cpu_arr, ..*old(self) }),
                // ---- cpu_array: only the targeted slot's lock state changed ----
                final(self).cpu_arr.unchanged_except(&old(self).cpu_arr, cpu_id),
                final(self).cpu_arr.inv(),
                // ---- LocalContext: phases preserved ----
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                // ---- The lock perm + lock ensures (forwarded from LockedArray::wlock) ----
                wlock_ensures(old(self).cpu_arr.spec_index(cpu_id).view(), final(self).cpu_arr.spec_index(cpu_id).view(), old(self).cpu_arr.lock_id_by_index(cpu_id), final(lctx), ret.view()),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(self).cpu_arr.lock_id_by_index(cpu_id), KernelObjId::Cpu(cpu_id))),
                typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Cpu(cpu_id), TypedHeldLock { lock_id: final(self).cpu_arr.lock_id_by_index(cpu_id), mode: TypedLockMode::Write }),
                !(final(self).cpu_arr.spec_index(cpu_id).view().view().view().state is Off) ==> final(lctx).held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR),
        {
            proof {
                assert(old(self).cpu_arr.inv() && old(self).cpu_arr.spec_index(cpu_id).view().inv()) by { reveal(cpu_array_wf); };
                assert(old(lctx).lock_id_acyclic(old(self).cpu_arr.lock_id_by_index(cpu_id))) by { reveal(lock_id_set_aligned); };
            }
            assert(wlock_requires(self.cpu_arr.spec_index(cpu_id).view(), &*lctx)) by { reveal(LockedArray::typed_lock_map_aligned); };
            let ret = self.cpu_arr.wlock(cpu_id, Tracked(&mut *lctx), Ghost(KernelObjId::Cpu(cpu_id)));
            assert(old(self).cpu_published[cpu_id as int].view() == (old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid)) by { reveal(cpu_published_wf); };
            proof {
                assert(cpu_array_wf(self.cpu_arr, self.dflt_pt.view())) by { reveal(cpu_array_wf); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(cpu_published_wf); };
                assert(self.process_management_inv()) by { reveal(container_cpu_wf); reveal(process_cpu_wf); reveal(thread_cpu_wf); };
                assert(cpu_dirty_map_wf(self.ctn_mp, self.cpu_set_mp, self.prc_mp, self.cpu_arr, self.cpu_tlb, self.pt_mp, self.pcid_needflush)) by { reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(container_cpu_wf); };
                assert(tlb_wf_spec(self.cpu_tlb, self.pt_mp, self.cpu_arr, self.pcid_needflush)) by { reveal(tlb_wf_spec); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedArray::typed_lock_map_aligned); };
                assert(!(self.cpu_arr.spec_index(cpu_id).view().view().view().state is Off) ==> lctx.held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR)) by { reveal(cpu_array_wf); reveal(lock_id_set_aligned); broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different; };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
            }
            ret
        }

        /// Acquire the terminal-major lock for a CPU already Off in a closed
        /// slot of the held CPU set.
        pub fn wlock_off_cpu(
            &mut self,
            cpu_id: CpuId,
            cpu_set_ptr: RwLockCpuSetPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Tracked<LockPerm>)
            requires
                old(self).inv(),
                index_valid(NUM_CPUS, cpu_id),
                old(self).cpu_set_mp.dom().contains(cpu_set_ptr),
                typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), cpu_set_ptr, TypedLockMode::Write),
                old(self).cpu_set_mp.spec_index(cpu_set_ptr).view().owned_cpus.closed_view().contains(cpu_id),
                old(lctx).lock_id_acyclic(old(self).cpu_arr.lock_id_by_index(cpu_id)),
                old(lctx).kernel_view_locking_state() is Acquire,
                !old(lctx).cpu_lock_map().dom().contains(cpu_id),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                final(self).cpu_published[cpu_id as int].view() == (final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                *final(self) == (KernelK { cpu_arr: final(self).cpu_arr, ..*old(self) }),
                final(self).cpu_arr.unchanged_except(&old(self).cpu_arr, cpu_id),
                final(self).cpu_arr.inv(),
                final(self).cpu_arr.view().len() == old(self).cpu_arr.view().len(),
                final(self).cpu_arr.spec_index(cpu_id).view().is_init() == old(self).cpu_arr.spec_index(cpu_id).view().is_init(),
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                wlock_ensures(old(self).cpu_arr.spec_index(cpu_id).view(), final(self).cpu_arr.spec_index(cpu_id).view(), old(self).cpu_arr.lock_id_by_index(cpu_id), final(lctx), ret.view()),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(self).cpu_arr.lock_id_by_index(cpu_id), KernelObjId::Cpu(cpu_id))),
                typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Cpu(cpu_id), TypedHeldLock { lock_id: final(self).cpu_arr.lock_id_by_index(cpu_id), mode: TypedLockMode::Write }),
                final(self).cpu_arr.spec_index(cpu_id).view().view().view().state is Off,
        {
            proof {
                assert(old(self).cpu_arr.inv() && old(self).cpu_arr.spec_index(cpu_id).view().inv()) by { reveal(cpu_array_wf); };
                assert(old(self).cpu_arr.spec_index(cpu_id).view().view().view().state is Off) by { reveal(container_cpu_set_wf); reveal(cpu_set_perms_wf); reveal(container_cpu_wf); };
            }
            assert(wlock_requires(self.cpu_arr.spec_index(cpu_id).view(), &*lctx)) by { reveal(LockedArray::typed_lock_map_aligned); };
            let ret = self.cpu_arr.wlock(cpu_id, Tracked(&mut *lctx), Ghost(KernelObjId::Cpu(cpu_id)));
            assert(old(self).cpu_published[cpu_id as int].view() == (old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid)) by { reveal(cpu_published_wf); };
            proof {
                assert(cpu_array_wf(self.cpu_arr, self.dflt_pt.view())) by { reveal(cpu_array_wf); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(cpu_published_wf); };
                assert(self.process_management_inv()) by {
                    reveal(container_cpu_wf);
                    reveal(process_cpu_wf);
                    reveal(thread_cpu_wf);
                };
                assert(cpu_dirty_map_wf(self.ctn_mp, self.cpu_set_mp, self.prc_mp, self.cpu_arr, self.cpu_tlb, self.pt_mp, self.pcid_needflush)) by { reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(container_cpu_wf); };
                assert(tlb_wf_spec(self.cpu_tlb, self.pt_mp, self.cpu_arr, self.pcid_needflush)) by { reveal(tlb_wf_spec); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedArray::typed_lock_map_aligned); };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
            }
            ret
        }

        pub fn wunlock_cpu(
            &mut self,
            cpu_id: CpuId,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                index_valid(NUM_CPUS, cpu_id),
                old(self).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
                typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id() == old(self).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
                old(self).cpu_published[cpu_id as int].view() == (old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                final(self).cpu_published[cpu_id as int].view() == (final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                // ---- Every held lock still matches lctx (cpu now released) ----
                // ---- Dynamic lock ids remain aligned ----
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                // ---- Field framing: only cpu_array's lock state moves ----
                *final(self) == (KernelK { cpu_arr: final(self).cpu_arr, ..*old(self) }),
                // ---- cpu_array: only the targeted slot's lock state changed (now unlocked) ----
                final(self).cpu_arr.unchanged_except(&old(self).cpu_arr, cpu_id),
                final(self).cpu_arr.inv(),
                final(self).cpu_arr.spec_index(cpu_id).view().locking_thread() is None,
                !final(self).cpu_arr.spec_index(cpu_id).view().locked(),
                final(self).cpu_arr.lock_id_by_index(cpu_id) == old(self).cpu_arr.lock_id_by_index(cpu_id),
                wunlock_ensures(old(self).cpu_arr.spec_index(cpu_id).view(), final(self).cpu_arr.spec_index(cpu_id).view()),
                // ---- LocalContext: lock dropped; thread preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` transitions it Acquire -> Release, so restating
                // `== old` would contradict it and make the postcondition `false`
                // in an Acquire section. `unlock_ensures` is the source of truth
                // for the phase transition (same trap as the NOTE on
                // `LockedArray::wunlock`). user_view is separately preserved.
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,
                final(lctx).lock_id_set() == old(lctx).lock_id_set().remove((old(self).cpu_arr.lock_id_by_index(cpu_id), KernelObjId::Cpu(cpu_id))),
                typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Cpu(cpu_id)),
                final(lctx).no_locks_held() ==> final(self).all_objects_unlocked(final(lctx)),
        {
            proof {
                assert(old(self).cpu_arr.inv()) by { reveal(cpu_array_wf); };
                assert(old(lctx).lock_entry_contains(old(self).cpu_arr.lock_id_by_index(cpu_id), KernelObjId::Cpu(cpu_id))) by { reveal(LockedArray::typed_lock_map_aligned); };
                assert(old(lctx).lock_id_set().contains((old(self).cpu_arr.lock_id_by_index(cpu_id), KernelObjId::Cpu(cpu_id)))) by { reveal(lock_id_set_aligned); };
            }
            assert(self.cpu_arr.spec_index(cpu_id).view().wlocked_by(&*lctx)) by { reveal(LockedArray::typed_lock_map_aligned); };
            self.cpu_arr.wunlock(cpu_id, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::Cpu(cpu_id)));
            // Re-establish inv(). Only `cpu_array[cpu_id]`'s lock state moved
            // (now unlocked); every payload view, every other slot, and every
            // other KernelK field is unchanged. Same template as wlock_cpu.
            proof {
                assert(cpu_array_wf(self.cpu_arr, self.dflt_pt.view())) by { reveal(cpu_array_wf); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(cpu_published_wf); };
                assert(self.process_management_inv()) by { reveal(container_cpu_wf); reveal(process_cpu_wf); reveal(thread_cpu_wf); };
                assert(cpu_dirty_map_wf(self.ctn_mp, self.cpu_set_mp, self.prc_mp, self.cpu_arr, self.cpu_tlb, self.pt_mp, self.pcid_needflush)) by { reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(container_cpu_wf); };
                assert(tlb_wf_spec(self.cpu_tlb, self.pt_mp, self.cpu_arr, self.pcid_needflush)) by { reveal(tlb_wf_spec); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedArray::typed_lock_map_aligned); };
                assert(lctx.no_locks_held() ==> self.all_objects_unlocked(lctx)) by { if lctx.no_locks_held() { no_locks_held_imply_all_objects_unlocked(&*self, &*lctx); } };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
            }
        }

}
} // verus!
