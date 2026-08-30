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
                old(lctx).kernel_view_locking_state() is Acquire,
                !old(self).cpu_arr.spec_index(cpu_id).view().locked_by_thread(old(lctx).thread_id()),
                old(lctx).lock_id_acyclic(old(self).cpu_arr.lock_id_by_index(cpu_id)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                // ---- Every held lock still matches lctx (cpu now locked) ----
                // ---- Dynamic lock ids remain aligned ----
                lock_id_aligned(final(self), final(lctx)),
                // ---- Field framing: only cpu_array's lock state moves ----
                final(self).pt_mp     == old(self).pt_mp,
                final(self).it_mp     == old(self).it_mp,
                final(self).irt     == old(self).irt,
                final(self).pg_arr        == old(self).pg_arr,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).iommu_tlb           == old(self).iommu_tlb,
                final(self).rt_ctn    == old(self).rt_ctn,
                final(self).ctn_mp     == old(self).ctn_mp,
                final(self).sched_mp     == old(self).sched_mp,
                final(self).pcid_allc_mp == old(self).pcid_allc_mp,
                final(self).prc_mp       == old(self).prc_mp,
                final(self).thr_mp        == old(self).thr_mp,
                final(self).ep_mp      == old(self).ep_mp,
                final(self).allc_4k_mp  == old(self).allc_4k_mp,
                final(self).allc_2m_mp  == old(self).allc_2m_mp,
                final(self).allc_1g_mp  == old(self).allc_1g_mp,
                final(self).dflt_pt == old(self).dflt_pt,
                // ---- cpu_array: only the targeted slot's lock state changed ----
                final(self).cpu_arr.unchanged_except(&old(self).cpu_arr, cpu_id),
                final(self).cpu_arr.inv(),
                cpu_objects_unlocked(old(self).cpu_arr, old(lctx).thread_id())
                    ==> cpu_objects_unlocked_except(final(self).cpu_arr, final(lctx).thread_id(), set![cpu_id]),
                // ---- LocalContext: phases preserved ----
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                // ---- The lock perm + lock ensures (forwarded from LockedArray::wlock) ----
                wlock_ensures(old(self).cpu_arr.spec_index(cpu_id).view(), final(self).cpu_arr.spec_index(cpu_id).view(), old(self).cpu_arr.lock_id_by_index(cpu_id), final(lctx), ret.view()),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(self).cpu_arr.lock_id_by_index(cpu_id), KernelObjId::Cpu(cpu_id))),
        {
            proof {
                assert(old(self).cpu_arr.inv()) by { reveal(cpu_array_wf); };
            }
            let ret = self.cpu_arr.wlock(cpu_id, Tracked(&mut *lctx), Ghost(KernelObjId::Cpu(cpu_id)));
            proof {
                assert(cpu_array_wf(self.cpu_arr, self.dflt_pt.view())) by { reveal(cpu_array_wf); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.process_management_inv()) by {
                    assert(container_cpu_wf(self.ctn_mp, self.cpu_arr)) by { reveal(container_perms_wf); reveal(container_cpu_wf); };
                    assert(process_cpu_wf(self.prc_mp, self.cpu_arr)) by { reveal(process_cpu_wf); };
                    assert(thread_cpu_wf(self.thr_mp, self.cpu_arr)) by { reveal(thread_cpu_wf); };
                };
                assert(cpu_dirty_map_wf(self.ctn_mp, self.prc_mp, self.cpu_arr, self.cpu_tlb, self.pt_mp)) by { reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(container_cpu_wf); };
                assert(tlb_wf_spec(self.cpu_tlb, self.pt_mp, self.cpu_arr)) by { reveal(tlb_wf_spec); };
                assert(lock_id_aligned(self, &*lctx)) by { reveal(lock_id_aligned); };
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
                old(self).cpu_arr.spec_index(cpu_id).view().wlocked_by(old(lctx)),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id() == old(self).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                // ---- Every held lock still matches lctx (cpu now released) ----
                // ---- Dynamic lock ids remain aligned ----
                lock_id_aligned(final(self), final(lctx)),
                // ---- Field framing: only cpu_array's lock state moves ----
                final(self).pt_mp     == old(self).pt_mp,
                final(self).it_mp     == old(self).it_mp,
                final(self).irt     == old(self).irt,
                final(self).pg_arr        == old(self).pg_arr,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).iommu_tlb           == old(self).iommu_tlb,
                final(self).rt_ctn    == old(self).rt_ctn,
                final(self).ctn_mp     == old(self).ctn_mp,
                final(self).sched_mp     == old(self).sched_mp,
                final(self).pcid_allc_mp == old(self).pcid_allc_mp,
                final(self).prc_mp       == old(self).prc_mp,
                final(self).thr_mp        == old(self).thr_mp,
                final(self).ep_mp      == old(self).ep_mp,
                final(self).allc_4k_mp  == old(self).allc_4k_mp,
                final(self).allc_2m_mp  == old(self).allc_2m_mp,
                final(self).allc_1g_mp  == old(self).allc_1g_mp,
                final(self).dflt_pt == old(self).dflt_pt,
                // ---- cpu_array: only the targeted slot's lock state changed (now unlocked) ----
                final(self).cpu_arr.unchanged_except(&old(self).cpu_arr, cpu_id),
                final(self).cpu_arr.inv(),
                final(self).cpu_arr.spec_index(cpu_id).view().locking_thread() is None,
                !final(self).cpu_arr.spec_index(cpu_id).view().locked(),
                final(self).cpu_arr.lock_id_by_index(cpu_id) == old(self).cpu_arr.lock_id_by_index(cpu_id),
                wunlock_ensures(old(self).cpu_arr.spec_index(cpu_id).view(), final(self).cpu_arr.spec_index(cpu_id).view()),
                cpu_objects_unlocked_except(old(self).cpu_arr, old(lctx).thread_id(), set![cpu_id]) ==> cpu_objects_unlocked(final(self).cpu_arr, final(lctx).thread_id()),
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
        {
            proof {
                assert(old(self).cpu_arr.inv()) by { reveal(cpu_array_wf); };
                assert(old(lctx).lock_id_set().contains((old(self).cpu_arr.lock_id_by_index(cpu_id), KernelObjId::Cpu(cpu_id)))) by { reveal(lock_id_aligned); };
            }
            self.cpu_arr.wunlock(cpu_id, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::Cpu(cpu_id)));
            // Re-establish inv(). Only `cpu_array[cpu_id]`'s lock state moved
            // (now unlocked); every payload view, every other slot, and every
            // other KernelK field is unchanged. Same template as wlock_cpu.
            proof {
                assert(cpu_array_wf(self.cpu_arr, self.dflt_pt.view())) by { reveal(cpu_array_wf); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.process_management_inv()) by {
                    assert(container_cpu_wf(self.ctn_mp, self.cpu_arr)) by { reveal(container_perms_wf); reveal(container_cpu_wf); };
                    assert(process_cpu_wf(self.prc_mp, self.cpu_arr)) by { reveal(process_cpu_wf); };
                    assert(thread_cpu_wf(self.thr_mp, self.cpu_arr)) by { reveal(thread_cpu_wf); };
                };
                assert(cpu_dirty_map_wf(self.ctn_mp, self.prc_mp, self.cpu_arr, self.cpu_tlb, self.pt_mp)) by { reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(container_cpu_wf); };
                assert(tlb_wf_spec(self.cpu_tlb, self.pt_mp, self.cpu_arr)) by { reveal(tlb_wf_spec); };
                assert(lock_id_aligned(self, &*lctx)) by { reveal(lock_id_aligned); };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
            }
        }

}
} // verus!
