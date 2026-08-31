use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
        pub fn wlock_page(
            &mut self,
            page_index: PageIndex,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Tracked<LockPerm>)
            requires
                old(self).inv(),
                index_valid(NUM_PAGES, page_index),
                old(lctx).kernel_view_locking_state() is Acquire,
                !old(self).pg_arr.spec_index(page_index).view().locked_by_thread(old(lctx).thread_id()),
                old(lctx).lock_id_acyclic(old(self).pg_arr.lock_id_by_index(page_index)),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                // ---- Every held lock still matches lctx (page slot now locked) ----
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                // ---- Field framing: only page_array's slot lock state moves ----
                final(self).pt_mp     == old(self).pt_mp,
                final(self).it_mp     == old(self).it_mp,
                final(self).irt     == old(self).irt,
                final(self).cpu_arr         == old(self).cpu_arr,
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
                // ---- page_array: only the targeted slot's lock state changed ----
                final(self).pg_arr.unchanged_except(&old(self).pg_arr, page_index),
                typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_index), TypedHeldLock {
                    lock_id: final(self).pg_arr.lock_id_by_index(page_index),
                    mode: TypedLockMode::Write,
                }),
                page_objects_unlocked(old(self).pg_arr, old(lctx).thread_id()) ==> page_objects_unlocked_except(final(self).pg_arr, final(lctx).thread_id(), set![page_index]),
                // ---- LocalContext: phases preserved ----
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                // ---- The lock perm + lock ensures (forwarded from LockedArray::wlock) ----
                wlock_ensures(old(self).pg_arr.spec_index(page_index).view(), final(self).pg_arr.spec_index(page_index).view(), old(self).pg_arr.lock_id_by_index(page_index), final(lctx), ret.view()),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(self).pg_arr.lock_id_by_index(page_index), KernelObjId::Page(page_index))),
        {
            proof {
                assert(old(self).pg_arr.inv()) by { reveal(page_array_wf); };
            }
            let ret = self.pg_arr.wlock(page_index, Tracked(&mut *lctx), Ghost(KernelObjId::Page(page_index)));
            proof {
                assert(page_array_wf(self.pg_arr)) by { lemma_no_change_imply_page_array_wf_forall(); };
                assert(page_invariant_fields_unchanged(old(self).pg_arr, self.pg_arr)) by { page_lock_op_preserves_invariant_fields(old(self).pg_arr, self.pg_arr, page_index); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.memory_management_inv()) by { lemma_no_change_imply_memory_management_inv_for_page_fields_forall(); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by {
                    reveal(LockedArray::typed_lock_map_aligned);
                };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
            }
            ret
        }

        pub fn wunlock_page(
            &mut self,
            page_index: PageIndex,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                index_valid(NUM_PAGES, page_index),
                old(self).pg_arr.spec_index(page_index).view().being_killed() == false,
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id() == old(self).pg_arr.spec_index(page_index).view().locking_thread()->Write_lock_id,
                typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_index, TypedLockMode::Write),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                // ---- Every held lock still matches lctx (page slot now released) ----
                typed_lock_maps_aligned(final(self), final(lctx)),
                lock_id_set_aligned(final(lctx)),
                final(self).pt_mp     == old(self).pt_mp,
                final(self).it_mp     == old(self).it_mp,
                final(self).irt     == old(self).irt,
                final(self).cpu_arr         == old(self).cpu_arr,
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
                // ---- page_array: only the targeted slot's lock state changed (now unlocked) ----
                final(self).pg_arr.unchanged_except(&old(self).pg_arr, page_index),
                final(self).pg_arr.lock_id_by_index(page_index) == old(self).pg_arr.lock_id_by_index(page_index),
                typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Page(page_index)),
                // ---- LocalContext: lock dropped; thread preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` flips it Acquire → Release (same trap as the
                // `LockedArray::wunlock` NOTE).
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,
                // ---- wunlock ensures (forwarded from LockedArray::wunlock) ----
                wunlock_ensures(old(self).pg_arr.spec_index(page_index).view(), final(self).pg_arr.spec_index(page_index).view()),
                page_objects_unlocked_except(old(self).pg_arr, old(lctx).thread_id(), set![page_index]) ==> page_objects_unlocked(final(self).pg_arr, final(lctx).thread_id()),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().remove((old(self).pg_arr.lock_id_by_index(page_index), KernelObjId::Page(page_index))),
                unlock_ensures(old(lctx), final(lctx), (), lock_perm.view().lock_id(), KernelObjId::Page(page_index), old(self).pg_arr.lock_id_by_index(page_index)),
        {
            assert(self.pg_arr.inv()) by { reveal(page_array_wf); };
            assert({
                &&& self.pg_arr.spec_index(page_index).view().wlocked_by(lctx)
                &&& lctx.lock_entry_contains(self.pg_arr.lock_id_by_index(page_index), KernelObjId::Page(page_index))
            }) by { reveal(LockedArray::typed_lock_map_aligned); };
            assert(lctx.lock_id_set().contains((self.pg_arr.lock_id_by_index(page_index), KernelObjId::Page(page_index)))) by {
                reveal(lock_id_set_aligned);
            };
            self.pg_arr.wunlock(page_index, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::Page(page_index)));
            proof {
                assert(page_array_wf(self.pg_arr)) by { lemma_no_change_imply_page_array_wf_forall(); };
                assert(page_invariant_fields_unchanged(old(self).pg_arr, self.pg_arr)) by { page_lock_op_preserves_invariant_fields(old(self).pg_arr, self.pg_arr, page_index); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.memory_management_inv()) by { lemma_no_change_imply_memory_management_inv_for_page_fields_forall(); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by {
                    reveal(LockedArray::typed_lock_map_aligned);
                };
            }
        }

}
} // verus!
