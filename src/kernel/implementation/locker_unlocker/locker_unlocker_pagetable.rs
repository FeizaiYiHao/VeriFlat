use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
        pub fn wlock_pagetable(
            &mut self,
            pagetable_ptr: RwLockPageTableRoot,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Tracked<LockPerm>)
            requires
                old(self).inv(),
                old(self).pt_mp.dom().contains(pagetable_ptr),
                wlock_requires(old(self).pt_mp.spec_index(pagetable_ptr), old(lctx)),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).lock_id_acyclic(old(self).pt_mp.lock_id_by_key(pagetable_ptr)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                lock_id_aligned(final(self), final(lctx)),
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
                final(self).pt_mp.unchanged_except(&old(self).pt_mp, pagetable_ptr),
                pagetable_objects_unlocked(old(self).pt_mp, old(lctx).thread_id()) ==> pagetable_objects_unlocked_except(final(self).pt_mp, final(lctx).thread_id(), set![pagetable_ptr]),
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                wlock_ensures(old(self).pt_mp.spec_index(pagetable_ptr), final(self).pt_mp.spec_index(pagetable_ptr), old(self).pt_mp.lock_id_by_key(pagetable_ptr), final(lctx), ret.view()),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(self).pt_mp.lock_id_by_key(pagetable_ptr), KernelObjId::PageTable(pagetable_ptr))),
                forall|other_pagetable: RwLockPageTableRoot|
                    #![trigger final(lctx).lock_id_set().contains((final(self).pt_mp.lock_id_by_key(other_pagetable), KernelObjId::PageTable(other_pagetable)))]
                    old(self).pt_mp.dom().contains(other_pagetable)
                        && other_pagetable != pagetable_ptr
                    ==> final(lctx).lock_id_set().contains((final(self).pt_mp.lock_id_by_key(other_pagetable), KernelObjId::PageTable(other_pagetable))) == old(lctx).lock_id_set().contains((old(self).pt_mp.lock_id_by_key(other_pagetable), KernelObjId::PageTable(other_pagetable))),
        {
            proof {
                assert(old(self).pt_mp.perms_wf()) by { reveal(pagetable_perms_wf); };
            }
            let ret = self.pt_mp.wlock(pagetable_ptr, Tracked(&mut *lctx), Ghost(KernelObjId::PageTable(pagetable_ptr)));
            proof {
                assert(pagetable_invariant_fields_unchanged(old(self).pt_mp, self.pt_mp)) by { pagetable_lock_op_preserves_invariant_fields(old(self).pt_mp, self.pt_mp, pagetable_ptr); };
                assert(self.subsystems_inv()) by {
                    assert(pagetable_perms_wf(self.pt_mp)) by { lemma_no_change_imply_pagetable_perms_wf_forall(); };
                    reveal(KernelK::default_pagetable_wf);
                };
                assert(self.memory_management_inv()) by {
                    assert(process_pagetable_match(self.prc_mp, self.pt_mp)) by { lemma_no_change_imply_process_pagetable_match_for_pagetable_fields_forall(); };
                    assert(page_pagetable_wf(self.pt_mp, self.pg_arr)) by { lemma_no_change_imply_page_pagetable_wf_for_pagetable_fields_forall(); };
                    assert(container_process_page_pagetable_wf(self.ctn_mp, self.prc_mp, self.pt_mp, self.pg_arr)) by { lemma_no_change_imply_container_process_page_pagetable_wf_for_pagetable_fields_forall(); };
                    assert(pagetable_pages_wf(self.pt_mp, self.pg_arr)) by { lemma_no_change_imply_pagetable_pages_wf_for_pagetable_fields_forall(); };
                };
                assert(cpu_dirty_map_wf(self.ctn_mp, self.prc_mp, self.cpu_arr, self.cpu_tlb, self.pt_mp)) by { lemma_no_change_imply_cpu_dirty_map_wf_for_pagetable_fields_forall(); };
                assert(tlb_wf_spec(self.cpu_tlb, self.pt_mp, self.cpu_arr)) by { lemma_no_change_imply_tlb_wf_spec_for_pagetable_fields_forall(); };
                assert(lock_id_aligned(self, &*lctx)) by { reveal(lock_id_aligned); };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
            }
            ret
        }

        pub fn wunlock_pagetable(
            &mut self,
            pagetable_ptr: RwLockPageTableRoot,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                old(self).pt_mp.dom().contains(pagetable_ptr),
                old(self).pt_mp.spec_index(pagetable_ptr).wlocked_by(old(lctx)),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id() == old(self).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
                old(lctx).lock_id_set().contains((old(self).pt_mp.lock_id_by_key(pagetable_ptr), KernelObjId::PageTable(pagetable_ptr))),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                lock_id_aligned(final(self), final(lctx)),
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
                final(self).pt_mp.unchanged_except(&old(self).pt_mp, pagetable_ptr),
                final(self).pt_mp.lock_id_by_key(pagetable_ptr) == old(self).pt_mp.lock_id_by_key(pagetable_ptr),
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,
                wunlock_ensures(old(self).pt_mp.spec_index(pagetable_ptr), final(self).pt_mp.spec_index(pagetable_ptr)),
                pagetable_objects_unlocked_except(old(self).pt_mp, old(lctx).thread_id(), set![pagetable_ptr]) ==> pagetable_objects_unlocked(final(self).pt_mp, final(lctx).thread_id()),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().remove((old(self).pt_mp.lock_id_by_key(pagetable_ptr), KernelObjId::PageTable(pagetable_ptr))),
                forall|other_pagetable: RwLockPageTableRoot|
                    #![trigger final(lctx).lock_id_set().contains((final(self).pt_mp.lock_id_by_key(other_pagetable), KernelObjId::PageTable(other_pagetable)))]
                    old(self).pt_mp.dom().contains(other_pagetable)
                        && other_pagetable != pagetable_ptr
                    ==> final(lctx).lock_id_set().contains((final(self).pt_mp.lock_id_by_key(other_pagetable), KernelObjId::PageTable(other_pagetable))) == old(lctx).lock_id_set().contains((old(self).pt_mp.lock_id_by_key(other_pagetable), KernelObjId::PageTable(other_pagetable))),
        {
            proof {
                assert({
                    &&& old(self).pt_mp.perms_wf()
                    &&& old(self).pt_mp.spec_index(pagetable_ptr).inv()
                }) by { reveal(pagetable_perms_wf); };
            }
            self.pt_mp.wunlock(pagetable_ptr, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::PageTable(pagetable_ptr)));
            proof {
                assert(pagetable_invariant_fields_unchanged(old(self).pt_mp, self.pt_mp)) by { pagetable_lock_op_preserves_invariant_fields(old(self).pt_mp, self.pt_mp, pagetable_ptr); };
                assert(self.subsystems_inv()) by {
                    assert(pagetable_perms_wf(self.pt_mp)) by { lemma_no_change_imply_pagetable_perms_wf_forall(); };
                    reveal(KernelK::default_pagetable_wf);
                };
                assert(self.memory_management_inv()) by {
                    assert(process_pagetable_match(self.prc_mp, self.pt_mp)) by { lemma_no_change_imply_process_pagetable_match_for_pagetable_fields_forall(); };
                    assert(page_pagetable_wf(self.pt_mp, self.pg_arr)) by { lemma_no_change_imply_page_pagetable_wf_for_pagetable_fields_forall(); };
                    assert(container_process_page_pagetable_wf(self.ctn_mp, self.prc_mp, self.pt_mp, self.pg_arr)) by { lemma_no_change_imply_container_process_page_pagetable_wf_for_pagetable_fields_forall(); };
                    assert(pagetable_pages_wf(self.pt_mp, self.pg_arr)) by { lemma_no_change_imply_pagetable_pages_wf_for_pagetable_fields_forall(); };
                };
                assert(cpu_dirty_map_wf(self.ctn_mp, self.prc_mp, self.cpu_arr, self.cpu_tlb, self.pt_mp)) by { lemma_no_change_imply_cpu_dirty_map_wf_for_pagetable_fields_forall(); };
                assert(tlb_wf_spec(self.cpu_tlb, self.pt_mp, self.cpu_arr)) by { lemma_no_change_imply_tlb_wf_spec_for_pagetable_fields_forall(); };
                assert(lock_id_aligned(self, &*lctx)) by { reveal(lock_id_aligned); };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
            }
        }
}
} // verus!
