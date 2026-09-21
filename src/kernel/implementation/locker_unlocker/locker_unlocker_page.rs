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
                old(lctx).lock_id_acyclic(old(self).pg_arr.lock_id_by_index(page_index)),
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                !old(lctx).page_lock_map().dom().contains(page_index),
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                // ---- Every held lock still matches lctx (page slot now locked) ----
                typed_lock_maps_aligned(final(self), final(lctx)),
                // ---- Field framing: only page_array's slot lock state moves ----
                *final(self) == (KernelK { pg_arr: final(self).pg_arr, ..*old(self) }),
                // ---- page_array: only the targeted slot's lock state changed ----
                final(self).pg_arr.unchanged_except(&old(self).pg_arr, page_index),
                // ---- The lock perm + lock ensures (forwarded from LockedArray::wlock) ----
                wlock_ensures(old(self).pg_arr.spec_index(page_index).view(), final(self).pg_arr.spec_index(page_index).view(), old(self).pg_arr.lock_id_by_index(page_index), final(lctx), ret.view()),
                lock_ensures(old(lctx), final(lctx), old(self).pg_arr.lock_id_by_index(page_index), KernelObjId::Page(page_index)),
        {
            proof {
                page_array_wf_at(old(self).pg_arr, page_index);
                assert(!lctx.page_lock_map().dom().contains(page_index)) by {
                    if lctx.page_lock_map().dom().contains(page_index) {
                        assert(lctx.typed_lock_entry(KernelObjId::Page(page_index)).unwrap().lock_id == self.pg_arr.lock_id_by_index(page_index)) by { reveal(LockedArray::typed_lock_map_aligned); };
                        assert(lctx.lock_id_set().contains((self.pg_arr.lock_id_by_index(page_index), KernelObjId::Page(page_index)))) by { reveal(lock_id_set_aligned); };
                    }
                };
                assert(wlock_requires(self.pg_arr.spec_index(page_index).view(), &*lctx)) by { reveal(LockedArray::typed_lock_map_aligned); };
            }
            let ret = self.pg_arr.wlock(page_index, Tracked(&mut *lctx), Ghost(KernelObjId::Page(page_index)));
            proof {
                assert(page_array_wf(self.pg_arr)) by { lemma_page_array_wf_preserved_for_lock_op_forall(); };
                assert(page_invariant_fields_unchanged(old(self).pg_arr, self.pg_arr)) by { page_lock_op_preserves_invariant_fields(old(self).pg_arr, self.pg_arr, page_index); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.memory_management_inv()) by { lemma_memory_management_inv_preserved_for_page_invariant_fields_forall(); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedArray::typed_lock_map_aligned); };
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
                typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_index, TypedLockMode::Write),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id() == old(self).pg_arr.spec_index(page_index).view().locking_thread()->Write_lock_id,
                typed_lock_maps_aligned(old(self), old(lctx)),
                lock_id_set_aligned(old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                // ---- Every held lock still matches lctx (page slot now released) ----
                typed_lock_maps_aligned(final(self), final(lctx)),
                *final(self) == (KernelK { pg_arr: final(self).pg_arr, ..*old(self) }),
                // ---- page_array: only the targeted slot's lock state changed (now unlocked) ----
                final(self).pg_arr.unchanged_except(&old(self).pg_arr, page_index),
                final(self).pg_arr.lock_id_by_index(page_index) == old(self).pg_arr.lock_id_by_index(page_index),
                // ---- wunlock ensures (forwarded from LockedArray::wunlock) ----
                wunlock_ensures(old(self).pg_arr.spec_index(page_index).view(), final(self).pg_arr.spec_index(page_index).view()),
                unlock_ensures(old(lctx), final(lctx), KernelObjId::Page(page_index), old(self).pg_arr.lock_id_by_index(page_index)),
        {
            assert(self.pg_arr.inv()) by { reveal(page_array_wf); };
            assert({
                &&& typed_lock_map_contains_mode(lctx.page_lock_map(), page_index, TypedLockMode::Write)
                &&& lctx.lock_entry_contains(self.pg_arr.lock_id_by_index(page_index), KernelObjId::Page(page_index))
            }) by { reveal(LockedArray::typed_lock_map_aligned); };
            assert(lctx.lock_id_set().contains((self.pg_arr.lock_id_by_index(page_index), KernelObjId::Page(page_index)))) by {
                reveal(lock_id_set_aligned);
            };
            assert(self.pg_arr.spec_index(page_index).view().wlocked_by(&*lctx)) by { reveal(LockedArray::typed_lock_map_aligned); };
            self.pg_arr.wunlock(page_index, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::Page(page_index)));
            proof {
                assert(page_array_wf(self.pg_arr)) by { lemma_page_array_wf_preserved_for_lock_op_forall(); };
                assert(page_invariant_fields_unchanged(old(self).pg_arr, self.pg_arr)) by { page_lock_op_preserves_invariant_fields(old(self).pg_arr, self.pg_arr, page_index); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.memory_management_inv()) by { lemma_memory_management_inv_preserved_for_page_invariant_fields_forall(); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedArray::typed_lock_map_aligned); };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                };
            }
        }
}
} // verus!
