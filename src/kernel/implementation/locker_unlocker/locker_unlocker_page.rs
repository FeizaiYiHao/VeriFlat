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
                {
                    let major = old(self).pg_arr.lock_id_by_index(page_index).major;
                    &&& old(lctx).pcid_needflush_lock_map().dom().is_empty()
                    &&& old(lctx).cpu_offline_flag_lock_map().dom().is_empty()
                    &&& forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off)
                    &&& forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(self).pg_arr.lock_id_by_index(held_page).major < major || (old(self).pg_arr.lock_id_by_index(held_page).major == major && held_page < page_index)
                    &&& major < FREE_PAGE_LOCK_MAJOR ==> {
                        &&& old(lctx).scheduler_lock_map().dom().is_empty()
                        &&& old(lctx).cpu_set_lock_map().dom().is_empty()
                        &&& old(lctx).holds_no_allocator_locks(PageSize::SZ4k)
                        &&& old(lctx).holds_no_allocator_locks(PageSize::SZ2m)
                        &&& old(lctx).holds_no_allocator_locks(PageSize::SZ1g)
                    }
                    &&& major < MAPPED_PAGE_LOCK_MAJOR ==> {
                        &&& old(lctx).endpoint_lock_map().dom().is_empty()
                        &&& old(lctx).pagetable_lock_map().dom().is_empty()
                        &&& old(lctx).iommu_table_lock_map().dom().is_empty()
                        &&& forall|held_thread: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(held_thread)] old(lctx).thread_lock_map().dom().contains(held_thread) ==> {
                            let state = old(self).thr_mp.spec_index(held_thread).view().state;
                            !(state.is_endpoint_waiting() || state is WAITING_REPLY || state is IPC_ENDPOINT_TRANSIT)
                        }
                    }
                },
                typed_lock_maps_aligned(old(self), old(lctx)),
            ensures
                !old(lctx).page_lock_map().dom().contains(page_index),
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
                kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
                kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
                // ---- Every held lock still matches lctx (page slot now locked) ----
                typed_lock_maps_aligned(final(self), final(lctx)),
                // ---- Field framing: only page_array's slot lock state moves ----
                *final(self) == (KernelK { pg_arr: final(self).pg_arr, ..*old(self) }),
                // ---- page_array: only the targeted slot's lock state changed ----
                final(self).pg_arr.unchanged_except(&old(self).pg_arr, page_index),
                held_pages_unchanged(old(self).pg_arr, final(self).pg_arr, old(lctx)),
                // ---- The lock perm + lock ensures (forwarded from LockedArray::wlock) ----
                wlock_ensures(old(self).pg_arr.spec_index(page_index).view(), final(self).pg_arr.spec_index(page_index).view(), old(self).pg_arr.lock_id_by_index(page_index), final(lctx), ret.view()),
                lock_ensures(old(lctx), final(lctx), old(self).pg_arr.lock_id_by_index(page_index), KernelObjId::Page(page_index)),
        {
            proof {
                page_array_wf_at(old(self).pg_arr, page_index);
                assert(old(lctx).lock_id_acyclic(old(self).pg_arr.lock_id_by_index(page_index))) by {
                    reveal(LocalContext::lock_id_acyclic); reveal(UnLockedMap::typed_flag_lock_map_aligned);
                    reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned); reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
                };
                assert(!lctx.page_lock_map().dom().contains(page_index)) by {
                    reveal(LocalContext::lock_id_acyclic); reveal(UnLockedMap::typed_flag_lock_map_aligned);
                    if lctx.page_lock_map().dom().contains(page_index) {
                        assert(lctx.page_lock_map().index(page_index).lock_id == self.pg_arr.lock_id_by_index(page_index)) by { reveal(LockedArray::typed_lock_map_aligned); };
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
                assert(held_pages_unchanged(old(self).pg_arr, self.pg_arr, old(lctx))) by { reveal(LockedArray::typed_lock_map_aligned); };
                assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
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
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
                kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
                kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
                kernel_k_to_nonlock_kernel_u(*final(self)) == kernel_k_to_nonlock_kernel_u(*old(self)),
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
            assert(self.pg_arr.spec_index(page_index).view().wlocked_by(&*lctx)) by { reveal(LockedArray::typed_lock_map_aligned); };
            self.pg_arr.wunlock(page_index, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::Page(page_index)));
            proof {
                assert(page_array_wf(self.pg_arr)) by { lemma_page_array_wf_preserved_for_lock_op_forall(); };
                assert(page_invariant_fields_unchanged(old(self).pg_arr, self.pg_arr)) by { page_lock_op_preserves_invariant_fields(old(self).pg_arr, self.pg_arr, page_index); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.memory_management_inv()) by { lemma_memory_management_inv_preserved_for_page_invariant_fields_forall(); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedArray::typed_lock_map_aligned); };
                assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
                assert(kernel_k_to_nonlock_kernel_u(*self) == kernel_k_to_nonlock_kernel_u(*old(self))) by { kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(old(self), self); };
            }
        }
}
} // verus!
