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
                !old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).scheduler_lock_map().dom().is_empty(),
                old(lctx).cpu_set_lock_map().dom().is_empty(),
                old(lctx).iommu_table_lock_map().dom().is_empty(),
                old(lctx).pcid_needflush_lock_map().dom().is_empty(),
                old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
                old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
                old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
                forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
                forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(self).pg_arr.lock_id_by_index(held_page).major < PAGE_TABLE_LOCK_MAJOR,
                forall|held_pagetable: RwLockPageTableRoot| #![trigger old(lctx).pagetable_lock_map().dom().contains(held_pagetable)] old(lctx).pagetable_lock_map().dom().contains(held_pagetable) ==> held_pagetable < pagetable_ptr,
                typed_lock_maps_aligned(old(self), old(lctx)),
            ensures
                pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pagetable_ptr, final(self).pt_mp.spec_index(pagetable_ptr).view()),
                final(self).pt_mp.spec_index(pagetable_ptr).view().leaves_present(),
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                final(self).inv(),
                kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
                kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
                kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
                typed_lock_maps_aligned(final(self), final(lctx)),
                *final(self) == (KernelK { pt_mp: final(self).pt_mp, ..*old(self) }),
                final(self).pt_mp.unchanged_except(&old(self).pt_mp, pagetable_ptr),
                final(self).pt_mp.lock_id_by_key(pagetable_ptr) == old(self).pt_mp.lock_id_by_key(pagetable_ptr),
                forall|other_pagetable: RwLockPageTableRoot|
                    #![trigger final(self).pt_mp.lock_id_by_key(other_pagetable)]
                    other_pagetable != pagetable_ptr && old(self).pt_mp.dom().contains(other_pagetable)
                    ==> final(self).pt_mp.dom().contains(other_pagetable)
                        && final(self).pt_mp.lock_id_by_key(other_pagetable) == old(self).pt_mp.lock_id_by_key(other_pagetable),
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                wlock_ensures(old(self).pt_mp.spec_index(pagetable_ptr), final(self).pt_mp.spec_index(pagetable_ptr), old(self).pt_mp.lock_id_by_key(pagetable_ptr), final(lctx), ret.view()),
                typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::PageTable(pagetable_ptr), TypedHeldLock { lock_id: final(self).pt_mp.lock_id_by_key(pagetable_ptr), mode: TypedLockMode::Write }),
        {
            proof {
                pagetable_perms_wf_at(old(self).pt_mp, pagetable_ptr);
                assert(old(lctx).lock_id_acyclic(old(self).pt_mp.lock_id_by_key(pagetable_ptr))) by {
                    reveal(LocalContext::lock_id_acyclic); reveal(UnLockedMap::typed_flag_lock_map_aligned);
                    reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned); reveal(pagetable_perms_wf);
                };
                assert(!old(self).pt_mp.spec_index(pagetable_ptr).locked_by_thread(old(lctx).thread_id())) by {
                    if old(self).pt_mp.spec_index(pagetable_ptr).locked_by_thread(old(lctx).thread_id()) {
                        assert(old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
                    }
                };
            }
            assert(wlock_requires(self.pt_mp.spec_index(pagetable_ptr), &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            let ret = self.pt_mp.wlock(pagetable_ptr, Tracked(&mut *lctx), Ghost(KernelObjId::PageTable(pagetable_ptr)));
            proof {
                assert(pagetable_tlb_entries_present(self.cpu_tlb, self.cpu_arr, self.pcid_needflush, pagetable_ptr, self.pt_mp.spec_index(pagetable_ptr).view())) by { reveal(tlb_wf_spec); };
                assert(self.pt_mp.spec_index(pagetable_ptr).view().leaves_present()) by { reveal(pagetable_perms_wf); reveal(pagetable_hidden_leaves_only_when_wlocked); };
                assert(pagetable_invariant_fields_unchanged(old(self).pt_mp, self.pt_mp)) by { pagetable_lock_op_preserves_invariant_fields(old(self).pt_mp, self.pt_mp, pagetable_ptr); };
                assert(self.subsystems_inv()) by {
                    lemma_pagetable_perms_wf_preserved_for_lock_op_forall();
                    reveal(KernelK::default_pagetable_wf);
                };
                assert(self.memory_management_inv()) by {
                    lemma_process_pagetable_match_preserved_for_pagetable_invariant_fields_forall();
                    lemma_page_pagetable_wf_preserved_for_pagetable_invariant_fields_forall();
                    lemma_container_process_page_pagetable_wf_preserved_for_pagetable_invariant_fields_forall();
                    lemma_pagetable_pages_wf_preserved_for_pagetable_invariant_fields_forall();
                };
                assert(cpu_dirty_map_wf(self.ctn_mp, self.cpu_set_mp, self.prc_mp, self.cpu_arr, self.cpu_tlb, self.pt_mp, self.pcid_needflush)) by { lemma_cpu_dirty_map_wf_preserved_for_pagetable_invariant_fields_forall(); };
                assert(tlb_wf_spec(self.cpu_tlb, self.pt_mp, self.cpu_arr, self.pcid_needflush)) by { lemma_tlb_wf_spec_preserved_for_pagetable_invariant_fields_forall(); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
                assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by {
                    broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
                    reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
                    reveal(kernel_pagetable_nonlock_fields_unchanged);
                };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
            }
            ret
        }

        pub fn wlock_pagetable_pair(
            &mut self,
            source_pagetable: RwLockPageTableRoot,
            target_pagetable: RwLockPageTableRoot,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: (Tracked<LockPerm>, Tracked<LockPerm>))
            requires
                old(self).inv(),
                source_pagetable != target_pagetable,
                old(self).pt_mp.dom().contains(source_pagetable),
                old(self).pt_mp.dom().contains(target_pagetable),
                !old(lctx).pagetable_lock_map().dom().contains(source_pagetable),
                !old(lctx).pagetable_lock_map().dom().contains(target_pagetable),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).scheduler_lock_map().dom().is_empty(),
                old(lctx).cpu_set_lock_map().dom().is_empty(),
                old(lctx).iommu_table_lock_map().dom().is_empty(),
                old(lctx).pcid_needflush_lock_map().dom().is_empty(),
                old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
                old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
                old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
                forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
                forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(self).pg_arr.lock_id_by_index(held_page).major < PAGE_TABLE_LOCK_MAJOR,
                forall|held_pagetable: RwLockPageTableRoot| #![trigger old(lctx).pagetable_lock_map().dom().contains(held_pagetable)] old(lctx).pagetable_lock_map().dom().contains(held_pagetable) ==> held_pagetable < source_pagetable && held_pagetable < target_pagetable,
                typed_lock_maps_aligned(old(self), old(lctx)),
            ensures
                old(self).pt_mp.spec_index(source_pagetable).locking_thread() is None,
                old(self).pt_mp.spec_index(target_pagetable).locking_thread() is None,
                final(self).pt_mp.spec_index(source_pagetable).view() == old(self).pt_mp.spec_index(source_pagetable).view(),
                final(self).pt_mp.spec_index(target_pagetable).view() == old(self).pt_mp.spec_index(target_pagetable).view(),
                forall|p: RwLockPageTableRoot| #![trigger final(self).pt_mp.spec_index(p)] old(self).pt_mp.dom().contains(p) && p != source_pagetable && p != target_pagetable ==> final(self).pt_mp.spec_index(p) == old(self).pt_mp.spec_index(p),
                pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, source_pagetable, final(self).pt_mp.spec_index(source_pagetable).view()),
                pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, target_pagetable, final(self).pt_mp.spec_index(target_pagetable).view()),
                final(self).pt_mp.spec_index(source_pagetable).view().leaves_present(),
                final(self).pt_mp.spec_index(target_pagetable).view().leaves_present(),
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                final(self).inv(),
                kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
                kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
                kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
                typed_lock_maps_aligned(final(self), final(lctx)),
                *final(self) == (KernelK { pt_mp: final(self).pt_mp, ..*old(self) }),
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                final(lctx).page_lock_map() == old(lctx).page_lock_map(),
                final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
                final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
                final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
                final(lctx).container_lock_map() == old(lctx).container_lock_map(),
                final(lctx).process_lock_map() == old(lctx).process_lock_map(),
                final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
                final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
                final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
                final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
                final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
                final(lctx).pagetable_lock_map() == if source_pagetable < target_pagetable {
                    old(lctx).pagetable_lock_map()
                        .insert(source_pagetable, TypedHeldLock { lock_id: final(self).pt_mp.lock_id_by_key(source_pagetable), mode: TypedLockMode::Write })
                        .insert(target_pagetable, TypedHeldLock { lock_id: final(self).pt_mp.lock_id_by_key(target_pagetable), mode: TypedLockMode::Write })
                } else {
                    old(lctx).pagetable_lock_map()
                        .insert(target_pagetable, TypedHeldLock { lock_id: final(self).pt_mp.lock_id_by_key(target_pagetable), mode: TypedLockMode::Write })
                        .insert(source_pagetable, TypedHeldLock { lock_id: final(self).pt_mp.lock_id_by_key(source_pagetable), mode: TypedLockMode::Write })
                },
                final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
                final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
                final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
                final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
                typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Write),
                typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
                ret.0.view().state() is WriteLock,
                ret.0.view().thread_id() == final(lctx).thread_id(),
                ret.0.view().lock_id() == final(self).pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
                ret.1.view().state() is WriteLock,
                ret.1.view().thread_id() == final(lctx).thread_id(),
                ret.1.view().lock_id() == final(self).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        {
            if source_pagetable < target_pagetable {
                let Tracked(source_perm) = self.wlock_pagetable(source_pagetable, Tracked(&mut *lctx));
                let Tracked(target_perm) = self.wlock_pagetable(target_pagetable, Tracked(&mut *lctx));
                proof {
                    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
                    assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
                }
                (Tracked(source_perm), Tracked(target_perm))
            } else {
                let Tracked(target_perm) = self.wlock_pagetable(target_pagetable, Tracked(&mut *lctx));
                let Tracked(source_perm) = self.wlock_pagetable(source_pagetable, Tracked(&mut *lctx));
                proof {
                    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
                    assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
                }
                (Tracked(source_perm), Tracked(target_perm))
            }
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
                pagetable_tlb_entries_present(old(self).cpu_tlb, old(self).cpu_arr, old(self).pcid_needflush, pagetable_ptr, old(self).pt_mp.spec_index(pagetable_ptr).view()),
                old(self).pt_mp.spec_index(pagetable_ptr).view().leaves_present(),
                typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id() == old(self).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
                typed_lock_maps_aligned(old(self), old(lctx)),
            ensures
                final(lctx).cpu_id() == old(lctx).cpu_id(),
                final(self).inv(),
                kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
                kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
                kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
                typed_lock_maps_aligned(final(self), final(lctx)),
                *final(self) == (KernelK { pt_mp: final(self).pt_mp, ..*old(self) }),
                final(self).pt_mp.unchanged_except(&old(self).pt_mp, pagetable_ptr),
                final(self).pt_mp.lock_id_by_key(pagetable_ptr) == old(self).pt_mp.lock_id_by_key(pagetable_ptr),
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,
                wunlock_ensures(old(self).pt_mp.spec_index(pagetable_ptr), final(self).pt_mp.spec_index(pagetable_ptr)),
                typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::PageTable(pagetable_ptr)),
        {
            proof {
                assert({
                    &&& old(self).pt_mp.perms_wf()
                    &&& old(self).pt_mp.spec_index(pagetable_ptr).inv()
                }) by { reveal(pagetable_perms_wf); };
                assert(old(lctx).lock_entry_contains(old(self).pt_mp.lock_id_by_key(pagetable_ptr), KernelObjId::PageTable(pagetable_ptr))) by { reveal(LockedMap::typed_lock_map_aligned); };
            }
            assert(self.pt_mp.spec_index(pagetable_ptr).wlocked_by(&*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            self.pt_mp.wunlock(pagetable_ptr, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::PageTable(pagetable_ptr)));
            proof {
                assert(pagetable_invariant_fields_unchanged(old(self).pt_mp, self.pt_mp)) by { pagetable_lock_op_preserves_invariant_fields(old(self).pt_mp, self.pt_mp, pagetable_ptr); };
                assert(self.subsystems_inv()) by {
                    lemma_pagetable_perms_wf_preserved_for_lock_op_forall();
                    reveal(KernelK::default_pagetable_wf);
                };
                assert(self.memory_management_inv()) by {
                    lemma_process_pagetable_match_preserved_for_pagetable_invariant_fields_forall();
                    lemma_page_pagetable_wf_preserved_for_pagetable_invariant_fields_forall();
                    lemma_container_process_page_pagetable_wf_preserved_for_pagetable_invariant_fields_forall();
                    lemma_pagetable_pages_wf_preserved_for_pagetable_invariant_fields_forall();
                };
                assert(cpu_dirty_map_wf(self.ctn_mp, self.cpu_set_mp, self.prc_mp, self.cpu_arr, self.cpu_tlb, self.pt_mp, self.pcid_needflush)) by { lemma_cpu_dirty_map_wf_preserved_for_pagetable_invariant_fields_forall(); };
                assert(tlb_wf_spec(self.cpu_tlb, self.pt_mp, self.cpu_arr, self.pcid_needflush)) by { reveal(tlb_wf_spec); };
                assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
                assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by {
                    broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
                    reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged);
                };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
            }
        }
}
} // verus!
