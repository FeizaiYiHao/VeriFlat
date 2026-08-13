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
                cpu_id_valid(cpu_id),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).lock_id_acyclic(old(self).cpu_array.lock_id_by_index(cpu_id)),
                old(self).locked_objects_match_lctx(old(lctx)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
                // ---- Every held lock still matches lctx (cpu now locked) ----
                final(self).locked_objects_match_lctx(final(lctx)),

                // ---- Dynamic lock ids remain aligned ----
                lock_id_aligned(final(self), final(lctx)),

                // ---- Field framing: only cpu_array's lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).iommu_table_map     == old(self).iommu_table_map,
                final(self).iommu_root_table     == old(self).iommu_root_table,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).iommu_tlb           == old(self).iommu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).scheduler_map     == old(self).scheduler_map,
                final(self).pcid_allocator_map == old(self).pcid_allocator_map,
                final(self).process_map       == old(self).process_map,
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_4k_map  == old(self).allocator_4k_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- cpu_array: only the targeted slot's lock state changed ----
                final(self).cpu_array.unchanged_except(&old(self).cpu_array, cpu_id),
                final(self).cpu_array.inv(),
                cpu_objects_unlocked(old(self).cpu_array, old(lctx).thread_id())
                    ==> cpu_objects_unlocked_except(
                        final(self).cpu_array, final(lctx).thread_id(), cpu_id),

                // ---- LocalContext: phases preserved ----
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),

                // ---- The lock perm + lock ensures (forwarded from LockedArray::wlock) ----
                wlock_ensures(
                    old(self).cpu_array.spec_index(cpu_id).view(),
                    final(self).cpu_array.spec_index(cpu_id).view(),
                    old(self).cpu_array.lock_id_by_index(cpu_id),
                    final(lctx),
                    ret.view(),
                ),
                final(lctx).lock_id_set() == old(lctx).lock_id_set().insert(
                    (
                        final(self).cpu_array.lock_id_by_index(cpu_id),
                        KernelObjId::Cpu(cpu_id),
                    ),
                ),
                final(lctx).stable_lock_id_set() == old(lctx).stable_lock_id_set(),
        {
            proof {
                assert(old(self).cpu_array.inv()) by {
                    reveal(cpu_array_wf);
                };
                assert({
                    &&& old(lctx).lock_entry_fresh(
                        old(self).cpu_array.lock_id_by_index(cpu_id),
                        KernelObjId::Cpu(cpu_id),
                        MUTABLE_LOCK_ID,
                    )
                    &&& old(lctx).lock_entry_contains_for(
                        old(self).cpu_array.lock_id_by_index(cpu_id),
                        KernelObjId::Cpu(cpu_id),
                        MUTABLE_LOCK_ID,
                    ) == old(self).cpu_array.spec_index(cpu_id).view()
                        .wlocked_by_thread(old(lctx).thread_id())
                }) by {
                    reveal(lock_id_aligned);
                };
            }
            let ret = self.cpu_array.wlock(cpu_id, Tracked(&mut *lctx), Ghost(KernelObjId::Cpu(cpu_id)));
            proof {
                assert(self.inv()) by {
                    assert(cpu_array_wf(
                        self.cpu_array,
                        self.default_pagetable.view(),
                    )) by {
                        reveal(cpu_array_wf);
                    };
                    assert(self.subsystems_inv()) by {
                        reveal(KernelK::default_pagetable_wf);
                    };
                    assert(self.process_management_inv()) by {
                        assert(container_cpu_wf(
                            self.container_map,
                            self.cpu_array,
                        )) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(container_perms_wf);
                            reveal(container_cpu_wf);
                        };
                        assert(process_cpu_wf(
                            self.process_map,
                            self.cpu_array,
                        )) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(process_cpu_wf);
                        };
                        assert(thread_cpu_wf(
                            self.thread_map,
                            self.cpu_array,
                        )) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(thread_cpu_wf);
                        };
                    };
                    assert(cpu_dirty_map_wf(
                        self.container_map,
                        self.process_map,
                        self.cpu_array,
                        self.cpu_tlb,
                        self.pagetable_map,
                    )) by {
                        reveal(LockedArray::payloads_unchanged);
                        reveal(cpu_dirty_map_contains_container_processes);
                        reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                        reveal(cpu_dirty_map_proc_pcid_match);
                        reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                        reveal(container_cpu_wf);
                    };
                    assert(tlb_wf_spec(
                        self.cpu_tlb,
                        self.pagetable_map,
                        self.cpu_array,
                    )) by {
                        reveal(LockedArray::payloads_unchanged);
                        reveal(tlb_wf_spec);
                    };
                    reveal(KernelK::inv);
                };
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);
                    reveal(lock_ensures);
                };
                assert(cpu_objects_unlocked(
                    old(self).cpu_array, old(lctx).thread_id(),
                ) ==> cpu_objects_unlocked_except(
                    self.cpu_array, lctx.thread_id(), cpu_id,
                )) by {
                    reveal(cpu_objects_unlocked_except);
                };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                };
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
                cpu_id_valid(cpu_id),
                old(self).cpu_array.spec_index(cpu_id).view().being_killed() == false,
                old(self).cpu_array.spec_index(cpu_id).view().wlocked_by(old(lctx)),
                lock_perm.view().state() is WriteLock,
                lock_perm.view().thread_id() == old(lctx).thread_id(),
                lock_perm.view().lock_id()
                    == old(self).cpu_array.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
                old(self).locked_objects_match_lctx(old(lctx)),
                lock_id_aligned(old(self), old(lctx)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),
                kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),

                // ---- Every held lock still matches lctx (cpu now released) ----
                final(self).locked_objects_match_lctx(final(lctx)),

                // ---- Dynamic lock ids remain aligned ----
                lock_id_aligned(final(self), final(lctx)),

                // ---- Field framing: only cpu_array's lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).iommu_table_map     == old(self).iommu_table_map,
                final(self).iommu_root_table     == old(self).iommu_root_table,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).iommu_tlb           == old(self).iommu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).scheduler_map     == old(self).scheduler_map,
                final(self).pcid_allocator_map == old(self).pcid_allocator_map,
                final(self).process_map       == old(self).process_map,
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_4k_map  == old(self).allocator_4k_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- cpu_array: only the targeted slot's lock state changed (now unlocked) ----
                final(self).cpu_array.unchanged_except(&old(self).cpu_array, cpu_id),
                final(self).cpu_array.inv(),
                final(self).cpu_array.spec_index(cpu_id).view().locking_thread() is None,
                !final(self).cpu_array.spec_index(cpu_id).view().locked(),
                final(self).cpu_array.lock_id_by_index(cpu_id)
                    == old(self).cpu_array.lock_id_by_index(cpu_id),
                wunlock_ensures(
                    old(self).cpu_array.spec_index(cpu_id).view(),
                    final(self).cpu_array.spec_index(cpu_id).view(),
                ),
                cpu_objects_unlocked_except(
                    old(self).cpu_array, old(lctx).thread_id(), cpu_id,
                ) ==> cpu_objects_unlocked(
                    final(self).cpu_array, final(lctx).thread_id()),

                // ---- LocalContext: lock dropped; thread preserved ----
                // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
                // `unlock_ensures` transitions it Acquire -> Release, so restating
                // `== old` would contradict it and make the postcondition `false`
                // in an Acquire section. `unlock_ensures` is the source of truth
                // for the phase transition (same trap as the NOTE on
                // `LockedArray::wunlock`). user_view is separately preserved.
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() is Release,

                final(lctx).lock_id_set() == old(lctx).lock_id_set().remove(
                    (
                        old(self).cpu_array.lock_id_by_index(cpu_id),
                        KernelObjId::Cpu(cpu_id),
                    ),
                ),
                final(lctx).stable_lock_id_set() == old(lctx).stable_lock_id_set(),
        {
            proof {
                assert(old(self).cpu_array.inv()) by {
                    reveal(cpu_array_wf);
                };
                assert(old(lctx).lock_entry_contains_for(
                    old(self).cpu_array.lock_id_by_index(cpu_id),
                    KernelObjId::Cpu(cpu_id),
                    MUTABLE_LOCK_ID,
                )) by {
                    reveal(lock_id_aligned);
                };
            }
            self.cpu_array.wunlock(cpu_id, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::Cpu(cpu_id)));
            // Re-establish inv(). Only `cpu_array[cpu_id]`'s lock state moved
            // (now unlocked); every payload view, every other slot, and every
            // other KernelK field is unchanged. Same template as wlock_cpu.
            proof {
                assert(self.inv()) by {
                    assert(cpu_array_wf(
                        self.cpu_array,
                        self.default_pagetable.view(),
                    )) by {
                        reveal(cpu_array_wf);
                    };
                    assert(self.subsystems_inv()) by {
                        reveal(KernelK::default_pagetable_wf);
                    };
                    assert(self.process_management_inv()) by {
                        assert(container_cpu_wf(
                            self.container_map,
                            self.cpu_array,
                        )) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(container_perms_wf);
                            reveal(container_cpu_wf);
                        };
                        assert(process_cpu_wf(
                            self.process_map,
                            self.cpu_array,
                        )) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(process_cpu_wf);
                        };
                        assert(thread_cpu_wf(
                            self.thread_map,
                            self.cpu_array,
                        )) by {
                            reveal(LockedArray::payloads_unchanged);
                            reveal(thread_cpu_wf);
                        };
                    };
                    assert(cpu_dirty_map_wf(
                        self.container_map,
                        self.process_map,
                        self.cpu_array,
                        self.cpu_tlb,
                        self.pagetable_map,
                    )) by {
                        reveal(LockedArray::payloads_unchanged);
                        reveal(cpu_dirty_map_contains_container_processes);
                        reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                        reveal(cpu_dirty_map_proc_pcid_match);
                        reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                        reveal(container_cpu_wf);
                    };
                    assert(tlb_wf_spec(
                        self.cpu_tlb,
                        self.pagetable_map,
                        self.cpu_array,
                    )) by {
                        reveal(LockedArray::payloads_unchanged);
                        reveal(tlb_wf_spec);
                    };
                    reveal(KernelK::inv);
                };
                assert(lock_id_aligned(self, &*lctx)) by {
                    reveal(lock_id_aligned);
                    reveal(unlock_ensures);
                };
                assert(cpu_objects_unlocked_except(
                    old(self).cpu_array, old(lctx).thread_id(), cpu_id,
                ) ==> cpu_objects_unlocked(
                    self.cpu_array, lctx.thread_id(),
                )) by {
                    reveal(cpu_objects_unlocked_except);
                };
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
                };
            }
        }


}
} // verus!
