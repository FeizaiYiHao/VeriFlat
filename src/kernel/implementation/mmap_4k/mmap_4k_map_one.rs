use vstd::prelude::*;
use crate::*;
use super::mmap_4k_context::{
    mmap_4k_held_context,
    mmap_4k_no_page_locks,
    mmap_4k_other_objects_unlocked,
};
use super::mmap_4k_range_induction::pagetable_leaf_insert_preserves_prepared_range_forall;
use super::mmap_4k_syscall_def::mmap_4k_range_prepared;
verus! {

impl KernelK {
    /// Publish one 4K leaf after the directory walk has already been prepared.
    /// The leaf publication contributes exactly one recorded user step.
    pub(super) fn map_one_mmap_4k_page(
        &mut self,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        process_ptr: RwLockProcessPtr,
        container_ptr: RwLockContainerPtr,
        cpu_id: CpuId,
        pagetable_ptr: RwLockPageTableRoot,
        va: VAddr,
        range: &VaRange4K,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
        Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
    )
        requires
            mmap_4k_held_context(
                old(self), old(lctx), alloc_ptr_4k, thread_ptr, process_ptr,
                container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                pagetable_lock_perm,
            ),
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
            va_4k_valid(va),
            range.wf(),
            old(self).container_map.spec_index(container_ptr).being_killed() == false,
            old(self).process_map.spec_index(process_ptr).being_killed() == false,
            old(self).process_map.spec_index(process_ptr).view().pagetable
                == pagetable_ptr,
            old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(self).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            old(self).thread_map.spec_index(thread_ptr).view().quota_4k >= 1,
            thread_effective_quota_4k(
                old(self).thread_map.spec_index(thread_ptr),
            ) >= 1,
            old(self).pagetable_map.spec_index(pagetable_ptr).view().wf(),
            old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end <= spec_va2index(va).0 && pei_valid(spec_va2index(va).0),
            pei_valid(spec_va2index(va).1),
            pei_valid(spec_va2index(va).2),
            pei_valid(spec_va2index(va).3),
            old(self).pagetable_map.spec_index(pagetable_ptr).view()
                .spec_4k_entry_useable(
                    spec_va2index(va).0,
                    spec_va2index(va).1,
                    spec_va2index(va).2,
                    spec_va2index(va).3,
                ),
            old(self).pagetable_map.spec_index(pagetable_ptr).view()
                .spec_resolve_mapping_l2(
                    spec_va2index(va).0,
                    spec_va2index(va).1,
                    spec_va2index(va).2,
                ) is Some,
            mmap_4k_range_prepared(
                old(self).pagetable_map.spec_index(pagetable_ptr).view(),
                range,
            ),
            mmap_4k_no_page_locks(old(lctx)),
            page_objects_unlocked(old(self).page_array, old(lctx).thread_id()),
        ensures
            mmap_4k_held_context(
                final(self), final(lctx), alloc_ptr_4k, thread_ptr, process_ptr,
                container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                pagetable_lock_perm,
            ),
            final(steps).steps.len() == old(steps).steps.len() + 1,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
            mmap_4k_no_page_locks(final(lctx)),
            page_objects_unlocked(final(self).page_array, final(lctx).thread_id()),
            final(lctx).lock_id_set() == old(lctx).lock_id_set(),
            final(lctx).stable_lock_id_set() == old(lctx).stable_lock_id_set(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().wf(),
            final(self).container_map.spec_index(container_ptr).being_killed() == false,
            final(self).process_map.spec_index(process_ptr).being_killed() == false,
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            final(self).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            final(self).thread_map.spec_index(thread_ptr).view().quota_4k
                == old(self).thread_map.spec_index(thread_ptr).view().quota_4k - 1,
            final(self).process_map.spec_index(process_ptr)
                == old(self).process_map.spec_index(process_ptr),
            final(self).container_map.spec_index(container_ptr)
                == old(self).container_map.spec_index(container_ptr),
            final(self).cpu_array.spec_index(cpu_id).view()
                == old(self).cpu_array.spec_index(cpu_id).view(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k()
                == old(self).pagetable_map.spec_index(pagetable_ptr).view()
                    .mapping_4k().insert(
                        va,
                        final(self).pagetable_map.spec_index(pagetable_ptr)
                            .view().mapping_4k().spec_index(va),
                    ),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end,
            mmap_4k_range_prepared(
                final(self).pagetable_map.spec_index(pagetable_ptr).view(),
                range,
            ),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger final(self).pagetable_map.spec_index(pagetable_ptr)
                    .view().spec_resolve_mapping_l2(l4i, l3i, l2i)]
                final(self).pagetable_map.spec_index(pagetable_ptr).view()
                    .kernel_l4_end <= l4i && pei_valid(l4i)
                    && pei_valid(l3i)
                    && pei_valid(l2i)
                ==> final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(l4i, l3i, l2i)
                    == old(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(l4i, l3i, l2i),
            final(self).pagetable_map.spec_index(pagetable_ptr).view()
                .mapping_4k().dom().contains(va),
            final(self).pagetable_map.spec_index(pagetable_ptr).view()
                .mapping_4k().spec_index(va).present,
            final(self).pagetable_map.spec_index(pagetable_ptr).view()
                .mapping_4k().spec_index(va).write,
            final(self).pagetable_map.spec_index(pagetable_ptr).view()
                .mapping_4k().spec_index(va).execute_disable,
    {
        proof {
            assert(self.pagetable_map.perms_wf()
                && self.pagetable_map.spec_index(pagetable_ptr).is_init()) by {
                reveal(pagetable_perms_wf);

            };
        }
        let (page_ptr, Tracked(page_lock_perm)) = self.stage_mmap_4k_page(
            alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id,
            pagetable_ptr, Tracked(&mut *lctx), Tracked(&mut *steps),
            Tracked(thread_lock_perm), Tracked(pagetable_lock_perm),
        );
        assert(!self.pagetable_map.spec_index(pagetable_ptr).view()
            .mapping_4k().dom().contains(va)) by {
            reveal(PageTable::wf_mapping_4k);
            spec_va_4k_index_roundtrip();
        };
        self.map_owned_4k_page(
            page_ptr, thread_ptr, pagetable_ptr, va, true, true,
            Tracked(&mut *lctx), Tracked(&page_lock_perm),
            Tracked(thread_lock_perm), Tracked(pagetable_lock_perm),
        );
        proof {
            assert(page_objects_unlocked_except(
                self.page_array, lctx.thread_id(),
                set![page_ptr2page_index(page_ptr)],
            )) by {
                reveal(page_objects_unlocked_except);
            };
        }
        self.wunlock_page(
            page_ptr2page_index(page_ptr),
            Tracked(&mut *lctx),
            Tracked(page_lock_perm),
        );
        proof {
            assert({
                &&& lctx.lock_id_set() == old(lctx).lock_id_set()
                &&& lctx.stable_lock_id_set() == old(lctx).stable_lock_id_set()
                &&& self.cpu_array.spec_index(cpu_id).view()
                    .locked_by_thread(lctx.thread_id())
                &&& self.container_map.spec_index(container_ptr)
                    .locked_by_thread(lctx.thread_id())
                &&& self.process_map.spec_index(process_ptr)
                    .locked_by_thread(lctx.thread_id())
                &&& self.thread_map.spec_index(thread_ptr)
                    .locked_by_thread(lctx.thread_id())
                &&& self.pagetable_map.spec_index(pagetable_ptr)
                    .locked_by_thread(lctx.thread_id())
            }) by {
                reveal(lock_id_aligned);
            };
            self.kernel_step_boundary(&mut *lctx, &mut *steps);
            assert(self.allocator_4k_map.dom().contains(alloc_ptr_4k)) by {
                reveal(container_allocator_wf);
            };
            assert(self.pagetable_map.spec_index(pagetable_ptr).view().wf()) by {
                reveal(pagetable_perms_wf);
            };
            assert(mmap_4k_range_prepared(
                self.pagetable_map.spec_index(pagetable_ptr).view(),
                range,
            )) by {
                pagetable_leaf_insert_preserves_prepared_range_forall();
            };
        }
    }
}

} // verus!
