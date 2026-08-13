use vstd::prelude::*;
use crate::*;
use super::mmap_4k_context::{
    mmap_4k_held_context,
    mmap_4k_no_page_locks,
    mmap_4k_other_objects_unlocked,
};
use super::mmap_4k_create_entry_install::MissingPageTableLevel;

verus! {

impl KernelK {
    /// Allocate and install one missing directory page, then end the kernel
    /// section.  Directory topology is absent from `PageTableU`, so this
    /// boundary is a stuttering user step.
    pub(super) fn install_one_mmap_4k_directory_page(
        &mut self,
        level: MissingPageTableLevel,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        process_ptr: RwLockProcessPtr,
        container_ptr: RwLockContainerPtr,
        cpu_id: CpuId,
        pagetable_ptr: RwLockPageTableRoot,
        va: VAddr,
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
            old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(self).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            thread_effective_quota_4k(
                old(self).thread_map.spec_index(thread_ptr),
            ) >= 1,
            old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                <= spec_va2index(va).0 < 512,
            spec_va2index(va).1 < 512,
            spec_va2index(va).2 < 512,
            match level {
                MissingPageTableLevel::L4 =>
                    old(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l4(spec_va2index(va).0) is None,
                MissingPageTableLevel::L3 => {
                    &&& old(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l4(spec_va2index(va).0) is Some
                    &&& old(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l3(
                            spec_va2index(va).0, spec_va2index(va).1,
                        ) is None
                    &&& old(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_1g_l3(
                            spec_va2index(va).0, spec_va2index(va).1,
                        ) is None
                },
                MissingPageTableLevel::L2 => {
                    &&& old(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l3(
                            spec_va2index(va).0, spec_va2index(va).1,
                        ) is Some
                    &&& old(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(
                            spec_va2index(va).0,
                            spec_va2index(va).1,
                            spec_va2index(va).2,
                        ) is None
                    &&& old(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_2m_l2(
                            spec_va2index(va).0,
                            spec_va2index(va).1,
                            spec_va2index(va).2,
                        ) is None
                },
            },
            mmap_4k_no_page_locks(old(lctx)),
            page_objects_unlocked(old(self).page_array, old(lctx).thread_id()),
        ensures
            mmap_4k_held_context(
                final(self), final(lctx), alloc_ptr_4k, thread_ptr, process_ptr,
                container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                pagetable_lock_perm,
            ),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
            mmap_4k_no_page_locks(final(lctx)),
            page_objects_unlocked(final(self).page_array, final(lctx).thread_id()),
            final(lctx).lock_id_set() == old(lctx).lock_id_set(),
            final(lctx).stable_lock_id_set() == old(lctx).stable_lock_id_set(),
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
            final(self).pagetable_map.spec_index(pagetable_ptr).view().wf(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end,
            final(self).pagetable_map.spec_index(pagetable_ptr).view().user_view()
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().user_view(),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger final(self).pagetable_map.spec_index(pagetable_ptr)
                    .view().spec_resolve_mapping_l2(l4i, l3i, l2i)]
                old(self).pagetable_map.spec_index(pagetable_ptr).view()
                    .kernel_l4_end <= l4i < 512
                    && 0 <= l3i < 512
                    && 0 <= l2i < 512
                    && old(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                ==> final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(l4i, l3i, l2i)
                    == old(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(l4i, l3i, l2i),
            match level {
                MissingPageTableLevel::L4 => {
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l4(spec_va2index(va).0) is Some
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l3(
                            spec_va2index(va).0, spec_va2index(va).1,
                        ) is None
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_1g_l3(
                            spec_va2index(va).0, spec_va2index(va).1,
                        ) is None
                },
                MissingPageTableLevel::L3 => {
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l3(
                            spec_va2index(va).0, spec_va2index(va).1,
                        ) is Some
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(
                            spec_va2index(va).0,
                            spec_va2index(va).1,
                            spec_va2index(va).2,
                        ) is None
                    &&& final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_2m_l2(
                            spec_va2index(va).0,
                            spec_va2index(va).1,
                            spec_va2index(va).2,
                        ) is None
                },
                MissingPageTableLevel::L2 =>
                    final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(
                            spec_va2index(va).0,
                            spec_va2index(va).1,
                            spec_va2index(va).2,
                        ) is Some,
            },
    {
        let (page_ptr, Tracked(page_lock_perm)) = self.stage_mmap_4k_page(
            alloc_ptr_4k,
            thread_ptr,
            process_ptr,
            container_ptr,
            cpu_id,
            pagetable_ptr,
            Tracked(&mut *lctx),
            Tracked(&mut *steps),
            Tracked(thread_lock_perm),
            Tracked(pagetable_lock_perm),
        );
        self.install_staged_4k_page_table_page(
            level,
            page_ptr,
            thread_ptr,
            pagetable_ptr,
            va,
            Tracked(&mut *lctx),
            Tracked(&page_lock_perm),
            Tracked(thread_lock_perm),
            Tracked(pagetable_lock_perm),
        );
        proof {
            assert(page_objects_unlocked_except(
                self.page_array, lctx.thread_id(),
                page_ptr2page_index(page_ptr),
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
            assert(
                page_objects_unlocked(self.page_array, lctx.thread_id())
                && mmap_4k_other_objects_unlocked(
                    self, lctx.thread_id(), cpu_id, container_ptr,
                    process_ptr, thread_ptr, pagetable_ptr,
                )
            ) by {
                reveal(no_new_locks_by_thread);
            };
            assert(self.allocator_4k_map.dom().contains(alloc_ptr_4k)) by {
                reveal(container_allocator_wf);
            };
            assert(self.pagetable_map.spec_index(pagetable_ptr).view().wf()) by {
                reveal(pagetable_perms_wf);
            };
        }
    }
}

} // verus!
