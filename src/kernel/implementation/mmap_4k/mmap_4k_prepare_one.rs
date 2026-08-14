use vstd::prelude::*;

use crate::*;
use super::mmap_4k_context::{mmap_4k_held_context, mmap_4k_no_page_locks};
use super::mmap_4k_create_entry_install::MissingPageTableLevel;

verus! {

impl KernelK {
    /// Prepare the complete L4/L3/L2 walk for one empty 4K address.
    ///
    /// At most three directory pages are consumed.  Every directory store is
    /// followed by a kernel boundary, but directory topology is outside
    /// `PageTableU`, so no user step is appended.
    pub(super) fn prepare_one_mmap_4k_path(
        &mut self,
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
            old(self).container_map.spec_index(container_ptr).being_killed() == false,
            old(self).process_map.spec_index(process_ptr).being_killed() == false,
            old(self).process_map.spec_index(process_ptr).view().pagetable
                == pagetable_ptr,
            old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(self).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            old(self).thread_map.spec_index(thread_ptr).view().quota_4k >= 3,
            thread_effective_quota_4k(
                old(self).thread_map.spec_index(thread_ptr),
            ) >= 3,
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
            old(self).thread_map.spec_index(thread_ptr).view().quota_4k - 3
                <= final(self).thread_map.spec_index(thread_ptr).view().quota_4k,
            final(self).thread_map.spec_index(thread_ptr).view().quota_4k
                <= old(self).thread_map.spec_index(thread_ptr).view().quota_4k,
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
                    .kernel_l4_end <= l4i && pei_valid(l4i)
                    && pei_valid(l3i)
                    && pei_valid(l2i)
                    && old(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                ==> final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(l4i, l3i, l2i)
                    == old(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(l4i, l3i, l2i),
            final(self).pagetable_map.spec_index(pagetable_ptr).view()
                .spec_4k_entry_useable(
                    spec_va2index(va).0,
                    spec_va2index(va).1,
                    spec_va2index(va).2,
                    spec_va2index(va).3,
                ),
            final(self).pagetable_map.spec_index(pagetable_ptr).view()
                .spec_resolve_mapping_l2(
                    spec_va2index(va).0,
                    spec_va2index(va).1,
                    spec_va2index(va).2,
                ) is Some,
    {
        proof {
            assert(self.pagetable_map.perms_wf()
                && self.pagetable_map.spec_index(pagetable_ptr).is_init()) by {
                reveal(pagetable_perms_wf);
                reveal(pagetables_inv);
            };
        }
        let indices = va2index(va);
        let error_code;
        {
            let pagetable = self.pagetable_map.borrow(
                pagetable_ptr,
                Tracked(pagetable_lock_perm),
            );
            let (_, code, _) = pagetable.resolve_mapping_4k_l1(
                indices.0, indices.1, indices.2, indices.3,
            );
            error_code = code;
        }

        match error_code {
            PageTableErrorCode::L4EntryNotExist => {
                self.install_one_mmap_4k_directory_page(
                    MissingPageTableLevel::L4, alloc_ptr_4k, thread_ptr,
                    process_ptr, container_ptr, cpu_id, pagetable_ptr, va,
                    Tracked(&mut *lctx), Tracked(&mut *steps),
                    Tracked(thread_lock_perm), Tracked(pagetable_lock_perm),
                );
                self.install_one_mmap_4k_directory_page(
                    MissingPageTableLevel::L3, alloc_ptr_4k, thread_ptr,
                    process_ptr, container_ptr, cpu_id, pagetable_ptr, va,
                    Tracked(&mut *lctx), Tracked(&mut *steps),
                    Tracked(thread_lock_perm), Tracked(pagetable_lock_perm),
                );
                self.install_one_mmap_4k_directory_page(
                    MissingPageTableLevel::L2, alloc_ptr_4k, thread_ptr,
                    process_ptr, container_ptr, cpu_id, pagetable_ptr, va,
                    Tracked(&mut *lctx), Tracked(&mut *steps),
                    Tracked(thread_lock_perm), Tracked(pagetable_lock_perm),
                );
            },
            PageTableErrorCode::L3EntryNotExist => {
                self.install_one_mmap_4k_directory_page(
                    MissingPageTableLevel::L3, alloc_ptr_4k, thread_ptr,
                    process_ptr, container_ptr, cpu_id, pagetable_ptr, va,
                    Tracked(&mut *lctx), Tracked(&mut *steps),
                    Tracked(thread_lock_perm), Tracked(pagetable_lock_perm),
                );
                self.install_one_mmap_4k_directory_page(
                    MissingPageTableLevel::L2, alloc_ptr_4k, thread_ptr,
                    process_ptr, container_ptr, cpu_id, pagetable_ptr, va,
                    Tracked(&mut *lctx), Tracked(&mut *steps),
                    Tracked(thread_lock_perm), Tracked(pagetable_lock_perm),
                );
            },
            PageTableErrorCode::L2EntryNotExist => {
                self.install_one_mmap_4k_directory_page(
                    MissingPageTableLevel::L2, alloc_ptr_4k, thread_ptr,
                    process_ptr, container_ptr, cpu_id, pagetable_ptr, va,
                    Tracked(&mut *lctx), Tracked(&mut *steps),
                    Tracked(thread_lock_perm), Tracked(pagetable_lock_perm),
                );
            },
            PageTableErrorCode::L1EntryNotExist
            | PageTableErrorCode::NoError
            | PageTableErrorCode::EntryTakenBy4k
            | PageTableErrorCode::EntryTakenBy2m
            | PageTableErrorCode::EntryTakenBy1g => {},
        }

        proof {
            assert(self.pagetable_map.spec_index(pagetable_ptr).view()
                .spec_4k_entry_useable(
                    spec_va2index(va).0,
                    spec_va2index(va).1,
                    spec_va2index(va).2,
                    spec_va2index(va).3,
                )) by {
                reveal(PageTable::wf_mapping_4k);
            };
        }
    }
}

} // verus!
