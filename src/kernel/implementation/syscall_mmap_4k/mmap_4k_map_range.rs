use vstd::prelude::*;
use crate::*;
use super::mmap_4k_context::{
    mmap_4k_held_context,
    mmap_4k_allocation_ready,
};
use super::mmap_4k_build_structure::Mmap4kStructureBuild;

verus! {

/// Every not-yet-processed VA is still absent from the 4K mapping.
pub open spec fn mmap_4k_leaf_range_empty_from(
    pagetable: PageTable<PT_TYPE>,
    range: &VaRange4K,
    first: int,
) -> bool {
    forall|i: int|
        #![trigger pagetable.mapping_4k().dom().contains(
            range.view().spec_index(i),
        )]
        first <= i < range.len
        ==> !pagetable.mapping_4k().dom().contains(
            range.view().spec_index(i),
        )
}

/// Every VA in the range already has the L1 table needed by a 4K leaf.
pub open spec fn mmap_4k_leaf_range_prepared(
    pagetable: PageTable<PT_TYPE>,
    range: &VaRange4K,
) -> bool {
    forall|i: int|
        #![trigger pagetable.spec_resolve_mapping_l2(
            spec_va2index(range.view().spec_index(i)).0,
            spec_va2index(range.view().spec_index(i)).1,
            spec_va2index(range.view().spec_index(i)).2,
        )]
        0 <= i < range.len
        ==> {
            let indices = spec_va2index(range.view().spec_index(i));
            &&& pagetable.kernel_l4_end <= indices.0
            &&& pei_valid(indices.0)
            &&& pei_valid(indices.1)
            &&& pei_valid(indices.2)
            &&& pei_valid(indices.3)
            &&& pagetable.spec_resolve_mapping_l2(
                indices.0, indices.1, indices.2,
            ) is Some
        }
}

/// Abstract permissions accumulated by the mutating loop.
pub open spec fn mmap_4k_leaf_range_mapped_prefix(
    pagetable: PageTable<PT_TYPE>,
    range: &VaRange4K,
    upper: int,
) -> bool {
    forall|i: int|
        #![trigger pagetable.mapping_4k().dom().contains(
            range.view().spec_index(i),
        )]
        #![trigger pagetable.mapping_4k().spec_index(
            range.view().spec_index(i),
        )]
        0 <= i < upper
        ==> {
            let va = range.view().spec_index(i);
            &&& pagetable.mapping_4k().dom().contains(va)
            &&& pagetable.mapping_4k().spec_index(va).present
            &&& pagetable.mapping_4k().spec_index(va).write
            &&& !pagetable.mapping_4k().spec_index(va).execute_disable
        }
}

/// Physical publication for the completed range. A resolved L1 entry is
/// kernel-present by definition; architectural present is stated separately.
pub open spec fn mmap_4k_leaf_range_pte_present(
    pagetable: PageTable<PT_TYPE>,
    range: &VaRange4K,
) -> bool {
    forall|i: int|
        #![trigger pagetable.mapping_4k().dom().contains(
            range.view().spec_index(i),
        )]
        #![trigger pagetable.spec_resolve_mapping_l2(
            spec_va2index(range.view().spec_index(i)).0,
            spec_va2index(range.view().spec_index(i)).1,
            spec_va2index(range.view().spec_index(i)).2,
        )]
        #![trigger pagetable.spec_resolve_mapping_4k_l1(
            spec_va2index(range.view().spec_index(i)).0,
            spec_va2index(range.view().spec_index(i)).1,
            spec_va2index(range.view().spec_index(i)).2,
            spec_va2index(range.view().spec_index(i)).3,
        )]
        0 <= i < range.len
        ==> {
            let va = range.view().spec_index(i);
            let indices = spec_va2index(va);
            &&& pagetable.kernel_l4_end <= indices.0
            &&& pei_valid(indices.0)
            &&& pei_valid(indices.1)
            &&& pei_valid(indices.2)
            &&& pei_valid(indices.3)
            &&& pagetable.spec_resolve_mapping_l2(
                indices.0, indices.1, indices.2,
            ) is Some
            &&& pagetable.mapping_4k().dom().contains(va)
            &&& pagetable.mapping_4k().spec_index(va).present
            &&& pagetable.spec_resolve_mapping_4k_l1(
                indices.0, indices.1, indices.2, indices.3,
            ) is Some
            &&& pagetable.spec_resolve_mapping_4k_l1(
                indices.0, indices.1, indices.2, indices.3,
            )->0.perm.present
            &&& pagetable.spec_resolve_mapping_4k_l1(
                indices.0, indices.1, indices.2, indices.3,
            )->0.perm.kernel_present
        }
}

impl KernelK {
    /// Publish one data page for every VA after the three directory passes
    /// have certified the complete range structure.
    pub(super) fn mmap_4k_map_leaf_range(
        &mut self,
        range: &VaRange4K,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        process_ptr: RwLockProcessPtr,
        container_ptr: RwLockContainerPtr,
        cpu_id: CpuId,
        pagetable_ptr: RwLockPageTableRoot,
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
            mmap_4k_allocation_ready(old(self), old(lctx)),
            range.wf(),
            range.len > 0,
            old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(self).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            old(self).thread_map.spec_index(thread_ptr).view().quota_4k
                >= range.len,
            old(self).pagetable_map.spec_index(pagetable_ptr).view()
                .spec_mapping_4k_va_range_empty(
                    range.start,
                    range.view().spec_index((range.len - 1) as int),
                ),
            old(self).pagetable_map.spec_index(pagetable_ptr).view()
                .spec_va_range_structure_present(
                    range.start,
                    range.view().spec_index((range.len - 1) as int),
                ),
        ensures
            mmap_4k_held_context(
                final(self), final(lctx), alloc_ptr_4k, thread_ptr, process_ptr,
                container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                pagetable_lock_perm,
            ),
            final(steps).steps.len() == old(steps).steps.len() + range.len,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
            mmap_4k_allocation_ready(final(self), final(lctx)),
            final(lctx).lock_id_set() == old(lctx).lock_id_set(),
            final(lctx).lock_id_set() == old(lctx).lock_id_set(),
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            final(self).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            final(self).thread_map.spec_index(thread_ptr).view().quota_4k
                == old(self).thread_map.spec_index(thread_ptr).view().quota_4k
                    - range.len,
            final(self).process_map.spec_index(process_ptr)
                == old(self).process_map.spec_index(process_ptr),
            final(self).container_map.spec_index(container_ptr)
                == old(self).container_map.spec_index(container_ptr),
            final(self).cpu_array.spec_index(cpu_id).view()
                == old(self).cpu_array.spec_index(cpu_id).view(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end,
            mmap_4k_leaf_range_prepared(
                final(self).pagetable_map.spec_index(pagetable_ptr).view(),
                range,
            ),
            mmap_4k_leaf_range_mapped_prefix(
                final(self).pagetable_map.spec_index(pagetable_ptr).view(),
                range,
                range.len as int,
            ),
            mmap_4k_leaf_range_pte_present(
                final(self).pagetable_map.spec_index(pagetable_ptr).view(),
                range,
            ),
    {
        proof {
            assert(mmap_4k_leaf_range_empty_from(
                self.pagetable_map.spec_index(pagetable_ptr).view(), range, 0,
            )) by {
                reveal(PageTable::spec_mapping_4k_va_range_empty);
                range.va_range_lemma();
            };
            assert(mmap_4k_leaf_range_prepared(
                self.pagetable_map.spec_index(pagetable_ptr).view(), range,
            )) by {
                reveal(PageTable::spec_va_range_structure_present);
                range.va_range_lemma();
            };
        }
        let mut i: usize = 0;
        while i < range.len
            invariant
                mmap_4k_held_context(
                    self, &*lctx, alloc_ptr_4k, thread_ptr, process_ptr,
                    container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                    pagetable_lock_perm,
                ),
                steps.snap_shot == kernel_k_to_kernel_u(*self),
                mmap_4k_allocation_ready(self, &*lctx),
                range.wf(),
                range.len > 0,
                0 <= i <= range.len,
                steps.steps.len() == old(steps).steps.len() + i,
                lctx.lock_id_set() == old(lctx).lock_id_set(),
                lctx.lock_id_set() == old(lctx).lock_id_set(),
                old(self).thread_map.dom().contains(thread_ptr),
                old(self).process_map.dom().contains(process_ptr),
                old(self).container_map.dom().contains(container_ptr),
                old(self).pagetable_map.dom().contains(pagetable_ptr),
                self.thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
                self.thread_map.spec_index(thread_ptr).view()
                    .free_quota_pending_clean(),
                old(self).thread_map.spec_index(thread_ptr).view().quota_4k
                    >= range.len,
                self.thread_map.spec_index(thread_ptr).view().quota_4k
                    == old(self).thread_map.spec_index(thread_ptr).view().quota_4k - i,
                self.process_map.spec_index(process_ptr)
                    == old(self).process_map.spec_index(process_ptr),
                self.container_map.spec_index(container_ptr)
                    == old(self).container_map.spec_index(container_ptr),
                self.cpu_array.spec_index(cpu_id).view()
                    == old(self).cpu_array.spec_index(cpu_id).view(),
                self.pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
                    == old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
                self.pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
                    == old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
                self.pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                    == old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end,
                mmap_4k_leaf_range_prepared(
                    self.pagetable_map.spec_index(pagetable_ptr).view(), range,
                ),
                mmap_4k_leaf_range_mapped_prefix(
                    self.pagetable_map.spec_index(pagetable_ptr).view(),
                    range,
                    i as int,
                ),
                mmap_4k_leaf_range_empty_from(
                    self.pagetable_map.spec_index(pagetable_ptr).view(),
                    range,
                    i as int,
                ),
            decreases range.len - i,
        {
            let current_va = range.index(i);
            self.map_one_mmap_4k_page(
                alloc_ptr_4k,
                thread_ptr,
                process_ptr,
                container_ptr,
                cpu_id,
                pagetable_ptr,
                current_va,
                Tracked(&mut *lctx),
                Tracked(&mut *steps),
                Tracked(thread_lock_perm),
                Tracked(pagetable_lock_perm),
            );
            proof {
                assert(mmap_4k_leaf_range_prepared(
                    self.pagetable_map.spec_index(pagetable_ptr).view(), range,
                )) by {
                    spec_va_4k_valid_imply_indices_valid();
                };
                assert(mmap_4k_leaf_range_mapped_prefix(
                    self.pagetable_map.spec_index(pagetable_ptr).view(),
                    range,
                    (i + 1) as int,
                )) by {
                    reveal(PageTable::wf_mapping_4k);
                    broadcast use vstd::map::group_map_lemmas;
                    seq_index_lemma::<VAddr>();
                };
            }
            i = i + 1;
        }
        proof {
            assert(mmap_4k_leaf_range_pte_present(
                self.pagetable_map.spec_index(pagetable_ptr).view(), range,
            )) by {
                assert(self.pagetable_map.spec_index(pagetable_ptr).view()
                    .wf_mapping_4k()) by {
                    reveal(pagetable_perms_wf);
                };
                reveal(PageTable::wf_mapping_4k);
                spec_va_4k_index_roundtrip();
            };
        }
    }

    /// Compose the three directory passes with the final per-VA leaf pass.
    pub(super) fn mmap_4k_build_and_map_leaf_range(
        &mut self,
        range: &VaRange4K,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        process_ptr: RwLockProcessPtr,
        container_ptr: RwLockContainerPtr,
        cpu_id: CpuId,
        pagetable_ptr: RwLockPageTableRoot,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
        Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: Mmap4kStructureBuild)
        requires
            mmap_4k_held_context(
                old(self), old(lctx), alloc_ptr_4k, thread_ptr, process_ptr,
                container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                pagetable_lock_perm,
            ),
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
            mmap_4k_allocation_ready(old(self), old(lctx)),
            range.wf(),
            range.len > 0,
            range.len <= usize::MAX / 4usize,
            old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(self).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            old(self).thread_map.spec_index(thread_ptr).view().quota_4k
                >= 4 * range.len,
            old(self).pagetable_map.spec_index(pagetable_ptr).view().wf(),
            old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                <= spec_v2l4index(range.start),
            old(self).pagetable_map.spec_index(pagetable_ptr).view()
                .spec_mapping_4k_va_range_empty(
                    range.start,
                    range.view().spec_index((range.len - 1) as int),
                ),
        ensures
            mmap_4k_held_context(
                final(self), final(lctx), alloc_ptr_4k, thread_ptr, process_ptr,
                container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                pagetable_lock_perm,
            ),
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
            mmap_4k_allocation_ready(final(self), final(lctx)),
            final(lctx).lock_id_set() == old(lctx).lock_id_set(),
            final(lctx).lock_id_set() == old(lctx).lock_id_set(),
            final(self).cpu_array.spec_index(cpu_id).view().locking_thread()
                == old(self).cpu_array.spec_index(cpu_id).view().locking_thread(),
            final(self).cpu_array.lock_id_by_index(cpu_id)
                == old(self).cpu_array.lock_id_by_index(cpu_id),
            final(self).container_map.spec_index(container_ptr).locking_thread()
                == old(self).container_map.spec_index(container_ptr).locking_thread(),
            final(self).process_map.spec_index(process_ptr).locking_thread()
                == old(self).process_map.spec_index(process_ptr).locking_thread(),
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            final(self).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            ret is Ready ==>
                final(steps).steps.len() == old(steps).steps.len() + range.len,
            (ret is NoQuota || ret is InUse) ==>
                final(steps).steps == old(steps).steps,
            ret is Ready ==> mmap_4k_leaf_range_mapped_prefix(
                final(self).pagetable_map.spec_index(pagetable_ptr).view(),
                range,
                range.len as int,
            ),
            ret is Ready ==> mmap_4k_leaf_range_pte_present(
                final(self).pagetable_map.spec_index(pagetable_ptr).view(),
                range,
            ),
    {
        let structure = self.mmap_4k_build_structure(
            range,
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
        match structure {
            Mmap4kStructureBuild::Ready => {
                self.mmap_4k_map_leaf_range(
                    range,
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
                Mmap4kStructureBuild::Ready
            },
            Mmap4kStructureBuild::NoQuota => Mmap4kStructureBuild::NoQuota,
            Mmap4kStructureBuild::InUse => Mmap4kStructureBuild::InUse,
        }
    }
}

} // verus!
