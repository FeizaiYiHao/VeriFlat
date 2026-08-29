use vstd::prelude::*;
use crate::*;
use super::mmap_4k_map_one_leaf::map_one_mmap_4k_page;
use super::syscall_mmap_4k_spec::mmap_4k_lock_scope;

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

    /// Build each target path immediately before publishing its data page.
    /// A resolved L1 entry is kernel-present by definition; architectural
    /// present is stated separately by the range postcondition.
    pub(super) fn mmap_4k_map_leaf_range(
        kernel: &mut KernelK,
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
                old(kernel), old(lctx), alloc_ptr_4k, thread_ptr, process_ptr,
                container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                pagetable_lock_perm,
            ),
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
            mmap_4k_allocation_ready(old(kernel), old(lctx)),
            mmap_4k_lock_scope(
                old(kernel), old(lctx), cpu_id, container_ptr, process_ptr,
                thread_ptr, pagetable_ptr,
            ),
            old(kernel).container_map.spec_index(container_ptr)
                .locked_by_thread(old(lctx).thread_id()),
            old(kernel).process_map.spec_index(process_ptr)
                .locked_by_thread(old(lctx).thread_id()),
            old(lctx).lock_entry_contains(
                old(kernel).container_map.lock_id_by_key(container_ptr),
                KernelObjId::Container(container_ptr),
            ),
            old(lctx).lock_entry_contains(
                old(kernel).process_map.lock_id_by_key(process_ptr),
                KernelObjId::Process(process_ptr),
            ),
            range.wf(),
            range.len > 0,
            old(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(kernel).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            range.len <= usize::MAX / 4usize,
            old(kernel).thread_map.spec_index(thread_ptr).view().quota_4k
                >= 4 * range.len,
            old(kernel).pagetable_map.spec_index(pagetable_ptr).view().wf(),
            old(kernel).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                <= spec_v2l4index(range.start),
            old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                .spec_mapping_4k_va_range_empty(
                    range.start,
                    range.view().spec_index((range.len - 1) as int),
                ),
            old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                .spec_mapping_4k_va_range_buildable(range),
        ensures
            mmap_4k_held_context(
                final(kernel), final(lctx), alloc_ptr_4k, thread_ptr, process_ptr,
                container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                pagetable_lock_perm,
            ),
            final(steps).steps.len() == old(steps).steps.len() + range.len,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
            mmap_4k_allocation_ready(final(kernel), final(lctx)),
            mmap_4k_lock_scope(
                final(kernel), final(lctx), cpu_id, container_ptr, process_ptr,
                thread_ptr, pagetable_ptr,
            ),
            final(lctx).lock_id_set() == old(lctx).lock_id_set(),
            final(lctx).lock_entry_contains(
                final(kernel).container_map.lock_id_by_key(container_ptr),
                KernelObjId::Container(container_ptr),
            ),
            final(lctx).lock_entry_contains(
                final(kernel).process_map.lock_id_by_key(process_ptr),
                KernelObjId::Process(process_ptr),
            ),
            final(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            final(kernel).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            final(kernel).thread_map.spec_index(thread_ptr).view().quota_4k
                <= old(kernel).thread_map.spec_index(thread_ptr).view().quota_4k
                    - range.len,
            final(kernel).thread_map.spec_index(thread_ptr).view().quota_4k
                >= old(kernel).thread_map.spec_index(thread_ptr).view().quota_4k
                    - 4 * range.len,
            final(kernel).process_map.spec_index(process_ptr)
                == old(kernel).process_map.spec_index(process_ptr),
            final(kernel).container_map.spec_index(container_ptr)
                == old(kernel).container_map.spec_index(container_ptr),
            final(kernel).cpu_array.spec_index(cpu_id).view()
                == old(kernel).cpu_array.spec_index(cpu_id).view(),
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
                == old(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
                == old(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                == old(kernel).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end,
            mmap_4k_leaf_range_mapped_prefix(
                final(kernel).pagetable_map.spec_index(pagetable_ptr).view(),
                range,
                range.len as int,
            ),
    {
        let range_start = range.start;
        proof {
            assert({
                &&& kernel.pagetable_map.spec_index(pagetable_ptr).view()
                    .wf_mapping_1g()
                &&& kernel.pagetable_map.spec_index(pagetable_ptr).view()
                    .wf_mapping_2m()
                &&& kernel.pagetable_map.spec_index(pagetable_ptr).view()
                    .wf_mapping_4k()
            }) by {
                reveal(pagetable_perms_wf);
            };
            assert(mmap_4k_leaf_range_empty_from(
                kernel.pagetable_map.spec_index(pagetable_ptr).view(), range, 0,
            )) by {
                reveal(PageTable::spec_mapping_4k_va_range_empty);
                range.va_range_lemma();
            };
        }
        let mut i: usize = 0;
        while i < range.len
            invariant
                mmap_4k_held_context(
                    kernel, &*lctx, alloc_ptr_4k, thread_ptr, process_ptr,
                    container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                    pagetable_lock_perm,
                ),
                steps.snap_shot == kernel_k_to_kernel_u(*kernel),
                mmap_4k_allocation_ready(kernel, &*lctx),
                mmap_4k_lock_scope(
                    kernel, &*lctx, cpu_id, container_ptr, process_ptr,
                    thread_ptr, pagetable_ptr,
                ),
                range.wf(),
                range.len > 0,
                range_start == range.start,
                0 <= i <= range.len,
                steps.steps.len() == old(steps).steps.len() + i,
                lctx.lock_id_set() == old(lctx).lock_id_set(),
                kernel.container_map.spec_index(container_ptr)
                    .locked_by_thread(lctx.thread_id()),
                kernel.process_map.spec_index(process_ptr)
                    .locked_by_thread(lctx.thread_id()),
                lctx.lock_entry_contains(
                    kernel.container_map.lock_id_by_key(container_ptr),
                    KernelObjId::Container(container_ptr),
                ),
                lctx.lock_entry_contains(
                    kernel.process_map.lock_id_by_key(process_ptr),
                    KernelObjId::Process(process_ptr),
                ),
                old(kernel).thread_map.dom().contains(thread_ptr),
                old(kernel).process_map.dom().contains(process_ptr),
                old(kernel).container_map.dom().contains(container_ptr),
                old(kernel).pagetable_map.dom().contains(pagetable_ptr),
                old(kernel).pagetable_map.spec_index(pagetable_ptr).view().wf(),
                kernel.thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
                kernel.thread_map.spec_index(thread_ptr).view()
                    .free_quota_pending_clean(),
                old(kernel).thread_map.spec_index(thread_ptr).view().quota_4k
                    >= 4 * range.len,
                kernel.thread_map.spec_index(thread_ptr).view().quota_4k
                    >= 4 * (range.len - i),
                kernel.thread_map.spec_index(thread_ptr).view().quota_4k
                    >= old(kernel).thread_map.spec_index(thread_ptr).view().quota_4k
                        - 4 * i,
                kernel.thread_map.spec_index(thread_ptr).view().quota_4k
                    <= old(kernel).thread_map.spec_index(thread_ptr).view().quota_4k - i,
                kernel.process_map.spec_index(process_ptr)
                    == old(kernel).process_map.spec_index(process_ptr),
                kernel.container_map.spec_index(container_ptr)
                    == old(kernel).container_map.spec_index(container_ptr),
                kernel.cpu_array.spec_index(cpu_id).view()
                    == old(kernel).cpu_array.spec_index(cpu_id).view(),
                kernel.pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
                    == old(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
                kernel.pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
                    == old(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
                kernel.pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                    == old(kernel).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end,
                kernel.pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                    <= spec_v2l4index(range.start),
                kernel.pagetable_map.spec_index(pagetable_ptr).view().wf(),
                old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                    .spec_mapping_4k_va_range_buildable(range),
                old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                    .wf_mapping_1g(),
                old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                    .wf_mapping_2m(),
                old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                    .wf_mapping_4k(),
                mmap_4k_leaf_range_mapped_prefix(
                    kernel.pagetable_map.spec_index(pagetable_ptr).view(),
                    range,
                    i as int,
                ),
                mmap_4k_leaf_range_empty_from(
                    kernel.pagetable_map.spec_index(pagetable_ptr).view(),
                    range,
                    i as int,
                ),
            decreases range.len - i,
        {
            let current_va = range.index(i);
            proof {
                assert({
                    &&& spec_va_4k_valid(range_start)
                    &&& spec_va_4k_valid(current_va)
                    &&& range_start <= current_va
                    &&& va_4k_valid(current_va)
                }) by {
                    range.va_range_lemma();
                };
                assert(spec_v2l4index(range_start)
                    <= spec_v2l4index(current_va)) by (bit_vector)
                    requires
                        spec_va_4k_valid(range_start),
                        spec_va_4k_valid(current_va),
                        range_start <= current_va,
                ;
                assert(kernel.pagetable_map.spec_index(pagetable_ptr).view()
                    .kernel_l4_end <= spec_v2l4index(current_va)) by {
                    range.va_range_lemma();
                };
                assert({
                    &&& pei_valid(spec_v2l4index(current_va))
                    &&& pei_valid(spec_v2l3index(current_va))
                    &&& pei_valid(spec_v2l2index(current_va))
                    &&& pei_valid(spec_v2l1index(current_va))
                }) by {
                    spec_va_4k_valid_imply_indices_valid();
                };
                assert(old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                    .spec_4k_entry_useable(
                        spec_v2l4index(current_va), spec_v2l3index(current_va),
                        spec_v2l2index(current_va), spec_v2l1index(current_va),
                    )) by {
                    range.va_range_lemma();
                    seq_index_lemma::<VAddr>();
                    assert(old(kernel).pagetable_map.spec_index(pagetable_ptr)
                        .view().spec_resolve_mapping_4k_l1(
                            spec_va2index(range.view().spec_index(i as int)).0,
                            spec_va2index(range.view().spec_index(i as int)).1,
                            spec_va2index(range.view().spec_index(i as int)).2,
                            spec_va2index(range.view().spec_index(i as int)).3,
                        ) is None) by {
                            seq_index_lemma::<VAddr>();
                        };
                };
                assert({
                    &&& kernel.pagetable_map.spec_index(pagetable_ptr).view()
                        .wf_mapping_1g()
                    &&& kernel.pagetable_map.spec_index(pagetable_ptr).view()
                        .wf_mapping_2m()
                    &&& kernel.pagetable_map.spec_index(pagetable_ptr).view()
                        .wf_mapping_4k()
                }) by {
                    reveal(pagetable_perms_wf);
                };
                assert({
                    &&& kernel.pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_1g_l3(
                            spec_v2l4index(current_va), spec_v2l3index(current_va),
                        ) is None
                    &&& kernel.pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_2m_l2(
                            spec_v2l4index(current_va), spec_v2l3index(current_va),
                            spec_v2l2index(current_va),
                        ) is None
                }) by {
                    reveal(PageTable::wf_mapping_1g);
                    reveal(PageTable::wf_mapping_2m);
                };
                assert({
                    &&& !kernel.pagetable_map.spec_index(pagetable_ptr).view()
                        .mapping_4k().dom().contains(current_va)
                    &&& kernel.pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_4k_l1(
                            spec_v2l4index(current_va), spec_v2l3index(current_va),
                            spec_v2l2index(current_va), spec_v2l1index(current_va),
                        ) is None
                }) by {
                    range.va_range_lemma();
                    seq_index_lemma::<VAddr>();
                    reveal(PageTable::wf_mapping_4k);
                    spec_va_4k_index_roundtrip();
                };
            }
            mmap_4k_build_one_structure(kernel,
                current_va,
                alloc_ptr_4k,
                thread_ptr,
                process_ptr,
                container_ptr,
                cpu_id,
                pagetable_ptr,
                1 + 4 * (range.len - i - 1),
                Tracked(&mut *lctx),
                Tracked(&mut *steps),
                Tracked(thread_lock_perm),
                Tracked(pagetable_lock_perm),
            );
            proof {
                assert(thread_effective_quota_4k(
                    kernel.thread_map.spec_index(thread_ptr),
                ) >= 1) by {
                    reveal(thread_perms_wf);
                };
            }
            map_one_mmap_4k_page(kernel,
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
                assert(mmap_4k_leaf_range_mapped_prefix(
                    kernel.pagetable_map.spec_index(pagetable_ptr).view(),
                    range,
                    (i + 1) as int,
                )) by {
                    assert(kernel.pagetable_map.spec_index(pagetable_ptr).view()
                        .wf_mapping_4k()) by {
                        reveal(pagetable_perms_wf);
                    };
                    reveal(PageTable::wf_mapping_4k);
                    seq_index_lemma::<VAddr>();
                    range.va_range_lemma();
                };
            }
            i = i + 1;
        }
    }

} // verus!
