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
        #![trigger pagetable.mapping_4k().dom().contains(range.view().spec_index(i))]
        first <= i < range.len
        ==> !pagetable.mapping_4k().dom().contains(range.view().spec_index(i))
}

/// Every VA in the range already has the L1 table needed by a 4K leaf.
pub open spec fn mmap_4k_leaf_range_mapped_prefix(
    pagetable: PageTable<PT_TYPE>,
    range: &VaRange4K,
    upper: int,
) -> bool {
    forall|i: int|
        #![trigger pagetable.mapping_4k().dom().contains(range.view().spec_index(i))]
        #![trigger pagetable.mapping_4k().spec_index(range.view().spec_index(i))]
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
    /// A resolved L1 entry is krnl-present by definition; architectural
    /// present is stated separately by the range postcondition.
    pub(super) fn mmap_4k_map_leaf_range(
        krnl: &mut KernelK,
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
            mmap_4k_held_context(old(krnl), old(lctx), alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, thread_lock_perm, pagetable_lock_perm),
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
            mmap_4k_allocation_ready(old(krnl), old(lctx)),
            mmap_4k_lock_scope(old(krnl), old(lctx), cpu_id, container_ptr, process_ptr, thread_ptr, pagetable_ptr),
            old(krnl).ctn_mp.spec_index(container_ptr).locked_by_thread(old(lctx).thread_id()),
            old(krnl).prc_mp.spec_index(process_ptr).locked_by_thread(old(lctx).thread_id()),
            range.wf(),
            range.len > 0,
            old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            range.len <= usize::MAX / 4usize,
            old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k >= 4 * range.len,
            old(krnl).pt_mp.spec_index(pagetable_ptr).view().wf(),
            old(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(range.start),
            old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_mapping_4k_va_range_empty(range.start, range.view().spec_index((range.len - 1) as int)),
            old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_mapping_4k_va_range_buildable(range),
        ensures
            mmap_4k_held_context(final(krnl), final(lctx), alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, thread_lock_perm, pagetable_lock_perm),
            final(steps).steps.len() == old(steps).steps.len() + range.len,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
            mmap_4k_allocation_ready(final(krnl), final(lctx)),
            mmap_4k_lock_scope(final(krnl), final(lctx), cpu_id, container_ptr, process_ptr, thread_ptr, pagetable_ptr),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            final(krnl).thr_mp.spec_index(thread_ptr).view().state == old(krnl).thr_mp.spec_index(thread_ptr).view().state,
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k <= old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k - range.len,
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k >= old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k - 4 * range.len,
            final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
            final(krnl).ctn_mp.spec_index(container_ptr) == old(krnl).ctn_mp.spec_index(container_ptr),
            final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_2m() == old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_2m(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_1g() == old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_1g(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end,
            mmap_4k_leaf_range_mapped_prefix(final(krnl).pt_mp.spec_index(pagetable_ptr).view(), range, range.len as int),
    {
        let range_start = range.start;
        proof {
            assert({
                &&& krnl.pt_mp.spec_index(pagetable_ptr).view()
                    .wf_mapping_1g()
                &&& krnl.pt_mp.spec_index(pagetable_ptr).view()
                    .wf_mapping_2m()
                &&& krnl.pt_mp.spec_index(pagetable_ptr).view()
                    .wf_mapping_4k()
            }) by { reveal(pagetable_perms_wf); };
            assert(mmap_4k_leaf_range_empty_from(krnl.pt_mp.spec_index(pagetable_ptr).view(), range, 0)) by {
                reveal(PageTable::spec_mapping_4k_va_range_empty);
                range.va_range_lemma();
            };
        }
        let mut i: usize = 0;
        while i < range.len
            invariant
                mmap_4k_held_context(krnl, &*lctx, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, thread_lock_perm, pagetable_lock_perm),
                steps.snap_shot == kernel_k_to_kernel_u(*krnl),
                mmap_4k_allocation_ready(krnl, &*lctx),
                mmap_4k_lock_scope(krnl, &*lctx, cpu_id, container_ptr, process_ptr, thread_ptr, pagetable_ptr),
                range.wf(),
                range.len > 0,
                range_start == range.start,
                0 <= i <= range.len,
                steps.steps.len() == old(steps).steps.len() + i,
                typed_lock_maps_unchanged(old(lctx), lctx),
                krnl.ctn_mp.spec_index(container_ptr)
                    .locked_by_thread(lctx.thread_id()),
                krnl.prc_mp.spec_index(process_ptr)
                    .locked_by_thread(lctx.thread_id()),
                old(krnl).thr_mp.dom().contains(thread_ptr),
                old(krnl).prc_mp.dom().contains(process_ptr),
                old(krnl).ctn_mp.dom().contains(container_ptr),
                old(krnl).pt_mp.dom().contains(pagetable_ptr),
                old(krnl).pt_mp.spec_index(pagetable_ptr).view().wf(),
                krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
                krnl.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
                krnl.thr_mp.spec_index(thread_ptr).view().state == old(krnl).thr_mp.spec_index(thread_ptr).view().state,
                old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k >= 4 * range.len,
                krnl.thr_mp.spec_index(thread_ptr).view().quota_4k >= 4 * (range.len - i),
                krnl.thr_mp.spec_index(thread_ptr).view().quota_4k >= old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k - 4 * i,
                krnl.thr_mp.spec_index(thread_ptr).view().quota_4k <= old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k - i,
                krnl.prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
                krnl.ctn_mp.spec_index(container_ptr) == old(krnl).ctn_mp.spec_index(container_ptr),
                krnl.cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
                krnl.pt_mp.spec_index(pagetable_ptr).view().mapping_2m() == old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_2m(),
                krnl.pt_mp.spec_index(pagetable_ptr).view().mapping_1g() == old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_1g(),
                krnl.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end,
                krnl.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(range.start),
                krnl.pt_mp.spec_index(pagetable_ptr).view().wf(),
                old(krnl).pt_mp.spec_index(pagetable_ptr).view()
                    .spec_mapping_4k_va_range_buildable(range),
                old(krnl).pt_mp.spec_index(pagetable_ptr).view()
                    .wf_mapping_1g(),
                old(krnl).pt_mp.spec_index(pagetable_ptr).view()
                    .wf_mapping_2m(),
                old(krnl).pt_mp.spec_index(pagetable_ptr).view()
                    .wf_mapping_4k(),
                mmap_4k_leaf_range_mapped_prefix(krnl.pt_mp.spec_index(pagetable_ptr).view(), range, i as int),
                mmap_4k_leaf_range_empty_from(krnl.pt_mp.spec_index(pagetable_ptr).view(), range, i as int),
            decreases range.len - i,
        {
            let current_va = range.index(i);
            proof {
                assert({
                    &&& spec_va_4k_valid(range_start)
                    &&& spec_va_4k_valid(current_va)
                    &&& range_start <= current_va
                    &&& va_4k_valid(current_va)
                }) by { range.va_range_lemma(); };
                assert(spec_v2l4index(range_start) <= spec_v2l4index(current_va)) by (bit_vector)
                    requires
                        spec_va_4k_valid(range_start),
                        spec_va_4k_valid(current_va),
                        range_start <= current_va,
                ;
                assert(krnl.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(current_va)) by { range.va_range_lemma(); };
                assert({
                    &&& pei_valid(spec_v2l4index(current_va))
                    &&& pei_valid(spec_v2l3index(current_va))
                    &&& pei_valid(spec_v2l2index(current_va))
                    &&& pei_valid(spec_v2l1index(current_va))
                }) by { spec_va_4k_valid_imply_indices_valid(); };
                assert(old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_4k_entry_useable(spec_v2l4index(current_va), spec_v2l3index(current_va), spec_v2l2index(current_va), spec_v2l1index(current_va))) by {
                    range.va_range_lemma();
                    seq_index_lemma::<VAddr>();
                    assert(old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_4k_l1(spec_va2index(range.view().spec_index(i as int)).0, spec_va2index(range.view().spec_index(i as int)).1, spec_va2index(range.view().spec_index(i as int)).2, spec_va2index(range.view().spec_index(i as int)).3) is None) by { seq_index_lemma::<VAddr>(); };
                };
                assert({
                    &&& krnl.pt_mp.spec_index(pagetable_ptr).view()
                        .wf_mapping_1g()
                    &&& krnl.pt_mp.spec_index(pagetable_ptr).view()
                        .wf_mapping_2m()
                    &&& krnl.pt_mp.spec_index(pagetable_ptr).view()
                        .wf_mapping_4k()
                }) by { reveal(pagetable_perms_wf); };
                assert({
                    &&& krnl.pt_mp.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_1g_l3(spec_v2l4index(current_va), spec_v2l3index(current_va)) is None
                    &&& krnl.pt_mp.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_2m_l2(spec_v2l4index(current_va), spec_v2l3index(current_va), spec_v2l2index(current_va)) is None
                }) by { reveal(PageTable::wf_mapping_1g); reveal(PageTable::wf_mapping_2m); };
                assert({
                    &&& !krnl.pt_mp.spec_index(pagetable_ptr).view()
                        .mapping_4k().dom().contains(current_va)
                    &&& krnl.pt_mp.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_4k_l1(spec_v2l4index(current_va), spec_v2l3index(current_va), spec_v2l2index(current_va), spec_v2l1index(current_va)) is None
                }) by {
                    range.va_range_lemma();
                    seq_index_lemma::<VAddr>();
                    reveal(PageTable::wf_mapping_4k);
                    spec_va_4k_index_roundtrip();
                };
            }
            mmap_4k_build_one_structure(krnl, current_va, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, 1 + 4 * (range.len - i - 1), Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm));
            proof {
                assert(thread_effective_quota_4k(krnl.thr_mp.spec_index(thread_ptr)) >= 1) by { reveal(thread_perms_wf); };
            }
            map_one_mmap_4k_page(krnl, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, current_va, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm));
            proof {
                assert(mmap_4k_leaf_range_mapped_prefix(krnl.pt_mp.spec_index(pagetable_ptr).view(), range, (i + 1) as int)) by {
                    assert(krnl.pt_mp.spec_index(pagetable_ptr).view().wf_mapping_4k()) by { reveal(pagetable_perms_wf); };
                    reveal(PageTable::wf_mapping_4k);
                    seq_index_lemma::<VAddr>();
                    range.va_range_lemma();
                };
            }
            i = i + 1;
        }
    }

} // verus!
