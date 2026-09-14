use vstd::prelude::*;
use crate::*;
use super::mmap_4k_map_one_leaf::map_one_mmap_4k_page;

verus! {
/// Every not-yet-processed VA is still absent from the 4K mapping.
pub open spec fn mmap_4k_leaf_range_empty_from(pagetable: PageTable<PT_TYPE>, range: &VaRange4K, first: int) -> bool {
    forall|i: int|
        #![trigger pagetable.mapping_4k().dom().contains(range.view().spec_index(i))]
        first <= i < range.len
        ==> !pagetable.mapping_4k().dom().contains(range.view().spec_index(i))
}

/// Every VA in the range already has the L1 table needed by a 4K leaf.
pub open spec fn mmap_4k_leaf_range_mapped_prefix(pagetable: PageTable<PT_TYPE>, range: &VaRange4K, upper: int) -> bool {
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
    pub(super) fn mmap_4k_map_leaf_range(krnl: &mut KernelK, range: &VaRange4K, alloc_ptr_4k: RwLockPageAllocatorPtr, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, cpu_id: CpuId, pagetable_ptr: RwLockPageTableRoot, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, Tracked(thread_lock_perm): Tracked<&LockPerm>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>)
        requires
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            lock_id_set_aligned(old(lctx)),
            index_valid(NUM_CPUS, cpu_id),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            old(krnl).ctn_mp.dom().contains(container_ptr),
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            old(krnl).prc_mp.dom().contains(process_ptr),
            old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
            old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
            old(krnl).thr_mp.dom().contains(thread_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
            old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
            ((old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr && old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable_ptr) || typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write)),
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            old(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
            old(krnl).pt_mp.dom().contains(pagetable_ptr),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            pagetable_lock_perm.state() is WriteLock,
            pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
            pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable_ptr,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
            old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
            old(lctx).container_lock_map().dom() =~= set![container_ptr],
            old(lctx).process_lock_map().dom() =~= set![process_ptr],
            old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
            old(lctx).endpoint_lock_map().dom().is_empty(),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).pcid_allocator_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pagetable_lock_map().dom() =~= set![pagetable_ptr],
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(lctx).container_lock_map().dom().contains(container_ptr),
            old(lctx).process_lock_map().dom().contains(process_ptr),
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
            forall|pt: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(pt)]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            final(krnl).ctn_mp.dom().contains(container_ptr),
            final(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            final(krnl).prc_mp.dom().contains(process_ptr),
            final(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
            final(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
            final(krnl).thr_mp.dom().contains(thread_ptr),
            typed_lock_map_contains_mode(final(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
            final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            final(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
            ((final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr && final(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable_ptr) || typed_lock_map_contains_mode(final(lctx).process_lock_map(), process_ptr, TypedLockMode::Write)),
            thread_lock_perm.thread_id() == final(lctx).thread_id(),
            thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            final(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
            final(krnl).pt_mp.dom().contains(pagetable_ptr),
            typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            pagetable_lock_perm.thread_id() == final(lctx).thread_id(),
            pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            final(steps).steps.len() == old(steps).steps.len() + range.len,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
            final(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
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
                &&& krnl.pt_mp.spec_index(pagetable_ptr).view().wf_mapping_1g()
                &&& krnl.pt_mp.spec_index(pagetable_ptr).view().wf_mapping_2m()
                &&& krnl.pt_mp.spec_index(pagetable_ptr).view().wf_mapping_4k()
            }) by { reveal(pagetable_perms_wf); };
            assert(mmap_4k_leaf_range_empty_from(krnl.pt_mp.spec_index(pagetable_ptr).view(), range, 0)) by {
                reveal(PageTable::spec_mapping_4k_va_range_empty);
                range.va_range_lemma();
            };
        }
        let mut i: usize = 0;
        while i < range.len
            invariant
                forall|pt: RwLockPageTableRoot| #![trigger krnl.pt_mp.spec_index(pt)]
                    old(lctx).pagetable_lock_map().dom().contains(pt)
                    && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
                    ==> pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pt, krnl.pt_mp.spec_index(pt).view()),
                lctx.cpu_id() == old(lctx).cpu_id(),
                index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
                krnl.inv(),
                lctx.kernel_view_locking_state() is Acquire,
                typed_lock_maps_aligned(krnl, &*lctx),
                lock_id_set_aligned(&*lctx),
                index_valid(NUM_CPUS, cpu_id),
                typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
                krnl.cpu_arr.spec_index(cpu_id).view().being_killed() == false,
                krnl.ctn_mp.dom().contains(container_ptr),
                krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
                krnl.prc_mp.dom().contains(process_ptr),
                krnl.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
                krnl.prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
                krnl.thr_mp.dom().contains(thread_ptr),
                typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
                krnl.thr_mp.spec_index(thread_ptr).being_killed() == false,
                krnl.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
                ((krnl.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr && krnl.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable_ptr) || typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write)),
                thread_lock_perm.state() is WriteLock,
                thread_lock_perm.thread_id() == lctx.thread_id(),
                thread_lock_perm.lock_id() == krnl.thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
                krnl.allc_4k_mp.dom().contains(alloc_ptr_4k),
                krnl.pt_mp.dom().contains(pagetable_ptr),
                typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
                pagetable_lock_perm.state() is WriteLock,
                pagetable_lock_perm.thread_id() == lctx.thread_id(),
                pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
                steps.snap_shot == kernel_k_to_kernel_u(*krnl),
                lctx.page_lock_map().dom().is_empty(),
                lctx.holds_no_allocator_locks(PageSize::SZ4k),
                lctx.held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
                lctx.cpu_lock_map().dom() =~= set![cpu_id],
                lctx.container_lock_map().dom() =~= set![container_ptr],
                lctx.process_lock_map().dom() =~= set![process_ptr],
                lctx.thread_lock_map().dom() =~= set![thread_ptr],
                lctx.endpoint_lock_map().dom().is_empty(),
                lctx.scheduler_lock_map().dom().is_empty(),
                lctx.pcid_allocator_lock_map().dom().is_empty(),
                lctx.cpu_set_lock_map().dom().is_empty(),
                lctx.pagetable_lock_map().dom() =~= set![pagetable_ptr],
                lctx.iommu_table_lock_map().dom().is_empty(),
                lctx.allocator_quota_4k_lock_map().dom().is_empty(),
                lctx.allocator_cache_4k_lock_map().dom().is_empty(),
                lctx.allocator_global_pool_4k_lock_map().dom().is_empty(),
                lctx.allocator_quota_2m_lock_map().dom().is_empty(),
                lctx.allocator_cache_2m_lock_map().dom().is_empty(),
                lctx.allocator_global_pool_2m_lock_map().dom().is_empty(),
                lctx.allocator_quota_1g_lock_map().dom().is_empty(),
                lctx.allocator_cache_1g_lock_map().dom().is_empty(),
                lctx.allocator_global_pool_1g_lock_map().dom().is_empty(),
                lctx.pcid_needflush_lock_map().dom().is_empty(),
                range.wf(),
                range.len > 0,
                range_start == range.start,
                0 <= i <= range.len,
                steps.steps.len() == old(steps).steps.len() + i,
                typed_lock_maps_unchanged(old(lctx), lctx),
                lctx.container_lock_map().dom().contains(container_ptr),
                lctx.process_lock_map().dom().contains(process_ptr),
                old(krnl).thr_mp.dom().contains(thread_ptr),
                old(krnl).prc_mp.dom().contains(process_ptr),
                old(krnl).ctn_mp.dom().contains(container_ptr),
                old(krnl).pt_mp.dom().contains(pagetable_ptr),
                old(krnl).pt_mp.spec_index(pagetable_ptr).view().wf(),
                krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
                krnl.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
                krnl.thr_mp.spec_index(thread_ptr).view().state == old(krnl).thr_mp.spec_index(thread_ptr).view().state,
                krnl.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable_ptr,
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
                old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_mapping_4k_va_range_buildable(range),
                old(krnl).pt_mp.spec_index(pagetable_ptr).view().wf_mapping_1g(),
                old(krnl).pt_mp.spec_index(pagetable_ptr).view().wf_mapping_2m(),
                old(krnl).pt_mp.spec_index(pagetable_ptr).view().wf_mapping_4k(),
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
                    &&& krnl.pt_mp.spec_index(pagetable_ptr).view().wf_mapping_1g()
                    &&& krnl.pt_mp.spec_index(pagetable_ptr).view().wf_mapping_2m()
                    &&& krnl.pt_mp.spec_index(pagetable_ptr).view().wf_mapping_4k()
                }) by { reveal(pagetable_perms_wf); };
                assert({
                    &&& krnl.pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_1g_l3(spec_v2l4index(current_va), spec_v2l3index(current_va)) is None
                    &&& krnl.pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_2m_l2(spec_v2l4index(current_va), spec_v2l3index(current_va), spec_v2l2index(current_va)) is None
                }) by { reveal(PageTable::wf_mapping_1g); reveal(PageTable::wf_mapping_2m); };
                assert({
                    &&& !krnl.pt_mp.spec_index(pagetable_ptr).view().mapping_4k().dom().contains(current_va)
                    &&& krnl.pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_4k_l1(spec_v2l4index(current_va), spec_v2l3index(current_va), spec_v2l2index(current_va), spec_v2l1index(current_va)) is None
                }) by {
                    range.va_range_lemma();
                    seq_index_lemma::<VAddr>();
                    reveal(PageTable::wf_mapping_4k);
                    spec_va_4k_index_roundtrip();
                };
            }
            mmap_4k_build_one_structure(krnl, current_va, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm));
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
