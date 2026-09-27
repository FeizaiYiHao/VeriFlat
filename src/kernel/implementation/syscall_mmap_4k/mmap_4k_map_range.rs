use vstd::prelude::*;
use crate::*;
use super::mmap_4k_map_one_leaf::map_one_mmap_4k_page;
use super::syscall_mmap_4k_spec::mmap_4k_range_step;

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
    pub(super) fn mmap_4k_map_leaf_range(
        krnl: &mut KernelK, range: &VaRange4K, alloc_ptr_4k: RwLockPageAllocatorPtr, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr,
        container_ptr: RwLockContainerPtr, cpu_id: CpuId, pagetable_ptr: RwLockPageTableRoot, Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>, Tracked(thread_lock_perm): Tracked<&LockPerm>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
    )
        requires
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            index_valid(NUM_CPUS, cpu_id),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
            old(krnl).ctn_mp.dom().contains(container_ptr),
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            old(krnl).prc_mp.dom().contains(process_ptr),
            !old(krnl).prc_mp.spec_index(process_ptr).view().zombie,
            old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
            old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
            old(krnl).thr_mp.dom().contains(thread_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
            old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
            old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
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
            old(steps).snapshot_k() == *old(krnl),
            old(lctx).page_lock_map().dom().is_empty(),
            forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            forall|held_thread: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(held_thread)] old(lctx).thread_lock_map().dom().contains(held_thread) ==> !(old(krnl).thr_mp.spec_index(held_thread).view().state is SCHEDULED),
            old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
            old(lctx).container_lock_map().dom().is_empty(),
            old(lctx).process_lock_map().dom().is_empty(),
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
            range.wf(),
            range.len > 0,
            old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k >= 4 * range.len,
            old(krnl).pt_mp.spec_index(pagetable_ptr).view().wf(),
            old(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(range.start),
            old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_mapping_4k_va_range_empty(range.start, range.view().spec_index((range.len - 1) as int)),
            old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_mapping_4k_va_range_buildable(range),
            old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap4k { range: *range, mapped: 0, directory: Mmap4kDirectory::None }),
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
            final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
            thread_lock_perm.thread_id() == final(lctx).thread_id(),
            thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            final(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
            final(krnl).pt_mp.dom().contains(pagetable_ptr),
            typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            pagetable_lock_perm.thread_id() == final(lctx).thread_id(),
            pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            old(steps).nonlock_view().len() + range.len <= final(steps).nonlock_view().len(),
            final(steps).nonlock_view().len() <= old(steps).nonlock_view().len() + 4 * range.len,
            final(steps).nonlock_view().subrange(0, old(steps).nonlock_view().len() as int) == old(steps).nonlock_view(),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            final(steps).snapshot_k() == *final(krnl),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            final(krnl).thr_mp.spec_index(thread_ptr).view().state == old(krnl).thr_mp.spec_index(thread_ptr).view().state,
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k <= old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k - range.len,
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k >= old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k - 4 * range.len,
            final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_2m() == old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_2m(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_1g() == old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_1g(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end,
            mmap_4k_leaf_range_mapped_prefix(final(krnl).pt_mp.spec_index(pagetable_ptr).view(), range, range.len as int),
            final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap4k { range: *range, mapped: range.len, directory: Mmap4kDirectory::None }),
            old(steps).view().len() + range.len <= final(steps).view().len() <= old(steps).view().len() + 4 * range.len,
            forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
            forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==> mmap_4k_range_step(final(steps).view()[j], cpu_id, thread_ptr),
    {
        let range_start = range.start;
        proof {
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
                krnl.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
                thread_lock_perm.state() is WriteLock,
                thread_lock_perm.thread_id() == lctx.thread_id(),
                thread_lock_perm.lock_id() == krnl.thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
                krnl.allc_4k_mp.dom().contains(alloc_ptr_4k),
                krnl.pt_mp.dom().contains(pagetable_ptr),
                typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
                pagetable_lock_perm.state() is WriteLock,
                pagetable_lock_perm.thread_id() == lctx.thread_id(),
                pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
                steps.nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
                steps.snapshot_k() == *krnl,
                lctx.page_lock_map().dom().is_empty(),
                forall|held_cpu_id: CpuId| #![trigger lctx.cpu_lock_map().dom().contains(held_cpu_id)] lctx.cpu_lock_map().dom().contains(held_cpu_id) ==> !(krnl.cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
                forall|held_thread: RwLockThreadPtr| #![trigger lctx.thread_lock_map().dom().contains(held_thread)] lctx.thread_lock_map().dom().contains(held_thread) ==> !(krnl.thr_mp.spec_index(held_thread).view().state is SCHEDULED),
                lctx.cpu_lock_map().dom() =~= set![cpu_id],
                lctx.container_lock_map().dom().is_empty(),
                lctx.process_lock_map().dom().is_empty(),
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
                old(steps).nonlock_view().len() + i <= steps.nonlock_view().len(),
                steps.nonlock_view().len() <= old(steps).nonlock_view().len() + 4 * i,
                steps.nonlock_view().subrange(0, old(steps).nonlock_view().len() as int) == old(steps).nonlock_view(),
                typed_lock_maps_unchanged(old(lctx), lctx),
                old(krnl).thr_mp.dom().contains(thread_ptr),
                old(krnl).prc_mp.dom().contains(process_ptr),
                old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
                !krnl.prc_mp.spec_index(process_ptr).view().zombie,
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
                krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap4k { range: *range, mapped: i, directory: Mmap4kDirectory::None }),
                old(steps).view().len() + i <= steps.view().len() <= old(steps).view().len() + 4 * i,
                forall|j: int| #![trigger steps.view()[j]] 0 <= j < old(steps).view().len() ==> steps.view()[j] == old(steps).view()[j],
                forall|j: int| #![trigger steps.view()[j]] old(steps).view().len() <= j < steps.view().len() ==> mmap_4k_range_step(steps.view()[j], cpu_id, thread_ptr),
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
                assert(krnl.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(current_va)) by { spec_v2l4index_monotonic(range_start, current_va); };
                assert({
                    &&& pei_valid(spec_v2l4index(current_va))
                    &&& pei_valid(spec_v2l3index(current_va))
                    &&& pei_valid(spec_v2l2index(current_va))
                    &&& pei_valid(spec_v2l1index(current_va))
                }) by { spec_va_4k_valid_imply_indices_valid(); };
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
                    spec_va_4k_index_roundtrip_at(
                        current_va, spec_v2l4index(current_va), spec_v2l3index(current_va), spec_v2l2index(current_va),
                        spec_v2l1index(current_va),
                    );
                };
            }
            proof { assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); }; }
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
            proof { assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; }; }
            mmap_4k_build_one_structure(
                krnl, current_va, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, None, Tracked(&mut *lctx),
                Tracked(&mut *steps), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm), Tracked(None), Tracked(None),
            );
            proof { assert(!krnl.prc_mp.spec_index(process_ptr).view().zombie) by { reveal(process_cpu_wf); }; }
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
            map_one_mmap_4k_page(
                krnl, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, current_va, Tracked(&mut *lctx), Tracked(&mut *steps),
                Tracked(thread_lock_perm), Tracked(pagetable_lock_perm),
            );
            proof {
                assert(steps.nonlock_view().subrange(0, old(steps).nonlock_view().len() as int) == old(steps).nonlock_view()) by {
                    vstd::seq::lemma_seq_subrange_composition(
                        steps.nonlock_view(), 0, (steps.nonlock_view().len() - 1) as int, 0, old(steps).nonlock_view().len() as int,
                    );
                };
                assert(!krnl.prc_mp.spec_index(process_ptr).view().zombie) by { reveal(process_cpu_wf); };
            }
            i = i + 1;
        }
    }
} // verus!
