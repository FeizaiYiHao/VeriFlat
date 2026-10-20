use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use super::syscall_new_process_spec::{new_process_publish_step, new_process_publish_step_pre};
#[cfg(verus_keep_ghost)]
use super::syscall_new_process_trace::new_process_publish_step_pre_from_k;
use super::syscall_new_process_publish_step::end_new_process_publish_step;
use crate::*;
use super::syscall_new_process_with_iommu_release::release_staged_process_with_iommu_input_locks;

verus! {
pub(super) fn publish_staged_process_with_iommu(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    container_ptr: RwLockContainerPtr, parent_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr,
    source_pagetable_ptr: RwLockPageTableRoot, source_range: &VaRange4K, pcid: Pcid, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr,
    iommu_table_page_ptr: PagePtr, iommu_l4_page_ptr: PagePtr, process_page_lock_perm: Tracked<LockPerm>, pagetable_page_lock_perm: Tracked<LockPerm>,
    l4_page_lock_perm: Tracked<LockPerm>, iommu_table_page_lock_perm: Tracked<LockPerm>, iommu_l4_page_lock_perm: Tracked<LockPerm>,
    Tracked(cpu_lock_perm): Tracked<&LockPerm>, pcid_allocator_lock_perm: Tracked<LockPerm>,
    parent_lock_perm: Tracked<LockPerm>, Tracked(current_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>, Ghost(regs): Ghost<Registers>, Ghost(endpoint_index): Ghost<Option<EndpointIdx>>,
) -> (ret: (RwLockProcessPtr, RwLockPageTableRoot, RwLockPageTableRoot, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>))
    requires
        old(steps).snapshot_k() == *old(krnl),
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator == pcid_allocator_ptr,
        old(krnl).pcid_allc_mp.dom().contains(pcid_allocator_ptr),
        typed_lock_map_contains_mode(old(lctx).pcid_allocator_lock_map(), pcid_allocator_ptr, TypedLockMode::Write),
        old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).view().pcid_is_free(pcid),
        pcid_allocator_lock_perm.view().state() is WriteLock,
        pcid_allocator_lock_perm.view().thread_id() == old(lctx).thread_id(),
        pcid_allocator_lock_perm.view().lock_id() == old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(parent_ptr),
        old(krnl).prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == container_ptr,
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), parent_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(parent_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(parent_ptr).view().state.view() is Running || old(krnl).prc_mp.spec_index(parent_ptr).view().state.view() is Zombie,
        parent_lock_perm.view().state() is WriteLock,
        parent_lock_perm.view().thread_id() == old(lctx).thread_id(),
        parent_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(parent_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == source_pagetable_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view() == set![process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr],
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().is_empty(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_1g.view().is_empty(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::NewProcess(NewProcessProgress { range: *source_range, regs, endpoint_index, with_iommu: true, child: None })),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 5,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable_ptr).wf(),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Write),
        source_pagetable_lock_perm.state() is WriteLock,
        source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        source_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Write_lock_id,
        page_ptr_valid(process_page_ptr) && page_ptr_valid(pagetable_page_ptr) && page_ptr_valid(l4_page_ptr) && page_ptr_valid(iommu_table_page_ptr) && page_ptr_valid(iommu_l4_page_ptr),
        process_page_ptr != pagetable_page_ptr && process_page_ptr != l4_page_ptr && process_page_ptr != iommu_table_page_ptr && process_page_ptr != iommu_l4_page_ptr
            && pagetable_page_ptr != l4_page_ptr && pagetable_page_ptr != iommu_table_page_ptr && pagetable_page_ptr != iommu_l4_page_ptr
            && l4_page_ptr != iommu_table_page_ptr && l4_page_ptr != iommu_l4_page_ptr && iommu_table_page_ptr != iommu_l4_page_ptr,
        !old(krnl).prc_mp.dom().contains(process_page_ptr),
        !old(krnl).pt_mp.dom().contains(pagetable_page_ptr),
        !old(krnl).it_mp.dom().contains(iommu_table_page_ptr),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().owning_container == container_ptr,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().owning_container == container_ptr,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().owning_container == container_ptr,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().owning_container == container_ptr,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().owning_container == container_ptr,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(process_page_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pagetable_page_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(l4_page_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(iommu_table_page_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(iommu_l4_page_ptr), TypedLockMode::Write),
        process_page_lock_perm.view().state() is WriteLock && process_page_lock_perm.view().thread_id() == old(lctx).thread_id() && process_page_lock_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().locking_thread()->Write_lock_id,
        pagetable_page_lock_perm.view().state() is WriteLock && pagetable_page_lock_perm.view().thread_id() == old(lctx).thread_id() && pagetable_page_lock_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().locking_thread()->Write_lock_id,
        l4_page_lock_perm.view().state() is WriteLock && l4_page_lock_perm.view().thread_id() == old(lctx).thread_id() && l4_page_lock_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().locking_thread()->Write_lock_id,
        iommu_table_page_lock_perm.view().state() is WriteLock && iommu_table_page_lock_perm.view().thread_id() == old(lctx).thread_id()
            && iommu_table_page_lock_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().locking_thread()->Write_lock_id,
        iommu_l4_page_lock_perm.view().state() is WriteLock && iommu_l4_page_lock_perm.view().thread_id() == old(lctx).thread_id() && iommu_l4_page_lock_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().locking_thread()->Write_lock_id,
        old(lctx).page_lock_map().dom() == set![page_ptr2page_index(process_page_ptr), page_ptr2page_index(pagetable_page_ptr), page_ptr2page_index(l4_page_ptr), page_ptr2page_index(iommu_table_page_ptr), page_ptr2page_index(iommu_l4_page_ptr)],
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom() =~= set![parent_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom() =~= set![pcid_allocator_ptr],
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr],
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(steps).view() == old(steps).view().push(final(steps).view().last()),
        new_process_publish_step_pre(final(steps).view().last().old_u, cpu_id),
        new_process_publish_step(final(steps).view().last().old_u, final(steps).view().last().new_u, cpu_id),
        pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, ret.1, pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), ret.1)),
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, source_pagetable_ptr, pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable_ptr))
            ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, source_pagetable_ptr, pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable_ptr)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
        final(steps).nonlock_view().subrange(0, old(steps).nonlock_view().len() as int) == old(steps).nonlock_view(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).page_lock_map().dom().is_empty(),
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        final(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        final(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        final(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        final(lctx).container_lock_map().dom().is_empty(),
        final(lctx).process_lock_map().dom() =~= set![ret.0],
        final(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        final(lctx).scheduler_lock_map().dom().is_empty(),
        final(lctx).pcid_allocator_lock_map().dom().is_empty(),
        final(lctx).cpu_set_lock_map().dom().is_empty(),
        final(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr, ret.1],
        final(lctx).pagetable_window_lock_map().dom().is_empty(),
        final(lctx).iommu_table_lock_map().dom() =~= set![ret.2],
        final(lctx).iommu_root_table_lock_map().dom().is_empty(),
        final(lctx).pcid_needflush_lock_map().dom().is_empty(),
        final(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_lock_perm.thread_id() == final(lctx).thread_id(),
        cpu_lock_perm.lock_id() == final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        final(krnl).ctn_mp.dom().contains(container_ptr),
        final(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler,
        final(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k,
        final(krnl).prc_mp.dom().contains(ret.0),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), ret.0, TypedLockMode::Write),
        !final(krnl).prc_mp.spec_index(ret.0).being_killed(),
        final(krnl).prc_mp.spec_index(ret.0).view().state.view() is Creating,
        !final(krnl).prc_mp.spec_index(ret.0).view().zombie,
        final(krnl).prc_mp.spec_index(ret.0).view_rodata().view().owning_container == container_ptr,
        final(krnl).prc_mp.spec_index(ret.0).view_rodata().view().pagetable == ret.1,
        final(krnl).prc_mp.spec_index(ret.0).view().iommu_table == Some(ret.2),
        final(krnl).it_mp.dom().contains(ret.2),
        final(krnl).it_mp.spec_index(ret.2).view().is_empty(),
        typed_lock_map_contains_mode(final(lctx).iommu_table_lock_map(), ret.2, TypedLockMode::Write),
        ret.3.view().state() is WriteLock,
        ret.3.view().thread_id() == final(lctx).thread_id(),
        ret.3.view().lock_id() == final(krnl).prc_mp.spec_index(ret.0).locking_thread()->Write_lock_id,
        final(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !final(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc != ret.0,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == source_pagetable_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Share4k {
            source_range: *source_range, target_range: *source_range, shared: 0,
            origin: Share4kOrigin::NewProcess(NewProcessProgress { range: *source_range, regs, endpoint_index, with_iommu: true, child: Some(ret.0) }),
        }),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k - 5,
        current_thread_lock_perm.thread_id() == final(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        source_pagetable_ptr != ret.1,
        final(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Write),
        final(krnl).pt_mp.spec_index(source_pagetable_ptr).view().proc_ptr == parent_ptr,
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable_ptr).wf(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable_ptr) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable_ptr),
        source_pagetable_lock_perm.thread_id() == final(lctx).thread_id(),
        source_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Write_lock_id,
        final(krnl).pt_mp.dom().contains(ret.1),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), ret.1, TypedLockMode::Write),
        final(krnl).pt_mp.spec_index(ret.1).view().proc_ptr == ret.0,
        final(krnl).pt_mp.spec_index(ret.1).view().kernel_l4_end == old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().kernel_l4_end,
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), ret.1).is_empty(),
        ret.4.view().state() is WriteLock,
        ret.4.view().thread_id() == final(lctx).thread_id(),
        ret.4.view().lock_id() == final(krnl).pt_mp.spec_index(ret.1).locking_thread()->Write_lock_id,
        ret.5.view().state() is WriteLock,
        ret.5.view().thread_id() == final(lctx).thread_id(),
        ret.5.view().lock_id() == final(krnl).it_mp.spec_index(ret.2).locking_thread()->Write_lock_id,
{
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    let tracked mut pcid_allocator_lock_perm = pcid_allocator_lock_perm.get();
    let tracked mut parent_lock_perm = parent_lock_perm.get();
    let tracked process_page_lock_perm = process_page_lock_perm.get();
    let tracked pagetable_page_lock_perm = pagetable_page_lock_perm.get();
    let tracked l4_page_lock_perm = l4_page_lock_perm.get();
    let tracked iommu_table_page_lock_perm = iommu_table_page_lock_perm.get();
    let tracked iommu_l4_page_lock_perm = iommu_l4_page_lock_perm.get();
    proof {
        assert(new_process_publish_step_pre(kernel_k_to_kernel_u(*old(krnl)), cpu_id)) by {
            process_thread_wf_at(old(krnl).prc_mp, old(krnl).thr_mp, current_thread_ptr);
            new_process_publish_step_pre_from_k(old(krnl), old(lctx), cpu_id, parent_ptr, current_thread_ptr, container_ptr, *source_range, regs, endpoint_index, true);
        };
        assert(krnl.prc_mp.spec_index(parent_ptr).view_rodata().view().depth < usize::MAX) by {
            let uppers = krnl.prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view();
            assert(uppers.no_duplicates() && uppers.len() == krnl.prc_mp.spec_index(parent_ptr).view_rodata().view().depth) by { process_perms_wf_at(krnl.prc_mp, parent_ptr); };
            assert(uppers.len() <= NUM_PAGES) by {
                let c = krnl.prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container;
                let tree = krnl.ctn_mp.spec_index(c).view_ghost().owned_processes.view();
                container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, parent_ptr); container_process_wf_container_at(krnl.ctn_mp, krnl.prc_mp, c, parent_ptr);
                per_container_process_tree_wf_at(krnl.ctn_mp, krnl.prc_mp, c); process_uppertree_seq_wf_dom_at(krnl.ctn_mp.spec_index(c).view().root_process, tree, krnl.prc_mp, parent_ptr);
                lemma_kernel_object_ptr_seq_len_bounded(&*krnl, uppers);
            };
        };
        assert(page_ptr2page_index(process_page_ptr) != page_ptr2page_index(pagetable_page_ptr) && page_ptr2page_index(process_page_ptr) != page_ptr2page_index(l4_page_ptr)
            && page_ptr2page_index(process_page_ptr) != page_ptr2page_index(iommu_table_page_ptr) && page_ptr2page_index(process_page_ptr) != page_ptr2page_index(iommu_l4_page_ptr)
            && page_ptr2page_index(pagetable_page_ptr) != page_ptr2page_index(l4_page_ptr) && page_ptr2page_index(pagetable_page_ptr) != page_ptr2page_index(iommu_table_page_ptr) && page_ptr2page_index(pagetable_page_ptr) != page_ptr2page_index(iommu_l4_page_ptr)
            && page_ptr2page_index(l4_page_ptr) != page_ptr2page_index(iommu_table_page_ptr) && page_ptr2page_index(l4_page_ptr) != page_ptr2page_index(iommu_l4_page_ptr) && page_ptr2page_index(iommu_table_page_ptr) != page_ptr2page_index(iommu_l4_page_ptr)) by {
            page_ptr2page_index_neq(process_page_ptr, pagetable_page_ptr);
            page_ptr2page_index_neq(process_page_ptr, l4_page_ptr);
            page_ptr2page_index_neq(process_page_ptr, iommu_table_page_ptr);
            page_ptr2page_index_neq(process_page_ptr, iommu_l4_page_ptr);
            page_ptr2page_index_neq(pagetable_page_ptr, l4_page_ptr);
            page_ptr2page_index_neq(pagetable_page_ptr, iommu_table_page_ptr);
            page_ptr2page_index_neq(pagetable_page_ptr, iommu_l4_page_ptr);
            page_ptr2page_index_neq(l4_page_ptr, iommu_table_page_ptr);
            page_ptr2page_index_neq(l4_page_ptr, iommu_l4_page_ptr);
            page_ptr2page_index_neq(iommu_table_page_ptr, iommu_l4_page_ptr);
        };
    }
    let (child_ptr, target_pagetable_ptr, iommu_table_ptr, Tracked(child_lock_perm), Tracked(target_pagetable_lock_perm), Tracked(iommu_table_lock_perm)) = create_process_with_iommu_from_staged_pages(
        krnl, process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, current_thread_ptr,
        container_ptr, pcid_allocator_ptr, pcid, Tracked(&mut *lctx), Tracked(&process_page_lock_perm), Tracked(&pagetable_page_lock_perm),
        Tracked(&l4_page_lock_perm), Tracked(&iommu_table_page_lock_perm), Tracked(&iommu_l4_page_lock_perm),
        Tracked(&parent_lock_perm), Tracked(&current_thread_lock_perm), Tracked(&pcid_allocator_lock_perm),
    );
    proof { assert(krnl.prc_mp.spec_index(parent_ptr).view().state.view() is Running || krnl.prc_mp.spec_index(parent_ptr).view().state.view() is Zombie) by { reveal(create_process_with_iommu_from_staged_pages_eof_transition_framing); }; }
    release_staged_process_with_iommu_input_locks(
        krnl, Tracked(&mut *lctx), cpu_id, container_ptr, parent_ptr, child_ptr, current_thread_ptr, pcid_allocator_ptr, source_pagetable_ptr,
        target_pagetable_ptr, iommu_table_ptr, process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr,
        Tracked(process_page_lock_perm), Tracked(pagetable_page_lock_perm), Tracked(l4_page_lock_perm), Tracked(iommu_table_page_lock_perm),
        Tracked(iommu_l4_page_lock_perm), Tracked(parent_lock_perm), Tracked(pcid_allocator_lock_perm),
    );
    proof { reveal(create_process_with_iommu_from_staged_pages_eof_transition_framing); reveal(kernel_thread_quota_4k_changed); }
    end_new_process_publish_step(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, parent_ptr, child_ptr, current_thread_ptr, pcid_allocator_ptr, source_pagetable_ptr,
        target_pagetable_ptr, Some(iommu_table_ptr), source_range, pcid, Tracked(current_thread_lock_perm), Ghost(regs), Ghost(endpoint_index),
    );
    proof {
        assert(krnl.ctn_mp.dom().contains(container_ptr)) by { container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, current_thread_ptr); };
        assert(krnl.pt_mp.spec_index(source_pagetable_ptr).view().proc_ptr == parent_ptr) by { process_thread_wf_at(old(krnl).prc_mp, old(krnl).thr_mp, current_thread_ptr); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, current_thread_ptr); reveal(process_pagetable_match); };
        assert(krnl.pt_mp.spec_index(target_pagetable_ptr).view().kernel_l4_end == old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().kernel_l4_end) by {
            krnl.default_pagetable_wf_at(target_pagetable_ptr); old(krnl).default_pagetable_wf_at(source_pagetable_ptr);
        };
    }
    proof { assert(pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, target_pagetable_ptr, pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable_ptr))) by { reveal(tlb_wf_spec); }; }
    (child_ptr, target_pagetable_ptr, iommu_table_ptr, Tracked(child_lock_perm), Tracked(target_pagetable_lock_perm), Tracked(iommu_table_lock_perm))
}
}
