use vstd::prelude::*;
use crate::*;
use super::syscall_new_container_spec::{new_container_finish_step, new_container_finish_step_pre};
use super::syscall_new_container_trace::{new_container_finish_step_from_u, new_container_finish_step_pre_from_u};
use super::syscall_new_container_cpu::transfer_new_container_cpu;
#[cfg(not(feature = "split-crates"))]
use crate::implementation::create_thread_from_staged_page::create_thread_from_staged_page_merged;

verus! {
/// Moves the Off CPU and the staged root-thread page into the child container,
/// releases the child scheduler, and closes the container-creation step.
#[verifier::spinoff_prover]
pub(super) fn end_new_container_created_step(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    caller_cpu_id: CpuId, transfer_cpu_id: CpuId, parent_cpu_set: RwLockCpuSetPtr, child_cpu_set: RwLockCpuSetPtr,
    parent_container_ptr: RwLockContainerPtr, parent_process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr,
    source_pagetable_ptr: RwLockPageTableRoot, child_container_ptr: RwLockContainerPtr, child_process_ptr: RwLockProcessPtr,
    child_pagetable_ptr: RwLockPageTableRoot, child_scheduler_ptr: RwLockSchedulerPtr, thread_page_ptr: PagePtr,
    Tracked(parent_container_lock_perm): Tracked<&LockPerm>, Tracked(child_container_lock_perm): Tracked<&LockPerm>,
    Tracked(thread_page_lock_perm): Tracked<&LockPerm>, child_scheduler_lock_perm: Tracked<LockPerm>,
    transfer_cpu_lock_perm: Tracked<LockPerm>, parent_cpu_set_lock_perm: Tracked<LockPerm>, child_cpu_set_lock_perm: Tracked<LockPerm>,
)
    requires
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, source_pagetable_ptr, old(krnl).pt_mp.spec_index(source_pagetable_ptr).view()),
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, child_pagetable_ptr, old(krnl).pt_mp.spec_index(child_pagetable_ptr).view()),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().leaves_present(),
        old(krnl).pt_mp.spec_index(child_pagetable_ptr).view().leaves_present(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        caller_cpu_id == old(lctx).cpu_id(),
        index_valid(NUM_CPUS, transfer_cpu_id),
        transfer_cpu_id != caller_cpu_id,
        old(krnl).cpu_published[transfer_cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().current_pcid),
        page_ptr_valid(thread_page_ptr),
        parent_container_ptr != child_container_ptr,
        old(lctx).page_lock_map().dom() =~= set![page_ptr2page_index(thread_page_ptr)],
        old(lctx).cpu_lock_map().dom() =~= set![caller_cpu_id, transfer_cpu_id],
        old(lctx).container_lock_map().dom() =~= set![parent_container_ptr, child_container_ptr],
        old(lctx).process_lock_map().dom() =~= set![parent_process_ptr, child_process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom() =~= set![child_scheduler_ptr],
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom() =~= set![parent_cpu_set, child_cpu_set],
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr, child_pagetable_ptr],
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(thread_page_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), parent_container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), child_container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), child_scheduler_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), caller_cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), transfer_cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), parent_cpu_set, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), child_cpu_set, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), parent_process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), child_process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), child_pagetable_ptr, TypedLockMode::Write),
        !old(steps).snapshot_k().prc_mp.dom().contains(child_process_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view() == set![thread_page_ptr],
        old(krnl).ctn_mp.dom().contains(parent_container_ptr),
        old(krnl).ctn_mp.dom().contains(child_container_ptr),
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        !old(krnl).ctn_mp.spec_index(child_container_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata().view().parent == Some(parent_container_ptr),
        old(krnl).ctn_mp.spec_index(parent_container_ptr).view_rodata().view().cpu_set == parent_cpu_set,
        old(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata().view().cpu_set == child_cpu_set,
        old(krnl).cpu_set_mp.spec_index(parent_cpu_set).view().owned_cpus.closed_view().contains(transfer_cpu_id),
        transfer_cpu_lock_perm.view().state() is WriteLock,
        transfer_cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        transfer_cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(transfer_cpu_id).view().locking_thread()->Write_lock_id,
        parent_cpu_set_lock_perm.view().state() is WriteLock,
        parent_cpu_set_lock_perm.view().thread_id() == old(lctx).thread_id(),
        parent_cpu_set_lock_perm.view().lock_id() == old(krnl).cpu_set_mp.spec_index(parent_cpu_set).locking_thread()->Write_lock_id,
        child_cpu_set_lock_perm.view().state() is WriteLock,
        child_cpu_set_lock_perm.view().thread_id() == old(lctx).thread_id(),
        child_cpu_set_lock_perm.view().lock_id() == old(krnl).cpu_set_mp.spec_index(child_cpu_set).locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view().contains(thread_page_ptr),
        parent_container_lock_perm.state() is WriteLock,
        parent_container_lock_perm.thread_id() == old(lctx).thread_id(),
        parent_container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        child_container_lock_perm.state() is WriteLock,
        child_container_lock_perm.thread_id() == old(lctx).thread_id(),
        child_container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(child_container_ptr).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(child_process_ptr),
        !old(krnl).prc_mp.spec_index(child_process_ptr).view().zombie,
        old(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().pagetable == child_pagetable_ptr,
        old(krnl).prc_mp.spec_index(child_process_ptr).view().iommu_table is None,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).sched_mp.dom().contains(child_scheduler_ptr),
        child_scheduler_lock_perm.view().state() is WriteLock,
        child_scheduler_lock_perm.view().thread_id() == old(lctx).thread_id(),
        child_scheduler_lock_perm.view().lock_id() == old(krnl).sched_mp.spec_index(child_scheduler_ptr).locking_thread()->Write_lock_id,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page_ptr)).view().view().owning_container == parent_container_ptr,
        thread_page_lock_perm.state() is WriteLock,
        thread_page_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page_ptr)).view().locking_thread()->Write_lock_id,
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(steps).view() == old(steps).view().push(final(steps).view().last()),
        final(steps).view().last().old_u == old(steps).snapshot_u(),
        kernel_u_cpu_and_page_owner_changed(kernel_k_to_kernel_u(*old(krnl)), final(steps).view().last().new_u, transfer_cpu_id, parent_container_ptr, child_container_ptr, thread_page_ptr),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).page_lock_map().dom() =~= set![page_ptr2page_index(thread_page_ptr)],
        final(lctx).cpu_lock_map().dom() =~= set![caller_cpu_id],
        final(lctx).container_lock_map().dom() =~= set![parent_container_ptr, child_container_ptr],
        final(lctx).process_lock_map().dom() =~= set![parent_process_ptr, child_process_ptr],
        final(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        final(lctx).endpoint_lock_map().dom().is_empty(),
        final(lctx).scheduler_lock_map().dom().is_empty(),
        final(lctx).pcid_allocator_lock_map().dom().is_empty(),
        final(lctx).cpu_set_lock_map().dom().is_empty(),
        final(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr, child_pagetable_ptr],
        final(lctx).iommu_table_lock_map().dom().is_empty(),
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        final(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        final(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        final(lctx).pcid_needflush_lock_map().dom().is_empty(),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(thread_page_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), caller_cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), parent_container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), child_container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), parent_process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), child_process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), child_pagetable_ptr, TypedLockMode::Write),
        final(steps).nonlock_view() == old(steps).nonlock_view().push(final(steps).nonlock_view().last()),
        final(steps).snapshot_k() == *final(krnl),
        final(krnl).cpu_arr.spec_index(caller_cpu_id).view() == old(krnl).cpu_arr.spec_index(caller_cpu_id).view(),
        final(krnl).cpu_published[caller_cpu_id as int].view() == old(krnl).cpu_published[caller_cpu_id as int].view(),
        pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, source_pagetable_ptr, final(krnl).pt_mp.spec_index(source_pagetable_ptr).view()),
        pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, child_pagetable_ptr, final(krnl).pt_mp.spec_index(child_pagetable_ptr).view()),
        final(krnl).pt_mp.spec_index(source_pagetable_ptr).view().leaves_present(),
        final(krnl).pt_mp.spec_index(child_pagetable_ptr).view().leaves_present(),
        final(krnl).ctn_mp.dom().contains(parent_container_ptr),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(parent_container_ptr).view_rodata(),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view_ghost() == old(krnl).ctn_mp.spec_index(parent_container_ptr).view_ghost(),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread() == old(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread(),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed() == old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view() == (Container { owned_pages: final(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_pages, ..old(krnl).ctn_mp.spec_index(parent_container_ptr).view() }),
        final(krnl).ctn_mp.dom().contains(child_container_ptr),
        final(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata(),
        final(krnl).ctn_mp.spec_index(child_container_ptr).view_ghost() == old(krnl).ctn_mp.spec_index(child_container_ptr).view_ghost(),
        final(krnl).ctn_mp.spec_index(child_container_ptr).locking_thread() == old(krnl).ctn_mp.spec_index(child_container_ptr).locking_thread(),
        final(krnl).ctn_mp.spec_index(child_container_ptr).being_killed() == old(krnl).ctn_mp.spec_index(child_container_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(child_container_ptr).view() == (Container { owned_pages: final(krnl).ctn_mp.spec_index(child_container_ptr).view().owned_pages, ..old(krnl).ctn_mp.spec_index(child_container_ptr).view() }),
        final(krnl).prc_mp.dom().contains(parent_process_ptr),
        final(krnl).prc_mp.spec_index(parent_process_ptr) == old(krnl).prc_mp.spec_index(parent_process_ptr),
        final(krnl).prc_mp.dom().contains(child_process_ptr),
        final(krnl).prc_mp.spec_index(child_process_ptr) == old(krnl).prc_mp.spec_index(child_process_ptr),
        final(krnl).thr_mp.dom().contains(current_thread_ptr),
        final(krnl).thr_mp.spec_index(current_thread_ptr) == old(krnl).thr_mp.spec_index(current_thread_ptr),
        final(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        final(krnl).pt_mp.spec_index(source_pagetable_ptr) == old(krnl).pt_mp.spec_index(source_pagetable_ptr),
        final(krnl).pt_mp.dom().contains(child_pagetable_ptr),
        final(krnl).pt_mp.spec_index(child_pagetable_ptr) == old(krnl).pt_mp.spec_index(child_pagetable_ptr),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page_ptr)).view().view().owning_container == child_container_ptr,
        thread_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page_ptr)).view().locking_thread()->Write_lock_id,
{
    transfer_new_container_cpu(
        krnl, Tracked(&mut *lctx), parent_container_ptr, child_container_ptr, parent_cpu_set, child_cpu_set, transfer_cpu_id,
        transfer_cpu_lock_perm, parent_cpu_set_lock_perm, child_cpu_set_lock_perm,
    );
    transfer_staged_4k_page_to_child_container(
        krnl, Tracked(&mut *lctx), thread_page_ptr, current_thread_ptr, parent_container_ptr, child_container_ptr,
        Tracked(thread_page_lock_perm), Tracked(parent_container_lock_perm), Tracked(child_container_lock_perm),
    );
    krnl.wunlock_scheduler(child_scheduler_ptr, Tracked(&mut *lctx), child_scheduler_lock_perm);
    proof {
        assert(kernel_process_added(&steps.snapshot_k(), &*krnl, child_process_ptr)) by { reveal(kernel_process_added); };
        assert(krnl.prc_mp.spec_index(child_process_ptr).view().pagetable == child_pagetable_ptr) by { reveal(process_pagetable_match); };
        assert(kernel_u_cpu_and_page_owner_changed(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), transfer_cpu_id, parent_container_ptr, child_container_ptr, thread_page_ptr)) by {
            kernel_cpu_and_page_owner_changed_implies_u_step(old(krnl), &*krnl, transfer_cpu_id,
                parent_container_ptr, child_container_ptr, thread_page_ptr);
        };
        krnl.kernel_step_boundary_process_added(&mut *lctx, &mut *steps, child_process_ptr, current_thread_ptr);
    }
}

/// Shares the parent's page range into the child process's page table; directory
/// pages are funded by the parent thread and moved into the child container.
#[verifier::spinoff_prover]
pub(super) fn share_new_container_range(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, caller_cpu_id: CpuId,
    source_range: &VaRange4K, parent_container_ptr: RwLockContainerPtr, child_container_ptr: RwLockContainerPtr, parent_process_ptr: RwLockProcessPtr,
    child_process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, source_pagetable_ptr: RwLockPageTableRoot,
    child_pagetable_ptr: RwLockPageTableRoot, child_allocator_4k_ptr: RwLockPageAllocatorPtr, thread_page_ptr: PagePtr,
    Tracked(parent_container_lock_perm): Tracked<&LockPerm>, Tracked(child_container_lock_perm): Tracked<&LockPerm>,
    Tracked(current_thread_lock_perm): Tracked<&LockPerm>, Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>,
    Tracked(child_pagetable_lock_perm): Tracked<&LockPerm>, Ghost(record): Ghost<NewContainerProgress>,
)
    requires
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, source_pagetable_ptr, old(krnl).pt_mp.spec_index(source_pagetable_ptr).view()),
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, child_pagetable_ptr, old(krnl).pt_mp.spec_index(child_pagetable_ptr).view()),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().leaves_present(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k() == *old(krnl),
        index_valid(NUM_CPUS, caller_cpu_id),
        caller_cpu_id == old(lctx).cpu_id(),
        parent_container_ptr != child_container_ptr,
        old(lctx).page_lock_map().dom() =~= set![page_ptr2page_index(thread_page_ptr)],
        old(lctx).cpu_lock_map().dom() =~= set![caller_cpu_id],
        old(lctx).process_lock_map().dom() =~= set![parent_process_ptr, child_process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr, child_pagetable_ptr],
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), caller_cpu_id, TypedLockMode::Write),
        !(old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().state is Off),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).ctn_mp.dom().contains(parent_container_ptr),
        old(krnl).ctn_mp.dom().contains(child_container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), parent_container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), child_container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        !old(krnl).ctn_mp.spec_index(child_container_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata().view().parent == Some(parent_container_ptr),
        old(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata().view().allocator_ptr_4k == child_allocator_4k_ptr,
        old(krnl).ctn_mp.spec_index(child_container_ptr).view_ghost().uppertree_seq.view() == old(krnl).ctn_mp.spec_index(parent_container_ptr).view_ghost().uppertree_seq.view().push(parent_container_ptr),
        parent_container_lock_perm.state() is WriteLock,
        parent_container_lock_perm.thread_id() == old(lctx).thread_id(),
        parent_container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        child_container_lock_perm.state() is WriteLock,
        child_container_lock_perm.thread_id() == old(lctx).thread_id(),
        child_container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(child_container_ptr).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(parent_process_ptr),
        old(krnl).prc_mp.dom().contains(child_process_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), child_process_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(child_process_ptr).view().zombie,
        old(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().owning_container == child_container_ptr,
        old(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().pagetable == child_pagetable_ptr,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == parent_container_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_process_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == source_pagetable_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id: caller_cpu_id }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view() == set![thread_page_ptr],
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().is_empty(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_1g.view().is_empty(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Share4k {
            source_range: *source_range, target_range: *source_range, shared: 0,
            origin: Share4kOrigin::NewContainer(NewContainerProgress { child_container: Some(child_container_ptr), ..record }),
        }),
        old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        old(krnl).ctn_mp.spec_index(child_container_ptr).view().root_process == child_process_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 1 + 3 * source_range.len,
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        old(krnl).pt_mp.dom().contains(child_pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), child_pagetable_ptr, TypedLockMode::Write),
        source_pagetable_lock_perm.state() is WriteLock,
        source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        source_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Write_lock_id,
        child_pagetable_lock_perm.state() is WriteLock,
        child_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        child_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(child_pagetable_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.spec_index(child_pagetable_ptr).view().is_empty(),
        source_range.wf(),
        source_range.len > 0,
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(source_range.start),
        share_mapping_4k_source_range_present(old(krnl), source_pagetable_ptr, source_range),
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(krnl).prc_mp.spec_index(child_process_ptr).view().pagetable == child_pagetable_ptr,
        final(krnl).prc_mp.spec_index(parent_process_ptr).view().pagetable == source_pagetable_ptr,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() + source_range.len <= final(steps).view().len() <= old(steps).view().len() + 4 * source_range.len,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==>
            share_4k_range_step(final(steps).view()[j], caller_cpu_id),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        old(steps).nonlock_view().len() as int + source_range.len as int <= final(steps).nonlock_view().len() as int,
        final(steps).nonlock_view().len() as int <= old(steps).nonlock_view().len() as int + 4 * source_range.len as int,
        kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
        final(krnl).irt.owners() == final(steps).snapshot_k().irt.owners(),
        final(krnl).irt.iommu_roots() == final(steps).snapshot_k().irt.iommu_roots(),
        final(krnl).cpu_tlb.view() == final(steps).snapshot_k().cpu_tlb.view(),
        final(krnl).iommu_tlb.view() == final(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(krnl)),
        final(krnl).cpu_arr.spec_index(caller_cpu_id).view() == old(krnl).cpu_arr.spec_index(caller_cpu_id).view(),
        final(krnl).cpu_published[caller_cpu_id as int].view() == old(krnl).cpu_published[caller_cpu_id as int].view(),
        pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, source_pagetable_ptr, final(krnl).pt_mp.spec_index(source_pagetable_ptr).view()),
        pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, child_pagetable_ptr, final(krnl).pt_mp.spec_index(child_pagetable_ptr).view()),
        final(krnl).pt_mp.spec_index(source_pagetable_ptr).view().leaves_present(),
        final(krnl).pt_mp.spec_index(child_pagetable_ptr).view().leaves_present(),
        final(krnl).ctn_mp.dom().contains(parent_container_ptr),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(parent_container_ptr).view_rodata(),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view_ghost() == old(krnl).ctn_mp.spec_index(parent_container_ptr).view_ghost(),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread() == old(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread(),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed() == old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view() == (Container { owned_pages: final(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_pages, ..old(krnl).ctn_mp.spec_index(parent_container_ptr).view() }),
        final(krnl).ctn_mp.dom().contains(child_container_ptr),
        final(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata(),
        final(krnl).ctn_mp.spec_index(child_container_ptr).view_ghost() == old(krnl).ctn_mp.spec_index(child_container_ptr).view_ghost(),
        final(krnl).ctn_mp.spec_index(child_container_ptr).locking_thread() == old(krnl).ctn_mp.spec_index(child_container_ptr).locking_thread(),
        final(krnl).ctn_mp.spec_index(child_container_ptr).being_killed() == old(krnl).ctn_mp.spec_index(child_container_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(child_container_ptr).view() == (Container { owned_pages: final(krnl).ctn_mp.spec_index(child_container_ptr).view().owned_pages, ..old(krnl).ctn_mp.spec_index(child_container_ptr).view() }),
        final(krnl).prc_mp.spec_index(parent_process_ptr) == old(krnl).prc_mp.spec_index(parent_process_ptr),
        final(krnl).prc_mp.spec_index(child_process_ptr) == old(krnl).prc_mp.spec_index(child_process_ptr),
        final(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        current_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_process_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == parent_container_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id: caller_cpu_id }),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view() == set![thread_page_ptr],
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().is_empty(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_1g.view().is_empty(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Share4k {
            source_range: *source_range, target_range: *source_range, shared: source_range.len,
            origin: Share4kOrigin::NewContainer(NewContainerProgress { child_container: Some(child_container_ptr), ..record }),
        }),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k - 3 * source_range.len,
        source_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Write_lock_id,
        child_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(child_pagetable_ptr).locking_thread()->Write_lock_id,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page_ptr)).view() == old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page_ptr)).view(),
{
    proof {
        use_type_invariant(&*steps);
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl);
        assert(krnl.allc_4k_mp.dom().contains(child_allocator_4k_ptr)) by { reveal(container_allocator_wf); };
        assert(lctx.page_lock_map().dom().contains(page_ptr2page_index(thread_page_ptr))) by { vstd::set::axiom_set_ext_equal(lctx.page_lock_map().dom(), set![page_ptr2page_index(thread_page_ptr)]); };
        assert(lctx.thread_lock_map().dom() == set![current_thread_ptr, current_thread_ptr]) by { vstd::set::axiom_set_ext_equal(lctx.thread_lock_map().dom(), set![current_thread_ptr, current_thread_ptr]); };
        assert(krnl.pt_mp.spec_index(source_pagetable_ptr).view().wf()) by { reveal(pagetable_perms_wf); };
        assert(krnl.prc_mp.spec_index(parent_process_ptr).view().pagetable == source_pagetable_ptr && krnl.prc_mp.spec_index(child_process_ptr).view().pagetable == child_pagetable_ptr) by { reveal(process_thread_wf); reveal(process_pagetable_match); };
        assert(!krnl.prc_mp.spec_index(parent_process_ptr).view().zombie) by { reveal(process_thread_wf); };
        assert(krnl.pt_mp.spec_index(source_pagetable_ptr).view().proc_ptr == parent_process_ptr && krnl.pt_mp.spec_index(child_pagetable_ptr).view().proc_ptr == child_process_ptr) by { reveal(process_pagetable_match); };
        assert(krnl.pt_mp.spec_index(child_pagetable_ptr).view().kernel_l4_end == krnl.pt_mp.spec_index(source_pagetable_ptr).view().kernel_l4_end) by { reveal(KernelK::default_pagetable_wf); };
        assert(krnl.pt_mp.spec_index(child_pagetable_ptr).view().spec_mapping_4k_va_range_empty(source_range.start, source_range.view().spec_index((source_range.len - 1) as int))) by { reveal(PageTable::spec_mapping_4k_va_range_empty); };
        assert(share_mapping_4k_range_owner_compatible(krnl, source_pagetable_ptr, parent_container_ptr, source_range)) by {
            reveal(mapped_4k_page_pagetable_wf); reveal(container_process_page_pagetable_wf); reveal(process_thread_wf); reveal(container_subtree_set_exclusive);
        };
        assert(share_mapping_4k_range_owner_compatible(krnl, source_pagetable_ptr, child_container_ptr, source_range)) by { broadcast use vstd::seq_lib::lemma_seq_contains_after_push; };
        assert({
            &&& share_4k_objects_k(*krnl, caller_cpu_id).source_thread == current_thread_ptr && share_4k_objects_k(*krnl, caller_cpu_id).quota_thread == current_thread_ptr
            &&& share_4k_objects_k(*krnl, caller_cpu_id).target == child_process_ptr && share_4k_objects_k(*krnl, caller_cpu_id).target_container == child_container_ptr
            &&& share_4k_objects_k(*krnl, caller_cpu_id).transfer_source == Some(parent_container_ptr)
        }) by { reveal(share_4k_objects_k); };
    }
    let ghost origin = Share4kOrigin::NewContainer(NewContainerProgress { child_container: Some(child_container_ptr), ..record });
    share_mapping_4k_build_and_share(
        krnl, source_range, source_range, child_allocator_4k_ptr, current_thread_ptr, current_thread_ptr, current_thread_ptr, child_process_ptr, child_container_ptr,
        caller_cpu_id, source_pagetable_ptr, child_pagetable_ptr, Some(parent_container_ptr), Ghost(origin), Tracked(&mut *lctx), Tracked(&mut *steps),
        Tracked(current_thread_lock_perm), Tracked(current_thread_lock_perm), Tracked(source_pagetable_lock_perm), Tracked(child_pagetable_lock_perm),
        Tracked(Some(parent_container_lock_perm)), Tracked(Some(child_container_lock_perm)),
    );
}

/// Creates the child's root thread from the staged page, releases every held lock,
/// and closes the new-thread step.
#[verifier::spinoff_prover]
pub(super) fn create_new_container_root_thread_and_finish(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    caller_cpu_id: CpuId, parent_container_ptr: RwLockContainerPtr, child_container_ptr: RwLockContainerPtr,
    parent_process_ptr: RwLockProcessPtr, child_process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr,
    source_pagetable_ptr: RwLockPageTableRoot, child_pagetable_ptr: RwLockPageTableRoot, child_scheduler_ptr: RwLockSchedulerPtr,
    thread_page_ptr: PagePtr, caller_cpu_lock_perm: Tracked<LockPerm>, parent_container_lock_perm: Tracked<LockPerm>,
    child_container_lock_perm: Tracked<LockPerm>, parent_process_lock_perm: Tracked<LockPerm>, child_process_lock_perm: Tracked<LockPerm>,
    current_thread_lock_perm: Tracked<LockPerm>, source_pagetable_lock_perm: Tracked<LockPerm>, child_pagetable_lock_perm: Tracked<LockPerm>,
    thread_page_lock_perm: Tracked<LockPerm>, initial_regs: &Registers,
) -> (new_thread_ptr: RwLockThreadPtr)
    requires
        old(steps).snapshot_k() == *old(krnl),
        old(krnl).prc_mp.spec_index(parent_process_ptr).view().pagetable == source_pagetable_ptr,
        old(krnl).prc_mp.spec_index(child_process_ptr).view().pagetable == child_pagetable_ptr,
        old(krnl).prc_mp.spec_index(child_process_ptr).view().iommu_table is None,
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, source_pagetable_ptr, old(krnl).pt_mp.spec_index(source_pagetable_ptr).view()),
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, child_pagetable_ptr, old(krnl).pt_mp.spec_index(child_pagetable_ptr).view()),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().leaves_present(),
        old(krnl).pt_mp.spec_index(child_pagetable_ptr).view().leaves_present(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        old(krnl).irt.owners() == old(steps).snapshot_k().irt.owners(),
        old(krnl).irt.iommu_roots() == old(steps).snapshot_k().irt.iommu_roots(),
        old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
        old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        caller_cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_published[caller_cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_pcid),
        page_ptr_valid(thread_page_ptr),
        parent_container_ptr != child_container_ptr,
        source_pagetable_ptr != child_pagetable_ptr,
        old(lctx).page_lock_map().dom() =~= set![page_ptr2page_index(thread_page_ptr)],
        old(lctx).cpu_lock_map().dom() =~= set![caller_cpu_id],
        old(lctx).container_lock_map().dom() =~= set![parent_container_ptr, child_container_ptr],
        old(lctx).process_lock_map().dom() =~= set![parent_process_ptr, child_process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr, child_pagetable_ptr],
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), caller_cpu_id, TypedLockMode::Write),
        !(old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().state is Off),
        caller_cpu_lock_perm.view().state() is WriteLock,
        caller_cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        caller_cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(caller_cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(child_container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), parent_container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), child_container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        !old(krnl).ctn_mp.spec_index(child_container_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata().view().scheduler == child_scheduler_ptr,
        parent_container_lock_perm.view().state() is WriteLock,
        parent_container_lock_perm.view().thread_id() == old(lctx).thread_id(),
        parent_container_lock_perm.view().lock_id() == old(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        child_container_lock_perm.view().state() is WriteLock,
        child_container_lock_perm.view().thread_id() == old(lctx).thread_id(),
        child_container_lock_perm.view().lock_id() == old(krnl).ctn_mp.spec_index(child_container_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), parent_process_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(parent_process_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(parent_process_ptr).view_rodata().view().owning_container == parent_container_ptr,
        parent_process_lock_perm.view().state() is WriteLock,
        parent_process_lock_perm.view().thread_id() == old(lctx).thread_id(),
        parent_process_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(parent_process_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), child_process_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(child_process_ptr).being_killed(),
        !old(krnl).prc_mp.spec_index(child_process_ptr).view().zombie,
        old(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().owning_container == child_container_ptr,
        child_process_lock_perm.view().state() is WriteLock,
        child_process_lock_perm.view().thread_id() == old(lctx).thread_id(),
        child_process_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(child_process_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_process_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id: caller_cpu_id }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view() == set![thread_page_ptr],
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().is_empty(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_1g.view().is_empty(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() matches Some(SyscallProgress::Share4k { source_range, shared, origin, .. })
            && shared == source_range.len && origin is NewContainer && origin->NewContainer_0.child_container == Some(child_container_ptr) && origin->NewContainer_0.regs == *initial_regs,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == parent_container_ptr,
        old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        old(krnl).ctn_mp.spec_index(child_container_ptr).view().root_process == child_process_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 1,
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Write),
        source_pagetable_lock_perm.view().state() is WriteLock,
        source_pagetable_lock_perm.view().thread_id() == old(lctx).thread_id(),
        source_pagetable_lock_perm.view().lock_id() == old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), child_pagetable_ptr, TypedLockMode::Write),
        child_pagetable_lock_perm.view().state() is WriteLock,
        child_pagetable_lock_perm.view().thread_id() == old(lctx).thread_id(),
        child_pagetable_lock_perm.view().lock_id() == old(krnl).pt_mp.spec_index(child_pagetable_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(thread_page_ptr), TypedLockMode::Write),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page_ptr)).view().view().owning_container == child_container_ptr,
        thread_page_lock_perm.view().state() is WriteLock,
        thread_page_lock_perm.view().thread_id() == old(lctx).thread_id(),
        thread_page_lock_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page_ptr)).view().locking_thread()->Write_lock_id,
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(steps).view() == old(steps).view().push(final(steps).view().last()),
        final(steps).view().last().new_u == kernel_k_to_kernel_u(*final(krnl)),
        new_container_finish_step_pre(final(steps).view().last().old_u, caller_cpu_id),
        new_container_finish_step(final(steps).view().last().old_u, final(steps).view().last().new_u, caller_cpu_id),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).nonlock_view() == old(steps).nonlock_view().push(final(steps).nonlock_view().last()),
        final(steps).snapshot_k() == *final(krnl),
{
    let tracked caller_cpu_lock_perm = caller_cpu_lock_perm.get();
    let tracked parent_container_lock_perm = parent_container_lock_perm.get();
    let tracked child_container_lock_perm = child_container_lock_perm.get();
    let tracked parent_process_lock_perm = parent_process_lock_perm.get();
    let tracked child_process_lock_perm = child_process_lock_perm.get();
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked source_pagetable_lock_perm = source_pagetable_lock_perm.get();
    let tracked child_pagetable_lock_perm = child_pagetable_lock_perm.get();
    let tracked thread_page_lock_perm = thread_page_lock_perm.get();
    proof { assert(krnl.sched_mp.dom().contains(child_scheduler_ptr) && !krnl.sched_mp.spec_index(child_scheduler_ptr).being_killed()) by { container_scheduler_wf_at(krnl.ctn_mp, krnl.sched_mp, child_container_ptr); reveal(scheduler_perms_wf); }; }
    let Tracked(child_scheduler_lock_perm) = krnl.wlock_scheduler(child_scheduler_ptr, Tracked(&mut *lctx));
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        use_type_invariant(&*steps);
        assert(steps.snapshot_u() == kernel_k_to_kernel_u(*krnl)) by { kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl); };
        krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
        use_type_invariant(&*steps);
        assert(new_container_finish_step_pre(steps.snapshot_u(), caller_cpu_id) && steps.snapshot_u().container_map[child_container_ptr].root_process == child_process_ptr) by {
            reveal(process_thread_wf); reveal(share_4k_objects_k);
            kernel_write_held_context_projection(&*krnl, &*lctx, caller_cpu_id, parent_process_ptr, current_thread_ptr, None);
            kernel_write_held_context_projection(&*krnl, &*lctx, caller_cpu_id, child_process_ptr, current_thread_ptr, None);
            kernel_share_4k_objects_projection(&*krnl, &*lctx, caller_cpu_id);
            kernel_cpu_thread_projection_at(&*krnl, caller_cpu_id, parent_process_ptr, current_thread_ptr, None);
            new_container_finish_step_pre_from_u(steps.snapshot_u(), caller_cpu_id, parent_process_ptr, current_thread_ptr, parent_container_ptr, child_container_ptr, child_process_ptr);
        };
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
    }
    let (new_thread_ptr, Tracked(new_thread_lock_perm)) = create_thread_from_staged_page_merged(
        krnl, thread_page_ptr, child_process_ptr, current_thread_ptr, child_container_ptr, child_scheduler_ptr, Tracked(&mut *lctx),
        Tracked(&thread_page_lock_perm), Tracked(&child_process_lock_perm), Tracked(&current_thread_lock_perm),
        Tracked(&child_scheduler_lock_perm), initial_regs,
    );
    krnl.wunlock_thread(new_thread_ptr, Tracked(&mut *lctx), Tracked(new_thread_lock_perm));
    krnl.wunlock_process(child_process_ptr, Tracked(&mut *lctx), Tracked(child_process_lock_perm));
    krnl.wunlock_pagetable(child_pagetable_ptr, Tracked(&mut *lctx), Tracked(child_pagetable_lock_perm));
    krnl.wunlock_pagetable(source_pagetable_ptr, Tracked(&mut *lctx), Tracked(source_pagetable_lock_perm));
    krnl.wunlock_page(page_ptr2page_index(thread_page_ptr), Tracked(&mut *lctx), Tracked(thread_page_lock_perm));
    krnl.wunlock_scheduler(child_scheduler_ptr, Tracked(&mut *lctx), Tracked(child_scheduler_lock_perm));
    krnl.set_thread_syscall_progress(current_thread_ptr, Ghost(None), Tracked(&*lctx), Tracked(&current_thread_lock_perm));
    krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
    proof { assert(krnl.prc_mp.spec_index(parent_process_ptr).view().owned_threads.view().len() != 0) by { reveal(process_thread_wf); }; }
    krnl.wunlock_process(parent_process_ptr, Tracked(&mut *lctx), Tracked(parent_process_lock_perm));
    proof {
        assert(!krnl.ctn_mp.spec_index(parent_container_ptr).view_ghost().owned_processes.view().is_empty() && !krnl.ctn_mp.spec_index(child_container_ptr).view_ghost().owned_processes.view().is_empty()) by {
            reveal(container_process_wf);
        };
    }
    krnl.wunlock_container(child_container_ptr, Tracked(&mut *lctx), Tracked(child_container_lock_perm));
    krnl.wunlock_container(parent_container_ptr, Tracked(&mut *lctx), Tracked(parent_container_lock_perm));
    krnl.wunlock_cpu(caller_cpu_id, Tracked(&mut *lctx), Tracked(caller_cpu_lock_perm));
    proof {
        assert(kernel_new_thread_fields(&steps.snapshot_k(), krnl, child_process_ptr, current_thread_ptr, child_container_ptr, new_thread_ptr, *initial_regs, None, None)) by {
            reveal(kernel_new_thread_fields); reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
        };
        assert(new_container_finish_step(steps.snapshot_u(), kernel_k_to_kernel_u(*krnl), caller_cpu_id)) by {
            reveal(kernel_new_thread_fields);
            kernel_cpu_thread_projection_at(&steps.snapshot_k(), caller_cpu_id, child_process_ptr, current_thread_ptr, None);
            kernel_new_thread_fields_and_parent_unlocks_implies_u_step(&steps.snapshot_k(), &*krnl, caller_cpu_id, child_process_ptr,
                current_thread_ptr, child_container_ptr, new_thread_ptr, *initial_regs, parent_process_ptr, parent_container_ptr, None);
            new_container_finish_step_from_u(steps.snapshot_u(), kernel_k_to_kernel_u(*krnl), caller_cpu_id, parent_process_ptr, current_thread_ptr, parent_container_ptr,
                child_container_ptr, child_process_ptr, new_thread_ptr, *initial_regs);
        };
        steps.end_kernel_step_new_thread(&*krnl, &*lctx, child_process_ptr, current_thread_ptr, child_container_ptr, new_thread_ptr, *initial_regs, None, None);
    }
    new_thread_ptr
}
}
