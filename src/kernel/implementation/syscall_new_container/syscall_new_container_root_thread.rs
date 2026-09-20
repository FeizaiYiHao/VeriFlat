use vstd::prelude::*;
use crate::*;
#[cfg(not(feature = "split-crates"))]
use crate::implementation::create_thread_from_staged_page::
    create_thread_from_staged_page_merged;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub(super) fn create_root_thread_and_finish_new_container(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    caller_cpu_id: CpuId, parent_container_ptr: RwLockContainerPtr, parent_process_ptr: RwLockProcessPtr,
    current_thread_ptr: RwLockThreadPtr, source_pagetable_ptr: RwLockPageTableRoot,
    child_container_ptr: RwLockContainerPtr, child_process_ptr: RwLockProcessPtr,
    child_pagetable_ptr: RwLockPageTableRoot, child_scheduler_ptr: RwLockSchedulerPtr,
    child_allocator_4k_ptr: RwLockPageAllocatorPtr, thread_page_ptr: PagePtr,
    caller_cpu_lock_perm: Tracked<LockPerm>, parent_container_lock_perm: Tracked<LockPerm>,
    parent_process_lock_perm: Tracked<LockPerm>, current_thread_lock_perm: Tracked<LockPerm>,
    source_pagetable_lock_perm: Tracked<LockPerm>, child_container_lock_perm: Tracked<LockPerm>,
    child_process_lock_perm: Tracked<LockPerm>, child_pagetable_lock_perm: Tracked<LockPerm>,
    child_scheduler_lock_perm: Tracked<LockPerm>, thread_page_lock_perm: Tracked<LockPerm>, initial_regs: &Registers,
) -> (new_thread_ptr: RwLockThreadPtr)
    requires
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, source_pagetable_ptr, old(krnl).pt_mp.spec_index(source_pagetable_ptr).view()),
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, child_pagetable_ptr, old(krnl).pt_mp.spec_index(child_pagetable_ptr).view()),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Release,
        index_valid(NUM_CPUS, caller_cpu_id),
        old(krnl).cpu_published[caller_cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_pcid),
        page_ptr_valid(thread_page_ptr),
        parent_container_ptr != child_container_ptr,
        parent_process_ptr != child_process_ptr,
        source_pagetable_ptr != child_pagetable_ptr,
        old(lctx).page_lock_map().dom() =~= set![page_ptr2page_index(thread_page_ptr)],
        old(lctx).cpu_lock_map().dom() =~= set![caller_cpu_id],
        old(lctx).container_lock_map().dom() =~= set![parent_container_ptr, child_container_ptr],
        old(lctx).process_lock_map().dom() =~= set![parent_process_ptr, child_process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom() =~= set![child_scheduler_ptr],
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr, child_pagetable_ptr],
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), caller_cpu_id, TypedLockMode::Write),
        !old(krnl).cpu_arr.spec_index(caller_cpu_id)
            .view().being_killed(),
        caller_cpu_lock_perm.view().state() is WriteLock,
        caller_cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        caller_cpu_lock_perm.view().lock_id()
            == old(krnl).cpu_arr.spec_index(caller_cpu_id)
                .view().locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(parent_container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), parent_container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        parent_container_lock_perm.view().state() is WriteLock,
        parent_container_lock_perm.view().thread_id()
            == old(lctx).thread_id(),
        parent_container_lock_perm.view().lock_id()
            == old(krnl).ctn_mp.spec_index(parent_container_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(parent_process_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), parent_process_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(parent_process_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(parent_process_ptr)
            .view_rodata().view().owning_container
            == parent_container_ptr,
        parent_process_lock_perm.view().state() is WriteLock,
        parent_process_lock_perm.view().thread_id() == old(lctx).thread_id(),
        parent_process_lock_perm.view().lock_id()
            == old(krnl).prc_mp.spec_index(parent_process_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().owning_container == parent_container_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().owning_proc == parent_process_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().proc_pagetable_ptr == source_pagetable_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().state is RUNNING,
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().temp_alloc_cache_4k.view() == set![thread_page_ptr],
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().temp_alloc_cache_2m.view().is_empty(),
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().temp_alloc_cache_1g.view().is_empty(),
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().quota_4k >= 1,
        old(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().free_quota_pending_clean(),
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id()
            == old(krnl).thr_mp.spec_index(current_thread_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Write),
        source_pagetable_lock_perm.view().state() is WriteLock,
        source_pagetable_lock_perm.view().thread_id()
            == old(lctx).thread_id(),
        source_pagetable_lock_perm.view().lock_id()
            == old(krnl).pt_mp.spec_index(source_pagetable_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(child_container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), child_container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(child_container_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(child_container_ptr)
            .view_rodata().view().parent == Some(parent_container_ptr),
        old(krnl).ctn_mp.spec_index(child_container_ptr)
            .view_rodata().view().scheduler == child_scheduler_ptr,
        old(krnl).ctn_mp.spec_index(child_container_ptr)
            .view_rodata().view().allocator_ptr_4k == child_allocator_4k_ptr,
        old(krnl).allc_4k_mp.dom().contains(child_allocator_4k_ptr),
        child_container_lock_perm.view().state() is WriteLock,
        child_container_lock_perm.view().thread_id()
            == old(lctx).thread_id(),
        child_container_lock_perm.view().lock_id()
            == old(krnl).ctn_mp.spec_index(child_container_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(child_process_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), child_process_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(child_process_ptr).being_killed(),
        !old(krnl).prc_mp.spec_index(child_process_ptr).view().zombie,
        old(krnl).prc_mp.spec_index(child_process_ptr)
            .view_rodata().view().owning_container == child_container_ptr,
        old(krnl).prc_mp.spec_index(child_process_ptr)
            .view_rodata().view().pagetable == child_pagetable_ptr,
        child_process_lock_perm.view().state() is WriteLock,
        child_process_lock_perm.view().thread_id() == old(lctx).thread_id(),
        child_process_lock_perm.view().lock_id()
            == old(krnl).prc_mp.spec_index(child_process_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(child_pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), child_pagetable_ptr, TypedLockMode::Write),
        child_pagetable_lock_perm.view().state() is WriteLock,
        child_pagetable_lock_perm.view().thread_id()
            == old(lctx).thread_id(),
        child_pagetable_lock_perm.view().lock_id()
            == old(krnl).pt_mp.spec_index(child_pagetable_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).sched_mp.dom().contains(child_scheduler_ptr),
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), child_scheduler_ptr, TypedLockMode::Write),
        !old(krnl).sched_mp.spec_index(child_scheduler_ptr).being_killed(),
        child_scheduler_lock_perm.view().state() is WriteLock,
        child_scheduler_lock_perm.view().thread_id()
            == old(lctx).thread_id(),
        child_scheduler_lock_perm.view().lock_id()
            == old(krnl).sched_mp.spec_index(child_scheduler_ptr)
                .locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(thread_page_ptr), TypedLockMode::Write),
        !old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page_ptr))
            .view().being_killed(),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page_ptr))
            .view().view().state
            == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page_ptr))
            .view().view().owning_container == parent_container_ptr,
        old(krnl).ctn_mp.spec_index(parent_container_ptr)
            .view().owned_pages.view().contains(thread_page_ptr),
        old(krnl).ctn_mp.spec_index(parent_container_ptr)
            .view().owned_processes.view().contains(parent_process_ptr),
        old(krnl).ctn_mp.spec_index(child_container_ptr)
            .view().owned_processes.view().contains(child_process_ptr),
        thread_page_lock_perm.view().state() is WriteLock,
        thread_page_lock_perm.view().thread_id() == old(lctx).thread_id(),
        thread_page_lock_perm.view().lock_id()
            == old(krnl).pg_arr.spec_index(
                page_ptr2page_index(thread_page_ptr),
            ).view().locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(steps).steps == record_user_view_change(
            old(steps).steps,
            old(steps).snap_shot,
            kernel_k_to_kernel_u(*final(krnl)),
        ),
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        new_thread_ptr == thread_page_ptr,
        final(krnl).thr_mp.dom().contains(new_thread_ptr),
        final(krnl).thr_mp.spec_index(new_thread_ptr)
            .view().state is SCHEDULED,
        final(krnl).thr_mp.spec_index(new_thread_ptr)
            .view().owning_container == child_container_ptr,
        final(krnl).thr_mp.spec_index(new_thread_ptr)
            .view().owning_proc == child_process_ptr,
        final(krnl).ctn_mp.dom().contains(child_container_ptr),
        final(krnl).ctn_mp.spec_index(child_container_ptr)
            .view_rodata().view().parent
            == old(krnl).ctn_mp.spec_index(child_container_ptr)
                .view_rodata().view().parent,
        final(krnl).ctn_mp.spec_index(child_container_ptr)
            .view_rodata().view().allocator_ptr_4k == child_allocator_4k_ptr,
        final(krnl).prc_mp.dom().contains(child_process_ptr),
        final(krnl).prc_mp.spec_index(child_process_ptr)
            .view_rodata().view().owning_container
            == old(krnl).prc_mp.spec_index(child_process_ptr)
                .view_rodata().view().owning_container,
        final(krnl).prc_mp.spec_index(child_process_ptr)
            .view().quota_4k
            == old(krnl).prc_mp.spec_index(child_process_ptr)
                .view().quota_4k,
        final(krnl).allc_4k_mp.dom().contains(child_allocator_4k_ptr),
        final(krnl).allc_4k_mp.spec_index(child_allocator_4k_ptr)
            == old(krnl).allc_4k_mp.spec_index(child_allocator_4k_ptr),
        final(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(current_thread_ptr)
            .view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k
            == old(krnl).thr_mp.spec_index(current_thread_ptr)
                .view().quota_4k - 1,
{
    let tracked caller_cpu_lock_perm = caller_cpu_lock_perm.get();
    let tracked parent_container_lock_perm = parent_container_lock_perm.get();
    let tracked parent_process_lock_perm = parent_process_lock_perm.get();
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked source_pagetable_lock_perm = source_pagetable_lock_perm.get();
    let tracked child_container_lock_perm = child_container_lock_perm.get();
    let tracked child_process_lock_perm = child_process_lock_perm.get();
    let tracked child_pagetable_lock_perm = child_pagetable_lock_perm.get();
    let tracked child_scheduler_lock_perm = child_scheduler_lock_perm.get();
    let tracked thread_page_lock_perm = thread_page_lock_perm.get();
    let ghost caller_quota_4k = krnl.thr_mp
        .spec_index(current_thread_ptr).view().quota_4k;
    transfer_staged_thread_page_to_child(
        krnl,
        Tracked(&mut *lctx),
        thread_page_ptr,
        current_thread_ptr,
        parent_container_ptr,
        child_container_ptr,
        Tracked(&thread_page_lock_perm),
        Tracked(&parent_container_lock_perm),
        Tracked(&child_container_lock_perm),
    );
    let (
        new_thread_ptr,
        Tracked(new_thread_lock_perm),
    ) = create_thread_from_staged_page_merged(
        krnl,
        thread_page_ptr,
        child_process_ptr,
        current_thread_ptr,
        child_container_ptr,
        child_scheduler_ptr,
        Tracked(&mut *lctx),
        Tracked(&thread_page_lock_perm),
        Tracked(&child_process_lock_perm),
        Tracked(&current_thread_lock_perm),
        Tracked(&child_scheduler_lock_perm),
        initial_regs,
    );

    krnl.wunlock_thread(
        new_thread_ptr,
        Tracked(&mut *lctx),
        Tracked(new_thread_lock_perm),
    );
    krnl.wunlock_process(
        child_process_ptr,
        Tracked(&mut *lctx),
        Tracked(child_process_lock_perm),
    );
    krnl.wunlock_pagetable(
        child_pagetable_ptr,
        Tracked(&mut *lctx),
        Tracked(child_pagetable_lock_perm),
    );
    krnl.wunlock_pagetable(
        source_pagetable_ptr,
        Tracked(&mut *lctx),
        Tracked(source_pagetable_lock_perm),
    );
    krnl.wunlock_page(
        page_ptr2page_index(thread_page_ptr),
        Tracked(&mut *lctx),
        Tracked(thread_page_lock_perm),
    );
    krnl.wunlock_scheduler(
        child_scheduler_ptr,
        Tracked(&mut *lctx),
        Tracked(child_scheduler_lock_perm),
    );
    krnl.wunlock_thread(
        current_thread_ptr,
        Tracked(&mut *lctx),
        Tracked(current_thread_lock_perm),
    );
    proof {
        assert(
            krnl.thr_mp.spec_index(current_thread_ptr).view().quota_4k
                == caller_quota_4k - 1
        ) by {
            reveal(wunlock_ensures);
        };
        assert(
            krnl.prc_mp.spec_index(parent_process_ptr)
                .view().owned_threads.view().len() != 0
        ) by {
            reveal(process_thread_wf);
        };
    }
    krnl.wunlock_process(
        parent_process_ptr,
        Tracked(&mut *lctx),
        Tracked(parent_process_lock_perm),
    );
    proof {
        assert({
            &&& krnl.ctn_mp.spec_index(child_container_ptr)
                .view().owned_processes.view().contains(child_process_ptr)
            &&& krnl.ctn_mp.spec_index(parent_container_ptr)
                .view().owned_processes.view().contains(parent_process_ptr)
            &&& !krnl.ctn_mp.spec_index(child_container_ptr)
                .view().owned_processes.view().is_empty()
            &&& !krnl.ctn_mp.spec_index(parent_container_ptr)
                .view().owned_processes.view().is_empty()
        }) by {
            reveal(container_process_wf);
        };
    }
    krnl.wunlock_container(
        child_container_ptr,
        Tracked(&mut *lctx),
        Tracked(child_container_lock_perm),
    );
    krnl.wunlock_container(
        parent_container_ptr,
        Tracked(&mut *lctx),
        Tracked(parent_container_lock_perm),
    );
    krnl.wunlock_cpu(
        caller_cpu_id,
        Tracked(&mut *lctx),
        Tracked(caller_cpu_lock_perm),
    );
    proof {
        assert(lctx.no_locks_held()) by {
            reveal(LocalContext::no_locks_held);
            reveal(LocalContext::holds_no_allocator_locks);
        };
        steps.end_kernel_step(&*krnl, &*lctx);
    }
    new_thread_ptr
}


}
