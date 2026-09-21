use vstd::prelude::*;
use crate::*;
#[cfg(feature = "split-crates")]
use veriflat_kernel_core::kernel_u_new_thread_changed;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::create_thread_from_staged_page::kernel_u_new_thread_changed;
use super::super::syscall_new_process_spec::kernel_u_new_process_shared;
use super::super::syscall_new_process_with_iommu_publish::publish_staged_process_with_iommu;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub(in super::super) fn commit_new_process_with_iommu_and_endpoint(
    krnl: &mut KernelK, source_range: &VaRange4K, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, container_ptr: RwLockContainerPtr,
    parent_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, scheduler_ptr: RwLockSchedulerPtr,
    allocator_ptr: RwLockPageAllocatorPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr,
    source_pagetable_ptr: RwLockPageTableRoot, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, pcid: Pcid,
    cpu_lock_perm: Tracked<LockPerm>, container_lock_perm: Tracked<LockPerm>,
    pcid_allocator_lock_perm: Tracked<LockPerm>, parent_lock_perm: Tracked<LockPerm>,
    current_thread_lock_perm: Tracked<LockPerm>, source_pagetable_lock_perm: Tracked<LockPerm>,
    endpoint_lock_perm: Tracked<LockPerm>, initial_regs: &Registers,
) -> (ret: (RwLockProcessPtr, RwLockPageTableRoot, RwLockThreadPtr))
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        edp_idx_valid(endpoint_index),
        source_range.wf(),
        source_range.len > 0,
        source_range.len <= (usize::MAX - 6) / 3,
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_lock_perm.view().state() is WriteLock,
        cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator == pcid_allocator_ptr,
        container_lock_perm.view().state() is WriteLock,
        container_lock_perm.view().thread_id() == old(lctx).thread_id(),
        container_lock_perm.view().lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
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
        parent_lock_perm.view().state() is WriteLock,
        parent_lock_perm.view().thread_id() == old(lctx).thread_id(),
        parent_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(parent_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == source_pagetable_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 6 + 3 * source_range.len,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.wf(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).ep_mp.dom().contains(endpoint_ptr),
        old(krnl).ep_mp.spec_index(endpoint_ptr).is_init(),
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
        !old(krnl).ep_mp.spec_index(endpoint_ptr).being_killed(),
        old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((current_thread_ptr, endpoint_index)),
        old(krnl).ctn_mp.dom().contains(old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container),
        {
            ||| old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container == container_ptr
            ||| old(krnl).ctn_mp.spec_index(old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container).view_ghost().subtree_set.view().contains(container_ptr)
        },
        endpoint_lock_perm.view().state() is WriteLock,
        endpoint_lock_perm.view().thread_id() == old(lctx).thread_id(),
        endpoint_lock_perm.view().lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, source_pagetable_ptr, old(krnl).pt_mp.spec_index(source_pagetable_ptr).view()),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().wf(),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Write),
        source_pagetable_lock_perm.view().state() is WriteLock,
        source_pagetable_lock_perm.view().thread_id() == old(lctx).thread_id(),
        source_pagetable_lock_perm.view().lock_id() == old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(source_range.start),
        share_mapping_4k_source_range_present(old(krnl), source_pagetable_ptr, source_range),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom() =~= set![container_ptr],
        old(lctx).process_lock_map().dom() =~= set![parent_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom() =~= set![pcid_allocator_ptr],
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr],
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        final(steps).steps.len() == old(steps).steps.len() + source_range.len + 2,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(krnl)),
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        kernel_u_create_process_with_iommu_changed(final(steps).steps.spec_index(old(steps).steps.len() as int).old_u, final(steps).steps.spec_index(old(steps).steps.len() as int).new_u, parent_ptr, ret.0),
        kernel_u_new_process_shared(final(steps).steps.spec_index(old(steps).steps.len() as int).new_u, final(steps).steps.spec_index((old(steps).steps.len() + source_range.len) as int).new_u, parent_ptr, ret.0, source_range),
        kernel_u_new_thread_changed(final(steps).steps.last().old_u, final(steps).steps.last().new_u, ret.0),
        final(krnl).prc_mp.dom().contains(ret.0),
        final(krnl).prc_mp.spec_index(ret.0).view().iommu_table == Some(ret.1),
        final(krnl).it_mp.dom().contains(ret.1),
        final(krnl).it_mp.spec_index(ret.1).view().is_empty(),
        final(krnl).thr_mp.dom().contains(ret.2),
        final(krnl).thr_mp.spec_index(ret.2).view().state is SCHEDULED,
        final(krnl).thr_mp.spec_index(ret.2).view().owning_proc == ret.0,
        final(krnl).thr_mp.spec_index(ret.2).view().owning_container == container_ptr,
        final(krnl).thr_mp.spec_index(ret.2).view().endpoint_descriptors.wf(),
        final(krnl).thr_mp.spec_index(ret.2).view().endpoint_descriptors.spec_index(0) == Some(endpoint_ptr),
{
    let tracked cpu_lock_perm = cpu_lock_perm.get();
    let tracked container_lock_perm = container_lock_perm.get();
    let tracked pcid_allocator_lock_perm = pcid_allocator_lock_perm.get();
    let tracked parent_lock_perm = parent_lock_perm.get();
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked source_pagetable_lock_perm = source_pagetable_lock_perm.get();
    let tracked endpoint_lock_perm = endpoint_lock_perm.get();
    let (process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr, Tracked(process_page_lock_perm), Tracked(pagetable_page_lock_perm), Tracked(l4_page_lock_perm), Tracked(iommu_table_page_lock_perm), Tracked(iommu_l4_page_lock_perm)) = allocate_new_process_with_iommu_pages(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), current_thread_ptr, container_ptr, cpu_id, Tracked(&current_thread_lock_perm),
    );
    proof {
        assert(!krnl.prc_mp.dom().contains(process_page_ptr)) by { page_ptr_roundtrip(); reveal(process_pages_wf); };
        assert(!krnl.pt_mp.dom().contains(pagetable_page_ptr)) by { page_ptr_roundtrip(); reveal(pagetable_pages_wf); };
        assert(!krnl.it_mp.dom().contains(iommu_table_page_ptr)) by { page_ptr_roundtrip(); reveal(iommu_table_pages_wf); };
    }
    let (child_ptr, target_pagetable_ptr, iommu_table_ptr, Tracked(child_lock_perm), Tracked(target_pagetable_lock_perm), Tracked(iommu_table_lock_perm)) = publish_staged_process_with_iommu(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, parent_ptr, current_thread_ptr,
        pcid_allocator_ptr, source_pagetable_ptr, pcid, process_page_ptr, pagetable_page_ptr, l4_page_ptr,
        iommu_table_page_ptr, iommu_l4_page_ptr, Tracked(process_page_lock_perm), Tracked(pagetable_page_lock_perm),
        Tracked(l4_page_lock_perm), Tracked(iommu_table_page_lock_perm), Tracked(iommu_l4_page_lock_perm),
        Tracked(&cpu_lock_perm), Tracked(&container_lock_perm), Tracked(pcid_allocator_lock_perm), Tracked(parent_lock_perm),
        Tracked(&current_thread_lock_perm), Tracked(&source_pagetable_lock_perm),
    );
    proof {
        assert(krnl.allc_4k_mp.dom().contains(allocator_ptr)) by { reveal(container_allocator_wf); };
        assert(share_mapping_4k_source_range_present(krnl, source_pagetable_ptr, source_range)) by { reveal(PageTable::wf_mapping_4k); reveal(mapped_4k_page_pagetable_wf); source_range.va_range_lemma(); };
    }
    proof {
        assert({
            &&& lctx.page_lock_map().dom().is_empty()
            &&& lctx.thread_lock_map().dom() == set![current_thread_ptr]
            &&& lctx.pagetable_lock_map().dom() == set![source_pagetable_ptr, target_pagetable_ptr]
            &&& lctx.held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR)
        });
        assert(lctx.thread_lock_map().dom() == set![current_thread_ptr, current_thread_ptr]);

        assert(share_mapping_4k_range_owner_compatible(krnl, source_pagetable_ptr, container_ptr, source_range)) by { source_range.va_range_lemma(); reveal(mapped_4k_page_pagetable_wf); reveal(container_process_page_pagetable_wf); reveal(container_page_owner_wf); reveal(process_thread_wf); reveal(container_subtree_set_exclusive); };
        assert(krnl.pt_mp.spec_index(target_pagetable_ptr).view().spec_mapping_4k_va_range_empty(source_range.start, source_range.view().spec_index((source_range.len - 1) as int))) by { reveal(PageTable::spec_mapping_4k_va_range_empty); };
    }
    share_mapping_4k_build_and_share(
        krnl, source_range, source_range, allocator_ptr, current_thread_ptr, current_thread_ptr, child_ptr, container_ptr,
        cpu_id, source_pagetable_ptr, target_pagetable_ptr, Tracked(&mut *lctx), Tracked(&mut *steps),
        Tracked(&current_thread_lock_perm), Tracked(&current_thread_lock_perm),
        Tracked(&source_pagetable_lock_perm), Tracked(&target_pagetable_lock_perm),
    );
    proof {
        assert(kernel_u_new_process_shared(steps.steps.spec_index(old(steps).steps.len() as int).new_u, steps.steps.last().new_u, parent_ptr, child_ptr, source_range)) by {
            reveal(kernel_k_to_kernel_u);
            reveal(process_pagetable_match);
        };
        assert(krnl.sched_mp.dom().contains(scheduler_ptr) && krnl.sched_mp.lock_id_by_key(scheduler_ptr).major == SCHEDULER_LOCK_MAJOR) by { reveal(container_scheduler_wf); reveal(scheduler_perms_wf); };
    }
    let ghost before_scheduler_lock = *krnl;
    let Tracked(scheduler_lock_perm) = krnl.wlock_scheduler(scheduler_ptr, Tracked(&mut *lctx));
    proof {
        assert(steps.snap_shot == kernel_k_to_kernel_u(*krnl)) by {
            kernel_no_change_to_user_view_fields_imply_kernel_u_eq(&before_scheduler_lock, krnl);
        };
        assert(!krnl.prc_mp.spec_index(child_ptr).view().zombie) by { reveal(process_pagetable_match); };
        assert(lctx.holds_no_allocator_locks(PageSize::SZ4k) && lctx.holds_no_allocator_locks(PageSize::SZ2m) && lctx.holds_no_allocator_locks(PageSize::SZ1g)) by { reveal(LocalContext::holds_no_allocator_locks); };
    }
    proof {
        assert({
            &&& krnl.ep_mp.dom().contains(endpoint_ptr)
            &&& krnl.ep_mp.spec_index(endpoint_ptr).is_init()
            &&& typed_lock_map_contains_mode(lctx.endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write)
            &&& !krnl.ep_mp.spec_index(endpoint_ptr).being_killed()
            &&& krnl.ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((current_thread_ptr, endpoint_index))
            &&& endpoint_lock_perm.lock_id() == krnl.ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id
        }) by { reveal(endpoint_perms_wf); };
        assert(krnl.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.wf() && krnl.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr)) by { reveal(thread_perms_wf); reveal(thread_endpoint_ref_counter_wf); };
        assert(krnl.ctn_mp.dom().contains(krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container)) by { reveal(container_endpoint_wf); };
        assert({
            ||| krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container == container_ptr
            ||| krnl.ctn_mp.spec_index(krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container).view_ghost().subtree_set.view().contains(container_ptr)
        }) by { reveal(container_thread_endpoint_wf); };
        assert({
            &&& krnl.prc_mp.spec_index(child_ptr).view().iommu_table == Some(iommu_table_ptr)
            &&& krnl.it_mp.dom().contains(iommu_table_ptr)
            &&& typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write)
            &&& krnl.it_mp.spec_index(iommu_table_ptr).view().is_empty()
            &&& iommu_table_lock_perm.lock_id() == krnl.it_mp.spec_index(iommu_table_ptr).locking_thread()->Write_lock_id
        }) by { reveal(process_iommu_table_match); };
    }
    let new_thread_ptr = create_initial_thread_with_iommu_endpoint_and_finish_new_process(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, child_ptr, current_thread_ptr, scheduler_ptr,
        endpoint_ptr, endpoint_index, source_pagetable_ptr, target_pagetable_ptr, iommu_table_ptr,
        Tracked(cpu_lock_perm), Tracked(container_lock_perm), Tracked(child_lock_perm), Tracked(current_thread_lock_perm),
        Tracked(scheduler_lock_perm), Tracked(endpoint_lock_perm), Tracked(source_pagetable_lock_perm),
        Tracked(target_pagetable_lock_perm), Tracked(iommu_table_lock_perm), initial_regs,
    );
    (child_ptr, iommu_table_ptr, new_thread_ptr)
}
}
