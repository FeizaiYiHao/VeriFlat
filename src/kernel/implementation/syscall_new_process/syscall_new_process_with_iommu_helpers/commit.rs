use vstd::prelude::*;
use crate::*;
#[cfg(feature = "split-crates")]
use veriflat_kernel_core::kernel_u_new_thread_changed;
#[cfg(not(feature = "split-crates"))]
#[cfg(verus_keep_ghost)]
use crate::kernel::implementation::create_thread_from_staged_page::kernel_u_new_thread_changed;
use super::super::syscall_new_process_spec::*;
use super::super::syscall_new_process_trace::*;
use super::super::syscall_new_process_with_iommu_publish::publish_staged_process_with_iommu;
use super::*;
use super::super::syscall_new_process_enter::enter_new_process_commit;
use super::super::syscall_new_process_share_finish::share_and_finish_new_process;

verus! {
#[verifier::spinoff_prover]
pub(in super::super) fn commit_new_process_with_iommu_and_endpoint(
    krnl: &mut KernelK, source_range: &VaRange4K, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    container_ptr: RwLockContainerPtr, parent_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, scheduler_ptr: RwLockSchedulerPtr,
    allocator_ptr: RwLockPageAllocatorPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, source_pagetable_ptr: RwLockPageTableRoot,
    endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, pcid: Pcid, cpu_lock_perm: Tracked<LockPerm>,
    pcid_allocator_lock_perm: Tracked<LockPerm>, parent_lock_perm: Tracked<LockPerm>, current_thread_lock_perm: Tracked<LockPerm>,
    source_pagetable_lock_perm: Tracked<LockPerm>, endpoint_lock_perm: Tracked<LockPerm>, initial_regs: &Registers,
) -> (ret: (RwLockProcessPtr, RwLockPageTableRoot, RwLockThreadPtr))
    requires
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, prc_mp: old(krnl).prc_mp, thr_mp: old(krnl).thr_mp, ep_mp: old(krnl).ep_mp, pt_mp: old(krnl).pt_mp, pcid_allc_mp: old(krnl).pcid_allc_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(krnl).prc_mp.unchanged_except(&old(steps).snapshot_k().prc_mp, parent_ptr),
        old(krnl).thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, current_thread_ptr),
        old(krnl).pt_mp.unchanged_except(&old(steps).snapshot_k().pt_mp, source_pagetable_ptr),
        old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        old(steps).snapshot_k().prc_mp.spec_index(parent_ptr).locking_thread() is None,
        old(steps).snapshot_k().thr_mp.spec_index(current_thread_ptr).locking_thread() is None,
        old(steps).snapshot_k().pt_mp.spec_index(source_pagetable_ptr).locking_thread() is None,
        old(steps).snapshot_k().ep_mp.spec_index(endpoint_ptr).locking_thread() is None,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state == CpuState::Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        old(krnl).ep_mp.unchanged_except(&old(steps).snapshot_k().ep_mp, endpoint_ptr),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        edp_idx_valid(endpoint_index),
        source_range.wf(),
        source_range.len > 0,
        source_range.len <= (usize::MAX - 6) / 3,
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        old(krnl).irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
        old(krnl).irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
        old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
        old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_lock_perm.view().state() is WriteLock,
        cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == allocator_ptr,
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
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 6 + 3 * source_range.len,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
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
        endpoint_lock_perm.view().state() is WriteLock,
        endpoint_lock_perm.view().thread_id() == old(lctx).thread_id(),
        endpoint_lock_perm.view().lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, source_pagetable_ptr, old(krnl).pt_mp.spec_index(source_pagetable_ptr).view()),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().leaves_present(),
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
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom() =~= set![parent_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom() =~= set![pcid_allocator_ptr],
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr],
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        new_process_enter_step_pre(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, *source_range, Some(endpoint_index), true),
    ensures
        old(steps).view().len() as int + source_range.len as int + 3 <= final(steps).view().len() as int <= old(steps).view().len() as int + 4 * source_range.len as int + 3,
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        new_process_commit_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id,
            *source_range, *initial_regs, Some(endpoint_index), true),
        final(steps).view().last().new_u == kernel_k_to_kernel_u(*final(krnl)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        old(steps).nonlock_view().len() as int + source_range.len as int + 3 <= final(steps).nonlock_view().len() as int,
        final(steps).nonlock_view().len() as int <= old(steps).nonlock_view().len() as int + 4 * source_range.len as int + 3,
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).nonlock_view().last().new_u == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        kernel_u_new_thread_changed(final(steps).nonlock_view().last().old_u, final(steps).nonlock_view().last().new_u, ret.0, current_thread_ptr, container_ptr, cpu_id, ret.2, *initial_regs, Some(endpoint_ptr), None),
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
    let tracked pcid_allocator_lock_perm = pcid_allocator_lock_perm.get();
    let tracked parent_lock_perm = parent_lock_perm.get();
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked source_pagetable_lock_perm = source_pagetable_lock_perm.get();
    let tracked endpoint_lock_perm = endpoint_lock_perm.get();
    let ghost entry_u = kernel_k_to_kernel_u(old(steps).snapshot_k());
    enter_new_process_commit(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, parent_ptr, current_thread_ptr, pcid_allocator_ptr, source_pagetable_ptr, Some(endpoint_ptr), endpoint_index,
        source_range, Tracked(&current_thread_lock_perm), Ghost(*initial_regs), Ghost(true),
    );
    proof { assert(krnl.ctn_mp.dom().contains(container_ptr)) by { container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, current_thread_ptr); }; }
    let (process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr, Tracked(process_page_lock_perm), Tracked(pagetable_page_lock_perm), Tracked(l4_page_lock_perm),
        Tracked(iommu_table_page_lock_perm), Tracked(iommu_l4_page_lock_perm)) = allocate_new_process_with_iommu_pages(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), current_thread_ptr, container_ptr, cpu_id, Tracked(&current_thread_lock_perm),
    );
    proof {
        assert(!krnl.prc_mp.dom().contains(process_page_ptr)) by { page_ptr_roundtrip(); if krnl.prc_mp.dom().contains(process_page_ptr) { process_pages_wf_process_entry_at(krnl.pg_arr, krnl.prc_mp, process_page_ptr); } };
        assert(!krnl.pt_mp.dom().contains(pagetable_page_ptr)) by { page_ptr_roundtrip(); if krnl.pt_mp.dom().contains(pagetable_page_ptr) { pagetable_pages_wf_root_entry_at(krnl.pt_mp, krnl.pg_arr, pagetable_page_ptr); } };
        assert(!krnl.it_mp.dom().contains(iommu_table_page_ptr)) by { page_ptr_roundtrip(); if krnl.it_mp.dom().contains(iommu_table_page_ptr) { pagetable_pages_wf_root_entry_at(krnl.it_mp, krnl.pg_arr, iommu_table_page_ptr); } };
    }
    let ghost publish_before = steps.view();
    let (child_ptr, target_pagetable_ptr, iommu_table_ptr, Tracked(child_lock_perm), Tracked(target_pagetable_lock_perm), Tracked(iommu_table_lock_perm)) = publish_staged_process_with_iommu(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, parent_ptr, current_thread_ptr, pcid_allocator_ptr,
        source_pagetable_ptr, source_range, pcid, process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr,
        Tracked(process_page_lock_perm), Tracked(pagetable_page_lock_perm), Tracked(l4_page_lock_perm), Tracked(iommu_table_page_lock_perm),
        Tracked(iommu_l4_page_lock_perm), Tracked(&cpu_lock_perm), Tracked(pcid_allocator_lock_perm),
        Tracked(parent_lock_perm), Tracked(&current_thread_lock_perm), Tracked(&source_pagetable_lock_perm), Ghost(*initial_regs), Ghost(Some(endpoint_index)),
    );
    proof {
        assert(new_process_trace_after_publish(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), entry_u, cpu_id,
            *source_range, *initial_regs, Some(endpoint_index), true)) by {
            new_process_trace_publish_step(&*steps, publish_before, old(steps).view().len() as int, entry_u, cpu_id, *source_range, *initial_regs, Some(endpoint_index), true);
        };
        assert(share_mapping_4k_source_range_present(krnl, source_pagetable_ptr, source_range)) by { share_mapping_4k_source_range_present_from_wf(krnl, source_pagetable_ptr, source_range); source_range.va_range_lemma(); };
    }
    let new_thread_ptr = share_and_finish_new_process(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, source_range, container_ptr, parent_ptr, child_ptr, current_thread_ptr, scheduler_ptr, allocator_ptr,
        source_pagetable_ptr, target_pagetable_ptr, Some(iommu_table_ptr), Some(endpoint_ptr), endpoint_index, Tracked(cpu_lock_perm), Tracked(child_lock_perm),
        Tracked(current_thread_lock_perm), Tracked(Some(endpoint_lock_perm)), Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm),
        Tracked(Some(iommu_table_lock_perm)), initial_regs, Ghost(old(steps).view().len() as int), Ghost(entry_u),
    );
    (child_ptr, iommu_table_ptr, new_thread_ptr)
}
}
