use vstd::prelude::*;
use crate::*;
use super::syscall_new_container_spec::*;
use super::syscall_new_container_trace::*;
use super::syscall_new_container_share::{create_new_container_root_thread_and_finish, share_new_container_range};

verus! {
/// Shares the parent's range into the published child and finishes the call: the share steps and the finish step
/// after the partial trace that starts at `start`.
pub(super) fn commit_new_container_share_and_finish(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, caller_cpu_id: CpuId,
    source_range: &VaRange4K, parent_container_ptr: RwLockContainerPtr, child_container_ptr: RwLockContainerPtr, parent_process_ptr: RwLockProcessPtr,
    child_process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, source_pagetable_ptr: RwLockPageTableRoot,
    child_pagetable_ptr: RwLockPageTableRoot, child_allocator_4k_ptr: RwLockPageAllocatorPtr, child_scheduler_ptr: RwLockSchedulerPtr,
    thread_page_ptr: PagePtr, endpoint: Option<RwLockEndpointPtr>, endpoint_index: EndpointIdx, caller_cpu_lock_perm: Tracked<LockPerm>,
    parent_container_lock_perm: Tracked<LockPerm>, child_container_lock_perm: Tracked<LockPerm>, parent_process_lock_perm: Tracked<LockPerm>,
    child_process_lock_perm: Tracked<LockPerm>, current_thread_lock_perm: Tracked<LockPerm>, source_pagetable_lock_perm: Tracked<LockPerm>,
    child_pagetable_lock_perm: Tracked<LockPerm>, thread_page_lock_perm: Tracked<LockPerm>, endpoint_lock_perm: Tracked<Option<LockPerm>>,
    initial_regs: &Registers, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(record): Ghost<NewContainerProgress>,
    Tracked(source_window_perms): Tracked<Map<WindowVa, LockPerm>>, Ghost(entry_k): Ghost<KernelK>, Ghost(entry_lctx): Ghost<LocalContext>,
) -> (new_thread_ptr: RwLockThreadPtr)
    requires
        0 <= start <= old(steps).view().len(),
        new_container_trace_after_publish(old(steps).view().subrange(start, old(steps).view().len() as int), pre, caller_cpu_id, *source_range, record.funding,
            record.process_quota, record.transfer_cpu, *initial_regs, record.endpoint_index),
        record.range == *source_range,
        record.regs == *initial_regs,
        record.endpoint_index == if endpoint is Some { Some(endpoint_index) } else { None },
        old(steps).snapshot_k() == *old(krnl),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        index_valid(NUM_CPUS, caller_cpu_id),
        caller_cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_op.view().view()[caller_cpu_id as int] is InStep,
        old(krnl).cpu_hw_cr3_pcid[caller_cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_pcid),
        page_ptr_valid(thread_page_ptr),
        parent_container_ptr != child_container_ptr,
        source_pagetable_ptr != child_pagetable_ptr,
        old(lctx).page_lock_map().dom() =~= set![page_ptr2page_index(thread_page_ptr)],
        old(lctx).cpu_lock_map().dom() =~= set![caller_cpu_id],
        old(lctx).container_lock_map().dom() =~= set![parent_container_ptr, child_container_ptr],
        old(lctx).process_lock_map().dom() =~= set![parent_process_ptr, child_process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        endpoint is None ==> old(lctx).endpoint_lock_map().dom().is_empty(),
        endpoint is Some ==> {
            let endpoint_ptr = endpoint->Some_0;
            &&& edp_idx_valid(endpoint_index)
            &&& old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr]
            &&& old(krnl).ep_mp.dom().contains(endpoint_ptr)
            &&& old(krnl).ep_mp.spec_index(endpoint_ptr).is_init()
            &&& typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write)
            &&& !old(krnl).ep_mp.spec_index(endpoint_ptr).being_killed()
            &&& old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((current_thread_ptr, endpoint_index))
            &&& endpoint_lock_perm.view() is Some
            &&& endpoint_lock_perm.view()->Some_0.state() is WriteLock
            &&& endpoint_lock_perm.view()->Some_0.thread_id() == old(lctx).thread_id()
            &&& endpoint_lock_perm.view()->Some_0.lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id
        },
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr, child_pagetable_ptr],
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), caller_cpu_id, TypedLockMode::Write),
        !old(krnl).cpu_arr.spec_index(caller_cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(caller_cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        caller_cpu_lock_perm.view().state() is WriteLock,
        caller_cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        caller_cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(caller_cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(thread_page_ptr), TypedLockMode::Write),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page_ptr)).view().view().owning_container == child_container_ptr,
        thread_page_lock_perm.view().state() is WriteLock,
        thread_page_lock_perm.view().thread_id() == old(lctx).thread_id(),
        thread_page_lock_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page_ptr)).view().locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(parent_container_ptr),
        old(krnl).ctn_mp.dom().contains(child_container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), parent_container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), child_container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        !old(krnl).ctn_mp.spec_index(child_container_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata().view().parent == Some(parent_container_ptr),
        old(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata().view().allocator_ptr_4k == child_allocator_4k_ptr,
        old(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata().view().scheduler == child_scheduler_ptr,
        old(krnl).ctn_mp.spec_index(child_container_ptr).view_ghost().uppertree_seq.view() == old(krnl).ctn_mp.spec_index(parent_container_ptr).view_ghost().uppertree_seq.view().push(parent_container_ptr),
        old(krnl).ctn_mp.spec_index(child_container_ptr).view().root_process == child_process_ptr,
        parent_container_lock_perm.view().state() is WriteLock,
        parent_container_lock_perm.view().thread_id() == old(lctx).thread_id(),
        parent_container_lock_perm.view().lock_id() == old(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        child_container_lock_perm.view().state() is WriteLock,
        child_container_lock_perm.view().thread_id() == old(lctx).thread_id(),
        child_container_lock_perm.view().lock_id() == old(krnl).ctn_mp.spec_index(child_container_ptr).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(parent_process_ptr),
        old(krnl).prc_mp.dom().contains(child_process_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), parent_process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), child_process_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(parent_process_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(parent_process_ptr).view().state.view() is Running || old(krnl).prc_mp.spec_index(parent_process_ptr).view().state.view() is Zombie,
        old(krnl).prc_mp.spec_index(parent_process_ptr).view_rodata().view().owning_container == parent_container_ptr,
        !old(krnl).prc_mp.spec_index(child_process_ptr).being_killed(),
        !old(krnl).prc_mp.spec_index(child_process_ptr).view().zombie,
        old(krnl).prc_mp.spec_index(child_process_ptr).view().state.view() is Creating,
        old(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().owning_container == child_container_ptr,
        old(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().pagetable == child_pagetable_ptr,
        old(krnl).prc_mp.spec_index(child_process_ptr).view().iommu_table is None,
        parent_process_lock_perm.view().state() is WriteLock,
        parent_process_lock_perm.view().thread_id() == old(lctx).thread_id(),
        parent_process_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(parent_process_ptr).locking_thread()->Write_lock_id,
        child_process_lock_perm.view().state() is WriteLock,
        child_process_lock_perm.view().thread_id() == old(lctx).thread_id(),
        child_process_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(child_process_ptr).locking_thread()->Write_lock_id,
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
        !old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Share4k {
            source_range: *source_range, target_range: *source_range, shared: 0,
            origin: Share4kOrigin::NewContainer(NewContainerProgress { child_container: Some(child_container_ptr), ..record }),
        }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 1 + 3 * source_range.len,
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        old(krnl).pt_mp.dom().contains(child_pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Read),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), child_pagetable_ptr, TypedLockMode::Write),
        source_pagetable_lock_perm.view().state() is ReadLock,
        source_pagetable_lock_perm.view().thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread() is Read,
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), source_pagetable_lock_perm.view().lock_id()),
        child_pagetable_lock_perm.view().state() is WriteLock,
        child_pagetable_lock_perm.view().thread_id() == old(lctx).thread_id(),
        child_pagetable_lock_perm.view().lock_id() == old(krnl).pt_mp.spec_index(child_pagetable_ptr).locking_thread()->Write_lock_id,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), child_pagetable_ptr).is_empty(),
        source_range.wf(),
        source_range.len > 0,
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(source_range.start),
        entry_k.pt_mp.dom().contains(source_pagetable_ptr),
        pagetable_c(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).wf(),
        entry_k.pt_mp.spec_index(source_pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(source_range.start),
        forall|j: int| #![trigger source_range.view().spec_index(j)] 0 <= j < source_range.len ==> {
            &&& pagetable_c(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).mapping_4k().dom().contains(source_range.view().spec_index(j))
            &&& pagetable_c(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).mapping_4k().spec_index(source_range.view().spec_index(j)).present
        },
        forall|w: WindowVa| #![trigger va_range_2m_windows(*source_range).contains(w)]
            va_range_2m_windows(*source_range).contains(w) && pagetable_c(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> source_window_perms.dom().contains(w),
        forall|w: WindowVa| #![trigger source_window_perms.dom().contains(w)] source_window_perms.dom().contains(w) ==> {
            &&& va_range_2m_windows(*source_range).contains(w)
            &&& pagetable_c(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
            &&& typed_lock_map_contains_mode(entry_lctx.pagetable_window_lock_map(), (source_pagetable_ptr, w), TypedLockMode::Write)
            &&& source_window_perms.index(w).state() is WriteLock
            &&& source_window_perms.index(w).thread_id() == entry_lctx.thread_id()
            &&& pagetable_c(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).lower.l2_lock_of(pagetable_c(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                .lock_perm_match(spec_v2l2index(w.va), &source_window_perms.index(w))
            &&& pagetable_c(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).window_leaves_present(w)
            &&& !pagetable_c(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).lower.window_stale_cpus.dom().contains((pagetable_c(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
        },
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger entry_lctx.pagetable_window_lock_map().dom().contains((p, w))]
            entry_lctx.pagetable_window_lock_map().dom().contains((p, w)) == (p == source_pagetable_ptr && source_window_perms.dom().contains(w)),
        held_pagetable_windows_unchanged(entry_k.pt_mp, entry_k.pt_lower.view(), old(krnl).pt_mp, old(krnl).pt_lower.view(), &entry_lctx),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view() == entry_k.pt_mp.spec_index(source_pagetable_ptr).view(),
        old(lctx).pagetable_window_lock_map() == entry_lctx.pagetable_window_lock_map(),
        entry_lctx.thread_id() == old(lctx).thread_id(),
    ensures
        old(steps).view().len() as int + source_range.len as int + 1 <= final(steps).view().len() as int <= old(steps).view().len() as int + 4 * source_range.len as int + 1,
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        new_container_commit_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, caller_cpu_id, *source_range, record.funding,
            record.process_quota, record.transfer_cpu, *initial_regs, record.endpoint_index),
        final(steps).view().last().new_u == kernel_k_to_kernel_u(*final(krnl)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
{
    let tracked parent_container_lock_perm = parent_container_lock_perm.get();
    let tracked child_container_lock_perm = child_container_lock_perm.get();
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked source_pagetable_lock_perm = source_pagetable_lock_perm.get();
    let tracked child_pagetable_lock_perm = child_pagetable_lock_perm.get();
    let tracked endpoint_lock_perm = endpoint_lock_perm.get();
    let ghost share_before = steps.view();
    let Tracked(child_window_perms) = share_new_container_range(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), caller_cpu_id, source_range, parent_container_ptr, child_container_ptr,
        parent_process_ptr, child_process_ptr, current_thread_ptr, source_pagetable_ptr, child_pagetable_ptr, child_allocator_4k_ptr, thread_page_ptr,
        Tracked(&parent_container_lock_perm), Tracked(&child_container_lock_perm), Tracked(&current_thread_lock_perm),
        Tracked(&source_pagetable_lock_perm), Tracked(&child_pagetable_lock_perm), Ghost(record), Ghost(entry_k), Ghost(entry_lctx),
    );
    proof {
        assert(new_container_trace_after_share(steps.view(), start, pre, caller_cpu_id, *source_range, record.funding, record.process_quota, record.transfer_cpu,
            *initial_regs, record.endpoint_index)) by {
            new_container_trace_share_steps(&*steps, share_before, start, pre, caller_cpu_id, *source_range, record.funding, record.process_quota,
                record.transfer_cpu, *initial_regs, record.endpoint_index);
        };
        assert(krnl.cpu_op.view().view()[caller_cpu_id as int] is InStep) by { cpu_op_wf_at(old(krnl).cpu_op.view().view(), old(krnl).cpu_arr, caller_cpu_id); cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, caller_cpu_id); };
        if let Some(endpoint_ptr) = endpoint {
            assert({
                &&& krnl.ep_mp.dom().contains(endpoint_ptr)
                &&& krnl.ep_mp.spec_index(endpoint_ptr).is_init()
                &&& typed_lock_map_contains_mode(lctx.endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write)
                &&& !krnl.ep_mp.spec_index(endpoint_ptr).being_killed()
                &&& krnl.ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((current_thread_ptr, endpoint_index))
                &&& endpoint_lock_perm->Some_0.lock_id() == krnl.ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id
            }) by { endpoint_perms_wf_at(krnl.ep_mp, endpoint_ptr); };
            assert(krnl.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.wf() && krnl.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr)) by {
                thread_perms_wf_at(krnl.thr_mp, current_thread_ptr); thread_endpoint_ref_counter_wf_endpoint_at(krnl.thr_mp, krnl.ep_mp, endpoint_ptr, current_thread_ptr, endpoint_index);
            };
        }
    }
    let ghost finish_before = steps.view();
    let new_thread_ptr = create_new_container_root_thread_and_finish(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), caller_cpu_id, parent_container_ptr, child_container_ptr, parent_process_ptr,
        child_process_ptr, current_thread_ptr, source_pagetable_ptr, child_pagetable_ptr, child_scheduler_ptr, thread_page_ptr, endpoint, endpoint_index,
        caller_cpu_lock_perm, Tracked(parent_container_lock_perm), Tracked(child_container_lock_perm), parent_process_lock_perm,
        child_process_lock_perm, Tracked(current_thread_lock_perm), Tracked(source_pagetable_lock_perm), Tracked(child_pagetable_lock_perm),
        thread_page_lock_perm, Tracked(endpoint_lock_perm), initial_regs, source_range, Tracked(source_window_perms), Tracked(child_window_perms), Ghost(entry_k),
        Ghost(entry_lctx),
    );
    proof {
        assert(new_container_commit_trace(steps.view().subrange(start, steps.view().len() as int), pre, caller_cpu_id, *source_range, record.funding,
            record.process_quota, record.transfer_cpu, *initial_regs, record.endpoint_index)) by {
            new_container_trace_finish_step(&*steps, finish_before, start, pre, caller_cpu_id, *source_range, record.funding, record.process_quota,
                record.transfer_cpu, *initial_regs, record.endpoint_index);
        };
    }
    new_thread_ptr
}
}
