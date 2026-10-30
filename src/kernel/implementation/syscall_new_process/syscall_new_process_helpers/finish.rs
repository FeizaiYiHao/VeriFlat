use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::super::syscall_new_process_spec::{new_process_finish_step, new_process_finish_step_pre};
#[cfg(verus_keep_ghost)]
use super::super::syscall_new_process_trace::{new_process_finish_step_from_u, new_process_finish_step_pre_from_k};
#[cfg(verus_keep_ghost)]
use super::finish_eof::{create_initial_thread_and_finish_new_process_eof, create_initial_thread_and_finish_new_process_eof_transition_framing};
use super::finish_helpers::release_new_process_locks_and_attach_endpoint;
#[cfg(feature = "split-crates")]
use veriflat_kernel_core::{create_thread_from_staged_page_merged, kernel_u_new_thread_changed};
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::create_thread_from_staged_page::create_thread_from_staged_page_merged;
#[cfg(all(not(feature = "split-crates"), verus_keep_ghost))]
use crate::kernel::implementation::create_thread_from_staged_page::kernel_u_new_thread_changed;

verus! {
#[verifier::spinoff_prover]
pub(in super::super) fn create_initial_thread_and_finish_new_process(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    container_ptr: RwLockContainerPtr, child_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, scheduler_ptr: RwLockSchedulerPtr,
    endpoint: Option<RwLockEndpointPtr>, endpoint_index: EndpointIdx, source_pagetable_ptr: RwLockPageTableRoot,
    target_pagetable_ptr: RwLockPageTableRoot, iommu_table: Option<RwLockPageTableRoot>, cpu_lock_perm: Tracked<LockPerm>,
    child_lock_perm: Tracked<LockPerm>, current_thread_lock_perm: Tracked<LockPerm>, scheduler_lock_perm: Tracked<LockPerm>,
    endpoint_lock_perm: Tracked<Option<LockPerm>>, source_pagetable_lock_perm: Tracked<LockPerm>, target_pagetable_lock_perm: Tracked<LockPerm>,
    iommu_table_lock_perm: Tracked<Option<LockPerm>>, initial_regs: &Registers, source_range: &VaRange4K, Tracked(source_window_perms): Tracked<Map<WindowVa, LockPerm>>, Tracked(target_window_perms): Tracked<Map<WindowVa, LockPerm>>,
    Ghost(entry_k): Ghost<KernelK>, Ghost(entry_lctx): Ghost<LocalContext>,
) -> (new_thread_ptr: RwLockThreadPtr)
    requires
        *old(krnl) == (KernelK { sched_mp: old(krnl).sched_mp, ..old(steps).snapshot_k() }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == source_pagetable_ptr,
        old(krnl).prc_mp.spec_index(child_ptr).view().pagetable == target_pagetable_ptr,
        old(krnl).prc_mp.spec_index(child_ptr).view().iommu_table == iommu_table,
        old(krnl).prc_mp.spec_index(child_ptr).view().state.view() is Creating,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        old(lctx).page_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom() =~= set![child_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        endpoint is None ==> old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom() =~= set![(scheduler_ptr, cpu_id)],
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr, target_pagetable_ptr],
        iommu_table is None ==> old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        cpu_lock_perm.view().state() is WriteLock,
        cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
        old(krnl).prc_mp.dom().contains(child_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), child_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(child_ptr).being_killed(),
        !old(krnl).prc_mp.spec_index(child_ptr).view().zombie,
        old(krnl).prc_mp.spec_index(child_ptr).view_rodata().view().owning_container == container_ptr,
        child_lock_perm.view().state() is WriteLock,
        child_lock_perm.view().thread_id() == old(lctx).thread_id(),
        child_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(child_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state is RUNNING,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() matches Some(SyscallProgress::Share4k { source_range: r, shared, origin, .. })
            && r == *source_range && shared == source_range.len && origin == Share4kOrigin::NewProcess(NewProcessProgress {
                range: *source_range, regs: *initial_regs, endpoint_index: if endpoint is Some { Some(endpoint_index) } else { None }, with_iommu: iommu_table is Some, child: Some(child_ptr),
            }),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 1,
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).sched_mp.dom().contains(scheduler_ptr),
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (scheduler_ptr, cpu_id), TypedLockMode::Write),
        scheduler_lock_perm.view().state() is WriteLock,
        scheduler_lock_perm.view().thread_id() == old(lctx).thread_id(),
        scheduler_lock_perm.view().lock_id() == old(krnl).sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        endpoint is Some ==> {
            let endpoint_ptr = endpoint->Some_0;
            &&& edp_idx_valid(endpoint_index)
            &&& old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr]
            &&& old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.wf()
            &&& old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == endpoint
            &&& old(krnl).ep_mp.dom().contains(endpoint_ptr)
            &&& old(krnl).ep_mp.spec_index(endpoint_ptr).is_init()
            &&& typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write)
            &&& !old(krnl).ep_mp.spec_index(endpoint_ptr).being_killed()
            &&& endpoint_lock_perm.view() is Some
            &&& endpoint_lock_perm.view()->Some_0.state() is WriteLock
            &&& endpoint_lock_perm.view()->Some_0.thread_id() == old(lctx).thread_id()
            &&& endpoint_lock_perm.view()->Some_0.lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id
        },
        source_pagetable_ptr != target_pagetable_ptr,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        old(krnl).pt_mp.dom().contains(target_pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable_ptr, TypedLockMode::Write),
        target_pagetable_lock_perm.view().state() is WriteLock,
        target_pagetable_lock_perm.view().thread_id() == old(lctx).thread_id(),
        target_pagetable_lock_perm.view().lock_id() == old(krnl).pt_mp.spec_index(target_pagetable_ptr).locking_thread()->Write_lock_id,
        source_range.wf(),
        source_range.len > 0,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Read),
        source_pagetable_lock_perm.view().state() is ReadLock,
        source_pagetable_lock_perm.view().thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread() is Read,
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), source_pagetable_lock_perm.view().lock_id()),
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
            &&& pagetable_c(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).lower.l2_owner(pagetable_c(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
                == (SpinLockState::Some { thread_id: source_window_perms.index(w).thread_id(), lock_id: source_window_perms.index(w).lock_id() })
            &&& pagetable_c(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).window_leaves_present(w)
            &&& !pagetable_c(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).lower.window_stale_cpus.dom().contains((pagetable_c(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
        },
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger entry_lctx.pagetable_window_lock_map().dom().contains((p, w))]
            entry_lctx.pagetable_window_lock_map().dom().contains((p, w)) == (p == source_pagetable_ptr && source_window_perms.dom().contains(w)),
        held_pagetable_windows_unchanged(entry_k.pt_mp, entry_k.pt_lower.view(), old(krnl).pt_mp, old(krnl).pt_lower.view(), &entry_lctx),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view() == entry_k.pt_mp.spec_index(source_pagetable_ptr).view(),
        entry_lctx.thread_id() == old(lctx).thread_id(),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w)) ==> entry_lctx.pagetable_window_lock_map().dom().contains((p, w)) || (p == target_pagetable_ptr && target_window_perms.dom().contains(w)),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger entry_lctx.pagetable_window_lock_map().dom().contains((p, w))]
            entry_lctx.pagetable_window_lock_map().dom().contains((p, w)) ==> old(lctx).pagetable_window_lock_map().dom().contains((p, w))
                && old(lctx).pagetable_window_lock_map().index((p, w)) == entry_lctx.pagetable_window_lock_map().index((p, w)),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable_ptr).leaves_present(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable_ptr).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        old(krnl).pt_mp.spec_index(target_pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(source_range.start),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*source_range).contains(w)]
            va_range_2m_windows(*source_range).contains(w) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable_ptr).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> target_window_perms.dom().contains(w),
        forall|w: WindowVa| #![trigger target_window_perms.dom().contains(w)] target_window_perms.dom().contains(w) ==> {
            &&& va_range_2m_windows(*source_range).contains(w)
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable_ptr).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
            &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (target_pagetable_ptr, w), TypedLockMode::Write)
            &&& target_window_perms.index(w).state() is WriteLock
            &&& target_window_perms.index(w).thread_id() == old(lctx).thread_id()
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable_ptr).lower.l2_owner(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable_ptr).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
                == (SpinLockState::Some { thread_id: target_window_perms.index(w).thread_id(), lock_id: target_window_perms.index(w).lock_id() })
        },
        iommu_table is Some ==> {
            let iommu_table_ptr = iommu_table->Some_0;
            &&& old(lctx).iommu_table_lock_map().dom() =~= set![iommu_table_ptr]
            &&& old(krnl).prc_mp.spec_index(child_ptr).view().iommu_table == iommu_table
            &&& old(krnl).it_mp.dom().contains(iommu_table_ptr)
            &&& typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write)
            &&& old(krnl).it_mp.spec_index(iommu_table_ptr).view().is_empty()
            &&& iommu_table_lock_perm.view() is Some
            &&& iommu_table_lock_perm.view()->Some_0.state() is WriteLock
            &&& iommu_table_lock_perm.view()->Some_0.thread_id() == old(lctx).thread_id()
            &&& iommu_table_lock_perm.view()->Some_0.lock_id() == old(krnl).it_mp.spec_index(iommu_table_ptr).locking_thread()->Write_lock_id
        },
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(steps).view() == old(steps).view().push(final(steps).view().last()),
        final(steps).view().last().new_u == kernel_k_to_kernel_u(*final(krnl)),
        new_process_finish_step_pre(final(steps).view().last().old_u, cpu_id),
        new_process_finish_step(final(steps).view().last().old_u, final(steps).view().last().new_u, cpu_id),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        final(steps).snapshot_k() == *final(krnl),
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(krnl).thr_mp.dom().contains(new_thread_ptr),
        final(krnl).thr_mp.spec_index(new_thread_ptr).view().state is SCHEDULED,
        final(krnl).thr_mp.spec_index(new_thread_ptr).view().owning_proc == child_ptr,
        final(krnl).thr_mp.spec_index(new_thread_ptr).view().owning_container == container_ptr,
        endpoint is Some ==> final(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.wf(),
        endpoint is Some ==> final(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.spec_index(0) == endpoint,
        iommu_table is Some ==> final(krnl).prc_mp.dom().contains(child_ptr) && final(krnl).prc_mp.spec_index(child_ptr).view().iommu_table == iommu_table,
        iommu_table is Some ==> final(krnl).it_mp.dom().contains(iommu_table->Some_0) && final(krnl).it_mp.spec_index(iommu_table->Some_0).view().is_empty(),
{
    hide(Seq::contains);
    proof {
        kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl); steps.rebase_snapshot_k_if_unchanged(&*krnl);
        assert(krnl.cpu_arr.spec_index(cpu_id).view().view().kernel_call_perm() is None) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
    }
    let tracked cpu_lock_perm = cpu_lock_perm.get();
    let tracked child_lock_perm = child_lock_perm.get();
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked scheduler_lock_perm = scheduler_lock_perm.get();
    let tracked endpoint_lock_perm = endpoint_lock_perm.get();
    let tracked source_pagetable_lock_perm = source_pagetable_lock_perm.get();
    let tracked target_pagetable_lock_perm = target_pagetable_lock_perm.get();
    let tracked iommu_table_lock_perm = iommu_table_lock_perm.get();
    let (thread_page_ptr, Tracked(thread_page_lock_perm)) = allocate_free_4k_page(krnl, current_thread_ptr, container_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&current_thread_lock_perm));
    let ghost parent_ptr = old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc;
    let ghost finish_k = *krnl;
    let ghost finish_lctx = *lctx;
    proof {
        krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), target_pagetable_ptr);
        pagetable_lower_backup_wf_at(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable_ptr); pagetable_lower_backup_wf_at(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable_ptr);
        assert(krnl.prc_mp.dom().contains(parent_ptr) && !krnl.prc_mp.spec_index(parent_ptr).view().zombie && krnl.prc_mp.spec_index(parent_ptr).view().pagetable == source_pagetable_ptr
            && parent_ptr != child_ptr) by { process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, current_thread_ptr); };
    }
    let (new_thread_ptr, Tracked(new_thread_lock_perm)) = create_thread_from_staged_page_merged(
        krnl, thread_page_ptr, child_ptr, current_thread_ptr, container_ptr, scheduler_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&thread_page_lock_perm),
        Tracked(&child_lock_perm), Tracked(&current_thread_lock_perm), Tracked(&scheduler_lock_perm), initial_regs,
    );
    let ghost mid_k = *krnl;
    proof {
        assert(iommu_table is Some ==> krnl.prc_mp.spec_index(child_ptr).view().iommu_table == iommu_table) by { reveal(process_iommu_table_match); };
        if let Some(endpoint_ptr) = endpoint {
            assert({
                ||| krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container == container_ptr
                ||| krnl.ctn_mp.spec_index(krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container).view_ghost().subtree_set.view().contains(container_ptr)
            }) by { container_endpoint_wf_at(krnl.ctn_mp, krnl.ep_mp, endpoint_ptr); container_thread_endpoint_wf_at(krnl.ctn_mp, krnl.thr_mp, krnl.ep_mp, current_thread_ptr, endpoint_index); };
        }
    }
    release_new_process_locks_and_attach_endpoint(
        krnl, Tracked(&mut *lctx), cpu_id, container_ptr, child_ptr, current_thread_ptr, new_thread_ptr, scheduler_ptr, endpoint, source_pagetable_ptr, target_pagetable_ptr,
        iommu_table, Tracked(cpu_lock_perm), Tracked(child_lock_perm), Tracked(current_thread_lock_perm), Tracked(new_thread_lock_perm), Tracked(thread_page_lock_perm),
        Tracked(scheduler_lock_perm), Tracked(endpoint_lock_perm), Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm), Tracked(iommu_table_lock_perm),
        source_range, Tracked(source_window_perms), Tracked(target_window_perms), Ghost(entry_k), Ghost(entry_lctx),
    );
    proof {
        assert(create_initial_thread_and_finish_new_process_eof_transition_framing(finish_k, mid_k, *krnl, child_ptr, current_thread_ptr, container_ptr, cpu_id, new_thread_ptr, *initial_regs, endpoint)) by {
            reveal(create_initial_thread_and_finish_new_process_eof_transition_framing);
        };
        create_initial_thread_and_finish_new_process_eof(finish_k, mid_k, *krnl, child_ptr, current_thread_ptr, container_ptr, cpu_id, new_thread_ptr, *initial_regs, endpoint);
    }
    end_new_process_finish_step(
        &*krnl, Tracked(&*lctx), Tracked(&mut *steps), cpu_id, container_ptr, child_ptr, current_thread_ptr, new_thread_ptr, endpoint, endpoint_index, iommu_table,
        initial_regs, Ghost(parent_ptr), Ghost(finish_k), Ghost(finish_lctx), Ghost(*source_range),
    );
    new_thread_ptr
}

/// Ends the finish step that created `new_thread_ptr` from the staged page and released every lock since `finish_k`.
fn end_new_process_finish_step(
    krnl: &KernelK, Tracked(lctx): Tracked<&LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, container_ptr: RwLockContainerPtr,
    child_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, new_thread_ptr: RwLockThreadPtr, endpoint: Option<RwLockEndpointPtr>,
    endpoint_index: EndpointIdx, iommu_table: Option<RwLockPageTableRoot>, initial_regs: &Registers, Ghost(parent_ptr): Ghost<RwLockProcessPtr>,
    Ghost(finish_k): Ghost<KernelK>, Ghost(finish_lctx): Ghost<LocalContext>, Ghost(source_range): Ghost<VaRange4K>,
)
    requires
        old(steps).snapshot_k() == finish_k,
        ({
            let source = finish_k.prc_mp.spec_index(parent_ptr).view().pagetable;
            let target = finish_k.prc_mp.spec_index(child_ptr).view().pagetable;
            &&& krnl.pt_lower.view() =~= finish_k.pt_lower.view().insert(source, krnl.pt_lower.view().spec_index(source)).insert(target, krnl.pt_lower.view().spec_index(target))
            &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source).lower.pagetable_window_locks == pagetable_window_locks_after_unlocking_range(pagetable_c(finish_k.pt_mp, finish_k.pt_lower.view(), source).lower.pagetable_window_locks, source_range)
            &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target).lower.pagetable_window_locks == pagetable_window_locks_after_unlocking_range(pagetable_c(finish_k.pt_mp, finish_k.pt_lower.view(), target).lower.pagetable_window_locks, source_range)
        }),
        krnl.inv(),
        lctx.kernel_view_locking_state() is Release,
        kernel_new_thread_fields(&finish_k, krnl, child_ptr, current_thread_ptr, container_ptr, cpu_id, new_thread_ptr, *initial_regs, endpoint, None),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(&finish_k, &finish_lctx),
        typed_lock_map_contains_mode(finish_lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(finish_lctx.process_lock_map(), child_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(finish_lctx.thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(finish_lctx.pagetable_lock_map(), finish_k.prc_mp.spec_index(parent_ptr).view().pagetable, TypedLockMode::Read),
        typed_lock_map_contains_mode(finish_lctx.pagetable_lock_map(), finish_k.prc_mp.spec_index(child_ptr).view().pagetable, TypedLockMode::Write),
        finish_k.prc_mp.spec_index(child_ptr).view().iommu_table matches Some(t) ==> typed_lock_map_contains_mode(finish_lctx.iommu_table_lock_map(), t, TypedLockMode::Write),
        finish_k.cpu_arr.spec_index(cpu_id).value.view().view().current_thread == Some(current_thread_ptr),
        finish_k.thr_mp.dom().contains(current_thread_ptr),
        finish_k.thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_ptr,
        finish_k.thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr,
        finish_k.thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() matches Some(SyscallProgress::Share4k { source_range: r, shared, origin, .. })
            && r == source_range && shared == source_range.len && origin == Share4kOrigin::NewProcess(NewProcessProgress {
                range: source_range, regs: *initial_regs, endpoint_index: if endpoint is Some { Some(endpoint_index) } else { None }, with_iommu: iommu_table is Some, child: Some(child_ptr),
            }),
        endpoint is Some ==> {
            &&& edp_idx_valid(endpoint_index)
            &&& finish_k.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == endpoint
            &&& finish_k.ep_mp.dom().contains(endpoint->Some_0)
            &&& typed_lock_map_contains_mode(finish_lctx.endpoint_lock_map(), endpoint->Some_0, TypedLockMode::Write)
        },
        finish_k.ctn_mp.dom().contains(container_ptr),
        parent_ptr != child_ptr,
        finish_k.prc_mp.dom().contains(parent_ptr),
        !finish_k.prc_mp.spec_index(parent_ptr).view().zombie,
        finish_k.prc_mp.dom().contains(child_ptr),
        !finish_k.prc_mp.spec_index(child_ptr).view().zombie,
        finish_k.prc_mp.spec_index(child_ptr).view_rodata().view().owning_container == container_ptr,
        forall|p: RwLockContainerPtr| #![trigger krnl.ctn_mp.spec_index(p)]
            finish_k.ctn_mp.dom().contains(p) ==> krnl.ctn_mp.spec_index(p).locking_thread() == finish_k.ctn_mp.spec_index(p).locking_thread() && krnl.ctn_mp.spec_index(p).lock_process_owner_u() == finish_k.ctn_mp.spec_index(p).lock_process_owner_u(),
        forall|p: RwLockProcessPtr| #![trigger krnl.prc_mp.spec_index(p)]
            finish_k.prc_mp.dom().contains(p) ==> if p == child_ptr { krnl.prc_mp.spec_index(p).locking_thread() is None } else { krnl.prc_mp.spec_index(p).locking_thread() == finish_k.prc_mp.spec_index(p).locking_thread() },
        forall|p: RwLockThreadPtr| #![trigger krnl.thr_mp.spec_index(p)]
            finish_k.thr_mp.dom().contains(p) && p != new_thread_ptr ==> if p == current_thread_ptr { krnl.thr_mp.spec_index(p).locking_thread() is None } else { krnl.thr_mp.spec_index(p).locking_thread() == finish_k.thr_mp.spec_index(p).locking_thread() },
        forall|p: RwLockEndpointPtr| #![trigger krnl.ep_mp.spec_index(p)]
            finish_k.ep_mp.dom().contains(p) ==> if endpoint == Some(p) { krnl.ep_mp.spec_index(p).locking_thread() is None } else { krnl.ep_mp.spec_index(p).locking_thread() == finish_k.ep_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger krnl.pt_mp.spec_index(p)]
            finish_k.pt_mp.dom().contains(p) ==> if p == finish_k.prc_mp.spec_index(child_ptr).view().pagetable { krnl.pt_mp.spec_index(p).locking_thread() is None }
                else if p == finish_k.prc_mp.spec_index(parent_ptr).view().pagetable { !(krnl.pt_mp.spec_index(p).locking_thread() is Write) }
                else { krnl.pt_mp.spec_index(p).locking_thread() == finish_k.pt_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger krnl.it_mp.spec_index(p)]
            finish_k.it_mp.dom().contains(p) ==> if finish_k.prc_mp.spec_index(child_ptr).view().iommu_table == Some(p) { krnl.it_mp.spec_index(p).locking_thread() is None }
                else { krnl.it_mp.spec_index(p).locking_thread() == finish_k.it_mp.spec_index(p).locking_thread() },
        forall|i: CpuId| #![trigger krnl.cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> if i == cpu_id { krnl.cpu_arr.spec_index(i).value.locking_thread() is None } else { krnl.cpu_arr.spec_index(i).value.locking_thread() == finish_k.cpu_arr.spec_index(i).value.locking_thread() },
        forall|i: CpuId| #![trigger krnl.cpu_op.view().view()[i as int]] index_valid(NUM_CPUS, i) && i != cpu_id ==> krnl.cpu_op.view().view()[i as int] == finish_k.cpu_op.view().view()[i as int],
        krnl.cpu_op.view().view()[cpu_id as int] == cpu_op_after_step(finish_k.cpu_arr.spec_index(cpu_id).view().view().view().state),
        krnl.thr_mp.spec_index(new_thread_ptr).locking_thread() is None,
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(steps).view() == old(steps).view().push(final(steps).view().last()),
        final(steps).view().last().new_u == kernel_k_to_kernel_u(*krnl),
        new_process_finish_step_pre(final(steps).view().last().old_u, cpu_id),
        new_process_finish_step(final(steps).view().last().old_u, final(steps).view().last().new_u, cpu_id),
        final(steps).snapshot_k() == *krnl,
{
    proof {
        steps.end_kernel_step_new_thread(krnl, lctx, child_ptr, current_thread_ptr, container_ptr, cpu_id, new_thread_ptr, *initial_regs, endpoint, None);
        assert(new_process_finish_step_pre(steps.view().last().old_u, cpu_id) && new_process_finish_step(steps.view().last().old_u, steps.view().last().new_u, cpu_id)) by {
            reveal(kernel_new_thread_fields);
            new_process_finish_step_pre_from_k(&finish_k, &finish_lctx, cpu_id, parent_ptr, child_ptr, current_thread_ptr, container_ptr, endpoint, endpoint_index, *initial_regs, iommu_table is Some);
            kernel_new_thread_fields_and_unlocks_source_runlocked_implies_u_step(&finish_k, krnl, cpu_id, child_ptr, current_thread_ptr, container_ptr, new_thread_ptr, *initial_regs, endpoint, parent_ptr);
            let source = finish_k.prc_mp.spec_index(parent_ptr).view().pagetable;
            let target = finish_k.prc_mp.spec_index(child_ptr).view().pagetable;
            new_process_finish_step_from_u(kernel_k_to_kernel_u(finish_k), kernel_k_to_kernel_u(*krnl), cpu_id, parent_ptr, child_ptr, current_thread_ptr, container_ptr, new_thread_ptr, endpoint, *initial_regs,
                pagetable_c(finish_k.pt_mp, finish_k.pt_lower.view(), source).lower.pagetable_window_locks, pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source).lower.pagetable_window_locks,
                pagetable_c(finish_k.pt_mp, finish_k.pt_lower.view(), target).lower.pagetable_window_locks, pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target).lower.pagetable_window_locks);
        };
    }
}
}
