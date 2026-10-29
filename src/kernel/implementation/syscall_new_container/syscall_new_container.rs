use vstd::prelude::*;
use crate::*;
use super::syscall_new_container_commit::commit_new_container;
use super::syscall_new_container_spec::*;
use super::syscall_new_container_trace::*;
use super::syscall_new_container_lock_owners::{new_container_lock_process_and_thread, new_container_lock_source_windows};

verus! {
/// Exec state handed from the lock-and-check prefix of `syscall_new_container` to its commit.
pub(super) struct NewContainerEntryLocked {
    pub parent_container_ptr: RwLockContainerPtr, pub parent_process_ptr: RwLockProcessPtr, pub current_thread_ptr: RwLockThreadPtr,
    pub source_pagetable_ptr: RwLockPageTableRoot, pub parent_cpu_set: RwLockCpuSetPtr, pub source_range: VaRange4K,
    pub endpoint: Option<RwLockEndpointPtr>, pub endpoint_slot: EndpointIdx,
    pub cpu_lock_perm: Tracked<LockPerm>, pub container_lock_perm: Tracked<LockPerm>, pub process_lock_perm: Tracked<LockPerm>,
    pub thread_lock_perm: Tracked<LockPerm>, pub source_pagetable_lock_perm: Tracked<LockPerm>, pub cpu_set_lock_perm: Tracked<LockPerm>,
    pub endpoint_lock_perm: Tracked<Option<LockPerm>>, pub source_window_perms: Tracked<Map<WindowVa, LockPerm>>,
}

/// Exec state handed from the owner-locking prefix of `new_container_lock_entry` to its endpoint, pagetable, and cpu-set checks.
pub(super) struct NewContainerOwnersLocked {
    pub parent_container_ptr: RwLockContainerPtr, pub parent_process_ptr: RwLockProcessPtr, pub current_thread_ptr: RwLockThreadPtr,
    pub source_pagetable_ptr: RwLockPageTableRoot, pub parent_cpu_set: RwLockCpuSetPtr, pub source_range: VaRange4K, pub endpoint: Option<RwLockEndpointPtr>,
    pub cpu_lock_perm: Tracked<LockPerm>, pub container_lock_perm: Tracked<LockPerm>, pub process_lock_perm: Tracked<LockPerm>, pub thread_lock_perm: Tracked<LockPerm>,
}

/// Releases every lock `new_container_lock_entry` holds once its source or CPU-set check fails and ends the step unchanged;
/// `cpu_set_unlocked_k` is the kernel just before the CPU set was locked. The source table is read-held, and when
/// `windows_held` its existing windows over `source_range` are held with perms `source_window_perms`.
fn new_container_release_entry_locks(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, container_ptr: RwLockContainerPtr,
    process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, cpu_set_ptr: RwLockCpuSetPtr, endpoint: Option<RwLockEndpointPtr>,
    source_range: &VaRange4K, windows_held: bool, Ghost(cpu_set_unlocked_k): Ghost<KernelK>, Tracked(cpu_lock_perm): Tracked<LockPerm>,
    Tracked(container_lock_perm): Tracked<LockPerm>, Tracked(process_lock_perm): Tracked<LockPerm>, Tracked(thread_lock_perm): Tracked<LockPerm>,
    Tracked(pagetable_lock_perm): Tracked<LockPerm>, Tracked(cpu_set_lock_perm): Tracked<LockPerm>, Tracked(endpoint_lock_perm): Tracked<Option<LockPerm>>,
    Tracked(source_window_perms): Tracked<Map<WindowVa, LockPerm>>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, ctn_mp: old(krnl).ctn_mp, prc_mp: old(krnl).prc_mp, thr_mp: old(krnl).thr_mp, ep_mp: old(krnl).ep_mp,
            pt_mp: old(krnl).pt_mp, pt_lower: old(krnl).pt_lower, cpu_set_mp: old(krnl).cpu_set_mp, ..old(steps).snapshot_k() }),
        *old(krnl) == (KernelK { cpu_set_mp: old(krnl).cpu_set_mp, ..cpu_set_unlocked_k }),
        old(krnl).cpu_arr.entries_unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
        old(steps).snapshot_k().cpu_op.view().view()[cpu_id as int] is Trap,
        old(krnl).ctn_mp.unchanged_except(&old(steps).snapshot_k().ctn_mp, container_ptr),
        old(krnl).prc_mp.unchanged_except(&old(steps).snapshot_k().prc_mp, process_ptr),
        old(krnl).thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, thread_ptr),
        old(krnl).pt_mp.unchanged_except(&old(steps).snapshot_k().pt_mp, pagetable_ptr),
        old(krnl).cpu_set_mp.unchanged_except(&cpu_set_unlocked_k.cpu_set_mp, cpu_set_ptr),
        match endpoint { Some(p) => old(krnl).ep_mp.unchanged_except(&old(steps).snapshot_k().ep_mp, p), None => old(krnl).ep_mp == old(steps).snapshot_k().ep_mp },
        old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        old(steps).snapshot_k().ctn_mp.spec_index(container_ptr).locking_thread() is None,
        old(steps).snapshot_k().prc_mp.spec_index(process_ptr).locking_thread() is None,
        old(steps).snapshot_k().thr_mp.spec_index(thread_ptr).locking_thread() is None,
        endpoint is Some ==> old(steps).snapshot_k().ep_mp.spec_index(endpoint->Some_0).locking_thread() is None,
        cpu_set_unlocked_k.cpu_set_mp.spec_index(cpu_set_ptr).locking_thread() is None,
        !cpu_set_unlocked_k.cpu_set_mp.spec_index(cpu_set_ptr).being_killed() && !old(krnl).cpu_set_mp.spec_index(cpu_set_ptr).being_killed(),
        container_cpu_set_wf(cpu_set_unlocked_k.ctn_mp, cpu_set_unlocked_k.cpu_set_mp),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), &cpu_set_unlocked_k),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom() =~= set![container_ptr],
        old(lctx).process_lock_map().dom() =~= set![process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(lctx).pagetable_lock_map().dom() =~= set![pagetable_ptr],
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (windows_held && p == pagetable_ptr && source_window_perms.dom().contains(w)),
        !windows_held ==> old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom() =~= set![cpu_set_ptr],
        endpoint is None ==> old(lctx).endpoint_lock_map().dom().is_empty(),
        endpoint is Some ==> old(lctx).endpoint_lock_map().dom() =~= set![endpoint->Some_0],
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        cpu_lock_perm.state() is WriteLock && cpu_lock_perm.thread_id() == old(lctx).thread_id() && cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        !old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty(),
        container_lock_perm.state() is WriteLock && container_lock_perm.thread_id() == old(lctx).thread_id() && container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(process_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(process_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Running || old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Zombie,
        process_lock_perm.state() is WriteLock && process_lock_perm.thread_id() == old(lctx).thread_id() && process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id: cpu_id }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None,
        !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        thread_lock_perm.state() is WriteLock && thread_lock_perm.thread_id() == old(lctx).thread_id() && thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        pagetable_lock_perm.state() is ReadLock && pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        {
            let entry = old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr);
            &&& entry.inv() && !entry.wlocked() && !entry.locked_by_thread(old(lctx).thread_id())
            &&& old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread() == (RwLockState::Read {
                reader_map: (if entry.locking_thread() is Read { entry.locking_thread()->Read_reader_map } else { Map::empty() }).insert(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
            })
        },
        windows_held ==> {
            let table = pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr);
            &&& source_range.wf() && source_range.len > 0
            &&& table.kernel_l4_end() <= spec_va2index(source_range.start).0
            &&& forall|w: WindowVa| #![trigger va_range_2m_windows(*source_range).contains(w)]
                va_range_2m_windows(*source_range).contains(w) && table.higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> source_window_perms.dom().contains(w)
            &&& forall|w: WindowVa| #![trigger source_window_perms.dom().contains(w)] source_window_perms.dom().contains(w) ==> {
                &&& va_range_2m_windows(*source_range).contains(w)
                &&& table.higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable_ptr, w), TypedLockMode::Write)
                &&& source_window_perms.index(w).state() is WriteLock && source_window_perms.index(w).thread_id() == old(lctx).thread_id()
                &&& table.lower.l2_lock_of(table.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va))).lock_perm_match(spec_v2l2index(w.va), &source_window_perms.index(w))
                &&& table.window_leaves_present(w)
                &&& !table.lower.window_stale_cpus.dom().contains((table.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            }
        },
        old(krnl).cpu_set_mp.dom().contains(cpu_set_ptr),
        typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), cpu_set_ptr, TypedLockMode::Write),
        cpu_set_lock_perm.state() is WriteLock && cpu_set_lock_perm.thread_id() == old(lctx).thread_id() && cpu_set_lock_perm.lock_id() == old(krnl).cpu_set_mp.spec_index(cpu_set_ptr).locking_thread()->Write_lock_id,
        (endpoint_lock_perm is Some) == (endpoint is Some),
        endpoint is Some ==> {
            let endpoint_ptr = endpoint->Some_0;
            &&& old(krnl).ep_mp.dom().contains(endpoint_ptr)
            &&& typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write)
            &&& endpoint_lock_perm->Some_0.state() is WriteLock
            &&& endpoint_lock_perm->Some_0.thread_id() == old(lctx).thread_id()
            &&& endpoint_lock_perm->Some_0.lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id
        },
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(steps).view() == old(steps).view(),
        final(steps).nonlock_view() == old(steps).nonlock_view(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(old(steps).snapshot_k()),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).no_locks_held(),
{
    krnl.wunlock_cpu_set(cpu_set_ptr, Tracked(&mut *lctx), Tracked(cpu_set_lock_perm));
    proof { container_nonlock_fields_and_quotas_unchanged_for_cpu_set_relock(&cpu_set_unlocked_k, &*krnl, cpu_set_ptr); }
    if windows_held {
        krnl.unlock_pagetable_range_existing_windows(pagetable_ptr, source_range, Tracked(&pagetable_lock_perm), Tracked(&mut *lctx), Tracked(source_window_perms));
    }
    proof {
        let entry = steps.snapshot_k().pt_mp.spec_index(pagetable_ptr);
        if entry.locking_thread() is Read {
            assert(entry.locking_thread()->Read_reader_map.insert(lctx.thread_id(), pagetable_lock_perm.lock_id()).remove(lctx.thread_id()) =~= entry.locking_thread()->Read_reader_map);
        } else {
            assert(Map::<LockThreadId, LockToken>::empty().insert(lctx.thread_id(), pagetable_lock_perm.lock_id()).remove(lctx.thread_id()).dom() =~= Set::empty());
        }
    }
    krnl.runlock_pagetable(pagetable_ptr, Tracked(&mut *lctx), Tracked(pagetable_lock_perm));
    if endpoint.is_some() {
        let tracked endpoint_lock_perm = endpoint_lock_perm.tracked_unwrap();
        krnl.wunlock_endpoint(endpoint.unwrap(), Tracked(&mut *lctx), Tracked(endpoint_lock_perm));
    }
    krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
    krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
    krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
    krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        steps.end_kernel_step_unchanged(&*krnl, &*lctx);
    }
}

/// Validates the arguments and locks the cpu, its container, process, and thread, rejecting every failing check with all
/// locks released and a stutter trace; otherwise returns the four locks held with the caller's quota and endpoint slot checked.
fn new_container_lock_owners(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    va: usize, range: usize, funding_page_count: usize, process_quota_4k: usize, transfer_cpu_id: CpuId, endpoint_index: Option<EndpointIdx>,
    initial_regs: &Registers,
) -> (ret: Result<NewContainerOwnersLocked, RetValueType>)
    requires
        index_valid(NUM_CPUS, cpu_id),
        endpoint_index is Some ==> edp_idx_valid(endpoint_index->Some_0),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        old(steps).nonlock_view().len() == 0,
        old(steps).snapshot_k() == *old(krnl),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        ret is Err ==> ({
            let r = ret->Err_0;
            &&& new_container_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs, endpoint_index, r)
            &&& final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl))
            &&& final(steps).snapshot_k() == *final(krnl)
            &&& final(krnl).all_objects_unlocked(final(lctx))
            &&& typed_lock_maps_aligned(final(krnl), final(lctx))
            &&& final(lctx).no_locks_held()
            &&& final(steps).nonlock_view().len() == 0
            &&& !(r is SuccessThreeUsize)
            &&& !(new_container_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, endpoint_index) is Success)
            &&& r == new_container_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, endpoint_index)
        }),
        ret is Ok ==> ({
            let e = ret->Ok_0;
            &&& *final(steps) == *old(steps)
            &&& e.source_range == (VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) })
            &&& e.source_range.wf()
            &&& 0 < range <= (usize::MAX - 9) / 3 && range <= usize::MAX / 4096 && va_4k_valid(va) && index_valid(NUM_CPUS, transfer_cpu_id)
            &&& va < usize::MAX - range * 4096 && va_4k_range_valid(va, range)
            &&& process_quota_4k <= funding_page_count && funding_page_count <= usize::MAX - 9 - 3 * range
            &&& *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, cpu_op: final(krnl).cpu_op, ctn_mp: final(krnl).ctn_mp, prc_mp: final(krnl).prc_mp, thr_mp: final(krnl).thr_mp, ..*old(krnl) })
            &&& final(krnl).cpu_arr.entries_unchanged_except(&old(krnl).cpu_arr, cpu_id)
            &&& final(krnl).cpu_op.view().view() == old(krnl).cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep)
            &&& final(krnl).ctn_mp.unchanged_except(&old(krnl).ctn_mp, e.parent_container_ptr)
            &&& final(krnl).prc_mp.unchanged_except(&old(krnl).prc_mp, e.parent_process_ptr)
            &&& final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, e.current_thread_ptr)
            &&& old(krnl).cpu_arr.spec_index(cpu_id).value.locking_thread() is None
            &&& old(krnl).ctn_mp.spec_index(e.parent_container_ptr).locking_thread() is None
            &&& old(krnl).prc_mp.spec_index(e.parent_process_ptr).locking_thread() is None
            &&& old(krnl).thr_mp.spec_index(e.current_thread_ptr).locking_thread() is None
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view()
            &&& final(krnl).ctn_mp.spec_index(e.parent_container_ptr).view() == old(krnl).ctn_mp.spec_index(e.parent_container_ptr).view()
            &&& final(krnl).ctn_mp.spec_index(e.parent_container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(e.parent_container_ptr).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(e.parent_container_ptr).view_ghost() == old(krnl).ctn_mp.spec_index(e.parent_container_ptr).view_ghost()
            &&& final(krnl).prc_mp.spec_index(e.parent_process_ptr).view() == old(krnl).prc_mp.spec_index(e.parent_process_ptr).view()
            &&& final(krnl).prc_mp.spec_index(e.parent_process_ptr).view_rodata() == old(krnl).prc_mp.spec_index(e.parent_process_ptr).view_rodata()
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view() == old(krnl).thr_mp.spec_index(e.current_thread_ptr).view()
            &&& final(krnl).inv()
            &&& final(lctx).kernel_view_locking_state() is Acquire
            &&& kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl))
            &&& kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl))
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state == CpuState::Running
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(e.current_thread_ptr)
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == e.parent_container_ptr
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(e.parent_process_ptr)
            &&& !final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() && !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed()
            &&& final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid)
            &&& final(lctx).page_lock_map().dom().is_empty() && final(lctx).endpoint_lock_map().dom().is_empty() && final(lctx).pagetable_lock_map().dom().is_empty() && final(lctx).pagetable_window_lock_map().dom().is_empty()
            &&& final(lctx).scheduler_lock_map().dom().is_empty() && final(lctx).pcid_allocator_lock_map().dom().is_empty() && final(lctx).cpu_set_lock_map().dom().is_empty()
            &&& final(lctx).iommu_table_lock_map().dom().is_empty() && final(lctx).iommu_root_table_lock_map().dom().is_empty() && final(lctx).pcid_needflush_lock_map().dom().is_empty()
            &&& final(lctx).cpu_offline_flag_lock_map().dom().is_empty()
            &&& final(lctx).holds_no_allocator_locks(PageSize::SZ4k) && final(lctx).holds_no_allocator_locks(PageSize::SZ2m) && final(lctx).holds_no_allocator_locks(PageSize::SZ1g)
            &&& final(lctx).cpu_lock_map().dom() =~= set![cpu_id]
            &&& final(lctx).container_lock_map().dom() =~= set![e.parent_container_ptr]
            &&& final(lctx).process_lock_map().dom() =~= set![e.parent_process_ptr]
            &&& final(lctx).thread_lock_map().dom() =~= set![e.current_thread_ptr]
            &&& typed_lock_maps_aligned(final(krnl), final(lctx))
            &&& typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write)
            &&& e.cpu_lock_perm.view().state() is WriteLock
            &&& e.cpu_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& e.cpu_lock_perm.view().lock_id() == final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id
            &&& final(krnl).ctn_mp.dom().contains(e.parent_container_ptr)
            &&& typed_lock_map_contains_mode(final(lctx).container_lock_map(), e.parent_container_ptr, TypedLockMode::Write)
            &&& !final(krnl).ctn_mp.spec_index(e.parent_container_ptr).being_killed()
            &&& !old(krnl).ctn_mp.spec_index(e.parent_container_ptr).being_killed()
            &&& !final(krnl).ctn_mp.spec_index(e.parent_container_ptr).view().zombie
            &&& final(krnl).ctn_mp.spec_index(e.parent_container_ptr).lock_process_owner_u() == Some(LockOwnerId::Some(final(krnl).prc_mp.spec_index(e.parent_process_ptr).view_rodata().view().depth))
            &&& final(krnl).ctn_mp.spec_index(e.parent_container_ptr).view_rodata().view().depth < MAX_CONTAINER_TREE_DEPTH
            &&& final(krnl).ctn_mp.spec_index(e.parent_container_ptr).view_rodata().view().cpu_set == e.parent_cpu_set
            &&& !final(krnl).ctn_mp.spec_index(e.parent_container_ptr).view_ghost().owned_processes.view().is_empty()
            &&& e.container_lock_perm.view().state() is WriteLock
            &&& e.container_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& e.container_lock_perm.view().lock_id() == final(krnl).ctn_mp.spec_index(e.parent_container_ptr).locking_thread()->Write_lock_id
            &&& final(krnl).prc_mp.dom().contains(e.parent_process_ptr)
            &&& typed_lock_map_contains_mode(final(lctx).process_lock_map(), e.parent_process_ptr, TypedLockMode::Write)
            &&& !final(krnl).prc_mp.spec_index(e.parent_process_ptr).being_killed()
            &&& !old(krnl).prc_mp.spec_index(e.parent_process_ptr).being_killed()
            &&& final(krnl).prc_mp.spec_index(e.parent_process_ptr).view_rodata().view().owning_container == e.parent_container_ptr
            &&& (final(krnl).prc_mp.spec_index(e.parent_process_ptr).view().state.view() is Running || final(krnl).prc_mp.spec_index(e.parent_process_ptr).view().state.view() is Zombie)
            &&& !old(krnl).prc_mp.spec_index(e.parent_process_ptr).view().zombie
            &&& e.process_lock_perm.view().state() is WriteLock
            &&& e.process_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& e.process_lock_perm.view().lock_id() == final(krnl).prc_mp.spec_index(e.parent_process_ptr).locking_thread()->Write_lock_id
            &&& final(krnl).thr_mp.dom().contains(e.current_thread_ptr)
            &&& typed_lock_map_contains_mode(final(lctx).thread_lock_map(), e.current_thread_ptr, TypedLockMode::Write)
            &&& !final(krnl).thr_mp.spec_index(e.current_thread_ptr).being_killed()
            &&& !old(krnl).thr_mp.spec_index(e.current_thread_ptr).being_killed()
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().owning_container == e.parent_container_ptr
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().owning_proc == e.parent_process_ptr
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().proc_pagetable_ptr == e.source_pagetable_ptr
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id: cpu_id })
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().temp_alloc_clean()
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().syscall_progress.view() is None
            &&& !final(krnl).thr_mp.spec_index(e.current_thread_ptr).view_ghost().exited
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().free_quota_pending_clean()
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().quota_4k >= 9 + funding_page_count + 3 * range
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().quota_2m >= 2
            &&& endpoint_index is Some ==> old(krnl).thr_mp.spec_index(e.current_thread_ptr).view().endpoint_descriptors.wf()
            &&& endpoint_index is Some ==> e.endpoint is Some && e.endpoint == final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index->Some_0)
            &&& endpoint_index is None ==> e.endpoint is None
            &&& e.thread_lock_perm.view().state() is WriteLock
            &&& e.thread_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& e.thread_lock_perm.view().lock_id() == final(krnl).thr_mp.spec_index(e.current_thread_ptr).locking_thread()->Write_lock_id
        }),
{
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    if range == 0 || range > usize::MAX / 4096usize || range > (usize::MAX - 9usize) / 3usize || !va_4k_valid(va) || transfer_cpu_id >= NUM_CPUS {
        proof {
            enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); steps.end_kernel_step_unchanged(&*krnl, &*lctx);
            new_container_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs, endpoint_index,
                RetValueType::Error);
        }
        return Err(RetValueType::Error);
    }
    let span = range * 4096usize;
    if va >= usize::MAX - span || !va_4k_range_valid(va, range) {
        proof {
            enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); steps.end_kernel_step_unchanged(&*krnl, &*lctx);
            new_container_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs, endpoint_index,
                RetValueType::Error);
        }
        return Err(RetValueType::Error);
    }
    let source_range = VaRange4K::new(va, range);
    if process_quota_4k > funding_page_count || funding_page_count > usize::MAX - 9 - 3 * range {
        proof {
            enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); steps.end_kernel_step_unchanged(&*krnl, &*lctx);
            new_container_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs, endpoint_index,
                RetValueType::Error);
        }
        return Err(RetValueType::Error);
    }
    let cpu_lock_res = wlock_cpu_if_running(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id);
    if cpu_lock_res.is_none() {
        proof {
            new_container_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs, endpoint_index, RetValueType::CpuIdle);
            new_container_result_from_k(old(krnl), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, endpoint_index, RetValueType::CpuIdle);
        }
        return Err(RetValueType::CpuIdle);
    }
    let Tracked(cpu_lock_perm) = cpu_lock_res.unwrap();
    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    let parent_container_ptr = cpu.owning_container();
    let parent_process_ptr = cpu.current_process().unwrap();
    let current_thread_ptr = cpu.current_thread().unwrap();
    proof {
        assert(krnl.ctn_mp.dom().contains(parent_container_ptr) && krnl.ctn_mp.spec_index(parent_container_ptr).view_rodata().view().depth == krnl.cpu_arr.spec_index(cpu_id).view().view().view().container_depth) by {
            container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id);
        };
        assert({
            &&& krnl.prc_mp.dom().contains(parent_process_ptr)
            &&& krnl.prc_mp.spec_index(parent_process_ptr).view_rodata().view().owning_container == parent_container_ptr
            &&& !krnl.prc_mp.spec_index(parent_process_ptr).view().zombie
            &&& krnl.prc_mp.spec_index(parent_process_ptr).view_rodata().view().depth == krnl.cpu_arr.spec_index(cpu_id).view().view().view().process_depth
            &&& krnl.prc_mp.spec_index(parent_process_ptr).view_rodata().view().container_depth == krnl.ctn_mp.spec_index(parent_container_ptr).view_rodata().view().depth
        }) by { process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, parent_process_ptr); };
        assert({
            &&& krnl.thr_mp.dom().contains(current_thread_ptr)
            &&& krnl.thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id })
            &&& krnl.thr_mp.spec_index(current_thread_ptr).view().owning_container == parent_container_ptr
            &&& krnl.thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_process_ptr
            &&& krnl.thr_mp.spec_index(current_thread_ptr).view().container_depth == krnl.prc_mp.spec_index(parent_process_ptr).view_rodata().view().container_depth
            &&& krnl.thr_mp.spec_index(current_thread_ptr).view().process_depth == krnl.prc_mp.spec_index(parent_process_ptr).view_rodata().view().depth
        }) by { thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, current_thread_ptr); };
    }
    let requested = LockOwnerId::Some(krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm)).process_depth());
    let container_res = krnl.wlock_container_unless_killed(parent_container_ptr, requested, Tracked(&mut *lctx));
    let Tracked(container_lock_perm) = match container_res {
        DynamicWLockResult::Acquired(perm) => perm,
        DynamicWLockResult::Killed(_) => {
            krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
            proof {
                assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
                steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(parent_container_ptr), None, None, None, None, None);
                new_container_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs, endpoint_index,
                    RetValueType::ErrorContainerKilled);
                new_container_result_from_k(old(krnl), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, endpoint_index, RetValueType::ErrorContainerKilled);
            }
            return Err(RetValueType::ErrorContainerKilled);
        },
        DynamicWLockResult::DepthConflict { .. } => {
            proof { assert(krnl.pt_mp.dom().contains(krnl.prc_mp.spec_index(parent_process_ptr).view().pagetable)) by { process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, parent_process_ptr); }; }
            krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
            proof {
                assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
                steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(parent_container_ptr), None, None, None, None, None);
                new_container_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs, endpoint_index,
                    RetValueType::ErrorContainerLockOrderConflict);
                new_container_result_from_k(old(krnl), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, endpoint_index, RetValueType::ErrorContainerLockOrderConflict);
            }
            return Err(RetValueType::ErrorContainerLockOrderConflict);
        },
    };
    proof { assert(!krnl.ctn_mp.spec_index(parent_container_ptr).view_ghost().owned_processes.view().is_empty()) by { container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, parent_process_ptr); }; }
    let parent_container = krnl.ctn_mp.borrow_typed(parent_container_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(&container_lock_perm));
    let parent_zombie = parent_container.zombie;
    let parent_depth = krnl.ctn_mp.borrow_rodata(parent_container_ptr).borrow().depth;
    let parent_cpu_set = krnl.ctn_mp.borrow_rodata(parent_container_ptr).borrow().cpu_set;
    if parent_zombie || parent_depth >= MAX_CONTAINER_TREE_DEPTH {
        let error = if parent_zombie { RetValueType::ErrorContainerZombie } else { RetValueType::Error };
        krnl.wunlock_container(parent_container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(parent_container_ptr), None, None, None, None, None);
            new_container_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs, endpoint_index,
                error);
            new_container_result_from_k(old(krnl), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, endpoint_index, error);
        }
        return Err(error);
    }
    proof {
        assert(source_range == (VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) })) by { source_range.va_range_lemma(); };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    new_container_lock_process_and_thread(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, endpoint_index, initial_regs,
        source_range, parent_container_ptr, parent_process_ptr, current_thread_ptr, parent_cpu_set, Tracked(cpu_lock_perm), Tracked(container_lock_perm),
    )
}

/// Takes the owner locks from `new_container_lock_owners`, then locks the optional endpoint, source pagetable, and cpu set,
/// rejecting every failing check with all locks released and a stutter trace; otherwise the locks are returned held with
/// exactly the state `commit_new_container` requires, and the syscall result is pinned to Success.
#[verifier::spinoff_prover]
fn new_container_lock_entry(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    va: usize, range: usize, funding_page_count: usize, process_quota_4k: usize, transfer_cpu_id: CpuId, endpoint_index: Option<EndpointIdx>,
    initial_regs: &Registers,
) -> (ret: Result<NewContainerEntryLocked, RetValueType>)
    requires
        index_valid(NUM_CPUS, cpu_id),
        endpoint_index is Some ==> edp_idx_valid(endpoint_index->Some_0),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        old(steps).nonlock_view().len() == 0,
        old(steps).snapshot_k() == *old(krnl),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        ret is Err ==> ({
            let r = ret->Err_0;
            &&& new_container_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs, endpoint_index, r)
            &&& final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl))
            &&& final(steps).snapshot_k() == *final(krnl)
            &&& final(krnl).all_objects_unlocked(final(lctx))
            &&& typed_lock_maps_aligned(final(krnl), final(lctx))
            &&& final(lctx).no_locks_held()
            &&& final(steps).nonlock_view().len() == 0
            &&& !(r is SuccessThreeUsize)
            &&& !(new_container_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, endpoint_index) is Success)
            &&& r == new_container_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, endpoint_index)
        }),
        ret is Ok ==> ({
            let e = ret->Ok_0;
            &&& *final(steps) == *old(steps)
            &&& e.source_range == (VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) })
            &&& new_container_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, endpoint_index) is Success
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, cpu_op: final(krnl).cpu_op, ctn_mp: final(krnl).ctn_mp, prc_mp: final(krnl).prc_mp,
                thr_mp: final(krnl).thr_mp, ep_mp: final(krnl).ep_mp, pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, cpu_set_mp: final(krnl).cpu_set_mp, ..*old(krnl) })
            &&& (e.endpoint is Some) == (endpoint_index is Some)
            &&& endpoint_index is Some ==> e.endpoint_slot == endpoint_index->Some_0
            &&& endpoint_index is Some ==> old(krnl).thr_mp.spec_index(e.current_thread_ptr).view().endpoint_descriptors.wf()
            &&& endpoint_index is Some ==> e.endpoint == old(krnl).thr_mp.spec_index(e.current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index->Some_0)
            &&& e.endpoint is Some ==> old(krnl).ep_mp.spec_index(e.endpoint->Some_0).locking_thread() is None
            &&& match e.endpoint { Some(p) => final(krnl).ep_mp.unchanged_except(&old(krnl).ep_mp, p), None => final(krnl).ep_mp == old(krnl).ep_mp }
            &&& final(krnl).cpu_arr.entries_unchanged_except(&old(krnl).cpu_arr, cpu_id)
            &&& final(krnl).cpu_op.view().view() == old(krnl).cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep)
            &&& final(krnl).ctn_mp.unchanged_except(&old(krnl).ctn_mp, e.parent_container_ptr)
            &&& final(krnl).prc_mp.unchanged_except(&old(krnl).prc_mp, e.parent_process_ptr)
            &&& final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, e.current_thread_ptr)
            &&& final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, e.source_pagetable_ptr)
            &&& old(krnl).cpu_arr.spec_index(cpu_id).value.locking_thread() is None
            &&& old(krnl).ctn_mp.spec_index(e.parent_container_ptr).locking_thread() is None
            &&& old(krnl).prc_mp.spec_index(e.parent_process_ptr).locking_thread() is None
            &&& old(krnl).thr_mp.spec_index(e.current_thread_ptr).locking_thread() is None
            &&& !(old(krnl).pt_mp.spec_index(e.source_pagetable_ptr).locking_thread() is Write)
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state == CpuState::Running
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(e.current_thread_ptr)
            &&& final(krnl).pt_mp.spec_index(e.source_pagetable_ptr).view() == old(krnl).pt_mp.spec_index(e.source_pagetable_ptr).view()
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), e.source_pagetable_ptr).wf()
            &&& final(krnl).inv()
            &&& final(lctx).kernel_view_locking_state() is Acquire
            &&& kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl))
            &&& kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp)
            &&& kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &KernelK { cpu_set_mp: old(krnl).cpu_set_mp, ..*final(krnl) })
            &&& final(krnl).cpu_set_mp.unchanged_except(&old(krnl).cpu_set_mp, e.parent_cpu_set)
            &&& old(krnl).cpu_set_mp.spec_index(e.parent_cpu_set).locking_thread() is None
            &&& !old(krnl).cpu_set_mp.spec_index(e.parent_cpu_set).being_killed() && !final(krnl).cpu_set_mp.spec_index(e.parent_cpu_set).being_killed()
            &&& cpu_id == final(lctx).cpu_id()
            &&& final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid)
            &&& process_quota_4k <= funding_page_count
            &&& funding_page_count <= usize::MAX - 9 - 3 * e.source_range.len
            &&& e.source_range.wf()
            &&& e.source_range.len > 0
            &&& e.source_range.len <= (usize::MAX - 9) / 3
            &&& index_valid(NUM_CPUS, transfer_cpu_id)
            &&& final(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().state is Off
            &&& final(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().owning_container == e.parent_container_ptr
            &&& transfer_cpu_id != cpu_id
            &&& final(krnl).cpu_set_mp.dom().contains(e.parent_cpu_set)
            &&& final(krnl).cpu_set_mp.spec_index(e.parent_cpu_set).view().owned_cpus.closed_view().contains(transfer_cpu_id)
            &&& final(krnl).ctn_mp.spec_index(e.parent_container_ptr).view_rodata().view().cpu_set == e.parent_cpu_set
            &&& typed_lock_map_contains_mode(final(lctx).cpu_set_lock_map(), e.parent_cpu_set, TypedLockMode::Write)
            &&& e.cpu_set_lock_perm.view().state() is WriteLock
            &&& e.cpu_set_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& e.cpu_set_lock_perm.view().lock_id() == final(krnl).cpu_set_mp.spec_index(e.parent_cpu_set).locking_thread()->Write_lock_id
            &&& final(krnl).pt_mp.spec_index(e.source_pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(e.source_range.start)
            &&& final(lctx).page_lock_map().dom().is_empty()
            &&& final(lctx).cpu_lock_map().dom() =~= set![cpu_id]
            &&& final(lctx).container_lock_map().dom() =~= set![e.parent_container_ptr]
            &&& final(lctx).process_lock_map().dom() =~= set![e.parent_process_ptr]
            &&& final(lctx).thread_lock_map().dom() =~= set![e.current_thread_ptr]
            &&& e.endpoint is None ==> final(lctx).endpoint_lock_map().dom().is_empty()
            &&& e.endpoint is Some ==> {
                let endpoint_ptr = e.endpoint->Some_0;
                &&& edp_idx_valid(e.endpoint_slot)
                &&& final(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr]
                &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().endpoint_descriptors.wf()
                &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().endpoint_descriptors.spec_index(e.endpoint_slot) == e.endpoint
                &&& final(krnl).ep_mp.dom().contains(endpoint_ptr)
                &&& final(krnl).ep_mp.spec_index(endpoint_ptr).is_init()
                &&& typed_lock_map_contains_mode(final(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write)
                &&& !final(krnl).ep_mp.spec_index(endpoint_ptr).being_killed()
                &&& final(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((e.current_thread_ptr, e.endpoint_slot))
                &&& e.endpoint_lock_perm.view() is Some
                &&& e.endpoint_lock_perm.view()->Some_0.state() is WriteLock
                &&& e.endpoint_lock_perm.view()->Some_0.thread_id() == final(lctx).thread_id()
                &&& e.endpoint_lock_perm.view()->Some_0.lock_id() == final(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id
            }
            &&& final(lctx).scheduler_lock_map().dom().is_empty()
            &&& final(lctx).pcid_allocator_lock_map().dom().is_empty()
            &&& final(lctx).cpu_set_lock_map().dom() =~= set![e.parent_cpu_set]
            &&& final(lctx).pagetable_lock_map().dom() =~= set![e.source_pagetable_ptr]
            &&& final(lctx).iommu_table_lock_map().dom().is_empty()
            &&& final(lctx).iommu_root_table_lock_map().dom().is_empty()
            &&& held_locks_order_below(final(krnl), final(lctx), ALLOCATOR_CACHE_4K_MAJOR)
            &&& typed_lock_maps_aligned(final(krnl), final(lctx))
            &&& typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write)
            &&& !final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed()
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == e.parent_container_ptr
            &&& e.cpu_lock_perm.view().state() is WriteLock
            &&& e.cpu_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& e.cpu_lock_perm.view().lock_id() == final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id
            &&& final(krnl).ctn_mp.dom().contains(e.parent_container_ptr)
            &&& typed_lock_map_contains_mode(final(lctx).container_lock_map(), e.parent_container_ptr, TypedLockMode::Write)
            &&& !final(krnl).ctn_mp.spec_index(e.parent_container_ptr).being_killed()
            &&& !final(krnl).ctn_mp.spec_index(e.parent_container_ptr).view().zombie
            &&& final(krnl).ctn_mp.spec_index(e.parent_container_ptr).lock_process_owner_u() == Some(LockOwnerId::Some(final(krnl).prc_mp.spec_index(e.parent_process_ptr).view_rodata().view().depth))
            &&& final(krnl).ctn_mp.spec_index(e.parent_container_ptr).view_rodata().view().depth < MAX_CONTAINER_TREE_DEPTH
            &&& e.container_lock_perm.view().state() is WriteLock
            &&& e.container_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& e.container_lock_perm.view().lock_id() == final(krnl).ctn_mp.spec_index(e.parent_container_ptr).locking_thread()->Write_lock_id
            &&& final(krnl).prc_mp.dom().contains(e.parent_process_ptr)
            &&& typed_lock_map_contains_mode(final(lctx).process_lock_map(), e.parent_process_ptr, TypedLockMode::Write)
            &&& !final(krnl).prc_mp.spec_index(e.parent_process_ptr).being_killed()
            &&& final(krnl).prc_mp.spec_index(e.parent_process_ptr).view_rodata().view().owning_container == e.parent_container_ptr
            &&& (final(krnl).prc_mp.spec_index(e.parent_process_ptr).view().state.view() is Running || final(krnl).prc_mp.spec_index(e.parent_process_ptr).view().state.view() is Zombie)
            &&& e.process_lock_perm.view().state() is WriteLock
            &&& e.process_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& e.process_lock_perm.view().lock_id() == final(krnl).prc_mp.spec_index(e.parent_process_ptr).locking_thread()->Write_lock_id
            &&& final(krnl).thr_mp.dom().contains(e.current_thread_ptr)
            &&& typed_lock_map_contains_mode(final(lctx).thread_lock_map(), e.current_thread_ptr, TypedLockMode::Write)
            &&& !final(krnl).thr_mp.spec_index(e.current_thread_ptr).being_killed()
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().owning_container == e.parent_container_ptr
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().owning_proc == e.parent_process_ptr
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().proc_pagetable_ptr == e.source_pagetable_ptr
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id: cpu_id })
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().temp_alloc_clean()
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().syscall_progress.view() is None
            &&& !final(krnl).thr_mp.spec_index(e.current_thread_ptr).view_ghost().exited
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().free_quota_pending_clean()
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().quota_4k >= 9 + funding_page_count + 3 * e.source_range.len
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().quota_2m >= 2
            &&& e.thread_lock_perm.view().state() is WriteLock
            &&& e.thread_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& e.thread_lock_perm.view().lock_id() == final(krnl).thr_mp.spec_index(e.current_thread_ptr).locking_thread()->Write_lock_id
            &&& final(krnl).pt_mp.dom().contains(e.source_pagetable_ptr)
            &&& typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), e.source_pagetable_ptr, TypedLockMode::Read)
            &&& e.source_pagetable_lock_perm.view().state() is ReadLock
            &&& e.source_pagetable_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& final(krnl).pt_mp.spec_index(e.source_pagetable_ptr).locking_thread() is Read
            &&& final(krnl).pt_mp.spec_index(e.source_pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(final(lctx).thread_id(), e.source_pagetable_lock_perm.view().lock_id())
        }),
        ret is Ok ==> forall|j: int| #![trigger ret->Ok_0.source_range.view().spec_index(j)] 0 <= j < ret->Ok_0.source_range.len ==> {
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), ret->Ok_0.source_pagetable_ptr).mapping_4k().dom().contains(ret->Ok_0.source_range.view().spec_index(j))
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), ret->Ok_0.source_pagetable_ptr).mapping_4k().spec_index(ret->Ok_0.source_range.view().spec_index(j)).present
        },
        ret is Ok ==> forall|w: WindowVa| #![trigger va_range_2m_windows(ret->Ok_0.source_range).contains(w)]
            va_range_2m_windows(ret->Ok_0.source_range).contains(w)
                && pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), ret->Ok_0.source_pagetable_ptr).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                ==> ret->Ok_0.source_window_perms.view().dom().contains(w),
        ret is Ok ==> forall|w: WindowVa| #![trigger ret->Ok_0.source_window_perms.view().dom().contains(w)] ret->Ok_0.source_window_perms.view().dom().contains(w) ==> {
            &&& va_range_2m_windows(ret->Ok_0.source_range).contains(w)
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), ret->Ok_0.source_pagetable_ptr).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
            &&& typed_lock_map_contains_mode(final(lctx).pagetable_window_lock_map(), (ret->Ok_0.source_pagetable_ptr, w), TypedLockMode::Write)
            &&& ret->Ok_0.source_window_perms.view().index(w).state() is WriteLock
            &&& ret->Ok_0.source_window_perms.view().index(w).thread_id() == final(lctx).thread_id()
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), ret->Ok_0.source_pagetable_ptr).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(),
                ret->Ok_0.source_pagetable_ptr).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va))).lock_perm_match(spec_v2l2index(w.va), &ret->Ok_0.source_window_perms.view().index(w))
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), ret->Ok_0.source_pagetable_ptr).window_leaves_present(w)
            &&& !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), ret->Ok_0.source_pagetable_ptr).lower.window_stale_cpus.dom().contains((pagetable_c(final(krnl).pt_mp,
                final(krnl).pt_lower.view(), ret->Ok_0.source_pagetable_ptr).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
        },
        ret is Ok ==> forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == ret->Ok_0.source_pagetable_ptr && ret->Ok_0.source_window_perms.view().dom().contains(w)),
{
    let owners = match new_container_lock_owners(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, endpoint_index, initial_regs,
    ) {
        Ok(owners) => owners,
        Err(error) => return Err(error),
    };
    let NewContainerOwnersLocked {
        parent_container_ptr, parent_process_ptr, current_thread_ptr, source_pagetable_ptr, parent_cpu_set, source_range, endpoint: endpoint_option,
        cpu_lock_perm, container_lock_perm, process_lock_perm, thread_lock_perm,
    } = owners;
    let endpoint_ptr = match endpoint_option { Some(ptr) => ptr, None => 0 };
    let tracked mut endpoint_lock_perm_opt: Option<LockPerm> = None;
    if endpoint_index.is_some() {
        proof {
            assert(krnl.ep_mp.dom().contains(endpoint_ptr) && krnl.ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((current_thread_ptr, endpoint_index->Some_0))) by {
                thread_endpoint_ref_counter_wf_thread_at(krnl.thr_mp, krnl.ep_mp, current_thread_ptr, endpoint_index->Some_0);
            };
        }
        let Tracked(endpoint_lock_perm) = krnl.wlock_endpoint(endpoint_ptr, Tracked(&mut *lctx));
        proof { endpoint_lock_perm_opt = Some(endpoint_lock_perm); }
    }
    proof {
        assert({
            &&& krnl.pt_mp.dom().contains(source_pagetable_ptr)
            &&& !lctx.pagetable_lock_map().dom().contains(source_pagetable_ptr)
            &&& krnl.prc_mp.spec_index(parent_process_ptr).view().pagetable == source_pagetable_ptr
        }) by { process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, current_thread_ptr); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, parent_process_ptr); };
    }
    proof {
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, source_pagetable_ptr);
        krnl.pt_mp.typed_lock_map_aligned_locked_at(lctx.pagetable_lock_map(), lctx.thread_id(), source_pagetable_ptr);
    }
    let Tracked(source_pagetable_lock_perm) = krnl.rlock_pagetable(source_pagetable_ptr, Tracked(&mut *lctx));
    proof { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, source_pagetable_ptr); }
    let (l4_ok, source_ready, source_window_perms) = new_container_lock_source_windows(krnl, Tracked(&mut *lctx), source_pagetable_ptr, &source_range, Tracked(&source_pagetable_lock_perm));
    let Tracked(source_window_perms) = source_window_perms;
    proof {
        assert(krnl.cpu_set_mp.dom().contains(parent_cpu_set)) by { container_cpu_set_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, parent_container_ptr); };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        // The caller's thread lives in the parent container, so its cpu set is not marked.
        assert(!krnl.cpu_set_mp.spec_index(parent_cpu_set).being_killed()) by {
            container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, current_thread_ptr); container_cpu_set_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, parent_container_ptr);
            cpu_set_kill_mark_wf_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.prc_mp, parent_cpu_set);
        };
    }
    let ghost cpu_set_unlocked_k = *krnl;
    let Tracked(cpu_set_lock_perm) = krnl.wlock_cpu_set(parent_cpu_set, Tracked(&mut *lctx));
    let parent_set = krnl.cpu_set_mp.borrow_typed(parent_cpu_set, Ghost(lctx.cpu_set_lock_map()), Tracked(&*lctx), Tracked(&cpu_set_lock_perm));
    let transfer_cpu_owned = parent_set.owned_cpus.contains(transfer_cpu_id);
    let transfer_cpu_off = parent_set.owned_cpus.is_closed(transfer_cpu_id);
    proof { assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; }; }
    if !source_ready || !transfer_cpu_owned || !transfer_cpu_off {
        let error = if !source_ready { RetValueType::Error } else if !transfer_cpu_owned { RetValueType::ErrorIpcCpuOwnerMismatch } else { RetValueType::ErrorIpcCpuNotOff };
        proof {
            assert(new_container_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, endpoint_index) == error) by {
                reveal(container_cpu_wf); new_container_result_from_k(old(krnl), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, endpoint_index, error);
            };
        }
        new_container_release_entry_locks(
            krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, parent_container_ptr, parent_process_ptr, current_thread_ptr, source_pagetable_ptr, parent_cpu_set,
            endpoint_option, &source_range, l4_ok, Ghost(cpu_set_unlocked_k), cpu_lock_perm, container_lock_perm, process_lock_perm, thread_lock_perm,
            Tracked(source_pagetable_lock_perm), Tracked(cpu_set_lock_perm), Tracked(endpoint_lock_perm_opt), Tracked(source_window_perms),
        );
        proof {
            new_container_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs, endpoint_index, error);
        }
        return Err(error);
    }
    proof {
        assert(krnl.cpu_arr.spec_index(transfer_cpu_id).view().view().view().state is Off
            && krnl.cpu_arr.spec_index(transfer_cpu_id).view().view().view().owning_container == parent_container_ptr) by { container_cpu_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, parent_container_ptr, transfer_cpu_id); };
        new_container_result_from_k(old(krnl), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, endpoint_index, RetValueType::Success);
        pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable_ptr);
    }
    let (endpoint, endpoint_slot) = match endpoint_index { Some(index) => (Some(endpoint_ptr), index), None => (None, 0) };
    Ok(NewContainerEntryLocked {
        parent_container_ptr, parent_process_ptr, current_thread_ptr, source_pagetable_ptr, parent_cpu_set, source_range, endpoint, endpoint_slot,
        cpu_lock_perm, container_lock_perm, process_lock_perm,
        thread_lock_perm, source_pagetable_lock_perm: Tracked(source_pagetable_lock_perm), cpu_set_lock_perm: Tracked(cpu_set_lock_perm),
        endpoint_lock_perm: Tracked(endpoint_lock_perm_opt), source_window_perms: Tracked(source_window_perms),
    })
}

/// Shared body of the container-creation syscalls: `endpoint_index` seeds the child's root thread.
fn syscall_new_container_common(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    va: usize, range: usize, funding_page_count: usize, process_quota_4k: usize, transfer_cpu_id: CpuId, endpoint_index: Option<EndpointIdx>,
    initial_regs: &Registers,
) -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
        endpoint_index is Some ==> edp_idx_valid(endpoint_index->Some_0),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        old(steps).nonlock_view().len() == 0,
        old(steps).snapshot_k() == *old(krnl),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        new_container_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
            kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, va, range,
            funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs, endpoint_index, ret),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).no_locks_held(),
        !(ret is SuccessThreeUsize) ==> final(steps).nonlock_view().len() == 0,
        ret is SuccessThreeUsize ==> range as int + 3 <= final(steps).nonlock_view().len() as int <= 4 * range as int + 3,
        (ret is SuccessThreeUsize) == (new_container_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, endpoint_index) is Success),
        !(ret is SuccessThreeUsize) ==> ret == new_container_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, endpoint_index),
{
    let entry = match new_container_lock_entry(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, endpoint_index, initial_regs) {
        Ok(entry) => entry,
        Err(ret) => return ret,
    };
    let NewContainerEntryLocked {
        parent_container_ptr, parent_process_ptr, current_thread_ptr, source_pagetable_ptr, parent_cpu_set, source_range, endpoint, endpoint_slot, cpu_lock_perm,
        container_lock_perm, process_lock_perm, thread_lock_perm, source_pagetable_lock_perm, cpu_set_lock_perm, endpoint_lock_perm, source_window_perms,
    } = entry;
    let (child_container_ptr, child_process_ptr, new_thread_ptr) = commit_new_container(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, parent_container_ptr, parent_process_ptr, current_thread_ptr, source_pagetable_ptr,
        &source_range, funding_page_count, process_quota_4k, transfer_cpu_id, parent_cpu_set, endpoint, endpoint_slot, cpu_lock_perm, container_lock_perm,
        process_lock_perm, thread_lock_perm, source_pagetable_lock_perm, cpu_set_lock_perm, endpoint_lock_perm, source_window_perms, initial_regs,
    );
    let ret = RetValueType::SuccessThreeUsize { value1: child_container_ptr, value2: child_process_ptr, value3: new_thread_ptr };
    proof {
        new_container_syscall_trace_from_commit(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), cpu_id, va, range, funding_page_count,
            process_quota_4k, transfer_cpu_id, *initial_regs, endpoint_index, ret);
    }
    ret
}

/// Creates a child container of the caller's container whose root thread starts with no endpoint.
pub fn syscall_new_container(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    va: usize, range: usize, funding_page_count: usize, process_quota_4k: usize, transfer_cpu_id: CpuId, initial_regs: &Registers,
) -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        old(steps).nonlock_view().len() == 0,
        old(steps).snapshot_k() == *old(krnl),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        new_container_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
            kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, va, range,
            funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs, None, ret),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).no_locks_held(),
        !(ret is SuccessThreeUsize) ==> final(steps).nonlock_view().len() == 0,
        ret is SuccessThreeUsize ==> range as int + 3 <= final(steps).nonlock_view().len() as int <= 4 * range as int + 3,
        (ret is SuccessThreeUsize) == (new_container_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, None) is Success),
        !(ret is SuccessThreeUsize) ==> ret == new_container_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, None),
{
    syscall_new_container_common(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, None, initial_regs)
}

/// Creates a child container of the caller's container whose root thread holds, in descriptor 0, the
/// endpoint of the caller's descriptor `endpoint_index`.
pub fn syscall_new_container_with_endpoint(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    va: usize, range: usize, funding_page_count: usize, process_quota_4k: usize, transfer_cpu_id: CpuId, endpoint_index: EndpointIdx,
    initial_regs: &Registers,
) -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
        edp_idx_valid(endpoint_index),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        old(steps).nonlock_view().len() == 0,
        old(steps).snapshot_k() == *old(krnl),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        new_container_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
            kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, va, range,
            funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs, Some(endpoint_index), ret),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).no_locks_held(),
        !(ret is SuccessThreeUsize) ==> final(steps).nonlock_view().len() == 0,
        ret is SuccessThreeUsize ==> range as int + 3 <= final(steps).nonlock_view().len() as int <= 4 * range as int + 3,
        (ret is SuccessThreeUsize) == (new_container_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, Some(endpoint_index)) is Success),
        !(ret is SuccessThreeUsize) ==> ret == new_container_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, Some(endpoint_index)),
{
    syscall_new_container_common(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, Some(endpoint_index), initial_regs)
}
}
