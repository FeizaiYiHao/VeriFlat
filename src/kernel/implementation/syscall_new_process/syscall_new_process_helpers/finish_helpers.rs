use vstd::prelude::*;
use crate::*;
use super::finish_release::{release_new_process_child_locks, release_new_process_thread_locks_and_attach_endpoint};

verus! {
/// Releases the child's IOMMU table when the process has one; a single call keeps the caller's later proof on one path.
pub(super) fn wunlock_new_process_iommu_table(krnl: &mut KernelK, iommu_table: Option<RwLockPageTableRoot>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(lock_perm): Tracked<Option<LockPerm>>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        iommu_table is Some ==> {
            let iommu_table_ptr = iommu_table->Some_0;
            &&& old(krnl).it_mp.dom().contains(iommu_table_ptr)
            &&& old(krnl).it_mp.spec_index(iommu_table_ptr).view().leaves_present()
            &&& typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write)
            &&& lock_perm is Some
            &&& lock_perm->Some_0.state() is WriteLock
            &&& lock_perm->Some_0.thread_id() == old(lctx).thread_id()
            &&& lock_perm->Some_0.lock_id() == old(krnl).it_mp.spec_index(iommu_table_ptr).locking_thread()->Write_lock_id
        },
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        iommu_table is None ==> *final(krnl) == *old(krnl) && *final(lctx) == *old(lctx),
        iommu_table is Some ==> {
            let iommu_table_ptr = iommu_table->Some_0;
            &&& kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl))
            &&& kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp)
            &&& kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl))
            &&& *final(krnl) == (KernelK { it_mp: final(krnl).it_mp, ..*old(krnl) })
            &&& final(krnl).it_mp.unchanged_except(&old(krnl).it_mp, iommu_table_ptr)
            &&& final(krnl).it_mp.lock_id_by_key(iommu_table_ptr) == old(krnl).it_mp.lock_id_by_key(iommu_table_ptr)
            &&& wunlock_ensures(old(krnl).it_mp.spec_index(iommu_table_ptr), final(krnl).it_mp.spec_index(iommu_table_ptr))
            &&& unlock_ensures(old(lctx), final(lctx), KernelObjId::IommuTable(iommu_table_ptr), old(krnl).it_mp.lock_id_by_key(iommu_table_ptr))
        },
{
    if let Some(iommu_table_ptr) = iommu_table {
        let tracked lock_perm = lock_perm.tracked_unwrap();
        krnl.wunlock_iommu_table(iommu_table_ptr, Tracked(&mut *lctx), Tracked(lock_perm));
    }
}

/// Release phase of new-process finish: unlocks the child's IOMMU table, the child, both page tables, the new thread's page,
/// and the scheduler shard, clears the staging thread's progress, attaches the initial endpoint to the scheduled new thread,
/// and unlocks both threads and the cpu, leaving no lock held.
pub(super) fn release_new_process_locks_and_attach_endpoint(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, container_ptr: RwLockContainerPtr, child_ptr: RwLockProcessPtr,
    current_thread_ptr: RwLockThreadPtr, new_thread_ptr: RwLockThreadPtr, scheduler_ptr: RwLockSchedulerPtr, endpoint: Option<RwLockEndpointPtr>,
    source_pagetable_ptr: RwLockPageTableRoot, target_pagetable_ptr: RwLockPageTableRoot, iommu_table: Option<RwLockPageTableRoot>,
    Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(child_lock_perm): Tracked<LockPerm>, Tracked(current_thread_lock_perm): Tracked<LockPerm>,
    Tracked(new_thread_lock_perm): Tracked<LockPerm>, Tracked(thread_page_lock_perm): Tracked<LockPerm>, Tracked(scheduler_lock_perm): Tracked<LockPerm>,
    Tracked(endpoint_lock_perm): Tracked<Option<LockPerm>>, Tracked(source_pagetable_lock_perm): Tracked<LockPerm>, Tracked(target_pagetable_lock_perm): Tracked<LockPerm>,
    Tracked(iommu_table_lock_perm): Tracked<Option<LockPerm>>, source_range: &VaRange4K, Tracked(source_window_perms): Tracked<Map<WindowVa, LockPerm>>, Tracked(target_window_perms): Tracked<Map<WindowVa, LockPerm>>,
    Ghost(entry_k): Ghost<KernelK>, Ghost(entry_lctx): Ghost<LocalContext>,
)
    requires
        old(krnl).inv(),
        index_valid(NUM_CPUS, cpu_id),
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).page_lock_map().dom() =~= set![page_ptr2page_index(new_thread_ptr)],
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom() =~= set![child_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, new_thread_ptr],
        endpoint is None ==> old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom() =~= set![(scheduler_ptr, cpu_id)],
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr, target_pagetable_ptr],
        iommu_table is None ==> old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        cpu_lock_perm.state() is WriteLock && cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(child_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), child_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(child_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(child_ptr).view().state.view() is Running,
        iommu_table is Some ==> old(krnl).prc_mp.spec_index(child_ptr).view().iommu_table == iommu_table,
        child_lock_perm.state() is WriteLock && child_lock_perm.thread_id() == old(lctx).thread_id(),
        child_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(child_ptr).locking_thread()->Write_lock_id,
        current_thread_ptr != new_thread_ptr,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state is RUNNING,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        current_thread_lock_perm.state() is WriteLock && current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(new_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), new_thread_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.spec_index(new_thread_ptr).is_init(),
        !old(krnl).thr_mp.spec_index(new_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(new_thread_ptr).view().state is SCHEDULED,
        old(krnl).thr_mp.spec_index(new_thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.wf(),
        old(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.spec_index(0) is None,
        old(krnl).thr_mp.spec_index(new_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(new_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(new_thread_ptr).view().syscall_progress.view() is None,
        !old(krnl).thr_mp.spec_index(new_thread_ptr).view_ghost().exited,
        new_thread_lock_perm.state() is WriteLock && new_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        new_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(new_thread_ptr).locking_thread()->Write_lock_id,
        page_ptr_valid(new_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(new_thread_ptr), TypedLockMode::Write),
        thread_page_lock_perm.state() is WriteLock && thread_page_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(new_thread_ptr)).view().locking_thread()->Write_lock_id,
        old(krnl).sched_mp.dom().contains(scheduler_ptr),
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (scheduler_ptr, cpu_id), TypedLockMode::Write),
        scheduler_lock_perm.state() is WriteLock && scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
        scheduler_lock_perm.lock_id() == old(krnl).sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        source_pagetable_ptr != target_pagetable_ptr,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        old(krnl).pt_mp.dom().contains(target_pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable_ptr, TypedLockMode::Write),
        target_pagetable_lock_perm.state() is WriteLock && target_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        target_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(target_pagetable_ptr).locking_thread()->Write_lock_id,
        source_range.wf(),
        source_range.len > 0,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Read),
        source_pagetable_lock_perm.state() is ReadLock,
        source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread() is Read,
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), source_pagetable_lock_perm.lock_id()),
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
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable_ptr).lower.l2_lock_of(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable_ptr).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                .lock_perm_match(spec_v2l2index(w.va), &target_window_perms.index(w))
        },
        iommu_table is Some ==> {
            let iommu_table_ptr = iommu_table->Some_0;
            &&& old(lctx).iommu_table_lock_map().dom() =~= set![iommu_table_ptr]
            &&& old(krnl).it_mp.dom().contains(iommu_table_ptr)
            &&& typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write)
            &&& old(krnl).it_mp.spec_index(iommu_table_ptr).view().is_empty()
            &&& iommu_table_lock_perm is Some
            &&& iommu_table_lock_perm->Some_0.state() is WriteLock && iommu_table_lock_perm->Some_0.thread_id() == old(lctx).thread_id()
            &&& iommu_table_lock_perm->Some_0.lock_id() == old(krnl).it_mp.spec_index(iommu_table_ptr).locking_thread()->Write_lock_id
        },
        endpoint is Some ==> {
            let endpoint_ptr = endpoint->Some_0;
            &&& old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr]
            &&& old(krnl).ep_mp.dom().contains(endpoint_ptr)
            &&& typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write)
            &&& {
                ||| old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container == container_ptr
                ||| old(krnl).ctn_mp.spec_index(old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container).view_ghost().subtree_set.view().contains(container_ptr)
            }
            &&& endpoint_lock_perm is Some
            &&& endpoint_lock_perm->Some_0.state() is WriteLock && endpoint_lock_perm->Some_0.thread_id() == old(lctx).thread_id()
            &&& endpoint_lock_perm->Some_0.lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id
        },
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        *final(krnl) == (KernelK { it_mp: final(krnl).it_mp, prc_mp: final(krnl).prc_mp, pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, pg_arr: final(krnl).pg_arr, sched_mp: final(krnl).sched_mp,
            thr_mp: final(krnl).thr_mp, ep_mp: final(krnl).ep_mp, cpu_arr: final(krnl).cpu_arr, ..*old(krnl) }),
        forall|p: RwLockProcessPtr| #![trigger final(krnl).prc_mp.spec_index(p)]
            old(krnl).prc_mp.dom().contains(p) ==> if p == child_ptr { final(krnl).prc_mp.spec_index(p).locking_thread() is None } else { final(krnl).prc_mp.spec_index(p).locking_thread() == old(krnl).prc_mp.spec_index(p).locking_thread() },
        forall|p: RwLockThreadPtr| #![trigger final(krnl).thr_mp.spec_index(p)]
            old(krnl).thr_mp.dom().contains(p) ==> if p == current_thread_ptr || p == new_thread_ptr { final(krnl).thr_mp.spec_index(p).locking_thread() is None }
                else { final(krnl).thr_mp.spec_index(p).locking_thread() == old(krnl).thr_mp.spec_index(p).locking_thread() },
        forall|p: RwLockEndpointPtr| #![trigger final(krnl).ep_mp.spec_index(p)]
            old(krnl).ep_mp.dom().contains(p) ==> if endpoint == Some(p) { final(krnl).ep_mp.spec_index(p).locking_thread() is None } else { final(krnl).ep_mp.spec_index(p).locking_thread() == old(krnl).ep_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(p)]
            old(krnl).pt_mp.dom().contains(p) ==> if p == target_pagetable_ptr { final(krnl).pt_mp.spec_index(p).locking_thread() is None }
                else if p == source_pagetable_ptr { !(final(krnl).pt_mp.spec_index(p).locking_thread() is Write) }
                else { final(krnl).pt_mp.spec_index(p).locking_thread() == old(krnl).pt_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger final(krnl).it_mp.spec_index(p)]
            old(krnl).it_mp.dom().contains(p) ==> if iommu_table == Some(p) { final(krnl).it_mp.spec_index(p).locking_thread() is None } else { final(krnl).it_mp.spec_index(p).locking_thread() == old(krnl).it_mp.spec_index(p).locking_thread() },
        forall|i: CpuId| #![trigger final(krnl).cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> if i == cpu_id { final(krnl).cpu_arr.spec_index(i).value.locking_thread() is None } else { final(krnl).cpu_arr.spec_index(i).value.locking_thread() == old(krnl).cpu_arr.spec_index(i).value.locking_thread() },
        final(krnl).pt_mp.dom() == old(krnl).pt_mp.dom(),
        kernel_pagetable_nonlock_fields_unchanged(old(krnl).pt_mp, old(krnl).pt_lower.view(), final(krnl).pt_mp, final(krnl).pt_lower.view()),
        final(krnl).it_mp.dom() == old(krnl).it_mp.dom(),
        forall|p: RwLockPageTableRoot| #![trigger final(krnl).it_mp.spec_index(p)] old(krnl).it_mp.dom().contains(p) ==> final(krnl).it_mp.spec_index(p).view() == old(krnl).it_mp.spec_index(p).view(),
        kernel_cpu_nonlock_fields_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr),
        kernel_process_nonlock_fields_unchanged(old(krnl).prc_mp, final(krnl).prc_mp),
        iommu_table is Some ==> final(krnl).prc_mp.dom().contains(child_ptr) && final(krnl).prc_mp.spec_index(child_ptr).view().iommu_table == iommu_table,
        final(krnl).sched_mp.dom() == old(krnl).sched_mp.dom(),
        forall|s: RwLockSchedulerPtr| #![trigger scheduler_shards_of(final(krnl).sched_mp.spec_index(s))]
            old(krnl).sched_mp.dom().contains(s) ==> scheduler_shards_of(final(krnl).sched_mp.spec_index(s)) == scheduler_shards_of(old(krnl).sched_mp.spec_index(s)),
        final(krnl).thr_mp.dom() == old(krnl).thr_mp.dom(),
        forall|t: RwLockThreadPtr| #![trigger final(krnl).thr_mp.spec_index(t)]
            old(krnl).thr_mp.dom().contains(t) ==> {
                &&& final(krnl).thr_mp.spec_index(t).being_killed() == old(krnl).thr_mp.spec_index(t).being_killed()
                &&& t != current_thread_ptr && t != new_thread_ptr ==> final(krnl).thr_mp.spec_index(t).view() == old(krnl).thr_mp.spec_index(t).view()
            },
        final(krnl).thr_mp.spec_index(current_thread_ptr).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(current_thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
        !final(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        final(krnl).thr_mp.spec_index(new_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(new_thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(new_thread_ptr).view() == (Thread { endpoint_descriptors: final(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors, ..old(krnl).thr_mp.spec_index(new_thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.view() == if endpoint is Some {
            old(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.view().update(0, endpoint)
        } else { old(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.view() },
        final(krnl).ep_mp.dom() == old(krnl).ep_mp.dom(),
        forall|e: RwLockEndpointPtr| #![trigger final(krnl).ep_mp.spec_index(e)]
            old(krnl).ep_mp.dom().contains(e) ==> {
                let a = old(krnl).ep_mp.spec_index(e);
                let b = final(krnl).ep_mp.spec_index(e);
                &&& b.view().queue.view() == a.view().queue.view()
                &&& b.view().queue_state == a.view().queue_state
                &&& b.view().owning_threads.view() == if endpoint == Some(e) { a.view().owning_threads.view().insert((new_thread_ptr, 0usize)) } else { a.view().owning_threads.view() }
                &&& b.view().owning_container == a.view().owning_container
                &&& b.being_killed() == a.being_killed()
            },
{
    release_new_process_child_locks(
        krnl, Tracked(&mut *lctx), cpu_id, child_ptr, new_thread_ptr, scheduler_ptr, source_pagetable_ptr, target_pagetable_ptr, iommu_table, Tracked(child_lock_perm),
        Tracked(thread_page_lock_perm), Tracked(scheduler_lock_perm), Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm), Tracked(iommu_table_lock_perm),
        source_range, Tracked(source_window_perms), Tracked(target_window_perms), Ghost(entry_k), Ghost(entry_lctx),
    );
    release_new_process_thread_locks_and_attach_endpoint(
        krnl, Tracked(&mut *lctx), cpu_id, container_ptr, current_thread_ptr, new_thread_ptr, endpoint, Tracked(cpu_lock_perm), Tracked(current_thread_lock_perm),
        Tracked(new_thread_lock_perm), Tracked(endpoint_lock_perm),
    );
}
}
