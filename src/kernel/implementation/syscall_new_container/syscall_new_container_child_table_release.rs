use vstd::prelude::*;
use crate::*;

verus! {
/// First release phase of the child's root-thread creation: unlocks the child's and the parent's held windows of the range, the
/// child process, both page tables, the new thread's page, and the scheduler shard, leaving the thread and endpoint locks held.
pub(super) fn release_new_container_child_table_locks(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, parent_process_ptr: RwLockProcessPtr, child_process_ptr: RwLockProcessPtr,
    new_thread_ptr: RwLockThreadPtr, source_pagetable_ptr: RwLockPageTableRoot, child_pagetable_ptr: RwLockPageTableRoot, scheduler_ptr: RwLockSchedulerPtr,
    Tracked(child_process_lock_perm): Tracked<LockPerm>, Tracked(thread_page_lock_perm): Tracked<LockPerm>, Tracked(scheduler_lock_perm): Tracked<LockPerm>,
    Tracked(source_pagetable_lock_perm): Tracked<LockPerm>, Tracked(child_pagetable_lock_perm): Tracked<LockPerm>, source_range: &VaRange4K,
    Tracked(source_window_perms): Tracked<Map<WindowVa, LockPerm>>, Tracked(child_window_perms): Tracked<Map<WindowVa, LockPerm>>,
    Ghost(entry_k): Ghost<KernelK>, Ghost(entry_lctx): Ghost<LocalContext>,
)
    requires
        old(krnl).inv(),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).page_lock_map().dom() =~= set![page_ptr2page_index(new_thread_ptr)],
        old(lctx).process_lock_map().dom() =~= set![parent_process_ptr, child_process_ptr],
        old(lctx).scheduler_lock_map().dom() =~= set![(scheduler_ptr, cpu_id)],
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr, child_pagetable_ptr],
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        parent_process_ptr != child_process_ptr,
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), parent_process_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(parent_process_ptr).being_killed(),
        old(krnl).prc_mp.dom().contains(child_process_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), child_process_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(child_process_ptr).being_killed(),
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) && old(krnl).ctn_mp.spec_index(c).killer_info() is Some
            ==> old(krnl).ctn_mp.spec_index(c).killer_info()->Some_0.process != child_process_ptr,
        old(krnl).prc_mp.spec_index(child_process_ptr).view().state.view() is Running,
        child_process_lock_perm.state() is WriteLock && child_process_lock_perm.thread_id() == old(lctx).thread_id(),
        child_process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(child_process_ptr).locking_thread()->Write_lock_id,
        page_ptr_valid(new_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(new_thread_ptr), TypedLockMode::Write),
        thread_page_lock_perm.state() is WriteLock && thread_page_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(new_thread_ptr)).view().locking_thread()->Write_lock_id,
        old(krnl).sched_mp.dom().contains(scheduler_ptr),
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (scheduler_ptr, cpu_id), TypedLockMode::Write),
        scheduler_lock_perm.state() is WriteLock && scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
        scheduler_lock_perm.lock_id() == old(krnl).sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        source_pagetable_ptr != child_pagetable_ptr,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Read),
        source_pagetable_lock_perm.state() is ReadLock && source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread() is Read,
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), source_pagetable_lock_perm.lock_id()),
        old(krnl).pt_mp.dom().contains(child_pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), child_pagetable_ptr, TypedLockMode::Write),
        child_pagetable_lock_perm.state() is WriteLock && child_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        child_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(child_pagetable_ptr).locking_thread()->Write_lock_id,
        source_range.wf(),
        source_range.len > 0,
        entry_k.pt_mp.dom().contains(source_pagetable_ptr),
        whole_pagetable(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).wf(),
        entry_k.pt_mp.spec_index(source_pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(source_range.start),
        forall|j: int| #![trigger source_range.view().spec_index(j)] 0 <= j < source_range.len ==> {
            &&& whole_pagetable(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).mapping_4k().dom().contains(source_range.view().spec_index(j))
            &&& whole_pagetable(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).mapping_4k().spec_index(source_range.view().spec_index(j)).present
        },
        forall|w: WindowVa| #![trigger va_range_2m_windows(*source_range).contains(w)]
            va_range_2m_windows(*source_range).contains(w) && whole_pagetable(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> source_window_perms.dom().contains(w),
        forall|w: WindowVa| #![trigger source_window_perms.dom().contains(w)] source_window_perms.dom().contains(w) ==> {
            &&& va_range_2m_windows(*source_range).contains(w)
            &&& whole_pagetable(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
            &&& typed_lock_map_contains_mode(entry_lctx.pagetable_window_lock_map(), (source_pagetable_ptr, w), TypedLockMode::Write)
            &&& source_window_perms.index(w).state() is WriteLock
            &&& source_window_perms.index(w).thread_id() == entry_lctx.thread_id()
            &&& whole_pagetable(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).lower.l2_owner(whole_pagetable(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
                == (RwLockState::Write { thread_id: source_window_perms.index(w).thread_id(), lock_id: source_window_perms.index(w).lock_id() })
            &&& whole_pagetable(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).window_leaves_present(w)
            &&& !whole_pagetable(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).lower.window_stale_cpus.dom().contains((
                whole_pagetable(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            &&& !whole_pagetable(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).lower.l2_entry_hides_l1(whole_pagetable(entry_k.pt_mp, entry_k.pt_lower.view(), source_pagetable_ptr).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
        },
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger entry_lctx.pagetable_window_lock_map().dom().contains((p, w))]
            entry_lctx.pagetable_window_lock_map().dom().contains((p, w)) == (p == source_pagetable_ptr && source_window_perms.dom().contains(w)),
        held_pagetable_windows_unchanged(entry_k.pt_mp, entry_k.pt_lower.view(), old(krnl).pt_mp, old(krnl).pt_lower.view(), &entry_lctx),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view() == entry_k.pt_mp.spec_index(source_pagetable_ptr).view(),
        entry_lctx.thread_id() == old(lctx).thread_id(),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w)) ==> entry_lctx.pagetable_window_lock_map().dom().contains((p, w)) || (p == child_pagetable_ptr && child_window_perms.dom().contains(w)),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger entry_lctx.pagetable_window_lock_map().dom().contains((p, w))]
            entry_lctx.pagetable_window_lock_map().dom().contains((p, w)) ==> old(lctx).pagetable_window_lock_map().dom().contains((p, w))
                && old(lctx).pagetable_window_lock_map().index((p, w)) == entry_lctx.pagetable_window_lock_map().index((p, w)),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), child_pagetable_ptr).leaves_present(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), child_pagetable_ptr).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        old(krnl).pt_mp.spec_index(child_pagetable_ptr).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        forall|l4i: L4Index| #![trigger old(krnl).pt_mp.spec_index(child_pagetable_ptr).view().spec_held_l4(l4i)]
            old(krnl).pt_mp.spec_index(child_pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && old(krnl).pt_mp.spec_index(child_pagetable_ptr).view().spec_held_l4(l4i) is Some ==> old(krnl).pt_mp.spec_index(child_pagetable_ptr).view().spec_resolve_mapping_l4(l4i) is Some,
        forall|l4i: L4Index, l3i: L3Index| #![trigger old(krnl).pt_mp.spec_index(child_pagetable_ptr).view().spec_held_l3(l4i, l3i)]
            old(krnl).pt_mp.spec_index(child_pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && old(krnl).pt_mp.spec_index(child_pagetable_ptr).view().spec_held_l3(l4i, l3i) is Some
                ==> old(krnl).pt_mp.spec_index(child_pagetable_ptr).view().spec_resolve_mapping_l3(l4i, l3i) is Some,
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), child_pagetable_ptr).lower.l2_page(p).entry_lock(i).l1()]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), child_pagetable_ptr).lower.l2_perms.dom().contains(p) && pei_valid(i) ==> !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), child_pagetable_ptr).lower.l2_entry_hides_l1(p, i),
        old(krnl).pt_mp.spec_index(child_pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(source_range.start),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*source_range).contains(w)]
            va_range_2m_windows(*source_range).contains(w) && whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), child_pagetable_ptr).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> child_window_perms.dom().contains(w),
        forall|w: WindowVa| #![trigger child_window_perms.dom().contains(w)] child_window_perms.dom().contains(w) ==> {
            &&& va_range_2m_windows(*source_range).contains(w)
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), child_pagetable_ptr).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
            &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (child_pagetable_ptr, w), TypedLockMode::Write)
            &&& child_window_perms.index(w).state() is WriteLock
            &&& child_window_perms.index(w).thread_id() == old(lctx).thread_id()
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), child_pagetable_ptr).lower.l2_owner(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), child_pagetable_ptr).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
                == (RwLockState::Write { thread_id: child_window_perms.index(w).thread_id(), lock_id: child_window_perms.index(w).lock_id() })
        },
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).page_lock_map().dom().is_empty(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map().dom() =~= set![parent_process_ptr],
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), parent_process_ptr, TypedLockMode::Write),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map().dom().is_empty(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map().dom().is_empty(),
        final(lctx).pagetable_window_lock_map().dom().is_empty(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        *final(krnl) == (KernelK { prc_mp: final(krnl).prc_mp, pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, pg_arr: final(krnl).pg_arr, sched_mp: final(krnl).sched_mp, ..*old(krnl) }),
        forall|p: RwLockProcessPtr| #![trigger final(krnl).prc_mp.spec_index(p)]
            old(krnl).prc_mp.dom().contains(p) ==> if p == child_process_ptr { final(krnl).prc_mp.spec_index(p).locking_thread() is None } else { final(krnl).prc_mp.spec_index(p) == old(krnl).prc_mp.spec_index(p) },
        final(krnl).prc_mp.dom() == old(krnl).prc_mp.dom(),
        kernel_process_nonlock_fields_unchanged(old(krnl).prc_mp, final(krnl).prc_mp),
        forall|p: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(p)]
            old(krnl).pt_mp.dom().contains(p) ==> if p == child_pagetable_ptr { final(krnl).pt_mp.spec_index(p).locking_thread() is None }
                else if p == source_pagetable_ptr { !(final(krnl).pt_mp.spec_index(p).locking_thread() is Write) }
                else { final(krnl).pt_mp.spec_index(p).locking_thread() == old(krnl).pt_mp.spec_index(p).locking_thread() },
        final(krnl).pt_mp.dom() == old(krnl).pt_mp.dom(),
        kernel_pagetable_nonlock_fields_unchanged(old(krnl).pt_mp, old(krnl).pt_lower.view(), final(krnl).pt_mp, final(krnl).pt_lower.view()),
        final(krnl).pt_lower.view() =~= old(krnl).pt_lower.view().insert(source_pagetable_ptr, final(krnl).pt_lower.view().spec_index(source_pagetable_ptr)) .insert(child_pagetable_ptr, final(krnl).pt_lower.view().spec_index(child_pagetable_ptr)),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable_ptr).lower.pagetable_window_locks
            == pagetable_window_locks_after_unlocking_range(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable_ptr).lower.pagetable_window_locks, *source_range),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), child_pagetable_ptr).lower.pagetable_window_locks
            == pagetable_window_locks_after_unlocking_range(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), child_pagetable_ptr).lower.pagetable_window_locks, *source_range),
        final(krnl).sched_mp.dom() == old(krnl).sched_mp.dom(),
        forall|s: RwLockSchedulerPtr| #![trigger scheduler_shards_of(final(krnl).sched_mp.spec_index(s))]
            old(krnl).sched_mp.dom().contains(s) ==> scheduler_shards_of(final(krnl).sched_mp.spec_index(s)) == scheduler_shards_of(old(krnl).sched_mp.spec_index(s)),
{
    hide(typed_lock_maps_aligned);
    krnl.unlock_pagetable_range_existing_windows(child_pagetable_ptr, source_range, Tracked(&child_pagetable_lock_perm), Tracked(&mut *lctx), Tracked(child_window_perms));
    proof { assert(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable_ptr) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable_ptr)); }
    krnl.unlock_pagetable_range_existing_windows(source_pagetable_ptr, source_range, Tracked(&source_pagetable_lock_perm), Tracked(&mut *lctx), Tracked(source_window_perms));
    krnl.wunlock_process(child_process_ptr, Tracked(&mut *lctx), Tracked(child_process_lock_perm));
    krnl.runlock_pagetable(cpu_id, source_pagetable_ptr, Tracked(&mut *lctx), Tracked(source_pagetable_lock_perm));
    krnl.wunlock_pagetable(child_pagetable_ptr, Tracked(&mut *lctx), Tracked(child_pagetable_lock_perm));
    krnl.wunlock_page(page_ptr2page_index(new_thread_ptr), Tracked(&mut *lctx), Tracked(thread_page_lock_perm));
    krnl.wunlock_scheduler_shard(scheduler_ptr, cpu_id, Tracked(&mut *lctx), Tracked(scheduler_lock_perm));
    proof {
        assert(kernel_process_nonlock_fields_unchanged(old(krnl).prc_mp, krnl.prc_mp)
            && kernel_pagetable_nonlock_fields_unchanged(old(krnl).pt_mp, old(krnl).pt_lower.view(), krnl.pt_mp, krnl.pt_lower.view())) by {
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); broadcast use kernel_pagetable_nonlock_fields_unchanged_transitive;
        };
    }
}
}
