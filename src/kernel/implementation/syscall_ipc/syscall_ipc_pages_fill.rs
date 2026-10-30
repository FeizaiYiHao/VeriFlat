use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_spec::*;
use super::syscall_ipc_trace::*;

verus! {
/// The L2 index bounds `lo..=hi` of `range` inside the L3 entry of `cur_va`: an existing window under that entry lies in `range` exactly
/// when its L2 index is between them.
fn ipc_pages_fill_l2_bounds(range: &VaRange4K, cur_va: VAddr, cur: (L4Index, L3Index, L2Index, L1Index), start_indices: (L4Index, L3Index, L2Index, L1Index),
    end_indices: (L4Index, L3Index, L2Index, L1Index)) -> (ret: (L2Index, L2Index))
    requires
        range.wf(),
        range.len > 0,
        spec_va_4k_valid(cur_va),
        range.start <= cur_va <= range.view()[range.len - 1],
        cur == spec_va2index(cur_va),
        start_indices == spec_va2index(range.start),
        end_indices == spec_va2index(range.view()[range.len - 1]),
    ensures
        pei_valid(ret.0) && pei_valid(ret.1),
        ret.0 <= cur.2 <= ret.1,
        forall|w: WindowVa| #![trigger va_range_2m_windows(*range).contains(w)] w.wf() && spec_v2l4index(w.va) == cur.0 && spec_v2l3index(w.va) == cur.1
            ==> va_range_2m_windows(*range).contains(w) == (ret.0 <= spec_v2l2index(w.va) <= ret.1),
{
    let lo = if cur.0 == start_indices.0 && cur.1 == start_indices.1 { start_indices.2 } else { 0 };
    let hi = if cur.0 == end_indices.0 && cur.1 == end_indices.1 { end_indices.2 } else { 511 };
    proof {
        broadcast use spec_va_2m_valid_index_roundtrip, spec_index2va_2m_valid;
        spec_va_4k_valid_index_roundtrip(cur_va); spec_va_4k_valid_index_roundtrip(range.start); spec_va_4k_valid_index_roundtrip(range.view()[range.len - 1]);
        spec_index2va_le_implies_4k_indices_lex_le(start_indices, cur); spec_index2va_le_implies_4k_indices_lex_le(cur, end_indices);
    }
    (lo, hi)
}

/// Builds the missing L4, L3 and L2 directories of target page `i` of a pages rendezvous under the write-held target page table,
/// one `Share4kDirectory` step per new directory, and adds the windows minted with a new L2 page to the held target windows.
pub(super) fn ipc_pages_fill_target_page(
    krnl: &mut KernelK, target_range: &VaRange4K, i: usize, start_indices: (L4Index, L3Index, L2Index, L1Index), end_indices: (L4Index, L3Index, L2Index, L1Index),
    target_allocator: RwLockPageAllocatorPtr, target_thread: RwLockThreadPtr, target_process: RwLockProcessPtr, target_container: RwLockContainerPtr, cpu_id: CpuId,
    target_pagetable: RwLockPageTableRoot, current_thread_ptr: RwLockThreadPtr, Ghost(start): Ghost<int>, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>, Tracked(target_thread_lock_perm): Tracked<&LockPerm>, Tracked(current_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(target_pagetable_lock_perm): Tracked<&LockPerm>, Tracked(window_perms): Tracked<&mut Map<WindowVa, LockPerm>>,
)
    requires
        old(krnl).inv(),
        old(steps).snapshot_k() == *old(krnl),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view()->Some_0->Share4k_origin matches Share4kOrigin::IpcPages { peer }
            ==> old(krnl).thr_mp.spec_index(peer).view().state is IPC_TRANSIT && old(krnl).thr_mp.spec_index(peer).view().state->IPC_TRANSIT_partner == current_thread_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is Some,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view()->Some_0 is Share4k,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view()->Some_0->Share4k_target_range == *target_range,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view()->Some_0->Share4k_shared < old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view()->Some_0->Share4k_source_range.len,
        current_thread_ptr == target_thread || old(krnl).thr_mp.spec_index(target_thread).view().syscall_progress.view() is None,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), share_4k_objects_k(*old(krnl), cpu_id).source_thread, TypedLockMode::Write),
        share_4k_objects_k(*old(krnl), cpu_id).quota_thread == target_thread && share_4k_objects_k(*old(krnl), cpu_id).target == target_process,
        share_4k_objects_k(*old(krnl), cpu_id).target_container == target_container && share_4k_objects_k(*old(krnl), cpu_id).transfer_source is None,
        old(krnl).ctn_mp.dom().contains(target_container),
        old(krnl).ctn_mp.spec_index(target_container).view_rodata().view().allocator_ptr_4k == target_allocator,
        old(krnl).allc_4k_mp.dom().contains(target_allocator),
        old(krnl).prc_mp.dom().contains(target_process),
        old(krnl).prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container,
        old(krnl).prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable,
        old(krnl).thr_mp.dom().contains(target_thread),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), target_thread, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(target_thread).being_killed(),
        !thread_is_dangling(old(krnl).thr_mp.spec_index(target_thread)),
        old(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        old(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process,
        old(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable,
        old(krnl).thr_mp.spec_index(target_thread).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(target_thread).view().free_quota_pending_clean(),
        thread_effective_quota_4k(old(krnl).thr_mp.spec_index(target_thread)) >= 3,
        target_thread_lock_perm.state() is WriteLock,
        target_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        target_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(target_thread).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(target_pagetable),
        old(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
        target_pagetable_lock_perm.state() is WriteLock,
        target_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        target_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).wf(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).kernel_l4_end() <= spec_va2index(target_range.start).0,
        target_range.wf(),
        i < target_range.len,
        start_indices == spec_va2index(target_range.start),
        end_indices == spec_va2index(target_range.view()[target_range.len - 1]),
        ({
            let indices = spec_va2index(target_range.view().spec_index(i as int));
            &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_1g().dom().contains(spec_index2va((indices.0, indices.1, 0, 0)))
            &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_2m().dom().contains(spec_index2va((indices.0, indices.1, indices.2, 0)))
            &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_4k().dom().contains(target_range.view().spec_index(i as int))
        }),
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, w))
                == (va_range_2m_windows(*target_range).contains(w) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some),
        forall|w: WindowVa|
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, w))]
            #![trigger va_range_2m_windows(*target_range).contains(w)]
            old(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, w)) ==> {
            &&& old(window_perms).dom().contains(w)
            &&& old(window_perms).index(w).state() is WriteLock
            &&& old(window_perms).index(w).thread_id() == old(lctx).thread_id()
            &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (target_pagetable, w), TypedLockMode::Write)
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).lower.l2_owner(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
                == (SpinLockState::Some { thread_id: old(window_perms).index(w).thread_id(), lock_id: old(window_perms).index(w).lock_id() })
        },
        forall|w: WindowVa| #![trigger old(window_perms).dom().contains(w)]
            old(window_perms).dom().contains(w) ==> old(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, w)),
        0 <= start <= old(steps).view().len(),
        forall|j: int| #![trigger old(steps).view()[j]] start <= j < old(steps).view().len()
            ==> share_4k_range_step(old(steps).view()[j], cpu_id) || ipc_pages_downgrade_step_pre(old(steps).view()[j].old_u, cpu_id) && ipc_pages_downgrade_step(old(steps).view()[j].old_u, old(steps).view()[j].new_u, cpu_id),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        nonwindow_typed_lock_maps_unchanged(old(lctx), final(lctx)),
        held_locks_order_below(final(krnl), final(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        final(steps).snapshot_k() == *final(krnl),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        old(steps).view().len() <= final(steps).view().len() <= old(steps).view().len() + 3,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|j: int| #![trigger final(steps).view()[j]] start <= j < final(steps).view().len()
            ==> share_4k_range_step(final(steps).view()[j], cpu_id) || ipc_pages_downgrade_step_pre(final(steps).view()[j].old_u, cpu_id) && ipc_pages_downgrade_step(final(steps).view()[j].old_u, final(steps).view()[j].new_u, cpu_id),
        share_4k_objects_k(*final(krnl), cpu_id) == share_4k_objects_k(*old(krnl), cpu_id),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        final(krnl).cpu_op.view().view()[cpu_id as int] == old(krnl).cpu_op.view().view()[cpu_id as int],
        final(krnl).ctn_mp.dom().contains(target_container),
        final(krnl).ctn_mp.spec_index(target_container).view_rodata() == old(krnl).ctn_mp.spec_index(target_container).view_rodata(),
        final(krnl).allc_4k_mp.dom().contains(target_allocator),
        final(krnl).prc_mp.dom().contains(target_process),
        final(krnl).prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container,
        final(krnl).prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable,
        held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
        held_threads_unchanged_except(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx), set![target_thread, current_thread_ptr]),
        held_pagetables_unchanged_except(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx), set![target_pagetable]),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w)) && old(lctx).pagetable_lock_map().dom().contains(p) && p != target_pagetable ==> {
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), p).window_view(w) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), p).window_view(w)
                &&& forall|v: VAddr|
                    #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), p).mapping_4k().dom().contains(v)]
                    #![trigger pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), p).mapping_4k().dom().contains(v)]
                    spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
                        &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), p).mapping_4k().dom().contains(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), p).mapping_4k().dom().contains(v)
                        &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), p).mapping_4k().dom().contains(v)
                            ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), p).mapping_4k().spec_index(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), p).mapping_4k().spec_index(v)
                    }
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), p).mapping_2m().dom().contains(w.va) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), p).mapping_2m().dom().contains(w.va)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), p).mapping_2m().dom().contains(w.va)
                    ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), p).mapping_2m().spec_index(w.va) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), p).mapping_2m().spec_index(w.va)
            },
        final(krnl).thr_mp.dom().contains(target_thread),
        final(krnl).thr_mp.spec_index(target_thread).being_killed() == old(krnl).thr_mp.spec_index(target_thread).being_killed(),
        !thread_is_dangling(final(krnl).thr_mp.spec_index(target_thread)),
        final(krnl).thr_mp.spec_index(target_thread).view_ghost() == old(krnl).thr_mp.spec_index(target_thread).view_ghost(),
        final(krnl).thr_mp.spec_index(target_thread).view().owning_container == old(krnl).thr_mp.spec_index(target_thread).view().owning_container,
        final(krnl).thr_mp.spec_index(target_thread).view().owning_proc == old(krnl).thr_mp.spec_index(target_thread).view().owning_proc,
        final(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr,
        final(krnl).thr_mp.spec_index(target_thread).view().state == old(krnl).thr_mp.spec_index(target_thread).view().state,
        final(krnl).thr_mp.spec_index(target_thread).view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(target_thread).view().endpoint_descriptors.view(),
        final(krnl).thr_mp.spec_index(target_thread).view().upper_container_seq == old(krnl).thr_mp.spec_index(target_thread).view().upper_container_seq,
        current_thread_ptr != target_thread ==> final(krnl).thr_mp.spec_index(target_thread).view().syscall_progress.view() == old(krnl).thr_mp.spec_index(target_thread).view().syscall_progress.view(),
        final(krnl).thr_mp.dom().contains(current_thread_ptr),
        current_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost(),
        current_thread_ptr != target_thread ==> final(krnl).thr_mp.spec_index(current_thread_ptr).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(current_thread_ptr).view() }),
        ({
            let progress = old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view()->Some_0;
            let final_progress = final(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view();
            final_progress == Some(SyscallProgress::Share4k { source_range: progress->Share4k_source_range, target_range: progress->Share4k_target_range, shared: progress->Share4k_shared,
                directory: final_progress->Some_0->Share4k_directory, origin: progress->Share4k_origin })
        }),
        final(krnl).thr_mp.spec_index(target_thread).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(target_thread).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(target_thread).view().quota_4k - 3 <= final(krnl).thr_mp.spec_index(target_thread).view().quota_4k,
        target_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(target_thread).locking_thread()->Write_lock_id,
        final(krnl).pt_mp.dom().contains(target_pagetable),
        final(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        target_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).wf(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).kernel_l4_end() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).kernel_l4_end(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_4k() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_4k(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_2m(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_1g(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).spec_resolve_mapping_l2(l4i, l3i, l2i)]
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some,
        ({
            let va = target_range.view().spec_index(i as int);
            &&& pei_valid(spec_v2l4index(va)) && pei_valid(spec_v2l3index(va)) && pei_valid(spec_v2l2index(va))
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).kernel_l4_end() <= spec_v2l4index(va)
            &&& final(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, window_of(va)))
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some
        }),
        forall|p: RwLockPageTableRoot, w: WindowVa|
            #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            p != target_pagetable ==> final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == old(lctx).pagetable_window_lock_map().dom().contains((p, w)),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w))
                ==> final(lctx).pagetable_window_lock_map().dom().contains((p, w)) && final(lctx).pagetable_window_lock_map().index((p, w)) == old(lctx).pagetable_window_lock_map().index((p, w)),
        forall|w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, w))]
            final(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, w))
                == (va_range_2m_windows(*target_range).contains(w) && pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some),
        forall|w: WindowVa|
            #![trigger final(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, w))]
            #![trigger va_range_2m_windows(*target_range).contains(w)]
            final(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, w)) ==> {
            &&& final(window_perms).dom().contains(w)
            &&& final(window_perms).index(w).state() is WriteLock
            &&& final(window_perms).index(w).thread_id() == final(lctx).thread_id()
            &&& typed_lock_map_contains_mode(final(lctx).pagetable_window_lock_map(), (target_pagetable, w), TypedLockMode::Write)
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.l2_owner(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
                == (SpinLockState::Some { thread_id: final(window_perms).index(w).thread_id(), lock_id: final(window_perms).index(w).lock_id() })
        },
        forall|w: WindowVa| #![trigger final(window_perms).dom().contains(w)]
            final(window_perms).dom().contains(w) ==> final(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, w)),
{
    let cur_va = target_range.index(i);
    let cur = va2index(cur_va);
    proof { target_range.va_range_lemma(); }
    let (lo, hi) = ipc_pages_fill_l2_bounds(target_range, cur_va, cur, start_indices, end_indices);
    proof {
        broadcast use spec_va_2m_valid_index_roundtrip, spec_index2va_2m_valid;
        va_range_2m_windows_contains_window_of_first_n_pages(*target_range, target_range.len as int);
        spec_va_4k_valid_index_roundtrip(cur_va); spec_va_4k_valid_index_roundtrip(target_range.start); spec_va_4k_valid_index_roundtrip(target_range.view()[target_range.len - 1]);
        spec_v2l4index_monotonic(target_range.start, cur_va);
        spec_index2va_le_implies_4k_indices_lex_le(start_indices, cur); spec_index2va_le_implies_4k_indices_lex_le(cur, end_indices);
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl);
        pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).higher.wf_mapping_1g_at(cur.0, cur.1);
        pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).wf_mapping_2m_at(cur.0, cur.1, cur.2);
        pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).wf_mapping_4k_at(cur.0, cur.1, cur.2, cur.3);
    }
    let ghost before = steps.view();
    let Tracked(minted) = mmap_4k_build_one_structure(
        krnl, cur_va, lo, hi, target_allocator, target_thread, target_process, target_container, cpu_id, target_pagetable, None, current_thread_ptr,
        Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(target_thread_lock_perm), Tracked(current_thread_lock_perm), Tracked(target_pagetable_lock_perm), Tracked(None), Tracked(None),
        Tracked(&*window_perms),
    );
    proof {
        share_4k_range_steps_from_directory(&*steps, before, before.len() as int, cpu_id);
        window_perms.tracked_union_prefer_right(minted);
    }
}
} // verus!
