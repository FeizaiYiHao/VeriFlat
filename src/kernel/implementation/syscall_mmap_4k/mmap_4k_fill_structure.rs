use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_mmap_4k_spec::mmap_4k_range_step;
#[cfg(verus_keep_ghost)]
use super::syscall_mmap_4k_trace::mmap_4k_range_steps_from_directory;

verus! {
/// Under the pagetable's big write lock, for page `i` of `range`: installs its L4 directory if missing and then its L3 directory
/// if missing, recording one directory step per installed page. A new L2 page starts with the range's windows under it held by
/// `lo..=hi`, whose perms join `window_perms`; every other held window keeps its lock entry, perm, and L2 lock.
fn mmap_4k_fill_page_directories(
    krnl: &mut KernelK, range: &VaRange4K, i: usize, start_indices: (L4Index, L3Index, L2Index, L1Index), end_indices: (L4Index, L3Index, L2Index, L1Index),
    alloc_ptr_4k: RwLockPageAllocatorPtr, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, cpu_id: CpuId,
    pagetable_ptr: RwLockPageTableRoot, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, Tracked(thread_lock_perm): Tracked<&LockPerm>,
    Tracked(pagetable_lock_perm): Tracked<&LockPerm>, Tracked(window_perms): Tracked<Map<WindowVa, LockPerm>>,
) -> (ret: Tracked<Map<WindowVa, LockPerm>>)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k() == *old(krnl),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
        old(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
        old(krnl).prc_mp.dom().contains(process_ptr),
        old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        !thread_is_dangling(old(krnl).thr_mp.spec_index(thread_ptr)),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k >= 2,
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is Some,
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0 is Mmap4k,
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_range == *range,
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_mapped == 0,
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_phase is Fill,
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        range.wf(),
        i < range.len,
        start_indices == spec_va2index(range.start),
        end_indices == spec_va2index(range.view()[range.len - 1]),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(range.start),
        !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g().dom().contains(spec_index2va((spec_v2l4index(range.view()[i as int]), spec_v2l3index(range.view()[i as int]), 0, 0))),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == pagetable_ptr && va_range_2m_windows(*range).contains(w)
                && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some),
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) ==> {
            let table = pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr);
            &&& window_perms.dom().contains(w)
            &&& window_perms.index(w).state() is WriteLock
            &&& window_perms.index(w).thread_id() == old(lctx).thread_id()
            &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable_ptr, w), TypedLockMode::Write)
            &&& table.lower.l2_lock_of(table.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va))).lock_perm_match(spec_v2l2index(w.va), &window_perms.index(w))
        },
    ensures
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        nonwindow_typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        held_locks_order_below(final(krnl), final(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len() <= old(steps).view().len() + 2,
        final(steps).nonlock_view().len() - old(steps).nonlock_view().len() == final(steps).view().len() - old(steps).view().len(),
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==> mmap_4k_range_step(final(steps).view()[j], cpu_id),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        final(krnl).ctn_mp.dom().contains(container_ptr),
        final(krnl).ctn_mp.spec_index(container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata(),
        final(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
        final(krnl).prc_mp.dom().contains(process_ptr),
        final(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        final(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
        final(krnl).thr_mp.dom().contains(thread_ptr),
        !final(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        !thread_is_dangling(final(krnl).thr_mp.spec_index(thread_ptr)),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        final(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        final(krnl).thr_mp.spec_index(thread_ptr).view().state == old(krnl).thr_mp.spec_index(thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k - 2 <= final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k <= old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k,
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is Some,
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0 is Mmap4k,
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_range == *range,
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_mapped == 0,
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_phase is Fill,
        thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).pt_mp.dom().contains(pagetable_ptr),
        pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.window_stale_cpus == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.window_stale_cpus,
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(spec_v2l4index(range.view()[i as int]), spec_v2l3index(range.view()[i as int])) is Some,
        forall|l4i: L4Index, l3i: L3Index| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i)]
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i)
                && !(l4i == spec_v2l4index(range.view()[i as int]) && l3i == spec_v2l3index(range.view()[i as int]))
                ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i),
        ({
            let cur = spec_va2index(range.view()[i as int]);
            let lo = if cur.0 == start_indices.0 && cur.1 == start_indices.1 { start_indices.2 } else { 0usize };
            let hi = if cur.0 == end_indices.0 && cur.1 == end_indices.1 { end_indices.2 } else { 511usize };
            let installed = pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(cur.0, cur.1) is None;
            &&& forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (old(lctx).pagetable_window_lock_map().dom().contains((p, w))
                    || (installed && p == pagetable_ptr && w.wf() && spec_v2l4index(w.va) == cur.0 && spec_v2l3index(w.va) == cur.1 && lo <= spec_v2l2index(w.va) <= hi))
            &&& forall|w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w))]
                final(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) && installed && w.wf() && spec_v2l4index(w.va) == cur.0 && spec_v2l3index(w.va) == cur.1
                    && lo <= spec_v2l2index(w.va) <= hi ==> {
                    let table = pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr);
                    &&& ret.view().dom().contains(w)
                    &&& ret.view().index(w).state() is WriteLock
                    &&& ret.view().index(w).thread_id() == final(lctx).thread_id()
                    &&& typed_lock_map_contains_mode(final(lctx).pagetable_window_lock_map(), (pagetable_ptr, w), TypedLockMode::Write)
                    &&& table.lower.l2_lock_of(table.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va))).lock_perm_match(spec_v2l2index(w.va), &ret.view().index(w))
                }
        }),
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) ==> ret.view().dom().contains(w) && ret.view().index(w) == window_perms.index(w),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().index((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w)) ==> final(lctx).pagetable_window_lock_map().index((p, w)) == old(lctx).pagetable_window_lock_map().index((p, w)),
        forall|l4i: L4Index, l3i: L3Index| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i))]
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_exists(l4i, l3i)
                ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i))
                    == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.l2_lock_of(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i)),
{
    let tracked mut window_perms = window_perms;
    proof { broadcast use spec_va_2m_valid_index_roundtrip, spec_index2va_2m_valid; }
    let cur_va = range.index(i);
    let cur = va2index(cur_va);
    proof {
        range.va_range_lemma();
        spec_va_4k_valid_index_roundtrip(cur_va);
        spec_va_4k_valid_index_roundtrip(range.start);
        spec_va_4k_valid_index_roundtrip(range.view()[range.len - 1]);
        spec_v2l4index_monotonic(range.start, cur_va);
        spec_index2va_le_implies_4k_indices_lex_le(start_indices, cur);
        spec_index2va_le_implies_4k_indices_lex_le(cur, end_indices);
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
    }
    let (l4_present, l3_present) = {
        let pagetable = krnl.pt_mp.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
        match pagetable.get_entry_l4(cur.0) {
            None => (false, false),
            Some(l4_entry) => (true, pagetable.get_entry_l3(cur.0, cur.1, &l4_entry).is_some()),
        }
    };
    if !l4_present {
        proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
        let ghost before = steps.view();
        let _ = install_one_mmap_4k_directory_page(
            krnl, MissingPageTableLevel::L4, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, (cur.0, cur.1, cur.2), cur.2, cur.2, true, None, Ghost(thread_ptr),
            Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm), Tracked(None), Tracked(None),
        );
        proof { mmap_4k_range_steps_from_directory(&*steps, before, old(steps).view().len() as int, cpu_id); }
    }
    if !l3_present {
        let lo = if cur.0 == start_indices.0 && cur.1 == start_indices.1 { start_indices.2 } else { 0 };
        let hi = if cur.0 == end_indices.0 && cur.1 == end_indices.1 { end_indices.2 } else { 511 };
        proof {
            kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl);
            pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr); pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).higher.wf_mapping_1g_at(cur.0, cur.1);
        }
        let ghost before = steps.view();
        let Tracked(minted) = install_one_mmap_4k_directory_page(
            krnl, MissingPageTableLevel::L3, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, (cur.0, cur.1, cur.2), lo, hi, true, None, Ghost(thread_ptr),
            Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm), Tracked(None), Tracked(None),
        );
        proof {
            mmap_4k_range_steps_from_directory(&*steps, before, old(steps).view().len() as int, cpu_id);
            broadcast use Set::lemma_map_by_contains;
            let key_map = Map::new(minted.dom().map_by(|l2i: L2Index| WindowVa { va: spec_index2va((cur.0, cur.1, l2i, 0usize)) }, |w: WindowVa| spec_v2l2index(w.va)),
                |w: WindowVa| spec_v2l2index(w.va));
            let tracked moved = Map::<L2Index, LockPerm>::tracked_map_keys(minted, key_map);
            window_perms.tracked_union_prefer_right(moved);
        }
    }
    Tracked(window_perms)
}

/// In the fill phase, under the pagetable's big write lock and holding exactly the existing 2M windows of `range` through
/// `window_perms`: installs every missing L4 and L3 directory on the walks of `range`, page by page, recording one directory
/// step per installed page. A new L2 page starts with the range's windows under it held, and their perms join the returned
/// map, so afterwards every window of the range exists and is held through it.
pub(super) fn mmap_4k_fill_range_structure(
    krnl: &mut KernelK, range: &VaRange4K, alloc_ptr_4k: RwLockPageAllocatorPtr, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr,
    cpu_id: CpuId, pagetable_ptr: RwLockPageTableRoot, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, Tracked(thread_lock_perm): Tracked<&LockPerm>,
    Tracked(pagetable_lock_perm): Tracked<&LockPerm>, Tracked(window_perms): Tracked<Map<WindowVa, LockPerm>>,
) -> (ret: Tracked<Map<WindowVa, LockPerm>>)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k() == *old(krnl),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
        old(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
        old(krnl).prc_mp.dom().contains(process_ptr),
        old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        !thread_is_dangling(old(krnl).thr_mp.spec_index(thread_ptr)),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k >= 4 * range.len,
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap4k { range: *range, mapped: 0, directory: Mmap4kDirectory::None, phase: Mmap4kPhase::Fill }),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        range.wf(),
        range.len > 0,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(range.start),
        forall|j: int| #![trigger range.view()[j]] 0 <= j < range.len
            ==> !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g().dom().contains(spec_index2va((spec_v2l4index(range.view()[j]), spec_v2l3index(range.view()[j]), 0, 0))),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == pagetable_ptr && va_range_2m_windows(*range).contains(w)
                && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some),
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) ==> {
            let table = pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr);
            &&& window_perms.dom().contains(w)
            &&& window_perms.index(w).state() is WriteLock
            &&& window_perms.index(w).thread_id() == old(lctx).thread_id()
            &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable_ptr, w), TypedLockMode::Write)
            &&& table.lower.l2_lock_of(table.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va))).lock_perm_match(spec_v2l2index(w.va), &window_perms.index(w))
        },
    ensures
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        nonwindow_typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        held_locks_order_below(final(krnl), final(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len() <= old(steps).view().len() + 2 * range.len,
        final(steps).nonlock_view().len() - old(steps).nonlock_view().len() == final(steps).view().len() - old(steps).view().len(),
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==> mmap_4k_range_step(final(steps).view()[j], cpu_id),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        final(krnl).ctn_mp.dom().contains(container_ptr),
        final(krnl).ctn_mp.spec_index(container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata(),
        final(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
        final(krnl).prc_mp.dom().contains(process_ptr),
        final(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        final(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
        final(krnl).thr_mp.dom().contains(thread_ptr),
        !final(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        !thread_is_dangling(final(krnl).thr_mp.spec_index(thread_ptr)),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        final(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        final(krnl).thr_mp.spec_index(thread_ptr).view().state == old(krnl).thr_mp.spec_index(thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k - 2 * range.len <= final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k <= old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k,
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is Some,
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0 is Mmap4k,
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_range == *range,
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_mapped == 0,
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_phase is Fill,
        thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).pt_mp.dom().contains(pagetable_ptr),
        pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.window_stale_cpus == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.window_stale_cpus,
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).higher.spec_mapping_4k_va_range_windows_exist(range),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == pagetable_ptr && va_range_2m_windows(*range).contains(w)),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*range).contains(w)] va_range_2m_windows(*range).contains(w) ==> {
            let table = pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr);
            &&& typed_lock_map_contains_mode(final(lctx).pagetable_window_lock_map(), (pagetable_ptr, w), TypedLockMode::Write)
            &&& ret.view().dom().contains(w)
            &&& ret.view().index(w).state() is WriteLock
            &&& ret.view().index(w).thread_id() == final(lctx).thread_id()
            &&& table.lower.l2_lock_of(table.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va))).lock_perm_match(spec_v2l2index(w.va), &ret.view().index(w))
        },
{
    let tracked mut window_perms = window_perms;
    let range_len = range.len;
    let start_indices = va2index(range.start);
    let end_indices = va2index(range.index(range_len - 1));
    let mut i: usize = 0;
    while i < range_len
        invariant
            krnl.inv(),
            lctx.kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(krnl, lctx),
            nonwindow_typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.thread_id() == old(lctx).thread_id(),
            held_locks_order_below(krnl, lctx, ALLOCATOR_CACHE_4K_MAJOR),
            steps.snapshot_k() == *krnl,
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
            typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            lctx.page_lock_map().dom().is_empty(),
            lctx.scheduler_lock_map().dom().is_empty(),
            lctx.cpu_set_lock_map().dom().is_empty(),
            krnl.cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
            !krnl.cpu_arr.spec_index(cpu_id).view().being_killed(),
            krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
            krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
            krnl.cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
            old(krnl).ctn_mp.dom().contains(container_ptr),
            krnl.ctn_mp.dom().contains(container_ptr),
            krnl.ctn_mp.spec_index(container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata(),
            krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            krnl.allc_4k_mp.dom().contains(alloc_ptr_4k),
            krnl.prc_mp.dom().contains(process_ptr),
            krnl.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
            krnl.prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
            old(krnl).thr_mp.dom().contains(thread_ptr),
            krnl.thr_mp.dom().contains(thread_ptr),
            !krnl.thr_mp.spec_index(thread_ptr).being_killed(),
            !thread_is_dangling(krnl.thr_mp.spec_index(thread_ptr)),
            krnl.thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
            krnl.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
            krnl.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
            krnl.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable_ptr,
            krnl.thr_mp.spec_index(thread_ptr).view().state == old(krnl).thr_mp.spec_index(thread_ptr).view().state,
            krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            krnl.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k >= 4 * range_len,
            old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k - 2 * i <= krnl.thr_mp.spec_index(thread_ptr).view().quota_4k <= old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k,
            krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is Some,
            krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0 is Mmap4k,
            krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_range == *range,
            krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_mapped == 0,
            krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_phase is Fill,
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == krnl.thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            krnl.pt_mp.dom().contains(pagetable_ptr),
            pagetable_lock_perm.state() is WriteLock,
            pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
            pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_4k() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k(),
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m(),
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g(),
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).lower.window_stale_cpus == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.window_stale_cpus,
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).kernel_l4_end() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end(),
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(range.start),
            range.wf(),
            range.len == range_len,
            0 < range_len,
            i <= range_len,
            start_indices == spec_va2index(range.start),
            end_indices == spec_va2index(range.view()[range_len - 1]),
            forall|j: int| #![trigger range.view()[j]] 0 <= j < range.len
                ==> !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g().dom().contains(spec_index2va((spec_v2l4index(range.view()[j]), spec_v2l3index(range.view()[j]), 0, 0))),
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger lctx.pagetable_window_lock_map().dom().contains((p, w))]
                lctx.pagetable_window_lock_map().dom().contains((p, w)) == (p == pagetable_ptr && va_range_2m_windows(*range).contains(w)
                    && pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some),
            forall|w: WindowVa|
                #![trigger lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, w))]
                #![trigger va_range_2m_windows(*range).contains(w)]
                lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) ==> {
                let table = pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
                &&& window_perms.dom().contains(w)
                &&& window_perms.index(w).state() is WriteLock
                &&& window_perms.index(w).thread_id() == lctx.thread_id()
                &&& typed_lock_map_contains_mode(lctx.pagetable_window_lock_map(), (pagetable_ptr, w), TypedLockMode::Write)
                &&& table.lower.l2_lock_of(table.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va))).lock_perm_match(spec_v2l2index(w.va), &window_perms.index(w))
            },
            0 < i ==> forall|l4i: L4Index, l3i: L3Index|
                #![trigger pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i)]
                #![trigger pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).higher.spec_resolve_mapping_l3(l4i, l3i)]
                pei_valid(l4i) && pei_valid(l3i) && (start_indices.0 < l4i || (start_indices.0 == l4i && start_indices.1 <= l3i))
                    && (l4i < spec_v2l4index(range.view()[i - 1]) || (l4i == spec_v2l4index(range.view()[i - 1]) && l3i <= spec_v2l3index(range.view()[i - 1])))
                    ==> pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i) is Some,
            old(steps).view().len() <= steps.view().len() <= old(steps).view().len() + 2 * i,
            steps.nonlock_view().len() - old(steps).nonlock_view().len() == steps.view().len() - old(steps).view().len(),
            forall|j: int| #![trigger steps.view()[j]] 0 <= j < old(steps).view().len() ==> steps.view()[j] == old(steps).view()[j],
            forall|j: int| #![trigger steps.view()[j]] old(steps).view().len() <= j < steps.view().len() ==> mmap_4k_range_step(steps.view()[j], cpu_id),
        decreases range_len - i,
    {
        proof {
            range.va_range_lemma();
            spec_va_4k_valid_index_roundtrip(range.view()[i as int]);
            spec_va_4k_valid_index_roundtrip(range.start);
            spec_index2va_le_implies_4k_indices_lex_le(start_indices, spec_va2index(range.view()[i as int]));
            broadcast use spec_va_2m_valid_index_roundtrip, spec_index2va_2m_valid;
            spec_va_4k_valid_index_roundtrip(range.view()[range.len - 1]);
            spec_v2l4index_monotonic(range.start, range.view()[i as int]);
            spec_index2va_le_implies_4k_indices_lex_le(spec_va2index(range.view()[i as int]), end_indices);
            if 0 < i {
                let prev_va = range.view()[i - 1];
                let cur_va = range.view()[i as int];
                assert((spec_v2l4index(cur_va) == spec_v2l4index(prev_va) && spec_v2l3index(cur_va) == spec_v2l3index(prev_va))
                    || (spec_v2l4index(cur_va) == spec_v2l4index(prev_va) && spec_v2l3index(cur_va) == add(spec_v2l3index(prev_va), 1usize))
                    || (spec_v2l4index(cur_va) == add(spec_v2l4index(prev_va), 1usize) && spec_v2l3index(cur_va) == 0 && spec_v2l3index(prev_va) == 511)) by (bit_vector)
                    requires spec_va_4k_valid(prev_va), spec_va_4k_valid(cur_va), cur_va == add(prev_va, 4096usize);
            }
        }
        let Tracked(next) = mmap_4k_fill_page_directories(krnl, range, i, start_indices, end_indices, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr,
            Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm), Tracked(window_perms));
        proof { window_perms = next; }
        i = i + 1;
    }
    proof { broadcast use spec_va_2m_valid_index_roundtrip; }
    Tracked(window_perms)
}
} // verus!
