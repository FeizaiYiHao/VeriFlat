use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::set::lemma_set_remove_len;

verus! {
use crate::*;
use super::mmap_4k_build_structure_spec::*;
#[cfg(verus_keep_ghost)]
use super::mmap_4k_create_entry_install_eof::*;

    /// Consume one staged 4K page and publish it as exactly one page-table
    /// structure page.  The parent pointer is intentionally recovered from the
    /// locked PageTable here rather than accepted from the caller: the semantic
    /// missing level determines both the parent and the PageTable operation.
    ///
    /// Hidden Page/Thread state is made consistent while the krnl phase is
    /// Acquire. The single parent-entry store closes it into Release. Directory
    /// topology is absent from `PageTableU`, while the consumed quota is visible
    /// through `ThreadU` at the following boundary.
    ///
    /// L4 and L3 need the table's big write lock (`write_held`); an L2 page is linked under either big-lock mode while this thread
    /// holds the 2M window. A new L2 page starts with windows `lo..=hi` held by this thread and returns their lock perms.
    #[verifier::spinoff_prover]
    pub(super) fn install_staged_4k_page_table_page(
        krnl: &mut KernelK, level: MissingPageTableLevel, page_ptr: PagePtr, quota_thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr,
        pagetable_ptr: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index), lo: L2Index, hi: L2Index, write_held: bool, Tracked(lctx): Tracked<&mut LocalContext>,
        page_lock_perm: Tracked<&LockPerm>, quota_thread_lock_perm: Tracked<&LockPerm>, pagetable_lock_perm: Tracked<&LockPerm>, Tracked(window_perm): Tracked<Option<&LockPerm>>,
    ) -> (ret: Tracked<Map<L2Index, LockPerm>>)
        requires
            old(krnl).inv(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(lctx).kernel_view_locking_state() is Acquire,
            page_ptr_valid(page_ptr),
            old(krnl).thr_mp.dom().contains(quota_thread_ptr),
            old(krnl).thr_mp.spec_index(quota_thread_ptr).being_killed() == false,
            mmap_4k_quota_thread_container_compatible(old(krnl), old(lctx), quota_thread_ptr, container_ptr),
            old(krnl).prc_mp.dom().contains(process_ptr),
            old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
            old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
            old(krnl).pt_mp.dom().contains(pagetable_ptr),
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= indices.0,
            pei_valid(indices.0),
            pei_valid(indices.1),
            pei_valid(indices.2),
            KERNEL_MEM_END_L4INDEX <= indices.0,
            pei_valid(lo) && pei_valid(hi) && lo <= hi,
            page_table_key_2m_valid::<PT_TYPE>(spec_index2va((indices.0, indices.1, indices.2, 0))),
            !(level is L2) ==> write_held,
            level is L2 ==> old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, WindowVa { va: spec_index2va((indices.0, indices.1, indices.2, 0usize)) })),
            level is L2 ==> window_perm is Some
                && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.l2_owner(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2)
                    == (SpinLockState::Some { thread_id: window_perm->Some_0.thread_id(), lock_id: window_perm->Some_0.lock_id() }),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: quota_thread_ptr }),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == container_ptr,
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr),
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k >= 1,
            typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
            page_lock_perm.view().state() is WriteLock,
            page_lock_perm.view().thread_id() == old(lctx).thread_id(),
            page_lock_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), quota_thread_ptr, TypedLockMode::Write),
            quota_thread_lock_perm.view().state() is WriteLock,
            quota_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
            quota_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(quota_thread_ptr).locking_thread()->Write_lock_id,
            pagetable_lock_perm.view().thread_id() == old(lctx).thread_id(),
            write_held ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            write_held ==> pagetable_lock_perm.view().state() is WriteLock,
            write_held ==> pagetable_lock_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            !write_held ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
            !write_held ==> pagetable_lock_perm.view().state() is ReadLock,
            !write_held ==> old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.view().lock_id()),
            match level {
                MissingPageTableLevel::L4 => pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(indices.0) is None,
                MissingPageTableLevel::L3 => {
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(indices.0) is Some
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is None
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_1g_l3(indices.0, indices.1) is None
                },
                MissingPageTableLevel::L2 => {
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None
                },
            },
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            final(lctx).page_lock_map() == old(lctx).page_lock_map().insert(page_ptr2page_index(page_ptr), TypedHeldLock {
                lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write }),
            final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
            final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
            final(lctx).container_lock_map() == old(lctx).container_lock_map(),
            final(lctx).process_lock_map() == old(lctx).process_lock_map(),
            final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
            final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
            final(lctx).allocator_quota_4k_lock_map() == old(lctx).allocator_quota_4k_lock_map(),
            final(lctx).allocator_cache_4k_lock_map() == old(lctx).allocator_cache_4k_lock_map(),
            final(lctx).allocator_global_pool_4k_lock_map() == old(lctx).allocator_global_pool_4k_lock_map(),
            final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            !(level is L3) ==> final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
            !(level is L3) ==> ret.view() == Map::<L2Index, LockPerm>::empty(),
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (old(lctx).pagetable_window_lock_map().dom().contains((p, w))
                    || (level is L3 && p == pagetable_ptr && w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1 && lo <= spec_v2l2index(w.va) <= hi)),
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().index((p, w))]
                old(lctx).pagetable_window_lock_map().dom().contains((p, w))
                    && !(level is L3 && p == pagetable_ptr && w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1 && lo <= spec_v2l2index(w.va) <= hi)
                    ==> final(lctx).pagetable_window_lock_map().index((p, w)) == old(lctx).pagetable_window_lock_map().index((p, w)),
            forall|w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().index((pagetable_ptr, w))]
                level is L3 && w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1 && lo <= spec_v2l2index(w.va) <= hi
                    ==> final(lctx).pagetable_window_lock_map().index((pagetable_ptr, w)) == (TypedHeldLock { lock_id: window_lock_id_of(pagetable_ptr, w), mode: TypedLockMode::Write }),
            forall|i: L2Index| #![trigger ret.view().dom().contains(i)] ret.view().dom().contains(i) == (level is L3 && lo <= i <= hi),
            forall|i: L2Index| #![trigger ret.view().index(i)] level is L3 && lo <= i <= hi ==> {
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_owner(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(indices.0, indices.1), i)
                    == (SpinLockState::Some { thread_id: ret.view().index(i).thread_id(), lock_id: ret.view().index(i).lock_id() })
                &&& ret.view().index(i).state() is WriteLock
                &&& ret.view().index(i).thread_id() == final(lctx).thread_id()
            },
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
            typed_lock_map_contains_mode(final(lctx).thread_lock_map(), quota_thread_ptr, TypedLockMode::Write),
            page_lock_perm.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
            quota_thread_lock_perm.view().lock_id() == final(krnl).thr_mp.spec_index(quota_thread_ptr).locking_thread()->Write_lock_id,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).being_killed() == false,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view() == (Thread {
                quota_4k: final(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k, temp_alloc_cache_4k: final(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_4k,
                syscall_progress: final(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(quota_thread_ptr).view()
            }),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view() == mmap_4k_progress_after_directory(old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view(), level),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(quota_thread_ptr).view_ghost(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_4k.view().remove(page_ptr),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k - 1,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_2m.view() == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_2m.view(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_1g.view() == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_1g.view(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_2m == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_2m,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_1g == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_1g,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().free_quota_pending_fields_unchanged(&old(krnl).thr_mp.spec_index(quota_thread_ptr).view()),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().state == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().state,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().blocking_endpoint_ptr,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_container == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_container,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().upper_container_seq == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().upper_container_seq,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_proc == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_proc,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().proc_pagetable_ptr,
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr == old(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr,
            final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, pagetable_ptr),
            final(krnl).pt_lower.view() == old(krnl).pt_lower.view().insert(pagetable_ptr, final(krnl).pt_lower.view().spec_index(pagetable_ptr)),
            final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread() == old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread(),
            final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(page_ptr)),
            final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, quota_thread_ptr),
            *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, pg_arr: final(krnl).pg_arr, thr_mp: final(krnl).thr_mp, ..*old(krnl) }),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k() =~= pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_2m() =~= pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_1g() =~= pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.window_stale_cpus == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.window_stale_cpus,
            level is L2 ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).higher == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).higher,
            !(level is L3) ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks,
            !(level is L3) ==> forall|p: PageMapPtr, i: L2Index| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_owner(p, i)]
                pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_owner(p, i) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.l2_owner(p, i),
            level is L3 ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks == Map::new(
                pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks.dom() + Set::<usize>::range(0, 512).map_by(|i: usize| WindowVa { va: spec_index2va((indices.0, indices.1, i, 0usize)) }, |w: WindowVa| spec_v2l2index(w.va)),
                |w: WindowVa| if pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks.dom().contains(w) {
                    pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks[w]
                } else if lo <= spec_v2l2index(w.va) <= hi { LockStateU::WriteLocked } else { LockStateU::Unlocked }),
            forall|l4i: L4Index, l3i: L3Index| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i)]
                pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && !(level is L3 && l4i == indices.0 && l3i == indices.1)
                    ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i)]
                pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                    ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_owner(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i), l2i)]
                pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_exists(l4i, l3i)
                    ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_owner(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i), l2i)
                        == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.l2_owner(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i), l2i),
            match level {
                MissingPageTableLevel::L4 => {
                    &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(indices.0) is Some
                    &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is None
                    &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_1g_l3(indices.0, indices.1) is None
                },
                MissingPageTableLevel::L3 => {
                    &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some
                    &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None
                    &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None
                },
                MissingPageTableLevel::L2 => pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
            },
    {
        let page_index = page_ptr2page_index(page_ptr);
        let ghost window_va = WindowVa { va: spec_index2va((indices.0, indices.1, indices.2, 0usize)) };
        let ghost staged_k = *krnl;
        assert(krnl.pt_mp.perms_wf() && krnl.pt_mp.spec_index(pagetable_ptr).inv() && krnl.thr_mp.perms_wf() && krnl.thr_mp.spec_index(quota_thread_ptr).inv()) by {
            pagetable_perms_wf_map(krnl.pt_mp);
            pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); thread_perms_wf_map(krnl.thr_mp); thread_perms_wf_at(krnl.thr_mp, quota_thread_ptr);
        };
        assert(index_valid(NUM_PAGES, page_index) && krnl.pg_arr.inv() && krnl.pg_arr.spec_index(page_index).view().is_init() && krnl.pg_arr.spec_index(page_index).view().inv()
            && krnl.pg_arr.spec_index(page_index).view().view().inv() && krnl.pg_arr.spec_index(page_index).view().view().addr == page_ptr) by {
            page_ptr_valid_imply_page_index_valid(); page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, page_index);
        };
        assert(!pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).page_closure().contains(page_ptr)) by {
            if pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).page_closure().contains(page_ptr) {
                pagetable_pages_wf_closure_entry_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pagetable_ptr, page_ptr);
            }
        };
        proof {
            pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
            if write_held { krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); }
            else { krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); }
            if write_held { pagetable_lower_backup_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr); }
            if level is L2 {
                pagetable_window_typed_lock_map_aligned_at(krnl.pt_mp, krnl.pt_lower.view(), lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr, window_va);
                spec_va_4k_index_roundtrip_at(window_va.va, indices.0, indices.1, indices.2, 0usize);
            }
        }

        let parent_page_map_ptr;
        {
            let pagetable = krnl.pt_mp.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), pagetable_lock_perm);
            parent_page_map_ptr = match level {
                MissingPageTableLevel::L4 => pagetable.cr3,
                MissingPageTableLevel::L3 => pagetable.get_entry_l4(indices.0).unwrap().addr,
                MissingPageTableLevel::L2 => {
                    let l4_entry = pagetable.get_entry_l4(indices.0).unwrap();
                    pagetable.get_entry_l3(indices.0, indices.1, &l4_entry).unwrap().addr
                },
            };
        }

        let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
        let Tracked(page_perm) = {
            let page = krnl.pg_arr.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), page_lock_perm);
            let tracked_perm = take_perm_4k(page);
            page.state = PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: pagetable_ptr, table_type: PT_TYPE } };
            tracked_perm
        };
        {
            let thread = krnl.thr_mp.borrow_mut_typed(quota_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), quota_thread_lock_perm);
            thread.temp_alloc_cache_4k = Ghost(thread.temp_alloc_cache_4k.view().remove(page_ptr));
            thread.quota_4k = thread.quota_4k - 1;
            thread.syscall_progress = Ghost(mmap_4k_progress_after_directory(thread.syscall_progress.view(), level));
        }
        let full_indices = (indices.0, indices.1, indices.2, 0usize);
        let tracked mut windows: Map<L2Index, LockPerm> = Map::tracked_empty();
        match level {
            MissingPageTableLevel::L4 => {
                let (page_map_ptr, Tracked(page_map_perm)) = page_perm_to_page_map(page_ptr, Tracked(page_perm));
                pagetable_map_create_entry_l4(&mut krnl.pt_mp, Tracked(krnl.pt_lower.borrow()), pagetable_ptr, full_indices, page_map_ptr, Tracked(page_map_perm), Tracked(&mut *lctx),
                    pagetable_lock_perm);
            },
            MissingPageTableLevel::L3 => {
                let Tracked(minted) = pagetable_map_create_entry_l3(&mut krnl.pt_mp, Tracked(krnl.pt_lower.borrow_mut()), pagetable_ptr, full_indices, parent_page_map_ptr, page_ptr,
                    Tracked(page_perm), lo, hi, Tracked(&mut *lctx), pagetable_lock_perm);
                proof { windows = minted; }
            },
            MissingPageTableLevel::L2 => {
                let (page_map_ptr, Tracked(page_map_perm)) = page_perm_to_page_map(page_ptr, Tracked(page_perm));
                let tracked window_perm = window_perm.tracked_unwrap();
                if write_held {
                    pagetable_map_create_entry_l2_wlocked(&mut krnl.pt_mp, Tracked(krnl.pt_lower.borrow_mut()), pagetable_ptr, full_indices, parent_page_map_ptr, page_map_ptr,
                        Tracked(page_map_perm), Tracked(window_perm), Tracked(&mut *lctx), pagetable_lock_perm);
                } else {
                    pagetable_map_create_entry_l2(&krnl.pt_mp, Tracked(krnl.pt_lower.borrow_mut()), pagetable_ptr, full_indices, parent_page_map_ptr, page_map_ptr, Tracked(page_map_perm),
                        Tracked(window_perm), Tracked(&mut *lctx), pagetable_lock_perm);
                }
            },
        }
        proof {
            lctx.update_lock_id(KernelObjId::Page(page_index), old_page_lock_id, krnl.pg_arr.lock_id_by_index(page_index));
            assert(krnl.pt_lower.view() =~= staged_k.pt_lower.view().insert(pagetable_ptr, krnl.pt_lower.view().spec_index(pagetable_ptr)));
            assert(install_staged_4k_page_table_page_eof_transition_framing(staged_k, *krnl, level, page_ptr, quota_thread_ptr, pagetable_ptr)) by {
                reveal(install_staged_4k_page_table_page_eof_transition_framing);
            };
            install_staged_4k_page_table_page_eof(staged_k, *krnl, level, page_ptr, quota_thread_ptr, process_ptr, container_ptr, pagetable_ptr);
            held_pagetables_unchanged_except_for_unchanged_except(old(krnl).pt_mp, krnl.pt_mp, old(lctx), pagetable_ptr);
        }
        Tracked(windows)
    }
}
