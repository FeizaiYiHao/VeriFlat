use vstd::prelude::*;

verus! {
use crate::*;
use super::mmap_4k_build_structure::MissingPageTableLevel;
use super::mmap_4k_build_structure_spec::*;
use super::map_iommu_4k_spec::*;
#[cfg(verus_keep_ghost)]
use super::map_iommu_4k_directory_eof::*;

/// IOMMU mirror of `install_staged_4k_page_table_page`: consume one staged 4K page and publish it as exactly one table
/// page of the write-held IOMMU table `iommu_table_ptr`. The parent pointer is recovered from the locked table, and the
/// missing level selects both the parent and the create-entry primitive.
pub fn install_staged_4k_iommu_table_page(
    krnl: &mut KernelK, level: MissingPageTableLevel, pg_ptr: PagePtr, quota_thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr,
    iommu_table_ptr: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index), Tracked(lctx): Tracked<&mut LocalContext>,
    page_lock_perm: Tracked<&LockPerm>, quota_thread_lock_perm: Tracked<&LockPerm>, iommu_table_lock_perm: Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        page_ptr_valid(pg_ptr),
        old(krnl).thrd_mp.dom().contains(quota_thrd_ptr),
        old(krnl).thrd_mp.spec_index(quota_thrd_ptr).being_killed() == false,
        mmap_4k_quota_thread_container_compatible(old(krnl), old(lctx), quota_thrd_ptr, ctn_ptr),
        old(krnl).prc_mp.dom().contains(prc_ptr),
        old(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container == ctn_ptr,
        old(krnl).prc_mp.spec_index(prc_ptr).view().iommu_table == Some(iommu_table_ptr),
        old(krnl).it_mp.dom().contains(iommu_table_ptr),
        pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: quota_thrd_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == ctn_ptr,
        old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().temp_alloc_cache_4k.view().contains(pg_ptr),
        old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().quota_4k >= 1,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write),
        page_lock_perm.view().state() is WriteLock,
        page_lock_perm.view().thread_id() == old(lctx).thread_id(),
        page_lock_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), quota_thrd_ptr, TypedLockMode::Write),
        quota_thread_lock_perm.view().state() is WriteLock,
        quota_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        quota_thread_lock_perm.view().lock_id() == old(krnl).thrd_mp.spec_index(quota_thrd_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write),
        iommu_table_lock_perm.view().state() is WriteLock,
        iommu_table_lock_perm.view().thread_id() == old(lctx).thread_id(),
        iommu_table_lock_perm.view().lock_id() == old(krnl).it_mp.spec_index(iommu_table_ptr).locking_thread()->Write_lock_id,
        match level {
            MissingPageTableLevel::L4 => old(krnl).it_mp.spec_index(iommu_table_ptr).view().spec_resolve_mapping_l4(indices.0) is None,
            MissingPageTableLevel::L3 => {
                &&& old(krnl).it_mp.spec_index(iommu_table_ptr).view().spec_resolve_mapping_l4(indices.0) is Some
                &&& old(krnl).it_mp.spec_index(iommu_table_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1) is None
            },
            MissingPageTableLevel::L2 => {
                &&& old(krnl).it_mp.spec_index(iommu_table_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1) is Some
                &&& old(krnl).it_mp.spec_index(iommu_table_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None
            },
        },
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).page_lock_map() == old(lctx).page_lock_map().insert(page_ptr2page_index(pg_ptr), TypedHeldLock {
            lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(pg_ptr)), mode: TypedLockMode::Write }),
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
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_quota_4k_lock_map() == old(lctx).allocator_quota_4k_lock_map(),
        final(lctx).allocator_cache_4k_lock_map() == old(lctx).allocator_cache_4k_lock_map(),
        final(lctx).allocator_global_pool_4k_lock_map() == old(lctx).allocator_global_pool_4k_lock_map(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), quota_thrd_ptr, TypedLockMode::Write),
        page_lock_perm.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id,
        quota_thread_lock_perm.view().lock_id() == final(krnl).thrd_mp.spec_index(quota_thrd_ptr).locking_thread()->Write_lock_id,
        iommu_table_lock_perm.view().lock_id() == final(krnl).it_mp.spec_index(iommu_table_ptr).locking_thread()->Write_lock_id,
        final(krnl).thrd_mp.spec_index(quota_thrd_ptr).being_killed() == false,
        final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view() == (Thread {
            quota_4k: final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().quota_4k, temp_alloc_cache_4k: final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().temp_alloc_cache_4k,
            syscall_progress: final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().syscall_progress, ..old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view()
        }),
        final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().syscall_progress.view() == iommu_map_4k_progress_after_directory(old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().syscall_progress.view(), level),
        final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().temp_alloc_cache_4k.view().remove(pg_ptr),
        final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().quota_4k == old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().quota_4k - 1,
        final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().temp_alloc_cache_2m.view() == old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().temp_alloc_cache_2m.view(),
        final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().temp_alloc_cache_1g.view() == old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().temp_alloc_cache_1g.view(),
        final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().quota_2m == old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().quota_2m,
        final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().quota_1g == old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().quota_1g,
        final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().free_quota_pending_fields_unchanged(&old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view()),
        final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().state == old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().state,
        final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().blocking_endpoint_ptr == old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().blocking_endpoint_ptr,
        final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().owning_container == old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().owning_container,
        final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().upper_container_seq == old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().upper_container_seq,
        final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().owning_proc == old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().owning_proc,
        final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().proc_pagetable_ptr == old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().proc_pagetable_ptr,
        *final(krnl) == (KernelK { it_mp: final(krnl).it_mp, pg_arr: final(krnl).pg_arr, thrd_mp: final(krnl).thrd_mp, ..*old(krnl) }),
        final(krnl).it_mp.unchanged_except(&old(krnl).it_mp, iommu_table_ptr),
        final(krnl).it_mp.spec_index(iommu_table_ptr).locking_thread() == old(krnl).it_mp.spec_index(iommu_table_ptr).locking_thread(),
        final(krnl).it_mp.spec_index(iommu_table_ptr).view().kernel_l4_end == old(krnl).it_mp.spec_index(iommu_table_ptr).view().kernel_l4_end,
        final(krnl).it_mp.spec_index(iommu_table_ptr).view().proc_ptr == old(krnl).it_mp.spec_index(iommu_table_ptr).view().proc_ptr,
        final(krnl).it_mp.spec_index(iommu_table_ptr).view().did == old(krnl).it_mp.spec_index(iommu_table_ptr).view().did,
        final(krnl).it_mp.spec_index(iommu_table_ptr).view().page_closure() == old(krnl).it_mp.spec_index(iommu_table_ptr).view().page_closure().insert(pg_ptr),
        final(krnl).it_mp.spec_index(iommu_table_ptr).view().mapping_4k() == old(krnl).it_mp.spec_index(iommu_table_ptr).view().mapping_4k(),
        final(krnl).it_mp.spec_index(iommu_table_ptr).view().mapping_2m() == old(krnl).it_mp.spec_index(iommu_table_ptr).view().mapping_2m(),
        final(krnl).it_mp.spec_index(iommu_table_ptr).view().mapping_1g() == old(krnl).it_mp.spec_index(iommu_table_ptr).view().mapping_1g(),
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(pg_ptr)),
        final(krnl).thrd_mp.unchanged_except(&old(krnl).thrd_mp, quota_thrd_ptr),
        match level {
            MissingPageTableLevel::L4 => {
                &&& final(krnl).it_mp.spec_index(iommu_table_ptr).view().spec_resolve_mapping_l4(indices.0) is Some
                &&& final(krnl).it_mp.spec_index(iommu_table_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1) is None
                &&& final(krnl).it_mp.spec_index(iommu_table_ptr).view().spec_resolve_mapping_1g_l3(indices.0, indices.1) is None
            },
            MissingPageTableLevel::L3 => {
                &&& final(krnl).it_mp.spec_index(iommu_table_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1) is Some
                &&& final(krnl).it_mp.spec_index(iommu_table_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None
                &&& final(krnl).it_mp.spec_index(iommu_table_ptr).view().spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None
            },
            MissingPageTableLevel::L2 => {
                &&& final(krnl).it_mp.spec_index(iommu_table_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some
                &&& final(krnl).it_mp.spec_index(iommu_table_ptr).view().spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None
            },
        },
{
    let pg_idx = page_ptr2page_index(pg_ptr);
    let ghost staged_k = *krnl;
    assert(krnl.thrd_mp.perms_wf() && krnl.thrd_mp.spec_index(quota_thrd_ptr).inv()) by { thread_perms_wf_map(krnl.thrd_mp); thread_perms_wf_at(krnl.thrd_mp, quota_thrd_ptr); };
    assert(index_valid(NUM_PAGES, pg_idx) && krnl.pg_arr.inv() && krnl.pg_arr.spec_index(pg_idx).view().is_init() && krnl.pg_arr.spec_index(pg_idx).view().inv()
        && krnl.pg_arr.spec_index(pg_idx).view().view().inv() && krnl.pg_arr.spec_index(pg_idx).view().view().addr == pg_ptr) by {
        page_ptr_valid_imply_page_index_valid(); page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, pg_idx);
    };
    assert(!krnl.it_mp.spec_index(iommu_table_ptr).view().page_closure().contains(pg_ptr)) by {
        if krnl.it_mp.spec_index(iommu_table_ptr).view().page_closure().contains(pg_ptr) { iommu_table_pages_wf_closure_page_at(krnl.it_mp, krnl.pg_arr, iommu_table_ptr, pg_ptr); }
    };
    proof {
        iommu_table_perms_wf_map(krnl.it_mp); iommu_table_perms_wf_at(krnl.it_mp, iommu_table_ptr); iommu_table_perms_wf_kernel_l4_end_at(krnl.it_mp, iommu_table_ptr);
        krnl.it_mp.typed_lock_map_aligned_write_at(lctx.iommu_table_lock_map(), lctx.thread_id(), iommu_table_ptr);
    }
    assert(krnl.it_mp.spec_index(iommu_table_ptr).view().spec_resolve_mapping_1g_l3(indices.0, indices.1) is None
        && krnl.it_mp.spec_index(iommu_table_ptr).view().spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None) by {
        iommu_table_no_huge_leaf_wf_at(krnl.it_mp, iommu_table_ptr);
        krnl.it_mp.spec_index(iommu_table_ptr).view().wf_mapping_1g_at(indices.0, indices.1); krnl.it_mp.spec_index(iommu_table_ptr).view().wf_mapping_2m_at(indices.0, indices.1, indices.2);
    };

    let parent_page_map_ptr;
    {
        let it = krnl.it_mp.borrow_typed(iommu_table_ptr, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), iommu_table_lock_perm);
        parent_page_map_ptr = match level {
            MissingPageTableLevel::L4 => it.cr3,
            MissingPageTableLevel::L3 => it.get_entry_l4(indices.0).unwrap().addr,
            MissingPageTableLevel::L2 => {
                let l4_entry = it.get_entry_l4(indices.0).unwrap();
                it.get_entry_l3(indices.0, indices.1, &l4_entry).unwrap().addr
            },
        };
    }

    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(pg_idx);
    let Tracked(page_perm) = {
        let page = krnl.pg_arr.borrow_mut_typed(pg_idx, Ghost(lctx.page_lock_map()), Tracked(&*lctx), page_lock_perm);
        let tracked_perm = take_perm_4k(page);
        page.state = PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: iommu_table_ptr, table_type: IOMMU_TYPE } };
        tracked_perm
    };
    {
        let thread = krnl.thrd_mp.borrow_mut_typed(quota_thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), quota_thread_lock_perm);
        thread.temp_alloc_cache_4k = Ghost(thread.temp_alloc_cache_4k.view().remove(pg_ptr));
        thread.quota_4k = thread.quota_4k - 1;
        thread.syscall_progress = Ghost(iommu_map_4k_progress_after_directory(thread.syscall_progress.view(), level));
    }
    let (page_map_ptr, Tracked(page_map_perm)) = page_perm_to_page_map(pg_ptr, Tracked(page_perm));
    match level {
        MissingPageTableLevel::L4 => {
            iommu_table_map_create_entry_l4(&mut krnl.it_mp, iommu_table_ptr, (indices.0, indices.1), page_map_ptr, Tracked(page_map_perm), Tracked(&mut *lctx), iommu_table_lock_perm);
        },
        MissingPageTableLevel::L3 => {
            iommu_table_map_create_entry_l3(&mut krnl.it_mp, iommu_table_ptr, indices, parent_page_map_ptr, page_map_ptr, Tracked(page_map_perm), Tracked(&mut *lctx), iommu_table_lock_perm);
        },
        MissingPageTableLevel::L2 => {
            iommu_table_map_create_entry_l2(&mut krnl.it_mp, iommu_table_ptr, indices, parent_page_map_ptr, page_map_ptr, Tracked(page_map_perm), Tracked(&mut *lctx), iommu_table_lock_perm);
        },
    }
    proof {
        lctx.update_lock_id(KernelObjId::Page(pg_idx), old_page_lock_id, krnl.pg_arr.lock_id_by_index(pg_idx));
        assert(install_staged_4k_iommu_table_page_eof_transition_framing(staged_k, *krnl, level, pg_ptr, quota_thrd_ptr, iommu_table_ptr)) by {
            reveal(install_staged_4k_iommu_table_page_eof_transition_framing);
        };
        install_staged_4k_iommu_table_page_eof(staged_k, *krnl, level, pg_ptr, quota_thrd_ptr, prc_ptr, ctn_ptr, iommu_table_ptr);
    }
}
}
