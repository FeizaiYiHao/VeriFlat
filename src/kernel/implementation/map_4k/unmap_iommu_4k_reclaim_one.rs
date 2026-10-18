use vstd::prelude::*;
use crate::*;
use super::unmap_iommu_4k_remove::remove_iommu_4k_mapping_without_free;
use super::unmap_iommu_4k_reclaim::remove_last_iommu_4k_mapping_to_allocator;

verus! {
proof fn prove_unmapped_iommu_4k_page_owner_position_in_thread_container_chain(
    krnl: &KernelK, iommu_table: RwLockPageTableRoot, iova: VAddr, page_ptr: PagePtr, thread_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, depth: usize, thread_depth: usize,
)
    requires
        krnl.inv(),
        krnl.it_mp.dom().contains(iommu_table),
        krnl.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(iova),
        krnl.it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(iova).addr == page_ptr,
        page_ptr_valid(page_ptr),
        krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == owner,
        krnl.ctn_mp.dom().contains(owner),
        krnl.ctn_mp.spec_index(owner).view_rodata().view().depth == depth,
        krnl.thr_mp.dom().contains(thread_ptr),
        !thread_is_dangling(krnl.thr_mp.spec_index(thread_ptr)),
        krnl.prc_mp.spec_index(krnl.thr_mp.spec_index(thread_ptr).view().owning_proc).view().iommu_table == Some(iommu_table)
            || krnl.prc_mp.spec_index(krnl.it_mp.spec_index(iommu_table).view().proc_ptr).view_rodata().view().owning_container == krnl.thr_mp.spec_index(thread_ptr).view().owning_container,
        krnl.thr_mp.spec_index(thread_ptr).view().container_depth == thread_depth,
    ensures
        depth <= thread_depth,
        thread_depth <= MAX_CONTAINER_TREE_DEPTH,
        if depth == thread_depth { owner == krnl.thr_mp.spec_index(thread_ptr).view().owning_container } else { krnl.thr_mp.spec_index(thread_ptr).view().upper_container_seq.view().spec_index(depth as int) == owner },
{
    let page_index = page_ptr2page_index(page_ptr);
    let proc_ptr = krnl.it_mp.spec_index(iommu_table).view().proc_ptr;
    let thread_proc = krnl.thr_mp.spec_index(thread_ptr).view().owning_proc;
    let thread_owner = krnl.thr_mp.spec_index(thread_ptr).view().owning_container;
    assert(krnl.pg_arr.spec_index(page_index).view().view().state == PageState::Mapped4k && krnl.pg_arr.spec_index(page_index).view().view().iommu_mappings().contains((iommu_table, iova))) by { reveal(page_iommu_table_wf); };
    assert(krnl.prc_mp.dom().contains(proc_ptr) && {
            ||| krnl.prc_mp.spec_index(proc_ptr).view_rodata().view().owning_container == owner
            ||| krnl.ctn_mp.spec_index(owner).view_ghost().subtree_set.view().contains(krnl.prc_mp.spec_index(proc_ptr).view_rodata().view().owning_container)
        }) by { reveal(page_iommu_table_wf); };
    assert(krnl.prc_mp.dom().contains(thread_proc) && krnl.prc_mp.spec_index(thread_proc).view_rodata().view().owning_container == thread_owner) by { reveal(process_thread_wf); };
    assert(krnl.prc_mp.spec_index(proc_ptr).view_rodata().view().owning_container == thread_owner) by { if krnl.prc_mp.spec_index(thread_proc).view().iommu_table == Some(iommu_table) { assert(proc_ptr == thread_proc) by { reveal(process_iommu_table_match); }; } };
    assert(krnl.ctn_mp.dom().contains(thread_owner) && krnl.ctn_mp.spec_index(thread_owner).view_ghost().owned_threads.view().contains(thread_ptr)
        && krnl.thr_mp.spec_index(thread_ptr).view().upper_container_seq == krnl.ctn_mp.spec_index(thread_owner).view_ghost().uppertree_seq
        && thread_depth == krnl.ctn_mp.spec_index(thread_owner).view_rodata().view().depth) by { reveal(container_thread_wf); };
    assert(krnl.thr_mp.spec_index(thread_ptr).view().upper_container_seq.view().len() == thread_depth
        && thread_depth <= MAX_CONTAINER_TREE_DEPTH) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    if owner != thread_owner {
        assert(krnl.ctn_mp.spec_index(thread_owner).view_ghost().uppertree_seq.view().len() > depth
            && krnl.ctn_mp.spec_index(thread_owner).view_ghost().uppertree_seq.view().spec_index(depth as int) == owner) by { reveal(container_subtree_set_wf); };
    }
}

/// Unmaps one hidden 4K leaf of a write-locked IOMMU table and frees its page when no other mapping remains.
pub fn reclaim_unmapped_iommu_4k_page(
    krnl: &mut KernelK, iommu_table: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index, L1Index), thread_ptr: RwLockThreadPtr, cpu_id: CpuId, indirect: &mut [usize; MAX_CONTAINER_TREE_DEPTH], direct: &mut usize,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, iommu_table_perm: Tracked<&LockPerm>, thread_perm: Tracked<&LockPerm>,
)
    requires
        old(steps).snapshot_k() == *old(krnl),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).page_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_MAJOR),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        !thread_is_dangling(old(krnl).thr_mp.spec_index(thread_ptr)),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc).view().iommu_table == Some(iommu_table)
            || old(krnl).prc_mp.spec_index(old(krnl).it_mp.spec_index(iommu_table).view().proc_ptr).view_rodata().view().owning_container == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container,
        *old(direct) == old(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
        forall|depth: int| #![trigger old(indirect)[depth]] 0 <= depth < old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth ==> old(indirect)[depth] == old(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(depth),
        old(krnl).it_mp.dom().contains(iommu_table),
        pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va(indices)),
        !old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(spec_index2va(indices)).present,
        typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table, TypedLockMode::Write),
        iommu_table_perm.view().state() is WriteLock,
        iommu_table_perm.view().thread_id() == old(lctx).thread_id(),
        iommu_table_perm.view().lock_id() == old(krnl).it_mp.spec_index(iommu_table).locking_thread()->Write_lock_id,
    ensures
        final(steps).view() == old(steps).view(),
        final(steps).snapshot_k() == *final(krnl),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        held_threads_unchanged_except(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx), set![thread_ptr]),
        final(steps).nonlock_view() == old(steps).nonlock_view(),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { direct_free_quota_pending_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k,
            indirect_free_quota_pending_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        *final(direct) == final(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
        forall|depth: int| #![trigger final(indirect)[depth]] 0 <= depth < final(krnl).thr_mp.spec_index(thread_ptr).view().container_depth ==> final(indirect)[depth] == final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(depth),
        final(krnl).it_mp.dom().contains(iommu_table),
        final(krnl).it_mp.spec_index(iommu_table).locking_thread() == old(krnl).it_mp.spec_index(iommu_table).locking_thread(),
        final(krnl).it_mp.spec_index(iommu_table).being_killed() == old(krnl).it_mp.spec_index(iommu_table).being_killed(),
        final(krnl).it_mp.spec_index(iommu_table).view().mapping_4k() == old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().remove(spec_index2va(indices)),
        final(krnl).it_mp.spec_index(iommu_table).view().mapping_2m() == old(krnl).it_mp.spec_index(iommu_table).view().mapping_2m(),
        final(krnl).it_mp.spec_index(iommu_table).view().mapping_1g() == old(krnl).it_mp.spec_index(iommu_table).view().mapping_1g(),
        final(krnl).it_mp.spec_index(iommu_table).view().kernel_l4_end == old(krnl).it_mp.spec_index(iommu_table).view().kernel_l4_end,
{
    let iova = index2va(indices);
    proof {
        iommu_table_perms_wf_map(krnl.it_mp);
        iommu_table_perms_wf_at(krnl.it_mp, iommu_table);
        iommu_table_perms_wf_kernel_l4_end_at(krnl.it_mp, iommu_table);
    }
    let it = krnl.it_mp.borrow_typed(iommu_table, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), iommu_table_perm);
    assert(it.spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some) by { reveal(PageTable::wf_mapping_4k); };
    let l4 = it.get_entry_l4(indices.0).unwrap();
    let l3 = it.get_entry_l3(indices.0, indices.1, &l4).unwrap();
    let l2 = it.get_entry_l2(indices.0, indices.1, indices.2, &l3).unwrap();
    let page_ptr = it.get_entry_l1(indices.0, indices.1, indices.2, indices.3, &l2).unwrap().addr;
    let page_index = page_ptr2page_index(page_ptr);
    proof { assert(krnl.pg_arr.lock_id_by_index(page_index).major == MAPPED_PAGE_LOCK_MAJOR) by { page_iommu_table_wf_table_at(krnl.ctn_mp, krnl.prc_mp, krnl.it_mp, krnl.pg_arr, iommu_table, iova); }; }
    let Tracked(page_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));
    proof { page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, page_index); }
    let page = krnl.pg_arr.borrow_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(&page_perm));
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
    if page.ref_count > 1 || page.is_io_page {
        remove_iommu_4k_mapping_without_free(krnl, iommu_table, indices, page_ptr, Tracked(&mut *lctx), iommu_table_perm, Tracked(&page_perm));
        krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_perm));
    } else {
        let owner = page.owning_container;
        proof { assert(krnl.ctn_mp.dom().contains(owner)) by { container_page_owner_backward_at(krnl.ctn_mp, krnl.pg_arr, page_index); }; container_perms_wf_at(krnl.ctn_mp, owner); }
        let owner_ro = krnl.ctn_mp.borrow_rodata(owner).borrow();
        let depth = owner_ro.depth;
        let allocator_ptr = owner_ro.allocator_ptr_4k;
        proof { thread_perms_wf_map(krnl.thr_mp); thread_perms_wf_at(krnl.thr_mp, thread_ptr); }
        let thread = krnl.thr_mp.borrow_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), thread_perm);
        let thread_depth = thread.container_depth;
        proof { prove_unmapped_iommu_4k_page_owner_position_in_thread_container_chain(krnl, iommu_table, iova, page_ptr, thread_ptr, owner, depth, thread_depth); }
        proof { assert(krnl.allc_4k_mp.dom().contains(allocator_ptr) && lctx.page_lock_map().dom().contains(page_index)) by { container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, owner); }; page_array_wf_at(krnl.pg_arr, page_index); }
        let Tracked(cache_perm) = krnl.wlock_allocator_cache_4k(allocator_ptr, cpu_id, Tracked(&mut *lctx));
        let cache = krnl.allc_4k_mp.borrow_cache_typed(allocator_ptr, cpu_id, Ghost(lctx.allocator_cache_4k_lock_map()), Tracked(&*lctx), Tracked(&cache_perm));
        if cache.linked_list.len() == ALLOCATOR_MAX_WATERMARK {
            let Tracked(pool_perm) = krnl.wlock_allocator_global_pool_4k(allocator_ptr, Tracked(&mut *lctx));
            proof { assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; }; }
            proof { assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; }; }
            proof { kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl); }
            drain_4k_cache_batch(krnl, allocator_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&cache_perm), Tracked(&pool_perm));
            krnl.wunlock_allocator_global_pool_4k(allocator_ptr, Tracked(&mut *lctx), Tracked(pool_perm));
            proof {
                kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl);
                krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
            }
        }
        assert(krnl.ctn_mp.dom().contains(owner) && krnl.ctn_mp.spec_index(owner).view_rodata().view().depth == depth
            && krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr) by { container_page_owner_backward_at(krnl.ctn_mp, krnl.pg_arr, page_index); };
        let mut counter = if depth == thread_depth { *direct } else { indirect[depth] };
        remove_last_iommu_4k_mapping_to_allocator(krnl, iommu_table, indices, page_ptr, thread_ptr, owner, depth, allocator_ptr, cpu_id, &mut counter, Tracked(&mut *lctx), iommu_table_perm, Tracked(&page_perm), thread_perm, Tracked(&cache_perm));
        if depth == thread_depth { *direct = counter; } else { indirect[depth] = counter; }
        krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_perm));
        krnl.wunlock_allocator_cache_4k(allocator_ptr, cpu_id, Tracked(&mut *lctx), Tracked(cache_perm));
        proof { assert(lctx.allocator_cache_4k_lock_map() == old(lctx).allocator_cache_4k_lock_map()); assert(lctx.allocator_global_pool_4k_lock_map() == old(lctx).allocator_global_pool_4k_lock_map()); }
    }
    proof {
        assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
            map_insert_overwrite_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: old_page_lock_id, mode: TypedLockMode::Write }, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
            map_insert_remove_absent_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
        };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl);
        krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
    }
}
}
