use vstd::prelude::*;
use crate::*;
use super::unmap_4k_remove::remove_4k_mapping_without_free;
use super::unmap_4k_reclaim::remove_last_4k_mapping_to_allocator;

verus! {
#[verifier::spinoff_prover]
proof fn prove_unmapped_4k_page_owner_position_in_thread_container_chain(
    krnl: &KernelK, pagetable: RwLockPageTableRoot, va: VAddr, page_ptr: PagePtr, thread_ptr: RwLockThreadPtr,
    owner: RwLockContainerPtr, depth: usize, thread_depth: usize,
)
    requires
        krnl.inv(),
        krnl.pt_mp.dom().contains(pagetable),
        krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va),
        krnl.pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).addr
            == page_ptr,
        page_ptr_valid(page_ptr),
        krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view()
            .owning_container == owner,
        krnl.ctn_mp.dom().contains(owner),
        krnl.ctn_mp.spec_index(owner).view_rodata().view().depth == depth,
        krnl.thr_mp.dom().contains(thread_ptr),
        krnl.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable,
        krnl.thr_mp.spec_index(thread_ptr).view().container_depth == thread_depth,
    ensures
        depth <= thread_depth,
        thread_depth <= MAX_CONTAINER_TREE_DEPTH,
        if depth == thread_depth {
            owner == krnl.thr_mp.spec_index(thread_ptr).view().owning_container
        } else {
            krnl.thr_mp.spec_index(thread_ptr).view().upper_container_seq.view()
                .spec_index(depth as int) == owner
        },
{
    let page_index = page_ptr2page_index(page_ptr);
    let proc_ptr = krnl.pt_mp.spec_index(pagetable).view().proc_ptr;
    let thread_proc = krnl.thr_mp.spec_index(thread_ptr).view().owning_proc;
    let thread_owner = krnl.thr_mp.spec_index(thread_ptr).view().owning_container;
    assert(index_valid(NUM_PAGES, page_index)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(
        krnl.pg_arr.spec_index(page_index).view().view().state == PageState::Mapped4k
        && krnl.pg_arr.spec_index(page_index).view().view()
            .mappings().contains((pagetable, va))
        && krnl.pt_mp.spec_index(pagetable).view().mapping_4k()
            .spec_index(va).owning_container@ == owner
    ) by {
        reveal(mapped_4k_page_pagetable_wf);
    };
    assert(
        krnl.prc_mp.dom().contains(proc_ptr)
        && {
            ||| krnl.prc_mp.spec_index(proc_ptr)
                .view_rodata().view().owning_container == owner
            ||| krnl.ctn_mp.spec_index(owner).view_ghost().subtree_set.view()
                .contains(
                    krnl.prc_mp.spec_index(proc_ptr)
                        .view_rodata().view().owning_container,
                )
        }
    ) by {
        reveal(container_process_page_pagetable_wf);
    };
    assert(
        krnl.prc_mp.dom().contains(thread_proc)
        && !krnl.prc_mp.spec_index(thread_proc).view().zombie
        && krnl.prc_mp.spec_index(thread_proc).view().pagetable == pagetable
        && krnl.prc_mp.spec_index(thread_proc)
            .view_rodata().view().owning_container == thread_owner
    ) by {
        reveal(process_thread_wf);
    };
    assert(proc_ptr == thread_proc) by { reveal(process_pagetable_match); };
    assert(
        owner == thread_owner
        || krnl.ctn_mp.spec_index(owner).view_ghost().subtree_set.view()
            .contains(thread_owner)
    );
    assert(
        krnl.ctn_mp.dom().contains(thread_owner)
        && krnl.ctn_mp.spec_index(thread_owner)
            .view_ghost().owned_threads.view().contains(thread_ptr)
        && krnl.thr_mp.spec_index(thread_ptr).view().upper_container_seq
            == krnl.ctn_mp.spec_index(thread_owner).view_ghost().uppertree_seq
        && thread_depth == krnl.ctn_mp.spec_index(thread_owner)
            .view_rodata().view().depth
    ) by {
        reveal(container_thread_wf);
    };
    assert(
        krnl.thr_mp.spec_index(thread_ptr).view().upper_container_seq.view().len()
            == thread_depth
        && thread_depth <= MAX_CONTAINER_TREE_DEPTH
    ) by {
        reveal(container_perms_wf);
        reveal(container_tree_fields_wf);
    };
    if owner == thread_owner {
    } else {
        assert(
            krnl.ctn_mp.spec_index(thread_owner)
                .view_ghost().uppertree_seq.view().len() > depth
            && krnl.ctn_mp.spec_index(thread_owner)
                .view_ghost().uppertree_seq.view().spec_index(depth as int)
                == owner
        ) by {
            reveal(container_subtree_set_wf);
        };
        assert(
            krnl.thr_mp.spec_index(thread_ptr).view().upper_container_seq.view()
                .spec_index(depth as int) == owner
        );
    }
}

pub fn reclaim_unmapped_4k_page(krnl: &mut KernelK, pagetable: RwLockPageTableRoot, va: VAddr, thread_ptr: RwLockThreadPtr, cpu_id: CpuId, indirect: &mut [usize; MAX_CONTAINER_TREE_DEPTH], direct: &mut usize, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, pagetable_perm: Tracked<&LockPerm>, thread_perm: Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable,
        *old(direct) == old(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
        forall|depth: int| #![trigger old(indirect)[depth]] 0 <= depth < old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth ==> old(indirect)[depth] == old(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(depth),
        old(krnl).pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(va).0,
        old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va),
        !old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).present,
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pagetable, old(krnl).pt_mp.spec_index(pagetable).view()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
    ensures
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        final(steps).steps == old(steps).steps,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { direct_free_quota_pending_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k, indirect_free_quota_pending_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        *final(direct) == final(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
        forall|depth: int| #![trigger final(indirect)[depth]] 0 <= depth < final(krnl).thr_mp.spec_index(thread_ptr).view().container_depth ==> final(indirect)[depth] == final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(depth),
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().remove(va),
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_2m() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_2m(),
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_1g() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_1g(),
        final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end,
        pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pagetable, final(krnl).pt_mp.spec_index(pagetable).view()),
{
    let indices = va2index(va);
    proof {
        pagetable_perms_wf_at(krnl.pt_mp, pagetable);
        assert(spec_index2va(indices) == va) by {
            spec_va_4k_index_roundtrip_at(
                va, indices.0, indices.1, indices.2, indices.3,
            );
        };
    }
    let pt = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), pagetable_perm);
    assert(pt.spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some) by { reveal(PageTable::wf_mapping_4k); };
    let l4 = pt.get_entry_l4(indices.0).unwrap();
    let l3 = pt.get_entry_l3(indices.0, indices.1, &l4).unwrap();
    let l2 = pt.get_entry_l2(indices.0, indices.1, indices.2, &l3).unwrap();
    let page_ptr = pt.get_entry_l1(indices.0, indices.1, indices.2, indices.3, &l2).unwrap().addr;
    assert(page_ptr_valid(page_ptr)) by { reveal(mapped_4k_page_pagetable_wf); };
    let page_index = page_ptr2page_index(page_ptr);
    proof {
        assert(index_valid(NUM_PAGES, page_index)) by { page_ptr_valid_imply_page_index_valid(); };
        page_array_wf_at(krnl.pg_arr, page_index);
        assert(
            krnl.pg_arr.lock_id_by_index(page_index).major
                == MAPPED_PAGE_LOCK_MAJOR
            && lctx.lock_id_acyclic(
                krnl.pg_arr.lock_id_by_index(page_index),
            )
        ) by {
            reveal(mapped_4k_page_pagetable_wf);
        };
    }
    let Tracked(page_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));
    proof { page_array_wf_at(krnl.pg_arr, page_index); }
    let page = krnl.pg_arr.borrow_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(&page_perm));
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
    if page.ref_count > 1 || page.is_io_page {
        remove_4k_mapping_without_free(krnl, pagetable, va, page_ptr, Tracked(&mut *lctx), pagetable_perm, Tracked(&page_perm));
        krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_perm));
    } else {
        let owner = page.owning_container;
        proof {
            assert(krnl.ctn_mp.dom().contains(owner)) by { reveal(container_page_owner_wf); };
            container_perms_wf_at(krnl.ctn_mp, owner);
        }
        let owner_ro = krnl.ctn_mp.borrow_rodata(owner).borrow();
        let depth = owner_ro.depth;
        let allocator_ptr = owner_ro.allocator_ptr_4k;
        proof { thread_perms_wf_at(krnl.thr_mp, thread_ptr); }
        let thread = krnl.thr_mp.borrow_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), thread_perm);
        let thread_depth = thread.container_depth;
        proof {
            prove_unmapped_4k_page_owner_position_in_thread_container_chain(
                krnl, pagetable, va, page_ptr, thread_ptr, owner, depth, thread_depth,
            );
        }
        assert(lctx.allocator_cache_4k_lock_map().dom().is_empty() && lctx.allocator_global_pool_4k_lock_map().dom().is_empty() && lctx.allocator_quota_4k_lock_map().dom().is_empty()) by { reveal(LocalContext::holds_no_allocator_locks); };
        proof {
            assert(krnl.allc_4k_mp.dom().contains(allocator_ptr)) by { reveal(container_allocator_wf); };
            allocator_perms_wf_at(krnl.allc_4k_mp, allocator_ptr);
            page_array_wf_at(krnl.pg_arr, page_index);
            assert(
                krnl.allc_4k_mp.spec_index(allocator_ptr).wf()
                && lctx.held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR)
            );
        }
        let Tracked(cache_perm) = krnl.wlock_allocator_cache_4k(allocator_ptr, cpu_id, Tracked(&mut *lctx));
        let cache = krnl.allc_4k_mp.borrow_cache_typed(allocator_ptr, cpu_id, Ghost(lctx.allocator_cache_4k_lock_map()), Tracked(&*lctx), Tracked(&cache_perm));
        if cache.linked_list.len() == ALLOCATOR_MAX_WATERMARK {
            let Tracked(pool_perm) = krnl.wlock_allocator_global_pool_4k(allocator_ptr, Tracked(&mut *lctx));
            drain_4k_cache_batch(krnl, allocator_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&cache_perm), Tracked(&pool_perm));
            krnl.wunlock_allocator_global_pool_4k(allocator_ptr, Tracked(&mut *lctx), Tracked(pool_perm));
            proof { krnl.kernel_step_boundary(&mut *lctx, &mut *steps); }
        }
        assert(krnl.ctn_mp.dom().contains(owner) && krnl.ctn_mp.spec_index(owner).view_rodata().view().depth == depth && krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr) by { reveal(container_page_owner_wf); reveal(container_thread_wf); reveal(container_uppertree_seq_wf); };
        let mut counter = if depth == thread_depth { *direct } else { indirect[depth] };
        remove_last_4k_mapping_to_allocator(krnl, pagetable, va, page_ptr, thread_ptr, owner, depth, allocator_ptr, cpu_id, &mut counter, Tracked(&mut *lctx), pagetable_perm, Tracked(&page_perm), thread_perm, Tracked(&cache_perm));
        if depth == thread_depth { *direct = counter; } else { indirect[depth] = counter; }
        krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_perm));
        krnl.wunlock_allocator_cache_4k(allocator_ptr, cpu_id, Tracked(&mut *lctx), Tracked(cache_perm));
        proof {
            assert(lctx.allocator_cache_4k_lock_map() == old(lctx).allocator_cache_4k_lock_map()) by { map_insert_remove_absent_lemma(old(lctx).allocator_cache_4k_lock_map(), (allocator_ptr, cpu_id), TypedHeldLock { lock_id: krnl.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.lock_id_by_index(cpu_id), mode: TypedLockMode::Write }); };
            assert(lctx.allocator_global_pool_4k_lock_map() == old(lctx).allocator_global_pool_4k_lock_map()) by { map_insert_remove_absent_lemma(old(lctx).allocator_global_pool_4k_lock_map(), allocator_ptr, TypedHeldLock { lock_id: krnl.allc_4k_mp.spec_index(allocator_ptr).global_pool.lock_id(), mode: TypedLockMode::Write }); };
        }
    }
    proof {
        assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
            map_insert_overwrite_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: old_page_lock_id, mode: TypedLockMode::Write }, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
            map_insert_remove_absent_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
        };
        assert(lctx.held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR)) by { broadcast use held_lock_major_lt_preserved_for_typed_maps_unchanged; };
        assert(lctx.holds_no_allocator_locks(PageSize::SZ4k)) by { reveal(LocalContext::holds_no_allocator_locks); };
        krnl.kernel_step_boundary(&mut *lctx, &mut *steps);
    }
}
}
