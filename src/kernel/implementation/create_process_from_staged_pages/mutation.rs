use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub fn create_process_from_staged_pages(
    krnl: &mut KernelK, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr,
    parent_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid: Pcid, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(process_page_lock_perm): Tracked<&LockPerm>, Tracked(pagetable_page_lock_perm): Tracked<&LockPerm>,
    Tracked(l4_page_lock_perm): Tracked<&LockPerm>, Tracked(container_lock_perm): Tracked<&LockPerm>,
    Tracked(parent_lock_perm): Tracked<&LockPerm>, Tracked(staging_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(pcid_allocator_lock_perm): Tracked<&LockPerm>,
) -> (ret: (RwLockProcessPtr, RwLockPageTableRoot, Tracked<LockPerm>, Tracked<LockPerm>))
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        page_ptr_valid(process_page_ptr),
        page_ptr_valid(pagetable_page_ptr),
        page_ptr_valid(l4_page_ptr),
        index_valid(NUM_PAGES, page_ptr2page_index(process_page_ptr)),
        index_valid(NUM_PAGES, page_ptr2page_index(pagetable_page_ptr)),
        index_valid(NUM_PAGES, page_ptr2page_index(l4_page_ptr)),
        !old(krnl).prc_mp.dom().contains(process_page_ptr),
        !old(krnl).pt_mp.dom().contains(pagetable_page_ptr),
        process_page_ptr != pagetable_page_ptr,
        process_page_ptr != l4_page_ptr,
        pagetable_page_ptr != l4_page_ptr,
        old(krnl).ctn_mp.dom().contains(container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        container_lock_perm.state() is WriteLock,
        container_lock_perm.thread_id() == old(lctx).thread_id(),
        container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(parent_ptr),
        old(krnl).prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == container_ptr,
        old(krnl).prc_mp.spec_index(parent_ptr).view_rodata().view().depth < usize::MAX,
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), parent_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(parent_ptr).being_killed(),
        parent_lock_perm.state() is WriteLock,
        parent_lock_perm.thread_id() == old(lctx).thread_id(),
        parent_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(parent_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(staging_thread_ptr),
        old(krnl).thr_mp.spec_index(staging_thread_ptr).view().owning_container == container_ptr,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), staging_thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(staging_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(staging_thread_ptr).view().quota_4k >= 3,
        old(krnl).thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= set![process_page_ptr, pagetable_page_ptr, l4_page_ptr],
        old(krnl).thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_2m.view().is_empty(),
        old(krnl).thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_1g.view().is_empty(),
        old(krnl).thr_mp.spec_index(staging_thread_ptr).view().free_quota_pending_clean(),
        staging_thread_lock_perm.state() is WriteLock,
        staging_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        staging_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(staging_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).pcid_allc_mp.dom().contains(pcid_allocator_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator == pcid_allocator_ptr,
        typed_lock_map_contains_mode(old(lctx).pcid_allocator_lock_map(), pcid_allocator_ptr, TypedLockMode::Write),
        old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).view().pcid_is_free(pcid),
        pcid_allocator_lock_perm.state() is WriteLock,
        pcid_allocator_lock_perm.thread_id() == old(lctx).thread_id(),
        pcid_allocator_lock_perm.lock_id() == old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).locking_thread()->Write_lock_id,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().owning_container == container_ptr,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(process_page_ptr), TypedLockMode::Write),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().owning_container == container_ptr,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pagetable_page_ptr), TypedLockMode::Write),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().owning_container == container_ptr,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(l4_page_ptr), TypedLockMode::Write),
        process_page_lock_perm.state() is WriteLock,
        process_page_lock_perm.thread_id() == old(lctx).thread_id(),
        process_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().locking_thread()->Write_lock_id,
        pagetable_page_lock_perm.state() is WriteLock,
        pagetable_page_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().locking_thread()->Write_lock_id,
        l4_page_lock_perm.state() is WriteLock,
        l4_page_lock_perm.thread_id() == old(lctx).thread_id(),
        l4_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        kernel_u_create_process_changed(
            kernel_k_to_kernel_u(*old(krnl)),
            kernel_k_to_kernel_u(*final(krnl)),
            parent_ptr,
            process_page_ptr,
        ),
        kernel_k_to_kernel_u(*final(krnl))
            != kernel_k_to_kernel_u(*old(krnl)),
        ret.0 == process_page_ptr,
        ret.1 == pagetable_page_ptr,
        create_process_from_staged_pages_kernel_state_framing(
            *old(krnl),
            *final(krnl),
            process_page_ptr,
            pagetable_page_ptr,
            l4_page_ptr,
            parent_ptr,
            staging_thread_ptr,
            container_ptr,
            pcid_allocator_ptr,
            pcid,
        ),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), process_page_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), pagetable_page_ptr, TypedLockMode::Write),
        ret.2.view().state() is WriteLock,
        ret.2.view().thread_id() == final(lctx).thread_id(),
        ret.2.view().lock_id() == final(krnl).prc_mp.spec_index(process_page_ptr).locking_thread()->Write_lock_id,
        ret.3.view().state() is WriteLock,
        ret.3.view().thread_id() == final(lctx).thread_id(),
        ret.3.view().lock_id() == final(krnl).pt_mp.spec_index(pagetable_page_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), staging_thread_ptr, TypedLockMode::Write),
        staging_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(staging_thread_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        container_lock_perm.lock_id() == final(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), parent_ptr, TypedLockMode::Write),
        parent_lock_perm.lock_id() == final(krnl).prc_mp.spec_index(parent_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).pcid_allocator_lock_map(), pcid_allocator_ptr, TypedLockMode::Write),
        pcid_allocator_lock_perm.lock_id() == final(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(process_page_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pagetable_page_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(l4_page_ptr), TypedLockMode::Write),
        process_page_lock_perm.thread_id() == final(lctx).thread_id(),
        process_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().locking_thread()->Write_lock_id,
        pagetable_page_lock_perm.thread_id() == final(lctx).thread_id(),
        pagetable_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().locking_thread()->Write_lock_id,
        l4_page_lock_perm.thread_id() == final(lctx).thread_id(),
        l4_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().locking_thread()->Write_lock_id,
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(lctx).process_lock_map() == old(lctx).process_lock_map().insert(process_page_ptr, TypedHeldLock { lock_id: final(krnl).prc_mp.lock_id_by_key(process_page_ptr), mode: TypedLockMode::Write }),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map().insert(pagetable_page_ptr, TypedHeldLock { lock_id: final(krnl).pt_mp.lock_id_by_key(pagetable_page_ptr), mode: TypedLockMode::Write }),
        final(lctx).page_lock_map() == old(lctx).page_lock_map()
            .insert(page_ptr2page_index(l4_page_ptr), TypedHeldLock {
                lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(l4_page_ptr)), mode: TypedLockMode::Write,
            })
            .insert(page_ptr2page_index(pagetable_page_ptr), TypedHeldLock {
                lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(pagetable_page_ptr)), mode: TypedLockMode::Write,
            })
            .insert(page_ptr2page_index(process_page_ptr), TypedHeldLock {
                lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(process_page_ptr)), mode: TypedLockMode::Write,
            }),
        final(krnl).prc_mp.lock_id_by_key(process_page_ptr).major == PROCESS_LOCK_MAJOR,
        final(krnl).pt_mp.lock_id_by_key(pagetable_page_ptr).major == PAGE_TABLE_LOCK_MAJOR,
        final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(l4_page_ptr)).major < MAPPED_PAGE_LOCK_MAJOR,
        final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(pagetable_page_ptr)).major < MAPPED_PAGE_LOCK_MAJOR,
        final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(process_page_ptr)).major < MAPPED_PAGE_LOCK_MAJOR,
        final(lctx).lock_id_set() == old(lctx).lock_id_set()
            .remove((old(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(l4_page_ptr)), KernelObjId::Page(page_ptr2page_index(l4_page_ptr))))
            .insert((final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(l4_page_ptr)), KernelObjId::Page(page_ptr2page_index(l4_page_ptr))))
            .remove((old(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(pagetable_page_ptr)), KernelObjId::Page(page_ptr2page_index(pagetable_page_ptr))))
            .insert((final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(pagetable_page_ptr)), KernelObjId::Page(page_ptr2page_index(pagetable_page_ptr))))
            .insert((final(krnl).pt_mp.lock_id_by_key(pagetable_page_ptr), KernelObjId::PageTable(pagetable_page_ptr)))
            .remove((old(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(process_page_ptr)), KernelObjId::Page(page_ptr2page_index(process_page_ptr))))
            .insert((final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(process_page_ptr)), KernelObjId::Page(page_ptr2page_index(process_page_ptr))))
            .insert((final(krnl).prc_mp.lock_id_by_key(process_page_ptr), KernelObjId::Process(process_page_ptr))),
{
    let process_page_index = page_ptr2page_index(process_page_ptr);
    let pagetable_page_index = page_ptr2page_index(pagetable_page_ptr);
    let l4_page_index = page_ptr2page_index(l4_page_ptr);
    proof {
        assert(krnl.pg_arr.inv()) by { reveal(page_array_wf); };
        assert(krnl.prc_mp.view().spec_index(parent_ptr).is_init() && krnl.prc_mp.view().spec_index(parent_ptr).addr() == parent_ptr && krnl.prc_mp.spec_index(parent_ptr).inv()) by { process_perms_wf_at(krnl.prc_mp, parent_ptr); };
        assert(krnl.ctn_mp.view().spec_index(container_ptr).is_init() && krnl.ctn_mp.view().spec_index(container_ptr).addr() == container_ptr && krnl.ctn_mp.spec_index(container_ptr).inv()) by { container_perms_wf_at(krnl.ctn_mp, container_ptr); };
        assert(krnl.pcid_allc_mp.spec_index(pcid_allocator_ptr).inv()) by { pcid_allocator_perms_wf_at(krnl.pcid_allc_mp, pcid_allocator_ptr); };
        assert(krnl.thr_mp.view().spec_index(staging_thread_ptr).is_init() && krnl.thr_mp.view().spec_index(staging_thread_ptr).addr() == staging_thread_ptr && krnl.thr_mp.spec_index(staging_thread_ptr).inv()) by { thread_perms_wf_at(krnl.thr_mp, staging_thread_ptr); };
        assert(krnl.pg_arr.spec_index(l4_page_index).view().is_init() && krnl.pg_arr.spec_index(l4_page_index).view().view().inv() && krnl.pg_arr.spec_index(l4_page_index).view().view().addr == l4_page_ptr && krnl.pg_arr.spec_index(l4_page_index).view().view().perm_4k.view().is_some()) by {
            reveal(page_array_wf);
            page_ptr_roundtrip();
        };
        assert(
            krnl.pg_arr.spec_index(pagetable_page_index).view().is_init()
                && krnl.pg_arr.spec_index(pagetable_page_index).view().view().inv()
                && krnl.pg_arr.spec_index(pagetable_page_index).view().view().addr == pagetable_page_ptr
                && krnl.pg_arr.spec_index(pagetable_page_index).view().view().perm_4k.view().is_some()
        ) by {
            reveal(page_array_wf);
            page_ptr_roundtrip();
        };
        assert(
            krnl.pg_arr.spec_index(process_page_index).view().is_init()
                && krnl.pg_arr.spec_index(process_page_index).view().view().inv()
                && krnl.pg_arr.spec_index(process_page_index).view().view().addr == process_page_ptr
                && krnl.pg_arr.spec_index(process_page_index).view().view().perm_4k.view().is_some()
        ) by {
            reveal(page_array_wf);
            page_ptr_roundtrip();
        };
        assert(krnl.dflt_pt.view().wf()) by { reveal(KernelK::default_pagetable_wf); };
        assert(pei_valid(krnl.dflt_pt.view().kernel_l4_end)) by { reveal(PageTable::kernel_entries_wf); };
        assert(l4_page_index != pagetable_page_index
            && l4_page_index != process_page_index
            && pagetable_page_index != process_page_index) by {
            page_ptr2page_index_neq(l4_page_ptr, pagetable_page_ptr);
            page_ptr2page_index_neq(l4_page_ptr, process_page_ptr);
            page_ptr2page_index_neq(pagetable_page_ptr, process_page_ptr);
        };
    }
    let ghost parent_ancestors =
        krnl.prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view();
    let ghost ancestors = parent_ancestors.push(parent_ptr);
    let ghost parent_children =
        krnl.prc_mp.spec_index(parent_ptr).view().children.view();
    proof {
        let process_tree_dom =
            krnl.ctn_mp.spec_index(container_ptr).view().owned_processes.view();
        let root_process =
            krnl.ctn_mp.spec_index(container_ptr).view().root_process;
        assert(process_tree_dom.contains(parent_ptr)) by {
            reveal(container_process_wf);
        };
        assert(process_tree_wf(
            root_process,
            process_tree_dom,
            krnl.prc_mp,
        )) by {
            reveal(per_container_process_tree_wf);
        };
        assert(process_tree_dom.subset_of(krnl.prc_mp.dom())) by {
            reveal(container_process_wf);
        };
        assert(parent_ancestors.to_set().subset_of(process_tree_dom)) by {
            parent_ancestors.to_set_ensures();
            reveal(process_uppertree_seq_wf);
            reveal(Set::subset_of);
        };
        assert(ancestors.to_set().subset_of(process_tree_dom)) by {
            parent_ancestors.to_set_ensures();
            ancestors.to_set_ensures();
            reveal(Set::subset_of);
        };
        assert(ancestors.to_set().subset_of(krnl.prc_mp.dom())) by {
            reveal(Set::subset_of);
        };
        assert(!ancestors.to_set().contains(process_page_ptr)) by {
            reveal(Set::subset_of);
        };
        assert(parent_ancestors.no_duplicates()) by {
            process_perms_wf_at(krnl.prc_mp, parent_ptr);
        };
        assert(!parent_ancestors.contains(parent_ptr)) by {
            reveal(process_uppertree_seq_wf);
            reveal(process_perms_wf);
        };
        assert(ancestors.no_duplicates()) by {
            seq_push_unique_lemma::<RwLockProcessPtr>();
        };
        assert(!krnl.prc_mp.spec_index(parent_ptr)
            .view().children.view().contains(process_page_ptr)) by {
            reveal(process_children_parent_wf);
        };
        assert(parent_children.len() <= NUM_PAGES) by {
            assert(parent_children.no_duplicates()) by {
                process_perms_wf_at(krnl.prc_mp, parent_ptr);
            };
            reveal(process_children_parent_wf);
            lemma_kernel_object_ptr_seq_len_bounded(&*krnl, parent_children);
        };
        assert(parent_children.len() < usize::MAX) by {
            assert(NUM_PAGES < usize::MAX) by (compute);
        };
        assert(krnl.pcid_allc_mp.spec_index(pcid_allocator_ptr)
            .view().process_is_unallocated(process_page_ptr)) by {
            reveal(PcidAllocator::process_is_unallocated);
            reveal(process_pcid_allocator_wf);
        };
    }
    let ghost page_array_before_l4_retype = krnl.pg_arr;
    let ghost old_l4_page_lock_id = krnl.pg_arr.lock_id_by_index(l4_page_index);
    let l4_page_mut = krnl.pg_arr.borrow_mut_typed(l4_page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(l4_page_lock_perm));
    let Tracked(l4_page_perm) = retype_owned_4k_to_kernel_object(
        l4_page_mut,
        PageState::Allocated4k {
            state: Allocated4KPageState::PageTable {
                pagetable_root: pagetable_page_ptr,
            },
        },
    );
    proof {
        page_pagetable_wf_preserved_for_nonmapped_page_change(
            krnl.pt_mp,
            krnl.pt_mp,
            page_array_before_l4_retype,
            krnl.pg_arr,
            l4_page_index,
        );
    }
    proof { lctx.update_lock_id(KernelObjId::Page(l4_page_index), old_l4_page_lock_id, krnl.pg_arr.lock_id_by_index(l4_page_index)); }
    proof {
        assert(krnl.thr_mp.perms_wf()) by {
            reveal(thread_perms_wf);
        };
    }
    {
        let staging_thread_mut = krnl.thr_mp.borrow_mut_typed(staging_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(staging_thread_lock_perm));
        proof {
            lemma_set_ext_equal_three_distinct_len(
                staging_thread_mut.temp_alloc_cache_4k.view(),
                process_page_ptr,
                pagetable_page_ptr,
                l4_page_ptr,
            );
            assert(staging_thread_mut.temp_alloc_cache_4k.view().contains(l4_page_ptr)) by {
                broadcast use vstd::set::lemma_set_insert_same;
                broadcast use vstd::set::lemma_set_insert_different;
            };
        }
        staging_thread_mut.consume_staged_4k(l4_page_ptr);
    }
    let (l4_ptr, Tracked(mut l4_perm)) = page_perm_to_page_map(l4_page_ptr, Tracked(l4_page_perm));
    let default_pt = krnl.dflt_pt.borrow();
    default_pt.copy_kernel_entries_to_unpublished_root(l4_ptr, Tracked(&mut l4_perm));
    proof { assert(default_pt.kernel_entries.view().len() == default_pt.kernel_l4_end) by { reveal(PageTable::kernel_entries_wf); }; }
    let pagetable_value = PageTable::<PT_TYPE>::new(Some(pcid), Ghost(default_pt.kernel_entries.view()), l4_ptr, Tracked(l4_perm), default_pt.kernel_l4_end, process_page_ptr);

    proof {
        assert(typed_lock_map_contains_mode(
            lctx.page_lock_map(),
            pagetable_page_index,
            TypedLockMode::Write,
        )) by {
            reveal(typed_lock_map_contains_mode);
            broadcast use vstd::set::lemma_set_insert_different;
        };
    }
    let ghost page_array_before_pagetable_retype = krnl.pg_arr;
    let ghost old_pagetable_page_lock_id = krnl.pg_arr.lock_id_by_index(pagetable_page_index);
    let pagetable_page_mut = krnl.pg_arr.borrow_mut_typed(pagetable_page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(pagetable_page_lock_perm));
    let Tracked(pagetable_page_perm) = retype_owned_4k_to_kernel_object(
        pagetable_page_mut,
        PageState::Allocated4k {
            state: Allocated4KPageState::AsPageTableRoot,
        },
    );
    proof {
        page_pagetable_wf_preserved_for_nonmapped_page_change(
            krnl.pt_mp,
            krnl.pt_mp,
            page_array_before_pagetable_retype,
            krnl.pg_arr,
            pagetable_page_index,
        );
    }
    proof { lctx.update_lock_id(KernelObjId::Page(pagetable_page_index), old_pagetable_page_lock_id, krnl.pg_arr.lock_id_by_index(pagetable_page_index)); }
    {
        let staging_thread_mut = krnl.thr_mp.borrow_mut_typed(staging_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(staging_thread_lock_perm));
        proof {
            assert(staging_thread_mut.temp_alloc_cache_4k.view().contains(pagetable_page_ptr)) by {
                broadcast use vstd::set::lemma_set_insert_same;
                broadcast use vstd::set::lemma_set_insert_different;
                broadcast use vstd::set::lemma_set_remove_different;
            };
        }
        staging_thread_mut.consume_staged_4k(pagetable_page_ptr);
    }
    proof {
        assert(krnl.pt_mp.perms_wf()) by {
            reveal(pagetable_perms_wf);
        };
    }
    let Tracked(pagetable_lock_perm) = krnl.retype_page_to_pagetable_and_insert(pagetable_page_ptr, pagetable_value, Tracked(pagetable_page_perm), Tracked(&mut *lctx));

    let parent_depth = krnl.prc_mp.borrow_rodata(parent_ptr).borrow().depth;
    let cr3 = l4_ptr;
    let process_value = Process::new_fresh(process_page_ptr, pcid, pagetable_page_ptr, krnl.ctn_mp.borrow_rodata(container_ptr).borrow().depth, parent_depth + 1);
    let process_rodata = ReadOnlyNode::new(ProcessRO { owning_container: container_ptr, container_depth: krnl.ctn_mp.borrow_rodata(container_ptr).borrow().depth, parent: Some(parent_ptr), depth: parent_depth + 1, pagetable: pagetable_page_ptr, cr3, pcid }, Ghost(process_page_ptr));
    let process_ghost = ProcessGhost { uppertree_seq: Ghost(ancestors), subtree_set: Ghost(Set::empty()) };
    proof {
        assert(parent_ancestors.len() == parent_depth) by {
            process_perms_wf_at(krnl.prc_mp, parent_ptr);
        };
        assert(ancestors.len() == process_rodata.view().depth) by {
            seq_push_lemma::<RwLockProcessPtr>();
        };
    }
    proof {
        assert(typed_lock_map_contains_mode(
            lctx.page_lock_map(),
            process_page_index,
            TypedLockMode::Write,
        )) by {
            reveal(typed_lock_map_contains_mode);
            broadcast use vstd::set::lemma_set_insert_different;
        };
    }
    let ghost page_array_before_process_retype = krnl.pg_arr;
    let ghost old_process_page_lock_id = krnl.pg_arr.lock_id_by_index(process_page_index);
    let process_page_mut = krnl.pg_arr.borrow_mut_typed(process_page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(process_page_lock_perm));
    let Tracked(process_page_perm) = retype_owned_4k_to_kernel_object(
        process_page_mut,
        PageState::Allocated4k {
            state: Allocated4KPageState::AsProcess,
        },
    );
    proof {
        page_pagetable_wf_preserved_for_nonmapped_page_change(
            krnl.pt_mp,
            krnl.pt_mp,
            page_array_before_process_retype,
            krnl.pg_arr,
            process_page_index,
        );
    }
    proof { lctx.update_lock_id(KernelObjId::Page(process_page_index), old_process_page_lock_id, krnl.pg_arr.lock_id_by_index(process_page_index)); }
    {
        let staging_thread_mut = krnl.thr_mp.borrow_mut_typed(staging_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(staging_thread_lock_perm));
        proof {
            assert(staging_thread_mut.temp_alloc_cache_4k.view().contains(process_page_ptr)) by {
                broadcast use vstd::set::lemma_set_insert_same;
                broadcast use vstd::set::lemma_set_insert_different;
                broadcast use vstd::set::lemma_set_remove_different;
            };
        }
        staging_thread_mut.consume_staged_4k(process_page_ptr);
    }
    proof {
        assert(krnl.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_clean()) by {
            reveal(Thread::temp_alloc_clean);
            broadcast use vstd::set_lib::lemma_set_is_empty_len0;
        };
    }
    proof {
        assert(krnl.prc_mp.perms_wf()) by {
            reveal(process_perms_wf);
        };
    }
    let Tracked(process_lock_perm) = krnl.retype_page_to_process_and_insert(process_page_ptr, process_value, process_rodata, process_ghost, Tracked(process_page_perm), Tracked(&mut *lctx));
    let ghost process_map_after_mint = krnl.prc_mp;
    proof {
        assert(krnl.prc_mp.typed_lock_map_aligned(
            lctx.process_lock_map(),
            lctx.thread_id(),
        ));
    }

    let child_mut = krnl.prc_mp.borrow_mut_typed(process_page_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(&process_lock_perm));
    let (child_node_addr, child_node_perm) = child_mut.parent_linkedlist_node.take();
    proof {
        assert(process_perms_wf(krnl.prc_mp)) by {
            reveal(process_perms_wf);
            reveal(process_tree_fields_wf);
            reveal(LockedMap::unchanged_except);
        };
        assert(krnl.prc_mp.spec_index(parent_ptr)
            == process_map_after_mint.spec_index(parent_ptr)) by {
            reveal(LockedMap::unchanged_except);
        };
        assert(process_map_after_mint.spec_index(parent_ptr)
            == old(krnl).prc_mp.spec_index(parent_ptr));
        assert(krnl.prc_mp.typed_lock_map_aligned(
            lctx.process_lock_map(),
            lctx.thread_id(),
        )) by {
            reveal(LockedMap::typed_lock_map_aligned);
        };
        assert(typed_lock_map_contains_mode(
            lctx.process_lock_map(),
            parent_ptr,
            TypedLockMode::Write,
        )) by {
            reveal(typed_lock_map_contains_mode);
            broadcast use vstd::set::lemma_set_insert_different;
        };
    }
    let parent_mut = krnl.prc_mp.borrow_mut_typed(parent_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(parent_lock_perm));
    parent_mut.add_child(process_page_ptr, child_node_addr, child_node_perm);
    proof {
        assert(process_perms_wf(krnl.prc_mp)) by {
            reveal(process_perms_wf);
            reveal(process_tree_fields_wf);
            reveal(LockedMap::unchanged_except);
            seq_push_unique_lemma::<RwLockProcessPtr>();
        };
        assert(krnl.prc_mp.typed_lock_map_aligned(
            lctx.process_lock_map(),
            lctx.thread_id(),
        )) by {
            reveal(LockedMap::typed_lock_map_aligned);
        };
    }

    proof {
        assert(ancestors.to_set().subset_of(krnl.prc_mp.dom())) by { ancestors.to_set_ensures(); reveal(process_uppertree_seq_wf); };
        process_insert_child_into_ancestor_subtree_sets(
            &mut krnl.prc_mp,
            ancestors,
            process_page_ptr,
            lctx.process_lock_map(),
            lctx.thread_id(),
        );
    }
    let ghost container_map_before_process_publish = krnl.ctn_mp;
    proof {
        assert(krnl.ctn_mp.perms_wf()) by {
            reveal(container_perms_wf);
        };
        assert(krnl.pcid_allc_mp.perms_wf()) by {
            reveal(pcid_allocator_perms_wf);
        };
    }
    let container_mut = krnl.ctn_mp.borrow_mut_typed(container_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(container_lock_perm));
    container_mut.add_owned_process(process_page_ptr);
    let pcid_allocator_mut = krnl.pcid_allc_mp.borrow_mut_typed(pcid_allocator_ptr, Ghost(lctx.pcid_allocator_lock_map()), Tracked(&*lctx), Tracked(pcid_allocator_lock_perm));
    pcid_allocator_mut.alloc(pcid, process_page_ptr);

    proof {
        assert(create_process_from_staged_pages_kernel_state_framing(
            *old(krnl),
            *krnl,
            process_page_ptr,
            pagetable_page_ptr,
            l4_page_ptr,
            parent_ptr,
            staging_thread_ptr,
            container_ptr,
            pcid_allocator_ptr,
            pcid,
        )) by {
            ancestors.to_set_ensures();
            broadcast use vstd::set::lemma_set_insert_same;
            broadcast use vstd::set::lemma_set_insert_different;
            broadcast use vstd::set::lemma_set_remove_same;
            broadcast use vstd::set::lemma_set_remove_different;
        };
        create_process_from_staged_pages_eof(
            *old(krnl),
            *krnl,
            process_page_ptr,
            pagetable_page_ptr,
            l4_page_ptr,
            parent_ptr,
            staging_thread_ptr,
            container_ptr,
            pcid_allocator_ptr,
            pcid,
        );
    }
    (process_page_ptr, pagetable_page_ptr, Tracked(process_lock_perm), Tracked(pagetable_lock_perm))
}


}
