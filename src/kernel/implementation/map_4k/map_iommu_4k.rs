use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::map_iommu_4k_eof::*;

verus! {
/// Maps the page of the 4K leaf `va` of the read-held page table `source_pagetable` into the write-held IOMMU table
/// `iommu_table_ptr` at `iova`, whose L1 page is already linked, and records `(iommu_table_ptr, iova)` on that page under the
/// page's own lock. Both tables belong to `process_ptr`, whose live thread `thread_ptr` keeps it from emptying its tables.
pub fn map_shared_page_into_iommu_4k(
    krnl: &mut KernelK, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, source_pagetable: RwLockPageTableRoot, iommu_table_ptr: RwLockPageTableRoot, va: VAddr, iova: VAddr,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>, Tracked(iommu_table_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(krnl).pg_arr.spec_index(held_page).view().view().orders_below_table_locks(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(krnl).prc_mp.dom().contains(process_ptr),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        !thread_is_dangling(old(krnl).thr_mp.spec_index(thread_ptr)),
        !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
        old(krnl).pt_mp.dom().contains(source_pagetable),
        old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == process_ptr,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Read),
        source_pagetable_lock_perm.state() is ReadLock,
        source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), source_pagetable_lock_perm.lock_id()),
        va_4k_valid(va),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).kernel_l4_end() <= spec_va2index(va).0,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().dom().contains(va),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().spec_index(va).present,
        old(krnl).it_mp.dom().contains(iommu_table_ptr),
        old(krnl).it_mp.spec_index(iommu_table_ptr).view().proc_ptr == process_ptr,
        typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write),
        iommu_table_lock_perm.state() is WriteLock,
        iommu_table_lock_perm.thread_id() == old(lctx).thread_id(),
        iommu_table_lock_perm.lock_id() == old(krnl).it_mp.spec_index(iommu_table_ptr).locking_thread()->Write_lock_id,
        va_4k_valid(iova),
        !old(krnl).it_mp.spec_index(iommu_table_ptr).view().mapping_4k().dom().contains(iova),
        old(krnl).it_mp.spec_index(iommu_table_ptr).view().spec_resolve_mapping_l2(spec_va2index(iova).0, spec_va2index(iova).1, spec_va2index(iova).2) is Some,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { it_mp: final(krnl).it_mp, pg_arr: final(krnl).pg_arr, ..*old(krnl) }),
        final(krnl).it_mp.unchanged_except(&old(krnl).it_mp, iommu_table_ptr),
        final(krnl).it_mp.spec_index(iommu_table_ptr).locking_thread() == old(krnl).it_mp.spec_index(iommu_table_ptr).locking_thread(),
        final(krnl).it_mp.spec_index(iommu_table_ptr).being_killed() == old(krnl).it_mp.spec_index(iommu_table_ptr).being_killed(),
        final(krnl).it_mp.spec_index(iommu_table_ptr).view().mapping_4k()
            == old(krnl).it_mp.spec_index(iommu_table_ptr).view().mapping_4k().insert(iova, pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().spec_index(va)),
        final(krnl).it_mp.spec_index(iommu_table_ptr).view().mapping_2m() == old(krnl).it_mp.spec_index(iommu_table_ptr).view().mapping_2m(),
        final(krnl).it_mp.spec_index(iommu_table_ptr).view().mapping_1g() == old(krnl).it_mp.spec_index(iommu_table_ptr).view().mapping_1g(),
        final(krnl).it_mp.spec_index(iommu_table_ptr).view().page_closure() == old(krnl).it_mp.spec_index(iommu_table_ptr).view().page_closure(),
        final(krnl).it_mp.spec_index(iommu_table_ptr).view().proc_ptr == old(krnl).it_mp.spec_index(iommu_table_ptr).view().proc_ptr,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger final(krnl).it_mp.spec_index(iommu_table_ptr).view().spec_resolve_mapping_l2(l4i, l3i, l2i)]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> final(krnl).it_mp.spec_index(iommu_table_ptr).view().spec_resolve_mapping_l2(l4i, l3i, l2i) == old(krnl).it_mp.spec_index(iommu_table_ptr).view().spec_resolve_mapping_l2(l4i, l3i, l2i),
        held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
{
    let source_indices = va2index(va);
    let indices = va2index(iova);
    proof {
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, source_pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable);
        iommu_table_perms_wf_map(krnl.it_mp); iommu_table_perms_wf_at(krnl.it_mp, iommu_table_ptr); iommu_table_perms_wf_kernel_l4_end_at(krnl.it_mp, iommu_table_ptr);
    }
    assert({
        &&& spec_index2va(source_indices) == va
        &&& spec_index2va(indices) == iova
        &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable).spec_resolve_mapping_4k_l1(source_indices.0, source_indices.1, source_indices.2, source_indices.3) is Some
    }) by {
        spec_va_4k_index_roundtrip_at(va, source_indices.0, source_indices.1, source_indices.2, source_indices.3);
        spec_va_4k_index_roundtrip_at(iova, indices.0, indices.1, indices.2, indices.3);
        pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable).wf_mapping_4k_at(source_indices.0, source_indices.1, source_indices.2, source_indices.3);
    };
    let source_entry;
    {
        let source = krnl.pt_mp.borrow_typed(source_pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(source_pagetable_lock_perm));
        let tracked source_lower = krnl.pt_lower.borrow().tracked_borrow(source_pagetable);
        source_entry = source.resolve_mapping_4k_l1(Tracked(source_lower), source_indices.0, source_indices.1, source_indices.2, source_indices.3).2.unwrap();
    }
    let page_ptr = source_entry.addr;
    let page_index = page_ptr2page_index(page_ptr);
    proof {
        assert({
            &&& index_valid(NUM_PAGES, page_index)
            &&& krnl.pg_arr.spec_index(page_index).view().view().state is Mapped4k
            &&& !lctx.page_lock_map().dom().contains(page_index)
            &&& krnl.pg_arr.lock_id_by_index(page_index).major == MAPPED_PAGE_LOCK_MAJOR
        }) by { page_ptr_valid_imply_page_index_valid(); mapped_4k_page_pagetable_wf_pagetable_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, source_pagetable, va); };
    }
    let target_l1_ptr;
    {
        let it = krnl.it_mp.borrow_typed(iommu_table_ptr, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), Tracked(iommu_table_lock_perm));
        let l4 = it.get_entry_l4(indices.0).unwrap();
        let l3 = it.get_entry_l3(indices.0, indices.1, &l4).unwrap();
        let l2 = it.get_entry_l2(indices.0, indices.1, indices.2, &l3).unwrap();
        target_l1_ptr = l2.addr;
    }
    let Tracked(page_lock_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));
    let ghost locked_k = *krnl;
    proof {
        assert(krnl.pg_arr.inv() && krnl.pg_arr.spec_index(page_index).view().inv()) by { page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, page_index); };
        assert(!krnl.pg_arr.spec_index(page_index).view().view().iommu_mappings().contains((iommu_table_ptr, iova))) by {
            page_iommu_table_wf_page_at(krnl.ctn_mp, krnl.prc_mp, krnl.it_mp, krnl.pg_arr, page_index, iommu_table_ptr, iova);
        };
        assert(krnl.pg_arr.spec_index(page_index).view().view().ref_count < usize::MAX) by { mapped_4k_page_ref_count_lt_usize_max(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, page_index); };
    }
    page_array_add_4k_iommu_mapping(&mut krnl.pg_arr, page_index, iommu_table_ptr, iova, Tracked(&*lctx), Tracked(&page_lock_perm));
    iommu_table_map_insert_4k(&mut krnl.it_mp, iommu_table_ptr, indices, target_l1_ptr, &source_entry, Tracked(&mut *lctx), Tracked(iommu_table_lock_perm));
    proof {
        locked_k.it_mp.typed_lock_map_aligned_write_at(lctx.iommu_table_lock_map(), lctx.thread_id(), iommu_table_ptr);
        assert(map_shared_page_into_iommu_4k_eof_transition_framing(locked_k, *krnl, page_index, source_pagetable, va, iommu_table_ptr, iova)) by {
            reveal(map_shared_page_into_iommu_4k_eof_transition_framing);
        };
        map_shared_page_into_iommu_4k_eof(locked_k, *krnl, page_index, process_ptr, thread_ptr, source_pagetable, va, iommu_table_ptr, iova);
    }
    krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_lock_perm));
    proof {
        assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
            map_insert_remove_absent_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
        };
    }
}
}
