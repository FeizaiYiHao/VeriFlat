use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::unmap_iommu_4k_remove_eof::*;

verus! {
/// Unmaps one hidden 4K leaf of a write-locked IOMMU table whose page keeps another mapping or is an I/O page; the page
/// drops the IOMMU reverse entry and is not freed.
pub fn remove_iommu_4k_mapping_without_free(
    krnl: &mut KernelK, iommu_table: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index, L1Index), page_ptr: PagePtr, Tracked(lctx): Tracked<&mut LocalContext>,
    iommu_table_perm: Tracked<&LockPerm>, page_perm: Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).it_mp.dom().contains(iommu_table),
        pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va(indices)),
        !old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(spec_index2va(indices)).present,
        old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(spec_index2va(indices)).addr == page_ptr,
        page_ptr_valid(page_ptr),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count > 1 || old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().is_io_page,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        page_perm.view().state() is WriteLock,
        page_perm.view().thread_id() == old(lctx).thread_id(),
        page_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table, TypedLockMode::Write),
        iommu_table_perm.view().state() is WriteLock,
        iommu_table_perm.view().thread_id() == old(lctx).thread_id(),
        iommu_table_perm.view().lock_id() == old(krnl).it_mp.spec_index(iommu_table).locking_thread()->Write_lock_id,
        iommu_table_tlb_entries_present(old(krnl).iommu_tlb, old(krnl).irt.view(), old(krnl).it_mp, iommu_table),
    ensures
        final(krnl).inv(),
        iommu_table_tlb_entries_present(final(krnl).iommu_tlb, final(krnl).irt.view(), final(krnl).it_mp, iommu_table),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(page_ptr)), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write }),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { it_mp: final(krnl).it_mp, pg_arr: final(krnl).pg_arr, ..*old(krnl) }),
        final(krnl).it_mp.unchanged_except(&old(krnl).it_mp, iommu_table),
        final(krnl).it_mp.spec_index(iommu_table).locking_thread() == old(krnl).it_mp.spec_index(iommu_table).locking_thread(),
        final(krnl).it_mp.spec_index(iommu_table).being_killed() == old(krnl).it_mp.spec_index(iommu_table).being_killed(),
        final(krnl).it_mp.spec_index(iommu_table).view().mapping_4k() == old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().remove(spec_index2va(indices)),
        final(krnl).it_mp.spec_index(iommu_table).view().mapping_2m() == old(krnl).it_mp.spec_index(iommu_table).view().mapping_2m(),
        final(krnl).it_mp.spec_index(iommu_table).view().mapping_1g() == old(krnl).it_mp.spec_index(iommu_table).view().mapping_1g(),
        final(krnl).it_mp.spec_index(iommu_table).view().page_closure() == old(krnl).it_mp.spec_index(iommu_table).view().page_closure(),
        final(krnl).it_mp.spec_index(iommu_table).view().kernel_entries == old(krnl).it_mp.spec_index(iommu_table).view().kernel_entries,
        final(krnl).it_mp.spec_index(iommu_table).view().kernel_l4_end == old(krnl).it_mp.spec_index(iommu_table).view().kernel_l4_end,
        final(krnl).it_mp.spec_index(iommu_table).view().cr3 == old(krnl).it_mp.spec_index(iommu_table).view().cr3,
        final(krnl).it_mp.spec_index(iommu_table).view().proc_ptr == old(krnl).it_mp.spec_index(iommu_table).view().proc_ptr,
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(page_ptr)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count - 1,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().iommu_mappings()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().iommu_mappings().remove((iommu_table, spec_index2va(indices))),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state
            == if old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count > 1 { PageState::Mapped4k } else { PageState::Unavailable },
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread(),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
{
    let page_index = page_ptr2page_index(page_ptr);
    let iova = index2va(indices);
    proof {
        iommu_table_perms_wf_map(krnl.it_mp);
        iommu_table_perms_wf_at(krnl.it_mp, iommu_table);
        iommu_table_perms_wf_kernel_l4_end_at(krnl.it_mp, iommu_table);
    }
    let l1_ptr;
    {
        let it = krnl.it_mp.borrow_typed(iommu_table, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), iommu_table_perm);
        assert(it.spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some) by { reveal(PageTable::wf_mapping_4k); };
        let l4 = it.get_entry_l4(indices.0).unwrap();
        let l3 = it.get_entry_l3(indices.0, indices.1, &l4).unwrap();
        let l2 = it.get_entry_l2(indices.0, indices.1, indices.2, &l3).unwrap();
        l1_ptr = l2.addr;
    }
    assert(index_valid(NUM_PAGES, page_index) && krnl.pg_arr.inv() && krnl.pg_arr.spec_index(page_index).view().inv() && krnl.pg_arr.spec_index(page_index).view().view().state is Mapped4k
        && krnl.pg_arr.spec_index(page_index).view().view().iommu_mappings().contains((iommu_table, iova))) by {
        page_ptr_valid_imply_page_index_valid(); page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, page_index); page_iommu_table_wf_table_at(krnl.ctn_mp, krnl.prc_mp, krnl.it_mp, krnl.pg_arr, iommu_table, iova); page_ptr_roundtrip();
    };
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
    page_array_remove_4k_iommu_mapping_without_free(&mut krnl.pg_arr, page_index, iommu_table, iova, Tracked(&*lctx), page_perm);
    iommu_table_map_unmap_4k_kernel(&mut krnl.it_mp, iommu_table, indices, l1_ptr, Tracked(&mut *lctx), iommu_table_perm);
    proof { lctx.update_lock_id(KernelObjId::Page(page_index), old_page_lock_id, krnl.pg_arr.lock_id_by_index(page_index)); }

    proof {
        old(krnl).it_mp.typed_lock_map_aligned_write_at(old(lctx).iommu_table_lock_map(), old(lctx).thread_id(), iommu_table);
        assert(remove_iommu_4k_mapping_without_free_eof_transition_framing(*old(krnl), *krnl, iommu_table, spec_index2va(indices), page_ptr)) by { reveal(remove_iommu_4k_mapping_without_free_eof_transition_framing); };
        remove_iommu_4k_mapping_without_free_eof(*old(krnl), *krnl, iommu_table, spec_index2va(indices), page_ptr);
        assert(krnl.it_mp.spec_index(iommu_table).view().user_view(LockStateU::Unlocked).mapping_4k =~= old(krnl).it_mp.spec_index(iommu_table).view().user_view(LockStateU::Unlocked).mapping_4k);
        assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), krnl)) by {
            broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); kernel_pagetable_nonlock_fields_unchanged_for_equal(old(krnl).pt_mp, old(krnl).pt_lower.view(), krnl.pt_mp, krnl.pt_lower.view()); reveal(kernel_iommu_table_nonlock_fields_unchanged);
        };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
    }
}
}
