use vstd::prelude::*;
use crate::*;

verus! {
/// Clears the present bit of one 4K leaf of a write-locked IOMMU table. No attached function translates through a
/// write-locked table, so no IOTLB domain caches the leaf.
pub fn clear_iommu_4k_mapping_present(
    krnl: &mut KernelK, iommu_table: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index, L1Index), Tracked(lctx): Tracked<&mut LocalContext>,
    iommu_table_perm: Tracked<&LockPerm>,
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
        old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(spec_index2va(indices)).present,
        typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table, TypedLockMode::Write),
        iommu_table_perm.view().state() is WriteLock,
        iommu_table_perm.view().thread_id() == old(lctx).thread_id(),
        iommu_table_perm.view().lock_id() == old(krnl).it_mp.spec_index(iommu_table).locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { it_mp: final(krnl).it_mp, ..*old(krnl) }),
        final(krnl).it_mp.unchanged_except(&old(krnl).it_mp, iommu_table),
        final(krnl).it_mp.spec_index(iommu_table).locking_thread() == old(krnl).it_mp.spec_index(iommu_table).locking_thread(),
        final(krnl).it_mp.spec_index(iommu_table).being_killed() == old(krnl).it_mp.spec_index(iommu_table).being_killed(),
        final(krnl).it_mp.spec_index(iommu_table).view().mapping_4k() == old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().insert(spec_index2va(indices),
            MapEntry { present: false, ..old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(spec_index2va(indices)) }),
        final(krnl).it_mp.spec_index(iommu_table).view().mapping_2m() == old(krnl).it_mp.spec_index(iommu_table).view().mapping_2m(),
        final(krnl).it_mp.spec_index(iommu_table).view().mapping_1g() == old(krnl).it_mp.spec_index(iommu_table).view().mapping_1g(),
        final(krnl).it_mp.spec_index(iommu_table).view().page_closure() == old(krnl).it_mp.spec_index(iommu_table).view().page_closure(),
        final(krnl).it_mp.spec_index(iommu_table).view().kernel_entries == old(krnl).it_mp.spec_index(iommu_table).view().kernel_entries,
        final(krnl).it_mp.spec_index(iommu_table).view().kernel_l4_end == old(krnl).it_mp.spec_index(iommu_table).view().kernel_l4_end,
        final(krnl).it_mp.spec_index(iommu_table).view().cr3 == old(krnl).it_mp.spec_index(iommu_table).view().cr3,
        final(krnl).it_mp.spec_index(iommu_table).view().pcid == old(krnl).it_mp.spec_index(iommu_table).view().pcid,
        final(krnl).it_mp.spec_index(iommu_table).view().proc_ptr == old(krnl).it_mp.spec_index(iommu_table).view().proc_ptr,
{
    proof {
        iommu_table_perms_wf_at(krnl.it_mp, iommu_table);
        assert(krnl.it_mp.spec_index(iommu_table).view().kernel_l4_end == 0) by { reveal(PageTable::kernel_entries_wf); };
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
    iommu_table_map_clear_4k_present(&mut krnl.it_mp, iommu_table, indices, l1_ptr, Tracked(&mut *lctx), iommu_table_perm);
    proof {
        old(krnl).it_mp.typed_lock_map_aligned_write_at(old(lctx).iommu_table_lock_map(), old(lctx).thread_id(), iommu_table);
        assert(krnl.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
        assert(krnl.memory_management_inv()) by {
            assert(pagetable_pages_wf(krnl.it_mp, krnl.pg_arr)) by { reveal(pagetable_pages_wf); };
            assert(page_iommu_table_wf(krnl.ctn_mp, krnl.prc_mp, krnl.it_mp, krnl.pg_arr)) by { reveal(page_iommu_table_wf); };
            assert(process_iommu_table_match(krnl.prc_mp, krnl.it_mp)) by { reveal(process_iommu_table_match); };
            assert(pagetable_no_huge_leaf_wf(krnl.pt_mp, krnl.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
            assert(process_emptied_tables_wf(krnl.prc_mp, krnl.pt_mp, krnl.it_mp)) by { reveal(process_emptied_tables_wf); reveal(process_iommu_table_match); };
            assert(process_kernel_pages_owner_wf(krnl.pg_arr, krnl.prc_mp, krnl.pt_mp, krnl.it_mp)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(*old(krnl), *krnl); };
        };
        assert(iommu_root_table_process_wf(krnl.irt.view(), krnl.prc_mp, krnl.it_mp)) by { reveal(iommu_root_table_process_wf); };
        assert(iommu_tlb_wf_spec(krnl.iommu_tlb, krnl.irt.view(), krnl.prc_mp, krnl.it_mp)) by { reveal(iommu_tlb_wf_spec); reveal(iommu_root_table_process_wf); reveal(iommu_table_lock_wf); };
        assert(iommu_table_lock_wf(krnl.irt.view(), krnl.prc_mp, krnl.it_mp)) by { reveal(iommu_table_lock_wf); };
    }
}
}
