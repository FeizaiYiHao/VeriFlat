use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::unmap_iommu_4k_present_eof::*;

verus! {
/// Disables R/W of one 4K leaf under the table write lock, retaining its mapping for stale IOTLB entries until flush.
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
        final(krnl).it_mp.spec_index(iommu_table).view().spec_resolve_mapping_4k_l1(indices.0, indices.1, indices.2, indices.3) is Some,
        !final(krnl).it_mp.spec_index(iommu_table).view().spec_resolve_mapping_4k_l1(indices.0, indices.1, indices.2, indices.3)->0.perm.present,
        !final(krnl).it_mp.spec_index(iommu_table).view().spec_resolve_mapping_4k_l1(indices.0, indices.1, indices.2, indices.3)->0.perm.write,
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
        final(krnl).it_mp.spec_index(iommu_table).view().did == old(krnl).it_mp.spec_index(iommu_table).view().did,
        old(krnl).it_mp.spec_index(iommu_table).view().did is None ==> iommu_table_tlb_entries_present(final(krnl).iommu_tlb, final(krnl).irt.view(), final(krnl).it_mp, iommu_table),
{
    proof {
        iommu_table_perms_wf_map(krnl.it_mp);
        iommu_table_perms_wf_at(krnl.it_mp, iommu_table);
        iommu_table_perms_wf_kernel_l4_end_at(krnl.it_mp, iommu_table);
    }
    let l1_ptr;
    {
        let it = krnl.it_mp.borrow_typed(iommu_table, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), iommu_table_perm);
        assert(it.spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some) by { it.wf_mapping_4k_at(indices.0, indices.1, indices.2, indices.3); };
        let l4 = it.get_entry_l4(indices.0).unwrap();
        let l3 = it.get_entry_l3(indices.0, indices.1, &l4).unwrap();
        let l2 = it.get_entry_l2(indices.0, indices.1, indices.2, &l3).unwrap();
        l1_ptr = l2.addr;
    }
    iommu_table_map_clear_4k_present(&mut krnl.it_mp, iommu_table, indices, l1_ptr, Tracked(&mut *lctx), iommu_table_perm);
    proof {
        old(krnl).it_mp.typed_lock_map_aligned_write_at(old(lctx).iommu_table_lock_map(), old(lctx).thread_id(), iommu_table);
        let (i0, i1, i2, i3) = indices;
        let target_va = spec_index2va(indices);
        assert(spec_v2l4index(target_va) == i0 && spec_v2l3index(target_va) == i1 && spec_v2l2index(target_va) == i2 && spec_v2l1index(target_va) == i3) by (bit_vector)
            requires i0 < 512, i1 < 512, i2 < 512, i3 < 512, target_va == (i0 << 39 | i1 << 30 | i2 << 21 | i3 << 12);
        assert(clear_iommu_4k_mapping_present_eof_transition_framing(*old(krnl), *krnl, iommu_table, spec_index2va(indices))) by { reveal(clear_iommu_4k_mapping_present_eof_transition_framing); };
        clear_iommu_4k_mapping_present_eof(*old(krnl), *krnl, iommu_table, spec_index2va(indices));
    }
}
}
