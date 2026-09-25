use vstd::prelude::*;
use crate::*;

verus! {
pub fn clear_4k_mapping_present(krnl: &mut KernelK, pagetable: RwLockPageTableRoot, va: VAddr, Tracked(lctx): Tracked<&mut LocalContext>, pagetable_perm: Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(va).0,
        old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va),
        old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).present,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        kernel_k_to_nonlock_kernel_u(*final(krnl)) != kernel_k_to_nonlock_kernel_u(*old(krnl)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).lock_id_set() == old(lctx).lock_id_set(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, ..*old(krnl) }),
        final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, pagetable),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().insert(va, MapEntry { present: false, ..old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va) }),
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_2m() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_2m(),
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_1g() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_1g(),
        final(krnl).pt_mp.spec_index(pagetable).view().page_closure() == old(krnl).pt_mp.spec_index(pagetable).view().page_closure(),
        final(krnl).pt_mp.spec_index(pagetable).view().kernel_entries == old(krnl).pt_mp.spec_index(pagetable).view().kernel_entries,
        final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end,
        final(krnl).pt_mp.spec_index(pagetable).view().cr3 == old(krnl).pt_mp.spec_index(pagetable).view().cr3,
        final(krnl).pt_mp.spec_index(pagetable).view().pcid == old(krnl).pt_mp.spec_index(pagetable).view().pcid,
        final(krnl).pt_mp.spec_index(pagetable).view().proc_ptr == old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr,
{
    let indices = va2index(va);
    assert(krnl.pt_mp.perms_wf() && krnl.pt_mp.spec_index(pagetable).inv() && spec_index2va(indices) == va) by {
        reveal(pagetable_perms_wf);
        spec_va_4k_index_roundtrip_at(
            va, indices.0, indices.1, indices.2, indices.3,
        );
    };
    let l1_ptr;
    {
        let pt = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), pagetable_perm);
        assert(pt.spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some) by { reveal(PageTable::wf_mapping_4k); };
        let l4 = pt.get_entry_l4(indices.0).unwrap();
        let l3 = pt.get_entry_l3(indices.0, indices.1, &l4).unwrap();
        let l2 = pt.get_entry_l2(indices.0, indices.1, indices.2, &l3).unwrap();
        l1_ptr = l2.addr;
    }
    pagetable_map_clear_4k_present(&mut krnl.pt_mp, pagetable, indices, l1_ptr, Tracked(&mut *lctx), pagetable_perm);
    proof {
        assert(krnl.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
        assert(krnl.memory_management_inv()) by {
            assert(pagetable_pages_wf(krnl.pt_mp, krnl.pg_arr)) by { reveal(pagetable_pages_wf); };
            assert(page_pagetable_wf(krnl.pt_mp, krnl.pg_arr)) by { reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); };
            assert(container_process_page_pagetable_wf(krnl.ctn_mp, krnl.prc_mp, krnl.pt_mp, krnl.pg_arr)) by { reveal(container_process_page_pagetable_wf); reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); };
            assert(process_pagetable_match(krnl.prc_mp, krnl.pt_mp)) by { reveal(process_pagetable_match); };
        };
        assert(cpu_dirty_map_wf(krnl.ctn_mp, krnl.cpu_set_mp, krnl.prc_mp, krnl.cpu_arr, krnl.cpu_tlb, krnl.pt_mp, krnl.pcid_needflush)) by { reveal(cpu_dirty_map_contains_pagetable_pcid_match); };
        assert(tlb_wf_spec(krnl.cpu_tlb, krnl.pt_mp, krnl.cpu_arr, krnl.pcid_needflush)) by { reveal(tlb_wf_spec); };
        assert(kernel_k_to_nonlock_kernel_u(*old(krnl)).process_map.spec_index(old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr).pagetable.unwrap().mapping_4k.dom().contains(va)
            && !kernel_k_to_nonlock_kernel_u(*krnl).process_map.spec_index(old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr).pagetable.unwrap().mapping_4k.dom().contains(va)) by {
                reveal(kernel_k_to_nonlock_kernel_u);
                reveal(process_pagetable_match);
            };
    }
}
}
