use vstd::prelude::*;
use crate::*;

verus! {
/// Closes `inv()` after `wlock_iommu_table`: the owner process is write-held and no root entry of its functions is
/// installed, so the table may become write-locked.
pub(super) proof fn wlock_iommu_table_eof(pre: KernelK, post: KernelK, pre_lctx: LocalContext, iommu_table_ptr: RwLockPageTableRoot)
    requires
        pre.inv(),
        pre.it_mp.dom().contains(iommu_table_ptr),
        typed_lock_map_contains_mode(pre_lctx.process_lock_map(), pre.it_mp.spec_index(iommu_table_ptr).view().proc_ptr, TypedLockMode::Write),
        forall|bus: usize, device: usize, function: usize| #![trigger pre.irt.view().spec_index_iommu_root(bus, device, function)]
            pci_bdf_valid(bus, device, function) && pre.irt.view().spec_index_owner(bus, device, function) == pre.it_mp.spec_index(iommu_table_ptr).view().proc_ptr
                ==> pre.irt.view().spec_index_iommu_root(bus, device, function) is None,
        typed_lock_maps_aligned(&pre, &pre_lctx),
        post == (KernelK { it_mp: post.it_mp, ..pre }),
        post.it_mp.perms_wf(),
        post.it_mp.unchanged_except(&pre.it_mp, iommu_table_ptr),
        post.it_mp.spec_index(iommu_table_ptr).inv(),
        post.it_mp.spec_index(iommu_table_ptr).view() == pre.it_mp.spec_index(iommu_table_ptr).view(),
        post.it_mp.spec_index(iommu_table_ptr).view_rodata() == pre.it_mp.spec_index(iommu_table_ptr).view_rodata(),
        post.it_mp.spec_index(iommu_table_ptr).view_ghost() == pre.it_mp.spec_index(iommu_table_ptr).view_ghost(),
        post.it_mp.spec_index(iommu_table_ptr).being_killed() == pre.it_mp.spec_index(iommu_table_ptr).being_killed(),
        post.it_mp.spec_index(iommu_table_ptr).killer_info() == pre.it_mp.spec_index(iommu_table_ptr).killer_info(),
        !pre.it_mp.spec_index(iommu_table_ptr).locked(),
        post.it_mp.spec_index(iommu_table_ptr).locking_thread() is Write,
        post.it_mp.spec_index(iommu_table_ptr).locking_thread()->Write_thread_id == pre_lctx.thread_id(),
    ensures
        post.inv(),
        post.it_mp.spec_index(iommu_table_ptr).view().leaves_present(),
{
    assert(post.it_mp.spec_index(iommu_table_ptr).view().leaves_present()) by { reveal(iommu_table_perms_wf); reveal(iommu_table_hidden_leaves_only_when_wlocked); };
    assert(iommu_table_perms_wf(post.it_mp)) by { reveal(iommu_table_perms_wf); reveal(iommu_table_hidden_leaves_only_when_wlocked); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(process_emptied_tables_wf); reveal(process_iommu_table_match); };
    assert(post.memory_management_inv()) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); reveal(iommu_table_pages_wf); reveal(process_iommu_table_match); reveal(page_iommu_table_wf); };
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf_spec); reveal(iommu_root_table_process_wf); };
    assert(iommu_table_lock_wf(post.irt.view(), post.prc_mp, post.it_mp)) by {
        reveal(iommu_table_lock_wf); reveal(process_iommu_table_match);
        pre.prc_mp.typed_lock_map_aligned_write_at(pre_lctx.process_lock_map(), pre_lctx.thread_id(), pre.it_mp.spec_index(iommu_table_ptr).view().proc_ptr);
    };
}

/// Closes `inv()` after `wunlock_iommu_table`: the released table's leaves are present.
pub(super) proof fn wunlock_iommu_table_eof(pre: KernelK, post: KernelK, iommu_table_ptr: RwLockPageTableRoot)
    requires
        pre.inv(),
        pre.it_mp.dom().contains(iommu_table_ptr),
        pre.it_mp.spec_index(iommu_table_ptr).view().leaves_present(),
        post == (KernelK { it_mp: post.it_mp, ..pre }),
        post.it_mp.perms_wf(),
        post.it_mp.unchanged_except(&pre.it_mp, iommu_table_ptr),
        wunlock_ensures(pre.it_mp.spec_index(iommu_table_ptr), post.it_mp.spec_index(iommu_table_ptr)),
    ensures
        post.inv(),
{
    assert(iommu_table_perms_wf(post.it_mp)) by { reveal(iommu_table_perms_wf); reveal(iommu_table_hidden_leaves_only_when_wlocked); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(process_emptied_tables_wf); reveal(process_iommu_table_match); };
    assert(post.memory_management_inv()) by {
        process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post);
        iommu_table_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); reveal(process_iommu_table_match); reveal(page_iommu_table_wf);
    };
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf_spec); reveal(iommu_root_table_process_wf); };
    assert(iommu_table_lock_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_table_lock_wf); };
}

/// Closes `inv()` after an IOMMU root-table write lock or unlock: only the root table's lock state moved.
pub(super) proof fn iommu_root_table_lock_op_eof(pre: KernelK, post: KernelK)
    requires
        pre.inv(),
        post == (KernelK { irt: post.irt, ..pre }),
        post.irt.inv(),
        post.irt.view() == pre.irt.view(),
    ensures
        post.inv(),
{
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
}
} // verus!
