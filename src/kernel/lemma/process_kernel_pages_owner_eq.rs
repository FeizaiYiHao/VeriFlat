use vstd::prelude::*;
use crate::*;
use crate::kernel::*;
verus! {
/// Framing lemma for `process_kernel_pages_owner_wf`: every page that makes up a process keeps its state and owner,
/// every process keeps its container, and every page-table and IOMMU-table root keeps its process.
pub proof fn process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre: KernelK, post: KernelK)
    requires
        pre.memory_management_inv(),
        forall|p_i: PageIndex|
            #![trigger post.pg_arr.spec_index(p_i).view().view().state]
            index_valid(NUM_PAGES, p_i) && (page_state_is_process_kernel_page(pre.pg_arr.spec_index(p_i).view().view().state) || page_state_is_process_kernel_page(post.pg_arr.spec_index(p_i).view().view().state))
                ==> post.pg_arr.spec_index(p_i).view().view().state == pre.pg_arr.spec_index(p_i).view().view().state && post.pg_arr.spec_index(p_i).view().view().owning_container == pre.pg_arr.spec_index(p_i).view().view().owning_container,
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p).view_rodata()] pre.prc_mp.dom().contains(p) ==> post.prc_mp.spec_index(p).view_rodata().view().owning_container == pre.prc_mp.spec_index(p).view_rodata().view().owning_container,
        forall|pt: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(pt).view()] pre.pt_mp.dom().contains(pt) ==> post.pt_mp.spec_index(pt).view().proc_ptr == pre.pt_mp.spec_index(pt).view().proc_ptr,
        forall|it: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(it).view()] pre.it_mp.dom().contains(it) ==> post.it_mp.spec_index(it).view().proc_ptr == pre.it_mp.spec_index(it).view().proc_ptr,
    ensures
        process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp),
{ reveal(process_kernel_pages_owner_wf); reveal(process_pages_wf); reveal(pagetable_pages_wf); reveal(process_pagetable_match); reveal(process_iommu_table_match); }
}
