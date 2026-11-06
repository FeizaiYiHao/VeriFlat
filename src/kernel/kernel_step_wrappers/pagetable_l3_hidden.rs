use vstd::prelude::*;
use crate::*;

verus! {
/// Hiding the resolving L3 entry `(l4i, l3i)` of the page table of a live process drops the windows under it from the table's window locks. The L2 page that entry links has the window `(l4i, l3i, 0)`, so the owning process's projected window locks lose it and the user projection changes.
pub proof fn kernel_pagetable_l3_windows_removed_implies_u_neq(pre: &KernelK, post: &KernelK, pagetable: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index)
    requires
        process_pagetable_wf(pre.prc_mp, pre.pt_mp),
        post.prc_mp == pre.prc_mp,
        pre.pt_mp.dom().contains(pagetable),
        post.pt_mp.dom().contains(pagetable),
        post.pt_mp.spec_index(pagetable).view().proc_ptr == pre.pt_mp.spec_index(pagetable).view().proc_ptr,
        !pre.prc_mp.spec_index(pre.pt_mp.spec_index(pagetable).view().proc_ptr).view().zombie,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).wf(),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).kernel_l4_end() <= l4i && pei_valid(l4i),
        pei_valid(l3i),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l3(l4i, l3i) is Some,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).lower.pagetable_window_locks == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.pagetable_window_locks.remove_keys(
            whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.pagetable_window_locks.dom().filter(|w: WindowVa| spec_v2l4index(w.va) == l4i && spec_v2l3index(w.va) == l3i)),
    ensures kernel_k_to_kernel_u(*pre) != kernel_k_to_kernel_u(*post),
{
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let p = old_c.spec_resolve_mapping_l3(l4i, l3i)->0.addr;
    let rev = old_c.higher.l2_rev_map.view().spec_index(p);
    let w = WindowVa { va: spec_index2va((l4i, l3i, 0usize, 0usize)) };
    let process = pre.pt_mp.spec_index(pagetable).view().proc_ptr;
    old_c.higher.wf_l4_at(l4i);
    old_c.l3_links_l2_wf_at(old_c.spec_resolve_mapping_l4(l4i)->0.addr, l3i);
    old_c.tables_reachable_wf_l2_at(p);
    old_c.higher.disjoint_l4_l3_implies_held_l3_addr_unique_at(l4i, l3i, rev.0, rev.1);
    old_c.wf_window_locks_l2_entry_at(p, 0usize);
    old_c.wf_window_locks_va_at(w);
    spec_va_2m_valid_index_roundtrip(w.va);
    spec_index2va_injective();
    process_pagetable_wf_pagetable_at(pre.prc_mp, pre.pt_mp, pagetable);
    kernel_process_projection_at(pre, process);
    kernel_process_projection_at(post, process);
}
} // verus!
