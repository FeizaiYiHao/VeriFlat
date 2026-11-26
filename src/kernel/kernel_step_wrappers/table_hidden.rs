use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal};
use crate::*;

verus! {
/// Hiding the user root entry `l4i` of the page table `root` drops every 4K, 2M, and 1G mapping and every window lock under `l4i`
/// from the projection of `root`, which its owning process shows unless it is a zombie; the table's lock mode and every other part
/// of the projection stay.
pub proof fn pagetable_l4_entry_hidden_implies_u_pagetable_l4_range_removed(pre: KernelK, post: KernelK, root: RwLockPageTableRoot, l4i: L4Index)
    requires
        process_pagetable_wf(pre.prc_mp, pre.pt_mp),
        pre.pt_mp.dom().contains(root),
        post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..pre }),
        post.pt_mp.unchanged_except(&pre.pt_mp, root),
        post.pt_mp.spec_index(root).locking_thread() == pre.pt_mp.spec_index(root).locking_thread(),
        post.pt_lower.view() == pre.pt_lower.view().insert(root, post.pt_lower.view().spec_index(root)),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).mapping_4k()
            == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).mapping_4k().remove_keys(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).mapping_4k().dom().filter(|va: VAddr| spec_v2l4index(va) == l4i)),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).mapping_2m()
            == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).mapping_2m().remove_keys(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).mapping_2m().dom().filter(|va: VAddr| spec_v2l4index(va) == l4i)),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).mapping_1g()
            == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).mapping_1g().remove_keys(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).mapping_1g().dom().filter(|va: VAddr| spec_v2l4index(va) == l4i)),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), root).lower.pagetable_window_locks == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.pagetable_window_locks.remove_keys(
            whole_pagetable(pre.pt_mp, pre.pt_lower.view(), root).lower.pagetable_window_locks.dom().filter(|w: WindowVa| spec_v2l4index(w.va) == l4i)),
        post.pt_mp.spec_index(root).view().higher.pci.mapping_counts() == pre.pt_mp.spec_index(root).view().higher.pci.mapping_counts(),
    ensures
        ({
            let a = kernel_k_to_kernel_u(pre);
            let prc_ptr = pre.pt_mp.spec_index(root).view().higher.proc_ptr;
            let table = pagetable_map_user_view(pre.pt_mp, pre.pt_lower.view()).spec_index(root);
            let hidden = PageTableU {
                mapping_4k: table.mapping_4k.remove_keys(table.mapping_4k.dom().filter(|va: VAddr| spec_v2l4index(va) == l4i)),
                mapping_2m: table.mapping_2m.remove_keys(table.mapping_2m.dom().filter(|va: VAddr| spec_v2l4index(va) == l4i)),
                mapping_1g: table.mapping_1g.remove_keys(table.mapping_1g.dom().filter(|va: VAddr| spec_v2l4index(va) == l4i)),
                pagetable_window_locks: table.pagetable_window_locks.remove_keys(table.pagetable_window_locks.dom().filter(|w: WindowVa| spec_v2l4index(w.va) == l4i)),
                ..table
            };
            &&& a.process_map.dom().contains(prc_ptr)
            &&& a.process_map[prc_ptr].pagetable == if a.process_map[prc_ptr].zombie { None } else { Some(table) }
            &&& kernel_k_to_kernel_u(post) == (KernelU {
                process_map: a.process_map.insert(prc_ptr, ProcessU { pagetable: if a.process_map[prc_ptr].zombie { None } else { Some(hidden) }, ..a.process_map[prc_ptr] }),
                ..a
            })
        }),
{
    let a = kernel_k_to_kernel_u(pre);
    let b = kernel_k_to_kernel_u(post);
    let prc_ptr = pre.pt_mp.spec_index(root).view().higher.proc_ptr;
    let table = pagetable_map_user_view(pre.pt_mp, pre.pt_lower.view()).spec_index(root);
    let hidden = PageTableU {
        mapping_4k: table.mapping_4k.remove_keys(table.mapping_4k.dom().filter(|va: VAddr| spec_v2l4index(va) == l4i)),
        mapping_2m: table.mapping_2m.remove_keys(table.mapping_2m.dom().filter(|va: VAddr| spec_v2l4index(va) == l4i)),
        mapping_1g: table.mapping_1g.remove_keys(table.mapping_1g.dom().filter(|va: VAddr| spec_v2l4index(va) == l4i)),
        pagetable_window_locks: table.pagetable_window_locks.remove_keys(table.pagetable_window_locks.dom().filter(|w: WindowVa| spec_v2l4index(w.va) == l4i)),
        ..table
    };
    let post_table = pagetable_map_user_view(post.pt_mp, post.pt_lower.view()).spec_index(root);
    kernel_k_to_kernel_u_implies_domains_and_scalars_from_k(&pre); kernel_k_to_kernel_u_implies_domains_and_scalars_from_k(&post);
    kernel_cpu_array_unchanged_implies_u_cpu_array(&pre, &post); kernel_container_maps_unchanged_implies_u_container_map(&pre, &post);
    kernel_thread_map_unchanged_implies_u_thread_map(&pre, &post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(&pre, &post);
    process_pagetable_wf_pagetable_at(pre.prc_mp, pre.pt_mp, root);
    kernel_process_projection_at(&pre, prc_ptr);
    assert(post_table == hidden) by {
        assert(post_table.mapping_4k =~= hidden.mapping_4k);
        assert(post_table.mapping_2m =~= hidden.mapping_2m);
        assert(post_table.mapping_1g =~= hidden.mapping_1g);
        assert(post_table.pagetable_window_locks =~= hidden.pagetable_window_locks);
    };
    assert_maps_equal!(b.process_map, a.process_map.insert(prc_ptr, ProcessU { pagetable: if a.process_map[prc_ptr].zombie { None } else { Some(hidden) }, ..a.process_map[prc_ptr] }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(&pre, p); kernel_process_projection_at(&post, p); process_pagetable_wf_process_at(pre.prc_mp, pre.pt_mp, p); }
    });
}

/// When no user root entry of the page table `root` below `l4i` resolves, the table its owning process shows, if any, has no
/// 4K, 2M or 1G mapping and no window lock whose L4 index is below `l4i`.
pub proof fn pagetable_user_roots_below_unresolved_implies_u_pagetable_keys_at_or_above(k: &KernelK, root: RwLockPageTableRoot, l4i: L4Index)
    requires
        k.inv(),
        k.pt_mp.dom().contains(root),
        forall|i4: L4Index| #![trigger whole_pagetable(k.pt_mp, k.pt_lower.view(), root).spec_resolve_mapping_l4(i4)]
            whole_pagetable(k.pt_mp, k.pt_lower.view(), root).kernel_l4_end() <= i4 && i4 < l4i
                ==> whole_pagetable(k.pt_mp, k.pt_lower.view(), root).spec_resolve_mapping_l4(i4) is None,
    ensures
        ({
            let u = kernel_k_to_kernel_u(*k);
            let prc_ptr = k.pt_mp.spec_index(root).view().higher.proc_ptr;
            let table = u.process_map[prc_ptr].pagetable->Some_0;
            u.process_map.dom().contains(prc_ptr) && u.process_map[prc_ptr].pagetable is Some ==> {
                &&& forall|va: VAddr| #![trigger table.mapping_4k.dom().contains(va)] table.mapping_4k.dom().contains(va) ==> l4i <= spec_v2l4index(va)
                &&& forall|va: VAddr| #![trigger table.mapping_2m.dom().contains(va)] table.mapping_2m.dom().contains(va) ==> l4i <= spec_v2l4index(va)
                &&& forall|va: VAddr| #![trigger table.mapping_1g.dom().contains(va)] table.mapping_1g.dom().contains(va) ==> l4i <= spec_v2l4index(va)
                &&& forall|w: WindowVa| #![trigger table.pagetable_window_locks.dom().contains(w)] table.pagetable_window_locks.dom().contains(w) ==> l4i <= spec_v2l4index(w.va)
            }
        }),
{
    k.default_pagetable_wf_at(root);
    pagetable_lower_wf_at(k.pt_mp, k.pt_lower.view(), root);
    process_pagetable_wf_pagetable_at(k.prc_mp, k.pt_mp, root);
    kernel_process_projection_at(k, k.pt_mp.spec_index(root).view().higher.proc_ptr);
    broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip, spec_va_1g_valid_index_roundtrip;
    reveal(WholePageTable::wf_mapping_4k); reveal(WholePageTable::wf_mapping_2m); reveal(PageTableHigher::wf_mapping_1g); reveal(WholePageTable::wf_window_locks);
}
}
