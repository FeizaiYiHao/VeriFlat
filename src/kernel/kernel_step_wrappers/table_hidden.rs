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
    ensures
        ({
            let a = kernel_k_to_kernel_u(pre);
            let prc_ptr = pre.pt_mp.spec_index(root).view().proc_ptr;
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
    let prc_ptr = pre.pt_mp.spec_index(root).view().proc_ptr;
    let table = pagetable_map_user_view(pre.pt_mp, pre.pt_lower.view()).spec_index(root);
    let hidden = PageTableU {
        mapping_4k: table.mapping_4k.remove_keys(table.mapping_4k.dom().filter(|va: VAddr| spec_v2l4index(va) == l4i)),
        mapping_2m: table.mapping_2m.remove_keys(table.mapping_2m.dom().filter(|va: VAddr| spec_v2l4index(va) == l4i)),
        mapping_1g: table.mapping_1g.remove_keys(table.mapping_1g.dom().filter(|va: VAddr| spec_v2l4index(va) == l4i)),
        pagetable_window_locks: table.pagetable_window_locks.remove_keys(table.pagetable_window_locks.dom().filter(|w: WindowVa| spec_v2l4index(w.va) == l4i)),
        ..table
    };
    let post_table = pagetable_map_user_view(post.pt_mp, post.pt_lower.view()).spec_index(root);
    kernel_u_domains_projection(&pre); kernel_u_domains_projection(&post);
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
}
