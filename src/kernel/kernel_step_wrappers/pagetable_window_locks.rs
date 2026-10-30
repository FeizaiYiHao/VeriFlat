use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal};
use crate::*;

verus! {
/// Changing kernel-only state, the kernel-only fields of the thread `thread_ptr`, and the window locks of the page table
/// `pagetable` of the live process `process_ptr`, while every non-lock field and every lock mode stays, replaces only those
/// window locks in the projection.
pub proof fn kernel_pagetable_window_locks_changed_implies_u_window_locks_replaced(
    pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, pagetable: RwLockPageTableRoot, thread_ptr: RwLockThreadPtr,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        post.prc_mp.dom().contains(process_ptr),
        !post.prc_mp.spec_index(process_ptr).view().zombie,
        post.prc_mp.spec_index(process_ptr).view().pagetable == pagetable,
        *post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, pg_arr: post.pg_arr, thr_mp: post.thr_mp, allc_4k_mp: post.allc_4k_mp, ..*pre }),
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable),
        post.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread(),
        post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable)),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).locking_thread() == pre.thr_mp.spec_index(thread_ptr).locking_thread(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post),
        kernel_container_nonlock_fields_and_quotas_unchanged(pre, post),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let table = a.process_map[process_ptr].pagetable->Some_0;
            &&& a.process_map.dom().contains(process_ptr)
            &&& a.process_map[process_ptr].pagetable is Some
            &&& table.pagetable_window_locks == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.pagetable_window_locks
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                process_map: a.process_map.insert(process_ptr, ProcessU {
                    pagetable: Some(PageTableU { pagetable_window_locks: pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable).lower.pagetable_window_locks, ..table }),
                    ..a.process_map[process_ptr]
                }),
                ..a
            })
        }),
{
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    let windows = pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable).lower.pagetable_window_locks;
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    process_pagetable_match_process_at(post.prc_mp, post.pt_mp, process_ptr); kernel_process_projection_at(pre, process_ptr); kernel_process_projection_at(post, process_ptr);
    assert(post.irt.view().user_view() == pre.irt.view().user_view() && post.dflt_pt == pre.dflt_pt) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
    assert_maps_equal!(b.container_map, a.container_map, c => {
        if pre.ctn_mp.dom().contains(c) { kernel_container_projection_at(pre, c); kernel_container_projection_at(post, c); }
        reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
    });
    assert_maps_equal!(b.thread_map, a.thread_map, t => {
        if pre.thr_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); kernel_thread_projection_at(post, t); }
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
    });
    let table = a.process_map[process_ptr].pagetable->Some_0;
    assert_maps_equal!(b.process_map, a.process_map.insert(process_ptr, ProcessU { pagetable: Some(PageTableU { pagetable_window_locks: windows, ..table }), ..a.process_map[process_ptr] }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); kernel_process_projection_at(post, p); process_pagetable_match_process_at(post.prc_mp, post.pt_mp, p); }
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged);
    });
}
}
