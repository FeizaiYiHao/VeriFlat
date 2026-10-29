use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_sets_equal};
use crate::*;

verus! {
/// Releasing the unlocked, unqueued endpoint `endpoint_ptr` held only at descriptor `index` of `thread_ptr` clears the
/// descriptor, records the thread's new progress, removes the endpoint from the endpoint map and its owner's endpoint set,
/// and returns one 4K quota to the container owning the endpoint's page; it projects to `kernel_u_endpoint_released`.
pub proof fn kernel_endpoint_released_implies_u_step(before: &KernelK, after: &KernelK, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, index: EndpointIdx)
    requires
        index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        *after == (KernelK { ctn_mp: after.ctn_mp, thr_mp: after.thr_mp, ep_mp: after.ep_mp, pg_arr: after.pg_arr, allc_4k_mp: after.allc_4k_mp, ..*before }),
        before.thr_mp.dom().contains(thread_ptr),
        before.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[index as int] == Some(endpoint_ptr),
        after.thr_mp.unchanged_except(&before.thr_mp, thread_ptr),
        after.thr_mp.spec_index(thread_ptr).view() == (Thread {
            endpoint_descriptors: after.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors,
            syscall_progress: after.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..before.thr_mp.spec_index(thread_ptr).view()
        }),
        after.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view() == before.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view().update(index as int, None),
        after.thr_mp.spec_index(thread_ptr).locking_thread() == before.thr_mp.spec_index(thread_ptr).locking_thread(),
        after.thr_mp.spec_index(thread_ptr).being_killed() == before.thr_mp.spec_index(thread_ptr).being_killed(),
        before.ep_mp.dom().contains(endpoint_ptr),
        before.ep_mp.spec_index(endpoint_ptr).locking_thread() is None,
        before.ep_mp.spec_index(endpoint_ptr).view().owning_threads.view() == set![(thread_ptr, index)],
        before.ep_mp.spec_index(endpoint_ptr).view().queue.view() == Seq::<RwLockThreadPtr>::empty(),
        after.ep_mp.dom() == before.ep_mp.dom().remove(endpoint_ptr),
        forall|e: RwLockEndpointPtr| #![trigger after.ep_mp.spec_index(e)] after.ep_mp.dom().contains(e) ==> after.ep_mp.spec_index(e) == before.ep_mp.spec_index(e),
        after.ctn_mp.dom() == before.ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger after.ctn_mp.spec_index(c)]
            before.ctn_mp.dom().contains(c) ==> {
                let a = before.ctn_mp.spec_index(c);
                let b = after.ctn_mp.spec_index(c);
                &&& b.view() == a.view()
                &&& b.view_rodata() == a.view_rodata()
                &&& b.locking_thread() == a.locking_thread()
                &&& b.control() == a.control()
                &&& b.view_ghost() == if c == before.ep_mp.spec_index(endpoint_ptr).view().owning_container {
                        ContainerGhost { owned_endpoints: Ghost(a.view_ghost().owned_endpoints.view().remove(endpoint_ptr)), ..a.view_ghost() }
                    } else { a.view_ghost() }
                &&& after.allc_4k_mp.spec_index(a.view_rodata().view().allocator_ptr_4k).quota.view().view() as int
                    == before.allc_4k_mp.spec_index(a.view_rodata().view().allocator_ptr_4k).quota.view().view() as int + if a.view().owned_pages.view().contains(endpoint_ptr) { 1int } else { 0int }
            },
    ensures
        kernel_u_endpoint_released(kernel_k_to_kernel_u(*before), kernel_k_to_kernel_u(*after), thread_ptr, index as int),
        ({
            let thread = before.thr_mp.spec_index(thread_ptr);
            let t = thread.view();
            kernel_k_to_kernel_u(*before).thread_map[thread_ptr] == (ThreadU {
                lock_state: thread.lock_state_u(), state: t.state, caller: t.caller, callee: t.callee, owning_container: t.owning_container, owning_proc: t.owning_proc,
                last_cpu: t.last_cpu, quota_4k: t.quota_4k, quota_2m: t.quota_2m, quota_1g: t.quota_1g, endpoint_descriptors: t.endpoint_descriptors.view(),
                blocking_endpoint_ptr: t.blocking_endpoint_ptr, ipc_payload: t.ipc_payload, error_code: t.error_code,
                trap_frame: if t.trap_frame.is_some() { Some(*t.trap_frame.get_some_0()) } else { None }, syscall_progress: t.syscall_progress.view(), killed: thread.being_killed(),
            })
        }),
        kernel_k_to_kernel_u(*before).thread_map.dom().contains(thread_ptr),
        ({
            let pre = kernel_k_to_kernel_u(*before);
            kernel_k_to_kernel_u(*after).thread_map == pre.thread_map.insert(thread_ptr, ThreadU {
                endpoint_descriptors: pre.thread_map[thread_ptr].endpoint_descriptors.update(index as int, None),
                syscall_progress: after.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(), ..pre.thread_map[thread_ptr]
            })
        }),
        kernel_k_to_kernel_u(*before) != kernel_k_to_kernel_u(*after),
        kernel_k_to_nonlock_kernel_u(*before) != kernel_k_to_nonlock_kernel_u(*after),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    kernel_thread_projection_at(before, thread_ptr); kernel_endpoint_projection_at(before, endpoint_ptr);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    let endpoint = pre.endpoint_map[endpoint_ptr];
    assert_maps_equal!(post.thread_map, pre.thread_map.insert(thread_ptr, ThreadU {
        endpoint_descriptors: pre.thread_map[thread_ptr].endpoint_descriptors.update(index as int, None),
        syscall_progress: after.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(), ..pre.thread_map[thread_ptr]
    }), t => { if before.thr_mp.dom().contains(t) { kernel_thread_projection_at(before, t); kernel_thread_projection_at(after, t); } });
    assert_maps_equal!(post.endpoint_map, pre.endpoint_map.remove(endpoint_ptr), e => {
        if after.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(before, e); kernel_endpoint_projection_at(after, e); }
    });
    assert_maps_equal!(post.container_map, Map::new(pre.container_map.dom(), |c: RwLockContainerPtr| {
        let container = pre.container_map[c];
        ContainerU {
            owned_endpoints: if c == endpoint.owning_container { container.owned_endpoints.remove(endpoint_ptr) } else { container.owned_endpoints },
            quota_4k: if container.owned_pages.contains(endpoint_ptr) { (container.quota_4k + 1) as usize } else { container.quota_4k }, ..container
        }
    }), c => {
        if before.ctn_mp.dom().contains(c) { kernel_container_projection_at(before, c); kernel_container_projection_at(after, c); }
    });
    kernel_cpu_array_unchanged_implies_u_cpu_array(before, after); kernel_process_maps_unchanged_implies_u_process_map(before, after);
    assert(kernel_k_to_nonlock_kernel_u(*before).endpoint_map.dom().contains(endpoint_ptr) && !kernel_k_to_nonlock_kernel_u(*after).endpoint_map.dom().contains(endpoint_ptr)) by {
        reveal(kernel_k_to_nonlock_kernel_u);
    };
    reveal(kernel_u_endpoint_released);
}

/// Releasing the endpoint held only at descriptor `index` of the write-held killed thread `thread_ptr` projects to
/// `kernel_u_killed_endpoint_released`, changes both projections, and changes no thread outside `thread_ptr`'s container.
pub proof fn kernel_killed_endpoint_released_implies_u_step(before: &KernelK, after: &KernelK, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, index: EndpointIdx)
    requires
        index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        *after == (KernelK { ctn_mp: after.ctn_mp, thr_mp: after.thr_mp, ep_mp: after.ep_mp, pg_arr: after.pg_arr, allc_4k_mp: after.allc_4k_mp, ..*before }),
        before.thr_mp.dom().contains(thread_ptr),
        before.thr_mp.spec_index(thread_ptr).view().state is KILLED,
        before.thr_mp.spec_index(thread_ptr).locking_thread() is Write,
        before.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view().len() == MAX_NUM_ENDPOINT_DESCRIPTORS,
        before.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[index as int] == Some(endpoint_ptr),
        after.thr_mp.unchanged_except(&before.thr_mp, thread_ptr),
        after.thr_mp.spec_index(thread_ptr).view() == (Thread { endpoint_descriptors: after.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors, ..before.thr_mp.spec_index(thread_ptr).view() }),
        after.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view() == before.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view().update(index as int, None),
        after.thr_mp.spec_index(thread_ptr).locking_thread() == before.thr_mp.spec_index(thread_ptr).locking_thread(),
        after.thr_mp.spec_index(thread_ptr).being_killed() == before.thr_mp.spec_index(thread_ptr).being_killed(),
        before.ep_mp.dom().contains(endpoint_ptr),
        before.ep_mp.spec_index(endpoint_ptr).locking_thread() is None,
        before.ep_mp.spec_index(endpoint_ptr).view().owning_threads.view() == set![(thread_ptr, index)],
        before.ep_mp.spec_index(endpoint_ptr).view().queue.view() == Seq::<RwLockThreadPtr>::empty(),
        after.ep_mp.dom() == before.ep_mp.dom().remove(endpoint_ptr),
        forall|e: RwLockEndpointPtr| #![trigger after.ep_mp.spec_index(e)] after.ep_mp.dom().contains(e) ==> after.ep_mp.spec_index(e) == before.ep_mp.spec_index(e),
        after.ctn_mp.dom() == before.ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger after.ctn_mp.spec_index(c)]
            before.ctn_mp.dom().contains(c) ==> {
                let a = before.ctn_mp.spec_index(c);
                let b = after.ctn_mp.spec_index(c);
                &&& b.view() == a.view()
                &&& b.view_rodata() == a.view_rodata()
                &&& b.locking_thread() == a.locking_thread()
                &&& b.control() == a.control()
                &&& b.view_ghost() == if c == before.ep_mp.spec_index(endpoint_ptr).view().owning_container {
                        ContainerGhost { owned_endpoints: Ghost(a.view_ghost().owned_endpoints.view().remove(endpoint_ptr)), ..a.view_ghost() }
                    } else { a.view_ghost() }
                &&& after.allc_4k_mp.spec_index(a.view_rodata().view().allocator_ptr_4k).quota.view().view() as int
                    == before.allc_4k_mp.spec_index(a.view_rodata().view().allocator_ptr_4k).quota.view().view() as int + if a.view().owned_pages.view().contains(endpoint_ptr) { 1int } else { 0int }
            },
    ensures
        kernel_u_killed_endpoint_released(kernel_k_to_kernel_u(*before), kernel_k_to_kernel_u(*after)),
        ({
            let pre = kernel_k_to_kernel_u(*before);
            let post = kernel_k_to_kernel_u(*after);
            forall|t: RwLockThreadPtr| #![trigger pre.thread_map[t]]
                pre.thread_map.dom().contains(t) && (!post.thread_map.dom().contains(t) || post.thread_map[t] != pre.thread_map[t]) ==> pre.thread_map[t].owning_container == before.thr_mp.spec_index(thread_ptr).view().owning_container
        }),
        kernel_k_to_kernel_u(*before) != kernel_k_to_kernel_u(*after),
        kernel_k_to_nonlock_kernel_u(*before) != kernel_k_to_nonlock_kernel_u(*after),
{
    kernel_endpoint_released_implies_u_step(before, after, thread_ptr, endpoint_ptr, index);
    kernel_thread_projection_at(after, thread_ptr);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    let thread = pre.thread_map[thread_ptr];
    assert_sets_equal!(pre.thread_map.dom().filter(|t: RwLockThreadPtr| post.thread_map[t] != pre.thread_map[t]), set![thread_ptr]);
    assert_sets_equal!(Set::<int>::range(0, MAX_NUM_ENDPOINT_DESCRIPTORS as int).filter(|j: int| post.thread_map[thread_ptr].endpoint_descriptors[j] != thread.endpoint_descriptors[j]), set![index as int]);
    reveal(kernel_u_killed_endpoint_released);
}
}
