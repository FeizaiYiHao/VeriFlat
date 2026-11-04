use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_sets_equal};
use crate::*;

verus! {
/// Releasing the unlocked, unqueued endpoint `ep_ptr` held only at descriptor `index` of `thrd_ptr` clears the
/// descriptor, records the thread's new progress, removes the endpoint from the endpoint map and its owner's endpoint set,
/// and returns one 4K quota to the container owning the endpoint's page; it projects to `kernel_u_endpoint_released`.
pub proof fn kernel_endpoint_released_implies_u_step(before: &KernelK, after: &KernelK, thrd_ptr: RwLockThreadPtr, ep_ptr: RwLockEndpointPtr, index: EndpointIdx)
    requires
        index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        *after == (KernelK { ctn_mp: after.ctn_mp, thrd_mp: after.thrd_mp, ep_mp: after.ep_mp, pg_arr: after.pg_arr, allc_4k_mp: after.allc_4k_mp, ..*before }),
        before.thrd_mp.dom().contains(thrd_ptr),
        before.thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors.view()[index as int] == Some(ep_ptr),
        after.thrd_mp.unchanged_except(&before.thrd_mp, thrd_ptr),
        after.thrd_mp.spec_index(thrd_ptr).view() == (Thread {
            endpoint_descriptors: after.thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors,
            syscall_progress: after.thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..before.thrd_mp.spec_index(thrd_ptr).view()
        }),
        after.thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors.view() == before.thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors.view().update(index as int, None),
        after.thrd_mp.spec_index(thrd_ptr).locking_thread() == before.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        after.thrd_mp.spec_index(thrd_ptr).being_killed() == before.thrd_mp.spec_index(thrd_ptr).being_killed(),
        before.ep_mp.dom().contains(ep_ptr),
        before.ep_mp.spec_index(ep_ptr).locking_thread() is None,
        before.ep_mp.spec_index(ep_ptr).view().owning_threads.view() == set![(thrd_ptr, index)],
        before.ep_mp.spec_index(ep_ptr).view().queue.view() == Seq::<RwLockThreadPtr>::empty(),
        after.ep_mp.dom() == before.ep_mp.dom().remove(ep_ptr),
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
                &&& b.view_ghost() == if c == before.ep_mp.spec_index(ep_ptr).view().owning_container {
                        ContainerGhost { owned_endpoints: Ghost(a.view_ghost().owned_endpoints.view().remove(ep_ptr)), ..a.view_ghost() }
                    } else { a.view_ghost() }
                &&& after.allc_4k_mp.spec_index(a.view_rodata().view().allocator_ptr_4k).quota.view().view() as int
                    == before.allc_4k_mp.spec_index(a.view_rodata().view().allocator_ptr_4k).quota.view().view() as int + if a.view().owned_pages.view().contains(ep_ptr) { 1int } else { 0int }
            },
    ensures
        kernel_u_endpoint_released(kernel_k_to_kernel_u(*before), kernel_k_to_kernel_u(*after), thrd_ptr, index as int),
        ({
            let thread = before.thrd_mp.spec_index(thrd_ptr);
            let t = thread.view();
            kernel_k_to_kernel_u(*before).thread_map[thrd_ptr] == (ThreadU {
                lock_state: thread.lock_state_u(), state: t.state, caller: t.caller, callee: t.callee, owning_container: t.owning_container, owning_proc: t.owning_proc,
                last_cpu: t.last_cpu, quota_4k: t.quota_4k, quota_2m: t.quota_2m, quota_1g: t.quota_1g, endpoint_descriptors: t.endpoint_descriptors.view(),
                blocking_endpoint_ptr: t.blocking_endpoint_ptr, ipc_payload: t.ipc_payload, error_code: t.error_code,
                trap_frame: if t.trap_frame.is_some() { Some(*t.trap_frame.get_some_0()) } else { None }, syscall_progress: t.syscall_progress.view(), killed: thread.being_killed(),
            })
        }),
        kernel_k_to_kernel_u(*before).thread_map.dom().contains(thrd_ptr),
        ({
            let pre = kernel_k_to_kernel_u(*before);
            kernel_k_to_kernel_u(*after).thread_map == pre.thread_map.insert(thrd_ptr, ThreadU {
                endpoint_descriptors: pre.thread_map[thrd_ptr].endpoint_descriptors.update(index as int, None),
                syscall_progress: after.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(), ..pre.thread_map[thrd_ptr]
            })
        }),
        kernel_k_to_kernel_u(*before) != kernel_k_to_kernel_u(*after),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    kernel_thread_projection_at(before, thrd_ptr); kernel_endpoint_projection_at(before, ep_ptr);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    let endpoint = pre.endpoint_map[ep_ptr];
    assert_maps_equal!(post.thread_map, pre.thread_map.insert(thrd_ptr, ThreadU {
        endpoint_descriptors: pre.thread_map[thrd_ptr].endpoint_descriptors.update(index as int, None),
        syscall_progress: after.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(), ..pre.thread_map[thrd_ptr]
    }), t => { if before.thrd_mp.dom().contains(t) { kernel_thread_projection_at(before, t); kernel_thread_projection_at(after, t); } });
    assert_maps_equal!(post.endpoint_map, pre.endpoint_map.remove(ep_ptr), e => {
        if after.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(before, e); kernel_endpoint_projection_at(after, e); }
    });
    assert_maps_equal!(post.container_map, Map::new(pre.container_map.dom(), |c: RwLockContainerPtr| {
        let container = pre.container_map[c];
        ContainerU {
            owned_endpoints: if c == endpoint.owning_container { container.owned_endpoints.remove(ep_ptr) } else { container.owned_endpoints },
            quota_4k: if container.owned_pages.contains(ep_ptr) { (container.quota_4k + 1) as usize } else { container.quota_4k }, ..container
        }
    }), c => {
        if before.ctn_mp.dom().contains(c) { kernel_container_projection_at(before, c); kernel_container_projection_at(after, c); }
    });
    kernel_cpu_array_unchanged_implies_u_cpu_array(before, after); kernel_process_maps_unchanged_implies_u_process_map(before, after);
    reveal(kernel_u_endpoint_released);
}

/// Releasing the endpoint held only at descriptor `index` of the write-held killed thread `thrd_ptr` projects to
/// `kernel_u_killed_endpoint_released`, changes the projection, and changes no thread outside `thrd_ptr`'s container.
pub proof fn kernel_killed_endpoint_released_implies_u_step(before: &KernelK, after: &KernelK, thrd_ptr: RwLockThreadPtr, ep_ptr: RwLockEndpointPtr, index: EndpointIdx)
    requires
        index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        *after == (KernelK { ctn_mp: after.ctn_mp, thrd_mp: after.thrd_mp, ep_mp: after.ep_mp, pg_arr: after.pg_arr, allc_4k_mp: after.allc_4k_mp, ..*before }),
        before.thrd_mp.dom().contains(thrd_ptr),
        before.thrd_mp.spec_index(thrd_ptr).view().state is KILLED,
        before.thrd_mp.spec_index(thrd_ptr).locking_thread() is Write,
        before.thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors.view().len() == MAX_NUM_ENDPOINT_DESCRIPTORS,
        before.thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors.view()[index as int] == Some(ep_ptr),
        after.thrd_mp.unchanged_except(&before.thrd_mp, thrd_ptr),
        after.thrd_mp.spec_index(thrd_ptr).view() == (Thread { endpoint_descriptors: after.thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors, ..before.thrd_mp.spec_index(thrd_ptr).view() }),
        after.thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors.view() == before.thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors.view().update(index as int, None),
        after.thrd_mp.spec_index(thrd_ptr).locking_thread() == before.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        after.thrd_mp.spec_index(thrd_ptr).being_killed() == before.thrd_mp.spec_index(thrd_ptr).being_killed(),
        before.ep_mp.dom().contains(ep_ptr),
        before.ep_mp.spec_index(ep_ptr).locking_thread() is None,
        before.ep_mp.spec_index(ep_ptr).view().owning_threads.view() == set![(thrd_ptr, index)],
        before.ep_mp.spec_index(ep_ptr).view().queue.view() == Seq::<RwLockThreadPtr>::empty(),
        after.ep_mp.dom() == before.ep_mp.dom().remove(ep_ptr),
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
                &&& b.view_ghost() == if c == before.ep_mp.spec_index(ep_ptr).view().owning_container {
                        ContainerGhost { owned_endpoints: Ghost(a.view_ghost().owned_endpoints.view().remove(ep_ptr)), ..a.view_ghost() }
                    } else { a.view_ghost() }
                &&& after.allc_4k_mp.spec_index(a.view_rodata().view().allocator_ptr_4k).quota.view().view() as int
                    == before.allc_4k_mp.spec_index(a.view_rodata().view().allocator_ptr_4k).quota.view().view() as int + if a.view().owned_pages.view().contains(ep_ptr) { 1int } else { 0int }
            },
    ensures
        kernel_u_killed_endpoint_released(kernel_k_to_kernel_u(*before), kernel_k_to_kernel_u(*after)),
        ({
            let pre = kernel_k_to_kernel_u(*before);
            let post = kernel_k_to_kernel_u(*after);
            forall|t: RwLockThreadPtr| #![trigger pre.thread_map[t]]
                pre.thread_map.dom().contains(t) && (!post.thread_map.dom().contains(t) || post.thread_map[t] != pre.thread_map[t]) ==> pre.thread_map[t].owning_container == before.thrd_mp.spec_index(thrd_ptr).view().owning_container
        }),
        kernel_k_to_kernel_u(*before) != kernel_k_to_kernel_u(*after),
{
    kernel_endpoint_released_implies_u_step(before, after, thrd_ptr, ep_ptr, index);
    kernel_thread_projection_at(after, thrd_ptr);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    let thread = pre.thread_map[thrd_ptr];
    assert_sets_equal!(pre.thread_map.dom().filter(|t: RwLockThreadPtr| post.thread_map[t] != pre.thread_map[t]), set![thrd_ptr]);
    assert_sets_equal!(Set::<int>::range(0, MAX_NUM_ENDPOINT_DESCRIPTORS as int).filter(|j: int| post.thread_map[thrd_ptr].endpoint_descriptors[j] != thread.endpoint_descriptors[j]), set![index as int]);
    reveal(kernel_u_killed_endpoint_released);
}
}
