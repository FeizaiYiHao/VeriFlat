use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal};
use crate::*;

verus! {
/// Unchanged container nonlock fields, quotas, and container lock owners project to an unchanged container map.
pub proof fn kernel_container_nonlock_fields_and_locks_unchanged_implies_u_container_map(pre: &KernelK, post: &KernelK, include_lock_state: bool)
    requires
        kernel_container_nonlock_fields_and_quotas_unchanged(pre, post),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)]
            pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).locking_thread() == pre.ctn_mp.spec_index(p).locking_thread(),
    ensures kernel_k_user_projection(*post, include_lock_state).container_map == kernel_k_user_projection(*pre, include_lock_state).container_map,
{
    hide(kernel_k_user_projection);
    reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    assert_maps_equal!(post_u.container_map, pre_u.container_map, c => { if pre.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(pre, include_lock_state, c); } if post.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(post, include_lock_state, c); } });
}

/// Unchanged process and table nonlock fields and lock owners project to an unchanged process map.
pub proof fn kernel_process_nonlock_fields_and_locks_unchanged_implies_u_process_map(pre: &KernelK, post: &KernelK, include_lock_state: bool)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, post.pt_mp),
        kernel_pagetable_nonlock_fields_unchanged(pre.it_mp, post.it_mp),
        kernel_process_nonlock_fields_unchanged(pre.prc_mp, post.prc_mp),
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) && post.prc_mp.dom().contains(p) ==> post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) && post.pt_mp.dom().contains(p) ==> post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
            pre.it_mp.dom().contains(p) && post.it_mp.dom().contains(p) ==> post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread(),
    ensures kernel_k_user_projection(*post, include_lock_state).process_map == kernel_k_user_projection(*pre, include_lock_state).process_map,
{
    hide(kernel_k_user_projection);
    reveal(kernel_process_nonlock_fields_unchanged); kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    assert_maps_equal!(post_u.process_map, pre_u.process_map, p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_user_projection_at(pre, include_lock_state, p); } if post.prc_mp.dom().contains(p) { kernel_process_user_projection_at(post, include_lock_state, p); }
        process_pagetable_match_process_at(post.prc_mp, post.pt_mp, p); process_iommu_table_match_process_at(post.prc_mp, post.it_mp, p); reveal(kernel_pagetable_nonlock_fields_unchanged);
    });
}

/// Unchanged endpoint nonlock fields and lock owners project to an unchanged endpoint map.
pub proof fn kernel_endpoint_nonlock_fields_and_locks_unchanged_implies_u_endpoint_map(pre: &KernelK, post: &KernelK, include_lock_state: bool)
    requires
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        forall|p: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(p)]
            pre.ep_mp.dom().contains(p) ==> post.ep_mp.spec_index(p).locking_thread() == pre.ep_mp.spec_index(p).locking_thread(),
    ensures kernel_k_user_projection(*post, include_lock_state).endpoint_map == kernel_k_user_projection(*pre, include_lock_state).endpoint_map,
{
    hide(kernel_k_user_projection);
    reveal(kernel_endpoint_nonlock_fields_unchanged);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => { if pre.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(pre, include_lock_state, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(post, include_lock_state, e); } });
}

/// Cpu `cpu_id` entering `state` with no current process or thread, every other cpu and every cpu lock owner unchanged,
/// projects to that cpu-array update.
pub proof fn kernel_cpu_state_set_and_current_cleared_implies_u_cpu_array(pre: &KernelK, post: &KernelK, cpu_id: CpuId, state: CpuState, include_lock_state: bool)
    requires
        index_valid(NUM_CPUS, cpu_id),
        forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> post.cpu_arr.spec_index(i).value.locking_thread() == pre.cpu_arr.spec_index(i).value.locking_thread(),
        forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> {
                let a = pre.cpu_arr.spec_index(i).value.view().view();
                let b = post.cpu_arr.spec_index(i).value.view().view();
                &&& b.owning_container == a.owning_container
                &&& b.state == if i == cpu_id { state } else { a.state }
                &&& b.current_process == if i == cpu_id { None } else { a.current_process }
                &&& b.current_thread == if i == cpu_id { None } else { a.current_thread }
                &&& post.cpu_arr.spec_index(i).value.killer_info() == pre.cpu_arr.spec_index(i).value.killer_info()
            },
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let post_u = kernel_k_user_projection(*post, include_lock_state);
            post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU { state, current_process: None, current_thread: None, ..pre_u.cpu_array[cpu_id as int] })
        }),
{
    hide(kernel_k_user_projection);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU { state, current_process: None, current_thread: None, ..pre_u.cpu_array[cpu_id as int] }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, include_lock_state, i as usize); kernel_cpu_user_projection_at(post, include_lock_state, i as usize); }
    });
}

/// The IPC block fields project to the thread map with only the blocking thread waiting on the endpoint.
pub proof fn kernel_ipc_block_fields_implies_u_thread_map(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    waiting_state: ThreadState, payload: IPCPayLoad, regs: Registers, flushed_default_pcid: bool, include_lock_state: bool,
)
    requires kernel_ipc_block_fields(pre, post, cpu_id, thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, regs, flushed_default_pcid),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let post_u = kernel_k_user_projection(*post, include_lock_state);
            post_u.thread_map == pre_u.thread_map.insert(thread_ptr, ThreadU {
                state: waiting_state, blocking_endpoint_ptr: Some(endpoint_ptr), ipc_payload: payload, trap_frame: Some(regs), ..pre_u.thread_map.spec_index(thread_ptr)
            })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_ipc_block_fields);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thread_ptr, ThreadU {
        state: waiting_state, blocking_endpoint_ptr: Some(endpoint_ptr), ipc_payload: payload, trap_frame: Some(regs), ..pre_u.thread_map.spec_index(thread_ptr)
    }), t => { if pre.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(pre, include_lock_state, t); } if post.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(post, include_lock_state, t); } });
}

/// The IPC block fields project to the endpoint map with only the blocking thread appended to the endpoint queue.
pub proof fn kernel_ipc_block_fields_implies_u_endpoint_map(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    waiting_state: ThreadState, payload: IPCPayLoad, regs: Registers, flushed_default_pcid: bool, include_lock_state: bool,
)
    requires kernel_ipc_block_fields(pre, post, cpu_id, thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, regs, flushed_default_pcid),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let post_u = kernel_k_user_projection(*post, include_lock_state);
            let endpoint = pre_u.endpoint_map.spec_index(endpoint_ptr);
            post_u.endpoint_map == pre_u.endpoint_map.insert(endpoint_ptr, EndpointU {
                queue: endpoint.queue.push(thread_ptr),
                queue_state: if endpoint.queue.len() == 0 {
                    match waiting_state { ThreadState::SENDING | ThreadState::CALLING => EndpointState::SEND, _ => EndpointState::RECEIVE }
                } else { endpoint.queue_state },
                ..endpoint
            })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_ipc_block_fields);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    let endpoint = pre_u.endpoint_map.spec_index(endpoint_ptr);
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map.insert(endpoint_ptr, EndpointU {
        queue: endpoint.queue.push(thread_ptr),
        queue_state: if endpoint.queue.len() == 0 {
            match waiting_state { ThreadState::SENDING | ThreadState::CALLING => EndpointState::SEND, _ => EndpointState::RECEIVE }
        } else { endpoint.queue_state },
        ..endpoint
    }), e => { if pre.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(pre, include_lock_state, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(post, include_lock_state, e); } });
}

/// The call-handoff fields project to the cpu array with only `cpu_id` switched to the callee.
pub proof fn kernel_ipc_call_handoff_fields_implies_u_cpu_array(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, caller_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    callee_ptr: RwLockThreadPtr, regs: Registers, flushed_pcid: Option<Pcid>, include_lock_state: bool,
)
    requires kernel_ipc_call_handoff_fields(pre, post, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, regs, flushed_pcid),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let post_u = kernel_k_user_projection(*post, include_lock_state);
            post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU {
                current_process: Some(pre_u.thread_map.spec_index(callee_ptr).owning_proc), current_thread: Some(callee_ptr), ..pre_u.cpu_array[cpu_id as int]
            })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_ipc_call_handoff_fields);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    if pre.thr_mp.dom().contains(callee_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, callee_ptr); } if index_valid(NUM_CPUS, cpu_id) { kernel_cpu_user_projection_at(pre, include_lock_state, cpu_id); }
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU {
        current_process: Some(pre_u.thread_map.spec_index(callee_ptr).owning_proc), current_thread: Some(callee_ptr), ..pre_u.cpu_array[cpu_id as int]
    }), i => { if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, include_lock_state, i as usize); kernel_cpu_user_projection_at(post, include_lock_state, i as usize); } });
}

/// The call-handoff fields project to the thread map with the caller waiting for the reply and the callee running.
pub proof fn kernel_ipc_call_handoff_fields_implies_u_thread_map(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, caller_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    callee_ptr: RwLockThreadPtr, regs: Registers, flushed_pcid: Option<Pcid>, include_lock_state: bool,
)
    requires kernel_ipc_call_handoff_fields(pre, post, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, regs, flushed_pcid),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let post_u = kernel_k_user_projection(*post, include_lock_state);
            let caller = pre_u.thread_map.spec_index(caller_ptr);
            let callee = pre_u.thread_map.spec_index(callee_ptr);
            post_u.thread_map == pre_u.thread_map.insert(caller_ptr, ThreadU { state: ThreadState::WAITING_REPLY, callee: Some(callee_ptr), trap_frame: Some(regs), ..caller })
                .insert(callee_ptr, ThreadU { state: ThreadState::RUNNING { cpu_id }, caller: Some(caller_ptr), last_cpu: cpu_id, blocking_endpoint_ptr: None, trap_frame: None, ..callee })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_ipc_call_handoff_fields); kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    if pre.thr_mp.dom().contains(caller_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, caller_ptr); } if pre.thr_mp.dom().contains(callee_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, callee_ptr); }
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    let caller = pre_u.thread_map.spec_index(caller_ptr);
    let callee = pre_u.thread_map.spec_index(callee_ptr);
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(caller_ptr, ThreadU { state: ThreadState::WAITING_REPLY, callee: Some(callee_ptr), trap_frame: Some(regs), ..caller })
        .insert(callee_ptr, ThreadU { state: ThreadState::RUNNING { cpu_id }, caller: Some(caller_ptr), last_cpu: cpu_id, blocking_endpoint_ptr: None, trap_frame: None, ..callee }), t => {
        if pre.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(pre, include_lock_state, t); }
        if post.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(post, include_lock_state, t); }
    });
}

/// The call-handoff fields project to the endpoint map with only the callee dequeued from the endpoint.
pub proof fn kernel_ipc_call_handoff_fields_implies_u_endpoint_map(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, caller_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    callee_ptr: RwLockThreadPtr, regs: Registers, flushed_pcid: Option<Pcid>, include_lock_state: bool,
)
    requires kernel_ipc_call_handoff_fields(pre, post, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, regs, flushed_pcid),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let post_u = kernel_k_user_projection(*post, include_lock_state);
            let endpoint = pre_u.endpoint_map.spec_index(endpoint_ptr);
            post_u.endpoint_map == pre_u.endpoint_map.insert(endpoint_ptr, EndpointU { queue: endpoint.queue.skip(1), ..endpoint })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_ipc_call_handoff_fields);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    if pre.ep_mp.dom().contains(endpoint_ptr) { kernel_endpoint_user_projection_at(pre, include_lock_state, endpoint_ptr); }
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    let endpoint = pre_u.endpoint_map.spec_index(endpoint_ptr);
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map.insert(endpoint_ptr, EndpointU { queue: endpoint.queue.skip(1), ..endpoint }), e => {
        if pre.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(pre, include_lock_state, e); }
        if post.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(post, include_lock_state, e); }
    });
}

/// The cpu-off fields project to the container map with the requeued thread and the cleared request bit of the cpu's container.
pub proof fn kernel_cpu_went_off_fields_implies_u_container_map(pre: &KernelK, post: &KernelK, cpu_id: CpuId, regs: Registers, flushed_default_pcid: bool, include_lock_state: bool)
    requires
        container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp),
        kernel_cpu_went_off_fields(pre, post, cpu_id, regs, flushed_default_pcid),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let post_u = kernel_k_user_projection(*post, include_lock_state);
            let cpu = pre_u.cpu_array[cpu_id as int];
            let container = pre_u.container_map.spec_index(cpu.owning_container);
            post_u.container_map == pre_u.container_map.insert(cpu.owning_container, ContainerU {
                scheduler: match cpu.current_thread {
                    Some(prev) => container.scheduler.update(cpu_id as int, container.scheduler[cpu_id as int].push(prev)),
                    None => container.scheduler,
                },
                cpu_offline_requests: container.cpu_offline_requests.update(cpu_id as int, false),
                ..container
            })
        }),
{
    reveal(kernel_cpu_went_off_fields); reveal(container_cpu_set_wf);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    let cpu = pre_u.cpu_array[cpu_id as int];
    let container = pre_u.container_map.spec_index(cpu.owning_container);
    assert_maps_equal!(post_u.container_map, pre_u.container_map.insert(cpu.owning_container, ContainerU {
        scheduler: match cpu.current_thread {
            Some(prev) => container.scheduler.update(cpu_id as int, container.scheduler[cpu_id as int].push(prev)),
            None => container.scheduler,
        },
        cpu_offline_requests: container.cpu_offline_requests.update(cpu_id as int, false),
        ..container
    }), c => {});
}

/// The cpu-off fields project to the thread map with only the cpu's running thread, if any, requeued with `regs`.
pub proof fn kernel_cpu_went_off_fields_implies_u_thread_map(pre: &KernelK, post: &KernelK, cpu_id: CpuId, regs: Registers, flushed_default_pcid: bool, include_lock_state: bool)
    requires kernel_cpu_went_off_fields(pre, post, cpu_id, regs, flushed_default_pcid),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let post_u = kernel_k_user_projection(*post, include_lock_state);
            post_u.thread_map == match pre_u.cpu_array[cpu_id as int].current_thread {
                Some(prev) => pre_u.thread_map.insert(prev, ThreadU {
                    state: ThreadState::SCHEDULED { cpu_id }, error_code: None, trap_frame: Some(regs), ..pre_u.thread_map.spec_index(prev)
                }),
                None => pre_u.thread_map,
            }
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_cpu_went_off_fields);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    assert(post_u.thread_map.dom() == post.thr_mp.dom() && pre_u.thread_map.dom() == pre.thr_mp.dom() && pre_u.cpu_array[cpu_id as int].current_thread == pre.cpu_arr.spec_index(cpu_id).value.view().view().current_thread) by { reveal(kernel_k_user_projection); };
    match pre_u.cpu_array[cpu_id as int].current_thread {
        Some(prev) => {
            assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(prev, ThreadU {
                state: ThreadState::SCHEDULED { cpu_id }, error_code: None, trap_frame: Some(regs), ..pre_u.thread_map.spec_index(prev)
            }), t => { reveal(kernel_k_user_projection); });
        },
        None => { assert_maps_equal!(post_u.thread_map, pre_u.thread_map, t => { reveal(kernel_k_user_projection); }); },
    }
}

/// The page-owner move leaves the process map projection unchanged: only the write-held table `table` changed, with equal mappings.
pub proof fn kernel_thread_quota_and_page_owner_changed_implies_u_process_map(pre: &KernelK, post: &KernelK, lctx: &LocalContext, table: RwLockPageTableRoot)
    requires
        process_pagetable_match(pre.prc_mp, pre.pt_mp),
        post.prc_mp == pre.prc_mp,
        post.it_mp == pre.it_mp,
        post.pt_mp.unchanged_except(&pre.pt_mp, table),
        pre.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        post.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), table, TypedLockMode::Write),
        post.pt_mp.spec_index(table).view().mapping_4k() == pre.pt_mp.spec_index(table).view().mapping_4k(),
        post.pt_mp.spec_index(table).view().mapping_2m() == pre.pt_mp.spec_index(table).view().mapping_2m(),
        post.pt_mp.spec_index(table).view().mapping_1g() == pre.pt_mp.spec_index(table).view().mapping_1g(),
    ensures kernel_k_to_kernel_u(*post).process_map == kernel_k_to_kernel_u(*pre).process_map,
{
    pre.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), table);
    post.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), table);
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post); reveal(process_pagetable_match);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    assert_maps_equal!(b.process_map, a.process_map, p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); }
    });
}

/// The write-held thread `thread` losing one 4K quota projects to that thread-map update.
pub proof fn kernel_thread_quota_and_page_owner_changed_implies_u_thread_map(pre: &KernelK, post: &KernelK, lctx: &LocalContext, thread: RwLockThreadPtr)
    requires
        pre.thr_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        post.thr_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread, TypedLockMode::Write),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread),
        kernel_thread_quota_4k_changed(pre, post, thread, -1),
        post.thr_mp.spec_index(thread).view().syscall_progress == pre.thr_mp.spec_index(thread).view().syscall_progress,
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let b = kernel_k_to_kernel_u(*post);
            b.thread_map == a.thread_map.insert(thread, ThreadU { quota_4k: (a.thread_map[thread].quota_4k - 1) as usize, ..a.thread_map[thread] })
        }),
{
    pre.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread);
    post.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread);
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post); reveal(kernel_thread_quota_4k_changed);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    assert_maps_equal!(b.thread_map, a.thread_map.insert(thread, ThreadU { quota_4k: (a.thread_map[thread].quota_4k - 1) as usize, ..a.thread_map[thread] }), p => {
        if pre.thr_mp.dom().contains(p) { kernel_thread_projection_at(pre, p); } if post.thr_mp.dom().contains(p) { kernel_thread_projection_at(post, p); }
    });
}

/// Moving `page` from the owned pages of `source` to those of `target` projects to that container-map update.
pub proof fn kernel_thread_quota_and_page_owner_changed_implies_u_container_map(pre: &KernelK, post: &KernelK, source: RwLockContainerPtr, target: RwLockContainerPtr, page: PagePtr)
    requires
        *post == (KernelK { pg_arr: post.pg_arr, ctn_mp: post.ctn_mp, thr_mp: post.thr_mp, pt_mp: post.pt_mp, ..*pre }),
        source != target,
        pre.ctn_mp.dom().contains(source),
        pre.ctn_mp.dom().contains(target),
        post.ctn_mp.dom() == pre.ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)] pre.ctn_mp.dom().contains(c) ==> {
            &&& post.ctn_mp.spec_index(c).view_rodata() == pre.ctn_mp.spec_index(c).view_rodata()
            &&& post.ctn_mp.spec_index(c).view_ghost() == pre.ctn_mp.spec_index(c).view_ghost()
            &&& post.ctn_mp.spec_index(c).locking_thread() == pre.ctn_mp.spec_index(c).locking_thread()
            &&& post.ctn_mp.spec_index(c).being_killed() == pre.ctn_mp.spec_index(c).being_killed()
            &&& post.ctn_mp.spec_index(c).view() == (Container { owned_pages: post.ctn_mp.spec_index(c).view().owned_pages, ..pre.ctn_mp.spec_index(c).view() })
            &&& post.ctn_mp.spec_index(c).view().owned_pages.view() == if c == source { pre.ctn_mp.spec_index(c).view().owned_pages.view().remove(page) }
                else if c == target { pre.ctn_mp.spec_index(c).view().owned_pages.view().insert(page) } else { pre.ctn_mp.spec_index(c).view().owned_pages.view() }
        },
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let b = kernel_k_to_kernel_u(*post);
            b.container_map == a.container_map.insert(source, ContainerU { owned_pages: a.container_map[source].owned_pages.remove(page), ..a.container_map[source] })
                .insert(target, ContainerU { owned_pages: a.container_map[target].owned_pages.insert(page), ..a.container_map[target] })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    assert_maps_equal!(b.container_map, a.container_map.insert(source, ContainerU { owned_pages: a.container_map[source].owned_pages.remove(page), ..a.container_map[source] })
        .insert(target, ContainerU { owned_pages: a.container_map[target].owned_pages.insert(page), ..a.container_map[target] }), p => {
            if pre.ctn_mp.dom().contains(p) { kernel_container_projection_at(pre, p); } if post.ctn_mp.dom().contains(p) { kernel_container_projection_at(post, p); }
        });
}

/// Only the lock mode of cpu `cpu_id` changing, to `mode`, projects to that cpu-array update.
pub proof fn kernel_cpu_lock_mode_changed_implies_u_cpu_array(pre: &KernelK, post: &KernelK, cpu_id: CpuId, mode: LockStateU)
    requires
        index_valid(NUM_CPUS, cpu_id),
        post.cpu_arr.unchanged_except(&pre.cpu_arr, cpu_id),
        kernel_cpu_nonlock_fields_unchanged(pre.cpu_arr, post.cpu_arr),
        post.cpu_arr.spec_index(cpu_id).value.lock_state_u() == mode,
    ensures kernel_k_to_kernel_u(*post).cpu_array == kernel_k_to_kernel_u(*pre).cpu_array.update(cpu_id as int, CpuU { lock_state: mode, ..kernel_k_to_kernel_u(*pre).cpu_array[cpu_id as int] }),
{
    reveal(kernel_cpu_nonlock_fields_unchanged); kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    assert_seqs_equal!(b.cpu_array == a.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, ..a.cpu_array[cpu_id as int] }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); }
    });
}

/// Only the lock modes of `container` and, with `cpu_set_unlocked`, of its cpu set changing, to `mode`, project to that container-map update.
pub proof fn kernel_container_lock_mode_changed_implies_u_container_map(
    pre: &KernelK, post: &KernelK, container: Option<RwLockContainerPtr>, mode: LockStateU, cpu_set_unlocked: Option<KernelK>,
)
    requires
        match container {
            Some(c) => {
                &&& pre.ctn_mp.dom().contains(c)
                &&& post.ctn_mp.unchanged_except(&pre.ctn_mp, c)
                &&& post.ctn_mp.spec_index(c).lock_state_u() == mode
            },
            None => post.ctn_mp == pre.ctn_mp,
        },
        match cpu_set_unlocked {
            Some(mid) => {
                let s = post.ctn_mp.spec_index(container->Some_0).view_rodata().view().cpu_set;
                &&& container is Some
                &&& container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)
                &&& *post == (KernelK { cpu_set_mp: post.cpu_set_mp, ..mid })
                &&& post.cpu_set_mp.unchanged_except(&mid.cpu_set_mp, s)
                &&& post.cpu_set_mp.spec_index(s).lock_state_u() == mode
                &&& kernel_container_nonlock_fields_and_quotas_unchanged(pre, &mid)
            },
            None => kernel_container_nonlock_fields_and_quotas_unchanged(pre, post),
        },
    ensures
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            kernel_k_to_kernel_u(*post).container_map == match container {
                Some(c) => old_u.container_map.insert(c, ContainerU {
                    lock_state: mode, cpu_set_lock: if cpu_set_unlocked is Some { mode } else { old_u.container_map[c].cpu_set_lock }, ..old_u.container_map[c]
                }),
                None => old_u.container_map,
            }
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post); reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
    let old_u = kernel_k_to_kernel_u(*pre);
    let new_u = kernel_k_to_kernel_u(*post);
    assert_maps_equal!(new_u.container_map, match container {
        Some(c) => old_u.container_map.insert(c, ContainerU {
            lock_state: mode, cpu_set_lock: if cpu_set_unlocked is Some { mode } else { old_u.container_map[c].cpu_set_lock }, ..old_u.container_map[c]
        }),
        None => old_u.container_map,
    }, p => {
        if pre.ctn_mp.dom().contains(p) { kernel_container_projection_at(pre, p); } if post.ctn_mp.dom().contains(p) { kernel_container_projection_at(post, p); } reveal(container_cpu_set_wf);
    });
}

/// Only the lock modes of `process_ptr` and, with `pagetable`, of its pagetable changing, to `mode`, project to that process-map update.
pub proof fn kernel_process_lock_mode_changed_implies_u_process_map(pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, mode: LockStateU, pagetable: bool)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        post.it_mp == pre.it_mp,
        post.prc_mp.unchanged_except(&pre.prc_mp, process_ptr),
        post.prc_mp.spec_index(process_ptr).lock_state_u() == mode,
        kernel_process_nonlock_fields_unchanged(pre.prc_mp, post.prc_mp),
        kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, post.pt_mp),
        if pagetable {
            let table = post.prc_mp.spec_index(process_ptr).view().pagetable;
            &&& !post.prc_mp.spec_index(process_ptr).view().zombie
            &&& post.pt_mp.unchanged_except(&pre.pt_mp, table)
            &&& post.pt_mp.spec_index(table).lock_state_u() == mode
        } else { post.pt_mp == pre.pt_mp },
    ensures
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            kernel_k_to_kernel_u(*post).process_map == old_u.process_map.insert(process_ptr, ProcessU {
                lock_state: mode,
                pagetable: if pagetable { Some(PageTableU { lock_state: mode, ..old_u.process_map[process_ptr].pagetable->Some_0 }) } else { old_u.process_map[process_ptr].pagetable },
                ..old_u.process_map[process_ptr]
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post); reveal(kernel_process_nonlock_fields_unchanged);
    let old_u = kernel_k_to_kernel_u(*pre);
    let new_u = kernel_k_to_kernel_u(*post);
    assert_maps_equal!(new_u.process_map, old_u.process_map.insert(process_ptr, ProcessU {
        lock_state: mode,
        pagetable: if pagetable { Some(PageTableU { lock_state: mode, ..old_u.process_map[process_ptr].pagetable->Some_0 }) } else { old_u.process_map[process_ptr].pagetable },
        ..old_u.process_map[process_ptr]
    }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); }
        reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(process_pagetable_match);
    });
}

/// Only the lock mode of `thread_ptr` changing, to `mode`, projects to that thread-map update.
pub proof fn kernel_thread_lock_mode_changed_implies_u_thread_map(pre: &KernelK, post: &KernelK, thread_ptr: RwLockThreadPtr, mode: LockStateU)
    requires
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).lock_state_u() == mode,
        kernel_thread_nonlock_fields_unchanged(pre.thr_mp, post.thr_mp),
    ensures
        kernel_k_to_kernel_u(*post).thread_map == kernel_k_to_kernel_u(*pre).thread_map.insert(thread_ptr, ThreadU { lock_state: mode, ..kernel_k_to_kernel_u(*pre).thread_map.spec_index(thread_ptr) }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post); reveal(kernel_thread_nonlock_fields_unchanged);
    let old_u = kernel_k_to_kernel_u(*pre);
    let new_u = kernel_k_to_kernel_u(*post);
    assert_maps_equal!(new_u.thread_map, old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: mode, ..old_u.thread_map.spec_index(thread_ptr) }), t => {
        if pre.thr_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thr_mp.dom().contains(t) { kernel_thread_projection_at(post, t); }
    });
}

/// Only the lock mode of `endpoint_ptr`, if any, changing, to `mode`, projects to that endpoint-map update.
pub proof fn kernel_endpoint_lock_mode_changed_implies_u_endpoint_map(pre: &KernelK, post: &KernelK, endpoint_ptr: Option<RwLockEndpointPtr>, mode: LockStateU)
    requires
        match endpoint_ptr {
            Some(e) => post.ep_mp.unchanged_except(&pre.ep_mp, e) && post.ep_mp.spec_index(e).lock_state_u() == mode,
            None => post.ep_mp == pre.ep_mp,
        },
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
    ensures
        kernel_k_to_kernel_u(*post).endpoint_map == match endpoint_ptr {
            Some(e) => kernel_k_to_kernel_u(*pre).endpoint_map.insert(e, EndpointU { lock_state: mode, ..kernel_k_to_kernel_u(*pre).endpoint_map.spec_index(e) }),
            None => kernel_k_to_kernel_u(*pre).endpoint_map,
        },
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post); reveal(kernel_endpoint_nonlock_fields_unchanged);
    let old_u = kernel_k_to_kernel_u(*pre);
    let new_u = kernel_k_to_kernel_u(*post);
    match endpoint_ptr {
        Some(e) => {
            assert_maps_equal!(new_u.endpoint_map, old_u.endpoint_map.insert(e, EndpointU { lock_state: mode, ..old_u.endpoint_map.spec_index(e) }), p => {
                if pre.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(pre, p); } if post.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(post, p); }
            });
        },
        None => { assert_maps_equal!(new_u.endpoint_map, old_u.endpoint_map, p => {
            if pre.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(pre, p); } if post.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(post, p); }
        }); },
    }
}
} // verus!
