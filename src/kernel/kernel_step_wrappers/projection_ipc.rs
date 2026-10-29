use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal};
use crate::*;
#[cfg(verus_keep_ghost)]
use super::projection::kernel_lock_states_unchanged_implies_u_container_map;

verus! {
/// Dequeuing under held cpu/process/thread locks leaves the container projection unchanged.
#[verifier::spinoff_prover]
proof fn kernel_thread_dequeued_implies_u_container_map(before: &KernelK, entry: &KernelK, after: &KernelK)
    requires
        kernel_container_nonlock_fields_and_quotas_unchanged(before, entry),
        *after == (KernelK { thr_mp: after.thr_mp, ep_mp: after.ep_mp, ..*entry }),
        forall|p: RwLockContainerPtr| #![trigger after.ctn_mp.spec_index(p)] before.ctn_mp.dom().contains(p) && after.ctn_mp.dom().contains(p) ==> {
            &&& after.ctn_mp.spec_index(p).locking_thread() == before.ctn_mp.spec_index(p).locking_thread()
            &&& after.ctn_mp.spec_index(p).lock_process_owner_u() == before.ctn_mp.spec_index(p).lock_process_owner_u()
        },
    ensures kernel_k_to_kernel_u(*after).container_map == kernel_k_to_kernel_u(*before).container_map,
{
    kernel_u_domains_projection(after); kernel_u_domains_projection(before);
    assert_maps_equal!(kernel_k_to_kernel_u(*after).container_map, kernel_k_to_kernel_u(*before).container_map, p => {
        if after.ctn_mp.dom().contains(p) { kernel_container_projection_at(after, p); } if before.ctn_mp.dom().contains(p) { kernel_container_projection_at(before, p); }
        reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
    });
}

/// A process map with unchanged nonlock fields and lock states projects to the same process map.
#[verifier::spinoff_prover]
proof fn kernel_thread_dequeued_implies_u_process_map(before: &KernelK, entry: &KernelK, after: &KernelK, lctx: &LocalContext)
    requires
        process_pagetable_match(after.prc_mp, after.pt_mp),
        process_iommu_table_match(after.prc_mp, after.it_mp),
        typed_lock_maps_aligned(after, lctx),
        kernel_cpu_process_thread_nonlock_fields_unchanged(before, entry),
        *after == (KernelK { thr_mp: after.thr_mp, ep_mp: after.ep_mp, ..*entry }),
        forall|p: RwLockProcessPtr| #![trigger after.prc_mp.spec_index(p)] before.prc_mp.dom().contains(p) && after.prc_mp.dom().contains(p) ==>
            after.prc_mp.spec_index(p).locking_thread() == before.prc_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger after.pt_mp.spec_index(p)] before.pt_mp.dom().contains(p) && after.pt_mp.dom().contains(p) ==>
            after.pt_mp.spec_index(p).locking_thread() == before.pt_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger after.it_mp.spec_index(p)] before.it_mp.dom().contains(p) && after.it_mp.dom().contains(p) ==>
            after.it_mp.spec_index(p).locking_thread() == before.it_mp.spec_index(p).locking_thread(),
    ensures
        kernel_k_to_kernel_u(*after).process_map == kernel_k_to_kernel_u(*before).process_map,
{
    kernel_u_domains_projection(after); kernel_u_domains_projection(before);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    assert_maps_equal!(post.process_map, pre.process_map, p => {
        if after.prc_mp.dom().contains(p) { kernel_process_projection_at(after, p); } if before.prc_mp.dom().contains(p) { kernel_process_projection_at(before, p); }
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged);
        reveal(process_pagetable_match); reveal(process_iommu_table_match); reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
    });
}

/// Write-locking the cpu and both threads and dequeuing the channel head into transit with the running thread projects to that user
/// step; the channel ends write-locked exactly when `channel_held`.
#[verifier::spinoff_prover]
pub proof fn kernel_thread_dequeued_and_locks_changed_implies_u_step(
    before: &KernelK, entry: &KernelK, after: &KernelK, lctx: &LocalContext, cpu_id: CpuId,
    current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr, channel_endpoint_ptr: RwLockEndpointPtr, channel_held: bool,
)
    requires
        after.inv(),
        typed_lock_maps_aligned(after, lctx),
        before.cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        forall|i: CpuId| #![trigger after.cpu_op.view().view()[i as int]] index_valid(NUM_CPUS, i) && i != cpu_id ==> after.cpu_op.view().view()[i as int] == before.cpu_op.view().view()[i as int],
        entry.thr_mp.dom().contains(current_thread_ptr),
        entry.thr_mp.dom().contains(peer_thread_ptr),
        current_thread_ptr != peer_thread_ptr,
        kernel_cpu_process_thread_nonlock_fields_unchanged(before, entry),
        kernel_container_nonlock_fields_and_quotas_unchanged(before, entry),
        kernel_endpoint_nonlock_fields_unchanged(before.ep_mp, entry.ep_mp),
        before.irt.view().owners() == entry.irt.view().owners(),
        before.irt.view().iommu_roots() == entry.irt.view().iommu_roots(),
        before.cpu_tlb.view() == entry.cpu_tlb.view(),
        before.iommu_tlb.view() == entry.iommu_tlb.view(),
        *after == (KernelK { thr_mp: after.thr_mp, ep_mp: after.ep_mp, ..*entry }),
        after.thr_mp.dom() == entry.thr_mp.dom(),
        forall|t: RwLockThreadPtr| #![trigger after.thr_mp.spec_index(t)] entry.thr_mp.dom().contains(t) && t != current_thread_ptr && t != peer_thread_ptr ==>
            after.thr_mp.spec_index(t) == entry.thr_mp.spec_index(t),
        after.thr_mp.spec_index(current_thread_ptr).view() == (Thread {
            syscall_progress: after.thr_mp.spec_index(current_thread_ptr).view().syscall_progress, ..entry.thr_mp.spec_index(current_thread_ptr).view()
        }),
        after.thr_mp.spec_index(current_thread_ptr).being_killed() == entry.thr_mp.spec_index(current_thread_ptr).being_killed(),
        after.thr_mp.spec_index(peer_thread_ptr).view().non_ipc_fields_unchanged(&entry.thr_mp.spec_index(peer_thread_ptr).view()),
        after.thr_mp.spec_index(peer_thread_ptr).view().state == (ThreadState::IPC_TRANSIT { partner: current_thread_ptr, wait: if entry.thr_mp.spec_index(peer_thread_ptr).view().state is SENDING { IpcWait::Send } else { IpcWait::Receive } }),
        after.thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr is None,
        after.thr_mp.spec_index(peer_thread_ptr).view().caller == entry.thr_mp.spec_index(peer_thread_ptr).view().caller,
        after.thr_mp.spec_index(peer_thread_ptr).view().callee == entry.thr_mp.spec_index(peer_thread_ptr).view().callee,
        after.thr_mp.spec_index(peer_thread_ptr).view().ipc_payload == entry.thr_mp.spec_index(peer_thread_ptr).view().ipc_payload,
        after.thr_mp.spec_index(peer_thread_ptr).view().error_code == entry.thr_mp.spec_index(peer_thread_ptr).view().error_code,
        after.thr_mp.spec_index(peer_thread_ptr).view().trap_frame == entry.thr_mp.spec_index(peer_thread_ptr).view().trap_frame,
        after.thr_mp.spec_index(peer_thread_ptr).view().syscall_progress == entry.thr_mp.spec_index(peer_thread_ptr).view().syscall_progress,
        after.thr_mp.spec_index(peer_thread_ptr).being_killed() == entry.thr_mp.spec_index(peer_thread_ptr).being_killed(),
        after.ep_mp.unchanged_except(&entry.ep_mp, channel_endpoint_ptr),
        after.ep_mp.spec_index(channel_endpoint_ptr).view() == (Endpoint { queue: after.ep_mp.spec_index(channel_endpoint_ptr).view().queue, ..entry.ep_mp.spec_index(channel_endpoint_ptr).view() }),
        after.ep_mp.spec_index(channel_endpoint_ptr).view().queue.view() == entry.ep_mp.spec_index(channel_endpoint_ptr).view().queue.view().skip(1),
        after.ep_mp.spec_index(channel_endpoint_ptr).being_killed() == entry.ep_mp.spec_index(channel_endpoint_ptr).being_killed(),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        forall|p: RwLockContainerPtr| #![trigger after.ctn_mp.spec_index(p)] before.ctn_mp.dom().contains(p) && after.ctn_mp.dom().contains(p) ==> {
            &&& after.ctn_mp.spec_index(p).locking_thread() == before.ctn_mp.spec_index(p).locking_thread()
            &&& after.ctn_mp.spec_index(p).lock_process_owner_u() == before.ctn_mp.spec_index(p).lock_process_owner_u()
        },
        forall|p: RwLockProcessPtr| #![trigger after.prc_mp.spec_index(p)] before.prc_mp.dom().contains(p) && after.prc_mp.dom().contains(p) ==>
            after.prc_mp.spec_index(p).locking_thread() == before.prc_mp.spec_index(p).locking_thread(),
        forall|p: RwLockThreadPtr| #![trigger after.thr_mp.spec_index(p)] before.thr_mp.dom().contains(p) && after.thr_mp.dom().contains(p) && p != current_thread_ptr && p != peer_thread_ptr ==>
            after.thr_mp.spec_index(p).locking_thread() == before.thr_mp.spec_index(p).locking_thread(),
        forall|p: RwLockEndpointPtr| #![trigger after.ep_mp.spec_index(p)] before.ep_mp.dom().contains(p) && after.ep_mp.dom().contains(p) && !(channel_held && p == channel_endpoint_ptr) ==>
            after.ep_mp.spec_index(p).locking_thread() == before.ep_mp.spec_index(p).locking_thread(),
        channel_held ==> typed_lock_map_contains_mode(lctx.endpoint_lock_map(), channel_endpoint_ptr, TypedLockMode::Write),
        forall|p: RwLockPageTableRoot| #![trigger after.pt_mp.spec_index(p)] before.pt_mp.dom().contains(p) && after.pt_mp.dom().contains(p) ==>
            after.pt_mp.spec_index(p).locking_thread() == before.pt_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger after.it_mp.spec_index(p)] before.it_mp.dom().contains(p) && after.it_mp.dom().contains(p) ==>
            after.it_mp.spec_index(p).locking_thread() == before.it_mp.spec_index(p).locking_thread(),
        forall|i: CpuId| #![trigger after.cpu_arr.spec_index(i)] index_valid(NUM_CPUS, i) && i != cpu_id ==>
            after.cpu_arr.spec_index(i).value.locking_thread() == before.cpu_arr.spec_index(i).value.locking_thread(),
    ensures
        kernel_k_to_kernel_u(*before) != kernel_k_to_kernel_u(*after),
        kernel_k_to_kernel_u(*before).thread_map.dom().contains(current_thread_ptr),
        kernel_k_to_kernel_u(*before).thread_map[current_thread_ptr].syscall_progress == entry.thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view(),
        ({
            let pre = kernel_k_to_kernel_u(*before);
            let post = kernel_k_to_kernel_u(*after);
            post == (KernelU {
                cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, op: after.cpu_op.view().view()[cpu_id as int], ..pre.cpu_array[cpu_id as int] }),
                thread_map: pre.thread_map.insert(current_thread_ptr, ThreadU {
                    lock_state: LockStateU::WriteLocked, syscall_progress: after.thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view(), ..pre.thread_map[current_thread_ptr]
                }).insert(peer_thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, blocking_endpoint_ptr: None,
                    state: ThreadState::IPC_TRANSIT { partner: current_thread_ptr, wait: if pre.thread_map[peer_thread_ptr].state is SENDING { IpcWait::Send } else { IpcWait::Receive } }, ..pre.thread_map[peer_thread_ptr] }),
                endpoint_map: pre.endpoint_map.insert(channel_endpoint_ptr, EndpointU {
                    lock_state: if channel_held { LockStateU::WriteLocked } else { pre.endpoint_map[channel_endpoint_ptr].lock_state }, queue: pre.endpoint_map[channel_endpoint_ptr].queue.skip(1),
                    ..pre.endpoint_map[channel_endpoint_ptr]
                }),
                ..pre
            })
        }),
{
    assert(entry.dflt_pt == before.dflt_pt) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    if before.thr_mp.dom().contains(current_thread_ptr) { kernel_thread_projection_at(before, current_thread_ptr); }
    if before.thr_mp.dom().contains(peer_thread_ptr) { kernel_thread_projection_at(before, peer_thread_ptr); }
    if before.ep_mp.dom().contains(channel_endpoint_ptr) { kernel_endpoint_projection_at(before, channel_endpoint_ptr); }
    if index_valid(NUM_CPUS, cpu_id) { kernel_cpu_projection_at(before, cpu_id); }
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    after.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), current_thread_ptr);
    after.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), peer_thread_ptr);
    if channel_held { after.ep_mp.typed_lock_map_aligned_write_at(lctx.endpoint_lock_map(), lctx.thread_id(), channel_endpoint_ptr); }
    assert(index_valid(NUM_CPUS, cpu_id) && after.cpu_arr.spec_index(cpu_id).value.locking_thread() is Write) by { reveal(LockedArray::typed_lock_map_aligned); };
    assert(post.iommu_root_table == pre.iommu_root_table) by { reveal(IommuRootTable::user_view); };
    assert(pre.thread_map.dom().contains(current_thread_ptr) && pre.thread_map[current_thread_ptr].syscall_progress == entry.thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view()) by {
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
    };
    assert_seqs_equal!(post.cpu_array == pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, op: after.cpu_op.view().view()[cpu_id as int], ..pre.cpu_array[cpu_id as int] }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(before, i as usize); kernel_cpu_projection_at(after, i as usize); }
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
    });
    kernel_thread_dequeued_and_locks_changed_implies_u_thread_map(before, entry, after, current_thread_ptr, peer_thread_ptr);
    kernel_thread_dequeued_and_locks_changed_implies_u_endpoint_map(before, entry, after, channel_endpoint_ptr, channel_held);
    kernel_thread_dequeued_implies_u_container_map(before, entry, after);
    kernel_thread_dequeued_implies_u_process_map(before, entry, after, lctx);
}

/// Write-locking both threads, recording the running thread's progress, and moving the channel head into transit with
/// the running thread projects to exactly those two thread entries.
proof fn kernel_thread_dequeued_and_locks_changed_implies_u_thread_map(
    before: &KernelK, entry: &KernelK, after: &KernelK, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr,
)
    requires
        entry.thr_mp.dom().contains(current_thread_ptr),
        entry.thr_mp.dom().contains(peer_thread_ptr),
        current_thread_ptr != peer_thread_ptr,
        kernel_cpu_process_thread_nonlock_fields_unchanged(before, entry),
        after.thr_mp.dom() == entry.thr_mp.dom(),
        forall|t: RwLockThreadPtr| #![trigger after.thr_mp.spec_index(t)] entry.thr_mp.dom().contains(t) && t != current_thread_ptr && t != peer_thread_ptr ==>
            after.thr_mp.spec_index(t) == entry.thr_mp.spec_index(t),
        after.thr_mp.spec_index(current_thread_ptr).view() == (Thread {
            syscall_progress: after.thr_mp.spec_index(current_thread_ptr).view().syscall_progress, ..entry.thr_mp.spec_index(current_thread_ptr).view()
        }),
        after.thr_mp.spec_index(current_thread_ptr).being_killed() == entry.thr_mp.spec_index(current_thread_ptr).being_killed(),
        after.thr_mp.spec_index(current_thread_ptr).locking_thread() is Write,
        after.thr_mp.spec_index(peer_thread_ptr).view().non_ipc_fields_unchanged(&entry.thr_mp.spec_index(peer_thread_ptr).view()),
        after.thr_mp.spec_index(peer_thread_ptr).view().state == (ThreadState::IPC_TRANSIT { partner: current_thread_ptr, wait: if entry.thr_mp.spec_index(peer_thread_ptr).view().state is SENDING { IpcWait::Send } else { IpcWait::Receive } }),
        after.thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr is None,
        after.thr_mp.spec_index(peer_thread_ptr).view().caller == entry.thr_mp.spec_index(peer_thread_ptr).view().caller,
        after.thr_mp.spec_index(peer_thread_ptr).view().callee == entry.thr_mp.spec_index(peer_thread_ptr).view().callee,
        after.thr_mp.spec_index(peer_thread_ptr).view().ipc_payload == entry.thr_mp.spec_index(peer_thread_ptr).view().ipc_payload,
        after.thr_mp.spec_index(peer_thread_ptr).view().error_code == entry.thr_mp.spec_index(peer_thread_ptr).view().error_code,
        after.thr_mp.spec_index(peer_thread_ptr).view().trap_frame == entry.thr_mp.spec_index(peer_thread_ptr).view().trap_frame,
        after.thr_mp.spec_index(peer_thread_ptr).view().syscall_progress == entry.thr_mp.spec_index(peer_thread_ptr).view().syscall_progress,
        after.thr_mp.spec_index(peer_thread_ptr).being_killed() == entry.thr_mp.spec_index(peer_thread_ptr).being_killed(),
        after.thr_mp.spec_index(peer_thread_ptr).locking_thread() is Write,
        forall|p: RwLockThreadPtr| #![trigger after.thr_mp.spec_index(p)] before.thr_mp.dom().contains(p) && after.thr_mp.dom().contains(p) && p != current_thread_ptr && p != peer_thread_ptr ==>
            after.thr_mp.spec_index(p).locking_thread() == before.thr_mp.spec_index(p).locking_thread(),
    ensures
        ({
            let pre = kernel_k_to_kernel_u(*before);
            kernel_k_to_kernel_u(*after).thread_map == pre.thread_map.insert(current_thread_ptr, ThreadU {
                lock_state: LockStateU::WriteLocked, syscall_progress: after.thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view(), ..pre.thread_map[current_thread_ptr]
            }).insert(peer_thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, blocking_endpoint_ptr: None,
                state: ThreadState::IPC_TRANSIT { partner: current_thread_ptr, wait: if pre.thread_map[peer_thread_ptr].state is SENDING { IpcWait::Send } else { IpcWait::Receive } }, ..pre.thread_map[peer_thread_ptr] })
        }),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    assert_maps_equal!(post.thread_map, pre.thread_map.insert(current_thread_ptr, ThreadU {
        lock_state: LockStateU::WriteLocked, syscall_progress: after.thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view(), ..pre.thread_map[current_thread_ptr]
    }).insert(peer_thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, blocking_endpoint_ptr: None,
        state: ThreadState::IPC_TRANSIT { partner: current_thread_ptr, wait: if pre.thread_map[peer_thread_ptr].state is SENDING { IpcWait::Send } else { IpcWait::Receive } }, ..pre.thread_map[peer_thread_ptr] }), p => {
        if before.thr_mp.dom().contains(p) { kernel_thread_projection_at(before, p); } if after.thr_mp.dom().contains(p) { kernel_thread_projection_at(after, p); }
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
    });
}

/// Dequeuing the channel head projects to the channel endpoint with its queue advanced, write-locked exactly when
/// `channel_held`.
proof fn kernel_thread_dequeued_and_locks_changed_implies_u_endpoint_map(
    before: &KernelK, entry: &KernelK, after: &KernelK, channel_endpoint_ptr: RwLockEndpointPtr, channel_held: bool,
)
    requires
        kernel_endpoint_nonlock_fields_unchanged(before.ep_mp, entry.ep_mp),
        after.ep_mp.unchanged_except(&entry.ep_mp, channel_endpoint_ptr),
        after.ep_mp.spec_index(channel_endpoint_ptr).view() == (Endpoint { queue: after.ep_mp.spec_index(channel_endpoint_ptr).view().queue, ..entry.ep_mp.spec_index(channel_endpoint_ptr).view() }),
        after.ep_mp.spec_index(channel_endpoint_ptr).view().queue.view() == entry.ep_mp.spec_index(channel_endpoint_ptr).view().queue.view().skip(1),
        after.ep_mp.spec_index(channel_endpoint_ptr).being_killed() == entry.ep_mp.spec_index(channel_endpoint_ptr).being_killed(),
        forall|p: RwLockEndpointPtr| #![trigger after.ep_mp.spec_index(p)] before.ep_mp.dom().contains(p) && after.ep_mp.dom().contains(p) && !(channel_held && p == channel_endpoint_ptr) ==>
            after.ep_mp.spec_index(p).locking_thread() == before.ep_mp.spec_index(p).locking_thread(),
        channel_held ==> after.ep_mp.spec_index(channel_endpoint_ptr).locking_thread() is Write,
    ensures
        ({
            let pre = kernel_k_to_kernel_u(*before);
            kernel_k_to_kernel_u(*after).endpoint_map == pre.endpoint_map.insert(channel_endpoint_ptr, EndpointU {
                lock_state: if channel_held { LockStateU::WriteLocked } else { pre.endpoint_map[channel_endpoint_ptr].lock_state }, queue: pre.endpoint_map[channel_endpoint_ptr].queue.skip(1),
                ..pre.endpoint_map[channel_endpoint_ptr]
            })
        }),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    assert_maps_equal!(post.endpoint_map, pre.endpoint_map.insert(channel_endpoint_ptr, EndpointU {
        lock_state: if channel_held { LockStateU::WriteLocked } else { pre.endpoint_map[channel_endpoint_ptr].lock_state }, queue: pre.endpoint_map[channel_endpoint_ptr].queue.skip(1),
        ..pre.endpoint_map[channel_endpoint_ptr]
    }), p => {
        if before.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(before, p); } if after.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(after, p); }
        reveal(kernel_endpoint_nonlock_fields_unchanged);
    });
}

pub proof fn kernel_process_map_unchanged_implies_u_map(pre: &KernelK, post: &KernelK, lctx: &LocalContext)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        post.prc_mp.typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id()),
        kernel_process_nonlock_fields_unchanged(pre.prc_mp, post.prc_mp),
        kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view()),
        kernel_iommu_table_nonlock_fields_unchanged(pre.it_mp, post.it_mp),
        forall|p: RwLockProcessPtr| #![trigger pre.prc_mp.spec_index(p)] #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) && post.prc_mp.dom().contains(p) ==> post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger pre.it_mp.spec_index(p)] #![trigger post.it_mp.spec_index(p)]
            pre.it_mp.dom().contains(p) && post.it_mp.dom().contains(p) ==> post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger pre.pt_mp.spec_index(p)] #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) && post.pt_mp.dom().contains(p) ==> post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread(),
    ensures
        ({
            let before = kernel_k_to_kernel_u(*pre);
            let after = kernel_k_to_kernel_u(*post);
            after.process_map == before.process_map
        }),
{
    reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
    reveal(process_pagetable_match); reveal(process_iommu_table_match);
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    assert_maps_equal!(after.process_map, before.process_map, p => {
        if post.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); kernel_process_projection_at(post, p); }
    });
}

#[verifier::spinoff_prover]
pub proof fn kernel_pagetable_pair_lock_modes_changed_implies_u_map(pre: &KernelK, post: &KernelK, lctx: &LocalContext, source: RwLockProcessPtr, target: RwLockProcessPtr)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        post.prc_mp.typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id()),
        post.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        kernel_process_nonlock_fields_unchanged(pre.prc_mp, post.prc_mp),
        kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view()),
        kernel_iommu_table_nonlock_fields_unchanged(pre.it_mp, post.it_mp),
        forall|p: RwLockProcessPtr| #![trigger pre.prc_mp.spec_index(p)] #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) && post.prc_mp.dom().contains(p) ==> post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger pre.it_mp.spec_index(p)] #![trigger post.it_mp.spec_index(p)]
            pre.it_mp.dom().contains(p) && post.it_mp.dom().contains(p) ==> post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger pre.pt_mp.spec_index(p)] #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) && post.pt_mp.dom().contains(p) && (p != pre.prc_mp.spec_index(source).view().pagetable && p != pre.prc_mp.spec_index(target).view().pagetable) ==> post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread(),
        source != target,
        pre.prc_mp.dom().contains(source),
        pre.prc_mp.dom().contains(target),
        !pre.prc_mp.spec_index(source).view().zombie,
        !pre.prc_mp.spec_index(target).view().zombie,
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pre.prc_mp.spec_index(source).view().pagetable, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pre.prc_mp.spec_index(target).view().pagetable, TypedLockMode::Write),
    ensures
        ({
            let before = kernel_k_to_kernel_u(*pre);
            let after = kernel_k_to_kernel_u(*post);
            let processes = before.process_map;
            let locked_processes = processes.insert(source, ProcessU {
                pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..processes[source].pagetable->Some_0 }), ..processes[source]
            }).insert(target, ProcessU {
                pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..processes[target].pagetable->Some_0 }), ..processes[target]
            });
            after.process_map == locked_processes
        }),
{
    post.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pre.prc_mp.spec_index(source).view().pagetable);
    post.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pre.prc_mp.spec_index(target).view().pagetable);
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    let processes = before.process_map;
    let locked_processes = processes.insert(source, ProcessU {
        pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..processes[source].pagetable->Some_0 }), ..processes[source]
    }).insert(target, ProcessU {
        pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..processes[target].pagetable->Some_0 }), ..processes[target]
    });
    reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
    reveal(process_pagetable_match); reveal(process_iommu_table_match);
    assert_maps_equal!(after.process_map, locked_processes, p => {
        if post.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); kernel_process_projection_at(post, p); }
    });
}

#[verifier::spinoff_prover]
pub proof fn kernel_cpu_and_two_threads_lock_modes_changed_implies_u_step(
    pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu: CpuId,
    caller: RwLockThreadPtr, peer: RwLockThreadPtr, endpoint: RwLockEndpointPtr, tables: Option<(RwLockProcessPtr, RwLockProcessPtr)>,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        typed_lock_maps_aligned(post, lctx),
        index_valid(NUM_CPUS, cpu),
        forall|i: CpuId| #![trigger post.cpu_op.view().view()[i as int]] index_valid(NUM_CPUS, i) && i != cpu ==> post.cpu_op.view().view()[i as int] == pre.cpu_op.view().view()[i as int],
        pre.thr_mp.dom().contains(caller),
        pre.thr_mp.dom().contains(peer),
        pre.ep_mp.dom().contains(endpoint),
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post),
        kernel_container_nonlock_fields_and_quotas_unchanged(pre, post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        pre.irt.view().owners() == post.irt.view().owners(),
        pre.irt.view().iommu_roots() == post.irt.view().iommu_roots(),
        pre.cpu_tlb.view() == post.cpu_tlb.view(),
        pre.iommu_tlb.view() == post.iommu_tlb.view(),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), caller, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), peer, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.endpoint_lock_map(), endpoint, TypedLockMode::Write),
        tables matches Some((source, target)) ==> {
            &&& source != target
            &&& pre.prc_mp.dom().contains(source) && pre.prc_mp.dom().contains(target)
            &&& !pre.prc_mp.spec_index(source).view().zombie && !pre.prc_mp.spec_index(target).view().zombie
            &&& typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pre.prc_mp.spec_index(source).view().pagetable, TypedLockMode::Write)
            &&& typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pre.prc_mp.spec_index(target).view().pagetable, TypedLockMode::Write)
        },
        forall|i: CpuId| #![trigger pre.cpu_arr.spec_index(i)] #![trigger post.cpu_arr.spec_index(i)] index_valid(NUM_CPUS, i) && i != cpu ==>
            post.cpu_arr.spec_index(i).value.locking_thread() == pre.cpu_arr.spec_index(i).value.locking_thread(),
        forall|p: RwLockContainerPtr| #![trigger pre.ctn_mp.spec_index(p)] #![trigger post.ctn_mp.spec_index(p)]
            pre.ctn_mp.dom().contains(p) && post.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).locking_thread() == pre.ctn_mp.spec_index(p).locking_thread() && post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
        forall|p: RwLockProcessPtr| #![trigger pre.prc_mp.spec_index(p)] #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) && post.prc_mp.dom().contains(p) ==> post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread(),
        forall|p: RwLockThreadPtr| #![trigger pre.thr_mp.spec_index(p)] #![trigger post.thr_mp.spec_index(p)]
            pre.thr_mp.dom().contains(p) && post.thr_mp.dom().contains(p) && p != caller && p != peer ==> post.thr_mp.spec_index(p).locking_thread() == pre.thr_mp.spec_index(p).locking_thread(),
        forall|p: RwLockEndpointPtr| #![trigger pre.ep_mp.spec_index(p)] #![trigger post.ep_mp.spec_index(p)]
            pre.ep_mp.dom().contains(p) && post.ep_mp.dom().contains(p) && p != endpoint ==> post.ep_mp.spec_index(p).locking_thread() == pre.ep_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger pre.it_mp.spec_index(p)] #![trigger post.it_mp.spec_index(p)]
            pre.it_mp.dom().contains(p) && post.it_mp.dom().contains(p) ==> post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger pre.pt_mp.spec_index(p)] #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) && post.pt_mp.dom().contains(p) && (tables is None || p != pre.prc_mp.spec_index(tables->Some_0.0).view().pagetable && p != pre.prc_mp.spec_index(tables->Some_0.1).view().pagetable)
                ==> post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread(),
    ensures
        kernel_k_to_kernel_u(*pre).thread_map[caller].owning_proc == pre.thr_mp.spec_index(caller).view().owning_proc,
        kernel_k_to_kernel_u(*pre).thread_map[peer].owning_proc == pre.thr_mp.spec_index(peer).view().owning_proc,
        kernel_k_to_kernel_u(*pre).thread_map[caller].owning_container == pre.thr_mp.spec_index(caller).view().owning_container,
        kernel_k_to_kernel_u(*pre).thread_map[peer].owning_container == pre.thr_mp.spec_index(peer).view().owning_container,
        pre.cpu_arr.spec_index(cpu).value.locking_thread() is None ==> kernel_k_to_kernel_u(*pre).cpu_array[cpu as int].lock_state is Unlocked,
        kernel_k_to_kernel_u(*post).cpu_array[cpu as int].lock_state is WriteLocked,
        ({
            let before = kernel_k_to_kernel_u(*pre);
            let processes = before.process_map;
            let locked_processes = match tables {
                None => processes,
                Some((source, target)) => processes.insert(source, ProcessU {
                    pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..processes[source].pagetable->Some_0 }), ..processes[source]
                }).insert(target, ProcessU {
                    pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..processes[target].pagetable->Some_0 }), ..processes[target]
                }),
            };
            kernel_k_to_kernel_u(*post) == (KernelU {
                cpu_array: before.cpu_array.update(cpu as int, CpuU { lock_state: LockStateU::WriteLocked, op: post.cpu_op.view().view()[cpu as int], ..before.cpu_array[cpu as int] }),
                process_map: locked_processes,
                thread_map: before.thread_map.insert(caller, ThreadU { lock_state: LockStateU::WriteLocked, ..before.thread_map[caller] }).insert(peer, ThreadU { lock_state: LockStateU::WriteLocked, ..before.thread_map[peer] }),
                endpoint_map: before.endpoint_map.insert(endpoint, EndpointU { lock_state: LockStateU::WriteLocked, ..before.endpoint_map[endpoint] }),
                ..before
            })
        }),
{
    assert(post.dflt_pt == pre.dflt_pt) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
    post.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), caller);
    post.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), peer);
    post.ep_mp.typed_lock_map_aligned_write_at(lctx.endpoint_lock_map(), lctx.thread_id(), endpoint);
    assert(post.cpu_arr.spec_index(cpu).value.locking_thread() is Write) by { reveal(LockedArray::typed_lock_map_aligned); };
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    let processes = before.process_map;
    let locked_processes = match tables {
        None => processes,
        Some((source, target)) => processes.insert(source, ProcessU {
            pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..processes[source].pagetable->Some_0 }), ..processes[source]
        }).insert(target, ProcessU {
            pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..processes[target].pagetable->Some_0 }), ..processes[target]
        }),
    };
    if index_valid(NUM_CPUS, cpu) { kernel_cpu_projection_at(pre, cpu); } if index_valid(NUM_CPUS, cpu) { kernel_cpu_projection_at(post, cpu); }
    if pre.thr_mp.dom().contains(caller) { kernel_thread_projection_at(pre, caller); } if post.thr_mp.dom().contains(caller) { kernel_thread_projection_at(post, caller); }
    if pre.thr_mp.dom().contains(peer) { kernel_thread_projection_at(pre, peer); } if post.thr_mp.dom().contains(peer) { kernel_thread_projection_at(post, peer); }
    if pre.ep_mp.dom().contains(endpoint) { kernel_endpoint_projection_at(pre, endpoint); }
    assert_seqs_equal!(after.cpu_array == before.cpu_array.update(cpu as int, CpuU { lock_state: LockStateU::WriteLocked, op: post.cpu_op.view().view()[cpu as int], ..before.cpu_array[cpu as int] }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); }
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
    });
    assert(after.process_map == locked_processes) by {
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
        match tables {
            Some((source, target)) => kernel_pagetable_pair_lock_modes_changed_implies_u_map(pre, post, lctx, source, target),
            None => kernel_process_map_unchanged_implies_u_map(pre, post, lctx),
        }
    };
    kernel_lock_states_unchanged_implies_u_container_map(pre, post);
    kernel_two_threads_write_locked_implies_u_thread_map(pre, post, caller, peer);
    kernel_endpoint_write_locked_implies_u_endpoint_map(pre, post, endpoint);
    assert(after.iommu_root_table == before.iommu_root_table) by { reveal(IommuRootTable::user_view); };
}

/// Write-locking `caller` and `peer`, all other thread locks and nonlock thread fields unchanged, projects to those two
/// thread-map lock-state updates.
proof fn kernel_two_threads_write_locked_implies_u_thread_map(pre: &KernelK, post: &KernelK, caller: RwLockThreadPtr, peer: RwLockThreadPtr)
    requires
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post),
        pre.thr_mp.dom().contains(caller) && pre.thr_mp.dom().contains(peer),
        post.thr_mp.spec_index(caller).locking_thread() is Write && post.thr_mp.spec_index(peer).locking_thread() is Write,
        forall|p: RwLockThreadPtr| #![trigger pre.thr_mp.spec_index(p)] #![trigger post.thr_mp.spec_index(p)]
            pre.thr_mp.dom().contains(p) && post.thr_mp.dom().contains(p) && p != caller && p != peer ==> post.thr_mp.spec_index(p).locking_thread() == pre.thr_mp.spec_index(p).locking_thread(),
    ensures
        ({
            let before = kernel_k_to_kernel_u(*pre);
            kernel_k_to_kernel_u(*post).thread_map == before.thread_map.insert(caller, ThreadU { lock_state: LockStateU::WriteLocked, ..before.thread_map[caller] }).insert(peer, ThreadU { lock_state: LockStateU::WriteLocked, ..before.thread_map[peer] })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    assert_maps_equal!(after.thread_map, before.thread_map.insert(caller, ThreadU { lock_state: LockStateU::WriteLocked, ..before.thread_map[caller] })
        .insert(peer, ThreadU { lock_state: LockStateU::WriteLocked, ..before.thread_map[peer] }), p => {
            if pre.thr_mp.dom().contains(p) { kernel_thread_projection_at(pre, p); } if post.thr_mp.dom().contains(p) { kernel_thread_projection_at(post, p); }
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
        });
}

/// Write-locking `endpoint`, all other endpoint locks and nonlock endpoint fields unchanged, projects to that
/// endpoint-map lock-state update.
proof fn kernel_endpoint_write_locked_implies_u_endpoint_map(pre: &KernelK, post: &KernelK, endpoint: RwLockEndpointPtr)
    requires
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        pre.ep_mp.dom().contains(endpoint),
        post.ep_mp.spec_index(endpoint).locking_thread() is Write,
        forall|p: RwLockEndpointPtr| #![trigger pre.ep_mp.spec_index(p)] #![trigger post.ep_mp.spec_index(p)]
            pre.ep_mp.dom().contains(p) && post.ep_mp.dom().contains(p) && p != endpoint ==> post.ep_mp.spec_index(p).locking_thread() == pre.ep_mp.spec_index(p).locking_thread(),
    ensures
        kernel_k_to_kernel_u(*post).endpoint_map == kernel_k_to_kernel_u(*pre).endpoint_map.insert(endpoint, EndpointU { lock_state: LockStateU::WriteLocked, ..kernel_k_to_kernel_u(*pre).endpoint_map[endpoint] }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    assert_maps_equal!(after.endpoint_map, before.endpoint_map.insert(endpoint, EndpointU { lock_state: LockStateU::WriteLocked, ..before.endpoint_map[endpoint] }), p => {
        if pre.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(pre, p); } if post.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(post, p); }
        reveal(kernel_endpoint_nonlock_fields_unchanged);
    });
}

#[verifier::spinoff_prover]
pub proof fn kernel_cpu_process_thread_endpoint_lock_modes_changed_implies_u_step(
    pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    endpoint_ptr: Option<RwLockEndpointPtr>, write_locked: bool, container: Option<RwLockContainerPtr>, pagetable: bool, cpu_set_unlocked: Option<KernelK>,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        typed_lock_maps_aligned(post, lctx),
        index_valid(NUM_CPUS, cpu_id),
        *post == (KernelK { cpu_arr: post.cpu_arr, cpu_op: post.cpu_op, prc_mp: post.prc_mp, thr_mp: post.thr_mp, ep_mp: post.ep_mp, sched_mp: post.sched_mp, ctn_mp: post.ctn_mp, pt_mp: post.pt_mp, pcid_allc_mp: post.pcid_allc_mp, cpu_set_mp: post.cpu_set_mp, ..*pre }),
        match container {
            Some(c) => {
                &&& pre.ctn_mp.dom().contains(c)
                &&& post.ctn_mp.unchanged_except(&pre.ctn_mp, c)
                &&& if write_locked { typed_lock_map_contains_mode(lctx.container_lock_map(), c, TypedLockMode::Write) } else { post.ctn_mp.spec_index(c).locking_thread() is None }
            },
            None => post.ctn_mp == pre.ctn_mp,
        },
        if pagetable {
            let table = post.prc_mp.spec_index(process_ptr).view().pagetable;
            &&& !post.prc_mp.spec_index(process_ptr).view().zombie
            &&& post.pt_mp.unchanged_except(&pre.pt_mp, table)
            &&& if write_locked { typed_lock_map_contains_mode(lctx.pagetable_lock_map(), table, TypedLockMode::Write) } else { post.pt_mp.spec_index(table).locking_thread() is None }
        } else { post.pt_mp == pre.pt_mp },
        post.cpu_arr.entries_unchanged_except(&pre.cpu_arr, cpu_id),
        forall|i: CpuId| #![trigger post.cpu_op.view().view()[i as int]] index_valid(NUM_CPUS, i) && i != cpu_id ==> post.cpu_op.view().view()[i as int] == pre.cpu_op.view().view()[i as int],
        post.prc_mp.unchanged_except(&pre.prc_mp, process_ptr),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        match endpoint_ptr { Some(e) => post.ep_mp.unchanged_except(&pre.ep_mp, e), None => post.ep_mp == pre.ep_mp },
        if write_locked { typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write) } else { post.cpu_arr.spec_index(cpu_id).value.locking_thread() is None },
        if write_locked { typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write) } else { post.prc_mp.spec_index(process_ptr).locking_thread() is None },
        if write_locked { typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write) } else { post.thr_mp.spec_index(thread_ptr).locking_thread() is None },
        endpoint_ptr is Some ==> if write_locked { typed_lock_map_contains_mode(lctx.endpoint_lock_map(), endpoint_ptr->Some_0, TypedLockMode::Write) } else { post.ep_mp.spec_index(endpoint_ptr->Some_0).locking_thread() is None },
        match cpu_set_unlocked {
            Some(mid) => {
                let s = post.ctn_mp.spec_index(container->Some_0).view_rodata().view().cpu_set;
                &&& container is Some
                &&& container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)
                &&& *post == (KernelK { cpu_set_mp: post.cpu_set_mp, ..mid })
                &&& post.cpu_set_mp.unchanged_except(&mid.cpu_set_mp, s)
                &&& post.cpu_set_mp.spec_index(s).being_killed() == mid.cpu_set_mp.spec_index(s).being_killed()
                &&& if write_locked { typed_lock_map_contains_mode(lctx.cpu_set_lock_map(), s, TypedLockMode::Write) } else { post.cpu_set_mp.spec_index(s).locking_thread() is None }
                &&& kernel_container_nonlock_fields_and_quotas_unchanged(pre, &mid)
            },
            None => kernel_container_nonlock_fields_and_quotas_unchanged(pre, post),
        },
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
    ensures
        forall|c: CpuId| #![trigger kernel_k_to_kernel_u(*pre).cpu_array[c as int]] index_valid(NUM_CPUS, c) ==> kernel_k_to_kernel_u(*pre).cpu_array[c as int] == (CpuU {
            lock_state: pre.cpu_arr.spec_index(c).value.lock_state_u(), owning_container: pre.cpu_arr.spec_index(c).value.view().view().owning_container,
            state: pre.cpu_arr.spec_index(c).value.view().view().state, current_process: pre.cpu_arr.spec_index(c).value.view().view().current_process,
            current_thread: pre.cpu_arr.spec_index(c).value.view().view().current_thread, killed: pre.cpu_arr.spec_index(c).value.being_killed(),
            op: pre.cpu_op.view().view()[c as int],
        }),
        pagetable && post.inv() ==> kernel_k_to_kernel_u(*pre).kernel_l4_end == post.pt_mp.spec_index(post.prc_mp.spec_index(process_ptr).view().pagetable).view().kernel_l4_end,
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let mode = if write_locked { LockStateU::WriteLocked } else { LockStateU::Unlocked };
            kernel_k_to_kernel_u(*post) == (KernelU {
                cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, op: post.cpu_op.view().view()[cpu_id as int], ..old_u.cpu_array[cpu_id as int] }),
                container_map: match container {
                    Some(c) => old_u.container_map.insert(c, ContainerU {
                        lock_state: mode, lock_process_owner: if write_locked { post.ctn_mp.spec_index(c).lock_process_owner_u() } else { None },
                        cpu_set_lock: if cpu_set_unlocked is Some { mode } else { old_u.container_map[c].cpu_set_lock }, ..old_u.container_map[c]
                    }),
                    None => old_u.container_map,
                },
                process_map: old_u.process_map.insert(process_ptr, ProcessU {
                    lock_state: mode,
                    pagetable: if pagetable { Some(PageTableU { lock_state: mode, ..old_u.process_map[process_ptr].pagetable->Some_0 }) } else { old_u.process_map[process_ptr].pagetable },
                    ..old_u.process_map[process_ptr]
                }),
                thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: mode, ..old_u.thread_map.spec_index(thread_ptr) }),
                endpoint_map: match endpoint_ptr {
                    Some(e) => old_u.endpoint_map.insert(e, EndpointU { lock_state: mode, ..old_u.endpoint_map.spec_index(e) }),
                    None => old_u.endpoint_map,
                },
                ..old_u
            })
        }),
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let c = post.cpu_arr.spec_index(cpu_id).value.view().view();
            let thread = post.thr_mp.spec_index(thread_ptr);
            let t = thread.view();
            &&& old_u.cpu_array[cpu_id as int] == (CpuU {
                lock_state: pre.cpu_arr.spec_index(cpu_id).value.lock_state_u(), owning_container: c.owning_container, state: c.state,
                current_process: c.current_process, current_thread: c.current_thread, killed: post.cpu_arr.spec_index(cpu_id).value.being_killed(),
                op: pre.cpu_op.view().view()[cpu_id as int],
            })
            &&& old_u.cpu_array.len() == NUM_CPUS
            &&& old_u.container_map.dom() == post.ctn_mp.dom()
            &&& old_u.process_map.dom() == post.prc_mp.dom()
            &&& old_u.thread_map.dom() == post.thr_mp.dom()
            &&& old_u.endpoint_map.dom() == post.ep_mp.dom()
            &&& old_u.process_map.spec_index(process_ptr).lock_state == pre.prc_mp.spec_index(process_ptr).lock_state_u()
            &&& old_u.process_map.spec_index(process_ptr).killed == post.prc_mp.spec_index(process_ptr).being_killed()
            &&& old_u.thread_map.spec_index(thread_ptr) == (ThreadU {
                lock_state: pre.thr_mp.spec_index(thread_ptr).lock_state_u(), state: t.state, caller: t.caller, callee: t.callee,
                owning_container: t.owning_container, owning_proc: t.owning_proc, last_cpu: t.last_cpu, quota_4k: t.quota_4k, quota_2m: t.quota_2m, quota_1g: t.quota_1g,
                endpoint_descriptors: t.endpoint_descriptors.view(), blocking_endpoint_ptr: t.blocking_endpoint_ptr, ipc_payload: t.ipc_payload,
                error_code: t.error_code, trap_frame: if t.trap_frame.is_some() { Some(*t.trap_frame.get_some_0()) } else { None },
                syscall_progress: t.syscall_progress.view(), killed: thread.being_killed(),
            })
            &&& endpoint_ptr is Some ==> old_u.endpoint_map.spec_index(endpoint_ptr->Some_0).lock_state == pre.ep_mp.spec_index(endpoint_ptr->Some_0).lock_state_u()
            &&& container matches Some(c) ==> {
                &&& old_u.container_map[c].lock_state == pre.ctn_mp.spec_index(c).lock_state_u()
                &&& cpu_set_unlocked is Some ==> old_u.container_map[c].cpu_set_lock == pre.cpu_set_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().cpu_set).lock_state_u()
                &&& old_u.container_map[c].killed == post.ctn_mp.spec_index(c).being_killed()
                &&& old_u.container_map[c].zombie == post.ctn_mp.spec_index(c).view().zombie
                &&& old_u.container_map[c].depth == post.ctn_mp.spec_index(c).view_rodata().view().depth
                &&& old_u.container_map[c].free_pcids == PcidAllocator::free_pcids(post.pcid_allc_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator).view().ref_counters.view())
            }
            &&& pagetable ==> {
                let table = post.prc_mp.spec_index(process_ptr).view().pagetable;
                &&& old_u.process_map.spec_index(process_ptr).pagetable is Some
                &&& old_u.process_map.spec_index(process_ptr).pagetable->Some_0.lock_state == pre.pt_mp.spec_index(table).lock_state_u()
                &&& old_u.process_map.spec_index(process_ptr).pagetable->Some_0.mapping_4k == pagetable_c(post.pt_mp, post.pt_lower.view(), table).user_view(LockStateU::Unlocked).mapping_4k
            }
        }),
{
    kernel_u_cpu_array_projection(pre);
    if pagetable && post.inv() { reveal(KernelK::default_pagetable_wf); }
    if write_locked {
        if let Some(c) = container { post.ctn_mp.typed_lock_map_aligned_write_at(lctx.container_lock_map(), lctx.thread_id(), c); }
        if cpu_set_unlocked is Some {
            post.cpu_set_mp.typed_lock_map_aligned_write_at(lctx.cpu_set_lock_map(), lctx.thread_id(), post.ctn_mp.spec_index(container->Some_0).view_rodata().view().cpu_set);
        }
        if pagetable { post.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), post.prc_mp.spec_index(process_ptr).view().pagetable); }
        post.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), process_ptr);
        post.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr);
        if endpoint_ptr is Some { post.ep_mp.typed_lock_map_aligned_write_at(lctx.endpoint_lock_map(), lctx.thread_id(), endpoint_ptr->Some_0); }
        assert(post.cpu_arr.spec_index(cpu_id).value.locking_thread() is Write) by { reveal(LockedArray::typed_lock_map_aligned); };
    }
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post); reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
    reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
    reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
    let mode = if write_locked { LockStateU::WriteLocked } else { LockStateU::Unlocked };
    kernel_cpu_lock_mode_changed_implies_u_cpu_array(pre, post, cpu_id, mode);
    kernel_container_lock_mode_changed_implies_u_container_map(pre, post, container, mode, cpu_set_unlocked);
    kernel_process_lock_mode_changed_implies_u_process_map(pre, post, process_ptr, mode, pagetable);
    kernel_thread_lock_mode_changed_implies_u_thread_map(pre, post, thread_ptr, mode);
    kernel_endpoint_lock_mode_changed_implies_u_endpoint_map(pre, post, endpoint_ptr, mode);
    kernel_cpu_projection_at(pre, cpu_id);
    if pre.prc_mp.dom().contains(process_ptr) { kernel_process_projection_at(pre, process_ptr); } if post.prc_mp.dom().contains(process_ptr) { kernel_process_projection_at(post, process_ptr); }
    if pre.thr_mp.dom().contains(thread_ptr) { kernel_thread_projection_at(pre, thread_ptr); }
    if let Some(c) = container { if pre.ctn_mp.dom().contains(c) { kernel_container_projection_at(pre, c); } }
    if pre.ep_mp.dom().contains(endpoint_ptr->Some_0) { kernel_endpoint_projection_at(pre, endpoint_ptr->Some_0); }
}

#[verifier::spinoff_prover]
pub(super) proof fn kernel_ipc_block_fields_implies_u_step(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    waiting_state: ThreadState, payload: IPCPayLoad, regs: Registers, flushed_default_pcid: bool, include_lock_state: bool,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        kernel_ipc_block_fields(pre, post, cpu_id, thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, regs, flushed_default_pcid),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)] pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
    ensures
        kernel_u_ipc_block_changed(kernel_k_user_projection(*pre, include_lock_state), kernel_k_user_projection(*post, include_lock_state),
            cpu_id, thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, regs, flushed_default_pcid),
{
    hide(kernel_k_user_projection);
    reveal(kernel_u_ipc_block_changed); reveal(kernel_ipc_block_fields); kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    kernel_cpu_user_projection_at(pre, include_lock_state, cpu_id); if pre.thr_mp.dom().contains(thread_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, thread_ptr); }
    if pre.ep_mp.dom().contains(endpoint_ptr) { kernel_endpoint_user_projection_at(pre, include_lock_state, endpoint_ptr); }
    if pre.prc_mp.dom().contains(pre.thr_mp.spec_index(thread_ptr).view().owning_proc) { kernel_process_user_projection_at(pre, include_lock_state, pre.thr_mp.spec_index(thread_ptr).view().owning_proc); }
    kernel_cpu_state_set_and_current_cleared_implies_u_cpu_array(pre, post, cpu_id, CpuState::Idle, include_lock_state);
    kernel_container_nonlock_fields_and_locks_unchanged_implies_u_container_map(pre, post, include_lock_state);
    kernel_process_nonlock_fields_and_locks_unchanged_implies_u_process_map(pre, post, include_lock_state);
    kernel_ipc_block_fields_implies_u_thread_map(pre, post, cpu_id, thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, regs, flushed_default_pcid, include_lock_state);
    kernel_ipc_block_fields_implies_u_endpoint_map(pre, post, cpu_id, thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, regs, flushed_default_pcid, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { pre.irt.view().user_view_unfold(); post.irt.view().user_view_unfold(); };
}

#[verifier::spinoff_prover]
pub(super) proof fn kernel_ipc_call_handoff_fields_implies_u_step(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, caller_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    callee_ptr: RwLockThreadPtr, regs: Registers, flushed_pcid: Option<Pcid>, include_lock_state: bool,
)
    requires
        post.inv(),
        kernel_ipc_call_handoff_fields(pre, post, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, regs, flushed_pcid),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)] pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
    ensures
        kernel_u_ipc_call_handoff_changed(kernel_k_user_projection(*pre, include_lock_state), kernel_k_user_projection(*post, include_lock_state),
            cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, regs, flushed_pcid),
{
    hide(kernel_k_user_projection);
    reveal(kernel_u_ipc_call_handoff_changed); reveal(kernel_ipc_call_handoff_fields);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    kernel_cpu_user_projection_at(pre, include_lock_state, cpu_id);
    if pre.thr_mp.dom().contains(caller_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, caller_ptr); } if pre.thr_mp.dom().contains(callee_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, callee_ptr); }
    if pre.ep_mp.dom().contains(endpoint_ptr) { kernel_endpoint_user_projection_at(pre, include_lock_state, endpoint_ptr); }
    if pre.prc_mp.dom().contains(pre.thr_mp.spec_index(caller_ptr).view().owning_proc) { kernel_process_user_projection_at(pre, include_lock_state, pre.thr_mp.spec_index(caller_ptr).view().owning_proc); }
    kernel_ipc_call_handoff_fields_implies_u_cpu_array(pre, post, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, regs, flushed_pcid, include_lock_state);
    kernel_container_nonlock_fields_and_locks_unchanged_implies_u_container_map(pre, post, include_lock_state);
    kernel_process_nonlock_fields_and_locks_unchanged_implies_u_process_map(pre, post, include_lock_state);
    kernel_ipc_call_handoff_fields_implies_u_thread_map(pre, post, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, regs, flushed_pcid, include_lock_state);
    kernel_ipc_call_handoff_fields_implies_u_endpoint_map(pre, post, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, regs, flushed_pcid, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { pre.irt.view().user_view_unfold(); post.irt.view().user_view_unfold(); };
    if let Some(pcid) = flushed_pcid { kernel_cpu_tlb_within_may_cache_projection(post, include_lock_state, cpu_id, pcid, post.cpu_tlb.spec_index((cpu_id, pcid))); }
}

#[verifier::spinoff_prover]
pub(super) proof fn kernel_ipc_accept_call_fields_implies_u_step(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    caller_ptr: RwLockThreadPtr, include_lock_state: bool,
)
    requires
        kernel_ipc_accept_call_fields(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr),
    ensures
        kernel_u_ipc_accept_call_changed(kernel_k_user_projection(*pre, include_lock_state), kernel_k_user_projection(*post, include_lock_state),
            cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr),
{
    hide(kernel_k_user_projection);
    reveal(kernel_u_ipc_accept_call_changed);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    reveal(kernel_ipc_accept_call_fields); kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    kernel_cpu_user_projection_at(pre, include_lock_state, cpu_id); if pre.thr_mp.dom().contains(callee_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, callee_ptr); }
    if pre.thr_mp.dom().contains(caller_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, caller_ptr); }
    if pre.ep_mp.dom().contains(endpoint_ptr) { kernel_endpoint_user_projection_at(pre, include_lock_state, endpoint_ptr); }
    if pre.prc_mp.dom().contains(pre.thr_mp.spec_index(callee_ptr).view().owning_proc) { kernel_process_user_projection_at(pre, include_lock_state, pre.thr_mp.spec_index(callee_ptr).view().owning_proc); }
    let callee = pre_u.thread_map.spec_index(callee_ptr);
    let caller = pre_u.thread_map.spec_index(caller_ptr);
    let endpoint = pre_u.endpoint_map.spec_index(endpoint_ptr);
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, include_lock_state, i as usize); kernel_cpu_user_projection_at(post, include_lock_state, i as usize); } });
    assert_maps_equal!(post_u.container_map, pre_u.container_map, c => { if pre.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(pre, include_lock_state, c); } if post.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(post, include_lock_state, c); } });
    assert_maps_equal!(post_u.process_map, pre_u.process_map, p => { if pre.prc_mp.dom().contains(p) { kernel_process_user_projection_at(pre, include_lock_state, p); } if post.prc_mp.dom().contains(p) { kernel_process_user_projection_at(post, include_lock_state, p); } });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(callee_ptr, ThreadU { caller: Some(caller_ptr), ..callee }).insert(caller_ptr, ThreadU {
        state: ThreadState::WAITING_REPLY, callee: Some(callee_ptr), blocking_endpoint_ptr: None, ..caller
    }), t => { if pre.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(pre, include_lock_state, t); } if post.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(post, include_lock_state, t); } });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map.insert(endpoint_ptr, EndpointU { queue: endpoint.queue.skip(1), ..endpoint }), e => {
        if pre.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(pre, include_lock_state, e); }
        if post.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(post, include_lock_state, e); }
    });
}

#[verifier::spinoff_prover]
pub(super) proof fn kernel_ipc_reply_handoff_fields_implies_u_step(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    caller_ptr: RwLockThreadPtr, regs: Registers, flushed_pcid: Option<Pcid>, include_lock_state: bool,
)
    requires
        post.inv(),
        kernel_ipc_reply_handoff_fields(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)] pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
    ensures
        kernel_u_ipc_reply_handoff_changed(kernel_k_user_projection(*pre, include_lock_state), kernel_k_user_projection(*post, include_lock_state),
            cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid),
{
    hide(kernel_k_user_projection);
    reveal(kernel_u_ipc_reply_handoff_changed); kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    kernel_ipc_reply_handoff_fields_implies_u_cpu_array(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid, include_lock_state);
    kernel_ipc_reply_handoff_fields_implies_u_thread_map(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid, include_lock_state);
    kernel_ipc_reply_handoff_fields_implies_u_process_map(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid, include_lock_state);
    kernel_ipc_reply_handoff_fields_implies_u_container_map(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid, include_lock_state);
    reveal(kernel_ipc_reply_handoff_fields);
    kernel_cpu_user_projection_at(pre, include_lock_state, cpu_id); if pre.thr_mp.dom().contains(callee_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, callee_ptr); }
    if pre.thr_mp.dom().contains(caller_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, caller_ptr); }
    if pre.ep_mp.dom().contains(endpoint_ptr) { kernel_endpoint_user_projection_at(pre, include_lock_state, endpoint_ptr); }
    if pre.prc_mp.dom().contains(pre.thr_mp.spec_index(callee_ptr).view().owning_proc) { kernel_process_user_projection_at(pre, include_lock_state, pre.thr_mp.spec_index(callee_ptr).view().owning_proc); }
    let endpoint = pre_u.endpoint_map.spec_index(endpoint_ptr);
    assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { pre.irt.view().user_view_unfold(); post.irt.view().user_view_unfold(); };
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map.insert(endpoint_ptr, EndpointU {
        queue: endpoint.queue.push(callee_ptr), queue_state: if endpoint.queue.len() == 0 { EndpointState::RECEIVE } else { endpoint.queue_state }, ..endpoint
    }), e => { if pre.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(pre, include_lock_state, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(post, include_lock_state, e); } });
    if let Some(pcid) = flushed_pcid { kernel_cpu_tlb_within_may_cache_projection(post, include_lock_state, cpu_id, pcid, post.cpu_tlb.spec_index((cpu_id, pcid))); }
}

/// The reply-handoff fields project to the cpu array with only `cpu_id` switched to the caller.
proof fn kernel_ipc_reply_handoff_fields_implies_u_cpu_array(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    caller_ptr: RwLockThreadPtr, regs: Registers, flushed_pcid: Option<Pcid>, include_lock_state: bool,
)
    requires kernel_ipc_reply_handoff_fields(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let post_u = kernel_k_user_projection(*post, include_lock_state);
            let cpu = pre_u.cpu_array[cpu_id as int];
            post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU { current_process: Some(pre_u.thread_map.spec_index(caller_ptr).owning_proc), current_thread: Some(caller_ptr), ..cpu })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_ipc_reply_handoff_fields);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    if pre.thr_mp.dom().contains(caller_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, caller_ptr); } if index_valid(NUM_CPUS, cpu_id) { kernel_cpu_user_projection_at(pre, include_lock_state, cpu_id); }
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    let cpu = pre_u.cpu_array[cpu_id as int];
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU {
        current_process: Some(pre_u.thread_map.spec_index(caller_ptr).owning_proc), current_thread: Some(caller_ptr), ..cpu
    }), i => { if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, include_lock_state, i as usize); kernel_cpu_user_projection_at(post, include_lock_state, i as usize); } });
}

/// The reply-handoff fields project to the thread map with the callee waiting on the endpoint and the caller running.
proof fn kernel_ipc_reply_handoff_fields_implies_u_thread_map(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    caller_ptr: RwLockThreadPtr, regs: Registers, flushed_pcid: Option<Pcid>, include_lock_state: bool,
)
    requires kernel_ipc_reply_handoff_fields(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let post_u = kernel_k_user_projection(*post, include_lock_state);
            let callee = pre_u.thread_map.spec_index(callee_ptr);
            let caller = pre_u.thread_map.spec_index(caller_ptr);
            post_u.thread_map == pre_u.thread_map.insert(callee_ptr, ThreadU {
                state: ThreadState::RECEIVING_CALL, caller: None, blocking_endpoint_ptr: Some(endpoint_ptr), ipc_payload: IPCPayLoad::Empty, trap_frame: Some(regs), ..callee
            }).insert(caller_ptr, ThreadU { state: ThreadState::RUNNING { cpu_id }, callee: None, last_cpu: cpu_id, trap_frame: None, ..caller })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_ipc_reply_handoff_fields); kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    if pre.thr_mp.dom().contains(callee_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, callee_ptr); } if pre.thr_mp.dom().contains(caller_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, caller_ptr); }
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    let callee = pre_u.thread_map.spec_index(callee_ptr);
    let caller = pre_u.thread_map.spec_index(caller_ptr);
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(callee_ptr, ThreadU {
        state: ThreadState::RECEIVING_CALL, caller: None, blocking_endpoint_ptr: Some(endpoint_ptr), ipc_payload: IPCPayLoad::Empty, trap_frame: Some(regs), ..callee
    }).insert(caller_ptr, ThreadU { state: ThreadState::RUNNING { cpu_id }, callee: None, last_cpu: cpu_id, trap_frame: None, ..caller }), t => {
        if pre.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(pre, include_lock_state, t); }
        if post.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(post, include_lock_state, t); }
    });
}

/// The reply-handoff fields leave the process map projection unchanged.
proof fn kernel_ipc_reply_handoff_fields_implies_u_process_map(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    caller_ptr: RwLockThreadPtr, regs: Registers, flushed_pcid: Option<Pcid>, include_lock_state: bool,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        kernel_ipc_reply_handoff_fields(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid),
    ensures kernel_k_user_projection(*post, include_lock_state).process_map == kernel_k_user_projection(*pre, include_lock_state).process_map,
{
    hide(kernel_k_user_projection);
    reveal(kernel_ipc_reply_handoff_fields); reveal(kernel_process_nonlock_fields_unchanged); kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    assert_maps_equal!(post_u.process_map, pre_u.process_map, p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_user_projection_at(pre, include_lock_state, p); } if post.prc_mp.dom().contains(p) { kernel_process_user_projection_at(post, include_lock_state, p); }
        reveal(process_pagetable_match); reveal(process_iommu_table_match); reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
    });
}

/// The reply-handoff fields leave the container map projection unchanged.
proof fn kernel_ipc_reply_handoff_fields_implies_u_container_map(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    caller_ptr: RwLockThreadPtr, regs: Registers, flushed_pcid: Option<Pcid>, include_lock_state: bool,
)
    requires
        kernel_ipc_reply_handoff_fields(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)] pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
    ensures kernel_k_user_projection(*post, include_lock_state).container_map == kernel_k_user_projection(*pre, include_lock_state).container_map,
{
    hide(kernel_k_user_projection);
    reveal(kernel_ipc_reply_handoff_fields); reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    assert_maps_equal!(post_u.container_map, pre_u.container_map, c => { if pre.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(pre, include_lock_state, c); } if post.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(post, include_lock_state, c); } });
}

#[verifier::spinoff_prover]
pub(super) proof fn kernel_ipc_rendezvous_fields_implies_u_step(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, caller_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, peer_thread_ptr: RwLockThreadPtr, peer_result: RetValueType,
    cpu_transfer: Option<(CpuId, RwLockThreadPtr)>, pci_transfer: Option<(PciBdf, RwLockProcessPtr, RwLockProcessPtr)>, include_lock_state: bool,
)
    requires
        post.inv(),
        kernel_ipc_rendezvous_fields(pre, post, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer),
        post.cpu_op.view().view() == pre.cpu_op.view().view(),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)]
            pre.ctn_mp.dom().contains(p) && post.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).locking_thread() == pre.ctn_mp.spec_index(p).locking_thread() && post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) && post.prc_mp.dom().contains(p) ==> post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread(),
        forall|p: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(p)]
            pre.thr_mp.dom().contains(p) && post.thr_mp.dom().contains(p) ==> post.thr_mp.spec_index(p).locking_thread() == pre.thr_mp.spec_index(p).locking_thread(),
        forall|p: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(p)]
            pre.ep_mp.dom().contains(p) && post.ep_mp.dom().contains(p) ==> post.ep_mp.spec_index(p).locking_thread() == pre.ep_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) && post.pt_mp.dom().contains(p) ==> post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
            pre.it_mp.dom().contains(p) && post.it_mp.dom().contains(p) ==> post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread(),
        forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> post.cpu_arr.spec_index(i).value.locking_thread() == pre.cpu_arr.spec_index(i).value.locking_thread(),
        post.cpu_set_mp.dom() == pre.cpu_set_mp.dom(),
        forall|p: RwLockCpuSetPtr| #![trigger post.cpu_set_mp.spec_index(p)]
            pre.cpu_set_mp.dom().contains(p) ==> post.cpu_set_mp.spec_index(p).locking_thread() == pre.cpu_set_mp.spec_index(p).locking_thread() && post.cpu_set_mp.spec_index(p).being_killed() == pre.cpu_set_mp.spec_index(p).being_killed(),
    ensures
        kernel_u_ipc_rendezvous_changed(kernel_k_user_projection(*pre, include_lock_state), kernel_k_user_projection(*post, include_lock_state),
            cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer),
{
    hide(kernel_k_user_projection);
    reveal(kernel_u_ipc_rendezvous_changed); reveal(kernel_ipc_rendezvous_fields); kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    kernel_cpu_user_projection_at(pre, include_lock_state, cpu_id); if pre.thr_mp.dom().contains(caller_thread_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, caller_thread_ptr); }
    if pre.thr_mp.dom().contains(peer_thread_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, peer_thread_ptr); }
    if pre.ep_mp.dom().contains(endpoint_ptr) { kernel_endpoint_user_projection_at(pre, include_lock_state, endpoint_ptr); }
    if pre.prc_mp.dom().contains(pre.thr_mp.spec_index(caller_thread_ptr).view().owning_proc) { kernel_process_user_projection_at(pre, include_lock_state, pre.thr_mp.spec_index(caller_thread_ptr).view().owning_proc); }
    if pre.ctn_mp.dom().contains(pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container) { kernel_container_user_projection_at(pre, include_lock_state, pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container); }
    if let Some((transfer, receiver)) = cpu_transfer { kernel_cpu_user_projection_at(pre, include_lock_state, transfer); if pre.thr_mp.dom().contains(receiver) { kernel_thread_user_projection_at(pre, include_lock_state, receiver); } }
    if let Some((bdf, sender, receiver)) = pci_transfer {
        let old_did = match pre.prc_mp.spec_index(sender).view().iommu_table { Some(t) => pre.it_mp.spec_index(t).view().did, None => None };
        if pre.prc_mp.dom().contains(sender) {
            kernel_process_user_projection_at(pre, include_lock_state, sender); kernel_process_user_projection_at(post, include_lock_state, sender); process_iommu_table_match_process_at(post.prc_mp, post.it_mp, sender);
        }
        if pre.prc_mp.dom().contains(receiver) { kernel_process_user_projection_at(pre, include_lock_state, receiver); }
        pre.irt.view().user_view_unfold();
        if iommu_roots_attached(pre.irt.view().iommu_roots())[bdf.0 as int][bdf.1 as int][bdf.2 as int] && old_did is Some {
            assert(post.iommu_tlb.view().dom().contains(old_did->Some_0));
            assert(vtd_domain_id_valid(old_did->Some_0)) by { reveal(IommuTLB::inv); };
            kernel_iommu_tlb_within_may_cache_projection(post, include_lock_state, old_did->Some_0, post.iommu_tlb.spec_index(old_did->Some_0));
        }
    }
    kernel_ipc_rendezvous_fields_implies_u_cpu_array(pre, post, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer, include_lock_state);
    kernel_ipc_rendezvous_fields_implies_u_container_map(pre, post, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer, include_lock_state);
    kernel_ipc_rendezvous_fields_implies_u_process_map(pre, post, pci_transfer, include_lock_state);
    kernel_ipc_rendezvous_fields_implies_u_iommu_root_table(pre, post, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer, include_lock_state);
    kernel_ipc_rendezvous_fields_implies_u_thread_map(pre, post, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer, include_lock_state);
    kernel_ipc_rendezvous_fields_implies_u_endpoint_map(pre, post, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer, include_lock_state);
}

/// The rendezvous fields project to the cpu array with only a handed-over cpu moved to the receiver's container.
#[verifier::spinoff_prover]
proof fn kernel_ipc_rendezvous_fields_implies_u_cpu_array(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, caller_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, peer_thread_ptr: RwLockThreadPtr, peer_result: RetValueType,
    cpu_transfer: Option<(CpuId, RwLockThreadPtr)>, pci_transfer: Option<(PciBdf, RwLockProcessPtr, RwLockProcessPtr)>, include_lock_state: bool,
)
    requires
        kernel_ipc_rendezvous_fields(pre, post, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer),
        post.cpu_op.view().view() == pre.cpu_op.view().view(),
        forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> post.cpu_arr.spec_index(i).value.locking_thread() == pre.cpu_arr.spec_index(i).value.locking_thread(),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let post_u = kernel_k_user_projection(*post, include_lock_state);
            post_u.cpu_array == match cpu_transfer {
                Some((transfer_cpu, receiver)) => pre_u.cpu_array.update(transfer_cpu as int, CpuU {
                    owning_container: pre_u.thread_map.spec_index(receiver).owning_container, ..pre_u.cpu_array[transfer_cpu as int]
                }),
                None => pre_u.cpu_array,
            }
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_ipc_rendezvous_fields);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    match cpu_transfer {
        Some((transfer_cpu, receiver)) => {
            if pre.thr_mp.dom().contains(receiver) { kernel_thread_user_projection_at(pre, include_lock_state, receiver); } if index_valid(NUM_CPUS, transfer_cpu) { kernel_cpu_user_projection_at(pre, include_lock_state, transfer_cpu); }
            assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(transfer_cpu as int, CpuU {
                owning_container: pre_u.thread_map.spec_index(receiver).owning_container, ..pre_u.cpu_array[transfer_cpu as int]
            }), i => { if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, include_lock_state, i as usize); kernel_cpu_user_projection_at(post, include_lock_state, i as usize); } });
        },
        None => { assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, include_lock_state, i as usize); kernel_cpu_user_projection_at(post, include_lock_state, i as usize); } }); },
    }
}

/// The rendezvous fields project to the container map with only the peer pushed onto its wake cpu's scheduler queue.
#[verifier::spinoff_prover]
proof fn kernel_ipc_rendezvous_fields_implies_u_container_map(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, caller_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, peer_thread_ptr: RwLockThreadPtr, peer_result: RetValueType,
    cpu_transfer: Option<(CpuId, RwLockThreadPtr)>, pci_transfer: Option<(PciBdf, RwLockProcessPtr, RwLockProcessPtr)>, include_lock_state: bool,
)
    requires
        container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp),
        kernel_ipc_rendezvous_fields(pre, post, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)]
            pre.ctn_mp.dom().contains(p) && post.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).locking_thread() == pre.ctn_mp.spec_index(p).locking_thread() && post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
        post.cpu_set_mp.dom() == pre.cpu_set_mp.dom(),
        forall|p: RwLockCpuSetPtr| #![trigger post.cpu_set_mp.spec_index(p)]
            pre.cpu_set_mp.dom().contains(p) ==> post.cpu_set_mp.spec_index(p).locking_thread() == pre.cpu_set_mp.spec_index(p).locking_thread() && post.cpu_set_mp.spec_index(p).being_killed() == pre.cpu_set_mp.spec_index(p).being_killed(),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let post_u = kernel_k_user_projection(*post, include_lock_state);
            let peer = pre_u.thread_map.spec_index(peer_thread_ptr);
            let caller = pre_u.thread_map.spec_index(caller_thread_ptr);
            let wake_cpu = if peer.owning_container == caller.owning_container { cpu_id } else { peer.last_cpu };
            let container = pre_u.container_map.spec_index(peer.owning_container);
            post_u.container_map == pre_u.container_map.insert(peer.owning_container, ContainerU {
                scheduler: container.scheduler.update(wake_cpu as int, container.scheduler[wake_cpu as int].push(peer_thread_ptr)), ..container
            })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_ipc_rendezvous_fields); kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    if pre.thr_mp.dom().contains(peer_thread_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, peer_thread_ptr); } if pre.thr_mp.dom().contains(caller_thread_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, caller_thread_ptr); }
    if pre.ctn_mp.dom().contains(pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container) { kernel_container_user_projection_at(pre, include_lock_state, pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container); }
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    let peer = pre_u.thread_map.spec_index(peer_thread_ptr);
    let container = pre_u.container_map.spec_index(peer.owning_container);
    let caller = pre_u.thread_map.spec_index(caller_thread_ptr);
    let wake_cpu = if peer.owning_container == caller.owning_container { cpu_id } else { peer.last_cpu };
    assert_maps_equal!(post_u.container_map, pre_u.container_map.insert(peer.owning_container, ContainerU {
        scheduler: container.scheduler.update(wake_cpu as int, container.scheduler[wake_cpu as int].push(peer_thread_ptr)), ..container
    }), c => { if pre.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(pre, include_lock_state, c); } if post.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(post, include_lock_state, c); } reveal(container_cpu_set_wf); });
}

/// The rendezvous fields project to the process map with only a handed-over PCI function moved from the sender to the
/// receiver process.
proof fn kernel_ipc_rendezvous_fields_implies_u_process_map(
    pre: &KernelK, post: &KernelK, pci_transfer: Option<(PciBdf, RwLockProcessPtr, RwLockProcessPtr)>, include_lock_state: bool,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view()),
        pci_transfer is None ==> kernel_iommu_table_nonlock_fields_unchanged(pre.it_mp, post.it_mp),
        pci_transfer is None ==> kernel_process_nonlock_fields_unchanged(pre.prc_mp, post.prc_mp),
        pci_transfer matches Some((bdf, sender, receiver)) ==> {
            &&& pre.prc_mp.dom().contains(sender)
            &&& pre.prc_mp.dom().contains(receiver)
            &&& sender != receiver
            &&& post.it_mp.dom() == pre.it_mp.dom()
            &&& forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
                pre.it_mp.dom().contains(p) ==> {
                    let before = pre.it_mp.spec_index(p).view();
                    let after = post.it_mp.spec_index(p).view();
                    &&& pre.prc_mp.spec_index(sender).view().iommu_table != Some(p) ==> after.did == before.did
                    &&& after.mapping_4k().filter_keys(|va: VAddr| after.mapping_4k().spec_index(va).present) == before.mapping_4k().filter_keys(|va: VAddr| before.mapping_4k().spec_index(va).present)
                    &&& after.mapping_2m().filter_keys(|va: VAddr| after.mapping_2m().spec_index(va).present) == before.mapping_2m().filter_keys(|va: VAddr| before.mapping_2m().spec_index(va).present)
                    &&& after.mapping_1g().filter_keys(|va: VAddr| after.mapping_1g().spec_index(va).present) == before.mapping_1g().filter_keys(|va: VAddr| before.mapping_1g().spec_index(va).present)
                }
            &&& post.prc_mp.dom() == pre.prc_mp.dom()
            &&& forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
                pre.prc_mp.dom().contains(p) ==> {
                    let a = pre.prc_mp.spec_index(p);
                    let b = post.prc_mp.spec_index(p);
                    let pci = a.view_ghost().owned_pci_functions.view();
                    &&& b.view().zombie == a.view().zombie
                    &&& b.view().pagetable == a.view().pagetable
                    &&& b.view().iommu_table == a.view().iommu_table
                    &&& b.view_ghost().owned_pci_functions.view() == if p == sender { pci.remove(bdf) } else if p == receiver { pci.insert(bdf) } else { pci }
                    &&& b.view().quota_4k == a.view().quota_4k
                    &&& b.view().quota_2m == a.view().quota_2m
                    &&& b.view().quota_1g == a.view().quota_1g
                    &&& b.view().children.view() == a.view().children.view()
                    &&& b.view_rodata().view().parent == a.view_rodata().view().parent
                    &&& b.view_rodata().view().depth == a.view_rodata().view().depth
                    &&& b.view_rodata().view().pcid == a.view_rodata().view().pcid
                    &&& b.view_rodata().view().owning_container == a.view_rodata().view().owning_container
                    &&& b.view_ghost().uppertree_seq.view() == a.view_ghost().uppertree_seq.view()
                    &&& b.view_ghost().subtree_set.view() == a.view_ghost().subtree_set.view()
                    &&& b.being_killed() == a.being_killed()
                    &&& b.view().owned_threads.view() == a.view().owned_threads.view()
                }
        },
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) && post.prc_mp.dom().contains(p) ==> post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) && post.pt_mp.dom().contains(p) ==> post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
            pre.it_mp.dom().contains(p) && post.it_mp.dom().contains(p) ==> post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread(),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let post_u = kernel_k_user_projection(*post, include_lock_state);
            &&& post_u.process_map == match pci_transfer {
                Some((bdf, sender, receiver)) => {
                    let s = pre_u.process_map.spec_index(sender);
                    let r = pre_u.process_map.spec_index(receiver);
                    let s_table = match s.iommu_table { Some(t) => Some(PageTableU { did: post_u.process_map.spec_index(sender).iommu_table->Some_0.did, ..t }), None => None };
                    pre_u.process_map.insert(sender, ProcessU { iommu_table: s_table, owned_pci_functions: s.owned_pci_functions.remove(bdf), ..s })
                        .insert(receiver, ProcessU { owned_pci_functions: r.owned_pci_functions.insert(bdf), ..r })
                },
                None => pre_u.process_map,
            }
        }),
{
    match pci_transfer {
        Some((bdf, sender, receiver)) => { kernel_ipc_rendezvous_fields_implies_u_process_map_pci_moved(pre, post, bdf, sender, receiver, include_lock_state); },
        None => { kernel_process_nonlock_fields_and_locks_unchanged_implies_u_process_map(pre, post, include_lock_state); },
    }
}

/// Process fields equal except the PCI function `bdf` moved from `sender` to `receiver` project to that process-map update.
proof fn kernel_ipc_rendezvous_fields_implies_u_process_map_pci_moved(
    pre: &KernelK, post: &KernelK, bdf: PciBdf, sender: RwLockProcessPtr, receiver: RwLockProcessPtr, include_lock_state: bool,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view()),
        post.it_mp.dom() == pre.it_mp.dom(),
        forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
            pre.it_mp.dom().contains(p) ==> {
                let before = pre.it_mp.spec_index(p).view();
                let after = post.it_mp.spec_index(p).view();
                &&& pre.prc_mp.spec_index(sender).view().iommu_table != Some(p) ==> after.did == before.did
                &&& after.mapping_4k().filter_keys(|va: VAddr| after.mapping_4k().spec_index(va).present) == before.mapping_4k().filter_keys(|va: VAddr| before.mapping_4k().spec_index(va).present)
                &&& after.mapping_2m().filter_keys(|va: VAddr| after.mapping_2m().spec_index(va).present) == before.mapping_2m().filter_keys(|va: VAddr| before.mapping_2m().spec_index(va).present)
                &&& after.mapping_1g().filter_keys(|va: VAddr| after.mapping_1g().spec_index(va).present) == before.mapping_1g().filter_keys(|va: VAddr| before.mapping_1g().spec_index(va).present)
            },
        pre.prc_mp.dom().contains(sender),
        pre.prc_mp.dom().contains(receiver),
        sender != receiver,
        post.prc_mp.dom() == pre.prc_mp.dom(),
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) ==> {
                let a = pre.prc_mp.spec_index(p);
                let b = post.prc_mp.spec_index(p);
                let pci = a.view_ghost().owned_pci_functions.view();
                &&& b.view().zombie == a.view().zombie
                &&& b.view().pagetable == a.view().pagetable
                &&& b.view().iommu_table == a.view().iommu_table
                &&& b.view_ghost().owned_pci_functions.view() == if p == sender { pci.remove(bdf) } else if p == receiver { pci.insert(bdf) } else { pci }
                &&& b.view().quota_4k == a.view().quota_4k
                &&& b.view().quota_2m == a.view().quota_2m
                &&& b.view().quota_1g == a.view().quota_1g
                &&& b.view().children.view() == a.view().children.view()
                &&& b.view_rodata().view().parent == a.view_rodata().view().parent
                &&& b.view_rodata().view().depth == a.view_rodata().view().depth
                &&& b.view_rodata().view().pcid == a.view_rodata().view().pcid
                &&& b.view_rodata().view().owning_container == a.view_rodata().view().owning_container
                &&& b.view_ghost().uppertree_seq.view() == a.view_ghost().uppertree_seq.view()
                &&& b.view_ghost().subtree_set.view() == a.view_ghost().subtree_set.view()
                &&& b.being_killed() == a.being_killed()
                &&& b.view().owned_threads.view() == a.view().owned_threads.view()
            },
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) && post.prc_mp.dom().contains(p) ==> post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) && post.pt_mp.dom().contains(p) ==> post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
            pre.it_mp.dom().contains(p) && post.it_mp.dom().contains(p) ==> post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread(),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let post_u = kernel_k_user_projection(*post, include_lock_state);
            let s = pre_u.process_map.spec_index(sender);
            let r = pre_u.process_map.spec_index(receiver);
            let s_table = match s.iommu_table { Some(t) => Some(PageTableU { did: post_u.process_map.spec_index(sender).iommu_table->Some_0.did, ..t }), None => None };
            &&& post_u.process_map == pre_u.process_map.insert(sender, ProcessU { iommu_table: s_table, owned_pci_functions: s.owned_pci_functions.remove(bdf), ..s })
                .insert(receiver, ProcessU { owned_pci_functions: r.owned_pci_functions.insert(bdf), ..r })
        }),
{
    hide(kernel_k_user_projection);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    let s = pre_u.process_map.spec_index(sender);
    let r = pre_u.process_map.spec_index(receiver);
    let s_table = match s.iommu_table { Some(t) => Some(PageTableU { did: post_u.process_map.spec_index(sender).iommu_table->Some_0.did, ..t }), None => None };
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(sender, ProcessU { iommu_table: s_table, owned_pci_functions: s.owned_pci_functions.remove(bdf), ..s })
        .insert(receiver, ProcessU { owned_pci_functions: r.owned_pci_functions.insert(bdf), ..r }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_user_projection_at(pre, include_lock_state, p); } if post.prc_mp.dom().contains(p) { kernel_process_user_projection_at(post, include_lock_state, p); }
        process_pagetable_match_process_at(post.prc_mp, post.pt_mp, p); process_iommu_table_match_process_at(post.prc_mp, post.it_mp, p); process_iommu_table_match_process_at(post.prc_mp, post.it_mp, sender);
        reveal(kernel_pagetable_nonlock_fields_unchanged);
    });
}

/// The rendezvous fields project to the root table with only a handed-over PCI function owned, detached, by the receiver.
proof fn kernel_ipc_rendezvous_fields_implies_u_iommu_root_table(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, caller_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, peer_thread_ptr: RwLockThreadPtr, peer_result: RetValueType,
    cpu_transfer: Option<(CpuId, RwLockThreadPtr)>, pci_transfer: Option<(PciBdf, RwLockProcessPtr, RwLockProcessPtr)>, include_lock_state: bool,
)
    requires
        kernel_ipc_rendezvous_fields(pre, post, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let post_u = kernel_k_user_projection(*post, include_lock_state);
            post_u.iommu_root_table == match pci_transfer {
                Some((bdf, _, receiver)) => IommuRootTableU {
                    owners: seq3_update(pre_u.iommu_root_table.owners, bdf.0 as int, bdf.1 as int, bdf.2 as int, receiver),
                    attached: seq3_update(pre_u.iommu_root_table.attached, bdf.0 as int, bdf.1 as int, bdf.2 as int, false),
                },
                None => pre_u.iommu_root_table,
            }
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_ipc_rendezvous_fields); kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    pre.irt.view().user_view_unfold(); post.irt.view().user_view_unfold();
    if let Some((bdf, _, receiver)) = pci_transfer {
        let attached = seq3_update(pre_u.iommu_root_table.attached, bdf.0 as int, bdf.1 as int, bdf.2 as int, false);
        assert_seqs_equal!(post_u.iommu_root_table.attached == attached, b => {
            assert_seqs_equal!(post_u.iommu_root_table.attached[b] == attached[b], d => {
                assert_seqs_equal!(post_u.iommu_root_table.attached[b][d] == attached[b][d], f => {
                    assert((post.irt.view().spec_index_iommu_root(b as usize, d as usize, f as usize) is Some) == attached[b][d][f]);
                });
            });
        });
    }
}

/// The rendezvous fields project to the thread map with only the peer scheduled on its wake cpu with `peer_result`.
#[verifier::spinoff_prover]
proof fn kernel_ipc_rendezvous_fields_implies_u_thread_map(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, caller_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, peer_thread_ptr: RwLockThreadPtr, peer_result: RetValueType,
    cpu_transfer: Option<(CpuId, RwLockThreadPtr)>, pci_transfer: Option<(PciBdf, RwLockProcessPtr, RwLockProcessPtr)>, include_lock_state: bool,
)
    requires
        kernel_ipc_rendezvous_fields(pre, post, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer),
        forall|p: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(p)]
            pre.thr_mp.dom().contains(p) && post.thr_mp.dom().contains(p) ==> post.thr_mp.spec_index(p).locking_thread() == pre.thr_mp.spec_index(p).locking_thread(),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let post_u = kernel_k_user_projection(*post, include_lock_state);
            let peer = pre_u.thread_map.spec_index(peer_thread_ptr);
            let caller = pre_u.thread_map.spec_index(caller_thread_ptr);
            let wake_cpu = if peer.owning_container == caller.owning_container { cpu_id } else { peer.last_cpu };
            post_u.thread_map == pre_u.thread_map.insert(peer_thread_ptr, ThreadU {
                state: ThreadState::SCHEDULED { cpu_id: wake_cpu }, blocking_endpoint_ptr: None, ipc_payload: IPCPayLoad::Empty, error_code: Some(peer_result), ..peer
            })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_ipc_rendezvous_fields);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    if pre.thr_mp.dom().contains(caller_thread_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, caller_thread_ptr); } if pre.thr_mp.dom().contains(peer_thread_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, peer_thread_ptr); }
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    let peer = pre_u.thread_map.spec_index(peer_thread_ptr);
    let caller = pre_u.thread_map.spec_index(caller_thread_ptr);
    let wake_cpu = if peer.owning_container == caller.owning_container { cpu_id } else { peer.last_cpu };
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(peer_thread_ptr, ThreadU {
        state: ThreadState::SCHEDULED { cpu_id: wake_cpu }, blocking_endpoint_ptr: None, ipc_payload: IPCPayLoad::Empty, error_code: Some(peer_result), ..peer
    }), t => { if pre.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(pre, include_lock_state, t); } if post.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(post, include_lock_state, t); } });
}

/// The rendezvous fields project to the endpoint map with only the peer dequeued from the endpoint.
#[verifier::spinoff_prover]
proof fn kernel_ipc_rendezvous_fields_implies_u_endpoint_map(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, caller_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, peer_thread_ptr: RwLockThreadPtr, peer_result: RetValueType,
    cpu_transfer: Option<(CpuId, RwLockThreadPtr)>, pci_transfer: Option<(PciBdf, RwLockProcessPtr, RwLockProcessPtr)>, include_lock_state: bool,
)
    requires
        kernel_ipc_rendezvous_fields(pre, post, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer),
        forall|p: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(p)]
            pre.ep_mp.dom().contains(p) && post.ep_mp.dom().contains(p) ==> post.ep_mp.spec_index(p).locking_thread() == pre.ep_mp.spec_index(p).locking_thread(),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let post_u = kernel_k_user_projection(*post, include_lock_state);
            let endpoint = pre_u.endpoint_map.spec_index(endpoint_ptr);
            post_u.endpoint_map == pre_u.endpoint_map.insert(endpoint_ptr, EndpointU { queue: endpoint.queue.skip(1), ..endpoint })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_ipc_rendezvous_fields);
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

} // verus!
