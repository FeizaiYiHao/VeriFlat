use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal};
use crate::*;
use super::syscall_ipc_spec::*;
verus! {
/// The cpu, the running thread with its pages progress, the recorded peer in transit with it, and the channel at its descriptor
/// `endpoint_index` are write-held on `krnl`, which gives the pages finish pre and the user-view context of the finish step.
pub(super) proof fn ipc_pages_finish_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, peer_ptr: RwLockThreadPtr,
    channel_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, result: RetValueType, wake_cpu: CpuId,
)
    requires
        edp_idx_valid(endpoint_index),
        krnl.inv(),
        typed_lock_maps_aligned(krnl, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), peer_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.endpoint_lock_map(), channel_ptr, TypedLockMode::Write),
        krnl.prc_mp.dom().contains(process_ptr),
        krnl.thr_mp.dom().contains(peer_ptr),
        krnl.ep_mp.dom().contains(channel_ptr),
        krnl.cpu_arr.spec_index(cpu_id).value.view().view().current_process == Some(process_ptr),
        krnl.cpu_arr.spec_index(cpu_id).value.view().view().current_thread == Some(thread_ptr),
        ({
            let progress = krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view();
            &&& progress is Some
            &&& progress->Some_0 is IpcPages
            &&& progress->Some_0->IpcPages_peer == peer_ptr
            &&& progress->Some_0->IpcPages_released == Some(result)
            &&& progress->Some_0->IpcPages_tables is Unlocked
        }),
        krnl.thr_mp.dom().contains(thread_ptr),
        krnl.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[endpoint_index as int] == Some(channel_ptr),
        krnl.thr_mp.spec_index(peer_ptr).view().state is IPC_TRANSIT,
        krnl.thr_mp.spec_index(peer_ptr).view().state->IPC_TRANSIT_partner == thread_ptr,
        wake_cpu == if krnl.thr_mp.spec_index(peer_ptr).view().owning_container == krnl.thr_mp.spec_index(thread_ptr).view().owning_container { cpu_id }
            else { krnl.thr_mp.spec_index(peer_ptr).view().last_cpu },
    ensures
        ({
            let pre = kernel_k_to_kernel_u(*krnl);
            let progress = pre.thread_map[thread_ptr].syscall_progress;
            &&& wake_cpu == if pre.thread_map[peer_ptr].owning_container == pre.thread_map[thread_ptr].owning_container { cpu_id } else { pre.thread_map[peer_ptr].last_cpu }
            &&& ipc_pages_held(pre, cpu_id, endpoint_index)
            &&& pre.cpu_array[cpu_id as int].current_process == Some(process_ptr)
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& pre.cpu_array[cpu_id as int].state == krnl.cpu_arr.spec_index(cpu_id).view().view().view().state
            &&& progress->Some_0->IpcPages_peer == peer_ptr
            &&& progress->Some_0->IpcPages_released == Some(result)
            &&& progress->Some_0->IpcPages_tables is Unlocked
            &&& pre.thread_map[thread_ptr].endpoint_descriptors[endpoint_index as int] == Some(channel_ptr)
            &&& pre.container_map.dom().contains(pre.thread_map[peer_ptr].owning_container)
        }),
{
    container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, peer_ptr);
    kernel_write_held_context_projection(krnl, lctx, cpu_id, process_ptr, thread_ptr, Some(channel_ptr)); kernel_write_held_context_projection(krnl, lctx, cpu_id, process_ptr, peer_ptr, None);
    kernel_cpu_thread_projection_at(krnl, cpu_id, process_ptr, peer_ptr, Some(channel_ptr)); kernel_thread_projection_at(krnl, thread_ptr);
}

/// The running thread on `krnl` that meets the queue head `peer_ptr` with a same-length Pages payload from another process gives the pages
/// enter pre and the user-view context of the enter step.
pub(super) proof fn ipc_pages_enter_step_pre_from_k(
    krnl: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, channel_ptr: RwLockEndpointPtr, peer_ptr: RwLockThreadPtr,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, range: VaRange4K, peer_range: VaRange4K,
)
    requires
        range.wf(),
        range.len > 0,
        ({
            let cpu = krnl.cpu_arr.spec_index(cpu_id).value;
            let caller = krnl.thr_mp.spec_index(thread_ptr);
            let peer = krnl.thr_mp.spec_index(peer_ptr);
            let channel = krnl.ep_mp.spec_index(channel_ptr);
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& cpu.locking_thread() is None
            &&& cpu.view().view().state is Running
            &&& cpu.view().view().current_process == Some(process_ptr)
            &&& cpu.view().view().current_thread == Some(thread_ptr)
            &&& krnl.prc_mp.dom().contains(process_ptr)
            &&& krnl.thr_mp.dom().contains(thread_ptr)
            &&& caller.locking_thread() is None
            &&& caller.view().syscall_progress.view() is None
            &&& !caller.being_killed()
            &&& caller.view().state == (ThreadState::RUNNING { cpu_id })
            &&& caller.view().owning_proc == process_ptr
            &&& krnl.ctn_mp.dom().contains(caller.view().owning_container)
            &&& edp_idx_valid(endpoint_index)
            &&& caller.view().endpoint_descriptors.view()[endpoint_index as int] == Some(channel_ptr)
            &&& krnl.ep_mp.dom().contains(channel_ptr)
            &&& channel.locking_thread() is None
            &&& !channel.view().queue.view().contains(thread_ptr)
            &&& waiting_state is SENDING || waiting_state is RECEIVING
            &&& channel.view().queue.view().len() > 0
            &&& channel.view().queue.view()[0] == peer_ptr
            &&& (channel.view().queue_state is SEND) != (waiting_state is SENDING)
            &&& krnl.thr_mp.dom().contains(peer_ptr)
            &&& peer.locking_thread() is None
            &&& peer_ptr != thread_ptr
            &&& !peer.being_killed()
            &&& peer.view().state == (if waiting_state is SENDING { ThreadState::RECEIVING } else { ThreadState::SENDING })
            &&& peer.view().blocking_endpoint_ptr == Some(channel_ptr)
            &&& krnl.ctn_mp.dom().contains(peer.view().owning_container)
            &&& peer.view().ipc_payload == (IPCPayLoad::Pages { va_range: peer_range })
            &&& peer_range.len == range.len
            &&& peer.view().owning_proc != process_ptr
        }),
    ensures
        ipc_pages_enter_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, endpoint_index, waiting_state, range),
        ({
            let pre = kernel_k_to_kernel_u(*krnl);
            &&& pre.cpu_array[cpu_id as int].current_process == Some(process_ptr)
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& pre.thread_map[thread_ptr].endpoint_descriptors[endpoint_index as int] == Some(channel_ptr)
            &&& pre.endpoint_map[channel_ptr].queue[0] == peer_ptr
            &&& pre.thread_map[peer_ptr].ipc_payload == (IPCPayLoad::Pages { va_range: peer_range })
        }),
{
    kernel_cpu_thread_projection_at(krnl, cpu_id, process_ptr, thread_ptr, Some(channel_ptr)); kernel_thread_projection_at(krnl, peer_ptr);
    ipc_pages_enter_step_pre_from_u(kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, thread_ptr, channel_ptr, peer_ptr, endpoint_index, waiting_state, range, peer_range);
}

/// The cpu, the running thread recording an unlocked pages rendezvous, its peer, and the channel write-held on `krnl`, with the sender's page table not
/// write-locked and the receiver's unlocked to fill it or not write-locked to read it as `tables` asks, give the lock-tables pre and the user-view
/// context of the lock-tables step.
pub(super) proof fn ipc_pages_lock_tables_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, peer_ptr: RwLockThreadPtr, channel_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    source_thread: RwLockThreadPtr, target_thread: RwLockThreadPtr, source_process: RwLockProcessPtr, target_process: RwLockProcessPtr,
    source_pagetable: RwLockPageTableRoot, target_pagetable: RwLockPageTableRoot, tables: IpcPagesTables,
)
    requires
        edp_idx_valid(endpoint_index),
        typed_lock_maps_aligned(krnl, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), peer_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.endpoint_lock_map(), channel_ptr, TypedLockMode::Write),
        krnl.thr_mp.dom().contains(thread_ptr),
        krnl.thr_mp.dom().contains(peer_ptr),
        krnl.cpu_arr.spec_index(cpu_id).value.view().view().current_process is Some,
        krnl.cpu_arr.spec_index(cpu_id).value.view().view().current_thread == Some(thread_ptr),
        ({
            let progress = krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view();
            &&& progress is Some
            &&& progress->Some_0 is IpcPages
            &&& progress->Some_0->IpcPages_peer == peer_ptr
            &&& progress->Some_0->IpcPages_tables is Unlocked
            &&& progress->Some_0->IpcPages_released is None
        }),
        krnl.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[endpoint_index as int] == Some(channel_ptr),
        source_thread == thread_ptr && target_thread == peer_ptr || source_thread == peer_ptr && target_thread == thread_ptr,
        krnl.thr_mp.spec_index(peer_ptr).view().state == (ThreadState::IPC_TRANSIT { partner: thread_ptr, wait: if source_thread == thread_ptr { IpcWait::Receive } else { IpcWait::Send } }),
        krnl.thr_mp.spec_index(source_thread).view().owning_proc == source_process,
        krnl.thr_mp.spec_index(target_thread).view().owning_proc == target_process,
        source_process != target_process,
        krnl.prc_mp.dom().contains(source_process),
        krnl.prc_mp.dom().contains(target_process),
        !krnl.prc_mp.spec_index(source_process).view().zombie,
        !krnl.prc_mp.spec_index(target_process).view().zombie,
        krnl.prc_mp.spec_index(source_process).view().pagetable == source_pagetable,
        krnl.prc_mp.spec_index(target_process).view().pagetable == target_pagetable,
        krnl.pt_mp.dom().contains(source_pagetable),
        krnl.pt_mp.dom().contains(target_pagetable),
        tables is Read || tables is Fill,
        !(krnl.pt_mp.spec_index(source_pagetable).locking_thread() is Write),
        tables is Fill ==> krnl.pt_mp.spec_index(target_pagetable).locking_thread() is None,
        tables is Read ==> !(krnl.pt_mp.spec_index(target_pagetable).locking_thread() is Write),
    ensures
        ipc_pages_lock_tables_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, endpoint_index, tables),
        ({
            let pre = kernel_k_to_kernel_u(*krnl);
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& pre.thread_map[thread_ptr].syscall_progress == krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()
            &&& pre.thread_map[ipc_pages_sender(pre, cpu_id)].owning_proc == source_process
            &&& pre.thread_map[ipc_pages_receiver(pre, cpu_id)].owning_proc == target_process
        }),
{
    krnl.ep_mp.typed_lock_map_aligned_write_at(lctx.endpoint_lock_map(), lctx.thread_id(), channel_ptr);
    kernel_write_held_context_projection(krnl, lctx, cpu_id, source_process, thread_ptr, Some(channel_ptr)); kernel_write_held_context_projection(krnl, lctx, cpu_id, target_process, peer_ptr, None);
    kernel_cpu_thread_projection_at(krnl, cpu_id, source_process, peer_ptr, None); kernel_thread_projection_at(krnl, thread_ptr);
    kernel_pagetable_mappings_projection_at(krnl, source_process); kernel_pagetable_mappings_projection_at(krnl, target_process);
    ipc_pages_lock_tables_step_pre_from_u(kernel_k_to_kernel_u(*krnl), cpu_id, endpoint_index, tables);
}

/// The cpu, the running thread recording a pages rendezvous locked as `tables`, its peer, the channel, the sender's page table read-held, and the
/// receiver's held as `tables` records on `krnl` give the check pre and the user-view context of the check step.
pub(super) proof fn ipc_pages_check_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, peer_ptr: RwLockThreadPtr, channel_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    source_thread: RwLockThreadPtr, target_thread: RwLockThreadPtr, source_process: RwLockProcessPtr, target_process: RwLockProcessPtr,
    source_pagetable: RwLockPageTableRoot, target_pagetable: RwLockPageTableRoot, tables: IpcPagesTables,
)
    requires
        edp_idx_valid(endpoint_index),
        typed_lock_maps_aligned(krnl, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), peer_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.endpoint_lock_map(), channel_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), source_pagetable, TypedLockMode::Read),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), target_pagetable, if tables is Fill { TypedLockMode::Write } else { TypedLockMode::Read }),
        krnl.thr_mp.dom().contains(thread_ptr),
        krnl.thr_mp.dom().contains(peer_ptr),
        krnl.cpu_arr.spec_index(cpu_id).value.view().view().current_process is Some,
        krnl.cpu_arr.spec_index(cpu_id).value.view().view().current_thread == Some(thread_ptr),
        tables is Read || tables is Fill,
        ({
            let progress = krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view();
            &&& progress is Some
            &&& progress->Some_0 is IpcPages
            &&& progress->Some_0->IpcPages_peer == peer_ptr
            &&& progress->Some_0->IpcPages_tables == tables
            &&& progress->Some_0->IpcPages_released is None
        }),
        krnl.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[endpoint_index as int] == Some(channel_ptr),
        source_thread == thread_ptr && target_thread == peer_ptr || source_thread == peer_ptr && target_thread == thread_ptr,
        krnl.thr_mp.spec_index(peer_ptr).view().state == (ThreadState::IPC_TRANSIT { partner: thread_ptr, wait: if source_thread == thread_ptr { IpcWait::Receive } else { IpcWait::Send } }),
        krnl.thr_mp.spec_index(source_thread).view().owning_proc == source_process,
        krnl.thr_mp.spec_index(target_thread).view().owning_proc == target_process,
        source_process != target_process,
        krnl.prc_mp.dom().contains(source_process),
        krnl.prc_mp.dom().contains(target_process),
        !krnl.prc_mp.spec_index(source_process).view().zombie,
        !krnl.prc_mp.spec_index(target_process).view().zombie,
        krnl.prc_mp.spec_index(source_process).view().pagetable == source_pagetable,
        krnl.prc_mp.spec_index(target_process).view().pagetable == target_pagetable,
    ensures
        ipc_pages_check_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, endpoint_index),
        ({
            let pre = kernel_k_to_kernel_u(*krnl);
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& pre.thread_map[thread_ptr].syscall_progress == krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()
            &&& pre.thread_map[ipc_pages_sender(pre, cpu_id)].owning_proc == source_process
            &&& pre.thread_map[ipc_pages_receiver(pre, cpu_id)].owning_proc == target_process
        }),
{
    krnl.ep_mp.typed_lock_map_aligned_write_at(lctx.endpoint_lock_map(), lctx.thread_id(), channel_ptr);
    krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), source_pagetable);
    if tables is Fill { krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), target_pagetable); }
    else { krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), target_pagetable); }
    kernel_write_held_context_projection(krnl, lctx, cpu_id, source_process, thread_ptr, Some(channel_ptr)); kernel_write_held_context_projection(krnl, lctx, cpu_id, target_process, peer_ptr, None);
    kernel_cpu_thread_projection_at(krnl, cpu_id, source_process, peer_ptr, None); kernel_thread_projection_at(krnl, thread_ptr);
    kernel_pagetable_mappings_projection_at(krnl, source_process); kernel_pagetable_mappings_projection_at(krnl, target_process);
    ipc_pages_check_step_pre_from_u(kernel_k_to_kernel_u(*krnl), cpu_id, endpoint_index);
}

/// The pages checks on `krnl`, in the implementation's order and on the running thread's recorded ranges, give `ret` as the check result on
/// its user projection. A target leaf the free check meets is visible: the target page table has every leaf present, or it is not
/// write-locked and every existing 2M window of the target range has its leaves present.
pub(super) proof fn ipc_pages_check_result_from_k(
    krnl: &KernelK, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, peer_ptr: RwLockThreadPtr, source_thread: RwLockThreadPtr, target_thread: RwLockThreadPtr,
    source_process: RwLockProcessPtr, target_process: RwLockProcessPtr, source_pagetable: RwLockPageTableRoot, target_pagetable: RwLockPageTableRoot,
    target_container: RwLockContainerPtr, source_range: VaRange4K, target_range: VaRange4K, tables: IpcPagesTables, ret: RetValueType,
    found: Option<(L4Index, L3Index, L2Index, L1Index)>,
)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        krnl.thr_mp.dom().contains(thread_ptr),
        krnl.thr_mp.dom().contains(peer_ptr),
        krnl.cpu_arr.spec_index(cpu_id).value.view().view().current_thread == Some(thread_ptr),
        krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::IpcPages { source_range, target_range, peer: peer_ptr, tables, released: None }),
        source_thread == thread_ptr && target_thread == peer_ptr || source_thread == peer_ptr && target_thread == thread_ptr,
        krnl.thr_mp.spec_index(peer_ptr).view().state == (ThreadState::IPC_TRANSIT { partner: thread_ptr, wait: if source_thread == thread_ptr { IpcWait::Receive } else { IpcWait::Send } }),
        krnl.thr_mp.spec_index(source_thread).view().owning_proc == source_process,
        krnl.thr_mp.spec_index(target_thread).view().owning_proc == target_process,
        krnl.thr_mp.spec_index(target_thread).view().owning_container == target_container,
        krnl.ctn_mp.dom().contains(target_container),
        krnl.prc_mp.dom().contains(source_process),
        krnl.prc_mp.dom().contains(target_process),
        !krnl.prc_mp.spec_index(source_process).view().zombie,
        !krnl.prc_mp.spec_index(target_process).view().zombie,
        krnl.prc_mp.spec_index(source_process).view().pagetable == source_pagetable,
        krnl.prc_mp.spec_index(target_process).view().pagetable == target_pagetable,
        krnl.pt_mp.dom().contains(source_pagetable),
        krnl.pt_mp.dom().contains(target_pagetable),
        source_range.wf(),
        target_range.wf(),
        target_range.len > 0,
        ({
            let source_table = pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable);
            let target_table = pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable);
            let target_start = spec_va2index(target_range.start);
            let target_end = spec_va2index(target_range.view().spec_index(target_range.len - 1));
            let target_clear = target_table.spec_mapping_4k_range_empty(target_start, target_end) && forall|j: int| #![trigger target_range.view().spec_index(j)] 0 <= j < target_range.len ==> {
                let indices = spec_va2index(target_range.view().spec_index(j));
                &&& !target_table.mapping_1g().dom().contains(spec_index2va((indices.0, indices.1, 0, 0)))
                &&& !target_table.mapping_2m().dom().contains(spec_index2va((indices.0, indices.1, indices.2, 0)))
                &&& !target_table.mapping_4k().dom().contains(target_range.view().spec_index(j))
            };
            &&& ret == if spec_va2index(source_range.start).0 < source_table.kernel_l4_end() { RetValueType::Error }
                else if !(forall|j: int| #![trigger source_range.view().spec_index(j)] 0 <= j < source_range.len ==> {
                    &&& source_table.mapping_4k().dom().contains(source_range.view().spec_index(j))
                    &&& source_table.mapping_4k().spec_index(source_range.view().spec_index(j)).present
                }) { RetValueType::ErrorIpcSourceUnmapped }
                else if krnl.thr_mp.spec_index(target_thread).view().quota_4k < 3 * target_range.len { RetValueType::ErrorNoQuota }
                else if spec_va2index(target_range.start).0 < target_table.kernel_l4_end() { RetValueType::Error }
                else if !target_clear { RetValueType::ErrorVaInUse }
                else if !share_mapping_4k_range_owner_compatible(krnl, source_pagetable, target_container, &source_range) { RetValueType::ErrorIpcPageOwnerMismatch }
                else { RetValueType::Success }
            &&& ret is ErrorVaInUse ==> target_table.leaves_present() || {
                &&& !(krnl.pt_mp.spec_index(target_pagetable).locking_thread() is Write)
                &&& forall|w: WindowVa| #![trigger va_range_2m_windows(target_range).contains(w)]
                    va_range_2m_windows(target_range).contains(w) && target_table.higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> target_table.window_leaves_present(w)
            }
            &&& ret is ErrorVaInUse && found is Some ==> {
                let f = found->Some_0;
                &&& pei_valid(f.0) && pei_valid(f.1) && pei_valid(f.2) && pei_valid(f.3)
                &&& spec_l4_index_path_le(target_start, f)
                &&& spec_l4_index_path_le(f, target_end)
                &&& target_table.mapping_4k().dom().contains(spec_index2va(f))
            }
            &&& ret is ErrorVaInUse && found is None ==> target_table.spec_mapping_4k_range_empty(target_start, target_end)
            &&& ret is ErrorVaInUse && found is None ==> target_table.spec_mapping_4k_va_range_empty(target_range.start, target_range.view().spec_index(target_range.len - 1))
        }),
    ensures ipc_pages_check_result(kernel_k_to_kernel_u(*krnl), cpu_id) == ret,
{
    kernel_cpu_thread_projection_at(krnl, cpu_id, source_process, thread_ptr, None); kernel_thread_projection_at(krnl, peer_ptr);
    kernel_process_projection_at(krnl, source_process); kernel_process_projection_at(krnl, target_process);
    kernel_l4_end_projection_at(krnl, source_pagetable); kernel_l4_end_projection_at(krnl, target_pagetable); kernel_container_ancestry_projection_at(krnl, target_container);
    let checked = pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable);
    if ret is ErrorVaInUse {
        let u_table = kernel_k_to_kernel_u(*krnl).process_map[target_process].pagetable->Some_0;
        pagetable_hidden_leaves_only_when_locked_at(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable);
        target_range.va_range_lemma();
        if found is Some {
            let f = found->Some_0;
            let fv = spec_index2va((f.0, f.1, f.2, f.3));
            spec_va_4k_index_roundtrip_at(fv, f.0, f.1, f.2, f.3);
            if !checked.leaves_present() { va_range_2m_windows_contains_window_of_every_va_in_range(target_range); checked.wf_mapping_4k_at(f.0, f.1, f.2, f.3); }
            assert(checked.mapping_4k().spec_index(fv).present);
            assert(u_table.mapping_4k.dom().contains(fv));
        } else {
            reveal(PageTableC::spec_mapping_4k_va_range_empty);
        }
    }
}

/// The cpu, the running thread that shared every page of a pages rendezvous, its peer, and both page tables read-held on `krnl` give the
/// unlock-tables pre and the user-view context of the unlock-tables step.
pub(super) proof fn ipc_pages_unlock_tables_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, peer_ptr: RwLockThreadPtr, source_thread: RwLockThreadPtr,
    target_thread: RwLockThreadPtr, source_process: RwLockProcessPtr, target_process: RwLockProcessPtr, source_pagetable: RwLockPageTableRoot,
    target_pagetable: RwLockPageTableRoot, source_range: VaRange4K, target_range: VaRange4K,
)
    requires
        typed_lock_maps_aligned(krnl, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), peer_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), source_pagetable, TypedLockMode::Read),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), target_pagetable, TypedLockMode::Read),
        krnl.thr_mp.dom().contains(thread_ptr),
        krnl.thr_mp.dom().contains(peer_ptr),
        krnl.cpu_arr.spec_index(cpu_id).value.view().view().current_process is Some,
        krnl.cpu_arr.spec_index(cpu_id).value.view().view().current_thread == Some(thread_ptr),
        krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Share4k {
            source_range, target_range, shared: source_range.len, directory: krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->Share4k_directory, origin: Share4kOrigin::IpcPages { peer: peer_ptr },
        }),
        source_thread == thread_ptr && target_thread == peer_ptr || source_thread == peer_ptr && target_thread == thread_ptr,
        krnl.thr_mp.spec_index(peer_ptr).view().state == (ThreadState::IPC_TRANSIT { partner: thread_ptr, wait: if source_thread == thread_ptr { IpcWait::Receive } else { IpcWait::Send } }),
        krnl.thr_mp.spec_index(source_thread).view().owning_proc == source_process,
        krnl.thr_mp.spec_index(target_thread).view().owning_proc == target_process,
        krnl.ctn_mp.dom().contains(krnl.thr_mp.spec_index(target_thread).view().owning_container),
        source_process != target_process,
        krnl.prc_mp.dom().contains(source_process),
        krnl.prc_mp.dom().contains(target_process),
        !krnl.prc_mp.spec_index(source_process).view().zombie,
        !krnl.prc_mp.spec_index(target_process).view().zombie,
        krnl.prc_mp.spec_index(source_process).view().pagetable == source_pagetable,
        krnl.prc_mp.spec_index(target_process).view().pagetable == target_pagetable,
    ensures
        ipc_pages_unlock_tables_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        ({
            let pre = kernel_k_to_kernel_u(*krnl);
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& pre.thread_map[thread_ptr].syscall_progress == krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()
            &&& share_4k_objects(pre, cpu_id).target == target_process
            &&& pre.thread_map[share_4k_objects(pre, cpu_id).source_thread].owning_proc == source_process
        }),
{
    reveal(share_4k_objects_k);
    krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), source_pagetable); krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), target_pagetable);
    kernel_write_held_context_projection(krnl, lctx, cpu_id, source_process, thread_ptr, None); kernel_write_held_context_projection(krnl, lctx, cpu_id, target_process, peer_ptr, None);
    kernel_cpu_thread_projection_at(krnl, cpu_id, source_process, peer_ptr, None); kernel_share_4k_objects_projection(krnl, lctx, cpu_id);
    kernel_pagetable_mappings_projection_at(krnl, source_process); kernel_pagetable_mappings_projection_at(krnl, target_process);
    ipc_pages_unlock_tables_step_pre_from_u(kernel_k_to_kernel_u(*krnl), cpu_id);
}

/// The unlocked rendezvous context on `pre` whose queue head carries a same-length Pages payload from another
/// process is the pages enter pre.
pub(super) proof fn ipc_pages_enter_step_pre_from_u(
    pre: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, channel_ptr: RwLockEndpointPtr, peer_ptr: RwLockThreadPtr,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, range: VaRange4K, peer_range: VaRange4K,
)
    requires
        range.wf(),
        range.len > 0,
        {
            let cpu = pre.cpu_array[cpu_id as int];
            let caller = pre.thread_map.spec_index(thread_ptr);
            let peer = pre.thread_map.spec_index(peer_ptr);
            let channel = pre.endpoint_map.spec_index(channel_ptr);
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& cpu.lock_state is Unlocked
            &&& cpu.state is Running
            &&& cpu.current_process == Some(process_ptr)
            &&& cpu.current_thread == Some(thread_ptr)
            &&& pre.process_map.dom().contains(process_ptr)
            &&& pre.thread_map.dom().contains(thread_ptr)
            &&& caller.lock_state is Unlocked
            &&& caller.syscall_progress is None
            &&& !caller.killed
            &&& caller.state == (ThreadState::RUNNING { cpu_id })
            &&& caller.owning_proc == process_ptr
            &&& pre.container_map.dom().contains(caller.owning_container)
            &&& edp_idx_valid(endpoint_index)
            &&& caller.endpoint_descriptors[endpoint_index as int] == Some(channel_ptr)
            &&& pre.endpoint_map.dom().contains(channel_ptr)
            &&& channel.lock_state is Unlocked
            &&& !channel.queue.contains(thread_ptr)
            &&& waiting_state is SENDING || waiting_state is RECEIVING
            &&& channel.queue.len() > 0
            &&& channel.queue[0] == peer_ptr
            &&& (channel.queue_state is SEND) != (waiting_state is SENDING)
            &&& pre.thread_map.dom().contains(peer_ptr)
            &&& peer.lock_state is Unlocked
            &&& peer_ptr != thread_ptr
            &&& !peer.killed
            &&& peer.state == (if waiting_state is SENDING { ThreadState::RECEIVING } else { ThreadState::SENDING })
            &&& peer.blocking_endpoint_ptr == Some(channel_ptr)
            &&& pre.container_map.dom().contains(peer.owning_container)
            &&& peer.ipc_payload == (IPCPayLoad::Pages { va_range: peer_range })
            &&& peer_range.len == range.len
            &&& peer.owning_proc != process_ptr
        },
    ensures
        ipc_pages_enter_step_pre(pre, cpu_id, endpoint_index, waiting_state, range),
{ reveal(ipc_pages_enter_step_pre); reveal(ipc_rendezvous_step_pre); reveal(ipc_step_pre); }

/// Write-locking the rendezvous context, moving the queue head into transit with the caller, and recording both ranges is the pages enter
/// step on `pre`/`post`.
pub(super) proof fn ipc_pages_enter_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, channel_ptr: RwLockEndpointPtr,
    peer_ptr: RwLockThreadPtr, endpoint_index: EndpointIdx, waiting_state: ThreadState, source_range: VaRange4K, target_range: VaRange4K,
)
    requires
        pre.cpu_array[cpu_id as int].current_process == Some(process_ptr),
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.thread_map[thread_ptr].endpoint_descriptors[endpoint_index as int] == Some(channel_ptr),
        pre.endpoint_map[channel_ptr].queue[0] == peer_ptr,
        pre.thread_map[peer_ptr].ipc_payload == (IPCPayLoad::Pages { va_range: if waiting_state is SENDING { target_range } else { source_range } }),
        post == (KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, op: CpuOpState::InStep, ..pre.cpu_array[cpu_id as int] }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU {
                lock_state: LockStateU::WriteLocked,
                syscall_progress: Some(SyscallProgress::IpcPages { source_range, target_range, peer: peer_ptr, tables: IpcPagesTables::Unlocked, released: None }),
                ..pre.thread_map[thread_ptr]
            }).insert(peer_ptr, ThreadU { lock_state: LockStateU::WriteLocked, blocking_endpoint_ptr: None,
                state: ThreadState::IPC_TRANSIT { partner: thread_ptr, wait: if pre.thread_map[peer_ptr].state is SENDING { IpcWait::Send } else { IpcWait::Receive } }, ..pre.thread_map[peer_ptr] }),
            endpoint_map: pre.endpoint_map.insert(channel_ptr, EndpointU {
                lock_state: LockStateU::WriteLocked, queue: pre.endpoint_map[channel_ptr].queue.skip(1), ..pre.endpoint_map[channel_ptr]
            }),
            ..pre
        }),
    ensures
        ipc_pages_enter_step(pre, post, cpu_id, endpoint_index, waiting_state, if waiting_state is SENDING { source_range } else { target_range }),
{ reveal(ipc_pages_enter_step); }

/// The held pages context on `pre` with both page tables present, the sender's not write-locked, and the receiver's unlocked to fill it
/// or not write-locked to read it as `tables` asks, is the lock-tables pre.
pub(super) proof fn ipc_pages_lock_tables_step_pre_from_u(pre: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, tables: IpcPagesTables)
    requires
        {
            let progress = pre.thread_map[pre.cpu_array[cpu_id as int].current_thread->Some_0].syscall_progress->Some_0;
            let source = pre.process_map[pre.thread_map[ipc_pages_sender(pre, cpu_id)].owning_proc].pagetable->Some_0;
            let target = pre.process_map[pre.thread_map[ipc_pages_receiver(pre, cpu_id)].owning_proc].pagetable->Some_0;
            &&& ipc_pages_held(pre, cpu_id, endpoint_index)
            &&& progress->IpcPages_tables is Unlocked
            &&& progress->IpcPages_released is None
            &&& tables is Read || tables is Fill
            &&& ipc_pages_tables_present(pre, cpu_id)
            &&& !(source.lock_state is WriteLocked)
            &&& if tables is Fill { target.lock_state is Unlocked } else { !(target.lock_state is WriteLocked) }
        },
    ensures ipc_pages_lock_tables_step_pre(pre, cpu_id, endpoint_index, tables),
{ reveal(ipc_pages_lock_tables_step_pre); }

/// Read-locking the sender's page table, read-locking or write-locking the receiver's as `tables` records, leaving `source_windows` and
/// `target_windows` the K-state window locks after locking both ranges' windows when both are user ranges, and recording `tables` is the
/// lock-tables step on `pre`/`post`.
pub(super) proof fn ipc_pages_lock_tables_step_from_u(
    pre: KernelU, post: KernelU, pre_k: &KernelK, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, source_range: VaRange4K, target_range: VaRange4K, peer_ptr: RwLockThreadPtr,
    source: RwLockProcessPtr, target: RwLockProcessPtr, source_table: RwLockPageTableRoot, target_table: RwLockPageTableRoot, tables: IpcPagesTables,
    source_windows: Map<WindowVa, LockStateU>, target_windows: Map<WindowVa, LockStateU>,
)
    requires
        pre == kernel_k_to_kernel_u(*pre_k),
        pre_k.inv(),
        pre_k.prc_mp.dom().contains(source),
        pre_k.prc_mp.dom().contains(target),
        !pre_k.prc_mp.spec_index(source).view().zombie,
        !pre_k.prc_mp.spec_index(target).view().zombie,
        pre_k.prc_mp.spec_index(source).view().pagetable == source_table,
        pre_k.prc_mp.spec_index(target).view().pagetable == target_table,
        pre_k.pt_mp.dom().contains(source_table),
        pre_k.pt_mp.dom().contains(target_table),
        {
            let source_c = pagetable_c(pre_k.pt_mp, pre_k.pt_lower.view(), source_table);
            let target_c = pagetable_c(pre_k.pt_mp, pre_k.pt_lower.view(), target_table);
            let user = source_c.kernel_l4_end() <= spec_va2index(source_range.start).0 && target_c.kernel_l4_end() <= spec_va2index(target_range.start).0;
            &&& source_windows == if user { pagetable_window_locks_after_locking_range(source_c.lower.pagetable_window_locks, source_range) } else { source_c.lower.pagetable_window_locks }
            &&& target_windows == if user { pagetable_window_locks_after_locking_range(target_c.lower.pagetable_window_locks, target_range) } else { target_c.lower.pagetable_window_locks }
        },
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.thread_map[thread_ptr].syscall_progress == Some(SyscallProgress::IpcPages { source_range, target_range, peer: peer_ptr, tables: IpcPagesTables::Unlocked, released: None }),
        pre.thread_map[ipc_pages_sender(pre, cpu_id)].owning_proc == source,
        pre.thread_map[ipc_pages_receiver(pre, cpu_id)].owning_proc == target,
        post == (KernelU {
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { syscall_progress: Some(SyscallProgress::IpcPages { source_range, target_range, peer: peer_ptr, tables, released: None }), ..pre.thread_map[thread_ptr] }),
            process_map: pre.process_map.insert(source, ProcessU {
                pagetable: Some(PageTableU { lock_state: LockStateU::ReadLocked, pagetable_window_locks: source_windows, ..pre.process_map[source].pagetable->Some_0 }), ..pre.process_map[source]
            }).insert(target, ProcessU {
                pagetable: Some(PageTableU { lock_state: if tables is Fill { LockStateU::WriteLocked } else { LockStateU::ReadLocked }, pagetable_window_locks: target_windows, ..pre.process_map[target].pagetable->Some_0 }), ..pre.process_map[target]
            }),
            ..pre
        }),
    ensures ipc_pages_lock_tables_step(pre, post, cpu_id, tables),
{ reveal(ipc_pages_lock_tables_step); kernel_process_projection_at(pre_k, source); kernel_process_projection_at(pre_k, target); kernel_l4_end_projection_at(pre_k, source_table); kernel_l4_end_projection_at(pre_k, target_table); }

/// The held pages context on `pre` with the sender's page table read-locked, the receiver's held as the recorded tables mode asks, and
/// nothing released is the check pre.
pub(super) proof fn ipc_pages_check_step_pre_from_u(pre: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx)
    requires
        {
            let progress = pre.thread_map[pre.cpu_array[cpu_id as int].current_thread->Some_0].syscall_progress->Some_0;
            let source = pre.process_map[pre.thread_map[ipc_pages_sender(pre, cpu_id)].owning_proc].pagetable->Some_0;
            let target = pre.process_map[pre.thread_map[ipc_pages_receiver(pre, cpu_id)].owning_proc].pagetable->Some_0;
            &&& ipc_pages_held(pre, cpu_id, endpoint_index)
            &&& progress->IpcPages_tables is Read || progress->IpcPages_tables is Fill
            &&& progress->IpcPages_released is None
            &&& ipc_pages_tables_present(pre, cpu_id)
            &&& source.lock_state is ReadLocked
            &&& target.lock_state == if progress->IpcPages_tables is Fill { LockStateU::WriteLocked } else { LockStateU::ReadLocked }
        },
    ensures ipc_pages_check_step_pre(pre, cpu_id, endpoint_index),
{ reveal(ipc_pages_check_step_pre); }

/// Recording a passed check as the start of sharing is the check step on `pre`/`post`.
pub(super) proof fn ipc_pages_passed_check_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, source_range: VaRange4K, target_range: VaRange4K, peer_ptr: RwLockThreadPtr, tables: IpcPagesTables,
)
    requires
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.thread_map[thread_ptr].syscall_progress == Some(SyscallProgress::IpcPages { source_range, target_range, peer: peer_ptr, tables, released: None }),
        ipc_pages_check_result(pre, cpu_id) is Success,
        post == (KernelU {
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU {
                syscall_progress: Some(SyscallProgress::Share4k { source_range, target_range, shared: 0, directory: Mmap4kDirectory::None, origin: Share4kOrigin::IpcPages { peer: peer_ptr } }),
                ..pre.thread_map[thread_ptr]
            }),
            ..pre
        }),
    ensures ipc_pages_check_step(pre, post, cpu_id),
{ reveal(ipc_pages_check_step); }

/// Recording the share progress on the running thread of a passed pages check, with only that thread's progress changed from `pre` to
/// `post`, is the check step on their user projections.
pub(super) proof fn ipc_pages_passed_check_step_from_k(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, source_range: VaRange4K, target_range: VaRange4K, peer_ptr: RwLockThreadPtr, tables: IpcPagesTables,
)
    requires
        *post == (KernelK { thr_mp: post.thr_mp, ..*pre }),
        pre.thr_mp.dom().contains(thread_ptr),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..pre.thr_mp.spec_index(thread_ptr).view() }),
        post.thr_mp.spec_index(thread_ptr).locking_thread() == pre.thr_mp.spec_index(thread_ptr).locking_thread(),
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
        index_valid(NUM_CPUS, cpu_id),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::IpcPages { source_range, target_range, peer: peer_ptr, tables, released: None }),
        post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Share4k { source_range, target_range, shared: 0, directory: Mmap4kDirectory::None, origin: Share4kOrigin::IpcPages { peer: peer_ptr } }),
        ipc_pages_check_result(kernel_k_to_kernel_u(*pre), cpu_id) is Success,
    ensures ipc_pages_check_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id),
{
    kernel_thread_syscall_progress_changed_implies_u_step(pre, post, thread_ptr); kernel_cpu_projection_at(pre, cpu_id); kernel_thread_projection_at(pre, thread_ptr);
    ipc_pages_passed_check_step_from_u(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id, thread_ptr, source_range, target_range, peer_ptr, tables);
}

/// Recording a failed check while releasing both page tables, which other readers may still hold, and leaving `source_windows` and
/// `target_windows` the K-state window locks after unlocking both ranges' windows when both are user ranges, is the check step on
/// `pre`/`post`.
pub(super) proof fn ipc_pages_failed_check_step_from_u(
    pre: KernelU, post: KernelU, pre_k: &KernelK, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, source_range: VaRange4K, target_range: VaRange4K, peer_ptr: RwLockThreadPtr,
    tables: IpcPagesTables, result: RetValueType, source: RwLockProcessPtr, target: RwLockProcessPtr, source_table: RwLockPageTableRoot, target_table: RwLockPageTableRoot,
    source_state: LockStateU, target_state: LockStateU, source_windows: Map<WindowVa, LockStateU>, target_windows: Map<WindowVa, LockStateU>,
)
    requires
        pre == kernel_k_to_kernel_u(*pre_k),
        pre_k.inv(),
        pre_k.prc_mp.dom().contains(source),
        pre_k.prc_mp.dom().contains(target),
        !pre_k.prc_mp.spec_index(source).view().zombie,
        !pre_k.prc_mp.spec_index(target).view().zombie,
        pre_k.prc_mp.spec_index(source).view().pagetable == source_table,
        pre_k.prc_mp.spec_index(target).view().pagetable == target_table,
        pre_k.pt_mp.dom().contains(source_table),
        pre_k.pt_mp.dom().contains(target_table),
        {
            let source_c = pagetable_c(pre_k.pt_mp, pre_k.pt_lower.view(), source_table);
            let target_c = pagetable_c(pre_k.pt_mp, pre_k.pt_lower.view(), target_table);
            let user = source_c.kernel_l4_end() <= spec_va2index(source_range.start).0 && target_c.kernel_l4_end() <= spec_va2index(target_range.start).0;
            &&& source_windows == if user { pagetable_window_locks_after_unlocking_range(source_c.lower.pagetable_window_locks, source_range) } else { source_c.lower.pagetable_window_locks }
            &&& target_windows == if user { pagetable_window_locks_after_unlocking_range(target_c.lower.pagetable_window_locks, target_range) } else { target_c.lower.pagetable_window_locks }
        },
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.thread_map[thread_ptr].syscall_progress == Some(SyscallProgress::IpcPages { source_range, target_range, peer: peer_ptr, tables, released: None }),
        result == ipc_pages_check_result(pre, cpu_id),
        !(result is Success),
        source != target,
        pre.thread_map[ipc_pages_sender(pre, cpu_id)].owning_proc == source,
        pre.thread_map[ipc_pages_receiver(pre, cpu_id)].owning_proc == target,
        source_state is Unlocked || source_state is ReadLocked,
        target_state is Unlocked || target_state is ReadLocked,
        post == (KernelU {
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { syscall_progress: Some(SyscallProgress::IpcPages { source_range, target_range, peer: peer_ptr, tables: IpcPagesTables::Unlocked, released: Some(result) }), ..pre.thread_map[thread_ptr] }),
            process_map: pre.process_map.insert(source, ProcessU {
                pagetable: Some(PageTableU { lock_state: source_state, pagetable_window_locks: source_windows, ..pre.process_map[source].pagetable->Some_0 }), ..pre.process_map[source]
            }).insert(target, ProcessU {
                pagetable: Some(PageTableU { lock_state: target_state, pagetable_window_locks: target_windows, ..pre.process_map[target].pagetable->Some_0 }), ..pre.process_map[target]
            }),
            ..pre
        }),
    ensures ipc_pages_check_step(pre, post, cpu_id),
{ reveal(ipc_pages_check_step); kernel_process_projection_at(pre_k, source); kernel_process_projection_at(pre_k, target); kernel_l4_end_projection_at(pre_k, source_table); kernel_l4_end_projection_at(pre_k, target_table); }

/// The fully shared pages context on `pre` with both page tables read-locked is the unlock-tables pre.
pub(super) proof fn ipc_pages_unlock_tables_step_pre_from_u(pre: KernelU, cpu_id: CpuId)
    requires
        {
            let progress = pre.thread_map[pre.cpu_array[cpu_id as int].current_thread->Some_0].syscall_progress->Some_0;
            let objects = share_4k_objects(pre, cpu_id);
            let source = pre.thread_map[objects.source_thread].owning_proc;
            &&& share_4k_locked(pre, cpu_id)
            &&& progress->Share4k_origin is IpcPages
            &&& pre.thread_map[progress->Share4k_origin->IpcPages_peer].state is IPC_TRANSIT
            &&& progress->Share4k_shared == progress->Share4k_source_range.len
            &&& source != objects.target
            &&& pre.process_map.dom().contains(source)
            &&& pre.process_map.dom().contains(objects.target)
            &&& pre.process_map[source].pagetable is Some
            &&& pre.process_map[objects.target].pagetable is Some
            &&& pre.process_map[source].pagetable->Some_0.lock_state is ReadLocked
            &&& pre.process_map[objects.target].pagetable->Some_0.lock_state is ReadLocked
        },
    ensures ipc_pages_unlock_tables_step_pre(pre, cpu_id),
{ reveal(ipc_pages_unlock_tables_step_pre); }

/// Releasing both page tables after sharing, which other readers may still hold, leaving `source_windows` and `target_windows` the K-state
/// window locks after unlocking both ranges' windows, and recording Success is the unlock-tables step on `pre`/`post`.
pub(super) proof fn ipc_pages_unlock_tables_step_from_u(
    pre: KernelU, post: KernelU, pre_k: &KernelK, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, source_range: VaRange4K, target_range: VaRange4K, peer_ptr: RwLockThreadPtr,
    source: RwLockProcessPtr, target: RwLockProcessPtr, source_table: RwLockPageTableRoot, target_table: RwLockPageTableRoot, source_state: LockStateU, target_state: LockStateU,
    source_windows: Map<WindowVa, LockStateU>, target_windows: Map<WindowVa, LockStateU>,
)
    requires
        pre == kernel_k_to_kernel_u(*pre_k),
        pre_k.inv(),
        pre_k.prc_mp.dom().contains(source),
        pre_k.prc_mp.dom().contains(target),
        !pre_k.prc_mp.spec_index(source).view().zombie,
        !pre_k.prc_mp.spec_index(target).view().zombie,
        pre_k.prc_mp.spec_index(source).view().pagetable == source_table,
        pre_k.prc_mp.spec_index(target).view().pagetable == target_table,
        pre_k.pt_mp.dom().contains(source_table),
        pre_k.pt_mp.dom().contains(target_table),
        source_windows == pagetable_window_locks_after_unlocking_range(pagetable_c(pre_k.pt_mp, pre_k.pt_lower.view(), source_table).lower.pagetable_window_locks, source_range),
        target_windows == pagetable_window_locks_after_unlocking_range(pagetable_c(pre_k.pt_mp, pre_k.pt_lower.view(), target_table).lower.pagetable_window_locks, target_range),
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.thread_map[thread_ptr].syscall_progress == Some(SyscallProgress::Share4k { source_range, target_range, shared: source_range.len, directory: pre.thread_map[thread_ptr].syscall_progress->Some_0->Share4k_directory, origin: Share4kOrigin::IpcPages { peer: peer_ptr } }),
        share_4k_objects(pre, cpu_id).target == target,
        pre.thread_map[share_4k_objects(pre, cpu_id).source_thread].owning_proc == source,
        source != target,
        source_state is Unlocked || source_state is ReadLocked,
        target_state is Unlocked || target_state is ReadLocked,
        post == (KernelU {
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU {
                syscall_progress: Some(SyscallProgress::IpcPages { source_range, target_range, peer: peer_ptr, tables: IpcPagesTables::Unlocked, released: Some(RetValueType::Success) }),
                ..pre.thread_map[thread_ptr]
            }),
            process_map: pre.process_map.insert(source, ProcessU {
                pagetable: Some(PageTableU { lock_state: source_state, pagetable_window_locks: source_windows, ..pre.process_map[source].pagetable->Some_0 }), ..pre.process_map[source]
            }).insert(target, ProcessU {
                pagetable: Some(PageTableU { lock_state: target_state, pagetable_window_locks: target_windows, ..pre.process_map[target].pagetable->Some_0 }), ..pre.process_map[target]
            }),
            ..pre
        }),
    ensures ipc_pages_unlock_tables_step(pre, post, cpu_id),
{ reveal(ipc_pages_unlock_tables_step); kernel_process_projection_at(pre_k, source); kernel_process_projection_at(pre_k, target); }

/// Scheduling the transit peer with the released result while releasing the pages context is the pages
/// finish step on `pre`/`post`.
pub(super) proof fn ipc_pages_finish_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, peer_ptr: RwLockThreadPtr, channel_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx, result: RetValueType, wake_cpu: CpuId,
)
    requires
        wake_cpu == if pre.thread_map[peer_ptr].owning_container == pre.thread_map[thread_ptr].owning_container { cpu_id } else { pre.thread_map[peer_ptr].last_cpu },
        {
            let progress = pre.thread_map[thread_ptr].syscall_progress;
            &&& ipc_pages_held(pre, cpu_id, endpoint_index)
            &&& pre.cpu_array[cpu_id as int].current_process == Some(process_ptr)
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& progress->Some_0->IpcPages_peer == peer_ptr
            &&& progress->Some_0->IpcPages_released == Some(result)
            &&& progress->Some_0->IpcPages_tables is Unlocked
            &&& pre.thread_map[thread_ptr].endpoint_descriptors[endpoint_index as int] == Some(channel_ptr)
            &&& pre.container_map.dom().contains(pre.thread_map[peer_ptr].owning_container)
        },
        {
            let container = pre.thread_map[peer_ptr].owning_container;
            post == (KernelU {
                cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: cpu_op_after_step(pre.cpu_array[cpu_id as int].state), ..pre.cpu_array[cpu_id as int] }),
                container_map: pre.container_map.insert(container, ContainerU {
                    scheduler: pre.container_map[container].scheduler.update(wake_cpu as int, pre.container_map[container].scheduler[wake_cpu as int].push(peer_ptr)), ..pre.container_map[container]
                }),
                thread_map: pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..pre.thread_map[thread_ptr] }).insert(peer_ptr, ThreadU {
                    lock_state: LockStateU::Unlocked, state: ThreadState::SCHEDULED { cpu_id: wake_cpu }, blocking_endpoint_ptr: None, ipc_payload: IPCPayLoad::Empty, error_code: Some(result), ..pre.thread_map[peer_ptr]
                }),
                endpoint_map: pre.endpoint_map.insert(channel_ptr, EndpointU { lock_state: LockStateU::Unlocked, queue: pre.endpoint_map[channel_ptr].queue,
                    owning_threads: pre.endpoint_map[channel_ptr].owning_threads, ..pre.endpoint_map[channel_ptr]
                }),
                ..pre
            })
        },
    ensures
        ipc_pages_finish_step_pre(pre, cpu_id, endpoint_index),
        ipc_pages_finish_step(pre, post, cpu_id, endpoint_index),
{ reveal(ipc_pages_finish_step_pre); reveal(ipc_pages_finish_step); }

/// The enter step pushed since `before` is the partial pages trace after entering.
pub(super) proof fn ipc_pages_trace_enter_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, range: VaRange4K)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        ipc_pages_enter_step_pre(pre, cpu_id, endpoint_index, waiting_state, range),
        ipc_pages_enter_step(pre, post, cpu_id, endpoint_index, waiting_state, range),
    ensures
        ipc_pages_trace_after_enter(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, cpu_id, endpoint_index, waiting_state, range),
{ reveal(ipc_pages_trace_after_enter); }

/// The lock-tables step in mode `tables` pushed after the partial trace that starts at `start` is the partial trace after locking.
pub(super) proof fn ipc_pages_trace_lock_step(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, lock_pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx,
    waiting_state: ThreadState, range: VaRange4K, tables: IpcPagesTables,
)
    requires
        0 <= start <= before.len(),
        ipc_pages_trace_after_enter(before.subrange(start, before.len() as int), pre, cpu_id, endpoint_index, waiting_state, range),
        steps.view() == before.push(KernelStep { old_u: lock_pre, new_u: post }),
        ipc_pages_lock_tables_step_pre(lock_pre, cpu_id, endpoint_index, tables),
        ipc_pages_lock_tables_step(lock_pre, post, cpu_id, tables),
    ensures
        ipc_pages_trace_after_lock(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, endpoint_index, waiting_state, range, tables),
{ reveal(ipc_pages_trace_after_enter); reveal(ipc_pages_trace_after_lock); }

/// A failed check step pushed after the partial trace that starts at `start` completes the mapping trace.
pub(super) proof fn ipc_pages_trace_failed_check_step(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, check_pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx,
    waiting_state: ThreadState, range: VaRange4K, tables: IpcPagesTables, result: RetValueType,
)
    requires
        0 <= start <= before.len(),
        ipc_pages_trace_after_lock(before.subrange(start, before.len() as int), pre, cpu_id, endpoint_index, waiting_state, range, tables),
        tables is Read || tables is Fill,
        steps.view() == before.push(KernelStep { old_u: check_pre, new_u: post }),
        ipc_pages_check_step_pre(check_pre, cpu_id, endpoint_index),
        ipc_pages_check_step(check_pre, post, cpu_id),
        result == ipc_pages_check_result(check_pre, cpu_id),
        !(result is Success),
    ensures
        ipc_pages_mapping_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, endpoint_index, waiting_state, range, result),
{ reveal(ipc_pages_trace_after_lock); reveal(ipc_pages_mapping_trace); }

/// A passed check step and the directory, downgrade, and share steps pushed after the partial trace that starts at `start` are the
/// partial trace after sharing.
pub(super) proof fn ipc_pages_trace_share_steps(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState,
    range: VaRange4K, tables: IpcPagesTables,
)
    requires
        0 <= start <= before.len(),
        ipc_pages_trace_after_lock(before.subrange(start, before.len() as int), pre, cpu_id, endpoint_index, waiting_state, range, tables),
        tables is Read || tables is Fill,
        before.len() + range.len + 1 <= steps.view().len() <= before.len() + 4 * range.len + 2,
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        ipc_pages_check_result(steps.view()[before.len() as int].old_u, cpu_id) is Success,
        ipc_pages_check_step_pre(steps.view()[before.len() as int].old_u, cpu_id, endpoint_index),
        ipc_pages_check_step(steps.view()[before.len() as int].old_u, steps.view()[before.len() as int].new_u, cpu_id),
        forall|j: int| #![trigger steps.view()[j]] before.len() < j < steps.view().len()
            ==> share_4k_range_step(steps.view()[j], cpu_id) || ipc_pages_downgrade_step_pre(steps.view()[j].old_u, cpu_id) && ipc_pages_downgrade_step(steps.view()[j].old_u, steps.view()[j].new_u, cpu_id),
    ensures
        ipc_pages_trace_after_share(steps.view(), start, pre, cpu_id, endpoint_index, waiting_state, range),
{ reveal(ipc_pages_trace_after_lock); reveal(ipc_pages_trace_after_share); }

/// The unlock-tables step pushed after the partial trace that starts at `start` completes the successful mapping trace.
pub(super) proof fn ipc_pages_trace_unlock_step(steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, unlock_pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, range: VaRange4K)
    requires
        0 <= start <= before.len(),
        ipc_pages_trace_after_share(before, start, pre, cpu_id, endpoint_index, waiting_state, range),
        steps.view() == before.push(KernelStep { old_u: unlock_pre, new_u: post }),
        ipc_pages_unlock_tables_step_pre(unlock_pre, cpu_id),
        ipc_pages_unlock_tables_step(unlock_pre, post, cpu_id),
    ensures
        ipc_pages_mapping_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, endpoint_index, waiting_state, range, RetValueType::Success),
{ reveal(ipc_pages_trace_after_share); reveal(ipc_pages_mapping_trace); }

/// The finish step pushed after the mapping trace that starts at `start` completes the pages rendezvous trace.
pub(super) proof fn ipc_pages_rendezvous_trace_finish_step(steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, finish_pre: KernelU, post: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, range: VaRange4K, result: RetValueType)
    requires
        0 <= start <= before.len(),
        ipc_pages_mapping_trace(before.subrange(start, before.len() as int), pre, cpu_id, endpoint_index, waiting_state, range, result),
        steps.view() == before.push(KernelStep { old_u: finish_pre, new_u: post }),
        ipc_pages_finish_step_pre(finish_pre, cpu_id, endpoint_index),
        ipc_pages_finish_step(finish_pre, post, cpu_id, endpoint_index),
        result is Success || result is ErrorIpcSourceUnmapped || result is ErrorIpcPageOwnerMismatch || result is ErrorNoQuota || result is ErrorVaInUse || result is Error,
    ensures
        ipc_pages_rendezvous_syscall_trace(steps.view().subrange(start, steps.view().len() as int), pre, post, cpu_id, endpoint_index, waiting_state, range, result),
{
    reveal(ipc_pages_rendezvous_syscall_trace); reveal(ipc_pages_mapping_trace);
    let trace = steps.view().subrange(start, steps.view().len() as int);
    vstd::assert_seqs_equal!(trace.subrange(0, trace.len() - 1) == before.subrange(start, before.len() as int));
}

/// A pages call rejected before any visible change records no step.
pub(super) proof fn ipc_pages_syscall_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, range: VaRange4K, regs: Registers, flushed_default_pcid: bool, ret: RetValueType)
    requires
        trace.len() == 0,
        ret is Error,
    ensures
        ipc_pages_syscall_trace(trace, pre, pre, cpu_id, endpoint_index, waiting_state, range, regs, flushed_default_pcid, ret),
{ reveal(ipc_pages_syscall_trace); reveal(ipc_pages_rendezvous_syscall_trace); }

/// The cpu, the running thread that starts sharing a pages rendezvous at its first page, its peer, the sender's page table read-held, and the
/// receiver's write-held on `krnl` give the downgrade pre and the receiver's process in the user view.
pub(super) proof fn ipc_pages_downgrade_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, peer_ptr: RwLockThreadPtr, source_thread: RwLockThreadPtr,
    target_thread: RwLockThreadPtr, source_process: RwLockProcessPtr, target_process: RwLockProcessPtr, source_pagetable: RwLockPageTableRoot,
    target_pagetable: RwLockPageTableRoot, source_range: VaRange4K, target_range: VaRange4K,
)
    requires
        typed_lock_maps_aligned(krnl, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), peer_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), source_pagetable, TypedLockMode::Read),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
        krnl.thr_mp.dom().contains(thread_ptr),
        krnl.thr_mp.dom().contains(peer_ptr),
        krnl.cpu_arr.spec_index(cpu_id).value.view().view().current_process is Some,
        krnl.cpu_arr.spec_index(cpu_id).value.view().view().current_thread == Some(thread_ptr),
        krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Share4k {
            source_range, target_range, shared: 0, directory: krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->Share4k_directory, origin: Share4kOrigin::IpcPages { peer: peer_ptr },
        }),
        source_thread == thread_ptr && target_thread == peer_ptr || source_thread == peer_ptr && target_thread == thread_ptr,
        krnl.thr_mp.spec_index(peer_ptr).view().state == (ThreadState::IPC_TRANSIT { partner: thread_ptr, wait: if source_thread == thread_ptr { IpcWait::Receive } else { IpcWait::Send } }),
        krnl.thr_mp.spec_index(source_thread).view().owning_proc == source_process,
        krnl.thr_mp.spec_index(target_thread).view().owning_proc == target_process,
        krnl.ctn_mp.dom().contains(krnl.thr_mp.spec_index(target_thread).view().owning_container),
        source_process != target_process,
        krnl.prc_mp.dom().contains(source_process),
        krnl.prc_mp.dom().contains(target_process),
        !krnl.prc_mp.spec_index(source_process).view().zombie,
        !krnl.prc_mp.spec_index(target_process).view().zombie,
        krnl.prc_mp.spec_index(source_process).view().pagetable == source_pagetable,
        krnl.prc_mp.spec_index(target_process).view().pagetable == target_pagetable,
    ensures
        ipc_pages_downgrade_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        share_4k_objects(kernel_k_to_kernel_u(*krnl), cpu_id).target == target_process,
        kernel_k_to_kernel_u(*krnl).process_map.dom().contains(source_process),
        kernel_k_to_kernel_u(*krnl).process_map.dom().contains(target_process),
        kernel_k_to_kernel_u(*krnl).process_map[source_process].pagetable is Some,
        kernel_k_to_kernel_u(*krnl).process_map[source_process].pagetable->Some_0.lock_state is ReadLocked,
        kernel_k_to_kernel_u(*krnl).thread_map.dom().contains(thread_ptr),
{
    reveal(share_4k_objects_k);
    krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), source_pagetable); krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), target_pagetable);
    kernel_write_held_context_projection(krnl, lctx, cpu_id, source_process, thread_ptr, None); kernel_write_held_context_projection(krnl, lctx, cpu_id, target_process, peer_ptr, None);
    kernel_cpu_thread_projection_at(krnl, cpu_id, source_process, peer_ptr, None); kernel_share_4k_objects_projection(krnl, lctx, cpu_id);
    kernel_pagetable_mappings_projection_at(krnl, source_process); kernel_pagetable_mappings_projection_at(krnl, target_process);
    ipc_pages_downgrade_step_pre_from_u(kernel_k_to_kernel_u(*krnl), cpu_id);
}

/// The pages context on `pre` that starts sharing at its first page with the sender's page table read-locked and the receiver's
/// write-locked is the downgrade pre.
pub(super) proof fn ipc_pages_downgrade_step_pre_from_u(pre: KernelU, cpu_id: CpuId)
    requires
        {
            let progress = pre.thread_map[pre.cpu_array[cpu_id as int].current_thread->Some_0].syscall_progress->Some_0;
            let objects = share_4k_objects(pre, cpu_id);
            let source = pre.thread_map[objects.source_thread].owning_proc;
            &&& share_4k_locked(pre, cpu_id)
            &&& progress->Share4k_origin is IpcPages
            &&& progress->Share4k_shared == 0
            &&& source != objects.target
            &&& pre.process_map.dom().contains(source)
            &&& pre.process_map.dom().contains(objects.target)
            &&& pre.process_map[source].pagetable is Some
            &&& pre.process_map[objects.target].pagetable is Some
            &&& pre.process_map[source].pagetable->Some_0.lock_state is ReadLocked
            &&& pre.process_map[objects.target].pagetable->Some_0.lock_state is WriteLocked
        },
    ensures ipc_pages_downgrade_step_pre(pre, cpu_id),
{ reveal(ipc_pages_downgrade_step_pre); }

/// Turning the write lock on the receiver's page table into a read lock while the sender's page table and the running thread keep their
/// state is the downgrade step on `pre`/`post`.
pub(super) proof fn ipc_pages_downgrade_step_from_u(
    pre: KernelU, post: KernelU, pre_k: &KernelK, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, source: RwLockProcessPtr, target: RwLockProcessPtr, source_table: RwLockPageTableRoot,
    target_table: RwLockPageTableRoot, source_state: LockStateU,
)
    requires
        pre == kernel_k_to_kernel_u(*pre_k),
        pre_k.prc_mp.dom().contains(source),
        pre_k.prc_mp.dom().contains(target),
        !pre_k.prc_mp.spec_index(source).view().zombie,
        !pre_k.prc_mp.spec_index(target).view().zombie,
        pre_k.prc_mp.spec_index(source).view().pagetable == source_table,
        pre_k.prc_mp.spec_index(target).view().pagetable == target_table,
        pre_k.pt_mp.dom().contains(source_table),
        pre_k.pt_mp.dom().contains(target_table),
        share_4k_objects(pre, cpu_id).target == target,
        source != target,
        pre.thread_map.dom().contains(thread_ptr),
        pre.process_map.dom().contains(source),
        pre.process_map[source].pagetable is Some,
        pre.process_map[source].pagetable->Some_0.lock_state == source_state,
        post == (KernelU {
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { syscall_progress: pre.thread_map[thread_ptr].syscall_progress, ..pre.thread_map[thread_ptr] }),
            process_map: pre.process_map.insert(source, ProcessU {
                pagetable: Some(PageTableU { lock_state: source_state, pagetable_window_locks: pagetable_c(pre_k.pt_mp, pre_k.pt_lower.view(), source_table).lower.pagetable_window_locks, ..pre.process_map[source].pagetable->Some_0 }), ..pre.process_map[source]
            }).insert(target, ProcessU {
                pagetable: Some(PageTableU { lock_state: LockStateU::ReadLocked, pagetable_window_locks: pagetable_c(pre_k.pt_mp, pre_k.pt_lower.view(), target_table).lower.pagetable_window_locks, ..pre.process_map[target].pagetable->Some_0 }), ..pre.process_map[target]
            }),
            ..pre
        }),
    ensures ipc_pages_downgrade_step(pre, post, cpu_id),
{
    reveal(ipc_pages_downgrade_step); kernel_process_projection_at(pre_k, source); kernel_process_projection_at(pre_k, target);
    assert_maps_equal!(post.thread_map, pre.thread_map);
    assert_maps_equal!(post.process_map, pre.process_map.insert(target, ProcessU {
        pagetable: Some(PageTableU { lock_state: LockStateU::ReadLocked, ..pre.process_map[target].pagetable->Some_0 }), ..pre.process_map[target]
    }));
}

/// The downgrade step recorded after the steps from `start` on, each a share or downgrade step, keeps every step from `start` on a share
/// or downgrade step.
pub(super) proof fn ipc_pages_trace_downgrade_step(steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, post: KernelU, cpu_id: CpuId)
    requires
        0 <= start <= before.len(),
        forall|j: int| #![trigger before[j]] start <= j < before.len()
            ==> share_4k_range_step(before[j], cpu_id) || ipc_pages_downgrade_step_pre(before[j].old_u, cpu_id) && ipc_pages_downgrade_step(before[j].old_u, before[j].new_u, cpu_id),
        steps.view() == record_user_view_change(before, pre, post),
        ipc_pages_downgrade_step_pre(pre, cpu_id),
        ipc_pages_downgrade_step(pre, post, cpu_id),
    ensures
        before.len() <= steps.view().len() <= before.len() + 1,
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len()
            ==> share_4k_range_step(steps.view()[j], cpu_id) || ipc_pages_downgrade_step_pre(steps.view()[j].old_u, cpu_id) && ipc_pages_downgrade_step(steps.view()[j].old_u, steps.view()[j].new_u, cpu_id),
{}
} // verus!
