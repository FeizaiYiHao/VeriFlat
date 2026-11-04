use vstd::prelude::*;
use vstd::assert_seqs_equal;
use crate::*;
use super::syscall_thread_exit_spec::*;
#[cfg(all(verus_keep_ghost, feature = "split-crates"))]
use veriflat_map_4k::map_4k::hide_user_l4_entries_eof::hide_user_l4_entry_eof_transition_framing;
#[cfg(all(verus_keep_ghost, not(feature = "split-crates")))]
use crate::kernel::implementation::map_4k::hide_user_l4_entries_eof::hide_user_l4_entry_eof_transition_framing;
#[cfg(all(verus_keep_ghost, feature = "split-crates"))]
use veriflat_map_4k::map_4k::hide_user_l4_entries_trace::hide_user_l4_entries_hide_step_from_k;
#[cfg(all(verus_keep_ghost, not(feature = "split-crates")))]
use crate::kernel::implementation::map_4k::hide_user_l4_entries_trace::hide_user_l4_entries_hide_step_from_k;
verus! {
/// Each return path's entry-state K facts give its value as the user-view result.
pub(super) proof fn thread_exit_syscall_result_from_k(krnl: &KernelK, cpu_id: CpuId, ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            let c = cpu.view().view();
            let container = krnl.ctn_mp.spec_index(c.owning_container);
            let process = krnl.prc_mp.spec_index(c.current_process->Some_0);
            let thread = krnl.thrd_mp.spec_index(c.current_thread->Some_0);
            let caller = thread.view().caller;
            let live = c.state is Running && !cpu.being_killed();
            let peer_killed = caller is Some && krnl.thrd_mp.spec_index(caller->Some_0).being_killed();
            let owner = container.lock_process_owner_u();
            let conflict = owner is Some && owner->Some_0 < LockOwnerId::Some(process.view_rodata().view().depth);
            &&& live ==> krnl.ctn_mp.dom().contains(c.owning_container) && krnl.prc_mp.dom().contains(c.current_process->Some_0) && krnl.thrd_mp.dom().contains(c.current_thread->Some_0)
            &&& live && caller is Some && (ret is CpuIdle || ret is ErrorIpcPeerKilled) ==> krnl.thrd_mp.dom().contains(caller->Some_0)
            &&& ret is CpuIdle ==> !live || (!container.being_killed() && !conflict && !process.being_killed() && !thread.being_killed() && !peer_killed)
            &&& ret is ErrorContainerKilled ==> live && container.being_killed()
            &&& ret is ErrorContainerLockOrderConflict ==> live && !container.being_killed() && conflict
            &&& ret is ErrorProcessKilled ==> live && !container.being_killed() && !conflict && process.being_killed()
            &&& ret is ErrorThreadKilled ==> live && !container.being_killed() && !conflict && !process.being_killed() && thread.being_killed()
            &&& ret is ErrorIpcPeerKilled ==> live && !container.being_killed() && !conflict && !process.being_killed() && !thread.being_killed() && peer_killed
            &&& ret is CpuIdle || ret is ErrorContainerKilled || ret is ErrorContainerLockOrderConflict || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorIpcPeerKilled
        },
    ensures
        thread_exit_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id) == ret,
{
    let c = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
    kernel_cpu_projection_at(krnl, cpu_id);
    if krnl.ctn_mp.dom().contains(c.owning_container) { kernel_container_projection_at(krnl, c.owning_container); }
    if krnl.prc_mp.dom().contains(c.current_process->Some_0) { kernel_process_projection_at(krnl, c.current_process->Some_0); }
    if krnl.thrd_mp.dom().contains(c.current_thread->Some_0) {
        let caller = krnl.thrd_mp.spec_index(c.current_thread->Some_0).view().caller;
        kernel_thread_projection_at(krnl, c.current_thread->Some_0);
        if caller is Some && krnl.thrd_mp.dom().contains(caller->Some_0) { kernel_thread_projection_at(krnl, caller->Some_0); }
    }
}

/// The entry state's K facts give the enter step precondition for the running `thrd_ptr` of `prc_ptr` in
/// `ctn_ptr`, whose caller `caller` is a dangling thread exactly when `dangling`.
pub(super) proof fn thread_exit_enter_step_pre_from_k(
    krnl: &KernelK, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, caller: Option<RwLockThreadPtr>, dangling: bool,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            let c = cpu.view().view();
            let thread = krnl.thrd_mp.spec_index(thrd_ptr);
            &&& cpu.locking_thread() is None
            &&& c.state is Running
            &&& !cpu.being_killed()
            &&& c.current_process == Some(prc_ptr)
            &&& c.current_thread == Some(thrd_ptr)
            &&& c.owning_container == ctn_ptr
            &&& krnl.ctn_mp.dom().contains(ctn_ptr)
            &&& krnl.ctn_mp.spec_index(ctn_ptr).locking_thread() is None
            &&& !krnl.ctn_mp.spec_index(ctn_ptr).being_killed()
            &&& krnl.prc_mp.dom().contains(prc_ptr)
            &&& krnl.prc_mp.spec_index(prc_ptr).locking_thread() is None
            &&& !krnl.prc_mp.spec_index(prc_ptr).being_killed()
            &&& krnl.thrd_mp.dom().contains(thrd_ptr)
            &&& thread.locking_thread() is None
            &&& thread.view().syscall_progress.view() is None
            &&& !thread.being_killed()
            &&& thread.view().state == (ThreadState::RUNNING { cpu_id })
            &&& thread.view().owning_proc == prc_ptr
            &&& thread.view().owning_container == ctn_ptr
            &&& thread.view().caller == caller
        },
        caller matches Some(caller_ptr) ==> {
            let caller_thread = krnl.thrd_mp.spec_index(caller_ptr);
            &&& krnl.thrd_mp.dom().contains(caller_ptr)
            &&& caller_thread.locking_thread() is None
            &&& !caller_thread.being_killed()
            &&& caller_thread.view().state.is_reply_waiting()
            &&& (caller_thread.view().state is DANGLING) == dangling
        },
    ensures
        thread_exit_enter_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_process == Some(prc_ptr),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].owning_container == ctn_ptr,
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].caller == caller,
        kernel_k_to_kernel_u(*krnl).process_map[prc_ptr].depth == krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().depth,
        caller matches Some(caller_ptr) ==> (kernel_k_to_kernel_u(*krnl).thread_map[caller_ptr].state is DANGLING) == dangling,
{
    kernel_cpu_thread_projection_at(krnl, cpu_id, prc_ptr, thrd_ptr, None); kernel_container_projection_at(krnl, ctn_ptr); kernel_process_projection_at(krnl, prc_ptr);
    if let Some(caller_ptr) = caller { kernel_thread_projection_at(krnl, caller_ptr); }
    reveal(thread_exit_enter_step_pre);
}

/// Acquiring the caller's context locks, waking the caller the thread serves or taking over its dangling thread, and
/// recording the progress is the enter step on `pre`/`post`.
pub(super) proof fn thread_exit_enter_step_from_u(
    pre: KernelU, locked: KernelU, woken: KernelU, post: KernelU, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, caller: Option<RwLockThreadPtr>, dangling: bool,
)
    requires
        thread_exit_enter_step_pre(pre, cpu_id),
        pre.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        pre.cpu_array[cpu_id as int].current_process == Some(prc_ptr),
        pre.cpu_array[cpu_id as int].owning_container == ctn_ptr,
        pre.thread_map[thrd_ptr].caller == caller,
        caller matches Some(caller_ptr) ==> (pre.thread_map[caller_ptr].state is DANGLING) == dangling,
        locked == (KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, op: CpuOpState::InStep, ..pre.cpu_array[cpu_id as int] }),
            container_map: pre.container_map.insert(ctn_ptr, ContainerU {
                lock_state: LockStateU::WriteLocked, lock_process_owner: Some(LockOwnerId::Some(pre.process_map[prc_ptr].depth)), ..pre.container_map[ctn_ptr]
            }),
            process_map: pre.process_map.insert(prc_ptr, ProcessU { lock_state: LockStateU::WriteLocked, ..pre.process_map[prc_ptr] }),
            thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { lock_state: LockStateU::WriteLocked, ..pre.thread_map.spec_index(thrd_ptr) }),
            ..pre
        }),
        woken == match caller {
            Some(caller_ptr) => if dangling {
                KernelU {
                    thread_map: locked.thread_map.insert(thrd_ptr, ThreadU { caller: None, ..locked.thread_map[thrd_ptr] }).insert(caller_ptr, ThreadU {
                        state: ThreadState::KILLED, callee: None, lock_state: LockStateU::WriteLocked, ..locked.thread_map[caller_ptr]
                    }),
                    ..locked
                }
            } else {
                let container = locked.thread_map[caller_ptr].owning_container;
                KernelU {
                    container_map: locked.container_map.insert(container, ContainerU {
                        scheduler: locked.container_map[container].scheduler.update(cpu_id as int, locked.container_map[container].scheduler[cpu_id as int].push(caller_ptr)),
                        ..locked.container_map[container]
                    }),
                    thread_map: locked.thread_map.insert(thrd_ptr, ThreadU { caller: None, ..locked.thread_map[thrd_ptr] }).insert(caller_ptr, ThreadU {
                        state: ThreadState::SCHEDULED { cpu_id }, callee: None, error_code: Some(RetValueType::ErrorIpcCalleeExited), ..locked.thread_map[caller_ptr]
                    }),
                    ..locked
                }
            },
            None => locked,
        },
        post == (KernelU { thread_map: woken.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: Some(SyscallProgress::ThreadExit { next: 0 }), ..woken.thread_map[thrd_ptr] }), ..woken }),
    ensures
        thread_exit_enter_step(pre, post, cpu_id),
{ reveal(thread_exit_enter_step_pre); reveal(thread_exit_enter_step); }

/// A state holding the cpu, `ctn_ptr`, `prc_ptr`, and the running `thrd_ptr` of `ctn_ptr` that records
/// exit position `next` gives the drop step precondition.
pub(super) proof fn thread_exit_drop_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, next: EndpointIdx,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), ctn_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), prc_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == ctn_ptr,
        krnl.prc_mp.dom().contains(prc_ptr),
        krnl.thrd_mp.dom().contains(thrd_ptr),
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExit { next }),
    ensures
        thread_exit_drop_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_process == Some(prc_ptr),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].owning_container == ctn_ptr,
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].owning_container == ctn_ptr,
{ kernel_write_held_context_projection(krnl, lctx, cpu_id, prc_ptr, thrd_ptr, None); kernel_cpu_thread_projection_at(krnl, cpu_id, prc_ptr, thrd_ptr, None); reveal(thread_exit_drop_step_pre); }

/// Releasing descriptor `index`, the first one at or after the recorded position `next`, is the drop step on
/// `pre`/`post`.
pub(super) proof fn thread_exit_drop_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, ep_ptr: RwLockEndpointPtr, next: EndpointIdx, index: EndpointIdx,
)
    requires
        thread_exit_drop_step_pre(pre, cpu_id),
        next <= index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        pre.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        {
            let thread = pre.thread_map.spec_index(thrd_ptr);
            &&& thread.syscall_progress == Some(SyscallProgress::ThreadExit { next })
            &&& forall|j: int| #![trigger thread.endpoint_descriptors[j]] next <= j < index ==> thread.endpoint_descriptors[j] is None
            &&& thread.endpoint_descriptors[index as int] == Some(ep_ptr)
            &&& pre.endpoint_map.dom().contains(ep_ptr)
            &&& pre.endpoint_map.spec_index(ep_ptr).lock_state is Unlocked
            &&& pre.endpoint_map.spec_index(ep_ptr).owning_threads.len() > 1
        },
        post == (KernelU {
            thread_map: pre.thread_map.insert(thrd_ptr, ThreadU {
                endpoint_descriptors: pre.thread_map[thrd_ptr].endpoint_descriptors.update(index as int, None),
                syscall_progress: Some(SyscallProgress::ThreadExit { next: (index + 1) as EndpointIdx }), ..pre.thread_map[thrd_ptr]
            }),
            endpoint_map: pre.endpoint_map.insert(ep_ptr, EndpointU {
                owning_threads: pre.endpoint_map[ep_ptr].owning_threads.remove((thrd_ptr, index)), ..pre.endpoint_map[ep_ptr]
            }),
            ..pre
        }),
    ensures
        thread_exit_drop_step(pre, post, cpu_id),
{ reveal(thread_exit_drop_step); }

/// Releasing the endpoint whose last reference is descriptor `index`, the first one at or after the recorded position
/// `next`, is the release step on `pre`/`post`.
pub(super) proof fn thread_exit_release_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, next: EndpointIdx, index: EndpointIdx)
    requires
        next <= index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        pre.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        {
            let thread = pre.thread_map.spec_index(thrd_ptr);
            &&& thread.syscall_progress == Some(SyscallProgress::ThreadExit { next })
            &&& forall|j: int| #![trigger thread.endpoint_descriptors[j]] next <= j < index ==> thread.endpoint_descriptors[j] is None
        },
        kernel_u_endpoint_released(pre, post, thrd_ptr, index as int),
        post.thread_map == pre.thread_map.insert(thrd_ptr, ThreadU {
            endpoint_descriptors: pre.thread_map[thrd_ptr].endpoint_descriptors.update(index as int, None),
            syscall_progress: Some(SyscallProgress::ThreadExit { next: (index + 1) as EndpointIdx }), ..pre.thread_map[thrd_ptr]
        }),
    ensures
        thread_exit_release_step(pre, post, cpu_id),
{ reveal(thread_exit_release_step); }

/// A state holding the cpu, `ctn_ptr`, `prc_ptr`, and the running `thrd_ptr` that has released every
/// descriptor and has no caller gives the finish step precondition.
pub(super) proof fn thread_exit_finish_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), ctn_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), prc_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == ctn_ptr,
        krnl.prc_mp.dom().contains(prc_ptr),
        krnl.thrd_mp.dom().contains(thrd_ptr),
        {
            let process = krnl.prc_mp.spec_index(prc_ptr).view();
            let thread = krnl.thrd_mp.spec_index(thrd_ptr).view();
            &&& thread.owning_container == ctn_ptr
            &&& thread.caller is None
            &&& thread.syscall_progress.view() is Some
            &&& forall|j: int| #![trigger thread.endpoint_descriptors.view()[j]] 0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==> thread.endpoint_descriptors.view()[j] is None
            &&& if process.owned_threads.view().len() == 1 {
                &&& thread.syscall_progress.view() == Some(SyscallProgress::ThreadExitZombie)
                &&& process.quota_4k == 0
                &&& process.quota_2m == 0
                &&& process.quota_1g == 0
                &&& thread.quota_4k == 0
                &&& thread.quota_2m == 0
                &&& thread.quota_1g == 0
            } else { thread.syscall_progress.view() matches Some(SyscallProgress::ThreadExit { .. }) }
        },
    ensures
        thread_exit_finish_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_process == Some(prc_ptr),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].owning_container == ctn_ptr,
{
    kernel_write_held_context_projection(krnl, lctx, cpu_id, prc_ptr, thrd_ptr, None);
    kernel_cpu_thread_projection_at(krnl, cpu_id, prc_ptr, thrd_ptr, None); kernel_process_projection_at(krnl, prc_ptr);
    reveal(thread_exit_finish_step_pre);
}

/// Removing the exiting thread while releasing its cpu, container, and process is the finish step on `pre`/`post`.
pub(super) proof fn thread_exit_finish_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    flushed_default_pcid: bool,
)
    requires
        thread_exit_finish_step_pre(pre, cpu_id),
        pre.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        pre.cpu_array[cpu_id as int].current_process == Some(prc_ptr),
        pre.cpu_array[cpu_id as int].owning_container == ctn_ptr,
        kernel_u_thread_exit_changed(KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: CpuOpState::Trap, ..pre.cpu_array[cpu_id as int] }),
            container_map: pre.container_map.insert(ctn_ptr, ContainerU { lock_state: LockStateU::Unlocked, lock_process_owner: None, ..pre.container_map[ctn_ptr] }),
            process_map: pre.process_map.insert(prc_ptr, ProcessU { lock_state: LockStateU::Unlocked, ..pre.process_map[prc_ptr] }),
            ..pre
        }, post, cpu_id, thrd_ptr, flushed_default_pcid),
    ensures
        thread_exit_finish_step(pre, post, cpu_id),
{ reveal(thread_exit_finish_step); }

/// A state holding the cpu, `ctn_ptr`, `prc_ptr`, and the running `thrd_ptr`, the process's last thread
/// that has released every descriptor and has no caller, with the process's page table and IOMMU table unlocked, gives
/// the lock-table step precondition and the projected DID of the IOMMU table.
pub(super) proof fn thread_exit_lock_table_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    pagetable: RwLockPageTableRoot,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), ctn_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), prc_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        krnl.prc_mp.dom().contains(prc_ptr),
        krnl.thrd_mp.dom().contains(thrd_ptr),
        {
            let process = krnl.prc_mp.spec_index(prc_ptr).view();
            let thread = krnl.thrd_mp.spec_index(thrd_ptr).view();
            &&& thread.owning_proc == prc_ptr
            &&& thread.owning_container == ctn_ptr
            &&& thread.syscall_progress.view() matches Some(SyscallProgress::ThreadExit { .. })
            &&& thread.caller is None
            &&& forall|j: int| #![trigger thread.endpoint_descriptors.view()[j]] 0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==> thread.endpoint_descriptors.view()[j] is None
            &&& process.owned_threads.view().len() == 1
            &&& !process.zombie
            &&& process.pagetable == pagetable
            &&& krnl.pt_mp.dom().contains(pagetable)
            &&& krnl.pt_mp.spec_index(pagetable).locking_thread() is None
            &&& process.iommu_table matches Some(t) ==> krnl.it_mp.dom().contains(t) && krnl.it_mp.spec_index(t).locking_thread() is None
        },
    ensures
        thread_exit_lock_table_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].owning_proc == prc_ptr,
        krnl.prc_mp.spec_index(prc_ptr).view().iommu_table matches Some(t) ==> kernel_k_to_kernel_u(*krnl).process_map[prc_ptr].iommu_table->Some_0.did == krnl.it_mp.spec_index(t).view().did,
{
    kernel_write_held_context_projection(krnl, lctx, cpu_id, prc_ptr, thrd_ptr, None);
    kernel_cpu_thread_projection_at(krnl, cpu_id, prc_ptr, thrd_ptr, None); kernel_process_projection_at(krnl, prc_ptr);
    kernel_pagetable_mappings_projection_at(krnl, prc_ptr);
    if krnl.prc_mp.spec_index(prc_ptr).view().iommu_table is Some { kernel_iommu_table_mappings_projection_at(krnl, prc_ptr); }
    reveal(thread_exit_lock_table_step_pre);
}

/// Write-locking the tables of the process of the running last thread while recording reclaim progress (`pre` to `mid`),
/// then, for a process with an IOMMU table of DID `did`, detaching that table (`mid` to `post`), is the lock-table step on
/// `pre`/`post`.
pub(super) proof fn thread_exit_lock_table_step_from_u(
    pre: KernelU, mid: KernelU, post: KernelU, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, did: Option<VtdDomainId>,
)
    requires
        thread_exit_lock_table_step_pre(pre, cpu_id),
        pre.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        pre.thread_map[thrd_ptr].owning_proc == prc_ptr,
        mid == (KernelU {
            thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: Some(SyscallProgress::ThreadExitReclaim { flushed: false }), ..pre.thread_map[thrd_ptr] }),
            process_map: pre.process_map.insert(prc_ptr, ProcessU {
                pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..pre.process_map[prc_ptr].pagetable->Some_0 }),
                iommu_table: match pre.process_map[prc_ptr].iommu_table { Some(t) => Some(PageTableU { lock_state: LockStateU::WriteLocked, ..t }), None => None },
                ..pre.process_map[prc_ptr]
            }),
            ..pre
        }),
        pre.process_map[prc_ptr].iommu_table is None ==> post == mid,
        pre.process_map[prc_ptr].iommu_table matches Some(t) ==> {
            let p = mid.process_map[prc_ptr];
            &&& t.did == did
            &&& post == (KernelU {
                process_map: mid.process_map.insert(prc_ptr, ProcessU { iommu_table: match p.iommu_table { Some(t) => Some(PageTableU { did: None, ..t }), None => None }, ..p }),
                iommu_root_table: IommuRootTableU {
                    attached: Seq::new(PCI_BUS_COUNT as nat, |bus: int| Seq::new(PCI_DEVICE_COUNT as nat, |device: int|
                        Seq::new(PCI_FUNCTION_COUNT as nat, |function: int| mid.iommu_root_table.attached[bus][device][function] && mid.iommu_root_table.owners[bus][device][function] != prc_ptr))),
                    ..mid.iommu_root_table
                },
                iommu_tlb: match did { Some(d) => mid.iommu_tlb.insert(d, SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }), None => mid.iommu_tlb },
                ..mid
            })
        },
    ensures
        thread_exit_lock_table_step(pre, post, cpu_id),
{
    reveal(thread_exit_lock_table_step);
    if pre.process_map[prc_ptr].iommu_table is Some {
        let attached = post.iommu_root_table.attached;
        let expected = thread_exit_detached_attached(pre.iommu_root_table, prc_ptr);
        assert_seqs_equal!(attached, expected, bus => {
            assert_seqs_equal!(attached[bus], expected[bus], device => { assert_seqs_equal!(attached[bus][device], expected[bus][device], function => {}); });
        });
        assert(post.process_map =~= pre.process_map.insert(prc_ptr, ProcessU {
            pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..pre.process_map[prc_ptr].pagetable->Some_0 }),
            iommu_table: Some(PageTableU { lock_state: LockStateU::WriteLocked, did: None, ..pre.process_map[prc_ptr].iommu_table->Some_0 }), ..pre.process_map[prc_ptr]
        }));
    }
}

/// A state holding the cpu, `ctn_ptr`, `prc_ptr` with its page table `pagetable`, and the running `thrd_ptr` that
/// records unflushed reclaim progress gives the reclaim precondition of a table-hidden step and shows the process's page table.
pub(super) proof fn thread_exit_table_hidden_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    pagetable: RwLockPageTableRoot,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), ctn_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), prc_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        krnl.prc_mp.dom().contains(prc_ptr),
        !krnl.prc_mp.spec_index(prc_ptr).view().zombie,
        krnl.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: false }),
    ensures
        thread_exit_reclaim_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, false),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].owning_proc == prc_ptr,
        kernel_k_to_kernel_u(*krnl).process_map[prc_ptr].pagetable is Some,
{
    kernel_write_held_context_projection(krnl, lctx, cpu_id, prc_ptr, thrd_ptr, None);
    reveal(thread_exit_reclaim_step_pre);
}

/// Dropping from the shown page table of the running thread's process `prc_ptr` every 4K, 2M and 1G mapping and every window
/// lock under root entry `l4i`, and nothing else, is a table-hidden step on `pre`/`post`.
pub(super) proof fn thread_exit_table_hidden_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, l4i: L4Index)
    requires
        pre.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        pre.thread_map[thrd_ptr].owning_proc == prc_ptr,
        pre.process_map[prc_ptr].pagetable is Some,
        ({
            let table = pre.process_map[prc_ptr].pagetable->Some_0;
            post == (KernelU {
                process_map: pre.process_map.insert(prc_ptr, ProcessU {
                    pagetable: if pre.process_map[prc_ptr].pagetable is Some {
                        Some(PageTableU {
                            mapping_4k: table.mapping_4k.remove_keys(table.mapping_4k.dom().filter(|va: VAddr| spec_v2l4index(va) == l4i)),
                            mapping_2m: table.mapping_2m.remove_keys(table.mapping_2m.dom().filter(|va: VAddr| spec_v2l4index(va) == l4i)),
                            mapping_1g: table.mapping_1g.remove_keys(table.mapping_1g.dom().filter(|va: VAddr| spec_v2l4index(va) == l4i)),
                            pagetable_window_locks: table.pagetable_window_locks.remove_keys(table.pagetable_window_locks.dom().filter(|w: WindowVa| spec_v2l4index(w.va) == l4i)),
                            ..table
                        })
                    } else {
                        None
                    },
                    ..pre.process_map[prc_ptr]
                }),
                ..pre
            })
        }),
    ensures thread_exit_table_hidden_step(pre, post, cpu_id),
{
    reveal(thread_exit_table_hidden_step);
    let o = pre.process_map[prc_ptr].pagetable->Some_0;
    let n = post.process_map[prc_ptr].pagetable->Some_0;
    assert(n.mapping_4k =~= o.mapping_4k.restrict(n.mapping_4k.dom()));
    assert(n.mapping_2m =~= o.mapping_2m.restrict(n.mapping_2m.dom()));
    assert(n.mapping_1g =~= o.mapping_1g.restrict(n.mapping_1g.dom()));
    assert(n.pagetable_window_locks =~= o.pagetable_window_locks.restrict(n.pagetable_window_locks.dom()));
}

/// The steps `steps[before_len + k]` for `k < count`, each recorded across hiding user root entry `hidden[k].0` of the page table
/// `pagetable` of the running last thread's process from `hidden[k].1` to `hidden[k].2`, where `hidden[k].1` keeps every cpu,
/// process and thread that `lctx` holds as in `entry`, extend the partial trace that starts at `start` and ends at `before_len`.
pub(super) proof fn thread_exit_table_hidden_steps_implies_partial_trace(
    steps: Seq<KernelStep>, start: int, before_len: int, pre: KernelU, hidden: Seq<(L4Index, KernelK, KernelK)>, entry: &KernelK, lctx: &LocalContext, cpu_id: CpuId,
    ctn_ptr: RwLockContainerPtr, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot, count: int,
)
    requires
        0 <= start <= before_len,
        0 <= count <= hidden.len(),
        before_len + hidden.len() <= steps.len(),
        thread_exit_partial_trace(steps.subrange(start, before_len), pre, cpu_id),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), ctn_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), prc_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        entry.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        entry.prc_mp.dom().contains(prc_ptr),
        !entry.prc_mp.spec_index(prc_ptr).view().zombie,
        entry.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        entry.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        entry.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        entry.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: false }),
        forall|k: int| #![trigger hidden[k]] 0 <= k < hidden.len() ==> {
            &&& steps[before_len + k] == (KernelStep { old_u: kernel_k_to_kernel_u(hidden[k].1), new_u: kernel_k_to_kernel_u(hidden[k].2) })
            &&& process_pagetable_wf(hidden[k].1.prc_mp, hidden[k].1.pt_mp)
            &&& hide_user_l4_entry_eof_transition_framing(hidden[k].1, hidden[k].2, pagetable, hidden[k].0)
            &&& typed_lock_maps_aligned(&hidden[k].1, lctx)
            &&& held_cpus_unchanged(entry.cpu_arr, hidden[k].1.cpu_arr, lctx) && held_processes_unchanged(entry.prc_mp, hidden[k].1.prc_mp, lctx)
            &&& held_threads_unchanged(entry.thrd_mp, hidden[k].1.thrd_mp, lctx)
        },
    ensures thread_exit_partial_trace(steps.subrange(start, before_len + count), pre, cpu_id),
    decreases count,
{
    if count > 0 {
        let h = hidden[count - 1];
        thread_exit_table_hidden_steps_implies_partial_trace(steps, start, before_len, pre, hidden, entry, lctx, cpu_id, ctn_ptr, prc_ptr, thrd_ptr, pagetable, count - 1);
        process_pagetable_wf_process_at(h.1.prc_mp, h.1.pt_mp, prc_ptr);
        hide_user_l4_entries_hide_step_from_k(&h.1, &h.2, pagetable, h.0);
        thread_exit_table_hidden_step_pre_from_k(&h.1, lctx, cpu_id, ctn_ptr, prc_ptr, thrd_ptr, pagetable);
        thread_exit_table_hidden_step_from_u(kernel_k_to_kernel_u(h.1), kernel_k_to_kernel_u(h.2), cpu_id, prc_ptr, thrd_ptr, h.0);
        reveal(thread_exit_partial_trace);
        assert(steps.subrange(start, before_len + count) =~= steps.subrange(start, before_len + count - 1).push(steps[before_len + count - 1]));
    }
}

/// A state holding the cpu, `ctn_ptr`, `prc_ptr` with its page table `pagetable` and IOMMU table
/// `iommu_table`, and the running `thrd_ptr` that records flushed reclaim progress gives the reclaim precondition of
/// an IOMMU leaf step.
pub(super) proof fn thread_exit_iommu_leaf_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    pagetable: RwLockPageTableRoot, iommu_table: RwLockPageTableRoot,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), ctn_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), prc_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), iommu_table, TypedLockMode::Write),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        krnl.prc_mp.dom().contains(prc_ptr),
        !krnl.prc_mp.spec_index(prc_ptr).view().zombie,
        krnl.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        krnl.prc_mp.spec_index(prc_ptr).view().iommu_table == Some(iommu_table),
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: true }),
    ensures
        thread_exit_reclaim_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, true),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].owning_proc == prc_ptr,
        kernel_k_to_kernel_u(*krnl).process_map[prc_ptr].iommu_table is Some,
        kernel_k_to_kernel_u(*krnl).process_map[prc_ptr].iommu_table->Some_0.lock_state is WriteLocked,
{
    kernel_write_held_context_projection(krnl, lctx, cpu_id, prc_ptr, thrd_ptr, None);
    reveal(thread_exit_reclaim_step_pre);
}

/// Removing the 4K leaf `iova` of the locked, detached IOMMU table after the flush is an IOMMU leaf step on `pre`/`post`.
pub(super) proof fn thread_exit_iommu_leaf_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, iova: VAddr)
    requires
        pre.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        pre.thread_map[thrd_ptr].owning_proc == prc_ptr,
        pre.process_map[prc_ptr].iommu_table is Some,
        pre.process_map[prc_ptr].iommu_table->Some_0.lock_state is WriteLocked,
        pre.process_map[prc_ptr].iommu_table->Some_0.mapping_4k.dom().contains(iova),
        post == (KernelU {
            process_map: pre.process_map.insert(prc_ptr, ProcessU {
                iommu_table: Some(PageTableU { mapping_4k: pre.process_map[prc_ptr].iommu_table->Some_0.mapping_4k.remove(iova), ..pre.process_map[prc_ptr].iommu_table->Some_0 }),
                ..pre.process_map[prc_ptr]
            }),
            ..pre
        }),
    ensures
        thread_exit_iommu_leaf_step(pre, post, cpu_id),
{
    reveal(thread_exit_iommu_leaf_step);
    let mapping = pre.process_map[prc_ptr].iommu_table->Some_0.mapping_4k;
    let kept = post.process_map[prc_ptr].iommu_table->Some_0.mapping_4k.dom();
    assert(kept =~= mapping.dom().remove(iova));
    assert(mapping.dom().difference(kept) =~= set![iova]);
    assert(mapping.remove(iova) =~= mapping.restrict(kept));
}

/// Removing the present 4K leaf `iova` of the write-held, detached IOMMU table `iommu_table` of `prc_ptr` from `pre` to
/// `post`, with page, 4K-allocator, and `thrd_ptr` bookkeeping, where `post` holds the cpu, `ctn_ptr`, `prc_ptr`
/// with its page table `pagetable`, and the running `thrd_ptr` that records flushed reclaim progress, is an IOMMU leaf step
/// after its reclaim precondition, and changes the projection.
pub(super) proof fn thread_exit_iommu_leaf_step_from_k(
    pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    pagetable: RwLockPageTableRoot, iommu_table: RwLockPageTableRoot, iova: VAddr,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(post, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), ctn_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), prc_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), iommu_table, TypedLockMode::Write),
        post.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        post.prc_mp.dom().contains(prc_ptr),
        !post.prc_mp.spec_index(prc_ptr).view().zombie,
        post.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        post.prc_mp.spec_index(prc_ptr).view().iommu_table == Some(iommu_table),
        post.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        post.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: true }),
        process_iommu_table_wf(pre.prc_mp, pre.it_mp),
        pre.it_mp.dom().contains(iommu_table),
        pre.it_mp.spec_index(iommu_table).view().proc_ptr == prc_ptr,
        *post == (KernelK { it_mp: post.it_mp, pg_arr: post.pg_arr, thrd_mp: post.thrd_mp, allc_4k_mp: post.allc_4k_mp, ..*pre }),
        post.it_mp.unchanged_except(&pre.it_mp, iommu_table),
        post.it_mp.spec_index(iommu_table).locking_thread() == pre.it_mp.spec_index(iommu_table).locking_thread(),
        post.it_mp.spec_index(iommu_table).view().proc_ptr == prc_ptr,
        post.it_mp.spec_index(iommu_table).view().did == pre.it_mp.spec_index(iommu_table).view().did,
        pre.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(iova),
        pre.it_mp.spec_index(iommu_table).view().mapping_4k()[iova].present,
        post.it_mp.spec_index(iommu_table).view().mapping_4k() == pre.it_mp.spec_index(iommu_table).view().mapping_4k().remove(iova),
        post.it_mp.spec_index(iommu_table).view().mapping_2m() == pre.it_mp.spec_index(iommu_table).view().mapping_2m(),
        post.it_mp.spec_index(iommu_table).view().mapping_1g() == pre.it_mp.spec_index(iommu_table).view().mapping_1g(),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() == pre.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, &KernelK { it_mp: pre.it_mp, ..*post }),
        kernel_container_nonlock_fields_and_quotas_unchanged(pre, post),
    ensures
        thread_exit_reclaim_step_pre(kernel_k_to_kernel_u(*pre), cpu_id, true),
        thread_exit_iommu_leaf_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id),
        kernel_k_to_kernel_u(*pre) != kernel_k_to_kernel_u(*post),
{
    thread_exit_iommu_leaf_step_pre_from_k(post, lctx, cpu_id, ctn_ptr, prc_ptr, thrd_ptr, pagetable, iommu_table);
    kernel_iommu_table_4k_mapping_removed_implies_u_step(pre, post, iommu_table, iova, thrd_ptr);
    reveal(thread_exit_reclaim_step_pre);
    thread_exit_iommu_leaf_step_from_u(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id, prc_ptr, thrd_ptr, iova);
}

/// A state holding the cpu, `ctn_ptr`, `prc_ptr` with its page table `pagetable` of PCID `pcid`, and the
/// running `thrd_ptr` that records unflushed reclaim progress, where no user 4K leaf of the page table is left, gives
/// the flush step precondition.
pub(super) proof fn thread_exit_flush_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    pagetable: RwLockPageTableRoot, pcid: Pcid,
)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), ctn_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), prc_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        krnl.prc_mp.dom().contains(prc_ptr),
        !krnl.prc_mp.spec_index(prc_ptr).view().zombie,
        krnl.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().pcid == pcid,
        krnl.pt_mp.dom().contains(pagetable),
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: false }),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && KERNEL_MEM_END_L4INDEX <= l4i && krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end <= l4i
                && whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))) ==> !whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present,
    ensures
        thread_exit_flush_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].owning_proc == prc_ptr,
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].owning_container == ctn_ptr,
        kernel_k_to_kernel_u(*krnl).process_map[prc_ptr].pcid == pcid,
{
    kernel_write_held_context_projection(krnl, lctx, cpu_id, prc_ptr, thrd_ptr, None); kernel_pagetable_user_4k_unmapped_projection_at(krnl, prc_ptr);
    reveal(thread_exit_flush_step_pre); reveal(thread_exit_reclaim_step_pre);
}

/// Recording the flush, with the cpu set of the thread's container left in a mode no writer holds, is the flushed step
/// on `pre`/`post`.
pub(super) proof fn thread_exit_flushed_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, cpu_set_lock: LockStateU)
    requires
        pre.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        pre.thread_map.dom().contains(thrd_ptr),
        pre.thread_map[thrd_ptr].owning_container == ctn_ptr,
        !(cpu_set_lock is WriteLocked),
        post == (KernelU {
            thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: Some(SyscallProgress::ThreadExitReclaim { flushed: true }), ..pre.thread_map[thrd_ptr] }),
            container_map: pre.container_map.insert(ctn_ptr, ContainerU { cpu_set_lock, ..pre.container_map[ctn_ptr] }),
            ..pre
        }),
    ensures
        thread_exit_flushed_step(pre, post, cpu_id),
{ reveal(thread_exit_flushed_step); }

/// Recording the flush (`pre` to `post`) by the running thread `thrd_ptr` of the process `prc_ptr` with PCID `pcid`,
/// once no user 4K leaf of its page table `pagetable` is left, where `pre` extends the step's start `snap` by page-table
/// ghost state and by this thread's released read hold on the cpu set of its container, is a middle step on `snap`/`post`.
pub(super) proof fn thread_exit_flush_recorded_implies_flushed_step(
    snap: &KernelK, pre: &KernelK, lctx: &LocalContext, post: &KernelK, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot, pcid: Pcid,
)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(pre, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), ctn_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), prc_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        pre.prc_mp.dom().contains(prc_ptr),
        !pre.prc_mp.spec_index(prc_ptr).view().zombie,
        pre.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        pre.prc_mp.spec_index(prc_ptr).view_rodata().view().pcid == pcid,
        pre.pt_mp.dom().contains(pagetable),
        pre.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: false }),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && KERNEL_MEM_END_L4INDEX <= l4i && pre.pt_mp.spec_index(pagetable).view().kernel_l4_end <= l4i
                && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))) ==> !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present,
        *pre == (KernelK { pt_mp: pre.pt_mp, pt_lower: pre.pt_lower, cpu_set_mp: pre.cpu_set_mp, ..*snap }),
        pre.pt_mp.dom() == snap.pt_mp.dom(),
        forall|pt: RwLockPageTableRoot| #![trigger pre.pt_mp.spec_index(pt)] snap.pt_mp.dom().contains(pt) ==> {
            &&& pre.pt_mp.spec_index(pt).locking_thread() == snap.pt_mp.spec_index(pt).locking_thread()
            &&& whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pt).mapping_4k() == whole_pagetable(snap.pt_mp, snap.pt_lower.view(), pt).mapping_4k()
            &&& whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pt).mapping_2m() == whole_pagetable(snap.pt_mp, snap.pt_lower.view(), pt).mapping_2m()
            &&& whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pt).mapping_1g() == whole_pagetable(snap.pt_mp, snap.pt_lower.view(), pt).mapping_1g()
            &&& whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pt).lower.pagetable_window_locks == whole_pagetable(snap.pt_mp, snap.pt_lower.view(), pt).lower.pagetable_window_locks
        },
        pre.ctn_mp.dom().contains(ctn_ptr),
        pre.cpu_set_mp.unchanged_except(&snap.cpu_set_mp, pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set),
        pre.cpu_set_mp.spec_index(pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).being_killed() == snap.cpu_set_mp.spec_index(pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).being_killed(),
        !(pre.cpu_set_mp.spec_index(pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).locking_thread() is Write),
        *post == (KernelK { thrd_mp: post.thrd_mp, ..*pre }),
        pre.thrd_mp.dom().contains(thrd_ptr),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..pre.thrd_mp.spec_index(thrd_ptr).view() }),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() == pre.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        post.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
        post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: true }),
    ensures thread_exit_middle_step(KernelStep { old_u: kernel_k_to_kernel_u(*snap), new_u: kernel_k_to_kernel_u(*post) }, cpu_id),
{
    let ghost_tables = KernelK { pt_mp: pre.pt_mp, pt_lower: pre.pt_lower, ..*snap };
    let cpu_set_lock = pre.cpu_set_mp.spec_index(pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).lock_state_u();
    reveal(kernel_cpu_nonlock_fields_unchanged); kernel_u_domains_projection(snap);
    kernel_cpu_tlb_updated_implies_u_step(snap, &ghost_tables);
    kernel_cpu_set_lock_mode_changed_implies_u_step(&ghost_tables, pre, ctn_ptr);
    kernel_thread_syscall_progress_changed_implies_u_step(pre, post, thrd_ptr);
    thread_exit_flush_step_pre_from_k(pre, lctx, cpu_id, ctn_ptr, prc_ptr, thrd_ptr, pagetable, pcid);
    assert(thread_exit_flush_step_pre(kernel_k_to_kernel_u(*snap), cpu_id)) by { reveal(thread_exit_flush_step_pre); reveal(thread_exit_reclaim_step_pre); };
    thread_exit_flushed_step_from_u(kernel_k_to_kernel_u(*snap), kernel_k_to_kernel_u(*post), cpu_id, thrd_ptr, ctn_ptr, cpu_set_lock);
}

/// A state holding the cpu, `ctn_ptr`, `prc_ptr` with its page table `pagetable`, and the running `thrd_ptr`
/// that records the progress before returning its `size` quota gives the quota step precondition.
pub(super) proof fn thread_exit_quota_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    pagetable: RwLockPageTableRoot, size: PageSize,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), ctn_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), prc_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        krnl.prc_mp.dom().contains(prc_ptr),
        !krnl.prc_mp.spec_index(prc_ptr).view().zombie,
        krnl.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(thread_exit_quota_progress_before(size)),
    ensures
        thread_exit_quota_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].syscall_progress == Some(thread_exit_quota_progress_before(size)),
{
    kernel_write_held_context_projection(krnl, lctx, cpu_id, prc_ptr, thrd_ptr, None);
    reveal(thread_exit_quota_step_pre);
}

/// Returning the `size` quota of the running last thread and of its process to their container is the quota step on
/// `pre`/`post`.
pub(super) proof fn thread_exit_quota_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, size: PageSize)
    requires
        pre.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        pre.thread_map[thrd_ptr].syscall_progress == Some(thread_exit_quota_progress_before(size)),
        ({
            let thread = pre.thread_map[thrd_ptr];
            let process = pre.process_map[thread.owning_proc];
            let container = pre.container_map[thread.owning_container];
            let progress = Some(SyscallProgress::ThreadExitQuota { returned: size });
            post == (KernelU {
                container_map: pre.container_map.insert(thread.owning_container, match size {
                    PageSize::SZ4k => ContainerU { quota_4k: (container.quota_4k + process.quota_4k + thread.quota_4k) as usize, ..container },
                    PageSize::SZ2m => ContainerU { quota_2m: (container.quota_2m + process.quota_2m + thread.quota_2m) as usize, ..container },
                    PageSize::SZ1g => ContainerU { quota_1g: (container.quota_1g + process.quota_1g + thread.quota_1g) as usize, ..container },
                }),
                process_map: pre.process_map.insert(thread.owning_proc, match size {
                    PageSize::SZ4k => ProcessU { quota_4k: 0, ..process },
                    PageSize::SZ2m => ProcessU { quota_2m: 0, ..process },
                    PageSize::SZ1g => ProcessU { quota_1g: 0, ..process },
                }),
                thread_map: pre.thread_map.insert(thrd_ptr, match size {
                    PageSize::SZ4k => ThreadU { quota_4k: 0, syscall_progress: progress, ..thread },
                    PageSize::SZ2m => ThreadU { quota_2m: 0, syscall_progress: progress, ..thread },
                    PageSize::SZ1g => ThreadU { quota_1g: 0, syscall_progress: progress, ..thread },
                }),
                ..pre
            })
        }),
    ensures
        thread_exit_quota_step(pre, post, cpu_id),
{ reveal(thread_exit_quota_step); }

/// A state holding the cpu, `ctn_ptr`, `prc_ptr` with its page table `pagetable` and IOMMU table
/// `iommu_table`, and the running `thrd_ptr` that has returned every quota size, where no user 4K leaf of the page
/// table and no 4K leaf of the IOMMU table is left, gives the unlock-table step precondition.
pub(super) proof fn thread_exit_unlock_table_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr,
    pagetable: RwLockPageTableRoot, iommu_table: Option<RwLockPageTableRoot>,
)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), ctn_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), prc_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        krnl.prc_mp.dom().contains(prc_ptr),
        !krnl.prc_mp.spec_index(prc_ptr).view().zombie,
        krnl.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        krnl.prc_mp.spec_index(prc_ptr).view().iommu_table == iommu_table,
        krnl.pt_mp.dom().contains(pagetable),
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitQuota { returned: PageSize::SZ1g }),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && KERNEL_MEM_END_L4INDEX <= l4i && krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end <= l4i
                && whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))) ==> !whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present,
        iommu_table matches Some(it) ==> forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
            #![trigger krnl.it_mp.spec_index(it).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> !krnl.it_mp.spec_index(it).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
    ensures
        thread_exit_unlock_table_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        kernel_k_to_kernel_u(*krnl).thread_map[thrd_ptr].owning_proc == prc_ptr,
{
    kernel_write_held_context_projection(krnl, lctx, cpu_id, prc_ptr, thrd_ptr, None); kernel_pagetable_user_4k_unmapped_projection_at(krnl, prc_ptr);
    if iommu_table is Some { kernel_iommu_table_4k_unmapped_projection_at(krnl, prc_ptr); }
    reveal(thread_exit_unlock_table_step_pre);
}

/// Unlocking the reclaimed page table and IOMMU table once every quota size is returned is the unlock-table step on
/// `pre`/`post`.
pub(super) proof fn thread_exit_unlock_table_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr)
    requires
        pre.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        post == (KernelU {
            thread_map: pre.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: Some(SyscallProgress::ThreadExitZombie), ..pre.thread_map[thrd_ptr] }),
            process_map: pre.process_map.insert(pre.thread_map[thrd_ptr].owning_proc, ProcessU {
                pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, ..pre.process_map[pre.thread_map[thrd_ptr].owning_proc].pagetable->Some_0 }),
                iommu_table: match pre.process_map[pre.thread_map[thrd_ptr].owning_proc].iommu_table {
                    Some(t) => Some(PageTableU { lock_state: LockStateU::Unlocked, ..t }),
                    None => None,
                },
                ..pre.process_map[pre.thread_map[thrd_ptr].owning_proc]
            }),
            ..pre
        }),
    ensures
        thread_exit_unlock_table_step(pre, post, cpu_id),
{ reveal(thread_exit_unlock_table_step); }

/// The one step pushed since `before` is the partial trace after entering.
pub(super) proof fn thread_exit_trace_enter_step(steps: &KernelSteps, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId)
    requires
        steps.view() == before.push(KernelStep { old_u: pre, new_u: post }),
        thread_exit_enter_step_pre(pre, cpu_id),
        thread_exit_enter_step(pre, post, cpu_id),
    ensures
        thread_exit_partial_trace(steps.view().subrange(before.len() as int, steps.view().len() as int), pre, cpu_id),
{ reveal(thread_exit_partial_trace); }

/// A middle step pushed after the partial trace that starts at `start` extends it.
pub(super) proof fn thread_exit_trace_push(steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, step_pre: KernelU, step_post: KernelU, cpu_id: CpuId)
    requires
        0 <= start <= before.len(),
        thread_exit_partial_trace(before.subrange(start, before.len() as int), pre, cpu_id),
        steps.view() == before.push(KernelStep { old_u: step_pre, new_u: step_post }),
        thread_exit_middle_step(KernelStep { old_u: step_pre, new_u: step_post }, cpu_id),
    ensures
        thread_exit_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id),
{
    reveal(thread_exit_partial_trace);
    assert(steps.view().subrange(start, steps.view().len() as int) =~= before.subrange(start, before.len() as int).push(KernelStep { old_u: step_pre, new_u: step_post }));
}

/// Steps reclaiming killed threads of the running thread's container `ctn_ptr`, recorded after the partial trace
/// that starts at `start` while the running thread's cpu, the thread, and the lock modes of its process and container keep
/// their projection at `entry`, extend it.
pub(super) proof fn thread_exit_trace_from_killed_thread_reclaim(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, entry: KernelU, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr,
    prc_ptr: RwLockProcessPtr,
)
    requires
        0 <= start <= before.len(),
        thread_exit_partial_trace(before.subrange(start, before.len() as int), pre, cpu_id),
        kernel_steps_prefix_unchanged(before, steps.view()),
        thread_exit_drop_step_pre(entry, cpu_id),
        entry.cpu_array[cpu_id as int].owning_container == ctn_ptr,
        entry.cpu_array[cpu_id as int].current_process == Some(prc_ptr),
        entry.thread_map[entry.cpu_array[cpu_id as int].current_thread->Some_0].owning_container == ctn_ptr,
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            let old_u = steps.view()[j].old_u;
            let new_u = steps.view()[j].new_u;
            let thrd_ptr = entry.cpu_array[cpu_id as int].current_thread->Some_0;
            &&& kernel_u_killed_thread_reclaim_step(old_u, new_u, cpu_id)
            &&& forall|t: RwLockThreadPtr| #![trigger old_u.thread_map[t]]
                old_u.thread_map.dom().contains(t) && (!new_u.thread_map.dom().contains(t) || new_u.thread_map[t] != old_u.thread_map[t]) ==> old_u.thread_map[t].owning_container == ctn_ptr
            &&& old_u.cpu_array[cpu_id as int] == entry.cpu_array[cpu_id as int]
            &&& old_u.thread_map.dom().contains(thrd_ptr)
            &&& old_u.thread_map[thrd_ptr] == entry.thread_map[thrd_ptr]
            &&& old_u.process_map.dom().contains(prc_ptr)
            &&& old_u.process_map[prc_ptr].lock_state == entry.process_map[prc_ptr].lock_state
            &&& old_u.container_map.dom().contains(ctn_ptr)
            &&& old_u.container_map[ctn_ptr].lock_state == entry.container_map[ctn_ptr].lock_state
        },
    ensures
        thread_exit_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id),
{
    reveal(thread_exit_partial_trace); reveal(thread_exit_drop_step_pre); reveal(kernel_steps_prefix_unchanged);
    assert(steps.view().subrange(start, steps.view().len() as int) =~= before.subrange(start, before.len() as int) + steps.view().subrange(before.len() as int, steps.view().len() as int));
}

/// TLB flushes of the PCID of the running last thread's process, recorded after the partial trace that starts at
/// `start` while the thread's held objects keep their projection at `entry`, extend it.
pub(super) proof fn thread_exit_trace_from_tlb_flush(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, entry: KernelU, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr,
    ctn_ptr: RwLockContainerPtr, pcid: Pcid,
)
    requires
        0 <= start <= before.len() <= steps.view().len(),
        thread_exit_partial_trace(before.subrange(start, before.len() as int), pre, cpu_id),
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        thread_exit_flush_step_pre(entry, cpu_id),
        entry.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr),
        entry.thread_map[thrd_ptr].owning_proc == prc_ptr,
        entry.thread_map[thrd_ptr].owning_container == ctn_ptr,
        entry.process_map[prc_ptr].pcid == pcid,
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            let old_u = steps.view()[j].old_u;
            let locked = KernelU { container_map: old_u.container_map.insert(ctn_ptr, ContainerU { cpu_set_lock: LockStateU::ReadLocked, ..old_u.container_map[ctn_ptr] }), ..old_u };
            &&& steps.view()[j].new_u == locked || kernel_u_cpu_tlb_cleared(locked, steps.view()[j].new_u, pcid)
            &&& old_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& old_u.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr)
            &&& old_u.thread_map.dom().contains(thrd_ptr)
            &&& old_u.thread_map[thrd_ptr] == entry.thread_map[thrd_ptr]
            &&& old_u.process_map.dom().contains(prc_ptr)
            &&& old_u.process_map[prc_ptr].lock_state == entry.process_map[prc_ptr].lock_state
            &&& old_u.process_map[prc_ptr].pagetable == entry.process_map[prc_ptr].pagetable
            &&& old_u.process_map[prc_ptr].pcid == entry.process_map[prc_ptr].pcid
            &&& old_u.container_map.dom().contains(ctn_ptr)
            &&& old_u.container_map[ctn_ptr].lock_state is WriteLocked
            &&& old_u.kernel_l4_end == entry.kernel_l4_end
        },
    ensures
        thread_exit_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id),
{
    reveal(thread_exit_partial_trace); reveal(thread_exit_flush_step_pre); reveal(thread_exit_reclaim_step_pre); reveal(thread_exit_tlb_flush_step);
    let trace = steps.view().subrange(start, steps.view().len() as int);
    let old_trace = before.subrange(start, before.len() as int);
    assert forall|j: int| #![trigger trace[j]] 0 < j < trace.len() implies thread_exit_middle_step(trace[j], cpu_id) by { if start + j < before.len() { assert(trace[j] == old_trace[j]); } else { assert(trace[j] == steps.view()[start + j]); } };
}

/// Quota refunds to the container chain of the running last thread after the flush is recorded, pushed after the
/// partial trace that starts at `start`, extend it.
pub(super) proof fn thread_exit_trace_from_refund(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr,
    ctn_ptr: RwLockContainerPtr,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        0 <= start <= before.len() <= steps.view().len(),
        thread_exit_partial_trace(before.subrange(start, before.len() as int), pre, cpu_id),
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            let old_u = steps.view()[j].old_u;
            &&& kernel_u_container_quota_4k_increased(old_u, steps.view()[j].new_u, ctn_ptr)
            &&& old_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& old_u.cpu_array[cpu_id as int].current_thread == Some(thrd_ptr)
            &&& old_u.thread_map.dom().contains(thrd_ptr)
            &&& old_u.thread_map[thrd_ptr].lock_state is WriteLocked
            &&& old_u.thread_map[thrd_ptr].owning_container == ctn_ptr
            &&& old_u.thread_map[thrd_ptr].owning_proc == prc_ptr
            &&& old_u.thread_map[thrd_ptr].syscall_progress == Some(SyscallProgress::ThreadExitReclaim { flushed: true })
            &&& old_u.process_map.dom().contains(prc_ptr)
            &&& old_u.process_map[prc_ptr].lock_state is WriteLocked
            &&& old_u.process_map[prc_ptr].pagetable is Some
            &&& old_u.process_map[prc_ptr].pagetable->Some_0.lock_state is WriteLocked
            &&& old_u.container_map.dom().contains(ctn_ptr)
            &&& old_u.container_map[ctn_ptr].lock_state is WriteLocked
        },
    ensures
        thread_exit_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id),
{
    reveal(thread_exit_partial_trace); reveal(thread_exit_reclaim_step_pre);
    assert forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() implies thread_exit_refund_step(steps.view()[j].old_u, steps.view()[j].new_u, cpu_id) by { thread_exit_refund_step_from_u(steps.view()[j].old_u, steps.view()[j].new_u, cpu_id); };
    let trace = steps.view().subrange(start, steps.view().len() as int);
    let old_trace = before.subrange(start, before.len() as int);
    assert forall|j: int| #![trigger trace[j]] 0 < j < trace.len() implies thread_exit_middle_step(trace[j], cpu_id) by { if start + j < before.len() { assert(trace[j] == old_trace[j]); } else { assert(trace[j] == steps.view()[start + j]); } };
}

/// Growing the 4K quota of the running thread's container or of one of its ancestors, and nothing else, is a refund step.
pub(super) proof fn thread_exit_refund_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId)
    requires kernel_u_container_quota_4k_increased(pre, post, pre.thread_map.spec_index(pre.cpu_array[cpu_id as int].current_thread->Some_0).owning_container),
    ensures thread_exit_refund_step(pre, post, cpu_id),
{
    reveal(thread_exit_refund_step);
    assert(post.process_map == pre.process_map) by { reveal(kernel_u_container_quota_4k_increased); };
    assert((KernelU { process_map: post.process_map, ..pre }) == pre);
}

/// The finish step pushed after the partial trace that starts at `start` completes the trace of an exit.
pub(super) proof fn thread_exit_trace_finish_step(steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, finish_pre: KernelU, post: KernelU, cpu_id: CpuId)
    requires
        0 <= start <= before.len(),
        thread_exit_partial_trace(before.subrange(start, before.len() as int), pre, cpu_id),
        steps.view() == before.push(KernelStep { old_u: finish_pre, new_u: post }),
        thread_exit_finish_step_pre(finish_pre, cpu_id),
        thread_exit_finish_step(finish_pre, post, cpu_id),
    ensures
        thread_exit_syscall_trace(steps.view().subrange(start, steps.view().len() as int), pre, post, cpu_id, true),
{
    reveal(thread_exit_partial_trace); reveal(thread_exit_syscall_trace);
    assert(steps.view().subrange(start, steps.view().len() as int) =~= before.subrange(start, before.len() as int).push(KernelStep { old_u: finish_pre, new_u: post }));
}

/// A rejected call records no step.
pub(super) proof fn thread_exit_trace_stutter(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId)
    requires
        trace.len() == 0,
    ensures
        thread_exit_syscall_trace(trace, pre, pre, cpu_id, false),
{ reveal(thread_exit_syscall_trace); }
} // verus!
