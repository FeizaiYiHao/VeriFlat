use vstd::prelude::*;
use vstd::assert_seqs_equal;
use crate::*;
use super::syscall_thread_exit_spec::*;
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
            let thread = krnl.thr_mp.spec_index(c.current_thread->Some_0);
            let caller = thread.view().caller;
            let live = c.state is Running && !cpu.being_killed();
            let peer_killed = caller is Some && krnl.thr_mp.spec_index(caller->Some_0).being_killed();
            let owner = container.lock_process_owner_u();
            let conflict = owner is Some && owner->Some_0 < LockOwnerId::Some(process.view_rodata().view().depth);
            &&& live ==> krnl.ctn_mp.dom().contains(c.owning_container) && krnl.prc_mp.dom().contains(c.current_process->Some_0) && krnl.thr_mp.dom().contains(c.current_thread->Some_0)
            &&& live && caller is Some && (ret is CpuIdle || ret is ErrorIpcPeerKilled) ==> krnl.thr_mp.dom().contains(caller->Some_0)
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
    if krnl.thr_mp.dom().contains(c.current_thread->Some_0) {
        let caller = krnl.thr_mp.spec_index(c.current_thread->Some_0).view().caller;
        kernel_thread_projection_at(krnl, c.current_thread->Some_0);
        if caller is Some && krnl.thr_mp.dom().contains(caller->Some_0) { kernel_thread_projection_at(krnl, caller->Some_0); }
    }
}

/// The entry state's K facts give the enter step precondition for the running `thread_ptr` of `process_ptr` in
/// `container_ptr`, whose caller `caller` is a dangling thread exactly when `dangling`.
pub(super) proof fn thread_exit_enter_step_pre_from_k(
    krnl: &KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, caller: Option<RwLockThreadPtr>, dangling: bool,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view();
            let c = cpu.view().view();
            let thread = krnl.thr_mp.spec_index(thread_ptr);
            &&& cpu.locking_thread() is None
            &&& c.state is Running
            &&& !cpu.being_killed()
            &&& c.current_process == Some(process_ptr)
            &&& c.current_thread == Some(thread_ptr)
            &&& c.owning_container == container_ptr
            &&& krnl.ctn_mp.dom().contains(container_ptr)
            &&& krnl.ctn_mp.spec_index(container_ptr).locking_thread() is None
            &&& !krnl.ctn_mp.spec_index(container_ptr).being_killed()
            &&& krnl.prc_mp.dom().contains(process_ptr)
            &&& krnl.prc_mp.spec_index(process_ptr).locking_thread() is None
            &&& !krnl.prc_mp.spec_index(process_ptr).being_killed()
            &&& krnl.thr_mp.dom().contains(thread_ptr)
            &&& thread.locking_thread() is None
            &&& thread.view().syscall_progress.view() is None
            &&& !thread.being_killed()
            &&& thread.view().state == (ThreadState::RUNNING { cpu_id })
            &&& thread.view().owning_proc == process_ptr
            &&& thread.view().owning_container == container_ptr
            &&& thread.view().caller == caller
        },
        caller matches Some(caller_ptr) ==> {
            let caller_thread = krnl.thr_mp.spec_index(caller_ptr);
            &&& krnl.thr_mp.dom().contains(caller_ptr)
            &&& caller_thread.locking_thread() is None
            &&& !caller_thread.being_killed()
            &&& caller_thread.view().state.is_reply_waiting()
            &&& (caller_thread.view().state is DANGLING) == dangling
        },
    ensures
        thread_exit_enter_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_process == Some(process_ptr),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].owning_container == container_ptr,
        kernel_k_to_kernel_u(*krnl).thread_map[thread_ptr].caller == caller,
        kernel_k_to_kernel_u(*krnl).process_map[process_ptr].depth == krnl.prc_mp.spec_index(process_ptr).view_rodata().view().depth,
        caller matches Some(caller_ptr) ==> (kernel_k_to_kernel_u(*krnl).thread_map[caller_ptr].state is DANGLING) == dangling,
{
    kernel_cpu_thread_projection_at(krnl, cpu_id, process_ptr, thread_ptr, None); kernel_container_projection_at(krnl, container_ptr); kernel_process_projection_at(krnl, process_ptr);
    if let Some(caller_ptr) = caller { kernel_thread_projection_at(krnl, caller_ptr); }
    reveal(thread_exit_enter_step_pre);
}

/// Acquiring the caller's context locks, waking the caller the thread serves or taking over its dangling thread, and
/// recording the progress is the enter step on `pre`/`post`.
pub(super) proof fn thread_exit_enter_step_from_u(
    pre: KernelU, locked: KernelU, woken: KernelU, post: KernelU, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, caller: Option<RwLockThreadPtr>, dangling: bool,
)
    requires
        thread_exit_enter_step_pre(pre, cpu_id),
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.cpu_array[cpu_id as int].current_process == Some(process_ptr),
        pre.cpu_array[cpu_id as int].owning_container == container_ptr,
        pre.thread_map[thread_ptr].caller == caller,
        caller matches Some(caller_ptr) ==> (pre.thread_map[caller_ptr].state is DANGLING) == dangling,
        locked == (KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, op: CpuOpState::InStep, ..pre.cpu_array[cpu_id as int] }),
            container_map: pre.container_map.insert(container_ptr, ContainerU {
                lock_state: LockStateU::WriteLocked, lock_process_owner: Some(LockOwnerId::Some(pre.process_map[process_ptr].depth)), ..pre.container_map[container_ptr]
            }),
            process_map: pre.process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::WriteLocked, ..pre.process_map[process_ptr] }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, ..pre.thread_map.spec_index(thread_ptr) }),
            ..pre
        }),
        woken == match caller {
            Some(caller_ptr) => if dangling {
                KernelU {
                    thread_map: locked.thread_map.insert(thread_ptr, ThreadU { caller: None, ..locked.thread_map[thread_ptr] }).insert(caller_ptr, ThreadU {
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
                    thread_map: locked.thread_map.insert(thread_ptr, ThreadU { caller: None, ..locked.thread_map[thread_ptr] }).insert(caller_ptr, ThreadU {
                        state: ThreadState::SCHEDULED { cpu_id }, callee: None, error_code: Some(RetValueType::ErrorIpcCalleeExited), ..locked.thread_map[caller_ptr]
                    }),
                    ..locked
                }
            },
            None => locked,
        },
        post == (KernelU { thread_map: woken.thread_map.insert(thread_ptr, ThreadU { syscall_progress: Some(SyscallProgress::ThreadExit { next: 0 }), ..woken.thread_map[thread_ptr] }), ..woken }),
    ensures
        thread_exit_enter_step(pre, post, cpu_id),
{ reveal(thread_exit_enter_step_pre); reveal(thread_exit_enter_step); }

/// A state holding the cpu, `container_ptr`, `process_ptr`, and the running `thread_ptr` of `container_ptr` that records
/// exit position `next` gives the drop step precondition.
pub(super) proof fn thread_exit_drop_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, next: EndpointIdx,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
        krnl.prc_mp.dom().contains(process_ptr),
        krnl.thr_mp.dom().contains(thread_ptr),
        krnl.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExit { next }),
    ensures
        thread_exit_drop_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_process == Some(process_ptr),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].owning_container == container_ptr,
        kernel_k_to_kernel_u(*krnl).thread_map[thread_ptr].owning_container == container_ptr,
{ kernel_write_held_context_projection(krnl, lctx, cpu_id, process_ptr, thread_ptr, None); kernel_cpu_thread_projection_at(krnl, cpu_id, process_ptr, thread_ptr, None); reveal(thread_exit_drop_step_pre); }

/// Releasing descriptor `index`, the first one at or after the recorded position `next`, is the drop step on
/// `pre`/`post`.
pub(super) proof fn thread_exit_drop_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, next: EndpointIdx, index: EndpointIdx,
)
    requires
        thread_exit_drop_step_pre(pre, cpu_id),
        next <= index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        {
            let thread = pre.thread_map.spec_index(thread_ptr);
            &&& thread.syscall_progress == Some(SyscallProgress::ThreadExit { next })
            &&& forall|j: int| #![trigger thread.endpoint_descriptors[j]] next <= j < index ==> thread.endpoint_descriptors[j] is None
            &&& thread.endpoint_descriptors[index as int] == Some(endpoint_ptr)
            &&& pre.endpoint_map.dom().contains(endpoint_ptr)
            &&& pre.endpoint_map.spec_index(endpoint_ptr).lock_state is Unlocked
            &&& pre.endpoint_map.spec_index(endpoint_ptr).owning_threads.len() > 1
        },
        post == (KernelU {
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU {
                endpoint_descriptors: pre.thread_map[thread_ptr].endpoint_descriptors.update(index as int, None),
                syscall_progress: Some(SyscallProgress::ThreadExit { next: (index + 1) as EndpointIdx }), ..pre.thread_map[thread_ptr]
            }),
            endpoint_map: pre.endpoint_map.insert(endpoint_ptr, EndpointU {
                owning_threads: pre.endpoint_map[endpoint_ptr].owning_threads.remove((thread_ptr, index)), ..pre.endpoint_map[endpoint_ptr]
            }),
            ..pre
        }),
    ensures
        thread_exit_drop_step(pre, post, cpu_id),
{ reveal(thread_exit_drop_step); }

/// Releasing the endpoint whose last reference is descriptor `index`, the first one at or after the recorded position
/// `next`, is the release step on `pre`/`post`.
pub(super) proof fn thread_exit_release_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, next: EndpointIdx, index: EndpointIdx)
    requires
        next <= index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        {
            let thread = pre.thread_map.spec_index(thread_ptr);
            &&& thread.syscall_progress == Some(SyscallProgress::ThreadExit { next })
            &&& forall|j: int| #![trigger thread.endpoint_descriptors[j]] next <= j < index ==> thread.endpoint_descriptors[j] is None
        },
        kernel_u_endpoint_released(pre, post, thread_ptr, index as int),
        post.thread_map == pre.thread_map.insert(thread_ptr, ThreadU {
            endpoint_descriptors: pre.thread_map[thread_ptr].endpoint_descriptors.update(index as int, None),
            syscall_progress: Some(SyscallProgress::ThreadExit { next: (index + 1) as EndpointIdx }), ..pre.thread_map[thread_ptr]
        }),
    ensures
        thread_exit_release_step(pre, post, cpu_id),
{ reveal(thread_exit_release_step); }

/// A state holding the cpu, `container_ptr`, `process_ptr`, and the running `thread_ptr` that has released every
/// descriptor and has no caller gives the finish step precondition.
pub(super) proof fn thread_exit_finish_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
        krnl.prc_mp.dom().contains(process_ptr),
        krnl.thr_mp.dom().contains(thread_ptr),
        {
            let process = krnl.prc_mp.spec_index(process_ptr).view();
            let thread = krnl.thr_mp.spec_index(thread_ptr).view();
            &&& thread.owning_container == container_ptr
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
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_process == Some(process_ptr),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].owning_container == container_ptr,
{
    kernel_write_held_context_projection(krnl, lctx, cpu_id, process_ptr, thread_ptr, None);
    kernel_cpu_thread_projection_at(krnl, cpu_id, process_ptr, thread_ptr, None); kernel_process_projection_at(krnl, process_ptr);
    reveal(thread_exit_finish_step_pre);
}

/// Removing the exiting thread while releasing its cpu, container, and process is the finish step on `pre`/`post`.
pub(super) proof fn thread_exit_finish_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    flushed_default_pcid: bool,
)
    requires
        thread_exit_finish_step_pre(pre, cpu_id),
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.cpu_array[cpu_id as int].current_process == Some(process_ptr),
        pre.cpu_array[cpu_id as int].owning_container == container_ptr,
        kernel_u_thread_exit_changed(KernelU {
            cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: CpuOpState::Trap, ..pre.cpu_array[cpu_id as int] }),
            container_map: pre.container_map.insert(container_ptr, ContainerU { lock_state: LockStateU::Unlocked, lock_process_owner: None, ..pre.container_map[container_ptr] }),
            process_map: pre.process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::Unlocked, ..pre.process_map[process_ptr] }),
            ..pre
        }, post, cpu_id, thread_ptr, flushed_default_pcid),
    ensures
        thread_exit_finish_step(pre, post, cpu_id),
{ reveal(thread_exit_finish_step); }

/// A state holding the cpu, `container_ptr`, `process_ptr`, and the running `thread_ptr`, the process's last thread
/// that has released every descriptor and has no caller, with the process's page table and IOMMU table unlocked, gives
/// the lock-table step precondition and the projected DID of the IOMMU table.
pub(super) proof fn thread_exit_lock_table_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    pagetable: RwLockPageTableRoot,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        krnl.prc_mp.dom().contains(process_ptr),
        krnl.thr_mp.dom().contains(thread_ptr),
        {
            let process = krnl.prc_mp.spec_index(process_ptr).view();
            let thread = krnl.thr_mp.spec_index(thread_ptr).view();
            &&& thread.owning_proc == process_ptr
            &&& thread.owning_container == container_ptr
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
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        kernel_k_to_kernel_u(*krnl).thread_map[thread_ptr].owning_proc == process_ptr,
        krnl.prc_mp.spec_index(process_ptr).view().iommu_table matches Some(t)
            ==> kernel_k_to_kernel_u(*krnl).process_map[process_ptr].iommu_table->Some_0.did == krnl.it_mp.spec_index(t).view().did,
{
    kernel_write_held_context_projection(krnl, lctx, cpu_id, process_ptr, thread_ptr, None);
    kernel_cpu_thread_projection_at(krnl, cpu_id, process_ptr, thread_ptr, None); kernel_process_projection_at(krnl, process_ptr);
    kernel_pagetable_mappings_projection_at(krnl, process_ptr);
    if krnl.prc_mp.spec_index(process_ptr).view().iommu_table is Some { kernel_iommu_table_mappings_projection_at(krnl, process_ptr); }
    reveal(thread_exit_lock_table_step_pre);
}

/// Write-locking the tables of the process of the running last thread while recording reclaim progress (`pre` to `mid`),
/// then, for a process with an IOMMU table of DID `did`, detaching that table (`mid` to `post`), is the lock-table step on
/// `pre`/`post`.
pub(super) proof fn thread_exit_lock_table_step_from_u(
    pre: KernelU, mid: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, did: Option<VtdDomainId>,
)
    requires
        thread_exit_lock_table_step_pre(pre, cpu_id),
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.thread_map[thread_ptr].owning_proc == process_ptr,
        mid == (KernelU {
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { syscall_progress: Some(SyscallProgress::ThreadExitReclaim { flushed: false }), ..pre.thread_map[thread_ptr] }),
            process_map: pre.process_map.insert(process_ptr, ProcessU {
                pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..pre.process_map[process_ptr].pagetable->Some_0 }),
                iommu_table: match pre.process_map[process_ptr].iommu_table { Some(t) => Some(PageTableU { lock_state: LockStateU::WriteLocked, ..t }), None => None },
                ..pre.process_map[process_ptr]
            }),
            ..pre
        }),
        pre.process_map[process_ptr].iommu_table is None ==> post == mid,
        pre.process_map[process_ptr].iommu_table matches Some(t) ==> {
            let p = mid.process_map[process_ptr];
            &&& t.did == did
            &&& post == (KernelU {
                process_map: mid.process_map.insert(process_ptr, ProcessU { iommu_table: match p.iommu_table { Some(t) => Some(PageTableU { did: None, ..t }), None => None }, ..p }),
                iommu_root_table: IommuRootTableU {
                    attached: Seq::new(PCI_BUS_COUNT as nat, |bus: int| Seq::new(PCI_DEVICE_COUNT as nat, |device: int|
                        Seq::new(PCI_FUNCTION_COUNT as nat, |function: int| mid.iommu_root_table.attached[bus][device][function] && mid.iommu_root_table.owners[bus][device][function] != process_ptr))),
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
    if pre.process_map[process_ptr].iommu_table is Some {
        let attached = post.iommu_root_table.attached;
        let expected = thread_exit_detached_attached(pre.iommu_root_table, process_ptr);
        assert_seqs_equal!(attached, expected, bus => {
            assert_seqs_equal!(attached[bus], expected[bus], device => { assert_seqs_equal!(attached[bus][device], expected[bus][device], function => {}); });
        });
        assert(post.process_map =~= pre.process_map.insert(process_ptr, ProcessU {
            pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..pre.process_map[process_ptr].pagetable->Some_0 }),
            iommu_table: Some(PageTableU { lock_state: LockStateU::WriteLocked, did: None, ..pre.process_map[process_ptr].iommu_table->Some_0 }), ..pre.process_map[process_ptr]
        }));
    }
}

/// A state holding the cpu, `container_ptr`, `process_ptr` with its page table `pagetable`, and the running `thread_ptr`
/// that records unflushed reclaim progress, where the page table's kernel L4 end is at most the L4 index of `va`, gives
/// the reclaim precondition of a leaf step.
pub(super) proof fn thread_exit_leaf_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    pagetable: RwLockPageTableRoot, va: VAddr,
)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        krnl.prc_mp.dom().contains(process_ptr),
        !krnl.prc_mp.spec_index(process_ptr).view().zombie,
        krnl.prc_mp.spec_index(process_ptr).view().pagetable == pagetable,
        krnl.pt_mp.dom().contains(pagetable),
        krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_v2l4index(va),
        krnl.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        krnl.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: false }),
    ensures
        thread_exit_reclaim_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, false),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        kernel_k_to_kernel_u(*krnl).thread_map[thread_ptr].owning_proc == process_ptr,
        kernel_k_to_kernel_u(*krnl).kernel_l4_end <= spec_v2l4index(va),
{
    kernel_write_held_context_projection(krnl, lctx, cpu_id, process_ptr, thread_ptr, None); kernel_l4_end_projection_at(krnl, pagetable);
    reveal(thread_exit_reclaim_step_pre);
}

/// Clearing the user 4K leaf `va` of the locked page table before the flush is a leaf step on `pre`/`post`.
pub(super) proof fn thread_exit_leaf_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, va: VAddr)
    requires
        thread_exit_reclaim_step_pre(pre, cpu_id, false),
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.thread_map[thread_ptr].owning_proc == process_ptr,
        pre.process_map[process_ptr].pagetable->Some_0.mapping_4k.dom().contains(va),
        spec_va_4k_valid(va),
        pre.kernel_l4_end <= spec_v2l4index(va),
        post == (KernelU {
            process_map: pre.process_map.insert(process_ptr, ProcessU {
                pagetable: Some(PageTableU { mapping_4k: pre.process_map[process_ptr].pagetable->Some_0.mapping_4k.remove(va), ..pre.process_map[process_ptr].pagetable->Some_0 }),
                ..pre.process_map[process_ptr]
            }),
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { syscall_progress: Some(SyscallProgress::ThreadExitReclaim { flushed: false }), ..pre.thread_map[thread_ptr] }),
            ..pre
        }),
    ensures
        thread_exit_leaf_step(pre, post, cpu_id),
{
    reveal(thread_exit_reclaim_step_pre); reveal(thread_exit_leaf_step);
    let mapping = pre.process_map[process_ptr].pagetable->Some_0.mapping_4k;
    let kept = post.process_map[process_ptr].pagetable->Some_0.mapping_4k.dom();
    assert(pre.thread_map.insert(thread_ptr, ThreadU { syscall_progress: Some(SyscallProgress::ThreadExitReclaim { flushed: false }), ..pre.thread_map[thread_ptr] }) =~= pre.thread_map);
    assert(kept =~= mapping.dom().remove(va));
    assert(mapping.dom().difference(kept) =~= set![va]);
    assert(mapping.remove(va) =~= mapping.restrict(kept));
}

/// A state holding the cpu, `container_ptr`, `process_ptr` with its page table `pagetable` and IOMMU table
/// `iommu_table`, and the running `thread_ptr` that records flushed reclaim progress gives the reclaim precondition of
/// an IOMMU leaf step.
pub(super) proof fn thread_exit_iommu_leaf_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    pagetable: RwLockPageTableRoot, iommu_table: RwLockPageTableRoot,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), iommu_table, TypedLockMode::Write),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        krnl.prc_mp.dom().contains(process_ptr),
        !krnl.prc_mp.spec_index(process_ptr).view().zombie,
        krnl.prc_mp.spec_index(process_ptr).view().pagetable == pagetable,
        krnl.prc_mp.spec_index(process_ptr).view().iommu_table == Some(iommu_table),
        krnl.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        krnl.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: true }),
    ensures
        thread_exit_reclaim_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, true),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        kernel_k_to_kernel_u(*krnl).thread_map[thread_ptr].owning_proc == process_ptr,
        kernel_k_to_kernel_u(*krnl).process_map[process_ptr].iommu_table is Some,
        kernel_k_to_kernel_u(*krnl).process_map[process_ptr].iommu_table->Some_0.lock_state is WriteLocked,
{
    kernel_write_held_context_projection(krnl, lctx, cpu_id, process_ptr, thread_ptr, None);
    reveal(thread_exit_reclaim_step_pre);
}

/// Removing the 4K leaf `iova` of the locked, detached IOMMU table after the flush is an IOMMU leaf step on `pre`/`post`.
pub(super) proof fn thread_exit_iommu_leaf_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, iova: VAddr)
    requires
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.thread_map[thread_ptr].owning_proc == process_ptr,
        pre.process_map[process_ptr].iommu_table is Some,
        pre.process_map[process_ptr].iommu_table->Some_0.lock_state is WriteLocked,
        pre.process_map[process_ptr].iommu_table->Some_0.mapping_4k.dom().contains(iova),
        post == (KernelU {
            process_map: pre.process_map.insert(process_ptr, ProcessU {
                iommu_table: Some(PageTableU { mapping_4k: pre.process_map[process_ptr].iommu_table->Some_0.mapping_4k.remove(iova), ..pre.process_map[process_ptr].iommu_table->Some_0 }),
                ..pre.process_map[process_ptr]
            }),
            ..pre
        }),
    ensures
        thread_exit_iommu_leaf_step(pre, post, cpu_id),
{
    reveal(thread_exit_iommu_leaf_step);
    let mapping = pre.process_map[process_ptr].iommu_table->Some_0.mapping_4k;
    let kept = post.process_map[process_ptr].iommu_table->Some_0.mapping_4k.dom();
    assert(kept =~= mapping.dom().remove(iova));
    assert(mapping.dom().difference(kept) =~= set![iova]);
    assert(mapping.remove(iova) =~= mapping.restrict(kept));
}

/// Removing the present 4K leaf `iova` of the write-held, detached IOMMU table `iommu_table` of `process_ptr` from `pre` to
/// `post`, with page, 4K-allocator, and `thread_ptr` bookkeeping, where `post` holds the cpu, `container_ptr`, `process_ptr`
/// with its page table `pagetable`, and the running `thread_ptr` that records flushed reclaim progress, is an IOMMU leaf step
/// after its reclaim precondition, and changes the projection.
pub(super) proof fn thread_exit_iommu_leaf_step_from_k(
    pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    pagetable: RwLockPageTableRoot, iommu_table: RwLockPageTableRoot, iova: VAddr,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(post, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), iommu_table, TypedLockMode::Write),
        post.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        post.prc_mp.dom().contains(process_ptr),
        !post.prc_mp.spec_index(process_ptr).view().zombie,
        post.prc_mp.spec_index(process_ptr).view().pagetable == pagetable,
        post.prc_mp.spec_index(process_ptr).view().iommu_table == Some(iommu_table),
        post.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        post.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: true }),
        process_iommu_table_match(pre.prc_mp, pre.it_mp),
        pre.it_mp.dom().contains(iommu_table),
        pre.it_mp.spec_index(iommu_table).view().proc_ptr == process_ptr,
        *post == (KernelK { it_mp: post.it_mp, pg_arr: post.pg_arr, thr_mp: post.thr_mp, allc_4k_mp: post.allc_4k_mp, ..*pre }),
        post.it_mp.unchanged_except(&pre.it_mp, iommu_table),
        post.it_mp.spec_index(iommu_table).locking_thread() == pre.it_mp.spec_index(iommu_table).locking_thread(),
        post.it_mp.spec_index(iommu_table).view().proc_ptr == process_ptr,
        post.it_mp.spec_index(iommu_table).view().did == pre.it_mp.spec_index(iommu_table).view().did,
        pre.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(iova),
        pre.it_mp.spec_index(iommu_table).view().mapping_4k()[iova].present,
        post.it_mp.spec_index(iommu_table).view().mapping_4k() == pre.it_mp.spec_index(iommu_table).view().mapping_4k().remove(iova),
        post.it_mp.spec_index(iommu_table).view().mapping_2m() == pre.it_mp.spec_index(iommu_table).view().mapping_2m(),
        post.it_mp.spec_index(iommu_table).view().mapping_1g() == pre.it_mp.spec_index(iommu_table).view().mapping_1g(),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).locking_thread() == pre.thr_mp.spec_index(thread_ptr).locking_thread(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, &KernelK { it_mp: pre.it_mp, ..*post }),
        kernel_container_nonlock_fields_and_quotas_unchanged(pre, post),
    ensures
        thread_exit_reclaim_step_pre(kernel_k_to_kernel_u(*pre), cpu_id, true),
        thread_exit_iommu_leaf_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id),
        kernel_k_to_kernel_u(*pre) != kernel_k_to_kernel_u(*post),
{
    thread_exit_iommu_leaf_step_pre_from_k(post, lctx, cpu_id, container_ptr, process_ptr, thread_ptr, pagetable, iommu_table);
    kernel_iommu_table_4k_mapping_removed_implies_u_step(pre, post, iommu_table, iova, thread_ptr);
    reveal(thread_exit_reclaim_step_pre);
    thread_exit_iommu_leaf_step_from_u(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id, process_ptr, thread_ptr, iova);
}

/// A state holding the cpu, `container_ptr`, `process_ptr` with its page table `pagetable` of PCID `pcid`, and the
/// running `thread_ptr` that records unflushed reclaim progress, where no user 4K leaf of the page table is left, gives
/// the flush step precondition.
pub(super) proof fn thread_exit_flush_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    pagetable: RwLockPageTableRoot, pcid: Pcid,
)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        krnl.prc_mp.dom().contains(process_ptr),
        !krnl.prc_mp.spec_index(process_ptr).view().zombie,
        krnl.prc_mp.spec_index(process_ptr).view().pagetable == pagetable,
        krnl.prc_mp.spec_index(process_ptr).view_rodata().view().pcid == pcid,
        krnl.pt_mp.dom().contains(pagetable),
        krnl.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        krnl.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: false }),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && KERNEL_MEM_END_L4INDEX <= l4i && krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end <= l4i
                && pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                ==> !pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present,
    ensures
        thread_exit_flush_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        kernel_k_to_kernel_u(*krnl).thread_map[thread_ptr].owning_proc == process_ptr,
        kernel_k_to_kernel_u(*krnl).thread_map[thread_ptr].owning_container == container_ptr,
        kernel_k_to_kernel_u(*krnl).process_map[process_ptr].pcid == pcid,
{
    kernel_write_held_context_projection(krnl, lctx, cpu_id, process_ptr, thread_ptr, None); kernel_pagetable_user_4k_unmapped_projection_at(krnl, process_ptr);
    reveal(thread_exit_flush_step_pre); reveal(thread_exit_reclaim_step_pre);
}

/// Recording the flush is the flushed step on `pre`/`post`.
pub(super) proof fn thread_exit_flushed_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr)
    requires
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.thread_map.dom().contains(thread_ptr),
        post == (KernelU {
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { syscall_progress: Some(SyscallProgress::ThreadExitReclaim { flushed: true }), ..pre.thread_map[thread_ptr] }),
            ..pre
        }),
    ensures
        thread_exit_flushed_step(pre, post, cpu_id),
{ reveal(thread_exit_flushed_step); }

/// A state holding the cpu, `container_ptr`, `process_ptr` with its page table `pagetable`, and the running `thread_ptr`
/// that records the progress before returning its `size` quota gives the quota step precondition.
pub(super) proof fn thread_exit_quota_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    pagetable: RwLockPageTableRoot, size: PageSize,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        krnl.prc_mp.dom().contains(process_ptr),
        !krnl.prc_mp.spec_index(process_ptr).view().zombie,
        krnl.prc_mp.spec_index(process_ptr).view().pagetable == pagetable,
        krnl.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        krnl.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(thread_exit_quota_progress_before(size)),
    ensures
        thread_exit_quota_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        kernel_k_to_kernel_u(*krnl).thread_map[thread_ptr].syscall_progress == Some(thread_exit_quota_progress_before(size)),
{
    kernel_write_held_context_projection(krnl, lctx, cpu_id, process_ptr, thread_ptr, None);
    reveal(thread_exit_quota_step_pre);
}

/// Returning the `size` quota of the running last thread and of its process to their container is the quota step on
/// `pre`/`post`.
pub(super) proof fn thread_exit_quota_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, size: PageSize)
    requires
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        pre.thread_map[thread_ptr].syscall_progress == Some(thread_exit_quota_progress_before(size)),
        ({
            let thread = pre.thread_map[thread_ptr];
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
                thread_map: pre.thread_map.insert(thread_ptr, match size {
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

/// A state holding the cpu, `container_ptr`, `process_ptr` with its page table `pagetable` and IOMMU table
/// `iommu_table`, and the running `thread_ptr` that has returned every quota size, where no user 4K leaf of the page
/// table and no 4K leaf of the IOMMU table is left, gives the unlock-table step precondition.
pub(super) proof fn thread_exit_unlock_table_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    pagetable: RwLockPageTableRoot, iommu_table: Option<RwLockPageTableRoot>,
)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        krnl.prc_mp.dom().contains(process_ptr),
        !krnl.prc_mp.spec_index(process_ptr).view().zombie,
        krnl.prc_mp.spec_index(process_ptr).view().pagetable == pagetable,
        krnl.prc_mp.spec_index(process_ptr).view().iommu_table == iommu_table,
        krnl.pt_mp.dom().contains(pagetable),
        krnl.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        krnl.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitQuota { returned: PageSize::SZ1g }),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && KERNEL_MEM_END_L4INDEX <= l4i && krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end <= l4i
                && pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                ==> !pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present,
        iommu_table matches Some(it) ==> forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
            #![trigger krnl.it_mp.spec_index(it).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> !krnl.it_mp.spec_index(it).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
    ensures
        thread_exit_unlock_table_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        kernel_k_to_kernel_u(*krnl).thread_map[thread_ptr].owning_proc == process_ptr,
{
    kernel_write_held_context_projection(krnl, lctx, cpu_id, process_ptr, thread_ptr, None); kernel_pagetable_user_4k_unmapped_projection_at(krnl, process_ptr);
    if iommu_table is Some { kernel_iommu_table_4k_unmapped_projection_at(krnl, process_ptr); }
    reveal(thread_exit_unlock_table_step_pre);
}

/// Unlocking the reclaimed page table and IOMMU table once every quota size is returned is the unlock-table step on
/// `pre`/`post`.
pub(super) proof fn thread_exit_unlock_table_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr)
    requires
        pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        post == (KernelU {
            thread_map: pre.thread_map.insert(thread_ptr, ThreadU { syscall_progress: Some(SyscallProgress::ThreadExitZombie), ..pre.thread_map[thread_ptr] }),
            process_map: pre.process_map.insert(pre.thread_map[thread_ptr].owning_proc, ProcessU {
                pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, ..pre.process_map[pre.thread_map[thread_ptr].owning_proc].pagetable->Some_0 }),
                iommu_table: match pre.process_map[pre.thread_map[thread_ptr].owning_proc].iommu_table {
                    Some(t) => Some(PageTableU { lock_state: LockStateU::Unlocked, ..t }),
                    None => None,
                },
                ..pre.process_map[pre.thread_map[thread_ptr].owning_proc]
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

/// Steps reclaiming killed threads of the running thread's container `container_ptr`, recorded after the partial trace
/// that starts at `start` while the running thread's cpu, the thread, and the lock modes of its process and container keep
/// their projection at `entry`, extend it.
pub(super) proof fn thread_exit_trace_from_killed_thread_reclaim(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, entry: KernelU, cpu_id: CpuId, container_ptr: RwLockContainerPtr,
    process_ptr: RwLockProcessPtr,
)
    requires
        0 <= start <= before.len(),
        thread_exit_partial_trace(before.subrange(start, before.len() as int), pre, cpu_id),
        kernel_steps_prefix_unchanged(before, steps.view()),
        thread_exit_drop_step_pre(entry, cpu_id),
        entry.cpu_array[cpu_id as int].owning_container == container_ptr,
        entry.cpu_array[cpu_id as int].current_process == Some(process_ptr),
        entry.thread_map[entry.cpu_array[cpu_id as int].current_thread->Some_0].owning_container == container_ptr,
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            let old_u = steps.view()[j].old_u;
            let new_u = steps.view()[j].new_u;
            let thread_ptr = entry.cpu_array[cpu_id as int].current_thread->Some_0;
            &&& kernel_u_killed_thread_reclaim_step(old_u, new_u, cpu_id)
            &&& forall|t: RwLockThreadPtr| #![trigger old_u.thread_map[t]]
                old_u.thread_map.dom().contains(t) && (!new_u.thread_map.dom().contains(t) || new_u.thread_map[t] != old_u.thread_map[t]) ==> old_u.thread_map[t].owning_container == container_ptr
            &&& old_u.cpu_array[cpu_id as int] == entry.cpu_array[cpu_id as int]
            &&& old_u.thread_map.dom().contains(thread_ptr)
            &&& old_u.thread_map[thread_ptr] == entry.thread_map[thread_ptr]
            &&& old_u.process_map.dom().contains(process_ptr)
            &&& old_u.process_map[process_ptr].lock_state == entry.process_map[process_ptr].lock_state
            &&& old_u.container_map.dom().contains(container_ptr)
            &&& old_u.container_map[container_ptr].lock_state == entry.container_map[container_ptr].lock_state
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
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, entry: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr,
    container_ptr: RwLockContainerPtr, pcid: Pcid,
)
    requires
        0 <= start <= before.len() <= steps.view().len(),
        thread_exit_partial_trace(before.subrange(start, before.len() as int), pre, cpu_id),
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        thread_exit_flush_step_pre(entry, cpu_id),
        entry.cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        entry.thread_map[thread_ptr].owning_proc == process_ptr,
        entry.thread_map[thread_ptr].owning_container == container_ptr,
        entry.process_map[process_ptr].pcid == pcid,
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            let old_u = steps.view()[j].old_u;
            &&& kernel_u_cpu_tlb_cleared(old_u, steps.view()[j].new_u, pcid)
            &&& old_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& old_u.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& old_u.thread_map.dom().contains(thread_ptr)
            &&& old_u.thread_map[thread_ptr] == entry.thread_map[thread_ptr]
            &&& old_u.process_map.dom().contains(process_ptr)
            &&& old_u.process_map[process_ptr].lock_state == entry.process_map[process_ptr].lock_state
            &&& old_u.process_map[process_ptr].pagetable == entry.process_map[process_ptr].pagetable
            &&& old_u.process_map[process_ptr].pcid == entry.process_map[process_ptr].pcid
            &&& old_u.container_map.dom().contains(container_ptr)
            &&& old_u.container_map[container_ptr].lock_state is WriteLocked
            &&& old_u.kernel_l4_end == entry.kernel_l4_end
        },
    ensures
        thread_exit_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id),
{
    reveal(thread_exit_partial_trace); reveal(thread_exit_flush_step_pre); reveal(thread_exit_reclaim_step_pre);
    let trace = steps.view().subrange(start, steps.view().len() as int);
    let old_trace = before.subrange(start, before.len() as int);
    assert forall|j: int| #![trigger trace[j]] 0 < j < trace.len() implies thread_exit_middle_step(trace[j], cpu_id) by {
        if start + j < before.len() { assert(trace[j] == old_trace[j]); } else { assert(trace[j] == steps.view()[start + j]); }
    };
}

/// Quota refunds to the container chain of the running last thread after the flush is recorded, pushed after the
/// partial trace that starts at `start`, extend it.
pub(super) proof fn thread_exit_trace_from_refund(
    steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr,
    container_ptr: RwLockContainerPtr,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        0 <= start <= before.len() <= steps.view().len(),
        thread_exit_partial_trace(before.subrange(start, before.len() as int), pre, cpu_id),
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() ==> steps.view()[j] == before[j],
        forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() ==> {
            let old_u = steps.view()[j].old_u;
            &&& kernel_u_container_quota_4k_increased(old_u, steps.view()[j].new_u, container_ptr)
            &&& old_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& old_u.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& old_u.thread_map.dom().contains(thread_ptr)
            &&& old_u.thread_map[thread_ptr].lock_state is WriteLocked
            &&& old_u.thread_map[thread_ptr].owning_container == container_ptr
            &&& old_u.thread_map[thread_ptr].owning_proc == process_ptr
            &&& old_u.thread_map[thread_ptr].syscall_progress == Some(SyscallProgress::ThreadExitReclaim { flushed: true })
            &&& old_u.process_map.dom().contains(process_ptr)
            &&& old_u.process_map[process_ptr].lock_state is WriteLocked
            &&& old_u.process_map[process_ptr].pagetable is Some
            &&& old_u.process_map[process_ptr].pagetable->Some_0.lock_state is WriteLocked
            &&& old_u.container_map.dom().contains(container_ptr)
            &&& old_u.container_map[container_ptr].lock_state is WriteLocked
        },
    ensures
        thread_exit_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id),
{
    reveal(thread_exit_partial_trace); reveal(thread_exit_reclaim_step_pre);
    assert forall|j: int| #![trigger steps.view()[j]] before.len() <= j < steps.view().len() implies thread_exit_refund_step(steps.view()[j].old_u, steps.view()[j].new_u, cpu_id) by { thread_exit_refund_step_from_u(steps.view()[j].old_u, steps.view()[j].new_u, cpu_id); };
    let trace = steps.view().subrange(start, steps.view().len() as int);
    let old_trace = before.subrange(start, before.len() as int);
    assert forall|j: int| #![trigger trace[j]] 0 < j < trace.len() implies thread_exit_middle_step(trace[j], cpu_id) by {
        if start + j < before.len() { assert(trace[j] == old_trace[j]); } else { assert(trace[j] == steps.view()[start + j]); }
    };
}

/// A state holding the cpu, `container_ptr`, `process_ptr` with its page table `pagetable`, and the running `thread_ptr`
/// that records flushed reclaim progress gives the reclaim precondition after the flush.
pub(super) proof fn thread_exit_reclaim_flushed_step_pre_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        krnl.prc_mp.dom().contains(process_ptr),
        !krnl.prc_mp.spec_index(process_ptr).view().zombie,
        krnl.prc_mp.spec_index(process_ptr).view().pagetable == pagetable,
        krnl.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        krnl.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: true }),
    ensures
        thread_exit_reclaim_step_pre(kernel_k_to_kernel_u(*krnl), cpu_id, true),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int].current_thread == Some(thread_ptr),
        kernel_k_to_kernel_u(*krnl).thread_map[thread_ptr].owning_proc == process_ptr,
{
    kernel_write_held_context_projection(krnl, lctx, cpu_id, process_ptr, thread_ptr, None);
    reveal(thread_exit_reclaim_step_pre);
}

/// Replacing the window locks of the page table of the running thread's process `process_ptr` by `windows`, which differ
/// from them only at `locked`, now write-locked from unlocked, and at `unlocked`, now unlocked from write-locked, after the
/// flush is a middle step.
pub(super) proof fn thread_exit_pagetable_windows_changed_step_from_u(
    pre: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, windows: Map<WindowVa, LockStateU>, locked: WindowVa, unlocked: WindowVa,
)
    requires
        thread_exit_reclaim_step_pre(pre, cpu_id, true),
        pre.thread_map[pre.cpu_array[cpu_id as int].current_thread->Some_0].owning_proc == process_ptr,
        pre.process_map[process_ptr].pagetable is Some,
        windows.dom() == pre.process_map[process_ptr].pagetable->Some_0.pagetable_window_locks.dom(),
        forall|w: WindowVa| #![trigger windows[w]] windows.dom().contains(w) && windows[w] != pre.process_map[process_ptr].pagetable->Some_0.pagetable_window_locks[w] ==> {
            let o = pre.process_map[process_ptr].pagetable->Some_0.pagetable_window_locks[w];
            ||| w == locked && o is Unlocked && windows[w] is WriteLocked
            ||| w == unlocked && o is WriteLocked && windows[w] is Unlocked
        },
        post == (KernelU {
            process_map: pre.process_map.insert(process_ptr, ProcessU {
                pagetable: Some(PageTableU { pagetable_window_locks: windows, ..pre.process_map[process_ptr].pagetable->Some_0 }), ..pre.process_map[process_ptr]
            }),
            ..pre
        }),
    ensures thread_exit_middle_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{
    reveal(thread_exit_pagetable_windows_changed_step);
    let o = pre.process_map[process_ptr].pagetable->Some_0.pagetable_window_locks;
    let locked_set = o.dom().filter(|w: WindowVa| o[w] is Unlocked && windows[w] is WriteLocked);
    let unlocked_set = o.dom().filter(|w: WindowVa| o[w] is WriteLocked && windows[w] is Unlocked);
    assert(post.process_map[process_ptr].pagetable->Some_0.pagetable_window_locks == windows);
    assert(locked_set.subset_of(set![locked]) && unlocked_set.subset_of(set![unlocked]));
    vstd::set_lib::lemma_len_subset(locked_set, set![locked]); vstd::set_lib::lemma_len_subset(unlocked_set, set![unlocked]);
}

/// From `pre` to `post`, only kernel-only state, the running thread `thread_ptr`'s kernel-only fields, and the window locks
/// of the page table `pagetable` of its live process `process_ptr` change, and those window locks change only at `w`, to
/// `v`: write-locked from unlocked, or unlocked from write-locked or unlocked. Either side meets the reclaim precondition
/// after the flush; then both do and the step is a middle step. When the non-lock fields are not known unchanged, `post`
/// changes only the page table maps and keeps the process's mappings.
pub(super) proof fn thread_exit_window_locks_changed_implies_windows_changed_step(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, pagetable: RwLockPageTableRoot, thread_ptr: RwLockThreadPtr, w: WindowVa, v: LockStateU,
)
    requires
        thread_exit_reclaim_step_pre(kernel_k_to_kernel_u(*pre), cpu_id, true) && kernel_k_to_kernel_u(*pre).cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            && kernel_k_to_kernel_u(*pre).thread_map[thread_ptr].owning_proc == process_ptr
            || thread_exit_reclaim_step_pre(kernel_k_to_kernel_u(*post), cpu_id, true) && kernel_k_to_kernel_u(*post).cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
                && kernel_k_to_kernel_u(*post).thread_map[thread_ptr].owning_proc == process_ptr,
        process_pagetable_match(post.prc_mp, post.pt_mp),
        post.prc_mp.dom().contains(process_ptr),
        !post.prc_mp.spec_index(process_ptr).view().zombie,
        post.prc_mp.spec_index(process_ptr).view().pagetable == pagetable,
        pre.thr_mp.dom().contains(thread_ptr),
        *post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, pg_arr: post.pg_arr, thr_mp: post.thr_mp, allc_4k_mp: post.allc_4k_mp, ..*pre }),
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable),
        post.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread(),
        post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable)),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).locking_thread() == pre.thr_mp.spec_index(thread_ptr).locking_thread(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post) && kernel_container_nonlock_fields_and_quotas_unchanged(pre, post) || {
            &&& *post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..*pre })
            &&& pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k()
            &&& pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable).mapping_2m() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m()
            &&& pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable).mapping_1g() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_1g()
        },
        pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.pagetable_window_locks.dom().contains(w),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable).lower.pagetable_window_locks == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.pagetable_window_locks.insert(w, v),
        v is WriteLocked && pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.pagetable_window_locks[w] is Unlocked
            || v is Unlocked && (pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.pagetable_window_locks[w] is WriteLocked
                || pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.pagetable_window_locks[w] is Unlocked),
    ensures
        thread_exit_reclaim_step_pre(kernel_k_to_kernel_u(*pre), cpu_id, true),
        thread_exit_reclaim_step_pre(kernel_k_to_kernel_u(*post), cpu_id, true),
        thread_exit_middle_step(KernelStep { old_u: kernel_k_to_kernel_u(*pre), new_u: kernel_k_to_kernel_u(*post) }, cpu_id),
{
    if !(kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post) && kernel_container_nonlock_fields_and_quotas_unchanged(pre, post)) {
        broadcast use kernel_iommu_table_nonlock_fields_unchanged_for_equal, kernel_cpu_nonlock_fields_unchanged_for_equal, kernel_process_nonlock_fields_unchanged_for_equal,
            kernel_thread_nonlock_fields_unchanged_for_equal;
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged); };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(pre, post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
    }
    kernel_pagetable_window_locks_changed_implies_u_window_locks_replaced(pre, post, process_ptr, pagetable, thread_ptr);
    process_pagetable_match_process_at(post.prc_mp, post.pt_mp, process_ptr); kernel_process_projection_at(pre, process_ptr);
    assert(pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable).lower.pagetable_window_locks.dom() =~= pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.pagetable_window_locks.dom());
    reveal(thread_exit_reclaim_step_pre);
    thread_exit_pagetable_windows_changed_step_from_u(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id, process_ptr,
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable).lower.pagetable_window_locks, w, w);
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

/// A middle step recorded, if it changes the projection, after the partial trace that starts at `start` extends it.
pub(super) proof fn recorded_step_implies_thread_exit_trace(steps: &KernelSteps, before: Seq<KernelStep>, start: int, pre: KernelU, step_pre: KernelU, step_post: KernelU, cpu_id: CpuId)
    requires
        0 <= start <= before.len(),
        thread_exit_partial_trace(before.subrange(start, before.len() as int), pre, cpu_id),
        steps.view() == record_user_view_change(before, step_pre, step_post),
        thread_exit_middle_step(KernelStep { old_u: step_pre, new_u: step_post }, cpu_id),
    ensures
        thread_exit_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, before) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
{
    reveal(kernel_steps_prefix_unchanged);
    if step_pre == step_post { assert(steps.view().subrange(start, steps.view().len() as int) =~= before.subrange(start, before.len() as int)); }
    else {
        thread_exit_trace_push(steps, before, start, pre, step_pre, step_post, cpu_id);
        assert forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, before) implies #[trigger] kernel_steps_prefix_unchanged(base, steps.view()) by { assert(steps.view().subrange(0, base.len() as int) =~= before.subrange(0, base.len() as int)); };
    }
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
