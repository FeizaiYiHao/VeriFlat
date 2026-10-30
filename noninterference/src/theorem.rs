use vstd::prelude::*;
use crate::*;
use crate::{ni_alloc_quota::*, ni_cpu_hotplug::*, ni_ipc::*, ni_mmap_4k::*, ni_new_container::*, ni_new_endpoint::*, ni_new_process::*, ni_new_thread::*, ni_pci::*,
    ni_rebalance::*, ni_schedule::*, ni_share_4k::*, ni_unmap_4k::*, ni_iommu_map_4k::*, ni_iommu_unmap_4k::*, ni_kill_container::*, ni_kill_process::*, ni_thread_exit::*, ni_trap::*, ni_env::*};
use veriflat_map_4k::*;
use veriflat_syscall_alloc_quota::syscall_alloc_quota::syscall_alloc_quota_spec::*;
use veriflat_syscall_cpu_hotplug::syscall_cpu_hotplug::{syscall_cpu_offline_check_spec::*, syscall_cpu_hotplug_spec::*};
use veriflat_syscall_iommu_map_4k::syscall_iommu_map_4k::syscall_iommu_map_4k_spec::*;
use veriflat_syscall_iommu_unmap_4k::syscall_iommu_unmap_4k::syscall_iommu_unmap_4k_spec::*;
use veriflat_syscall_kill_process::{syscall_kill_container::syscall_kill_container_spec::*, syscall_kill_process::syscall_kill_process_spec::*};
use veriflat_syscall_ipc::syscall_ipc::{syscall_ipc_call_spec::*, syscall_ipc_spec::*};
use veriflat_syscall_mmap_4k::syscall_mmap_4k::syscall_mmap_4k_spec::*;
use veriflat_syscall_new_container::syscall_new_container::syscall_new_container_spec::*;
use veriflat_syscall_new_process::syscall_new_process::syscall_new_process_spec::*;
use veriflat_syscall_new_thread::{syscall_new_endpoint::syscall_new_endpoint_spec::*, syscall_new_thread::syscall_new_thread_spec::*};
use veriflat_syscall_pci::syscall_pci::syscall_pci_spec::*;
use veriflat_syscall_schedule::{rebalance_pull::rebalance_pull_spec::*, syscall_schedule::syscall_schedule_spec::*};
use veriflat_syscall_thread_exit::syscall_thread_exit::syscall_thread_exit_spec::*;
use veriflat_syscall_unmap_4k::syscall_unmap_4k::syscall_unmap_4k_spec::*;

verus! {
/// One step of a syscall or of the hardware environment, with the arguments its step specification takes.
pub ghost enum StepLabel {
    Mmap4kHold { range: VaRange4K }, Mmap4kEnter { range: VaRange4K, phase: Mmap4kPhase }, Mmap4kDirectory, Mmap4kDowngrade, Mmap4kLeaf, Mmap4kExit, Mmap4kRelease,
    Unmap4kEnter { range: VaRange4K }, Unmap4kLeaf { va: VAddr }, Unmap4kTlbCleared { pcid: Pcid }, Unmap4kFlushed, Unmap4kRefund, Unmap4kExit,
    IommuMap4kEnter { va_range: VaRange4K, iova_range: VaRange4K }, IommuMap4kDirectory, IommuMap4kLeaf, IommuMap4kExit,
    IommuUnmap4kEnter { iova_range: VaRange4K }, IommuUnmap4kLeaf, IommuUnmap4kFlush, IommuUnmap4kRefund, IommuUnmap4kExit,
    AllocQuota4k { alloc_amount: usize }, AllocThreadQuota4k { alloc_amount: usize },
    AllocQuota2m { alloc_amount: usize }, AllocThreadQuota2m { alloc_amount: usize },
    Schedule { entry_regs: Registers, flushed_pcid: Option<Pcid> }, RebalancePull,
    CpuOfflineRequest { target: CpuId }, CpuOfflineCheckHold, CpuOfflineCheck { regs: Registers, flushed_default_pcid: bool }, CpuOfflineCheckRelease, CpuOnline { target: CpuId },
    CpuOfflineRequestChild { target: CpuId }, CpuOnlineChild { target: CpuId },
    PciAttach { bus: usize, device: usize, function: usize },
    NewThreadEnter { regs: Registers, endpoint_index: Option<EndpointIdx> }, NewThreadFinish,
    NewEndpointEnter { slot: EndpointIdx }, NewEndpointFinish,
    NewProcessEnter { range: VaRange4K, regs: Registers, endpoint_index: Option<EndpointIdx>, with_iommu: bool }, NewProcessPublish, NewProcessFinish,
    NewContainerEnter { range: VaRange4K, funding: usize, process_quota: usize, transfer_cpu: CpuId, regs: Registers, endpoint_index: Option<EndpointIdx> }, NewContainerPublish, NewContainerFinish,
    Share4kDirectory, Share4kLeaf,
    IpcBlock { channel_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, regs: Registers, flushed_default_pcid: bool },
    IpcRendezvous { channel_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad },
    IpcCallHandoff { channel_index: EndpointIdx, regs: Registers, flushed_pcid: Option<Pcid> }, IpcAcceptCall { channel_index: EndpointIdx },
    IpcReplyHandoff { channel_index: EndpointIdx, regs: Registers, flushed_pcid: Option<Pcid> },
    IpcEndpointTransit { channel_index: EndpointIdx, waiting_state: ThreadState, payload_index: EndpointIdx }, IpcEndpointFinish,
    IpcPagesEnter { channel_index: EndpointIdx, waiting_state: ThreadState, range: VaRange4K }, IpcPagesLockTables { channel_index: EndpointIdx, tables: IpcPagesTables },
    IpcPagesCheck { channel_index: EndpointIdx }, IpcPagesDowngrade, IpcPagesUnlockTables, IpcPagesFinish { channel_index: EndpointIdx },
    KillContainerEnter { child_index: usize }, KillContainerMarkChild, KillContainerMarkRoot, KillContainerRetireRoot, KillContainerCpus, KillContainerMoveCpu,
    KillContainerPages, KillContainerMovePage { size: PageSize }, KillContainerRetireStage, KillContainerRetire, KillContainerFinish,
    KillProcessEnter { child_index: usize }, KillProcessMarkChild, KillProcessDangling, KillProcessMarkThread, KillProcessDequeueScheduled,
    KillProcessDequeueEndpoint, KillProcessCpuToIdle, KillProcessUnlink, KillProcessDescriptorDropped, KillProcessCallerWoken, KillProcessCallerTakenOver,
    KillProcessDanglingReclaimed, KillProcessEndpointReleased, KillProcessReassignFunctions, KillProcessLockTable, KillProcessLeaf, KillProcessTlbCleared,
    KillProcessFlushed, KillProcessIommuLeaf, KillProcessPagetableWindowsChanged, KillProcessRefund, KillProcessQuota, KillProcessUnlockTable, KillProcessZombify,
    KillProcessZombieRetire, KillProcessRetire, KillProcessFinish,
    ThreadExitEnter, ThreadExitDescriptorDropped, ThreadExitCallerWoken, ThreadExitCallerTakenOver, ThreadExitDanglingReclaimed, ThreadExitEndpointReleased,
    ThreadExitDrop, ThreadExitRelease, ThreadExitLockTable, ThreadExitLeaf, ThreadExitTlbCleared, ThreadExitFlushed, ThreadExitIommuLeaf,
    ThreadExitPagetableWindowsChanged, ThreadExitRefund, ThreadExitQuota, ThreadExitUnlockTable, ThreadExitFinish,
    TrapEnter, TrapReturn, TrapDivert,
    CpuTlbFilled { cpu_id: CpuId, pcid: Pcid, added: SingleTLB }, IommuTlbFilled { did: VtdDomainId, added: SingleTLB }, IommuContextCacheFilled,
}

/// `new_u` follows `old_u` by the step `label` on cpu `cpu_id`.
pub open spec fn labeled_step(label: StepLabel, old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    match label {
        StepLabel::Mmap4kHold { range } => mmap_4k_hold_step_pre(old_u, cpu_id, range) && mmap_4k_hold_step(old_u, new_u, cpu_id),
        StepLabel::Mmap4kEnter { range, phase } => mmap_4k_enter_step_pre(old_u, cpu_id, range, phase) && mmap_4k_enter_step(old_u, new_u, cpu_id, range, phase),
        StepLabel::Mmap4kDirectory => mmap_4k_directory_step_pre(old_u, cpu_id) && mmap_4k_directory_step(old_u, new_u, cpu_id),
        StepLabel::Mmap4kDowngrade => mmap_4k_downgrade_step_pre(old_u, cpu_id) && mmap_4k_downgrade_step(old_u, new_u, cpu_id),
        StepLabel::Mmap4kLeaf => mmap_4k_leaf_step_pre(old_u, cpu_id) && mmap_4k_leaf_step(old_u, new_u, cpu_id),
        StepLabel::Mmap4kExit => mmap_4k_exit_step_pre(old_u, cpu_id) && mmap_4k_exit_step(old_u, new_u, cpu_id),
        StepLabel::Mmap4kRelease => mmap_4k_release_step_pre(old_u, cpu_id) && mmap_4k_release_step(old_u, new_u, cpu_id),
        StepLabel::Unmap4kEnter { range } => unmap_4k_enter_step_pre(old_u, cpu_id, range) && unmap_4k_enter_step(old_u, new_u, cpu_id, range),
        StepLabel::Unmap4kLeaf { va } => unmap_4k_leaf_step_pre(old_u, cpu_id, va) && unmap_4k_leaf_step(old_u, new_u, cpu_id, va),
        StepLabel::Unmap4kTlbCleared { pcid } => unmap_4k_flush_step_pre(old_u, cpu_id) && kernel_u_cpu_tlb_cleared(old_u, new_u, pcid),
        StepLabel::Unmap4kFlushed => unmap_4k_flush_step_pre(old_u, cpu_id) && unmap_4k_flushed_step(old_u, new_u, cpu_id),
        StepLabel::Unmap4kRefund => unmap_4k_refund_step_pre(old_u, cpu_id)
            && kernel_u_container_quota_4k_increased(old_u, new_u, old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].owning_container),
        StepLabel::Unmap4kExit => unmap_4k_exit_step_pre(old_u, cpu_id) && unmap_4k_exit_step(old_u, new_u, cpu_id),
        StepLabel::IommuMap4kEnter { va_range, iova_range } =>
            iommu_map_4k_enter_step_pre(old_u, cpu_id, va_range, iova_range) && iommu_map_4k_enter_step(old_u, new_u, cpu_id, va_range, iova_range),
        StepLabel::IommuMap4kDirectory => iommu_map_4k_directory_step_pre(old_u, cpu_id) && iommu_map_4k_directory_step(old_u, new_u, cpu_id),
        StepLabel::IommuMap4kLeaf => iommu_map_4k_leaf_step_pre(old_u, cpu_id) && iommu_map_4k_leaf_step(old_u, new_u, cpu_id),
        StepLabel::IommuMap4kExit => iommu_map_4k_exit_step_pre(old_u, cpu_id) && iommu_map_4k_exit_step(old_u, new_u, cpu_id),
        StepLabel::IommuUnmap4kEnter { iova_range } =>
            iommu_unmap_4k_enter_step_pre(old_u, cpu_id, iova_range) && iommu_unmap_4k_enter_step(old_u, new_u, cpu_id, iova_range),
        StepLabel::IommuUnmap4kLeaf => iommu_unmap_4k_leaf_step_pre(old_u, cpu_id) && iommu_unmap_4k_leaf_step(old_u, new_u, cpu_id),
        StepLabel::IommuUnmap4kFlush => iommu_unmap_4k_flush_step_pre(old_u, cpu_id) && iommu_unmap_4k_flush_step(old_u, new_u, cpu_id),
        StepLabel::IommuUnmap4kRefund => iommu_unmap_4k_refund_step_pre(old_u, cpu_id)
            && kernel_u_container_quota_4k_increased(old_u, new_u, old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].owning_container),
        StepLabel::IommuUnmap4kExit => iommu_unmap_4k_exit_step_pre(old_u, cpu_id) && iommu_unmap_4k_exit_step(old_u, new_u, cpu_id),
        StepLabel::AllocQuota4k { alloc_amount } => alloc_quota_4k_step_pre(old_u, cpu_id, alloc_amount) && alloc_quota_4k_step(old_u, new_u, cpu_id, alloc_amount),
        StepLabel::AllocThreadQuota4k { alloc_amount } => alloc_thread_quota_4k_step_pre(old_u, cpu_id, alloc_amount) && alloc_thread_quota_4k_step(old_u, new_u, cpu_id, alloc_amount),
        StepLabel::AllocQuota2m { alloc_amount } => alloc_quota_2m_step_pre(old_u, cpu_id, alloc_amount) && alloc_quota_2m_step(old_u, new_u, cpu_id, alloc_amount),
        StepLabel::AllocThreadQuota2m { alloc_amount } => alloc_thread_quota_2m_step_pre(old_u, cpu_id, alloc_amount) && alloc_thread_quota_2m_step(old_u, new_u, cpu_id, alloc_amount),
        StepLabel::Schedule { entry_regs, flushed_pcid } => schedule_step_pre(old_u, cpu_id) && schedule_step(old_u, new_u, cpu_id, entry_regs, flushed_pcid),
        StepLabel::RebalancePull => rebalance_pull_step_pre(old_u, cpu_id) && rebalance_pull_step(old_u, new_u, cpu_id),
        StepLabel::CpuOfflineRequest { target } => cpu_offline_request_step_pre(old_u, cpu_id, target) && cpu_offline_request_step(old_u, new_u, cpu_id, target),
        StepLabel::CpuOfflineCheckHold => cpu_offline_check_hold_step_pre(old_u, cpu_id) && cpu_offline_check_hold_step(old_u, new_u, cpu_id),
        StepLabel::CpuOfflineCheck { regs, flushed_default_pcid } => cpu_offline_check_step_pre(old_u, cpu_id) && cpu_offline_check_step(old_u, new_u, cpu_id, regs, flushed_default_pcid),
        StepLabel::CpuOfflineCheckRelease => cpu_offline_check_release_step_pre(old_u, cpu_id) && cpu_offline_check_release_step(old_u, new_u, cpu_id),
        StepLabel::CpuOnline { target } => cpu_online_step_pre(old_u, cpu_id, target) && cpu_online_step(old_u, new_u, cpu_id, target),
        StepLabel::CpuOfflineRequestChild { target } =>
            cpu_offline_request_child_step_pre(old_u, cpu_id, target) && cpu_offline_request_child_step(old_u, new_u, cpu_id, target),
        StepLabel::CpuOnlineChild { target } => cpu_online_child_step_pre(old_u, cpu_id, target) && cpu_online_child_step(old_u, new_u, cpu_id, target),
        StepLabel::PciAttach { bus, device, function } => pci_attach_dma_step_pre(old_u, cpu_id, bus, device, function) && pci_attach_dma_step(old_u, new_u, cpu_id, bus, device, function),
        StepLabel::NewThreadEnter { regs, endpoint_index } =>
            new_thread_enter_step_pre(old_u, cpu_id, endpoint_index) && new_thread_enter_step(old_u, new_u, cpu_id, regs, endpoint_index),
        StepLabel::NewThreadFinish => new_thread_finish_step_pre(old_u, cpu_id) && new_thread_finish_step(old_u, new_u, cpu_id),
        StepLabel::NewEndpointEnter { slot } => new_endpoint_enter_step_pre(old_u, cpu_id, slot) && new_endpoint_enter_step(old_u, new_u, cpu_id, slot),
        StepLabel::NewEndpointFinish => new_endpoint_finish_step_pre(old_u, cpu_id) && new_endpoint_finish_step(old_u, new_u, cpu_id),
        StepLabel::NewProcessEnter { range, regs, endpoint_index, with_iommu } => new_process_enter_step_pre(old_u, cpu_id, range, endpoint_index, with_iommu)
            && new_process_enter_step(old_u, new_u, cpu_id, range, regs, endpoint_index, with_iommu),
        StepLabel::NewProcessPublish => new_process_publish_step_pre(old_u, cpu_id) && new_process_publish_step(old_u, new_u, cpu_id),
        StepLabel::NewProcessFinish => new_process_finish_step_pre(old_u, cpu_id) && new_process_finish_step(old_u, new_u, cpu_id),
        StepLabel::NewContainerEnter { range, funding, process_quota, transfer_cpu, regs, endpoint_index } =>
            new_container_enter_step_pre(old_u, cpu_id, range, funding, process_quota, transfer_cpu, endpoint_index)
            && new_container_enter_step(old_u, new_u, cpu_id, range, funding, process_quota, transfer_cpu, regs, endpoint_index),
        StepLabel::NewContainerPublish => new_container_publish_step_pre(old_u, cpu_id) && new_container_publish_step(old_u, new_u, cpu_id),
        StepLabel::NewContainerFinish => new_container_finish_step_pre(old_u, cpu_id) && new_container_finish_step(old_u, new_u, cpu_id),
        StepLabel::Share4kDirectory => share_4k_directory_step_pre(old_u, cpu_id) && share_4k_directory_step(old_u, new_u, cpu_id),
        StepLabel::Share4kLeaf => share_4k_leaf_step_pre(old_u, cpu_id) && share_4k_leaf_step(old_u, new_u, cpu_id),
        StepLabel::IpcBlock { channel_index, waiting_state, payload, regs, flushed_default_pcid } => ipc_block_step_pre(old_u, cpu_id, channel_index, waiting_state)
            && ipc_block_step(old_u, new_u, cpu_id, channel_index, waiting_state, payload, regs, flushed_default_pcid),
        StepLabel::IpcRendezvous { channel_index, waiting_state, payload } => ipc_rendezvous_step_pre(old_u, cpu_id, channel_index, waiting_state, payload)
            && ipc_rendezvous_step(old_u, new_u, cpu_id, channel_index, waiting_state, payload),
        StepLabel::IpcCallHandoff { channel_index, regs, flushed_pcid } => ipc_call_handoff_step_pre(old_u, cpu_id, channel_index)
            && ipc_call_handoff_step(old_u, new_u, cpu_id, channel_index, regs, flushed_pcid),
        StepLabel::IpcAcceptCall { channel_index } => ipc_accept_call_step_pre(old_u, cpu_id, channel_index) && ipc_accept_call_step(old_u, new_u, cpu_id, channel_index),
        StepLabel::IpcReplyHandoff { channel_index, regs, flushed_pcid } => ipc_reply_handoff_step_pre(old_u, cpu_id, channel_index)
            && ipc_reply_handoff_step(old_u, new_u, cpu_id, channel_index, regs, flushed_pcid),
        StepLabel::IpcEndpointTransit { channel_index, waiting_state, payload_index } =>
            ipc_endpoint_transit_step_pre(old_u, cpu_id, channel_index, waiting_state, payload_index)
            && ipc_endpoint_transit_step(old_u, new_u, cpu_id, channel_index, waiting_state, payload_index),
        StepLabel::IpcEndpointFinish => ipc_endpoint_finish_step_pre(old_u, cpu_id) && ipc_endpoint_finish_step(old_u, new_u, cpu_id),
        StepLabel::IpcPagesEnter { channel_index, waiting_state, range } => ipc_pages_enter_step_pre(old_u, cpu_id, channel_index, waiting_state, range)
            && ipc_pages_enter_step(old_u, new_u, cpu_id, channel_index, waiting_state, range),
        StepLabel::IpcPagesLockTables { channel_index, tables } =>
            ipc_pages_lock_tables_step_pre(old_u, cpu_id, channel_index, tables) && ipc_pages_lock_tables_step(old_u, new_u, cpu_id, tables),
        StepLabel::IpcPagesCheck { channel_index } => ipc_pages_check_step_pre(old_u, cpu_id, channel_index) && ipc_pages_check_step(old_u, new_u, cpu_id),
        StepLabel::IpcPagesDowngrade => ipc_pages_downgrade_step_pre(old_u, cpu_id) && ipc_pages_downgrade_step(old_u, new_u, cpu_id),
        StepLabel::IpcPagesUnlockTables => ipc_pages_unlock_tables_step_pre(old_u, cpu_id) && ipc_pages_unlock_tables_step(old_u, new_u, cpu_id),
        StepLabel::IpcPagesFinish { channel_index } =>
            ipc_pages_finish_step_pre(old_u, cpu_id, channel_index) && ipc_pages_finish_step(old_u, new_u, cpu_id, channel_index),
        StepLabel::KillContainerEnter { child_index } => kill_container_enter_step_pre(old_u, cpu_id, child_index) && kill_container_enter_step(old_u, new_u, cpu_id, child_index),
        StepLabel::KillContainerMarkChild => kill_container_step_pre(old_u, cpu_id) && kill_container_mark_child_step(old_u, new_u, cpu_id),
        StepLabel::KillContainerMarkRoot => kill_container_step_pre(old_u, cpu_id) && kill_container_mark_root_step(old_u, new_u, cpu_id),
        StepLabel::KillContainerRetireRoot => kill_container_step_pre(old_u, cpu_id) && kill_container_retire_root_step(old_u, new_u, cpu_id),
        StepLabel::KillContainerCpus => kill_container_step_pre(old_u, cpu_id) && kill_container_cpus_step(old_u, new_u, cpu_id),
        StepLabel::KillContainerMoveCpu => kill_container_step_pre(old_u, cpu_id) && kill_container_move_cpu_step(old_u, new_u, cpu_id),
        StepLabel::KillContainerPages => kill_container_step_pre(old_u, cpu_id) && kill_container_pages_step(old_u, new_u, cpu_id),
        StepLabel::KillContainerMovePage { size } => kill_container_step_pre(old_u, cpu_id) && kill_container_move_page_step(old_u, new_u, cpu_id, size),
        StepLabel::KillContainerRetireStage => kill_container_step_pre(old_u, cpu_id) && kill_container_retire_stage_step(old_u, new_u, cpu_id),
        StepLabel::KillContainerRetire => kill_container_step_pre(old_u, cpu_id) && kill_container_retire_step(old_u, new_u, cpu_id),
        StepLabel::KillContainerFinish => kill_container_finish_step_pre(old_u, cpu_id) && kill_container_finish_step(old_u, new_u, cpu_id),
        StepLabel::KillProcessEnter { child_index } => kill_process_enter_step_pre(old_u, cpu_id, child_index) && kill_process_enter_step(old_u, new_u, cpu_id, child_index),
        StepLabel::KillProcessMarkChild => kill_process_step_pre(old_u, cpu_id) && kill_process_mark_child_step(old_u, new_u, cpu_id),
        StepLabel::KillProcessDangling => kill_process_step_pre(old_u, cpu_id) && kill_process_dangling_step(old_u, new_u, cpu_id),
        StepLabel::KillProcessMarkThread => kill_process_step_pre(old_u, cpu_id) && kill_process_mark_thread_step(old_u, new_u, cpu_id),
        StepLabel::KillProcessDequeueScheduled => kill_process_step_pre(old_u, cpu_id) && kill_process_dequeue_scheduled_step(old_u, new_u, cpu_id),
        StepLabel::KillProcessDequeueEndpoint => kill_process_step_pre(old_u, cpu_id) && kill_process_dequeue_endpoint_step(old_u, new_u, cpu_id),
        StepLabel::KillProcessCpuToIdle => kill_process_step_pre(old_u, cpu_id) && kill_process_cpu_to_idle_step(old_u, new_u, cpu_id),
        StepLabel::KillProcessUnlink => kill_process_step_pre(old_u, cpu_id) && kill_process_unlink_step(old_u, new_u, cpu_id),
        StepLabel::KillProcessDescriptorDropped => kill_process_step_pre(old_u, cpu_id) && kill_process_reclaim_in_target(old_u, new_u, cpu_id) && kernel_u_killed_descriptor_dropped(old_u, new_u),
        StepLabel::KillProcessCallerWoken => kill_process_step_pre(old_u, cpu_id) && kill_process_reclaim_in_target(old_u, new_u, cpu_id) && kernel_u_killed_caller_woken(old_u, new_u, cpu_id),
        StepLabel::KillProcessCallerTakenOver => kill_process_step_pre(old_u, cpu_id) && kill_process_reclaim_in_target(old_u, new_u, cpu_id) && kernel_u_killed_caller_taken_over(old_u, new_u),
        StepLabel::KillProcessDanglingReclaimed => kill_process_step_pre(old_u, cpu_id) && kill_process_reclaim_in_target(old_u, new_u, cpu_id) && kernel_u_dangling_thread_reclaimed(old_u, new_u),
        StepLabel::KillProcessEndpointReleased => kill_process_step_pre(old_u, cpu_id) && kill_process_reclaim_in_target(old_u, new_u, cpu_id) && kernel_u_killed_endpoint_released(old_u, new_u),
        StepLabel::KillProcessReassignFunctions => kill_process_step_pre(old_u, cpu_id) && kill_process_reassign_functions_step(old_u, new_u, cpu_id),
        StepLabel::KillProcessLockTable => kill_process_step_pre(old_u, cpu_id) && kill_process_lock_table_step(old_u, new_u, cpu_id),
        StepLabel::KillProcessLeaf => kill_process_step_pre(old_u, cpu_id) && kill_process_leaf_step(old_u, new_u, cpu_id),
        StepLabel::KillProcessTlbCleared => kill_process_step_pre(old_u, cpu_id) && kill_process_flush_step_pre(old_u, cpu_id) && kernel_u_cpu_tlb_cleared(old_u, new_u, old_u.process_map[kill_target(old_u, cpu_id)].pcid),
        StepLabel::KillProcessFlushed => kill_process_step_pre(old_u, cpu_id) && kill_process_flush_step_pre(old_u, cpu_id) && kill_process_flushed_step(old_u, new_u, cpu_id),
        StepLabel::KillProcessIommuLeaf => kill_process_step_pre(old_u, cpu_id) && kill_process_iommu_leaf_step(old_u, new_u, cpu_id),
        StepLabel::KillProcessPagetableWindowsChanged => kill_process_step_pre(old_u, cpu_id) && kill_process_pagetable_windows_changed_step(old_u, new_u, cpu_id),
        StepLabel::KillProcessRefund => kill_process_step_pre(old_u, cpu_id) && kill_process_refund_step(old_u, new_u, cpu_id),
        StepLabel::KillProcessQuota => kill_process_step_pre(old_u, cpu_id) && kill_process_quota_step(old_u, new_u, cpu_id),
        StepLabel::KillProcessUnlockTable => kill_process_step_pre(old_u, cpu_id) && kill_process_unlock_table_step(old_u, new_u, cpu_id),
        StepLabel::KillProcessZombify => kill_process_step_pre(old_u, cpu_id) && kill_process_zombify_step(old_u, new_u, cpu_id),
        StepLabel::KillProcessZombieRetire => kill_process_step_pre(old_u, cpu_id) && kill_process_zombie_retire_step(old_u, new_u, cpu_id),
        StepLabel::KillProcessRetire => kill_process_step_pre(old_u, cpu_id) && kill_process_retire_step(old_u, new_u, cpu_id),
        StepLabel::KillProcessFinish => kill_process_finish_step_pre(old_u, cpu_id) && kill_process_finish_step(old_u, new_u, cpu_id),
        StepLabel::ThreadExitEnter => thread_exit_enter_step_pre(old_u, cpu_id) && thread_exit_enter_step(old_u, new_u, cpu_id),
        StepLabel::ThreadExitDescriptorDropped => thread_exit_drop_step_pre(old_u, cpu_id) && thread_exit_reclaim_in_container(old_u, new_u, cpu_id) && kernel_u_killed_descriptor_dropped(old_u, new_u),
        StepLabel::ThreadExitCallerWoken => thread_exit_drop_step_pre(old_u, cpu_id) && thread_exit_reclaim_in_container(old_u, new_u, cpu_id) && kernel_u_killed_caller_woken(old_u, new_u, cpu_id),
        StepLabel::ThreadExitCallerTakenOver => thread_exit_drop_step_pre(old_u, cpu_id) && thread_exit_reclaim_in_container(old_u, new_u, cpu_id) && kernel_u_killed_caller_taken_over(old_u, new_u),
        StepLabel::ThreadExitDanglingReclaimed => thread_exit_drop_step_pre(old_u, cpu_id) && thread_exit_reclaim_in_container(old_u, new_u, cpu_id) && kernel_u_dangling_thread_reclaimed(old_u, new_u),
        StepLabel::ThreadExitEndpointReleased => thread_exit_drop_step_pre(old_u, cpu_id) && thread_exit_reclaim_in_container(old_u, new_u, cpu_id) && kernel_u_killed_endpoint_released(old_u, new_u),
        StepLabel::ThreadExitDrop => thread_exit_drop_step_pre(old_u, cpu_id) && thread_exit_drop_step(old_u, new_u, cpu_id),
        StepLabel::ThreadExitRelease => thread_exit_drop_step_pre(old_u, cpu_id) && thread_exit_release_step(old_u, new_u, cpu_id),
        StepLabel::ThreadExitLockTable => thread_exit_lock_table_step_pre(old_u, cpu_id) && thread_exit_lock_table_step(old_u, new_u, cpu_id),
        StepLabel::ThreadExitLeaf => thread_exit_reclaim_step_pre(old_u, cpu_id, false) && thread_exit_leaf_step(old_u, new_u, cpu_id),
        StepLabel::ThreadExitTlbCleared => thread_exit_flush_step_pre(old_u, cpu_id)
            && kernel_u_cpu_tlb_cleared(old_u, new_u, old_u.process_map[old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].owning_proc].pcid),
        StepLabel::ThreadExitFlushed => thread_exit_flush_step_pre(old_u, cpu_id) && thread_exit_flushed_step(old_u, new_u, cpu_id),
        StepLabel::ThreadExitIommuLeaf => thread_exit_reclaim_step_pre(old_u, cpu_id, true) && thread_exit_iommu_leaf_step(old_u, new_u, cpu_id),
        StepLabel::ThreadExitPagetableWindowsChanged => thread_exit_reclaim_step_pre(old_u, cpu_id, true) && thread_exit_pagetable_windows_changed_step(old_u, new_u, cpu_id),
        StepLabel::ThreadExitRefund => thread_exit_reclaim_step_pre(old_u, cpu_id, true) && thread_exit_refund_step(old_u, new_u, cpu_id),
        StepLabel::ThreadExitQuota => thread_exit_quota_step_pre(old_u, cpu_id) && thread_exit_quota_step(old_u, new_u, cpu_id),
        StepLabel::ThreadExitUnlockTable => thread_exit_unlock_table_step_pre(old_u, cpu_id) && thread_exit_unlock_table_step(old_u, new_u, cpu_id),
        StepLabel::ThreadExitFinish => thread_exit_finish_step_pre(old_u, cpu_id) && thread_exit_finish_step(old_u, new_u, cpu_id),
        StepLabel::TrapEnter => kernel_u_trap_enter_step_pre(old_u, cpu_id) && kernel_u_trap_enter_step(old_u, new_u, cpu_id),
        StepLabel::TrapReturn => kernel_u_trap_return_step_pre(old_u, cpu_id) && kernel_u_trap_return_step(old_u, new_u, cpu_id),
        StepLabel::TrapDivert => kernel_u_trap_divert_step_pre(old_u, cpu_id) && kernel_u_trap_divert_step(old_u, new_u, cpu_id),
        StepLabel::CpuTlbFilled { cpu_id: filled_cpu, pcid, added } => kernel_u_cpu_tlb_filled_step(old_u, new_u, filled_cpu, pcid, added),
        StepLabel::IommuTlbFilled { did, added } => kernel_u_iommu_tlb_filled_step(old_u, new_u, did, added),
        StepLabel::IommuContextCacheFilled => kernel_u_iommu_context_cache_filled_step(old_u, new_u),
    }
}

/// Isolation is symmetric in its two domains.
pub proof fn isolated_symmetric(u: KernelU, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires isolated(u, a, b),
    ensures isolated(u, b, a),
{}

/// Unwinding over a trace. `us[i + 1]` follows `us[i]`, both user projections of well-formed kernels, by the
/// step `labels[i]` of cpu `cpus[i]` of domain `steppers[i]`, which is `a` or `b`; a hardware TLB or context-cache fill
/// changes no domain view, so it may be attributed to either domain. When a step receives an
/// endpoint or shares a page from a peer outside its domain, that peer is honest: the other domain neither
/// holds nor waits on the endpoint, and the other domain maps no copy of the page in a page table or IOMMU table. Then `us[n]` is isolated,
/// and steps of `a` from `us[m]` to `us[n]` leave the view of `b` unchanged.
pub proof fn trace_ni_at(us: Seq<KernelU>, labels: Seq<StepLabel>, cpus: Seq<CpuId>, steppers: Seq<RwLockContainerPtr>, a: RwLockContainerPtr, b: RwLockContainerPtr, m: int, n: int)
    requires
        us.len() == labels.len() + 1,
        cpus.len() == labels.len(),
        steppers.len() == labels.len(),
        0 <= n < us.len(),
        isolated(us[0], a, b),
        forall|i: int| #![trigger labels[i]] 0 <= i < labels.len() ==> {
            let u = us[i];
            let x = steppers[i];
            let y = if x == a { b } else { a };
            let progress = u.thread_map[u.cpu_array[cpus[i] as int].current_thread->Some_0].syscall_progress->Some_0;
            let peer = progress->IpcEndpoint_peer;
            let payload = u.thread_map[peer].endpoint_descriptors[u.thread_map[peer].ipc_payload->Endpoint_endpoint_index as int]->Some_0;
            let source = u.thread_map[share_4k_objects(u, cpus[i]).source_thread].owning_proc;
            &&& x == a || x == b
            &&& kernel_u_ownership_wf(u)
            &&& kernel_u_ownership_wf(us[i + 1])
            &&& steps_in_domain(u, cpus[i], x)
            &&& labeled_step(labels[i], u, us[i + 1], cpus[i])
            &&& labels[i] is IpcEndpointFinish && !progress->IpcEndpoint_caller_sends && !in_domain(u, x, u.thread_map[peer].owning_container) ==> {
                &&& forall|t: RwLockThreadPtr, j: EndpointIdx| #![trigger u.endpoint_map[payload].owning_threads.contains((t, j))]
                    u.endpoint_map[payload].owning_threads.contains((t, j)) ==> !in_domain(u, y, u.thread_map[t].owning_container)
                &&& forall|j: int| #![trigger u.endpoint_map[payload].queue[j]]
                    0 <= j < u.endpoint_map[payload].queue.len() ==> !in_domain(u, y, u.thread_map[u.endpoint_map[payload].queue[j]].owning_container)
            }
            &&& labels[i] is Share4kLeaf && !in_domain(u, x, u.process_map[source].owning_container) ==> {
                let shared = u.process_map[source].pagetable->Some_0.mapping_4k[progress->Share4k_source_range.view()[progress->Share4k_shared as int]].addr;
                &&& forall|q: RwLockProcessPtr, v: VAddr| #![trigger u.process_map[q].pagetable->Some_0.mapping_4k[v]]
                    u.process_map.dom().contains(q) && in_domain(u, y, u.process_map[q].owning_container) && u.process_map[q].pagetable is Some && u.process_map[q].pagetable->Some_0.mapping_4k.dom().contains(v)
                        ==> u.process_map[q].pagetable->Some_0.mapping_4k[v].addr != shared
                &&& forall|q: RwLockProcessPtr, v: VAddr| #![trigger u.process_map[q].iommu_table->Some_0.mapping_4k[v]]
                    u.process_map.dom().contains(q) && in_domain(u, y, u.process_map[q].owning_container) && u.process_map[q].iommu_table is Some && u.process_map[q].iommu_table->Some_0.mapping_4k.dom().contains(v)
                        ==> u.process_map[q].iommu_table->Some_0.mapping_4k[v].addr != shared
            }
        },
    ensures
        isolated(us[n], a, b),
        0 <= m <= n && (forall|i: int| #![trigger steppers[i]] m <= i < n ==> steppers[i] == a) ==> domain_view(us[n], b) =~~= domain_view(us[m], b),
    decreases n,
{
    if n > 0 {
        let i = n - 1;
        let (old_u, new_u, cpu_id) = (us[i], us[n], cpus[i]);
        let x = steppers[i];
        let y = if x == a { b } else { a };
        let progress = old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].syscall_progress->Some_0;
        let peer = progress->IpcEndpoint_peer;
        let payload = old_u.thread_map[peer].endpoint_descriptors[old_u.thread_map[peer].ipc_payload->Endpoint_endpoint_index as int]->Some_0;
        let source = old_u.thread_map[share_4k_objects(old_u, cpu_id).source_thread].owning_proc;
        trace_ni_at(us, labels, cpus, steppers, a, b, m, i);
        if x != a { isolated_symmetric(old_u, a, b); }
        match labels[i] {
            StepLabel::Mmap4kHold { range } => { mmap_4k_hold_step_lr(old_u, new_u, cpu_id, range, x, y); mmap_4k_hold_step_iso(old_u, new_u, cpu_id, range, x, y); },
            StepLabel::Mmap4kEnter { range, phase } => { mmap_4k_enter_step_lr(old_u, new_u, cpu_id, range, phase, x, y); mmap_4k_enter_step_iso(old_u, new_u, cpu_id, range, phase, x, y); },
            StepLabel::Mmap4kDirectory => { mmap_4k_directory_step_lr(old_u, new_u, cpu_id, x, y); mmap_4k_directory_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::Mmap4kDowngrade => { mmap_4k_downgrade_step_lr(old_u, new_u, cpu_id, x, y); mmap_4k_downgrade_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::Mmap4kLeaf => { mmap_4k_leaf_step_lr(old_u, new_u, cpu_id, x, y); mmap_4k_leaf_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::Mmap4kExit => { mmap_4k_exit_step_lr(old_u, new_u, cpu_id, x, y); mmap_4k_exit_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::Mmap4kRelease => { mmap_4k_release_step_lr(old_u, new_u, cpu_id, x, y); mmap_4k_release_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::Unmap4kEnter { range } => { unmap_4k_enter_step_lr(old_u, new_u, cpu_id, range, x, y); unmap_4k_enter_step_iso(old_u, new_u, cpu_id, range, x, y); },
            StepLabel::Unmap4kLeaf { va } => { unmap_4k_leaf_step_lr(old_u, new_u, cpu_id, va, x, y); unmap_4k_leaf_step_iso(old_u, new_u, cpu_id, va, x, y); },

            StepLabel::Unmap4kTlbCleared { pcid } => { unmap_4k_tlb_cleared_step_lr(old_u, new_u, cpu_id, pcid, x, y); unmap_4k_tlb_cleared_step_iso(old_u, new_u, cpu_id, pcid, x, y); },
            StepLabel::Unmap4kFlushed => { unmap_4k_flushed_step_lr(old_u, new_u, cpu_id, x, y); unmap_4k_flushed_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::Unmap4kRefund => { unmap_4k_refund_step_lr(old_u, new_u, cpu_id, x, y); unmap_4k_refund_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::Unmap4kExit => { unmap_4k_exit_step_lr(old_u, new_u, cpu_id, x, y); unmap_4k_exit_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::IommuMap4kEnter { va_range, iova_range } => {
                iommu_map_4k_enter_step_lr(old_u, new_u, cpu_id, va_range, iova_range, x, y); iommu_map_4k_enter_step_iso(old_u, new_u, cpu_id, va_range, iova_range, x, y);
            },
            StepLabel::IommuMap4kDirectory => { iommu_map_4k_directory_step_lr(old_u, new_u, cpu_id, x, y); iommu_map_4k_directory_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::IommuMap4kLeaf => { iommu_map_4k_leaf_step_lr(old_u, new_u, cpu_id, x, y); iommu_map_4k_leaf_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::IommuMap4kExit => { iommu_map_4k_exit_step_lr(old_u, new_u, cpu_id, x, y); iommu_map_4k_exit_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::IommuUnmap4kEnter { iova_range } => {
                iommu_unmap_4k_enter_step_lr(old_u, new_u, cpu_id, iova_range, x, y); iommu_unmap_4k_enter_step_iso(old_u, new_u, cpu_id, iova_range, x, y);
            },
            StepLabel::IommuUnmap4kLeaf => { iommu_unmap_4k_leaf_step_lr(old_u, new_u, cpu_id, x, y); iommu_unmap_4k_leaf_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::IommuUnmap4kFlush => { iommu_unmap_4k_flush_step_lr(old_u, new_u, cpu_id, x, y); iommu_unmap_4k_flush_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::IommuUnmap4kRefund => { iommu_unmap_4k_refund_step_lr(old_u, new_u, cpu_id, x, y); iommu_unmap_4k_refund_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::IommuUnmap4kExit => { iommu_unmap_4k_exit_step_lr(old_u, new_u, cpu_id, x, y); iommu_unmap_4k_exit_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::AllocQuota4k { alloc_amount } => { alloc_quota_4k_step_lr(old_u, new_u, cpu_id, alloc_amount, x, y); alloc_quota_4k_step_iso(old_u, new_u, cpu_id, alloc_amount, x, y); },
            StepLabel::AllocThreadQuota4k { alloc_amount } => { alloc_thread_quota_4k_step_lr(old_u, new_u, cpu_id, alloc_amount, x, y); alloc_thread_quota_4k_step_iso(old_u, new_u, cpu_id, alloc_amount, x, y); },
            StepLabel::AllocQuota2m { alloc_amount } => { alloc_quota_2m_step_lr(old_u, new_u, cpu_id, alloc_amount, x, y); alloc_quota_2m_step_iso(old_u, new_u, cpu_id, alloc_amount, x, y); },
            StepLabel::AllocThreadQuota2m { alloc_amount } => { alloc_thread_quota_2m_step_lr(old_u, new_u, cpu_id, alloc_amount, x, y); alloc_thread_quota_2m_step_iso(old_u, new_u, cpu_id, alloc_amount, x, y); },
            StepLabel::Schedule { entry_regs, flushed_pcid } => { schedule_step_lr(old_u, new_u, cpu_id, entry_regs, flushed_pcid, x, y); schedule_step_iso(old_u, new_u, cpu_id, entry_regs, flushed_pcid, x, y); },
            StepLabel::RebalancePull => { rebalance_pull_step_lr(old_u, new_u, cpu_id, x, y); rebalance_pull_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::CpuOfflineRequest { target } => { cpu_offline_request_step_lr(old_u, new_u, cpu_id, target, x, y); cpu_offline_request_step_iso(old_u, new_u, cpu_id, target, x, y); },
            StepLabel::CpuOfflineCheckHold => { cpu_offline_check_hold_step_lr(old_u, new_u, cpu_id, x, y); cpu_offline_check_hold_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::CpuOfflineCheck { regs, flushed_default_pcid } => {
                cpu_offline_check_step_lr(old_u, new_u, cpu_id, regs, flushed_default_pcid, x, y); cpu_offline_check_step_iso(old_u, new_u, cpu_id, regs, flushed_default_pcid, x, y);
            },
            StepLabel::CpuOfflineCheckRelease => { cpu_offline_check_release_step_lr(old_u, new_u, cpu_id, x, y); cpu_offline_check_release_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::CpuOnline { target } => { cpu_online_step_lr(old_u, new_u, cpu_id, target, x, y); cpu_online_step_iso(old_u, new_u, cpu_id, target, x, y); },
            StepLabel::CpuOfflineRequestChild { target } => { cpu_offline_request_child_step_lr(old_u, new_u, cpu_id, target, x, y); cpu_offline_request_child_step_iso(old_u, new_u, cpu_id, target, x, y); },
            StepLabel::CpuOnlineChild { target } => { cpu_online_child_step_lr(old_u, new_u, cpu_id, target, x, y); cpu_online_child_step_iso(old_u, new_u, cpu_id, target, x, y); },
            StepLabel::PciAttach { bus, device, function } => { pci_attach_dma_step_lr(old_u, new_u, cpu_id, bus, device, function, x, y); pci_attach_dma_step_iso(old_u, new_u, cpu_id, bus, device, function, x, y); },
            StepLabel::NewThreadEnter { regs, endpoint_index } => { new_thread_enter_step_lr(old_u, new_u, cpu_id, regs, endpoint_index, x, y); new_thread_enter_step_iso(old_u, new_u, cpu_id, regs, endpoint_index, x, y); },
            StepLabel::NewThreadFinish => { new_thread_finish_step_lr(old_u, new_u, cpu_id, x, y); new_thread_finish_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::NewEndpointEnter { slot } => { new_endpoint_enter_step_lr(old_u, new_u, cpu_id, slot, x, y); new_endpoint_enter_step_iso(old_u, new_u, cpu_id, slot, x, y); },
            StepLabel::NewEndpointFinish => { new_endpoint_finish_step_lr(old_u, new_u, cpu_id, x, y); new_endpoint_finish_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::NewProcessEnter { range, regs, endpoint_index, with_iommu } => {
                new_process_enter_step_lr(old_u, new_u, cpu_id, range, regs, endpoint_index, with_iommu, x, y);
                new_process_enter_step_iso(old_u, new_u, cpu_id, range, regs, endpoint_index, with_iommu, x, y);
            },
            StepLabel::NewProcessPublish => { new_process_publish_step_lr(old_u, new_u, cpu_id, x, y); new_process_publish_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::NewProcessFinish => { new_process_finish_step_lr(old_u, new_u, cpu_id, x, y); new_process_finish_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::NewContainerEnter { range, funding, process_quota, transfer_cpu, regs, endpoint_index } => {
                new_container_enter_step_lr(old_u, new_u, cpu_id, range, funding, process_quota, transfer_cpu, regs, endpoint_index, x, y);
                new_container_enter_step_iso(old_u, new_u, cpu_id, range, funding, process_quota, transfer_cpu, regs, endpoint_index, x, y);
            },
            StepLabel::NewContainerPublish => { new_container_publish_step_lr(old_u, new_u, cpu_id, x, y); new_container_publish_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::NewContainerFinish => { new_container_finish_step_lr(old_u, new_u, cpu_id, x, y); new_container_finish_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::Share4kDirectory => { share_4k_directory_step_lr(old_u, new_u, cpu_id, x, y); share_4k_directory_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::Share4kLeaf => { share_4k_leaf_step_lr(old_u, new_u, cpu_id, x, y); share_4k_leaf_step_iso(old_u, new_u, cpu_id, progress, source, x, y); },
            StepLabel::IpcBlock { channel_index, waiting_state, payload, regs, flushed_default_pcid } => {
                ipc_block_step_lr(old_u, new_u, cpu_id, channel_index, waiting_state, payload, regs, flushed_default_pcid, x, y);
                ipc_block_step_iso(old_u, new_u, cpu_id, channel_index, waiting_state, payload, regs, flushed_default_pcid, x, y);
            },
            StepLabel::IpcRendezvous { channel_index, waiting_state, payload } => {
                ipc_rendezvous_step_lr(old_u, new_u, cpu_id, channel_index, waiting_state, payload, x, y);
                ipc_rendezvous_step_iso(old_u, new_u, cpu_id, channel_index, waiting_state, payload, x, y);
            },
            StepLabel::IpcCallHandoff { channel_index, regs, flushed_pcid } => {
                ipc_call_handoff_step_lr(old_u, new_u, cpu_id, channel_index, regs, flushed_pcid, x, y); ipc_call_handoff_step_iso(old_u, new_u, cpu_id, channel_index, regs, flushed_pcid, x, y);
            },
            StepLabel::IpcAcceptCall { channel_index } => { ipc_accept_call_step_lr(old_u, new_u, cpu_id, channel_index, x, y); ipc_accept_call_step_iso(old_u, new_u, cpu_id, channel_index, x, y); },
            StepLabel::IpcReplyHandoff { channel_index, regs, flushed_pcid } => {
                ipc_reply_handoff_step_lr(old_u, new_u, cpu_id, channel_index, regs, flushed_pcid, x, y); ipc_reply_handoff_step_iso(old_u, new_u, cpu_id, channel_index, regs, flushed_pcid, x, y);
            },
            StepLabel::IpcEndpointTransit { channel_index, waiting_state, payload_index } => {
                ipc_endpoint_transit_step_lr(old_u, new_u, cpu_id, channel_index, waiting_state, payload_index, x, y);
                ipc_endpoint_transit_step_iso(old_u, new_u, cpu_id, channel_index, waiting_state, payload_index, x, y);
            },
            StepLabel::IpcEndpointFinish => { ipc_endpoint_finish_step_lr(old_u, new_u, cpu_id, peer, payload, x, y); ipc_endpoint_finish_step_iso(old_u, new_u, cpu_id, peer, payload, x, y); },
            StepLabel::IpcPagesEnter { channel_index, waiting_state, range } => {
                ipc_pages_enter_step_lr(old_u, new_u, cpu_id, channel_index, waiting_state, range, x, y);
                ipc_pages_enter_step_iso(old_u, new_u, cpu_id, channel_index, waiting_state, range, x, y);
            },
            StepLabel::IpcPagesLockTables { channel_index, tables } => {
                ipc_pages_lock_tables_step_lr(old_u, new_u, cpu_id, channel_index, tables, x, y); ipc_pages_lock_tables_step_iso(old_u, new_u, cpu_id, channel_index, tables, x, y);
            },
            StepLabel::IpcPagesCheck { channel_index } => { ipc_pages_check_step_lr(old_u, new_u, cpu_id, channel_index, x, y); ipc_pages_check_step_iso(old_u, new_u, cpu_id, channel_index, x, y); },
            StepLabel::IpcPagesDowngrade => { ipc_pages_downgrade_step_lr(old_u, new_u, cpu_id, x, y); ipc_pages_downgrade_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::IpcPagesUnlockTables => { ipc_pages_unlock_tables_step_lr(old_u, new_u, cpu_id, x, y); ipc_pages_unlock_tables_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::IpcPagesFinish { channel_index } => { ipc_pages_finish_step_lr(old_u, new_u, cpu_id, channel_index, x, y); ipc_pages_finish_step_iso(old_u, new_u, cpu_id, channel_index, x, y); },
            StepLabel::KillContainerEnter { child_index } => {
                kill_container_enter_step_lr(old_u, new_u, cpu_id, child_index, x, y); kill_container_enter_step_iso(old_u, new_u, cpu_id, child_index, x, y);
            },
            StepLabel::KillContainerMarkChild => { kill_container_mark_child_step_lr(old_u, new_u, cpu_id, x, y); kill_container_mark_child_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillContainerMarkRoot => { kill_container_mark_root_step_lr(old_u, new_u, cpu_id, x, y); kill_container_mark_root_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillContainerRetireRoot => { kill_container_retire_root_step_lr(old_u, new_u, cpu_id, x, y); kill_container_retire_root_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillContainerCpus => { kill_container_cpus_step_lr(old_u, new_u, cpu_id, x, y); kill_container_cpus_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillContainerMoveCpu => { kill_container_move_cpu_step_lr(old_u, new_u, cpu_id, x, y); kill_container_move_cpu_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillContainerPages => { kill_container_pages_step_lr(old_u, new_u, cpu_id, x, y); kill_container_pages_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillContainerMovePage { size } => {
                kill_container_move_page_step_lr(old_u, new_u, cpu_id, size, x, y); kill_container_move_page_step_iso(old_u, new_u, cpu_id, size, x, y);
            },
            StepLabel::KillContainerRetireStage => { kill_container_retire_stage_step_lr(old_u, new_u, cpu_id, x, y); kill_container_retire_stage_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillContainerRetire => { kill_container_retire_step_lr(old_u, new_u, cpu_id, x, y); kill_container_retire_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillContainerFinish => { kill_container_finish_step_lr(old_u, new_u, cpu_id, x, y); kill_container_finish_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillProcessEnter { child_index } => {
                kill_process_enter_step_lr(old_u, new_u, cpu_id, child_index, x, y); kill_process_enter_step_iso(old_u, new_u, cpu_id, child_index, x, y);
            },
            StepLabel::KillProcessMarkChild => { kill_process_mark_child_step_lr(old_u, new_u, cpu_id, x, y); kill_process_mark_child_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillProcessDangling => { kill_process_dangling_step_lr(old_u, new_u, cpu_id, x, y); kill_process_dangling_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillProcessMarkThread => { kill_process_mark_thread_step_lr(old_u, new_u, cpu_id, x, y); kill_process_mark_thread_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillProcessDequeueScheduled => { kill_process_dequeue_scheduled_step_lr(old_u, new_u, cpu_id, x, y); kill_process_dequeue_scheduled_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillProcessDequeueEndpoint => { kill_process_dequeue_endpoint_step_lr(old_u, new_u, cpu_id, x, y); kill_process_dequeue_endpoint_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillProcessCpuToIdle => { kill_process_cpu_to_idle_step_lr(old_u, new_u, cpu_id, x, y); kill_process_cpu_to_idle_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillProcessUnlink => { kill_process_unlink_step_lr(old_u, new_u, cpu_id, x, y); kill_process_unlink_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillProcessDescriptorDropped => { kill_process_descriptor_dropped_step_lr(old_u, new_u, cpu_id, x, y); kill_process_descriptor_dropped_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillProcessCallerWoken => { kill_process_caller_woken_step_lr(old_u, new_u, cpu_id, x, y); kill_process_caller_woken_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillProcessCallerTakenOver => { kill_process_caller_taken_over_step_lr(old_u, new_u, cpu_id, x, y); kill_process_caller_taken_over_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillProcessDanglingReclaimed => { kill_process_dangling_reclaimed_step_lr(old_u, new_u, cpu_id, x, y); kill_process_dangling_reclaimed_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillProcessEndpointReleased => { kill_process_endpoint_released_step_lr(old_u, new_u, cpu_id, x, y); kill_process_endpoint_released_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillProcessReassignFunctions => { kill_process_reassign_functions_step_lr(old_u, new_u, cpu_id, x, y); kill_process_reassign_functions_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillProcessLockTable => { kill_process_lock_table_step_lr(old_u, new_u, cpu_id, x, y); kill_process_lock_table_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillProcessLeaf => { kill_process_leaf_step_lr(old_u, new_u, cpu_id, x, y); kill_process_leaf_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillProcessTlbCleared => { kill_process_tlb_cleared_step_lr(old_u, new_u, cpu_id, x, y); kill_process_tlb_cleared_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillProcessFlushed => { kill_process_flushed_step_lr(old_u, new_u, cpu_id, x, y); kill_process_flushed_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillProcessIommuLeaf => { kill_process_iommu_leaf_step_lr(old_u, new_u, cpu_id, x, y); kill_process_iommu_leaf_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillProcessPagetableWindowsChanged => { kill_process_pagetable_windows_changed_step_lr(old_u, new_u, cpu_id, x, y); kill_process_pagetable_windows_changed_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillProcessRefund => { kill_process_refund_step_lr(old_u, new_u, cpu_id, x, y); kill_process_refund_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillProcessQuota => { kill_process_quota_step_lr(old_u, new_u, cpu_id, x, y); kill_process_quota_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillProcessUnlockTable => { kill_process_unlock_table_step_lr(old_u, new_u, cpu_id, x, y); kill_process_unlock_table_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillProcessZombify => { kill_process_zombify_step_lr(old_u, new_u, cpu_id, x, y); kill_process_zombify_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillProcessZombieRetire => { kill_process_zombie_retire_step_lr(old_u, new_u, cpu_id, x, y); kill_process_zombie_retire_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillProcessRetire => { kill_process_retire_step_lr(old_u, new_u, cpu_id, x, y); kill_process_retire_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::KillProcessFinish => { kill_process_finish_step_lr(old_u, new_u, cpu_id, x, y); kill_process_finish_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::ThreadExitEnter => { thread_exit_enter_step_lr(old_u, new_u, cpu_id, x, y); thread_exit_enter_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::ThreadExitDescriptorDropped => { thread_exit_descriptor_dropped_step_lr(old_u, new_u, cpu_id, x, y); thread_exit_descriptor_dropped_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::ThreadExitCallerWoken => { thread_exit_caller_woken_step_lr(old_u, new_u, cpu_id, x, y); thread_exit_caller_woken_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::ThreadExitCallerTakenOver => { thread_exit_caller_taken_over_step_lr(old_u, new_u, cpu_id, x, y); thread_exit_caller_taken_over_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::ThreadExitDanglingReclaimed => { thread_exit_dangling_reclaimed_step_lr(old_u, new_u, cpu_id, x, y); thread_exit_dangling_reclaimed_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::ThreadExitEndpointReleased => { thread_exit_endpoint_released_step_lr(old_u, new_u, cpu_id, x, y); thread_exit_endpoint_released_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::ThreadExitDrop => { thread_exit_drop_step_lr(old_u, new_u, cpu_id, x, y); thread_exit_drop_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::ThreadExitRelease => { thread_exit_release_step_lr(old_u, new_u, cpu_id, x, y); thread_exit_release_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::ThreadExitLockTable => { thread_exit_lock_table_step_lr(old_u, new_u, cpu_id, x, y); thread_exit_lock_table_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::ThreadExitLeaf => { thread_exit_leaf_step_lr(old_u, new_u, cpu_id, x, y); thread_exit_leaf_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::ThreadExitTlbCleared => { thread_exit_tlb_cleared_step_lr(old_u, new_u, cpu_id, x, y); thread_exit_tlb_cleared_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::ThreadExitFlushed => { thread_exit_flushed_step_lr(old_u, new_u, cpu_id, x, y); thread_exit_flushed_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::ThreadExitIommuLeaf => { thread_exit_iommu_leaf_step_lr(old_u, new_u, cpu_id, x, y); thread_exit_iommu_leaf_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::ThreadExitPagetableWindowsChanged => { thread_exit_pagetable_windows_changed_step_lr(old_u, new_u, cpu_id, x, y); thread_exit_pagetable_windows_changed_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::ThreadExitRefund => { thread_exit_refund_step_lr(old_u, new_u, cpu_id, x, y); thread_exit_refund_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::ThreadExitQuota => { thread_exit_quota_step_lr(old_u, new_u, cpu_id, x, y); thread_exit_quota_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::ThreadExitUnlockTable => { thread_exit_unlock_table_step_lr(old_u, new_u, cpu_id, x, y); thread_exit_unlock_table_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::ThreadExitFinish => { thread_exit_finish_step_lr(old_u, new_u, cpu_id, x, y); thread_exit_finish_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::TrapEnter => { trap_enter_step_lr(old_u, new_u, cpu_id, x, y); trap_enter_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::TrapReturn => { trap_return_step_lr(old_u, new_u, cpu_id, x, y); trap_return_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::TrapDivert => { trap_divert_step_lr(old_u, new_u, cpu_id, x, y); trap_divert_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::CpuTlbFilled { cpu_id: filled_cpu, pcid, added } => { cpu_tlb_filled_step_lr(old_u, new_u, filled_cpu, pcid, added, y); cpu_tlb_filled_step_iso(old_u, new_u, filled_cpu, pcid, added, x, y); },
            StepLabel::IommuTlbFilled { did, added } => { iommu_tlb_filled_step_lr(old_u, new_u, did, added, y); iommu_tlb_filled_step_iso(old_u, new_u, did, added, x, y); },
            StepLabel::IommuContextCacheFilled => { iommu_context_cache_filled_step_lr(old_u, new_u, y); iommu_context_cache_filled_step_iso(old_u, new_u, x, y); },
        }
        if x != a { isolated_symmetric(new_u, b, a); }
    }
}
} // verus!
