//! A kernel step keeps the PCID of every process that lives before and after it, proved per label family from the step
//! specifications; and a hardware step changes no process, keeps every cpu's current process, and leaves no cpu inside a
//! kernel step or off that was not.
use vstd::prelude::*;
use crate::*;
use veriflat_syscall_merge_2m::syscall_merge_2m::syscall_merge_2m_spec::*;
use veriflat_syscall_split_2m::syscall_split_2m::syscall_split_2m_spec::*;
use veriflat_noninterference::{ni_alloc_quota::*, ni_cpu_hotplug::*, ni_ipc::*, ni_mmap_4k::*, ni_mmap_2m::*, ni_unmap_2m::*, ni_mmap_1g::*, ni_unmap_1g::*, ni_new_container::*, ni_new_endpoint::*,
    ni_new_process::*, ni_new_thread::*, ni_pci::*, ni_pci_bar::*, ni_rebalance::*, ni_schedule::*, ni_share_4k::*, ni_unmap_4k::*, ni_iommu_map_4k::*, ni_iommu_unmap_4k::*, ni_kill_container::*,
    ni_kill_process::*, ni_thread_exit::*, ni_trap::*, ni_env::*};
use veriflat_map_4k::*;
use veriflat_syscall_alloc_quota::syscall_alloc_quota::{syscall_alloc_quota_spec::*, syscall_alloc_quota_1g_spec::*};
use veriflat_syscall_cpu_hotplug::syscall_cpu_hotplug::{syscall_cpu_offline_check_spec::*, syscall_cpu_hotplug_spec::*};
use veriflat_syscall_iommu_map_4k::syscall_iommu_map_4k::syscall_iommu_map_4k_spec::*;
use veriflat_syscall_iommu_unmap_4k::syscall_iommu_unmap_4k::syscall_iommu_unmap_4k_spec::*;
use veriflat_syscall_kill_process::{syscall_kill_container::syscall_kill_container_spec::*, syscall_kill_process::syscall_kill_process_spec::*};
use veriflat_syscall_ipc::syscall_ipc::{syscall_ipc_call_spec::*, syscall_ipc_spec::*};
use veriflat_syscall_mmap_4k::syscall_mmap_4k::syscall_mmap_4k_spec::*;
use veriflat_syscall_mmap_2m::syscall_mmap_2m::syscall_mmap_2m_spec::*;
use veriflat_syscall_unmap_2m::syscall_unmap_2m::syscall_unmap_2m_spec::*;
use veriflat_map_4k::map_4k::mmap_1g_install_directory_spec::*;
use veriflat_syscall_mmap_1g::syscall_mmap_1g::syscall_mmap_1g_spec::*;
use veriflat_syscall_unmap_1g::syscall_unmap_1g::syscall_unmap_1g_spec::*;
use veriflat_syscall_new_container::syscall_new_container::syscall_new_container_spec::*;
use veriflat_syscall_new_process::syscall_new_process::syscall_new_process_spec::*;
use veriflat_syscall_new_thread::{syscall_new_endpoint::syscall_new_endpoint_spec::*, syscall_new_thread::syscall_new_thread_spec::*};
use veriflat_syscall_pci::syscall_pci::syscall_pci_spec::*;
use veriflat_syscall_pci_bar::syscall_pci_bar::syscall_pci_bar_spec::*;
use veriflat_syscall_schedule::{rebalance_pull::rebalance_pull_spec::*, syscall_schedule::syscall_schedule_spec::*};
use veriflat_syscall_thread_exit::syscall_thread_exit::syscall_thread_exit_spec::*;
use veriflat_syscall_unmap_4k::syscall_unmap_4k::syscall_unmap_4k_spec::*;

verus! {
/// Every process in both `u` and `u2` has the same PCID in both.
pub open spec fn process_pcids_kept(u: KernelU, u2: KernelU) -> bool {
    forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] u.process_map.dom().contains(p) && u2.process_map.dom().contains(p) ==> u2.process_map[p].pcid == u.process_map[p].pcid
}

/// A hardware step of cpu `d` changes no process and no current process, moves no cpu into a kernel step or off, and
/// changes the TLBs of no cpu except by the fill it names.
pub proof fn hardware_step_implies_cpus_kept(l: StepLabel, u: KernelU, u2: KernelU, d: CpuId)
    requires hardware_label(l), labeled_step(l, u, u2, d),
    ensures
        u2.process_map == u.process_map,
        u2.cpu_array.len() == u.cpu_array.len(),
        forall|c: int| #![trigger u2.cpu_array[c]] 0 <= c < u.cpu_array.len() ==> u2.cpu_array[c].current_process == u.cpu_array[c].current_process,
        forall|c: int| #![trigger u2.cpu_array[c]] 0 <= c < u.cpu_array.len() && (u2.cpu_array[c].op is InStep || u2.cpu_array[c].op is Off)
            ==> u2.cpu_array[c].op == u.cpu_array[c].op,
        !(l is CpuTlbFilled) ==> u2.cpu_tlb == u.cpu_tlb,
        l is CpuTlbFilled ==> u2.cpu_tlb == u.cpu_tlb.insert((l->CpuTlbFilled_cpu_id, l->CpuTlbFilled_pcid),
            single_tlb_union(u.cpu_tlb[(l->CpuTlbFilled_cpu_id, l->CpuTlbFilled_pcid)], l->CpuTlbFilled_added)),
{
    match l {
        StepLabel::TrapEnter => { reveal(kernel_u_trap_enter_step); },
        StepLabel::TrapReturn => { reveal(kernel_u_trap_return_step); },
        StepLabel::TrapDivert => { reveal(kernel_u_trap_divert_step); },
        StepLabel::RegsChanged { .. } => { reveal(kernel_u_regs_changed_step); },
        StepLabel::TrapReturnValuesWritten { .. } => { reveal(kernel_u_trap_return_values_written_step); },
        StepLabel::CpuTlbFilled { .. } => { reveal(kernel_u_cpu_tlb_filled_step); },
        StepLabel::IommuTlbFilled { .. } => { reveal(kernel_u_iommu_tlb_filled_step); },
        StepLabel::IommuContextCacheFilled => { reveal(kernel_u_iommu_context_cache_filled_step); },
        _ => {},
    }
}

/// A killed-thread reclaim step changes no process.
pub proof fn killed_thread_reclaim_implies_process_map_kept(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_killed_thread_reclaim_step(u, u2, d),
    ensures u2.process_map == u.process_map,
{
    reveal(kernel_u_killed_descriptor_dropped); reveal(kernel_u_killed_caller_woken); reveal(kernel_u_killed_caller_taken_over); reveal(kernel_u_dangling_thread_reclaimed);
    reveal(kernel_u_killed_endpoint_released); reveal(kernel_u_endpoint_released);
    if kernel_u_killed_descriptor_dropped(u, u2, d) {
        let changed = u.thread_map.dom().filter(|t: RwLockThreadPtr| u2.thread_map[t] != u.thread_map[t]);
        let t = changed.choose();
        assert(changed.contains(t));
        let thread = u.thread_map[t];
        let dropped = Set::<int>::range(0, MAX_NUM_ENDPOINT_DESCRIPTORS as int).filter(|j: int| u2.thread_map[t].endpoint_descriptors[j] != thread.endpoint_descriptors[j]);
        assert(dropped.contains(dropped.choose()));
    } else if kernel_u_killed_endpoint_released(u, u2, d) {
        let changed = u.thread_map.dom().filter(|t: RwLockThreadPtr| u2.thread_map[t] != u.thread_map[t]);
        let t = changed.choose();
        assert(changed.contains(t));
        let thread = u.thread_map[t];
        let dropped = Set::<int>::range(0, MAX_NUM_ENDPOINT_DESCRIPTORS as int).filter(|j: int| u2.thread_map[t].endpoint_descriptors[j] != thread.endpoint_descriptors[j]);
        assert(dropped.contains(dropped.choose()));
    } else if kernel_u_killed_caller_woken(u, u2, d) {
        let woken = u.thread_map.dom().filter(|t: RwLockThreadPtr| u.thread_map[t].state is WAITING_REPLY && u2.thread_map[t].state is SCHEDULED);
        assert(woken.contains(woken.choose()));
    } else if kernel_u_killed_caller_taken_over(u, u2, d) {
        let taken = u.thread_map.dom().filter(|t: RwLockThreadPtr| u.thread_map[t].state is DANGLING && u2.thread_map[t].state is KILLED);
        assert(taken.contains(taken.choose()));
    } else {
        let removed = u.thread_map.dom().difference(u2.thread_map.dom());
        assert(removed.contains(removed.choose()));
    }
}

/// The labels of the `map_4k` family.
pub open spec fn map_4k_label(l: StepLabel) -> bool {
    ||| l is Mmap4kHold || l is Mmap4kEnter || l is Mmap4kDirectory || l is Mmap4kDowngrade || l is Mmap4kLeaf || l is Mmap4kExit || l is Mmap4kRelease || l is Unmap4kEnter || l is Unmap4kLeaf
    ||| l is Unmap4kTlbFlush || l is Unmap4kTlbVaFlush || l is Unmap4kFlushed || l is Unmap4kRefund || l is Unmap4kExit
}

/// A step of the `map_4k` family keeps the PCID of every process alive before and after it.
pub proof fn map_4k_step_implies_process_pcids_kept(l: StepLabel, u: KernelU, u2: KernelU, d: CpuId)
    requires map_4k_label(l), labeled_step(l, u, u2, d),
    ensures process_pcids_kept(u, u2),
{
    match l {
        StepLabel::Mmap4kHold { .. } => { reveal(mmap_4k_hold_step); },
        StepLabel::Mmap4kEnter { .. } => { reveal(mmap_4k_enter_step); },
        StepLabel::Mmap4kDirectory => { reveal(mmap_4k_directory_step); },
        StepLabel::Mmap4kDowngrade => { reveal(mmap_4k_downgrade_step); },
        StepLabel::Mmap4kLeaf => { reveal(mmap_4k_leaf_step); },
        StepLabel::Mmap4kExit => { reveal(mmap_4k_exit_step); },
        StepLabel::Mmap4kRelease => { reveal(mmap_4k_release_step); },
        StepLabel::Unmap4kEnter { .. } => { reveal(unmap_4k_enter_step); },
        StepLabel::Unmap4kLeaf => { reveal(unmap_4k_leaf_step); },
        StepLabel::Unmap4kTlbFlush => { reveal(kernel_u_cpu_tlb_cleared); reveal(unmap_4k_tlb_flush_step); },
        StepLabel::Unmap4kTlbVaFlush => { reveal(kernel_u_cpu_tlb_va_flushed); reveal(unmap_4k_tlb_va_flush_step); },
        StepLabel::Unmap4kFlushed => { reveal(unmap_4k_flushed_step); },
        StepLabel::Unmap4kRefund => { reveal(kernel_u_container_quota_4k_increased); reveal(unmap_4k_refund_step); },
        StepLabel::Unmap4kExit => { reveal(unmap_4k_exit_step); },
        _ => {},
    }
}

/// The labels of the `map_2m` family.
pub open spec fn map_2m_label(l: StepLabel) -> bool {
    ||| l is Mmap2mHold || l is Mmap2mEnter || l is Mmap2mDirectory || l is Mmap2mDowngrade || l is Mmap2mFlush || l is Mmap2mFlushed || l is Mmap2mL1Reclaim || l is Mmap2mLeaf || l is Mmap2mExit
    ||| l is Mmap2mRelease || l is Unmap2mEnter || l is Unmap2mLeaf || l is Unmap2mTlbFlush || l is Unmap2mTlbVaFlush || l is Unmap2mFlushed || l is Unmap2mRefund || l is Unmap2mExit
}

/// A step of the `map_2m` family keeps the PCID of every process alive before and after it.
pub proof fn map_2m_step_implies_process_pcids_kept(l: StepLabel, u: KernelU, u2: KernelU, d: CpuId)
    requires map_2m_label(l), labeled_step(l, u, u2, d),
    ensures process_pcids_kept(u, u2),
{
    match l {
        StepLabel::Mmap2mHold { .. } => { reveal(mmap_4k_hold_step); },
        StepLabel::Mmap2mEnter { .. } => { reveal(mmap_2m_enter_step); },
        StepLabel::Mmap2mDirectory => { reveal(mmap_2m_directory_step); },
        StepLabel::Mmap2mDowngrade => { reveal(mmap_2m_downgrade_step); },
        StepLabel::Mmap2mFlush => { reveal(kernel_u_cpu_tlb_cleared); reveal(unmap_4k_tlb_flush_step); },
        StepLabel::Mmap2mFlushed => { reveal(mmap_2m_flushed_step); },
        StepLabel::Mmap2mL1Reclaim => { reveal(kernel_u_container_quota_4k_increased); },
        StepLabel::Mmap2mLeaf => { reveal(mmap_2m_leaf_step); },
        StepLabel::Mmap2mExit => { reveal(mmap_2m_exit_step); },
        StepLabel::Mmap2mRelease => { reveal(mmap_4k_release_step); },
        StepLabel::Unmap2mEnter { .. } => { reveal(unmap_2m_enter_step); },
        StepLabel::Unmap2mLeaf => { reveal(unmap_2m_leaf_step); },
        StepLabel::Unmap2mTlbFlush => { reveal(kernel_u_cpu_tlb_cleared); reveal(unmap_4k_tlb_flush_step); },
        StepLabel::Unmap2mTlbVaFlush => { reveal(kernel_u_cpu_tlb_va_flushed); reveal(unmap_4k_tlb_va_flush_step); },
        StepLabel::Unmap2mFlushed => { reveal(unmap_2m_flushed_step); },
        StepLabel::Unmap2mRefund => { reveal(kernel_u_container_quota_2m_increased); reveal(unmap_2m_refund_step); },
        StepLabel::Unmap2mExit => { reveal(unmap_2m_exit_step); },
        _ => {},
    }
}

/// The labels of the `map_1g` family.
pub open spec fn map_1g_label(l: StepLabel) -> bool {
    ||| l is Mmap1gEnter || l is Mmap1gHide || l is Mmap1gFlush || l is Mmap1gFlushed || l is Mmap1gReclaim || l is Mmap1gDirectory || l is Mmap1gLeaf || l is Mmap1gExit || l is Unmap1gEnter
    ||| l is Unmap1gLeaf || l is Unmap1gTlbFlush || l is Unmap1gFlushed || l is Unmap1gRefund || l is Unmap1gExit
}

/// A step of the `map_1g` family keeps the PCID of every process alive before and after it.
pub proof fn map_1g_step_implies_process_pcids_kept(l: StepLabel, u: KernelU, u2: KernelU, d: CpuId)
    requires map_1g_label(l), labeled_step(l, u, u2, d),
    ensures process_pcids_kept(u, u2),
{
    match l {
        StepLabel::Mmap1gEnter { .. } => { reveal(mmap_1g_enter_step); },
        StepLabel::Mmap1gHide => { reveal(mmap_1g_hide_step); },
        StepLabel::Mmap1gFlush => { reveal(kernel_u_cpu_tlb_cleared); reveal(unmap_4k_tlb_flush_step); },
        StepLabel::Mmap1gFlushed => { reveal(mmap_1g_flushed_step); },
        StepLabel::Mmap1gReclaim => { reveal(kernel_u_container_quota_4k_increased); },
        StepLabel::Mmap1gDirectory => { reveal(mmap_1g_directory_step); },
        StepLabel::Mmap1gLeaf => { reveal(mmap_1g_leaf_step); },
        StepLabel::Mmap1gExit => { reveal(mmap_1g_exit_step); },
        StepLabel::Unmap1gEnter { .. } => { reveal(unmap_1g_enter_step); },
        StepLabel::Unmap1gLeaf => { reveal(unmap_1g_leaf_step); },
        StepLabel::Unmap1gTlbFlush => { reveal(kernel_u_cpu_tlb_cleared); reveal(unmap_4k_tlb_flush_step); },
        StepLabel::Unmap1gFlushed => { reveal(unmap_1g_flushed_step); },
        StepLabel::Unmap1gRefund => { reveal(kernel_u_container_quota_1g_increased); reveal(unmap_1g_refund_step); },
        StepLabel::Unmap1gExit => { reveal(unmap_1g_exit_step); },
        _ => {},
    }
}

/// The labels of the `iommu` family.
pub open spec fn iommu_label(l: StepLabel) -> bool {
    ||| l is IommuMap4kEnter || l is IommuMap4kDirectory || l is IommuMap4kLeaf || l is IommuMap4kExit || l is IommuUnmap4kEnter || l is IommuUnmap4kLeaf || l is IommuUnmap4kFlush || l is IommuUnmap4kRefund
    ||| l is IommuUnmap4kExit
}

/// A step of the `iommu` family keeps the PCID of every process alive before and after it.
pub proof fn iommu_step_implies_process_pcids_kept(l: StepLabel, u: KernelU, u2: KernelU, d: CpuId)
    requires iommu_label(l), labeled_step(l, u, u2, d),
    ensures process_pcids_kept(u, u2),
{
    match l {
        StepLabel::IommuMap4kEnter { .. } => { reveal(iommu_map_4k_enter_step); },
        StepLabel::IommuMap4kDirectory => { reveal(iommu_map_4k_directory_step); },
        StepLabel::IommuMap4kLeaf => { reveal(iommu_map_4k_leaf_step); },
        StepLabel::IommuMap4kExit => { reveal(iommu_map_4k_exit_step); },
        StepLabel::IommuUnmap4kEnter { .. } => { reveal(iommu_unmap_4k_enter_step); },
        StepLabel::IommuUnmap4kLeaf => { reveal(iommu_unmap_4k_leaf_step); },
        StepLabel::IommuUnmap4kFlush => { reveal(iommu_unmap_4k_flush_step); },
        StepLabel::IommuUnmap4kRefund => { reveal(iommu_unmap_4k_refund_step); reveal(kernel_u_container_quota_4k_increased); },
        StepLabel::IommuUnmap4kExit => { reveal(iommu_unmap_4k_exit_step); },
        _ => {},
    }
}

/// The labels of the `quota_cpu` family.
pub open spec fn quota_cpu_label(l: StepLabel) -> bool {
    ||| l is AllocQuota4k || l is AllocThreadQuota4k || l is AllocQuota2m || l is AllocThreadQuota2m || l is AllocQuota1g || l is AllocThreadQuota1g || l is Schedule || l is Merge2m || l is Split2m
    ||| l is RebalancePull || l is OrphanPull || l is CpuOfflineRequest || l is CpuOfflineCheckHold || l is CpuOfflineCheck || l is CpuOfflineCheckRelease || l is CpuOnline || l is CpuOfflineRequestChild
    ||| l is CpuOnlineChild || l is PciAttach || l is PciClaim
}

/// A step of the `quota_cpu` family keeps the PCID of every process alive before and after it.
pub proof fn quota_cpu_step_implies_process_pcids_kept(l: StepLabel, u: KernelU, u2: KernelU, d: CpuId)
    requires quota_cpu_label(l), labeled_step(l, u, u2, d),
    ensures process_pcids_kept(u, u2),
{
    match l {
        StepLabel::AllocQuota4k { .. } => { reveal(kernel_u_only_process_quota_4k_changed); },
        StepLabel::AllocThreadQuota4k { .. } => { reveal(kernel_u_only_process2thread_quota_4k_changed); },
        StepLabel::AllocQuota2m { .. } => { reveal(kernel_u_only_process_quota_2m_changed); },
        StepLabel::AllocThreadQuota2m { .. } => { reveal(kernel_u_only_process2thread_quota_2m_changed); },
        StepLabel::AllocQuota1g { .. } => { reveal(kernel_u_only_process_quota_1g_changed); },
        StepLabel::AllocThreadQuota1g { .. } => { reveal(kernel_u_only_process2thread_quota_1g_changed); },
        StepLabel::Schedule { .. } => { reveal(kernel_u_context_switch_changed); },
        StepLabel::Merge2m => {  },
        StepLabel::Split2m => {  },
        StepLabel::RebalancePull => { reveal(kernel_u_rebalance_pull_changed); },
        StepLabel::OrphanPull { .. } => { reveal(kernel_u_orphan_pull_changed); },
        StepLabel::CpuOfflineRequest { .. } => { reveal(kernel_u_cpu_offline_request_changed); },
        StepLabel::CpuOfflineCheckHold => { reveal(cpu_offline_check_hold_step); },
        StepLabel::CpuOfflineCheck { .. } => { reveal(kernel_u_cpu_went_off_changed); },
        StepLabel::CpuOfflineCheckRelease => { reveal(cpu_offline_check_release_step); },
        StepLabel::CpuOnline { .. } => { reveal(kernel_u_cpu_online_changed); },
        StepLabel::CpuOfflineRequestChild { .. } => { reveal(kernel_u_cpu_offline_request_changed); },
        StepLabel::CpuOnlineChild { .. } => { reveal(kernel_u_cpu_online_changed); },
        StepLabel::PciAttach { .. } => { reveal(kernel_u_pci_attach_changed); },
        StepLabel::PciClaim { .. } => { reveal(kernel_u_pci_claim_changed); },
        _ => {},
    }
}

/// The labels of the `pci_bar` family.
pub open spec fn pci_bar_label(l: StepLabel) -> bool {
    ||| l is MapPciBar4kEnter || l is MapPciBar4kDirectory || l is MapPciBar4kExit || l is MapPciBar2mEnter || l is MapPciBar2mDirectory || l is MapPciBar2mFlush || l is MapPciBar2mFlushed
    ||| l is MapPciBar2mL1Reclaim || l is MapPciBar2mExit || l is UnmapPciBar4kHide || l is UnmapPciBar4kFlush || l is UnmapPciBar4kFlushed || l is UnmapPciBar4kExit || l is UnmapPciBar2mHide
    ||| l is UnmapPciBar2mFlush || l is UnmapPciBar2mFlushed || l is UnmapPciBar2mExit
}

/// A step of the `pci_bar` family keeps the PCID of every process alive before and after it.
pub proof fn pci_bar_step_implies_process_pcids_kept(l: StepLabel, u: KernelU, u2: KernelU, d: CpuId)
    requires pci_bar_label(l), labeled_step(l, u, u2, d),
    ensures process_pcids_kept(u, u2),
{
    match l {
        StepLabel::MapPciBar4kEnter { .. } => { reveal(map_pci_bar_4k_enter_step); },
        StepLabel::MapPciBar4kDirectory => { reveal(map_pci_bar_4k_directory_step); },
        StepLabel::MapPciBar4kExit { .. } => { reveal(map_pci_bar_4k_exit_step); },
        StepLabel::MapPciBar2mEnter { .. } => { reveal(map_pci_bar_2m_enter_step); },
        StepLabel::MapPciBar2mDirectory => { reveal(map_pci_bar_2m_directory_step); },
        StepLabel::MapPciBar2mFlush => { reveal(kernel_u_cpu_tlb_cleared); reveal(unmap_4k_tlb_flush_step); },
        StepLabel::MapPciBar2mFlushed => { reveal(map_pci_bar_2m_flushed_step); },
        StepLabel::MapPciBar2mL1Reclaim => { reveal(kernel_u_container_quota_4k_increased); },
        StepLabel::MapPciBar2mExit { .. } => { reveal(map_pci_bar_2m_exit_step); },
        StepLabel::UnmapPciBar4kHide { .. } => { reveal(unmap_pci_bar_4k_hide_step); },
        StepLabel::UnmapPciBar4kFlush => { reveal(kernel_u_cpu_tlb_cleared); reveal(unmap_4k_tlb_flush_step); },
        StepLabel::UnmapPciBar4kFlushed => { reveal(unmap_pci_bar_4k_flushed_step); },
        StepLabel::UnmapPciBar4kExit { .. } => { reveal(unmap_pci_bar_4k_exit_step); },
        StepLabel::UnmapPciBar2mHide { .. } => { reveal(unmap_pci_bar_2m_hide_step); },
        StepLabel::UnmapPciBar2mFlush => { reveal(kernel_u_cpu_tlb_cleared); reveal(unmap_4k_tlb_flush_step); },
        StepLabel::UnmapPciBar2mFlushed => { reveal(unmap_pci_bar_2m_flushed_step); },
        StepLabel::UnmapPciBar2mExit { .. } => { reveal(unmap_pci_bar_2m_exit_step); },
        _ => {},
    }
}

/// The labels of the `create` family.
pub open spec fn create_label(l: StepLabel) -> bool {
    ||| l is NewThreadEnter || l is NewThreadFinish || l is NewEndpointEnter || l is NewEndpointFinish || l is NewProcessEnter || l is NewProcessPublish || l is NewProcessFinish || l is NewContainerEnter
    ||| l is NewContainerPublish || l is NewContainerFinish || l is Share4kDirectory || l is Share4kLeaf
}

/// A step of the `create` family keeps the PCID of every process alive before and after it.
pub proof fn create_step_implies_process_pcids_kept(l: StepLabel, u: KernelU, u2: KernelU, d: CpuId)
    requires create_label(l), labeled_step(l, u, u2, d),
    ensures process_pcids_kept(u, u2),
{
    match l {
        StepLabel::NewThreadEnter { .. } => { reveal(new_thread_enter_step); reveal(new_thread_enter_step_pre); },
        StepLabel::NewThreadFinish => { reveal(kernel_u_new_thread_changed); reveal(new_thread_finish_step); reveal(new_thread_finish_step_pre); },
        StepLabel::NewEndpointEnter { .. } => { reveal(new_endpoint_enter_step); reveal(new_endpoint_enter_step_pre); },
        StepLabel::NewEndpointFinish => { reveal(kernel_u_new_endpoint_changed); reveal(new_endpoint_finish_step); reveal(new_endpoint_finish_step_pre); },
        StepLabel::NewProcessEnter { .. } => { reveal(new_process_enter_step); reveal(new_process_enter_step_pre); },
        StepLabel::NewProcessPublish => { reveal(new_process_publish_step); reveal(new_process_publish_step_pre); },
        StepLabel::NewProcessFinish => { reveal(kernel_u_new_thread_changed); reveal(new_process_finish_step); reveal(new_process_finish_step_pre); },
        StepLabel::NewContainerEnter { .. } => { reveal(new_container_enter_step); reveal(new_container_enter_step_pre); },
        StepLabel::NewContainerPublish => { reveal(kernel_u_container_root_created); reveal(new_container_publish_step); reveal(new_container_publish_step_pre); },
        StepLabel::NewContainerFinish => { reveal(kernel_u_new_thread_changed); reveal(new_container_finish_step); reveal(new_container_finish_step_pre); },
        StepLabel::Share4kDirectory => { reveal(share_4k_directory_at); reveal(share_4k_directory_step); reveal(share_4k_directory_step_pre); },
        StepLabel::Share4kLeaf => { reveal(share_4k_leaf_at); reveal(share_4k_leaf_step); reveal(share_4k_leaf_step_pre); },
        _ => {},
    }
}

/// The labels of the `ipc` family.
pub open spec fn ipc_label(l: StepLabel) -> bool {
    ||| l is IpcBlock || l is IpcRendezvous || l is IpcCallHandoff || l is IpcAcceptCall || l is IpcReplyHandoff || l is IpcReplyDanglingCallerTakenOver || l is IpcReplyDanglingReclaimed
    ||| l is IpcReplyDanglingCallerReleased || l is IpcEndpointTransit || l is IpcEndpointFinish || l is IpcPagesEnter || l is IpcPagesLockTables || l is IpcPagesCheck || l is IpcPagesDowngrade
    ||| l is IpcPagesUnlockTables || l is IpcPagesFinish
}

/// A step of the `ipc` family keeps the PCID of every process alive before and after it.
pub proof fn ipc_step_implies_process_pcids_kept(l: StepLabel, u: KernelU, u2: KernelU, d: CpuId)
    requires ipc_label(l), labeled_step(l, u, u2, d),
    ensures process_pcids_kept(u, u2),
{
    match l {
        StepLabel::IpcBlock { .. } => { reveal(kernel_u_ipc_block_changed); },
        StepLabel::IpcRendezvous { .. } => { reveal(kernel_u_ipc_rendezvous_changed); },
        StepLabel::IpcCallHandoff { .. } => { reveal(kernel_u_ipc_call_handoff_changed); },
        StepLabel::IpcAcceptCall { .. } => { reveal(kernel_u_ipc_accept_call_changed); },
        StepLabel::IpcReplyHandoff { .. } => { reveal(kernel_u_ipc_reply_handoff_changed); },
        StepLabel::IpcReplyDanglingCallerTakenOver { .. } => { reveal(ipc_reply_dangling_caller_taken_over_step); },
        StepLabel::IpcReplyDanglingReclaimed => { killed_thread_reclaim_implies_process_map_kept(u, u2, d); },
        StepLabel::IpcReplyDanglingCallerReleased => { reveal(ipc_reply_dangling_caller_released_step); },
        StepLabel::IpcEndpointTransit { .. } => { reveal(ipc_endpoint_transit_step); },
        StepLabel::IpcEndpointFinish => { reveal(ipc_endpoint_finish_step); },
        StepLabel::IpcPagesEnter { .. } => { reveal(ipc_pages_enter_step); },
        StepLabel::IpcPagesLockTables { .. } => { reveal(ipc_pages_lock_tables_step); },
        StepLabel::IpcPagesCheck { .. } => { reveal(ipc_pages_check_step); },
        StepLabel::IpcPagesDowngrade => { reveal(ipc_pages_downgrade_step); },
        StepLabel::IpcPagesUnlockTables => { reveal(ipc_pages_unlock_tables_step); },
        StepLabel::IpcPagesFinish { .. } => { reveal(ipc_pages_finish_step); },
        _ => {},
    }
}

/// The labels of the `kill_container` family.
pub open spec fn kill_container_label(l: StepLabel) -> bool {
    ||| l is KillContainerEnter || l is KillContainerMarkChild || l is KillContainerMarkRoot || l is KillContainerRetireRoot || l is KillContainerCpus || l is KillContainerMoveCpu || l is KillContainerPages
    ||| l is KillContainerMovePage || l is KillContainerRetireStage || l is KillContainerRetire || l is KillContainerFinish
}

/// A step of the `kill_container` family keeps the PCID of every process alive before and after it.
pub proof fn kill_container_step_implies_process_pcids_kept(l: StepLabel, u: KernelU, u2: KernelU, d: CpuId)
    requires kill_container_label(l), labeled_step(l, u, u2, d),
    ensures process_pcids_kept(u, u2),
{
    match l {
        StepLabel::KillContainerEnter { .. } => { reveal(kill_container_enter_step); },
        StepLabel::KillContainerMarkChild => { reveal(kill_container_mark_child_step); },
        StepLabel::KillContainerMarkRoot => { reveal(kill_container_mark_root_step); },
        StepLabel::KillContainerRetireRoot => { reveal(kill_container_retire_root_step); },
        StepLabel::KillContainerCpus => { reveal(kill_container_cpus_step); },
        StepLabel::KillContainerMoveCpu => { reveal(kill_container_move_cpu_step); },
        StepLabel::KillContainerPages => { reveal(kill_container_pages_step); },
        StepLabel::KillContainerMovePage { .. } => { reveal(kill_container_move_page_step); },
        StepLabel::KillContainerRetireStage => { reveal(kill_container_retire_stage_step); },
        StepLabel::KillContainerRetire => { reveal(kill_container_retire_step); },
        StepLabel::KillContainerFinish => { reveal(kill_container_finish_step); },
        _ => {},
    }
}

/// The labels of the `kill_process` family.
pub open spec fn kill_process_label(l: StepLabel) -> bool {
    ||| l is KillProcessEnter || l is KillProcessMarkChild || l is KillProcessDangling || l is KillProcessMarkThread || l is KillProcessDequeueScheduled || l is KillProcessDequeueEndpoint
    ||| l is KillProcessCpuToIdle || l is KillProcessUnlink || l is KillProcessDescriptorDropped || l is KillProcessCallerWoken || l is KillProcessCallerTakenOver || l is KillProcessDanglingReclaimed
    ||| l is KillProcessEndpointReleased || l is KillProcessLockTable || l is KillProcessTableHidden || l is KillProcessTlbCleared || l is KillProcessFlushed || l is KillProcessUnownFunctions
    ||| l is KillProcessIommuLeaf || l is KillProcessRefund || l is KillProcessQuota || l is KillProcessUnlockTable || l is KillProcessZombify || l is KillProcessZombieRetire || l is KillProcessRetire
    ||| l is KillProcessFinish
}

/// A step of the `kill_process` family keeps the PCID of every process alive before and after it.
pub proof fn kill_process_step_implies_process_pcids_kept(l: StepLabel, u: KernelU, u2: KernelU, d: CpuId)
    requires kill_process_label(l), labeled_step(l, u, u2, d),
    ensures process_pcids_kept(u, u2),
{
    match l {
        StepLabel::KillProcessEnter { .. } => { reveal(kill_process_enter_step); },
        StepLabel::KillProcessMarkChild => { reveal(kill_process_mark_child_step); },
        StepLabel::KillProcessDangling => { reveal(kill_process_dangling_step); },
        StepLabel::KillProcessMarkThread => { reveal(kill_process_mark_thread_step); },
        StepLabel::KillProcessDequeueScheduled => { reveal(kill_process_dequeue_scheduled_step); },
        StepLabel::KillProcessDequeueEndpoint => { reveal(kill_process_dequeue_endpoint_step); },
        StepLabel::KillProcessCpuToIdle => { reveal(kill_process_cpu_to_idle_step); },
        StepLabel::KillProcessUnlink => { reveal(kill_process_unlink_step); },
        StepLabel::KillProcessDescriptorDropped => { killed_thread_reclaim_implies_process_map_kept(u, u2, d); },
        StepLabel::KillProcessCallerWoken => { killed_thread_reclaim_implies_process_map_kept(u, u2, d); },
        StepLabel::KillProcessCallerTakenOver => { killed_thread_reclaim_implies_process_map_kept(u, u2, d); },
        StepLabel::KillProcessDanglingReclaimed => { killed_thread_reclaim_implies_process_map_kept(u, u2, d); },
        StepLabel::KillProcessEndpointReleased => { killed_thread_reclaim_implies_process_map_kept(u, u2, d); },
        StepLabel::KillProcessLockTable => { reveal(kill_process_lock_table_step); },
        StepLabel::KillProcessTableHidden => { reveal(kill_process_table_hidden_step); reveal(process_table_hidden_step); },
        StepLabel::KillProcessTlbCleared => { reveal(kernel_u_cpu_tlb_cleared); },
        StepLabel::KillProcessFlushed => { reveal(kill_process_flushed_step); },
        StepLabel::KillProcessUnownFunctions => { reveal(kill_process_unown_functions_step); },
        StepLabel::KillProcessIommuLeaf => { reveal(kill_process_iommu_leaf_step); },
        StepLabel::KillProcessRefund => {
            reveal(kernel_u_container_quota_1g_increased); reveal(kernel_u_container_quota_2m_increased); reveal(kernel_u_container_quota_4k_increased); reveal(kill_process_refund_step);
        },
        StepLabel::KillProcessQuota => { reveal(kill_process_quota_step); },
        StepLabel::KillProcessUnlockTable => { reveal(kill_process_unlock_table_step); },
        StepLabel::KillProcessZombify => { reveal(kill_process_zombify_step); },
        StepLabel::KillProcessZombieRetire => { reveal(kill_process_zombie_retire_step); },
        StepLabel::KillProcessRetire => { reveal(kill_process_retire_step); },
        StepLabel::KillProcessFinish => { reveal(kill_process_finish_step); },
        _ => {},
    }
}

/// The labels of the `thread_exit` family.
pub open spec fn thread_exit_label(l: StepLabel) -> bool {
    ||| l is ThreadExitEnter || l is ThreadExitDescriptorDropped || l is ThreadExitCallerWoken || l is ThreadExitCallerTakenOver || l is ThreadExitDanglingReclaimed || l is ThreadExitEndpointReleased
    ||| l is ThreadExitDrop || l is ThreadExitRelease || l is ThreadExitLockTable || l is ThreadExitTableHidden || l is ThreadExitTlbFlush || l is ThreadExitFlushed || l is ThreadExitUnown
    ||| l is ThreadExitIommuLeaf || l is ThreadExitRefund || l is ThreadExitQuota || l is ThreadExitUnlockTable || l is ThreadExitLockPcidAllocator || l is ThreadExitFinish
}

/// A step of the `thread_exit` family keeps the PCID of every process alive before and after it.
pub proof fn thread_exit_step_implies_process_pcids_kept(l: StepLabel, u: KernelU, u2: KernelU, d: CpuId)
    requires thread_exit_label(l), labeled_step(l, u, u2, d),
    ensures process_pcids_kept(u, u2),
{
    match l {
        StepLabel::ThreadExitEnter => { reveal(thread_exit_enter_step); },
        StepLabel::ThreadExitDescriptorDropped => { killed_thread_reclaim_implies_process_map_kept(u, u2, d); },
        StepLabel::ThreadExitCallerWoken => { killed_thread_reclaim_implies_process_map_kept(u, u2, d); },
        StepLabel::ThreadExitCallerTakenOver => { killed_thread_reclaim_implies_process_map_kept(u, u2, d); },
        StepLabel::ThreadExitDanglingReclaimed => { killed_thread_reclaim_implies_process_map_kept(u, u2, d); },
        StepLabel::ThreadExitEndpointReleased => { killed_thread_reclaim_implies_process_map_kept(u, u2, d); },
        StepLabel::ThreadExitDrop => { reveal(thread_exit_drop_step); },
        StepLabel::ThreadExitRelease => { reveal(kernel_u_endpoint_released); reveal(thread_exit_release_step); },
        StepLabel::ThreadExitLockTable => { reveal(thread_exit_lock_table_step); },
        StepLabel::ThreadExitTableHidden => { reveal(process_table_hidden_step); },
        StepLabel::ThreadExitTlbFlush => { reveal(kernel_u_cpu_tlb_cleared); reveal(thread_exit_tlb_flush_step); },
        StepLabel::ThreadExitFlushed => { reveal(thread_exit_flushed_step); },
        StepLabel::ThreadExitUnown => { reveal(thread_exit_unown_step); },
        StepLabel::ThreadExitIommuLeaf => { reveal(thread_exit_iommu_leaf_step); },
        StepLabel::ThreadExitRefund => {
            reveal(kernel_u_container_quota_1g_increased); reveal(kernel_u_container_quota_2m_increased); reveal(kernel_u_container_quota_4k_increased); reveal(thread_exit_refund_step);
        },
        StepLabel::ThreadExitQuota => { reveal(thread_exit_quota_step); },
        StepLabel::ThreadExitUnlockTable => { reveal(thread_exit_unlock_table_step); },
        StepLabel::ThreadExitLockPcidAllocator => { reveal(thread_exit_lock_pcid_allocator_step); },
        StepLabel::ThreadExitFinish => { reveal(kernel_u_thread_exit_changed); reveal(thread_exit_finish_step); },
        _ => {},
    }
}

/// A kernel step that is no hardware step keeps the PCID of every process alive before and after it.
pub proof fn kernel_step_implies_process_pcids_kept(l: StepLabel, u: KernelU, u2: KernelU, d: CpuId)
    requires !hardware_label(l), labeled_step(l, u, u2, d),
    ensures process_pcids_kept(u, u2),
{
    if map_4k_label(l) { map_4k_step_implies_process_pcids_kept(l, u, u2, d); }
    else if map_2m_label(l) { map_2m_step_implies_process_pcids_kept(l, u, u2, d); }
    else if map_1g_label(l) { map_1g_step_implies_process_pcids_kept(l, u, u2, d); }
    else if iommu_label(l) { iommu_step_implies_process_pcids_kept(l, u, u2, d); }
    else if quota_cpu_label(l) { quota_cpu_step_implies_process_pcids_kept(l, u, u2, d); }
    else if pci_bar_label(l) { pci_bar_step_implies_process_pcids_kept(l, u, u2, d); }
    else if create_label(l) { create_step_implies_process_pcids_kept(l, u, u2, d); }
    else if ipc_label(l) { ipc_step_implies_process_pcids_kept(l, u, u2, d); }
    else if kill_container_label(l) { kill_container_step_implies_process_pcids_kept(l, u, u2, d); }
    else if kill_process_label(l) { kill_process_step_implies_process_pcids_kept(l, u, u2, d); }
    else { thread_exit_step_implies_process_pcids_kept(l, u, u2, d); }
}
} // verus!
