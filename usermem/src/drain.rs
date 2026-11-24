//! A kernel step of a cpu of a domain changes the TLBs, mode, or current process of no other cpu outside that domain unless
//! that cpu is inside a kernel step or off, proved per label family from the step specifications; the kill TLB clear, whose
//! specification does not say whose cpu it clears, is the one exception. Hence such a step drains no buffer holding stores
//! of a cpu outside the domain but its own (`remote_cpu_views_within_domain_implies_drains_within_domain`).
use vstd::prelude::*;
use crate::*;
use crate::pcid::*;
use crate::invariant::*;
use crate::ni::*;
use veriflat_noninterference::{in_domain, steps_in_domain};
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
/// Every cpu other than `d` whose TLBs, mode, or current process the step from `u` to `u2` changes is inside a kernel step or
/// off in `u`, or is a cpu of the domain rooted at `x`.
pub open spec fn remote_cpu_views_within_domain(u: KernelU, u2: KernelU, d: CpuId, x: RwLockContainerPtr) -> bool {
    forall|c: CpuId| #![trigger u.cpu_array[c as int]] index_valid(NUM_CPUS, c) && c != d && !cpu_view_kept(u, u2, c)
        ==> u.cpu_array[c as int].op is InStep || u.cpu_array[c as int].op is Off || in_domain(u, x, u.cpu_array[c as int].owning_container)
}

/// A step that changes no cpu and no TLB changes the view of no cpu.
pub proof fn cpus_kept_implies_remote_cpu_views_within_domain(u: KernelU, u2: KernelU, d: CpuId, x: RwLockContainerPtr)
    requires u2.cpu_array == u.cpu_array, u2.cpu_tlb == u.cpu_tlb,
    ensures remote_cpu_views_within_domain(u, u2, d, x),
{}

/// A TLB clear keeps every cpu and every TLB key, and a TLB it changes is one of a cpu owned by `ctn`.
pub proof fn cpu_tlb_cleared_implies_changed_key_owned(pre: KernelU, u2: KernelU, pcid: Pcid, ctn: RwLockContainerPtr, key: (CpuId, Pcid))
    requires kernel_u_cpu_tlb_cleared(pre, u2, pcid, Some(ctn)),
    ensures
        u2.cpu_array == pre.cpu_array, pre.cpu_tlb.dom().contains(key) ==> u2.cpu_tlb.dom().contains(key),
        u2.cpu_tlb.dom().contains(key) && !(pre.cpu_tlb.dom().contains(key) && pre.cpu_tlb[key] == u2.cpu_tlb[key]) ==> pre.cpu_array[key.0 as int].owning_container == ctn,
{
    reveal(kernel_u_cpu_tlb_cleared);
    let changed = u2.cpu_tlb.dom().filter(|key: (CpuId, Pcid)| !pre.cpu_tlb.dom().contains(key) || pre.cpu_tlb[key] != u2.cpu_tlb[key]);
    if u2.cpu_tlb.dom().contains(key) && !(pre.cpu_tlb.dom().contains(key) && pre.cpu_tlb[key] == u2.cpu_tlb[key]) { assert(changed.contains(key)); }
}

/// A TLB clear on a cpu owned by `ctn` keeps the TLBs of every cpu `ctn` does not own.
pub proof fn cpu_tlb_cleared_outside_owner_implies_cpu_tlbs_kept(u: KernelU, pre: KernelU, u2: KernelU, pcid: Pcid, ctn: RwLockContainerPtr, c: CpuId)
    requires kernel_u_cpu_tlb_cleared(pre, u2, pcid, Some(ctn)), pre.cpu_tlb == u.cpu_tlb, pre.cpu_array == u.cpu_array, u.cpu_array[c as int].owning_container != ctn,
    ensures cpu_tlbs_kept(u, u2, c),
{
    assert forall|p: Pcid| #![trigger u2.cpu_tlb.dom().contains((c, p))] #![trigger u.cpu_tlb.dom().contains((c, p))]
        u2.cpu_tlb.dom().contains((c, p)) == u.cpu_tlb.dom().contains((c, p)) && (u.cpu_tlb.dom().contains((c, p)) ==> u2.cpu_tlb[(c, p)] == u.cpu_tlb[(c, p)]) by {
        cpu_tlb_cleared_implies_changed_key_owned(pre, u2, pcid, ctn, (c, p));
    };
}

/// A TLB clear on a cpu owned by `ctn`, a container of the domain rooted at `x`, from a state with the cpus and TLBs of `u`
/// changes the view of no cpu outside `x`.
pub proof fn cpu_tlb_cleared_in_domain_implies_remote_cpu_views_within_domain(u: KernelU, pre: KernelU, u2: KernelU, pcid: Pcid, ctn: RwLockContainerPtr, d: CpuId,
    x: RwLockContainerPtr)
    requires kernel_u_cpu_tlb_cleared(pre, u2, pcid, Some(ctn)), pre.cpu_array == u.cpu_array, pre.cpu_tlb == u.cpu_tlb, in_domain(u, x, ctn),
    ensures remote_cpu_views_within_domain(u, u2, d, x),
{
    assert forall|c: CpuId| #![trigger u.cpu_array[c as int]] index_valid(NUM_CPUS, c) && c != d && !cpu_view_kept(u, u2, c)
        implies u.cpu_array[c as int].op is InStep || u.cpu_array[c as int].op is Off || in_domain(u, x, u.cpu_array[c as int].owning_container) by {
        cpu_tlb_cleared_implies_changed_key_owned(pre, u2, pcid, ctn, (c, 0));
        if u.cpu_array[c as int].owning_container != ctn { cpu_tlb_cleared_outside_owner_implies_cpu_tlbs_kept(u, pre, u2, pcid, ctn, c); }
    };
}

/// A TLB flush step of the thread on cpu `d` of the domain rooted at `x` changes the view of no cpu outside `x`.
pub proof fn unmap_4k_tlb_flush_step_implies_remote_cpu_views_within_domain(u: KernelU, u2: KernelU, d: CpuId, x: RwLockContainerPtr)
    requires unmap_4k_tlb_flush_step(u, u2, d), kernel_u_ownership_wf(u), steps_in_domain(u, d, x), u.cpu_array[d as int].current_thread is Some,
    ensures remote_cpu_views_within_domain(u, u2, d, x),
{
    reveal(unmap_4k_tlb_flush_step); reveal(kernel_u_cpu_ownership_wf);
    let thread = u.thread_map[u.cpu_array[d as int].current_thread->Some_0];
    let locked = KernelU {
        container_map: u.container_map.insert(thread.owning_container,
            ContainerU { cpu_set_lock: u.container_map[thread.owning_container].cpu_set_lock.with_reader(d), ..u.container_map[thread.owning_container] }),
        ..u
    };
    if u2 == locked { cpus_kept_implies_remote_cpu_views_within_domain(u, u2, d, x); } else {
        cpu_tlb_cleared_in_domain_implies_remote_cpu_views_within_domain(u, locked, u2, u.process_map[thread.owning_proc].pcid, thread.owning_container, d, x);
    }
}

/// A thread-exit TLB flush step of the thread on cpu `d` of the domain rooted at `x` changes the view of no cpu outside `x`.
pub proof fn thread_exit_tlb_flush_step_implies_remote_cpu_views_within_domain(u: KernelU, u2: KernelU, d: CpuId, x: RwLockContainerPtr)
    requires thread_exit_tlb_flush_step(u, u2, d), kernel_u_ownership_wf(u), steps_in_domain(u, d, x), u.cpu_array[d as int].current_thread is Some,
    ensures remote_cpu_views_within_domain(u, u2, d, x),
{
    reveal(thread_exit_tlb_flush_step); reveal(kernel_u_cpu_ownership_wf);
    let thread = u.thread_map[u.cpu_array[d as int].current_thread->Some_0];
    let locked = KernelU {
        container_map: u.container_map.insert(thread.owning_container,
            ContainerU { cpu_set_lock: u.container_map[thread.owning_container].cpu_set_lock.with_reader(d), ..u.container_map[thread.owning_container] }),
        ..u
    };
    if u2 == locked { cpus_kept_implies_remote_cpu_views_within_domain(u, u2, d, x); } else {
        cpu_tlb_cleared_in_domain_implies_remote_cpu_views_within_domain(u, locked, u2, u.process_map[thread.owning_proc].pcid, thread.owning_container, d, x);
    }
}

/// A per-address TLB flush step of the thread on cpu `d` of the domain rooted at `x` changes the view of no cpu outside `x`.
pub proof fn unmap_4k_tlb_va_flush_step_implies_remote_cpu_views_within_domain(u: KernelU, u2: KernelU, d: CpuId, va: VAddr, count: usize, stride_2m: bool,
    x: RwLockContainerPtr)
    requires unmap_4k_tlb_va_flush_step(u, u2, d, va, count, stride_2m), kernel_u_ownership_wf(u), steps_in_domain(u, d, x), u.cpu_array[d as int].current_thread is Some,
    ensures remote_cpu_views_within_domain(u, u2, d, x),
{
    reveal(unmap_4k_tlb_va_flush_step); reveal(kernel_u_cpu_tlb_va_flushed); reveal(kernel_u_cpu_ownership_wf);
    let thread = u.thread_map[u.cpu_array[d as int].current_thread->Some_0];
    let locked = KernelU {
        container_map: u.container_map.insert(thread.owning_container,
            ContainerU { cpu_set_lock: u.container_map[thread.owning_container].cpu_set_lock.with_reader(d), ..u.container_map[thread.owning_container] }),
        ..u
    };
    if u2 == locked { cpus_kept_implies_remote_cpu_views_within_domain(u, u2, d, x); } else {
        assert forall|c: CpuId| #![trigger u.cpu_array[c as int]] index_valid(NUM_CPUS, c) && c != d && !cpu_view_kept(u, u2, c)
            implies u.cpu_array[c as int].op is InStep || u.cpu_array[c as int].op is Off || in_domain(u, x, u.cpu_array[c as int].owning_container) by {
            if !in_domain(u, x, u.cpu_array[c as int].owning_container) {
                assert forall|p: Pcid| #![trigger u2.cpu_tlb.dom().contains((c, p))] #![trigger u.cpu_tlb.dom().contains((c, p))]
                    u2.cpu_tlb.dom().contains((c, p)) == u.cpu_tlb.dom().contains((c, p)) && (u.cpu_tlb.dom().contains((c, p)) ==> u2.cpu_tlb[(c, p)] == u.cpu_tlb[(c, p)]) by {
                    if u2.cpu_tlb.dom().contains((c, p)) && !(u.cpu_tlb.dom().contains((c, p)) && u2.cpu_tlb[(c, p)] == u.cpu_tlb[(c, p)]) { assert(u2.cpu_tlb.dom().contains((c, p))); }
                };
            }
        };
    }
}

/// Forcing the cpu running the kill victim to idle changes a cpu of the killer's domain: the victim's container lies in it.
pub proof fn kill_process_cpu_to_idle_step_implies_remote_cpu_views_within_domain(u: KernelU, u2: KernelU, d: CpuId, x: RwLockContainerPtr)
    requires kernel_u_ownership_wf(u), steps_in_domain(u, d, x), u.container_map.dom().contains(x), kill_process_step_pre(u, d), kill_process_cpu_to_idle_step(u, u2, d),
    ensures remote_cpu_views_within_domain(u, u2, d, x),
{
    reveal(kill_process_step_pre); reveal(kill_process_cpu_to_idle_step); reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_process_threads_wf); reveal(kernel_u_running_thread_cpu_wf);
    let owner = u.cpu_array[d as int].owning_container;
    let target = u.process_map[kill_target(u, d)];
    assert(in_domain(u, x, target.owning_container)) by {
        reveal(kernel_u_container_tree_wf); reveal(kernel_u_process_ownership_wf);
        if target.owning_container != owner {
            if owner != x { assert(u.container_map[owner].uppertree_seq.contains(x)); }
            assert(u.container_map[target.owning_container].uppertree_seq.contains(x));
        }
    };
}

/// The cpu `target`, owned by the container of cpu `d` of the domain rooted at `x` or by a child of it, is a cpu of `x`.
pub proof fn target_container_own_or_child_implies_in_domain(u: KernelU, d: CpuId, target: CpuId, x: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(u), steps_in_domain(u, d, x), u.container_map.dom().contains(x), u.container_map.dom().contains(u.cpu_array[target as int].owning_container),
        ({
            let (t, o) = (u.cpu_array[target as int].owning_container, u.cpu_array[d as int].owning_container);
            t == o || u.container_map[t].parent == Some(o)
        }),
    ensures in_domain(u, x, u.cpu_array[target as int].owning_container),
{
    reveal(kernel_u_container_tree_wf);
    let (t, o) = (u.cpu_array[target as int].owning_container, u.cpu_array[d as int].owning_container);
    if t != o {
        assert(u.container_map[t].uppertree_seq.contains(o));
        if o != x { assert(u.container_map[x].subtree_set.contains(o)); assert(u.container_map[o].uppertree_seq.contains(x)); assert(u.container_map[t].uppertree_seq.contains(x)); }
        assert(u.container_map[x].subtree_set.contains(t));
    }
}

/// Moving a cpu of a killed container to the killer's container changes only that cpu's owner.
pub proof fn kill_container_move_cpu_step_implies_remote_cpu_views_within_domain(u: KernelU, u2: KernelU, d: CpuId, x: RwLockContainerPtr)
    requires kill_container_move_cpu_step(u, u2, d),
    ensures remote_cpu_views_within_domain(u, u2, d, x),
{
    reveal(kill_container_move_cpu_step);
    let moved = Set::range(0usize, NUM_CPUS).filter(|i: CpuId| u.cpu_array[i as int] != u2.cpu_array[i as int]);
    assert forall|c: CpuId| #![trigger u.cpu_array[c as int]] index_valid(NUM_CPUS, c) && c != d && !cpu_view_kept(u, u2, c)
        implies u.cpu_array[c as int].op is InStep || u.cpu_array[c as int].op is Off || in_domain(u, x, u.cpu_array[c as int].owning_container) by {
        if u.cpu_array[c as int] != u2.cpu_array[c as int] { assert(moved.contains(c)); }
    };
}

/// A killed-thread reclaim step changes no cpu and no TLB.
pub proof fn killed_thread_reclaim_implies_cpus_kept(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_killed_thread_reclaim_step(u, u2, d),
    ensures u2.cpu_array == u.cpu_array, u2.cpu_tlb == u.cpu_tlb,
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
/// A step of the `map_4k` family of a cpu of the domain rooted at `x` changes the view of no cpu outside `x` other than its own
/// that is neither inside a kernel step nor off.
pub proof fn map_4k_step_implies_remote_cpu_views_within_domain(l: StepLabel, u: KernelU, u2: KernelU, d: CpuId, x: RwLockContainerPtr)
    requires map_4k_label(l), labeled_step(l, u, u2, d), kernel_u_ownership_wf(u), steps_in_domain(u, d, x), u.container_map.dom().contains(x),
    ensures remote_cpu_views_within_domain(u, u2, d, x),
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
        StepLabel::Unmap4kTlbFlush => { reveal(unmap_4k_flush_step_pre); unmap_4k_tlb_flush_step_implies_remote_cpu_views_within_domain(u, u2, d, x); },
        StepLabel::Unmap4kTlbVaFlush => {
            let range = u.thread_map[u.cpu_array[d as int].current_thread->Some_0].syscall_progress->Some_0->Unmap4k_range;
            reveal(unmap_4k_flush_step_pre); unmap_4k_tlb_va_flush_step_implies_remote_cpu_views_within_domain(u, u2, d, range.start, range.len, false, x);
        },
        StepLabel::Unmap4kFlushed => { reveal(unmap_4k_flushed_step); },
        StepLabel::Unmap4kRefund => { reveal(kernel_u_container_quota_4k_increased); reveal(unmap_4k_refund_step); },
        StepLabel::Unmap4kExit => { reveal(unmap_4k_exit_step); },
        _ => {},
    }
}

/// A step of the `map_2m` family of a cpu of the domain rooted at `x` changes the view of no cpu outside `x` other than its own
/// that is neither inside a kernel step nor off.
pub proof fn map_2m_step_implies_remote_cpu_views_within_domain(l: StepLabel, u: KernelU, u2: KernelU, d: CpuId, x: RwLockContainerPtr)
    requires map_2m_label(l), labeled_step(l, u, u2, d), kernel_u_ownership_wf(u), steps_in_domain(u, d, x), u.container_map.dom().contains(x),
    ensures remote_cpu_views_within_domain(u, u2, d, x),
{
    match l {
        StepLabel::Mmap2mHold { .. } => { reveal(mmap_4k_hold_step); },
        StepLabel::Mmap2mEnter { .. } => { reveal(mmap_2m_enter_step); },
        StepLabel::Mmap2mDirectory => { reveal(mmap_2m_directory_step); },
        StepLabel::Mmap2mDowngrade => { reveal(mmap_2m_downgrade_step); },
        StepLabel::Mmap2mFlush => { reveal(mmap_2m_flush_step_pre); unmap_4k_tlb_flush_step_implies_remote_cpu_views_within_domain(u, u2, d, x); },
        StepLabel::Mmap2mFlushed => { reveal(mmap_2m_flushed_step); },
        StepLabel::Mmap2mL1Reclaim => { reveal(kernel_u_container_quota_4k_increased); },
        StepLabel::Mmap2mLeaf => { reveal(mmap_2m_leaf_step); },
        StepLabel::Mmap2mExit => { reveal(mmap_2m_exit_step); },
        StepLabel::Mmap2mRelease => { reveal(mmap_4k_release_step); },
        StepLabel::Unmap2mEnter { .. } => { reveal(unmap_2m_enter_step); },
        StepLabel::Unmap2mLeaf => { reveal(unmap_2m_leaf_step); },
        StepLabel::Unmap2mTlbFlush => { reveal(unmap_2m_flush_step_pre); unmap_4k_tlb_flush_step_implies_remote_cpu_views_within_domain(u, u2, d, x); },
        StepLabel::Unmap2mTlbVaFlush => {
            let range = u.thread_map[u.cpu_array[d as int].current_thread->Some_0].syscall_progress->Some_0->Unmap2m_range;
            reveal(unmap_2m_flush_step_pre); unmap_4k_tlb_va_flush_step_implies_remote_cpu_views_within_domain(u, u2, d, range.start, range.len, true, x);
        },
        StepLabel::Unmap2mFlushed => { reveal(unmap_2m_flushed_step); },
        StepLabel::Unmap2mRefund => { reveal(kernel_u_container_quota_2m_increased); reveal(unmap_2m_refund_step); },
        StepLabel::Unmap2mExit => { reveal(unmap_2m_exit_step); },
        _ => {},
    }
}

/// A step of the `map_1g` family of a cpu of the domain rooted at `x` changes the view of no cpu outside `x` other than its own
/// that is neither inside a kernel step nor off.
pub proof fn map_1g_step_implies_remote_cpu_views_within_domain(l: StepLabel, u: KernelU, u2: KernelU, d: CpuId, x: RwLockContainerPtr)
    requires map_1g_label(l), labeled_step(l, u, u2, d), kernel_u_ownership_wf(u), steps_in_domain(u, d, x), u.container_map.dom().contains(x),
    ensures remote_cpu_views_within_domain(u, u2, d, x),
{
    match l {
        StepLabel::Mmap1gEnter { .. } => { reveal(mmap_1g_enter_step); },
        StepLabel::Mmap1gHide => { reveal(mmap_1g_hide_step); },
        StepLabel::Mmap1gFlush => { reveal(mmap_1g_flush_step_pre); unmap_4k_tlb_flush_step_implies_remote_cpu_views_within_domain(u, u2, d, x); },
        StepLabel::Mmap1gFlushed => { reveal(mmap_1g_flushed_step); },
        StepLabel::Mmap1gReclaim => { reveal(kernel_u_container_quota_4k_increased); },
        StepLabel::Mmap1gDirectory => { reveal(mmap_1g_directory_step); },
        StepLabel::Mmap1gLeaf => { reveal(mmap_1g_leaf_step); },
        StepLabel::Mmap1gExit => { reveal(mmap_1g_exit_step); },
        StepLabel::Unmap1gEnter { .. } => { reveal(unmap_1g_enter_step); },
        StepLabel::Unmap1gLeaf => { reveal(unmap_1g_leaf_step); },
        StepLabel::Unmap1gTlbFlush => { reveal(unmap_1g_flush_step_pre); unmap_4k_tlb_flush_step_implies_remote_cpu_views_within_domain(u, u2, d, x); },
        StepLabel::Unmap1gFlushed => { reveal(unmap_1g_flushed_step); },
        StepLabel::Unmap1gRefund => { reveal(kernel_u_container_quota_1g_increased); reveal(unmap_1g_refund_step); },
        StepLabel::Unmap1gExit => { reveal(unmap_1g_exit_step); },
        _ => {},
    }
}

/// A step of the `iommu` family of a cpu of the domain rooted at `x` changes the view of no cpu outside `x` other than its own
/// that is neither inside a kernel step nor off.
pub proof fn iommu_step_implies_remote_cpu_views_within_domain(l: StepLabel, u: KernelU, u2: KernelU, d: CpuId, x: RwLockContainerPtr)
    requires iommu_label(l), labeled_step(l, u, u2, d), kernel_u_ownership_wf(u), steps_in_domain(u, d, x), u.container_map.dom().contains(x),
    ensures remote_cpu_views_within_domain(u, u2, d, x),
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

/// A step of the `quota_cpu` family of a cpu of the domain rooted at `x` changes the view of no cpu outside `x` other than its own
/// that is neither inside a kernel step nor off.
pub proof fn quota_cpu_step_implies_remote_cpu_views_within_domain(l: StepLabel, u: KernelU, u2: KernelU, d: CpuId, x: RwLockContainerPtr)
    requires quota_cpu_label(l), labeled_step(l, u, u2, d), kernel_u_ownership_wf(u), steps_in_domain(u, d, x), u.container_map.dom().contains(x),
    ensures remote_cpu_views_within_domain(u, u2, d, x),
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
        StepLabel::CpuOnline { target } => { reveal(kernel_u_cpu_online_changed); target_container_own_or_child_implies_in_domain(u, d, target, x); },
        StepLabel::CpuOfflineRequestChild { .. } => { reveal(kernel_u_cpu_offline_request_changed); },
        StepLabel::CpuOnlineChild { target } => { reveal(kernel_u_cpu_online_changed); target_container_own_or_child_implies_in_domain(u, d, target, x); },
        StepLabel::PciAttach { .. } => { reveal(kernel_u_pci_attach_changed); },
        StepLabel::PciClaim { .. } => { reveal(kernel_u_pci_claim_changed); },
        _ => {},
    }
}

/// A step of the `pci_bar` family of a cpu of the domain rooted at `x` changes the view of no cpu outside `x` other than its own
/// that is neither inside a kernel step nor off.
pub proof fn pci_bar_step_implies_remote_cpu_views_within_domain(l: StepLabel, u: KernelU, u2: KernelU, d: CpuId, x: RwLockContainerPtr)
    requires pci_bar_label(l), labeled_step(l, u, u2, d), kernel_u_ownership_wf(u), steps_in_domain(u, d, x), u.container_map.dom().contains(x),
    ensures remote_cpu_views_within_domain(u, u2, d, x),
{
    match l {
        StepLabel::MapPciBar4kEnter { .. } => { reveal(map_pci_bar_4k_enter_step); },
        StepLabel::MapPciBar4kDirectory => { reveal(map_pci_bar_4k_directory_step); },
        StepLabel::MapPciBar4kExit { .. } => { reveal(map_pci_bar_4k_exit_step); },
        StepLabel::MapPciBar2mEnter { .. } => { reveal(map_pci_bar_2m_enter_step); },
        StepLabel::MapPciBar2mDirectory => { reveal(map_pci_bar_2m_directory_step); },
        StepLabel::MapPciBar2mFlush => { reveal(map_pci_bar_2m_l1_step_pre); unmap_4k_tlb_flush_step_implies_remote_cpu_views_within_domain(u, u2, d, x); },
        StepLabel::MapPciBar2mFlushed => { reveal(map_pci_bar_2m_flushed_step); },
        StepLabel::MapPciBar2mL1Reclaim => { reveal(kernel_u_container_quota_4k_increased); },
        StepLabel::MapPciBar2mExit { .. } => { reveal(map_pci_bar_2m_exit_step); },
        StepLabel::UnmapPciBar4kHide { .. } => { reveal(unmap_pci_bar_4k_hide_step); },
        StepLabel::UnmapPciBar4kFlush => { reveal(unmap_pci_bar_4k_flush_step_pre); unmap_4k_tlb_flush_step_implies_remote_cpu_views_within_domain(u, u2, d, x); },
        StepLabel::UnmapPciBar4kFlushed => { reveal(unmap_pci_bar_4k_flushed_step); },
        StepLabel::UnmapPciBar4kExit { .. } => { reveal(unmap_pci_bar_4k_exit_step); },
        StepLabel::UnmapPciBar2mHide { .. } => { reveal(unmap_pci_bar_2m_hide_step); },
        StepLabel::UnmapPciBar2mFlush => { reveal(unmap_pci_bar_2m_flush_step_pre); unmap_4k_tlb_flush_step_implies_remote_cpu_views_within_domain(u, u2, d, x); },
        StepLabel::UnmapPciBar2mFlushed => { reveal(unmap_pci_bar_2m_flushed_step); },
        StepLabel::UnmapPciBar2mExit { .. } => { reveal(unmap_pci_bar_2m_exit_step); },
        _ => {},
    }
}

/// A step of the `create` family of a cpu of the domain rooted at `x` changes the view of no cpu outside `x` other than its own
/// that is neither inside a kernel step nor off.
pub proof fn create_step_implies_remote_cpu_views_within_domain(l: StepLabel, u: KernelU, u2: KernelU, d: CpuId, x: RwLockContainerPtr)
    requires create_label(l), labeled_step(l, u, u2, d), kernel_u_ownership_wf(u), steps_in_domain(u, d, x), u.container_map.dom().contains(x),
    ensures remote_cpu_views_within_domain(u, u2, d, x),
{
    reveal(kernel_u_cpu_ownership_wf);
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

/// A step of the `ipc` family of a cpu of the domain rooted at `x` changes the view of no cpu outside `x` other than its own
/// that is neither inside a kernel step nor off.
pub proof fn ipc_step_implies_remote_cpu_views_within_domain(l: StepLabel, u: KernelU, u2: KernelU, d: CpuId, x: RwLockContainerPtr)
    requires ipc_label(l), labeled_step(l, u, u2, d), kernel_u_ownership_wf(u), steps_in_domain(u, d, x), u.container_map.dom().contains(x),
    ensures remote_cpu_views_within_domain(u, u2, d, x),
{
    reveal(kernel_u_cpu_ownership_wf);
    match l {
        StepLabel::IpcBlock { .. } => { reveal(kernel_u_ipc_block_changed); },
        StepLabel::IpcRendezvous { .. } => { reveal(kernel_u_ipc_rendezvous_changed); },
        StepLabel::IpcCallHandoff { .. } => { reveal(kernel_u_ipc_call_handoff_changed); },
        StepLabel::IpcAcceptCall { .. } => { reveal(kernel_u_ipc_accept_call_changed); },
        StepLabel::IpcReplyHandoff { .. } => { reveal(kernel_u_ipc_reply_handoff_changed); },
        StepLabel::IpcReplyDanglingCallerTakenOver { .. } => { reveal(ipc_reply_dangling_caller_taken_over_step); },
        StepLabel::IpcReplyDanglingReclaimed => { killed_thread_reclaim_implies_cpus_kept(u, u2, d); },
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

/// A step of the `kill_container` family of a cpu of the domain rooted at `x` changes the view of no cpu outside `x` other than its own
/// that is neither inside a kernel step nor off.
pub proof fn kill_container_step_implies_remote_cpu_views_within_domain(l: StepLabel, u: KernelU, u2: KernelU, d: CpuId, x: RwLockContainerPtr)
    requires kill_container_label(l), labeled_step(l, u, u2, d), kernel_u_ownership_wf(u), steps_in_domain(u, d, x), u.container_map.dom().contains(x),
    ensures remote_cpu_views_within_domain(u, u2, d, x),
{
    match l {
        StepLabel::KillContainerEnter { .. } => { reveal(kill_container_enter_step); },
        StepLabel::KillContainerMarkChild => { reveal(kill_container_mark_child_step); },
        StepLabel::KillContainerMarkRoot => { reveal(kill_container_mark_root_step); },
        StepLabel::KillContainerRetireRoot => { reveal(kill_container_retire_root_step); },
        StepLabel::KillContainerCpus => { reveal(kill_container_cpus_step); },
        StepLabel::KillContainerMoveCpu => { kill_container_move_cpu_step_implies_remote_cpu_views_within_domain(u, u2, d, x); },
        StepLabel::KillContainerPages => { reveal(kill_container_pages_step); },
        StepLabel::KillContainerMovePage { .. } => { reveal(kill_container_move_page_step); },
        StepLabel::KillContainerRetireStage => { reveal(kill_container_retire_stage_step); },
        StepLabel::KillContainerRetire => { reveal(kill_container_retire_step); },
        StepLabel::KillContainerFinish => { reveal(kill_container_finish_step); },
        _ => {},
    }
}

/// A step of the `kill_process` family of a cpu of the domain rooted at `x` changes the view of no cpu outside `x` other than its own
/// that is neither inside a kernel step nor off, except by the kill TLB clear.
pub proof fn kill_process_step_implies_remote_cpu_views_within_domain(l: StepLabel, u: KernelU, u2: KernelU, d: CpuId, x: RwLockContainerPtr)
    requires kill_process_label(l), labeled_step(l, u, u2, d), kernel_u_ownership_wf(u), steps_in_domain(u, d, x), u.container_map.dom().contains(x), !(l is KillProcessTlbCleared),
    ensures remote_cpu_views_within_domain(u, u2, d, x),
{
    match l {
        StepLabel::KillProcessEnter { .. } => { reveal(kill_process_enter_step); },
        StepLabel::KillProcessMarkChild => { reveal(kill_process_mark_child_step); },
        StepLabel::KillProcessDangling => { reveal(kill_process_dangling_step); },
        StepLabel::KillProcessMarkThread => { reveal(kill_process_mark_thread_step); },
        StepLabel::KillProcessDequeueScheduled => { reveal(kill_process_dequeue_scheduled_step); },
        StepLabel::KillProcessDequeueEndpoint => { reveal(kill_process_dequeue_endpoint_step); },
        StepLabel::KillProcessCpuToIdle => { kill_process_cpu_to_idle_step_implies_remote_cpu_views_within_domain(u, u2, d, x); },
        StepLabel::KillProcessUnlink => { reveal(kill_process_unlink_step); },
        StepLabel::KillProcessDescriptorDropped => { killed_thread_reclaim_implies_cpus_kept(u, u2, d); },
        StepLabel::KillProcessCallerWoken => { killed_thread_reclaim_implies_cpus_kept(u, u2, d); },
        StepLabel::KillProcessCallerTakenOver => { killed_thread_reclaim_implies_cpus_kept(u, u2, d); },
        StepLabel::KillProcessDanglingReclaimed => { killed_thread_reclaim_implies_cpus_kept(u, u2, d); },
        StepLabel::KillProcessEndpointReleased => { killed_thread_reclaim_implies_cpus_kept(u, u2, d); },
        StepLabel::KillProcessLockTable => { reveal(kill_process_lock_table_step); },
        StepLabel::KillProcessTableHidden => { reveal(kill_process_table_hidden_step); reveal(process_table_hidden_step); },
        StepLabel::KillProcessTlbCleared => {},
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

/// A step of the `thread_exit` family of a cpu of the domain rooted at `x` changes the view of no cpu outside `x` other than its own
/// that is neither inside a kernel step nor off.
pub proof fn thread_exit_step_implies_remote_cpu_views_within_domain(l: StepLabel, u: KernelU, u2: KernelU, d: CpuId, x: RwLockContainerPtr)
    requires thread_exit_label(l), labeled_step(l, u, u2, d), kernel_u_ownership_wf(u), steps_in_domain(u, d, x), u.container_map.dom().contains(x),
    ensures remote_cpu_views_within_domain(u, u2, d, x),
{
    match l {
        StepLabel::ThreadExitEnter => { reveal(thread_exit_enter_step); },
        StepLabel::ThreadExitDescriptorDropped => { killed_thread_reclaim_implies_cpus_kept(u, u2, d); },
        StepLabel::ThreadExitCallerWoken => { killed_thread_reclaim_implies_cpus_kept(u, u2, d); },
        StepLabel::ThreadExitCallerTakenOver => { killed_thread_reclaim_implies_cpus_kept(u, u2, d); },
        StepLabel::ThreadExitDanglingReclaimed => { killed_thread_reclaim_implies_cpus_kept(u, u2, d); },
        StepLabel::ThreadExitEndpointReleased => { killed_thread_reclaim_implies_cpus_kept(u, u2, d); },
        StepLabel::ThreadExitDrop => { reveal(thread_exit_drop_step); },
        StepLabel::ThreadExitRelease => { reveal(kernel_u_endpoint_released); reveal(thread_exit_release_step); },
        StepLabel::ThreadExitLockTable => { reveal(thread_exit_lock_table_step); },
        StepLabel::ThreadExitTableHidden => { reveal(process_table_hidden_step); },
        StepLabel::ThreadExitTlbFlush => { reveal(thread_exit_flush_step_pre); reveal(thread_exit_reclaim_step_pre); thread_exit_tlb_flush_step_implies_remote_cpu_views_within_domain(u, u2, d, x); },
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

/// A kernel step that is no hardware step and no kill TLB clear, of a cpu of the domain rooted at `x`, changes the view of no
/// cpu outside `x` other than its own that is neither inside a kernel step nor off.
pub proof fn kernel_step_implies_remote_cpu_views_within_domain(l: StepLabel, u: KernelU, u2: KernelU, d: CpuId, x: RwLockContainerPtr)
    requires
        !hardware_label(l), !(l is KillProcessTlbCleared), labeled_step(l, u, u2, d), kernel_u_ownership_wf(u), steps_in_domain(u, d, x), u.container_map.dom().contains(x), u.container_map.dom().contains(x),
    ensures remote_cpu_views_within_domain(u, u2, d, x),
{
    if map_4k_label(l) { map_4k_step_implies_remote_cpu_views_within_domain(l, u, u2, d, x); }
    else if map_2m_label(l) { map_2m_step_implies_remote_cpu_views_within_domain(l, u, u2, d, x); }
    else if map_1g_label(l) { map_1g_step_implies_remote_cpu_views_within_domain(l, u, u2, d, x); }
    else if iommu_label(l) { iommu_step_implies_remote_cpu_views_within_domain(l, u, u2, d, x); }
    else if quota_cpu_label(l) { quota_cpu_step_implies_remote_cpu_views_within_domain(l, u, u2, d, x); }
    else if pci_bar_label(l) { pci_bar_step_implies_remote_cpu_views_within_domain(l, u, u2, d, x); }
    else if create_label(l) { create_step_implies_remote_cpu_views_within_domain(l, u, u2, d, x); }
    else if ipc_label(l) { ipc_step_implies_remote_cpu_views_within_domain(l, u, u2, d, x); }
    else if kill_container_label(l) { kill_container_step_implies_remote_cpu_views_within_domain(l, u, u2, d, x); }
    else if kill_process_label(l) { kill_process_step_implies_remote_cpu_views_within_domain(l, u, u2, d, x); }
    else { thread_exit_step_implies_remote_cpu_views_within_domain(l, u, u2, d, x); }
}

/// A step that changes the view of no cpu outside `x` other than `d` that is neither inside a kernel step nor off drains no
/// buffer holding stores of a cpu outside `x` other than `d`: a cpu with stores is neither (`store_buffers_covered`).
pub proof fn remote_cpu_views_within_domain_implies_drains_within_domain(old: MemState, new_u: KernelU, l: StepLabel, d: CpuId, x: RwLockContainerPtr)
    requires store_buffers_covered(old), remote_cpu_views_within_domain(old.u, new_u, d, x),
    ensures drains_within_domain(old, new_u, l, d, x),
{
    assert forall|c: CpuId| #![trigger old.bufs[c as int]] index_valid(NUM_CPUS, c) && c != d && drained(l, old.u, new_u, d, c) && old.bufs[c as int].len() > 0
        implies in_domain(old.u, x, old.u.cpu_array[c as int].owning_container) by {
        assert(store_covered(old.u, c, old.bufs[c as int][0]));
        assert(old.u.cpu_array[c as int] == old.u.cpu_array[c as int]);
    };
}
} // verus!
