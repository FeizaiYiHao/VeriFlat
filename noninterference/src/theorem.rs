use vstd::prelude::*;
use crate::*;
use crate::{ni_alloc_quota::*, ni_ipc::*, ni_mmap_4k::*, ni_new_container::*, ni_new_process::*, ni_new_thread::*, ni_schedule::*, ni_share_4k::*, ni_unmap_4k::*};
use veriflat_map_4k::*;
use veriflat_syscall_alloc_quota::syscall_alloc_quota::syscall_alloc_quota_spec::*;
use veriflat_syscall_ipc::syscall_ipc::syscall_ipc_spec::*;
use veriflat_syscall_mmap_4k::syscall_mmap_4k::syscall_mmap_4k_spec::*;
use veriflat_syscall_new_container::syscall_new_container::syscall_new_container_spec::*;
use veriflat_syscall_new_process::syscall_new_process::syscall_new_process_spec::*;
use veriflat_syscall_new_thread::syscall_new_thread::syscall_new_thread_spec::*;
use veriflat_syscall_schedule::syscall_schedule::syscall_schedule_spec::*;
use veriflat_syscall_unmap_4k::syscall_unmap_4k::syscall_unmap_4k_spec::*;

verus! {
/// One step of a syscall, with the arguments its step specification takes.
pub ghost enum StepLabel {
    Mmap4kEnter { range: VaRange4K }, Mmap4kDirectory, Mmap4kLeaf, Mmap4kExit,
    Unmap4kEnter { range: VaRange4K }, Unmap4kLeaf, Unmap4kTlbCleared { pcid: Pcid }, Unmap4kFlushed, Unmap4kRefund, Unmap4kExit,
    AllocQuota4k { alloc_amount: usize },
    Schedule { entry_regs: Registers, flushed_pcid: Option<Pcid> },
    NewThreadEnter { regs: Registers, endpoint_index: Option<EndpointIdx> }, NewThreadFinish,
    NewProcessEnter { range: VaRange4K, regs: Registers, endpoint_index: Option<EndpointIdx>, with_iommu: bool }, NewProcessPublish, NewProcessFinish,
    NewContainerEnter { range: VaRange4K, funding: usize, process_quota: usize, transfer_cpu: CpuId, regs: Registers }, NewContainerPublish, NewContainerFinish,
    Share4kDirectory, Share4kLeaf,
    IpcBlock { channel_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, regs: Registers, flushed_default_pcid: bool },
    IpcRendezvous { channel_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad },
    IpcEndpointTransit { channel_index: EndpointIdx, waiting_state: ThreadState, payload_index: EndpointIdx }, IpcEndpointFinish,
    IpcPagesEnter { channel_index: EndpointIdx, waiting_state: ThreadState, range: VaRange4K }, IpcPagesLockTables, IpcPagesCheck, IpcPagesUnlockTables,
    IpcPagesFinish,
}

/// `new_u` follows `old_u` by the step `label` on cpu `cpu_id`.
pub open spec fn labeled_step(label: StepLabel, old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    match label {
        StepLabel::Mmap4kEnter { range } => mmap_4k_enter_step_pre(old_u, cpu_id, range) && mmap_4k_enter_step(old_u, new_u, cpu_id, range),
        StepLabel::Mmap4kDirectory => mmap_4k_directory_step_pre(old_u, cpu_id) && mmap_4k_directory_step(old_u, new_u, cpu_id),
        StepLabel::Mmap4kLeaf => mmap_4k_leaf_step_pre(old_u, cpu_id) && mmap_4k_leaf_step(old_u, new_u, cpu_id),
        StepLabel::Mmap4kExit => mmap_4k_exit_step_pre(old_u, cpu_id) && mmap_4k_exit_step(old_u, new_u, cpu_id),
        StepLabel::Unmap4kEnter { range } => unmap_4k_enter_step_pre(old_u, cpu_id, range) && unmap_4k_enter_step(old_u, new_u, cpu_id, range),
        StepLabel::Unmap4kLeaf => unmap_4k_leaf_step_pre(old_u, cpu_id) && unmap_4k_leaf_step(old_u, new_u, cpu_id),
        StepLabel::Unmap4kTlbCleared { pcid } => unmap_4k_flush_step_pre(old_u, cpu_id) && kernel_u_cpu_tlb_cleared(old_u, new_u, pcid),
        StepLabel::Unmap4kFlushed => unmap_4k_flush_step_pre(old_u, cpu_id) && unmap_4k_flushed_step(old_u, new_u, cpu_id),
        StepLabel::Unmap4kRefund => unmap_4k_refund_step_pre(old_u, cpu_id)
            && kernel_u_container_quota_4k_increased(old_u, new_u, old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0].owning_container),
        StepLabel::Unmap4kExit => unmap_4k_exit_step_pre(old_u, cpu_id) && unmap_4k_exit_step(old_u, new_u, cpu_id),
        StepLabel::AllocQuota4k { alloc_amount } => alloc_quota_4k_step_pre(old_u, cpu_id, alloc_amount) && alloc_quota_4k_step(old_u, new_u, cpu_id, alloc_amount),
        StepLabel::Schedule { entry_regs, flushed_pcid } => schedule_step_pre(old_u, cpu_id) && schedule_step(old_u, new_u, cpu_id, entry_regs, flushed_pcid),
        StepLabel::NewThreadEnter { regs, endpoint_index } =>
            new_thread_enter_step_pre(old_u, cpu_id, endpoint_index) && new_thread_enter_step(old_u, new_u, cpu_id, regs, endpoint_index),
        StepLabel::NewThreadFinish => new_thread_finish_step_pre(old_u, cpu_id) && new_thread_finish_step(old_u, new_u, cpu_id),
        StepLabel::NewProcessEnter { range, regs, endpoint_index, with_iommu } => new_process_enter_step_pre(old_u, cpu_id, range, endpoint_index, with_iommu)
            && new_process_enter_step(old_u, new_u, cpu_id, range, regs, endpoint_index, with_iommu),
        StepLabel::NewProcessPublish => new_process_publish_step_pre(old_u, cpu_id) && new_process_publish_step(old_u, new_u, cpu_id),
        StepLabel::NewProcessFinish => new_process_finish_step_pre(old_u, cpu_id) && new_process_finish_step(old_u, new_u, cpu_id),
        StepLabel::NewContainerEnter { range, funding, process_quota, transfer_cpu, regs } =>
            new_container_enter_step_pre(old_u, cpu_id, range, funding, process_quota, transfer_cpu)
            && new_container_enter_step(old_u, new_u, cpu_id, range, funding, process_quota, transfer_cpu, regs),
        StepLabel::NewContainerPublish => new_container_publish_step_pre(old_u, cpu_id) && new_container_publish_step(old_u, new_u, cpu_id),
        StepLabel::NewContainerFinish => new_container_finish_step_pre(old_u, cpu_id) && new_container_finish_step(old_u, new_u, cpu_id),
        StepLabel::Share4kDirectory => share_4k_directory_step_pre(old_u, cpu_id) && share_4k_directory_step(old_u, new_u, cpu_id),
        StepLabel::Share4kLeaf => share_4k_leaf_step_pre(old_u, cpu_id) && share_4k_leaf_step(old_u, new_u, cpu_id),
        StepLabel::IpcBlock { channel_index, waiting_state, payload, regs, flushed_default_pcid } => ipc_block_step_pre(old_u, cpu_id, channel_index, waiting_state)
            && ipc_block_step(old_u, new_u, cpu_id, channel_index, waiting_state, payload, regs, flushed_default_pcid),
        StepLabel::IpcRendezvous { channel_index, waiting_state, payload } => ipc_rendezvous_step_pre(old_u, cpu_id, channel_index, waiting_state, payload)
            && ipc_rendezvous_step(old_u, new_u, cpu_id, channel_index, waiting_state, payload),
        StepLabel::IpcEndpointTransit { channel_index, waiting_state, payload_index } =>
            ipc_endpoint_transit_step_pre(old_u, cpu_id, channel_index, waiting_state, payload_index)
            && ipc_endpoint_transit_step(old_u, new_u, cpu_id, channel_index, waiting_state, payload_index),
        StepLabel::IpcEndpointFinish => ipc_endpoint_finish_step_pre(old_u, cpu_id) && ipc_endpoint_finish_step(old_u, new_u, cpu_id),
        StepLabel::IpcPagesEnter { channel_index, waiting_state, range } => ipc_pages_enter_step_pre(old_u, cpu_id, channel_index, waiting_state, range)
            && ipc_pages_enter_step(old_u, new_u, cpu_id, channel_index, waiting_state, range),
        StepLabel::IpcPagesLockTables => ipc_pages_lock_tables_step_pre(old_u, cpu_id) && ipc_pages_lock_tables_step(old_u, new_u, cpu_id),
        StepLabel::IpcPagesCheck => ipc_pages_check_step_pre(old_u, cpu_id) && ipc_pages_check_step(old_u, new_u, cpu_id),
        StepLabel::IpcPagesUnlockTables => ipc_pages_unlock_tables_step_pre(old_u, cpu_id) && ipc_pages_unlock_tables_step(old_u, new_u, cpu_id),
        StepLabel::IpcPagesFinish => ipc_pages_finish_step_pre(old_u, cpu_id) && ipc_pages_finish_step(old_u, new_u, cpu_id),
    }
}

/// Isolation is symmetric in its two domains.
pub proof fn isolated_symmetric(u: KernelU, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires isolated(u, a, b),
    ensures isolated(u, b, a),
{}

/// Unwinding over a trace. `us[i + 1]` follows `us[i]`, the user projection of a well-formed kernel, by the
/// step `labels[i]` of cpu `cpus[i]` of domain `steppers[i]`, which is `a` or `b`. When a step receives an
/// endpoint or shares a page from a peer outside its domain, that peer is honest: the other domain neither
/// holds nor waits on the endpoint, no peer of a rendezvous the other domain has in flight waits on it, and
/// the other domain maps no copy of the page. Then `us[n]` is isolated, and steps of `a` from `us[m]` to
/// `us[n]` leave the view of `b` unchanged.
pub proof fn trace_ni_at(
    us: Seq<KernelU>, labels: Seq<StepLabel>, cpus: Seq<CpuId>, steppers: Seq<RwLockContainerPtr>, a: RwLockContainerPtr, b: RwLockContainerPtr, m: int, n: int,
)
    requires
        us.len() == labels.len() + 1, cpus.len() == labels.len(), steppers.len() == labels.len(), 0 <= n < us.len(), isolated(us[0], a, b),
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
            &&& steps_in_domain(u, cpus[i], x)
            &&& labeled_step(labels[i], u, us[i + 1], cpus[i])
            &&& labels[i] is IpcEndpointFinish && !progress->IpcEndpoint_caller_sends && !in_domain(u, x, u.thread_map[peer].owning_container) ==> {
                &&& forall|t: RwLockThreadPtr, j: EndpointIdx| #![trigger u.endpoint_map[payload].owning_threads.contains((t, j))]
                    u.endpoint_map[payload].owning_threads.contains((t, j)) ==> !in_domain(u, y, u.thread_map[t].owning_container)
                &&& forall|j: int| #![trigger u.endpoint_map[payload].queue[j]]
                    0 <= j < u.endpoint_map[payload].queue.len() ==> !in_domain(u, y, u.thread_map[u.endpoint_map[payload].queue[j]].owning_container)
                &&& forall|t: RwLockThreadPtr| #![trigger u.thread_map[t].syscall_progress]
                    u.thread_map.dom().contains(t) && in_domain(u, y, u.thread_map[t].owning_container) && progress_peer(u.thread_map[t].syscall_progress) is Some
                    ==> u.thread_map[progress_peer(u.thread_map[t].syscall_progress)->Some_0].blocking_endpoint_ptr != Some(payload)
            }
            &&& labels[i] is Share4kLeaf && !in_domain(u, x, u.process_map[source].owning_container) ==> forall|q: RwLockProcessPtr, v: VAddr|
                #![trigger u.process_map[q].pagetable->Some_0.mapping_4k[v]]
                u.process_map.dom().contains(q) && in_domain(u, y, u.process_map[q].owning_container) && u.process_map[q].pagetable is Some
                && u.process_map[q].pagetable->Some_0.mapping_4k.dom().contains(v)
                ==> u.process_map[q].pagetable->Some_0.mapping_4k[v].addr
                    != u.process_map[source].pagetable->Some_0.mapping_4k[progress->Share4k_source_range.view()[progress->Share4k_shared as int]].addr
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
            StepLabel::Mmap4kEnter { range } => { mmap_4k_enter_step_lr(old_u, new_u, cpu_id, range, x, y); mmap_4k_enter_step_iso(old_u, new_u, cpu_id, range, x, y); },
            StepLabel::Mmap4kDirectory => { mmap_4k_directory_step_lr(old_u, new_u, cpu_id, x, y); mmap_4k_directory_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::Mmap4kLeaf => { mmap_4k_leaf_step_lr(old_u, new_u, cpu_id, x, y); mmap_4k_leaf_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::Mmap4kExit => { mmap_4k_exit_step_lr(old_u, new_u, cpu_id, x, y); mmap_4k_exit_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::Unmap4kEnter { range } => { unmap_4k_enter_step_lr(old_u, new_u, cpu_id, range, x, y); unmap_4k_enter_step_iso(old_u, new_u, cpu_id, range, x, y); },
            StepLabel::Unmap4kLeaf => { unmap_4k_leaf_step_lr(old_u, new_u, cpu_id, x, y); unmap_4k_leaf_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::Unmap4kTlbCleared { pcid } => {
                unmap_4k_tlb_cleared_step_lr(old_u, new_u, cpu_id, pcid, x, y); unmap_4k_tlb_cleared_step_iso(old_u, new_u, cpu_id, pcid, x, y);
            },
            StepLabel::Unmap4kFlushed => { unmap_4k_flushed_step_lr(old_u, new_u, cpu_id, x, y); unmap_4k_flushed_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::Unmap4kRefund => { unmap_4k_refund_step_lr(old_u, new_u, cpu_id, x, y); unmap_4k_refund_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::Unmap4kExit => { unmap_4k_exit_step_lr(old_u, new_u, cpu_id, x, y); unmap_4k_exit_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::AllocQuota4k { alloc_amount } => {
                alloc_quota_4k_step_lr(old_u, new_u, cpu_id, alloc_amount, x, y); alloc_quota_4k_step_iso(old_u, new_u, cpu_id, alloc_amount, x, y);
            },
            StepLabel::Schedule { entry_regs, flushed_pcid } => {
                schedule_step_lr(old_u, new_u, cpu_id, entry_regs, flushed_pcid, x, y); schedule_step_iso(old_u, new_u, cpu_id, entry_regs, flushed_pcid, x, y);
            },
            StepLabel::NewThreadEnter { regs, endpoint_index } => {
                new_thread_enter_step_lr(old_u, new_u, cpu_id, regs, endpoint_index, x, y); new_thread_enter_step_iso(old_u, new_u, cpu_id, regs, endpoint_index, x, y);
            },
            StepLabel::NewThreadFinish => { new_thread_finish_step_lr(old_u, new_u, cpu_id, x, y); new_thread_finish_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::NewProcessEnter { range, regs, endpoint_index, with_iommu } => {
                new_process_enter_step_lr(old_u, new_u, cpu_id, range, regs, endpoint_index, with_iommu, x, y);
                new_process_enter_step_iso(old_u, new_u, cpu_id, range, regs, endpoint_index, with_iommu, x, y);
            },
            StepLabel::NewProcessPublish => { new_process_publish_step_lr(old_u, new_u, cpu_id, x, y); new_process_publish_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::NewProcessFinish => { new_process_finish_step_lr(old_u, new_u, cpu_id, x, y); new_process_finish_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::NewContainerEnter { range, funding, process_quota, transfer_cpu, regs } => {
                new_container_enter_step_lr(old_u, new_u, cpu_id, range, funding, process_quota, transfer_cpu, regs, x, y);
                new_container_enter_step_iso(old_u, new_u, cpu_id, range, funding, process_quota, transfer_cpu, regs, x, y);
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
            StepLabel::IpcEndpointTransit { channel_index, waiting_state, payload_index } => {
                ipc_endpoint_transit_step_lr(old_u, new_u, cpu_id, channel_index, waiting_state, payload_index, x, y);
                ipc_endpoint_transit_step_iso(old_u, new_u, cpu_id, channel_index, waiting_state, payload_index, x, y);
            },
            StepLabel::IpcEndpointFinish => {
                ipc_endpoint_finish_step_lr(old_u, new_u, cpu_id, peer, payload, x, y); ipc_endpoint_finish_step_iso(old_u, new_u, cpu_id, peer, payload, x, y);
            },
            StepLabel::IpcPagesEnter { channel_index, waiting_state, range } => {
                ipc_pages_enter_step_lr(old_u, new_u, cpu_id, channel_index, waiting_state, range, x, y);
                ipc_pages_enter_step_iso(old_u, new_u, cpu_id, channel_index, waiting_state, range, x, y);
            },
            StepLabel::IpcPagesLockTables => { ipc_pages_lock_tables_step_lr(old_u, new_u, cpu_id, x, y); ipc_pages_lock_tables_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::IpcPagesCheck => { ipc_pages_check_step_lr(old_u, new_u, cpu_id, x, y); ipc_pages_check_step_iso(old_u, new_u, cpu_id, x, y); },
            StepLabel::IpcPagesUnlockTables => {
                ipc_pages_unlock_tables_step_lr(old_u, new_u, cpu_id, x, y); ipc_pages_unlock_tables_step_iso(old_u, new_u, cpu_id, x, y);
            },
            StepLabel::IpcPagesFinish => { ipc_pages_finish_step_lr(old_u, new_u, cpu_id, x, y); ipc_pages_finish_step_iso(old_u, new_u, cpu_id, x, y); },
        }
        if x != a { isolated_symmetric(new_u, b, a); }
    }
}
} // verus!
