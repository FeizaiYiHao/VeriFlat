use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::implementation::create_thread_from_staged_page::kernel_u_new_thread_changed;

/// K->U projection lemmas for lock-state, scheduling, process-table, container-publication, and peer-wakeup steps.
pub mod projection;
/// K->U point projections of single cpu, container, process, thread, endpoint, and page-table entries.
pub mod projection_at;
/// K->U projection lemmas for IPC dequeue, lock-mode changes, and the IPC block, call, accept, reply, and rendezvous steps.
pub mod projection_ipc;
/// K->U projection lemmas for process and thread publication, thread quota changes, and copied 4K mappings.
pub mod projection_publish;
/// K->U lemmas for quota, cpu, TLB, mapping, and lock-mode steps.
pub mod boundary;
/// Step-boundary wrappers of `KernelK` that record one section in `KernelSteps`.
pub mod boundary_steps;
/// K->U lemmas for endpoint creation, thread exit, caller wakeup, and descriptor release steps.
pub mod boundary_endpoint_thread_exit;
/// `KernelSteps` recorders of the IPC block, call, accept, reply, and rendezvous steps.
pub mod end_kernel_step_ipc;
/// `KernelSteps` recorders of the quota, cpu offline/online, PCI attach, and cpu-off steps.
pub mod end_kernel_step_quota_cpu;
/// K->U equalities of sections that only release locks.
pub mod release;
/// K->U lemmas for the steps that reclaim write-held killed threads or release the reclaiming cpu and thread, and the
/// lock-mode projections of held processes and containers.
pub mod killed_thread;
/// K->U lemmas for the steps of killing a process subtree.
pub mod kill;
/// K->U lemmas for the steps that reclaim an empty process during a kill.
pub mod kill_reclaim;
/// K->U lemmas for the step that retires an empty zombie process during a kill.
pub mod kill_retire;
/// K->U lemmas for the steps of killing a container subtree.
pub mod kill_container;
/// K->U lemmas for the step that retires an empty marked container.
pub mod kill_container_retire;
/// K->U lemmas for the steps that move a marked container's free pages to the killer's container.
pub mod kill_container_pages;
/// K->U lemmas for the steps that move a marked container's cpus to the killer's container.
pub mod kill_container_cpus;
/// K->U lemmas for the steps that enter and walk a container kill.
pub mod kill_container_walk;
/// Generic K->U bindings of projected entries, the stored snapshot, and root-table detaches.
pub mod bindings;
/// K->U lemmas for the step that releases an endpoint with its last descriptor.
pub mod endpoint_release;
/// Per-map K->U lemmas of the IPC block and call-handoff, cpu-off, thread-quota, and lock-mode steps.
pub mod per_map_projection;
/// Per-map K->U lemmas of unchanged maps and of the steps that reclaim or retire a process during a kill.
pub mod kill_per_map_projection;
/// Per-map K->U lemmas of the cpu-and-page-owner step and the process-table lock-state-and-progress step.
pub mod owner_and_tables_per_map_projection;
/// Per-entry and domain K->U lemmas of the unwrapped user projection `kernel_k_user_projection`.
pub mod user_projection_at;
/// K->U lemmas of read-mode page-table steps: held-window mappings, read-mode entry and exit, and downgrade.
pub mod pagetable_read_mode;
pub mod new_process_read_mode;
pub mod ipc_pages_tables;
/// K->U lemmas of IOMMU-table leaf publication and global IOTLB flush steps.
pub mod iommu_table_steps;
/// K->U lemmas of hardware TLB, IOTLB, and context-cache fills and of the TLB contents a CPU or the IOTLB may hold.
pub mod env_steps;
/// K->U lemma of a step that changes only one live process's page-table window locks.
pub mod pagetable_window_locks;

pub use projection::*;
pub use projection_at::*;
pub use projection_ipc::*;
pub use projection_publish::*;
pub use boundary::*;
pub use boundary_steps::*;
pub use boundary_endpoint_thread_exit::*;
pub use release::*;
pub use killed_thread::*;
pub use kill::*;
pub use kill_reclaim::*;
pub use kill_retire::*;
pub use kill_container::*;
pub use kill_container_retire::*;
pub use kill_container_pages::*;
pub use kill_container_cpus::*;
pub use kill_container_walk::*;
pub use bindings::*;
pub use endpoint_release::*;
pub use per_map_projection::*;
pub use kill_per_map_projection::*;
pub use owner_and_tables_per_map_projection::*;
pub use user_projection_at::*;
pub use pagetable_read_mode::*;
pub use new_process_read_mode::*;
pub use ipc_pages_tables::*;
pub use iommu_table_steps::*;
pub use env_steps::*;
pub use pagetable_window_locks::*;

verus! {
/// Each boundary refreshes both stored snapshots after recording its own section.
/// Rebasing K preserves the stored U projection and records no step.
pub tracked struct KernelSteps {
    ghost steps: Seq<KernelStep>,
    ghost snapshot_k: KernelK,
    ghost snapshot_u: KernelU,
}

impl KernelSteps {
    pub closed spec fn view(&self) -> Seq<KernelStep> { self.steps }
    pub closed spec fn snapshot_k(&self) -> KernelK { self.snapshot_k }
    pub closed spec fn snapshot_u(&self) -> KernelU { self.snapshot_u }

    #[verifier::type_invariant]
    pub open spec fn snapshots_consistent(&self) -> bool {
        self.snapshot_u() == kernel_k_to_kernel_u(self.snapshot_k())
    }

    pub proof fn new(krnl: &KernelK) -> (tracked ret: Self)
        ensures
            ret.view() == Seq::<KernelStep>::empty(),
            ret.snapshot_k() == *krnl,
            ret.snapshot_u() == kernel_k_to_kernel_u(*krnl),
    {
        KernelSteps { steps: Seq::empty(), snapshot_k: *krnl, snapshot_u: kernel_k_to_kernel_u(*krnl) }
    }

    /// Refresh K only if the complete projection still matches; otherwise retain
    /// the pending lock-mode transition for the next recording boundary.
    pub proof fn rebase_snapshot_k_if_unchanged(tracked &mut self, krnl: &KernelK)
        requires
            krnl.inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(self).snapshot_k(), krnl),
            kernel_endpoint_nonlock_fields_unchanged(old(self).snapshot_k().ep_mp, krnl.ep_mp),
            krnl.irt.view().owners() == old(self).snapshot_k().irt.view().owners(),
            krnl.irt.view().iommu_roots() == old(self).snapshot_k().irt.view().iommu_roots(),
            krnl.cpu_tlb.view() == old(self).snapshot_k().cpu_tlb.view(),
            krnl.iommu_tlb.view() == old(self).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(self).snapshot_k(), krnl),
        ensures
            final(self).view() == old(self).view(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).snapshot_u() == old(self).snapshot_u(),
            final(self).snapshot_u() == kernel_k_to_kernel_u(final(self).snapshot_k()),
            krnl.irt.view().owners() == final(self).snapshot_k().irt.view().owners(),
            krnl.irt.view().iommu_roots() == final(self).snapshot_k().irt.view().iommu_roots(),
            krnl.cpu_tlb.view() == final(self).snapshot_k().cpu_tlb.view(),
            krnl.iommu_tlb.view() == final(self).snapshot_k().iommu_tlb.view(),
            final(self).snapshot_k() == if old(self).snapshot_u() == kernel_k_to_kernel_u(*krnl) { *krnl } else { old(self).snapshot_k() },
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(self).snapshot_k(), krnl),
            kernel_endpoint_nonlock_fields_unchanged(final(self).snapshot_k().ep_mp, krnl.ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(self).snapshot_k(), krnl),
    {
        use_type_invariant(&*self);
        if self.snapshot_u() == kernel_k_to_kernel_u(*krnl) {
            *self = KernelSteps { steps: self.steps, snapshot_k: *krnl, snapshot_u: self.snapshot_u };
            kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*self, krnl);
        }
    }

    /// Strict stuttering boundary: the premises mention only K fields and lock modes.
    pub proof fn end_kernel_step_restored_locks(
        tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu: CpuId,
        container: Option<RwLockContainerPtr>, process: Option<RwLockProcessPtr>, thread: Option<RwLockThreadPtr>,
        endpoint: Option<RwLockEndpointPtr>, table: Option<RwLockPageTableRoot>, allocator: Option<RwLockPcidAllocatorPtr>,
    )
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            krnl.irt.view().owners() == old(self).snapshot_k().irt.view().owners(),
            krnl.irt.view().iommu_roots() == old(self).snapshot_k().irt.view().iommu_roots(),
            krnl.cpu_tlb.view() == old(self).snapshot_k().cpu_tlb.view(),
            krnl.iommu_tlb.view() == old(self).snapshot_k().iommu_tlb.view(),
            krnl.cpu_op.view().view() == old(self).snapshot_k().cpu_op.view().view(),
            krnl.dflt_pt == old(self).snapshot_k().dflt_pt,
            krnl.cpu_arr.entries_unchanged_except(&old(self).snapshot_k().cpu_arr, cpu),
            krnl.cpu_arr.spec_index(cpu).view().view().view() == old(self).snapshot_k().cpu_arr.spec_index(cpu).view().view().view(),
            krnl.cpu_arr.spec_index(cpu).value.killer_info() == old(self).snapshot_k().cpu_arr.spec_index(cpu).value.killer_info(),
            (krnl.cpu_arr.spec_index(cpu).value.locking_thread() is Write) == (old(self).snapshot_k().cpu_arr.spec_index(cpu).value.locking_thread() is Write),
            (krnl.cpu_arr.spec_index(cpu).value.locking_thread() is Read) == (old(self).snapshot_k().cpu_arr.spec_index(cpu).value.locking_thread() is Read),
            krnl.it_mp == old(self).snapshot_k().it_mp,
            krnl.cpu_set_mp == old(self).snapshot_k().cpu_set_mp,
            krnl.sched_mp == old(self).snapshot_k().sched_mp,
            krnl.allc_4k_mp == old(self).snapshot_k().allc_4k_mp,
            krnl.allc_2m_mp == old(self).snapshot_k().allc_2m_mp,
            krnl.allc_1g_mp == old(self).snapshot_k().allc_1g_mp,
            krnl.cpu_offline_mp == old(self).snapshot_k().cpu_offline_mp,
            match allocator {
                Some(p) => {
                    &&& krnl.pcid_allc_mp.unchanged_except(&old(self).snapshot_k().pcid_allc_mp, p)
                    &&& krnl.pcid_allc_mp.spec_index(p).view() == old(self).snapshot_k().pcid_allc_mp.spec_index(p).view()
                },
                None => krnl.pcid_allc_mp == old(self).snapshot_k().pcid_allc_mp,
            },
            match container {
                Some(p) => {
                    &&& krnl.ctn_mp.unchanged_except(&old(self).snapshot_k().ctn_mp, p)
                    &&& krnl.ctn_mp.spec_index(p).view() == old(self).snapshot_k().ctn_mp.spec_index(p).view()
                    &&& krnl.ctn_mp.spec_index(p).view_rodata() == old(self).snapshot_k().ctn_mp.spec_index(p).view_rodata()
                    &&& krnl.ctn_mp.spec_index(p).view_ghost() == old(self).snapshot_k().ctn_mp.spec_index(p).view_ghost()
                    &&& krnl.ctn_mp.spec_index(p).being_killed() == old(self).snapshot_k().ctn_mp.spec_index(p).being_killed()
                    &&& (krnl.ctn_mp.spec_index(p).locking_thread() is Write) == (old(self).snapshot_k().ctn_mp.spec_index(p).locking_thread() is Write)
                    &&& (krnl.ctn_mp.spec_index(p).locking_thread() is Read) == (old(self).snapshot_k().ctn_mp.spec_index(p).locking_thread() is Read)
                    &&& krnl.ctn_mp.spec_index(p).lock_process_owner_u() == old(self).snapshot_k().ctn_mp.spec_index(p).lock_process_owner_u()
                },
                None => krnl.ctn_mp == old(self).snapshot_k().ctn_mp,
            },
            match process {
                Some(p) => {
                    &&& krnl.prc_mp.unchanged_except(&old(self).snapshot_k().prc_mp, p)
                    &&& krnl.prc_mp.spec_index(p).view() == old(self).snapshot_k().prc_mp.spec_index(p).view()
                    &&& krnl.prc_mp.spec_index(p).view_rodata() == old(self).snapshot_k().prc_mp.spec_index(p).view_rodata()
                    &&& krnl.prc_mp.spec_index(p).view_ghost() == old(self).snapshot_k().prc_mp.spec_index(p).view_ghost()
                    &&& krnl.prc_mp.spec_index(p).being_killed() == old(self).snapshot_k().prc_mp.spec_index(p).being_killed()
                    &&& (krnl.prc_mp.spec_index(p).locking_thread() is Write) == (old(self).snapshot_k().prc_mp.spec_index(p).locking_thread() is Write)
                    &&& (krnl.prc_mp.spec_index(p).locking_thread() is Read) == (old(self).snapshot_k().prc_mp.spec_index(p).locking_thread() is Read)
                },
                None => krnl.prc_mp == old(self).snapshot_k().prc_mp,
            },
            match thread {
                Some(p) => {
                    &&& krnl.thr_mp.unchanged_except(&old(self).snapshot_k().thr_mp, p)
                    &&& krnl.thr_mp.spec_index(p).view() == old(self).snapshot_k().thr_mp.spec_index(p).view()
                    &&& krnl.thr_mp.spec_index(p).being_killed() == old(self).snapshot_k().thr_mp.spec_index(p).being_killed()
                    &&& (krnl.thr_mp.spec_index(p).locking_thread() is Write) == (old(self).snapshot_k().thr_mp.spec_index(p).locking_thread() is Write)
                    &&& (krnl.thr_mp.spec_index(p).locking_thread() is Read) == (old(self).snapshot_k().thr_mp.spec_index(p).locking_thread() is Read)
                },
                None => krnl.thr_mp == old(self).snapshot_k().thr_mp,
            },
            match endpoint {
                Some(p) => {
                    &&& krnl.ep_mp.unchanged_except(&old(self).snapshot_k().ep_mp, p)
                    &&& krnl.ep_mp.spec_index(p).view() == old(self).snapshot_k().ep_mp.spec_index(p).view()
                    &&& krnl.ep_mp.spec_index(p).being_killed() == old(self).snapshot_k().ep_mp.spec_index(p).being_killed()
                    &&& (krnl.ep_mp.spec_index(p).locking_thread() is Write) == (old(self).snapshot_k().ep_mp.spec_index(p).locking_thread() is Write)
                    &&& (krnl.ep_mp.spec_index(p).locking_thread() is Read) == (old(self).snapshot_k().ep_mp.spec_index(p).locking_thread() is Read)
                },
                None => krnl.ep_mp == old(self).snapshot_k().ep_mp,
            },
            match table {
                Some(p) => {
                    &&& krnl.pt_mp.unchanged_except(&old(self).snapshot_k().pt_mp, p)
                    &&& krnl.pt_mp.spec_index(p).view() == old(self).snapshot_k().pt_mp.spec_index(p).view()
                    &&& (krnl.pt_mp.spec_index(p).locking_thread() is Write) == (old(self).snapshot_k().pt_mp.spec_index(p).locking_thread() is Write)
                    &&& (krnl.pt_mp.spec_index(p).locking_thread() is Read) == (old(self).snapshot_k().pt_mp.spec_index(p).locking_thread() is Read)
                    &&& forall|q: RwLockPageTableRoot| #![trigger krnl.pt_lower.view().spec_index(q)] q != p ==> krnl.pt_lower.view().spec_index(q) == old(self).snapshot_k().pt_lower.view().spec_index(q)
                    &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), p).mapping_4k() == pagetable_c(old(self).snapshot_k().pt_mp, old(self).snapshot_k().pt_lower.view(), p).mapping_4k()
                    &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), p).mapping_2m() == pagetable_c(old(self).snapshot_k().pt_mp, old(self).snapshot_k().pt_lower.view(), p).mapping_2m()
                    &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), p).mapping_1g() == pagetable_c(old(self).snapshot_k().pt_mp, old(self).snapshot_k().pt_lower.view(), p).mapping_1g()
                    &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), p).lower.pagetable_window_locks == pagetable_c(old(self).snapshot_k().pt_mp, old(self).snapshot_k().pt_lower.view(), p).lower.pagetable_window_locks
                },
                None => {
                    &&& krnl.pt_mp == old(self).snapshot_k().pt_mp
                    &&& krnl.pt_lower == old(self).snapshot_k().pt_lower
                },
            },
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == old(self).snapshot_u(),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).snapshot_k() == *krnl,
            kernel_endpoint_nonlock_fields_unchanged(final(self).snapshot_k().ep_mp, krnl.ep_mp),
    {
        self.end_kernel_step_restored_locks_with_iommu_table(krnl, lctx, cpu, container, process, thread, endpoint, table, allocator, None);
    }

    /// `end_kernel_step_restored_locks` with one IOMMU table whose lock/unlock cycle restored its payload and lock mode.
    pub proof fn end_kernel_step_restored_locks_with_iommu_table(
        tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu: CpuId,
        container: Option<RwLockContainerPtr>, process: Option<RwLockProcessPtr>, thread: Option<RwLockThreadPtr>,
        endpoint: Option<RwLockEndpointPtr>, table: Option<RwLockPageTableRoot>, allocator: Option<RwLockPcidAllocatorPtr>,
        iommu_table: Option<RwLockPageTableRoot>,
    )
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            krnl.irt.view().owners() == old(self).snapshot_k().irt.view().owners(),
            krnl.irt.view().iommu_roots() == old(self).snapshot_k().irt.view().iommu_roots(),
            krnl.cpu_tlb.view() == old(self).snapshot_k().cpu_tlb.view(),
            krnl.iommu_tlb.view() == old(self).snapshot_k().iommu_tlb.view(),
            krnl.cpu_op.view().view() == old(self).snapshot_k().cpu_op.view().view(),
            krnl.dflt_pt == old(self).snapshot_k().dflt_pt,
            krnl.cpu_arr.entries_unchanged_except(&old(self).snapshot_k().cpu_arr, cpu),
            krnl.cpu_arr.spec_index(cpu).view().view().view() == old(self).snapshot_k().cpu_arr.spec_index(cpu).view().view().view(),
            krnl.cpu_arr.spec_index(cpu).value.killer_info() == old(self).snapshot_k().cpu_arr.spec_index(cpu).value.killer_info(),
            (krnl.cpu_arr.spec_index(cpu).value.locking_thread() is Write) == (old(self).snapshot_k().cpu_arr.spec_index(cpu).value.locking_thread() is Write),
            (krnl.cpu_arr.spec_index(cpu).value.locking_thread() is Read) == (old(self).snapshot_k().cpu_arr.spec_index(cpu).value.locking_thread() is Read),
            match iommu_table {
                Some(p) => {
                    &&& krnl.it_mp.unchanged_except(&old(self).snapshot_k().it_mp, p)
                    &&& krnl.it_mp.spec_index(p).view() == old(self).snapshot_k().it_mp.spec_index(p).view()
                    &&& (krnl.it_mp.spec_index(p).locking_thread() is Write) == (old(self).snapshot_k().it_mp.spec_index(p).locking_thread() is Write)
                    &&& (krnl.it_mp.spec_index(p).locking_thread() is Read) == (old(self).snapshot_k().it_mp.spec_index(p).locking_thread() is Read)
                },
                None => krnl.it_mp == old(self).snapshot_k().it_mp,
            },
            krnl.cpu_set_mp == old(self).snapshot_k().cpu_set_mp,
            krnl.sched_mp == old(self).snapshot_k().sched_mp,
            krnl.allc_4k_mp == old(self).snapshot_k().allc_4k_mp,
            krnl.allc_2m_mp == old(self).snapshot_k().allc_2m_mp,
            krnl.allc_1g_mp == old(self).snapshot_k().allc_1g_mp,
            krnl.cpu_offline_mp == old(self).snapshot_k().cpu_offline_mp,
            match allocator {
                Some(p) => {
                    &&& krnl.pcid_allc_mp.unchanged_except(&old(self).snapshot_k().pcid_allc_mp, p)
                    &&& krnl.pcid_allc_mp.spec_index(p).view() == old(self).snapshot_k().pcid_allc_mp.spec_index(p).view()
                },
                None => krnl.pcid_allc_mp == old(self).snapshot_k().pcid_allc_mp,
            },
            match container {
                Some(p) => {
                    &&& krnl.ctn_mp.unchanged_except(&old(self).snapshot_k().ctn_mp, p)
                    &&& krnl.ctn_mp.spec_index(p).view() == old(self).snapshot_k().ctn_mp.spec_index(p).view()
                    &&& krnl.ctn_mp.spec_index(p).view_rodata() == old(self).snapshot_k().ctn_mp.spec_index(p).view_rodata()
                    &&& krnl.ctn_mp.spec_index(p).view_ghost() == old(self).snapshot_k().ctn_mp.spec_index(p).view_ghost()
                    &&& krnl.ctn_mp.spec_index(p).being_killed() == old(self).snapshot_k().ctn_mp.spec_index(p).being_killed()
                    &&& (krnl.ctn_mp.spec_index(p).locking_thread() is Write) == (old(self).snapshot_k().ctn_mp.spec_index(p).locking_thread() is Write)
                    &&& (krnl.ctn_mp.spec_index(p).locking_thread() is Read) == (old(self).snapshot_k().ctn_mp.spec_index(p).locking_thread() is Read)
                    &&& krnl.ctn_mp.spec_index(p).lock_process_owner_u() == old(self).snapshot_k().ctn_mp.spec_index(p).lock_process_owner_u()
                },
                None => krnl.ctn_mp == old(self).snapshot_k().ctn_mp,
            },
            match process {
                Some(p) => {
                    &&& krnl.prc_mp.unchanged_except(&old(self).snapshot_k().prc_mp, p)
                    &&& krnl.prc_mp.spec_index(p).view() == old(self).snapshot_k().prc_mp.spec_index(p).view()
                    &&& krnl.prc_mp.spec_index(p).view_rodata() == old(self).snapshot_k().prc_mp.spec_index(p).view_rodata()
                    &&& krnl.prc_mp.spec_index(p).view_ghost() == old(self).snapshot_k().prc_mp.spec_index(p).view_ghost()
                    &&& krnl.prc_mp.spec_index(p).being_killed() == old(self).snapshot_k().prc_mp.spec_index(p).being_killed()
                    &&& (krnl.prc_mp.spec_index(p).locking_thread() is Write) == (old(self).snapshot_k().prc_mp.spec_index(p).locking_thread() is Write)
                    &&& (krnl.prc_mp.spec_index(p).locking_thread() is Read) == (old(self).snapshot_k().prc_mp.spec_index(p).locking_thread() is Read)
                },
                None => krnl.prc_mp == old(self).snapshot_k().prc_mp,
            },
            match thread {
                Some(p) => {
                    &&& krnl.thr_mp.unchanged_except(&old(self).snapshot_k().thr_mp, p)
                    &&& krnl.thr_mp.spec_index(p).view() == old(self).snapshot_k().thr_mp.spec_index(p).view()
                    &&& krnl.thr_mp.spec_index(p).being_killed() == old(self).snapshot_k().thr_mp.spec_index(p).being_killed()
                    &&& (krnl.thr_mp.spec_index(p).locking_thread() is Write) == (old(self).snapshot_k().thr_mp.spec_index(p).locking_thread() is Write)
                    &&& (krnl.thr_mp.spec_index(p).locking_thread() is Read) == (old(self).snapshot_k().thr_mp.spec_index(p).locking_thread() is Read)
                },
                None => krnl.thr_mp == old(self).snapshot_k().thr_mp,
            },
            match endpoint {
                Some(p) => {
                    &&& krnl.ep_mp.unchanged_except(&old(self).snapshot_k().ep_mp, p)
                    &&& krnl.ep_mp.spec_index(p).view() == old(self).snapshot_k().ep_mp.spec_index(p).view()
                    &&& krnl.ep_mp.spec_index(p).being_killed() == old(self).snapshot_k().ep_mp.spec_index(p).being_killed()
                    &&& (krnl.ep_mp.spec_index(p).locking_thread() is Write) == (old(self).snapshot_k().ep_mp.spec_index(p).locking_thread() is Write)
                    &&& (krnl.ep_mp.spec_index(p).locking_thread() is Read) == (old(self).snapshot_k().ep_mp.spec_index(p).locking_thread() is Read)
                },
                None => krnl.ep_mp == old(self).snapshot_k().ep_mp,
            },
            match table {
                Some(p) => {
                    &&& krnl.pt_mp.unchanged_except(&old(self).snapshot_k().pt_mp, p)
                    &&& krnl.pt_mp.spec_index(p).view() == old(self).snapshot_k().pt_mp.spec_index(p).view()
                    &&& (krnl.pt_mp.spec_index(p).locking_thread() is Write) == (old(self).snapshot_k().pt_mp.spec_index(p).locking_thread() is Write)
                    &&& (krnl.pt_mp.spec_index(p).locking_thread() is Read) == (old(self).snapshot_k().pt_mp.spec_index(p).locking_thread() is Read)
                    &&& forall|q: RwLockPageTableRoot| #![trigger krnl.pt_lower.view().spec_index(q)] q != p ==> krnl.pt_lower.view().spec_index(q) == old(self).snapshot_k().pt_lower.view().spec_index(q)
                    &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), p).mapping_4k() == pagetable_c(old(self).snapshot_k().pt_mp, old(self).snapshot_k().pt_lower.view(), p).mapping_4k()
                    &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), p).mapping_2m() == pagetable_c(old(self).snapshot_k().pt_mp, old(self).snapshot_k().pt_lower.view(), p).mapping_2m()
                    &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), p).mapping_1g() == pagetable_c(old(self).snapshot_k().pt_mp, old(self).snapshot_k().pt_lower.view(), p).mapping_1g()
                    &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), p).lower.pagetable_window_locks == pagetable_c(old(self).snapshot_k().pt_mp, old(self).snapshot_k().pt_lower.view(), p).lower.pagetable_window_locks
                },
                None => {
                    &&& krnl.pt_mp == old(self).snapshot_k().pt_mp
                    &&& krnl.pt_lower == old(self).snapshot_k().pt_lower
                },
            },
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == old(self).snapshot_u(),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).snapshot_k() == *krnl,
            kernel_endpoint_nonlock_fields_unchanged(final(self).snapshot_k().ep_mp, krnl.ep_mp),
    {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&self.snapshot_k(), krnl)) by {
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
            reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
            reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
        };
        assert(kernel_endpoint_nonlock_fields_unchanged(self.snapshot_k().ep_mp, krnl.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&self.snapshot_k(), krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_pcid_allocator_wf); };
        self.end_kernel_step_unchanged(krnl, lctx);
    }

    pub proof fn end_kernel_step_unchanged(tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext)
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(self).snapshot_k(), krnl),
            kernel_endpoint_nonlock_fields_unchanged(old(self).snapshot_k().ep_mp, krnl.ep_mp),
            krnl.irt.view().owners() == old(self).snapshot_k().irt.view().owners(),
            krnl.irt.view().iommu_roots() == old(self).snapshot_k().irt.view().iommu_roots(),
            krnl.cpu_tlb.view() == old(self).snapshot_k().cpu_tlb.view(),
            krnl.iommu_tlb.view() == old(self).snapshot_k().iommu_tlb.view(),
            krnl.cpu_op.view().view() == old(self).snapshot_k().cpu_op.view().view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(self).snapshot_k(), krnl),
            forall|p: RwLockContainerPtr| #![trigger krnl.ctn_mp.spec_index(p)]
                krnl.ctn_mp.dom().contains(p) && old(self).snapshot_k().ctn_mp.dom().contains(p) ==> {
                    let before = old(self).snapshot_k().ctn_mp.spec_index(p).locking_thread();
                    let after = krnl.ctn_mp.spec_index(p).locking_thread();
                    &&& (after is Write) == (before is Write)
                    &&& (after is Read) == (before is Read)
                    &&& krnl.ctn_mp.spec_index(p).lock_process_owner_u() == old(self).snapshot_k().ctn_mp.spec_index(p).lock_process_owner_u()
                },
            forall|p: RwLockProcessPtr| #![trigger krnl.prc_mp.spec_index(p)]
                krnl.prc_mp.dom().contains(p) && old(self).snapshot_k().prc_mp.dom().contains(p) ==> {
                    let before = old(self).snapshot_k().prc_mp.spec_index(p).locking_thread();
                    let after = krnl.prc_mp.spec_index(p).locking_thread();
                    &&& (after is Write) == (before is Write)
                    &&& (after is Read) == (before is Read)
                },
            forall|p: RwLockPageTableRoot| #![trigger krnl.pt_mp.spec_index(p)]
                krnl.pt_mp.dom().contains(p) && old(self).snapshot_k().pt_mp.dom().contains(p) ==> {
                    let before = old(self).snapshot_k().pt_mp.spec_index(p).locking_thread();
                    let after = krnl.pt_mp.spec_index(p).locking_thread();
                    &&& (after is Write) == (before is Write)
                    &&& (after is Read) == (before is Read)
                    &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), p).lower.pagetable_window_locks == pagetable_c(old(self).snapshot_k().pt_mp, old(self).snapshot_k().pt_lower.view(), p).lower.pagetable_window_locks
                },
            forall|p: RwLockPageTableRoot| #![trigger krnl.it_mp.spec_index(p)]
                krnl.it_mp.dom().contains(p) && old(self).snapshot_k().it_mp.dom().contains(p) ==> {
                    let before = old(self).snapshot_k().it_mp.spec_index(p).locking_thread();
                    let after = krnl.it_mp.spec_index(p).locking_thread();
                    &&& (after is Write) == (before is Write)
                    &&& (after is Read) == (before is Read)
                },
            forall|p: RwLockThreadPtr| #![trigger krnl.thr_mp.spec_index(p)]
                krnl.thr_mp.dom().contains(p) && old(self).snapshot_k().thr_mp.dom().contains(p) ==> {
                    let before = old(self).snapshot_k().thr_mp.spec_index(p).locking_thread();
                    let after = krnl.thr_mp.spec_index(p).locking_thread();
                    &&& (after is Write) == (before is Write)
                    &&& (after is Read) == (before is Read)
                },
            forall|p: RwLockEndpointPtr| #![trigger krnl.ep_mp.spec_index(p)]
                krnl.ep_mp.dom().contains(p) && old(self).snapshot_k().ep_mp.dom().contains(p) ==> {
                    let before = old(self).snapshot_k().ep_mp.spec_index(p).locking_thread();
                    let after = krnl.ep_mp.spec_index(p).locking_thread();
                    &&& (after is Write) == (before is Write)
                    &&& (after is Read) == (before is Read)
                },
            forall|i: CpuId| #![trigger krnl.cpu_arr.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> {
                    let before = old(self).snapshot_k().cpu_arr.spec_index(i).value.locking_thread();
                    let after = krnl.cpu_arr.spec_index(i).value.locking_thread();
                    &&& (after is Write) == (before is Write)
                    &&& (after is Read) == (before is Read)
                },
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == old(self).snapshot_u(),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).snapshot_k() == *krnl,
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(self).snapshot_k(), krnl),
            kernel_endpoint_nonlock_fields_unchanged(final(self).snapshot_k().ep_mp, krnl.ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(self).snapshot_k(), krnl),
    {
        use_type_invariant(&*self);
        assert(self.snapshot_u() == kernel_k_to_kernel_u(*krnl)) by { kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&self.snapshot_k(), krnl); };
        *self = KernelSteps { steps: self.steps, snapshot_k: *krnl, snapshot_u: self.snapshot_u };
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*self, krnl);
    }

    /// Finish without interleaving; append exactly the non-stuttering transition.
    #[verifier::spinoff_prover]
    proof fn end_kernel_step_raw(tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext)
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
        ensures
            final(self).view() == record_user_view_change(old(self).view(), old(self).snapshot_u(), kernel_k_to_kernel_u(*krnl)),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).snapshot_k() == *krnl,
    {
        use_type_invariant(&*self);
        *self = KernelSteps {
            steps: record_user_view_change(self.steps, self.snapshot_u, kernel_k_to_kernel_u(*krnl)),
            snapshot_k: *krnl, snapshot_u: kernel_k_to_kernel_u(*krnl),
        };
        reveal(kernel_steps_prefix_unchanged);
    }

    pub proof fn end_kernel_step_nonlock_fields_unchanged(tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext)
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(self).snapshot_k(), krnl),
            kernel_endpoint_nonlock_fields_unchanged(old(self).snapshot_k().ep_mp, krnl.ep_mp),
            krnl.irt.view().owners() == old(self).snapshot_k().irt.view().owners(),
            krnl.irt.view().iommu_roots() == old(self).snapshot_k().irt.view().iommu_roots(),
            krnl.cpu_tlb.view() == old(self).snapshot_k().cpu_tlb.view(),
            krnl.iommu_tlb.view() == old(self).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(self).snapshot_k(), krnl),
        ensures
            forall|start: int| #![trigger final(self).view().subrange(start, old(self).view().len() as int)]
                0 <= start <= old(self).view().len() ==> final(self).view().subrange(start, old(self).view().len() as int) == old(self).view().subrange(start, old(self).view().len() as int),
            final(self).view() == record_user_view_change(old(self).view(), old(self).snapshot_u(), kernel_k_to_kernel_u(*krnl)),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).snapshot_k() == *krnl,
    {
        use_type_invariant(&*self);
        self.end_kernel_step_raw(krnl, lctx);
    }

    pub proof fn end_kernel_step_new_thread(
        tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
        cpu_id: CpuId, new_thread_ptr: RwLockThreadPtr, initial_regs: Registers, initial_endpoint: Option<RwLockEndpointPtr>, staging_progress: Option<SyscallProgress>,
    )
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_new_thread_fields(&old(self).snapshot_k(), krnl, process_ptr, staging_thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, initial_endpoint, staging_progress),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).snapshot_k() == *krnl,
    {
        use_type_invariant(&*self);
        assert(self.snapshot_u() != kernel_k_to_kernel_u(*krnl)) by { reveal(kernel_new_thread_fields); kernel_u_domains_projection(&self.snapshot_k()); kernel_u_domains_projection(krnl); };
        self.end_kernel_step_raw(krnl, lctx);
    }

    /// Finish an endpoint creation: one quota of `staging_thread_ptr` funds `new_endpoint_ptr`, installed at its
    /// descriptor `endpoint_index`, with the staging thread's progress cleared.
    pub proof fn end_kernel_step_new_endpoint(
        tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, container_ptr: RwLockContainerPtr, staging_thread_ptr: RwLockThreadPtr,
        endpoint_index: EndpointIdx, new_endpoint_ptr: RwLockEndpointPtr,
    )
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_new_endpoint_fields(&old(self).snapshot_k(), krnl, container_ptr, staging_thread_ptr, endpoint_index, new_endpoint_ptr, None),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).snapshot_k() == *krnl,
    {
        use_type_invariant(&*self);
        assert(self.snapshot_u() != kernel_k_to_kernel_u(*krnl)) by { reveal(kernel_new_endpoint_fields); reveal(kernel_k_to_kernel_u); };
        self.end_kernel_step_raw(krnl, lctx);
    }

    /// Finish a thread exit: `thread_ptr` leaves the kernel and `cpu_id` goes idle.
    pub proof fn end_kernel_step_thread_exit(tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, flushed_default_pcid: bool)
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_thread_exit_fields(&old(self).snapshot_k(), krnl, cpu_id, thread_ptr, flushed_default_pcid),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).snapshot_k() == *krnl,
    {
        use_type_invariant(&*self);
        assert(self.snapshot_u() != kernel_k_to_kernel_u(*krnl)) by { reveal(kernel_thread_exit_fields); kernel_u_domains_projection(&self.snapshot_k()); kernel_u_domains_projection(krnl); };
        self.end_kernel_step_raw(krnl, lctx);
    }

    #[verifier::spinoff_prover]
    pub proof fn end_kernel_step_thread_state_changed(tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, thread_ptr: RwLockThreadPtr, old_state: ThreadState, new_state: ThreadState)
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_thread_state_changed(&old(self).snapshot_k(), krnl, thread_ptr),
            old(self).snapshot_k().thr_mp.dom().contains(thread_ptr),
            krnl.thr_mp.dom().contains(thread_ptr),
            old(self).snapshot_k().thr_mp.spec_index(thread_ptr).view().state == old_state,
            krnl.thr_mp.spec_index(thread_ptr).view().state == new_state,
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == record_user_view_change(old(self).view(), old(self).snapshot_u(), kernel_k_to_kernel_u(*krnl)),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).snapshot_k() == *krnl,
    {
        use_type_invariant(&*self);
        self.end_kernel_step_raw(krnl, lctx);
    }

    #[verifier::spinoff_prover]
    pub proof fn end_kernel_step_thread_syscall_progress_changed(tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, thread_ptr: RwLockThreadPtr)
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            old(self).snapshot_k().thr_mp.dom().contains(thread_ptr),
            krnl.thr_mp.dom().contains(thread_ptr),
            old(self).snapshot_k().thr_mp.spec_index(thread_ptr).view().syscall_progress.view() != krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(),
        ensures
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).snapshot_k() == *krnl,
    {
        use_type_invariant(&*self);
        assert(self.snapshot_u().thread_map.spec_index(thread_ptr).syscall_progress != kernel_k_to_kernel_u(*krnl).thread_map.spec_index(thread_ptr).syscall_progress) by {
            kernel_thread_projection_at(&self.snapshot_k(), thread_ptr); kernel_thread_projection_at(krnl, thread_ptr);
        };
        self.end_kernel_step_raw(krnl, lctx);
    }

    #[verifier::spinoff_prover]
    pub proof fn end_kernel_step_context_switch(tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, next_thread: RwLockThreadPtr, entry_regs: Registers, flushed_pcid: Option<Pcid>)
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_context_switch_fields(&old(self).snapshot_k(), krnl, cpu_id, next_thread, entry_regs, flushed_pcid),
            forall|p: RwLockContainerPtr| #![trigger krnl.ctn_mp.spec_index(p)] old(self).snapshot_k().ctn_mp.dom().contains(p) ==> krnl.ctn_mp.spec_index(p).lock_process_owner_u() == old(self).snapshot_k().ctn_mp.spec_index(p).lock_process_owner_u(),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).snapshot_k() == *krnl,
            kernel_u_context_switch_changed(kernel_k_to_kernel_u(old(self).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, next_thread, entry_regs, flushed_pcid),
            {
                let old_u = kernel_k_to_kernel_u(old(self).snapshot_k());
                let cpu = old_u.cpu_array[cpu_id as int];
                let container = old_u.container_map.spec_index(cpu.owning_container);
                let next = old_u.thread_map.spec_index(next_thread);
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& !(cpu.state is Off)
                &&& old_u.container_map.dom().contains(cpu.owning_container)
                &&& container.scheduler[cpu_id as int].len() > 0
                &&& container.scheduler[cpu_id as int][0] == next_thread
                &&& old_u.thread_map.dom().contains(next_thread)
                &&& next.lock_state is Unlocked
                &&& !next.killed
                &&& next.state is SCHEDULED
                &&& next.owning_container == cpu.owning_container
                &&& old_u.process_map.dom().contains(next.owning_proc)
                &&& cpu.current_thread != Some(next_thread)
                &&& cpu.current_process is Some == cpu.current_thread is Some
                &&& (cpu.current_thread is Some ==> {
                    let prev = old_u.thread_map.spec_index(cpu.current_thread.unwrap());
                    &&& old_u.thread_map.dom().contains(cpu.current_thread.unwrap())
                    &&& prev.lock_state is Unlocked
                    &&& !prev.killed
                    &&& prev.state == (ThreadState::RUNNING { cpu_id })
                    &&& prev.owning_proc == cpu.current_process.unwrap()
                    &&& old_u.process_map.dom().contains(cpu.current_process.unwrap())
                    &&& old_u.process_map.spec_index(cpu.current_process.unwrap()).lock_state is Unlocked
                    &&& !old_u.process_map.spec_index(cpu.current_process.unwrap()).killed
                })
            },
    {
        hide(kernel_k_user_projection);
        reveal(kernel_u_context_switch_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            let cpu = pre_u.cpu_array[cpu_id as int];
            &&& cpu.lock_state is Unlocked
            &&& pre_u.thread_map.spec_index(next_thread).lock_state is Unlocked
            &&& cpu.current_thread is Some ==> pre_u.thread_map.spec_index(cpu.current_thread.unwrap()).lock_state is Unlocked
            &&& cpu.current_process is Some ==> pre_u.process_map.spec_index(cpu.current_process.unwrap()).lock_state is Unlocked
        }) by {
            reveal(kernel_context_switch_fields); kernel_cpu_projection_at(&self.snapshot_k(), cpu_id); kernel_thread_projection_at(&self.snapshot_k(), next_thread);
            if let Some(t) = self.snapshot_k().cpu_arr.spec_index(cpu_id).value.view().view().current_thread { if self.snapshot_k().thr_mp.dom().contains(t) { kernel_thread_projection_at(&self.snapshot_k(), t); } }
            if let Some(p) = self.snapshot_k().cpu_arr.spec_index(cpu_id).value.view().view().current_process { if self.snapshot_k().prc_mp.dom().contains(p) { kernel_process_projection_at(&self.snapshot_k(), p); } }
        };
        assert(kernel_u_context_switch_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, next_thread, entry_regs, flushed_pcid)) by {
            kernel_context_switch_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, next_thread, entry_regs, flushed_pcid);
            reveal(kernel_k_to_kernel_u);
        };
        self.end_kernel_step_raw(krnl, lctx);
    }

    #[verifier::spinoff_prover]
    pub proof fn end_kernel_step_rebalance_pull(tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, victim: CpuId, thread: RwLockThreadPtr)
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_rebalance_pull_fields(&old(self).snapshot_k(), krnl, cpu_id, victim, thread),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).snapshot_k() == *krnl,
            kernel_u_rebalance_pull_changed(kernel_k_to_kernel_u(old(self).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, victim, thread),
            {
                let old_u = kernel_k_to_kernel_u(old(self).snapshot_k());
                let cpu = old_u.cpu_array[cpu_id as int];
                let queues = old_u.container_map.spec_index(cpu.owning_container).scheduler;
                let t = old_u.thread_map.spec_index(thread);
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& index_valid(NUM_CPUS, victim)
                &&& victim != cpu_id
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Idle
                &&& old_u.container_map.dom().contains(cpu.owning_container)
                &&& queues[cpu_id as int].len() == 0
                &&& first_nonempty_shard(queues, 0, cpu_id) == Some(victim)
                &&& queues[victim as int].len() > 0
                &&& queues[victim as int][0] == thread
                &&& old_u.thread_map.dom().contains(thread)
                &&& t.lock_state is Unlocked
                &&& !t.killed
                &&& t.state == (ThreadState::SCHEDULED { cpu_id: victim })
                &&& t.owning_container == cpu.owning_container
            },
    {
        hide(kernel_k_user_projection);
        reveal(kernel_u_rebalance_pull_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.thread_map.spec_index(thread).lock_state is Unlocked
        }) by {
            reveal(kernel_rebalance_pull_fields); kernel_cpu_projection_at(&self.snapshot_k(), cpu_id); kernel_thread_projection_at(&self.snapshot_k(), thread);
        };
        assert(kernel_u_rebalance_pull_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, victim, thread)) by {
            kernel_rebalance_pull_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, victim, thread);
            reveal(kernel_k_to_kernel_u);
        };
        self.end_kernel_step_raw(krnl, lctx);
    }
}

/// An index below the length of a kept prefix keeps its recorded step.
pub proof fn kernel_steps_prefix_unchanged_index(before: Seq<KernelStep>, after: Seq<KernelStep>, i: int)
    requires
        kernel_steps_prefix_unchanged(before, after),
        0 <= i < before.len(),
    ensures
        after[i] == before[i],
{ reveal(kernel_steps_prefix_unchanged); }
}
