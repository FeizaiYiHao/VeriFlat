use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal};
use crate::*;
#[cfg(verus_keep_ghost)]
use super::implementation::create_thread_from_staged_page::kernel_u_new_thread_changed;

/// K->U projection lemmas for lock-state, scheduling, IPC, publication, and new-thread steps.
pub mod projection;
/// Step-boundary wrappers and K->U lemmas for quota, cpu, TLB, mapping, endpoint, and thread-exit steps.
pub mod boundary;
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
/// Generic K->U bindings of projected entries, the stored snapshot, and root-table detaches.
pub mod bindings;

pub use projection::*;
pub use boundary::*;
pub use release::*;
pub use killed_thread::*;
pub use kill::*;
pub use kill_reclaim::*;
pub use kill_retire::*;
pub use bindings::*;

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
    #[verifier::opaque]
    pub open spec fn nonlock_view(&self) -> Seq<KernelStep> {
        self.view().filter_map(|step: KernelStep| step.nonlock_step())
    }
    pub open spec fn nonlock_snapshot_u(&self) -> KernelU { kernel_k_to_nonlock_kernel_u(self.snapshot_k()) }
    pub closed spec fn snapshot_k(&self) -> KernelK { self.snapshot_k }
    pub closed spec fn snapshot_u(&self) -> KernelU { self.snapshot_u }

    #[verifier::type_invariant]
    pub open spec fn snapshots_consistent(&self) -> bool {
        self.snapshot_u() == kernel_k_to_kernel_u(self.snapshot_k())
    }

    pub proof fn new(krnl: &KernelK) -> (tracked ret: Self)
        ensures
            ret.view() == Seq::<KernelStep>::empty(),
            ret.nonlock_view() == Seq::<KernelStep>::empty(),
            ret.snapshot_k() == *krnl,
            ret.snapshot_u() == kernel_k_to_kernel_u(*krnl),
    {
        reveal(KernelSteps::nonlock_view);
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
            final(self).nonlock_view() == old(self).nonlock_view(),
            final(self).snapshot_u() == old(self).snapshot_u(),
            final(self).snapshot_u() == kernel_k_to_kernel_u(final(self).snapshot_k()),
            krnl.irt.view().owners() == final(self).snapshot_k().irt.view().owners(),
            krnl.irt.view().iommu_roots() == final(self).snapshot_k().irt.view().iommu_roots(),
            krnl.cpu_tlb.view() == final(self).snapshot_k().cpu_tlb.view(),
            krnl.iommu_tlb.view() == final(self).snapshot_k().iommu_tlb.view(),
            final(self).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
            final(self).snapshot_k() == if old(self).snapshot_u() == kernel_k_to_kernel_u(*krnl) { *krnl } else { old(self).snapshot_k() },
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(self).snapshot_k(), krnl),
            kernel_endpoint_nonlock_fields_unchanged(final(self).snapshot_k().ep_mp, krnl.ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(self).snapshot_k(), krnl),
    {
        reveal(KernelSteps::nonlock_view);
        use_type_invariant(&*self);
        assert(self.nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl)) by { kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(&self.snapshot_k(), krnl); };
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
            krnl.dflt_pt == old(self).snapshot_k().dflt_pt,
            krnl.cpu_arr.unchanged_except(&old(self).snapshot_k().cpu_arr, cpu),
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
                },
                None => krnl.pt_mp == old(self).snapshot_k().pt_mp,
            },
        ensures
            kernel_k_to_nonlock_kernel_u(*krnl) == old(self).nonlock_snapshot_u(),
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).nonlock_view() == old(self).nonlock_view(),
            final(self).snapshot_u() == old(self).snapshot_u(),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).snapshot_k() == *krnl,
            kernel_endpoint_nonlock_fields_unchanged(final(self).snapshot_k().ep_mp, krnl.ep_mp),
    {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&self.snapshot_k(), krnl)) by {
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
            reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
            reveal(kernel_pagetable_nonlock_fields_unchanged);
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
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(self).snapshot_k(), krnl),
            forall|p: RwLockContainerPtr| #![trigger krnl.ctn_mp.spec_index(p)]
                krnl.ctn_mp.dom().contains(p) && old(self).snapshot_k().ctn_mp.dom().contains(p) ==> {
                    let before = old(self).snapshot_k().ctn_mp.spec_index(p).locking_thread();
                    let after = krnl.ctn_mp.spec_index(p).locking_thread();
                    &&& (after is Write) == (before is Write)
                    &&& (after is Read) == (before is Read)
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
            kernel_k_to_nonlock_kernel_u(*krnl) == old(self).nonlock_snapshot_u(),
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).nonlock_view() == old(self).nonlock_view(),
            final(self).snapshot_u() == old(self).snapshot_u(),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).snapshot_k() == *krnl,
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(self).snapshot_k(), krnl),
            kernel_endpoint_nonlock_fields_unchanged(final(self).snapshot_k().ep_mp, krnl.ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(self).snapshot_k(), krnl),
    {
        reveal(KernelSteps::nonlock_view);
        use_type_invariant(&*self);
        assert(self.snapshot_u() == kernel_k_to_kernel_u(*krnl)) by { kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&self.snapshot_k(), krnl); };
        assert(kernel_k_to_nonlock_kernel_u(*krnl) == self.nonlock_snapshot_u()) by { kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(&self.snapshot_k(), krnl); };
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
            final(self).nonlock_view() == record_user_view_change(old(self).nonlock_view(), old(self).nonlock_snapshot_u(), kernel_k_to_nonlock_kernel_u(*krnl)),
    {
        use_type_invariant(&*self);
        assert(self.nonlock_snapshot_u() == kernel_u_nonlock_fields(self.snapshot_u()) && kernel_k_to_nonlock_kernel_u(*krnl) == kernel_u_nonlock_fields(kernel_k_to_kernel_u(*krnl))) by {
            kernel_nonlock_projection_is_u_nonlock_fields(self.snapshot_k()); kernel_nonlock_projection_is_u_nonlock_fields(*krnl);
        };
        reveal(KernelSteps::nonlock_view);
        assert(record_user_view_change(self.view(), self.snapshot_u(), kernel_k_to_kernel_u(*krnl)).filter_map(|step: KernelStep| step.nonlock_step())
            == record_user_view_change(self.nonlock_view(), self.nonlock_snapshot_u(), kernel_k_to_nonlock_kernel_u(*krnl))) by {
            seq_filter_map_push_lemma(self.view(), KernelStep { old_u: self.snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }, |step: KernelStep| step.nonlock_step());
        };
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
            final(self).nonlock_view() == old(self).nonlock_view(),
            final(self).snapshot_k() == *krnl,
            final(self).nonlock_snapshot_u() == old(self).nonlock_snapshot_u(),
    {
        use_type_invariant(&*self);
        assert(self.nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl)) by { kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(&self.snapshot_k(), krnl); };
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
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            final(self).nonlock_view().last().new_u.process_map.spec_index(process_ptr).owned_threads.last() == new_thread_ptr,
            kernel_u_new_thread_changed(final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u,
                process_ptr, staging_thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, initial_endpoint, staging_progress),
    {
        use_type_invariant(&*self);
        assert(kernel_u_new_thread_changed(self.nonlock_snapshot_u(), kernel_k_to_nonlock_kernel_u(*krnl),
            process_ptr, staging_thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, initial_endpoint, staging_progress)) by {
            kernel_new_thread_fields_implies_u_step(&self.snapshot_k(), krnl, process_ptr, staging_thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, initial_endpoint, staging_progress);
        };
        assert(self.nonlock_snapshot_u() != kernel_k_to_nonlock_kernel_u(*krnl)
            && kernel_k_to_nonlock_kernel_u(*krnl).process_map.spec_index(process_ptr).owned_threads.last() == new_thread_ptr) by { reveal(kernel_u_new_thread_changed); };
        assert(self.snapshot_u() != kernel_k_to_kernel_u(*krnl)) by { reveal(kernel_new_thread_fields); kernel_u_domains_projection(&self.snapshot_k()); kernel_u_domains_projection(krnl); };
        self.end_kernel_step_raw(krnl, lctx);
    }

    /// `end_kernel_step_new_thread` for a thread funded by the live thread running on `cpu_id` inside its own live
    /// process and container, whose descriptor at `endpoint_index` names the optional initial endpoint.
    pub proof fn end_kernel_step_new_thread_on_cpu(
        tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
        staging_thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, new_thread_ptr: RwLockThreadPtr, initial_regs: Registers,
        initial_endpoint: Option<RwLockEndpointPtr>, endpoint_index: EndpointIdx, staging_progress: Option<SyscallProgress>,
    )
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_new_thread_fields(&old(self).snapshot_k(), krnl, process_ptr, staging_thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, initial_endpoint, staging_progress),
            index_valid(NUM_CPUS, cpu_id),
            {
                let pre = old(self).snapshot_k();
                let cpu = pre.cpu_arr.spec_index(cpu_id).value.view().view();
                let thread = pre.thr_mp.spec_index(staging_thread_ptr).view();
                &&& cpu.state is Running
                &&& cpu.current_process == Some(process_ptr)
                &&& cpu.current_thread == Some(staging_thread_ptr)
                &&& cpu.owning_container == container_ptr
                &&& !pre.prc_mp.spec_index(process_ptr).being_killed()
                &&& !pre.thr_mp.spec_index(staging_thread_ptr).being_killed()
                &&& thread.state == (ThreadState::RUNNING { cpu_id })
                &&& thread.owning_proc == process_ptr
                &&& thread.owning_container == container_ptr
                &&& (initial_endpoint is Some ==> edp_idx_valid(endpoint_index) && thread.endpoint_descriptors.view()[endpoint_index as int] == initial_endpoint)
            },
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            final(self).nonlock_view().last().new_u.process_map.spec_index(process_ptr).owned_threads.last() == new_thread_ptr,
            kernel_u_new_thread_changed(final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u,
                process_ptr, staging_thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, initial_endpoint, staging_progress),
            {
                let old_u = final(self).nonlock_view().last().old_u;
                let cpu = old_u.cpu_array[cpu_id as int];
                let thread = old_u.thread_map.spec_index(staging_thread_ptr);
                &&& cpu.state is Running
                &&& cpu.current_process == Some(process_ptr)
                &&& cpu.current_thread == Some(staging_thread_ptr)
                &&& cpu.owning_container == container_ptr
                &&& !old_u.process_map.spec_index(process_ptr).killed
                &&& !thread.killed
                &&& thread.state == (ThreadState::RUNNING { cpu_id })
                &&& thread.owning_proc == process_ptr
                &&& thread.owning_container == container_ptr
                &&& old_u.container_map.dom().contains(container_ptr)
                &&& old_u.process_map.dom().contains(process_ptr)
                &&& old_u.thread_map.dom().contains(staging_thread_ptr)
                &&& thread.quota_4k >= 1
                &&& (initial_endpoint is Some ==> edp_idx_valid(endpoint_index) && thread.endpoint_descriptors[endpoint_index as int] == initial_endpoint)
                &&& (initial_endpoint is Some ==> old_u.endpoint_map.dom().contains(initial_endpoint->Some_0))
            },
    {
        let pre_u = self.nonlock_snapshot_u();
        self.end_kernel_step_new_thread(krnl, lctx, process_ptr, staging_thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, initial_endpoint, staging_progress);
        assert({
            let cpu = pre_u.cpu_array[cpu_id as int];
            let thread = pre_u.thread_map.spec_index(staging_thread_ptr);
            &&& cpu.state is Running
            &&& cpu.current_process == Some(process_ptr)
            &&& cpu.current_thread == Some(staging_thread_ptr)
            &&& cpu.owning_container == container_ptr
            &&& !pre_u.process_map.spec_index(process_ptr).killed
            &&& !thread.killed
            &&& thread.state == (ThreadState::RUNNING { cpu_id })
            &&& thread.owning_proc == process_ptr
            &&& thread.owning_container == container_ptr
            &&& pre_u.container_map.dom().contains(container_ptr)
            &&& pre_u.process_map.dom().contains(process_ptr)
            &&& pre_u.thread_map.dom().contains(staging_thread_ptr)
            &&& thread.quota_4k >= 1
            &&& (initial_endpoint is Some ==> edp_idx_valid(endpoint_index) && thread.endpoint_descriptors[endpoint_index as int] == initial_endpoint)
            &&& (initial_endpoint is Some ==> pre_u.endpoint_map.dom().contains(initial_endpoint->Some_0))
        }) by { reveal(kernel_k_to_nonlock_kernel_u); reveal(kernel_new_thread_fields); };
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
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
    {
        use_type_invariant(&*self);
        assert(self.nonlock_snapshot_u() != kernel_k_to_nonlock_kernel_u(*krnl)) by { reveal(kernel_new_endpoint_fields); reveal(kernel_k_to_nonlock_kernel_u); };
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
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
    {
        use_type_invariant(&*self);
        assert(self.nonlock_snapshot_u() != kernel_k_to_nonlock_kernel_u(*krnl)) by { reveal(kernel_thread_exit_fields); reveal(kernel_k_to_nonlock_kernel_u); };
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
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            final(self).nonlock_view().last().old_u.thread_map.dom().contains(thread_ptr),
            final(self).nonlock_view().last().old_u.thread_map.spec_index(thread_ptr).state == old_state,
            final(self).nonlock_view().last().new_u.thread_map.dom().contains(thread_ptr),
            final(self).nonlock_view().last().new_u.thread_map.spec_index(thread_ptr).state == new_state,
    {
        use_type_invariant(&*self);
        kernel_thread_state_changed_implies_u_neq(&self.snapshot_k(), krnl, thread_ptr);
        assert(self.nonlock_snapshot_u().thread_map.dom().contains(thread_ptr)
            && self.nonlock_snapshot_u().thread_map.spec_index(thread_ptr).state == old_state) by { kernel_thread_nonlock_projection_at(&self.snapshot_k(), thread_ptr); };
        assert(kernel_k_to_nonlock_kernel_u(*krnl).thread_map.dom().contains(thread_ptr)
            && kernel_k_to_nonlock_kernel_u(*krnl).thread_map.spec_index(thread_ptr).state == new_state) by { kernel_thread_nonlock_projection_at(krnl, thread_ptr); };
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
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
    {
        use_type_invariant(&*self);
        assert(self.nonlock_snapshot_u().thread_map.spec_index(thread_ptr).syscall_progress != kernel_k_to_nonlock_kernel_u(*krnl).thread_map.spec_index(thread_ptr).syscall_progress) by {
            kernel_thread_nonlock_projection_at(&self.snapshot_k(), thread_ptr); kernel_thread_nonlock_projection_at(krnl, thread_ptr);
        };
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
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            kernel_u_context_switch_changed(final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u, cpu_id, next_thread, entry_regs, flushed_pcid),
            kernel_u_context_switch_changed(kernel_k_to_kernel_u(old(self).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, next_thread, entry_regs, flushed_pcid),
            {
                let old_u = final(self).nonlock_view().last().old_u;
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
        reveal(kernel_u_context_switch_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_nonlock_kernel_u(self.snapshot_k());
            let cpu = pre_u.cpu_array[cpu_id as int];
            &&& cpu.lock_state is Unlocked
            &&& pre_u.thread_map.spec_index(next_thread).lock_state is Unlocked
            &&& cpu.current_thread is Some ==> pre_u.thread_map.spec_index(cpu.current_thread.unwrap()).lock_state is Unlocked
            &&& cpu.current_process is Some ==> pre_u.process_map.spec_index(cpu.current_process.unwrap()).lock_state is Unlocked
        }) by { reveal(kernel_k_to_nonlock_kernel_u); reveal(kernel_context_switch_fields); };
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            let cpu = pre_u.cpu_array[cpu_id as int];
            &&& cpu.lock_state is Unlocked
            &&& pre_u.thread_map.spec_index(next_thread).lock_state is Unlocked
            &&& cpu.current_thread is Some ==> pre_u.thread_map.spec_index(cpu.current_thread.unwrap()).lock_state is Unlocked
            &&& cpu.current_process is Some ==> pre_u.process_map.spec_index(cpu.current_process.unwrap()).lock_state is Unlocked
        }) by { reveal(kernel_k_to_kernel_u); reveal(kernel_context_switch_fields); };
        assert(kernel_u_context_switch_changed(self.nonlock_snapshot_u(), kernel_k_to_nonlock_kernel_u(*krnl), cpu_id, next_thread, entry_regs, flushed_pcid)) by {
            kernel_context_switch_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, next_thread, entry_regs, flushed_pcid, false);
            reveal(kernel_k_to_nonlock_kernel_u);
        };
        assert(kernel_u_context_switch_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, next_thread, entry_regs, flushed_pcid)) by {
            kernel_context_switch_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, next_thread, entry_regs, flushed_pcid, true);
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
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            kernel_u_rebalance_pull_changed(final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u, cpu_id, victim, thread),
            kernel_u_rebalance_pull_changed(kernel_k_to_kernel_u(old(self).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, victim, thread),
            {
                let old_u = final(self).nonlock_view().last().old_u;
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
        reveal(kernel_u_rebalance_pull_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_nonlock_kernel_u(self.snapshot_k());
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.thread_map.spec_index(thread).lock_state is Unlocked
        }) by { reveal(kernel_k_to_nonlock_kernel_u); reveal(kernel_rebalance_pull_fields); };
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.thread_map.spec_index(thread).lock_state is Unlocked
        }) by { reveal(kernel_k_to_kernel_u); reveal(kernel_rebalance_pull_fields); };
        assert(kernel_u_rebalance_pull_changed(self.nonlock_snapshot_u(), kernel_k_to_nonlock_kernel_u(*krnl), cpu_id, victim, thread)) by {
            kernel_rebalance_pull_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, victim, thread, false);
            reveal(kernel_k_to_nonlock_kernel_u);
        };
        assert(kernel_u_rebalance_pull_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, victim, thread)) by {
            kernel_rebalance_pull_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, victim, thread, true);
            reveal(kernel_k_to_kernel_u);
        };
        self.end_kernel_step_raw(krnl, lctx);
    }

    #[verifier::spinoff_prover]
    pub proof fn end_kernel_step_ipc_block(
        tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
        endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, regs: Registers, flushed_default_pcid: bool,
    )
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_ipc_block_fields(&old(self).snapshot_k(), krnl, cpu_id, thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, regs, flushed_default_pcid),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            kernel_u_ipc_block_changed(old(self).snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, thread_ptr, endpoint_ptr,
                endpoint_index, waiting_state, payload, regs, flushed_default_pcid),
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            kernel_u_ipc_block_changed(final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u, cpu_id, thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, regs, flushed_default_pcid),
            {
                let old_u = final(self).nonlock_view().last().old_u;
                let cpu = old_u.cpu_array[cpu_id as int];
                let thread = old_u.thread_map.spec_index(thread_ptr);
                let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_thread == Some(thread_ptr)
                &&& cpu.current_process == Some(thread.owning_proc)
                &&& cpu.killed == old(self).snapshot_k().cpu_arr.spec_index(cpu_id).value.being_killed()
                &&& old_u.process_map.dom().contains(thread.owning_proc)
                &&& old_u.container_map.dom().contains(thread.owning_container)
                &&& old_u.thread_map.dom().contains(thread_ptr)
                &&& thread.lock_state is Unlocked
                &&& thread.syscall_progress is None
                &&& !thread.killed
                &&& thread.state == (ThreadState::RUNNING { cpu_id })
                &&& edp_idx_valid(endpoint_index)
                &&& thread.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
                &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
                &&& endpoint.lock_state is Unlocked
                &&& !endpoint.queue.contains(thread_ptr)
                &&& waiting_state.is_endpoint_waiting()
                &&& endpoint.queue.len() == 0 || (endpoint.queue_state is SEND) == waiting_state.is_endpoint_send_waiting()
            },
            {
                let old_u = kernel_k_to_kernel_u(old(self).snapshot_k());
                let cpu = old_u.cpu_array[cpu_id as int];
                let thread = old_u.thread_map.spec_index(thread_ptr);
                let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_thread == Some(thread_ptr)
                &&& cpu.current_process == Some(thread.owning_proc)
                &&& cpu.killed == old(self).snapshot_k().cpu_arr.spec_index(cpu_id).value.being_killed()
                &&& old_u.process_map.dom().contains(thread.owning_proc)
                &&& old_u.container_map.dom().contains(thread.owning_container)
                &&& old_u.thread_map.dom().contains(thread_ptr)
                &&& thread.lock_state is Unlocked
                &&& thread.syscall_progress is None
                &&& !thread.killed
                &&& thread.state == (ThreadState::RUNNING { cpu_id })
                &&& edp_idx_valid(endpoint_index)
                &&& thread.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
                &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
                &&& endpoint.lock_state is Unlocked
                &&& !endpoint.queue.contains(thread_ptr)
                &&& waiting_state.is_endpoint_waiting()
                &&& endpoint.queue.len() == 0 || (endpoint.queue_state is SEND) == waiting_state.is_endpoint_send_waiting()
            },
    {
        reveal(kernel_u_ipc_block_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_nonlock_kernel_u(self.snapshot_k());
            let thread = pre_u.thread_map.spec_index(thread_ptr);
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.cpu_array[cpu_id as int].killed == self.snapshot_k().cpu_arr.spec_index(cpu_id).value.being_killed()
            &&& thread.lock_state is Unlocked
            &&& thread.syscall_progress is None
            &&& pre_u.endpoint_map.spec_index(endpoint_ptr).lock_state is Unlocked
            &&& pre_u.container_map.dom().contains(thread.owning_container)
        }) by { reveal(kernel_k_to_nonlock_kernel_u); reveal(kernel_ipc_block_fields); };
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            let thread = pre_u.thread_map.spec_index(thread_ptr);
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.cpu_array[cpu_id as int].killed == self.snapshot_k().cpu_arr.spec_index(cpu_id).value.being_killed()
            &&& thread.lock_state is Unlocked
            &&& thread.syscall_progress is None
            &&& pre_u.endpoint_map.spec_index(endpoint_ptr).lock_state is Unlocked
            &&& pre_u.container_map.dom().contains(thread.owning_container)
        }) by { reveal(kernel_k_to_kernel_u); reveal(kernel_ipc_block_fields); };
        let pre_u = self.nonlock_snapshot_u();
        let post_u = kernel_k_to_nonlock_kernel_u(*krnl);
        assert(kernel_u_ipc_block_changed(pre_u, post_u, cpu_id, thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, regs, flushed_default_pcid)) by {
            kernel_ipc_block_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, regs, flushed_default_pcid, false);
            reveal(kernel_k_to_nonlock_kernel_u);
        };
        assert(kernel_u_ipc_block_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, regs, flushed_default_pcid)) by {
            kernel_ipc_block_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, regs, flushed_default_pcid, true);
            reveal(kernel_k_to_kernel_u);
        };
        self.end_kernel_step_raw(krnl, lctx);
    }

    #[verifier::spinoff_prover]
    pub proof fn end_kernel_step_ipc_call_handoff(
        tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, caller_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
        endpoint_index: EndpointIdx, callee_ptr: RwLockThreadPtr, regs: Registers, flushed_pcid: Option<Pcid>,
    )
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_ipc_call_handoff_fields(&old(self).snapshot_k(), krnl, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, regs, flushed_pcid),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            kernel_u_ipc_call_handoff_changed(old(self).snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, regs, flushed_pcid),
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            kernel_u_ipc_call_handoff_changed(final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, regs, flushed_pcid),
            {
                let old_u = final(self).nonlock_view().last().old_u;
                let cpu = old_u.cpu_array[cpu_id as int];
                let caller = old_u.thread_map.spec_index(caller_ptr);
                let callee = old_u.thread_map.spec_index(callee_ptr);
                let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_thread == Some(caller_ptr)
                &&& cpu.current_process == Some(caller.owning_proc)
                &&& old_u.process_map.dom().contains(caller.owning_proc)
                &&& old_u.container_map.dom().contains(caller.owning_container)
                &&& old_u.thread_map.dom().contains(caller_ptr)
                &&& caller.lock_state is Unlocked
                &&& caller.syscall_progress is None
                &&& !caller.killed
                &&& caller.state == (ThreadState::RUNNING { cpu_id })
                &&& caller.callee is None
                &&& edp_idx_valid(endpoint_index)
                &&& caller.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
                &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
                &&& endpoint.lock_state is Unlocked
                &&& !endpoint.queue.contains(caller_ptr)
                &&& endpoint.queue.len() > 0
                &&& endpoint.queue[0] == callee_ptr
                &&& endpoint.queue_state is RECEIVE
                &&& callee_ptr != caller_ptr
                &&& old_u.thread_map.dom().contains(callee_ptr)
                &&& callee.lock_state is Unlocked
                &&& !callee.killed
                &&& callee.state is RECEIVING_CALL
                &&& callee.caller is None
                &&& callee.callee is None
                &&& callee.blocking_endpoint_ptr == Some(endpoint_ptr)
                &&& callee.owning_container == caller.owning_container
                &&& old_u.process_map.dom().contains(callee.owning_proc)
            },
            {
                let old_u = kernel_k_to_kernel_u(old(self).snapshot_k());
                let cpu = old_u.cpu_array[cpu_id as int];
                let caller = old_u.thread_map.spec_index(caller_ptr);
                let callee = old_u.thread_map.spec_index(callee_ptr);
                let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_thread == Some(caller_ptr)
                &&& cpu.current_process == Some(caller.owning_proc)
                &&& old_u.process_map.dom().contains(caller.owning_proc)
                &&& old_u.container_map.dom().contains(caller.owning_container)
                &&& old_u.thread_map.dom().contains(caller_ptr)
                &&& caller.lock_state is Unlocked
                &&& caller.syscall_progress is None
                &&& !caller.killed
                &&& caller.state == (ThreadState::RUNNING { cpu_id })
                &&& caller.callee is None
                &&& edp_idx_valid(endpoint_index)
                &&& caller.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
                &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
                &&& endpoint.lock_state is Unlocked
                &&& !endpoint.queue.contains(caller_ptr)
                &&& endpoint.queue.len() > 0
                &&& endpoint.queue[0] == callee_ptr
                &&& endpoint.queue_state is RECEIVE
                &&& callee_ptr != caller_ptr
                &&& old_u.thread_map.dom().contains(callee_ptr)
                &&& callee.lock_state is Unlocked
                &&& !callee.killed
                &&& callee.state is RECEIVING_CALL
                &&& callee.caller is None
                &&& callee.callee is None
                &&& callee.blocking_endpoint_ptr == Some(endpoint_ptr)
                &&& callee.owning_container == caller.owning_container
                &&& old_u.process_map.dom().contains(callee.owning_proc)
            },
    {
        reveal(kernel_u_ipc_call_handoff_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_nonlock_kernel_u(self.snapshot_k());
            let first = pre_u.thread_map.spec_index(caller_ptr);
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& first.lock_state is Unlocked
            &&& first.syscall_progress is None
            &&& pre_u.thread_map.spec_index(callee_ptr).lock_state is Unlocked
            &&& pre_u.endpoint_map.spec_index(endpoint_ptr).lock_state is Unlocked
            &&& pre_u.container_map.dom().contains(first.owning_container)
        }) by { reveal(kernel_k_to_nonlock_kernel_u); reveal(kernel_ipc_call_handoff_fields); };
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            let first = pre_u.thread_map.spec_index(caller_ptr);
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& first.lock_state is Unlocked
            &&& first.syscall_progress is None
            &&& pre_u.thread_map.spec_index(callee_ptr).lock_state is Unlocked
            &&& pre_u.endpoint_map.spec_index(endpoint_ptr).lock_state is Unlocked
            &&& pre_u.container_map.dom().contains(first.owning_container)
        }) by { reveal(kernel_k_to_kernel_u); reveal(kernel_ipc_call_handoff_fields); };
        let pre_u = self.nonlock_snapshot_u();
        let post_u = kernel_k_to_nonlock_kernel_u(*krnl);
        assert(kernel_u_ipc_call_handoff_changed(pre_u, post_u, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, regs, flushed_pcid)) by {
            kernel_ipc_call_handoff_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, regs, flushed_pcid, false);
            reveal(kernel_k_to_nonlock_kernel_u);
        };
        assert(kernel_u_ipc_call_handoff_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, regs, flushed_pcid)) by {
            kernel_ipc_call_handoff_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, regs, flushed_pcid, true);
            reveal(kernel_k_to_kernel_u);
        };
        self.end_kernel_step_raw(krnl, lctx);
    }

    #[verifier::spinoff_prover]
    pub proof fn end_kernel_step_ipc_accept_call(tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, caller_ptr: RwLockThreadPtr)
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_ipc_accept_call_fields(&old(self).snapshot_k(), krnl, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            kernel_u_ipc_accept_call_changed(old(self).snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr),
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            kernel_u_ipc_accept_call_changed(final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr),
            {
                let old_u = final(self).nonlock_view().last().old_u;
                let cpu = old_u.cpu_array[cpu_id as int];
                let callee = old_u.thread_map.spec_index(callee_ptr);
                let caller = old_u.thread_map.spec_index(caller_ptr);
                let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_thread == Some(callee_ptr)
                &&& cpu.current_process == Some(callee.owning_proc)
                &&& old_u.process_map.dom().contains(callee.owning_proc)
                &&& old_u.container_map.dom().contains(callee.owning_container)
                &&& old_u.thread_map.dom().contains(callee_ptr)
                &&& callee.lock_state is Unlocked
                &&& callee.syscall_progress is None
                &&& !callee.killed
                &&& callee.state == (ThreadState::RUNNING { cpu_id })
                &&& callee.caller is None
                &&& callee.callee is None
                &&& edp_idx_valid(endpoint_index)
                &&& callee.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
                &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
                &&& endpoint.lock_state is Unlocked
                &&& !endpoint.queue.contains(callee_ptr)
                &&& endpoint.queue.len() > 0
                &&& endpoint.queue[0] == caller_ptr
                &&& endpoint.queue_state is SEND
                &&& caller_ptr != callee_ptr
                &&& old_u.thread_map.dom().contains(caller_ptr)
                &&& caller.lock_state is Unlocked
                &&& !caller.killed
                &&& caller.state is CALLING
                &&& caller.callee is None
                &&& caller.blocking_endpoint_ptr == Some(endpoint_ptr)
                &&& caller.owning_container == callee.owning_container
            },
            {
                let old_u = kernel_k_to_kernel_u(old(self).snapshot_k());
                let cpu = old_u.cpu_array[cpu_id as int];
                let callee = old_u.thread_map.spec_index(callee_ptr);
                let caller = old_u.thread_map.spec_index(caller_ptr);
                let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_thread == Some(callee_ptr)
                &&& cpu.current_process == Some(callee.owning_proc)
                &&& old_u.process_map.dom().contains(callee.owning_proc)
                &&& old_u.container_map.dom().contains(callee.owning_container)
                &&& old_u.thread_map.dom().contains(callee_ptr)
                &&& callee.lock_state is Unlocked
                &&& callee.syscall_progress is None
                &&& !callee.killed
                &&& callee.state == (ThreadState::RUNNING { cpu_id })
                &&& callee.caller is None
                &&& callee.callee is None
                &&& edp_idx_valid(endpoint_index)
                &&& callee.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
                &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
                &&& endpoint.lock_state is Unlocked
                &&& !endpoint.queue.contains(callee_ptr)
                &&& endpoint.queue.len() > 0
                &&& endpoint.queue[0] == caller_ptr
                &&& endpoint.queue_state is SEND
                &&& caller_ptr != callee_ptr
                &&& old_u.thread_map.dom().contains(caller_ptr)
                &&& caller.lock_state is Unlocked
                &&& !caller.killed
                &&& caller.state is CALLING
                &&& caller.callee is None
                &&& caller.blocking_endpoint_ptr == Some(endpoint_ptr)
                &&& caller.owning_container == callee.owning_container
            },
            final(self).nonlock_view().last().old_u.thread_map[caller_ptr].ipc_payload == old(self).snapshot_u().thread_map[caller_ptr].ipc_payload,
    {
        reveal(kernel_u_ipc_accept_call_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_nonlock_kernel_u(self.snapshot_k());
            let first = pre_u.thread_map.spec_index(callee_ptr);
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& first.lock_state is Unlocked
            &&& first.syscall_progress is None
            &&& pre_u.thread_map.spec_index(caller_ptr).lock_state is Unlocked
            &&& pre_u.endpoint_map.spec_index(endpoint_ptr).lock_state is Unlocked
            &&& pre_u.container_map.dom().contains(first.owning_container)
        }) by { reveal(kernel_k_to_nonlock_kernel_u); reveal(kernel_ipc_accept_call_fields); };
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            let first = pre_u.thread_map.spec_index(callee_ptr);
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& first.lock_state is Unlocked
            &&& first.syscall_progress is None
            &&& pre_u.thread_map.spec_index(caller_ptr).lock_state is Unlocked
            &&& pre_u.endpoint_map.spec_index(endpoint_ptr).lock_state is Unlocked
            &&& pre_u.container_map.dom().contains(first.owning_container)
        }) by { reveal(kernel_k_to_kernel_u); reveal(kernel_ipc_accept_call_fields); };
        assert(self.nonlock_snapshot_u().thread_map[caller_ptr].ipc_payload == self.snapshot_u().thread_map[caller_ptr].ipc_payload) by {
            reveal(kernel_k_to_kernel_u); reveal(kernel_k_to_nonlock_kernel_u); reveal(kernel_ipc_accept_call_fields);
        };
        let pre_u = self.nonlock_snapshot_u();
        let post_u = kernel_k_to_nonlock_kernel_u(*krnl);
        assert(kernel_u_ipc_accept_call_changed(pre_u, post_u, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr)) by {
            kernel_ipc_accept_call_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, false);
            reveal(kernel_k_to_nonlock_kernel_u);
        };
        assert(kernel_u_ipc_accept_call_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr)) by {
            kernel_ipc_accept_call_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, true);
            reveal(kernel_k_to_kernel_u);
        };
        self.end_kernel_step_raw(krnl, lctx);
    }

    #[verifier::spinoff_prover]
    pub proof fn end_kernel_step_ipc_reply_handoff(
        tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
        endpoint_index: EndpointIdx, caller_ptr: RwLockThreadPtr, regs: Registers, flushed_pcid: Option<Pcid>,
    )
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_ipc_reply_handoff_fields(&old(self).snapshot_k(), krnl, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            kernel_u_ipc_reply_handoff_changed(old(self).snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid),
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            kernel_u_ipc_reply_handoff_changed(final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid),
            {
                let old_u = final(self).nonlock_view().last().old_u;
                let cpu = old_u.cpu_array[cpu_id as int];
                let callee = old_u.thread_map.spec_index(callee_ptr);
                let caller = old_u.thread_map.spec_index(caller_ptr);
                let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_thread == Some(callee_ptr)
                &&& cpu.current_process == Some(callee.owning_proc)
                &&& old_u.process_map.dom().contains(callee.owning_proc)
                &&& old_u.container_map.dom().contains(callee.owning_container)
                &&& old_u.thread_map.dom().contains(callee_ptr)
                &&& callee.lock_state is Unlocked
                &&& callee.syscall_progress is None
                &&& !callee.killed
                &&& callee.state == (ThreadState::RUNNING { cpu_id })
                &&& callee.caller == Some(caller_ptr)
                &&& callee.callee is None
                &&& edp_idx_valid(endpoint_index)
                &&& callee.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
                &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
                &&& endpoint.lock_state is Unlocked
                &&& !endpoint.queue.contains(callee_ptr)
                &&& endpoint.queue.len() == 0 || endpoint.queue_state is RECEIVE
                &&& caller_ptr != callee_ptr
                &&& old_u.thread_map.dom().contains(caller_ptr)
                &&& caller.lock_state is Unlocked
                &&& !caller.killed
                &&& caller.state is WAITING_REPLY
                &&& caller.callee == Some(callee_ptr)
                &&& caller.owning_container == callee.owning_container
                &&& old_u.process_map.dom().contains(caller.owning_proc)
            },
            {
                let old_u = kernel_k_to_kernel_u(old(self).snapshot_k());
                let cpu = old_u.cpu_array[cpu_id as int];
                let callee = old_u.thread_map.spec_index(callee_ptr);
                let caller = old_u.thread_map.spec_index(caller_ptr);
                let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_thread == Some(callee_ptr)
                &&& cpu.current_process == Some(callee.owning_proc)
                &&& old_u.process_map.dom().contains(callee.owning_proc)
                &&& old_u.container_map.dom().contains(callee.owning_container)
                &&& old_u.thread_map.dom().contains(callee_ptr)
                &&& callee.lock_state is Unlocked
                &&& callee.syscall_progress is None
                &&& !callee.killed
                &&& callee.state == (ThreadState::RUNNING { cpu_id })
                &&& callee.caller == Some(caller_ptr)
                &&& callee.callee is None
                &&& edp_idx_valid(endpoint_index)
                &&& callee.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
                &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
                &&& endpoint.lock_state is Unlocked
                &&& !endpoint.queue.contains(callee_ptr)
                &&& endpoint.queue.len() == 0 || endpoint.queue_state is RECEIVE
                &&& caller_ptr != callee_ptr
                &&& old_u.thread_map.dom().contains(caller_ptr)
                &&& caller.lock_state is Unlocked
                &&& !caller.killed
                &&& caller.state is WAITING_REPLY
                &&& caller.callee == Some(callee_ptr)
                &&& caller.owning_container == callee.owning_container
                &&& old_u.process_map.dom().contains(caller.owning_proc)
            },
    {
        reveal(kernel_u_ipc_reply_handoff_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_nonlock_kernel_u(self.snapshot_k());
            let first = pre_u.thread_map.spec_index(callee_ptr);
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& first.lock_state is Unlocked
            &&& first.syscall_progress is None
            &&& pre_u.thread_map.spec_index(caller_ptr).lock_state is Unlocked
            &&& pre_u.endpoint_map.spec_index(endpoint_ptr).lock_state is Unlocked
            &&& pre_u.container_map.dom().contains(first.owning_container)
        }) by { reveal(kernel_k_to_nonlock_kernel_u); reveal(kernel_ipc_reply_handoff_fields); };
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            let first = pre_u.thread_map.spec_index(callee_ptr);
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& first.lock_state is Unlocked
            &&& first.syscall_progress is None
            &&& pre_u.thread_map.spec_index(caller_ptr).lock_state is Unlocked
            &&& pre_u.endpoint_map.spec_index(endpoint_ptr).lock_state is Unlocked
            &&& pre_u.container_map.dom().contains(first.owning_container)
        }) by { reveal(kernel_k_to_kernel_u); reveal(kernel_ipc_reply_handoff_fields); };
        let pre_u = self.nonlock_snapshot_u();
        let post_u = kernel_k_to_nonlock_kernel_u(*krnl);
        assert(kernel_u_ipc_reply_handoff_changed(pre_u, post_u, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid)) by {
            kernel_ipc_reply_handoff_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid, false);
            reveal(kernel_k_to_nonlock_kernel_u);
        };
        assert(kernel_u_ipc_reply_handoff_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid)) by {
            kernel_ipc_reply_handoff_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid, true);
            reveal(kernel_k_to_kernel_u);
        };
        self.end_kernel_step_raw(krnl, lctx);
    }

    #[verifier::spinoff_prover]
    pub proof fn end_kernel_step_ipc_rendezvous(
        tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, caller_thread_ptr: RwLockThreadPtr,
        endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, waiting_state: ThreadState, peer_thread_ptr: RwLockThreadPtr,
        peer_result: RetValueType, cpu_transfer: Option<(CpuId, RwLockThreadPtr)>, pci_transfer: Option<(PciBdf, RwLockProcessPtr, RwLockProcessPtr)>, payload: IPCPayLoad,
        cpu_sets_locked: bool,
    )
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_ipc_rendezvous_fields(&old(self).snapshot_k(), krnl, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer),
            krnl.cpu_set_mp.dom() == old(self).snapshot_k().cpu_set_mp.dom(),
            forall|p: RwLockCpuSetPtr| #![trigger krnl.cpu_set_mp.spec_index(p)]
                old(self).snapshot_k().cpu_set_mp.dom().contains(p) ==> krnl.cpu_set_mp.spec_index(p).locking_thread() == old(self).snapshot_k().cpu_set_mp.spec_index(p).locking_thread(),
            cpu_sets_locked ==> {
                let snap = old(self).snapshot_k();
                &&& snap.cpu_set_mp.spec_index(snap.ctn_mp.spec_index(snap.thr_mp.spec_index(caller_thread_ptr).view().owning_container).view_rodata().view().cpu_set).locking_thread() is None
                &&& snap.cpu_set_mp.spec_index(snap.ctn_mp.spec_index(snap.thr_mp.spec_index(peer_thread_ptr).view().owning_container).view_rodata().view().cpu_set).locking_thread() is None
            },
            forall|p: RwLockContainerPtr| #![trigger krnl.ctn_mp.spec_index(p)]
                old(self).snapshot_k().ctn_mp.dom().contains(p) && krnl.ctn_mp.dom().contains(p) ==> krnl.ctn_mp.spec_index(p).locking_thread() == old(self).snapshot_k().ctn_mp.spec_index(p).locking_thread(),
            forall|p: RwLockProcessPtr| #![trigger krnl.prc_mp.spec_index(p)]
                old(self).snapshot_k().prc_mp.dom().contains(p) && krnl.prc_mp.dom().contains(p) ==> krnl.prc_mp.spec_index(p).locking_thread() == old(self).snapshot_k().prc_mp.spec_index(p).locking_thread(),
            forall|p: RwLockThreadPtr| #![trigger krnl.thr_mp.spec_index(p)]
                old(self).snapshot_k().thr_mp.dom().contains(p) && krnl.thr_mp.dom().contains(p) ==> krnl.thr_mp.spec_index(p).locking_thread() == old(self).snapshot_k().thr_mp.spec_index(p).locking_thread(),
            forall|p: RwLockEndpointPtr| #![trigger krnl.ep_mp.spec_index(p)]
                old(self).snapshot_k().ep_mp.dom().contains(p) && krnl.ep_mp.dom().contains(p) ==> krnl.ep_mp.spec_index(p).locking_thread() == old(self).snapshot_k().ep_mp.spec_index(p).locking_thread(),
            forall|p: RwLockPageTableRoot| #![trigger krnl.pt_mp.spec_index(p)]
                old(self).snapshot_k().pt_mp.dom().contains(p) && krnl.pt_mp.dom().contains(p) ==> krnl.pt_mp.spec_index(p).locking_thread() == old(self).snapshot_k().pt_mp.spec_index(p).locking_thread(),
            forall|p: RwLockPageTableRoot| #![trigger krnl.it_mp.spec_index(p)]
                old(self).snapshot_k().it_mp.dom().contains(p) && krnl.it_mp.dom().contains(p) ==> krnl.it_mp.spec_index(p).locking_thread() == old(self).snapshot_k().it_mp.spec_index(p).locking_thread(),
            forall|i: CpuId| #![trigger krnl.cpu_arr.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> krnl.cpu_arr.spec_index(i).value.locking_thread() == old(self).snapshot_k().cpu_arr.spec_index(i).value.locking_thread(),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            kernel_u_ipc_rendezvous_changed(old(self).snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, caller_thread_ptr,
                endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer),
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            kernel_u_ipc_rendezvous_changed(final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer),
            {
                let old_u = final(self).nonlock_view().last().old_u;
                let cpu = old_u.cpu_array[cpu_id as int];
                let caller = old_u.thread_map.spec_index(caller_thread_ptr);
                let peer = old_u.thread_map.spec_index(peer_thread_ptr);
                let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_thread == Some(caller_thread_ptr)
                &&& cpu.current_process == Some(caller.owning_proc)
                &&& old_u.process_map.dom().contains(caller.owning_proc)
                &&& old_u.thread_map.dom().contains(caller_thread_ptr)
                &&& caller.lock_state is Unlocked
                &&& caller.syscall_progress is None
                &&& !caller.killed
                &&& caller.state == (ThreadState::RUNNING { cpu_id })
                &&& edp_idx_valid(endpoint_index)
                &&& caller.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
                &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
                &&& endpoint.lock_state is Unlocked
                &&& !endpoint.queue.contains(caller_thread_ptr)
                &&& waiting_state.is_endpoint_waiting()
                &&& endpoint.queue.len() > 0
                &&& endpoint.queue[0] == peer_thread_ptr
                &&& (endpoint.queue_state is SEND) != waiting_state.is_endpoint_send_waiting()
                &&& old_u.thread_map.dom().contains(peer_thread_ptr)
                &&& peer.lock_state is Unlocked
                &&& peer_thread_ptr != caller_thread_ptr
                &&& !peer.killed
                &&& peer.state.is_endpoint_waiting()
                &&& peer.blocking_endpoint_ptr == Some(endpoint_ptr)
                &&& old_u.container_map.dom().contains(peer.owning_container)
                &&& old_u.container_map.dom().contains(caller.owning_container)
                &&& cpu_sets_locked ==> old_u.container_map[caller.owning_container].cpu_set_lock is Unlocked && old_u.container_map[peer.owning_container].cpu_set_lock is Unlocked
                &&& cpu_transfer matches Some((transfer, _)) ==> old_u.cpu_array[transfer as int].lock_state is Unlocked
            },
            {
                let old_u = kernel_k_to_kernel_u(old(self).snapshot_k());
                let cpu = old_u.cpu_array[cpu_id as int];
                let caller = old_u.thread_map.spec_index(caller_thread_ptr);
                let peer = old_u.thread_map.spec_index(peer_thread_ptr);
                let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_thread == Some(caller_thread_ptr)
                &&& cpu.current_process == Some(caller.owning_proc)
                &&& old_u.process_map.dom().contains(caller.owning_proc)
                &&& old_u.thread_map.dom().contains(caller_thread_ptr)
                &&& caller.lock_state is Unlocked
                &&& caller.syscall_progress is None
                &&& !caller.killed
                &&& caller.state == (ThreadState::RUNNING { cpu_id })
                &&& edp_idx_valid(endpoint_index)
                &&& caller.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
                &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
                &&& endpoint.lock_state is Unlocked
                &&& !endpoint.queue.contains(caller_thread_ptr)
                &&& waiting_state.is_endpoint_waiting()
                &&& endpoint.queue.len() > 0
                &&& endpoint.queue[0] == peer_thread_ptr
                &&& (endpoint.queue_state is SEND) != waiting_state.is_endpoint_send_waiting()
                &&& old_u.thread_map.dom().contains(peer_thread_ptr)
                &&& peer.lock_state is Unlocked
                &&& peer_thread_ptr != caller_thread_ptr
                &&& !peer.killed
                &&& peer.state.is_endpoint_waiting()
                &&& peer.blocking_endpoint_ptr == Some(endpoint_ptr)
                &&& old_u.container_map.dom().contains(peer.owning_container)
                &&& old_u.container_map.dom().contains(caller.owning_container)
                &&& cpu_sets_locked ==> old_u.container_map[caller.owning_container].cpu_set_lock is Unlocked && old_u.container_map[peer.owning_container].cpu_set_lock is Unlocked
                &&& cpu_transfer matches Some((transfer, _)) ==> old_u.cpu_array[transfer as int].lock_state is Unlocked
            },
            ipc_rendezvous_result(final(self).nonlock_view().last().old_u, cpu_id, endpoint_index, waiting_state, payload) == ipc_rendezvous_result(old(self).snapshot_u(), cpu_id, endpoint_index, waiting_state, payload),
            final(self).nonlock_view().last().old_u.thread_map[caller_thread_ptr].owning_proc == old(self).snapshot_u().thread_map[caller_thread_ptr].owning_proc,
            final(self).nonlock_view().last().old_u.thread_map[peer_thread_ptr].owning_proc == old(self).snapshot_u().thread_map[peer_thread_ptr].owning_proc,
    {
        reveal(kernel_u_ipc_rendezvous_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_nonlock_kernel_u(self.snapshot_k());
            let caller = pre_u.thread_map.spec_index(caller_thread_ptr);
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& caller.lock_state is Unlocked
            &&& caller.syscall_progress is None
            &&& pre_u.endpoint_map.spec_index(endpoint_ptr).lock_state is Unlocked
            &&& pre_u.thread_map.spec_index(peer_thread_ptr).lock_state is Unlocked
            &&& pre_u.container_map.dom().contains(caller.owning_container)
            &&& pre_u.container_map[caller.owning_container].cpu_set_lock is Unlocked
            &&& pre_u.container_map[pre_u.thread_map.spec_index(peer_thread_ptr).owning_container].cpu_set_lock is Unlocked
            &&& cpu_transfer matches Some((transfer, _)) ==> pre_u.cpu_array[transfer as int].lock_state is Unlocked
        }) by { reveal(kernel_k_to_nonlock_kernel_u); reveal(kernel_ipc_rendezvous_fields); };
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            let caller = pre_u.thread_map.spec_index(caller_thread_ptr);
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& caller.lock_state is Unlocked
            &&& caller.syscall_progress is None
            &&& pre_u.endpoint_map.spec_index(endpoint_ptr).lock_state is Unlocked
            &&& pre_u.thread_map.spec_index(peer_thread_ptr).lock_state is Unlocked
            &&& pre_u.container_map.dom().contains(caller.owning_container)
            &&& cpu_sets_locked ==> pre_u.container_map[caller.owning_container].cpu_set_lock is Unlocked
                && pre_u.container_map[pre_u.thread_map.spec_index(peer_thread_ptr).owning_container].cpu_set_lock is Unlocked
            &&& cpu_transfer matches Some((transfer, _)) ==> pre_u.cpu_array[transfer as int].lock_state is Unlocked
        }) by { reveal(kernel_k_to_kernel_u); reveal(kernel_ipc_rendezvous_fields); };
        assert(self.snapshot_k().prc_mp.dom().contains(self.snapshot_k().thr_mp.spec_index(peer_thread_ptr).view().owning_proc)) by {
            reveal(kernel_ipc_rendezvous_fields); reveal(kernel_process_nonlock_fields_unchanged); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, peer_thread_ptr);
        };
        assert({
            &&& ipc_rendezvous_result(self.nonlock_snapshot_u(), cpu_id, endpoint_index, waiting_state, payload) == ipc_rendezvous_result(self.snapshot_u(), cpu_id, endpoint_index, waiting_state, payload)
            &&& self.nonlock_snapshot_u().thread_map[caller_thread_ptr].owning_proc == self.snapshot_u().thread_map[caller_thread_ptr].owning_proc
            &&& self.nonlock_snapshot_u().thread_map[peer_thread_ptr].owning_proc == self.snapshot_u().thread_map[peer_thread_ptr].owning_proc
        }) by { reveal(kernel_k_to_kernel_u); reveal(kernel_k_to_nonlock_kernel_u); reveal(kernel_ipc_rendezvous_fields); };
        let pre_u = self.nonlock_snapshot_u();
        let post_u = kernel_k_to_nonlock_kernel_u(*krnl);
        assert(kernel_u_ipc_rendezvous_changed(pre_u, post_u, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer)) by {
            kernel_ipc_rendezvous_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer, false);
            reveal(kernel_k_to_nonlock_kernel_u);
        };
        assert(kernel_u_ipc_rendezvous_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, caller_thread_ptr,
            endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer)) by {
            kernel_ipc_rendezvous_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer, true);
            reveal(kernel_k_to_kernel_u);
        };
        self.end_kernel_step_raw(krnl, lctx);
    }

    pub proof fn end_kernel_step_process_quota_4k_changed(tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, delta: int)
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_process_quota_4k_changed(&old(self).snapshot_k(), krnl, cpu_id, process_ptr, container_ptr, delta),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            kernel_u_only_process_quota_4k_changed(final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u, cpu_id, process_ptr, container_ptr, delta),
            kernel_u_only_process_quota_4k_changed(kernel_k_to_kernel_u(old(self).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, container_ptr, delta),
            {
                let old_u = final(self).nonlock_view().last().old_u;
                let cpu = old_u.cpu_array[cpu_id as int];
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_process == Some(process_ptr)
                &&& cpu.owning_container == container_ptr
                &&& old_u.container_map.dom().contains(container_ptr)
                &&& old_u.container_map.spec_index(container_ptr).lock_state is Unlocked
                &&& !old_u.container_map.spec_index(container_ptr).killed
                &&& !old_u.container_map.spec_index(container_ptr).zombie
                &&& old_u.container_map.spec_index(container_ptr).quota_4k >= delta
                &&& old_u.process_map.dom().contains(process_ptr)
                &&& old_u.process_map.spec_index(process_ptr).lock_state is Unlocked
                &&& !old_u.process_map.spec_index(process_ptr).killed
                &&& old_u.process_map.spec_index(process_ptr).quota_4k + delta <= usize::MAX
                &&& delta > 0
            },
            {
                let old_u = kernel_k_to_kernel_u(old(self).snapshot_k());
                let cpu = old_u.cpu_array[cpu_id as int];
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_process == Some(process_ptr)
                &&& cpu.owning_container == container_ptr
                &&& old_u.container_map.dom().contains(container_ptr)
                &&& old_u.container_map.spec_index(container_ptr).lock_state is Unlocked
                &&& !old_u.container_map.spec_index(container_ptr).killed
                &&& !old_u.container_map.spec_index(container_ptr).zombie
                &&& old_u.container_map.spec_index(container_ptr).quota_4k >= delta
                &&& old_u.process_map.dom().contains(process_ptr)
                &&& old_u.process_map.spec_index(process_ptr).lock_state is Unlocked
                &&& !old_u.process_map.spec_index(process_ptr).killed
                &&& old_u.process_map.spec_index(process_ptr).quota_4k + delta <= usize::MAX
                &&& delta > 0
            },
    {
        reveal(kernel_u_only_process_quota_4k_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_nonlock_kernel_u(self.snapshot_k());
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.container_map.spec_index(container_ptr).lock_state is Unlocked
            &&& pre_u.process_map.spec_index(process_ptr).lock_state is Unlocked
        }) by { reveal(kernel_k_to_nonlock_kernel_u); reveal(kernel_process_quota_4k_changed); };
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.container_map.spec_index(container_ptr).lock_state is Unlocked
            &&& pre_u.process_map.spec_index(process_ptr).lock_state is Unlocked
        }) by { reveal(kernel_k_to_kernel_u); reveal(kernel_process_quota_4k_changed); };
        assert(kernel_u_only_process_quota_4k_changed(self.nonlock_snapshot_u(), kernel_k_to_nonlock_kernel_u(*krnl), cpu_id, process_ptr, container_ptr, delta)) by {
            kernel_process_quota_4k_changed_implies_u_step(&self.snapshot_k(), krnl, cpu_id, process_ptr, container_ptr, delta, false);
            reveal(kernel_k_to_nonlock_kernel_u);
        };
        assert(kernel_u_only_process_quota_4k_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, container_ptr, delta)) by {
            kernel_process_quota_4k_changed_implies_u_step(&self.snapshot_k(), krnl, cpu_id, process_ptr, container_ptr, delta, true);
            reveal(kernel_k_to_kernel_u);
        };
        self.end_kernel_step_raw(krnl, lctx);
    }

    pub proof fn end_kernel_step_process2thread_quota_4k_changed(tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, delta: int)
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_process2thread_quota_4k_changed(&old(self).snapshot_k(), krnl, cpu_id, process_ptr, thread_ptr, delta),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            kernel_u_only_process2thread_quota_4k_changed(final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u, cpu_id, process_ptr, thread_ptr, delta),
            kernel_u_only_process2thread_quota_4k_changed(kernel_k_to_kernel_u(old(self).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, thread_ptr, delta),
            {
                let old_u = final(self).nonlock_view().last().old_u;
                let cpu = old_u.cpu_array[cpu_id as int];
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_process == Some(process_ptr)
                &&& cpu.current_thread == Some(thread_ptr)
                &&& old_u.process_map.dom().contains(process_ptr)
                &&& old_u.process_map.spec_index(process_ptr).lock_state is Unlocked
                &&& !old_u.process_map.spec_index(process_ptr).killed
                &&& old_u.process_map.spec_index(process_ptr).quota_4k >= delta
                &&& old_u.thread_map.dom().contains(thread_ptr)
                &&& old_u.thread_map.spec_index(thread_ptr).lock_state is Unlocked
                &&& !old_u.thread_map.spec_index(thread_ptr).killed
                &&& old_u.thread_map.spec_index(thread_ptr).quota_4k + delta <= usize::MAX
                &&& delta > 0
            },
            {
                let old_u = kernel_k_to_kernel_u(old(self).snapshot_k());
                let cpu = old_u.cpu_array[cpu_id as int];
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_process == Some(process_ptr)
                &&& cpu.current_thread == Some(thread_ptr)
                &&& old_u.process_map.dom().contains(process_ptr)
                &&& old_u.process_map.spec_index(process_ptr).lock_state is Unlocked
                &&& !old_u.process_map.spec_index(process_ptr).killed
                &&& old_u.process_map.spec_index(process_ptr).quota_4k >= delta
                &&& old_u.thread_map.dom().contains(thread_ptr)
                &&& old_u.thread_map.spec_index(thread_ptr).lock_state is Unlocked
                &&& !old_u.thread_map.spec_index(thread_ptr).killed
                &&& old_u.thread_map.spec_index(thread_ptr).quota_4k + delta <= usize::MAX
                &&& delta > 0
            },
    {
        reveal(kernel_u_only_process2thread_quota_4k_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_nonlock_kernel_u(self.snapshot_k());
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.process_map.spec_index(process_ptr).lock_state is Unlocked
            &&& pre_u.thread_map.spec_index(thread_ptr).lock_state is Unlocked
        }) by { reveal(kernel_k_to_nonlock_kernel_u); reveal(kernel_process2thread_quota_4k_changed); };
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.process_map.spec_index(process_ptr).lock_state is Unlocked
            &&& pre_u.thread_map.spec_index(thread_ptr).lock_state is Unlocked
        }) by { reveal(kernel_k_to_kernel_u); reveal(kernel_process2thread_quota_4k_changed); };
        assert(kernel_u_only_process2thread_quota_4k_changed(self.nonlock_snapshot_u(), kernel_k_to_nonlock_kernel_u(*krnl), cpu_id, process_ptr, thread_ptr, delta)) by {
            kernel_process2thread_quota_4k_changed_implies_u_step(&self.snapshot_k(), krnl, cpu_id, process_ptr, thread_ptr, delta, false);
            reveal(kernel_k_to_nonlock_kernel_u);
        };
        assert(kernel_u_only_process2thread_quota_4k_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, thread_ptr, delta)) by {
            kernel_process2thread_quota_4k_changed_implies_u_step(&self.snapshot_k(), krnl, cpu_id, process_ptr, thread_ptr, delta, true);
            reveal(kernel_k_to_kernel_u);
        };
        self.end_kernel_step_raw(krnl, lctx);
    }

    pub proof fn end_kernel_step_process_quota_2m_changed(tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, delta: int)
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_process_quota_2m_changed(&old(self).snapshot_k(), krnl, cpu_id, process_ptr, container_ptr, delta),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            kernel_u_only_process_quota_2m_changed(final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u, cpu_id, process_ptr, container_ptr, delta),
            kernel_u_only_process_quota_2m_changed(kernel_k_to_kernel_u(old(self).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, container_ptr, delta),
            {
                let old_u = final(self).nonlock_view().last().old_u;
                let cpu = old_u.cpu_array[cpu_id as int];
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_process == Some(process_ptr)
                &&& cpu.owning_container == container_ptr
                &&& old_u.container_map.dom().contains(container_ptr)
                &&& old_u.container_map.spec_index(container_ptr).lock_state is Unlocked
                &&& !old_u.container_map.spec_index(container_ptr).killed
                &&& !old_u.container_map.spec_index(container_ptr).zombie
                &&& old_u.container_map.spec_index(container_ptr).quota_2m >= delta
                &&& old_u.process_map.dom().contains(process_ptr)
                &&& old_u.process_map.spec_index(process_ptr).lock_state is Unlocked
                &&& !old_u.process_map.spec_index(process_ptr).killed
                &&& old_u.process_map.spec_index(process_ptr).quota_2m + delta <= usize::MAX
                &&& delta > 0
            },
            {
                let old_u = kernel_k_to_kernel_u(old(self).snapshot_k());
                let cpu = old_u.cpu_array[cpu_id as int];
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_process == Some(process_ptr)
                &&& cpu.owning_container == container_ptr
                &&& old_u.container_map.dom().contains(container_ptr)
                &&& old_u.container_map.spec_index(container_ptr).lock_state is Unlocked
                &&& !old_u.container_map.spec_index(container_ptr).killed
                &&& !old_u.container_map.spec_index(container_ptr).zombie
                &&& old_u.container_map.spec_index(container_ptr).quota_2m >= delta
                &&& old_u.process_map.dom().contains(process_ptr)
                &&& old_u.process_map.spec_index(process_ptr).lock_state is Unlocked
                &&& !old_u.process_map.spec_index(process_ptr).killed
                &&& old_u.process_map.spec_index(process_ptr).quota_2m + delta <= usize::MAX
                &&& delta > 0
            },
    {
        reveal(kernel_u_only_process_quota_2m_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_nonlock_kernel_u(self.snapshot_k());
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.container_map.spec_index(container_ptr).lock_state is Unlocked
            &&& pre_u.process_map.spec_index(process_ptr).lock_state is Unlocked
        }) by { reveal(kernel_k_to_nonlock_kernel_u); reveal(kernel_process_quota_2m_changed); };
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.container_map.spec_index(container_ptr).lock_state is Unlocked
            &&& pre_u.process_map.spec_index(process_ptr).lock_state is Unlocked
        }) by { reveal(kernel_k_to_kernel_u); reveal(kernel_process_quota_2m_changed); };
        assert(kernel_u_only_process_quota_2m_changed(self.nonlock_snapshot_u(), kernel_k_to_nonlock_kernel_u(*krnl), cpu_id, process_ptr, container_ptr, delta)) by {
            kernel_process_quota_2m_changed_implies_u_step(&self.snapshot_k(), krnl, cpu_id, process_ptr, container_ptr, delta, false);
            reveal(kernel_k_to_nonlock_kernel_u);
        };
        assert(kernel_u_only_process_quota_2m_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, container_ptr, delta)) by {
            kernel_process_quota_2m_changed_implies_u_step(&self.snapshot_k(), krnl, cpu_id, process_ptr, container_ptr, delta, true);
            reveal(kernel_k_to_kernel_u);
        };
        self.end_kernel_step_raw(krnl, lctx);
    }

    pub proof fn end_kernel_step_process2thread_quota_2m_changed(tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, delta: int)
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_process2thread_quota_2m_changed(&old(self).snapshot_k(), krnl, cpu_id, process_ptr, thread_ptr, delta),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            kernel_u_only_process2thread_quota_2m_changed(final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u, cpu_id, process_ptr, thread_ptr, delta),
            kernel_u_only_process2thread_quota_2m_changed(kernel_k_to_kernel_u(old(self).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, thread_ptr, delta),
            {
                let old_u = final(self).nonlock_view().last().old_u;
                let cpu = old_u.cpu_array[cpu_id as int];
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_process == Some(process_ptr)
                &&& cpu.current_thread == Some(thread_ptr)
                &&& old_u.process_map.dom().contains(process_ptr)
                &&& old_u.process_map.spec_index(process_ptr).lock_state is Unlocked
                &&& !old_u.process_map.spec_index(process_ptr).killed
                &&& old_u.process_map.spec_index(process_ptr).quota_2m >= delta
                &&& old_u.thread_map.dom().contains(thread_ptr)
                &&& old_u.thread_map.spec_index(thread_ptr).lock_state is Unlocked
                &&& !old_u.thread_map.spec_index(thread_ptr).killed
                &&& old_u.thread_map.spec_index(thread_ptr).quota_2m + delta <= usize::MAX
                &&& delta > 0
            },
            {
                let old_u = kernel_k_to_kernel_u(old(self).snapshot_k());
                let cpu = old_u.cpu_array[cpu_id as int];
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_process == Some(process_ptr)
                &&& cpu.current_thread == Some(thread_ptr)
                &&& old_u.process_map.dom().contains(process_ptr)
                &&& old_u.process_map.spec_index(process_ptr).lock_state is Unlocked
                &&& !old_u.process_map.spec_index(process_ptr).killed
                &&& old_u.process_map.spec_index(process_ptr).quota_2m >= delta
                &&& old_u.thread_map.dom().contains(thread_ptr)
                &&& old_u.thread_map.spec_index(thread_ptr).lock_state is Unlocked
                &&& !old_u.thread_map.spec_index(thread_ptr).killed
                &&& old_u.thread_map.spec_index(thread_ptr).quota_2m + delta <= usize::MAX
                &&& delta > 0
            },
    {
        reveal(kernel_u_only_process2thread_quota_2m_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_nonlock_kernel_u(self.snapshot_k());
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.process_map.spec_index(process_ptr).lock_state is Unlocked
            &&& pre_u.thread_map.spec_index(thread_ptr).lock_state is Unlocked
        }) by { reveal(kernel_k_to_nonlock_kernel_u); reveal(kernel_process2thread_quota_2m_changed); };
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.process_map.spec_index(process_ptr).lock_state is Unlocked
            &&& pre_u.thread_map.spec_index(thread_ptr).lock_state is Unlocked
        }) by { reveal(kernel_k_to_kernel_u); reveal(kernel_process2thread_quota_2m_changed); };
        assert(kernel_u_only_process2thread_quota_2m_changed(self.nonlock_snapshot_u(), kernel_k_to_nonlock_kernel_u(*krnl), cpu_id, process_ptr, thread_ptr, delta)) by {
            kernel_process2thread_quota_2m_changed_implies_u_step(&self.snapshot_k(), krnl, cpu_id, process_ptr, thread_ptr, delta, false);
            reveal(kernel_k_to_nonlock_kernel_u);
        };
        assert(kernel_u_only_process2thread_quota_2m_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, thread_ptr, delta)) by {
            kernel_process2thread_quota_2m_changed_implies_u_step(&self.snapshot_k(), krnl, cpu_id, process_ptr, thread_ptr, delta, true);
            reveal(kernel_k_to_kernel_u);
        };
        self.end_kernel_step_raw(krnl, lctx);
    }

    /// Records the offline-request step of `syscall_cpu_offline_request` or `syscall_cpu_offline_request_child`.
    pub proof fn end_kernel_step_cpu_offline_request_changed(tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, container_ptr: RwLockContainerPtr, target: CpuId)
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_cpu_offline_request_changed(&old(self).snapshot_k(), krnl, cpu_id, container_ptr, target),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            kernel_u_cpu_offline_request_changed(final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u, cpu_id, container_ptr, target),
            kernel_u_cpu_offline_request_changed(kernel_k_to_kernel_u(old(self).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, container_ptr, target),
            {
                let old_u = kernel_k_to_kernel_u(old(self).snapshot_k());
                let owner = old_u.cpu_array[cpu_id as int].owning_container;
                &&& old_u.cpu_array[cpu_id as int].lock_state is Unlocked
                &&& old_u.container_map[container_ptr].cpu_set_lock is Unlocked
                &&& owner == old(self).snapshot_k().cpu_arr.spec_index(cpu_id).value.view().view().owning_container
                &&& owner != container_ptr ==> old_u.container_map[owner].lock_state is Unlocked
            },
            {
                let old_u = final(self).nonlock_view().last().old_u;
                let owner = old_u.cpu_array[cpu_id as int].owning_container;
                &&& old_u.cpu_array[cpu_id as int].lock_state is Unlocked
                &&& old_u.container_map[container_ptr].cpu_set_lock is Unlocked
                &&& owner == old(self).snapshot_k().cpu_arr.spec_index(cpu_id).value.view().view().owning_container
                &&& owner != container_ptr ==> old_u.container_map[owner].lock_state is Unlocked
            },
    {
        reveal(kernel_u_cpu_offline_request_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_nonlock_kernel_u(self.snapshot_k());
            let owner = pre_u.cpu_array[cpu_id as int].owning_container;
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.container_map[container_ptr].cpu_set_lock is Unlocked
            &&& owner == self.snapshot_k().cpu_arr.spec_index(cpu_id).value.view().view().owning_container
            &&& owner != container_ptr ==> pre_u.container_map[owner].lock_state is Unlocked
        }) by { reveal(kernel_k_to_nonlock_kernel_u); reveal(kernel_cpu_offline_request_changed); };
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            let owner = pre_u.cpu_array[cpu_id as int].owning_container;
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.container_map[container_ptr].cpu_set_lock is Unlocked
            &&& owner == self.snapshot_k().cpu_arr.spec_index(cpu_id).value.view().view().owning_container
            &&& owner != container_ptr ==> pre_u.container_map[owner].lock_state is Unlocked
        }) by { reveal(kernel_k_to_kernel_u); reveal(kernel_cpu_offline_request_changed); };
        assert(kernel_u_cpu_offline_request_changed(self.nonlock_snapshot_u(), kernel_k_to_nonlock_kernel_u(*krnl), cpu_id, container_ptr, target)) by {
            kernel_cpu_offline_request_changed_implies_u_step(&self.snapshot_k(), krnl, cpu_id, container_ptr, target, false);
            reveal(kernel_k_to_nonlock_kernel_u);
        };
        assert(kernel_u_cpu_offline_request_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, container_ptr, target)) by {
            kernel_cpu_offline_request_changed_implies_u_step(&self.snapshot_k(), krnl, cpu_id, container_ptr, target, true);
            reveal(kernel_k_to_kernel_u);
        };
        self.end_kernel_step_raw(krnl, lctx);
    }

    /// Records the online step of `syscall_cpu_online` or `syscall_cpu_online_child`.
    pub proof fn end_kernel_step_cpu_online_changed(tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, container_ptr: RwLockContainerPtr, target: CpuId)
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_cpu_online_changed(&old(self).snapshot_k(), krnl, cpu_id, container_ptr, target),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            kernel_u_cpu_online_changed(final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u, cpu_id, container_ptr, target),
            kernel_u_cpu_online_changed(kernel_k_to_kernel_u(old(self).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, container_ptr, target),
            {
                let old_u = kernel_k_to_kernel_u(old(self).snapshot_k());
                let owner = old_u.cpu_array[cpu_id as int].owning_container;
                &&& old_u.cpu_array[cpu_id as int].lock_state is Unlocked
                &&& old_u.cpu_array[target as int].lock_state is Unlocked
                &&& old_u.container_map[container_ptr].cpu_set_lock is Unlocked
                &&& owner == old(self).snapshot_k().cpu_arr.spec_index(cpu_id).value.view().view().owning_container
                &&& owner != container_ptr ==> old_u.container_map[owner].lock_state is Unlocked
            },
            {
                let old_u = final(self).nonlock_view().last().old_u;
                let owner = old_u.cpu_array[cpu_id as int].owning_container;
                &&& old_u.cpu_array[cpu_id as int].lock_state is Unlocked
                &&& old_u.cpu_array[target as int].lock_state is Unlocked
                &&& old_u.container_map[container_ptr].cpu_set_lock is Unlocked
                &&& owner == old(self).snapshot_k().cpu_arr.spec_index(cpu_id).value.view().view().owning_container
                &&& owner != container_ptr ==> old_u.container_map[owner].lock_state is Unlocked
            },
    {
        reveal(kernel_u_cpu_online_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_nonlock_kernel_u(self.snapshot_k());
            let owner = pre_u.cpu_array[cpu_id as int].owning_container;
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.cpu_array[target as int].lock_state is Unlocked
            &&& pre_u.container_map[container_ptr].cpu_set_lock is Unlocked
            &&& owner == self.snapshot_k().cpu_arr.spec_index(cpu_id).value.view().view().owning_container
            &&& owner != container_ptr ==> pre_u.container_map[owner].lock_state is Unlocked
        }) by { reveal(kernel_k_to_nonlock_kernel_u); reveal(kernel_cpu_online_changed); };
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            let owner = pre_u.cpu_array[cpu_id as int].owning_container;
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.cpu_array[target as int].lock_state is Unlocked
            &&& pre_u.container_map[container_ptr].cpu_set_lock is Unlocked
            &&& owner == self.snapshot_k().cpu_arr.spec_index(cpu_id).value.view().view().owning_container
            &&& owner != container_ptr ==> pre_u.container_map[owner].lock_state is Unlocked
        }) by { reveal(kernel_k_to_kernel_u); reveal(kernel_cpu_online_changed); };
        assert(kernel_u_cpu_online_changed(self.nonlock_snapshot_u(), kernel_k_to_nonlock_kernel_u(*krnl), cpu_id, container_ptr, target)) by {
            kernel_cpu_online_changed_implies_u_step(&self.snapshot_k(), krnl, cpu_id, container_ptr, target, false);
            reveal(kernel_k_to_nonlock_kernel_u);
        };
        assert(kernel_u_cpu_online_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, container_ptr, target)) by {
            kernel_cpu_online_changed_implies_u_step(&self.snapshot_k(), krnl, cpu_id, container_ptr, target, true);
            reveal(kernel_k_to_kernel_u);
        };
        self.end_kernel_step_raw(krnl, lctx);
    }

    /// Records the attach step of `syscall_pci_attach_dma`: every lock is released again and only the
    /// context entry of `(bus, device, function)` now points at `root`.
    pub proof fn end_kernel_step_pci_attach(
        tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr, bus: usize, device: usize, function: usize,
        root: PageTableRoot,
    )
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            index_valid(NUM_CPUS, cpu_id),
            old(self).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
            old(self).snapshot_k().cpu_arr.spec_index(cpu_id).value.view().view().state is Running,
            old(self).snapshot_k().cpu_arr.spec_index(cpu_id).value.view().view().current_process == Some(process_ptr),
            old(self).snapshot_k().prc_mp.dom().contains(process_ptr),
            old(self).snapshot_k().prc_mp.spec_index(process_ptr).locking_thread() is None,
            !old(self).snapshot_k().prc_mp.spec_index(process_ptr).being_killed(),
            !old(self).snapshot_k().prc_mp.spec_index(process_ptr).view().zombie,
            old(self).snapshot_k().prc_mp.spec_index(process_ptr).view().iommu_table is Some,
            old(self).snapshot_k().prc_mp.spec_index(process_ptr).view_ghost().owned_pci_functions.view().contains((bus, device, function)),
            pci_bdf_valid(bus, device, function),
            old(self).snapshot_k().irt.view().spec_index_iommu_root(bus, device, function) is None,
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(self).snapshot_k(), krnl),
            kernel_endpoint_nonlock_fields_unchanged(old(self).snapshot_k().ep_mp, krnl.ep_mp),
            krnl.irt.view().owners() == old(self).snapshot_k().irt.view().owners(),
            krnl.irt.view().iommu_roots() == seq3_update(old(self).snapshot_k().irt.view().iommu_roots(), bus as int, device as int, function as int, Some(root)),
            krnl.cpu_tlb.view() == old(self).snapshot_k().cpu_tlb.view(),
            krnl.iommu_tlb.view() == old(self).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(self).snapshot_k(), krnl),
            forall|p: RwLockContainerPtr| #![trigger krnl.ctn_mp.spec_index(p)]
                krnl.ctn_mp.dom().contains(p) && old(self).snapshot_k().ctn_mp.dom().contains(p) ==> {
                    let before = old(self).snapshot_k().ctn_mp.spec_index(p).locking_thread();
                    let after = krnl.ctn_mp.spec_index(p).locking_thread();
                    &&& (after is Write) == (before is Write)
                    &&& (after is Read) == (before is Read)
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
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            kernel_u_pci_attach_changed(final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u, cpu_id, bus, device, function),
            kernel_u_pci_attach_changed(kernel_k_to_kernel_u(old(self).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, bus, device, function),
            kernel_k_to_kernel_u(old(self).snapshot_k()).cpu_array[cpu_id as int].lock_state is Unlocked,
            kernel_k_to_kernel_u(old(self).snapshot_k()).cpu_array[cpu_id as int].current_process == Some(process_ptr),
            kernel_k_to_kernel_u(old(self).snapshot_k()).process_map[process_ptr].lock_state is Unlocked,
            final(self).nonlock_view().last().old_u.cpu_array[cpu_id as int].lock_state is Unlocked,
            final(self).nonlock_view().last().old_u.cpu_array[cpu_id as int].current_process == Some(process_ptr),
            final(self).nonlock_view().last().old_u.process_map[process_ptr].lock_state is Unlocked,
    {
        reveal(kernel_u_pci_attach_changed);
        use_type_invariant(&*self);
        let snap = self.snapshot_k();
        let mid = KernelK { irt: krnl.irt, ..snap };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&mid, krnl)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&mid, krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
        kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&mid, krnl);
        kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(&mid, krnl);
        assert({
            let pre_u = kernel_k_to_kernel_u(snap);
            let attached = seq3_update(pre_u.iommu_root_table.attached, bus as int, device as int, function as int, true);
            &&& kernel_k_to_kernel_u(mid) == (KernelU { iommu_root_table: IommuRootTableU { attached, ..pre_u.iommu_root_table }, ..pre_u })
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.cpu_array[cpu_id as int].state is Running
            &&& pre_u.cpu_array[cpu_id as int].current_process == Some(process_ptr)
            &&& pre_u.process_map.dom().contains(process_ptr)
            &&& pre_u.process_map[process_ptr].lock_state is Unlocked
            &&& !pre_u.process_map[process_ptr].killed
            &&& pre_u.process_map[process_ptr].owned_pci_functions.contains((bus, device, function))
            &&& pre_u.process_map[process_ptr].iommu_table is Some
            &&& !pre_u.iommu_root_table.attached[bus as int][device as int][function as int]
        }) by {
            reveal(kernel_k_to_kernel_u); reveal(IommuRootTable::user_view);
            let pre_u = kernel_k_to_kernel_u(snap);
            let mid_u = kernel_k_to_kernel_u(mid);
            let attached = seq3_update(pre_u.iommu_root_table.attached, bus as int, device as int, function as int, true);
            assert_seqs_equal!(mid_u.iommu_root_table.attached == attached, b => {
                assert_seqs_equal!(mid_u.iommu_root_table.attached[b] == attached[b], d => {
                    assert_seqs_equal!(mid_u.iommu_root_table.attached[b][d] == attached[b][d], f => {});
                });
            });
            assert_seqs_equal!(mid_u.cpu_array == pre_u.cpu_array);
            assert_maps_equal!(mid_u.container_map, pre_u.container_map, c => {});
            assert_maps_equal!(mid_u.process_map, pre_u.process_map, p => {});
            assert_maps_equal!(mid_u.thread_map, pre_u.thread_map, t => {});
            assert_maps_equal!(mid_u.endpoint_map, pre_u.endpoint_map, e => {});
        };
        assert({
            let pre_u = kernel_k_to_nonlock_kernel_u(snap);
            let attached = seq3_update(pre_u.iommu_root_table.attached, bus as int, device as int, function as int, true);
            &&& kernel_k_to_nonlock_kernel_u(mid) == (KernelU { iommu_root_table: IommuRootTableU { attached, ..pre_u.iommu_root_table }, ..pre_u })
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.cpu_array[cpu_id as int].state is Running
            &&& pre_u.cpu_array[cpu_id as int].current_process == Some(process_ptr)
            &&& pre_u.process_map.dom().contains(process_ptr)
            &&& pre_u.process_map[process_ptr].lock_state is Unlocked
            &&& !pre_u.process_map[process_ptr].killed
            &&& pre_u.process_map[process_ptr].owned_pci_functions.contains((bus, device, function))
            &&& pre_u.process_map[process_ptr].iommu_table is Some
            &&& !pre_u.iommu_root_table.attached[bus as int][device as int][function as int]
        }) by {
            reveal(kernel_k_to_nonlock_kernel_u); reveal(IommuRootTable::user_view);
            let pre_u = kernel_k_to_nonlock_kernel_u(snap);
            let mid_u = kernel_k_to_nonlock_kernel_u(mid);
            let attached = seq3_update(pre_u.iommu_root_table.attached, bus as int, device as int, function as int, true);
            assert_seqs_equal!(mid_u.iommu_root_table.attached == attached, b => {
                assert_seqs_equal!(mid_u.iommu_root_table.attached[b] == attached[b], d => {
                    assert_seqs_equal!(mid_u.iommu_root_table.attached[b][d] == attached[b][d], f => {});
                });
            });
            assert_seqs_equal!(mid_u.cpu_array == pre_u.cpu_array);
            assert_maps_equal!(mid_u.container_map, pre_u.container_map, c => {});
            assert_maps_equal!(mid_u.process_map, pre_u.process_map, p => {});
            assert_maps_equal!(mid_u.thread_map, pre_u.thread_map, t => {});
            assert_maps_equal!(mid_u.endpoint_map, pre_u.endpoint_map, e => {});
        };
        self.end_kernel_step_raw(krnl, lctx);
    }

    pub proof fn end_kernel_step_cpu_went_off(tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, regs: Registers, flushed_default_pcid: bool)
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_cpu_went_off_fields(&old(self).snapshot_k(), krnl, cpu_id, regs, flushed_default_pcid),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            kernel_u_cpu_went_off_changed(final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u, cpu_id, regs, flushed_default_pcid),
            kernel_u_cpu_went_off_changed(kernel_k_to_kernel_u(old(self).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, regs, flushed_default_pcid),
            {
                let old_u = final(self).nonlock_view().last().old_u;
                let cpu = old_u.cpu_array[cpu_id as int];
                &&& cpu.lock_state is Unlocked
                &&& old_u.container_map[cpu.owning_container].cpu_set_lock is Unlocked
                &&& (cpu.current_thread is Some ==> old_u.thread_map[cpu.current_thread.unwrap()].lock_state is Unlocked && old_u.process_map[cpu.current_process.unwrap()].lock_state is Unlocked)
            },
            {
                let old_u = kernel_k_to_kernel_u(old(self).snapshot_k());
                let cpu = old_u.cpu_array[cpu_id as int];
                &&& cpu.lock_state is Unlocked
                &&& old_u.container_map[cpu.owning_container].cpu_set_lock is Unlocked
                &&& (cpu.current_thread is Some ==> old_u.thread_map[cpu.current_thread.unwrap()].lock_state is Unlocked && old_u.process_map[cpu.current_process.unwrap()].lock_state is Unlocked)
            },
    {
        reveal(kernel_u_cpu_went_off_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_nonlock_kernel_u(self.snapshot_k());
            let cpu = pre_u.cpu_array[cpu_id as int];
            &&& cpu.lock_state is Unlocked
            &&& pre_u.container_map[cpu.owning_container].cpu_set_lock is Unlocked
            &&& (cpu.current_thread is Some ==> pre_u.thread_map[cpu.current_thread.unwrap()].lock_state is Unlocked && pre_u.process_map[cpu.current_process.unwrap()].lock_state is Unlocked)
        }) by { reveal(kernel_k_to_nonlock_kernel_u); reveal(kernel_cpu_went_off_fields); };
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            let cpu = pre_u.cpu_array[cpu_id as int];
            &&& cpu.lock_state is Unlocked
            &&& pre_u.container_map[cpu.owning_container].cpu_set_lock is Unlocked
            &&& (cpu.current_thread is Some ==> pre_u.thread_map[cpu.current_thread.unwrap()].lock_state is Unlocked && pre_u.process_map[cpu.current_process.unwrap()].lock_state is Unlocked)
        }) by { reveal(kernel_k_to_kernel_u); reveal(kernel_cpu_went_off_fields); };
        assert(kernel_u_cpu_went_off_changed(self.nonlock_snapshot_u(), kernel_k_to_nonlock_kernel_u(*krnl), cpu_id, regs, flushed_default_pcid)) by {
            kernel_cpu_went_off_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, regs, flushed_default_pcid, false);
            reveal(kernel_k_to_nonlock_kernel_u);
        };
        assert(kernel_u_cpu_went_off_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, regs, flushed_default_pcid)) by {
            kernel_cpu_went_off_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, regs, flushed_default_pcid, true);
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
