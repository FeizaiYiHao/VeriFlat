use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal, assert_sets_equal};
use crate::*;
use super::implementation::create_thread_from_staged_page::kernel_u_new_thread_changed;
use super::implementation::create_process_from_staged_pages::{create_process_from_staged_pages_kernel_state_framing, kernel_u_create_process_changed};
use super::implementation::create_process_with_iommu_from_staged_pages::{
    create_process_with_iommu_from_staged_pages_kernel_state_framing, kernel_u_create_process_with_iommu_changed,
};

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
            krnl.irt.owners() == old(self).snapshot_k().irt.owners(),
            krnl.irt.iommu_roots() == old(self).snapshot_k().irt.iommu_roots(),
            krnl.cpu_tlb.view() == old(self).snapshot_k().cpu_tlb.view(),
            krnl.iommu_tlb.view() == old(self).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(self).snapshot_k(), krnl),
        ensures
            final(self).view() == old(self).view(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).nonlock_view() == old(self).nonlock_view(),
            final(self).snapshot_u() == old(self).snapshot_u(),
            krnl.irt.owners() == final(self).snapshot_k().irt.owners(),
            krnl.irt.iommu_roots() == final(self).snapshot_k().irt.iommu_roots(),
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
        reveal(KernelK::inv);
        assert(self.nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl)) by {
            kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(&self.snapshot_k(), krnl);
        };
        if self.snapshot_u() == kernel_k_to_kernel_u(*krnl) {
            *self = KernelSteps { steps: self.steps, snapshot_k: *krnl, snapshot_u: self.snapshot_u };
        }
        assert(kernel_endpoint_nonlock_fields_unchanged(self.snapshot_k().ep_mp, krnl.ep_mp)) by { broadcast use kernel_endpoint_nonlock_fields_unchanged_for_equal; };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&self.snapshot_k(), krnl)) by {
            broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
        };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&self.snapshot_k(), krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
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
            krnl.irt.owners() == old(self).snapshot_k().irt.owners(),
            krnl.irt.iommu_roots() == old(self).snapshot_k().irt.iommu_roots(),
            krnl.cpu_tlb.view() == old(self).snapshot_k().cpu_tlb.view(),
            krnl.iommu_tlb.view() == old(self).snapshot_k().iommu_tlb.view(),
            krnl.dflt_pt == old(self).snapshot_k().dflt_pt,
            krnl.cpu_arr.unchanged_except(&old(self).snapshot_k().cpu_arr, cpu),
            (krnl.cpu_arr.spec_index(cpu).value.locking_thread() is Write) == (old(self).snapshot_k().cpu_arr.spec_index(cpu).value.locking_thread() is Write),
            (krnl.cpu_arr.spec_index(cpu).value.locking_thread() is Read) == (old(self).snapshot_k().cpu_arr.spec_index(cpu).value.locking_thread() is Read),
            krnl.it_mp == old(self).snapshot_k().it_mp,
            krnl.cpu_set_mp == old(self).snapshot_k().cpu_set_mp,
            krnl.sched_mp == old(self).snapshot_k().sched_mp,
            krnl.allc_4k_mp == old(self).snapshot_k().allc_4k_mp,
            krnl.allc_2m_mp == old(self).snapshot_k().allc_2m_mp,
            krnl.allc_1g_mp == old(self).snapshot_k().allc_1g_mp,
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
            reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
        };
        assert(kernel_endpoint_nonlock_fields_unchanged(self.snapshot_k().ep_mp, krnl.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&self.snapshot_k(), krnl)) by {
            reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_pcid_allocator_wf);
        };
        self.end_kernel_step_unchanged(krnl, lctx);
    }

    pub proof fn end_kernel_step_unchanged(tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext)
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(self).snapshot_k(), krnl),
            kernel_endpoint_nonlock_fields_unchanged(old(self).snapshot_k().ep_mp, krnl.ep_mp),
            krnl.irt.owners() == old(self).snapshot_k().irt.owners(),
            krnl.irt.iommu_roots() == old(self).snapshot_k().irt.iommu_roots(),
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
        assert(kernel_k_to_nonlock_kernel_u(*krnl) == self.nonlock_snapshot_u()) by {
            kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(&self.snapshot_k(), krnl);
        };
        *self = KernelSteps { steps: self.steps, snapshot_k: *krnl, snapshot_u: self.snapshot_u };
        assert(kernel_endpoint_nonlock_fields_unchanged(self.snapshot_k().ep_mp, krnl.ep_mp)) by { broadcast use kernel_endpoint_nonlock_fields_unchanged_for_equal; };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&self.snapshot_k(), krnl)) by {
            broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
        };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&self.snapshot_k(), krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
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
        assert(self.nonlock_snapshot_u() == kernel_u_nonlock_fields(self.snapshot_u())
            && kernel_k_to_nonlock_kernel_u(*krnl) == kernel_u_nonlock_fields(kernel_k_to_kernel_u(*krnl))) by {
            reveal(kernel_k_to_kernel_u); reveal(kernel_k_to_nonlock_kernel_u); reveal(kernel_u_nonlock_fields);
            assert_seqs_equal!(self.nonlock_snapshot_u().cpu_array == kernel_u_nonlock_fields(self.snapshot_u()).cpu_array);
            assert_maps_equal!(self.nonlock_snapshot_u().container_map, kernel_u_nonlock_fields(self.snapshot_u()).container_map, p => {});
            assert_maps_equal!(self.nonlock_snapshot_u().process_map, kernel_u_nonlock_fields(self.snapshot_u()).process_map, p => {});
            assert_maps_equal!(self.nonlock_snapshot_u().thread_map, kernel_u_nonlock_fields(self.snapshot_u()).thread_map, p => {});
            assert_maps_equal!(self.nonlock_snapshot_u().endpoint_map, kernel_u_nonlock_fields(self.snapshot_u()).endpoint_map, p => {});
            assert_seqs_equal!(kernel_k_to_nonlock_kernel_u(*krnl).cpu_array == kernel_u_nonlock_fields(kernel_k_to_kernel_u(*krnl)).cpu_array);
            assert_maps_equal!(kernel_k_to_nonlock_kernel_u(*krnl).container_map, kernel_u_nonlock_fields(kernel_k_to_kernel_u(*krnl)).container_map, p => {});
            assert_maps_equal!(kernel_k_to_nonlock_kernel_u(*krnl).process_map, kernel_u_nonlock_fields(kernel_k_to_kernel_u(*krnl)).process_map, p => {});
            assert_maps_equal!(kernel_k_to_nonlock_kernel_u(*krnl).thread_map, kernel_u_nonlock_fields(kernel_k_to_kernel_u(*krnl)).thread_map, p => {});
            assert_maps_equal!(kernel_k_to_nonlock_kernel_u(*krnl).endpoint_map, kernel_u_nonlock_fields(kernel_k_to_kernel_u(*krnl)).endpoint_map, p => {});
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
            krnl.irt.owners() == old(self).snapshot_k().irt.owners(),
            krnl.irt.iommu_roots() == old(self).snapshot_k().irt.iommu_roots(),
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
            final(self).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
    {
        use_type_invariant(&*self);
        assert(self.nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl)) by {
            kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(&self.snapshot_k(), krnl);
        };
        self.end_kernel_step_raw(krnl, lctx);
    }

    pub proof fn end_kernel_step_new_thread(
        tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
        new_thread_ptr: RwLockThreadPtr, initial_regs: Registers, initial_endpoint: Option<RwLockEndpointPtr>, staging_progress: Option<SyscallProgress>,
    )
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_new_thread_fields(&old(self).snapshot_k(), krnl, process_ptr, staging_thread_ptr, container_ptr, new_thread_ptr, initial_regs, initial_endpoint, staging_progress),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            final(self).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
            final(self).nonlock_view().last().new_u.process_map.spec_index(process_ptr).owned_threads.last() == new_thread_ptr,
            kernel_u_new_thread_changed(final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u,
                process_ptr, staging_thread_ptr, container_ptr, new_thread_ptr, initial_regs, initial_endpoint, staging_progress),
    {
        use_type_invariant(&*self);
        assert(kernel_u_new_thread_changed(self.nonlock_snapshot_u(), kernel_k_to_nonlock_kernel_u(*krnl),
            process_ptr, staging_thread_ptr, container_ptr, new_thread_ptr, initial_regs, initial_endpoint, staging_progress)) by {
            kernel_new_thread_fields_implies_u_step(&self.snapshot_k(), krnl, process_ptr, staging_thread_ptr, container_ptr, new_thread_ptr, initial_regs, initial_endpoint, staging_progress);
        };
        assert(self.nonlock_snapshot_u() != kernel_k_to_nonlock_kernel_u(*krnl)
            && kernel_k_to_nonlock_kernel_u(*krnl).process_map.spec_index(process_ptr).owned_threads.last() == new_thread_ptr) by { reveal(kernel_u_new_thread_changed); };
        assert(self.snapshot_u() != kernel_k_to_kernel_u(*krnl)) by { reveal(kernel_new_thread_fields); reveal(kernel_k_to_kernel_u); };
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
            kernel_new_thread_fields(&old(self).snapshot_k(), krnl, process_ptr, staging_thread_ptr, container_ptr, new_thread_ptr, initial_regs, initial_endpoint, staging_progress),
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
            final(self).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
            final(self).nonlock_view().last().new_u.process_map.spec_index(process_ptr).owned_threads.last() == new_thread_ptr,
            kernel_u_new_thread_changed(final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u,
                process_ptr, staging_thread_ptr, container_ptr, new_thread_ptr, initial_regs, initial_endpoint, staging_progress),
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
        self.end_kernel_step_new_thread(krnl, lctx, process_ptr, staging_thread_ptr, container_ptr, new_thread_ptr, initial_regs, initial_endpoint, staging_progress);
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
        }) by { reveal(kernel_k_to_nonlock_kernel_u); reveal(kernel_new_thread_fields); reveal(kernel_u_new_thread_changed); };
    }

    #[verifier::spinoff_prover]
    pub proof fn end_kernel_step_thread_state_changed(
        tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, thread_ptr: RwLockThreadPtr, old_state: ThreadState, new_state: ThreadState,
    )
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
            final(self).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
            final(self).nonlock_view().last().old_u.thread_map.dom().contains(thread_ptr),
            final(self).nonlock_view().last().old_u.thread_map.spec_index(thread_ptr).state == old_state,
            final(self).nonlock_view().last().new_u.thread_map.dom().contains(thread_ptr),
            final(self).nonlock_view().last().new_u.thread_map.spec_index(thread_ptr).state == new_state,
    {
        use_type_invariant(&*self);
        kernel_thread_state_changed_implies_u_neq(&self.snapshot_k(), krnl, thread_ptr);
        assert(self.nonlock_snapshot_u().thread_map.dom().contains(thread_ptr)
            && self.nonlock_snapshot_u().thread_map.spec_index(thread_ptr).state == old_state) by { reveal(kernel_k_to_nonlock_kernel_u); };
        assert(kernel_k_to_nonlock_kernel_u(*krnl).thread_map.dom().contains(thread_ptr)
            && kernel_k_to_nonlock_kernel_u(*krnl).thread_map.spec_index(thread_ptr).state == new_state) by { reveal(kernel_k_to_nonlock_kernel_u); };
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
            final(self).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
    {
        use_type_invariant(&*self);
        assert(self.nonlock_snapshot_u().thread_map.spec_index(thread_ptr).syscall_progress != kernel_k_to_nonlock_kernel_u(*krnl).thread_map.spec_index(thread_ptr).syscall_progress) by { reveal(kernel_k_to_nonlock_kernel_u); };
        assert(self.snapshot_u().thread_map.spec_index(thread_ptr).syscall_progress != kernel_k_to_kernel_u(*krnl).thread_map.spec_index(thread_ptr).syscall_progress) by { reveal(kernel_k_to_kernel_u); };
        self.end_kernel_step_raw(krnl, lctx);
    }

    #[verifier::spinoff_prover]
    pub proof fn end_kernel_step_context_switch(
        tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, next_thread: RwLockThreadPtr,
        entry_regs: Registers, flushed_pcid: Option<Pcid>,
    )
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
            final(self).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
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
                &&& container.scheduler.len() > 0
                &&& container.scheduler[0] == next_thread
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
                &&& container.scheduler.len() > 0
                &&& container.scheduler[0] == next_thread
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
            final(self).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
            kernel_u_ipc_block_changed(
                final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u, cpu_id, thread_ptr, endpoint_ptr,
                endpoint_index, waiting_state, payload, regs, flushed_default_pcid,
            ),
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
                &&& old_u.process_map.dom().contains(thread.owning_proc)
                &&& old_u.process_map.spec_index(thread.owning_proc).lock_state is Unlocked
                &&& !old_u.process_map.spec_index(thread.owning_proc).killed
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
                &&& old_u.process_map.dom().contains(thread.owning_proc)
                &&& old_u.process_map.spec_index(thread.owning_proc).lock_state is Unlocked
                &&& !old_u.process_map.spec_index(thread.owning_proc).killed
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
            &&& pre_u.process_map.spec_index(thread.owning_proc).lock_state is Unlocked
            &&& thread.lock_state is Unlocked
            &&& thread.syscall_progress is None
            &&& pre_u.endpoint_map.spec_index(endpoint_ptr).lock_state is Unlocked
            &&& pre_u.container_map.dom().contains(thread.owning_container)
        }) by { reveal(kernel_k_to_nonlock_kernel_u); reveal(kernel_ipc_block_fields); };
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            let thread = pre_u.thread_map.spec_index(thread_ptr);
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.process_map.spec_index(thread.owning_proc).lock_state is Unlocked
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
    pub proof fn end_kernel_step_ipc_rendezvous(
        tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, caller_thread_ptr: RwLockThreadPtr,
        endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, waiting_state: ThreadState, peer_thread_ptr: RwLockThreadPtr,
        peer_result: RetValueType, cpu_transfer: Option<(CpuId, RwLockThreadPtr)>, payload: IPCPayLoad, cpu_sets_locked: bool,
    )
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_ipc_rendezvous_fields(
                &old(self).snapshot_k(), krnl, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result,
                cpu_transfer,
            ),
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
                endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer),
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            final(self).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
            kernel_u_ipc_rendezvous_changed(
                final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u, cpu_id, caller_thread_ptr, endpoint_ptr,
                endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer,
            ),
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
                &&& old_u.process_map.spec_index(caller.owning_proc).lock_state is Unlocked
                &&& !old_u.process_map.spec_index(caller.owning_proc).killed
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
                &&& waiting_state is SENDING || waiting_state is RECEIVING
                &&& endpoint.queue.len() > 0
                &&& endpoint.queue[0] == peer_thread_ptr
                &&& (endpoint.queue_state is SEND) != (waiting_state is SENDING)
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
                &&& old_u.process_map.spec_index(caller.owning_proc).lock_state is Unlocked
                &&& !old_u.process_map.spec_index(caller.owning_proc).killed
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
                &&& waiting_state is SENDING || waiting_state is RECEIVING
                &&& endpoint.queue.len() > 0
                &&& endpoint.queue[0] == peer_thread_ptr
                &&& (endpoint.queue_state is SEND) != (waiting_state is SENDING)
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
            ipc_rendezvous_result(final(self).nonlock_view().last().old_u, cpu_id, endpoint_index, waiting_state, payload)
                == ipc_rendezvous_result(old(self).snapshot_u(), cpu_id, endpoint_index, waiting_state, payload),
    {
        reveal(kernel_u_ipc_rendezvous_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_nonlock_kernel_u(self.snapshot_k());
            let caller = pre_u.thread_map.spec_index(caller_thread_ptr);
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.process_map.spec_index(caller.owning_proc).lock_state is Unlocked
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
            &&& pre_u.process_map.spec_index(caller.owning_proc).lock_state is Unlocked
            &&& caller.lock_state is Unlocked
            &&& caller.syscall_progress is None
            &&& pre_u.endpoint_map.spec_index(endpoint_ptr).lock_state is Unlocked
            &&& pre_u.thread_map.spec_index(peer_thread_ptr).lock_state is Unlocked
            &&& pre_u.container_map.dom().contains(caller.owning_container)
            &&& cpu_sets_locked ==> pre_u.container_map[caller.owning_container].cpu_set_lock is Unlocked
                && pre_u.container_map[pre_u.thread_map.spec_index(peer_thread_ptr).owning_container].cpu_set_lock is Unlocked
            &&& cpu_transfer matches Some((transfer, _)) ==> pre_u.cpu_array[transfer as int].lock_state is Unlocked
        }) by { reveal(kernel_k_to_kernel_u); reveal(kernel_ipc_rendezvous_fields); };
        assert(ipc_rendezvous_result(self.nonlock_snapshot_u(), cpu_id, endpoint_index, waiting_state, payload)
            == ipc_rendezvous_result(self.snapshot_u(), cpu_id, endpoint_index, waiting_state, payload)) by {
            reveal(kernel_k_to_kernel_u); reveal(kernel_k_to_nonlock_kernel_u); reveal(kernel_ipc_rendezvous_fields);
        };
        let pre_u = self.nonlock_snapshot_u();
        let post_u = kernel_k_to_nonlock_kernel_u(*krnl);
        assert(kernel_u_ipc_rendezvous_changed(
            pre_u, post_u, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer,
        )) by {
            kernel_ipc_rendezvous_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, false);
            reveal(kernel_k_to_nonlock_kernel_u);
        };
        assert(kernel_u_ipc_rendezvous_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, caller_thread_ptr,
            endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer)) by {
            kernel_ipc_rendezvous_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, true);
            reveal(kernel_k_to_kernel_u);
        };
        self.end_kernel_step_raw(krnl, lctx);
    }

    pub proof fn end_kernel_step_process_quota_4k_changed(
        tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
        container_ptr: RwLockContainerPtr, delta: int,
    )
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
            final(self).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
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

}

pub broadcast proof fn kernel_pagetable_nonlock_fields_unchanged_for_equal(pre: PageTableLockedMap, post: PageTableLockedMap)
    requires pre == post,
    ensures #[trigger] kernel_pagetable_nonlock_fields_unchanged(pre, post),
{
    reveal(kernel_pagetable_nonlock_fields_unchanged);
}

pub broadcast proof fn kernel_pagetable_nonlock_fields_unchanged_transitive(pre: PageTableLockedMap, middle: PageTableLockedMap, post: PageTableLockedMap)
    requires
        #[trigger] kernel_pagetable_nonlock_fields_unchanged(pre, middle),
        #[trigger] kernel_pagetable_nonlock_fields_unchanged(middle, post),
    ensures
        kernel_pagetable_nonlock_fields_unchanged(pre, post),
{
    reveal(kernel_pagetable_nonlock_fields_unchanged);
}

pub broadcast proof fn kernel_iommu_table_nonlock_fields_unchanged_for_equal(pre: IommuTableLockedMap, post: IommuTableLockedMap)
    requires pre == post,
    ensures #[trigger] kernel_iommu_table_nonlock_fields_unchanged(pre, post),
{
    reveal(kernel_iommu_table_nonlock_fields_unchanged);
}

pub broadcast proof fn kernel_iommu_table_nonlock_fields_unchanged_transitive(pre: IommuTableLockedMap, middle: IommuTableLockedMap, post: IommuTableLockedMap)
    requires
        #[trigger] kernel_iommu_table_nonlock_fields_unchanged(pre, middle),
        #[trigger] kernel_iommu_table_nonlock_fields_unchanged(middle, post),
    ensures
        kernel_iommu_table_nonlock_fields_unchanged(pre, post),
{
    reveal(kernel_iommu_table_nonlock_fields_unchanged);
}

pub broadcast proof fn kernel_cpu_nonlock_fields_unchanged_for_equal(pre: CpuLockedArray, post: CpuLockedArray)
    requires pre == post,
    ensures #[trigger] kernel_cpu_nonlock_fields_unchanged(pre, post),
{
    reveal(kernel_cpu_nonlock_fields_unchanged);
}

pub broadcast proof fn kernel_cpu_nonlock_fields_unchanged_transitive(pre: CpuLockedArray, middle: CpuLockedArray, post: CpuLockedArray)
    requires
        #[trigger] kernel_cpu_nonlock_fields_unchanged(pre, middle),
        #[trigger] kernel_cpu_nonlock_fields_unchanged(middle, post),
    ensures
        kernel_cpu_nonlock_fields_unchanged(pre, post),
{
    reveal(kernel_cpu_nonlock_fields_unchanged);
}

pub broadcast proof fn kernel_process_nonlock_fields_unchanged_for_equal(pre: ProcessLockedMap, post: ProcessLockedMap)
    requires pre == post,
    ensures #[trigger] kernel_process_nonlock_fields_unchanged(pre, post),
{
    reveal(kernel_process_nonlock_fields_unchanged);
}

pub broadcast proof fn kernel_process_nonlock_fields_unchanged_transitive(pre: ProcessLockedMap, middle: ProcessLockedMap, post: ProcessLockedMap)
    requires
        #[trigger] kernel_process_nonlock_fields_unchanged(pre, middle),
        #[trigger] kernel_process_nonlock_fields_unchanged(middle, post),
    ensures
        kernel_process_nonlock_fields_unchanged(pre, post),
{
    reveal(kernel_process_nonlock_fields_unchanged);
}

pub broadcast proof fn kernel_thread_nonlock_fields_unchanged_for_equal(pre: ThreadLockedMap, post: ThreadLockedMap)
    requires pre == post,
    ensures #[trigger] kernel_thread_nonlock_fields_unchanged(pre, post),
{
    reveal(kernel_thread_nonlock_fields_unchanged);
}

pub broadcast proof fn kernel_thread_nonlock_fields_unchanged_transitive(pre: ThreadLockedMap, middle: ThreadLockedMap, post: ThreadLockedMap)
    requires
        #[trigger] kernel_thread_nonlock_fields_unchanged(pre, middle),
        #[trigger] kernel_thread_nonlock_fields_unchanged(middle, post),
    ensures
        kernel_thread_nonlock_fields_unchanged(pre, post),
{
    reveal(kernel_thread_nonlock_fields_unchanged);
}

pub broadcast group group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive {
    kernel_pagetable_nonlock_fields_unchanged_for_equal,
    kernel_pagetable_nonlock_fields_unchanged_transitive,
    kernel_iommu_table_nonlock_fields_unchanged_for_equal,
    kernel_iommu_table_nonlock_fields_unchanged_transitive,
    kernel_cpu_nonlock_fields_unchanged_for_equal,
    kernel_cpu_nonlock_fields_unchanged_transitive,
    kernel_process_nonlock_fields_unchanged_for_equal,
    kernel_process_nonlock_fields_unchanged_transitive,
    kernel_thread_nonlock_fields_unchanged_for_equal,
    kernel_thread_nonlock_fields_unchanged_transitive,
}

pub broadcast proof fn kernel_endpoint_nonlock_fields_unchanged_for_equal(pre: EndpointLockedMap, post: EndpointLockedMap)
    requires pre == post,
    ensures #[trigger] kernel_endpoint_nonlock_fields_unchanged(pre, post),
{
    reveal(kernel_endpoint_nonlock_fields_unchanged);
}

pub broadcast proof fn kernel_endpoint_nonlock_fields_unchanged_transitive(pre: EndpointLockedMap, middle: EndpointLockedMap, post: EndpointLockedMap)
    requires
        #[trigger] kernel_endpoint_nonlock_fields_unchanged(pre, middle),
        #[trigger] kernel_endpoint_nonlock_fields_unchanged(middle, post),
    ensures kernel_endpoint_nonlock_fields_unchanged(pre, post),
{
    reveal(kernel_endpoint_nonlock_fields_unchanged);
}

pub broadcast group group_kernel_endpoint_nonlock_fields_unchanged_transitive {
    kernel_endpoint_nonlock_fields_unchanged_for_equal,
    kernel_endpoint_nonlock_fields_unchanged_transitive,
}

pub proof fn kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(steps: &KernelSteps, krnl: &KernelK)
    requires steps.snapshot_k() == *krnl,
    ensures kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), krnl), kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp), kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), krnl),
{
    broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, group_kernel_endpoint_nonlock_fields_unchanged_transitive;
    reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
}

pub broadcast proof fn kernel_cpu_process_thread_nonlock_fields_unchanged_transitive(pre: &KernelK, middle: &KernelK, post: &KernelK)
    requires
        #[trigger] kernel_cpu_process_thread_nonlock_fields_unchanged(pre, middle),
        #[trigger] kernel_cpu_process_thread_nonlock_fields_unchanged(middle, post),
    ensures
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post),
{
    broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
}

pub broadcast proof fn kernel_container_nonlock_fields_and_quotas_unchanged_transitive(pre: &KernelK, middle: &KernelK, post: &KernelK)
    requires
        #[trigger] kernel_container_nonlock_fields_and_quotas_unchanged(pre, middle),
        #[trigger] kernel_container_nonlock_fields_and_quotas_unchanged(middle, post),
    ensures
        kernel_container_nonlock_fields_and_quotas_unchanged(pre, post),
{
    reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
}

#[verifier::spinoff_prover]
pub proof fn kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(pre: &KernelK, post: &KernelK)
    requires
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        post.irt.owners() == pre.irt.owners(),
        post.irt.iommu_roots() == pre.irt.iommu_roots(),
        post.cpu_tlb.view() == pre.cpu_tlb.view(),
        post.iommu_tlb.view() == pre.iommu_tlb.view(),
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post),
        kernel_container_nonlock_fields_and_quotas_unchanged(pre, post),
    ensures
        kernel_k_to_nonlock_kernel_u(*pre) == kernel_k_to_nonlock_kernel_u(*post),
{
    reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(kernel_endpoint_nonlock_fields_unchanged);
    reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
    reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
    reveal(kernel_k_to_nonlock_kernel_u);
    let pre_u = kernel_k_to_nonlock_kernel_u(*pre);
    let post_u = kernel_k_to_nonlock_kernel_u(*post);
    assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { reveal(IommuRootTable::user_view); };
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array);
    assert_maps_equal!(post_u.container_map, pre_u.container_map, c => {});
    assert_maps_equal!(post_u.process_map, pre_u.process_map, p => {
        reveal(process_pagetable_match); reveal(process_iommu_table_match);
    });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map, t => {});
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => {});
}

/// A section that write-holds one thread throughout, changes no non-lock field, and moves
/// lock modes only on pages and allocator objects leaves the complete projection unchanged.
pub proof fn kernel_thread_write_held_section_implies_u_eq(pre: &KernelK, post: &KernelK, pre_lctx: &LocalContext, post_lctx: &LocalContext, thread_ptr: RwLockThreadPtr)
    requires
        post.inv(),
        pre.thr_mp.typed_lock_map_aligned(pre_lctx.thread_lock_map(), pre_lctx.thread_id()),
        post.thr_mp.typed_lock_map_aligned(post_lctx.thread_lock_map(), post_lctx.thread_id()),
        typed_lock_map_contains_mode(pre_lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(post_lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        *post == (KernelK { pg_arr: post.pg_arr, thr_mp: post.thr_mp, allc_4k_mp: post.allc_4k_mp, allc_2m_mp: post.allc_2m_mp, allc_1g_mp: post.allc_1g_mp, ..*pre }),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post),
        kernel_container_nonlock_fields_and_quotas_unchanged(pre, post),
    ensures
        kernel_k_to_kernel_u(*post) == kernel_k_to_kernel_u(*pre),
{
    broadcast use kernel_endpoint_nonlock_fields_unchanged_for_equal;
    pre.thr_mp.typed_lock_map_aligned_write_at(pre_lctx.thread_lock_map(), pre_lctx.thread_id(), thread_ptr);
    post.thr_mp.typed_lock_map_aligned_write_at(post_lctx.thread_lock_map(), post_lctx.thread_id(), thread_ptr);
    kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(pre, post);
}

/// Unchanged non-lock fields and user-visible lock modes leave the complete projection unchanged.
#[verifier::spinoff_prover]
pub proof fn kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(pre: &KernelK, post: &KernelK)
    requires
        post.inv(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        post.irt.owners() == pre.irt.owners(),
        post.irt.iommu_roots() == pre.irt.iommu_roots(),
        post.cpu_tlb.view() == pre.cpu_tlb.view(),
        post.iommu_tlb.view() == pre.iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(pre, post),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)]
            post.ctn_mp.dom().contains(p) && pre.ctn_mp.dom().contains(p) ==> {
                let before = pre.ctn_mp.spec_index(p).locking_thread();
                let after = post.ctn_mp.spec_index(p).locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
            },
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
            post.prc_mp.dom().contains(p) && pre.prc_mp.dom().contains(p) ==> {
                let before = pre.prc_mp.spec_index(p).locking_thread();
                let after = post.prc_mp.spec_index(p).locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
            },
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
            post.pt_mp.dom().contains(p) && pre.pt_mp.dom().contains(p) ==> {
                let before = pre.pt_mp.spec_index(p).locking_thread();
                let after = post.pt_mp.spec_index(p).locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
            },
        forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
            post.it_mp.dom().contains(p) && pre.it_mp.dom().contains(p) ==> {
                let before = pre.it_mp.spec_index(p).locking_thread();
                let after = post.it_mp.spec_index(p).locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
            },
        forall|p: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(p)]
            post.thr_mp.dom().contains(p) && pre.thr_mp.dom().contains(p) ==> {
                let before = pre.thr_mp.spec_index(p).locking_thread();
                let after = post.thr_mp.spec_index(p).locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
            },
        forall|p: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(p)]
            post.ep_mp.dom().contains(p) && pre.ep_mp.dom().contains(p) ==> {
                let before = pre.ep_mp.spec_index(p).locking_thread();
                let after = post.ep_mp.spec_index(p).locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
            },
        forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> {
                let before = pre.cpu_arr.spec_index(i).value.locking_thread();
                let after = post.cpu_arr.spec_index(i).value.locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
            },
    ensures
        kernel_k_to_kernel_u(*pre) == kernel_k_to_kernel_u(*post),
{
    kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(pre, post);
    reveal(kernel_k_to_kernel_u); reveal(kernel_k_to_nonlock_kernel_u);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    assert_seqs_equal!(before.cpu_array == after.cpu_array, i => {
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
    });
    assert_maps_equal!(before.container_map, after.container_map, p => { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); });
    assert_maps_equal!(before.process_map, after.process_map, p => {
        reveal(process_pagetable_match); reveal(process_iommu_table_match);
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged);
        reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
    });
    assert_maps_equal!(before.thread_map, after.thread_map, p => {
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
    });
    assert_maps_equal!(before.endpoint_map, after.endpoint_map, p => { reveal(kernel_endpoint_nonlock_fields_unchanged); });
}

#[verifier::spinoff_prover]
proof fn kernel_context_switch_fields_implies_u_step(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, next_thread: RwLockThreadPtr, entry_regs: Registers,
    flushed_pcid: Option<Pcid>, include_lock_state: bool,
)
    requires
        post.inv(),
        kernel_context_switch_fields(pre, post, cpu_id, next_thread, entry_regs, flushed_pcid),
    ensures
        kernel_u_context_switch_changed(kernel_k_user_projection(*pre, include_lock_state), kernel_k_user_projection(*post, include_lock_state), cpu_id, next_thread, entry_regs, flushed_pcid),
{
    reveal(kernel_u_context_switch_changed);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    assert(kernel_u_context_switch_changed(pre_u, post_u, cpu_id, next_thread, entry_regs, flushed_pcid)) by {
        reveal(kernel_context_switch_fields); reveal(kernel_endpoint_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged);
        let cpu = pre_u.cpu_array[cpu_id as int];
        let container = pre_u.container_map.spec_index(cpu.owning_container);
        let next = pre_u.thread_map.spec_index(next_thread);
        assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { reveal(IommuRootTable::user_view); };
        assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU {
            state: CpuState::Running, current_process: Some(next.owning_proc), current_thread: Some(next_thread), ..cpu
        }));
        assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => {});
        assert_maps_equal!(post_u.process_map, pre_u.process_map, p => {
            reveal(process_pagetable_match); reveal(process_iommu_table_match);
            reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
        });
        assert_maps_equal!(post_u.container_map, pre_u.container_map.insert(cpu.owning_container, ContainerU {
            scheduler: match cpu.current_thread { Some(prev) => container.scheduler.skip(1).push(prev), None => container.scheduler.skip(1) },
            ..container
        }), c => {});
        match cpu.current_thread {
            Some(prev) => {
                assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(prev, ThreadU {
                    state: ThreadState::SCHEDULED, error_code: None, trap_frame: Some(entry_regs), ..pre_u.thread_map.spec_index(prev)
                }).insert(next_thread, ThreadU { state: ThreadState::RUNNING { cpu_id }, error_code: None, trap_frame: None, ..next }), t => {});
            },
            None => {
                assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(next_thread, ThreadU {
                    state: ThreadState::RUNNING { cpu_id }, error_code: None, trap_frame: None, ..next
                }), t => {});
            },
        }
    };
}

/// Write-locking or releasing both IPC page tables and replacing `thread`'s progress changes only
/// those page-table lock states and that thread's progress.
#[verifier::spinoff_prover]
pub proof fn kernel_pagetable_pair_lock_states_and_progress_changed_implies_u_step(
    pre: &KernelK, post: &KernelK, lctx: &LocalContext, source: RwLockProcessPtr, target: RwLockProcessPtr,
    source_table: RwLockPageTableRoot, target_table: RwLockPageTableRoot, thread: RwLockThreadPtr, lock: bool,
)
    requires
        post.inv(),
        typed_lock_maps_aligned(post, lctx),
        source != target,
        pre.prc_mp.dom().contains(source),
        pre.prc_mp.dom().contains(target),
        !pre.prc_mp.spec_index(source).view().zombie,
        !pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(source).view().pagetable == source_table,
        pre.prc_mp.spec_index(target).view().pagetable == target_table,
        *post == (KernelK { pt_mp: post.pt_mp, thr_mp: post.thr_mp, ..*pre }),
        post.pt_mp.dom() == pre.pt_mp.dom(),
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)] pre.pt_mp.dom().contains(p) ==> {
            &&& post.pt_mp.spec_index(p).view() == pre.pt_mp.spec_index(p).view()
            &&& p != source_table && p != target_table ==> post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread()
        },
        lock ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), source_table, TypedLockMode::Write),
        lock ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), target_table, TypedLockMode::Write),
        !lock ==> post.pt_mp.spec_index(source_table).locking_thread() is None,
        !lock ==> post.pt_mp.spec_index(target_table).locking_thread() is None,
        pre.thr_mp.dom().contains(thread),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread),
        post.thr_mp.spec_index(thread).view() == (Thread { syscall_progress: post.thr_mp.spec_index(thread).view().syscall_progress, ..pre.thr_mp.spec_index(thread).view() }),
        post.thr_mp.spec_index(thread).locking_thread() == pre.thr_mp.spec_index(thread).locking_thread(),
        post.thr_mp.spec_index(thread).being_killed() == pre.thr_mp.spec_index(thread).being_killed(),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let state = if lock { LockStateU::WriteLocked } else { LockStateU::Unlocked };
            &&& a.thread_map.dom().contains(thread)
            &&& a.thread_map[thread].syscall_progress == pre.thr_mp.spec_index(thread).view().syscall_progress.view()
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                thread_map: a.thread_map.insert(thread, ThreadU { syscall_progress: post.thr_mp.spec_index(thread).view().syscall_progress.view(), ..a.thread_map[thread] }),
                process_map: a.process_map.insert(source, ProcessU {
                    pagetable: Some(PageTableU { lock_state: state, ..a.process_map[source].pagetable->Some_0 }), ..a.process_map[source]
                }).insert(target, ProcessU {
                    pagetable: Some(PageTableU { lock_state: state, ..a.process_map[target].pagetable->Some_0 }), ..a.process_map[target]
                }),
                ..a
            })
        }),
{
    if lock {
        post.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), source_table);
        post.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), target_table);
    }
    reveal(kernel_k_to_kernel_u);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    let state = if lock { LockStateU::WriteLocked } else { LockStateU::Unlocked };
    assert_maps_equal!(b.thread_map, a.thread_map.insert(thread, ThreadU { syscall_progress: post.thr_mp.spec_index(thread).view().syscall_progress.view(), ..a.thread_map[thread] }), t => {});
    assert_maps_equal!(b.process_map, a.process_map.insert(source, ProcessU {
        pagetable: Some(PageTableU { lock_state: state, ..a.process_map[source].pagetable->Some_0 }), ..a.process_map[source]
    }).insert(target, ProcessU {
        pagetable: Some(PageTableU { lock_state: state, ..a.process_map[target].pagetable->Some_0 }), ..a.process_map[target]
    }), p => { reveal(process_pagetable_match); });
}

pub proof fn kernel_restored_locks_implies_u_eq(
    pre: &KernelK, post: &KernelK, cpu: CpuId, container: Option<RwLockContainerPtr>, process: Option<RwLockProcessPtr>,
    thread: Option<RwLockThreadPtr>, endpoint: Option<RwLockEndpointPtr>, table: Option<RwLockPageTableRoot>,
)
    requires
        post.inv(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        post.irt.owners() == pre.irt.owners(),
        post.irt.iommu_roots() == pre.irt.iommu_roots(),
        post.cpu_tlb.view() == pre.cpu_tlb.view(),
        post.iommu_tlb.view() == pre.iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(pre, post),
        post.cpu_arr.unchanged_except(&pre.cpu_arr, cpu),
        (post.cpu_arr.spec_index(cpu).value.locking_thread() is Write) == (pre.cpu_arr.spec_index(cpu).value.locking_thread() is Write),
        (post.cpu_arr.spec_index(cpu).value.locking_thread() is Read) == (pre.cpu_arr.spec_index(cpu).value.locking_thread() is Read),
        post.it_mp == pre.it_mp,
        match container {
            Some(p) => {
                &&& post.ctn_mp.unchanged_except(&pre.ctn_mp, p)
                &&& (post.ctn_mp.spec_index(p).locking_thread() is Write) == (pre.ctn_mp.spec_index(p).locking_thread() is Write)
                &&& (post.ctn_mp.spec_index(p).locking_thread() is Read) == (pre.ctn_mp.spec_index(p).locking_thread() is Read)
            },
            None => post.ctn_mp == pre.ctn_mp,
        },
        match process {
            Some(p) => {
                &&& post.prc_mp.unchanged_except(&pre.prc_mp, p)
                &&& (post.prc_mp.spec_index(p).locking_thread() is Write) == (pre.prc_mp.spec_index(p).locking_thread() is Write)
                &&& (post.prc_mp.spec_index(p).locking_thread() is Read) == (pre.prc_mp.spec_index(p).locking_thread() is Read)
            },
            None => post.prc_mp == pre.prc_mp,
        },
        match thread {
            Some(p) => {
                &&& post.thr_mp.unchanged_except(&pre.thr_mp, p)
                &&& (post.thr_mp.spec_index(p).locking_thread() is Write) == (pre.thr_mp.spec_index(p).locking_thread() is Write)
                &&& (post.thr_mp.spec_index(p).locking_thread() is Read) == (pre.thr_mp.spec_index(p).locking_thread() is Read)
            },
            None => post.thr_mp == pre.thr_mp,
        },
        match endpoint {
            Some(p) => {
                &&& post.ep_mp.unchanged_except(&pre.ep_mp, p)
                &&& (post.ep_mp.spec_index(p).locking_thread() is Write) == (pre.ep_mp.spec_index(p).locking_thread() is Write)
                &&& (post.ep_mp.spec_index(p).locking_thread() is Read) == (pre.ep_mp.spec_index(p).locking_thread() is Read)
            },
            None => post.ep_mp == pre.ep_mp,
        },
        match table {
            Some(p) => {
                &&& post.pt_mp.unchanged_except(&pre.pt_mp, p)
                &&& (post.pt_mp.spec_index(p).locking_thread() is Write) == (pre.pt_mp.spec_index(p).locking_thread() is Write)
                &&& (post.pt_mp.spec_index(p).locking_thread() is Read) == (pre.pt_mp.spec_index(p).locking_thread() is Read)
            },
            None => post.pt_mp == pre.pt_mp,
        },
    ensures kernel_k_to_kernel_u(*post) == kernel_k_to_kernel_u(*pre),
{
    kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(pre, post);
}

pub proof fn kernel_container_publication_composes(
    pre: KernelU, published: KernelU, post: KernelU, parent: RwLockContainerPtr, child: RwLockContainerPtr, process: RwLockProcessPtr,
    thread: RwLockThreadPtr, cpu: CpuId, funding: usize, process_quota: usize, moved: Set<PagePtr>, thread_page: PagePtr, progress: Option<SyscallProgress>,
)
    requires
        moved.len() == 2 * 512 + 8 + funding,
    ensures
        kernel_u_container_root_published(pre, published, parent, child, process, thread, cpu, funding, process_quota, moved, thread_page, progress)
            && kernel_u_cpu_and_page_owner_changed(published, post, cpu, parent, child, thread_page)
            ==> kernel_u_container_root_created(pre, post, parent, child, process, thread, cpu, funding, process_quota, progress)
                && post.container_map[parent].children.last() == child && post.container_map[child].root_process == process,
{
    if kernel_u_container_root_published(pre, published, parent, child, process, thread, cpu, funding, process_quota, moved, thread_page, progress)
        && kernel_u_cpu_and_page_owner_changed(published, post, cpu, parent, child, thread_page) {
        reveal(kernel_u_container_root_published); reveal(kernel_u_cpu_and_page_owner_changed); reveal(kernel_u_container_root_created);
        let moved_all = pre.container_map[parent].owned_pages.difference(post.container_map[parent].owned_pages);
        assert_sets_equal!(post.container_map.dom(), pre.container_map.dom().insert(child));
        assert_sets_equal!(moved_all, moved.insert(thread_page));
        assert_seqs_equal!(post.cpu_array == pre.cpu_array.update(cpu as int, CpuU {
            lock_state: LockStateU::Unlocked, owning_container: child, ..pre.cpu_array[cpu as int]
        }));
    }
}

pub proof fn kernel_container_root_published_implies_u_step(
    before: &KernelK, after: &KernelK, parent: RwLockContainerPtr, child: RwLockContainerPtr, process: RwLockProcessPtr, thread: RwLockThreadPtr,
    transfer_cpu: CpuId, funding: usize, process_quota: usize, moved: Set<PagePtr>, thread_page: PagePtr, pcid_allocator: RwLockPcidAllocatorPtr,
    progress: Option<SyscallProgress>,
)
    requires
        before.inv(),
        before.ctn_mp.dom().contains(parent),
        !before.ctn_mp.dom().contains(child),
        !before.prc_mp.dom().contains(process),
        index_valid(NUM_CPUS, transfer_cpu),
        before.cpu_arr.spec_index(transfer_cpu).value.view().view().state is Off,
        before.cpu_arr.spec_index(transfer_cpu).value.view().view().owning_container == parent,
        kernel_cpu_nonlock_fields_unchanged(before.cpu_arr, after.cpu_arr),
        after.cpu_arr.spec_index(transfer_cpu).value.locking_thread() is Write,
        forall|i: CpuId| #![trigger after.cpu_arr.spec_index(i)] index_valid(NUM_CPUS, i) && i != transfer_cpu ==>
            after.cpu_arr.spec_index(i).value.locking_thread() == before.cpu_arr.spec_index(i).value.locking_thread(),
        after.ep_mp == before.ep_mp,
        after.it_mp == before.it_mp,
        after.irt == before.irt,
        after.cpu_tlb == before.cpu_tlb,
        after.iommu_tlb == before.iommu_tlb,
        after.dflt_pt == before.dflt_pt,
        forall|p: RwLockCpuSetPtr| #![trigger after.cpu_set_mp.spec_index(p)] before.cpu_set_mp.dom().contains(p) ==>
            after.cpu_set_mp.spec_index(p).locking_thread() == before.cpu_set_mp.spec_index(p).locking_thread(),
        before.thr_mp.spec_index(thread).view().quota_4k >= 8 + funding,
        after.thr_mp.unchanged_except(&before.thr_mp, thread),
        after.thr_mp.spec_index(thread).being_killed() == before.thr_mp.spec_index(thread).being_killed(),
        after.thr_mp.spec_index(thread).locking_thread() == before.thr_mp.spec_index(thread).locking_thread(),
        after.thr_mp.spec_index(thread).view().state == before.thr_mp.spec_index(thread).view().state,
        after.thr_mp.spec_index(thread).view().caller == before.thr_mp.spec_index(thread).view().caller,
        after.thr_mp.spec_index(thread).view().callee == before.thr_mp.spec_index(thread).view().callee,
        after.thr_mp.spec_index(thread).view().owning_container == before.thr_mp.spec_index(thread).view().owning_container,
        after.thr_mp.spec_index(thread).view().owning_proc == before.thr_mp.spec_index(thread).view().owning_proc,
        after.thr_mp.spec_index(thread).view().quota_4k == before.thr_mp.spec_index(thread).view().quota_4k - 8 - funding,
        after.thr_mp.spec_index(thread).view().quota_2m == before.thr_mp.spec_index(thread).view().quota_2m - 2,
        after.thr_mp.spec_index(thread).view().quota_1g == before.thr_mp.spec_index(thread).view().quota_1g,
        after.thr_mp.spec_index(thread).view().endpoint_descriptors.view() == before.thr_mp.spec_index(thread).view().endpoint_descriptors.view(),
        after.thr_mp.spec_index(thread).view().blocking_endpoint_ptr == before.thr_mp.spec_index(thread).view().blocking_endpoint_ptr,
        after.thr_mp.spec_index(thread).view().ipc_payload == before.thr_mp.spec_index(thread).view().ipc_payload,
        after.thr_mp.spec_index(thread).view().error_code == before.thr_mp.spec_index(thread).view().error_code,
        after.thr_mp.spec_index(thread).view().trap_frame == before.thr_mp.spec_index(thread).view().trap_frame,
        after.thr_mp.spec_index(thread).view().syscall_progress.view() == progress,
        after.ctn_mp.dom() == before.ctn_mp.dom().insert(child),
        forall|c: RwLockContainerPtr| #![trigger after.ctn_mp.spec_index(c)] before.ctn_mp.dom().contains(c) ==> {
            &&& after.ctn_mp.spec_index(c).view_rodata() == before.ctn_mp.spec_index(c).view_rodata()
            &&& after.ctn_mp.spec_index(c).view_ghost().uppertree_seq == before.ctn_mp.spec_index(c).view_ghost().uppertree_seq
            &&& after.ctn_mp.spec_index(c).view_ghost().owned_threads == before.ctn_mp.spec_index(c).view_ghost().owned_threads
            &&& after.ctn_mp.spec_index(c).view_ghost().owned_processes == before.ctn_mp.spec_index(c).view_ghost().owned_processes
            &&& after.ctn_mp.spec_index(c).view_ghost().subtree_set.view() == if before.ctn_mp.spec_index(parent).view_ghost().uppertree_seq.view().push(parent).contains(c) {
                before.ctn_mp.spec_index(c).view_ghost().subtree_set.view().insert(child)
            } else { before.ctn_mp.spec_index(c).view_ghost().subtree_set.view() }
            &&& after.ctn_mp.spec_index(c).view() == (Container { children: after.ctn_mp.spec_index(c).view().children,
                owned_pages: after.ctn_mp.spec_index(c).view().owned_pages, ..before.ctn_mp.spec_index(c).view() })
            &&& after.ctn_mp.spec_index(c).view().children.view() == if c == parent { before.ctn_mp.spec_index(c).view().children.view().push(child) } else { before.ctn_mp.spec_index(c).view().children.view() }
            &&& c != parent ==> after.ctn_mp.spec_index(c).view().owned_pages == before.ctn_mp.spec_index(c).view().owned_pages
            &&& after.ctn_mp.spec_index(c).locking_thread() == before.ctn_mp.spec_index(c).locking_thread()
            &&& after.ctn_mp.spec_index(c).being_killed() == before.ctn_mp.spec_index(c).being_killed()
        },
        after.ctn_mp.spec_index(parent).view().owned_pages.view().subset_of(before.ctn_mp.spec_index(parent).view().owned_pages.view()),
        moved.subset_of(before.ctn_mp.spec_index(parent).view().owned_pages.view()),
        after.ctn_mp.spec_index(parent).view().owned_pages.view() == before.ctn_mp.spec_index(parent).view().owned_pages.view().difference(moved),
        after.ctn_mp.spec_index(parent).view().owned_pages.view().contains(thread_page),
        moved.contains(child),
        moved.contains(process),
        moved.contains(after.ctn_mp.spec_index(child).view_rodata().view().cpu_set),
        after.cpu_set_mp.spec_index(after.ctn_mp.spec_index(child).view_rodata().view().cpu_set).locking_thread() is Write,
        after.ctn_mp.spec_index(child).locking_thread() is Write,
        !after.ctn_mp.spec_index(child).being_killed(),
        after.ctn_mp.spec_index(child).view().children.view().len() == 0,
        after.ctn_mp.spec_index(child).view_ghost().uppertree_seq.view() == before.ctn_mp.spec_index(parent).view_ghost().uppertree_seq.view().push(parent),
        after.ctn_mp.spec_index(child).view_ghost().subtree_set.view().is_empty(),
        after.ctn_mp.spec_index(child).view().root_process == process,
        after.ctn_mp.spec_index(child).view_ghost().owned_processes.view() == set![process],
        after.ctn_mp.spec_index(child).view_ghost().owned_threads.view().is_empty(),
        after.ctn_mp.spec_index(child).view().owned_endpoints.view().is_empty(),
        after.ctn_mp.spec_index(child).view().owned_pages.view() == moved,
        after.ctn_mp.spec_index(child).view_rodata().view().parent == Some(parent),
        after.ctn_mp.spec_index(child).view_rodata().view().depth == before.ctn_mp.spec_index(parent).view_rodata().view().depth + 1,
        after.sched_mp.spec_index(after.ctn_mp.spec_index(child).view_rodata().view().scheduler).view().queue.view().len() == 0,
        after.ctn_mp.spec_index(child).view_rodata().view().pcid_allocator == pcid_allocator,
        after.pcid_allc_mp.spec_index(pcid_allocator).view().ref_counters.spec_index(1usize) == 1,
        forall|pcid: Pcid| #![trigger after.pcid_allc_mp.spec_index(pcid_allocator).view().ref_counters.spec_index(pcid)]
            pcid_valid(pcid) && pcid != 1usize ==> after.pcid_allc_mp.spec_index(pcid_allocator).view().ref_counters.spec_index(pcid) == 0,
        after.allc_4k_mp.spec_index(after.ctn_mp.spec_index(child).view_rodata().view().allocator_ptr_4k).quota.view().view() == funding - process_quota,
        after.allc_2m_mp.spec_index(after.ctn_mp.spec_index(child).view_rodata().view().allocator_ptr_2m).quota.view().view() == 0,
        after.allc_1g_mp.spec_index(after.ctn_mp.spec_index(child).view_rodata().view().allocator_ptr_1g).quota.view().view() == 0,
        forall|p: RwLockSchedulerPtr| #![trigger after.sched_mp.spec_index(p)] before.sched_mp.dom().contains(p) ==>
            after.sched_mp.spec_index(p).view().queue.view() == before.sched_mp.spec_index(p).view().queue.view(),
        forall|p: RwLockPcidAllocatorPtr| #![trigger after.pcid_allc_mp.spec_index(p)] before.pcid_allc_mp.dom().contains(p) ==>
            after.pcid_allc_mp.spec_index(p).view().ref_counters.view() == before.pcid_allc_mp.spec_index(p).view().ref_counters.view(),
        before.allc_4k_mp.dom().subset_of(after.allc_4k_mp.dom()),
        forall|p: RwLockPageAllocatorPtr| #![trigger after.allc_4k_mp.spec_index(p)] before.allc_4k_mp.dom().contains(p) ==>
            after.allc_4k_mp.spec_index(p).quota.view().view() == before.allc_4k_mp.spec_index(p).quota.view().view(),
        before.allc_2m_mp.dom().subset_of(after.allc_2m_mp.dom()),
        forall|p: RwLockPageAllocatorPtr| #![trigger after.allc_2m_mp.spec_index(p)] before.allc_2m_mp.dom().contains(p) ==>
            after.allc_2m_mp.spec_index(p).quota.view().view() == before.allc_2m_mp.spec_index(p).quota.view().view(),
        forall|p: RwLockPageAllocatorPtr| #![trigger after.allc_1g_mp.spec_index(p)] before.allc_1g_mp.dom().contains(p) ==>
            after.allc_1g_mp.spec_index(p).quota.view().view() == before.allc_1g_mp.spec_index(p).quota.view().view(),
        after.prc_mp.dom() == before.prc_mp.dom().insert(process),
        forall|p: RwLockProcessPtr| #![trigger after.prc_mp.spec_index(p)] before.prc_mp.dom().contains(p) ==> after.prc_mp.spec_index(p) == before.prc_mp.spec_index(p),
        after.prc_mp.spec_index(process).locking_thread() is Write,
        !after.prc_mp.spec_index(process).being_killed(),
        !after.prc_mp.spec_index(process).view().zombie,
        after.prc_mp.spec_index(process).view().iommu_table is None,
        after.prc_mp.spec_index(process).view().owned_pci_functions.view().is_empty(),
        after.prc_mp.spec_index(process).view().quota_4k == process_quota,
        after.prc_mp.spec_index(process).view().quota_2m == 0,
        after.prc_mp.spec_index(process).view().quota_1g == 0,
        after.prc_mp.spec_index(process).view_rodata().view().parent is None,
        after.prc_mp.spec_index(process).view_rodata().view().depth == 0,
        after.prc_mp.spec_index(process).view().children.view().len() == 0,
        after.prc_mp.spec_index(process).view().owned_threads.view().len() == 0,
        after.prc_mp.spec_index(process).view_ghost().uppertree_seq.view().len() == 0,
        after.prc_mp.spec_index(process).view_ghost().subtree_set.view().is_empty(),
        before.pt_mp.dom().subset_of(after.pt_mp.dom()),
        forall|p: RwLockPageTableRoot| #![trigger after.pt_mp.spec_index(p)] before.pt_mp.dom().contains(p) ==> after.pt_mp.spec_index(p) == before.pt_mp.spec_index(p),
        after.pt_mp.dom().contains(after.prc_mp.spec_index(process).view().pagetable),
        after.pt_mp.spec_index(after.prc_mp.spec_index(process).view().pagetable).locking_thread() is Write,
        after.pt_mp.spec_index(after.prc_mp.spec_index(process).view().pagetable).view().is_empty(),
    ensures
        kernel_k_to_kernel_u(*before).thread_map.dom().contains(thread),
        kernel_k_to_kernel_u(*before).thread_map[thread].syscall_progress == before.thr_mp.spec_index(thread).view().syscall_progress.view(),
        kernel_u_container_root_published(kernel_k_to_kernel_u(*before), kernel_k_to_kernel_u(*after), parent, child, process, thread, transfer_cpu, funding, process_quota, moved, thread_page, progress),
{
    reveal(kernel_u_container_root_published); reveal(kernel_k_to_kernel_u);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    let ancestors = pre.container_map[parent].uppertree_seq.push(parent);
    assert(forall|c: RwLockContainerPtr| #![trigger post.container_map[c]] pre.container_map.dom().contains(c) ==>
        (ContainerU { children: pre.container_map[c].children, subtree_set: pre.container_map[c].subtree_set,
            owned_pages: pre.container_map[c].owned_pages, ..post.container_map[c] }) == pre.container_map[c]) by {
        reveal(container_scheduler_wf); reveal(container_pcid_allocator_wf); reveal(container_allocator_wf); reveal(container_cpu_set_wf);
    };
    assert_maps_equal!(post.process_map[process].pagetable->Some_0.mapping_1g, Map::empty());
    assert_seqs_equal!(post.cpu_array == pre.cpu_array.update(transfer_cpu as int, CpuU { lock_state: LockStateU::WriteLocked, ..pre.cpu_array[transfer_cpu as int] }), i => { reveal(kernel_cpu_nonlock_fields_unchanged); });
    assert_maps_equal!(post.thread_map, pre.thread_map.insert(thread, ThreadU {
        quota_4k: (pre.thread_map[thread].quota_4k - 8 - funding) as usize, quota_2m: (pre.thread_map[thread].quota_2m - 2) as usize,
        syscall_progress: progress, ..pre.thread_map[thread]
    }), p => {});
    assert_seqs_equal!(post.process_map[process].children == Seq::empty());
    assert_seqs_equal!(post.process_map[process].uppertree_seq == Seq::empty());
    assert_seqs_equal!(post.process_map[process].owned_threads == Seq::empty());
    assert_seqs_equal!(post.container_map[child].children == Seq::empty());
    assert_sets_equal!(post.container_map[child].owned_pages, moved);
    assert_sets_equal!(pre.container_map[parent].owned_pages.difference(post.container_map[parent].owned_pages), moved);
    assert_seqs_equal!(post.container_map[child].scheduler == Seq::empty());
    assert_sets_equal!(post.container_map[child].free_pcids, Set::range(1usize, PCID_MAX).remove(1usize));
    assert_maps_equal!(post.process_map, pre.process_map.insert(process, ProcessU {
        lock_state: LockStateU::WriteLocked, zombie: false,
        pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, mapping_4k: Map::empty(), mapping_2m: Map::empty(), mapping_1g: Map::empty() }),
        iommu_table: None, pcid: post.process_map[process].pcid, owned_pci_functions: Set::empty(), quota_4k: process_quota, quota_2m: 0, quota_1g: 0,
        parent: None, children: Seq::empty(), depth: 0, uppertree_seq: Seq::empty(), subtree_set: Set::empty(), owned_threads: Seq::empty(), killed: false,
    }), p => { reveal(process_pagetable_match); });
}

pub proof fn kernel_cpu_and_page_owner_changed_implies_u_step(before: &KernelK, after: &KernelK, cpu: CpuId, source: RwLockContainerPtr, target: RwLockContainerPtr, page: PagePtr)
    requires
        before.inv(),
        after.inv(),
        index_valid(NUM_CPUS, cpu),
        *after == (KernelK { pg_arr: after.pg_arr, ctn_mp: after.ctn_mp, cpu_arr: after.cpu_arr,
            cpu_set_mp: after.cpu_set_mp, sched_mp: after.sched_mp, ..*before }),
        after.cpu_arr.entries_unchanged_except(&before.cpu_arr, cpu),
        after.cpu_arr.spec_index(cpu).value.view().view().owning_container == target,
        after.cpu_arr.spec_index(cpu).value.view().view().state == before.cpu_arr.spec_index(cpu).value.view().view().state,
        after.cpu_arr.spec_index(cpu).value.view().view().current_process == before.cpu_arr.spec_index(cpu).value.view().view().current_process,
        after.cpu_arr.spec_index(cpu).value.view().view().current_thread == before.cpu_arr.spec_index(cpu).value.view().view().current_thread,
        after.cpu_arr.spec_index(cpu).value.locking_thread() is None,
        forall|s: RwLockSchedulerPtr| #![trigger after.sched_mp.spec_index(s)] before.sched_mp.dom().contains(s) ==>
            after.sched_mp.spec_index(s).view().queue.view() == before.sched_mp.spec_index(s).view().queue.view(),
        source != target,
        before.ctn_mp.dom().contains(source),
        before.ctn_mp.dom().contains(target),
        before.ctn_mp.spec_index(source).view().owned_pages.view().contains(page),
        after.cpu_set_mp.spec_index(before.ctn_mp.spec_index(source).view_rodata().view().cpu_set).locking_thread() is None,
        after.cpu_set_mp.spec_index(before.ctn_mp.spec_index(target).view_rodata().view().cpu_set).locking_thread() is None,
        forall|p: RwLockCpuSetPtr| #![trigger after.cpu_set_mp.spec_index(p)] before.cpu_set_mp.dom().contains(p) && p != before.ctn_mp.spec_index(source).view_rodata().view().cpu_set
            && p != before.ctn_mp.spec_index(target).view_rodata().view().cpu_set ==> after.cpu_set_mp.spec_index(p).locking_thread() == before.cpu_set_mp.spec_index(p).locking_thread(),
        after.ctn_mp.dom() == before.ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger after.ctn_mp.spec_index(c)] before.ctn_mp.dom().contains(c) ==> {
            &&& after.ctn_mp.spec_index(c).view_rodata() == before.ctn_mp.spec_index(c).view_rodata()
            &&& after.ctn_mp.spec_index(c).view_ghost() == before.ctn_mp.spec_index(c).view_ghost()
            &&& after.ctn_mp.spec_index(c).locking_thread() == before.ctn_mp.spec_index(c).locking_thread()
            &&& after.ctn_mp.spec_index(c).being_killed() == before.ctn_mp.spec_index(c).being_killed()
            &&& after.ctn_mp.spec_index(c).view() == (Container { owned_pages: after.ctn_mp.spec_index(c).view().owned_pages, ..before.ctn_mp.spec_index(c).view() })
            &&& after.ctn_mp.spec_index(c).view().owned_pages.view() == if c == source { before.ctn_mp.spec_index(c).view().owned_pages.view().remove(page) }
                else if c == target { before.ctn_mp.spec_index(c).view().owned_pages.view().insert(page) } else { before.ctn_mp.spec_index(c).view().owned_pages.view() }
        },
    ensures
        kernel_u_cpu_and_page_owner_changed(kernel_k_to_kernel_u(*before), kernel_k_to_kernel_u(*after), cpu, source, target, page),
{
    reveal(kernel_u_cpu_and_page_owner_changed); reveal(kernel_k_to_kernel_u);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    assert_seqs_equal!(post.cpu_array == pre.cpu_array.update(cpu as int, CpuU { lock_state: LockStateU::Unlocked, owning_container: target, ..pre.cpu_array[cpu as int] }));
    assert_maps_equal!(post.container_map, pre.container_map.insert(source, ContainerU { cpu_set_lock: LockStateU::Unlocked, owned_pages: pre.container_map[source].owned_pages.remove(page), ..pre.container_map[source] })
        .insert(target, ContainerU { cpu_set_lock: LockStateU::Unlocked, owned_pages: pre.container_map[target].owned_pages.insert(page), ..pre.container_map[target] }),
        c => { reveal(container_scheduler_wf); reveal(container_cpu_set_wf); });
}

pub proof fn kernel_peer_scheduled_and_locks_released_implies_u_step(
    before: &KernelK, after: &KernelK, cpu_id: CpuId, process: RwLockProcessPtr, caller: RwLockThreadPtr, peer: RwLockThreadPtr,
    endpoint: RwLockEndpointPtr, result: RetValueType, dequeue: bool, descriptor: Option<(RwLockThreadPtr, EndpointIdx)>,
)
    requires
        after.inv(),
        index_valid(NUM_CPUS, cpu_id),
        before.prc_mp.dom().contains(process),
        before.thr_mp.dom().contains(caller),
        before.thr_mp.dom().contains(peer),
        caller != peer,
        before.ep_mp.dom().contains(endpoint),
        !(before.thr_mp.spec_index(peer).view().state is SCHEDULED),
        descriptor matches Some((receiver, index)) ==> (receiver == caller || receiver == peer) && edp_idx_valid(index),
        *after == (KernelK { cpu_arr: after.cpu_arr, prc_mp: after.prc_mp, thr_mp: after.thr_mp, ep_mp: after.ep_mp, sched_mp: after.sched_mp, ..*before }),
        kernel_cpu_nonlock_fields_unchanged(before.cpu_arr, after.cpu_arr),
        kernel_process_nonlock_fields_unchanged(before.prc_mp, after.prc_mp),
        after.cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        forall|i: CpuId| #![trigger after.cpu_arr.spec_index(i)] index_valid(NUM_CPUS, i) && i != cpu_id ==>
            after.cpu_arr.spec_index(i).value.locking_thread() == before.cpu_arr.spec_index(i).value.locking_thread(),
        after.prc_mp.spec_index(process).locking_thread() is None,
        forall|p: RwLockProcessPtr| #![trigger after.prc_mp.spec_index(p)] before.prc_mp.dom().contains(p) && p != process ==>
            after.prc_mp.spec_index(p).locking_thread() == before.prc_mp.spec_index(p).locking_thread(),
        after.thr_mp.dom() == before.thr_mp.dom(),
        forall|t: RwLockThreadPtr| #![trigger after.thr_mp.spec_index(t)] before.thr_mp.dom().contains(t) ==> {
            &&& after.thr_mp.spec_index(t).view().state == if t == peer { ThreadState::SCHEDULED } else { before.thr_mp.spec_index(t).view().state }
            &&& after.thr_mp.spec_index(t).view().caller == before.thr_mp.spec_index(t).view().caller
            &&& after.thr_mp.spec_index(t).view().callee == before.thr_mp.spec_index(t).view().callee
            &&& after.thr_mp.spec_index(t).view().owning_container == before.thr_mp.spec_index(t).view().owning_container
            &&& after.thr_mp.spec_index(t).view().owning_proc == before.thr_mp.spec_index(t).view().owning_proc
            &&& after.thr_mp.spec_index(t).view().quota_4k == before.thr_mp.spec_index(t).view().quota_4k
            &&& after.thr_mp.spec_index(t).view().quota_2m == before.thr_mp.spec_index(t).view().quota_2m
            &&& after.thr_mp.spec_index(t).view().quota_1g == before.thr_mp.spec_index(t).view().quota_1g
            &&& after.thr_mp.spec_index(t).view().endpoint_descriptors.view() == if descriptor is Some && t == descriptor->Some_0.0 {
                before.thr_mp.spec_index(t).view().endpoint_descriptors.view().update(descriptor->Some_0.1 as int, Some(endpoint))
            } else { before.thr_mp.spec_index(t).view().endpoint_descriptors.view() }
            &&& after.thr_mp.spec_index(t).view().blocking_endpoint_ptr == if t == peer { None } else { before.thr_mp.spec_index(t).view().blocking_endpoint_ptr }
            &&& after.thr_mp.spec_index(t).view().ipc_payload == if t == peer { IPCPayLoad::Empty } else { before.thr_mp.spec_index(t).view().ipc_payload }
            &&& after.thr_mp.spec_index(t).view().error_code == if t == peer { Some(result) } else { before.thr_mp.spec_index(t).view().error_code }
            &&& after.thr_mp.spec_index(t).view().trap_frame == before.thr_mp.spec_index(t).view().trap_frame
            &&& t != caller ==> after.thr_mp.spec_index(t).view().syscall_progress == before.thr_mp.spec_index(t).view().syscall_progress
            &&& after.thr_mp.spec_index(t).being_killed() == before.thr_mp.spec_index(t).being_killed()
            &&& if t == caller || t == peer { after.thr_mp.spec_index(t).locking_thread() is None }
                else { after.thr_mp.spec_index(t).locking_thread() == before.thr_mp.spec_index(t).locking_thread() }
        },
        after.ep_mp.dom() == before.ep_mp.dom(),
        forall|e: RwLockEndpointPtr| #![trigger after.ep_mp.spec_index(e)] before.ep_mp.dom().contains(e) ==> {
            &&& after.ep_mp.spec_index(e).view().queue.view() == if e == endpoint && dequeue { before.ep_mp.spec_index(e).view().queue.view().skip(1) } else { before.ep_mp.spec_index(e).view().queue.view() }
            &&& after.ep_mp.spec_index(e).view().queue_state == before.ep_mp.spec_index(e).view().queue_state
            &&& after.ep_mp.spec_index(e).view().owning_container == before.ep_mp.spec_index(e).view().owning_container
            &&& after.ep_mp.spec_index(e).view().owning_threads.view() == if e == endpoint && descriptor is Some { before.ep_mp.spec_index(e).view().owning_threads.view().insert(descriptor->Some_0) } else { before.ep_mp.spec_index(e).view().owning_threads.view() }
            &&& after.ep_mp.spec_index(e).being_killed() == before.ep_mp.spec_index(e).being_killed()
            &&& if e == endpoint { after.ep_mp.spec_index(e).locking_thread() is None } else { after.ep_mp.spec_index(e).locking_thread() == before.ep_mp.spec_index(e).locking_thread() }
        },
        after.sched_mp.dom() == before.sched_mp.dom(),
        forall|s: RwLockSchedulerPtr| #![trigger after.sched_mp.spec_index(s)] before.sched_mp.dom().contains(s) ==>
            after.sched_mp.spec_index(s).view().queue.view() == if s == before.ctn_mp.spec_index(before.thr_mp.spec_index(peer).view().owning_container).view_rodata().view().scheduler {
                before.sched_mp.spec_index(s).view().queue.view().push(peer)
            } else { before.sched_mp.spec_index(s).view().queue.view() },
    ensures
        kernel_k_to_kernel_u(*before) != kernel_k_to_kernel_u(*after),
        kernel_k_to_kernel_u(*before).thread_map.dom().contains(caller),
        kernel_k_to_kernel_u(*before).thread_map[caller].syscall_progress == before.thr_mp.spec_index(caller).view().syscall_progress.view(),
        ({
            let pre = kernel_k_to_kernel_u(*before);
            let post = kernel_k_to_kernel_u(*after);
            let threads = match descriptor {
                Some((receiver, index)) => pre.thread_map.insert(receiver, ThreadU { endpoint_descriptors: pre.thread_map[receiver].endpoint_descriptors.update(index as int, Some(endpoint)), ..pre.thread_map[receiver] }),
                None => pre.thread_map,
            };
            let container = pre.thread_map[peer].owning_container;
            post == (KernelU {
                cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..pre.cpu_array[cpu_id as int] }),
                process_map: pre.process_map.insert(process, ProcessU { lock_state: LockStateU::Unlocked, ..pre.process_map[process] }),
                container_map: pre.container_map.insert(container, ContainerU { scheduler: pre.container_map[container].scheduler.push(peer), ..pre.container_map[container] }),
                thread_map: threads.insert(caller, ThreadU {
                    lock_state: LockStateU::Unlocked, syscall_progress: after.thr_mp.spec_index(caller).view().syscall_progress.view(), ..threads[caller]
                }).insert(peer, ThreadU {
                    lock_state: LockStateU::Unlocked, state: ThreadState::SCHEDULED, blocking_endpoint_ptr: None, ipc_payload: IPCPayLoad::Empty, error_code: Some(result), ..threads[peer]
                }),
                endpoint_map: pre.endpoint_map.insert(endpoint, EndpointU { lock_state: LockStateU::Unlocked,
                    queue: if dequeue { pre.endpoint_map[endpoint].queue.skip(1) } else { pre.endpoint_map[endpoint].queue },
                    owning_threads: if descriptor is Some { pre.endpoint_map[endpoint].owning_threads.insert(descriptor->Some_0) } else { pre.endpoint_map[endpoint].owning_threads }, ..pre.endpoint_map[endpoint]
                }),
                ..pre
            })
        }),
{
    reveal(kernel_k_to_kernel_u);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    let threads = match descriptor {
        Some((receiver, index)) => pre.thread_map.insert(receiver, ThreadU { endpoint_descriptors: pre.thread_map[receiver].endpoint_descriptors.update(index as int, Some(endpoint)), ..pre.thread_map[receiver] }),
        None => pre.thread_map,
    };
    let container = pre.thread_map[peer].owning_container;
    assert_seqs_equal!(post.cpu_array == pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..pre.cpu_array[cpu_id as int] }), i => { reveal(kernel_cpu_nonlock_fields_unchanged); });
    assert_maps_equal!(post.process_map, pre.process_map.insert(process, ProcessU { lock_state: LockStateU::Unlocked, ..pre.process_map[process] }), p => { reveal(kernel_process_nonlock_fields_unchanged); });
    assert_maps_equal!(post.container_map, pre.container_map.insert(container, ContainerU { scheduler: pre.container_map[container].scheduler.push(peer), ..pre.container_map[container] }), p => { reveal(container_thread_wf); reveal(container_scheduler_wf); });
    assert_maps_equal!(post.thread_map, threads.insert(caller, ThreadU {
        lock_state: LockStateU::Unlocked, syscall_progress: after.thr_mp.spec_index(caller).view().syscall_progress.view(), ..threads[caller]
    }).insert(peer, ThreadU {
        lock_state: LockStateU::Unlocked, state: ThreadState::SCHEDULED, blocking_endpoint_ptr: None, ipc_payload: IPCPayLoad::Empty, error_code: Some(result), ..threads[peer]
    }), t => {});
    assert_maps_equal!(post.endpoint_map, pre.endpoint_map.insert(endpoint, EndpointU { lock_state: LockStateU::Unlocked,
        queue: if dequeue { pre.endpoint_map[endpoint].queue.skip(1) } else { pre.endpoint_map[endpoint].queue },
        owning_threads: if descriptor is Some { pre.endpoint_map[endpoint].owning_threads.insert(descriptor->Some_0) } else { pre.endpoint_map[endpoint].owning_threads }, ..pre.endpoint_map[endpoint]
    }), e => {});
}

pub proof fn kernel_container_ancestry_projection_at(krnl: &KernelK, container: RwLockContainerPtr)
    requires krnl.ctn_mp.dom().contains(container),
    ensures
        kernel_k_to_kernel_u(*krnl).container_map.dom().contains(container),
        kernel_k_to_kernel_u(*krnl).container_map[container].uppertree_seq == krnl.ctn_mp.spec_index(container).view_ghost().uppertree_seq.view(),
{
    reveal(kernel_k_to_kernel_u);
}

pub proof fn kernel_thread_nonlock_projection_at(krnl: &KernelK, thread_ptr: RwLockThreadPtr)
    requires krnl.thr_mp.dom().contains(thread_ptr),
    ensures
        kernel_k_to_nonlock_kernel_u(*krnl).thread_map.dom().contains(thread_ptr),
        ({
            let thread = krnl.thr_mp.spec_index(thread_ptr);
            let t = thread.view();
            kernel_k_to_nonlock_kernel_u(*krnl).thread_map.spec_index(thread_ptr) == (ThreadU {
                lock_state: LockStateU::Unlocked, state: t.state, caller: t.caller, callee: t.callee,
                owning_container: t.owning_container, owning_proc: t.owning_proc,
                quota_4k: t.quota_4k, quota_2m: t.quota_2m, quota_1g: t.quota_1g,
                endpoint_descriptors: t.endpoint_descriptors.view(), blocking_endpoint_ptr: t.blocking_endpoint_ptr,
                ipc_payload: t.ipc_payload, error_code: t.error_code,
                trap_frame: if t.trap_frame.is_some() { Some(*t.trap_frame.get_some_0()) } else { None },
                syscall_progress: t.syscall_progress.view(), killed: thread.being_killed(),
            })
        }),
{
    reveal(kernel_k_to_nonlock_kernel_u);
}

pub proof fn kernel_process_nonlock_projection_at(krnl: &KernelK, ptr: RwLockProcessPtr)
    requires krnl.prc_mp.dom().contains(ptr),
    ensures
        kernel_k_to_nonlock_kernel_u(*krnl).process_map.dom().contains(ptr),
        ({
            let p = krnl.prc_mp.spec_index(ptr).view();
            let p_ghost = krnl.prc_mp.spec_index(ptr).view_ghost();
            let p_ro = krnl.prc_mp.spec_index(ptr).view_rodata().view();
            kernel_k_to_nonlock_kernel_u(*krnl).process_map[ptr] == (ProcessU {
                lock_state: LockStateU::Unlocked, zombie: p.zombie,
                pagetable: if p.zombie { None } else {
                    let t = pagetable_map_user_view(krnl.pt_mp).spec_index(p.pagetable);
                    Some(PageTableU { lock_state: LockStateU::Unlocked, ..t })
                },
                iommu_table: match (p.zombie, p.iommu_table) {
                    (false, Some(iommu_table)) => {
                        let t = iommu_table_map_user_view(krnl.it_mp).spec_index(iommu_table);
                        Some(PageTableU { lock_state: LockStateU::Unlocked, ..t })
                    },
                    _ => None,
                },
                pcid: p_ro.pcid, owned_pci_functions: p.owned_pci_functions.view(), quota_4k: p.quota_4k, quota_2m: p.quota_2m, quota_1g: p.quota_1g,
                parent: p_ro.parent, children: p.children.view(), depth: p_ro.depth, uppertree_seq: p_ghost.uppertree_seq.view(),
                subtree_set: p_ghost.subtree_set.view(), owned_threads: p.owned_threads.view(), killed: krnl.prc_mp.spec_index(ptr).being_killed(),
            })
        }),
{
    reveal(kernel_k_to_nonlock_kernel_u);
}

pub proof fn kernel_endpoint_queue_projection_at(krnl: &KernelK, endpoint: RwLockEndpointPtr)
    requires krnl.ep_mp.dom().contains(endpoint),
    ensures kernel_k_to_kernel_u(*krnl).endpoint_map[endpoint].queue == krnl.ep_mp.spec_index(endpoint).view().queue.view(),
{
    reveal(kernel_k_to_kernel_u);
}

/// Dequeuing under held cpu/process/thread locks leaves the container projection unchanged.
#[verifier::spinoff_prover]
proof fn kernel_thread_dequeued_implies_u_container_map(before: &KernelK, entry: &KernelK, after: &KernelK)
    requires
        kernel_container_nonlock_fields_and_quotas_unchanged(before, entry),
        *after == (KernelK { thr_mp: after.thr_mp, ep_mp: after.ep_mp, ..*entry }),
        forall|p: RwLockContainerPtr| #![trigger after.ctn_mp.spec_index(p)] before.ctn_mp.dom().contains(p) && after.ctn_mp.dom().contains(p) ==>
            after.ctn_mp.spec_index(p).locking_thread() == before.ctn_mp.spec_index(p).locking_thread(),
    ensures kernel_k_to_kernel_u(*after).container_map == kernel_k_to_kernel_u(*before).container_map,
{
    reveal(kernel_k_to_kernel_u);
    assert_maps_equal!(kernel_k_to_kernel_u(*after).container_map, kernel_k_to_kernel_u(*before).container_map, p => { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); });
}

/// Write-locking `process_ptr` with its other fields unchanged projects to that process write-locked.
#[verifier::spinoff_prover]
proof fn kernel_thread_dequeued_implies_u_process_map(before: &KernelK, entry: &KernelK, after: &KernelK, lctx: &LocalContext, process_ptr: RwLockProcessPtr)
    requires
        after.inv(),
        typed_lock_maps_aligned(after, lctx),
        kernel_cpu_process_thread_nonlock_fields_unchanged(before, entry),
        *after == (KernelK { thr_mp: after.thr_mp, ep_mp: after.ep_mp, ..*entry }),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        forall|p: RwLockProcessPtr| #![trigger after.prc_mp.spec_index(p)] before.prc_mp.dom().contains(p) && after.prc_mp.dom().contains(p) && p != process_ptr ==>
            after.prc_mp.spec_index(p).locking_thread() == before.prc_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger after.pt_mp.spec_index(p)] before.pt_mp.dom().contains(p) && after.pt_mp.dom().contains(p) ==>
            after.pt_mp.spec_index(p).locking_thread() == before.pt_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger after.it_mp.spec_index(p)] before.it_mp.dom().contains(p) && after.it_mp.dom().contains(p) ==>
            after.it_mp.spec_index(p).locking_thread() == before.it_mp.spec_index(p).locking_thread(),
    ensures
        kernel_k_to_kernel_u(*after).process_map
            == kernel_k_to_kernel_u(*before).process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::WriteLocked, ..kernel_k_to_kernel_u(*before).process_map[process_ptr] }),
{
    after.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), process_ptr);
    reveal(kernel_k_to_kernel_u);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    assert_maps_equal!(post.process_map, pre.process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::WriteLocked, ..pre.process_map[process_ptr] }), p => {
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged);
        reveal(process_pagetable_match); reveal(process_iommu_table_match); reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
    });
}

#[verifier::spinoff_prover]
pub proof fn kernel_thread_dequeued_and_locks_changed_implies_u_step(
    before: &KernelK, entry: &KernelK, after: &KernelK, lctx: &LocalContext, cpu_id: CpuId,
    process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr, channel_endpoint_ptr: RwLockEndpointPtr,
)
    requires
        after.inv(),
        typed_lock_maps_aligned(after, lctx),
        before.cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        entry.thr_mp.dom().contains(current_thread_ptr),
        entry.thr_mp.dom().contains(peer_thread_ptr),
        current_thread_ptr != peer_thread_ptr,
        kernel_cpu_process_thread_nonlock_fields_unchanged(before, entry),
        kernel_container_nonlock_fields_and_quotas_unchanged(before, entry),
        kernel_endpoint_nonlock_fields_unchanged(before.ep_mp, entry.ep_mp),
        before.irt.owners() == entry.irt.owners(),
        before.irt.iommu_roots() == entry.irt.iommu_roots(),
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
        after.thr_mp.spec_index(peer_thread_ptr).view().ipc_framed_fields_equal(&entry.thr_mp.spec_index(peer_thread_ptr).view()),
        after.thr_mp.spec_index(peer_thread_ptr).view().state is IPC_ENDPOINT_TRANSIT,
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
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        forall|p: RwLockContainerPtr| #![trigger after.ctn_mp.spec_index(p)] before.ctn_mp.dom().contains(p) && after.ctn_mp.dom().contains(p) ==>
            after.ctn_mp.spec_index(p).locking_thread() == before.ctn_mp.spec_index(p).locking_thread(),
        forall|p: RwLockProcessPtr| #![trigger after.prc_mp.spec_index(p)] before.prc_mp.dom().contains(p) && after.prc_mp.dom().contains(p) && p != process_ptr ==>
            after.prc_mp.spec_index(p).locking_thread() == before.prc_mp.spec_index(p).locking_thread(),
        forall|p: RwLockThreadPtr| #![trigger after.thr_mp.spec_index(p)] before.thr_mp.dom().contains(p) && after.thr_mp.dom().contains(p) && p != current_thread_ptr && p != peer_thread_ptr ==>
            after.thr_mp.spec_index(p).locking_thread() == before.thr_mp.spec_index(p).locking_thread(),
        forall|p: RwLockEndpointPtr| #![trigger after.ep_mp.spec_index(p)] before.ep_mp.dom().contains(p) && after.ep_mp.dom().contains(p) ==>
            after.ep_mp.spec_index(p).locking_thread() == before.ep_mp.spec_index(p).locking_thread(),
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
                cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, ..pre.cpu_array[cpu_id as int] }),
                process_map: pre.process_map.insert(process_ptr, ProcessU { lock_state: LockStateU::WriteLocked, ..pre.process_map[process_ptr] }),
                thread_map: pre.thread_map.insert(current_thread_ptr, ThreadU {
                    lock_state: LockStateU::WriteLocked, syscall_progress: after.thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view(), ..pre.thread_map[current_thread_ptr]
                }).insert(peer_thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, state: ThreadState::IPC_ENDPOINT_TRANSIT,
                    blocking_endpoint_ptr: None, ..pre.thread_map[peer_thread_ptr] }),
                endpoint_map: pre.endpoint_map.insert(channel_endpoint_ptr, EndpointU { queue: pre.endpoint_map[channel_endpoint_ptr].queue.skip(1), ..pre.endpoint_map[channel_endpoint_ptr] }),
                ..pre
            })
        }),
{
    assert(entry.dflt_pt == before.dflt_pt) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
    reveal(kernel_k_to_kernel_u);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    after.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), current_thread_ptr);
    after.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), peer_thread_ptr);
    reveal(LockedArray::typed_lock_map_aligned);
    assert(post.iommu_root_table == pre.iommu_root_table) by { reveal(IommuRootTable::user_view); };
    assert(pre.thread_map.dom().contains(current_thread_ptr) && pre.thread_map[current_thread_ptr].syscall_progress == entry.thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view()) by {
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
    };
    assert_seqs_equal!(post.cpu_array == pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, ..pre.cpu_array[cpu_id as int] }), i => {
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
    });
    assert_maps_equal!(post.thread_map, pre.thread_map.insert(current_thread_ptr, ThreadU {
        lock_state: LockStateU::WriteLocked, syscall_progress: after.thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view(), ..pre.thread_map[current_thread_ptr]
    }).insert(peer_thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, state: ThreadState::IPC_ENDPOINT_TRANSIT,
        blocking_endpoint_ptr: None, ..pre.thread_map[peer_thread_ptr] }), p => {
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
    });
    assert_maps_equal!(post.endpoint_map, pre.endpoint_map.insert(channel_endpoint_ptr, EndpointU {
        queue: pre.endpoint_map[channel_endpoint_ptr].queue.skip(1), ..pre.endpoint_map[channel_endpoint_ptr]
    }), p => { reveal(kernel_endpoint_nonlock_fields_unchanged); });
    kernel_thread_dequeued_implies_u_container_map(before, entry, after);
    kernel_thread_dequeued_implies_u_process_map(before, entry, after, lctx, process_ptr);
}

pub proof fn kernel_process_published_and_parent_unlocked_implies_u_step(
    before: &KernelK, after: &KernelK, lctx: &LocalContext, parent: RwLockProcessPtr, child: RwLockProcessPtr, thread: RwLockThreadPtr, container: RwLockContainerPtr,
    table: RwLockPageTableRoot, iommu: Option<RwLockPageTableRoot>, pcid_allocator: RwLockPcidAllocatorPtr, pcid: Pcid, progress: Option<SyscallProgress>,
)
    requires
        before.inv(),
        typed_lock_maps_aligned(after, lctx),
        *after == (KernelK { pg_arr: after.pg_arr, prc_mp: after.prc_mp, thr_mp: after.thr_mp, ctn_mp: after.ctn_mp,
            pt_mp: after.pt_mp, it_mp: after.it_mp, pcid_allc_mp: after.pcid_allc_mp, ..*before }),
        before.prc_mp.dom().contains(parent),
        !before.prc_mp.dom().contains(child),
        after.prc_mp.dom() == before.prc_mp.dom().insert(child),
        forall|p: RwLockProcessPtr| #![trigger after.prc_mp.spec_index(p)] before.prc_mp.dom().contains(p) ==> {
            &&& after.prc_mp.spec_index(p).view_rodata() == before.prc_mp.spec_index(p).view_rodata()
            &&& after.prc_mp.spec_index(p).view_ghost().uppertree_seq == before.prc_mp.spec_index(p).view_ghost().uppertree_seq
            &&& after.prc_mp.spec_index(p).view_ghost().subtree_set.view() == if before.prc_mp.spec_index(parent).view_ghost().uppertree_seq.view().push(parent).contains(p) {
                before.prc_mp.spec_index(p).view_ghost().subtree_set.view().insert(child)
            } else { before.prc_mp.spec_index(p).view_ghost().subtree_set.view() }
            &&& after.prc_mp.spec_index(p).view() == (Process { children: after.prc_mp.spec_index(p).view().children, ..before.prc_mp.spec_index(p).view() })
            &&& after.prc_mp.spec_index(p).view().children.view() == if p == parent { before.prc_mp.spec_index(p).view().children.view().push(child) } else { before.prc_mp.spec_index(p).view().children.view() }
            &&& after.prc_mp.spec_index(p).being_killed() == before.prc_mp.spec_index(p).being_killed()
            &&& if p == parent { after.prc_mp.spec_index(p).locking_thread() is None } else { after.prc_mp.spec_index(p).locking_thread() == before.prc_mp.spec_index(p).locking_thread() }
        },
        typed_lock_map_contains_mode(lctx.process_lock_map(), child, TypedLockMode::Write),
        !after.prc_mp.spec_index(child).being_killed(),
        !after.prc_mp.spec_index(child).view().zombie,
        after.prc_mp.spec_index(child).view().pagetable == table,
        after.prc_mp.spec_index(child).view().iommu_table == iommu,
        after.prc_mp.spec_index(child).view().owned_pci_functions.view().is_empty(),
        after.prc_mp.spec_index(child).view().quota_4k == 0,
        after.prc_mp.spec_index(child).view().quota_2m == 0,
        after.prc_mp.spec_index(child).view().quota_1g == 0,
        after.prc_mp.spec_index(child).view_rodata().view().parent == Some(parent),
        after.prc_mp.spec_index(child).view_rodata().view().depth == before.prc_mp.spec_index(parent).view_rodata().view().depth + 1,
        after.prc_mp.spec_index(child).view().children.view() == Seq::<RwLockProcessPtr>::empty(),
        after.prc_mp.spec_index(child).view().owned_threads.view() == Seq::<RwLockThreadPtr>::empty(),
        after.prc_mp.spec_index(child).view_ghost().uppertree_seq.view() == before.prc_mp.spec_index(parent).view_ghost().uppertree_seq.view().push(parent),
        after.prc_mp.spec_index(child).view_ghost().subtree_set.view().is_empty(),
        before.thr_mp.spec_index(thread).view().quota_4k >= if iommu is Some { 5usize } else { 3usize },
        after.thr_mp.unchanged_except(&before.thr_mp, thread),
        kernel_thread_quota_4k_changed(before, after, thread, if iommu is Some { -5 } else { -3 }),
        after.thr_mp.spec_index(thread).view().syscall_progress.view() == progress,
        after.thr_mp.spec_index(thread).locking_thread() == before.thr_mp.spec_index(thread).locking_thread(),
        after.ctn_mp.unchanged_except(&before.ctn_mp, container),
        after.ctn_mp.spec_index(container).view_rodata() == before.ctn_mp.spec_index(container).view_rodata(),
        after.ctn_mp.spec_index(container).view_ghost() == (ContainerGhost { owned_processes: after.ctn_mp.spec_index(container).view_ghost().owned_processes, ..before.ctn_mp.spec_index(container).view_ghost() }),
        after.ctn_mp.spec_index(container).being_killed() == before.ctn_mp.spec_index(container).being_killed(),
        after.ctn_mp.spec_index(container).locking_thread() == before.ctn_mp.spec_index(container).locking_thread(),
        after.ctn_mp.spec_index(container).view() == before.ctn_mp.spec_index(container).view(),
        after.ctn_mp.spec_index(container).view_ghost().owned_processes.view() == before.ctn_mp.spec_index(container).view_ghost().owned_processes.view().insert(child),
        before.ctn_mp.spec_index(container).view_rodata().view().pcid_allocator == pcid_allocator,
        after.pcid_allc_mp.unchanged_except(&before.pcid_allc_mp, pcid_allocator),
        PcidAllocator::free_pcids(before.pcid_allc_mp.spec_index(pcid_allocator).view().ref_counters.view()).contains(pcid),
        after.pcid_allc_mp.spec_index(pcid_allocator).view().alloc_ensures(&before.pcid_allc_mp.spec_index(pcid_allocator).view(), child, pcid),
        after.pt_mp.dom() == before.pt_mp.dom().insert(table),
        forall|p: RwLockPageTableRoot| #![trigger after.pt_mp.spec_index(p)] before.pt_mp.dom().contains(p) ==> after.pt_mp.spec_index(p) == before.pt_mp.spec_index(p),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), table, TypedLockMode::Write),
        after.pt_mp.spec_index(table).view().is_empty(),
        iommu is None ==> after.it_mp == before.it_mp,
        iommu matches Some(t) ==> {
            &&& after.it_mp.dom() == before.it_mp.dom().insert(t)
            &&& forall|p: RwLockPageTableRoot| #![trigger after.it_mp.spec_index(p)] before.it_mp.dom().contains(p) ==> after.it_mp.spec_index(p) == before.it_mp.spec_index(p)
            &&& typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), t, TypedLockMode::Write)
            &&& after.it_mp.spec_index(t).view().is_empty()
        },
    ensures
        ({
            let pre = kernel_k_to_kernel_u(*before);
            let post = kernel_k_to_kernel_u(*after);
            let ancestors = pre.process_map[parent].uppertree_seq.push(parent);
            let empty_table = PageTableU { lock_state: LockStateU::WriteLocked, mapping_4k: Map::empty(), mapping_2m: Map::empty(), mapping_1g: Map::empty() };
            let cost: usize = if (iommu is Some) { 5 } else { 3 };
            &&& pre.process_map.dom().contains(parent)
            &&& !pre.process_map.dom().contains(child)
            &&& pre.thread_map.dom().contains(thread)
            &&& pre.thread_map[thread].syscall_progress == before.thr_mp.spec_index(thread).view().syscall_progress.view()
            &&& pre.container_map.dom().contains(container)
            &&& pre.thread_map[thread].quota_4k >= cost
            &&& post.container_map[container].free_pcids.subset_of(pre.container_map[container].free_pcids)
            &&& pre.container_map[container].free_pcids.difference(post.container_map[container].free_pcids).len() == 1
            &&& post.process_map.dom() == pre.process_map.dom().insert(child)
            &&& forall|p: RwLockProcessPtr| #![trigger post.process_map[p]] pre.process_map.dom().contains(p) ==> post.process_map[p] == (ProcessU {
                lock_state: if p == parent { LockStateU::Unlocked } else { pre.process_map[p].lock_state },
                children: if p == parent { pre.process_map[p].children.push(child) } else { pre.process_map[p].children },
                subtree_set: if ancestors.contains(p) { pre.process_map[p].subtree_set.insert(child) } else { pre.process_map[p].subtree_set },
                ..pre.process_map[p]
            })
            &&& post.process_map[child] == (ProcessU {
                lock_state: LockStateU::WriteLocked, zombie: false, pagetable: Some(empty_table),
                iommu_table: if (iommu is Some) { Some(empty_table) } else { None }, pcid: post.process_map[child].pcid, owned_pci_functions: Set::empty(),
                quota_4k: 0, quota_2m: 0, quota_1g: 0, parent: Some(parent), children: Seq::empty(),
                depth: (pre.process_map[parent].depth + 1) as usize, uppertree_seq: ancestors,
                subtree_set: Set::empty(), owned_threads: Seq::empty(), killed: false,
            })
            &&& post == (KernelU {
                process_map: post.process_map,
                container_map: pre.container_map.insert(container, ContainerU {
                    owned_processes: pre.container_map[container].owned_processes.insert(child),
                    free_pcids: post.container_map[container].free_pcids, ..pre.container_map[container]
                }),
                thread_map: pre.thread_map.insert(thread, ThreadU { quota_4k: (pre.thread_map[thread].quota_4k - cost) as usize, syscall_progress: progress, ..pre.thread_map[thread] }),
                ..pre
            })
        }),
{
    reveal(kernel_k_to_kernel_u);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    let ancestors = pre.process_map[parent].uppertree_seq.push(parent);
    let cost: usize = if iommu is Some { 5 } else { 3 };
    after.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), child);
    after.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), table);
    if let Some(t) = iommu { after.it_mp.typed_lock_map_aligned_write_at(lctx.iommu_table_lock_map(), lctx.thread_id(), t); }
    assert_seqs_equal!(post.cpu_array == pre.cpu_array);
    assert_maps_equal!(post.endpoint_map, pre.endpoint_map, p => {});
    assert_maps_equal!(post.thread_map, pre.thread_map.insert(thread, ThreadU {
        quota_4k: (pre.thread_map[thread].quota_4k - cost) as usize, syscall_progress: progress, ..pre.thread_map[thread]
    }), p => { reveal(kernel_thread_quota_4k_changed); });
    assert_maps_equal!(post.container_map, pre.container_map.insert(container, ContainerU {
        owned_processes: pre.container_map[container].owned_processes.insert(child), free_pcids: post.container_map[container].free_pcids, ..pre.container_map[container]
    }), p => { reveal(container_pcid_allocator_wf); });
    assert_maps_equal!(post.process_map, Map::new(pre.process_map.dom(), |p: RwLockProcessPtr| ProcessU {
        lock_state: if p == parent { LockStateU::Unlocked } else { pre.process_map[p].lock_state },
        children: if p == parent { pre.process_map[p].children.push(child) } else { pre.process_map[p].children },
        subtree_set: if ancestors.contains(p) { pre.process_map[p].subtree_set.insert(child) } else { pre.process_map[p].subtree_set }, ..pre.process_map[p]
    }).insert(child, post.process_map[child]), p => { reveal(process_pagetable_match); reveal(process_iommu_table_match); });
    assert(post.container_map[container].free_pcids =~= pre.container_map[container].free_pcids.remove(pcid)) by { pcid_allocator_perms_wf_at(before.pcid_allc_mp, pcid_allocator); };
    assert_sets_equal!(pre.container_map[container].free_pcids.difference(post.container_map[container].free_pcids), set![pcid]);
    assert_maps_equal!(post.process_map[child].pagetable->Some_0.mapping_4k, Map::empty(), va => {});
    assert_maps_equal!(post.process_map[child].pagetable->Some_0.mapping_2m, Map::empty(), va => {});
    assert_maps_equal!(post.process_map[child].pagetable->Some_0.mapping_1g, Map::empty(), va => {});
    if iommu is Some {
        assert_maps_equal!(post.process_map[child].iommu_table->Some_0.mapping_4k, Map::empty(), va => {});
        assert_maps_equal!(post.process_map[child].iommu_table->Some_0.mapping_2m, Map::empty(), va => {});
        assert_maps_equal!(post.process_map[child].iommu_table->Some_0.mapping_1g, Map::empty(), va => {});
    }
}

pub proof fn kernel_thread_quota_and_page_owner_changed_implies_u_step(
    pre: &KernelK, post: &KernelK, lctx: &LocalContext, thread: RwLockThreadPtr,
    source: RwLockContainerPtr, target: RwLockContainerPtr, page: PagePtr, table: RwLockPageTableRoot,
)
    requires
        pre.inv(),
        pre.thr_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        post.thr_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread, TypedLockMode::Write),
        *post == (KernelK { pg_arr: post.pg_arr, ctn_mp: post.ctn_mp, thr_mp: post.thr_mp, pt_mp: post.pt_mp, ..*pre }),
        source != target,
        pre.ctn_mp.dom().contains(source),
        pre.ctn_mp.dom().contains(target),
        pre.ctn_mp.spec_index(source).view().owned_pages.view().contains(page),
        post.ctn_mp.dom() == pre.ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)] pre.ctn_mp.dom().contains(c) ==> {
            &&& post.ctn_mp.spec_index(c).view_rodata() == pre.ctn_mp.spec_index(c).view_rodata()
            &&& post.ctn_mp.spec_index(c).view_ghost() == pre.ctn_mp.spec_index(c).view_ghost()
            &&& post.ctn_mp.spec_index(c).locking_thread() == pre.ctn_mp.spec_index(c).locking_thread()
            &&& post.ctn_mp.spec_index(c).being_killed() == pre.ctn_mp.spec_index(c).being_killed()
            &&& post.ctn_mp.spec_index(c).view() == (Container { owned_pages: post.ctn_mp.spec_index(c).view().owned_pages, ..pre.ctn_mp.spec_index(c).view() })
            &&& post.ctn_mp.spec_index(c).view().owned_pages.view() == if c == source { pre.ctn_mp.spec_index(c).view().owned_pages.view().remove(page) }
                else if c == target { pre.ctn_mp.spec_index(c).view().owned_pages.view().insert(page) } else { pre.ctn_mp.spec_index(c).view().owned_pages.view() }
        },
        post.thr_mp.unchanged_except(&pre.thr_mp, thread),
        kernel_thread_quota_4k_changed(pre, post, thread, -1),
        post.thr_mp.spec_index(thread).view().syscall_progress == pre.thr_mp.spec_index(thread).view().syscall_progress,
        post.pt_mp.unchanged_except(&pre.pt_mp, table),
        pre.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        post.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), table, TypedLockMode::Write),
        post.pt_mp.spec_index(table).view().mapping_4k() == pre.pt_mp.spec_index(table).view().mapping_4k(),
        post.pt_mp.spec_index(table).view().mapping_2m() == pre.pt_mp.spec_index(table).view().mapping_2m(),
        post.pt_mp.spec_index(table).view().mapping_1g() == pre.pt_mp.spec_index(table).view().mapping_1g(),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let b = kernel_k_to_kernel_u(*post);
            &&& a.thread_map.dom().contains(thread)
            &&& a.thread_map[thread].lock_state is WriteLocked
            &&& a.thread_map[thread].quota_4k > 0
            &&& a.container_map.dom().contains(source) && a.container_map.dom().contains(target)
            &&& a.container_map[source].owned_pages.difference(b.container_map[source].owned_pages).len() == 1
            &&& b.container_map[source].owned_pages.subset_of(a.container_map[source].owned_pages)
            &&& b.container_map[target].owned_pages == a.container_map[target].owned_pages.union(a.container_map[source].owned_pages.difference(b.container_map[source].owned_pages))
            &&& b == (KernelU {
                thread_map: a.thread_map.insert(thread, ThreadU { quota_4k: (a.thread_map[thread].quota_4k - 1) as usize, ..a.thread_map[thread] }),
                container_map: a.container_map.insert(source, ContainerU { owned_pages: a.container_map[source].owned_pages.remove(page), ..a.container_map[source] })
                    .insert(target, ContainerU { owned_pages: a.container_map[target].owned_pages.insert(page), ..a.container_map[target] }),
                ..a
            })
        }),
{
    pre.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread);
    post.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread);
    pre.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), table);
    post.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), table);
    reveal(kernel_k_to_kernel_u);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    assert(a.thread_map[thread].quota_4k > 0) by { reveal(kernel_thread_quota_4k_changed); };
    assert_seqs_equal!(b.cpu_array == a.cpu_array);
    assert_maps_equal!(b.endpoint_map, a.endpoint_map, p => {});
    assert_maps_equal!(b.process_map, a.process_map, p => { reveal(process_pagetable_match); });
    assert_maps_equal!(b.thread_map, a.thread_map.insert(thread, ThreadU { quota_4k: (a.thread_map[thread].quota_4k - 1) as usize, ..a.thread_map[thread] }), p => { reveal(kernel_thread_quota_4k_changed); });
    assert_maps_equal!(b.container_map, a.container_map.insert(source, ContainerU { owned_pages: a.container_map[source].owned_pages.remove(page), ..a.container_map[source] })
        .insert(target, ContainerU { owned_pages: a.container_map[target].owned_pages.insert(page), ..a.container_map[target] }), p => {});
    assert_sets_equal!(a.container_map[source].owned_pages.difference(b.container_map[source].owned_pages), set![page]);
    assert_sets_equal!(b.container_map[target].owned_pages, a.container_map[target].owned_pages.union(a.container_map[source].owned_pages.difference(b.container_map[source].owned_pages)));
}

/// Copying one present source entry into an absent target address and replacing `progress_thread`'s
/// progress changes only the target pagetable's 4K mapping and that thread's progress.
pub proof fn kernel_4k_mapping_copied_implies_u_step(
    pre: &KernelK, post: &KernelK, lctx: &LocalContext, source: RwLockProcessPtr, target: RwLockProcessPtr,
    source_table: RwLockPageTableRoot, target_table: RwLockPageTableRoot, source_va: VAddr, target_va: VAddr, progress_thread: RwLockThreadPtr,
)
    requires
        pre.inv(),
        typed_lock_maps_aligned(pre, lctx),
        source != target,
        pre.prc_mp.dom().contains(source),
        pre.prc_mp.dom().contains(target),
        !pre.prc_mp.spec_index(source).view().zombie,
        !pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(source).view().pagetable == source_table,
        pre.prc_mp.spec_index(target).view().pagetable == target_table,
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), source_table, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), target_table, TypedLockMode::Write),
        pre.pt_mp.spec_index(source_table).view().mapping_4k().dom().contains(source_va),
        pre.pt_mp.spec_index(source_table).view().mapping_4k()[source_va].present,
        !pre.pt_mp.spec_index(target_table).view().mapping_4k().dom().contains(target_va) || !pre.pt_mp.spec_index(target_table).view().mapping_4k()[target_va].present,
        *post == (KernelK { pg_arr: post.pg_arr, pt_mp: post.pt_mp, thr_mp: post.thr_mp, ..*pre }),
        pre.thr_mp.dom().contains(progress_thread),
        post.thr_mp.unchanged_except(&pre.thr_mp, progress_thread),
        post.thr_mp.spec_index(progress_thread).view() == (Thread { syscall_progress: post.thr_mp.spec_index(progress_thread).view().syscall_progress, ..pre.thr_mp.spec_index(progress_thread).view() }),
        post.thr_mp.spec_index(progress_thread).locking_thread() == pre.thr_mp.spec_index(progress_thread).locking_thread(),
        post.thr_mp.spec_index(progress_thread).being_killed() == pre.thr_mp.spec_index(progress_thread).being_killed(),
        post.pt_mp.unchanged_except(&pre.pt_mp, target_table),
        post.pt_mp.spec_index(target_table).locking_thread() == pre.pt_mp.spec_index(target_table).locking_thread(),
        post.pt_mp.spec_index(target_table).view().mapping_4k() == pre.pt_mp.spec_index(target_table).view().mapping_4k().insert(target_va, pre.pt_mp.spec_index(source_table).view().mapping_4k()[source_va]),
        post.pt_mp.spec_index(target_table).view().mapping_2m() == pre.pt_mp.spec_index(target_table).view().mapping_2m(),
        post.pt_mp.spec_index(target_table).view().mapping_1g() == pre.pt_mp.spec_index(target_table).view().mapping_1g(),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let b = kernel_k_to_kernel_u(*post);
            &&& a.process_map.dom().contains(source) && a.process_map.dom().contains(target)
            &&& a.process_map[source].pagetable is Some && a.process_map[target].pagetable is Some
            &&& a.process_map[source].pagetable->Some_0.lock_state is WriteLocked
            &&& a.process_map[target].pagetable->Some_0.lock_state is WriteLocked
            &&& a.process_map[source].pagetable->Some_0.mapping_4k.dom().contains(source_va)
            &&& !a.process_map[target].pagetable->Some_0.mapping_4k.dom().contains(target_va)
            &&& a.thread_map.dom().contains(progress_thread)
            &&& a.thread_map[progress_thread].syscall_progress == pre.thr_mp.spec_index(progress_thread).view().syscall_progress.view()
            &&& b == (KernelU {
                thread_map: a.thread_map.insert(progress_thread, ThreadU {
                    syscall_progress: post.thr_mp.spec_index(progress_thread).view().syscall_progress.view(), ..a.thread_map[progress_thread]
                }),
                process_map: a.process_map.insert(target, ProcessU {
                    pagetable: Some(PageTableU { mapping_4k: a.process_map[target].pagetable->Some_0.mapping_4k.insert(target_va, a.process_map[source].pagetable->Some_0.mapping_4k[source_va]),
                        ..a.process_map[target].pagetable->Some_0 }), ..a.process_map[target]
                }),
                ..a
            })
        }),
{
    pre.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), source_table);
    pre.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), target_table);
    reveal(kernel_k_to_kernel_u);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    assert_seqs_equal!(b.cpu_array == a.cpu_array);
    assert_maps_equal!(b.container_map, a.container_map, p => {});
    assert_maps_equal!(b.thread_map, a.thread_map.insert(progress_thread, ThreadU {
        syscall_progress: post.thr_mp.spec_index(progress_thread).view().syscall_progress.view(), ..a.thread_map[progress_thread]
    }), t => {});
    assert_maps_equal!(b.endpoint_map, a.endpoint_map, p => {});
    assert_maps_equal!(b.process_map, a.process_map.insert(target, ProcessU {
        pagetable: Some(PageTableU { mapping_4k: a.process_map[target].pagetable->Some_0.mapping_4k.insert(target_va, a.process_map[source].pagetable->Some_0.mapping_4k[source_va]),
            ..a.process_map[target].pagetable->Some_0 }), ..a.process_map[target]
    }), p => {
        reveal(process_pagetable_match);
        if p == target {
            assert_maps_equal!(b.process_map[target].pagetable->Some_0.mapping_4k,
                a.process_map[target].pagetable->Some_0.mapping_4k.insert(target_va, a.process_map[source].pagetable->Some_0.mapping_4k[source_va]), va => {});
        }
    });
}

pub proof fn kernel_process_lock_mode_changed_implies_u_map(pre: &KernelK, post: &KernelK, lctx: &LocalContext, process: RwLockProcessPtr)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        post.prc_mp.typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id()),
        kernel_process_nonlock_fields_unchanged(pre.prc_mp, post.prc_mp),
        kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, post.pt_mp),
        kernel_iommu_table_nonlock_fields_unchanged(pre.it_mp, post.it_mp),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process, TypedLockMode::Write),
        forall|p: RwLockProcessPtr| #![trigger pre.prc_mp.spec_index(p)] #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) && post.prc_mp.dom().contains(p) && p != process ==> post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger pre.it_mp.spec_index(p)] #![trigger post.it_mp.spec_index(p)]
            pre.it_mp.dom().contains(p) && post.it_mp.dom().contains(p) ==> post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger pre.pt_mp.spec_index(p)] #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) && post.pt_mp.dom().contains(p) ==> post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread(),
    ensures
        ({
            let before = kernel_k_to_kernel_u(*pre);
            let after = kernel_k_to_kernel_u(*post);
            let processes = before.process_map.insert(process, ProcessU { lock_state: LockStateU::WriteLocked, ..before.process_map[process] });
            after.process_map == processes
        }),
{
    post.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), process);
    reveal(kernel_k_to_kernel_u);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    let processes = before.process_map.insert(process, ProcessU { lock_state: LockStateU::WriteLocked, ..before.process_map[process] });
    assert_maps_equal!(after.process_map, processes, p => {
        reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged);
        reveal(kernel_iommu_table_nonlock_fields_unchanged); reveal(process_pagetable_match); reveal(process_iommu_table_match);
    });
}

#[verifier::spinoff_prover]
pub proof fn kernel_process_and_pagetable_lock_modes_changed_implies_u_map(
    pre: &KernelK, post: &KernelK, lctx: &LocalContext, process: RwLockProcessPtr, source: RwLockProcessPtr, target: RwLockProcessPtr,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        post.prc_mp.typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id()),
        post.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        pre.prc_mp.dom().contains(process),
        kernel_process_nonlock_fields_unchanged(pre.prc_mp, post.prc_mp),
        kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, post.pt_mp),
        kernel_iommu_table_nonlock_fields_unchanged(pre.it_mp, post.it_mp),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process, TypedLockMode::Write),
        forall|p: RwLockProcessPtr| #![trigger pre.prc_mp.spec_index(p)] #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) && post.prc_mp.dom().contains(p) && p != process ==> post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread(),
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
            let processes = before.process_map.insert(process, ProcessU { lock_state: LockStateU::WriteLocked, ..before.process_map[process] });
            let locked_processes = processes.insert(source, ProcessU {
                pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..processes[source].pagetable->Some_0 }), ..processes[source]
            }).insert(target, ProcessU {
                pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..processes[target].pagetable->Some_0 }), ..processes[target]
            });
            after.process_map == locked_processes
        }),
{
    post.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), process);
    post.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pre.prc_mp.spec_index(source).view().pagetable);
    post.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pre.prc_mp.spec_index(target).view().pagetable);
    reveal(kernel_k_to_kernel_u);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    let processes = before.process_map.insert(process, ProcessU { lock_state: LockStateU::WriteLocked, ..before.process_map[process] });
    let locked_processes = processes.insert(source, ProcessU {
        pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..processes[source].pagetable->Some_0 }), ..processes[source]
    }).insert(target, ProcessU {
        pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..processes[target].pagetable->Some_0 }), ..processes[target]
    });
    assert_maps_equal!(after.process_map, locked_processes, p => {
        reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged);
        reveal(kernel_iommu_table_nonlock_fields_unchanged); reveal(process_pagetable_match); reveal(process_iommu_table_match);
    });
}

#[verifier::spinoff_prover]
pub proof fn kernel_cpu_and_two_threads_lock_modes_changed_implies_u_step(
    pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu: CpuId, process: RwLockProcessPtr,
    caller: RwLockThreadPtr, peer: RwLockThreadPtr, endpoint: RwLockEndpointPtr, tables: Option<(RwLockProcessPtr, RwLockProcessPtr)>,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        typed_lock_maps_aligned(post, lctx),
        index_valid(NUM_CPUS, cpu),
        pre.prc_mp.dom().contains(process),
        pre.thr_mp.dom().contains(caller),
        pre.thr_mp.dom().contains(peer),
        pre.ep_mp.dom().contains(endpoint),
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post),
        kernel_container_nonlock_fields_and_quotas_unchanged(pre, post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        pre.irt.owners() == post.irt.owners(),
        pre.irt.iommu_roots() == post.irt.iommu_roots(),
        pre.cpu_tlb.view() == post.cpu_tlb.view(),
        pre.iommu_tlb.view() == post.iommu_tlb.view(),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process, TypedLockMode::Write),
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
            pre.ctn_mp.dom().contains(p) && post.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).locking_thread() == pre.ctn_mp.spec_index(p).locking_thread(),
        forall|p: RwLockProcessPtr| #![trigger pre.prc_mp.spec_index(p)] #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) && post.prc_mp.dom().contains(p) && p != process ==> post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread(),
        forall|p: RwLockThreadPtr| #![trigger pre.thr_mp.spec_index(p)] #![trigger post.thr_mp.spec_index(p)]
            pre.thr_mp.dom().contains(p) && post.thr_mp.dom().contains(p) && p != caller && p != peer ==> post.thr_mp.spec_index(p).locking_thread() == pre.thr_mp.spec_index(p).locking_thread(),
        forall|p: RwLockEndpointPtr| #![trigger pre.ep_mp.spec_index(p)] #![trigger post.ep_mp.spec_index(p)]
            pre.ep_mp.dom().contains(p) && post.ep_mp.dom().contains(p) && p != endpoint ==> post.ep_mp.spec_index(p).locking_thread() == pre.ep_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger pre.it_mp.spec_index(p)] #![trigger post.it_mp.spec_index(p)]
            pre.it_mp.dom().contains(p) && post.it_mp.dom().contains(p) ==> post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger pre.pt_mp.spec_index(p)] #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) && post.pt_mp.dom().contains(p) && (tables is None || p != pre.prc_mp.spec_index(tables->Some_0.0).view().pagetable && p != pre.prc_mp.spec_index(tables->Some_0.1).view().pagetable) ==> post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread(),
    ensures
        kernel_k_to_kernel_u(*pre).thread_map[caller].owning_proc == pre.thr_mp.spec_index(caller).view().owning_proc,
        kernel_k_to_kernel_u(*pre).thread_map[peer].owning_proc == pre.thr_mp.spec_index(peer).view().owning_proc,
        kernel_k_to_kernel_u(*pre).thread_map[caller].owning_container == pre.thr_mp.spec_index(caller).view().owning_container,
        kernel_k_to_kernel_u(*pre).thread_map[peer].owning_container == pre.thr_mp.spec_index(peer).view().owning_container,
        pre.cpu_arr.spec_index(cpu).value.locking_thread() is None ==> kernel_k_to_kernel_u(*pre).cpu_array[cpu as int].lock_state is Unlocked,
        kernel_k_to_kernel_u(*post).cpu_array[cpu as int].lock_state is WriteLocked,
        ({
            let before = kernel_k_to_kernel_u(*pre);
            let processes = before.process_map.insert(process, ProcessU { lock_state: LockStateU::WriteLocked, ..before.process_map[process] });
            let locked_processes = match tables {
                None => processes,
                Some((source, target)) => processes.insert(source, ProcessU {
                    pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..processes[source].pagetable->Some_0 }), ..processes[source]
                }).insert(target, ProcessU {
                    pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..processes[target].pagetable->Some_0 }), ..processes[target]
                }),
            };
            kernel_k_to_kernel_u(*post) == (KernelU {
                cpu_array: before.cpu_array.update(cpu as int, CpuU { lock_state: LockStateU::WriteLocked, ..before.cpu_array[cpu as int] }),
                process_map: locked_processes,
                thread_map: before.thread_map.insert(caller, ThreadU { lock_state: LockStateU::WriteLocked, ..before.thread_map[caller] })
                    .insert(peer, ThreadU { lock_state: LockStateU::WriteLocked, ..before.thread_map[peer] }),
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
    reveal(kernel_k_to_kernel_u);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    let processes = before.process_map.insert(process, ProcessU { lock_state: LockStateU::WriteLocked, ..before.process_map[process] });
    let locked_processes = match tables {
        None => processes,
        Some((source, target)) => processes.insert(source, ProcessU {
            pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..processes[source].pagetable->Some_0 }), ..processes[source]
        }).insert(target, ProcessU {
            pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..processes[target].pagetable->Some_0 }), ..processes[target]
        }),
    };
    assert_seqs_equal!(after.cpu_array == before.cpu_array.update(cpu as int, CpuU { lock_state: LockStateU::WriteLocked, ..before.cpu_array[cpu as int] }), i => { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged); });
    assert(after.process_map == locked_processes) by {
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
        match tables {
            Some((source, target)) => kernel_process_and_pagetable_lock_modes_changed_implies_u_map(pre, post, lctx, process, source, target),
            None => kernel_process_lock_mode_changed_implies_u_map(pre, post, lctx, process),
        }
    };
    assert_maps_equal!(after.container_map, before.container_map, p => { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); });
    assert_maps_equal!(after.thread_map, before.thread_map.insert(caller, ThreadU { lock_state: LockStateU::WriteLocked, ..before.thread_map[caller] })
        .insert(peer, ThreadU { lock_state: LockStateU::WriteLocked, ..before.thread_map[peer] }), p => { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged); });
    assert_maps_equal!(after.endpoint_map, before.endpoint_map.insert(endpoint, EndpointU { lock_state: LockStateU::WriteLocked, ..before.endpoint_map[endpoint] }), p => { reveal(kernel_endpoint_nonlock_fields_unchanged); });
    assert(after.iommu_root_table == before.iommu_root_table) by { reveal(IommuRootTable::user_view); };
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
        *post == (KernelK { cpu_arr: post.cpu_arr, prc_mp: post.prc_mp, thr_mp: post.thr_mp, ep_mp: post.ep_mp, sched_mp: post.sched_mp, ctn_mp: post.ctn_mp, pt_mp: post.pt_mp, pcid_allc_mp: post.pcid_allc_mp, cpu_set_mp: post.cpu_set_mp, ..*pre }),
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
        post.cpu_arr.unchanged_except(&pre.cpu_arr, cpu_id),
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
                &&& if write_locked { typed_lock_map_contains_mode(lctx.cpu_set_lock_map(), s, TypedLockMode::Write) } else { post.cpu_set_mp.spec_index(s).locking_thread() is None }
                &&& kernel_container_nonlock_fields_and_quotas_unchanged(pre, &mid)
            },
            None => kernel_container_nonlock_fields_and_quotas_unchanged(pre, post),
        },
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
    ensures
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let mode = if write_locked { LockStateU::WriteLocked } else { LockStateU::Unlocked };
            kernel_k_to_kernel_u(*post) == (KernelU {
                cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, ..old_u.cpu_array[cpu_id as int] }),
                container_map: match container {
                    Some(c) => old_u.container_map.insert(c, ContainerU {
                        lock_state: mode, cpu_set_lock: if cpu_set_unlocked is Some { mode } else { old_u.container_map[c].cpu_set_lock }, ..old_u.container_map[c]
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
                current_process: c.current_process, current_thread: c.current_thread,
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
                owning_container: t.owning_container, owning_proc: t.owning_proc, quota_4k: t.quota_4k, quota_2m: t.quota_2m, quota_1g: t.quota_1g,
                endpoint_descriptors: t.endpoint_descriptors.view(), blocking_endpoint_ptr: t.blocking_endpoint_ptr, ipc_payload: t.ipc_payload,
                error_code: t.error_code, trap_frame: if t.trap_frame.is_some() { Some(*t.trap_frame.get_some_0()) } else { None },
                syscall_progress: t.syscall_progress.view(), killed: thread.being_killed(),
            })
            &&& endpoint_ptr is Some ==> old_u.endpoint_map.spec_index(endpoint_ptr->Some_0).lock_state == pre.ep_mp.spec_index(endpoint_ptr->Some_0).lock_state_u()
            &&& container matches Some(c) ==> {
                &&& old_u.container_map[c].lock_state == pre.ctn_mp.spec_index(c).lock_state_u()
                &&& cpu_set_unlocked is Some ==> old_u.container_map[c].cpu_set_lock == pre.cpu_set_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().cpu_set).lock_state_u()
                &&& old_u.container_map[c].killed == post.ctn_mp.spec_index(c).being_killed()
                &&& old_u.container_map[c].depth == post.ctn_mp.spec_index(c).view_rodata().view().depth
                &&& old_u.container_map[c].free_pcids == PcidAllocator::free_pcids(post.pcid_allc_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator).view().ref_counters.view())
            }
            &&& pagetable ==> {
                let table = post.prc_mp.spec_index(process_ptr).view().pagetable;
                &&& old_u.process_map.spec_index(process_ptr).pagetable is Some
                &&& old_u.process_map.spec_index(process_ptr).pagetable->Some_0.lock_state == pre.pt_mp.spec_index(table).lock_state_u()
                &&& old_u.process_map.spec_index(process_ptr).pagetable->Some_0.mapping_4k == post.pt_mp.spec_index(table).view().user_view(LockStateU::Unlocked).mapping_4k
            }
        }),
{
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
    reveal(kernel_k_to_kernel_u); reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
    reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
    reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(kernel_endpoint_nonlock_fields_unchanged);
    let old_u = kernel_k_to_kernel_u(*pre);
    let new_u = kernel_k_to_kernel_u(*post);
    let mode = if write_locked { LockStateU::WriteLocked } else { LockStateU::Unlocked };
    assert_seqs_equal!(new_u.cpu_array == old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, ..old_u.cpu_array[cpu_id as int] }));
    assert_maps_equal!(new_u.container_map, match container {
        Some(c) => old_u.container_map.insert(c, ContainerU {
            lock_state: mode, cpu_set_lock: if cpu_set_unlocked is Some { mode } else { old_u.container_map[c].cpu_set_lock }, ..old_u.container_map[c]
        }),
        None => old_u.container_map,
    }, p => { reveal(container_cpu_set_wf); });
    assert_maps_equal!(new_u.process_map, old_u.process_map.insert(process_ptr, ProcessU {
        lock_state: mode,
        pagetable: if pagetable { Some(PageTableU { lock_state: mode, ..old_u.process_map[process_ptr].pagetable->Some_0 }) } else { old_u.process_map[process_ptr].pagetable },
        ..old_u.process_map[process_ptr]
    }), p => { reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(process_pagetable_match); });
    assert_maps_equal!(new_u.thread_map, old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: mode, ..old_u.thread_map.spec_index(thread_ptr) }), t => {});
    match endpoint_ptr {
        Some(e) => { assert_maps_equal!(new_u.endpoint_map, old_u.endpoint_map.insert(e, EndpointU { lock_state: mode, ..old_u.endpoint_map.spec_index(e) }), p => {}); },
        None => { assert_maps_equal!(new_u.endpoint_map, old_u.endpoint_map, p => {}); },
    }
    if pagetable {
        assert(new_u.process_map[process_ptr].pagetable == Some(PageTableU { lock_state: mode, ..old_u.process_map[process_ptr].pagetable->Some_0 })) by { reveal(process_pagetable_match); };
    }
}

#[verifier::spinoff_prover]
proof fn kernel_ipc_block_fields_implies_u_step(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    waiting_state: ThreadState, payload: IPCPayLoad, regs: Registers, flushed_default_pcid: bool, include_lock_state: bool,
)
    requires
        post.inv(),
        kernel_ipc_block_fields(pre, post, cpu_id, thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, regs, flushed_default_pcid),
    ensures
        kernel_u_ipc_block_changed(kernel_k_user_projection(*pre, include_lock_state), kernel_k_user_projection(*post, include_lock_state),
            cpu_id, thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, regs, flushed_default_pcid),
{
    reveal(kernel_u_ipc_block_changed);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    reveal(kernel_ipc_block_fields); reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(kernel_process_nonlock_fields_unchanged);
    let cpu = pre_u.cpu_array[cpu_id as int];
    let thread = pre_u.thread_map.spec_index(thread_ptr);
    let endpoint = pre_u.endpoint_map.spec_index(endpoint_ptr);
    assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { reveal(IommuRootTable::user_view); };
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU {
        state: CpuState::Idle, current_process: None, current_thread: None, ..cpu
    }));
    assert_maps_equal!(post_u.container_map, pre_u.container_map, c => {});
    assert_maps_equal!(post_u.process_map, pre_u.process_map, p => {
        reveal(process_pagetable_match); reveal(process_iommu_table_match); reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
    });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thread_ptr, ThreadU {
        state: waiting_state, blocking_endpoint_ptr: Some(endpoint_ptr), ipc_payload: payload, trap_frame: Some(regs), ..thread
    }), t => {});
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map.insert(endpoint_ptr, EndpointU {
        queue: endpoint.queue.push(thread_ptr),
        queue_state: if endpoint.queue.len() == 0 {
            match waiting_state { ThreadState::SENDING | ThreadState::CALLING => EndpointState::SEND, _ => EndpointState::RECEIVE }
        } else { endpoint.queue_state },
        ..endpoint
    }), e => {});
}

#[verifier::spinoff_prover]
proof fn kernel_ipc_rendezvous_fields_implies_u_step(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, caller_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, peer_thread_ptr: RwLockThreadPtr, peer_result: RetValueType,
    cpu_transfer: Option<(CpuId, RwLockThreadPtr)>, include_lock_state: bool,
)
    requires
        post.inv(),
        kernel_ipc_rendezvous_fields(pre, post, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)]
            pre.ctn_mp.dom().contains(p) && post.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).locking_thread() == pre.ctn_mp.spec_index(p).locking_thread(),
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
            pre.cpu_set_mp.dom().contains(p) ==> post.cpu_set_mp.spec_index(p).locking_thread() == pre.cpu_set_mp.spec_index(p).locking_thread(),
    ensures
        kernel_u_ipc_rendezvous_changed(kernel_k_user_projection(*pre, include_lock_state), kernel_k_user_projection(*post, include_lock_state),
            cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer),
{
    reveal(kernel_u_ipc_rendezvous_changed);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    reveal(kernel_ipc_rendezvous_fields); reveal(kernel_process_nonlock_fields_unchanged);
    let peer = pre_u.thread_map.spec_index(peer_thread_ptr);
    let endpoint = pre_u.endpoint_map.spec_index(endpoint_ptr);
    let container = pre_u.container_map.spec_index(peer.owning_container);
    assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { reveal(IommuRootTable::user_view); };
    match cpu_transfer {
        Some((transfer_cpu, receiver)) => {
            assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(transfer_cpu as int, CpuU {
                owning_container: pre_u.thread_map.spec_index(receiver).owning_container, ..pre_u.cpu_array[transfer_cpu as int]
            }));
        },
        None => { assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array); },
    }
    assert_maps_equal!(post_u.container_map, pre_u.container_map.insert(peer.owning_container, ContainerU {
        scheduler: container.scheduler.push(peer_thread_ptr), ..container
    }), c => { reveal(container_cpu_set_wf); });
    assert_maps_equal!(post_u.process_map, pre_u.process_map, p => {
        reveal(process_pagetable_match); reveal(process_iommu_table_match); reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
    });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(peer_thread_ptr, ThreadU {
        state: ThreadState::SCHEDULED, blocking_endpoint_ptr: None, ipc_payload: IPCPayLoad::Empty, error_code: Some(peer_result), ..peer
    }), t => {});
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map.insert(endpoint_ptr, EndpointU { queue: endpoint.queue.skip(1), ..endpoint }), e => {});
}

pub proof fn kernel_write_held_context_projection(
    krnl: &KernelK, lctx: &LocalContext, cpu: CpuId, process: RwLockProcessPtr, thread: RwLockThreadPtr, endpoint: Option<RwLockEndpointPtr>,
)
    requires
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread, TypedLockMode::Write),
        endpoint matches Some(e) ==> krnl.ep_mp.dom().contains(e) && typed_lock_map_contains_mode(lctx.endpoint_lock_map(), e, TypedLockMode::Write),
    ensures
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu as int].lock_state is WriteLocked,
        kernel_k_to_kernel_u(*krnl).process_map[process].lock_state is WriteLocked,
        kernel_k_to_kernel_u(*krnl).thread_map[thread].lock_state is WriteLocked,
        endpoint matches Some(e) ==> kernel_k_to_kernel_u(*krnl).endpoint_map.dom().contains(e) && kernel_k_to_kernel_u(*krnl).endpoint_map[e].lock_state is WriteLocked,
        kernel_k_to_kernel_u(*krnl).process_map.dom().contains(process),
        kernel_k_to_kernel_u(*krnl).thread_map.dom().contains(thread),
        kernel_k_to_kernel_u(*krnl).thread_map[thread].owning_container == krnl.thr_mp.spec_index(thread).view().owning_container,
        kernel_k_to_kernel_u(*krnl).thread_map[thread].owning_proc == krnl.thr_mp.spec_index(thread).view().owning_proc,
        kernel_k_to_kernel_u(*krnl).thread_map[thread].syscall_progress == krnl.thr_mp.spec_index(thread).view().syscall_progress.view(),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu as int].current_thread == krnl.cpu_arr.spec_index(cpu).view().view().view().current_thread,
        kernel_k_to_kernel_u(*krnl).process_map[process].pcid == krnl.prc_mp.spec_index(process).view_rodata().view().pcid,
        !krnl.prc_mp.spec_index(process).view().zombie && typed_lock_map_contains_mode(lctx.pagetable_lock_map(), krnl.prc_mp.spec_index(process).view().pagetable, TypedLockMode::Write) ==> {
            &&& kernel_k_to_kernel_u(*krnl).process_map[process].pagetable is Some
            &&& kernel_k_to_kernel_u(*krnl).process_map[process].pagetable->Some_0.lock_state is WriteLocked
        },
        typed_lock_map_contains_mode(lctx.container_lock_map(), krnl.thr_mp.spec_index(thread).view().owning_container, TypedLockMode::Write) ==> {
            &&& kernel_k_to_kernel_u(*krnl).container_map.dom().contains(krnl.thr_mp.spec_index(thread).view().owning_container)
            &&& kernel_k_to_kernel_u(*krnl).container_map[krnl.thr_mp.spec_index(thread).view().owning_container].lock_state is WriteLocked
        },
        ({
            let container = krnl.thr_mp.spec_index(thread).view().owning_container;
            typed_lock_map_contains_mode(lctx.container_lock_map(), container, TypedLockMode::Write)
                && typed_lock_map_contains_mode(lctx.cpu_set_lock_map(), krnl.ctn_mp.spec_index(container).view_rodata().view().cpu_set, TypedLockMode::Write)
                ==> kernel_k_to_kernel_u(*krnl).container_map[container].cpu_set_lock is WriteLocked
        }),
        ({
            let owner = krnl.thr_mp.spec_index(thread).view().owning_proc;
            krnl.prc_mp.dom().contains(owner) && !krnl.prc_mp.spec_index(owner).view().zombie
                && typed_lock_map_contains_mode(lctx.pagetable_lock_map(), krnl.prc_mp.spec_index(owner).view().pagetable, TypedLockMode::Write) ==> {
                &&& kernel_k_to_kernel_u(*krnl).process_map.dom().contains(owner)
                &&& kernel_k_to_kernel_u(*krnl).process_map[owner].pagetable is Some
                &&& kernel_k_to_kernel_u(*krnl).process_map[owner].pagetable->Some_0.lock_state is WriteLocked
            }
        }),
        krnl.prc_mp.spec_index(process).view().iommu_table is None ==> kernel_k_to_kernel_u(*krnl).process_map[process].iommu_table is None,
        krnl.prc_mp.spec_index(process).view().iommu_table matches Some(t) && !krnl.prc_mp.spec_index(process).view().zombie
            && typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), t, TypedLockMode::Write) ==> {
            &&& kernel_k_to_kernel_u(*krnl).process_map[process].iommu_table is Some
            &&& kernel_k_to_kernel_u(*krnl).process_map[process].iommu_table->Some_0.lock_state is WriteLocked
        },
{
    reveal(kernel_k_to_kernel_u); reveal(LockedArray::typed_lock_map_aligned);
    krnl.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), process);
    krnl.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread);
    if let Some(e) = endpoint { krnl.ep_mp.typed_lock_map_aligned_write_at(lctx.endpoint_lock_map(), lctx.thread_id(), e); }
    let pagetable = krnl.prc_mp.spec_index(process).view().pagetable;
    let container = krnl.thr_mp.spec_index(thread).view().owning_container;
    if typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write) { krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable); }
    if typed_lock_map_contains_mode(lctx.container_lock_map(), container, TypedLockMode::Write) { krnl.ctn_mp.typed_lock_map_aligned_write_at(lctx.container_lock_map(), lctx.thread_id(), container); }
    let cpu_set = krnl.ctn_mp.spec_index(container).view_rodata().view().cpu_set;
    if typed_lock_map_contains_mode(lctx.cpu_set_lock_map(), cpu_set, TypedLockMode::Write) { krnl.cpu_set_mp.typed_lock_map_aligned_write_at(lctx.cpu_set_lock_map(), lctx.thread_id(), cpu_set); }
    let owner_table = krnl.prc_mp.spec_index(krnl.thr_mp.spec_index(thread).view().owning_proc).view().pagetable;
    if typed_lock_map_contains_mode(lctx.pagetable_lock_map(), owner_table, TypedLockMode::Write) { krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), owner_table); }
    if let Some(t) = krnl.prc_mp.spec_index(process).view().iommu_table {
        if typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), t, TypedLockMode::Write) { krnl.it_mp.typed_lock_map_aligned_write_at(lctx.iommu_table_lock_map(), lctx.thread_id(), t); }
    }
}

pub proof fn kernel_write_held_pagetable_mode(krnl: &KernelK, lctx: &LocalContext, table: RwLockPageTableRoot)
    requires
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), table, TypedLockMode::Write),
    ensures
        krnl.pt_mp.spec_index(table).locking_thread() is Write,
{
    krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), table);
}

/// Expose concrete entries of the user projection without unfolding every projected map at the caller.
pub proof fn kernel_cpu_thread_projection_at(krnl: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, endpoint_ptr: Option<RwLockEndpointPtr>)
    requires
        index_valid(NUM_CPUS, cpu_id),
        krnl.prc_mp.dom().contains(process_ptr),
        krnl.thr_mp.dom().contains(thread_ptr),
        endpoint_ptr is Some ==> krnl.ep_mp.dom().contains(endpoint_ptr->Some_0),
    ensures
        kernel_k_to_kernel_u(*krnl).cpu_array.len() == NUM_CPUS,
        kernel_k_to_kernel_u(*krnl).container_map.dom() == krnl.ctn_mp.dom(),
        kernel_k_to_kernel_u(*krnl).process_map.dom() == krnl.prc_mp.dom(),
        kernel_k_to_kernel_u(*krnl).thread_map.dom() == krnl.thr_mp.dom(),
        kernel_k_to_kernel_u(*krnl).endpoint_map.dom() == krnl.ep_mp.dom(),
        ({
            let cpu = krnl.cpu_arr.spec_index(cpu_id).value;
            let c = cpu.view().view();
            kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int] == (CpuU {
                lock_state: cpu.lock_state_u(), owning_container: c.owning_container, state: c.state,
                current_process: c.current_process, current_thread: c.current_thread,
            })
        }),
        kernel_k_to_kernel_u(*krnl).process_map.spec_index(process_ptr).lock_state == krnl.prc_mp.spec_index(process_ptr).lock_state_u(),
        kernel_k_to_kernel_u(*krnl).process_map.spec_index(process_ptr).killed == krnl.prc_mp.spec_index(process_ptr).being_killed(),
        ({
            let thread = krnl.thr_mp.spec_index(thread_ptr);
            let t = thread.view();
            kernel_k_to_kernel_u(*krnl).thread_map.spec_index(thread_ptr) == (ThreadU {
                lock_state: thread.lock_state_u(), state: t.state, caller: t.caller, callee: t.callee,
                owning_container: t.owning_container, owning_proc: t.owning_proc,
                quota_4k: t.quota_4k, quota_2m: t.quota_2m, quota_1g: t.quota_1g,
                endpoint_descriptors: t.endpoint_descriptors.view(), blocking_endpoint_ptr: t.blocking_endpoint_ptr,
                ipc_payload: t.ipc_payload, error_code: t.error_code,
                trap_frame: if t.trap_frame.is_some() { Some(*t.trap_frame.get_some_0()) } else { None },
                syscall_progress: t.syscall_progress.view(), killed: thread.being_killed(),
            })
        }),
        endpoint_ptr is Some ==> {
            let e = krnl.ep_mp.spec_index(endpoint_ptr->Some_0);
            kernel_k_to_kernel_u(*krnl).endpoint_map.spec_index(endpoint_ptr->Some_0) == (EndpointU {
                lock_state: e.lock_state_u(), queue: e.view().queue.view(), queue_state: e.view().queue_state,
                owning_threads: e.view().owning_threads.view(), owning_container: e.view().owning_container, killed: e.being_killed(),
            })
        },
        ({
            let c = krnl.thr_mp.spec_index(thread_ptr).view().owning_container;
            krnl.ctn_mp.dom().contains(c)
                ==> kernel_k_to_kernel_u(*krnl).container_map[c].free_pcids == PcidAllocator::free_pcids(krnl.pcid_allc_mp.spec_index(krnl.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator).view().ref_counters.view())
        }),
{
    reveal(kernel_k_to_kernel_u);
}

/// Every pagetable's first user L4 index is the projected user-VA bound.
pub proof fn kernel_l4_end_projection_at(krnl: &KernelK, pagetable_ptr: RwLockPageTableRoot)
    requires
        krnl.inv(),
        krnl.pt_mp.dom().contains(pagetable_ptr),
    ensures
        kernel_k_to_kernel_u(*krnl).kernel_l4_end == krnl.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end,
{ reveal(kernel_k_to_kernel_u); reveal(KernelK::default_pagetable_wf); }

/// A live process's projected page table carries its page table's lock mode, and shows the whole 4K, 2M, and 1G
/// mappings when every leaf is present.
pub proof fn kernel_pagetable_mappings_projection_at(krnl: &KernelK, process: RwLockProcessPtr)
    requires
        krnl.prc_mp.dom().contains(process),
        !krnl.prc_mp.spec_index(process).view().zombie,
        krnl.pt_mp.dom().contains(krnl.prc_mp.spec_index(process).view().pagetable),
    ensures
        ({
            let table = krnl.pt_mp.spec_index(krnl.prc_mp.spec_index(process).view().pagetable);
            let u = kernel_k_to_kernel_u(*krnl).process_map[process].pagetable;
            &&& kernel_k_to_kernel_u(*krnl).process_map.dom().contains(process)
            &&& u is Some
            &&& u->Some_0.lock_state == table.lock_state_u()
            &&& table.view().leaves_present() ==> {
                &&& u->Some_0.mapping_4k == table.view().mapping_4k()
                &&& u->Some_0.mapping_2m == table.view().mapping_2m()
                &&& u->Some_0.mapping_1g == table.view().mapping_1g()
            }
        }),
{
    reveal(kernel_k_to_kernel_u);
    let table = krnl.pt_mp.spec_index(krnl.prc_mp.spec_index(process).view().pagetable).view();
    let u = kernel_k_to_kernel_u(*krnl).process_map[process].pagetable->Some_0;
    if table.leaves_present() {
        assert_maps_equal!(u.mapping_4k, table.mapping_4k(), va => {});
        assert_maps_equal!(u.mapping_2m, table.mapping_2m(), va => {});
        assert_maps_equal!(u.mapping_1g, table.mapping_1g(), va => {});
    }
}

/// Project the cpu and its running thread while the thread records a share, the objects that share
/// names, the source thread's process, and the target page table's write lock.
pub proof fn kernel_share_4k_objects_projection(krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId)
    requires
        typed_lock_maps_aligned(krnl, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread is Some,
        typed_lock_map_contains_mode(lctx.thread_lock_map(), krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0, TypedLockMode::Write),
        krnl.thr_mp.spec_index(krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0).view().syscall_progress.view() matches Some(SyscallProgress::Share4k { .. }),
        krnl.thr_mp.dom().contains(share_4k_objects_k(*krnl, cpu_id).source_thread),
        krnl.thr_mp.dom().contains(share_4k_objects_k(*krnl, cpu_id).quota_thread),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), share_4k_objects_k(*krnl, cpu_id).source_thread, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), share_4k_objects_k(*krnl, cpu_id).quota_thread, TypedLockMode::Write),
        krnl.ctn_mp.dom().contains(share_4k_objects_k(*krnl, cpu_id).target_container),
    ensures
        ({
            let u = kernel_k_to_kernel_u(*krnl);
            let caller = krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0;
            let objects = share_4k_objects_k(*krnl, cpu_id);
            let target = krnl.prc_mp.spec_index(objects.target);
            &&& share_4k_locked(u, cpu_id)
            &&& u.cpu_array[cpu_id as int].current_thread == Some(caller)
            &&& u.thread_map[caller].syscall_progress == krnl.thr_mp.spec_index(caller).view().syscall_progress.view()
            &&& share_4k_objects(u, cpu_id) == objects
            &&& u.container_map.dom().contains(objects.target_container)
            &&& typed_lock_map_contains_mode(lctx.container_lock_map(), objects.target_container, TypedLockMode::Write) ==> u.container_map[objects.target_container].lock_state is WriteLocked
            &&& objects.transfer_source is Some && typed_lock_map_contains_mode(lctx.container_lock_map(), objects.transfer_source->Some_0, TypedLockMode::Write) ==> {
                &&& u.container_map.dom().contains(objects.transfer_source->Some_0)
                &&& u.container_map[objects.transfer_source->Some_0].lock_state is WriteLocked
            }
            &&& u.thread_map.dom().contains(objects.source_thread)
            &&& u.thread_map[objects.source_thread].owning_proc == krnl.thr_mp.spec_index(objects.source_thread).view().owning_proc
            &&& krnl.prc_mp.dom().contains(objects.target) && !target.view().zombie && typed_lock_map_contains_mode(lctx.pagetable_lock_map(), target.view().pagetable, TypedLockMode::Write) ==> {
                &&& u.process_map.dom().contains(objects.target)
                &&& u.process_map[objects.target].pagetable is Some
                &&& u.process_map[objects.target].pagetable->Some_0.lock_state is WriteLocked
            }
        }),
{
    reveal(kernel_k_to_kernel_u); reveal(LockedArray::typed_lock_map_aligned); reveal(share_4k_objects_k);
    let caller = krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0;
    krnl.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), caller);
    krnl.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), share_4k_objects_k(*krnl, cpu_id).source_thread);
    krnl.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), share_4k_objects_k(*krnl, cpu_id).quota_thread);
    let pagetable = krnl.prc_mp.spec_index(share_4k_objects_k(*krnl, cpu_id).target).view().pagetable;
    if typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write) { krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable); }
    let container = share_4k_objects_k(*krnl, cpu_id).target_container;
    if typed_lock_map_contains_mode(lctx.container_lock_map(), container, TypedLockMode::Write) { krnl.ctn_mp.typed_lock_map_aligned_write_at(lctx.container_lock_map(), lctx.thread_id(), container); }
    if let Some(source) = share_4k_objects_k(*krnl, cpu_id).transfer_source {
        if typed_lock_map_contains_mode(lctx.container_lock_map(), source, TypedLockMode::Write) { krnl.ctn_mp.typed_lock_map_aligned_write_at(lctx.container_lock_map(), lctx.thread_id(), source); }
    }
}

/// Project thread publication together with releasing the caller's observable locks.
#[verifier::spinoff_prover]
pub proof fn kernel_new_thread_fields_and_unlocks_implies_u_step(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, new_thread_ptr: RwLockThreadPtr, initial_regs: Registers,
    endpoint_ptr: Option<RwLockEndpointPtr>, release_source_process: Option<RwLockProcessPtr>, staging_progress: Option<SyscallProgress>,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        release_source_process matches Some(source) ==> source != process_ptr && pre.prc_mp.dom().contains(source) && !pre.prc_mp.spec_index(source).view().zombie && !pre.prc_mp.spec_index(process_ptr).view().zombie,
        index_valid(NUM_CPUS, cpu_id),
        kernel_new_thread_fields(pre, post, process_ptr, thread_ptr, container_ptr, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)]
            pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).locking_thread() == pre.ctn_mp.spec_index(p).locking_thread(),
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) ==> if p == process_ptr { post.prc_mp.spec_index(p).locking_thread() is None } else { post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread() },
        forall|p: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(p)]
            pre.thr_mp.dom().contains(p) ==> if p == thread_ptr { post.thr_mp.spec_index(p).locking_thread() is None } else { post.thr_mp.spec_index(p).locking_thread() == pre.thr_mp.spec_index(p).locking_thread() },
        forall|p: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(p)]
            pre.ep_mp.dom().contains(p) ==> if endpoint_ptr == Some(p) { post.ep_mp.spec_index(p).locking_thread() is None } else { post.ep_mp.spec_index(p).locking_thread() == pre.ep_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) ==> if release_source_process is Some && (p == pre.prc_mp.spec_index(process_ptr).view().pagetable || p == pre.prc_mp.spec_index(release_source_process->Some_0).view().pagetable) { post.pt_mp.spec_index(p).locking_thread() is None } else { post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
            pre.it_mp.dom().contains(p) ==> if release_source_process is Some && pre.prc_mp.spec_index(process_ptr).view().iommu_table == Some(p) { post.it_mp.spec_index(p).locking_thread() is None } else { post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread() },
        forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> if i == cpu_id { post.cpu_arr.spec_index(i).value.locking_thread() is None } else { post.cpu_arr.spec_index(i).value.locking_thread() == pre.cpu_arr.spec_index(i).value.locking_thread() },
        post.thr_mp.spec_index(new_thread_ptr).locking_thread() is None,
    ensures
        kernel_k_to_kernel_u(*post).process_map.spec_index(process_ptr).owned_threads.last() == new_thread_ptr,
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let mode = LockStateU::Unlocked;
            kernel_u_new_thread_changed(KernelU {
                cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, ..old_u.cpu_array[cpu_id as int] }),
                process_map: match release_source_process {
                    Some(source) => old_u.process_map.insert(source, ProcessU {
                        pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[source].pagetable->Some_0 }), ..old_u.process_map[source]
                    }).insert(process_ptr, ProcessU {
                        lock_state: mode, pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[process_ptr].pagetable->Some_0 }),
                        iommu_table: match old_u.process_map[process_ptr].iommu_table { Some(t) => Some(PageTableU { lock_state: mode, ..t }), None => None },
                        ..old_u.process_map[process_ptr]
                    }),
                    None => old_u.process_map.insert(process_ptr, ProcessU { lock_state: mode, ..old_u.process_map[process_ptr] }),
                },
                thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: mode, ..old_u.thread_map.spec_index(thread_ptr) }),
                endpoint_map: match endpoint_ptr {
                    Some(e) => old_u.endpoint_map.insert(e, EndpointU { lock_state: mode, ..old_u.endpoint_map.spec_index(e) }),
                    None => old_u.endpoint_map,
                },
                ..old_u
            }, kernel_k_to_kernel_u(*post), process_ptr, thread_ptr, container_ptr, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress)
        }),
{
    reveal(kernel_k_to_kernel_u);
    let old_u = kernel_k_to_kernel_u(*pre);
    let mode = LockStateU::Unlocked;
    let pre_u = KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, ..old_u.cpu_array[cpu_id as int] }),
        process_map: match release_source_process {
            Some(source) => old_u.process_map.insert(source, ProcessU {
                pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[source].pagetable->Some_0 }), ..old_u.process_map[source]
            }).insert(process_ptr, ProcessU {
                lock_state: mode, pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[process_ptr].pagetable->Some_0 }),
                iommu_table: match old_u.process_map[process_ptr].iommu_table { Some(t) => Some(PageTableU { lock_state: mode, ..t }), None => None },
                ..old_u.process_map[process_ptr]
            }),
            None => old_u.process_map.insert(process_ptr, ProcessU { lock_state: mode, ..old_u.process_map[process_ptr] }),
        },
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: mode, ..old_u.thread_map.spec_index(thread_ptr) }),
        endpoint_map: match endpoint_ptr {
            Some(e) => old_u.endpoint_map.insert(e, EndpointU { lock_state: mode, ..old_u.endpoint_map.spec_index(e) }),
            None => old_u.endpoint_map,
        },
        ..old_u
    };
    let post_u = kernel_k_to_kernel_u(*post);
    assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { reveal(kernel_new_thread_fields); reveal(IommuRootTable::user_view); };
    assert(post_u.process_map.spec_index(process_ptr).owned_threads.last() == new_thread_ptr
        && kernel_u_new_thread_changed(pre_u, post_u, process_ptr, thread_ptr, container_ptr, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress)) by {
        kernel_new_thread_fields_and_unlocks_implies_u_cpu_array(pre, post, cpu_id, process_ptr, thread_ptr, container_ptr, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress);
        kernel_new_thread_fields_and_unlocks_implies_u_thread_map(pre, post, process_ptr, thread_ptr, container_ptr, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress);
        kernel_new_thread_fields_and_unlocks_implies_u_endpoint_map(pre, post, process_ptr, thread_ptr, container_ptr, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress);
        kernel_new_thread_fields_and_unlocks_implies_u_container_map(pre, post, process_ptr, thread_ptr, container_ptr, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress, None);
        kernel_new_thread_fields_and_unlocks_implies_u_process_map(pre, post, process_ptr, thread_ptr, container_ptr, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress, release_source_process);
        reveal(kernel_new_thread_fields); reveal(kernel_u_new_thread_changed);
        assert_seqs_equal!(post_u.thread_map.spec_index(new_thread_ptr).endpoint_descriptors ==
            Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat, |i: int| if i == 0 { endpoint_ptr } else { None }));
    };
}

#[verifier::spinoff_prover]
pub proof fn kernel_new_thread_fields_and_parent_unlocks_implies_u_step(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    new_thread_ptr: RwLockThreadPtr, initial_regs: Registers, release_source_process: RwLockProcessPtr, release_source_container: RwLockContainerPtr,
    staging_progress: Option<SyscallProgress>,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        pre.prc_mp.spec_index(process_ptr).view().iommu_table is None,
        release_source_container != container_ptr && pre.ctn_mp.dom().contains(release_source_container),
        release_source_process != process_ptr && pre.prc_mp.dom().contains(release_source_process) && !pre.prc_mp.spec_index(release_source_process).view().zombie && !pre.prc_mp.spec_index(process_ptr).view().zombie,
        index_valid(NUM_CPUS, cpu_id),
        kernel_new_thread_fields(pre, post, process_ptr, thread_ptr, container_ptr, new_thread_ptr, initial_regs, None, staging_progress),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)]
            pre.ctn_mp.dom().contains(p) ==> if p == container_ptr || release_source_container == p { post.ctn_mp.spec_index(p).locking_thread() is None } else { post.ctn_mp.spec_index(p).locking_thread() == pre.ctn_mp.spec_index(p).locking_thread() },
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) ==> if p == process_ptr || release_source_process == p { post.prc_mp.spec_index(p).locking_thread() is None } else { post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread() },
        forall|p: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(p)]
            pre.thr_mp.dom().contains(p) ==> if p == thread_ptr { post.thr_mp.spec_index(p).locking_thread() is None } else { post.thr_mp.spec_index(p).locking_thread() == pre.thr_mp.spec_index(p).locking_thread() },
        forall|p: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(p)]
            pre.ep_mp.dom().contains(p) ==> post.ep_mp.spec_index(p).locking_thread() == pre.ep_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) ==> if (p == pre.prc_mp.spec_index(process_ptr).view().pagetable || p == pre.prc_mp.spec_index(release_source_process).view().pagetable) { post.pt_mp.spec_index(p).locking_thread() is None } else { post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
            pre.it_mp.dom().contains(p) ==> post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread(),
        forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> if i == cpu_id { post.cpu_arr.spec_index(i).value.locking_thread() is None } else { post.cpu_arr.spec_index(i).value.locking_thread() == pre.cpu_arr.spec_index(i).value.locking_thread() },
        post.thr_mp.spec_index(new_thread_ptr).locking_thread() is None,
    ensures
        kernel_k_to_kernel_u(*pre).process_map.spec_index(process_ptr).iommu_table is None,
        kernel_k_to_kernel_u(*post).process_map.spec_index(process_ptr).owned_threads.last() == new_thread_ptr,
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let mode = LockStateU::Unlocked;
            kernel_u_new_thread_changed(KernelU {
                cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, ..old_u.cpu_array[cpu_id as int] }),
                container_map: old_u.container_map.insert(release_source_container, ContainerU { lock_state: mode, ..old_u.container_map[release_source_container] })
                    .insert(container_ptr, ContainerU { lock_state: mode, ..old_u.container_map[container_ptr] }),
                process_map: old_u.process_map.insert(release_source_process, ProcessU {
                    lock_state: mode,
                    pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[release_source_process].pagetable->Some_0 }), ..old_u.process_map[release_source_process]
                }).insert(process_ptr, ProcessU {
                    lock_state: mode, pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[process_ptr].pagetable->Some_0 }),
                    iommu_table: None,
                    ..old_u.process_map[process_ptr]
                }),
                thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: mode, ..old_u.thread_map.spec_index(thread_ptr) }),
                endpoint_map: old_u.endpoint_map,
                ..old_u
            }, kernel_k_to_kernel_u(*post), process_ptr, thread_ptr, container_ptr, new_thread_ptr, initial_regs, None, staging_progress)
        }),
{
    reveal(kernel_new_thread_fields); reveal(kernel_k_to_kernel_u);
    let old_u = kernel_k_to_kernel_u(*pre);
    let mode = LockStateU::Unlocked;
    let pre_u = KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, ..old_u.cpu_array[cpu_id as int] }),
        container_map: old_u.container_map.insert(release_source_container, ContainerU { lock_state: mode, ..old_u.container_map[release_source_container] })
            .insert(container_ptr, ContainerU { lock_state: mode, ..old_u.container_map[container_ptr] }),
        process_map: old_u.process_map.insert(release_source_process, ProcessU {
            lock_state: mode,
            pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[release_source_process].pagetable->Some_0 }), ..old_u.process_map[release_source_process]
        }).insert(process_ptr, ProcessU {
            lock_state: mode, pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[process_ptr].pagetable->Some_0 }),
            iommu_table: None,
            ..old_u.process_map[process_ptr]
        }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: mode, ..old_u.thread_map.spec_index(thread_ptr) }),
        endpoint_map: old_u.endpoint_map,
        ..old_u
    };
    let post_u = kernel_k_to_kernel_u(*post);
    assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { reveal(IommuRootTable::user_view); };
    assert(post_u.process_map.spec_index(process_ptr).owned_threads.last() == new_thread_ptr && old_u.process_map[process_ptr].iommu_table is None
        && kernel_u_new_thread_changed(pre_u, post_u, process_ptr, thread_ptr, container_ptr, new_thread_ptr, initial_regs, None, staging_progress)) by {
        kernel_new_thread_fields_and_unlocks_implies_u_cpu_array(pre, post, cpu_id, process_ptr, thread_ptr, container_ptr, new_thread_ptr, initial_regs, None, staging_progress);
        kernel_new_thread_fields_and_unlocks_implies_u_thread_map(pre, post, process_ptr, thread_ptr, container_ptr, new_thread_ptr, initial_regs, None, staging_progress);
        kernel_new_thread_fields_and_unlocks_implies_u_endpoint_map(pre, post, process_ptr, thread_ptr, container_ptr, new_thread_ptr, initial_regs, None, staging_progress);
        kernel_new_thread_fields_and_unlocks_implies_u_container_map(pre, post, process_ptr, thread_ptr, container_ptr, new_thread_ptr, initial_regs, None, staging_progress, Some(release_source_container));
        kernel_new_thread_fields_and_parent_unlocks_implies_u_process_map(pre, post, process_ptr, thread_ptr, container_ptr, new_thread_ptr, initial_regs, staging_progress, release_source_process);
        reveal(kernel_u_new_thread_changed);
        assert_seqs_equal!(post_u.thread_map.spec_index(new_thread_ptr).endpoint_descriptors == Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat, |i: int| None));
    };
}

/// Thread publication with the caller's cpu released projects to the cpu array with only that cpu unlocked.
#[verifier::spinoff_prover]
pub proof fn kernel_new_thread_fields_and_unlocks_implies_u_cpu_array(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    new_thread_ptr: RwLockThreadPtr, initial_regs: Registers, endpoint_ptr: Option<RwLockEndpointPtr>, staging_progress: Option<SyscallProgress>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        kernel_new_thread_fields(pre, post, process_ptr, thread_ptr, container_ptr, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress),
        forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> if i == cpu_id { post.cpu_arr.spec_index(i).value.locking_thread() is None } else { post.cpu_arr.spec_index(i).value.locking_thread() == pre.cpu_arr.spec_index(i).value.locking_thread() },
    ensures
        kernel_k_to_kernel_u(*post).cpu_array == kernel_k_to_kernel_u(*pre).cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..kernel_k_to_kernel_u(*pre).cpu_array[cpu_id as int] }),
{
    reveal(kernel_k_to_kernel_u);
    let old_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    assert_seqs_equal!(post_u.cpu_array == old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..old_u.cpu_array[cpu_id as int] }), i => { reveal(kernel_new_thread_fields); });
}

/// Thread publication with the caller's thread released projects to the unlocked staging thread paying one quota and
/// recording `staging_progress`, plus the new thread.
#[verifier::spinoff_prover]
pub proof fn kernel_new_thread_fields_and_unlocks_implies_u_thread_map(
    pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    new_thread_ptr: RwLockThreadPtr, initial_regs: Registers, endpoint_ptr: Option<RwLockEndpointPtr>, staging_progress: Option<SyscallProgress>,
)
    requires
        kernel_new_thread_fields(pre, post, process_ptr, thread_ptr, container_ptr, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress),
        forall|p: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(p)]
            pre.thr_mp.dom().contains(p) ==> if p == thread_ptr { post.thr_mp.spec_index(p).locking_thread() is None } else { post.thr_mp.spec_index(p).locking_thread() == pre.thr_mp.spec_index(p).locking_thread() },
    ensures
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let unlocked = old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, ..old_u.thread_map.spec_index(thread_ptr) });
            let staging = unlocked.spec_index(thread_ptr);
            kernel_k_to_kernel_u(*post).thread_map == unlocked.insert(thread_ptr, ThreadU {
                quota_4k: (staging.quota_4k as int - 1) as usize, syscall_progress: staging_progress, ..staging
            }).insert(new_thread_ptr, kernel_k_to_kernel_u(*post).thread_map.spec_index(new_thread_ptr))
        }),
{
    reveal(kernel_k_to_kernel_u);
    let old_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let unlocked = old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, ..old_u.thread_map.spec_index(thread_ptr) });
    let staging = unlocked.spec_index(thread_ptr);
    assert_maps_equal!(post_u.thread_map, unlocked.insert(thread_ptr, ThreadU {
        quota_4k: (staging.quota_4k as int - 1) as usize, syscall_progress: staging_progress, ..staging
    }).insert(new_thread_ptr, post_u.thread_map.spec_index(new_thread_ptr)), t => { reveal(kernel_new_thread_fields); });
}

/// Thread publication with its initial endpoint released projects to that endpoint, unlocked, owning the new thread's
/// first descriptor; without one the endpoint map is unchanged.
#[verifier::spinoff_prover]
pub proof fn kernel_new_thread_fields_and_unlocks_implies_u_endpoint_map(
    pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    new_thread_ptr: RwLockThreadPtr, initial_regs: Registers, endpoint_ptr: Option<RwLockEndpointPtr>, staging_progress: Option<SyscallProgress>,
)
    requires
        kernel_new_thread_fields(pre, post, process_ptr, thread_ptr, container_ptr, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress),
        forall|p: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(p)]
            pre.ep_mp.dom().contains(p) ==> if endpoint_ptr == Some(p) { post.ep_mp.spec_index(p).locking_thread() is None } else { post.ep_mp.spec_index(p).locking_thread() == pre.ep_mp.spec_index(p).locking_thread() },
    ensures
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let unlocked = match endpoint_ptr {
                Some(e) => old_u.endpoint_map.insert(e, EndpointU { lock_state: LockStateU::Unlocked, ..old_u.endpoint_map.spec_index(e) }),
                None => old_u.endpoint_map,
            };
            match endpoint_ptr {
                Some(e) => kernel_k_to_kernel_u(*post).endpoint_map == unlocked.insert(e, EndpointU {
                    owning_threads: unlocked.spec_index(e).owning_threads.insert((new_thread_ptr, 0usize)), ..unlocked.spec_index(e)
                }),
                None => kernel_k_to_kernel_u(*post).endpoint_map == unlocked,
            }
        }),
{
    reveal(kernel_k_to_kernel_u);
    let old_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    match endpoint_ptr {
        Some(e) => {
            let unlocked = old_u.endpoint_map.insert(e, EndpointU { lock_state: LockStateU::Unlocked, ..old_u.endpoint_map.spec_index(e) });
            assert_maps_equal!(post_u.endpoint_map, unlocked.insert(e, EndpointU {
                owning_threads: unlocked.spec_index(e).owning_threads.insert((new_thread_ptr, 0usize)), ..unlocked.spec_index(e)
            }), ptr => { reveal(kernel_new_thread_fields); });
        },
        None => { assert_maps_equal!(post_u.endpoint_map, old_u.endpoint_map, ptr => { reveal(kernel_new_thread_fields); }); },
    }
}

/// Thread publication projects to its container owning and scheduling the new thread; with a released source
/// container, that container and the new thread's container are both unlocked.
#[verifier::spinoff_prover]
pub proof fn kernel_new_thread_fields_and_unlocks_implies_u_container_map(
    pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    new_thread_ptr: RwLockThreadPtr, initial_regs: Registers, endpoint_ptr: Option<RwLockEndpointPtr>, staging_progress: Option<SyscallProgress>,
    released_container: Option<RwLockContainerPtr>,
)
    requires
        kernel_new_thread_fields(pre, post, process_ptr, thread_ptr, container_ptr, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress),
        released_container matches Some(source) ==> pre.ctn_mp.dom().contains(source),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)]
            pre.ctn_mp.dom().contains(p) ==> if released_container is Some && (p == container_ptr || released_container == Some(p)) { post.ctn_mp.spec_index(p).locking_thread() is None }
                else { post.ctn_mp.spec_index(p).locking_thread() == pre.ctn_mp.spec_index(p).locking_thread() },
    ensures
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let unlocked = match released_container {
                Some(source) => old_u.container_map.insert(source, ContainerU { lock_state: LockStateU::Unlocked, ..old_u.container_map[source] })
                    .insert(container_ptr, ContainerU { lock_state: LockStateU::Unlocked, ..old_u.container_map[container_ptr] }),
                None => old_u.container_map,
            };
            kernel_k_to_kernel_u(*post).container_map == unlocked.insert(container_ptr, ContainerU {
                owned_threads: unlocked.spec_index(container_ptr).owned_threads.insert(new_thread_ptr),
                scheduler: unlocked.spec_index(container_ptr).scheduler.push(new_thread_ptr), ..unlocked.spec_index(container_ptr)
            })
        }),
{
    reveal(kernel_k_to_kernel_u);
    let old_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let unlocked = match released_container {
        Some(source) => old_u.container_map.insert(source, ContainerU { lock_state: LockStateU::Unlocked, ..old_u.container_map[source] })
            .insert(container_ptr, ContainerU { lock_state: LockStateU::Unlocked, ..old_u.container_map[container_ptr] }),
        None => old_u.container_map,
    };
    assert_maps_equal!(post_u.container_map, unlocked.insert(container_ptr, ContainerU {
        owned_threads: unlocked.spec_index(container_ptr).owned_threads.insert(new_thread_ptr),
        scheduler: unlocked.spec_index(container_ptr).scheduler.push(new_thread_ptr), ..unlocked.spec_index(container_ptr)
    }), c => { reveal(kernel_new_thread_fields); });
}

/// Thread publication with its process released projects to that process recording the new thread; with a released
/// source process, both page tables and the process's iommu table are unlocked too.
#[verifier::spinoff_prover]
pub proof fn kernel_new_thread_fields_and_unlocks_implies_u_process_map(
    pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    new_thread_ptr: RwLockThreadPtr, initial_regs: Registers, endpoint_ptr: Option<RwLockEndpointPtr>, staging_progress: Option<SyscallProgress>,
    release_source_process: Option<RwLockProcessPtr>,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        release_source_process matches Some(source) ==> source != process_ptr && pre.prc_mp.dom().contains(source) && !pre.prc_mp.spec_index(source).view().zombie && !pre.prc_mp.spec_index(process_ptr).view().zombie,
        kernel_new_thread_fields(pre, post, process_ptr, thread_ptr, container_ptr, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress),
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) ==> if p == process_ptr { post.prc_mp.spec_index(p).locking_thread() is None } else { post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) ==> if release_source_process is Some && (p == pre.prc_mp.spec_index(process_ptr).view().pagetable || p == pre.prc_mp.spec_index(release_source_process->Some_0).view().pagetable) { post.pt_mp.spec_index(p).locking_thread() is None } else { post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
            pre.it_mp.dom().contains(p) ==> if release_source_process is Some && pre.prc_mp.spec_index(process_ptr).view().iommu_table == Some(p) { post.it_mp.spec_index(p).locking_thread() is None } else { post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread() },
    ensures
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let mode = LockStateU::Unlocked;
            let unlocked = match release_source_process {
                Some(source) => old_u.process_map.insert(source, ProcessU {
                    pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[source].pagetable->Some_0 }), ..old_u.process_map[source]
                }).insert(process_ptr, ProcessU {
                    lock_state: mode, pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[process_ptr].pagetable->Some_0 }),
                    iommu_table: match old_u.process_map[process_ptr].iommu_table { Some(t) => Some(PageTableU { lock_state: mode, ..t }), None => None },
                    ..old_u.process_map[process_ptr]
                }),
                None => old_u.process_map.insert(process_ptr, ProcessU { lock_state: mode, ..old_u.process_map[process_ptr] }),
            };
            let process = unlocked.spec_index(process_ptr);
            kernel_k_to_kernel_u(*post).process_map == unlocked.insert(process_ptr, ProcessU { owned_threads: process.owned_threads.push(new_thread_ptr), ..process })
        }),
{
    reveal(kernel_k_to_kernel_u);
    let old_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let mode = LockStateU::Unlocked;
    let unlocked = match release_source_process {
        Some(source) => old_u.process_map.insert(source, ProcessU {
            pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[source].pagetable->Some_0 }), ..old_u.process_map[source]
        }).insert(process_ptr, ProcessU {
            lock_state: mode, pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[process_ptr].pagetable->Some_0 }),
            iommu_table: match old_u.process_map[process_ptr].iommu_table { Some(t) => Some(PageTableU { lock_state: mode, ..t }), None => None },
            ..old_u.process_map[process_ptr]
        }),
        None => old_u.process_map.insert(process_ptr, ProcessU { lock_state: mode, ..old_u.process_map[process_ptr] }),
    };
    let process = unlocked.spec_index(process_ptr);
    assert_maps_equal!(post_u.process_map, unlocked.insert(process_ptr, ProcessU { owned_threads: process.owned_threads.push(new_thread_ptr), ..process }), p => {
        reveal(kernel_new_thread_fields); reveal(process_pagetable_match); reveal(process_iommu_table_match);
        assert(post.prc_mp.spec_index(process_ptr).view().pagetable == pre.prc_mp.spec_index(process_ptr).view().pagetable) by { reveal(kernel_new_thread_fields); };
        if let Some(source) = release_source_process {
            assert(post.prc_mp.spec_index(source).view().pagetable == pre.prc_mp.spec_index(source).view().pagetable) by { reveal(kernel_new_thread_fields); };
        }
    });
}

/// Thread publication into a child process projects to the child recording the new thread, with the child and the
/// parent process and both of their page tables unlocked.
#[verifier::spinoff_prover]
pub proof fn kernel_new_thread_fields_and_parent_unlocks_implies_u_process_map(
    pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    new_thread_ptr: RwLockThreadPtr, initial_regs: Registers, staging_progress: Option<SyscallProgress>, release_source_process: RwLockProcessPtr,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        pre.prc_mp.spec_index(process_ptr).view().iommu_table is None,
        release_source_process != process_ptr && pre.prc_mp.dom().contains(release_source_process) && !pre.prc_mp.spec_index(release_source_process).view().zombie && !pre.prc_mp.spec_index(process_ptr).view().zombie,
        kernel_new_thread_fields(pre, post, process_ptr, thread_ptr, container_ptr, new_thread_ptr, initial_regs, None, staging_progress),
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) ==> if p == process_ptr || release_source_process == p { post.prc_mp.spec_index(p).locking_thread() is None } else { post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) ==> if (p == pre.prc_mp.spec_index(process_ptr).view().pagetable || p == pre.prc_mp.spec_index(release_source_process).view().pagetable) { post.pt_mp.spec_index(p).locking_thread() is None } else { post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
            pre.it_mp.dom().contains(p) ==> post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread(),
    ensures
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let mode = LockStateU::Unlocked;
            let unlocked = old_u.process_map.insert(release_source_process, ProcessU {
                lock_state: mode,
                pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[release_source_process].pagetable->Some_0 }), ..old_u.process_map[release_source_process]
            }).insert(process_ptr, ProcessU {
                lock_state: mode, pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[process_ptr].pagetable->Some_0 }),
                iommu_table: None,
                ..old_u.process_map[process_ptr]
            });
            let process = unlocked.spec_index(process_ptr);
            kernel_k_to_kernel_u(*post).process_map == unlocked.insert(process_ptr, ProcessU { owned_threads: process.owned_threads.push(new_thread_ptr), ..process })
        }),
{
    reveal(kernel_new_thread_fields); reveal(kernel_k_to_kernel_u);
    let old_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let mode = LockStateU::Unlocked;
    let unlocked = old_u.process_map.insert(release_source_process, ProcessU {
        lock_state: mode,
        pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[release_source_process].pagetable->Some_0 }), ..old_u.process_map[release_source_process]
    }).insert(process_ptr, ProcessU {
        lock_state: mode, pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[process_ptr].pagetable->Some_0 }),
        iommu_table: None,
        ..old_u.process_map[process_ptr]
    });
    let process = unlocked.spec_index(process_ptr);
    assert_maps_equal!(post_u.process_map, unlocked.insert(process_ptr, ProcessU { owned_threads: process.owned_threads.push(new_thread_ptr), ..process }), p => {
        reveal(process_pagetable_match); reveal(process_iommu_table_match);
        assert(post.prc_mp.spec_index(process_ptr).view().pagetable == pre.prc_mp.spec_index(process_ptr).view().pagetable) by { reveal(kernel_new_thread_fields); };
        assert(post.prc_mp.spec_index(release_source_process).view().pagetable == pre.prc_mp.spec_index(release_source_process).view().pagetable) by { reveal(kernel_new_thread_fields); };
    });
}

/// Changing one existing thread's permission moves only that entry of the non-lock thread projection.
pub proof fn kernel_thread_unchanged_except_implies_nonlock_u_thread_map_insert(pre: &KernelK, post: &KernelK, thread_ptr: RwLockThreadPtr)
    requires
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
    ensures
        kernel_k_to_nonlock_kernel_u(*post).thread_map.dom().contains(thread_ptr),
        kernel_k_to_nonlock_kernel_u(*post).thread_map == kernel_k_to_nonlock_kernel_u(*pre).thread_map.insert(thread_ptr, kernel_k_to_nonlock_kernel_u(*post).thread_map.spec_index(thread_ptr)),
{
    reveal(kernel_k_to_nonlock_kernel_u);
    let pre_u = kernel_k_to_nonlock_kernel_u(*pre);
    let post_u = kernel_k_to_nonlock_kernel_u(*post);
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thread_ptr, post_u.thread_map.spec_index(thread_ptr)), t => {});
}

/// The complete create-process K relation projects to the create-process non-lock user step.
pub proof fn kernel_create_process_framing_implies_nonlock_u_step(
    pre: KernelK, post: KernelK, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr, parent_ptr: RwLockProcessPtr,
    staging_thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        !pre.prc_mp.dom().contains(process_page_ptr),
        pre.prc_mp.dom().contains(parent_ptr),
        process_pagetable_match(post.prc_mp, post.pt_mp),
        create_process_from_staged_pages_kernel_state_framing(
            pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid,
        ),
    ensures
        kernel_u_create_process_changed(kernel_k_to_nonlock_kernel_u(pre), kernel_k_to_nonlock_kernel_u(post), parent_ptr, process_page_ptr, staging_thread_ptr),
        kernel_k_to_nonlock_kernel_u(post) != kernel_k_to_nonlock_kernel_u(pre),
{
    reveal(create_process_from_staged_pages_kernel_state_framing); reveal(kernel_u_create_process_changed); reveal(kernel_k_to_nonlock_kernel_u); reveal(process_pagetable_match);
    let pre_u = kernel_k_to_nonlock_kernel_u(pre);
    let post_u = kernel_k_to_nonlock_kernel_u(post);
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(staging_thread_ptr, post_u.thread_map.spec_index(staging_thread_ptr)), t => {});
}

/// The complete create-process-with-IOMMU K relation projects to its non-lock user step.
pub proof fn kernel_create_process_with_iommu_framing_implies_nonlock_u_step(
    pre: KernelK, post: KernelK, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr,
    iommu_table_page_ptr: PagePtr, iommu_l4_page_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        !pre.prc_mp.dom().contains(process_page_ptr),
        pre.prc_mp.dom().contains(parent_ptr),
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        create_process_with_iommu_from_staged_pages_kernel_state_framing(
            pre, post, process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr, staging_thread_ptr,
            container_ptr, pcid_allocator_ptr, pcid,
        ),
    ensures
        kernel_u_create_process_with_iommu_changed(kernel_k_to_nonlock_kernel_u(pre), kernel_k_to_nonlock_kernel_u(post), parent_ptr, process_page_ptr, staging_thread_ptr),
        kernel_k_to_nonlock_kernel_u(post) != kernel_k_to_nonlock_kernel_u(pre),
{
    reveal(create_process_with_iommu_from_staged_pages_kernel_state_framing);
    reveal(kernel_u_create_process_with_iommu_changed); reveal(kernel_k_to_nonlock_kernel_u); reveal(process_pagetable_match); reveal(process_iommu_table_match);
    let pre_u = kernel_k_to_nonlock_kernel_u(pre);
    let post_u = kernel_k_to_nonlock_kernel_u(post);
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(staging_thread_ptr, post_u.thread_map.spec_index(staging_thread_ptr)), t => {});
}

#[verifier::spinoff_prover]
proof fn kernel_new_thread_fields_implies_u_step(
    pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    new_thread_ptr: RwLockThreadPtr, initial_regs: Registers, initial_endpoint: Option<RwLockEndpointPtr>, staging_progress: Option<SyscallProgress>,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        kernel_new_thread_fields(pre, post, process_ptr, staging_thread_ptr, container_ptr, new_thread_ptr, initial_regs, initial_endpoint, staging_progress),
    ensures
        kernel_u_new_thread_changed(kernel_k_to_nonlock_kernel_u(*pre), kernel_k_to_nonlock_kernel_u(*post),
            process_ptr, staging_thread_ptr, container_ptr, new_thread_ptr, initial_regs, initial_endpoint, staging_progress),
{
    reveal(kernel_new_thread_fields); reveal(kernel_k_to_nonlock_kernel_u); reveal(kernel_u_new_thread_changed);
    let pre_u = kernel_k_to_nonlock_kernel_u(*pre);
    let post_u = kernel_k_to_nonlock_kernel_u(*post);
    assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { reveal(IommuRootTable::user_view); };
    match initial_endpoint {
        Some(e) => {
            assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map.insert(e, EndpointU {
                owning_threads: pre_u.endpoint_map.spec_index(e).owning_threads.insert((new_thread_ptr, 0usize)),
                ..pre_u.endpoint_map.spec_index(e)
            }), ptr => {});
        },
        None => { assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, ptr => {}); },
    }
    let staging = pre_u.thread_map.spec_index(staging_thread_ptr);
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array);
    assert_maps_equal!(post_u.container_map, pre_u.container_map.insert(container_ptr, ContainerU {
        owned_threads: pre_u.container_map.spec_index(container_ptr).owned_threads.insert(new_thread_ptr),
        scheduler: pre_u.container_map.spec_index(container_ptr).scheduler.push(new_thread_ptr),
        ..pre_u.container_map.spec_index(container_ptr)
    }), c => {});
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(staging_thread_ptr, ThreadU {
        quota_4k: (staging.quota_4k as int - 1) as usize, syscall_progress: staging_progress, ..staging
    }).insert(new_thread_ptr, post_u.thread_map.spec_index(new_thread_ptr)), t => {});
    assert_seqs_equal!(post_u.thread_map.spec_index(new_thread_ptr).endpoint_descriptors ==
        Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat, |i: int| if i == 0 { initial_endpoint } else { None }));
    let process = pre_u.process_map.spec_index(process_ptr);
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(process_ptr, ProcessU {
        owned_threads: process.owned_threads.push(new_thread_ptr), ..process
    }), p => {
        reveal(process_pagetable_match); reveal(process_iommu_table_match);
    });
}

proof fn kernel_thread_state_changed_implies_u_neq(pre: &KernelK, post: &KernelK, thread_ptr: RwLockThreadPtr)
    requires kernel_thread_state_changed(pre, post, thread_ptr),
    ensures kernel_k_to_nonlock_kernel_u(*pre) != kernel_k_to_nonlock_kernel_u(*post),
{
    assert(kernel_k_to_nonlock_kernel_u(*pre).thread_map.spec_index(thread_ptr).state != kernel_k_to_nonlock_kernel_u(*post).thread_map.spec_index(thread_ptr).state) by { reveal(kernel_thread_state_changed); reveal(kernel_k_to_nonlock_kernel_u); };
}

#[verifier::spinoff_prover]
proof fn kernel_thread_quota_4k_changed_implies_u_step(pre: &KernelK, post: &KernelK, thread_ptr: RwLockThreadPtr, delta: int)
    requires
        delta != 0,
        kernel_thread_quota_4k_changed(pre, post, thread_ptr, delta),
    ensures
        kernel_k_to_nonlock_kernel_u(*post).thread_map.spec_index(thread_ptr) == (ThreadU {
            quota_4k: (kernel_k_to_nonlock_kernel_u(*pre).thread_map.spec_index(thread_ptr).quota_4k as int + delta) as usize,
            syscall_progress: kernel_k_to_nonlock_kernel_u(*post).thread_map.spec_index(thread_ptr).syscall_progress,
            ..kernel_k_to_nonlock_kernel_u(*pre).thread_map.spec_index(thread_ptr)
        }),
        kernel_k_to_nonlock_kernel_u(*pre) != kernel_k_to_nonlock_kernel_u(*post),
{
    assert(kernel_k_to_nonlock_kernel_u(*post).thread_map.spec_index(thread_ptr) == (ThreadU {
        quota_4k: (kernel_k_to_nonlock_kernel_u(*pre).thread_map.spec_index(thread_ptr).quota_4k as int + delta) as usize,
        syscall_progress: kernel_k_to_nonlock_kernel_u(*post).thread_map.spec_index(thread_ptr).syscall_progress,
        ..kernel_k_to_nonlock_kernel_u(*pre).thread_map.spec_index(thread_ptr)
    })) by { reveal(kernel_thread_quota_4k_changed); reveal(kernel_k_to_nonlock_kernel_u); };
    assert(kernel_k_to_nonlock_kernel_u(*pre).thread_map.spec_index(thread_ptr).quota_4k != kernel_k_to_nonlock_kernel_u(*post).thread_map.spec_index(thread_ptr).quota_4k) by { reveal(kernel_thread_quota_4k_changed); reveal(kernel_k_to_nonlock_kernel_u); };
    assert(kernel_k_to_kernel_u(*pre).thread_map.spec_index(thread_ptr).quota_4k != kernel_k_to_kernel_u(*post).thread_map.spec_index(thread_ptr).quota_4k) by { reveal(kernel_thread_quota_4k_changed); reveal(kernel_k_to_kernel_u); };
}

#[verifier::spinoff_prover]
proof fn kernel_process_quota_4k_changed_implies_u_step(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, delta: int, include_lock_state: bool,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        kernel_process_quota_4k_changed(pre, post, cpu_id, process_ptr, container_ptr, delta),
    ensures
        kernel_u_only_process_quota_4k_changed(
            kernel_k_user_projection(*pre, include_lock_state), kernel_k_user_projection(*post, include_lock_state), cpu_id, process_ptr, container_ptr, delta,
        ),
{
    reveal(kernel_u_only_process_quota_4k_changed); reveal(kernel_process_quota_4k_changed); reveal(kernel_endpoint_nonlock_fields_unchanged);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { reveal(IommuRootTable::user_view); };
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array);
    let container = pre_u.container_map.spec_index(container_ptr);
    let process = pre_u.process_map.spec_index(process_ptr);
    assert_maps_equal!(post_u.container_map, pre_u.container_map.insert(container_ptr, ContainerU {
        quota_4k: (container.quota_4k as int - delta) as usize, ..container
    }), c => {});
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map, t => {});
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => {});
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(process_ptr, ProcessU {
        quota_4k: (process.quota_4k as int + delta) as usize, ..process
    }), p => {
        reveal(process_pagetable_match); reveal(process_iommu_table_match);
    });
}

#[verifier::spinoff_prover]
proof fn kernel_process_added_implies_u_neq(pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr)
    requires kernel_process_added(pre, post, process_ptr),
    ensures
        kernel_k_to_nonlock_kernel_u(*pre) != kernel_k_to_nonlock_kernel_u(*post),
        kernel_k_to_kernel_u(*pre) != kernel_k_to_kernel_u(*post),
{
    reveal(kernel_process_added); reveal(kernel_k_to_nonlock_kernel_u); reveal(kernel_k_to_kernel_u);
}

#[verifier::spinoff_prover]
proof fn kernel_process_4k_mapping_changed_implies_u_neq(pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires kernel_process_4k_mapping_changed(pre, post, process_ptr, pagetable_ptr, va),
    ensures
        kernel_k_to_nonlock_kernel_u(*pre) != kernel_k_to_nonlock_kernel_u(*post),
{
    assert(kernel_k_to_nonlock_kernel_u(*pre).process_map.spec_index(process_ptr).pagetable.unwrap().mapping_4k.dom().contains(va) != kernel_k_to_nonlock_kernel_u(*post).process_map.spec_index(process_ptr).pagetable.unwrap().mapping_4k.dom().contains(va)) by {
        reveal(kernel_process_4k_mapping_changed); reveal(kernel_k_to_nonlock_kernel_u);
    };
    assert(kernel_k_to_kernel_u(*pre).process_map.spec_index(process_ptr).pagetable.unwrap().mapping_4k.dom().contains(va)
        != kernel_k_to_kernel_u(*post).process_map.spec_index(process_ptr).pagetable.unwrap().mapping_4k.dom().contains(va)) by {
        reveal(kernel_process_4k_mapping_changed); reveal(kernel_k_to_kernel_u);
    };
}

pub proof fn kernel_cpu_tlb_updated_implies_u_step(pre: &KernelK, post: &KernelK)
    requires
        *post == (KernelK { cpu_arr: post.cpu_arr, cpu_tlb: post.cpu_tlb, pcid_needflush: post.pcid_needflush, ..*pre }),
        kernel_cpu_nonlock_fields_unchanged(pre.cpu_arr, post.cpu_arr),
        forall|cpu: CpuId| #![trigger post.cpu_arr.spec_index(cpu)] index_valid(NUM_CPUS, cpu) ==>
            post.cpu_arr.spec_index(cpu).value.locking_thread() == pre.cpu_arr.spec_index(cpu).value.locking_thread(),
    ensures
        kernel_k_to_kernel_u(*post) == (KernelU { cpu_tlb: post.cpu_tlb.view(), ..kernel_k_to_kernel_u(*pre) }),
{
    reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_k_to_kernel_u);
    assert_seqs_equal!(kernel_k_to_kernel_u(*post).cpu_array == kernel_k_to_kernel_u(*pre).cpu_array);
}

pub proof fn kernel_container_quota_4k_changed_implies_u_step(pre: &KernelK, post: &KernelK, container: RwLockContainerPtr, delta: int)
    requires
        kernel_container_quota_4k_changed(pre, post, container, delta),
        delta > 0,
    ensures
        kernel_k_to_kernel_u(*pre).container_map.dom().contains(container),
        kernel_k_to_kernel_u(*post).container_map[container].quota_4k as int == kernel_k_to_kernel_u(*pre).container_map[container].quota_4k as int + delta,
        kernel_k_to_kernel_u(*post) == (KernelU {
            container_map: kernel_k_to_kernel_u(*pre).container_map.insert(container, ContainerU {
                quota_4k: (kernel_k_to_kernel_u(*pre).container_map[container].quota_4k as int + delta) as usize,
                ..kernel_k_to_kernel_u(*pre).container_map[container]
            }), ..kernel_k_to_kernel_u(*pre)
        }),
{
    reveal(kernel_container_quota_4k_changed); reveal(kernel_k_to_kernel_u);
    reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    assert_maps_equal!(after.container_map, before.container_map.insert(container, ContainerU {
        quota_4k: (before.container_map[container].quota_4k as int + delta) as usize, ..before.container_map[container]
    }), c => {});
    assert_maps_equal!(after.thread_map, before.thread_map, t => {});
}

/// Clearing one present 4K entry and replacing one thread's progress removes that VA from the
/// owning process's user mapping and changes only that thread's progress.
pub proof fn kernel_pagetable_4k_present_cleared_and_progress_changed_implies_u_step(pre: &KernelK, post: &KernelK, pagetable: RwLockPageTableRoot, va: VAddr, thread_ptr: RwLockThreadPtr)
    requires
        process_pagetable_match(pre.prc_mp, pre.pt_mp),
        process_pagetable_match(post.prc_mp, post.pt_mp),
        pre.pt_mp.dom().contains(pagetable),
        *post == (KernelK { pt_mp: post.pt_mp, thr_mp: post.thr_mp, ..*pre }),
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable),
        post.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread(),
        post.pt_mp.spec_index(pagetable).view().proc_ptr == pre.pt_mp.spec_index(pagetable).view().proc_ptr,
        pre.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va),
        pre.pt_mp.spec_index(pagetable).view().mapping_4k()[va].present,
        post.pt_mp.spec_index(pagetable).view().mapping_4k() == pre.pt_mp.spec_index(pagetable).view().mapping_4k().insert(va, MapEntry { present: false, ..pre.pt_mp.spec_index(pagetable).view().mapping_4k()[va] }),
        post.pt_mp.spec_index(pagetable).view().mapping_2m() == pre.pt_mp.spec_index(pagetable).view().mapping_2m(),
        post.pt_mp.spec_index(pagetable).view().mapping_1g() == pre.pt_mp.spec_index(pagetable).view().mapping_1g(),
        pre.thr_mp.dom().contains(thread_ptr),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..pre.thr_mp.spec_index(thread_ptr).view() }),
        post.thr_mp.spec_index(thread_ptr).locking_thread() == pre.thr_mp.spec_index(thread_ptr).locking_thread(),
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
    ensures
        {
            let before = kernel_k_to_kernel_u(*pre);
            let process = pre.pt_mp.spec_index(pagetable).view().proc_ptr;
            &&& before.process_map.dom().contains(process)
            &&& before.process_map[process].pagetable is Some
            &&& before.process_map[process].pagetable->Some_0.mapping_4k.dom().contains(va)
            &&& before.thread_map.dom().contains(thread_ptr)
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                process_map: before.process_map.insert(process, ProcessU {
                    pagetable: Some(PageTableU { mapping_4k: before.process_map[process].pagetable->Some_0.mapping_4k.remove(va), ..before.process_map[process].pagetable->Some_0 }),
                    ..before.process_map[process]
                }),
                thread_map: before.thread_map.insert(thread_ptr, ThreadU { syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(), ..before.thread_map[thread_ptr] }),
                ..before
            })
        },
{
    reveal(kernel_k_to_kernel_u); reveal(process_pagetable_match);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    let process = pre.pt_mp.spec_index(pagetable).view().proc_ptr;
    assert_maps_equal!(after.process_map[process].pagetable->Some_0.mapping_4k,
        before.process_map[process].pagetable->Some_0.mapping_4k.remove(va), a => {});
    assert_maps_equal!(after.process_map, before.process_map.insert(process, ProcessU {
        pagetable: Some(PageTableU { mapping_4k: before.process_map[process].pagetable->Some_0.mapping_4k.remove(va), ..before.process_map[process].pagetable->Some_0 }),
        ..before.process_map[process]
    }), p => {});
    assert_maps_equal!(after.thread_map, before.thread_map.insert(thread_ptr, ThreadU { syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(), ..before.thread_map[thread_ptr] }), t => {});
}

/// Replacing one thread's progress changes only that thread's progress in the complete projection.
pub proof fn kernel_thread_syscall_progress_changed_implies_u_step(pre: &KernelK, post: &KernelK, thread_ptr: RwLockThreadPtr)
    requires
        *post == (KernelK { thr_mp: post.thr_mp, ..*pre }),
        pre.thr_mp.dom().contains(thread_ptr),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..pre.thr_mp.spec_index(thread_ptr).view() }),
        post.thr_mp.spec_index(thread_ptr).locking_thread() == pre.thr_mp.spec_index(thread_ptr).locking_thread(),
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
    ensures
        kernel_k_to_kernel_u(*pre).thread_map.dom().contains(thread_ptr),
        kernel_k_to_kernel_u(*post) == (KernelU {
            thread_map: kernel_k_to_kernel_u(*pre).thread_map.insert(thread_ptr, ThreadU {
                syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(), ..kernel_k_to_kernel_u(*pre).thread_map[thread_ptr]
            }),
            ..kernel_k_to_kernel_u(*pre)
        }),
{
    reveal(kernel_k_to_kernel_u);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    assert_maps_equal!(after.thread_map, before.thread_map.insert(thread_ptr, ThreadU {
        syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(), ..before.thread_map[thread_ptr]
    }), t => {});
}

/// A section that changes only one thread's quota, temporary cache, and progress plus the
/// kernel-only structure of one pagetable changes only that thread's quota and progress in
/// the complete projection. `lctx` is aligned with `post` and write-holds the cpu, thread,
/// and pagetable across the section.
#[verifier::spinoff_prover]
pub proof fn kernel_thread_quota_4k_and_progress_changed_implies_u_step(pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(post, lctx),
        pre.thr_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        pre.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        *post == (KernelK { pt_mp: post.pt_mp, pg_arr: post.pg_arr, thr_mp: post.thr_mp, ..*pre }),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread {
            quota_4k: post.thr_mp.spec_index(thread_ptr).view().quota_4k,
            temp_alloc_cache_4k: post.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k,
            syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress,
            ..pre.thr_mp.spec_index(thread_ptr).view()
        }),
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        post.pt_mp.spec_index(pagetable_ptr).view().mapping_4k() == pre.pt_mp.spec_index(pagetable_ptr).view().mapping_4k(),
        post.pt_mp.spec_index(pagetable_ptr).view().mapping_2m() == pre.pt_mp.spec_index(pagetable_ptr).view().mapping_2m(),
        post.pt_mp.spec_index(pagetable_ptr).view().mapping_1g() == pre.pt_mp.spec_index(pagetable_ptr).view().mapping_1g(),
    ensures
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let thread = pre.thr_mp.spec_index(thread_ptr).view();
            let process = pre_u.process_map.spec_index(process_ptr);
            &&& pre_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& pre_u.cpu_array[cpu_id as int].current_thread == pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread
            &&& pre_u.thread_map.dom().contains(thread_ptr)
            &&& pre_u.thread_map.spec_index(thread_ptr).lock_state is WriteLocked
            &&& pre_u.thread_map.spec_index(thread_ptr).owning_proc == thread.owning_proc
            &&& pre_u.thread_map.spec_index(thread_ptr).quota_4k == thread.quota_4k
            &&& pre_u.thread_map.spec_index(thread_ptr).syscall_progress == thread.syscall_progress.view()
            &&& pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr) ==> {
                &&& pre_u.process_map.dom().contains(process_ptr)
                &&& process.pagetable is Some
                &&& process.pagetable->Some_0.lock_state is WriteLocked
            }
        }),
        kernel_k_to_kernel_u(*post) == (KernelU {
            thread_map: kernel_k_to_kernel_u(*pre).thread_map.insert(thread_ptr, ThreadU {
                quota_4k: post.thr_mp.spec_index(thread_ptr).view().quota_4k,
                syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(),
                ..kernel_k_to_kernel_u(*pre).thread_map.spec_index(thread_ptr)
            }),
            ..kernel_k_to_kernel_u(*pre)
        }),
{
    reveal(kernel_k_to_kernel_u);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    pre.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr);
    post.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr);
    pre.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
    post.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
    assert(pre.cpu_arr.spec_index(cpu_id).view().wlocked_by_thread(lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); };
    assert(pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr) ==> pre.prc_mp.dom().contains(process_ptr) && !pre.prc_mp.spec_index(process_ptr).view().zombie && pre.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr) by { reveal(process_cpu_wf); reveal(process_pagetable_match); };
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array);
    assert_maps_equal!(post_u.container_map, pre_u.container_map, c => {});
    assert_maps_equal!(post_u.process_map, pre_u.process_map, p => { reveal(process_pagetable_match); });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thread_ptr, ThreadU {
        quota_4k: post.thr_mp.spec_index(thread_ptr).view().quota_4k,
        syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(),
        ..pre_u.thread_map.spec_index(thread_ptr)
    }), t => {});
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => {});
}

/// A section that changes one thread's quota, temporary cache, and progress and publishes one
/// present 4K entry of the running process's pagetable changes only that thread and that
/// process's pagetable mapping in the complete projection. `lctx` is aligned with `post` and
/// write-holds the cpu, thread, and pagetable across the section.
#[verifier::spinoff_prover]
pub proof fn kernel_thread_quota_4k_progress_and_4k_mapping_added_implies_u_step(pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(post, lctx),
        pre.thr_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        pre.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        *post == (KernelK { pt_mp: post.pt_mp, pg_arr: post.pg_arr, thr_mp: post.thr_mp, ..*pre }),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread {
            quota_4k: post.thr_mp.spec_index(thread_ptr).view().quota_4k,
            temp_alloc_cache_4k: post.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k,
            syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress,
            ..pre.thr_mp.spec_index(thread_ptr).view()
        }),
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        !pre.pt_mp.spec_index(pagetable_ptr).view().mapping_4k().dom().contains(va),
        post.pt_mp.spec_index(pagetable_ptr).view().mapping_4k() == pre.pt_mp.spec_index(pagetable_ptr).view().mapping_4k().insert(va, post.pt_mp.spec_index(pagetable_ptr).view().mapping_4k().spec_index(va)),
        post.pt_mp.spec_index(pagetable_ptr).view().mapping_4k().spec_index(va).present,
        post.pt_mp.spec_index(pagetable_ptr).view().mapping_2m() == pre.pt_mp.spec_index(pagetable_ptr).view().mapping_2m(),
        post.pt_mp.spec_index(pagetable_ptr).view().mapping_1g() == pre.pt_mp.spec_index(pagetable_ptr).view().mapping_1g(),
    ensures
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let thread = pre.thr_mp.spec_index(thread_ptr).view();
            let process = pre_u.process_map.spec_index(process_ptr);
            &&& pre_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& pre_u.cpu_array[cpu_id as int].current_thread == pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread
            &&& pre_u.thread_map.dom().contains(thread_ptr)
            &&& pre_u.thread_map.spec_index(thread_ptr).lock_state is WriteLocked
            &&& pre_u.thread_map.spec_index(thread_ptr).owning_container == thread.owning_container
            &&& pre_u.thread_map.spec_index(thread_ptr).owning_proc == thread.owning_proc
            &&& pre_u.thread_map.spec_index(thread_ptr).quota_4k == thread.quota_4k
            &&& pre_u.thread_map.spec_index(thread_ptr).syscall_progress == thread.syscall_progress.view()
            &&& pre_u.process_map.dom().contains(process_ptr)
            &&& process.pagetable is Some
            &&& process.pagetable->Some_0.lock_state is WriteLocked
            &&& !process.pagetable->Some_0.mapping_4k.dom().contains(va)
        }),
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let process = pre_u.process_map.spec_index(process_ptr);
            let pagetable = process.pagetable->Some_0;
            let entry = post.pt_mp.spec_index(pagetable_ptr).view().mapping_4k().spec_index(va);
            kernel_k_to_kernel_u(*post) == (KernelU {
                thread_map: pre_u.thread_map.insert(thread_ptr, ThreadU {
                    quota_4k: post.thr_mp.spec_index(thread_ptr).view().quota_4k,
                    syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(),
                    ..pre_u.thread_map.spec_index(thread_ptr)
                }),
                process_map: pre_u.process_map.insert(process_ptr, ProcessU {
                    pagetable: Some(PageTableU { mapping_4k: pagetable.mapping_4k.insert(va, entry), ..pagetable }),
                    ..process
                }),
                ..pre_u
            })
        }),
{
    reveal(kernel_k_to_kernel_u);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let process = pre_u.process_map.spec_index(process_ptr);
    let pagetable = process.pagetable->Some_0;
    let entry = post.pt_mp.spec_index(pagetable_ptr).view().mapping_4k().spec_index(va);
    let new_pagetable = PageTableU { mapping_4k: pagetable.mapping_4k.insert(va, entry), ..pagetable };
    pre.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr);
    post.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr);
    pre.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
    post.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
    assert(pre.cpu_arr.spec_index(cpu_id).view().wlocked_by_thread(lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); };
    assert(pre.prc_mp.dom().contains(process_ptr) && !pre.prc_mp.spec_index(process_ptr).view().zombie && pre.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr) by { reveal(process_cpu_wf); reveal(process_pagetable_match); };
    assert(pagetable == pre.pt_mp.spec_index(pagetable_ptr).view().user_view(pre.pt_mp.spec_index(pagetable_ptr).lock_state_u())) by { reveal(process_pagetable_match); };
    assert(post_u.process_map.spec_index(process_ptr).pagetable == Some(new_pagetable)) by {
        assert_maps_equal!(post.pt_mp.spec_index(pagetable_ptr).view().user_view(post.pt_mp.spec_index(pagetable_ptr).lock_state_u()).mapping_4k, new_pagetable.mapping_4k);
    };
    assert_maps_equal!(post_u.container_map, pre_u.container_map, c => {});
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(process_ptr, ProcessU { pagetable: Some(new_pagetable), ..process }), p => { reveal(process_pagetable_match); });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thread_ptr, ThreadU {
        quota_4k: post.thr_mp.spec_index(thread_ptr).view().quota_4k,
        syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(),
        ..pre_u.thread_map.spec_index(thread_ptr)
    }), t => {});
}

/// Setting the cpu, thread, and pagetable lock modes to the thread's mode and replacing the
/// thread's progress changes only those three projections. `lctx` is aligned with `pre`; the
/// objects it write-holds project as write-locked before the section.
#[verifier::spinoff_prover]
pub proof fn kernel_cpu_thread_pagetable_lock_states_and_progress_changed_implies_u_step(pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot)
    requires
        pre.inv(),
        typed_lock_maps_aligned(pre, lctx),
        index_valid(NUM_CPUS, cpu_id),
        *post == (KernelK { cpu_arr: post.cpu_arr, thr_mp: post.thr_mp, pt_mp: post.pt_mp, ..*pre }),
        post.cpu_arr.unchanged_except(&pre.cpu_arr, cpu_id),
        (post.cpu_arr.spec_index(cpu_id).value.locking_thread() is Write) == (post.thr_mp.spec_index(thread_ptr).locking_thread() is Write),
        (post.cpu_arr.spec_index(cpu_id).value.locking_thread() is Read) == (post.thr_mp.spec_index(thread_ptr).locking_thread() is Read),
        pre.thr_mp.dom().contains(thread_ptr),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..pre.thr_mp.spec_index(thread_ptr).view() }),
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        post.pt_mp.spec_index(pagetable_ptr).view() == pre.pt_mp.spec_index(pagetable_ptr).view(),
        (post.pt_mp.spec_index(pagetable_ptr).locking_thread() is Write) == (post.thr_mp.spec_index(thread_ptr).locking_thread() is Write),
        (post.pt_mp.spec_index(pagetable_ptr).locking_thread() is Read) == (post.thr_mp.spec_index(thread_ptr).locking_thread() is Read),
    ensures
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let thread = pre.thr_mp.spec_index(thread_ptr).view();
            let process = pre_u.process_map.spec_index(process_ptr);
            &&& pre_u.thread_map.dom().contains(thread_ptr)
            &&& pre_u.thread_map.spec_index(thread_ptr).owning_proc == thread.owning_proc
            &&& pre_u.thread_map.spec_index(thread_ptr).syscall_progress == thread.syscall_progress.view()
            &&& pre_u.process_map.dom().contains(process_ptr)
            &&& process.pagetable is Some
            &&& typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write) ==> pre_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write) ==> pre_u.thread_map.spec_index(thread_ptr).lock_state is WriteLocked
            &&& typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write) ==> process.pagetable->Some_0.lock_state is WriteLocked
            &&& pre_u.cpu_array[cpu_id as int].lock_state == pre.cpu_arr.spec_index(cpu_id).value.lock_state_u()
            &&& pre_u.cpu_array[cpu_id as int].state == pre.cpu_arr.spec_index(cpu_id).view().view().view().state
            &&& pre_u.cpu_array[cpu_id as int].current_thread == pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread
            &&& pre_u.thread_map.spec_index(thread_ptr).lock_state == pre.thr_mp.spec_index(thread_ptr).lock_state_u()
            &&& pre_u.thread_map.spec_index(thread_ptr).killed == pre.thr_mp.spec_index(thread_ptr).being_killed()
            &&& pre_u.thread_map.spec_index(thread_ptr).quota_4k == thread.quota_4k
            &&& process.pagetable->Some_0.lock_state == pre.pt_mp.spec_index(pagetable_ptr).lock_state_u()
            &&& process.pagetable->Some_0.mapping_4k.dom().subset_of(pre.pt_mp.spec_index(pagetable_ptr).view().mapping_4k().dom())
            &&& process.pagetable->Some_0.mapping_2m.dom().subset_of(pre.pt_mp.spec_index(pagetable_ptr).view().mapping_2m().dom())
            &&& process.pagetable->Some_0.mapping_1g.dom().subset_of(pre.pt_mp.spec_index(pagetable_ptr).view().mapping_1g().dom())
        }),
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let lock_state = post.thr_mp.spec_index(thread_ptr).lock_state_u();
            let process = pre_u.process_map.spec_index(process_ptr);
            kernel_k_to_kernel_u(*post) == (KernelU {
                cpu_array: pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state, ..pre_u.cpu_array[cpu_id as int] }),
                thread_map: pre_u.thread_map.insert(thread_ptr, ThreadU {
                    lock_state, syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(), ..pre_u.thread_map.spec_index(thread_ptr)
                }),
                process_map: pre_u.process_map.insert(process_ptr, ProcessU { pagetable: Some(PageTableU { lock_state, ..process.pagetable->Some_0 }), ..process }),
                ..pre_u
            })
        }),
{
    reveal(kernel_k_to_kernel_u);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let lock_state = post.thr_mp.spec_index(thread_ptr).lock_state_u();
    let process = pre_u.process_map.spec_index(process_ptr);
    assert(pre.prc_mp.dom().contains(process_ptr) && !pre.prc_mp.spec_index(process_ptr).view().zombie && pre.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr) by { reveal(process_cpu_wf); reveal(process_pagetable_match); };
    assert(typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write) ==> pre.cpu_arr.spec_index(cpu_id).view().wlocked_by_thread(lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); };
    if typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write) { pre.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr); }
    if typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write) { pre.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); }
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state, ..pre_u.cpu_array[cpu_id as int] }));
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(process_ptr, ProcessU { pagetable: Some(PageTableU { lock_state, ..process.pagetable->Some_0 }), ..process }), p => { reveal(process_pagetable_match); });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thread_ptr, ThreadU {
        lock_state, syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(), ..pre_u.thread_map.spec_index(thread_ptr)
    }), t => {});
}

/// Setting the cpu, container, process, pagetable, and thread lock modes to the thread's mode and
/// replacing the thread's progress changes only those five projections. `lctx` is aligned with
/// `pre`; the objects it write-holds project as write-locked before the section.
#[verifier::spinoff_prover]
pub proof fn kernel_thread_context_lock_states_and_progress_changed_implies_u_step(
    pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot,
)
    requires
        pre.inv(),
        typed_lock_maps_aligned(pre, lctx),
        index_valid(NUM_CPUS, cpu_id),
        *post == (KernelK { cpu_arr: post.cpu_arr, ctn_mp: post.ctn_mp, prc_mp: post.prc_mp, thr_mp: post.thr_mp, pt_mp: post.pt_mp, ..*pre }),
        post.cpu_arr.unchanged_except(&pre.cpu_arr, cpu_id),
        (post.cpu_arr.spec_index(cpu_id).value.locking_thread() is Write) == (post.thr_mp.spec_index(thread_ptr).locking_thread() is Write),
        (post.cpu_arr.spec_index(cpu_id).value.locking_thread() is Read) == (post.thr_mp.spec_index(thread_ptr).locking_thread() is Read),
        post.ctn_mp.unchanged_except(&pre.ctn_mp, container_ptr),
        post.ctn_mp.spec_index(container_ptr).view() == pre.ctn_mp.spec_index(container_ptr).view(),
        post.ctn_mp.spec_index(container_ptr).view_rodata() == pre.ctn_mp.spec_index(container_ptr).view_rodata(),
        post.ctn_mp.spec_index(container_ptr).view_ghost() == pre.ctn_mp.spec_index(container_ptr).view_ghost(),
        post.ctn_mp.spec_index(container_ptr).being_killed() == pre.ctn_mp.spec_index(container_ptr).being_killed(),
        (post.ctn_mp.spec_index(container_ptr).locking_thread() is Write) == (post.thr_mp.spec_index(thread_ptr).locking_thread() is Write),
        (post.ctn_mp.spec_index(container_ptr).locking_thread() is Read) == (post.thr_mp.spec_index(thread_ptr).locking_thread() is Read),
        post.prc_mp.unchanged_except(&pre.prc_mp, process_ptr),
        post.prc_mp.spec_index(process_ptr).view() == pre.prc_mp.spec_index(process_ptr).view(),
        post.prc_mp.spec_index(process_ptr).view_rodata() == pre.prc_mp.spec_index(process_ptr).view_rodata(),
        post.prc_mp.spec_index(process_ptr).view_ghost() == pre.prc_mp.spec_index(process_ptr).view_ghost(),
        post.prc_mp.spec_index(process_ptr).being_killed() == pre.prc_mp.spec_index(process_ptr).being_killed(),
        (post.prc_mp.spec_index(process_ptr).locking_thread() is Write) == (post.thr_mp.spec_index(thread_ptr).locking_thread() is Write),
        (post.prc_mp.spec_index(process_ptr).locking_thread() is Read) == (post.thr_mp.spec_index(thread_ptr).locking_thread() is Read),
        pre.thr_mp.dom().contains(thread_ptr),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..pre.thr_mp.spec_index(thread_ptr).view() }),
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        post.pt_mp.spec_index(pagetable_ptr).view() == pre.pt_mp.spec_index(pagetable_ptr).view(),
        (post.pt_mp.spec_index(pagetable_ptr).locking_thread() is Write) == (post.thr_mp.spec_index(thread_ptr).locking_thread() is Write),
        (post.pt_mp.spec_index(pagetable_ptr).locking_thread() is Read) == (post.thr_mp.spec_index(thread_ptr).locking_thread() is Read),
    ensures
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let thread = pre.thr_mp.spec_index(thread_ptr).view();
            let process = pre_u.process_map.spec_index(process_ptr);
            &&& pre_u.container_map.dom().contains(container_ptr)
            &&& pre_u.thread_map.dom().contains(thread_ptr)
            &&& pre_u.thread_map.spec_index(thread_ptr).owning_container == thread.owning_container
            &&& pre_u.thread_map.spec_index(thread_ptr).owning_proc == thread.owning_proc
            &&& pre_u.thread_map.spec_index(thread_ptr).syscall_progress == thread.syscall_progress.view()
            &&& pre_u.process_map.dom().contains(process_ptr)
            &&& process.pagetable is Some
            &&& typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write) ==> pre_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write) ==> pre_u.container_map.spec_index(container_ptr).lock_state is WriteLocked
            &&& typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write) ==> process.lock_state is WriteLocked
            &&& typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write) ==> pre_u.thread_map.spec_index(thread_ptr).lock_state is WriteLocked
            &&& typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write) ==> process.pagetable->Some_0.lock_state is WriteLocked
            &&& pre_u.cpu_array[cpu_id as int].lock_state == pre.cpu_arr.spec_index(cpu_id).value.lock_state_u()
            &&& pre_u.container_map.spec_index(container_ptr).lock_state == pre.ctn_mp.spec_index(container_ptr).lock_state_u()
            &&& process.lock_state == pre.prc_mp.spec_index(process_ptr).lock_state_u()
            &&& pre_u.thread_map.spec_index(thread_ptr).lock_state == pre.thr_mp.spec_index(thread_ptr).lock_state_u()
            &&& process.pagetable->Some_0.lock_state == pre.pt_mp.spec_index(pagetable_ptr).lock_state_u()
            &&& pre_u.cpu_array[cpu_id as int].state == pre.cpu_arr.spec_index(cpu_id).view().view().view().state
            &&& pre_u.cpu_array[cpu_id as int].current_thread == pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread
            &&& pre_u.container_map.spec_index(container_ptr).killed == pre.ctn_mp.spec_index(container_ptr).being_killed()
            &&& process.killed == pre.prc_mp.spec_index(process_ptr).being_killed()
            &&& pre_u.thread_map.spec_index(thread_ptr).killed == pre.thr_mp.spec_index(thread_ptr).being_killed()
            &&& forall|va: VAddr| #![trigger process.pagetable->Some_0.mapping_4k.dom().contains(va)]
                pre.pt_mp.spec_index(pagetable_ptr).view().mapping_4k().dom().contains(va) && pre.pt_mp.spec_index(pagetable_ptr).view().mapping_4k()[va].present
                ==> process.pagetable->Some_0.mapping_4k.dom().contains(va)
        }),
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let lock_state = post.thr_mp.spec_index(thread_ptr).lock_state_u();
            let process = pre_u.process_map.spec_index(process_ptr);
            kernel_k_to_kernel_u(*post) == (KernelU {
                cpu_array: pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state, ..pre_u.cpu_array[cpu_id as int] }),
                container_map: pre_u.container_map.insert(container_ptr, ContainerU { lock_state, ..pre_u.container_map.spec_index(container_ptr) }),
                process_map: pre_u.process_map.insert(process_ptr, ProcessU { lock_state, pagetable: Some(PageTableU { lock_state, ..process.pagetable->Some_0 }), ..process }),
                thread_map: pre_u.thread_map.insert(thread_ptr, ThreadU {
                    lock_state, syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(), ..pre_u.thread_map.spec_index(thread_ptr)
                }),
                ..pre_u
            })
        }),
{
    reveal(kernel_k_to_kernel_u);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let lock_state = post.thr_mp.spec_index(thread_ptr).lock_state_u();
    let process = pre_u.process_map.spec_index(process_ptr);
    assert(pre.prc_mp.dom().contains(process_ptr) && !pre.prc_mp.spec_index(process_ptr).view().zombie && pre.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr) by { reveal(process_cpu_wf); reveal(process_pagetable_match); };
    assert(typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write) ==> pre.cpu_arr.spec_index(cpu_id).view().wlocked_by_thread(lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); };
    if typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write) { pre.ctn_mp.typed_lock_map_aligned_write_at(lctx.container_lock_map(), lctx.thread_id(), container_ptr); }
    if typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write) { pre.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), process_ptr); }
    if typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write) { pre.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr); }
    if typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write) { pre.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); }
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state, ..pre_u.cpu_array[cpu_id as int] }));
    assert_maps_equal!(post_u.container_map, pre_u.container_map.insert(container_ptr, ContainerU { lock_state, ..pre_u.container_map.spec_index(container_ptr) }), c => {});
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(process_ptr, ProcessU {
        lock_state, pagetable: Some(PageTableU { lock_state, ..process.pagetable->Some_0 }), ..process
    }), p => { reveal(process_pagetable_match); });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thread_ptr, ThreadU {
        lock_state, syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(), ..pre_u.thread_map.spec_index(thread_ptr)
    }), t => {});
}

impl KernelK {
    pub proof fn kernel_step_boundary_nonlock_fields_unchanged(tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps)
        requires
            old(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(self).ep_mp),
            old(self).irt.owners() == old(steps).snapshot_k().irt.owners(),
            old(self).irt.iommu_roots() == old(steps).snapshot_k().irt.iommu_roots(),
            old(self).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            old(self).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(self)),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> {
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3 == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid
                &&& final(self).cpu_published[old(lctx).cpu_id() as int].view() == old(self).cpu_published[old(lctx).cpu_id() as int].view()
            },
            final(self).inv(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, final(self).pt_mp.spec_index(pt).view())]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(self).cpu_tlb, old(self).cpu_arr, old(self).pcid_needflush, pt, old(self).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, final(self).pt_mp.spec_index(pt).view()),
            forall|pagetable_ptr: RwLockPageTableRoot, cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr), final(self).cpu_tlb.spec_index((cpu_id, pcid))]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) && index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID ==> {
                    let before = old(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    let after = final(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    after is Some && after.unwrap().pagetable_ptr == pagetable_ptr && (before is None || before.unwrap().pagetable_ptr != pagetable_ptr
                        || single_cpu_single_pcid_tlb_subset_of_present_pagetable(old(self).cpu_tlb.spec_index((cpu_id, pcid)), old(self).pt_mp.spec_index(pagetable_ptr).view())
                        || (old(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush && old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid
                            && (!final(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush || final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid)))
                    ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(self).cpu_tlb.spec_index((cpu_id, pcid)), final(self).pt_mp.spec_index(pagetable_ptr).view())
                },
            forall|cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))]
                old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))
                ==> final(self).pcid_needflush.spec_index(cpu_id, pcid) == old(self).pcid_needflush.spec_index(cpu_id, pcid),
            forall|cpu_id: CpuId|
                #![trigger old(lctx).cpu_lock_map().dom().contains(cpu_id)]
                old(lctx).cpu_lock_map().dom().contains(cpu_id) ==> final(self).cpu_arr.spec_index(cpu_id).view() == old(self).cpu_arr.spec_index(cpu_id).view(),
            forall|container_ptr: RwLockContainerPtr|
                #![trigger old(lctx).container_lock_map().dom().contains(container_ptr)]
                old(lctx).container_lock_map().dom().contains(container_ptr) ==> {
                    &&& final(self).ctn_mp.dom().contains(container_ptr)
                    &&& final(self).ctn_mp.lock_id_by_key(container_ptr) == old(self).ctn_mp.lock_id_by_key(container_ptr)
                    &&& final(self).ctn_mp.spec_index(container_ptr) == old(self).ctn_mp.spec_index(container_ptr)
                },
            forall|process_ptr: RwLockProcessPtr|
                #![trigger old(lctx).process_lock_map().dom().contains(process_ptr)]
                old(lctx).process_lock_map().dom().contains(process_ptr) ==> {
                    &&& final(self).prc_mp.dom().contains(process_ptr)
                    &&& final(self).prc_mp.lock_id_by_key(process_ptr) == old(self).prc_mp.lock_id_by_key(process_ptr)
                    &&& final(self).prc_mp.spec_index(process_ptr) == old(self).prc_mp.spec_index(process_ptr)
                },
            forall|thread_ptr: RwLockThreadPtr|
                #![trigger old(lctx).thread_lock_map().dom().contains(thread_ptr)]
                old(lctx).thread_lock_map().dom().contains(thread_ptr) ==> {
                    &&& final(self).thr_mp.dom().contains(thread_ptr)
                    &&& final(self).thr_mp.lock_id_by_key(thread_ptr) == old(self).thr_mp.lock_id_by_key(thread_ptr)
                    &&& final(self).thr_mp.spec_index(thread_ptr) == old(self).thr_mp.spec_index(thread_ptr)
                },
            forall|pagetable_ptr: RwLockPageTableRoot|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) ==> {
                    &&& final(self).pt_mp.dom().contains(pagetable_ptr)
                    &&& final(self).pt_mp.lock_id_by_key(pagetable_ptr) == old(self).pt_mp.lock_id_by_key(pagetable_ptr)
                    &&& final(self).pt_mp.spec_index(pagetable_ptr) == old(self).pt_mp.spec_index(pagetable_ptr)
                },
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(self))),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).nonlock_view() == old(steps).nonlock_view(),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(self)),
            final(steps).snapshot_k() == *final(self),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(self)),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(self).ep_mp),
            final(self).dflt_pt == old(self).dflt_pt,
            containers_rodata_unchanged(old(self).ctn_mp, final(self).ctn_mp),
            processes_rodata_unchanged(old(self).prc_mp, final(self).prc_mp),
            held_containers_unchanged(old(self).ctn_mp, final(self).ctn_mp, old(lctx)),
            held_processes_unchanged(old(self).prc_mp, final(self).prc_mp, old(lctx)),
            held_threads_unchanged(old(self).thr_mp, final(self).thr_mp, old(lctx)),
            held_endpoints_unchanged(old(self).ep_mp, final(self).ep_mp, old(lctx)),
            held_schedulers_unchanged(old(self).sched_mp, final(self).sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(self).pcid_allc_mp, final(self).pcid_allc_mp, old(lctx)),
            held_cpu_sets_unchanged(old(self).cpu_set_mp, final(self).cpu_set_mp, old(lctx)),
            held_pagetables_unchanged(old(self).pt_mp, final(self).pt_mp, old(lctx)),
            held_iommu_tables_unchanged(old(self).it_mp, final(self).it_mp, old(lctx)),
            held_pages_unchanged(old(self).pg_arr, final(self).pg_arr, old(lctx)),
            held_cpus_unchanged(old(self).cpu_arr, final(self).cpu_arr, old(lctx)),
            held_allocator_objects_unchanged(old(self).allc_4k_mp, final(self).allc_4k_mp, old(lctx), PageSize::SZ4k),
            held_allocator_objects_unchanged(old(self).allc_2m_mp, final(self).allc_2m_mp, old(lctx), PageSize::SZ2m),
            held_allocator_objects_unchanged(old(self).allc_1g_mp, final(self).allc_1g_mp, old(lctx), PageSize::SZ1g),
    {
        use_type_invariant(&*steps);
        reveal(KernelSteps::nonlock_view);
        assert(steps.nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*self)) by {
            kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(&steps.snapshot_k(), &*self);
        };
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
        assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, self.ep_mp)) by { broadcast use kernel_endpoint_nonlock_fields_unchanged_for_equal; };
    }

    pub proof fn kernel_step_boundary_cpu_tlb_updated(tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, cpu_id: CpuId, pcid: Pcid, flushed: bool)
        requires
            *old(self) == (KernelK { cpu_arr: old(self).cpu_arr, cpu_tlb: old(self).cpu_tlb, pcid_needflush: old(self).pcid_needflush, ..old(steps).snapshot_k() }),
            forall|cpu: CpuId| #![trigger old(self).cpu_arr.spec_index(cpu)] index_valid(NUM_CPUS, cpu) ==>
                old(self).cpu_arr.spec_index(cpu).value.locking_thread() == old(steps).snapshot_k().cpu_arr.spec_index(cpu).value.locking_thread(),
            old(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(self).ep_mp),
            old(self).irt.owners() == old(steps).snapshot_k().irt.owners(),
            old(self).irt.iommu_roots() == old(steps).snapshot_k().irt.iommu_roots(),
            index_valid(NUM_CPUS, cpu_id),
            pcid_valid(pcid),
            old(self).cpu_tlb.view() == if flushed {
                old(steps).snapshot_k().cpu_tlb.view().insert((cpu_id, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })
            } else { old(steps).snapshot_k().cpu_tlb.view() },
            old(self).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(self)),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==>
                kernel_u_cpu_tlb_cleared(final(steps).view()[j].old_u, final(steps).view()[j].new_u, pcid),
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> {
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3 == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid
                &&& final(self).cpu_published[old(lctx).cpu_id() as int].view() == old(self).cpu_published[old(lctx).cpu_id() as int].view()
            },
            final(self).inv(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, final(self).pt_mp.spec_index(pt).view())]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(self).cpu_tlb, old(self).cpu_arr, old(self).pcid_needflush, pt, old(self).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, final(self).pt_mp.spec_index(pt).view()),
            forall|pagetable_ptr: RwLockPageTableRoot, cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr), final(self).cpu_tlb.spec_index((cpu_id, pcid))]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) && index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID ==> {
                    let before = old(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    let after = final(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    after is Some && after.unwrap().pagetable_ptr == pagetable_ptr && (before is None || before.unwrap().pagetable_ptr != pagetable_ptr
                        || single_cpu_single_pcid_tlb_subset_of_present_pagetable(old(self).cpu_tlb.spec_index((cpu_id, pcid)), old(self).pt_mp.spec_index(pagetable_ptr).view())
                        || (old(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush && old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid
                            && (!final(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush || final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid)))
                    ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(self).cpu_tlb.spec_index((cpu_id, pcid)), final(self).pt_mp.spec_index(pagetable_ptr).view())
                },
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(self))),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).nonlock_view() == if old(self).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view() {
                old(steps).nonlock_view()
            } else {
                old(steps).nonlock_view().push(KernelStep { old_u: old(steps).nonlock_snapshot_u(),
                    new_u: KernelU { cpu_tlb: old(self).cpu_tlb.view(), ..old(steps).nonlock_snapshot_u() } })
            },
            old(steps).nonlock_view().len() <= final(steps).nonlock_view().len() <= old(steps).nonlock_view().len() + 1,
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(self)),
            final(steps).snapshot_k() == *final(self),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(self)),
            held_containers_unchanged(old(self).ctn_mp, final(self).ctn_mp, old(lctx)),
            held_processes_unchanged(old(self).prc_mp, final(self).prc_mp, old(lctx)),
            held_threads_unchanged(old(self).thr_mp, final(self).thr_mp, old(lctx)),
            held_pagetables_unchanged(old(self).pt_mp, final(self).pt_mp, old(lctx)),
            held_iommu_tables_unchanged(old(self).it_mp, final(self).it_mp, old(lctx)),
            held_pages_unchanged(old(self).pg_arr, final(self).pg_arr, old(lctx)),
            held_cpus_unchanged(old(self).cpu_arr, final(self).cpu_arr, old(lctx)),
    {
        use_type_invariant(&*steps);
        reveal(KernelSteps::nonlock_view);
        assert(kernel_k_to_kernel_u(*self) == (KernelU { cpu_tlb: self.cpu_tlb.view(), ..steps.snapshot_u() })) by {
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
            kernel_cpu_tlb_updated_implies_u_step(&steps.snapshot_k(), &*self);
        };
        let pre_u = steps.nonlock_snapshot_u();
        let post_u = kernel_k_to_nonlock_kernel_u(*self);
        assert(post_u == (KernelU { cpu_tlb: self.cpu_tlb.view(), ..pre_u }) && pre_u.cpu_tlb == steps.snapshot_k().cpu_tlb.view()) by {
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
            kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(&KernelK { cpu_tlb: self.cpu_tlb, ..steps.snapshot_k() }, self);
            reveal(kernel_k_to_nonlock_kernel_u);
        };
        assert(steps.snapshot_u() != kernel_k_to_kernel_u(*self) ==> kernel_u_cpu_tlb_cleared(steps.snapshot_u(), kernel_k_to_kernel_u(*self), pcid)) by {
            reveal(kernel_u_cpu_tlb_cleared); reveal(kernel_k_to_kernel_u);
            if steps.snapshot_u() != kernel_k_to_kernel_u(*self) {
                assert(!steps.snapshot_u().cpu_tlb.dom().contains((cpu_id, pcid)) || steps.snapshot_u().cpu_tlb[(cpu_id, pcid)] != (SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })) by {
                    if steps.snapshot_u().cpu_tlb.dom().contains((cpu_id, pcid)) && steps.snapshot_u().cpu_tlb[(cpu_id, pcid)] == (SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }) {
                        assert_maps_equal!(steps.snapshot_u().cpu_tlb, self.cpu_tlb.view(), key => {});
                    }
                };
                assert_sets_equal!(self.cpu_tlb.view().dom().filter(|key: (CpuId, Pcid)| !steps.snapshot_u().cpu_tlb.dom().contains(key) || steps.snapshot_u().cpu_tlb[key] != self.cpu_tlb.view()[key]), set![(cpu_id, pcid)]);
            }
        };
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*self)) by {
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
            kernel_cpu_nonlock_fields_unchanged_for_equal(self.cpu_arr, self.cpu_arr);
            kernel_process_nonlock_fields_unchanged_for_equal(self.prc_mp, self.prc_mp);
            kernel_thread_nonlock_fields_unchanged_for_equal(self.thr_mp, self.thr_mp);
            kernel_pagetable_nonlock_fields_unchanged_for_equal(self.pt_mp, self.pt_mp);
            kernel_iommu_table_nonlock_fields_unchanged_for_equal(self.it_mp, self.it_mp);
        };
        assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, self.ep_mp)) by { broadcast use kernel_endpoint_nonlock_fields_unchanged_for_equal; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
    }

    #[verifier::spinoff_prover]
    pub proof fn kernel_step_boundary_container_quota_4k_changed(
        tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, container_ptr: RwLockContainerPtr, delta: int, origin: RwLockContainerPtr,
    )
        requires
            old(self).inv(),
            delta > 0,
            kernel_container_quota_4k_changed(&old(steps).snapshot_k(), old(self), container_ptr, delta),
            old(steps).snapshot_k().ctn_mp.dom().contains(origin),
            container_ptr == origin || old(steps).snapshot_k().ctn_mp.spec_index(origin).view_ghost().uppertree_seq.view().contains(container_ptr),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            kernel_u_container_quota_4k_increased(old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(self)), origin),
            old(steps).snapshot_u().container_map.dom().contains(container_ptr),
            kernel_k_to_kernel_u(*old(self)).container_map[container_ptr].quota_4k as int == old(steps).snapshot_u().container_map[container_ptr].quota_4k as int + delta,
            final(steps).view() == old(steps).view().push(KernelStep { old_u: old(steps).snapshot_u(), new_u: kernel_k_to_kernel_u(*old(self)) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            kernel_k_to_kernel_u(*old(self)) == (KernelU { container_map: old(steps).snapshot_u().container_map.insert(container_ptr, ContainerU {
                quota_4k: (old(steps).snapshot_u().container_map[container_ptr].quota_4k as int + delta) as usize,
                ..old(steps).snapshot_u().container_map[container_ptr]
            }), ..old(steps).snapshot_u() }),
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(self).inv(),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(self).cpu_published[old(lctx).cpu_id() as int].view() == old(self).cpu_published[old(lctx).cpu_id() as int].view(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, final(self).pt_mp.spec_index(pt).view())]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(self).cpu_tlb, old(self).cpu_arr, old(self).pcid_needflush, pt, old(self).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, final(self).pt_mp.spec_index(pt).view()),
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(self))),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep { old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*old(self)) }),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(self)),
            final(steps).snapshot_k() == *final(self),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(self)),
            final(steps).nonlock_view().last().new_u == (KernelU {
                container_map: final(steps).nonlock_view().last().old_u.container_map.insert(container_ptr, ContainerU {
                    quota_4k: (final(steps).nonlock_view().last().old_u.container_map.spec_index(container_ptr).quota_4k as int + delta) as usize,
                    ..final(steps).nonlock_view().last().old_u.container_map.spec_index(container_ptr)
                }),
                ..final(steps).nonlock_view().last().old_u
            }),
            containers_rodata_unchanged(old(self).ctn_mp, final(self).ctn_mp),
            held_containers_unchanged(old(self).ctn_mp, final(self).ctn_mp, old(lctx)),
            held_processes_unchanged(old(self).prc_mp, final(self).prc_mp, old(lctx)),
            held_threads_unchanged(old(self).thr_mp, final(self).thr_mp, old(lctx)),
            held_pagetables_unchanged(old(self).pt_mp, final(self).pt_mp, old(lctx)),
            held_pages_unchanged(old(self).pg_arr, final(self).pg_arr, old(lctx)),
            held_cpus_unchanged(old(self).cpu_arr, final(self).cpu_arr, old(lctx)),
    {
        use_type_invariant(&*steps);
        reveal(KernelSteps::nonlock_view);
        assert(steps.snapshot_u().container_map.dom().contains(container_ptr)
            && kernel_k_to_kernel_u(*self).container_map[container_ptr].quota_4k as int == steps.snapshot_u().container_map[container_ptr].quota_4k as int + delta
            && kernel_k_to_kernel_u(*self) != steps.snapshot_u() && kernel_k_to_kernel_u(*self) == (KernelU {
                container_map: steps.snapshot_u().container_map.insert(container_ptr, ContainerU {
                    quota_4k: (steps.snapshot_u().container_map[container_ptr].quota_4k as int + delta) as usize, ..steps.snapshot_u().container_map[container_ptr]
                }), ..steps.snapshot_u()
            })) by { kernel_container_quota_4k_changed_implies_u_step(&steps.snapshot_k(), &*self, container_ptr, delta); };
        assert(kernel_u_container_quota_4k_increased(steps.snapshot_u(), kernel_k_to_kernel_u(*self), origin)) by {
            reveal(kernel_u_container_quota_4k_increased);
            kernel_container_ancestry_projection_at(&steps.snapshot_k(), origin);
            let pre = steps.snapshot_u();
            let post = kernel_k_to_kernel_u(*self);
            assert_sets_equal!(pre.container_map.dom().filter(|c: RwLockContainerPtr| pre.container_map[c] != post.container_map[c]), set![container_ptr]);
            assert_sets_equal!(post.container_map.dom(), pre.container_map.dom());
        };
        let pre_u = steps.nonlock_snapshot_u();
        let post_u = kernel_k_to_nonlock_kernel_u(*self);
        assert(post_u != pre_u && post_u == (KernelU {
            container_map: pre_u.container_map.insert(container_ptr, ContainerU {
                quota_4k: (pre_u.container_map.spec_index(container_ptr).quota_4k as int + delta) as usize,
                ..pre_u.container_map.spec_index(container_ptr)
            }),
            ..pre_u
        })) by {
            reveal(KernelK::inv); reveal(kernel_container_quota_4k_changed); reveal(kernel_endpoint_nonlock_fields_unchanged);
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
            reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
            reveal(kernel_k_to_nonlock_kernel_u);
            assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { reveal(IommuRootTable::user_view); };
            assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array);
            assert_maps_equal!(post_u.thread_map, pre_u.thread_map, t => {});
            assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => {});
            assert_maps_equal!(post_u.process_map, pre_u.process_map, p => {
                reveal(process_pagetable_match); reveal(process_iommu_table_match);
            });
            assert_maps_equal!(post_u.container_map, pre_u.container_map.insert(container_ptr, post_u.container_map.spec_index(container_ptr)), c => {});
        };
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*self)) by {
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
            kernel_cpu_nonlock_fields_unchanged_for_equal(self.cpu_arr, self.cpu_arr);
            kernel_process_nonlock_fields_unchanged_for_equal(self.prc_mp, self.prc_mp);
            kernel_thread_nonlock_fields_unchanged_for_equal(self.thr_mp, self.thr_mp);
            kernel_pagetable_nonlock_fields_unchanged_for_equal(self.pt_mp, self.pt_mp);
            kernel_iommu_table_nonlock_fields_unchanged_for_equal(self.it_mp, self.it_mp);
        };
        assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, self.ep_mp)) by { broadcast use kernel_endpoint_nonlock_fields_unchanged_for_equal; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
    }

    pub proof fn kernel_step_boundary_thread_quota_4k_changed(
        tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, thread_ptr: RwLockThreadPtr, delta: int,
    )
        requires
            old(self).inv(),
            delta != 0,
            kernel_thread_quota_4k_changed(&old(steps).snapshot_k(), old(self), thread_ptr, delta),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> {
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3 == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid
                &&& final(self).cpu_published[old(lctx).cpu_id() as int].view() == old(self).cpu_published[old(lctx).cpu_id() as int].view()
            },
            final(self).inv(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, final(self).pt_mp.spec_index(pt).view())]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(self).cpu_tlb, old(self).cpu_arr, old(self).pcid_needflush, pt, old(self).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, final(self).pt_mp.spec_index(pt).view()),
            forall|pagetable_ptr: RwLockPageTableRoot, cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr), final(self).cpu_tlb.spec_index((cpu_id, pcid))]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) && index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID ==> {
                    let before = old(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    let after = final(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    after is Some && after.unwrap().pagetable_ptr == pagetable_ptr && (before is None || before.unwrap().pagetable_ptr != pagetable_ptr
                        || single_cpu_single_pcid_tlb_subset_of_present_pagetable(old(self).cpu_tlb.spec_index((cpu_id, pcid)), old(self).pt_mp.spec_index(pagetable_ptr).view())
                        || (old(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush && old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid
                            && (!final(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush || final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid)))
                    ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(self).cpu_tlb.spec_index((cpu_id, pcid)), final(self).pt_mp.spec_index(pagetable_ptr).view())
                },
            forall|cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))]
                old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))
                ==> final(self).pcid_needflush.spec_index(cpu_id, pcid) == old(self).pcid_needflush.spec_index(cpu_id, pcid),
            forall|cpu_id: CpuId|
                #![trigger old(lctx).cpu_lock_map().dom().contains(cpu_id)]
                old(lctx).cpu_lock_map().dom().contains(cpu_id) ==> final(self).cpu_arr.spec_index(cpu_id).view() == old(self).cpu_arr.spec_index(cpu_id).view(),
            forall|container_ptr: RwLockContainerPtr|
                #![trigger old(lctx).container_lock_map().dom().contains(container_ptr)]
                old(lctx).container_lock_map().dom().contains(container_ptr) ==> {
                    &&& final(self).ctn_mp.dom().contains(container_ptr)
                    &&& final(self).ctn_mp.lock_id_by_key(container_ptr) == old(self).ctn_mp.lock_id_by_key(container_ptr)
                    &&& final(self).ctn_mp.spec_index(container_ptr) == old(self).ctn_mp.spec_index(container_ptr)
                },
            forall|process_ptr: RwLockProcessPtr|
                #![trigger old(lctx).process_lock_map().dom().contains(process_ptr)]
                old(lctx).process_lock_map().dom().contains(process_ptr) ==> {
                    &&& final(self).prc_mp.dom().contains(process_ptr)
                    &&& final(self).prc_mp.lock_id_by_key(process_ptr) == old(self).prc_mp.lock_id_by_key(process_ptr)
                    &&& final(self).prc_mp.spec_index(process_ptr) == old(self).prc_mp.spec_index(process_ptr)
                },
            forall|thread_ptr: RwLockThreadPtr|
                #![trigger old(lctx).thread_lock_map().dom().contains(thread_ptr)]
                old(lctx).thread_lock_map().dom().contains(thread_ptr) ==> {
                    &&& final(self).thr_mp.dom().contains(thread_ptr)
                    &&& final(self).thr_mp.lock_id_by_key(thread_ptr) == old(self).thr_mp.lock_id_by_key(thread_ptr)
                    &&& final(self).thr_mp.spec_index(thread_ptr) == old(self).thr_mp.spec_index(thread_ptr)
                },
            forall|pagetable_ptr: RwLockPageTableRoot|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) ==> {
                    &&& final(self).pt_mp.dom().contains(pagetable_ptr)
                    &&& final(self).pt_mp.lock_id_by_key(pagetable_ptr) == old(self).pt_mp.lock_id_by_key(pagetable_ptr)
                    &&& final(self).pt_mp.spec_index(pagetable_ptr) == old(self).pt_mp.spec_index(pagetable_ptr)
                },
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == old(steps).view().push(KernelStep { old_u: old(steps).snapshot_u(), new_u: kernel_k_to_kernel_u(*old(self)) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep {
                old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*old(self)),
            }),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(self)),
            final(steps).snapshot_k() == *final(self),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(self)),
            final(steps).nonlock_view().last().new_u.thread_map.spec_index(thread_ptr) == (ThreadU {
                quota_4k: (final(steps).nonlock_view().last().old_u.thread_map.spec_index(thread_ptr).quota_4k as int + delta) as usize,
                syscall_progress: final(steps).nonlock_view().last().new_u.thread_map.spec_index(thread_ptr).syscall_progress,
                ..final(steps).nonlock_view().last().old_u.thread_map.spec_index(thread_ptr)
            }),
            final(self).dflt_pt == old(self).dflt_pt,
            containers_rodata_unchanged(old(self).ctn_mp, final(self).ctn_mp),
            processes_rodata_unchanged(old(self).prc_mp, final(self).prc_mp),
            held_containers_unchanged(old(self).ctn_mp, final(self).ctn_mp, old(lctx)),
            held_processes_unchanged(old(self).prc_mp, final(self).prc_mp, old(lctx)),
            held_threads_unchanged(old(self).thr_mp, final(self).thr_mp, old(lctx)),
            held_endpoints_unchanged(old(self).ep_mp, final(self).ep_mp, old(lctx)),
            held_schedulers_unchanged(old(self).sched_mp, final(self).sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(self).pcid_allc_mp, final(self).pcid_allc_mp, old(lctx)),
            held_cpu_sets_unchanged(old(self).cpu_set_mp, final(self).cpu_set_mp, old(lctx)),
            held_pagetables_unchanged(old(self).pt_mp, final(self).pt_mp, old(lctx)),
            held_iommu_tables_unchanged(old(self).it_mp, final(self).it_mp, old(lctx)),
            held_pages_unchanged(old(self).pg_arr, final(self).pg_arr, old(lctx)),
            held_cpus_unchanged(old(self).cpu_arr, final(self).cpu_arr, old(lctx)),
            held_allocator_objects_unchanged(old(self).allc_4k_mp, final(self).allc_4k_mp, old(lctx), PageSize::SZ4k),
            held_allocator_objects_unchanged(old(self).allc_2m_mp, final(self).allc_2m_mp, old(lctx), PageSize::SZ2m),
            held_allocator_objects_unchanged(old(self).allc_1g_mp, final(self).allc_1g_mp, old(lctx), PageSize::SZ1g),
    {
        use_type_invariant(&*steps);
        reveal(KernelSteps::nonlock_view);
        kernel_thread_quota_4k_changed_implies_u_step(&steps.snapshot_k(), &*self, thread_ptr, delta);
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, self.ep_mp)) by { broadcast use kernel_endpoint_nonlock_fields_unchanged_for_equal; };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
    }

    #[verifier::spinoff_prover]
    pub proof fn kernel_step_boundary_thread_syscall_progress_changed(
        tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, thread_ptr: RwLockThreadPtr,
    )
        requires
            old(self).inv(),
            old(steps).snapshot_k().thr_mp.dom().contains(thread_ptr),
            old(self).thr_mp.dom().contains(thread_ptr),
            old(steps).snapshot_k().thr_mp.spec_index(thread_ptr).view().syscall_progress.view() != old(self).thr_mp.spec_index(thread_ptr).view().syscall_progress.view(),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> {
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3 == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid
                &&& final(self).cpu_published[old(lctx).cpu_id() as int].view() == old(self).cpu_published[old(lctx).cpu_id() as int].view()
            },
            final(self).inv(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, final(self).pt_mp.spec_index(pt).view())]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(self).cpu_tlb, old(self).cpu_arr, old(self).pcid_needflush, pt, old(self).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, final(self).pt_mp.spec_index(pt).view()),
            forall|pagetable_ptr: RwLockPageTableRoot, cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr), final(self).cpu_tlb.spec_index((cpu_id, pcid))]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) && index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID ==> {
                    let before = old(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    let after = final(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    after is Some && after.unwrap().pagetable_ptr == pagetable_ptr && (before is None || before.unwrap().pagetable_ptr != pagetable_ptr
                        || single_cpu_single_pcid_tlb_subset_of_present_pagetable(old(self).cpu_tlb.spec_index((cpu_id, pcid)), old(self).pt_mp.spec_index(pagetable_ptr).view())
                        || (old(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush && old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid
                            && (!final(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush || final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid)))
                    ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(self).cpu_tlb.spec_index((cpu_id, pcid)), final(self).pt_mp.spec_index(pagetable_ptr).view())
                },
            forall|cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))]
                old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))
                ==> final(self).pcid_needflush.spec_index(cpu_id, pcid) == old(self).pcid_needflush.spec_index(cpu_id, pcid),
            forall|cpu_id: CpuId|
                #![trigger old(lctx).cpu_lock_map().dom().contains(cpu_id)]
                old(lctx).cpu_lock_map().dom().contains(cpu_id) ==> final(self).cpu_arr.spec_index(cpu_id).view() == old(self).cpu_arr.spec_index(cpu_id).view(),
            forall|container_ptr: RwLockContainerPtr|
                #![trigger old(lctx).container_lock_map().dom().contains(container_ptr)]
                old(lctx).container_lock_map().dom().contains(container_ptr) ==> {
                    &&& final(self).ctn_mp.dom().contains(container_ptr)
                    &&& final(self).ctn_mp.lock_id_by_key(container_ptr) == old(self).ctn_mp.lock_id_by_key(container_ptr)
                    &&& final(self).ctn_mp.spec_index(container_ptr) == old(self).ctn_mp.spec_index(container_ptr)
                },
            forall|process_ptr: RwLockProcessPtr|
                #![trigger old(lctx).process_lock_map().dom().contains(process_ptr)]
                old(lctx).process_lock_map().dom().contains(process_ptr) ==> {
                    &&& final(self).prc_mp.dom().contains(process_ptr)
                    &&& final(self).prc_mp.lock_id_by_key(process_ptr) == old(self).prc_mp.lock_id_by_key(process_ptr)
                    &&& final(self).prc_mp.spec_index(process_ptr) == old(self).prc_mp.spec_index(process_ptr)
                },
            forall|thread_ptr: RwLockThreadPtr|
                #![trigger old(lctx).thread_lock_map().dom().contains(thread_ptr)]
                old(lctx).thread_lock_map().dom().contains(thread_ptr) ==> {
                    &&& final(self).thr_mp.dom().contains(thread_ptr)
                    &&& final(self).thr_mp.lock_id_by_key(thread_ptr) == old(self).thr_mp.lock_id_by_key(thread_ptr)
                    &&& final(self).thr_mp.spec_index(thread_ptr) == old(self).thr_mp.spec_index(thread_ptr)
                },
            forall|pagetable_ptr: RwLockPageTableRoot|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) ==> {
                    &&& final(self).pt_mp.dom().contains(pagetable_ptr)
                    &&& final(self).pt_mp.lock_id_by_key(pagetable_ptr) == old(self).pt_mp.lock_id_by_key(pagetable_ptr)
                    &&& final(self).pt_mp.spec_index(pagetable_ptr) == old(self).pt_mp.spec_index(pagetable_ptr)
                },
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == old(steps).view().push(KernelStep { old_u: old(steps).snapshot_u(), new_u: kernel_k_to_kernel_u(*old(self)) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep {
                old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*old(self)),
            }),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(self)),
            final(steps).snapshot_k() == *final(self),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(self)),
            final(self).dflt_pt == old(self).dflt_pt,
            containers_rodata_unchanged(old(self).ctn_mp, final(self).ctn_mp),
            processes_rodata_unchanged(old(self).prc_mp, final(self).prc_mp),
            held_containers_unchanged(old(self).ctn_mp, final(self).ctn_mp, old(lctx)),
            held_processes_unchanged(old(self).prc_mp, final(self).prc_mp, old(lctx)),
            held_threads_unchanged(old(self).thr_mp, final(self).thr_mp, old(lctx)),
            held_endpoints_unchanged(old(self).ep_mp, final(self).ep_mp, old(lctx)),
            held_schedulers_unchanged(old(self).sched_mp, final(self).sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(self).pcid_allc_mp, final(self).pcid_allc_mp, old(lctx)),
            held_cpu_sets_unchanged(old(self).cpu_set_mp, final(self).cpu_set_mp, old(lctx)),
            held_pagetables_unchanged(old(self).pt_mp, final(self).pt_mp, old(lctx)),
            held_iommu_tables_unchanged(old(self).it_mp, final(self).it_mp, old(lctx)),
            held_pages_unchanged(old(self).pg_arr, final(self).pg_arr, old(lctx)),
            held_cpus_unchanged(old(self).cpu_arr, final(self).cpu_arr, old(lctx)),
            held_allocator_objects_unchanged(old(self).allc_4k_mp, final(self).allc_4k_mp, old(lctx), PageSize::SZ4k),
            held_allocator_objects_unchanged(old(self).allc_2m_mp, final(self).allc_2m_mp, old(lctx), PageSize::SZ2m),
            held_allocator_objects_unchanged(old(self).allc_1g_mp, final(self).allc_1g_mp, old(lctx), PageSize::SZ1g),
    {
        use_type_invariant(&*steps);
        reveal(KernelSteps::nonlock_view);
        steps.end_kernel_step_thread_syscall_progress_changed(&*self, &*lctx, thread_ptr);
        self.kernel_step_boundary_raw(lctx, steps);
        assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, self.ep_mp)) by { broadcast use kernel_endpoint_nonlock_fields_unchanged_for_equal; };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
    }

    #[verifier::spinoff_prover]
    pub proof fn kernel_step_boundary_thread_state_changed(
        tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, thread_ptr: RwLockThreadPtr,
        old_state: ThreadState, new_state: ThreadState,
    )
        requires
            old(self).inv(),
            kernel_thread_state_changed(&old(steps).snapshot_k(), old(self), thread_ptr),
            old(steps).snapshot_k().thr_mp.dom().contains(thread_ptr),
            old(self).thr_mp.dom().contains(thread_ptr),
            old(steps).snapshot_k().thr_mp.spec_index(thread_ptr).view().state == old_state,
            old(self).thr_mp.spec_index(thread_ptr).view().state == new_state,
            old(lctx).kernel_view_locking_state() is Release,
            old(lctx).thread_lock_map().dom().contains(thread_ptr),
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> {
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3 == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid
                &&& final(self).cpu_published[old(lctx).cpu_id() as int].view() == old(self).cpu_published[old(lctx).cpu_id() as int].view()
            },
            final(self).inv(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, final(self).pt_mp.spec_index(pt).view())]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(self).cpu_tlb, old(self).cpu_arr, old(self).pcid_needflush, pt, old(self).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, final(self).pt_mp.spec_index(pt).view()),
            forall|pagetable_ptr: RwLockPageTableRoot, cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr), final(self).cpu_tlb.spec_index((cpu_id, pcid))]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) && index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID ==> {
                    let before = old(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    let after = final(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    after is Some && after.unwrap().pagetable_ptr == pagetable_ptr && (before is None || before.unwrap().pagetable_ptr != pagetable_ptr
                        || single_cpu_single_pcid_tlb_subset_of_present_pagetable(old(self).cpu_tlb.spec_index((cpu_id, pcid)), old(self).pt_mp.spec_index(pagetable_ptr).view())
                        || (old(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush && old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid
                            && (!final(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush || final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid)))
                    ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(self).cpu_tlb.spec_index((cpu_id, pcid)), final(self).pt_mp.spec_index(pagetable_ptr).view())
                },
            forall|cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))]
                old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))
                ==> final(self).pcid_needflush.spec_index(cpu_id, pcid) == old(self).pcid_needflush.spec_index(cpu_id, pcid),
            forall|cpu_id: CpuId|
                #![trigger old(lctx).cpu_lock_map().dom().contains(cpu_id)]
                old(lctx).cpu_lock_map().dom().contains(cpu_id) ==> final(self).cpu_arr.spec_index(cpu_id).view() == old(self).cpu_arr.spec_index(cpu_id).view(),
            forall|container_ptr: RwLockContainerPtr|
                #![trigger old(lctx).container_lock_map().dom().contains(container_ptr)]
                old(lctx).container_lock_map().dom().contains(container_ptr) ==> {
                    &&& final(self).ctn_mp.dom().contains(container_ptr)
                    &&& final(self).ctn_mp.lock_id_by_key(container_ptr) == old(self).ctn_mp.lock_id_by_key(container_ptr)
                    &&& final(self).ctn_mp.spec_index(container_ptr) == old(self).ctn_mp.spec_index(container_ptr)
                },
            forall|process_ptr: RwLockProcessPtr|
                #![trigger old(lctx).process_lock_map().dom().contains(process_ptr)]
                old(lctx).process_lock_map().dom().contains(process_ptr) ==> {
                    &&& final(self).prc_mp.dom().contains(process_ptr)
                    &&& final(self).prc_mp.lock_id_by_key(process_ptr) == old(self).prc_mp.lock_id_by_key(process_ptr)
                    &&& final(self).prc_mp.spec_index(process_ptr) == old(self).prc_mp.spec_index(process_ptr)
                },
            forall|thread_ptr: RwLockThreadPtr|
                #![trigger old(lctx).thread_lock_map().dom().contains(thread_ptr)]
                old(lctx).thread_lock_map().dom().contains(thread_ptr) ==> {
                    &&& final(self).thr_mp.dom().contains(thread_ptr)
                    &&& final(self).thr_mp.lock_id_by_key(thread_ptr) == old(self).thr_mp.lock_id_by_key(thread_ptr)
                    &&& final(self).thr_mp.spec_index(thread_ptr) == old(self).thr_mp.spec_index(thread_ptr)
                },
            forall|pagetable_ptr: RwLockPageTableRoot|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) ==> {
                    &&& final(self).pt_mp.dom().contains(pagetable_ptr)
                    &&& final(self).pt_mp.lock_id_by_key(pagetable_ptr) == old(self).pt_mp.lock_id_by_key(pagetable_ptr)
                    &&& final(self).pt_mp.spec_index(pagetable_ptr) == old(self).pt_mp.spec_index(pagetable_ptr)
                },
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(self))),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep {
                old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*old(self)),
            }),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(self)),
            final(steps).snapshot_k() == *final(self),
            final(steps).nonlock_view().last().old_u.thread_map.dom().contains(thread_ptr),
            final(steps).nonlock_view().last().old_u.thread_map.spec_index(thread_ptr).state == old_state,
            final(steps).nonlock_view().last().new_u.thread_map.dom().contains(thread_ptr),
            final(steps).nonlock_view().last().new_u.thread_map.spec_index(thread_ptr).state == new_state,
            final(steps).nonlock_snapshot_u().thread_map.dom().contains(thread_ptr),
            final(steps).nonlock_snapshot_u().thread_map.spec_index(thread_ptr).state == new_state,
            final(self).dflt_pt == old(self).dflt_pt,
            containers_rodata_unchanged(old(self).ctn_mp, final(self).ctn_mp),
            processes_rodata_unchanged(old(self).prc_mp, final(self).prc_mp),
            held_containers_unchanged(old(self).ctn_mp, final(self).ctn_mp, old(lctx)),
            held_processes_unchanged(old(self).prc_mp, final(self).prc_mp, old(lctx)),
            held_threads_unchanged(old(self).thr_mp, final(self).thr_mp, old(lctx)),
            held_endpoints_unchanged(old(self).ep_mp, final(self).ep_mp, old(lctx)),
            held_schedulers_unchanged(old(self).sched_mp, final(self).sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(self).pcid_allc_mp, final(self).pcid_allc_mp, old(lctx)),
            held_cpu_sets_unchanged(old(self).cpu_set_mp, final(self).cpu_set_mp, old(lctx)),
            held_pagetables_unchanged(old(self).pt_mp, final(self).pt_mp, old(lctx)),
            held_iommu_tables_unchanged(old(self).it_mp, final(self).it_mp, old(lctx)),
            held_pages_unchanged(old(self).pg_arr, final(self).pg_arr, old(lctx)),
            held_cpus_unchanged(old(self).cpu_arr, final(self).cpu_arr, old(lctx)),
            held_allocator_objects_unchanged(old(self).allc_4k_mp, final(self).allc_4k_mp, old(lctx), PageSize::SZ4k),
            held_allocator_objects_unchanged(old(self).allc_2m_mp, final(self).allc_2m_mp, old(lctx), PageSize::SZ2m),
            held_allocator_objects_unchanged(old(self).allc_1g_mp, final(self).allc_1g_mp, old(lctx), PageSize::SZ1g),
    {
        use_type_invariant(&*steps);
        reveal(KernelSteps::nonlock_view);
        kernel_thread_state_changed_implies_u_neq(&steps.snapshot_k(), &*self, thread_ptr);
        assert(steps.nonlock_snapshot_u().thread_map.dom().contains(thread_ptr)
            && steps.nonlock_snapshot_u().thread_map.spec_index(thread_ptr).state == old_state) by { reveal(kernel_k_to_nonlock_kernel_u); };
        assert(kernel_k_to_nonlock_kernel_u(*self).thread_map.dom().contains(thread_ptr)
            && kernel_k_to_nonlock_kernel_u(*self).thread_map.spec_index(thread_ptr).state == new_state) by { reveal(kernel_k_to_nonlock_kernel_u); };
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        reveal(kernel_k_to_nonlock_kernel_u);
    }

    #[verifier::spinoff_prover]
    pub proof fn kernel_step_boundary_process_added(
        tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, process_ptr: RwLockProcessPtr,
        current_thread_ptr: RwLockThreadPtr,
    )
        requires
            old(self).inv(),
            kernel_process_added(&old(steps).snapshot_k(), old(self), process_ptr),
            old(self).prc_mp.dom().contains(process_ptr),
            !old(self).prc_mp.spec_index(process_ptr).view().zombie,
            old(self).thr_mp.dom().contains(current_thread_ptr),
            old(lctx).kernel_view_locking_state() is Release,
            old(lctx).process_lock_map().dom().contains(process_ptr),
            old(lctx).thread_lock_map().dom().contains(current_thread_ptr),
            old(lctx).pagetable_lock_map().dom().contains(old(self).prc_mp.spec_index(process_ptr).view().pagetable),
            {
                let iommu_table = old(self).prc_mp.spec_index(process_ptr).view().iommu_table;
                ||| iommu_table is None
                ||| iommu_table is Some && old(lctx).iommu_table_lock_map().dom().contains(iommu_table.unwrap())
            },
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> {
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3 == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid
                &&& final(self).cpu_published[old(lctx).cpu_id() as int].view() == old(self).cpu_published[old(lctx).cpu_id() as int].view()
            },
            final(self).inv(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, final(self).pt_mp.spec_index(pt).view())]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(self).cpu_tlb, old(self).cpu_arr, old(self).pcid_needflush, pt, old(self).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, final(self).pt_mp.spec_index(pt).view()),
            forall|pagetable_ptr: RwLockPageTableRoot, cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr), final(self).cpu_tlb.spec_index((cpu_id, pcid))]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) && index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID ==> {
                    let before = old(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    let after = final(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    after is Some && after.unwrap().pagetable_ptr == pagetable_ptr && (before is None || before.unwrap().pagetable_ptr != pagetable_ptr
                        || single_cpu_single_pcid_tlb_subset_of_present_pagetable(old(self).cpu_tlb.spec_index((cpu_id, pcid)), old(self).pt_mp.spec_index(pagetable_ptr).view())
                        || (old(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush && old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid
                            && (!final(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush || final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid)))
                    ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(self).cpu_tlb.spec_index((cpu_id, pcid)), final(self).pt_mp.spec_index(pagetable_ptr).view())
                },
            forall|cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))]
                old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))
                ==> final(self).pcid_needflush.spec_index(cpu_id, pcid) == old(self).pcid_needflush.spec_index(cpu_id, pcid),
            forall|cpu_id: CpuId|
                #![trigger old(lctx).cpu_lock_map().dom().contains(cpu_id)]
                old(lctx).cpu_lock_map().dom().contains(cpu_id) ==> final(self).cpu_arr.spec_index(cpu_id).view() == old(self).cpu_arr.spec_index(cpu_id).view(),
            forall|container_ptr: RwLockContainerPtr|
                #![trigger old(lctx).container_lock_map().dom().contains(container_ptr)]
                old(lctx).container_lock_map().dom().contains(container_ptr) ==> {
                    &&& final(self).ctn_mp.dom().contains(container_ptr)
                    &&& final(self).ctn_mp.lock_id_by_key(container_ptr) == old(self).ctn_mp.lock_id_by_key(container_ptr)
                    &&& final(self).ctn_mp.spec_index(container_ptr) == old(self).ctn_mp.spec_index(container_ptr)
                },
            forall|process_ptr: RwLockProcessPtr|
                #![trigger old(lctx).process_lock_map().dom().contains(process_ptr)]
                old(lctx).process_lock_map().dom().contains(process_ptr) ==> {
                    &&& final(self).prc_mp.dom().contains(process_ptr)
                    &&& final(self).prc_mp.lock_id_by_key(process_ptr) == old(self).prc_mp.lock_id_by_key(process_ptr)
                    &&& final(self).prc_mp.spec_index(process_ptr) == old(self).prc_mp.spec_index(process_ptr)
                },
            forall|thread_ptr: RwLockThreadPtr|
                #![trigger old(lctx).thread_lock_map().dom().contains(thread_ptr)]
                old(lctx).thread_lock_map().dom().contains(thread_ptr) ==> {
                    &&& final(self).thr_mp.dom().contains(thread_ptr)
                    &&& final(self).thr_mp.lock_id_by_key(thread_ptr) == old(self).thr_mp.lock_id_by_key(thread_ptr)
                    &&& final(self).thr_mp.spec_index(thread_ptr) == old(self).thr_mp.spec_index(thread_ptr)
                },
            forall|pagetable_ptr: RwLockPageTableRoot|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) ==> {
                    &&& final(self).pt_mp.dom().contains(pagetable_ptr)
                    &&& final(self).pt_mp.lock_id_by_key(pagetable_ptr) == old(self).pt_mp.lock_id_by_key(pagetable_ptr)
                    &&& final(self).pt_mp.spec_index(pagetable_ptr) == old(self).pt_mp.spec_index(pagetable_ptr)
                },
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == old(steps).view().push(KernelStep { old_u: old(steps).snapshot_u(), new_u: kernel_k_to_kernel_u(*old(self)) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep {
                old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*old(self)),
            }),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(self)),
            final(steps).snapshot_k() == *final(self),
            final(steps).nonlock_view().last().new_u.process_map.dom().contains(process_ptr),
            kernel_k_to_nonlock_kernel_u(*final(self)).process_map.dom().contains(process_ptr),
            final(steps).nonlock_view().last().new_u.process_map.spec_index(process_ptr) == kernel_k_to_nonlock_kernel_u(*final(self)).process_map.spec_index(process_ptr),
            final(steps).nonlock_view().last().new_u.thread_map.dom().contains(current_thread_ptr),
            kernel_k_to_nonlock_kernel_u(*final(self)).thread_map.dom().contains(current_thread_ptr),
            final(steps).nonlock_view().last().new_u.thread_map.spec_index(current_thread_ptr)
                == kernel_k_to_nonlock_kernel_u(*final(self)).thread_map.spec_index(current_thread_ptr),
            final(self).dflt_pt == old(self).dflt_pt,
            containers_rodata_unchanged(old(self).ctn_mp, final(self).ctn_mp),
            processes_rodata_unchanged(old(self).prc_mp, final(self).prc_mp),
            held_containers_unchanged(old(self).ctn_mp, final(self).ctn_mp, old(lctx)),
            held_processes_unchanged(old(self).prc_mp, final(self).prc_mp, old(lctx)),
            held_threads_unchanged(old(self).thr_mp, final(self).thr_mp, old(lctx)),
            held_endpoints_unchanged(old(self).ep_mp, final(self).ep_mp, old(lctx)),
            held_schedulers_unchanged(old(self).sched_mp, final(self).sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(self).pcid_allc_mp, final(self).pcid_allc_mp, old(lctx)),
            held_cpu_sets_unchanged(old(self).cpu_set_mp, final(self).cpu_set_mp, old(lctx)),
            held_pagetables_unchanged(old(self).pt_mp, final(self).pt_mp, old(lctx)),
            held_iommu_tables_unchanged(old(self).it_mp, final(self).it_mp, old(lctx)),
            held_pages_unchanged(old(self).pg_arr, final(self).pg_arr, old(lctx)),
            held_cpus_unchanged(old(self).cpu_arr, final(self).cpu_arr, old(lctx)),
            held_allocator_objects_unchanged(old(self).allc_4k_mp, final(self).allc_4k_mp, old(lctx), PageSize::SZ4k),
            held_allocator_objects_unchanged(old(self).allc_2m_mp, final(self).allc_2m_mp, old(lctx), PageSize::SZ2m),
            held_allocator_objects_unchanged(old(self).allc_1g_mp, final(self).allc_1g_mp, old(lctx), PageSize::SZ1g),
    {
        use_type_invariant(&*steps);
        reveal(KernelSteps::nonlock_view);
        kernel_process_added_implies_u_neq(&steps.snapshot_k(), &*self, process_ptr);
        assert(kernel_k_to_nonlock_kernel_u(*self).process_map.dom().contains(process_ptr)
            && kernel_k_to_nonlock_kernel_u(*self).thread_map.dom().contains(current_thread_ptr)) by { reveal(kernel_k_to_nonlock_kernel_u); };
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        reveal(kernel_k_to_nonlock_kernel_u);
        let pagetable = old(self).prc_mp.spec_index(process_ptr).view().pagetable;
        assert(old(self).pt_mp.dom().contains(pagetable)) by { reveal(process_pagetable_match); };
        let iommu_table = old(self).prc_mp.spec_index(process_ptr).view().iommu_table;
        if iommu_table is Some {
            assert(old(self).it_mp.dom().contains(iommu_table.unwrap())) by { reveal(process_iommu_table_match); };
        }
    }

    #[verifier::spinoff_prover]
    pub proof fn kernel_step_boundary_process_4k_mapping_changed(
        tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, process_ptr: RwLockProcessPtr,
        pagetable_ptr: RwLockPageTableRoot, va: VAddr, stable_process_ptr: RwLockProcessPtr, stable_pagetable_ptr: RwLockPageTableRoot,
        stable_thread_ptr: RwLockThreadPtr,
    )
        requires
            old(self).inv(),
            kernel_process_4k_mapping_changed(&old(steps).snapshot_k(), old(self), process_ptr, pagetable_ptr, va),
            old(self).prc_mp.dom().contains(process_ptr),
            !old(self).prc_mp.spec_index(process_ptr).view().zombie,
            old(self).prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr,
            old(self).thr_mp.dom().contains(stable_thread_ptr),
            old(lctx).kernel_view_locking_state() is Release,
            old(self).prc_mp.dom().contains(stable_process_ptr),
            !old(self).prc_mp.spec_index(stable_process_ptr).view().zombie,
            old(self).prc_mp.spec_index(stable_process_ptr).view().pagetable == stable_pagetable_ptr,
            old(lctx).pagetable_lock_map().dom().contains(stable_pagetable_ptr),
            old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr),
            old(lctx).thread_lock_map().dom().contains(stable_thread_ptr),
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> {
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3 == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_cr3
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_pcid
                &&& final(self).cpu_published[old(lctx).cpu_id() as int].view() == old(self).cpu_published[old(lctx).cpu_id() as int].view()
            },
            final(self).inv(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, final(self).pt_mp.spec_index(pt).view())]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(self).cpu_tlb, old(self).cpu_arr, old(self).pcid_needflush, pt, old(self).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, final(self).pt_mp.spec_index(pt).view()),
            forall|pagetable_ptr: RwLockPageTableRoot, cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr), final(self).cpu_tlb.spec_index((cpu_id, pcid))]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) && index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID ==> {
                    let before = old(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    let after = final(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    after is Some && after.unwrap().pagetable_ptr == pagetable_ptr && (before is None || before.unwrap().pagetable_ptr != pagetable_ptr
                        || single_cpu_single_pcid_tlb_subset_of_present_pagetable(old(self).cpu_tlb.spec_index((cpu_id, pcid)), old(self).pt_mp.spec_index(pagetable_ptr).view())
                        || (old(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush && old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid
                            && (!final(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush || final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid)))
                    ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(self).cpu_tlb.spec_index((cpu_id, pcid)), final(self).pt_mp.spec_index(pagetable_ptr).view())
                },
            forall|cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))]
                old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))
                ==> final(self).pcid_needflush.spec_index(cpu_id, pcid) == old(self).pcid_needflush.spec_index(cpu_id, pcid),
            forall|cpu_id: CpuId|
                #![trigger old(lctx).cpu_lock_map().dom().contains(cpu_id)]
                old(lctx).cpu_lock_map().dom().contains(cpu_id) ==> final(self).cpu_arr.spec_index(cpu_id).view() == old(self).cpu_arr.spec_index(cpu_id).view(),
            forall|container_ptr: RwLockContainerPtr|
                #![trigger old(lctx).container_lock_map().dom().contains(container_ptr)]
                old(lctx).container_lock_map().dom().contains(container_ptr) ==> {
                    &&& final(self).ctn_mp.dom().contains(container_ptr)
                    &&& final(self).ctn_mp.lock_id_by_key(container_ptr) == old(self).ctn_mp.lock_id_by_key(container_ptr)
                    &&& final(self).ctn_mp.spec_index(container_ptr) == old(self).ctn_mp.spec_index(container_ptr)
                },
            forall|process_ptr: RwLockProcessPtr|
                #![trigger old(lctx).process_lock_map().dom().contains(process_ptr)]
                old(lctx).process_lock_map().dom().contains(process_ptr) ==> {
                    &&& final(self).prc_mp.dom().contains(process_ptr)
                    &&& final(self).prc_mp.lock_id_by_key(process_ptr) == old(self).prc_mp.lock_id_by_key(process_ptr)
                    &&& final(self).prc_mp.spec_index(process_ptr) == old(self).prc_mp.spec_index(process_ptr)
                },
            forall|thread_ptr: RwLockThreadPtr|
                #![trigger old(lctx).thread_lock_map().dom().contains(thread_ptr)]
                old(lctx).thread_lock_map().dom().contains(thread_ptr) ==> {
                    &&& final(self).thr_mp.dom().contains(thread_ptr)
                    &&& final(self).thr_mp.lock_id_by_key(thread_ptr) == old(self).thr_mp.lock_id_by_key(thread_ptr)
                    &&& final(self).thr_mp.spec_index(thread_ptr) == old(self).thr_mp.spec_index(thread_ptr)
                },
            forall|pagetable_ptr: RwLockPageTableRoot|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) ==> {
                    &&& final(self).pt_mp.dom().contains(pagetable_ptr)
                    &&& final(self).pt_mp.lock_id_by_key(pagetable_ptr) == old(self).pt_mp.lock_id_by_key(pagetable_ptr)
                    &&& final(self).pt_mp.spec_index(pagetable_ptr) == old(self).pt_mp.spec_index(pagetable_ptr)
                },
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == old(steps).view().push(KernelStep { old_u: old(steps).snapshot_u(), new_u: kernel_k_to_kernel_u(*old(self)) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep {
                old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*old(self)),
            }),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(self)),
            final(steps).snapshot_k() == *final(self),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(self)),
            final(steps).nonlock_view().last().new_u.process_map.dom().contains(stable_process_ptr),
            kernel_k_to_nonlock_kernel_u(*final(self)).process_map.dom().contains(stable_process_ptr),
            final(steps).nonlock_view().last().new_u.process_map.spec_index(stable_process_ptr).pagetable
                == kernel_k_to_nonlock_kernel_u(*final(self)).process_map.spec_index(stable_process_ptr).pagetable,
            final(steps).nonlock_view().last().new_u.process_map.dom().contains(process_ptr),
            final(steps).nonlock_view().last().new_u.thread_map.dom().contains(stable_thread_ptr),
            kernel_k_to_nonlock_kernel_u(*final(self)).thread_map.dom().contains(stable_thread_ptr),
            final(steps).nonlock_view().last().new_u.thread_map.spec_index(stable_thread_ptr)
                == kernel_k_to_nonlock_kernel_u(*final(self)).thread_map.spec_index(stable_thread_ptr),
            old(lctx).process_lock_map().dom().contains(process_ptr) && ({
                let iommu_table = old(self).prc_mp.spec_index(process_ptr).view().iommu_table;
                ||| iommu_table is None
                ||| iommu_table is Some && old(lctx).iommu_table_lock_map().dom().contains(iommu_table.unwrap())
            }) ==> {
                &&& kernel_k_to_nonlock_kernel_u(*final(self)).process_map.dom().contains(process_ptr)
                &&& final(steps).nonlock_view().last().new_u.process_map.spec_index(process_ptr) == kernel_k_to_nonlock_kernel_u(*final(self)).process_map.spec_index(process_ptr)
            },
            final(self).dflt_pt == old(self).dflt_pt,
            containers_rodata_unchanged(old(self).ctn_mp, final(self).ctn_mp),
            processes_rodata_unchanged(old(self).prc_mp, final(self).prc_mp),
            held_containers_unchanged(old(self).ctn_mp, final(self).ctn_mp, old(lctx)),
            held_processes_unchanged(old(self).prc_mp, final(self).prc_mp, old(lctx)),
            held_threads_unchanged(old(self).thr_mp, final(self).thr_mp, old(lctx)),
            held_endpoints_unchanged(old(self).ep_mp, final(self).ep_mp, old(lctx)),
            held_schedulers_unchanged(old(self).sched_mp, final(self).sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(self).pcid_allc_mp, final(self).pcid_allc_mp, old(lctx)),
            held_cpu_sets_unchanged(old(self).cpu_set_mp, final(self).cpu_set_mp, old(lctx)),
            held_pagetables_unchanged(old(self).pt_mp, final(self).pt_mp, old(lctx)),
            held_iommu_tables_unchanged(old(self).it_mp, final(self).it_mp, old(lctx)),
            held_pages_unchanged(old(self).pg_arr, final(self).pg_arr, old(lctx)),
            held_cpus_unchanged(old(self).cpu_arr, final(self).cpu_arr, old(lctx)),
            held_allocator_objects_unchanged(old(self).allc_4k_mp, final(self).allc_4k_mp, old(lctx), PageSize::SZ4k),
            held_allocator_objects_unchanged(old(self).allc_2m_mp, final(self).allc_2m_mp, old(lctx), PageSize::SZ2m),
            held_allocator_objects_unchanged(old(self).allc_1g_mp, final(self).allc_1g_mp, old(lctx), PageSize::SZ1g),
    {
        use_type_invariant(&*steps);
        reveal(KernelSteps::nonlock_view);
        kernel_process_4k_mapping_changed_implies_u_neq(&steps.snapshot_k(), &*self, process_ptr, pagetable_ptr, va);
        assert(kernel_k_to_nonlock_kernel_u(*self).process_map.dom().contains(process_ptr) && kernel_k_to_nonlock_kernel_u(*self).process_map.dom().contains(stable_process_ptr)
            && kernel_k_to_nonlock_kernel_u(*self).thread_map.dom().contains(stable_thread_ptr)) by { reveal(kernel_k_to_nonlock_kernel_u); };
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        reveal(kernel_k_to_nonlock_kernel_u); reveal(process_pagetable_match); reveal(process_iommu_table_match);
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*self)) by {
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
            kernel_cpu_nonlock_fields_unchanged_for_equal(self.cpu_arr, self.cpu_arr);
            kernel_process_nonlock_fields_unchanged_for_equal(self.prc_mp, self.prc_mp);
            kernel_thread_nonlock_fields_unchanged_for_equal(self.thr_mp, self.thr_mp);
            kernel_pagetable_nonlock_fields_unchanged_for_equal(self.pt_mp, self.pt_mp);
            kernel_iommu_table_nonlock_fields_unchanged_for_equal(self.it_mp, self.it_mp);
        };
        assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, self.ep_mp)) by { broadcast use kernel_endpoint_nonlock_fields_unchanged_for_equal; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
    }

}
}
