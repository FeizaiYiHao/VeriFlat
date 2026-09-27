use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal};
use crate::*;
use super::implementation::create_thread_from_staged_page::kernel_u_new_thread_changed;

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
            broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
        };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&self.snapshot_k(), krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
    }

    /// Strict stuttering boundary: the premises mention only K fields and lock modes.
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
                krnl.ctn_mp.dom().contains(p) && old(self).snapshot_k().ctn_mp.dom().contains(p) ==> krnl.ctn_mp.spec_index(p).lock_state_u() == old(self).snapshot_k().ctn_mp.spec_index(p).lock_state_u(),
            forall|p: RwLockProcessPtr| #![trigger krnl.prc_mp.spec_index(p)]
                krnl.prc_mp.dom().contains(p) && old(self).snapshot_k().prc_mp.dom().contains(p) ==> krnl.prc_mp.spec_index(p).lock_state_u() == old(self).snapshot_k().prc_mp.spec_index(p).lock_state_u(),
            forall|p: RwLockPageTableRoot| #![trigger krnl.pt_mp.spec_index(p)]
                krnl.pt_mp.dom().contains(p) && old(self).snapshot_k().pt_mp.dom().contains(p) ==> krnl.pt_mp.spec_index(p).lock_state_u() == old(self).snapshot_k().pt_mp.spec_index(p).lock_state_u(),
            forall|p: RwLockPageTableRoot| #![trigger krnl.it_mp.spec_index(p)]
                krnl.it_mp.dom().contains(p) && old(self).snapshot_k().it_mp.dom().contains(p) ==> krnl.it_mp.spec_index(p).lock_state_u() == old(self).snapshot_k().it_mp.spec_index(p).lock_state_u(),
            forall|p: RwLockThreadPtr| #![trigger krnl.thr_mp.spec_index(p)]
                krnl.thr_mp.dom().contains(p) && old(self).snapshot_k().thr_mp.dom().contains(p) ==> krnl.thr_mp.spec_index(p).lock_state_u() == old(self).snapshot_k().thr_mp.spec_index(p).lock_state_u(),
            forall|p: RwLockEndpointPtr| #![trigger krnl.ep_mp.spec_index(p)]
                krnl.ep_mp.dom().contains(p) && old(self).snapshot_k().ep_mp.dom().contains(p) ==> krnl.ep_mp.spec_index(p).lock_state_u() == old(self).snapshot_k().ep_mp.spec_index(p).lock_state_u(),
            forall|i: CpuId| #![trigger krnl.cpu_arr.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> krnl.cpu_arr.spec_index(i).value.lock_state_u() == old(self).snapshot_k().cpu_arr.spec_index(i).value.lock_state_u(),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view(),
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
        *self = KernelSteps { steps: self.steps, snapshot_k: *krnl, snapshot_u: self.snapshot_u };
        assert(kernel_endpoint_nonlock_fields_unchanged(self.snapshot_k().ep_mp, krnl.ep_mp)) by { broadcast use kernel_endpoint_nonlock_fields_unchanged_for_equal; };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&self.snapshot_k(), krnl)) by {
            broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
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
            final(self).view() == record_user_view_change(old(self).view(), old(self).snapshot_u(), kernel_k_to_kernel_u(*krnl)),
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
        tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, process_ptr: RwLockProcessPtr,
        staging_thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, new_thread_ptr: RwLockThreadPtr, initial_regs: Registers,
        initial_endpoint: Option<RwLockEndpointPtr>,
    )
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_new_thread_fields(&old(self).snapshot_k(), krnl, process_ptr, staging_thread_ptr, container_ptr, new_thread_ptr, initial_regs, initial_endpoint),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == record_user_view_change(old(self).view(), old(self).snapshot_u(), kernel_k_to_kernel_u(*krnl)),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            final(self).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
            final(self).nonlock_view().last().new_u.process_map.spec_index(process_ptr).owned_threads.last() == new_thread_ptr,
            kernel_u_new_thread_changed(final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u,
                process_ptr, staging_thread_ptr, container_ptr, new_thread_ptr, initial_regs, initial_endpoint),
    {
        use_type_invariant(&*self);
        assert(kernel_u_new_thread_changed(self.nonlock_snapshot_u(), kernel_k_to_nonlock_kernel_u(*krnl),
            process_ptr, staging_thread_ptr, container_ptr, new_thread_ptr, initial_regs, initial_endpoint)) by {
            kernel_new_thread_fields_implies_u_step(&self.snapshot_k(), krnl, process_ptr, staging_thread_ptr, container_ptr, new_thread_ptr, initial_regs, initial_endpoint);
        };
        assert(self.nonlock_snapshot_u() != kernel_k_to_nonlock_kernel_u(*krnl)
            && kernel_k_to_nonlock_kernel_u(*krnl).process_map.spec_index(process_ptr).owned_threads.last() == new_thread_ptr) by { reveal(kernel_u_new_thread_changed); };
        self.end_kernel_step_raw(krnl, lctx);
    }

    /// `end_kernel_step_new_thread` for a thread funded by the live thread running on `cpu_id` inside its own live
    /// process and container, whose descriptor at `endpoint_index` names the optional initial endpoint.
    pub proof fn end_kernel_step_new_thread_on_cpu(
        tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
        staging_thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, new_thread_ptr: RwLockThreadPtr, initial_regs: Registers,
        initial_endpoint: Option<RwLockEndpointPtr>, endpoint_index: EndpointIdx,
    )
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_new_thread_fields(&old(self).snapshot_k(), krnl, process_ptr, staging_thread_ptr, container_ptr, new_thread_ptr, initial_regs, initial_endpoint),
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
            final(self).view() == record_user_view_change(old(self).view(), old(self).snapshot_u(), kernel_k_to_kernel_u(*krnl)),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            final(self).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
            kernel_u_new_thread_changed(final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u,
                process_ptr, staging_thread_ptr, container_ptr, new_thread_ptr, initial_regs, initial_endpoint),
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
                &&& (initial_endpoint is Some ==> edp_idx_valid(endpoint_index) && thread.endpoint_descriptors[endpoint_index as int] == initial_endpoint)
            },
    {
        let pre_u = self.nonlock_snapshot_u();
        self.end_kernel_step_new_thread(krnl, lctx, process_ptr, staging_thread_ptr, container_ptr, new_thread_ptr, initial_regs, initial_endpoint);
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
            &&& (initial_endpoint is Some ==> edp_idx_valid(endpoint_index) && thread.endpoint_descriptors[endpoint_index as int] == initial_endpoint)
        }) by { reveal(kernel_k_to_nonlock_kernel_u); reveal(kernel_new_thread_fields); };
    }

    #[verifier::spinoff_prover]
    pub proof fn end_kernel_step_thread_state_changed(
        tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, thread_ptr: RwLockThreadPtr,
        old_state: ThreadState, new_state: ThreadState,
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
            final(self).view() == record_user_view_change(old(self).view(), old(self).snapshot_u(), kernel_k_to_kernel_u(*krnl)),
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            final(self).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
    {
        use_type_invariant(&*self);
        assert(self.nonlock_snapshot_u().thread_map.spec_index(thread_ptr).syscall_progress != kernel_k_to_nonlock_kernel_u(*krnl).thread_map.spec_index(thread_ptr).syscall_progress) by { reveal(kernel_k_to_nonlock_kernel_u); };
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
            final(self).view() == record_user_view_change(old(self).view(), old(self).snapshot_u(), kernel_k_to_kernel_u(*krnl)),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            final(self).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
            kernel_u_context_switch_changed(
                final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u, cpu_id, next_thread, entry_regs, flushed_pcid,
            ),
    {
        use_type_invariant(&*self);
        let pre_u = self.nonlock_snapshot_u();
        let post_u = kernel_k_to_nonlock_kernel_u(*krnl);
        assert(kernel_u_context_switch_changed(pre_u, post_u, cpu_id, next_thread, entry_regs, flushed_pcid)) by {
            reveal(kernel_context_switch_fields); reveal(kernel_k_to_nonlock_kernel_u);
            reveal(kernel_endpoint_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged);
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
        self.end_kernel_step_raw(krnl, lctx);
    }

    #[verifier::spinoff_prover]
    pub proof fn end_kernel_step_ipc_block(
        tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, thread_ptr: RwLockThreadPtr,
        endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, regs: Registers,
        flushed_default_pcid: bool,
    )
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_ipc_block_fields(&old(self).snapshot_k(), krnl, cpu_id, thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, regs, flushed_default_pcid),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == record_user_view_change(old(self).view(), old(self).snapshot_u(), kernel_k_to_kernel_u(*krnl)),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            final(self).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
            kernel_u_ipc_block_changed(
                final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u, cpu_id, thread_ptr, endpoint_ptr,
                endpoint_index, waiting_state, payload, regs, flushed_default_pcid,
            ),
    {
        use_type_invariant(&*self);
        let pre_u = self.nonlock_snapshot_u();
        let post_u = kernel_k_to_nonlock_kernel_u(*krnl);
        assert(kernel_u_ipc_block_changed(pre_u, post_u, cpu_id, thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, regs, flushed_default_pcid)) by {
            reveal(kernel_ipc_block_fields); reveal(kernel_k_to_nonlock_kernel_u);
            reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(kernel_process_nonlock_fields_unchanged);
            let cpu = pre_u.cpu_array[cpu_id as int];
            let thread = pre_u.thread_map.spec_index(thread_ptr);
            let endpoint = pre_u.endpoint_map.spec_index(endpoint_ptr);
            assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { reveal(IommuRootTable::user_view); };
            assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU {
                state: CpuState::Idle, current_process: None, current_thread: None, ..cpu
            }));
            assert_maps_equal!(post_u.container_map, pre_u.container_map, c => {});
            assert_maps_equal!(post_u.process_map, pre_u.process_map, p => {
                reveal(process_pagetable_match); reveal(process_iommu_table_match);
                reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
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
        };
        self.end_kernel_step_raw(krnl, lctx);
    }

    #[verifier::spinoff_prover]
    pub proof fn end_kernel_step_ipc_rendezvous(
        tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, caller_thread_ptr: RwLockThreadPtr,
        endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, waiting_state: ThreadState, peer_thread_ptr: RwLockThreadPtr,
        peer_result: RetValueType, cpu_transfer: Option<(CpuId, RwLockThreadPtr)>,
    )
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_ipc_rendezvous_fields(
                &old(self).snapshot_k(), krnl, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result,
                cpu_transfer,
            ),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == record_user_view_change(old(self).view(), old(self).snapshot_u(), kernel_k_to_kernel_u(*krnl)),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            final(self).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
            kernel_u_ipc_rendezvous_changed(
                final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u, cpu_id, caller_thread_ptr, endpoint_ptr,
                endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer,
            ),
    {
        use_type_invariant(&*self);
        let pre_u = self.nonlock_snapshot_u();
        let post_u = kernel_k_to_nonlock_kernel_u(*krnl);
        assert(kernel_u_ipc_rendezvous_changed(
            pre_u, post_u, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer,
        )) by {
            reveal(kernel_ipc_rendezvous_fields); reveal(kernel_k_to_nonlock_kernel_u); reveal(kernel_process_nonlock_fields_unchanged);
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
            }), c => {});
            assert_maps_equal!(post_u.process_map, pre_u.process_map, p => {
                reveal(process_pagetable_match); reveal(process_iommu_table_match);
                reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
            });
            assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(peer_thread_ptr, ThreadU {
                state: ThreadState::SCHEDULED, blocking_endpoint_ptr: None, ipc_payload: IPCPayLoad::Empty, error_code: Some(peer_result), ..peer
            }), t => {});
            assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map.insert(endpoint_ptr, EndpointU { queue: endpoint.queue.skip(1), ..endpoint }), e => {});
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
            final(self).view() == record_user_view_change(old(self).view(), old(self).snapshot_u(), kernel_k_to_kernel_u(*krnl)),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            final(self).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
            kernel_u_only_process_quota_4k_changed(
                final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u, cpu_id, process_ptr, container_ptr, delta,
            ),
    {
        use_type_invariant(&*self);
        kernel_process_quota_4k_changed_implies_u_step(&self.snapshot_k(), krnl, cpu_id, process_ptr, container_ptr, delta);
        self.end_kernel_step_raw(krnl, lctx);
    }

}

pub broadcast proof fn kernel_pagetable_nonlock_fields_unchanged_for_equal(pre: PageTableLockedMap, post: PageTableLockedMap)
    requires pre == post,
    ensures #[trigger] kernel_pagetable_nonlock_fields_unchanged(pre, post),
{
    reveal(kernel_pagetable_nonlock_fields_unchanged);
}

pub broadcast proof fn kernel_pagetable_nonlock_fields_unchanged_transitive(
    pre: PageTableLockedMap, middle: PageTableLockedMap, post: PageTableLockedMap,
)
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

pub broadcast proof fn kernel_iommu_table_nonlock_fields_unchanged_transitive(
    pre: IommuTableLockedMap, middle: IommuTableLockedMap, post: IommuTableLockedMap,
)
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

pub broadcast proof fn kernel_process_nonlock_fields_unchanged_transitive(
    pre: ProcessLockedMap, middle: ProcessLockedMap, post: ProcessLockedMap,
)
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
    broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
    reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
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
    reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
    reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
    reveal(kernel_endpoint_nonlock_fields_unchanged);
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
        *post == (KernelK { pg_arr: post.pg_arr, thr_mp: post.thr_mp, allc_4k_mp: post.allc_4k_mp, ..*pre }),
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
            post.ctn_mp.dom().contains(p) && pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).lock_state_u() == pre.ctn_mp.spec_index(p).lock_state_u(),
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
            post.prc_mp.dom().contains(p) && pre.prc_mp.dom().contains(p) ==> post.prc_mp.spec_index(p).lock_state_u() == pre.prc_mp.spec_index(p).lock_state_u(),
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
            post.pt_mp.dom().contains(p) && pre.pt_mp.dom().contains(p) ==> post.pt_mp.spec_index(p).lock_state_u() == pre.pt_mp.spec_index(p).lock_state_u(),
        forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
            post.it_mp.dom().contains(p) && pre.it_mp.dom().contains(p) ==> post.it_mp.spec_index(p).lock_state_u() == pre.it_mp.spec_index(p).lock_state_u(),
        forall|p: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(p)]
            post.thr_mp.dom().contains(p) && pre.thr_mp.dom().contains(p) ==> post.thr_mp.spec_index(p).lock_state_u() == pre.thr_mp.spec_index(p).lock_state_u(),
        forall|p: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(p)]
            post.ep_mp.dom().contains(p) && pre.ep_mp.dom().contains(p) ==> post.ep_mp.spec_index(p).lock_state_u() == pre.ep_mp.spec_index(p).lock_state_u(),
        forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> post.cpu_arr.spec_index(i).value.lock_state_u() == pre.cpu_arr.spec_index(i).value.lock_state_u(),
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
proof fn kernel_new_thread_fields_implies_u_step(
    pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, new_thread_ptr: RwLockThreadPtr, initial_regs: Registers,
    initial_endpoint: Option<RwLockEndpointPtr>,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        kernel_new_thread_fields(pre, post, process_ptr, staging_thread_ptr, container_ptr, new_thread_ptr, initial_regs, initial_endpoint),
    ensures
        kernel_u_new_thread_changed(kernel_k_to_nonlock_kernel_u(*pre), kernel_k_to_nonlock_kernel_u(*post),
        process_ptr, staging_thread_ptr, container_ptr, new_thread_ptr, initial_regs, initial_endpoint),
{
    reveal(kernel_new_thread_fields);
    reveal(kernel_k_to_nonlock_kernel_u);
    reveal(kernel_u_new_thread_changed);
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
        quota_4k: (staging.quota_4k as int - 1) as usize, ..staging
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
proof fn kernel_thread_quota_4k_changed_implies_u_step(
    pre: &KernelK, post: &KernelK, thread_ptr: RwLockThreadPtr, delta: int,
)
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
}

#[verifier::spinoff_prover]
proof fn kernel_process_quota_4k_changed_implies_u_step(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, delta: int,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        kernel_process_quota_4k_changed(pre, post, cpu_id, process_ptr, container_ptr, delta),
    ensures
        kernel_u_only_process_quota_4k_changed(
            kernel_k_to_nonlock_kernel_u(*pre), kernel_k_to_nonlock_kernel_u(*post), cpu_id, process_ptr, container_ptr, delta,
        ),
{
    reveal(kernel_process_quota_4k_changed); reveal(kernel_endpoint_nonlock_fields_unchanged);
    reveal(kernel_k_to_nonlock_kernel_u);
    let pre_u = kernel_k_to_nonlock_kernel_u(*pre);
    let post_u = kernel_k_to_nonlock_kernel_u(*post);
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
    ensures kernel_k_to_nonlock_kernel_u(*pre) != kernel_k_to_nonlock_kernel_u(*post),
{
    reveal(kernel_process_added);
    reveal(kernel_k_to_nonlock_kernel_u);
}

#[verifier::spinoff_prover]
proof fn kernel_process_4k_mapping_changed_implies_u_neq(
    pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr,
)
    requires kernel_process_4k_mapping_changed(pre, post, process_ptr, pagetable_ptr, va),
    ensures kernel_k_to_nonlock_kernel_u(*pre) != kernel_k_to_nonlock_kernel_u(*post),
{
    assert(kernel_k_to_nonlock_kernel_u(*pre).process_map.spec_index(process_ptr).pagetable.unwrap().mapping_4k.dom().contains(va) != kernel_k_to_nonlock_kernel_u(*post).process_map.spec_index(process_ptr).pagetable.unwrap().mapping_4k.dom().contains(va)) by {
        reveal(kernel_process_4k_mapping_changed); reveal(kernel_k_to_nonlock_kernel_u);
    };
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
        post.cpu_arr.spec_index(cpu_id).value.lock_state_u() == post.thr_mp.spec_index(thread_ptr).lock_state_u(),
        pre.thr_mp.dom().contains(thread_ptr),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..pre.thr_mp.spec_index(thread_ptr).view() }),
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        post.pt_mp.spec_index(pagetable_ptr).view() == pre.pt_mp.spec_index(pagetable_ptr).view(),
        post.pt_mp.spec_index(pagetable_ptr).lock_state_u() == post.thr_mp.spec_index(thread_ptr).lock_state_u(),
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
            &&& pre_u.thread_map.spec_index(thread_ptr).lock_state == pre.thr_mp.spec_index(thread_ptr).lock_state_u()
            &&& process.pagetable->Some_0.lock_state == pre.pt_mp.spec_index(pagetable_ptr).lock_state_u()
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

impl KernelK {
    pub proof fn kernel_step_boundary_nonlock_fields_unchanged(
        tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps,
    )
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
            forall|pt: RwLockPageTableRoot| #![trigger final(self).pt_mp.spec_index(pt)]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(self).cpu_tlb, old(self).cpu_arr, old(self).pcid_needflush, pt, old(self).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, final(self).pt_mp.spec_index(pt).view()),
            forall|pagetable_ptr: RwLockPageTableRoot, cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr), final(self).cpu_tlb.spec_index((cpu_id, pcid))]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)
                && index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID
                ==> {
                    let before = old(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    let after = final(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    after is Some && after.unwrap().pagetable_ptr == pagetable_ptr
                    && (before is None || before.unwrap().pagetable_ptr != pagetable_ptr
                        || single_cpu_single_pcid_tlb_subset_of_present_pagetable(old(self).cpu_tlb.spec_index((cpu_id, pcid)), old(self).pt_mp.spec_index(pagetable_ptr).view())
                        || (old(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush
                            && old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid
                            && (!final(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush || final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid)))
                    ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(self).cpu_tlb.spec_index((cpu_id, pcid)), final(self).pt_mp.spec_index(pagetable_ptr).view())
                },
            forall|cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))]
                old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))
                ==> final(self).pcid_needflush.spec_index(cpu_id, pcid) == old(self).pcid_needflush.spec_index(cpu_id, pcid),
            forall|cpu_id: CpuId|
                #![trigger old(lctx).cpu_lock_map().dom().contains(cpu_id)]
                old(lctx).cpu_lock_map().dom().contains(cpu_id)
                ==> final(self).cpu_arr.spec_index(cpu_id).view() == old(self).cpu_arr.spec_index(cpu_id).view(),
            forall|container_ptr: RwLockContainerPtr|
                #![trigger old(lctx).container_lock_map().dom().contains(container_ptr)]
                old(lctx).container_lock_map().dom().contains(container_ptr)
                ==> {
                    &&& final(self).ctn_mp.dom().contains(container_ptr)
                    &&& final(self).ctn_mp.lock_id_by_key(container_ptr) == old(self).ctn_mp.lock_id_by_key(container_ptr)
                    &&& final(self).ctn_mp.spec_index(container_ptr) == old(self).ctn_mp.spec_index(container_ptr)
                },
            forall|process_ptr: RwLockProcessPtr|
                #![trigger old(lctx).process_lock_map().dom().contains(process_ptr)]
                old(lctx).process_lock_map().dom().contains(process_ptr)
                ==> {
                    &&& final(self).prc_mp.dom().contains(process_ptr)
                    &&& final(self).prc_mp.lock_id_by_key(process_ptr) == old(self).prc_mp.lock_id_by_key(process_ptr)
                    &&& final(self).prc_mp.spec_index(process_ptr) == old(self).prc_mp.spec_index(process_ptr)
                },
            forall|thread_ptr: RwLockThreadPtr|
                #![trigger old(lctx).thread_lock_map().dom().contains(thread_ptr)]
                old(lctx).thread_lock_map().dom().contains(thread_ptr)
                ==> {
                    &&& final(self).thr_mp.dom().contains(thread_ptr)
                    &&& final(self).thr_mp.lock_id_by_key(thread_ptr) == old(self).thr_mp.lock_id_by_key(thread_ptr)
                    &&& final(self).thr_mp.spec_index(thread_ptr) == old(self).thr_mp.spec_index(thread_ptr)
                },
            forall|pagetable_ptr: RwLockPageTableRoot|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)
                ==> {
                    &&& final(self).pt_mp.dom().contains(pagetable_ptr)
                    &&& final(self).pt_mp.lock_id_by_key(pagetable_ptr) == old(self).pt_mp.lock_id_by_key(pagetable_ptr)
                    &&& final(self).pt_mp.spec_index(pagetable_ptr) == old(self).pt_mp.spec_index(pagetable_ptr)
                },
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(self))),
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

    pub proof fn kernel_step_boundary_cpu_tlb_updated(
        tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps,
        cpu_id: CpuId, pcid: Pcid, flushed: bool,
    )
        requires
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
            forall|pt: RwLockPageTableRoot| #![trigger final(self).pt_mp.spec_index(pt)]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(self).cpu_tlb, old(self).cpu_arr, old(self).pcid_needflush, pt, old(self).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, final(self).pt_mp.spec_index(pt).view()),
            forall|pagetable_ptr: RwLockPageTableRoot, cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr), final(self).cpu_tlb.spec_index((cpu_id, pcid))]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)
                && index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID
                ==> {
                    let before = old(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    let after = final(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    after is Some && after.unwrap().pagetable_ptr == pagetable_ptr
                    && (before is None || before.unwrap().pagetable_ptr != pagetable_ptr
                        || single_cpu_single_pcid_tlb_subset_of_present_pagetable(old(self).cpu_tlb.spec_index((cpu_id, pcid)), old(self).pt_mp.spec_index(pagetable_ptr).view())
                        || (old(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush
                            && old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid
                            && (!final(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush || final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid)))
                    ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(self).cpu_tlb.spec_index((cpu_id, pcid)), final(self).pt_mp.spec_index(pagetable_ptr).view())
                },
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(self))),
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
        let pre_u = steps.nonlock_snapshot_u();
        let post_u = kernel_k_to_nonlock_kernel_u(*self);
        assert(post_u == (KernelU { cpu_tlb: self.cpu_tlb.view(), ..pre_u })
            && pre_u.cpu_tlb == steps.snapshot_k().cpu_tlb.view()) by {
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
            kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(&KernelK { cpu_tlb: self.cpu_tlb, ..steps.snapshot_k() }, self);
            reveal(kernel_k_to_nonlock_kernel_u);
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
        tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps,
        container_ptr: RwLockContainerPtr, delta: int,
    )
        requires
            old(self).inv(),
            delta > 0,
            kernel_container_quota_4k_changed(&old(steps).snapshot_k(), old(self), container_ptr, delta),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(self).inv(),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(self).cpu_published[old(lctx).cpu_id() as int].view() == old(self).cpu_published[old(lctx).cpu_id() as int].view(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|pt: RwLockPageTableRoot| #![trigger final(self).pt_mp.spec_index(pt)]
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
        let pre_u = steps.nonlock_snapshot_u();
        let post_u = kernel_k_to_nonlock_kernel_u(*self);
        assert(post_u != pre_u && post_u == (KernelU {
            container_map: pre_u.container_map.insert(container_ptr, ContainerU {
                quota_4k: (pre_u.container_map.spec_index(container_ptr).quota_4k as int + delta) as usize,
                ..pre_u.container_map.spec_index(container_ptr)
            }),
            ..pre_u
        })) by {
            reveal(KernelK::inv);
            reveal(kernel_container_quota_4k_changed); reveal(kernel_endpoint_nonlock_fields_unchanged);
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
            reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
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
        tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps,
        thread_ptr: RwLockThreadPtr, delta: int,
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
            forall|pt: RwLockPageTableRoot| #![trigger final(self).pt_mp.spec_index(pt)]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(self).cpu_tlb, old(self).cpu_arr, old(self).pcid_needflush, pt, old(self).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, final(self).pt_mp.spec_index(pt).view()),
            forall|pagetable_ptr: RwLockPageTableRoot, cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr), final(self).cpu_tlb.spec_index((cpu_id, pcid))]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)
                && index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID
                ==> {
                    let before = old(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    let after = final(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    after is Some && after.unwrap().pagetable_ptr == pagetable_ptr
                    && (before is None || before.unwrap().pagetable_ptr != pagetable_ptr
                        || single_cpu_single_pcid_tlb_subset_of_present_pagetable(old(self).cpu_tlb.spec_index((cpu_id, pcid)), old(self).pt_mp.spec_index(pagetable_ptr).view())
                        || (old(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush
                            && old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid
                            && (!final(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush || final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid)))
                    ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(self).cpu_tlb.spec_index((cpu_id, pcid)), final(self).pt_mp.spec_index(pagetable_ptr).view())
                },
            forall|cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))]
                old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))
                ==> final(self).pcid_needflush.spec_index(cpu_id, pcid) == old(self).pcid_needflush.spec_index(cpu_id, pcid),
            forall|cpu_id: CpuId|
                #![trigger old(lctx).cpu_lock_map().dom().contains(cpu_id)]
                old(lctx).cpu_lock_map().dom().contains(cpu_id)
                ==> final(self).cpu_arr.spec_index(cpu_id).view() == old(self).cpu_arr.spec_index(cpu_id).view(),
            forall|container_ptr: RwLockContainerPtr|
                #![trigger old(lctx).container_lock_map().dom().contains(container_ptr)]
                old(lctx).container_lock_map().dom().contains(container_ptr)
                ==> {
                    &&& final(self).ctn_mp.dom().contains(container_ptr)
                    &&& final(self).ctn_mp.lock_id_by_key(container_ptr) == old(self).ctn_mp.lock_id_by_key(container_ptr)
                    &&& final(self).ctn_mp.spec_index(container_ptr) == old(self).ctn_mp.spec_index(container_ptr)
                },
            forall|process_ptr: RwLockProcessPtr|
                #![trigger old(lctx).process_lock_map().dom().contains(process_ptr)]
                old(lctx).process_lock_map().dom().contains(process_ptr)
                ==> {
                    &&& final(self).prc_mp.dom().contains(process_ptr)
                    &&& final(self).prc_mp.lock_id_by_key(process_ptr) == old(self).prc_mp.lock_id_by_key(process_ptr)
                    &&& final(self).prc_mp.spec_index(process_ptr) == old(self).prc_mp.spec_index(process_ptr)
                },
            forall|thread_ptr: RwLockThreadPtr|
                #![trigger old(lctx).thread_lock_map().dom().contains(thread_ptr)]
                old(lctx).thread_lock_map().dom().contains(thread_ptr)
                ==> {
                    &&& final(self).thr_mp.dom().contains(thread_ptr)
                    &&& final(self).thr_mp.lock_id_by_key(thread_ptr) == old(self).thr_mp.lock_id_by_key(thread_ptr)
                    &&& final(self).thr_mp.spec_index(thread_ptr) == old(self).thr_mp.spec_index(thread_ptr)
                },
            forall|pagetable_ptr: RwLockPageTableRoot|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)
                ==> {
                    &&& final(self).pt_mp.dom().contains(pagetable_ptr)
                    &&& final(self).pt_mp.lock_id_by_key(pagetable_ptr) == old(self).pt_mp.lock_id_by_key(pagetable_ptr)
                    &&& final(self).pt_mp.spec_index(pagetable_ptr) == old(self).pt_mp.spec_index(pagetable_ptr)
                },
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(self))),
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
            forall|pt: RwLockPageTableRoot| #![trigger final(self).pt_mp.spec_index(pt)]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(self).cpu_tlb, old(self).cpu_arr, old(self).pcid_needflush, pt, old(self).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, final(self).pt_mp.spec_index(pt).view()),
            forall|pagetable_ptr: RwLockPageTableRoot, cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr), final(self).cpu_tlb.spec_index((cpu_id, pcid))]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)
                && index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID
                ==> {
                    let before = old(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    let after = final(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    after is Some && after.unwrap().pagetable_ptr == pagetable_ptr
                    && (before is None || before.unwrap().pagetable_ptr != pagetable_ptr
                        || single_cpu_single_pcid_tlb_subset_of_present_pagetable(old(self).cpu_tlb.spec_index((cpu_id, pcid)), old(self).pt_mp.spec_index(pagetable_ptr).view())
                        || (old(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush
                            && old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid
                            && (!final(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush || final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid)))
                    ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(self).cpu_tlb.spec_index((cpu_id, pcid)), final(self).pt_mp.spec_index(pagetable_ptr).view())
                },
            forall|cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))]
                old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))
                ==> final(self).pcid_needflush.spec_index(cpu_id, pcid) == old(self).pcid_needflush.spec_index(cpu_id, pcid),
            forall|cpu_id: CpuId|
                #![trigger old(lctx).cpu_lock_map().dom().contains(cpu_id)]
                old(lctx).cpu_lock_map().dom().contains(cpu_id)
                ==> final(self).cpu_arr.spec_index(cpu_id).view() == old(self).cpu_arr.spec_index(cpu_id).view(),
            forall|container_ptr: RwLockContainerPtr|
                #![trigger old(lctx).container_lock_map().dom().contains(container_ptr)]
                old(lctx).container_lock_map().dom().contains(container_ptr)
                ==> {
                    &&& final(self).ctn_mp.dom().contains(container_ptr)
                    &&& final(self).ctn_mp.lock_id_by_key(container_ptr) == old(self).ctn_mp.lock_id_by_key(container_ptr)
                    &&& final(self).ctn_mp.spec_index(container_ptr) == old(self).ctn_mp.spec_index(container_ptr)
                },
            forall|process_ptr: RwLockProcessPtr|
                #![trigger old(lctx).process_lock_map().dom().contains(process_ptr)]
                old(lctx).process_lock_map().dom().contains(process_ptr)
                ==> {
                    &&& final(self).prc_mp.dom().contains(process_ptr)
                    &&& final(self).prc_mp.lock_id_by_key(process_ptr) == old(self).prc_mp.lock_id_by_key(process_ptr)
                    &&& final(self).prc_mp.spec_index(process_ptr) == old(self).prc_mp.spec_index(process_ptr)
                },
            forall|thread_ptr: RwLockThreadPtr|
                #![trigger old(lctx).thread_lock_map().dom().contains(thread_ptr)]
                old(lctx).thread_lock_map().dom().contains(thread_ptr)
                ==> {
                    &&& final(self).thr_mp.dom().contains(thread_ptr)
                    &&& final(self).thr_mp.lock_id_by_key(thread_ptr) == old(self).thr_mp.lock_id_by_key(thread_ptr)
                    &&& final(self).thr_mp.spec_index(thread_ptr) == old(self).thr_mp.spec_index(thread_ptr)
                },
            forall|pagetable_ptr: RwLockPageTableRoot|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)
                ==> {
                    &&& final(self).pt_mp.dom().contains(pagetable_ptr)
                    &&& final(self).pt_mp.lock_id_by_key(pagetable_ptr) == old(self).pt_mp.lock_id_by_key(pagetable_ptr)
                    &&& final(self).pt_mp.spec_index(pagetable_ptr) == old(self).pt_mp.spec_index(pagetable_ptr)
                },
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(self))),
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
        assert(kernel_k_to_nonlock_kernel_u(steps.snapshot_k()).thread_map.spec_index(thread_ptr).syscall_progress != kernel_k_to_nonlock_kernel_u(*self).thread_map.spec_index(thread_ptr).syscall_progress) by { reveal(kernel_k_to_nonlock_kernel_u); };
        steps.end_kernel_step_raw(&*self, &*lctx);
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
            forall|pt: RwLockPageTableRoot| #![trigger final(self).pt_mp.spec_index(pt)]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(self).cpu_tlb, old(self).cpu_arr, old(self).pcid_needflush, pt, old(self).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, final(self).pt_mp.spec_index(pt).view()),
            forall|pagetable_ptr: RwLockPageTableRoot, cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr), final(self).cpu_tlb.spec_index((cpu_id, pcid))]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)
                && index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID
                ==> {
                    let before = old(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    let after = final(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    after is Some && after.unwrap().pagetable_ptr == pagetable_ptr
                    && (before is None || before.unwrap().pagetable_ptr != pagetable_ptr
                        || single_cpu_single_pcid_tlb_subset_of_present_pagetable(old(self).cpu_tlb.spec_index((cpu_id, pcid)), old(self).pt_mp.spec_index(pagetable_ptr).view())
                        || (old(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush
                            && old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid
                            && (!final(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush || final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid)))
                    ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(self).cpu_tlb.spec_index((cpu_id, pcid)), final(self).pt_mp.spec_index(pagetable_ptr).view())
                },
            forall|cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))]
                old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))
                ==> final(self).pcid_needflush.spec_index(cpu_id, pcid) == old(self).pcid_needflush.spec_index(cpu_id, pcid),
            forall|cpu_id: CpuId|
                #![trigger old(lctx).cpu_lock_map().dom().contains(cpu_id)]
                old(lctx).cpu_lock_map().dom().contains(cpu_id)
                ==> final(self).cpu_arr.spec_index(cpu_id).view() == old(self).cpu_arr.spec_index(cpu_id).view(),
            forall|container_ptr: RwLockContainerPtr|
                #![trigger old(lctx).container_lock_map().dom().contains(container_ptr)]
                old(lctx).container_lock_map().dom().contains(container_ptr)
                ==> {
                    &&& final(self).ctn_mp.dom().contains(container_ptr)
                    &&& final(self).ctn_mp.lock_id_by_key(container_ptr) == old(self).ctn_mp.lock_id_by_key(container_ptr)
                    &&& final(self).ctn_mp.spec_index(container_ptr) == old(self).ctn_mp.spec_index(container_ptr)
                },
            forall|process_ptr: RwLockProcessPtr|
                #![trigger old(lctx).process_lock_map().dom().contains(process_ptr)]
                old(lctx).process_lock_map().dom().contains(process_ptr)
                ==> {
                    &&& final(self).prc_mp.dom().contains(process_ptr)
                    &&& final(self).prc_mp.lock_id_by_key(process_ptr) == old(self).prc_mp.lock_id_by_key(process_ptr)
                    &&& final(self).prc_mp.spec_index(process_ptr) == old(self).prc_mp.spec_index(process_ptr)
                },
            forall|thread_ptr: RwLockThreadPtr|
                #![trigger old(lctx).thread_lock_map().dom().contains(thread_ptr)]
                old(lctx).thread_lock_map().dom().contains(thread_ptr)
                ==> {
                    &&& final(self).thr_mp.dom().contains(thread_ptr)
                    &&& final(self).thr_mp.lock_id_by_key(thread_ptr) == old(self).thr_mp.lock_id_by_key(thread_ptr)
                    &&& final(self).thr_mp.spec_index(thread_ptr) == old(self).thr_mp.spec_index(thread_ptr)
                },
            forall|pagetable_ptr: RwLockPageTableRoot|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)
                ==> {
                    &&& final(self).pt_mp.dom().contains(pagetable_ptr)
                    &&& final(self).pt_mp.lock_id_by_key(pagetable_ptr) == old(self).pt_mp.lock_id_by_key(pagetable_ptr)
                    &&& final(self).pt_mp.spec_index(pagetable_ptr) == old(self).pt_mp.spec_index(pagetable_ptr)
                },
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(self))),
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
            forall|pt: RwLockPageTableRoot| #![trigger final(self).pt_mp.spec_index(pt)]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(self).cpu_tlb, old(self).cpu_arr, old(self).pcid_needflush, pt, old(self).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, final(self).pt_mp.spec_index(pt).view()),
            forall|pagetable_ptr: RwLockPageTableRoot, cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr), final(self).cpu_tlb.spec_index((cpu_id, pcid))]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)
                && index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID
                ==> {
                    let before = old(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    let after = final(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    after is Some && after.unwrap().pagetable_ptr == pagetable_ptr
                    && (before is None || before.unwrap().pagetable_ptr != pagetable_ptr
                        || single_cpu_single_pcid_tlb_subset_of_present_pagetable(old(self).cpu_tlb.spec_index((cpu_id, pcid)), old(self).pt_mp.spec_index(pagetable_ptr).view())
                        || (old(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush
                            && old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid
                            && (!final(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush || final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid)))
                    ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(self).cpu_tlb.spec_index((cpu_id, pcid)), final(self).pt_mp.spec_index(pagetable_ptr).view())
                },
            forall|cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))]
                old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))
                ==> final(self).pcid_needflush.spec_index(cpu_id, pcid) == old(self).pcid_needflush.spec_index(cpu_id, pcid),
            forall|cpu_id: CpuId|
                #![trigger old(lctx).cpu_lock_map().dom().contains(cpu_id)]
                old(lctx).cpu_lock_map().dom().contains(cpu_id)
                ==> final(self).cpu_arr.spec_index(cpu_id).view() == old(self).cpu_arr.spec_index(cpu_id).view(),
            forall|container_ptr: RwLockContainerPtr|
                #![trigger old(lctx).container_lock_map().dom().contains(container_ptr)]
                old(lctx).container_lock_map().dom().contains(container_ptr)
                ==> {
                    &&& final(self).ctn_mp.dom().contains(container_ptr)
                    &&& final(self).ctn_mp.lock_id_by_key(container_ptr) == old(self).ctn_mp.lock_id_by_key(container_ptr)
                    &&& final(self).ctn_mp.spec_index(container_ptr) == old(self).ctn_mp.spec_index(container_ptr)
                },
            forall|process_ptr: RwLockProcessPtr|
                #![trigger old(lctx).process_lock_map().dom().contains(process_ptr)]
                old(lctx).process_lock_map().dom().contains(process_ptr)
                ==> {
                    &&& final(self).prc_mp.dom().contains(process_ptr)
                    &&& final(self).prc_mp.lock_id_by_key(process_ptr) == old(self).prc_mp.lock_id_by_key(process_ptr)
                    &&& final(self).prc_mp.spec_index(process_ptr) == old(self).prc_mp.spec_index(process_ptr)
                },
            forall|thread_ptr: RwLockThreadPtr|
                #![trigger old(lctx).thread_lock_map().dom().contains(thread_ptr)]
                old(lctx).thread_lock_map().dom().contains(thread_ptr)
                ==> {
                    &&& final(self).thr_mp.dom().contains(thread_ptr)
                    &&& final(self).thr_mp.lock_id_by_key(thread_ptr) == old(self).thr_mp.lock_id_by_key(thread_ptr)
                    &&& final(self).thr_mp.spec_index(thread_ptr) == old(self).thr_mp.spec_index(thread_ptr)
                },
            forall|pagetable_ptr: RwLockPageTableRoot|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)
                ==> {
                    &&& final(self).pt_mp.dom().contains(pagetable_ptr)
                    &&& final(self).pt_mp.lock_id_by_key(pagetable_ptr) == old(self).pt_mp.lock_id_by_key(pagetable_ptr)
                    &&& final(self).pt_mp.spec_index(pagetable_ptr) == old(self).pt_mp.spec_index(pagetable_ptr)
                },
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(self))),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep {
                old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*old(self)),
            }),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(self)),
            final(steps).snapshot_k() == *final(self),
            final(steps).nonlock_view().last().new_u.process_map.dom().contains(process_ptr),
            kernel_k_to_nonlock_kernel_u(*final(self)).process_map.dom().contains(process_ptr),
            final(steps).nonlock_view().last().new_u.process_map.spec_index(process_ptr)
                == kernel_k_to_nonlock_kernel_u(*final(self)).process_map.spec_index(process_ptr),
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
        tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps,
        process_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr,
        stable_process_ptr: RwLockProcessPtr, stable_pagetable_ptr: RwLockPageTableRoot,
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
            forall|pt: RwLockPageTableRoot| #![trigger final(self).pt_mp.spec_index(pt)]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(self).cpu_tlb, old(self).cpu_arr, old(self).pcid_needflush, pt, old(self).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(final(self).cpu_tlb, final(self).cpu_arr, final(self).pcid_needflush, pt, final(self).pt_mp.spec_index(pt).view()),
            forall|pagetable_ptr: RwLockPageTableRoot, cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr), final(self).cpu_tlb.spec_index((cpu_id, pcid))]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)
                && index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID
                ==> {
                    let before = old(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    let after = final(self).cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
                    after is Some && after.unwrap().pagetable_ptr == pagetable_ptr
                    && (before is None || before.unwrap().pagetable_ptr != pagetable_ptr
                        || single_cpu_single_pcid_tlb_subset_of_present_pagetable(old(self).cpu_tlb.spec_index((cpu_id, pcid)), old(self).pt_mp.spec_index(pagetable_ptr).view())
                        || (old(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush
                            && old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid
                            && (!final(self).pcid_needflush.spec_index(cpu_id, pcid).view().needflush || final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid)))
                    ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(self).cpu_tlb.spec_index((cpu_id, pcid)), final(self).pt_mp.spec_index(pagetable_ptr).view())
                },
            forall|cpu_id: CpuId, pcid: Pcid|
                #![trigger old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))]
                old(lctx).pcid_needflush_lock_map().dom().contains((cpu_id, pcid))
                ==> final(self).pcid_needflush.spec_index(cpu_id, pcid) == old(self).pcid_needflush.spec_index(cpu_id, pcid),
            forall|cpu_id: CpuId|
                #![trigger old(lctx).cpu_lock_map().dom().contains(cpu_id)]
                old(lctx).cpu_lock_map().dom().contains(cpu_id)
                ==> final(self).cpu_arr.spec_index(cpu_id).view() == old(self).cpu_arr.spec_index(cpu_id).view(),
            forall|container_ptr: RwLockContainerPtr|
                #![trigger old(lctx).container_lock_map().dom().contains(container_ptr)]
                old(lctx).container_lock_map().dom().contains(container_ptr)
                ==> {
                    &&& final(self).ctn_mp.dom().contains(container_ptr)
                    &&& final(self).ctn_mp.lock_id_by_key(container_ptr) == old(self).ctn_mp.lock_id_by_key(container_ptr)
                    &&& final(self).ctn_mp.spec_index(container_ptr) == old(self).ctn_mp.spec_index(container_ptr)
                },
            forall|process_ptr: RwLockProcessPtr|
                #![trigger old(lctx).process_lock_map().dom().contains(process_ptr)]
                old(lctx).process_lock_map().dom().contains(process_ptr)
                ==> {
                    &&& final(self).prc_mp.dom().contains(process_ptr)
                    &&& final(self).prc_mp.lock_id_by_key(process_ptr) == old(self).prc_mp.lock_id_by_key(process_ptr)
                    &&& final(self).prc_mp.spec_index(process_ptr) == old(self).prc_mp.spec_index(process_ptr)
                },
            forall|thread_ptr: RwLockThreadPtr|
                #![trigger old(lctx).thread_lock_map().dom().contains(thread_ptr)]
                old(lctx).thread_lock_map().dom().contains(thread_ptr)
                ==> {
                    &&& final(self).thr_mp.dom().contains(thread_ptr)
                    &&& final(self).thr_mp.lock_id_by_key(thread_ptr) == old(self).thr_mp.lock_id_by_key(thread_ptr)
                    &&& final(self).thr_mp.spec_index(thread_ptr) == old(self).thr_mp.spec_index(thread_ptr)
                },
            forall|pagetable_ptr: RwLockPageTableRoot|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)
                ==> {
                    &&& final(self).pt_mp.dom().contains(pagetable_ptr)
                    &&& final(self).pt_mp.lock_id_by_key(pagetable_ptr) == old(self).pt_mp.lock_id_by_key(pagetable_ptr)
                    &&& final(self).pt_mp.spec_index(pagetable_ptr) == old(self).pt_mp.spec_index(pagetable_ptr)
                },
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(self))),
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
                &&& final(steps).nonlock_view().last().new_u.process_map.spec_index(process_ptr)
                    == kernel_k_to_nonlock_kernel_u(*final(self)).process_map.spec_index(process_ptr)
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
        assert(kernel_k_to_nonlock_kernel_u(*self).process_map.dom().contains(process_ptr)
            && kernel_k_to_nonlock_kernel_u(*self).process_map.dom().contains(stable_process_ptr)
            && kernel_k_to_nonlock_kernel_u(*self).thread_map.dom().contains(stable_thread_ptr)) by { reveal(kernel_k_to_nonlock_kernel_u); };
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        reveal(kernel_k_to_nonlock_kernel_u);
        reveal(process_pagetable_match);
        reveal(process_iommu_table_match);
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
