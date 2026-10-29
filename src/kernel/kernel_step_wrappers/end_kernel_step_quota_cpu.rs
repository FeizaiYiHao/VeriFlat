use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal};
use crate::*;
#[cfg(verus_keep_ghost)]
use super::boundary::{
    kernel_cpu_offline_request_changed_implies_u_step, kernel_cpu_online_changed_implies_u_step, kernel_cpu_went_off_fields_implies_u_step,
    kernel_process2thread_quota_2m_changed_implies_u_step, kernel_process2thread_quota_4k_changed_implies_u_step,
    kernel_process_quota_2m_changed_implies_u_step, kernel_process_quota_4k_changed_implies_u_step,
};

verus! {
impl KernelSteps {
    pub proof fn end_kernel_step_process_quota_4k_changed(tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, delta: int)
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_process_quota_4k_changed(&old(self).snapshot_k(), krnl, cpu_id, process_ptr, container_ptr, delta),
            forall|p: RwLockContainerPtr| #![trigger krnl.ctn_mp.spec_index(p)] old(self).snapshot_k().ctn_mp.dom().contains(p) ==> krnl.ctn_mp.spec_index(p).lock_process_owner_u() == old(self).snapshot_k().ctn_mp.spec_index(p).lock_process_owner_u(),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).snapshot_k() == *krnl,
            kernel_u_only_process_quota_4k_changed(kernel_k_to_kernel_u(old(self).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, container_ptr, delta),
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
        hide(kernel_k_user_projection);
        reveal(kernel_u_only_process_quota_4k_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.container_map.spec_index(container_ptr).lock_state is Unlocked
            &&& pre_u.process_map.spec_index(process_ptr).lock_state is Unlocked
        }) by {
            reveal(kernel_process_quota_4k_changed); kernel_cpu_projection_at(&self.snapshot_k(), cpu_id);
            kernel_container_projection_at(&self.snapshot_k(), container_ptr); kernel_process_projection_at(&self.snapshot_k(), process_ptr);
        };
        assert(kernel_u_only_process_quota_4k_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, container_ptr, delta)) by {
            kernel_process_quota_4k_changed_implies_u_step(&self.snapshot_k(), krnl, cpu_id, process_ptr, container_ptr, delta);
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
            final(self).snapshot_k() == *krnl,
            kernel_u_only_process2thread_quota_4k_changed(kernel_k_to_kernel_u(old(self).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, thread_ptr, delta),
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
        hide(kernel_k_user_projection);
        reveal(kernel_u_only_process2thread_quota_4k_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.process_map.spec_index(process_ptr).lock_state is Unlocked
            &&& pre_u.thread_map.spec_index(thread_ptr).lock_state is Unlocked
        }) by {
            reveal(kernel_process2thread_quota_4k_changed); kernel_cpu_projection_at(&self.snapshot_k(), cpu_id); kernel_process_projection_at(&self.snapshot_k(), process_ptr);
            kernel_thread_projection_at(&self.snapshot_k(), thread_ptr);
        };
        assert(kernel_u_only_process2thread_quota_4k_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, thread_ptr, delta)) by {
            kernel_process2thread_quota_4k_changed_implies_u_step(&self.snapshot_k(), krnl, cpu_id, process_ptr, thread_ptr, delta);
            reveal(kernel_k_to_kernel_u);
        };
        self.end_kernel_step_raw(krnl, lctx);
    }

    pub proof fn end_kernel_step_process_quota_2m_changed(tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, delta: int)
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_process_quota_2m_changed(&old(self).snapshot_k(), krnl, cpu_id, process_ptr, container_ptr, delta),
            forall|p: RwLockContainerPtr| #![trigger krnl.ctn_mp.spec_index(p)] old(self).snapshot_k().ctn_mp.dom().contains(p) ==> krnl.ctn_mp.spec_index(p).lock_process_owner_u() == old(self).snapshot_k().ctn_mp.spec_index(p).lock_process_owner_u(),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).snapshot_k() == *krnl,
            kernel_u_only_process_quota_2m_changed(kernel_k_to_kernel_u(old(self).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, container_ptr, delta),
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
        hide(kernel_k_user_projection);
        reveal(kernel_u_only_process_quota_2m_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.container_map.spec_index(container_ptr).lock_state is Unlocked
            &&& pre_u.process_map.spec_index(process_ptr).lock_state is Unlocked
        }) by {
            reveal(kernel_process_quota_2m_changed); kernel_cpu_projection_at(&self.snapshot_k(), cpu_id);
            kernel_container_projection_at(&self.snapshot_k(), container_ptr); kernel_process_projection_at(&self.snapshot_k(), process_ptr);
        };
        assert(kernel_u_only_process_quota_2m_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, container_ptr, delta)) by {
            kernel_process_quota_2m_changed_implies_u_step(&self.snapshot_k(), krnl, cpu_id, process_ptr, container_ptr, delta);
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
            final(self).snapshot_k() == *krnl,
            kernel_u_only_process2thread_quota_2m_changed(kernel_k_to_kernel_u(old(self).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, thread_ptr, delta),
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
        hide(kernel_k_user_projection);
        reveal(kernel_u_only_process2thread_quota_2m_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.process_map.spec_index(process_ptr).lock_state is Unlocked
            &&& pre_u.thread_map.spec_index(thread_ptr).lock_state is Unlocked
        }) by {
            reveal(kernel_process2thread_quota_2m_changed); kernel_cpu_projection_at(&self.snapshot_k(), cpu_id); kernel_process_projection_at(&self.snapshot_k(), process_ptr);
            kernel_thread_projection_at(&self.snapshot_k(), thread_ptr);
        };
        assert(kernel_u_only_process2thread_quota_2m_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, thread_ptr, delta)) by {
            kernel_process2thread_quota_2m_changed_implies_u_step(&self.snapshot_k(), krnl, cpu_id, process_ptr, thread_ptr, delta);
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
            forall|p: RwLockContainerPtr| #![trigger krnl.ctn_mp.spec_index(p)] old(self).snapshot_k().ctn_mp.dom().contains(p) ==> krnl.ctn_mp.spec_index(p).lock_process_owner_u() == old(self).snapshot_k().ctn_mp.spec_index(p).lock_process_owner_u(),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).snapshot_k() == *krnl,
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
        hide(kernel_k_user_projection);
        reveal(kernel_u_cpu_offline_request_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            let owner = pre_u.cpu_array[cpu_id as int].owning_container;
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.container_map[container_ptr].cpu_set_lock is Unlocked
            &&& owner == self.snapshot_k().cpu_arr.spec_index(cpu_id).value.view().view().owning_container
            &&& owner != container_ptr ==> pre_u.container_map[owner].lock_state is Unlocked
        }) by {
            reveal(kernel_cpu_offline_request_changed); kernel_cpu_projection_at(&self.snapshot_k(), cpu_id);
            if self.snapshot_k().ctn_mp.dom().contains(container_ptr) { kernel_container_projection_at(&self.snapshot_k(), container_ptr); }
            if self.snapshot_k().ctn_mp.dom().contains(self.snapshot_k().cpu_arr.spec_index(cpu_id).value.view().view().owning_container) { kernel_container_projection_at(&self.snapshot_k(), self.snapshot_k().cpu_arr.spec_index(cpu_id).value.view().view().owning_container); }
        };
        assert(kernel_u_cpu_offline_request_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, container_ptr, target)) by {
            kernel_cpu_offline_request_changed_implies_u_step(&self.snapshot_k(), krnl, cpu_id, container_ptr, target);
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
            forall|p: RwLockContainerPtr| #![trigger krnl.ctn_mp.spec_index(p)] old(self).snapshot_k().ctn_mp.dom().contains(p) ==> krnl.ctn_mp.spec_index(p).lock_process_owner_u() == old(self).snapshot_k().ctn_mp.spec_index(p).lock_process_owner_u(),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).snapshot_k() == *krnl,
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
        hide(kernel_k_user_projection);
        reveal(kernel_u_cpu_online_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            let owner = pre_u.cpu_array[cpu_id as int].owning_container;
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.cpu_array[target as int].lock_state is Unlocked
            &&& pre_u.container_map[container_ptr].cpu_set_lock is Unlocked
            &&& owner == self.snapshot_k().cpu_arr.spec_index(cpu_id).value.view().view().owning_container
            &&& owner != container_ptr ==> pre_u.container_map[owner].lock_state is Unlocked
        }) by {
            reveal(kernel_cpu_online_changed); kernel_cpu_projection_at(&self.snapshot_k(), cpu_id); kernel_cpu_projection_at(&self.snapshot_k(), target);
            if self.snapshot_k().ctn_mp.dom().contains(container_ptr) { kernel_container_projection_at(&self.snapshot_k(), container_ptr); }
            if self.snapshot_k().ctn_mp.dom().contains(self.snapshot_k().cpu_arr.spec_index(cpu_id).value.view().view().owning_container) { kernel_container_projection_at(&self.snapshot_k(), self.snapshot_k().cpu_arr.spec_index(cpu_id).value.view().view().owning_container); }
        };
        assert(kernel_u_cpu_online_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, container_ptr, target)) by {
            kernel_cpu_online_changed_implies_u_step(&self.snapshot_k(), krnl, cpu_id, container_ptr, target);
            reveal(kernel_k_to_kernel_u);
        };
        self.end_kernel_step_raw(krnl, lctx);
    }

    /// Records the attach step of `syscall_pci_attach_dma`: every lock is released again, only the context entry of
    /// `(bus, device, function)` now points at `root`, and the caller's IOMMU table without a DID adopts the
    /// function's candidate DID.
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
            old(self).snapshot_k().it_mp.spec_index(old(self).snapshot_k().prc_mp.spec_index(process_ptr).view().iommu_table->Some_0).locking_thread() is None,
            old(self).snapshot_k().prc_mp.spec_index(process_ptr).view_ghost().owned_pci_functions.view().contains((bus, device, function)),
            pci_bdf_valid(bus, device, function),
            old(self).snapshot_k().irt.view().spec_index_iommu_root(bus, device, function) is None,
            kernel_pagetable_nonlock_fields_unchanged(old(self).snapshot_k().pt_mp, old(self).snapshot_k().pt_lower.view(), krnl.pt_mp, krnl.pt_lower.view()),
            kernel_cpu_nonlock_fields_unchanged(old(self).snapshot_k().cpu_arr, krnl.cpu_arr),
            kernel_process_nonlock_fields_unchanged(old(self).snapshot_k().prc_mp, krnl.prc_mp),
            kernel_thread_nonlock_fields_unchanged(old(self).snapshot_k().thr_mp, krnl.thr_mp),
            krnl.dflt_pt == old(self).snapshot_k().dflt_pt,
            krnl.it_mp.dom() == old(self).snapshot_k().it_mp.dom(),
            forall|p: RwLockPageTableRoot| #![trigger krnl.it_mp.spec_index(p)]
                old(self).snapshot_k().it_mp.dom().contains(p) ==> {
                    let table = old(self).snapshot_k().prc_mp.spec_index(process_ptr).view().iommu_table->Some_0;
                    let before = old(self).snapshot_k().it_mp.spec_index(p).view();
                    let after = krnl.it_mp.spec_index(p).view();
                    &&& after.did == if p != table { before.did } else if before.did is Some { before.did } else { Some(pci_bdf_did(bus, device, function)) }
                    &&& after.mapping_4k().filter_keys(|va: VAddr| after.mapping_4k().spec_index(va).present) == before.mapping_4k().filter_keys(|va: VAddr| before.mapping_4k().spec_index(va).present)
                    &&& after.mapping_2m().filter_keys(|va: VAddr| after.mapping_2m().spec_index(va).present) == before.mapping_2m().filter_keys(|va: VAddr| before.mapping_2m().spec_index(va).present)
                    &&& after.mapping_1g().filter_keys(|va: VAddr| after.mapping_1g().spec_index(va).present) == before.mapping_1g().filter_keys(|va: VAddr| before.mapping_1g().spec_index(va).present)
                },
            kernel_endpoint_nonlock_fields_unchanged(old(self).snapshot_k().ep_mp, krnl.ep_mp),
            krnl.irt.view().owners() == old(self).snapshot_k().irt.view().owners(),
            krnl.irt.view().iommu_roots() == seq3_update(old(self).snapshot_k().irt.view().iommu_roots(), bus as int, device as int, function as int, Some(root)),
            krnl.cpu_tlb.view() == old(self).snapshot_k().cpu_tlb.view(),
            krnl.iommu_tlb.view() == old(self).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(self).snapshot_k(), krnl),
            krnl.cpu_op.view().view() == old(self).snapshot_k().cpu_op.view().view(),
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
            final(self).snapshot_k() == *krnl,
            kernel_u_pci_attach_changed(kernel_k_to_kernel_u(old(self).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, bus, device, function),
            kernel_k_to_kernel_u(old(self).snapshot_k()).cpu_array[cpu_id as int].lock_state is Unlocked,
            kernel_k_to_kernel_u(old(self).snapshot_k()).cpu_array[cpu_id as int].current_process == Some(process_ptr),
            kernel_k_to_kernel_u(old(self).snapshot_k()).process_map[process_ptr].lock_state is Unlocked,
            kernel_k_to_kernel_u(old(self).snapshot_k()).process_map[process_ptr].iommu_table->Some_0.lock_state is Unlocked,
    {
        reveal(kernel_u_pci_attach_changed);
        use_type_invariant(&*self);
        let snap = self.snapshot_k();
        let mid = KernelK { irt: krnl.irt, it_mp: krnl.it_mp, ..snap };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&mid, krnl)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged); };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&mid, krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
        kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&mid, krnl);
        assert({
            let pre_u = kernel_k_to_kernel_u(snap);
            let attached = seq3_update(pre_u.iommu_root_table.attached, bus as int, device as int, function as int, true);
            let process = pre_u.process_map[process_ptr];
            let table = process.iommu_table->Some_0;
            let did = match table.did { Some(did) => did, None => pci_bdf_did(bus, device, function) };
            &&& kernel_k_to_kernel_u(mid) == (KernelU {
                process_map: pre_u.process_map.insert(process_ptr, ProcessU { iommu_table: Some(PageTableU { did: Some(did), ..table }), ..process }),
                iommu_root_table: IommuRootTableU { attached, ..pre_u.iommu_root_table }, ..pre_u
            })
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.cpu_array[cpu_id as int].state is Running
            &&& pre_u.cpu_array[cpu_id as int].current_process == Some(process_ptr)
            &&& pre_u.process_map.dom().contains(process_ptr)
            &&& pre_u.process_map[process_ptr].lock_state is Unlocked
            &&& !pre_u.process_map[process_ptr].killed
            &&& pre_u.process_map[process_ptr].owned_pci_functions.contains((bus, device, function))
            &&& pre_u.process_map[process_ptr].iommu_table is Some
            &&& pre_u.process_map[process_ptr].iommu_table->Some_0.lock_state is Unlocked
            &&& !pre_u.iommu_root_table.attached[bus as int][device as int][function as int]
        }) by {
            reveal(IommuRootTable::user_view); kernel_u_domains_projection(&snap); kernel_u_domains_projection(&mid);
            kernel_cpu_projection_at(&snap, cpu_id); kernel_process_projection_at(&snap, process_ptr);
            let pre_u = kernel_k_to_kernel_u(snap);
            let mid_u = kernel_k_to_kernel_u(mid);
            let attached = seq3_update(pre_u.iommu_root_table.attached, bus as int, device as int, function as int, true);
            assert_seqs_equal!(mid_u.iommu_root_table.attached == attached, b => {
                assert_seqs_equal!(mid_u.iommu_root_table.attached[b] == attached[b], d => {
                    assert_seqs_equal!(mid_u.iommu_root_table.attached[b][d] == attached[b][d], f => {});
                });
            });
            assert_seqs_equal!(mid_u.cpu_array == pre_u.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(&snap, i as usize); kernel_cpu_projection_at(&mid, i as usize); } });
            assert_maps_equal!(mid_u.container_map, pre_u.container_map, c => { if snap.ctn_mp.dom().contains(c) { kernel_container_projection_at(&snap, c); kernel_container_projection_at(&mid, c); } });
            let process = pre_u.process_map[process_ptr];
            let table = process.iommu_table->Some_0;
            let did = match table.did { Some(did) => did, None => pci_bdf_did(bus, device, function) };
            reveal(kernel_process_nonlock_fields_unchanged); process_iommu_table_match_process_at(krnl.prc_mp, krnl.it_mp, process_ptr);
            assert_maps_equal!(mid_u.process_map, pre_u.process_map.insert(process_ptr, ProcessU { iommu_table: Some(PageTableU { did: Some(did), ..table }), ..process }), p => {
                if snap.prc_mp.dom().contains(p) { kernel_process_projection_at(&snap, p); kernel_process_projection_at(&mid, p); process_iommu_table_match_process_at(krnl.prc_mp, krnl.it_mp, p); }
            });
            assert_maps_equal!(mid_u.thread_map, pre_u.thread_map, t => { if snap.thr_mp.dom().contains(t) { kernel_thread_projection_at(&snap, t); kernel_thread_projection_at(&mid, t); } });
            assert_maps_equal!(mid_u.endpoint_map, pre_u.endpoint_map, e => { if snap.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(&snap, e); kernel_endpoint_projection_at(&mid, e); } });
        };
        self.end_kernel_step_raw(krnl, lctx);
    }

    pub proof fn end_kernel_step_cpu_went_off(tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, regs: Registers, flushed_default_pcid: bool)
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_cpu_went_off_fields(&old(self).snapshot_k(), krnl, cpu_id, regs, flushed_default_pcid),
            forall|p: RwLockContainerPtr| #![trigger krnl.ctn_mp.spec_index(p)] old(self).snapshot_k().ctn_mp.dom().contains(p) ==> krnl.ctn_mp.spec_index(p).lock_process_owner_u() == old(self).snapshot_k().ctn_mp.spec_index(p).lock_process_owner_u(),
            // The snapshot write-holds `cpu_id` for this section; the went-off step releases that hold.
            old(self).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is Write,
            old(self).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread()->Write_thread_id == lctx.thread_id(),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).snapshot_k() == *krnl,
            kernel_u_cpu_went_off_changed(kernel_k_to_kernel_u(old(self).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, regs, flushed_default_pcid),
            {
                let old_u = kernel_k_to_kernel_u(old(self).snapshot_k());
                let cpu = old_u.cpu_array[cpu_id as int];
                &&& cpu.lock_state is WriteLocked
                &&& old_u.container_map[cpu.owning_container].cpu_set_lock is Unlocked
                &&& (cpu.current_thread is Some ==> old_u.thread_map[cpu.current_thread.unwrap()].lock_state is Unlocked && old_u.process_map[cpu.current_process.unwrap()].lock_state is Unlocked)
            },
    {
        hide(kernel_k_user_projection);
        reveal(kernel_u_cpu_went_off_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            let cpu = pre_u.cpu_array[cpu_id as int];
            &&& cpu.lock_state is WriteLocked
            &&& pre_u.container_map[cpu.owning_container].cpu_set_lock is Unlocked
            &&& (cpu.current_thread is Some ==> pre_u.thread_map[cpu.current_thread.unwrap()].lock_state is Unlocked && pre_u.process_map[cpu.current_process.unwrap()].lock_state is Unlocked)
        }) by {
            reveal(kernel_cpu_went_off_fields); kernel_cpu_projection_at(&self.snapshot_k(), cpu_id);
            if self.snapshot_k().ctn_mp.dom().contains(self.snapshot_k().cpu_arr.spec_index(cpu_id).value.view().view().owning_container) { kernel_container_projection_at(&self.snapshot_k(), self.snapshot_k().cpu_arr.spec_index(cpu_id).value.view().view().owning_container); }
            if let Some(t) = self.snapshot_k().cpu_arr.spec_index(cpu_id).value.view().view().current_thread { if self.snapshot_k().thr_mp.dom().contains(t) { kernel_thread_projection_at(&self.snapshot_k(), t); } }
            if let Some(p) = self.snapshot_k().cpu_arr.spec_index(cpu_id).value.view().view().current_process { if self.snapshot_k().prc_mp.dom().contains(p) { kernel_process_projection_at(&self.snapshot_k(), p); } }
        };
        assert(kernel_u_cpu_went_off_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, regs, flushed_default_pcid)) by {
            kernel_cpu_went_off_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, regs, flushed_default_pcid);
            reveal(kernel_k_to_kernel_u);
        };
        self.end_kernel_step_raw(krnl, lctx);
    }
}
} // verus!
