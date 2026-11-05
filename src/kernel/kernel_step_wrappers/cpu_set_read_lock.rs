use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_sets_equal};
use crate::*;

verus! {
/// Changing only the lock mode of the cpu set of the container `ctn_ptr`, with its mark kept, changes only that
/// container's cpu-set lock mode in the projection.
pub proof fn kernel_cpu_set_lock_mode_changed_implies_u_step(before: &KernelK, after: &KernelK, ctn_ptr: RwLockContainerPtr)
    requires
        container_cpu_set_wf(after.ctn_mp, after.cpu_set_mp),
        *after == (KernelK { cpu_set_mp: after.cpu_set_mp, ..*before }),
        before.ctn_mp.dom().contains(ctn_ptr),
        after.cpu_set_mp.unchanged_except(&before.cpu_set_mp, before.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set),
        after.cpu_set_mp.spec_index(before.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).being_killed()
            == before.cpu_set_mp.spec_index(before.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).being_killed(),
    ensures
        kernel_k_to_kernel_u(*before).container_map.dom().contains(ctn_ptr),
        ({
            let pre = kernel_k_to_kernel_u(*before);
            let cpu_set_lock = after.cpu_set_mp.spec_index(before.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).lock_state_u();
            kernel_k_to_kernel_u(*after) == (KernelU { container_map: pre.container_map.insert(ctn_ptr, ContainerU { cpu_set_lock, ..pre.container_map[ctn_ptr] }), ..pre })
        }),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    let cpu_set_lock = after.cpu_set_mp.spec_index(before.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).lock_state_u();
    container_cpu_set_wf_container_at(after.ctn_mp, after.cpu_set_mp, ctn_ptr);
    assert_maps_equal!(post.container_map, pre.container_map.insert(ctn_ptr, ContainerU { cpu_set_lock, ..pre.container_map[ctn_ptr] }), c => {
        if before.ctn_mp.dom().contains(c) {
            kernel_container_projection_at(before, c); kernel_container_projection_at(after, c); container_cpu_set_wf_container_at(after.ctn_mp, after.cpu_set_mp, c);
        }
    });
    kernel_cpu_array_unchanged_implies_u_cpu_array(before, after); kernel_process_maps_unchanged_implies_u_process_map(before, after);
    kernel_thread_map_unchanged_implies_u_thread_map(before, after); kernel_endpoint_map_unchanged_implies_u_endpoint_map(before, after);
}

impl KernelK {
    /// Records the section that read-locked the cpu set of the container `ctn_ptr` for the running cpu, or kept that cpu's
    /// read hold on it, and otherwise changed only cpu state, TLBs, needflush flags, and page-table ghost state that keeps
    /// every table's lock state and mappings: the recorded step adds the running cpu to that cpu set's readers in the
    /// projection and, at most, clears the TLB entry of cpu `cpu_id` for `pcid`.
    pub proof fn kernel_step_boundary_cpu_tlb_updated_cpu_set_rlocked(
        tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, cpu_id: CpuId, pcid: Pcid, flushed: bool, ctn_ptr: RwLockContainerPtr,
    )
        requires
            *old(self) == (KernelK {
                cpu_arr: old(self).cpu_arr, cpu_tlb: old(self).cpu_tlb, pcid_needflush: old(self).pcid_needflush, pt_mp: old(self).pt_mp, pt_lower: old(self).pt_lower,
                cpu_set_mp: old(self).cpu_set_mp, ..old(steps).snapshot_k()
            }),
            forall|cpu: CpuId| #![trigger old(self).cpu_arr.spec_index(cpu)] index_valid(NUM_CPUS, cpu) ==>
                old(self).cpu_arr.spec_index(cpu).value.locking_thread() == old(steps).snapshot_k().cpu_arr.spec_index(cpu).value.locking_thread(),
            old(self).pt_mp.dom() == old(steps).snapshot_k().pt_mp.dom(),
            forall|pt: RwLockPageTableRoot| #![trigger old(self).pt_mp.spec_index(pt)] old(steps).snapshot_k().pt_mp.dom().contains(pt) ==> {
                &&& old(self).pt_mp.spec_index(pt).locking_thread() == old(steps).snapshot_k().pt_mp.spec_index(pt).locking_thread()
                &&& whole_pagetable(old(self).pt_mp, old(self).pt_lower.view(), pt).mapping_4k() == whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pt).mapping_4k()
                &&& whole_pagetable(old(self).pt_mp, old(self).pt_lower.view(), pt).mapping_2m() == whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pt).mapping_2m()
                &&& whole_pagetable(old(self).pt_mp, old(self).pt_lower.view(), pt).mapping_1g() == whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pt).mapping_1g()
                &&& whole_pagetable(old(self).pt_mp, old(self).pt_lower.view(), pt).lower.pagetable_window_locks
                    == whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pt).lower.pagetable_window_locks
            },
            old(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(self)),
            index_valid(NUM_CPUS, cpu_id),
            pcid_valid(pcid),
            old(self).cpu_tlb.view() == if flushed {
                old(steps).snapshot_k().cpu_tlb.view().insert((cpu_id, pcid), old(self).cpu_tlb.spec_index((cpu_id, pcid)))
            } else { old(steps).snapshot_k().cpu_tlb.view() },
            flushed ==> cpu_tlb_within_may_cache(*old(self), cpu_id, pcid, old(self).cpu_tlb.spec_index((cpu_id, pcid)), old(self).cpu_tlb.structure_cache((cpu_id, pcid))),
            old(self).ctn_mp.dom().contains(ctn_ptr),
            old(self).cpu_set_mp.unchanged_except(&old(steps).snapshot_k().cpu_set_mp, old(self).ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set),
            old(self).cpu_set_mp.spec_index(old(self).ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).being_killed()
                == old(steps).snapshot_k().cpu_set_mp.spec_index(old(self).ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).being_killed(),
            old(self).cpu_set_mp.spec_index(old(self).ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).lock_state_u()
                == old(steps).snapshot_k().cpu_set_mp.spec_index(old(self).ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).lock_state_u().with_reader(old(lctx).cpu_id()),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==> {
                let old_u = final(steps).view()[j].old_u;
                let locked = KernelU { container_map: old_u.container_map.insert(ctn_ptr, ContainerU { cpu_set_lock: old_u.container_map[ctn_ptr].cpu_set_lock.with_reader(old(lctx).cpu_id()), ..old_u.container_map[ctn_ptr] }), ..old_u };
                final(steps).view()[j].new_u == locked || kernel_u_cpu_tlb_cleared(locked, final(steps).view()[j].new_u, pcid)
            },
            old(steps).snapshot_u().container_map.dom().contains(ctn_ptr),
            kernel_k_to_kernel_u(*old(self)) == (KernelU {
                cpu_tlb: old(self).cpu_tlb.view(),
                container_map: old(steps).snapshot_u().container_map.insert(ctn_ptr, ContainerU { cpu_set_lock: old(steps).snapshot_u().container_map[ctn_ptr].cpu_set_lock.with_reader(old(lctx).cpu_id()), ..old(steps).snapshot_u().container_map[ctn_ptr] }),
                ..old(steps).snapshot_u()
            }),
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            kernel_step_boundary_framing(*old(self), *final(self), *old(lctx)),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(self))),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).snapshot_k() == *final(self),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(self)),
            forall|p: RwLockPageTableRoot| #![trigger old(lctx).pagetable_lock_map().dom().contains(p)] typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), p, TypedLockMode::Write)
                ==> whole_pagetable(final(self).pt_mp, final(self).pt_lower.view(), p) == whole_pagetable(old(self).pt_mp, old(self).pt_lower.view(), p),
    {
        use_type_invariant(&*steps);
        let snap = steps.snapshot_k();
        let mid = KernelK { cpu_set_mp: self.cpu_set_mp, ..snap };
        let locked = KernelU {
            container_map: steps.snapshot_u().container_map.insert(ctn_ptr, ContainerU { cpu_set_lock: steps.snapshot_u().container_map[ctn_ptr].cpu_set_lock.with_reader(lctx.cpu_id()), ..steps.snapshot_u().container_map[ctn_ptr] }),
            ..steps.snapshot_u()
        };
        kernel_cpu_set_lock_mode_changed_implies_u_step(&snap, &mid, ctn_ptr); kernel_container_projection_at(&snap, ctn_ptr);
        assert(kernel_k_to_kernel_u(*self) == (KernelU { cpu_tlb: self.cpu_tlb.view(), ..locked })) by {
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
            kernel_cpu_tlb_updated_implies_u_step(&mid, &*self);
        };
        assert(locked != kernel_k_to_kernel_u(*self) ==> kernel_u_cpu_tlb_cleared(locked, kernel_k_to_kernel_u(*self), pcid)) by {
            reveal(kernel_u_cpu_tlb_cleared); kernel_u_domains_projection(&snap);
            if locked != kernel_k_to_kernel_u(*self) {
                kernel_cpu_tlb_within_may_cache_projection(self, cpu_id, pcid, self.cpu_tlb.spec_index((cpu_id, pcid)), self.cpu_tlb.structure_cache((cpu_id, pcid)));
                assert(!locked.cpu_tlb.dom().contains((cpu_id, pcid)) || locked.cpu_tlb[(cpu_id, pcid)] != self.cpu_tlb.spec_index((cpu_id, pcid))) by {
                    if locked.cpu_tlb.dom().contains((cpu_id, pcid)) && locked.cpu_tlb[(cpu_id, pcid)] == self.cpu_tlb.spec_index((cpu_id, pcid)) {
                        assert_maps_equal!(locked.cpu_tlb, self.cpu_tlb.view(), key => {});
                    }
                };
                assert_sets_equal!(self.cpu_tlb.view().dom().filter(|key: (CpuId, Pcid)| !locked.cpu_tlb.dom().contains(key) || locked.cpu_tlb[key] != self.cpu_tlb.view()[key]), set![(cpu_id, pcid)]);
            }
        };
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        reveal(LockedMap::typed_lock_map_aligned);
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*self);
    }
}
}
