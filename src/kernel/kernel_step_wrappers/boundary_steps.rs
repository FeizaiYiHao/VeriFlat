use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal, assert_sets_equal};
use crate::*;
#[cfg(verus_keep_ghost)]
use super::boundary::{kernel_process_added_implies_u_neq, kernel_thread_quota_4k_changed_implies_u_step};

verus! {
impl KernelK {
    pub proof fn kernel_step_boundary_nonlock_fields_unchanged(tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps)
        requires
            old(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(self).ep_mp),
            old(self).irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
            old(self).irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
            old(self).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            old(self).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(self)),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            kernel_step_boundary_framing(*old(self), *final(self), *old(lctx)),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|p: RwLockPageTableRoot| #![trigger old(lctx).pagetable_lock_map().dom().contains(p)] typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), p, TypedLockMode::Write)
                ==> pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), p) == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), p),
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(self))),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).nonlock_view() == old(steps).nonlock_view(),
            final(steps).snapshot_k() == *final(self),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(self)),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(self).ep_mp),
            forall|t: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(t)] old(lctx).thread_lock_map().dom().contains(t) ==> {
                let owner = old(self).thr_mp.spec_index(t).view().owning_container;
                &&& old(self).ctn_mp.dom().contains(owner)
                &&& final(self).ctn_mp.spec_index(owner).view_ghost().uppertree_seq == old(self).ctn_mp.spec_index(owner).view_ghost().uppertree_seq
            },
            forall|pt: RwLockPageTableRoot, window_va: WindowVa, va: VAddr|
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pt, window_va)), pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pt).mapping_4k().spec_index(va)]
                old(lctx).pagetable_lock_map().dom().contains(pt) && old(lctx).pagetable_window_lock_map().dom().contains((pt, window_va))
                    && spec_v2l4index(va) == spec_v2l4index(window_va.va) && spec_v2l3index(va) == spec_v2l3index(window_va.va) && spec_v2l2index(va) == spec_v2l2index(window_va.va)
                    && pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pt).mapping_4k().dom().contains(va) && page_ptr_valid(pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pt).mapping_4k().spec_index(va).addr) ==> {
                    let entry = pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pt).mapping_4k().spec_index(va);
                    let page_index = page_ptr2page_index(entry.addr);
                    &&& old(self).pg_arr.spec_index(page_index).view().view().owning_container == entry.owning_container.view()
                    &&& old(self).ctn_mp.dom().contains(entry.owning_container.view())
                    &&& final(self).ctn_mp.dom().contains(entry.owning_container.view())
                    &&& final(self).pg_arr.spec_index(page_index).view().view().state == PageState::Mapped4k
                    &&& final(self).pg_arr.spec_index(page_index).view().view().mappings().contains((pt, va))
                },
            forall|pt: RwLockPageTableRoot, va: VAddr|
                #![trigger typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pt, TypedLockMode::Write), pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pt).mapping_4k().spec_index(va)]
                typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pt, TypedLockMode::Write) && pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pt).mapping_4k().dom().contains(va)
                    && page_ptr_valid(pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pt).mapping_4k().spec_index(va).addr) ==> {
                    let entry = pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pt).mapping_4k().spec_index(va);
                    let page_index = page_ptr2page_index(entry.addr);
                    &&& old(self).pg_arr.spec_index(page_index).view().view().owning_container == entry.owning_container.view()
                    &&& old(self).ctn_mp.dom().contains(entry.owning_container.view())
                    &&& final(self).ctn_mp.dom().contains(entry.owning_container.view())
                    &&& final(self).pg_arr.spec_index(page_index).view().view().state == PageState::Mapped4k
                    &&& final(self).pg_arr.spec_index(page_index).view().view().mappings().contains((pt, va))
                },
    {
        use_type_invariant(&*steps);
        reveal(KernelSteps::nonlock_view);
        assert(steps.nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*self)) by { kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(&steps.snapshot_k(), &*self); };
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        reveal(LockedMap::typed_lock_map_aligned);
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*self);
        old(self).thr_mp.typed_lock_map_aligned_held_in_dom(old(lctx).thread_lock_map(), old(lctx).thread_id()); old(self).pt_mp.typed_lock_map_aligned_held_in_dom(old(lctx).pagetable_lock_map(), old(lctx).thread_id());
        reveal(container_page_owner_wf); reveal(container_thread_wf); reveal(mapped_4k_page_pagetable_wf);
    }

    pub proof fn kernel_step_boundary_cpu_tlb_updated(tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, cpu_id: CpuId, pcid: Pcid, flushed: bool)
        requires
            *old(self) == (KernelK {
                cpu_arr: old(self).cpu_arr, cpu_tlb: old(self).cpu_tlb, pcid_needflush: old(self).pcid_needflush, pt_mp: old(self).pt_mp, pt_lower: old(self).pt_lower, ..old(steps).snapshot_k()
            }),
            forall|cpu: CpuId| #![trigger old(self).cpu_arr.spec_index(cpu)] index_valid(NUM_CPUS, cpu) ==>
                old(self).cpu_arr.spec_index(cpu).value.locking_thread() == old(steps).snapshot_k().cpu_arr.spec_index(cpu).value.locking_thread(),
            old(self).pt_mp.dom() == old(steps).snapshot_k().pt_mp.dom(),
            forall|pt: RwLockPageTableRoot| #![trigger old(self).pt_mp.spec_index(pt)] old(steps).snapshot_k().pt_mp.dom().contains(pt) ==> {
                &&& old(self).pt_mp.spec_index(pt).view() == old(steps).snapshot_k().pt_mp.spec_index(pt).view()
                &&& old(self).pt_mp.spec_index(pt).locking_thread() == old(steps).snapshot_k().pt_mp.spec_index(pt).locking_thread()
                &&& old(self).pt_mp.spec_index(pt).being_killed() == old(steps).snapshot_k().pt_mp.spec_index(pt).being_killed()
                &&& old(self).pt_mp.lock_id_by_key(pt) == old(steps).snapshot_k().pt_mp.lock_id_by_key(pt)
                &&& pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pt).mapping_4k() == pagetable_c(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pt).mapping_4k()
                &&& pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pt).mapping_2m() == pagetable_c(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pt).mapping_2m()
                &&& pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), pt).mapping_1g() == pagetable_c(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pt).mapping_1g()
            },
            old(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(self).ep_mp),
            old(self).irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
            old(self).irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
            index_valid(NUM_CPUS, cpu_id),
            pcid_valid(pcid),
            old(self).cpu_tlb.view() == if flushed {
                old(steps).snapshot_k().cpu_tlb.view().insert((cpu_id, pcid), old(self).cpu_tlb.spec_index((cpu_id, pcid)))
            } else { old(steps).snapshot_k().cpu_tlb.view() },
            flushed ==> cpu_tlb_within_may_cache(*old(self), cpu_id, pcid, old(self).cpu_tlb.spec_index((cpu_id, pcid))),
            old(self).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(self)),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==>
                kernel_u_cpu_tlb_cleared(final(steps).view()[j].old_u, final(steps).view()[j].new_u, pcid),
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
            final(steps).nonlock_view() == if old(self).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view() {
                old(steps).nonlock_view()
            } else {
                old(steps).nonlock_view().push(KernelStep { old_u: old(steps).nonlock_snapshot_u(),
                    new_u: KernelU { cpu_tlb: old(self).cpu_tlb.view(), ..old(steps).nonlock_snapshot_u() } })
            },
            old(steps).nonlock_view().len() <= final(steps).nonlock_view().len() <= old(steps).nonlock_view().len() + 1,
            final(steps).snapshot_k() == *final(self),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(self)),
            forall|p: RwLockPageTableRoot| #![trigger old(lctx).pagetable_lock_map().dom().contains(p)] typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), p, TypedLockMode::Write)
                ==> pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), p) == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), p),
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
                kernel_cpu_tlb_within_may_cache_projection(self, true, cpu_id, pcid, self.cpu_tlb.spec_index((cpu_id, pcid)));
                assert(!steps.snapshot_u().cpu_tlb.dom().contains((cpu_id, pcid)) || steps.snapshot_u().cpu_tlb[(cpu_id, pcid)] != self.cpu_tlb.spec_index((cpu_id, pcid))) by {
                    if steps.snapshot_u().cpu_tlb.dom().contains((cpu_id, pcid)) && steps.snapshot_u().cpu_tlb[(cpu_id, pcid)] == self.cpu_tlb.spec_index((cpu_id, pcid)) {
                        assert_maps_equal!(steps.snapshot_u().cpu_tlb, self.cpu_tlb.view(), key => {});
                    }
                };
                assert_sets_equal!(self.cpu_tlb.view().dom().filter(|key: (CpuId, Pcid)| !steps.snapshot_u().cpu_tlb.dom().contains(key) || steps.snapshot_u().cpu_tlb[key] != self.cpu_tlb.view()[key]), set![(cpu_id, pcid)]);
            }
        };
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        reveal(LockedMap::typed_lock_map_aligned);
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*self);
    }

    #[verifier::spinoff_prover]
    pub proof fn kernel_step_boundary_container_quota_4k_changed(tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, container_ptr: RwLockContainerPtr, delta: int, origin: RwLockContainerPtr)
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
            kernel_step_boundary_framing(*old(self), *final(self), *old(lctx)),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep { old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*old(self)) }),
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
            forall|p: RwLockPageTableRoot| #![trigger old(lctx).pagetable_lock_map().dom().contains(p)] typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), p, TypedLockMode::Write)
                ==> pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), p) == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), p),
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
            reveal(kernel_container_quota_4k_changed); reveal(kernel_thread_nonlock_fields_unchanged); reveal(kernel_k_to_nonlock_kernel_u);
            assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array);
            assert_maps_equal!(post_u.thread_map, pre_u.thread_map, t => {});
            assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => {});
            reveal(process_pagetable_match);
            assert_maps_equal!(post_u.process_map, pre_u.process_map);
            assert_maps_equal!(post_u.container_map, pre_u.container_map.insert(container_ptr, post_u.container_map.spec_index(container_ptr)), c => {});
        };
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        reveal(LockedMap::typed_lock_map_aligned);
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*self);
    }

    pub proof fn kernel_step_boundary_thread_quota_4k_changed(tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, thread_ptr: RwLockThreadPtr, delta: int)
        requires
            old(self).inv(),
            delta != 0,
            kernel_thread_quota_4k_changed(&old(steps).snapshot_k(), old(self), thread_ptr, delta),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            kernel_step_boundary_framing(*old(self), *final(self), *old(lctx)),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|p: RwLockPageTableRoot| #![trigger old(lctx).pagetable_lock_map().dom().contains(p)] typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), p, TypedLockMode::Write)
                ==> pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), p) == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), p),
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == old(steps).view().push(KernelStep { old_u: old(steps).snapshot_u(), new_u: kernel_k_to_kernel_u(*old(self)) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep {
                old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*old(self)),
            }),
            final(steps).snapshot_k() == *final(self),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(self)),
    {
        use_type_invariant(&*steps);
        reveal(KernelSteps::nonlock_view);
        kernel_thread_quota_4k_changed_implies_u_step(&steps.snapshot_k(), &*self, thread_ptr, delta);
        assert(steps.snapshot_u() != kernel_k_to_kernel_u(*self)) by { kernel_nonlock_projection_is_u_nonlock_fields(steps.snapshot_k()); kernel_nonlock_projection_is_u_nonlock_fields(*self); };
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        reveal(LockedMap::typed_lock_map_aligned);
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*self);
    }

    #[verifier::spinoff_prover]
    pub proof fn kernel_step_boundary_thread_syscall_progress_changed(tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, thread_ptr: RwLockThreadPtr)
        requires
            old(self).inv(),
            old(steps).snapshot_k().thr_mp.dom().contains(thread_ptr),
            old(self).thr_mp.dom().contains(thread_ptr),
            old(steps).snapshot_k().thr_mp.spec_index(thread_ptr).view().syscall_progress.view() != old(self).thr_mp.spec_index(thread_ptr).view().syscall_progress.view(),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            kernel_step_boundary_framing(*old(self), *final(self), *old(lctx)),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|p: RwLockPageTableRoot| #![trigger old(lctx).pagetable_lock_map().dom().contains(p)] typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), p, TypedLockMode::Write)
                ==> pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), p) == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), p),
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == old(steps).view().push(KernelStep { old_u: old(steps).snapshot_u(), new_u: kernel_k_to_kernel_u(*old(self)) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep {
                old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*old(self)),
            }),
            final(steps).snapshot_k() == *final(self),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(self)),
    {
        use_type_invariant(&*steps);
        reveal(KernelSteps::nonlock_view);
        steps.end_kernel_step_thread_syscall_progress_changed(&*self, &*lctx, thread_ptr);
        self.kernel_step_boundary_raw(lctx, steps);
        reveal(LockedMap::typed_lock_map_aligned);
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*self);
    }

    /// Records the section that changed both the complete and the business projection.
    pub proof fn kernel_step_boundary_user_view_changed(tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps)
        requires
            old(self).inv(),
            kernel_k_to_kernel_u(old(steps).snapshot_k()) != kernel_k_to_kernel_u(*old(self)),
            kernel_k_to_nonlock_kernel_u(old(steps).snapshot_k()) != kernel_k_to_nonlock_kernel_u(*old(self)),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            kernel_step_boundary_framing(*old(self), *final(self), *old(lctx)),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|thread_ptr: RwLockThreadPtr|
                #![trigger old(lctx).thread_lock_map().dom().contains(thread_ptr)]
                #![trigger final(self).thr_mp.dom().contains(thread_ptr)]
                old(lctx).thread_lock_map().dom().contains(thread_ptr) ==> {
                    &&& final(self).thr_mp.dom().contains(thread_ptr)
                    &&& final(self).thr_mp.lock_id_by_key(thread_ptr) == old(self).thr_mp.lock_id_by_key(thread_ptr)
                    &&& final(self).thr_mp.spec_index(thread_ptr) == old(self).thr_mp.spec_index(thread_ptr)
                },
            forall|p: RwLockPageTableRoot| #![trigger old(lctx).pagetable_lock_map().dom().contains(p)] typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), p, TypedLockMode::Write)
                ==> pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), p) == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), p),
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == old(steps).view().push(KernelStep { old_u: old(steps).snapshot_u(), new_u: kernel_k_to_kernel_u(*old(self)) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep {
                old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*old(self)),
            }),
            final(steps).snapshot_k() == *final(self),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(self)),
    {
        use_type_invariant(&*steps);
        reveal(KernelSteps::nonlock_view);
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        reveal(LockedMap::typed_lock_map_aligned);
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*self);
    }

    #[verifier::spinoff_prover]
    pub proof fn kernel_step_boundary_thread_state_changed(tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, thread_ptr: RwLockThreadPtr, old_state: ThreadState, new_state: ThreadState)
        requires
            old(self).inv(),
            kernel_thread_state_changed(&old(steps).snapshot_k(), old(self), thread_ptr),
            old(steps).snapshot_k().thr_mp.spec_index(thread_ptr).view().state == old_state,
            old(self).thr_mp.spec_index(thread_ptr).view().state == new_state,
            old(lctx).kernel_view_locking_state() is Release,
            old(lctx).thread_lock_map().dom().contains(thread_ptr),
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            kernel_step_boundary_framing(*old(self), *final(self), *old(lctx)),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|p: RwLockPageTableRoot| #![trigger old(lctx).pagetable_lock_map().dom().contains(p)] typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), p, TypedLockMode::Write)
                ==> pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), p) == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), p),
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(self))),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep {
                old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*old(self)),
            }),
            final(steps).snapshot_k() == *final(self),
            final(steps).nonlock_view().last().old_u.thread_map.dom().contains(thread_ptr),
            final(steps).nonlock_view().last().old_u.thread_map.spec_index(thread_ptr).state == old_state,
            final(steps).nonlock_view().last().new_u.thread_map.dom().contains(thread_ptr),
            final(steps).nonlock_view().last().new_u.thread_map.spec_index(thread_ptr).state == new_state,
            final(steps).nonlock_snapshot_u().thread_map.dom().contains(thread_ptr),
            final(steps).nonlock_snapshot_u().thread_map.spec_index(thread_ptr).state == new_state,
    {
        use_type_invariant(&*steps);
        reveal(KernelSteps::nonlock_view);
        assert(steps.snapshot_k().thr_mp.dom().contains(thread_ptr) && old(self).thr_mp.dom().contains(thread_ptr)) by { reveal(kernel_thread_state_changed); };
        kernel_thread_state_changed_implies_u_neq(&steps.snapshot_k(), &*self, thread_ptr);
        assert(steps.nonlock_snapshot_u().thread_map.dom().contains(thread_ptr)
            && steps.nonlock_snapshot_u().thread_map.spec_index(thread_ptr).state == old_state) by { kernel_thread_nonlock_projection_at(&steps.snapshot_k(), thread_ptr); };
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        reveal(LockedMap::typed_lock_map_aligned);
        kernel_thread_nonlock_projection_at(old(self), thread_ptr); kernel_thread_nonlock_projection_at(&*self, thread_ptr);
    }

    #[verifier::spinoff_prover]
    pub proof fn kernel_step_boundary_process_added(tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr)
        requires
            old(self).inv(),
            kernel_process_added(&old(steps).snapshot_k(), old(self), process_ptr),
            !old(self).prc_mp.spec_index(process_ptr).view().zombie,
            old(self).thr_mp.dom().contains(current_thread_ptr),
            old(lctx).kernel_view_locking_state() is Release,
            old(lctx).process_lock_map().dom().contains(process_ptr),
            old(lctx).thread_lock_map().dom().contains(current_thread_ptr),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), old(self).prc_mp.spec_index(process_ptr).view().pagetable, TypedLockMode::Write),
            {
                let iommu_table = old(self).prc_mp.spec_index(process_ptr).view().iommu_table;
                ||| iommu_table is None
                ||| iommu_table is Some && old(lctx).iommu_table_lock_map().dom().contains(iommu_table.unwrap())
            },
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            kernel_step_boundary_framing(*old(self), *final(self), *old(lctx)),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|p: RwLockPageTableRoot| #![trigger old(lctx).pagetable_lock_map().dom().contains(p)] typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), p, TypedLockMode::Write)
                ==> pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), p) == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), p),
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == old(steps).view().push(KernelStep { old_u: old(steps).snapshot_u(), new_u: kernel_k_to_kernel_u(*old(self)) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep {
                old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*old(self)),
            }),
            final(steps).snapshot_k() == *final(self),
            final(steps).nonlock_view().last().new_u.process_map.dom().contains(process_ptr),
            kernel_k_to_nonlock_kernel_u(*final(self)).process_map.dom().contains(process_ptr),
            final(steps).nonlock_view().last().new_u.process_map.spec_index(process_ptr) == kernel_k_to_nonlock_kernel_u(*final(self)).process_map.spec_index(process_ptr),
            final(steps).nonlock_view().last().new_u.thread_map.dom().contains(current_thread_ptr),
            kernel_k_to_nonlock_kernel_u(*final(self)).thread_map.dom().contains(current_thread_ptr),
            final(steps).nonlock_view().last().new_u.thread_map.spec_index(current_thread_ptr) == kernel_k_to_nonlock_kernel_u(*final(self)).thread_map.spec_index(current_thread_ptr),
    {
        use_type_invariant(&*steps);
        reveal(KernelSteps::nonlock_view);
        assert(old(self).prc_mp.dom().contains(process_ptr)) by { reveal(kernel_process_added); };
        kernel_process_added_implies_u_neq(&steps.snapshot_k(), &*self, process_ptr);
        assert(kernel_k_to_nonlock_kernel_u(*self).process_map.dom().contains(process_ptr)
            && kernel_k_to_nonlock_kernel_u(*self).thread_map.dom().contains(current_thread_ptr)) by { reveal(kernel_k_to_nonlock_kernel_u); };
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        reveal(LockedMap::typed_lock_map_aligned);
        kernel_process_nonlock_projection_at(old(self), process_ptr); kernel_process_nonlock_projection_at(&*self, process_ptr);
        kernel_thread_nonlock_projection_at(old(self), current_thread_ptr); kernel_thread_nonlock_projection_at(&*self, current_thread_ptr);
        let pagetable = old(self).prc_mp.spec_index(process_ptr).view().pagetable;
        old(self).pt_mp.typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable);
        pagetable_lower_backup_wf_at(old(self).pt_mp, old(self).pt_lower.view(), pagetable); pagetable_lower_backup_wf_at(self.pt_mp, self.pt_lower.view(), pagetable);
        let iommu_table = old(self).prc_mp.spec_index(process_ptr).view().iommu_table;
        if iommu_table is Some {
            assert(old(self).it_mp.dom().contains(iommu_table.unwrap())) by { reveal(process_iommu_table_match); };
        }
    }

    #[verifier::spinoff_prover]
    pub proof fn kernel_step_boundary_process_4k_mapping_changed(
        tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, process_ptr: RwLockProcessPtr,
        pagetable_ptr: RwLockPageTableRoot, va: VAddr, stable_process_ptr: RwLockProcessPtr, stable_pagetable_ptr: RwLockPageTableRoot,
        stable_thread_ptr: RwLockThreadPtr, stable_owner_thread_ptr: RwLockThreadPtr,
    )
        requires
            old(self).inv(),
            kernel_process_4k_mapping_changed(&old(steps).snapshot_k(), old(self), process_ptr, pagetable_ptr, va),
            old(self).thr_mp.dom().contains(stable_thread_ptr),
            old(lctx).kernel_view_locking_state() is Release,
            old(self).prc_mp.dom().contains(stable_process_ptr),
            old(self).prc_mp.spec_index(stable_process_ptr).view().pagetable == stable_pagetable_ptr,
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), stable_pagetable_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            old(lctx).thread_lock_map().dom().contains(stable_thread_ptr),
            old(lctx).thread_lock_map().dom().contains(stable_owner_thread_ptr),
            old(self).thr_mp.dom().contains(stable_owner_thread_ptr),
            old(self).thr_mp.spec_index(stable_owner_thread_ptr).view().owning_proc == stable_process_ptr,
            !thread_is_dangling(old(self).thr_mp.spec_index(stable_owner_thread_ptr)),
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            kernel_step_boundary_framing(*old(self), *final(self), *old(lctx)),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|p: RwLockPageTableRoot| #![trigger old(lctx).pagetable_lock_map().dom().contains(p)] typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), p, TypedLockMode::Write)
                ==> pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), p) == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), p),
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == old(steps).view().push(KernelStep { old_u: old(steps).snapshot_u(), new_u: kernel_k_to_kernel_u(*old(self)) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep {
                old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*old(self)),
            }),
            final(steps).snapshot_k() == *final(self),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(self)),
            final(steps).nonlock_view().last().new_u.process_map.dom().contains(stable_process_ptr),
            kernel_k_to_nonlock_kernel_u(*final(self)).process_map.dom().contains(stable_process_ptr),
            final(steps).nonlock_view().last().new_u.process_map.spec_index(stable_process_ptr).pagetable == kernel_k_to_nonlock_kernel_u(*final(self)).process_map.spec_index(stable_process_ptr).pagetable,
            final(steps).nonlock_view().last().new_u.process_map.dom().contains(process_ptr),
            final(steps).nonlock_view().last().new_u.thread_map.dom().contains(stable_thread_ptr),
            kernel_k_to_nonlock_kernel_u(*final(self)).thread_map.dom().contains(stable_thread_ptr),
            final(steps).nonlock_view().last().new_u.thread_map.spec_index(stable_thread_ptr) == kernel_k_to_nonlock_kernel_u(*final(self)).thread_map.spec_index(stable_thread_ptr),
            old(lctx).process_lock_map().dom().contains(process_ptr) && ({
                let iommu_table = old(self).prc_mp.spec_index(process_ptr).view().iommu_table;
                ||| iommu_table is None
                ||| iommu_table is Some && old(lctx).iommu_table_lock_map().dom().contains(iommu_table.unwrap())
            }) ==> {
                &&& kernel_k_to_nonlock_kernel_u(*final(self)).process_map.dom().contains(process_ptr)
                &&& final(steps).nonlock_view().last().new_u.process_map.spec_index(process_ptr) == kernel_k_to_nonlock_kernel_u(*final(self)).process_map.spec_index(process_ptr)
            },
    {
        use_type_invariant(&*steps);
        reveal(KernelSteps::nonlock_view);
        assert(old(self).prc_mp.dom().contains(process_ptr) && !old(self).prc_mp.spec_index(process_ptr).view().zombie && old(self).prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr) by { reveal(kernel_process_4k_mapping_changed); };
        kernel_process_4k_mapping_changed_implies_u_neq(&steps.snapshot_k(), &*self, process_ptr, pagetable_ptr, va);
        assert(kernel_k_to_nonlock_kernel_u(*self).process_map.dom().contains(process_ptr) && kernel_k_to_nonlock_kernel_u(*self).process_map.dom().contains(stable_process_ptr)
            && kernel_k_to_nonlock_kernel_u(*self).thread_map.dom().contains(stable_thread_ptr)) by { kernel_u_nonlock_domains_projection(&*self); };
        assert(!self.prc_mp.spec_index(stable_process_ptr).view().zombie) by { process_thread_wf_at(self.prc_mp, self.thr_mp, stable_owner_thread_ptr); };
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        reveal(LockedMap::typed_lock_map_aligned);
        assert(!self.prc_mp.spec_index(stable_process_ptr).view().zombie) by { process_thread_wf_at(self.prc_mp, self.thr_mp, stable_owner_thread_ptr); };
        old(self).pt_mp.typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        old(self).pt_mp.typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), stable_pagetable_ptr);
        pagetable_lower_backup_wf_at(old(self).pt_mp, old(self).pt_lower.view(), pagetable_ptr); pagetable_lower_backup_wf_at(self.pt_mp, self.pt_lower.view(), pagetable_ptr);
        pagetable_lower_backup_wf_at(old(self).pt_mp, old(self).pt_lower.view(), stable_pagetable_ptr); pagetable_lower_backup_wf_at(self.pt_mp, self.pt_lower.view(), stable_pagetable_ptr);
        reveal(process_pagetable_match); reveal(process_iommu_table_match); kernel_u_nonlock_domains_projection(old(self)); kernel_u_nonlock_domains_projection(&*self);
        kernel_process_nonlock_projection_at(old(self), stable_process_ptr); kernel_process_nonlock_projection_at(&*self, stable_process_ptr);
        kernel_thread_nonlock_projection_at(old(self), stable_thread_ptr); kernel_thread_nonlock_projection_at(&*self, stable_thread_ptr);
        kernel_process_nonlock_projection_at(old(self), process_ptr); kernel_process_nonlock_projection_at(&*self, process_ptr);
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*self);
    }

    /// Records the section that changed `va` of `process_ptr`'s pagetable when the tables are held in either mode: the
    /// changed table is write-held or its window around `va` is held. Only the held windows of the stable table keep
    /// their 4K mappings, and the stable table keeps its lock state.
    pub proof fn kernel_step_boundary_process_4k_mapping_changed_windowed(
        tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, process_ptr: RwLockProcessPtr,
        pagetable_ptr: RwLockPageTableRoot, va: VAddr, stable_process_ptr: RwLockProcessPtr, stable_pagetable_ptr: RwLockPageTableRoot,
        stable_thread_ptr: RwLockThreadPtr, stable_owner_thread_ptr: RwLockThreadPtr,
    )
        requires
            old(self).inv(),
            kernel_process_4k_mapping_changed(&old(steps).snapshot_k(), old(self), process_ptr, pagetable_ptr, va),
            old(self).thr_mp.dom().contains(stable_thread_ptr),
            old(lctx).kernel_view_locking_state() is Release,
            old(self).prc_mp.dom().contains(stable_process_ptr),
            old(self).prc_mp.spec_index(stable_process_ptr).view().pagetable == stable_pagetable_ptr,
            old(lctx).pagetable_lock_map().dom().contains(stable_pagetable_ptr),
            old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write) || old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, window_of(va))),
            old(lctx).thread_lock_map().dom().contains(stable_thread_ptr),
            old(lctx).thread_lock_map().dom().contains(stable_owner_thread_ptr),
            old(self).thr_mp.dom().contains(stable_owner_thread_ptr),
            old(self).thr_mp.spec_index(stable_owner_thread_ptr).view().owning_proc == stable_process_ptr,
            !thread_is_dangling(old(self).thr_mp.spec_index(stable_owner_thread_ptr)),
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            kernel_step_boundary_framing(*old(self), *final(self), *old(lctx)),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|p: RwLockPageTableRoot| #![trigger old(lctx).pagetable_lock_map().dom().contains(p)] typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), p, TypedLockMode::Write)
                ==> pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), p) == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), p),
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == old(steps).view().push(KernelStep { old_u: old(steps).snapshot_u(), new_u: kernel_k_to_kernel_u(*old(self)) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep {
                old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*old(self)),
            }),
            final(steps).snapshot_k() == *final(self),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(self)),
            final(steps).nonlock_view().last().new_u.process_map.dom().contains(stable_process_ptr),
            kernel_k_to_nonlock_kernel_u(*final(self)).process_map.dom().contains(stable_process_ptr),
            final(steps).view().last().new_u.process_map.dom().contains(stable_process_ptr) && final(steps).view().last().new_u.process_map.spec_index(stable_process_ptr).pagetable is Some,
            kernel_k_to_kernel_u(*final(self)).process_map.dom().contains(stable_process_ptr) && kernel_k_to_kernel_u(*final(self)).process_map.spec_index(stable_process_ptr).pagetable is Some,
            final(steps).view().last().new_u.process_map.spec_index(stable_process_ptr).pagetable->Some_0.lock_state == kernel_k_to_kernel_u(*final(self)).process_map.spec_index(stable_process_ptr).pagetable->Some_0.lock_state,
            forall|wva: WindowVa, v: VAddr|
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((stable_pagetable_ptr, wva)), kernel_k_to_nonlock_kernel_u(*final(self)).process_map.spec_index(stable_process_ptr).pagetable->Some_0.mapping_4k.dom().contains(v)]
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((stable_pagetable_ptr, wva)), final(steps).nonlock_view().last().new_u.process_map.spec_index(stable_process_ptr).pagetable->Some_0.mapping_4k.dom().contains(v)]
                old(lctx).pagetable_window_lock_map().dom().contains((stable_pagetable_ptr, wva)) && spec_v2l4index(v) == spec_v2l4index(wva.va) && spec_v2l3index(v) == spec_v2l3index(wva.va) && spec_v2l2index(v) == spec_v2l2index(wva.va) ==> {
                    let pre_t = final(steps).nonlock_view().last().new_u.process_map.spec_index(stable_process_ptr).pagetable->Some_0;
                    let post_t = kernel_k_to_nonlock_kernel_u(*final(self)).process_map.spec_index(stable_process_ptr).pagetable->Some_0;
                    &&& post_t.mapping_4k.dom().contains(v) == pre_t.mapping_4k.dom().contains(v)
                    &&& pre_t.mapping_4k.dom().contains(v) ==> post_t.mapping_4k.spec_index(v) == pre_t.mapping_4k.spec_index(v)
                },
            final(steps).nonlock_view().last().new_u.process_map.dom().contains(process_ptr),
            final(steps).nonlock_view().last().new_u.thread_map.dom().contains(stable_thread_ptr),
            kernel_k_to_nonlock_kernel_u(*final(self)).thread_map.dom().contains(stable_thread_ptr),
            final(steps).nonlock_view().last().new_u.thread_map.spec_index(stable_thread_ptr) == kernel_k_to_nonlock_kernel_u(*final(self)).thread_map.spec_index(stable_thread_ptr),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write) && old(lctx).process_lock_map().dom().contains(process_ptr) && ({
                let iommu_table = old(self).prc_mp.spec_index(process_ptr).view().iommu_table;
                ||| iommu_table is None
                ||| iommu_table is Some && old(lctx).iommu_table_lock_map().dom().contains(iommu_table.unwrap())
            }) ==> {
                &&& kernel_k_to_nonlock_kernel_u(*final(self)).process_map.dom().contains(process_ptr)
                &&& final(steps).nonlock_view().last().new_u.process_map.spec_index(process_ptr) == kernel_k_to_nonlock_kernel_u(*final(self)).process_map.spec_index(process_ptr)
            },
    {
        use_type_invariant(&*steps);
        reveal(KernelSteps::nonlock_view);
        assert(old(self).prc_mp.dom().contains(process_ptr) && !old(self).prc_mp.spec_index(process_ptr).view().zombie && old(self).prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr) by { reveal(kernel_process_4k_mapping_changed); };
        kernel_process_4k_mapping_changed_implies_u_neq(&steps.snapshot_k(), &*self, process_ptr, pagetable_ptr, va);
        assert(kernel_k_to_nonlock_kernel_u(*self).process_map.dom().contains(process_ptr) && kernel_k_to_nonlock_kernel_u(*self).process_map.dom().contains(stable_process_ptr)
            && kernel_k_to_nonlock_kernel_u(*self).thread_map.dom().contains(stable_thread_ptr)) by { kernel_u_nonlock_domains_projection(&*self); };
        assert(!self.prc_mp.spec_index(stable_process_ptr).view().zombie) by { process_thread_wf_at(self.prc_mp, self.thr_mp, stable_owner_thread_ptr); };
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        reveal(LockedMap::typed_lock_map_aligned);
        assert(!self.prc_mp.spec_index(stable_process_ptr).view().zombie) by { process_thread_wf_at(self.prc_mp, self.thr_mp, stable_owner_thread_ptr); };
        if typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write) {
            old(self).pt_mp.typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
            pagetable_lower_backup_wf_at(old(self).pt_mp, old(self).pt_lower.view(), pagetable_ptr); pagetable_lower_backup_wf_at(self.pt_mp, self.pt_lower.view(), pagetable_ptr);
        }
        if typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), stable_pagetable_ptr, TypedLockMode::Write) {
            old(self).pt_mp.typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), stable_pagetable_ptr);
        } else {
            old(self).pt_mp.typed_lock_map_aligned_read_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), stable_pagetable_ptr);
        }
        reveal(process_pagetable_match); reveal(process_iommu_table_match); kernel_u_nonlock_domains_projection(old(self)); kernel_u_nonlock_domains_projection(&*self);
        kernel_process_projection_at(old(self), stable_process_ptr); kernel_process_projection_at(&*self, stable_process_ptr);
        kernel_held_pagetable_windows_unchanged_implies_u_window_mappings_eq(old(self), &*self, old(lctx), stable_process_ptr, stable_pagetable_ptr);
        kernel_thread_nonlock_projection_at(old(self), stable_thread_ptr); kernel_thread_nonlock_projection_at(&*self, stable_thread_ptr);
        kernel_process_nonlock_projection_at(old(self), process_ptr); kernel_process_nonlock_projection_at(&*self, process_ptr);
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*self);
    }
}
} // verus!
