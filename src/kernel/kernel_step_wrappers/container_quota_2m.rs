use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal, assert_sets_equal};
use crate::*;

verus! {
/// Changing only the 2M allocator quota of `container`, by `delta`, changes only that container's `quota_2m` in the projection.
pub proof fn kernel_container_quota_2m_changed_implies_u_step(pre: &KernelK, post: &KernelK, container: RwLockContainerPtr, delta: int)
    requires
        kernel_container_quota_2m_changed(pre, post, container, delta),
        delta > 0,
    ensures
        kernel_k_to_kernel_u(*pre).container_map.dom().contains(container),
        kernel_k_to_kernel_u(*post).container_map[container].quota_2m as int == kernel_k_to_kernel_u(*pre).container_map[container].quota_2m as int + delta,
        kernel_k_to_kernel_u(*post) == (KernelU {
            container_map: kernel_k_to_kernel_u(*pre).container_map.insert(container, ContainerU {
                quota_2m: (kernel_k_to_kernel_u(*pre).container_map[container].quota_2m as int + delta) as usize,
                ..kernel_k_to_kernel_u(*pre).container_map[container]
            }), ..kernel_k_to_kernel_u(*pre)
        }),
{
    reveal(kernel_container_quota_2m_changed); kernel_u_domains_projection(pre); kernel_u_domains_projection(post); reveal(kernel_thread_nonlock_fields_unchanged);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    if pre.ctn_mp.dom().contains(container) { kernel_container_projection_at(pre, container); } if post.ctn_mp.dom().contains(container) { kernel_container_projection_at(post, container); }
    assert_maps_equal!(after.container_map, before.container_map.insert(container, ContainerU {
        quota_2m: (before.container_map[container].quota_2m as int + delta) as usize, ..before.container_map[container]
    }), c => { if pre.ctn_mp.dom().contains(c) { kernel_container_projection_at(pre, c); } if post.ctn_mp.dom().contains(c) { kernel_container_projection_at(post, c); } });
    assert_maps_equal!(after.thread_map, before.thread_map, t => {
        if pre.thr_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thr_mp.dom().contains(t) { kernel_thread_projection_at(post, t); }
    });
    assert_seqs_equal!(after.cpu_array == before.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); } });
    assert_maps_equal!(after.process_map, before.process_map, p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); }
    });
    assert_maps_equal!(after.endpoint_map, before.endpoint_map, p => {
        if pre.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(pre, p); } if post.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(post, p); }
    });
}

impl KernelK {
    /// Records the step that returns `delta` 2M quota to `container_ptr`, an ancestor of `origin` or `origin` itself.
    pub proof fn kernel_step_boundary_container_quota_2m_changed(tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, container_ptr: RwLockContainerPtr, delta: int, origin: RwLockContainerPtr)
        requires
            old(self).inv(),
            delta > 0,
            kernel_container_quota_2m_changed(&old(steps).snapshot_k(), old(self), container_ptr, delta),
            old(steps).snapshot_k().ctn_mp.dom().contains(origin),
            container_ptr == origin || old(steps).snapshot_k().ctn_mp.spec_index(origin).view_ghost().uppertree_seq.view().contains(container_ptr),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            kernel_u_container_quota_2m_increased(old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(self)), origin),
            old(steps).snapshot_u().container_map.dom().contains(container_ptr),
            kernel_k_to_kernel_u(*old(self)).container_map[container_ptr].quota_2m as int == old(steps).snapshot_u().container_map[container_ptr].quota_2m as int + delta,
            final(steps).view() == old(steps).view().push(KernelStep { old_u: old(steps).snapshot_u(), new_u: kernel_k_to_kernel_u(*old(self)) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            kernel_k_to_kernel_u(*old(self)) == (KernelU { container_map: old(steps).snapshot_u().container_map.insert(container_ptr, ContainerU {
                quota_2m: (old(steps).snapshot_u().container_map[container_ptr].quota_2m as int + delta) as usize,
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
            final(steps).snapshot_k() == *final(self),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(self)),
            forall|p: RwLockPageTableRoot| #![trigger old(lctx).pagetable_lock_map().dom().contains(p)] typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), p, TypedLockMode::Write)
                ==> whole_pagetable(final(self).pt_mp, final(self).pt_lower.view(), p) == whole_pagetable(old(self).pt_mp, old(self).pt_lower.view(), p),
    {
        use_type_invariant(&*steps);
        assert(steps.snapshot_u().container_map.dom().contains(container_ptr)
            && kernel_k_to_kernel_u(*self).container_map[container_ptr].quota_2m as int == steps.snapshot_u().container_map[container_ptr].quota_2m as int + delta
            && kernel_k_to_kernel_u(*self) != steps.snapshot_u() && kernel_k_to_kernel_u(*self) == (KernelU {
                container_map: steps.snapshot_u().container_map.insert(container_ptr, ContainerU {
                    quota_2m: (steps.snapshot_u().container_map[container_ptr].quota_2m as int + delta) as usize, ..steps.snapshot_u().container_map[container_ptr]
                }), ..steps.snapshot_u()
            })) by { kernel_container_quota_2m_changed_implies_u_step(&steps.snapshot_k(), &*self, container_ptr, delta); };
        assert(kernel_u_container_quota_2m_increased(steps.snapshot_u(), kernel_k_to_kernel_u(*self), origin)) by {
            reveal(kernel_u_container_quota_2m_increased);
            kernel_container_ancestry_projection_at(&steps.snapshot_k(), origin);
            let pre = steps.snapshot_u();
            let post = kernel_k_to_kernel_u(*self);
            assert_sets_equal!(pre.container_map.dom().filter(|c: RwLockContainerPtr| pre.container_map[c] != post.container_map[c]), set![container_ptr]);
            assert_sets_equal!(post.container_map.dom(), pre.container_map.dom());
        };
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        reveal(LockedMap::typed_lock_map_aligned);
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*self);
    }
}
}
