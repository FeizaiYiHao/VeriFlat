use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal, assert_sets_equal};
use crate::*;

verus! {
/// Changing only the 1G allocator quota of `container`, by `delta`, changes only that container's `quota_1g` in the projection.
pub proof fn kernel_container_quota_1g_changed_implies_u_step(pre: &KernelK, post: &KernelK, container: RwLockContainerPtr, delta: int)
    requires
        kernel_container_quota_1g_changed(pre, post, container, delta),
        delta > 0,
    ensures
        kernel_k_to_kernel_u(*pre).container_map.dom().contains(container),
        kernel_k_to_kernel_u(*post).container_map[container].quota_1g as int == kernel_k_to_kernel_u(*pre).container_map[container].quota_1g as int + delta,
        kernel_k_to_kernel_u(*post) == (KernelU {
            container_map: kernel_k_to_kernel_u(*pre).container_map.insert(container, ContainerU {
                quota_1g: (kernel_k_to_kernel_u(*pre).container_map[container].quota_1g as int + delta) as usize,
                ..kernel_k_to_kernel_u(*pre).container_map[container]
            }), ..kernel_k_to_kernel_u(*pre)
        }),
{
    reveal(kernel_container_quota_1g_changed); kernel_u_domains_projection(pre); kernel_u_domains_projection(post); reveal(kernel_thread_nonlock_fields_unchanged);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    if pre.ctn_mp.dom().contains(container) { kernel_container_projection_at(pre, container); } if post.ctn_mp.dom().contains(container) { kernel_container_projection_at(post, container); }
    assert_maps_equal!(after.container_map, before.container_map.insert(container, ContainerU {
        quota_1g: (before.container_map[container].quota_1g as int + delta) as usize, ..before.container_map[container]
    }), c => { if pre.ctn_mp.dom().contains(c) { kernel_container_projection_at(pre, c); } if post.ctn_mp.dom().contains(c) { kernel_container_projection_at(post, c); } });
    assert_maps_equal!(after.thread_map, before.thread_map, t => {
        if pre.thrd_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thrd_mp.dom().contains(t) { kernel_thread_projection_at(post, t); }
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
    /// Records the step that returns `delta` 1G quota to `ctn_ptr`, an ancestor of `origin` or `origin` itself.
    pub proof fn kernel_step_boundary_container_quota_1g_changed(tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, ctn_ptr: RwLockContainerPtr, delta: int, origin: RwLockContainerPtr)
        requires
            old(self).inv(),
            delta > 0,
            kernel_container_quota_1g_changed(&old(steps).snapshot_k(), old(self), ctn_ptr, delta),
            old(steps).snapshot_k().ctn_mp.dom().contains(origin),
            ctn_ptr == origin || old(steps).snapshot_k().ctn_mp.spec_index(origin).view_ghost().uppertree_seq.view().contains(ctn_ptr),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            kernel_u_container_quota_1g_increased(old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(self)), origin),
            old(steps).snapshot_u().container_map.dom().contains(ctn_ptr),
            kernel_k_to_kernel_u(*old(self)).container_map[ctn_ptr].quota_1g as int == old(steps).snapshot_u().container_map[ctn_ptr].quota_1g as int + delta,
            final(steps).view() == old(steps).view().push(KernelStep { old_u: old(steps).snapshot_u(), new_u: kernel_k_to_kernel_u(*old(self)) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            kernel_k_to_kernel_u(*old(self)) == (KernelU { container_map: old(steps).snapshot_u().container_map.insert(ctn_ptr, ContainerU {
                quota_1g: (old(steps).snapshot_u().container_map[ctn_ptr].quota_1g as int + delta) as usize,
                ..old(steps).snapshot_u().container_map[ctn_ptr]
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
        assert(steps.snapshot_u().container_map.dom().contains(ctn_ptr)
            && kernel_k_to_kernel_u(*self).container_map[ctn_ptr].quota_1g as int == steps.snapshot_u().container_map[ctn_ptr].quota_1g as int + delta
            && kernel_k_to_kernel_u(*self) != steps.snapshot_u() && kernel_k_to_kernel_u(*self) == (KernelU {
                container_map: steps.snapshot_u().container_map.insert(ctn_ptr, ContainerU {
                    quota_1g: (steps.snapshot_u().container_map[ctn_ptr].quota_1g as int + delta) as usize, ..steps.snapshot_u().container_map[ctn_ptr]
                }), ..steps.snapshot_u()
            })) by { kernel_container_quota_1g_changed_implies_u_step(&steps.snapshot_k(), &*self, ctn_ptr, delta); };
        assert(kernel_u_container_quota_1g_increased(steps.snapshot_u(), kernel_k_to_kernel_u(*self), origin)) by {
            reveal(kernel_u_container_quota_1g_increased);
            kernel_container_ancestry_projection_at(&steps.snapshot_k(), origin);
            let pre = steps.snapshot_u();
            let post = kernel_k_to_kernel_u(*self);
            assert_sets_equal!(pre.container_map.dom().filter(|c: RwLockContainerPtr| pre.container_map[c] != post.container_map[c]), set![ctn_ptr]);
            assert_sets_equal!(post.container_map.dom(), pre.container_map.dom());
        };
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        reveal(LockedMap::typed_lock_map_aligned);
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*self);
    }
}

proof fn kernel_process_quota_1g_changed_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr, delta: int)
    requires
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        process_iommu_table_wf(post.prc_mp, post.it_mp),
        kernel_process_quota_1g_changed(pre, post, cpu_id, prc_ptr, ctn_ptr, delta),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)] pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
    ensures
        kernel_u_only_process_quota_1g_changed(kernel_k_user_projection(*pre), kernel_k_user_projection(*post), cpu_id, prc_ptr, ctn_ptr, delta),
{
    hide(kernel_k_user_projection);
    reveal(kernel_u_only_process_quota_1g_changed); reveal(kernel_process_quota_1g_changed); reveal(kernel_endpoint_nonlock_fields_unchanged);
    kernel_u_user_domains_projection(pre); kernel_u_user_domains_projection(post);
    kernel_cpu_user_projection_at(pre, cpu_id); kernel_container_user_projection_at(pre, ctn_ptr); kernel_process_user_projection_at(pre, prc_ptr);
    let pre_u = kernel_k_user_projection(*pre);
    let post_u = kernel_k_user_projection(*post);
    assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { reveal(IommuRootTable::user_view); };
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, i as usize); kernel_cpu_user_projection_at(post, i as usize); } });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map, t => { if pre.thrd_mp.dom().contains(t) { kernel_thread_user_projection_at(pre, t); } if post.thrd_mp.dom().contains(t) { kernel_thread_user_projection_at(post, t); } });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => { if pre.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(pre, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(post, e); } });
    kernel_process_quota_1g_changed_implies_u_container_map(pre, post, cpu_id, prc_ptr, ctn_ptr, delta);
    kernel_process_quota_1g_changed_implies_u_process_map(pre, post, cpu_id, prc_ptr, ctn_ptr, delta);
}

/// Moving `delta` 1G quota from a container to its running process lowers only that container's quota in the container projection.
proof fn kernel_process_quota_1g_changed_implies_u_container_map(pre: &KernelK, post: &KernelK, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr, delta: int)
    requires
        kernel_process_quota_1g_changed(pre, post, cpu_id, prc_ptr, ctn_ptr, delta),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)] pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre);
            let container = pre_u.container_map.spec_index(ctn_ptr);
            kernel_k_user_projection(*post).container_map == pre_u.container_map.insert(ctn_ptr, ContainerU { quota_1g: (container.quota_1g as int - delta) as usize, ..container })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_process_quota_1g_changed);
    kernel_u_user_domains_projection(pre); kernel_u_user_domains_projection(post);
    let pre_u = kernel_k_user_projection(*pre);
    let post_u = kernel_k_user_projection(*post);
    let container = pre_u.container_map.spec_index(ctn_ptr);
    assert_maps_equal!(post_u.container_map, pre_u.container_map.insert(ctn_ptr, ContainerU {
        quota_1g: (container.quota_1g as int - delta) as usize, ..container
    }), c => { if pre.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(pre, c); } if post.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(post, c); } });
}

/// Moving `delta` 1G quota from a container to its running process raises only that process's quota in the process projection.
proof fn kernel_process_quota_1g_changed_implies_u_process_map(pre: &KernelK, post: &KernelK, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr, delta: int)
    requires
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        process_iommu_table_wf(post.prc_mp, post.it_mp),
        kernel_process_quota_1g_changed(pre, post, cpu_id, prc_ptr, ctn_ptr, delta),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre);
            let process = pre_u.process_map.spec_index(prc_ptr);
            kernel_k_user_projection(*post).process_map == pre_u.process_map.insert(prc_ptr, ProcessU { quota_1g: (process.quota_1g as int + delta) as usize, ..process })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_process_quota_1g_changed);
    kernel_u_user_domains_projection(pre); kernel_u_user_domains_projection(post);
    let pre_u = kernel_k_user_projection(*pre);
    let post_u = kernel_k_user_projection(*post);
    let process = pre_u.process_map.spec_index(prc_ptr);
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(prc_ptr, ProcessU {
        quota_1g: (process.quota_1g as int + delta) as usize, ..process
    }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_user_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_user_projection_at(post, p); }
        process_pagetable_wf_process_at(post.prc_mp, post.pt_mp, p); process_iommu_table_wf_process_at(post.prc_mp, post.it_mp, p);
    });
}

proof fn kernel_process2thread_quota_1g_changed_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, delta: int)
    requires kernel_process2thread_quota_1g_changed(pre, post, cpu_id, prc_ptr, thrd_ptr, delta),
    ensures
        kernel_u_only_process2thread_quota_1g_changed(kernel_k_user_projection(*pre), kernel_k_user_projection(*post), cpu_id, prc_ptr, thrd_ptr, delta),
{
    hide(kernel_k_user_projection);
    reveal(kernel_u_only_process2thread_quota_1g_changed); reveal(kernel_process2thread_quota_1g_changed);
    kernel_u_user_domains_projection(pre); kernel_u_user_domains_projection(post);
    kernel_cpu_user_projection_at(pre, cpu_id); kernel_process_user_projection_at(pre, prc_ptr); kernel_thread_user_projection_at(pre, thrd_ptr);
    let pre_u = kernel_k_user_projection(*pre);
    let post_u = kernel_k_user_projection(*post);
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, i as usize); kernel_cpu_user_projection_at(post, i as usize); } });
    let process = pre_u.process_map.spec_index(prc_ptr);
    let thread = pre_u.thread_map.spec_index(thrd_ptr);
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thrd_ptr, ThreadU {
        quota_1g: (thread.quota_1g as int + delta) as usize, ..thread
    }), t => { if pre.thrd_mp.dom().contains(t) { kernel_thread_user_projection_at(pre, t); } if post.thrd_mp.dom().contains(t) { kernel_thread_user_projection_at(post, t); } });
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(prc_ptr, ProcessU {
        quota_1g: (process.quota_1g as int - delta) as usize, ..process
    }), p => { if pre.prc_mp.dom().contains(p) { kernel_process_user_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_user_projection_at(post, p); } });
    assert_maps_equal!(post_u.container_map, pre_u.container_map, c => { if pre.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(pre, c); } if post.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(post, c); } });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => { if pre.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(pre, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(post, e); } });
}

impl KernelSteps {
    pub proof fn end_kernel_step_process_quota_1g_changed(tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr, delta: int)
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_process_quota_1g_changed(&old(self).snapshot_k(), krnl, cpu_id, prc_ptr, ctn_ptr, delta),
            forall|p: RwLockContainerPtr| #![trigger krnl.ctn_mp.spec_index(p)] old(self).snapshot_k().ctn_mp.dom().contains(p) ==> krnl.ctn_mp.spec_index(p).lock_process_owner_u() == old(self).snapshot_k().ctn_mp.spec_index(p).lock_process_owner_u(),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).snapshot_k() == *krnl,
            kernel_u_only_process_quota_1g_changed(kernel_k_to_kernel_u(old(self).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, prc_ptr, ctn_ptr, delta),
            {
                let old_u = kernel_k_to_kernel_u(old(self).snapshot_k());
                let cpu = old_u.cpu_array[cpu_id as int];
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_process == Some(prc_ptr)
                &&& cpu.owning_container == ctn_ptr
                &&& old_u.container_map.dom().contains(ctn_ptr)
                &&& old_u.container_map.spec_index(ctn_ptr).lock_state is Unlocked
                &&& !old_u.container_map.spec_index(ctn_ptr).killed
                &&& !old_u.container_map.spec_index(ctn_ptr).zombie
                &&& old_u.container_map.spec_index(ctn_ptr).quota_1g >= delta
                &&& old_u.process_map.dom().contains(prc_ptr)
                &&& old_u.process_map.spec_index(prc_ptr).lock_state is Unlocked
                &&& !old_u.process_map.spec_index(prc_ptr).killed
                &&& old_u.process_map.spec_index(prc_ptr).quota_1g + delta <= usize::MAX
                &&& delta > 0
            },
    {
        hide(kernel_k_user_projection);
        reveal(kernel_u_only_process_quota_1g_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.container_map.spec_index(ctn_ptr).lock_state is Unlocked
            &&& pre_u.process_map.spec_index(prc_ptr).lock_state is Unlocked
        }) by {
            reveal(kernel_process_quota_1g_changed); kernel_cpu_projection_at(&self.snapshot_k(), cpu_id);
            kernel_container_projection_at(&self.snapshot_k(), ctn_ptr); kernel_process_projection_at(&self.snapshot_k(), prc_ptr);
        };
        assert(kernel_u_only_process_quota_1g_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, prc_ptr, ctn_ptr, delta)) by {
            kernel_process_quota_1g_changed_implies_u_step(&self.snapshot_k(), krnl, cpu_id, prc_ptr, ctn_ptr, delta);
            reveal(kernel_k_to_kernel_u);
        };
        self.end_kernel_step_raw(krnl, lctx);
    }

    pub proof fn end_kernel_step_process2thread_quota_1g_changed(tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, delta: int)
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_process2thread_quota_1g_changed(&old(self).snapshot_k(), krnl, cpu_id, prc_ptr, thrd_ptr, delta),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).snapshot_k() == *krnl,
            kernel_u_only_process2thread_quota_1g_changed(kernel_k_to_kernel_u(old(self).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, prc_ptr, thrd_ptr, delta),
            {
                let old_u = kernel_k_to_kernel_u(old(self).snapshot_k());
                let cpu = old_u.cpu_array[cpu_id as int];
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_process == Some(prc_ptr)
                &&& cpu.current_thread == Some(thrd_ptr)
                &&& old_u.process_map.dom().contains(prc_ptr)
                &&& old_u.process_map.spec_index(prc_ptr).lock_state is Unlocked
                &&& !old_u.process_map.spec_index(prc_ptr).killed
                &&& old_u.process_map.spec_index(prc_ptr).quota_1g >= delta
                &&& old_u.thread_map.dom().contains(thrd_ptr)
                &&& old_u.thread_map.spec_index(thrd_ptr).lock_state is Unlocked
                &&& !old_u.thread_map.spec_index(thrd_ptr).killed
                &&& old_u.thread_map.spec_index(thrd_ptr).quota_1g + delta <= usize::MAX
                &&& delta > 0
            },
    {
        hide(kernel_k_user_projection);
        reveal(kernel_u_only_process2thread_quota_1g_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.process_map.spec_index(prc_ptr).lock_state is Unlocked
            &&& pre_u.thread_map.spec_index(thrd_ptr).lock_state is Unlocked
        }) by {
            reveal(kernel_process2thread_quota_1g_changed); kernel_cpu_projection_at(&self.snapshot_k(), cpu_id); kernel_process_projection_at(&self.snapshot_k(), prc_ptr);
            kernel_thread_projection_at(&self.snapshot_k(), thrd_ptr);
        };
        assert(kernel_u_only_process2thread_quota_1g_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, prc_ptr, thrd_ptr, delta)) by {
            kernel_process2thread_quota_1g_changed_implies_u_step(&self.snapshot_k(), krnl, cpu_id, prc_ptr, thrd_ptr, delta);
            reveal(kernel_k_to_kernel_u);
        };
        self.end_kernel_step_raw(krnl, lctx);
    }
}
}
