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

/// Freeing a 1G page of the write-held table `table` to its owner `owner`'s 1G allocator `allc_ptr`, whose quota grows by one while every window lock stays, grows the 1G quota of `owner`, which is `origin` or one of its ancestors.
pub proof fn kernel_page_freed_to_owner_quota_1g_implies_u_step(
    pre: &KernelK, post: &KernelK, table: RwLockPageTableRoot, owner: RwLockContainerPtr, allc_ptr: RwLockPageAllocatorPtr, origin: RwLockContainerPtr,
)
    requires
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        process_iommu_table_wf(post.prc_mp, post.it_mp),
        container_allocator_wf(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp),
        *post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, pg_arr: post.pg_arr, allc_1g_mp: post.allc_1g_mp, ..*pre }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post),
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), p).lower.pagetable_window_locks == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), p).lower.pagetable_window_locks,
        post.pt_mp.unchanged_except(&pre.pt_mp, table) && post.pt_mp.spec_index(table).locking_thread() == pre.pt_mp.spec_index(table).locking_thread(),
        pre.ctn_mp.dom().contains(owner),
        pre.ctn_mp.dom().contains(origin),
        owner == origin || pre.ctn_mp.spec_index(origin).view().uppertree_seq.view().contains(owner),
        pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_1g == allc_ptr,
        pre.allc_1g_mp.dom().contains(allc_ptr),
        post.allc_1g_mp.dom() == pre.allc_1g_mp.dom(),
        forall|a: RwLockPageAllocatorPtr| #![trigger post.allc_1g_mp.spec_index(a)]
            pre.allc_1g_mp.dom().contains(a) && a != allc_ptr ==> post.allc_1g_mp.spec_index(a).quota.view().view() == pre.allc_1g_mp.spec_index(a).quota.view().view(),
        post.allc_1g_mp.spec_index(allc_ptr).quota.view().view() == pre.allc_1g_mp.spec_index(allc_ptr).quota.view().view() + 1,
    ensures
        kernel_u_container_quota_1g_increased(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), origin),
        kernel_k_to_kernel_u(*pre) != kernel_k_to_kernel_u(*post),
{
    let mid = KernelK { allc_1g_mp: pre.allc_1g_mp, ..*post };
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(pre, &mid)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
    kernel_endpoint_nonlock_fields_unchanged_for_equal(pre.ep_mp, mid.ep_mp);
    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(pre, &mid)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
    kernel_lock_states_unchanged_except_tables_of_implies_u_eq(pre, &mid, None);
    container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, owner);
    assert(kernel_container_quota_1g_changed(&mid, post, owner, 1)) by { reveal(kernel_container_quota_1g_changed); reveal(kernel_thread_nonlock_fields_unchanged); reveal(container_allocator_wf); };
    kernel_container_quota_1g_changed_implies_u_step(&mid, post, owner, 1);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    kernel_u_domains_projection(pre); kernel_container_projection_at(pre, origin);
    assert(kernel_u_container_quota_1g_increased(a, b, origin)) by {
        reveal(kernel_u_container_quota_1g_increased);
        kernel_container_ancestry_projection_at(pre, origin);
        assert_sets_equal!(a.container_map.dom().filter(|c: RwLockContainerPtr| a.container_map[c] != b.container_map[c]), set![owner]);
        assert_sets_equal!(b.container_map.dom(), a.container_map.dom());
    };
}


impl KernelK {
    /// Records the step that returns `delta` 1G quota to `ctn_ptr`, an ancestor of `origin` or `origin` itself.
    pub proof fn kernel_step_boundary_container_quota_1g_changed(tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, ctn_ptr: RwLockContainerPtr, delta: int, origin: RwLockContainerPtr)
        requires
            old(self).inv(),
            delta > 0,
            kernel_container_quota_1g_changed(&old(steps).snapshot_k(), old(self), ctn_ptr, delta),
            old(steps).snapshot_k().ctn_mp.dom().contains(origin),
            ctn_ptr == origin || old(steps).snapshot_k().ctn_mp.spec_index(origin).view().uppertree_seq.view().contains(ctn_ptr),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            kernel_u_container_quota_1g_increased(old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(self)), origin),
            old(steps).snapshot_u().container_map.dom().contains(ctn_ptr),
            kernel_k_to_kernel_u(*old(self)).container_map[ctn_ptr].quota_1g as int == old(steps).snapshot_u().container_map[ctn_ptr].quota_1g as int + delta,
            final(steps).view() == old(steps).view().push(KernelStep { old_u: old(steps).snapshot_u(), new_u: kernel_k_to_kernel_u(*old(self)) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            kernel_steps_prefix_unchanged(old(steps).view(), final(steps).view()),
            kernel_k_to_kernel_u(*old(self)) == (KernelU { container_map: old(steps).snapshot_u().container_map.insert(ctn_ptr, ContainerU {
                quota_1g: (old(steps).snapshot_u().container_map[ctn_ptr].quota_1g as int + delta) as usize,
                ..old(steps).snapshot_u().container_map[ctn_ptr]
            }), ..old(steps).snapshot_u() }),
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            kernel_step_boundary_framing(*old(self), *final(self), *old(lctx)),
            old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()) && (old(self).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep || old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().kernel_call_perm() is None)
                ==> final(self).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep && final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().kernel_call_perm() is None,
            forall|t: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(t)] old(lctx).thread_lock_map().dom().contains(t) ==> {
                let owner = old(self).thrd_mp.spec_index(t).view().owning_container;
                &&& old(self).ctn_mp.dom().contains(owner)
                &&& final(self).ctn_mp.spec_index(owner).view().uppertree_seq == old(self).ctn_mp.spec_index(owner).view().uppertree_seq
            },
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
        if old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()) { cpu_op_wf_at(old(self).cpu_op.view().view(), old(self).cpu_arr, old(lctx).cpu_id()); cpu_op_wf_at(self.cpu_op.view().view(), self.cpu_arr, old(lctx).cpu_id()); }
        old(self).thrd_mp.typed_lock_map_aligned_held_in_dom(old(lctx).thread_lock_map(), old(lctx).thread_id()); reveal(container_thread_wf);
    }
}

pub(super) proof fn kernel_process_quota_1g_changed_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr, delta: int)
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

pub(super) proof fn kernel_process2thread_quota_1g_changed_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, delta: int)
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
}
