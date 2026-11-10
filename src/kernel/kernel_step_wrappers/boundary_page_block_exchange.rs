#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
    pub proof fn kernel_step_boundary_free_4k_block_merged(tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, thread: RwLockThreadPtr, allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr)
        requires
            old(self).inv(),
            old(self).allc_4k_mp.dom().contains(allocator_4k),
            old(self).allc_2m_mp.dom().contains(allocator_2m),
            old(lctx).allocator_global_pool_4k_lock_map().dom().contains(allocator_4k),
            old(lctx).allocator_global_pool_2m_lock_map().dom().contains(allocator_2m),
            forall|cpu: CpuId| #![trigger old(lctx).allocator_cache_4k_lock_map().dom().contains((allocator_4k, cpu))] cpu < NUM_CPUS ==>
                old(lctx).allocator_cache_4k_lock_map().dom().contains((allocator_4k, cpu)),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
            old(steps).snapshot_k().thrd_mp.dom().contains(thread),
            old(self).thrd_mp.dom().contains(thread),
            old(self).thrd_mp.spec_index(thread).view().quota_4k != old(steps).snapshot_k().thrd_mp.spec_index(thread).view().quota_4k,
        ensures
            kernel_step_boundary_framing(*old(self), *final(self), *old(lctx)),
            old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()) && (old(self).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep || old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().kernel_call_perm() is None)
                ==> final(self).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep && final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().kernel_call_perm() is None,
            forall|p: RwLockPageTableRoot| #![trigger old(lctx).pagetable_lock_map().dom().contains(p)] typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), p, TypedLockMode::Write)
                ==> whole_pagetable(final(self).pt_mp, final(self).pt_lower.view(), p) == whole_pagetable(old(self).pt_mp, old(self).pt_lower.view(), p),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == old(steps).view().push(KernelStep { old_u: old(steps).snapshot_u(), new_u: kernel_k_to_kernel_u(*old(self)) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            kernel_steps_prefix_unchanged(old(steps).view(), final(steps).view()),
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).snapshot_k() == *final(self),
            forall|allocator: RwLockPageAllocatorPtr, source: usize|
                #![trigger old(lctx).allocator_cache_4k_lock_map().dom().contains((allocator, source))]
                #![trigger final(self).allc_4k_mp.spec_index(allocator).merge_2m_source_list(source)] source <= NUM_CPUS && old(self).allc_4k_mp.dom().contains(allocator)
                && (if source < NUM_CPUS { old(lctx).allocator_cache_4k_lock_map().dom().contains((allocator, source)) }
                    else { old(lctx).allocator_global_pool_4k_lock_map().dom().contains(allocator) }) ==> {
                    &&& final(self).allc_4k_mp.dom().contains(allocator)
                    &&& final(self).allc_4k_mp.spec_index(allocator).merge_2m_source_list(source) == old(self).allc_4k_mp.spec_index(allocator).merge_2m_source_list(source)
                },
            final(self).allc_4k_mp.dom().contains(allocator_4k),
            final(self).allc_2m_mp.dom().contains(allocator_2m),
            final(self).allc_4k_mp.spec_index(allocator_4k).owning_container == old(self).allc_4k_mp.spec_index(allocator_4k).owning_container,
            final(self).allc_2m_mp.spec_index(allocator_2m).owning_container == old(self).allc_2m_mp.spec_index(allocator_2m).owning_container,
            final(self).allc_2m_mp.spec_index(allocator_2m).global_pool == old(self).allc_2m_mp.spec_index(allocator_2m).global_pool,
            forall|page: PageIndex| #![trigger final(self).pg_arr.spec_index(page).view().view().state] #![trigger final(self).pg_arr.lock_id_by_index(page)]
                index_valid(NUM_PAGES, page) && (old(self).pg_arr.spec_index(page).view().view().state matches PageState::Free4k { allocator_ptr, state: _ } && allocator_ptr.view() == allocator_4k) ==> {
                    &&& final(self).pg_arr.spec_index(page).view().view().state == old(self).pg_arr.spec_index(page).view().view().state
                    &&& final(self).pg_arr.spec_index(page).view().view().owning_container == old(self).pg_arr.spec_index(page).view().view().owning_container
                    &&& final(self).pg_arr.lock_id_by_index(page).major == FREE_PAGE_LOCK_MAJOR
                },
            forall|target: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(target)] old(lctx).thread_lock_map().dom().contains(target) && old(self).thrd_mp.dom().contains(target) ==> {
                &&& final(self).thrd_mp.dom().contains(target)
                &&& final(self).thrd_mp.spec_index(target).view_lock() == old(self).thrd_mp.spec_index(target).view_lock()
                &&& final(self).thrd_mp.spec_index(target).is_init() == old(self).thrd_mp.spec_index(target).is_init()
                &&& final(self).thrd_mp.spec_index(target).view_rodata() == old(self).thrd_mp.spec_index(target).view_rodata()
                &&& final(self).thrd_mp.spec_index(target).view() == old(self).thrd_mp.spec_index(target).view()
                &&& final(self).thrd_mp.spec_index(target).locking_thread() == old(self).thrd_mp.spec_index(target).locking_thread()
                &&& final(self).thrd_mp.spec_index(target).control() == old(self).thrd_mp.spec_index(target).control()
            },
            old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()) ==> {
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view_lock() == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view_lock()
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().is_init() == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().is_init()
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view_rodata() == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view_rodata()
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view() == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view()
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().locking_thread() == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().locking_thread()
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().control() == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().control()
            },
    {
        use_type_invariant(&*steps);
        assert(steps.snapshot_u().thread_map[thread].quota_4k != kernel_k_to_kernel_u(*self).thread_map[thread].quota_4k) by {
            kernel_thread_projection_at(&steps.snapshot_k(), thread); kernel_thread_projection_at(&*self, thread);
        };
        self.kernel_step_boundary_raw(lctx, steps);
        assert(forall|p: RwLockPageTableRoot| #![trigger old(lctx).pagetable_lock_map().dom().contains(p)] typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), p, TypedLockMode::Write)
            ==> whole_pagetable(self.pt_mp, self.pt_lower.view(), p) == whole_pagetable(old(self).pt_mp, old(self).pt_lower.view(), p)) by { reveal(LockedMap::typed_lock_map_aligned); };
        reveal(allocator_free_4k_pages_wf); reveal(allocator_cpu_cache_4k_pages_wf); reveal(allocator_global_pool_4k_pages_wf);
        reveal(page_array_wf); reveal(LockedArray::lock_id_by_index);
        page_ptr_roundtrip(); page_index_roundtrip();
        assert(self.allc_4k_mp.spec_index(allocator_4k).owning_container == old(self).allc_4k_mp.spec_index(allocator_4k).owning_container) by {
            allocator_perms_wf_at(old(self).allc_4k_mp, allocator_4k); allocator_perms_wf_at(self.allc_4k_mp, allocator_4k);
            seq![self.allc_4k_mp.spec_index(allocator_4k).owning_container].lemma_index_contains(0);
            seq![old(self).allc_4k_mp.spec_index(allocator_4k).owning_container].lemma_index_contains(0);
        };
        assert(self.allc_2m_mp.spec_index(allocator_2m).owning_container == old(self).allc_2m_mp.spec_index(allocator_2m).owning_container) by {
            allocator_perms_wf_at(old(self).allc_2m_mp, allocator_2m); allocator_perms_wf_at(self.allc_2m_mp, allocator_2m);
            seq![self.allc_2m_mp.spec_index(allocator_2m).owning_container].lemma_index_contains(0);
            seq![old(self).allc_2m_mp.spec_index(allocator_2m).owning_container].lemma_index_contains(0);
        };
        reveal(kernel_steps_prefix_unchanged);
        if old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()) { cpu_op_wf_at(old(self).cpu_op.view().view(), old(self).cpu_arr, old(lctx).cpu_id()); cpu_op_wf_at(self.cpu_op.view().view(), self.cpu_arr, old(lctx).cpu_id()); }
    }

    pub proof fn kernel_step_boundary_free_2m_block_split(tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, thread: RwLockThreadPtr, allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr)
        requires
            old(self).inv(),
            old(self).allc_2m_mp.dom().contains(allocator_2m),
            old(self).allc_4k_mp.dom().contains(allocator_4k),
            old(lctx).allocator_global_pool_2m_lock_map().dom().contains(allocator_2m),
            old(lctx).allocator_global_pool_4k_lock_map().dom().contains(allocator_4k),
            forall|cpu: CpuId| #![trigger old(lctx).allocator_cache_2m_lock_map().dom().contains((allocator_2m, cpu))] cpu < NUM_CPUS ==>
                old(lctx).allocator_cache_2m_lock_map().dom().contains((allocator_2m, cpu)),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
            old(steps).snapshot_k().thrd_mp.dom().contains(thread),
            old(self).thrd_mp.dom().contains(thread),
            old(self).thrd_mp.spec_index(thread).view().quota_4k != old(steps).snapshot_k().thrd_mp.spec_index(thread).view().quota_4k,
        ensures
            kernel_step_boundary_framing(*old(self), *final(self), *old(lctx)),
            old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()) && (old(self).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep || old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().kernel_call_perm() is None)
                ==> final(self).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep && final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().kernel_call_perm() is None,
            forall|p: RwLockPageTableRoot| #![trigger old(lctx).pagetable_lock_map().dom().contains(p)] typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), p, TypedLockMode::Write)
                ==> whole_pagetable(final(self).pt_mp, final(self).pt_lower.view(), p) == whole_pagetable(old(self).pt_mp, old(self).pt_lower.view(), p),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == old(steps).view().push(KernelStep { old_u: old(steps).snapshot_u(), new_u: kernel_k_to_kernel_u(*old(self)) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            kernel_steps_prefix_unchanged(old(steps).view(), final(steps).view()),
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).snapshot_k() == *final(self),
            forall|allocator: RwLockPageAllocatorPtr, source: usize|
                #![trigger old(lctx).allocator_cache_2m_lock_map().dom().contains((allocator, source))]
                #![trigger final(self).allc_2m_mp.spec_index(allocator).merge_2m_source_list(source)] source <= NUM_CPUS && old(self).allc_2m_mp.dom().contains(allocator)
                && (if source < NUM_CPUS { old(lctx).allocator_cache_2m_lock_map().dom().contains((allocator, source)) }
                    else { old(lctx).allocator_global_pool_2m_lock_map().dom().contains(allocator) }) ==> {
                    &&& final(self).allc_2m_mp.dom().contains(allocator)
                    &&& final(self).allc_2m_mp.spec_index(allocator).merge_2m_source_list(source) == old(self).allc_2m_mp.spec_index(allocator).merge_2m_source_list(source)
                },
            final(self).allc_2m_mp.dom().contains(allocator_2m),
            final(self).allc_4k_mp.dom().contains(allocator_4k),
            final(self).allc_2m_mp.spec_index(allocator_2m).owning_container == old(self).allc_2m_mp.spec_index(allocator_2m).owning_container,
            final(self).allc_4k_mp.spec_index(allocator_4k).owning_container == old(self).allc_4k_mp.spec_index(allocator_4k).owning_container,
            final(self).allc_4k_mp.spec_index(allocator_4k).global_pool == old(self).allc_4k_mp.spec_index(allocator_4k).global_pool,
            forall|page: PageIndex| #![trigger final(self).pg_arr.spec_index(page).view().view().state] #![trigger final(self).pg_arr.lock_id_by_index(page)]
                index_valid(NUM_PAGES, page) && (old(self).pg_arr.spec_index(page).view().view().state matches PageState::Free2m { allocator_ptr, state: _ } && allocator_ptr.view() == allocator_2m) ==> {
                    &&& final(self).pg_arr.spec_index(page).view().view().state == old(self).pg_arr.spec_index(page).view().view().state
                    &&& final(self).pg_arr.spec_index(page).view().view().owning_container == old(self).pg_arr.spec_index(page).view().view().owning_container
                    &&& final(self).pg_arr.lock_id_by_index(page).major == FREE_PAGE_LOCK_MAJOR
                },
            forall|target: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(target)] old(lctx).thread_lock_map().dom().contains(target) && old(self).thrd_mp.dom().contains(target) ==> {
                &&& final(self).thrd_mp.dom().contains(target)
                &&& final(self).thrd_mp.spec_index(target).view_lock() == old(self).thrd_mp.spec_index(target).view_lock()
                &&& final(self).thrd_mp.spec_index(target).is_init() == old(self).thrd_mp.spec_index(target).is_init()
                &&& final(self).thrd_mp.spec_index(target).view_rodata() == old(self).thrd_mp.spec_index(target).view_rodata()
                &&& final(self).thrd_mp.spec_index(target).view() == old(self).thrd_mp.spec_index(target).view()
                &&& final(self).thrd_mp.spec_index(target).locking_thread() == old(self).thrd_mp.spec_index(target).locking_thread()
                &&& final(self).thrd_mp.spec_index(target).control() == old(self).thrd_mp.spec_index(target).control()
            },
            old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()) ==> {
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view_lock() == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view_lock()
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().is_init() == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().is_init()
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view_rodata() == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view_rodata()
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view() == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view()
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().locking_thread() == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().locking_thread()
                &&& final(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().control() == old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().control()
            },
    {
        use_type_invariant(&*steps);
        assert(steps.snapshot_u().thread_map[thread].quota_4k != kernel_k_to_kernel_u(*self).thread_map[thread].quota_4k) by {
            kernel_thread_projection_at(&steps.snapshot_k(), thread); kernel_thread_projection_at(&*self, thread);
        };
        self.kernel_step_boundary_raw(lctx, steps);
        assert(forall|p: RwLockPageTableRoot| #![trigger old(lctx).pagetable_lock_map().dom().contains(p)] typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), p, TypedLockMode::Write)
            ==> whole_pagetable(self.pt_mp, self.pt_lower.view(), p) == whole_pagetable(old(self).pt_mp, old(self).pt_lower.view(), p)) by { reveal(LockedMap::typed_lock_map_aligned); };
        reveal(allocator_free_2m_pages_wf); reveal(allocator_cpu_cache_2m_pages_wf); reveal(allocator_global_pool_2m_pages_wf);
        reveal(page_array_wf); reveal(LockedArray::lock_id_by_index);
        page_ptr_roundtrip(); page_index_roundtrip();
        assert(self.allc_2m_mp.spec_index(allocator_2m).owning_container == old(self).allc_2m_mp.spec_index(allocator_2m).owning_container) by {
            allocator_perms_wf_at(old(self).allc_2m_mp, allocator_2m); allocator_perms_wf_at(self.allc_2m_mp, allocator_2m);
            seq![self.allc_2m_mp.spec_index(allocator_2m).owning_container].lemma_index_contains(0);
            seq![old(self).allc_2m_mp.spec_index(allocator_2m).owning_container].lemma_index_contains(0);
        };
        assert(self.allc_4k_mp.spec_index(allocator_4k).owning_container == old(self).allc_4k_mp.spec_index(allocator_4k).owning_container) by {
            allocator_perms_wf_at(old(self).allc_4k_mp, allocator_4k); allocator_perms_wf_at(self.allc_4k_mp, allocator_4k);
            seq![self.allc_4k_mp.spec_index(allocator_4k).owning_container].lemma_index_contains(0);
            seq![old(self).allc_4k_mp.spec_index(allocator_4k).owning_container].lemma_index_contains(0);
        };
        reveal(kernel_steps_prefix_unchanged);
        if old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()) { cpu_op_wf_at(old(self).cpu_op.view().view(), old(self).cpu_arr, old(lctx).cpu_id()); cpu_op_wf_at(self.cpu_op.view().view(), self.cpu_arr, old(lctx).cpu_id()); }
    }
}

impl KernelSteps {
    /// Ends a section that changed the thread's 4K quota, recording the changed user view.
    pub proof fn end_kernel_step_thread_quota_4k_changed(tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, thread: RwLockThreadPtr)
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            old(self).snapshot_k().thrd_mp.dom().contains(thread),
            krnl.thrd_mp.dom().contains(thread),
            krnl.thrd_mp.spec_index(thread).view().quota_4k != old(self).snapshot_k().thrd_mp.spec_index(thread).view().quota_4k,
        ensures
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            kernel_steps_prefix_unchanged(old(self).view(), final(self).view()),
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).snapshot_k() == *krnl,
    {
        use_type_invariant(&*self);
        assert(self.snapshot_u().thread_map[thread].quota_4k != kernel_k_to_kernel_u(*krnl).thread_map[thread].quota_4k) by {
            kernel_thread_projection_at(&self.snapshot_k(), thread); kernel_thread_projection_at(krnl, thread);
        };
        self.end_kernel_step_raw(krnl, lctx);
    }
}

}
