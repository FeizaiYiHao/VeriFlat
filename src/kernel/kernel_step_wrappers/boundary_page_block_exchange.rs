#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal};
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
            old(self).thrd_mp.spec_index(thread).view().quota_4k + 512 == old(steps).snapshot_k().thrd_mp.spec_index(thread).view().quota_4k,
            old(self).thrd_mp.spec_index(thread).view().quota_2m == old(steps).snapshot_k().thrd_mp.spec_index(thread).view().quota_2m + 1,
        ensures
            kernel_step_boundary_framing(*old(self), *final(self), *old(lctx)),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == old(steps).view().push(KernelStep { old_u: old(steps).snapshot_u(), new_u: kernel_k_to_kernel_u(*old(self)) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
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
            old(self).thrd_mp.spec_index(thread).view().quota_2m + 1 == old(steps).snapshot_k().thrd_mp.spec_index(thread).view().quota_2m,
            old(self).thrd_mp.spec_index(thread).view().quota_4k == old(steps).snapshot_k().thrd_mp.spec_index(thread).view().quota_4k + 512,
        ensures
            kernel_step_boundary_framing(*old(self), *final(self), *old(lctx)),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == old(steps).view().push(KernelStep { old_u: old(steps).snapshot_u(), new_u: kernel_k_to_kernel_u(*old(self)) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
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
        assert(steps.snapshot_u().thread_map[thread].quota_2m != kernel_k_to_kernel_u(*self).thread_map[thread].quota_2m) by {
            kernel_thread_projection_at(&steps.snapshot_k(), thread); kernel_thread_projection_at(&*self, thread);
        };
        self.kernel_step_boundary_raw(lctx, steps);
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

    }
}

impl KernelSteps {
    pub proof fn end_kernel_step_thread_quota_4k_to_2m_exchanged(tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, thread: RwLockThreadPtr)
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            old(self).snapshot_k().thrd_mp.dom().contains(thread),
            krnl.thrd_mp.dom().contains(thread),
            krnl.thrd_mp.spec_index(thread).view().quota_4k + 512 == old(self).snapshot_k().thrd_mp.spec_index(thread).view().quota_4k,
            krnl.thrd_mp.spec_index(thread).view().quota_2m == old(self).snapshot_k().thrd_mp.spec_index(thread).view().quota_2m + 1,
        ensures
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
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

    pub proof fn end_kernel_step_thread_quota_2m_to_4k_exchanged(tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, thread: RwLockThreadPtr)
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            old(self).snapshot_k().thrd_mp.dom().contains(thread),
            krnl.thrd_mp.dom().contains(thread),
            krnl.thrd_mp.spec_index(thread).view().quota_2m + 1 == old(self).snapshot_k().thrd_mp.spec_index(thread).view().quota_2m,
            krnl.thrd_mp.spec_index(thread).view().quota_4k == old(self).snapshot_k().thrd_mp.spec_index(thread).view().quota_4k + 512,
        ensures
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).snapshot_k() == *krnl,
    {
        use_type_invariant(&*self);
        assert(self.snapshot_u().thread_map[thread].quota_2m != kernel_k_to_kernel_u(*krnl).thread_map[thread].quota_2m) by {
            kernel_thread_projection_at(&self.snapshot_k(), thread); kernel_thread_projection_at(krnl, thread);
        };
        self.end_kernel_step_raw(krnl, lctx);
    }

    pub proof fn end_kernel_step_cpu_and_thread_quotas_unchanged(tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext,
        cpu_id: CpuId, thread: RwLockThreadPtr)
        requires
            index_valid(NUM_CPUS, cpu_id),
            old(self).snapshot_k().inv(),
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            old(self).snapshot_k().thrd_mp.dom().contains(thread),
            krnl.thrd_mp.dom().contains(thread),
            *krnl == (KernelK { pg_arr: krnl.pg_arr, allc_4k_mp: krnl.allc_4k_mp, allc_2m_mp: krnl.allc_2m_mp,
                cpu_arr: krnl.cpu_arr, cpu_op: krnl.cpu_op, thrd_mp: krnl.thrd_mp, ..old(self).snapshot_k() }),
            krnl.allc_4k_mp.dom() == old(self).snapshot_k().allc_4k_mp.dom(),
            krnl.allc_2m_mp.dom() == old(self).snapshot_k().allc_2m_mp.dom(),
            forall|allocator: RwLockPageAllocatorPtr| #![trigger krnl.allc_4k_mp.spec_index(allocator)] old(self).snapshot_k().allc_4k_mp.dom().contains(allocator) ==>
                krnl.allc_4k_mp.spec_index(allocator).quota == old(self).snapshot_k().allc_4k_mp.spec_index(allocator).quota,
            forall|allocator: RwLockPageAllocatorPtr| #![trigger krnl.allc_2m_mp.spec_index(allocator)] old(self).snapshot_k().allc_2m_mp.dom().contains(allocator) ==>
                krnl.allc_2m_mp.spec_index(allocator).quota == old(self).snapshot_k().allc_2m_mp.spec_index(allocator).quota,
            krnl.cpu_arr.entries_unchanged_except(&old(self).snapshot_k().cpu_arr, cpu_id),
            krnl.cpu_arr.spec_index(cpu_id).view().view().view() == old(self).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view(),
            krnl.cpu_arr.spec_index(cpu_id).view().being_killed() == old(self).snapshot_k().cpu_arr.spec_index(cpu_id).view().being_killed(),
            krnl.cpu_arr.spec_index(cpu_id).view().killer_info() == old(self).snapshot_k().cpu_arr.spec_index(cpu_id).view().killer_info(),
            forall|other: CpuId| #![trigger krnl.cpu_op.view().view().spec_index(other as int)] index_valid(NUM_CPUS, other) && other != cpu_id ==>
                krnl.cpu_op.view().view().spec_index(other as int) == old(self).snapshot_k().cpu_op.view().view().spec_index(other as int),
            krnl.cpu_op.view().view()[cpu_id as int] == old(self).snapshot_k().cpu_op.view().view()[cpu_id as int],
            krnl.cpu_arr.spec_index(cpu_id).view().locking_thread() is None,
            old(self).snapshot_k().cpu_arr.spec_index(cpu_id).view().locking_thread() is None,
            krnl.thrd_mp.unchanged_except(&old(self).snapshot_k().thrd_mp, thread),
            krnl.thrd_mp.spec_index(thread).view() == old(self).snapshot_k().thrd_mp.spec_index(thread).view(),
            krnl.thrd_mp.spec_index(thread).being_killed() == old(self).snapshot_k().thrd_mp.spec_index(thread).being_killed(),
            krnl.thrd_mp.spec_index(thread).locking_thread() is None,
            old(self).snapshot_k().thrd_mp.spec_index(thread).locking_thread() is None,
        ensures
            final(self).view() == old(self).view(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            final(self).snapshot_k() == *krnl,
    {
        hide(kernel_k_user_projection);
        use_type_invariant(&*self);
        let pre = self.snapshot_k();
        kernel_u_domains_projection(&pre); kernel_u_domains_projection(krnl);
        let pre_u = kernel_k_to_kernel_u(pre);
        let post_u = kernel_k_to_kernel_u(*krnl);
        assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(&pre, i as usize); kernel_cpu_projection_at(krnl, i as usize); } });
        assert_maps_equal!(post_u.thread_map, pre_u.thread_map, ptr => { if pre.thrd_mp.dom().contains(ptr) { kernel_thread_projection_at(&pre, ptr); kernel_thread_projection_at(krnl, ptr); } });
        assert_maps_equal!(post_u.container_map, pre_u.container_map, ptr => {
            if pre.ctn_mp.dom().contains(ptr) {
                kernel_container_projection_at(&pre, ptr); kernel_container_projection_at(krnl, ptr);
                container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, ptr);
            }
        });
        assert_maps_equal!(post_u.process_map, pre_u.process_map, ptr => { if pre.prc_mp.dom().contains(ptr) { kernel_process_projection_at(&pre, ptr); kernel_process_projection_at(krnl, ptr); } });
        assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, ptr => { if pre.ep_mp.dom().contains(ptr) { kernel_endpoint_projection_at(&pre, ptr); kernel_endpoint_projection_at(krnl, ptr); } });
        reveal(kernel_k_to_kernel_u);
        self.end_kernel_step_raw(krnl, lctx);
    }
}

}
