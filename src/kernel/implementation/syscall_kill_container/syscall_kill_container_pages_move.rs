use vstd::prelude::*;
use crate::*;
use super::super::syscall_kill_process::syscall_kill_process_spec::KillTraceCtx;
#[cfg(feature = "split-crates")]
use veriflat_alloc_page::free_4k_page::kill_container_move_free_page_4k::kill_container_move_free_page_4k;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::free_4k_page::kill_container_move_free_page_4k::kill_container_move_free_page_4k;
#[cfg(feature = "split-crates")]
use veriflat_alloc_page::allocate_free_2m_page::kill_container_move_free_page_2m::kill_container_move_free_page_2m;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::allocate_free_2m_page::kill_container_move_free_page_2m::kill_container_move_free_page_2m;
#[cfg(verus_keep_ghost)]
use super::super::syscall_kill_process::syscall_kill_process_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_trace::kill_container_trace_push;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_pages_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_pages_trace::*;

verus! {
/// Move every page in the global pool of the marked container's 4K allocator `a4` to the global pool of the killer's
/// container's 4K allocator together with one page of 4K quota, one container kill step per page.
pub(crate) fn kill_container_pages_move_4k(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr, a4: RwLockPageAllocatorPtr, o4: RwLockPageAllocatorPtr,
    a2: RwLockPageAllocatorPtr, o2: RwLockPageAllocatorPtr, Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>,
    Tracked(thread_perm): Tracked<&LockPerm>, Tracked(container_perm): Tracked<&LockPerm>, Tracked(owner_perm): Tracked<&LockPerm>,
    Tracked(caches_4k): Tracked<&Map<CpuId, LockPerm>>, Tracked(caches_2m): Tracked<&Map<CpuId, LockPerm>>, Tracked(pools_4k): Tracked<&Map<RwLockPageAllocatorPtr, LockPerm>>,
    Tracked(pools_2m): Tracked<&Map<RwLockPageAllocatorPtr, LockPerm>>, Tracked(quotas_4k): Tracked<&Map<RwLockPageAllocatorPtr, LockPerm>>,
    Tracked(quotas_2m): Tracked<&Map<RwLockPageAllocatorPtr, LockPerm>>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        kill_container_pages_killer_state(*old(krnl), *old(lctx), cpu_id, process_ptr, thread_ptr, container_ptr, owner_ptr, *cpu_perm, *process_perm, *thread_perm, *container_perm,
            *owner_perm),
        kill_container_pages_allocator_locks(*old(krnl), *old(lctx), container_ptr, owner_ptr, a4, o4, a2, o2, *caches_4k, *caches_2m, *pools_4k, *pools_2m, *quotas_4k, *quotas_2m),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        ctx is Container,
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_container_progress(container_ptr, ContainerKillStage::Pages),
        !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        kill_container_pages_killer_state(*final(krnl), *final(lctx), cpu_id, process_ptr, thread_ptr, container_ptr, owner_ptr, *cpu_perm, *process_perm, *thread_perm, *container_perm,
            *owner_perm),
        kill_container_pages_allocator_locks(*final(krnl), *final(lctx), container_ptr, owner_ptr, a4, o4, a2, o2, *caches_4k, *caches_2m, *pools_4k, *pools_2m, *quotas_4k, *quotas_2m),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == old(krnl).thr_mp.spec_index(thread_ptr).view(),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        final(krnl).allc_4k_mp.spec_index(a4).global_pool.view().view().len() == 0,
        forall|i: CpuId| #![trigger final(krnl).allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i)
            ==> final(krnl).allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().view() == old(krnl).allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().view(),
        forall|i: CpuId| #![trigger final(krnl).allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i)
            ==> final(krnl).allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().view() == old(krnl).allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().view(),
        final(krnl).allc_2m_mp.spec_index(a2).global_pool.view() == old(krnl).allc_2m_mp.spec_index(a2).global_pool.view(),
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
            &&& final(krnl).ctn_mp.dom().contains(c)
            &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
            &&& final(krnl).ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
            &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes
            &&& final(krnl).ctn_mp.spec_index(c).view().children == old(krnl).ctn_mp.spec_index(c).view().children
        },
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        forall|s: RwLockCpuSetPtr| #![trigger old(lctx).cpu_set_lock_map().dom().contains(s)] old(lctx).cpu_set_lock_map().dom().contains(s)
            ==> final(krnl).cpu_set_mp.dom().contains(s) && final(krnl).cpu_set_mp.spec_index(s) == old(krnl).cpu_set_mp.spec_index(s),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
{
    proof { allocator_perms_wf_map(krnl.allc_4k_mp); allocator_perms_wf_at(krnl.allc_4k_mp, a4); }
    let tracked pool_perm = pools_4k.tracked_borrow(a4);
    let n = krnl.allc_4k_mp.borrow_global_pool_typed(a4, Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(pool_perm)).linked_list.len();
    proof { krnl.allc_4k_mp.spec_index(a4).global_pool.view().linked_list.lemma_len_view(); }
    let mut moved: usize = 0;
    proof { held_kernel_objects_unchanged_reflexive(&*krnl, &*lctx); }
    while moved < n
        invariant
            lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            krnl.cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
            krnl.cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
            krnl.prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
            krnl.thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
            krnl.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
            krnl.thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
            krnl.thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
            forall|s: RwLockCpuSetPtr| #![trigger old(lctx).cpu_set_lock_map().dom().contains(s)] old(lctx).cpu_set_lock_map().dom().contains(s)
                ==> krnl.cpu_set_mp.dom().contains(s) && krnl.cpu_set_mp.spec_index(s) == old(krnl).cpu_set_mp.spec_index(s),
            forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
                &&& krnl.ctn_mp.dom().contains(c)
                &&& krnl.ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
                &&& krnl.ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
                &&& krnl.ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
                &&& krnl.ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
                &&& krnl.ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
                &&& krnl.ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes
                &&& krnl.ctn_mp.spec_index(c).view().children == old(krnl).ctn_mp.spec_index(c).view().children
            },
            0 <= moved <= n,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.kernel_view_locking_state() is Acquire,
            typed_lock_maps_unchanged(old(lctx), lctx),
            steps.snapshot_k() == *krnl,
            kill_container_pages_killer_state(*krnl, *lctx, cpu_id, process_ptr, thread_ptr, container_ptr, owner_ptr, *cpu_perm, *process_perm, *thread_perm, *container_perm,
                *owner_perm),
            kill_container_pages_allocator_locks(*krnl, *lctx, container_ptr, owner_ptr, a4, o4, a2, o2, *caches_4k, *caches_2m, *pools_4k, *pools_2m, *quotas_4k, *quotas_2m),
            krnl.thr_mp.spec_index(thread_ptr).view() == old(krnl).thr_mp.spec_index(thread_ptr).view(),
            0 <= start <= old(steps).view().len(),
            ctx is Container,
            old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_container_progress(container_ptr, ContainerKillStage::Pages),
            !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
            old(steps).view().len() <= steps.view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            kill_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, ctx),
            krnl.allc_4k_mp.spec_index(a4).global_pool.view().view().len() == n - moved,
            forall|i: CpuId| #![trigger krnl.allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i)
                ==> krnl.allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().view() == old(krnl).allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().view(),
            forall|i: CpuId| #![trigger krnl.allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i)
                ==> krnl.allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().view() == old(krnl).allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().view(),
            krnl.allc_2m_mp.spec_index(a2).global_pool.view() == old(krnl).allc_2m_mp.spec_index(a2).global_pool.view(),
        decreases n - moved,
    {
        proof { allocator_perms_wf_map(krnl.allc_4k_mp); allocator_perms_wf_at(krnl.allc_4k_mp, a4); }
        let tracked pool_perm = pools_4k.tracked_borrow(a4);
        let tracked owner_pool_perm = pools_4k.tracked_borrow(o4);
        let tracked quota_perm = quotas_4k.tracked_borrow(a4);
        let tracked owner_quota_perm = quotas_4k.tracked_borrow(o4);
        let pool = krnl.allc_4k_mp.borrow_global_pool_typed(a4, Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(pool_perm));
        assert(pool.linked_list.len() > 0) by { pool.linked_list.lemma_len_view(); };
        let (_, page_ptr) = pool.peek_head();
        assert(page_ptr_valid(page_ptr)) by { allocator_free_page_ptrs_wf_global_at(krnl.allc_4k_mp, a4, page_ptr); };
        let page_index = page_ptr2page_index(page_ptr);
        assert(page_ptr_valid(page_ptr) && index_valid(NUM_PAGES, page_index) && krnl.pg_arr.lock_id_by_index(page_index).major == FREE_PAGE_LOCK_MAJOR) by {
            reveal(LinkedList::wf_value_list);
            container_allocator_free_4k_page_wf_global_at(krnl.allc_4k_mp, krnl.pg_arr, a4, page_ptr); page_ptr_valid_imply_page_index_valid(); page_array_wf_at(krnl.pg_arr, page_index);
        };
        let ghost before = *krnl;
        let ghost before_lctx = *lctx;
        let ghost base_steps = steps.view();
        let Tracked(page_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));
        kill_container_move_free_page_4k(krnl, Tracked(&mut *lctx), container_ptr, owner_ptr, a4, o4, page_ptr, Tracked(container_perm), Tracked(owner_perm), Tracked(pool_perm), Tracked(owner_pool_perm),
            Tracked(quota_perm), Tracked(owner_quota_perm), Tracked(&page_perm));
        krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_perm));
        proof {
            let owned = before.ctn_mp.spec_index(container_ptr).view().owned_pages.view();
            let owner_owned = before.ctn_mp.spec_index(owner_ptr).view().owned_pages.view();
            assert(owned.remove(page_ptr) =~= owned.difference(set![page_ptr]) && owner_owned.insert(page_ptr) =~= owner_owned.union(set![page_ptr]) && set![page_ptr].subset_of(owned));
            assert(typed_lock_maps_unchanged(old(lctx), lctx)) by { map_insert_remove_absent_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: before.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write }); };
            let moved_k = *krnl;
            kernel_container_free_4k_page_moved_implies_u_step(&before, &moved_k, container_ptr, owner_ptr, set![page_ptr]);
            kill_container_pages_pre_from_k(&before, &before_lctx, cpu_id, process_ptr, thread_ptr, container_ptr);
            kill_container_move_page_step_from_u(kernel_k_to_kernel_u(before), kernel_k_to_kernel_u(moved_k), cpu_id, container_ptr, owner_ptr, set![page_ptr], PageSize::SZ4k);
            krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
            kill_container_trace_push(&*steps, base_steps, start, pre, kernel_k_to_kernel_u(before), kernel_k_to_kernel_u(moved_k), cpu_id, ctx);
        }
        moved = moved + 1;
    }
}

/// Move every page in the global pool of the marked container's 2M allocator `a2` to the global pool of the killer's
/// container's 2M allocator together with one page of 2M quota, one container kill step per page.
pub(crate) fn kill_container_pages_move_2m(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr, a4: RwLockPageAllocatorPtr, o4: RwLockPageAllocatorPtr,
    a2: RwLockPageAllocatorPtr, o2: RwLockPageAllocatorPtr, Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>,
    Tracked(thread_perm): Tracked<&LockPerm>, Tracked(container_perm): Tracked<&LockPerm>, Tracked(owner_perm): Tracked<&LockPerm>,
    Tracked(caches_4k): Tracked<&Map<CpuId, LockPerm>>, Tracked(caches_2m): Tracked<&Map<CpuId, LockPerm>>, Tracked(pools_4k): Tracked<&Map<RwLockPageAllocatorPtr, LockPerm>>,
    Tracked(pools_2m): Tracked<&Map<RwLockPageAllocatorPtr, LockPerm>>, Tracked(quotas_4k): Tracked<&Map<RwLockPageAllocatorPtr, LockPerm>>,
    Tracked(quotas_2m): Tracked<&Map<RwLockPageAllocatorPtr, LockPerm>>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        kill_container_pages_killer_state(*old(krnl), *old(lctx), cpu_id, process_ptr, thread_ptr, container_ptr, owner_ptr, *cpu_perm, *process_perm, *thread_perm, *container_perm,
            *owner_perm),
        kill_container_pages_allocator_locks(*old(krnl), *old(lctx), container_ptr, owner_ptr, a4, o4, a2, o2, *caches_4k, *caches_2m, *pools_4k, *pools_2m, *quotas_4k, *quotas_2m),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        ctx is Container,
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_container_progress(container_ptr, ContainerKillStage::Pages),
        !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        kill_container_pages_killer_state(*final(krnl), *final(lctx), cpu_id, process_ptr, thread_ptr, container_ptr, owner_ptr, *cpu_perm, *process_perm, *thread_perm, *container_perm,
            *owner_perm),
        kill_container_pages_allocator_locks(*final(krnl), *final(lctx), container_ptr, owner_ptr, a4, o4, a2, o2, *caches_4k, *caches_2m, *pools_4k, *pools_2m, *quotas_4k, *quotas_2m),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == old(krnl).thr_mp.spec_index(thread_ptr).view(),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        final(krnl).allc_2m_mp.spec_index(a2).global_pool.view().view().len() == 0,
        forall|i: CpuId| #![trigger final(krnl).allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i)
            ==> final(krnl).allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().view() == old(krnl).allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().view(),
        forall|i: CpuId| #![trigger final(krnl).allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i)
            ==> final(krnl).allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().view() == old(krnl).allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().view(),
        final(krnl).allc_4k_mp.spec_index(a4).global_pool.view() == old(krnl).allc_4k_mp.spec_index(a4).global_pool.view(),
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
            &&& final(krnl).ctn_mp.dom().contains(c)
            &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
            &&& final(krnl).ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
            &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes
            &&& final(krnl).ctn_mp.spec_index(c).view().children == old(krnl).ctn_mp.spec_index(c).view().children
        },
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        forall|s: RwLockCpuSetPtr| #![trigger old(lctx).cpu_set_lock_map().dom().contains(s)] old(lctx).cpu_set_lock_map().dom().contains(s)
            ==> final(krnl).cpu_set_mp.dom().contains(s) && final(krnl).cpu_set_mp.spec_index(s) == old(krnl).cpu_set_mp.spec_index(s),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
{
    proof { allocator_perms_wf_map(krnl.allc_2m_mp); allocator_perms_wf_at(krnl.allc_2m_mp, a2); }
    let tracked pool_perm = pools_2m.tracked_borrow(a2);
    let n = krnl.allc_2m_mp.borrow_global_pool_typed(a2, Ghost(lctx.allocator_global_pool_2m_lock_map()), Tracked(&*lctx), Tracked(pool_perm)).linked_list.len();
    proof { krnl.allc_2m_mp.spec_index(a2).global_pool.view().linked_list.lemma_len_view(); }
    let mut moved: usize = 0;
    proof { held_kernel_objects_unchanged_reflexive(&*krnl, &*lctx); }
    while moved < n
        invariant
            lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            krnl.cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
            krnl.cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
            krnl.prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
            krnl.thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
            krnl.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
            krnl.thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
            krnl.thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
            forall|s: RwLockCpuSetPtr| #![trigger old(lctx).cpu_set_lock_map().dom().contains(s)] old(lctx).cpu_set_lock_map().dom().contains(s)
                ==> krnl.cpu_set_mp.dom().contains(s) && krnl.cpu_set_mp.spec_index(s) == old(krnl).cpu_set_mp.spec_index(s),
            forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
                &&& krnl.ctn_mp.dom().contains(c)
                &&& krnl.ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
                &&& krnl.ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
                &&& krnl.ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
                &&& krnl.ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
                &&& krnl.ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
                &&& krnl.ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes
                &&& krnl.ctn_mp.spec_index(c).view().children == old(krnl).ctn_mp.spec_index(c).view().children
            },
            0 <= moved <= n,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.kernel_view_locking_state() is Acquire,
            typed_lock_maps_unchanged(old(lctx), lctx),
            steps.snapshot_k() == *krnl,
            kill_container_pages_killer_state(*krnl, *lctx, cpu_id, process_ptr, thread_ptr, container_ptr, owner_ptr, *cpu_perm, *process_perm, *thread_perm, *container_perm,
                *owner_perm),
            kill_container_pages_allocator_locks(*krnl, *lctx, container_ptr, owner_ptr, a4, o4, a2, o2, *caches_4k, *caches_2m, *pools_4k, *pools_2m, *quotas_4k, *quotas_2m),
            krnl.thr_mp.spec_index(thread_ptr).view() == old(krnl).thr_mp.spec_index(thread_ptr).view(),
            0 <= start <= old(steps).view().len(),
            ctx is Container,
            old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_container_progress(container_ptr, ContainerKillStage::Pages),
            !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
            old(steps).view().len() <= steps.view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            kill_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, ctx),
            krnl.allc_2m_mp.spec_index(a2).global_pool.view().view().len() == n - moved,
            forall|i: CpuId| #![trigger krnl.allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i)
                ==> krnl.allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().view() == old(krnl).allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().view(),
            forall|i: CpuId| #![trigger krnl.allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i)
                ==> krnl.allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().view() == old(krnl).allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().view(),
            krnl.allc_4k_mp.spec_index(a4).global_pool.view() == old(krnl).allc_4k_mp.spec_index(a4).global_pool.view(),
        decreases n - moved,
    {
        proof { allocator_perms_wf_map(krnl.allc_2m_mp); allocator_perms_wf_at(krnl.allc_2m_mp, a2); }
        let tracked pool_perm = pools_2m.tracked_borrow(a2);
        let tracked owner_pool_perm = pools_2m.tracked_borrow(o2);
        let tracked quota_perm = quotas_2m.tracked_borrow(a2);
        let tracked owner_quota_perm = quotas_2m.tracked_borrow(o2);
        let pool = krnl.allc_2m_mp.borrow_global_pool_typed(a2, Ghost(lctx.allocator_global_pool_2m_lock_map()), Tracked(&*lctx), Tracked(pool_perm));
        assert(pool.linked_list.len() > 0) by { pool.linked_list.lemma_len_view(); };
        let (_, page_ptr) = pool.peek_head();
        assert(page_ptr_valid(page_ptr)) by { allocator_free_page_ptrs_wf_global_at(krnl.allc_2m_mp, a2, page_ptr); };
        let page_index = page_ptr2page_index(page_ptr);
        assert(page_ptr_valid(page_ptr) && index_valid(NUM_PAGES, page_index) && krnl.pg_arr.lock_id_by_index(page_index).major == FREE_PAGE_LOCK_MAJOR && page_index_2m_valid(page_index)
            && krnl.pg_arr.spec_index(page_index).view().view().state is Free2m) by {
            reveal(LinkedList::wf_value_list);
            container_allocator_free_2m_page_wf_global_at(krnl.allc_2m_mp, krnl.pg_arr, a2, page_ptr); page_ptr_valid_imply_page_index_valid(); page_array_wf_at(krnl.pg_arr, page_index); hugepage_2m_wf_head_at(krnl.pg_arr, page_index);
        };
        let ghost before = *krnl;
        let ghost before_lctx = *lctx;
        let ghost base_steps = steps.view();
        let Tracked(page_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));
        assert(lctx.page_lock_map().dom().disjoint(page_2m_tail_indices(page_index)));
        let Tracked(tail_perms) = wlock_owned_2m_page_tails(krnl, page_index, Tracked(&mut *lctx));
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), page_index, TypedLockMode::Write)) by {
            let tails = page_2m_tail_indices(page_index);
            assert(!tails.contains(page_index));
            assert(lctx.page_lock_map().dom().difference(tails).contains(page_index));
            assert(lctx.page_lock_map().remove_keys(tails).index(page_index) == lctx.page_lock_map().index(page_index));
        };
        kill_container_move_free_page_2m(krnl, Tracked(&mut *lctx), container_ptr, owner_ptr, a2, o2, page_ptr, Tracked(container_perm), Tracked(owner_perm), Tracked(pool_perm), Tracked(owner_pool_perm),
            Tracked(quota_perm), Tracked(owner_quota_perm), Tracked(&page_perm), Tracked(&tail_perms));
        wunlock_owned_2m_page_tails(krnl, page_index, Tracked(&mut *lctx), Tracked(tail_perms));
        krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_perm));
        proof {
            assert(lctx.page_lock_map() =~= old(lctx).page_lock_map());
            let moved_k = *krnl;
            kernel_container_free_2m_page_moved_implies_u_step(&before, &moved_k, container_ptr, owner_ptr, page_2m_all_ptrs(page_index));
            kill_container_pages_pre_from_k(&before, &before_lctx, cpu_id, process_ptr, thread_ptr, container_ptr);
            kill_container_move_page_step_from_u(kernel_k_to_kernel_u(before), kernel_k_to_kernel_u(moved_k), cpu_id, container_ptr, owner_ptr, page_2m_all_ptrs(page_index), PageSize::SZ2m);
            krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
            kill_container_trace_push(&*steps, base_steps, start, pre, kernel_k_to_kernel_u(before), kernel_k_to_kernel_u(moved_k), cpu_id, ctx);
        }
        moved = moved + 1;
    }
}
} // verus!
