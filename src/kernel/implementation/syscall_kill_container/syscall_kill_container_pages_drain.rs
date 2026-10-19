use vstd::prelude::*;
use crate::*;
#[cfg(feature = "split-crates")]
use veriflat_alloc_page::free_4k_page::move_cache_page_to_pool::move_cache_page_to_pool;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::free_4k_page::move_cache_page_to_pool::move_cache_page_to_pool;
#[cfg(feature = "split-crates")]
use veriflat_alloc_page::allocate_free_2m_page::move_cache_page_to_pool_2m::move_cache_page_to_pool_2m;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::allocate_free_2m_page::move_cache_page_to_pool_2m::move_cache_page_to_pool_2m;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_pages_spec::*;

verus! {
/// Move every page of the 4K allocator cache on cpu `c` of the marked container's allocator `a4` to that allocator's
/// global pool, one page per stuttering step.
fn kill_container_pages_drain_4k_cache(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr, a4: RwLockPageAllocatorPtr, o4: RwLockPageAllocatorPtr,
    a2: RwLockPageAllocatorPtr, o2: RwLockPageAllocatorPtr, Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>,
    Tracked(thread_perm): Tracked<&LockPerm>, Tracked(container_perm): Tracked<&LockPerm>, Tracked(owner_perm): Tracked<&LockPerm>,
    Tracked(caches_4k): Tracked<&Map<CpuId, LockPerm>>, Tracked(caches_2m): Tracked<&Map<CpuId, LockPerm>>, Tracked(pools_4k): Tracked<&Map<RwLockPageAllocatorPtr, LockPerm>>,
    Tracked(pools_2m): Tracked<&Map<RwLockPageAllocatorPtr, LockPerm>>, Tracked(quotas_4k): Tracked<&Map<RwLockPageAllocatorPtr, LockPerm>>,
    Tracked(quotas_2m): Tracked<&Map<RwLockPageAllocatorPtr, LockPerm>>, c: CpuId,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        kill_container_pages_killer_state(*old(krnl), *old(lctx), cpu_id, process_ptr, thread_ptr, container_ptr, owner_ptr, *cpu_perm, *process_perm, *thread_perm, *container_perm,
            *owner_perm),
        kill_container_pages_allocator_locks(*old(krnl), *old(lctx), container_ptr, owner_ptr, a4, o4, a2, o2, *caches_4k, *caches_2m, *pools_4k, *pools_2m, *quotas_4k, *quotas_2m),
        index_valid(NUM_CPUS, c),
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
        final(steps).view() == old(steps).view(),
        final(krnl).allc_4k_mp.spec_index(a4).cpu_caches.spec_index(c).view().view().view().len() == 0,
        forall|i: CpuId| #![trigger final(krnl).allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i) && i != c
            ==> final(krnl).allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().view() == old(krnl).allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().view(),
        forall|i: CpuId| #![trigger final(krnl).allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i)
            ==> final(krnl).allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().view() == old(krnl).allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().view(),
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
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        forall|s: RwLockCpuSetPtr| #![trigger old(lctx).cpu_set_lock_map().dom().contains(s)] old(lctx).cpu_set_lock_map().dom().contains(s)
            ==> final(krnl).cpu_set_mp.dom().contains(s) && final(krnl).cpu_set_mp.spec_index(s) == old(krnl).cpu_set_mp.spec_index(s),
{
    proof { allocator_perms_wf_map(krnl.allc_4k_mp); allocator_perms_wf_at(krnl.allc_4k_mp, a4); }
    let tracked cache_perm = caches_4k.tracked_borrow(c);
    let n = krnl.allc_4k_mp.borrow_cache_typed(a4, c, Ghost(lctx.allocator_cache_4k_lock_map()), Tracked(&*lctx), Tracked(cache_perm)).linked_list.len();
    proof { krnl.allc_4k_mp.spec_index(a4).cpu_caches.spec_index(c).view().view().linked_list.lemma_len_view(); }
    let mut moved: usize = 0;
    proof { held_kernel_objects_unchanged_reflexive(&*krnl, &*lctx); }
    while moved < n
        invariant
            krnl.cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
            krnl.cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
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
            index_valid(NUM_CPUS, c),
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
            steps.view() == old(steps).view(),
            krnl.allc_4k_mp.spec_index(a4).cpu_caches.spec_index(c).view().view().view().len() == n - moved,
            forall|i: CpuId| #![trigger krnl.allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i) && i != c
                ==> krnl.allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().view() == old(krnl).allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().view(),
            forall|i: CpuId| #![trigger krnl.allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i)
                ==> krnl.allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().view() == old(krnl).allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().view(),
        decreases n - moved,
    {
        proof { allocator_perms_wf_map(krnl.allc_4k_mp); allocator_perms_wf_at(krnl.allc_4k_mp, a4); }
        let tracked cache_perm = caches_4k.tracked_borrow(c);
        let tracked pool_perm = pools_4k.tracked_borrow(a4);
        let cache = krnl.allc_4k_mp.borrow_cache_typed(a4, c, Ghost(lctx.allocator_cache_4k_lock_map()), Tracked(&*lctx), Tracked(cache_perm));
        assert(cache.linked_list.len() > 0) by { cache.linked_list.lemma_len_view(); };
        let (_, page_ptr) = cache.linked_list.peek_head();
        assert(page_ptr_valid(page_ptr)) by { allocator_free_page_ptrs_wf_cache_at(krnl.allc_4k_mp, a4, c, page_ptr); };
        let page_index = page_ptr2page_index(page_ptr);
        assert(page_ptr_valid(page_ptr) && index_valid(NUM_PAGES, page_index) && krnl.pg_arr.lock_id_by_index(page_index).major == FREE_PAGE_LOCK_MAJOR) by {
            reveal(LinkedList::wf_value_list);
            container_allocator_free_4k_page_wf_cache_at(krnl.allc_4k_mp, krnl.pg_arr, a4, c, page_ptr); page_ptr_valid_imply_page_index_valid(); page_array_wf_at(krnl.pg_arr, page_index);
        };
        let ghost before = *krnl;
        let Tracked(page_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));
        move_cache_page_to_pool(krnl, a4, c, page_ptr, Tracked(&mut *lctx), Tracked(cache_perm), Tracked(pool_perm), Tracked(&page_perm));
        krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_perm));
        proof {
            assert(typed_lock_maps_unchanged(old(lctx), lctx)) by { map_insert_remove_absent_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write }); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&before, &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_endpoint_nonlock_fields_unchanged(before.ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&before, &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&before, &*krnl);
            krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
        }
        moved = moved + 1;
    }
}

/// Move every page of the 2M allocator cache on cpu `c` of the marked container's allocator `a2` to that allocator's
/// global pool, one page per stuttering step.
fn kill_container_pages_drain_2m_cache(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr, a4: RwLockPageAllocatorPtr, o4: RwLockPageAllocatorPtr,
    a2: RwLockPageAllocatorPtr, o2: RwLockPageAllocatorPtr, Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>,
    Tracked(thread_perm): Tracked<&LockPerm>, Tracked(container_perm): Tracked<&LockPerm>, Tracked(owner_perm): Tracked<&LockPerm>,
    Tracked(caches_4k): Tracked<&Map<CpuId, LockPerm>>, Tracked(caches_2m): Tracked<&Map<CpuId, LockPerm>>, Tracked(pools_4k): Tracked<&Map<RwLockPageAllocatorPtr, LockPerm>>,
    Tracked(pools_2m): Tracked<&Map<RwLockPageAllocatorPtr, LockPerm>>, Tracked(quotas_4k): Tracked<&Map<RwLockPageAllocatorPtr, LockPerm>>,
    Tracked(quotas_2m): Tracked<&Map<RwLockPageAllocatorPtr, LockPerm>>, c: CpuId,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        kill_container_pages_killer_state(*old(krnl), *old(lctx), cpu_id, process_ptr, thread_ptr, container_ptr, owner_ptr, *cpu_perm, *process_perm, *thread_perm, *container_perm,
            *owner_perm),
        kill_container_pages_allocator_locks(*old(krnl), *old(lctx), container_ptr, owner_ptr, a4, o4, a2, o2, *caches_4k, *caches_2m, *pools_4k, *pools_2m, *quotas_4k, *quotas_2m),
        index_valid(NUM_CPUS, c),
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
        final(steps).view() == old(steps).view(),
        final(krnl).allc_2m_mp.spec_index(a2).cpu_caches.spec_index(c).view().view().view().len() == 0,
        forall|i: CpuId| #![trigger final(krnl).allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i) && i != c
            ==> final(krnl).allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().view() == old(krnl).allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().view(),
        forall|i: CpuId| #![trigger final(krnl).allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i)
            ==> final(krnl).allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().view() == old(krnl).allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().view(),
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
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        forall|s: RwLockCpuSetPtr| #![trigger old(lctx).cpu_set_lock_map().dom().contains(s)] old(lctx).cpu_set_lock_map().dom().contains(s)
            ==> final(krnl).cpu_set_mp.dom().contains(s) && final(krnl).cpu_set_mp.spec_index(s) == old(krnl).cpu_set_mp.spec_index(s),
{
    proof { allocator_perms_wf_map(krnl.allc_2m_mp); allocator_perms_wf_at(krnl.allc_2m_mp, a2); }
    let tracked cache_perm = caches_2m.tracked_borrow(c);
    let n = krnl.allc_2m_mp.borrow_cache_typed(a2, c, Ghost(lctx.allocator_cache_2m_lock_map()), Tracked(&*lctx), Tracked(cache_perm)).linked_list.len();
    proof { krnl.allc_2m_mp.spec_index(a2).cpu_caches.spec_index(c).view().view().linked_list.lemma_len_view(); }
    let mut moved: usize = 0;
    proof { held_kernel_objects_unchanged_reflexive(&*krnl, &*lctx); }
    while moved < n
        invariant
            krnl.cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
            krnl.cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
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
            index_valid(NUM_CPUS, c),
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
            steps.view() == old(steps).view(),
            krnl.allc_2m_mp.spec_index(a2).cpu_caches.spec_index(c).view().view().view().len() == n - moved,
            forall|i: CpuId| #![trigger krnl.allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i) && i != c
                ==> krnl.allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().view() == old(krnl).allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().view(),
            forall|i: CpuId| #![trigger krnl.allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i)
                ==> krnl.allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().view() == old(krnl).allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().view(),
        decreases n - moved,
    {
        proof { allocator_perms_wf_map(krnl.allc_2m_mp); allocator_perms_wf_at(krnl.allc_2m_mp, a2); }
        let tracked cache_perm = caches_2m.tracked_borrow(c);
        let tracked pool_perm = pools_2m.tracked_borrow(a2);
        let cache = krnl.allc_2m_mp.borrow_cache_typed(a2, c, Ghost(lctx.allocator_cache_2m_lock_map()), Tracked(&*lctx), Tracked(cache_perm));
        assert(cache.linked_list.len() > 0) by { cache.linked_list.lemma_len_view(); };
        let (_, page_ptr) = cache.linked_list.peek_head();
        assert(page_ptr_valid(page_ptr)) by { allocator_free_page_ptrs_wf_cache_at(krnl.allc_2m_mp, a2, c, page_ptr); };
        let page_index = page_ptr2page_index(page_ptr);
        assert(page_ptr_valid(page_ptr) && index_valid(NUM_PAGES, page_index) && krnl.pg_arr.lock_id_by_index(page_index).major == FREE_PAGE_LOCK_MAJOR) by {
            reveal(LinkedList::wf_value_list);
            container_allocator_free_2m_page_wf_cache_at(krnl.allc_2m_mp, krnl.pg_arr, a2, c, page_ptr); page_ptr_valid_imply_page_index_valid(); page_array_wf_at(krnl.pg_arr, page_index);
        };
        let ghost before = *krnl;
        let Tracked(page_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));
        move_cache_page_to_pool_2m(krnl, a2, c, page_ptr, Tracked(&mut *lctx), Tracked(cache_perm), Tracked(pool_perm), Tracked(&page_perm));
        krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_perm));
        proof {
            assert(typed_lock_maps_unchanged(old(lctx), lctx)) by { map_insert_remove_absent_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write }); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&before, &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_endpoint_nonlock_fields_unchanged(before.ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&before, &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&before, &*krnl);
            krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
        }
        moved = moved + 1;
    }
}

/// Move every page of the marked container's 4K and then 2M allocator caches on every cpu to its allocators' global pools,
/// one page per stuttering step.
pub(crate) fn kill_container_pages_drain(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr, a4: RwLockPageAllocatorPtr, o4: RwLockPageAllocatorPtr,
    a2: RwLockPageAllocatorPtr, o2: RwLockPageAllocatorPtr, Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>,
    Tracked(thread_perm): Tracked<&LockPerm>, Tracked(container_perm): Tracked<&LockPerm>, Tracked(owner_perm): Tracked<&LockPerm>,
    Tracked(caches_4k): Tracked<&Map<CpuId, LockPerm>>, Tracked(caches_2m): Tracked<&Map<CpuId, LockPerm>>, Tracked(pools_4k): Tracked<&Map<RwLockPageAllocatorPtr, LockPerm>>,
    Tracked(pools_2m): Tracked<&Map<RwLockPageAllocatorPtr, LockPerm>>, Tracked(quotas_4k): Tracked<&Map<RwLockPageAllocatorPtr, LockPerm>>,
    Tracked(quotas_2m): Tracked<&Map<RwLockPageAllocatorPtr, LockPerm>>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        kill_container_pages_killer_state(*old(krnl), *old(lctx), cpu_id, process_ptr, thread_ptr, container_ptr, owner_ptr, *cpu_perm, *process_perm, *thread_perm, *container_perm,
            *owner_perm),
        kill_container_pages_allocator_locks(*old(krnl), *old(lctx), container_ptr, owner_ptr, a4, o4, a2, o2, *caches_4k, *caches_2m, *pools_4k, *pools_2m, *quotas_4k, *quotas_2m),
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
        final(steps).view() == old(steps).view(),
        forall|i: CpuId| #![trigger final(krnl).allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i)
            ==> final(krnl).allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().view().view().len() == 0,
        forall|i: CpuId| #![trigger final(krnl).allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i)
            ==> final(krnl).allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().view().view().len() == 0,
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
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
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
    let mut c: usize = 0;
    proof { held_kernel_objects_unchanged_reflexive(&*krnl, &*lctx); }
    while c < NUM_CPUS
        invariant
            lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            krnl.cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
            krnl.cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
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
            0 <= c <= NUM_CPUS,
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
            steps.view() == old(steps).view(),
            forall|i: CpuId| #![trigger krnl.allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i)] i < c
                ==> krnl.allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().view().view().len() == 0,
        decreases NUM_CPUS - c,
    {
        kill_container_pages_drain_4k_cache(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, container_ptr, owner_ptr, a4, o4, a2, o2, Tracked(cpu_perm),
            Tracked(process_perm), Tracked(thread_perm), Tracked(container_perm), Tracked(owner_perm), Tracked(caches_4k), Tracked(caches_2m), Tracked(pools_4k),
            Tracked(pools_2m), Tracked(quotas_4k), Tracked(quotas_2m), c);
        c = c + 1;
    }
    let mut c: usize = 0;
    while c < NUM_CPUS
        invariant
            lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            krnl.cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
            krnl.cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
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
            0 <= c <= NUM_CPUS,
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
            steps.view() == old(steps).view(),
            forall|i: CpuId| #![trigger krnl.allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i)
                ==> krnl.allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().view().view().len() == 0,
            forall|i: CpuId| #![trigger krnl.allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i)] i < c
                ==> krnl.allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().view().view().len() == 0,
        decreases NUM_CPUS - c,
    {
        kill_container_pages_drain_2m_cache(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, container_ptr, owner_ptr, a4, o4, a2, o2, Tracked(cpu_perm),
            Tracked(process_perm), Tracked(thread_perm), Tracked(container_perm), Tracked(owner_perm), Tracked(caches_4k), Tracked(caches_2m), Tracked(pools_4k),
            Tracked(pools_2m), Tracked(quotas_4k), Tracked(quotas_2m), c);
        c = c + 1;
    }
}
} // verus!
