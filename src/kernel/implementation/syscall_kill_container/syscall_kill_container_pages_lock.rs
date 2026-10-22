use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_pages_spec::*;
use super::syscall_kill_container_lock_pairs::{kill_container_wlock_pool_pairs, kill_container_wlock_quota_pairs};

verus! {
/// Write-hold the 4K and then the 2M allocator caches of the marked container `container_ptr` on every cpu in cpu order,
/// then the 4K and 2M global pools and quotas of its allocators and of the killer's container `owner_ptr`'s allocators,
/// each pair in container order; return the marked container's and the killer's container's 4K and 2M allocators.
pub(crate) fn kill_container_pages_lock(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    owner_ptr: RwLockContainerPtr, Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>,
    Tracked(container_perm): Tracked<&LockPerm>, Tracked(owner_perm): Tracked<&LockPerm>, Tracked(caches_4k): Tracked<&mut Map<CpuId, LockPerm>>,
    Tracked(caches_2m): Tracked<&mut Map<CpuId, LockPerm>>, Tracked(pools_4k): Tracked<&mut Map<RwLockPageAllocatorPtr, LockPerm>>,
    Tracked(pools_2m): Tracked<&mut Map<RwLockPageAllocatorPtr, LockPerm>>, Tracked(quotas_4k): Tracked<&mut Map<RwLockPageAllocatorPtr, LockPerm>>,
    Tracked(quotas_2m): Tracked<&mut Map<RwLockPageAllocatorPtr, LockPerm>>,
) -> (ret: (RwLockPageAllocatorPtr, RwLockPageAllocatorPtr, RwLockPageAllocatorPtr, RwLockPageAllocatorPtr))
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        kill_container_pages_killer_state(*old(krnl), *old(lctx), cpu_id, process_ptr, thread_ptr, container_ptr, owner_ptr, *cpu_perm, *process_perm, *thread_perm, *container_perm, *owner_perm),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(caches_4k).dom().is_empty(),
        old(caches_2m).dom().is_empty(),
        old(pools_4k).dom().is_empty(),
        old(pools_2m).dom().is_empty(),
        old(quotas_4k).dom().is_empty(),
        old(quotas_2m).dom().is_empty(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        *final(krnl) == (KernelK { allc_4k_mp: final(krnl).allc_4k_mp, allc_2m_mp: final(krnl).allc_2m_mp, ..*old(krnl) }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        kill_container_pages_killer_state(*final(krnl), *final(lctx), cpu_id, process_ptr, thread_ptr, container_ptr, owner_ptr, *cpu_perm, *process_perm, *thread_perm, *container_perm,
            *owner_perm),
        kill_container_pages_allocator_locks(*final(krnl), *final(lctx), container_ptr, owner_ptr, ret.0, ret.1, ret.2, ret.3, *final(caches_4k), *final(caches_2m), *final(pools_4k),
            *final(pools_2m), *final(quotas_4k), *final(quotas_2m)),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
{
    proof {
        container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr); container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, owner_ptr);
        container_perms_wf_at(krnl.ctn_mp, container_ptr); container_perms_wf_at(krnl.ctn_mp, owner_ptr);
    }
    let a4 = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().allocator_ptr_4k;
    let a2 = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().allocator_ptr_2m;
    let o4 = krnl.ctn_mp.borrow_rodata(owner_ptr).borrow().allocator_ptr_4k;
    let o2 = krnl.ctn_mp.borrow_rodata(owner_ptr).borrow().allocator_ptr_2m;
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
        assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
    }
    let mut c: usize = 0;
    while c < NUM_CPUS
        invariant
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            0 <= c <= NUM_CPUS,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.kernel_view_locking_state() is Acquire,
            *krnl == (KernelK { allc_4k_mp: krnl.allc_4k_mp, ..*old(krnl) }),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), krnl),
            kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), krnl),
            krnl.allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
            old(krnl).ctn_mp.dom().contains(container_ptr),
            old(krnl).ctn_mp.dom().contains(owner_ptr),
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == a4,
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_2m == a2,
            old(krnl).ctn_mp.spec_index(owner_ptr).view_rodata().view().allocator_ptr_4k == o4,
            old(krnl).ctn_mp.spec_index(owner_ptr).view_rodata().view().allocator_ptr_2m == o2,
            krnl.allc_4k_mp.dom().contains(a4),
            krnl.allc_4k_mp.dom().contains(o4),
            krnl.allc_2m_mp.dom().contains(a2),
            krnl.allc_2m_mp.dom().contains(o2),
            krnl.allc_4k_mp.spec_index(a4).owning_container == container_ptr,
            krnl.allc_4k_mp.spec_index(o4).owning_container == owner_ptr,
            krnl.allc_2m_mp.spec_index(a2).owning_container == container_ptr,
            krnl.allc_2m_mp.spec_index(o2).owning_container == owner_ptr,
            kill_container_pages_killer_state(*krnl, *lctx, cpu_id, process_ptr, thread_ptr, container_ptr, owner_ptr, *cpu_perm, *process_perm, *thread_perm, *container_perm, *owner_perm),
            lctx.allocator_quota_4k_lock_map().dom().is_empty(),
            lctx.allocator_global_pool_4k_lock_map().dom().is_empty(),
            lctx.holds_no_allocator_locks(PageSize::SZ2m),
            lctx.holds_no_allocator_locks(PageSize::SZ1g),
            forall|x: (RwLockPageAllocatorPtr, CpuId)| #![trigger lctx.allocator_cache_4k_lock_map().dom().contains(x)] lctx.allocator_cache_4k_lock_map().dom().contains(x) ==> x.0 == a4 && x.1 < c,
            forall|i: CpuId| #![trigger caches_4k.dom().contains(i)] #![trigger caches_4k[i]] #![trigger lctx.allocator_cache_4k_lock_map().dom().contains((a4, i))] i < c ==> {
                &&& caches_4k.dom().contains(i)
                &&& typed_lock_map_contains_mode(lctx.allocator_cache_4k_lock_map(), (a4, i), TypedLockMode::Write)
                &&& caches_4k[i].state() is WriteLock
                &&& caches_4k[i].thread_id() == lctx.thread_id()
                &&& caches_4k[i].lock_id() == krnl.allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().locking_thread()->Write_lock_id
            },
        decreases NUM_CPUS - c,
    {
        proof { krnl.cpu_arr.typed_lock_map_aligned_lock_id_at(lctx.cpu_lock_map(), lctx.thread_id(), cpu_id); krnl.thr_mp.typed_lock_map_aligned_lock_id_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr); }
        let Tracked(perm) = krnl.wlock_allocator_cache_4k(a4, c, Tracked(&mut *lctx));
        proof {
            caches_4k.tracked_insert(c, perm);
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        }
        c = c + 1;
    }
    let ghost cached_4k = *krnl;
    let mut c: usize = 0;
    while c < NUM_CPUS
        invariant
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            0 <= c <= NUM_CPUS,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.kernel_view_locking_state() is Acquire,
            *krnl == (KernelK { allc_4k_mp: krnl.allc_4k_mp, allc_2m_mp: krnl.allc_2m_mp, ..*old(krnl) }),
            krnl.allc_4k_mp == cached_4k.allc_4k_mp,
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), krnl),
            kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), krnl),
            krnl.allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
            krnl.allc_2m_mp.dom() == old(krnl).allc_2m_mp.dom(),
            old(krnl).ctn_mp.dom().contains(container_ptr),
            old(krnl).ctn_mp.dom().contains(owner_ptr),
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == a4,
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_2m == a2,
            old(krnl).ctn_mp.spec_index(owner_ptr).view_rodata().view().allocator_ptr_4k == o4,
            old(krnl).ctn_mp.spec_index(owner_ptr).view_rodata().view().allocator_ptr_2m == o2,
            krnl.allc_4k_mp.dom().contains(a4),
            krnl.allc_4k_mp.dom().contains(o4),
            krnl.allc_2m_mp.dom().contains(a2),
            krnl.allc_2m_mp.dom().contains(o2),
            krnl.allc_4k_mp.spec_index(a4).owning_container == container_ptr,
            krnl.allc_4k_mp.spec_index(o4).owning_container == owner_ptr,
            krnl.allc_2m_mp.spec_index(a2).owning_container == container_ptr,
            krnl.allc_2m_mp.spec_index(o2).owning_container == owner_ptr,
            kill_container_pages_killer_state(*krnl, *lctx, cpu_id, process_ptr, thread_ptr, container_ptr, owner_ptr, *cpu_perm, *process_perm, *thread_perm, *container_perm, *owner_perm),
            lctx.allocator_quota_4k_lock_map().dom().is_empty(),
            lctx.allocator_global_pool_4k_lock_map().dom().is_empty(),
            lctx.allocator_quota_2m_lock_map().dom().is_empty(),
            lctx.allocator_global_pool_2m_lock_map().dom().is_empty(),
            lctx.holds_no_allocator_locks(PageSize::SZ1g),
            forall|x: (RwLockPageAllocatorPtr, CpuId)| #![trigger lctx.allocator_cache_4k_lock_map().dom().contains(x)] lctx.allocator_cache_4k_lock_map().dom().contains(x) ==> x.0 == a4 && x.1 < NUM_CPUS,
            forall|i: CpuId| #![trigger caches_4k.dom().contains(i)] #![trigger caches_4k[i]] #![trigger lctx.allocator_cache_4k_lock_map().dom().contains((a4, i))] i < NUM_CPUS ==> {
                &&& caches_4k.dom().contains(i)
                &&& typed_lock_map_contains_mode(lctx.allocator_cache_4k_lock_map(), (a4, i), TypedLockMode::Write)
                &&& caches_4k[i].state() is WriteLock
                &&& caches_4k[i].thread_id() == lctx.thread_id()
                &&& caches_4k[i].lock_id() == krnl.allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().locking_thread()->Write_lock_id
            },
            forall|x: (RwLockPageAllocatorPtr, CpuId)| #![trigger lctx.allocator_cache_2m_lock_map().dom().contains(x)] lctx.allocator_cache_2m_lock_map().dom().contains(x) ==> x.0 == a2 && x.1 < c,
            forall|i: CpuId| #![trigger caches_2m.dom().contains(i)] #![trigger caches_2m[i]] #![trigger lctx.allocator_cache_2m_lock_map().dom().contains((a2, i))] i < c ==> {
                &&& caches_2m.dom().contains(i)
                &&& typed_lock_map_contains_mode(lctx.allocator_cache_2m_lock_map(), (a2, i), TypedLockMode::Write)
                &&& caches_2m[i].state() is WriteLock
                &&& caches_2m[i].thread_id() == lctx.thread_id()
                &&& caches_2m[i].lock_id() == krnl.allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().locking_thread()->Write_lock_id
            },
        decreases NUM_CPUS - c,
    {
        proof { krnl.cpu_arr.typed_lock_map_aligned_lock_id_at(lctx.cpu_lock_map(), lctx.thread_id(), cpu_id); krnl.thr_mp.typed_lock_map_aligned_lock_id_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr); }
        let Tracked(perm) = krnl.wlock_allocator_cache_2m(a2, c, Tracked(&mut *lctx));
        proof {
            caches_2m.tracked_insert(c, perm);
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        }
        c = c + 1;
    }
    kill_container_wlock_pool_pairs(krnl, Tracked(&mut *lctx), container_ptr, owner_ptr, a4, o4, a2, o2, Tracked(&mut *pools_4k), Tracked(&mut *pools_2m));
    kill_container_wlock_quota_pairs(krnl, Tracked(&mut *lctx), container_ptr, owner_ptr, a4, o4, a2, o2, Tracked(&mut *quotas_4k), Tracked(&mut *quotas_2m));
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    (a4, o4, a2, o2)
}

/// Release every allocator lock that `kill_container_pages_lock` took with the permissions given.
pub(crate) fn kill_container_pages_unlock(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, container_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr, a4: RwLockPageAllocatorPtr,
    o4: RwLockPageAllocatorPtr, a2: RwLockPageAllocatorPtr, o2: RwLockPageAllocatorPtr, Tracked(caches_4k): Tracked<Map<CpuId, LockPerm>>,
    Tracked(caches_2m): Tracked<Map<CpuId, LockPerm>>, Tracked(pools_4k): Tracked<Map<RwLockPageAllocatorPtr, LockPerm>>, Tracked(pools_2m): Tracked<Map<RwLockPageAllocatorPtr, LockPerm>>,
    Tracked(quotas_4k): Tracked<Map<RwLockPageAllocatorPtr, LockPerm>>, Tracked(quotas_2m): Tracked<Map<RwLockPageAllocatorPtr, LockPerm>>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        kill_container_pages_allocator_locks(*old(krnl), *old(lctx), container_ptr, owner_ptr, a4, o4, a2, o2, caches_4k, caches_2m, pools_4k, pools_2m, quotas_4k, quotas_2m),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { allc_4k_mp: final(krnl).allc_4k_mp, allc_2m_mp: final(krnl).allc_2m_mp, ..*old(krnl) }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        final(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        final(lctx).holds_no_allocator_locks(PageSize::SZ1g),
{
    let tracked mut caches_4k = caches_4k;
    let tracked mut caches_2m = caches_2m;
    let tracked mut pools_4k = pools_4k;
    let tracked mut pools_2m = pools_2m;
    let tracked mut quotas_4k = quotas_4k;
    let tracked mut quotas_2m = quotas_2m;
    let tracked quota = quotas_2m.tracked_remove(a2);
    krnl.wunlock_allocator_quota_2m(a2, Tracked(&mut *lctx), Tracked(quota));
    let tracked quota = quotas_2m.tracked_remove(o2);
    krnl.wunlock_allocator_quota_2m(o2, Tracked(&mut *lctx), Tracked(quota));
    let tracked quota = quotas_4k.tracked_remove(a4);
    krnl.wunlock_allocator_quota_4k(a4, Tracked(&mut *lctx), Tracked(quota));
    let tracked quota = quotas_4k.tracked_remove(o4);
    krnl.wunlock_allocator_quota_4k(o4, Tracked(&mut *lctx), Tracked(quota));
    let tracked pool = pools_2m.tracked_remove(a2);
    krnl.wunlock_allocator_global_pool_2m(a2, Tracked(&mut *lctx), Tracked(pool));
    let tracked pool = pools_2m.tracked_remove(o2);
    krnl.wunlock_allocator_global_pool_2m(o2, Tracked(&mut *lctx), Tracked(pool));
    let tracked pool = pools_4k.tracked_remove(a4);
    krnl.wunlock_allocator_global_pool_4k(a4, Tracked(&mut *lctx), Tracked(pool));
    let tracked pool = pools_4k.tracked_remove(o4);
    krnl.wunlock_allocator_global_pool_4k(o4, Tracked(&mut *lctx), Tracked(pool));
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        assert(lctx.allocator_quota_4k_lock_map().dom() =~= Set::<RwLockPageAllocatorPtr>::empty() && lctx.allocator_global_pool_4k_lock_map().dom() =~= Set::<RwLockPageAllocatorPtr>::empty());
        assert(lctx.allocator_quota_2m_lock_map().dom() =~= Set::<RwLockPageAllocatorPtr>::empty() && lctx.allocator_global_pool_2m_lock_map().dom() =~= Set::<RwLockPageAllocatorPtr>::empty());
    }
    let mut c: usize = 0;
    while c < NUM_CPUS
        invariant
            0 <= c <= NUM_CPUS,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.kernel_view_locking_state() is Release,
            *krnl == (KernelK { allc_4k_mp: krnl.allc_4k_mp, allc_2m_mp: krnl.allc_2m_mp, ..*old(krnl) }),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), krnl),
            kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), krnl),
            krnl.allc_4k_mp.dom().contains(a4),
            krnl.allc_2m_mp.dom().contains(a2),
            lctx.page_lock_map() == old(lctx).page_lock_map(),
            lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
            lctx.pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            lctx.cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            lctx.process_lock_map() == old(lctx).process_lock_map(),
            lctx.thread_lock_map() == old(lctx).thread_lock_map(),
            lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            lctx.scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            lctx.pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            lctx.pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            lctx.pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
            lctx.iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            lctx.iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
            lctx.allocator_quota_4k_lock_map().dom().is_empty(),
            lctx.allocator_global_pool_4k_lock_map().dom().is_empty(),
            lctx.allocator_quota_2m_lock_map().dom().is_empty(),
            lctx.allocator_global_pool_2m_lock_map().dom().is_empty(),
            lctx.holds_no_allocator_locks(PageSize::SZ1g),
            forall|x: (RwLockPageAllocatorPtr, CpuId)| #![trigger lctx.allocator_cache_4k_lock_map().dom().contains(x)] lctx.allocator_cache_4k_lock_map().dom().contains(x) ==> x.0 == a4 && c <= x.1 < NUM_CPUS,
            forall|x: (RwLockPageAllocatorPtr, CpuId)| #![trigger lctx.allocator_cache_2m_lock_map().dom().contains(x)] lctx.allocator_cache_2m_lock_map().dom().contains(x) ==> x.0 == a2 && c <= x.1 < NUM_CPUS,
            forall|i: CpuId| #![trigger caches_4k.dom().contains(i)] #![trigger caches_4k[i]] #![trigger lctx.allocator_cache_4k_lock_map().dom().contains((a4, i))] c <= i < NUM_CPUS ==> {
                &&& caches_4k.dom().contains(i)
                &&& typed_lock_map_contains_mode(lctx.allocator_cache_4k_lock_map(), (a4, i), TypedLockMode::Write)
                &&& caches_4k[i].state() is WriteLock
                &&& caches_4k[i].thread_id() == lctx.thread_id()
                &&& caches_4k[i].lock_id() == krnl.allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().locking_thread()->Write_lock_id
            },
            forall|i: CpuId| #![trigger caches_2m.dom().contains(i)] #![trigger caches_2m[i]] #![trigger lctx.allocator_cache_2m_lock_map().dom().contains((a2, i))] c <= i < NUM_CPUS ==> {
                &&& caches_2m.dom().contains(i)
                &&& typed_lock_map_contains_mode(lctx.allocator_cache_2m_lock_map(), (a2, i), TypedLockMode::Write)
                &&& caches_2m[i].state() is WriteLock
                &&& caches_2m[i].thread_id() == lctx.thread_id()
                &&& caches_2m[i].lock_id() == krnl.allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().locking_thread()->Write_lock_id
            },
        decreases NUM_CPUS - c,
    {
        let tracked perm = caches_4k.tracked_remove(c);
        krnl.wunlock_allocator_cache_4k(a4, c, Tracked(&mut *lctx), Tracked(perm));
        let tracked perm = caches_2m.tracked_remove(c);
        krnl.wunlock_allocator_cache_2m(a2, c, Tracked(&mut *lctx), Tracked(perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        }
        c = c + 1;
    }
    proof {
        assert(lctx.allocator_cache_4k_lock_map().dom() =~= Set::<(RwLockPageAllocatorPtr, CpuId)>::empty());
        assert(lctx.allocator_cache_2m_lock_map().dom() =~= Set::<(RwLockPageAllocatorPtr, CpuId)>::empty());
    }
}
} // verus!
