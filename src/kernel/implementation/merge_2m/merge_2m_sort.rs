#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::*;
use super::merge_2m_locking::Merge2mSourceLocks;
#[cfg(verus_keep_ghost)]
use super::merge_2m_sort_eof::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_scanner_spec::*;

verus! {
pub fn merge_2m_sort_sources(krnl: &mut KernelK, allocator: RwLockPageAllocatorPtr,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(locks): Tracked<&Merge2mSourceLocks>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), lctx),
        old(krnl).allc_4k_mp.dom().contains(allocator),
        lctx.kernel_view_locking_state() is Acquire,
        forall|cpu: CpuId| #![trigger locks.cache.dom().contains(cpu)] cpu < NUM_CPUS ==> locks.cache.dom().contains(cpu),
        forall|cpu: CpuId| #![trigger locks.cache[cpu]] cpu < NUM_CPUS ==> {
            &&& typed_lock_map_contains_mode(lctx.allocator_cache_4k_lock_map(), (allocator, cpu), TypedLockMode::Write)
            &&& locks.cache[cpu].state() is WriteLock
            &&& locks.cache[cpu].thread_id() == lctx.thread_id()
            &&& old(krnl).allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu).view().locking_thread() is Write
            &&& locks.cache[cpu].lock_id() == old(krnl).allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu).view().locking_thread()->Write_lock_id
        },
        typed_lock_map_contains_mode(lctx.allocator_global_pool_4k_lock_map(), allocator, TypedLockMode::Write),
        locks.pool4k.state() is WriteLock,
        locks.pool4k.thread_id() == lctx.thread_id(),
        old(krnl).allc_4k_mp.spec_index(allocator).global_pool.locking_thread() is Write,
        locks.pool4k.lock_id() == old(krnl).allc_4k_mp.spec_index(allocator).global_pool.locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), lctx),
        merge_2m_sort_eof_transition_framing(*old(krnl), *final(krnl), allocator, (NUM_CPUS + 1) as usize),
        merge_2m_source_pages(final(krnl).allc_4k_mp.spec_index(allocator)) == merge_2m_source_pages(old(krnl).allc_4k_mp.spec_index(allocator)),
        forall|source: usize| #![trigger final(krnl).allc_4k_mp.spec_index(allocator).merge_2m_source_list(source)] source <= NUM_CPUS ==>
            LinkedList::<PagePtr, 233>::values_sorted(final(krnl).allc_4k_mp.spec_index(allocator).merge_2m_source_list(source).view()),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
{
    proof {
        allocator_perms_wf_implies_map_perms_wf(krnl.allc_4k_mp);
        allocator_perms_wf_at(krnl.allc_4k_mp, allocator);
        reveal(merge_2m_sort_eof_transition_framing);
    }
    let mut source = 0usize;
    while source <= NUM_CPUS
        invariant
            source <= NUM_CPUS + 1,
            forall|cpu: CpuId| #![trigger locks.cache.dom().contains(cpu)] cpu < NUM_CPUS ==> locks.cache.dom().contains(cpu),
            forall|cpu: CpuId| #![trigger locks.cache[cpu]] cpu < NUM_CPUS ==> {
                &&& typed_lock_map_contains_mode(lctx.allocator_cache_4k_lock_map(), (allocator, cpu), TypedLockMode::Write)
                &&& locks.cache[cpu].state() is WriteLock
                &&& locks.cache[cpu].thread_id() == lctx.thread_id()
                &&& krnl.allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu).view().locking_thread() is Write
                &&& locks.cache[cpu].lock_id() == krnl.allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu).view().locking_thread()->Write_lock_id
            },
            typed_lock_map_contains_mode(lctx.allocator_global_pool_4k_lock_map(), allocator, TypedLockMode::Write),
            locks.pool4k.state() is WriteLock,
            locks.pool4k.thread_id() == lctx.thread_id(),
            krnl.allc_4k_mp.spec_index(allocator).global_pool.locking_thread() is Write,
            locks.pool4k.lock_id() == krnl.allc_4k_mp.spec_index(allocator).global_pool.locking_thread()->Write_lock_id,
            merge_2m_sort_eof_transition_framing(*old(krnl), *krnl, allocator, source),
            krnl.allc_4k_mp.dom().contains(allocator),
            krnl.allc_4k_mp.perms_wf(),
            krnl.allc_4k_mp.spec_index(allocator).wf(),
            krnl.allc_4k_mp.typed_quota_lock_map_aligned(lctx.allocator_quota_4k_lock_map(), lctx.thread_id()),
            krnl.allc_4k_mp.typed_cache_lock_map_aligned(lctx.allocator_cache_4k_lock_map(), lctx.thread_id()),
            krnl.allc_4k_mp.typed_global_pool_lock_map_aligned(lctx.allocator_global_pool_4k_lock_map(), lctx.thread_id()),
        decreases NUM_CPUS + 1 - source,
    {
        proof { reveal(merge_2m_sort_eof_transition_framing); }
        if source < NUM_CPUS {
            let tracked perm = locks.cache.tracked_borrow(source);
            krnl.allc_4k_mp.merge_2m_sort_source(allocator, source as u8, Ghost(lctx.allocator_quota_4k_lock_map()),
                Ghost(lctx.allocator_cache_4k_lock_map()), Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(lctx), Tracked(perm));
        } else {
            krnl.allc_4k_mp.merge_2m_sort_source(allocator, source as u8, Ghost(lctx.allocator_quota_4k_lock_map()),
                Ghost(lctx.allocator_cache_4k_lock_map()), Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(lctx), Tracked(&locks.pool4k));
        }
        source += 1;
    }
    proof { merge_2m_sort_eof_implies_kernel_inv_and_alignment(*old(krnl), *krnl, lctx, allocator); }
}
}
