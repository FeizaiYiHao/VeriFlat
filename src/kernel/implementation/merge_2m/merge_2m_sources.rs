#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_scanner_spec::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_set_folds::*;

verus! {
pub fn merge_2m_borrow_source<'a>(krnl: &'a KernelK, allocator: RwLockPageAllocatorPtr, source: usize,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(cache_perms): Tracked<&'a Map<CpuId, LockPerm>>,
    Tracked(pool_perm): Tracked<&'a LockPerm>) -> (ret: &'a LinkedList<PagePtr, 233>)
    requires
        krnl.inv(),
        typed_lock_maps_aligned(krnl, lctx),
        krnl.allc_4k_mp.dom().contains(allocator),
        source <= NUM_CPUS,
        source < NUM_CPUS ==> {
            &&& cache_perms.dom().contains(source)
            &&& cache_perms.spec_index(source).state() is WriteLock
            &&& cache_perms.spec_index(source).thread_id() == lctx.thread_id()
            &&& krnl.allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(source).view().locking_thread() is Write
            &&& cache_perms.spec_index(source).lock_id() == krnl.allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(source).view().locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(lctx.allocator_cache_4k_lock_map(), (allocator, source), TypedLockMode::Write)
        },
        source == NUM_CPUS ==> {
            &&& pool_perm.state() is WriteLock
            &&& pool_perm.thread_id() == lctx.thread_id()
            &&& krnl.allc_4k_mp.spec_index(allocator).global_pool.locking_thread() is Write
            &&& pool_perm.lock_id() == krnl.allc_4k_mp.spec_index(allocator).global_pool.locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(lctx.allocator_global_pool_4k_lock_map(), allocator, TypedLockMode::Write)
        },
    ensures
        ret.wf(),
        *ret == krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(source),
        ret.view().to_set().subset_of(merge_2m_source_pages(krnl.allc_4k_mp.spec_index(allocator))),
{
    assert(krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(source).view().to_set().subset_of(merge_2m_source_pages(krnl.allc_4k_mp.spec_index(allocator)))) by {
        let sets = Seq::new((NUM_CPUS + 1) as nat, |i: int| krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(i as usize).view().to_set());
        sequence_union_fold_implies_entry_subset(sets, source as int);
    };
    proof { allocator_perms_wf_map(krnl.allc_4k_mp); allocator_perms_wf_at(krnl.allc_4k_mp, allocator); }
    if source < NUM_CPUS {
        let cache = krnl.allc_4k_mp.borrow_cache_typed(allocator, source, Ghost(lctx.allocator_cache_4k_lock_map()),
            Tracked(lctx), Tracked(cache_perms.tracked_borrow(source)));
        &cache.linked_list
    } else {
        let pool = krnl.allc_4k_mp.borrow_global_pool_typed(allocator, Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(lctx), Tracked(pool_perm));
        &pool.linked_list
    }
}
}
