#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::*;

verus! {
pub fn split_2m_borrow_source<'a>(krnl: &'a KernelK, allocator: RwLockPageAllocatorPtr, source: usize,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(cache_perms): Tracked<&'a Map<CpuId, LockPerm>>,
    Tracked(pool_perm): Tracked<&'a LockPerm>) -> (ret: &'a LinkedList<PagePtr, 233>)
    requires
        krnl.inv(),
        typed_lock_maps_aligned(krnl, lctx),
        krnl.allc_2m_mp.dom().contains(allocator),
        source <= NUM_CPUS,
        source < NUM_CPUS ==> {
            &&& cache_perms.dom().contains(source)
            &&& cache_perms.spec_index(source).state() is WriteLock
            &&& cache_perms.spec_index(source).thread_id() == lctx.thread_id()
            &&& krnl.allc_2m_mp.spec_index(allocator).cpu_caches.spec_index(source).view().locking_thread() is Write
            &&& cache_perms.spec_index(source).lock_id() == krnl.allc_2m_mp.spec_index(allocator).cpu_caches.spec_index(source).view().locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(lctx.allocator_cache_2m_lock_map(), (allocator, source), TypedLockMode::Write)
        },
        source == NUM_CPUS ==> {
            &&& pool_perm.state() is WriteLock
            &&& pool_perm.thread_id() == lctx.thread_id()
            &&& krnl.allc_2m_mp.spec_index(allocator).global_pool.locking_thread() is Write
            &&& pool_perm.lock_id() == krnl.allc_2m_mp.spec_index(allocator).global_pool.locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(lctx.allocator_global_pool_2m_lock_map(), allocator, TypedLockMode::Write)
        },
    ensures
        ret.wf(),
        *ret == krnl.allc_2m_mp.spec_index(allocator).merge_2m_source_list(source),
{
    proof { assert(krnl.allc_2m_mp.perms_wf() && krnl.allc_2m_mp.spec_index(allocator).inv()) by { allocator_perms_wf_map(krnl.allc_2m_mp); allocator_perms_wf_at(krnl.allc_2m_mp, allocator); }; }
    if source < NUM_CPUS {
        let cache = krnl.allc_2m_mp.borrow_cache_typed(allocator, source, Ghost(lctx.allocator_cache_2m_lock_map()),
            Tracked(lctx), Tracked(cache_perms.tracked_borrow(source)));
        &cache.linked_list
    } else {
        let pool = krnl.allc_2m_mp.borrow_global_pool_typed(allocator, Ghost(lctx.allocator_global_pool_2m_lock_map()), Tracked(lctx), Tracked(pool_perm));
        &pool.linked_list
    }
}
pub fn split_2m_select_source(krnl: &KernelK, allocator: RwLockPageAllocatorPtr, cursor: &mut usize,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(cache_perms): Tracked<&Map<CpuId, LockPerm>>, Tracked(pool_perm): Tracked<&LockPerm>) -> (head: PageIndex)
    requires
        krnl.inv(),
        typed_lock_maps_aligned(krnl, lctx),
        krnl.allc_2m_mp.dom().contains(allocator),
        krnl.allc_2m_mp.spec_index(allocator).total_free_pages.view() > 0,
        *old(cursor) <= NUM_CPUS,
        forall|source: usize| #![trigger krnl.allc_2m_mp.spec_index(allocator).merge_2m_source_list(source)]
            #![trigger krnl.allc_2m_mp.spec_index(allocator).cpu_caches.spec_index(source)] source < *old(cursor) ==>
            krnl.allc_2m_mp.spec_index(allocator).merge_2m_source_list(source).length == 0
                && krnl.allc_2m_mp.spec_index(allocator).merge_2m_source_list(source).view().len() == 0,
        forall|cpu: CpuId| #![trigger cache_perms.spec_index(cpu)] cpu < NUM_CPUS ==> {
            &&& cache_perms.dom().contains(cpu)
            &&& cache_perms.spec_index(cpu).state() is WriteLock
            &&& cache_perms.spec_index(cpu).thread_id() == lctx.thread_id()
            &&& krnl.allc_2m_mp.spec_index(allocator).cpu_caches.spec_index(cpu).view().locking_thread() is Write
            &&& cache_perms.spec_index(cpu).lock_id() == krnl.allc_2m_mp.spec_index(allocator).cpu_caches.spec_index(cpu).view().locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(lctx.allocator_cache_2m_lock_map(), (allocator, cpu), TypedLockMode::Write)
        },
        pool_perm.state() is WriteLock,
        pool_perm.thread_id() == lctx.thread_id(),
        krnl.allc_2m_mp.spec_index(allocator).global_pool.locking_thread() is Write,
        pool_perm.lock_id() == krnl.allc_2m_mp.spec_index(allocator).global_pool.locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(lctx.allocator_global_pool_2m_lock_map(), allocator, TypedLockMode::Write),
    ensures
        *final(cursor) <= NUM_CPUS,
        *old(cursor) <= *final(cursor),
        forall|source: usize| #![trigger krnl.allc_2m_mp.spec_index(allocator).merge_2m_source_list(source)]
            #![trigger krnl.allc_2m_mp.spec_index(allocator).cpu_caches.spec_index(source)] source < *final(cursor) ==>
            krnl.allc_2m_mp.spec_index(allocator).merge_2m_source_list(source).length == 0
                && krnl.allc_2m_mp.spec_index(allocator).merge_2m_source_list(source).view().len() == 0,
        krnl.allc_2m_mp.spec_index(allocator).merge_2m_source_list(*final(cursor)).length > 0,
        krnl.allc_2m_mp.spec_index(allocator).merge_2m_source_list(*final(cursor)).view().len() > 0,
        krnl.allc_2m_mp.spec_index(allocator).merge_2m_source_list(*final(cursor)).view().spec_index(0) == spec_page_index2page_ptr(head),
        page_index_2m_valid(head),
        head <= NUM_PAGES - 512,
        krnl.pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator), state:
            if *final(cursor) < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: *final(cursor) } } else { FreePageAllocatorState::GlobalList } }),
        krnl.pg_arr.spec_index(head).view().view().owning_container == krnl.allc_2m_mp.spec_index(allocator).owning_container,
{
    let mut available = false;
    while *cursor < NUM_CPUS && !available
        invariant
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            krnl.allc_2m_mp.dom().contains(allocator),
            krnl.allc_2m_mp.spec_index(allocator).total_free_pages.view() > 0,
            forall|source: usize| #![trigger krnl.allc_2m_mp.spec_index(allocator).merge_2m_source_list(source)]
                    #![trigger krnl.allc_2m_mp.spec_index(allocator).cpu_caches.spec_index(source)] source < *cursor ==>
                krnl.allc_2m_mp.spec_index(allocator).merge_2m_source_list(source).length == 0
                    && krnl.allc_2m_mp.spec_index(allocator).merge_2m_source_list(source).view().len() == 0,
            forall|cpu: CpuId| #![trigger cache_perms.spec_index(cpu)] cpu < NUM_CPUS ==> {
                &&& cache_perms.dom().contains(cpu)
                &&& cache_perms.spec_index(cpu).state() is WriteLock
                &&& cache_perms.spec_index(cpu).thread_id() == lctx.thread_id()
                &&& krnl.allc_2m_mp.spec_index(allocator).cpu_caches.spec_index(cpu).view().locking_thread() is Write
                &&& cache_perms.spec_index(cpu).lock_id() == krnl.allc_2m_mp.spec_index(allocator).cpu_caches.spec_index(cpu).view().locking_thread()->Write_lock_id
                &&& typed_lock_map_contains_mode(lctx.allocator_cache_2m_lock_map(), (allocator, cpu), TypedLockMode::Write)
            },
            pool_perm.state() is WriteLock,
            pool_perm.thread_id() == lctx.thread_id(),
            krnl.allc_2m_mp.spec_index(allocator).global_pool.locking_thread() is Write,
            pool_perm.lock_id() == krnl.allc_2m_mp.spec_index(allocator).global_pool.locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(lctx.allocator_global_pool_2m_lock_map(), allocator, TypedLockMode::Write),
            *old(cursor) <= *cursor <= NUM_CPUS,
            available ==> krnl.allc_2m_mp.spec_index(allocator).merge_2m_source_list(*cursor).view().len() > 0,
        decreases NUM_CPUS - *cursor, if available { 0int } else { 1int },
    {
        let list = split_2m_borrow_source(krnl, allocator, *cursor, Tracked(lctx), Tracked(cache_perms), Tracked(pool_perm));
        proof { assert(list.view().len() == list.length) by { list.wf_implies_view_len_eq_len(); }; }
        available = list.len() != 0;
        if !available { *cursor += 1; }
    }
    proof {
        if *cursor == NUM_CPUS {
            assert(krnl.allc_2m_mp.spec_index(allocator).global_pool.view().linked_list.length > 0) by {
                allocator_perms_wf_at(krnl.allc_2m_mp, allocator);
                krnl.allc_2m_mp.spec_index(allocator).cpu_caches.view_index_eq_element_value();
                empty_caches_implies_cache_len_fold_zero(krnl.allc_2m_mp.spec_index(allocator).cpu_caches.view());
                krnl.allc_2m_mp.spec_index(allocator).global_pool.view().linked_list.wf_implies_view_len_eq_len();
            };
        }
    }
    let list = split_2m_borrow_source(krnl, allocator, *cursor, Tracked(lctx), Tracked(cache_perms), Tracked(pool_perm));
    proof { assert(list.view().len() == list.length) by { list.wf_implies_view_len_eq_len(); }; }
    let (_, pointer) = list.peek_head();
    proof {
        assert(page_ptr_valid(pointer)) by {
            if *cursor < NUM_CPUS { allocator_free_page_ptrs_wf_cache_at(krnl.allc_2m_mp, allocator, *cursor, pointer); }
            else { allocator_free_page_ptrs_wf_global_at(krnl.allc_2m_mp, allocator, pointer); }
        };
    }
    let head = page_ptr2page_index(pointer);
    proof {
        assert(krnl.pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator), state:
            if *cursor < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: *cursor } } else { FreePageAllocatorState::GlobalList } })
            && krnl.pg_arr.spec_index(head).view().view().owning_container == krnl.allc_2m_mp.spec_index(allocator).owning_container) by {
            if *cursor < NUM_CPUS { allocator_free_2m_pages_wf_cache_at(krnl.allc_2m_mp, krnl.pg_arr, allocator, *cursor, pointer); }
            else { allocator_free_2m_pages_wf_global_at(krnl.allc_2m_mp, krnl.pg_arr, allocator, pointer); }
        };
        assert(page_index_2m_valid(head)) by { hugepage_2m_wf_head_at(krnl.pg_arr, head); };
        assert(pointer == spec_page_index2page_ptr(head)) by { page_ptr_roundtrip(); };
    }
    head
}

}
