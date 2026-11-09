#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::*;
use super::split_2m_metadata::*;
use super::split_2m_thread_quotas::*;
#[cfg(verus_keep_ghost)]
use super::split_2m_commit_spec::*;
#[cfg(verus_keep_ghost)]
use super::split_2m_commit_eof::*;
#[cfg(verus_keep_ghost)]
use super::split_2m_entry_points::*;

verus! {
pub fn split_2m_commit(krnl: &mut KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, head: PageIndex, source: usize,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(cache_perms): Tracked<&Map<CpuId, LockPerm>>,
    Tracked(pool4_perm): Tracked<&LockPerm>, Tracked(pool2_perm): Tracked<&LockPerm>,
    Tracked(thread_perm): Tracked<&LockPerm>, Tracked(page_perms): Tracked<&Map<PageIndex, LockPerm>>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), lctx),
        lctx.kernel_view_locking_state() is Acquire,
        old(krnl).thrd_mp.dom().contains(thread),
        old(krnl).thrd_mp.spec_index(thread).view().temp_alloc_clean(),
        old(krnl).thrd_mp.spec_index(thread).view().quota_2m > 0,
        old(krnl).allc_4k_mp.dom().contains(allocator_4k),
        old(krnl).allc_2m_mp.dom().contains(allocator_2m),
        old(krnl).allc_4k_mp.spec_index(allocator_4k).owning_container == old(krnl).thrd_mp.spec_index(thread).view().owning_container,
        old(krnl).allc_2m_mp.spec_index(allocator_2m).owning_container == old(krnl).thrd_mp.spec_index(thread).view().owning_container,
        source <= NUM_CPUS,
        page_index_2m_valid(head),
        old(krnl).allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(source).view().len() > 0,
        old(krnl).allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(source).view().spec_index(0) == spec_page_index2page_ptr(head),
        old(krnl).pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator_2m), state:
            if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }),
        forall|cpu: CpuId| #![trigger cache_perms.spec_index(cpu)] #![trigger cache_perms.dom().contains(cpu)] cpu < NUM_CPUS ==> {
            &&& cache_perms.dom().contains(cpu)
            &&& cache_perms.spec_index(cpu).state() is WriteLock
            &&& cache_perms.spec_index(cpu).thread_id() == lctx.thread_id()
            &&& old(krnl).allc_2m_mp.spec_index(allocator_2m).cpu_caches.spec_index(cpu).view().locking_thread() is Write
            &&& cache_perms.spec_index(cpu).lock_id() == old(krnl).allc_2m_mp.spec_index(allocator_2m).cpu_caches.spec_index(cpu).view().locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(lctx.allocator_cache_2m_lock_map(), (allocator_2m, cpu), TypedLockMode::Write)
        },
        pool4_perm.state() is WriteLock,
        pool4_perm.thread_id() == lctx.thread_id(),
        old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.locking_thread() is Write,
        pool4_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(lctx.allocator_global_pool_4k_lock_map(), allocator_4k, TypedLockMode::Write),
        pool2_perm.state() is WriteLock,
        pool2_perm.thread_id() == lctx.thread_id(),
        old(krnl).allc_2m_mp.spec_index(allocator_2m).global_pool.locking_thread() is Write,
        pool2_perm.lock_id() == old(krnl).allc_2m_mp.spec_index(allocator_2m).global_pool.locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(lctx.allocator_global_pool_2m_lock_map(), allocator_2m, TypedLockMode::Write),
        thread_perm.state() is WriteLock,
        thread_perm.thread_id() == lctx.thread_id(),
        old(krnl).thrd_mp.spec_index(thread).locking_thread() is Write,
        thread_perm.lock_id() == old(krnl).thrd_mp.spec_index(thread).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread, TypedLockMode::Write),
        forall|index: PageIndex| #![trigger page_perms.spec_index(index)] #![trigger page_perms.dom().contains(index)] head <= index < head + 512 ==> {
            &&& page_perms.dom().contains(index)
            &&& page_perms.spec_index(index).state() is WriteLock
            &&& page_perms.spec_index(index).thread_id() == lctx.thread_id()
            &&& old(krnl).pg_arr.spec_index(index).view().locking_thread() is Write
            &&& page_perms.spec_index(index).lock_id() == old(krnl).pg_arr.spec_index(index).view().locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(lctx.page_lock_map(), index, TypedLockMode::Write)
        },
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), lctx),
        forall|index: PageIndex| #![trigger page_perms.spec_index(index)] #![trigger page_perms.dom().contains(index)] head <= index < head + 512 ==> {
            &&& page_perms.dom().contains(index)
            &&& page_perms.spec_index(index).state() is WriteLock
            &&& page_perms.spec_index(index).thread_id() == lctx.thread_id()
            &&& final(krnl).pg_arr.spec_index(index).view().locking_thread() is Write
            &&& page_perms.spec_index(index).lock_id() == final(krnl).pg_arr.spec_index(index).view().locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(lctx.page_lock_map(), index, TypedLockMode::Write)
        },
        split_2m_commit_eof_transition_framing(*old(krnl), *final(krnl), thread, allocator_4k, allocator_2m, head, source),
        final(krnl).thrd_mp.spec_index(thread).view().quota_4k == old(krnl).thrd_mp.spec_index(thread).view().quota_4k + 512,
        final(krnl).thrd_mp.spec_index(thread).view().quota_2m + 1 == old(krnl).thrd_mp.spec_index(thread).view().quota_2m,
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, thrd_mp: final(krnl).thrd_mp,
            allc_4k_mp: final(krnl).allc_4k_mp, allc_2m_mp: final(krnl).allc_2m_mp, ..*old(krnl) }),
        final(krnl).thrd_mp.unchanged_except(&old(krnl).thrd_mp, thread),
        final(krnl).thrd_mp.spec_index(thread).view() == (Thread { quota_4k: (old(krnl).thrd_mp.spec_index(thread).view().quota_4k + 512) as usize,
            quota_2m: (old(krnl).thrd_mp.spec_index(thread).view().quota_2m - 1) as usize, ..old(krnl).thrd_mp.spec_index(thread).view() }),
        final(krnl).allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
        final(krnl).allc_2m_mp.dom() == old(krnl).allc_2m_mp.dom(),
        final(krnl).allc_4k_mp.unchanged_except(&old(krnl).allc_4k_mp, allocator_4k),
        final(krnl).allc_2m_mp.unchanged_except(&old(krnl).allc_2m_mp, allocator_2m),
        final(krnl).allc_4k_mp.spec_index(allocator_4k).owning_container == old(krnl).allc_4k_mp.spec_index(allocator_4k).owning_container,
        final(krnl).allc_2m_mp.spec_index(allocator_2m).owning_container == old(krnl).allc_2m_mp.spec_index(allocator_2m).owning_container,
        final(krnl).allc_4k_mp.spec_index(allocator_4k).quota == old(krnl).allc_4k_mp.spec_index(allocator_4k).quota,
        final(krnl).allc_2m_mp.spec_index(allocator_2m).quota == old(krnl).allc_2m_mp.spec_index(allocator_2m).quota,
        final(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.locking_thread() == old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.locking_thread(),
        final(krnl).allc_2m_mp.spec_index(allocator_2m).global_pool.locking_thread() == old(krnl).allc_2m_mp.spec_index(allocator_2m).global_pool.locking_thread(),
        final(krnl).thrd_mp.spec_index(thread).locking_thread() == old(krnl).thrd_mp.spec_index(thread).locking_thread(),
        final(krnl).thrd_mp.spec_index(thread).view_rodata() == old(krnl).thrd_mp.spec_index(thread).view_rodata(),
        final(krnl).thrd_mp.spec_index(thread).view_ghost() == old(krnl).thrd_mp.spec_index(thread).view_ghost(),
        final(krnl).thrd_mp.spec_index(thread).being_killed() == old(krnl).thrd_mp.spec_index(thread).being_killed(),
        forall|cpu: CpuId| #![trigger final(krnl).allc_2m_mp.spec_index(allocator_2m).cpu_caches.spec_index(cpu)] cpu < NUM_CPUS ==>
            final(krnl).allc_2m_mp.spec_index(allocator_2m).cpu_caches.spec_index(cpu).view().locking_thread() == old(krnl).allc_2m_mp.spec_index(allocator_2m).cpu_caches.spec_index(cpu).view().locking_thread(),
        forall|s: usize| #![trigger final(krnl).allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(s)] s <= NUM_CPUS ==>
            final(krnl).allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(s).view() == if s == source {
                old(krnl).allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(s).view().skip(1)
            } else { old(krnl).allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(s).view() },
        forall|s: usize| #![trigger final(krnl).allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(s)] s <= NUM_CPUS && s != source ==>
            final(krnl).allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(s) == old(krnl).allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(s),
{
    proof {
        assert(PAGE_SZ_4K == 4096) by (bit_vector);
        allocator_perms_wf_map(krnl.allc_4k_mp); allocator_perms_wf_at(krnl.allc_4k_mp, allocator_4k);
        allocator_perms_wf_map(krnl.allc_2m_mp); allocator_perms_wf_at(krnl.allc_2m_mp, allocator_2m);
        page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, head);
        thread_perms_wf_map(krnl.thrd_mp); thread_perms_wf_at(krnl.thrd_mp, thread);
        thread_quota_4k_implies_split_quota_capacity(krnl, thread, allocator_4k);
        allocator_free_2m_pages_wf_at(krnl.allc_2m_mp, krnl.pg_arr, head);
    }
    let owner = krnl.pg_arr.borrow_typed(head, Ghost(lctx.page_lock_map()), Tracked(lctx), Tracked(page_perms.tracked_borrow(head))).owning_container;
    let (head_node, head_node_perm) = if source < NUM_CPUS {
        krnl.allc_2m_mp.pop_cache_page_typed(allocator_2m, source,
            Ghost(lctx.allocator_quota_2m_lock_map()), Ghost(lctx.allocator_cache_2m_lock_map()), Ghost(lctx.allocator_global_pool_2m_lock_map()),
            Tracked(lctx), Tracked(cache_perms.tracked_borrow(source)))
    } else {
        proof { krnl.allc_2m_mp.spec_index(allocator_2m).global_pool.view().linked_list.wf_implies_view_len_eq_len(); }
        krnl.allc_2m_mp.pop_global_pool_page_typed(allocator_2m,
            Ghost(lctx.allocator_quota_2m_lock_map()), Ghost(lctx.allocator_cache_2m_lock_map()), Ghost(lctx.allocator_global_pool_2m_lock_map()),
            Tracked(lctx), Tracked(pool2_perm))
    };
    assert(head_node == old(krnl).pg_arr.spec_index(head).view().view().free_list_node_storage.addr()) by {
        old(krnl).allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(source).wf_and_equal_values_implies_equal_addrs(
            head_node, old(krnl).pg_arr.spec_index(head).view().view().free_list_node_storage.addr());
    };
    let page = krnl.pg_arr.borrow_mut_typed(head, Ghost(lctx.page_lock_map()), Tracked(lctx), Tracked(page_perms.tracked_borrow(head)));
    let Tracked(mut children) = split_2m_head(page, Ghost(head), Ghost(allocator_4k), Ghost(old(krnl).pg_arr));
    assert(!krnl.allc_4k_mp.spec_index(allocator_4k).global_pool.view().view().contains(spec_page_index2page_ptr(head))) by {
        allocator_free_4k_pages_wf_global_at(old(krnl).allc_4k_mp, old(krnl).pg_arr, allocator_4k, spec_page_index2page_ptr(head));
        page_index_roundtrip();
    };
    krnl.allc_4k_mp.push_global_pool_page_typed(allocator_4k, head_node, head_node_perm,
        Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()), Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(lctx), Tracked(pool4_perm));
    let mut offset = 1usize;
    while offset < 512
        invariant
            old(krnl).inv(),
            typed_lock_maps_aligned(old(krnl), lctx),
            lctx.kernel_view_locking_state() is Acquire,
            old(krnl).thrd_mp.dom().contains(thread),
            old(krnl).thrd_mp.spec_index(thread).view().temp_alloc_clean(),
            old(krnl).thrd_mp.spec_index(thread).view().quota_2m > 0,
            old(krnl).allc_4k_mp.dom().contains(allocator_4k),
            old(krnl).allc_2m_mp.dom().contains(allocator_2m),
            old(krnl).allc_4k_mp.spec_index(allocator_4k).owning_container == old(krnl).thrd_mp.spec_index(thread).view().owning_container,
            old(krnl).allc_2m_mp.spec_index(allocator_2m).owning_container == old(krnl).thrd_mp.spec_index(thread).view().owning_container,
            source <= NUM_CPUS,
            page_index_2m_valid(head),
            old(krnl).allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(source).view().len() > 0,
            old(krnl).allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(source).view().spec_index(0) == spec_page_index2page_ptr(head),
            old(krnl).pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator_2m), state:
                if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }),
            forall|cpu: CpuId| #![trigger cache_perms.spec_index(cpu)] #![trigger cache_perms.dom().contains(cpu)] cpu < NUM_CPUS ==> {
                &&& cache_perms.dom().contains(cpu)
                &&& cache_perms.spec_index(cpu).state() is WriteLock
                &&& cache_perms.spec_index(cpu).thread_id() == lctx.thread_id()
                &&& old(krnl).allc_2m_mp.spec_index(allocator_2m).cpu_caches.spec_index(cpu).view().locking_thread() is Write
                &&& cache_perms.spec_index(cpu).lock_id() == old(krnl).allc_2m_mp.spec_index(allocator_2m).cpu_caches.spec_index(cpu).view().locking_thread()->Write_lock_id
                &&& typed_lock_map_contains_mode(lctx.allocator_cache_2m_lock_map(), (allocator_2m, cpu), TypedLockMode::Write)
            },
            pool4_perm.state() is WriteLock,
            pool4_perm.thread_id() == lctx.thread_id(),
            old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.locking_thread() is Write,
            pool4_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(lctx.allocator_global_pool_4k_lock_map(), allocator_4k, TypedLockMode::Write),
            pool2_perm.state() is WriteLock,
            pool2_perm.thread_id() == lctx.thread_id(),
            old(krnl).allc_2m_mp.spec_index(allocator_2m).global_pool.locking_thread() is Write,
            pool2_perm.lock_id() == old(krnl).allc_2m_mp.spec_index(allocator_2m).global_pool.locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(lctx.allocator_global_pool_2m_lock_map(), allocator_2m, TypedLockMode::Write),
            thread_perm.state() is WriteLock,
            thread_perm.thread_id() == lctx.thread_id(),
            old(krnl).thrd_mp.spec_index(thread).locking_thread() is Write,
            thread_perm.lock_id() == old(krnl).thrd_mp.spec_index(thread).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(lctx.thread_lock_map(), thread, TypedLockMode::Write),
            forall|index: PageIndex| #![trigger page_perms.spec_index(index)] #![trigger page_perms.dom().contains(index)] head <= index < head + 512 ==> {
                &&& page_perms.dom().contains(index)
                &&& page_perms.spec_index(index).state() is WriteLock
                &&& page_perms.spec_index(index).thread_id() == lctx.thread_id()
                &&& old(krnl).pg_arr.spec_index(index).view().locking_thread() is Write
                &&& page_perms.spec_index(index).lock_id() == old(krnl).pg_arr.spec_index(index).view().locking_thread()->Write_lock_id
                &&& typed_lock_map_contains_mode(lctx.page_lock_map(), index, TypedLockMode::Write)
            },
            1 <= offset <= 512,
            PAGE_SZ_4K == 4096,
            old(krnl).pg_arr.spec_index(head).view().view().inv(),
            owner == old(krnl).pg_arr.spec_index(head).view().view().owning_container,
            owner == old(krnl).allc_4k_mp.spec_index(allocator_4k).owning_container,
            old(krnl).thrd_mp.spec_index(thread).view().quota_4k <= usize::MAX - 512,
            old(krnl).allc_4k_mp.spec_index(allocator_4k).total_free_pages.view() <= usize::MAX - 512,
            krnl.pg_arr.inv(),
            krnl.thrd_mp == old(krnl).thrd_mp,
            krnl.thrd_mp.perms_wf(),
            krnl.allc_4k_mp.perms_wf(),
            krnl.allc_2m_mp.perms_wf(),
            krnl.allc_4k_mp.spec_index(allocator_4k).wf(),
            krnl.allc_2m_mp.spec_index(allocator_2m).wf(),
            typed_lock_maps_aligned(krnl, lctx),
            children.dom() == Set::<usize>::range(offset, 512),
            forall|i: usize| #![trigger children.spec_index(i)] offset <= i < 512 ==> {
                &&& children.spec_index(i).is_init()
                &&& children.spec_index(i).addr() == (head + i) * PAGE_SZ_4K
                &&& children.spec_index(i).value().view() == old(krnl).pg_arr.spec_index(head).view().view().perm_2m.view().unwrap().value().view().subrange(i * PAGE_SZ_4K, (i + 1) * PAGE_SZ_4K)
            },
            *krnl == (KernelK { pg_arr: krnl.pg_arr, thrd_mp: old(krnl).thrd_mp, allc_4k_mp: krnl.allc_4k_mp, allc_2m_mp: krnl.allc_2m_mp, ..*old(krnl) }),
            forall|index: PageIndex| #![trigger krnl.pg_arr.spec_index(index)] #![trigger old(krnl).pg_arr.spec_index(index)]
                index_valid(NUM_PAGES, index) && !Set::<PageIndex>::range(head, (head + offset) as usize).contains(index) ==> krnl.pg_arr.spec_index(index) == old(krnl).pg_arr.spec_index(index),
            forall|index: PageIndex| #![trigger krnl.pg_arr.spec_index(index)]
                #![trigger old(krnl).ctn_mp.spec_index(old(krnl).pg_arr.spec_index(head).view().view().owning_container).view().owned_pages.view().contains(spec_page_index2page_ptr(index))] Set::<PageIndex>::range(head, (head + offset) as usize).contains(index) ==> {
                let old_cell = old(krnl).pg_arr.spec_index(index).view();
                let new_cell = krnl.pg_arr.spec_index(index).view();
                let old_page = old_cell.view();
                let new_page = new_cell.view();
                &&& (index != head ==> spec_page_index_merge_2m_valid(head, index))
                &&& new_cell.is_init() == old_cell.is_init()
                &&& new_cell.locking_thread() == old_cell.locking_thread()
                &&& new_cell.being_killed() == old_cell.being_killed()
                &&& new_cell.view_rodata() == old_cell.view_rodata()
                &&& new_cell.view_ghost() == old_cell.view_ghost()
                &&& new_cell.control() == old_cell.control()
                &&& new_cell.killer_info() == old_cell.killer_info()
                &&& krnl.pg_arr.lock_id_by_index(index) == old(krnl).pg_arr.lock_id_by_index(index)
                &&& new_page == (Page { state: new_page.state, perm_4k: new_page.perm_4k, perm_2m: new_page.perm_2m,
                    owning_container: old(krnl).pg_arr.spec_index(head).view().view().owning_container,
                    free_list_node_storage: new_page.free_list_node_storage, ..old_page })
                &&& new_page.state == PageState::Free4k { allocator_ptr: Ghost(allocator_4k), state: FreePageAllocatorState::GlobalList }
                &&& new_page.perm_2m.view().is_none()
                &&& new_page.perm_4k.view().is_some()
                &&& new_page.perm_4k.view().unwrap().is_init()
                &&& new_page.perm_4k.view().unwrap().addr() == index * PAGE_SZ_4K
                &&& new_page.perm_4k.view().unwrap().value().view() == old(krnl).pg_arr.spec_index(head).view().view().perm_2m.view().unwrap().value().view().subrange((index - head) * PAGE_SZ_4K, (index - head + 1) * PAGE_SZ_4K)
                &&& !new_page.free_list_node_storage.is_init()
                &&& new_page.free_list_node_storage.addr() == old_page.free_list_node_storage.addr()
            },
            krnl.allc_4k_mp.unchanged_except(&old(krnl).allc_4k_mp, allocator_4k),
            krnl.allc_4k_mp.spec_index(allocator_4k).quota == old(krnl).allc_4k_mp.spec_index(allocator_4k).quota,
            krnl.allc_4k_mp.spec_index(allocator_4k).owning_container == old(krnl).allc_4k_mp.spec_index(allocator_4k).owning_container,
            krnl.allc_4k_mp.spec_index(allocator_4k).global_pool.is_init() == old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.is_init(),
            krnl.allc_4k_mp.spec_index(allocator_4k).global_pool.locking_thread() == old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.locking_thread(),
            krnl.allc_4k_mp.spec_index(allocator_4k).global_pool.being_killed() == old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.being_killed(),
            krnl.allc_4k_mp.spec_index(allocator_4k).global_pool.view_rodata() == old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.view_rodata(),
            krnl.allc_4k_mp.spec_index(allocator_4k).global_pool.view_ghost() == old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.view_ghost(),
            krnl.allc_4k_mp.spec_index(allocator_4k).global_pool.control() == old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.control(),
            krnl.allc_4k_mp.spec_index(allocator_4k).global_pool.killer_info() == old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.killer_info(),
            krnl.allc_4k_mp.spec_index(allocator_4k).global_pool.view().line_pad == old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.view().line_pad,
            krnl.allc_4k_mp.spec_index(allocator_4k).global_pool.view().linked_list.minor == old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.view().linked_list.minor,
            krnl.allc_4k_mp.spec_index(allocator_4k).global_pool.view().linked_list.container_depth == old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.view().linked_list.container_depth,
            krnl.allc_2m_mp.unchanged_except(&old(krnl).allc_2m_mp, allocator_2m),
            krnl.allc_2m_mp.spec_index(allocator_2m).quota == old(krnl).allc_2m_mp.spec_index(allocator_2m).quota,
            krnl.allc_2m_mp.spec_index(allocator_2m).owning_container == old(krnl).allc_2m_mp.spec_index(allocator_2m).owning_container,
            krnl.allc_2m_mp.spec_index(allocator_2m).global_pool.is_init() == old(krnl).allc_2m_mp.spec_index(allocator_2m).global_pool.is_init(),
            krnl.allc_2m_mp.spec_index(allocator_2m).global_pool.locking_thread() == old(krnl).allc_2m_mp.spec_index(allocator_2m).global_pool.locking_thread(),
            krnl.allc_2m_mp.spec_index(allocator_2m).global_pool.being_killed() == old(krnl).allc_2m_mp.spec_index(allocator_2m).global_pool.being_killed(),
            krnl.allc_2m_mp.spec_index(allocator_2m).global_pool.view_rodata() == old(krnl).allc_2m_mp.spec_index(allocator_2m).global_pool.view_rodata(),
            krnl.allc_2m_mp.spec_index(allocator_2m).global_pool.view_ghost() == old(krnl).allc_2m_mp.spec_index(allocator_2m).global_pool.view_ghost(),
            krnl.allc_2m_mp.spec_index(allocator_2m).global_pool.control() == old(krnl).allc_2m_mp.spec_index(allocator_2m).global_pool.control(),
            krnl.allc_2m_mp.spec_index(allocator_2m).global_pool.killer_info() == old(krnl).allc_2m_mp.spec_index(allocator_2m).global_pool.killer_info(),
            krnl.allc_2m_mp.spec_index(allocator_2m).global_pool.view().line_pad == old(krnl).allc_2m_mp.spec_index(allocator_2m).global_pool.view().line_pad,
            krnl.allc_2m_mp.spec_index(allocator_2m).global_pool.view().linked_list.minor == old(krnl).allc_2m_mp.spec_index(allocator_2m).global_pool.view().linked_list.minor,
            krnl.allc_2m_mp.spec_index(allocator_2m).global_pool.view().linked_list.container_depth == old(krnl).allc_2m_mp.spec_index(allocator_2m).global_pool.view().linked_list.container_depth,
            old(krnl).allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(NUM_CPUS) == old(krnl).allc_2m_mp.spec_index(allocator_2m).global_pool.view().linked_list,
            krnl.allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(NUM_CPUS) == krnl.allc_2m_mp.spec_index(allocator_2m).global_pool.view().linked_list,
            krnl.allc_4k_mp.spec_index(allocator_4k).cpu_caches == old(krnl).allc_4k_mp.spec_index(allocator_4k).cpu_caches,
            krnl.allc_4k_mp.spec_index(allocator_4k).total_free_pages.view() == old(krnl).allc_4k_mp.spec_index(allocator_4k).total_free_pages.view() + offset,
            krnl.allc_2m_mp.spec_index(allocator_2m).total_free_pages.view() + 1 == old(krnl).allc_2m_mp.spec_index(allocator_2m).total_free_pages.view(),
            krnl.allc_4k_mp.spec_index(allocator_4k).global_pool.view().view() == Seq::new(offset as nat, |i: int| spec_page_index2page_ptr((head + offset - 1 - i) as usize)) + old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.view().view(),
            forall|pointer: PagePtr| #![trigger krnl.allc_4k_mp.spec_index(allocator_4k).global_pool.view().view().contains(pointer)] #![trigger old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.view().view().contains(pointer)]
                krnl.allc_4k_mp.spec_index(allocator_4k).global_pool.view().view().contains(pointer)
                    == (old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.view().view().contains(pointer)
                        || (Set::<PageIndex>::range(head, (head + offset) as usize).contains((pointer / 4096) as usize) && pointer == spec_page_index2page_ptr((pointer / 4096) as usize))),
            forall|index: PageIndex| #![trigger krnl.pg_arr.spec_index(index)] Set::<PageIndex>::range(head, (head + offset) as usize).contains(index) ==>
                krnl.allc_4k_mp.spec_index(allocator_4k).global_pool.view().map().spec_index(krnl.pg_arr.spec_index(index).view().view().free_list_node_storage.addr()) == spec_page_index2page_ptr(index)
                && krnl.allc_4k_mp.spec_index(allocator_4k).global_pool.view().map().dom().contains(krnl.pg_arr.spec_index(index).view().view().free_list_node_storage.addr()),
            forall|key: usize| #![trigger krnl.allc_4k_mp.spec_index(allocator_4k).global_pool.view().map().spec_index(key)] #![trigger old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.view().map().dom().contains(key)]
                old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.view().map().dom().contains(key) ==>
                krnl.allc_4k_mp.spec_index(allocator_4k).global_pool.view().map().dom().contains(key)
                && krnl.allc_4k_mp.spec_index(allocator_4k).global_pool.view().map().spec_index(key) == old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.view().map().spec_index(key),
            forall|s: usize| #![trigger krnl.allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(s)] #![trigger krnl.allc_2m_mp.spec_index(allocator_2m).cpu_caches.spec_index(s)] s <= NUM_CPUS ==> {
                let before = old(krnl).allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(s);
                let after = krnl.allc_2m_mp.spec_index(allocator_2m).merge_2m_source_list(s);
                &&& (s != source ==> after == before)
                &&& after.view() == if s == source { before.view().skip(1) } else { before.view() }
                &&& after.map() == if s == source { before.map().remove(old(krnl).pg_arr.spec_index(head).view().view().free_list_node_storage.addr()) } else { before.map() }
                &&& forall|pointer: PagePtr| #![trigger after.view().contains(pointer)] #![trigger before.view().contains(pointer)]
                    after.view().contains(pointer) == (before.view().contains(pointer) && !(s == source && pointer == spec_page_index2page_ptr(head)))
            },
            forall|cpu: CpuId| #![trigger krnl.allc_2m_mp.spec_index(allocator_2m).cpu_caches.spec_index(cpu)] cpu < NUM_CPUS ==> {
                let old_cache = old(krnl).allc_2m_mp.spec_index(allocator_2m).cpu_caches.spec_index(cpu).view();
                let new_cache = krnl.allc_2m_mp.spec_index(allocator_2m).cpu_caches.spec_index(cpu).view();
                &&& new_cache.is_init() == old_cache.is_init()
                &&& new_cache.locking_thread() == old_cache.locking_thread()
                &&& new_cache.being_killed() == old_cache.being_killed()
                &&& new_cache.view_rodata() == old_cache.view_rodata()
                &&& new_cache.view_ghost() == old_cache.view_ghost()
                &&& new_cache.control() == old_cache.control()
                &&& new_cache.killer_info() == old_cache.killer_info()
                &&& new_cache.view().view().len() <= old_cache.view().view().len()
                &&& new_cache.view().line_pad == old_cache.view().line_pad
                &&& new_cache.view().linked_list.minor == old_cache.view().linked_list.minor
                &&& new_cache.view().linked_list.container_depth == old_cache.view().linked_list.container_depth
            },
        decreases 512 - offset,
    {
        let index = head + offset;
        proof { hugepage_2m_wf_tail_forward_at(old(krnl).pg_arr, head, index); page_array_wf_at(old(krnl).pg_arr, index); }
        assert(!krnl.allc_4k_mp.spec_index(allocator_4k).global_pool.view().view().contains(spec_page_index2page_ptr(index))) by {
            allocator_free_4k_pages_wf_global_at(old(krnl).allc_4k_mp, old(krnl).pg_arr, allocator_4k, spec_page_index2page_ptr(index));
            page_index_roundtrip();
        };
        let tracked child = children.tracked_remove(offset);
        let page = krnl.pg_arr.borrow_mut_typed(index, Ghost(lctx.page_lock_map()), Tracked(lctx), Tracked(page_perms.tracked_borrow(index)));
        let (node_addr, node_perm) = split_2m_tail(page, allocator_4k, owner, Tracked(child));
        krnl.allc_4k_mp.push_global_pool_page_typed(allocator_4k, node_addr, node_perm,
            Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()), Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(lctx), Tracked(pool4_perm));
        offset += 1;
    }
    let thread_value = krnl.thrd_mp.borrow_mut_typed(thread, Ghost(lctx.thread_lock_map()), Tracked(lctx), Tracked(thread_perm));
    split_2m_exchange_thread_quotas(thread_value);
    proof {
        assert(split_2m_commit_eof_transition_framing(*old(krnl), *krnl, thread, allocator_4k, allocator_2m, head, source)) by {
            reveal(split_2m_commit_eof_transition_framing);
        };
        split_2m_commit_eof_implies_kernel_inv(*old(krnl), *krnl, thread, allocator_4k, allocator_2m, head, source, lctx);
    }
}
}
