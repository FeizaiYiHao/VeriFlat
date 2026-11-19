#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::simple_pptr::*;
use crate::*;
use super::merge_2m_scan::*;
use super::merge_2m_scanner::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_commit_scanner_eof::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_commit_eof_complete_heads::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_scanner_spec::*;
use super::merge_2m_metadata::*;
use super::merge_2m_thread_quotas::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_commit_spec::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_commit_eof::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_entry_points::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_entry_folds::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_quota_folds::*;

verus! {
#[verifier::rlimit(40)]
pub fn merge_2m_commit(krnl: &mut KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, candidate: &Merge2mCandidate,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(cache_perms): Tracked<&Map<CpuId, LockPerm>>,
    Tracked(pool4_perm): Tracked<&LockPerm>, Tracked(pool2_perm): Tracked<&LockPerm>,
    Tracked(thread_perm): Tracked<&LockPerm>, Tracked(page_perms): Tracked<&Map<PageIndex, LockPerm>>, Ghost(scanner): Ghost<Merge2mScanner>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), lctx),
        lctx.kernel_view_locking_state() is Acquire,
        old(krnl).thrd_mp.dom().contains(thread),
        old(krnl).thrd_mp.spec_index(thread).view().temp_alloc_clean(),
        old(krnl).thrd_mp.spec_index(thread).view().quota_4k >= 512,
        old(krnl).allc_4k_mp.dom().contains(allocator_4k),
        old(krnl).allc_2m_mp.dom().contains(allocator_2m),
        old(krnl).allc_4k_mp.spec_index(allocator_4k).owning_container == old(krnl).thrd_mp.spec_index(thread).view().owning_container,
        old(krnl).allc_2m_mp.spec_index(allocator_2m).owning_container == old(krnl).thrd_mp.spec_index(thread).view().owning_container,
        forall|source: usize| #![trigger old(krnl).allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source)] source <= NUM_CPUS ==>
            LinkedList::<PagePtr, 233>::values_sorted(old(krnl).allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source).view()),
        scanner.wf(old(krnl).allc_4k_mp.spec_index(allocator_4k)),
        scanner.candidate == *candidate,
        scanner.returned_heads.view().contains(candidate.head),
        candidate.wf(),
        candidate.sources.len() == 512,
        merge_2m_complete_heads(merge_2m_source_pages(old(krnl).allc_4k_mp.spec_index(allocator_4k))).contains(candidate.head),
        page_index_2m_valid(candidate.head),
        forall|index: PageIndex| #![trigger old(krnl).pg_arr.spec_index(index)] candidate.head <= index < candidate.head + 512 ==> {
            let source = candidate.sources.view().spec_index(index as int - candidate.head as int) as usize;
            &&& index_valid(NUM_PAGES, index)
            &&& old(krnl).pg_arr.spec_index(index).view().view().state == PageState::Free4k { allocator_ptr: Ghost(allocator_4k), state:
                if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }
        },
        forall|cpu: CpuId| #![trigger cache_perms.spec_index(cpu)] #![trigger cache_perms.dom().contains(cpu)] cpu < NUM_CPUS ==> {
            &&& cache_perms.dom().contains(cpu)
            &&& cache_perms.spec_index(cpu).state() is WriteLock
            &&& cache_perms.spec_index(cpu).thread_id() == lctx.thread_id()
            &&& old(krnl).allc_4k_mp.spec_index(allocator_4k).cpu_caches.spec_index(cpu).view().locking_thread() is Write
            &&& cache_perms.spec_index(cpu).lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_4k).cpu_caches.spec_index(cpu).view().locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(lctx.allocator_cache_4k_lock_map(), (allocator_4k, cpu), TypedLockMode::Write)
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
        forall|index: PageIndex| #![trigger page_perms.spec_index(index)] #![trigger page_perms.dom().contains(index)] candidate.head <= index < candidate.head + 512 ==> {
            &&& page_perms.dom().contains(index)
            &&& page_perms.spec_index(index).state() is WriteLock
            &&& page_perms.spec_index(index).thread_id() == lctx.thread_id()
            &&& old(krnl).pg_arr.spec_index(index).view().locking_thread() is Write
            &&& page_perms.spec_index(index).lock_id() == old(krnl).pg_arr.spec_index(index).view().locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(lctx.page_lock_map(), index, TypedLockMode::Write)
        },
    ensures
        final(krnl).inv(),
        scanner.wf(final(krnl).allc_4k_mp.spec_index(allocator_4k)),
        merge_2m_complete_heads(merge_2m_source_pages(final(krnl).allc_4k_mp.spec_index(allocator_4k)))
            == merge_2m_complete_heads(merge_2m_source_pages(old(krnl).allc_4k_mp.spec_index(allocator_4k))).remove(candidate.head),
        merge_2m_complete_heads(merge_2m_source_pages(final(krnl).allc_4k_mp.spec_index(allocator_4k))).len() + 1
            == merge_2m_complete_heads(merge_2m_source_pages(old(krnl).allc_4k_mp.spec_index(allocator_4k))).len(),
        typed_lock_maps_aligned(final(krnl), lctx),
        merge_2m_commit_eof_transition_framing(*old(krnl), *final(krnl), thread, allocator_4k, allocator_2m, *candidate),
        final(krnl).thrd_mp.spec_index(thread).view().quota_4k + 512 == old(krnl).thrd_mp.spec_index(thread).view().quota_4k,
        final(krnl).thrd_mp.spec_index(thread).view().quota_2m == old(krnl).thrd_mp.spec_index(thread).view().quota_2m + 1,
{
    proof {
        assert(PAGE_SZ_4K == 4096) by (bit_vector);
        allocator_perms_wf_map(krnl.allc_4k_mp); allocator_perms_wf_at(krnl.allc_4k_mp, allocator_4k);
        allocator_perms_wf_map(krnl.allc_2m_mp); allocator_perms_wf_at(krnl.allc_2m_mp, allocator_2m);
        page_array_wf_map(krnl.pg_arr); thread_perms_wf_map(krnl.thrd_mp); thread_perms_wf_at(krnl.thrd_mp, thread);
        assert(krnl.allc_2m_mp.spec_index(allocator_2m).total_free_pages.view() < usize::MAX && krnl.thrd_mp.spec_index(thread).view().quota_2m < usize::MAX) by {
            allocator_free_page_ptrs_wf_implies_free_count_fold_bounded(krnl.allc_2m_mp, allocator_2m);
            container_thread_wf_thread_at(krnl.ctn_mp, krnl.thrd_mp, thread);
            container_allocator_2m_forward_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, allocator_2m);
            container_process_allocator_quota_2m_wf_at(krnl.ctn_mp, krnl.prc_mp, krnl.thrd_mp, krnl.allc_2m_mp, krnl.thrd_mp.spec_index(thread).view().owning_container);
            container_thread_and_perms_wf_implies_2m_fold_sum_ge_thread_quota(krnl.ctn_mp, krnl.prc_mp, krnl.thrd_mp, krnl.thrd_mp.spec_index(thread).view().owning_container, thread);
        };
    }
    let head = candidate.head;
    let ghost head_ptr = spec_page_index2page_ptr(head);
    assert(!krnl.allc_2m_mp.spec_index(allocator_2m).global_pool.view().view().contains(head_ptr)) by {
        allocator_free_2m_pages_wf_global_at(krnl.allc_2m_mp, krnl.pg_arr, allocator_2m, head_ptr);
        page_index_roundtrip();
    };
    proof { page_array_wf_at(old(krnl).pg_arr, head); }
    let tracked mut head_node_perm: Option<PointsTo<Node<PagePtr>>> = None;
    let tracked mut tail_perms: Map<usize, PagePerm4k> = Map::tracked_empty();
    let mut head_node_addr = 0usize;
    let mut offset = 0usize;
    while offset < 512
        invariant
            old(krnl).inv(),
            typed_lock_maps_aligned(old(krnl), lctx),
            lctx.kernel_view_locking_state() is Acquire,
            old(krnl).thrd_mp.dom().contains(thread),
            old(krnl).thrd_mp.spec_index(thread).view().temp_alloc_clean(),
            old(krnl).thrd_mp.spec_index(thread).view().quota_4k >= 512,
            old(krnl).allc_4k_mp.dom().contains(allocator_4k),
            old(krnl).allc_2m_mp.dom().contains(allocator_2m),
            old(krnl).allc_4k_mp.spec_index(allocator_4k).owning_container == old(krnl).thrd_mp.spec_index(thread).view().owning_container,
            old(krnl).allc_2m_mp.spec_index(allocator_2m).owning_container == old(krnl).thrd_mp.spec_index(thread).view().owning_container,
            scanner.wf(old(krnl).allc_4k_mp.spec_index(allocator_4k)),
            scanner.candidate == *candidate,
            scanner.returned_heads.view().contains(candidate.head),
            candidate.wf(),
            candidate.sources.len() == 512,
            page_index_2m_valid(candidate.head),
            forall|index: PageIndex| #![trigger old(krnl).pg_arr.spec_index(index)] candidate.head <= index < candidate.head + 512 ==> {
                let source = candidate.sources.view().spec_index(index as int - candidate.head as int) as usize;
                &&& index_valid(NUM_PAGES, index)
                &&& old(krnl).pg_arr.spec_index(index).view().view().state == PageState::Free4k { allocator_ptr: Ghost(allocator_4k), state:
                    if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }
            },
            forall|cpu: CpuId| #![trigger cache_perms.spec_index(cpu)] #![trigger cache_perms.dom().contains(cpu)] cpu < NUM_CPUS ==> {
                &&& cache_perms.dom().contains(cpu)
                &&& cache_perms.spec_index(cpu).state() is WriteLock
                &&& cache_perms.spec_index(cpu).thread_id() == lctx.thread_id()
                &&& old(krnl).allc_4k_mp.spec_index(allocator_4k).cpu_caches.spec_index(cpu).view().locking_thread() is Write
                &&& cache_perms.spec_index(cpu).lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_4k).cpu_caches.spec_index(cpu).view().locking_thread()->Write_lock_id
                &&& typed_lock_map_contains_mode(lctx.allocator_cache_4k_lock_map(), (allocator_4k, cpu), TypedLockMode::Write)
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
            forall|index: PageIndex| #![trigger page_perms.spec_index(index)] #![trigger page_perms.dom().contains(index)] candidate.head <= index < candidate.head + 512 ==> {
                &&& page_perms.dom().contains(index)
                &&& page_perms.spec_index(index).state() is WriteLock
                &&& page_perms.spec_index(index).thread_id() == lctx.thread_id()
                &&& old(krnl).pg_arr.spec_index(index).view().locking_thread() is Write
            &&& page_perms.spec_index(index).lock_id() == old(krnl).pg_arr.spec_index(index).view().locking_thread()->Write_lock_id
                &&& typed_lock_map_contains_mode(lctx.page_lock_map(), index, TypedLockMode::Write)
            },
            forall|source: usize| #![trigger krnl.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source)] source <= NUM_CPUS ==>
                LinkedList::<PagePtr, 233>::values_sorted(krnl.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source).view()),
            offset <= 512,
            head == candidate.head,
            head + 512 <= NUM_PAGES,
            page_index_2m_valid(head),
            old(krnl).pg_arr.spec_index(head).view().is_init(),
            old(krnl).pg_arr.spec_index(head).view().view().inv(),
            old(krnl).allc_2m_mp.spec_index(allocator_2m).total_free_pages.view() < usize::MAX,
            old(krnl).thrd_mp.spec_index(thread).view().quota_2m < usize::MAX,
            head_ptr == spec_page_index2page_ptr(head),
            !old(krnl).allc_2m_mp.spec_index(allocator_2m).global_pool.view().view().contains(head_ptr),
            PAGE_SZ_4K == 4096,
            old(krnl).pg_arr.spec_index(head).view().view().addr == head_ptr,
            old(krnl).allc_4k_mp.spec_index(allocator_4k).wf(),
            old(krnl).allc_2m_mp.perms_wf(),
            old(krnl).allc_2m_mp.spec_index(allocator_2m).wf(),
            old(krnl).thrd_mp.perms_wf(),
            krnl.allc_4k_mp.unchanged_except(&old(krnl).allc_4k_mp, allocator_4k),
            krnl.allc_4k_mp.spec_index(allocator_4k).quota == old(krnl).allc_4k_mp.spec_index(allocator_4k).quota,
            krnl.allc_4k_mp.spec_index(allocator_4k).owning_container == old(krnl).allc_4k_mp.spec_index(allocator_4k).owning_container,
            forall|source: usize| #![trigger krnl.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source)]
                #![trigger krnl.allc_4k_mp.spec_index(allocator_4k).cpu_caches.spec_index(source)] source <= NUM_CPUS ==> {
                let original = old(krnl).allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source);
                let current = krnl.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source);
                &&& forall|key: usize| #![trigger current.map().dom().contains(key)] #![trigger original.map().dom().contains(key)] {
                    let value = original.map().spec_index(key);
                    let removed = Set::<PageIndex>::range(head, (head + offset) as usize).contains(spec_page_ptr2page_index(value))
                        && value == spec_page_index2page_ptr(spec_page_ptr2page_index(value))
                        && candidate.sources.view().spec_index(spec_page_ptr2page_index(value) as int - head as int) as usize == source;
                    &&& current.map().dom().contains(key) == (original.map().dom().contains(key) && !removed)
                    &&& current.map().dom().contains(key) ==> current.map().spec_index(key) == value
                }
                &&& forall|pointer: PagePtr| #![trigger current.view().contains(pointer)] #![trigger original.view().contains(pointer)]
                    current.view().contains(pointer) == (original.view().contains(pointer) && !(Set::<PageIndex>::range(head, (head + offset) as usize).contains((pointer / 4096) as usize)
                        && pointer == spec_page_index2page_ptr((pointer / 4096) as usize)
                        && candidate.sources.view().spec_index((pointer / 4096) as int - head as int) as usize == source))
            },
            krnl.allc_4k_mp.spec_index(allocator_4k).global_pool.locking_thread() == old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.locking_thread(),
            krnl.allc_4k_mp.spec_index(allocator_4k).global_pool.is_init() == old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.is_init(),
            krnl.allc_4k_mp.spec_index(allocator_4k).global_pool.view_rodata() == old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.view_rodata(),
            krnl.allc_4k_mp.spec_index(allocator_4k).global_pool.view_ghost() == old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.view_ghost(),
            krnl.allc_4k_mp.spec_index(allocator_4k).global_pool.control() == old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.control(),
            krnl.allc_4k_mp.spec_index(allocator_4k).global_pool.killer_info() == old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.killer_info(),
            krnl.allc_4k_mp.spec_index(allocator_4k).global_pool.view().line_pad == old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.view().line_pad,
            krnl.allc_4k_mp.spec_index(allocator_4k).global_pool.view().linked_list.minor == old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.view().linked_list.minor,
            krnl.allc_4k_mp.spec_index(allocator_4k).global_pool.view().linked_list.container_depth == old(krnl).allc_4k_mp.spec_index(allocator_4k).global_pool.view().linked_list.container_depth,
            forall|cpu: CpuId| #![trigger krnl.allc_4k_mp.spec_index(allocator_4k).cpu_caches.spec_index(cpu)] cpu < NUM_CPUS ==> {
                let old_cache = old(krnl).allc_4k_mp.spec_index(allocator_4k).cpu_caches.spec_index(cpu).view();
                let new_cache = krnl.allc_4k_mp.spec_index(allocator_4k).cpu_caches.spec_index(cpu).view();

                &&& new_cache.is_init() == old_cache.is_init()
                &&& new_cache.locking_thread() == old_cache.locking_thread()
                &&& new_cache.being_killed() == old_cache.being_killed()
                &&& new_cache.control() == old_cache.control()
                &&& new_cache.killer_info() == old_cache.killer_info()
                &&& new_cache.view_rodata() == old_cache.view_rodata()
                &&& new_cache.view_ghost() == old_cache.view_ghost()
                &&& new_cache.view().view().len() <= old_cache.view().view().len()
                &&& new_cache.view().line_pad == old_cache.view().line_pad
                &&& new_cache.view().linked_list.minor == old_cache.view().linked_list.minor
                &&& new_cache.view().linked_list.container_depth == old_cache.view().linked_list.container_depth

            },
            krnl.pg_arr.inv(),
            krnl.allc_4k_mp.perms_wf(),
            krnl.allc_4k_mp.spec_index(allocator_4k).wf(),
            typed_lock_maps_aligned(krnl, lctx),
            *krnl == (KernelK { pg_arr: krnl.pg_arr, allc_4k_mp: krnl.allc_4k_mp, ..*old(krnl) }),
            tail_perms.dom() == Set::<usize>::range(1, if offset == 0 { 1usize } else { offset }),
            head_node_perm.is_some() <==> offset > 0,
            offset > 0 ==> head_node_addr == old(krnl).pg_arr.spec_index(head).view().view().free_list_node_storage.addr(),
            head_node_perm.is_some() ==> head_node_perm.unwrap().is_init() && head_node_perm.unwrap().addr() == head_node_addr && head_node_perm.unwrap().value().view() == head_ptr,
            forall|i: usize| #![trigger tail_perms.spec_index(i)] 1 <= i < offset ==> {
                &&& old(krnl).pg_arr.spec_index((head + i) as usize).view().view().state is Free4k
                &&& old(krnl).pg_arr.spec_index((head + i) as usize).view().view().perm_4k.view().is_some()
                &&& tail_perms.spec_index(i) == old(krnl).pg_arr.spec_index((head + i) as usize).view().view().perm_4k.view().unwrap()
                &&& tail_perms.spec_index(i).is_init()
                &&& tail_perms.spec_index(i).addr() == (head + i) * PAGE_SZ_4K
            },
            forall|index: PageIndex| #![trigger krnl.pg_arr.spec_index(index)] #![trigger old(krnl).pg_arr.spec_index(index)]
                index_valid(NUM_PAGES, index) && !(head < index < head + offset) ==> krnl.pg_arr.spec_index(index) == old(krnl).pg_arr.spec_index(index),
            forall|index: PageIndex| #![trigger krnl.pg_arr.spec_index(index)] head < index < head + offset ==> {
                let old_page = old(krnl).pg_arr.spec_index(index).view().view();
                let new_page = krnl.pg_arr.spec_index(index).view().view();
                &&& new_page.perm_2m.view().is_none()
                &&& new_page.state is Merged2m
                &&& new_page.perm_4k.view().is_none()
                &&& new_page.free_list_node_storage.is_init()
                &&& new_page.free_list_node_storage.addr() == old_page.free_list_node_storage.addr()
                &&& new_page == (Page { state: new_page.state, perm_4k: new_page.perm_4k, free_list_node_storage: new_page.free_list_node_storage, ..old_page })
                &&& krnl.pg_arr.spec_index(index).view().locking_thread() == old(krnl).pg_arr.spec_index(index).view().locking_thread()
                &&& krnl.pg_arr.spec_index(index).view().is_init() == old(krnl).pg_arr.spec_index(index).view().is_init()
                &&& krnl.pg_arr.spec_index(index).view().view_rodata() == old(krnl).pg_arr.spec_index(index).view().view_rodata()
                &&& krnl.pg_arr.spec_index(index).view().view_ghost() == old(krnl).pg_arr.spec_index(index).view().view_ghost()
                &&& krnl.pg_arr.spec_index(index).view().control() == old(krnl).pg_arr.spec_index(index).view().control()
                &&& krnl.pg_arr.spec_index(index).view().killer_info() == old(krnl).pg_arr.spec_index(index).view().killer_info()
                &&& krnl.pg_arr.lock_id_by_index(index) == old(krnl).pg_arr.lock_id_by_index(index)
            },
            forall|index: PageIndex| #![trigger old(krnl).pg_arr.spec_index(index).view().view().owning_container] head <= index < head + offset ==>
                old(krnl).pg_arr.spec_index(index).view().view().owning_container == old(krnl).allc_4k_mp.spec_index(allocator_4k).owning_container,
            krnl.allc_4k_mp.spec_index(allocator_4k).total_free_pages.view() + offset == old(krnl).allc_4k_mp.spec_index(allocator_4k).total_free_pages.view(),
        decreases 512 - offset,
    {
        let index = head + offset;
        proof { page_array_wf_at(old(krnl).pg_arr, index); allocator_free_4k_pages_wf_at(old(krnl).allc_4k_mp, old(krnl).pg_arr, index); }
        let page = krnl.pg_arr.borrow_typed(index, Ghost(lctx.page_lock_map()), Tracked(lctx), Tracked(page_perms.tracked_borrow(index)));
        let node_addr = page.free_list_node_storage.addr();
        let source = *candidate.sources.get(offset);
        assert(krnl.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source as usize).dom().contains(node_addr)) by {
            old(krnl).allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source as usize).wf_implies_view_len_eq_len();
            krnl.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source as usize).wf_implies_view_len_eq_len();
            page_index_roundtrip();
        };
        assert(krnl.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source as usize).map().spec_index(node_addr) == spec_page_index2page_ptr(index)) by { page_index_roundtrip(); };
        let tracked source_perm = if (source as usize) < NUM_CPUS { cache_perms.tracked_borrow(source as usize) } else { pool4_perm };
        let ghost before_allocator = krnl.allc_4k_mp.spec_index(allocator_4k);
        let (_, Tracked(node_perm)) = krnl.allc_4k_mp.merge_2m_remove_source(allocator_4k, source, node_addr,
            Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()), Ghost(lctx.allocator_global_pool_4k_lock_map()),
            Tracked(lctx), Tracked(source_perm));
        proof {
            before_allocator.merge_2m_source_list(source as usize).wf_implies_view_len_eq_len();
            krnl.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source as usize).wf_implies_view_len_eq_len();
        }
        if offset == 0 {
            head_node_addr = node_addr;
            proof { head_node_perm = Some(node_perm); }
        } else {
            let page = krnl.pg_arr.borrow_mut_typed(index, Ghost(lctx.page_lock_map()), Tracked(lctx), Tracked(page_perms.tracked_borrow(index)));
            let Tracked(perm) = merge_2m_tail(page, Tracked(node_perm));
            proof { tail_perms.tracked_insert(offset, perm); }
        }
        offset += 1;
    }
    proof { page_array_wf_at(old(krnl).pg_arr, head); }
    let page = krnl.pg_arr.borrow_mut_typed(head, Ghost(lctx.page_lock_map()), Tracked(lctx), Tracked(page_perms.tracked_borrow(head)));
    merge_2m_head(page, Ghost(head), Ghost(allocator_2m), Ghost(old(krnl).pg_arr), Tracked(tail_perms));
    let tracked node_perm = head_node_perm.tracked_take();
    krnl.allc_2m_mp.push_global_pool_page_typed(allocator_2m, head_node_addr, Tracked(node_perm),
        Ghost(lctx.allocator_quota_2m_lock_map()), Ghost(lctx.allocator_cache_2m_lock_map()), Ghost(lctx.allocator_global_pool_2m_lock_map()), Tracked(lctx), Tracked(pool2_perm));
    let thread_value = krnl.thrd_mp.borrow_mut_typed(thread, Ghost(lctx.thread_lock_map()), Tracked(lctx), Tracked(thread_perm));
    merge_2m_exchange_thread_quotas(thread_value);
    proof {


        assert(merge_2m_commit_eof_transition_framing(*old(krnl), *krnl, thread, allocator_4k, allocator_2m, *candidate)) by { reveal(merge_2m_commit_eof_transition_framing); };
        merge_2m_commit_eof_implies_kernel_inv(*old(krnl), *krnl, thread, allocator_4k, allocator_2m, *candidate, lctx);
        merge_2m_commit_eof_implies_scanner_wf(*old(krnl), *krnl, thread, allocator_4k, allocator_2m, scanner);
        merge_2m_commit_eof_implies_complete_head_removed(*old(krnl), *krnl, thread, allocator_4k, allocator_2m, *candidate);
    }
}
}
