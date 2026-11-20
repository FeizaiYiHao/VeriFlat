#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::simple_pptr::*;
#[cfg(verus_keep_ghost)]
use vstd::{assert_sets_equal, assert_sets_equal_internal};
use crate::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_scan::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_metadata_eof::*;

verus! {
/// Merge-loop state of `merge_2m_commit` before offset `offset`, from the entry state `pre` to `cur`: only the page array and the
/// 4K allocator `allocator_4k` change; its source lists stay sorted and have lost exactly the region pages before `offset`, each from
/// the source the candidate names; its locks, caches and counters keep their state with `offset` fewer free pages; the region pages
/// strictly between the head and `offset` are Merged2m tails whose 4K permissions `tail_perms` holds; the head's free-list node
/// `head_node_perm`, at `head_node_addr`, is taken once `offset > 0`; every other page is unchanged.
#[verifier::opaque]
pub open spec fn merge_2m_commit_eol_loop_framing(pre: KernelK, cur: KernelK, allocator_4k: RwLockPageAllocatorPtr, candidate: Merge2mCandidate, offset: usize,
    head_node_addr: usize, head_node_perm: Option<PointsTo<Node<PagePtr>>>, tail_perms: Map<usize, PagePerm4k>) -> bool
{
    let head = candidate.head;
    let head_ptr = spec_page_index2page_ptr(head);
    &&& offset <= 512
    &&& forall|source: usize| #![trigger cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source)] source <= NUM_CPUS ==>
        LinkedList::<PagePtr, 233>::values_sorted(cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source).view())
    &&& cur.allc_4k_mp.unchanged_except(&pre.allc_4k_mp, allocator_4k)
    &&& cur.allc_4k_mp.spec_index(allocator_4k).quota == pre.allc_4k_mp.spec_index(allocator_4k).quota
    &&& cur.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.allc_4k_mp.spec_index(allocator_4k).owning_container
    &&& forall|source: usize| #![trigger cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source)]
        #![trigger cur.allc_4k_mp.spec_index(allocator_4k).cpu_caches.spec_index(source)] source <= NUM_CPUS ==> {
        let original = pre.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source);
        let current = cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source);
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
    }
    &&& cur.allc_4k_mp.spec_index(allocator_4k).global_pool.locking_thread() == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.locking_thread()
    &&& cur.allc_4k_mp.spec_index(allocator_4k).global_pool.is_init() == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.is_init()
    &&& cur.allc_4k_mp.spec_index(allocator_4k).global_pool.view_rodata() == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.view_rodata()
    &&& cur.allc_4k_mp.spec_index(allocator_4k).global_pool.view_ghost() == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.view_ghost()
    &&& cur.allc_4k_mp.spec_index(allocator_4k).global_pool.control() == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.control()
    &&& cur.allc_4k_mp.spec_index(allocator_4k).global_pool.killer_info() == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.killer_info()
    &&& cur.allc_4k_mp.spec_index(allocator_4k).global_pool.view().line_pad == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.view().line_pad
    &&& cur.allc_4k_mp.spec_index(allocator_4k).global_pool.view().linked_list.minor == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.view().linked_list.minor
    &&& cur.allc_4k_mp.spec_index(allocator_4k).global_pool.view().linked_list.container_depth == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.view().linked_list.container_depth
    &&& forall|cpu: CpuId| #![trigger cur.allc_4k_mp.spec_index(allocator_4k).cpu_caches.spec_index(cpu)] cpu < NUM_CPUS ==> {
        let old_cache = pre.allc_4k_mp.spec_index(allocator_4k).cpu_caches.spec_index(cpu).view();
        let new_cache = cur.allc_4k_mp.spec_index(allocator_4k).cpu_caches.spec_index(cpu).view();
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
    }
    &&& cur == (KernelK { pg_arr: cur.pg_arr, allc_4k_mp: cur.allc_4k_mp, ..pre })
    &&& tail_perms.dom() == Set::<usize>::range(1, if offset == 0 { 1usize } else { offset })
    &&& head_node_perm.is_some() <==> offset > 0
    &&& offset > 0 ==> head_node_addr == pre.pg_arr.spec_index(head).view().view().free_list_node_storage.addr()
    &&& head_node_perm.is_some() ==> head_node_perm.unwrap().is_init() && head_node_perm.unwrap().addr() == head_node_addr && head_node_perm.unwrap().value().view() == head_ptr
    &&& forall|i: usize| #![trigger tail_perms.spec_index(i)] 1 <= i < offset ==> {
        &&& tail_perms.spec_index(i) == pre.pg_arr.spec_index((head + i) as usize).view().view().perm_4k.view().unwrap()
        &&& tail_perms.spec_index(i).is_init()
        &&& tail_perms.spec_index(i).addr() == (head + i) * PAGE_SZ_4K
    }
    &&& forall|index: PageIndex| #![trigger cur.pg_arr.spec_index(index)] #![trigger pre.pg_arr.spec_index(index)]
        index_valid(NUM_PAGES, index) && !(head < index < head + offset) ==> cur.pg_arr.spec_index(index) == pre.pg_arr.spec_index(index)
    &&& forall|index: PageIndex| #![trigger cur.pg_arr.spec_index(index)] head < index < head + offset ==> {
        let old_page = pre.pg_arr.spec_index(index).view().view();
        let new_page = cur.pg_arr.spec_index(index).view().view();
        &&& new_page.perm_2m.view().is_none()
        &&& new_page.state is Merged2m
        &&& new_page.perm_4k.view().is_none()
        &&& new_page.free_list_node_storage.is_init()
        &&& new_page.free_list_node_storage.addr() == old_page.free_list_node_storage.addr()
        &&& new_page == (Page { state: new_page.state, perm_4k: new_page.perm_4k, free_list_node_storage: new_page.free_list_node_storage, ..old_page })
        &&& cur.pg_arr.spec_index(index).view().locking_thread() == pre.pg_arr.spec_index(index).view().locking_thread()
        &&& cur.pg_arr.spec_index(index).view().is_init() == pre.pg_arr.spec_index(index).view().is_init()
        &&& cur.pg_arr.spec_index(index).view().view_rodata() == pre.pg_arr.spec_index(index).view().view_rodata()
        &&& cur.pg_arr.spec_index(index).view().view_ghost() == pre.pg_arr.spec_index(index).view().view_ghost()
        &&& cur.pg_arr.spec_index(index).view().control() == pre.pg_arr.spec_index(index).view().control()
        &&& cur.pg_arr.spec_index(index).view().killer_info() == pre.pg_arr.spec_index(index).view().killer_info()
        &&& cur.pg_arr.lock_id_by_index(index) == pre.pg_arr.lock_id_by_index(index)
    }
    &&& cur.allc_4k_mp.spec_index(allocator_4k).total_free_pages.view() + offset == pre.allc_4k_mp.spec_index(allocator_4k).total_free_pages.view()
}

/// The loop state before `offset` gives what removing the region page `candidate.head + offset` from its source list needs at `cur`:
/// the page is unchanged, and its free-list node is in the source list the candidate names, holding the page's pointer.
pub proof fn merge_2m_commit_eol_iteration_pre(pre: KernelK, cur: KernelK, allocator_4k: RwLockPageAllocatorPtr, candidate: Merge2mCandidate, offset: usize,
    head_node_addr: usize, head_node_perm: Option<PointsTo<Node<PagePtr>>>, tail_perms: Map<usize, PagePerm4k>)
    requires
        pre.inv(),
        pre.allc_4k_mp.dom().contains(allocator_4k),
        candidate.wf(),
        candidate.sources.len() == 512,
        page_index_2m_valid(candidate.head),
        forall|index: PageIndex| #![trigger pre.pg_arr.spec_index(index)] candidate.head <= index < candidate.head + 512 ==> {
            let source = candidate.sources.view().spec_index(index as int - candidate.head as int) as usize;
            &&& index_valid(NUM_PAGES, index)
            &&& pre.pg_arr.spec_index(index).view().view().state == PageState::Free4k { allocator_ptr: Ghost(allocator_4k), state:
                if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }
        },
        cur.allc_4k_mp.spec_index(allocator_4k).wf(),
        merge_2m_commit_eol_loop_framing(pre, cur, allocator_4k, candidate, offset, head_node_addr, head_node_perm, tail_perms),
        offset < 512,
    ensures
        ({
            let index = (candidate.head + offset) as usize;
            let source = candidate.sources.view().spec_index(offset as int) as usize;
            let node_addr = pre.pg_arr.spec_index(index).view().view().free_list_node_storage.addr();
            &&& index_valid(NUM_PAGES, index)
            &&& cur.pg_arr.spec_index(index) == pre.pg_arr.spec_index(index)
            &&& cur.allc_4k_mp.dom().contains(allocator_4k)
            &&& cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source).dom().contains(node_addr)
            &&& cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source).map().spec_index(node_addr) == spec_page_index2page_ptr(index)
            &&& source < NUM_CPUS ==> cur.allc_4k_mp.spec_index(allocator_4k).cpu_caches.spec_index(source).view().locking_thread()
                == pre.allc_4k_mp.spec_index(allocator_4k).cpu_caches.spec_index(source).view().locking_thread()
            &&& cur.allc_4k_mp.spec_index(allocator_4k).global_pool.locking_thread() == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.locking_thread()
        }),
{
    let index = (candidate.head + offset) as usize;
    let source = candidate.sources.view().spec_index(offset as int) as usize;
    reveal(merge_2m_commit_eol_loop_framing);
    page_array_wf_at(pre.pg_arr, index);
    allocator_perms_wf_map(pre.allc_4k_mp); allocator_perms_wf_at(pre.allc_4k_mp, allocator_4k);
    allocator_free_4k_pages_wf_at(pre.allc_4k_mp, pre.pg_arr, index);
    pre.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source).wf_implies_view_len_eq_len();
    cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source).wf_implies_view_len_eq_len();
    page_index_roundtrip();
}

/// EOL closure of the merge loop: after the region page `candidate.head + offset` left source list `source` from `cur` to `mid`, the
/// source lists of `mid` are sorted and have lost exactly the region pages up to `offset`, with one free page fewer.
pub proof fn merge_2m_commit_eol_step_source_lists(pre: KernelK, cur: KernelK, mid: KernelK, allocator_4k: RwLockPageAllocatorPtr, candidate: Merge2mCandidate,
    offset: usize, source: u8, node_perm: PointsTo<Node<PagePtr>>, head_node_addr: usize, head_node_perm: Option<PointsTo<Node<PagePtr>>>, tail_perms: Map<usize, PagePerm4k>)
    requires
        pre.inv(),
        pre.allc_4k_mp.dom().contains(allocator_4k),
        candidate.wf(),
        candidate.sources.len() == 512,
        page_index_2m_valid(candidate.head),
        forall|index: PageIndex| #![trigger pre.pg_arr.spec_index(index)] candidate.head <= index < candidate.head + 512 ==> {
            let source = candidate.sources.view().spec_index(index as int - candidate.head as int) as usize;
            &&& index_valid(NUM_PAGES, index)
            &&& pre.pg_arr.spec_index(index).view().view().state == PageState::Free4k { allocator_ptr: Ghost(allocator_4k), state:
                if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }
        },
        merge_2m_commit_eol_loop_framing(pre, cur, allocator_4k, candidate, offset, head_node_addr, head_node_perm, tail_perms),
        offset < 512,
        source == candidate.sources.view().spec_index(offset as int),
        cur.pg_arr.spec_index((candidate.head + offset) as usize) == pre.pg_arr.spec_index((candidate.head + offset) as usize),
        mid == (KernelK { allc_4k_mp: mid.allc_4k_mp, ..cur }),
        mid.allc_4k_mp.unchanged_except(&cur.allc_4k_mp, allocator_4k),
        PageAllocatorUnLockedMap::<ALLOCATOR_SIZE_4K>::merge_2m_remove_source_eof_transition_framing(cur.allc_4k_mp, mid.allc_4k_mp, allocator_4k, source,
            pre.pg_arr.spec_index((candidate.head + offset) as usize).view().view().free_list_node_storage.addr(), node_perm),
        forall|other: usize| #![trigger mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other)] other <= NUM_CPUS
            && LinkedList::<PagePtr, 233>::values_sorted(cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).view()) ==>
                LinkedList::<PagePtr, 233>::values_sorted(mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).view()),
        cur.allc_4k_mp.spec_index(allocator_4k).wf(),
        mid.allc_4k_mp.spec_index(allocator_4k).wf(),
        forall|other: usize, key: usize| #![trigger mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).map().dom().contains(key)]
            #![trigger cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).map().dom().contains(key)] other <= NUM_CPUS ==> {
            let before = cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).map();
            let after = mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).map();
            &&& after.dom().contains(key) == (before.dom().contains(key) && (other != source as usize || before.spec_index(key) != node_perm.value().view()))
            &&& after.dom().contains(key) ==> after.spec_index(key) == before.spec_index(key)
        },
        forall|other: usize, value: PagePtr| #![trigger mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).view().contains(value)]
            #![trigger cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).view().contains(value)] other <= NUM_CPUS ==>
            mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).view().contains(value)
                == (cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).view().contains(value) && (other != source as usize || value != node_perm.value().view())),
        forall|other: usize| #![trigger mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other)] other <= NUM_CPUS && other != source as usize ==>
            mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other) == cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other),
    ensures
        forall|source: usize| #![trigger mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source)] source <= NUM_CPUS ==>
            LinkedList::<PagePtr, 233>::values_sorted(mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source).view()),
        forall|source: usize| #![trigger mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source)]
            #![trigger mid.allc_4k_mp.spec_index(allocator_4k).cpu_caches.spec_index(source)] source <= NUM_CPUS ==> {
            let original = pre.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source);
            let current = mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source);
            &&& forall|key: usize| #![trigger current.map().dom().contains(key)] #![trigger original.map().dom().contains(key)] {
                let value = original.map().spec_index(key);
                let removed = Set::<PageIndex>::range(candidate.head, (candidate.head + offset + 1) as usize).contains(spec_page_ptr2page_index(value))
                    && value == spec_page_index2page_ptr(spec_page_ptr2page_index(value))
                    && candidate.sources.view().spec_index(spec_page_ptr2page_index(value) as int - candidate.head as int) as usize == source;
                &&& current.map().dom().contains(key) == (original.map().dom().contains(key) && !removed)
                &&& current.map().dom().contains(key) ==> current.map().spec_index(key) == value
            }
            &&& forall|pointer: PagePtr| #![trigger current.view().contains(pointer)] #![trigger original.view().contains(pointer)]
                current.view().contains(pointer) == (original.view().contains(pointer) && !(Set::<PageIndex>::range(candidate.head, (candidate.head + offset + 1) as usize).contains((pointer / 4096) as usize)
                    && pointer == spec_page_index2page_ptr((pointer / 4096) as usize)
                    && candidate.sources.view().spec_index((pointer / 4096) as int - candidate.head as int) as usize == source))
        },
        mid.allc_4k_mp.spec_index(allocator_4k).total_free_pages.view() + (offset + 1) as usize == pre.allc_4k_mp.spec_index(allocator_4k).total_free_pages.view(),
{
    let index = (candidate.head + offset) as usize;
    reveal(merge_2m_commit_eol_loop_framing);
    page_array_wf_at(pre.pg_arr, index);
    allocator_perms_wf_map(pre.allc_4k_mp); allocator_perms_wf_at(pre.allc_4k_mp, allocator_4k);
    allocator_free_4k_pages_wf_at(pre.allc_4k_mp, pre.pg_arr, index);
    page_index_roundtrip();
}

/// EOL closure of the merge loop: removing the region page `candidate.head + offset` from `cur` to `mid` keeps every other allocator,
/// the global pool's and the cpu caches' lock state and list metadata.
pub proof fn merge_2m_commit_eol_step_caches(pre: KernelK, cur: KernelK, mid: KernelK, allocator_4k: RwLockPageAllocatorPtr, candidate: Merge2mCandidate,
    offset: usize, source: u8, node_perm: PointsTo<Node<PagePtr>>, head_node_addr: usize, head_node_perm: Option<PointsTo<Node<PagePtr>>>, tail_perms: Map<usize, PagePerm4k>)
    requires
        pre.inv(),
        pre.allc_4k_mp.dom().contains(allocator_4k),
        candidate.wf(),
        candidate.sources.len() == 512,
        page_index_2m_valid(candidate.head),
        merge_2m_commit_eol_loop_framing(pre, cur, allocator_4k, candidate, offset, head_node_addr, head_node_perm, tail_perms),
        offset < 512,
        source == candidate.sources.view().spec_index(offset as int),
        mid == (KernelK { allc_4k_mp: mid.allc_4k_mp, ..cur }),
        mid.allc_4k_mp.unchanged_except(&cur.allc_4k_mp, allocator_4k),
        PageAllocatorUnLockedMap::<ALLOCATOR_SIZE_4K>::merge_2m_remove_source_eof_transition_framing(cur.allc_4k_mp, mid.allc_4k_mp, allocator_4k, source,
            pre.pg_arr.spec_index((candidate.head + offset) as usize).view().view().free_list_node_storage.addr(), node_perm),
        forall|other: usize| #![trigger mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other)] other <= NUM_CPUS
            && LinkedList::<PagePtr, 233>::values_sorted(cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).view()) ==>
                LinkedList::<PagePtr, 233>::values_sorted(mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).view()),
        cur.allc_4k_mp.spec_index(allocator_4k).wf(),
        mid.allc_4k_mp.spec_index(allocator_4k).wf(),
        forall|other: usize, key: usize| #![trigger mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).map().dom().contains(key)]
            #![trigger cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).map().dom().contains(key)] other <= NUM_CPUS ==> {
            let before = cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).map();
            let after = mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).map();
            &&& after.dom().contains(key) == (before.dom().contains(key) && (other != source as usize || before.spec_index(key) != node_perm.value().view()))
            &&& after.dom().contains(key) ==> after.spec_index(key) == before.spec_index(key)
        },
        forall|other: usize, value: PagePtr| #![trigger mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).view().contains(value)]
            #![trigger cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).view().contains(value)] other <= NUM_CPUS ==>
            mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).view().contains(value)
                == (cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).view().contains(value) && (other != source as usize || value != node_perm.value().view())),
        forall|other: usize| #![trigger mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other)] other <= NUM_CPUS && other != source as usize ==>
            mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other) == cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other),
    ensures
        mid.allc_4k_mp.unchanged_except(&pre.allc_4k_mp, allocator_4k),
        mid.allc_4k_mp.spec_index(allocator_4k).quota == pre.allc_4k_mp.spec_index(allocator_4k).quota,
        mid.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.allc_4k_mp.spec_index(allocator_4k).owning_container,
        mid.allc_4k_mp.spec_index(allocator_4k).global_pool.locking_thread() == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.locking_thread(),
        mid.allc_4k_mp.spec_index(allocator_4k).global_pool.is_init() == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.is_init(),
        mid.allc_4k_mp.spec_index(allocator_4k).global_pool.view_rodata() == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.view_rodata(),
        mid.allc_4k_mp.spec_index(allocator_4k).global_pool.view_ghost() == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.view_ghost(),
        mid.allc_4k_mp.spec_index(allocator_4k).global_pool.control() == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.control(),
        mid.allc_4k_mp.spec_index(allocator_4k).global_pool.killer_info() == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.killer_info(),
        mid.allc_4k_mp.spec_index(allocator_4k).global_pool.view().line_pad == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.view().line_pad,
        mid.allc_4k_mp.spec_index(allocator_4k).global_pool.view().linked_list.minor == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.view().linked_list.minor,
        mid.allc_4k_mp.spec_index(allocator_4k).global_pool.view().linked_list.container_depth == pre.allc_4k_mp.spec_index(allocator_4k).global_pool.view().linked_list.container_depth,
        forall|cpu: CpuId| #![trigger mid.allc_4k_mp.spec_index(allocator_4k).cpu_caches.spec_index(cpu)] cpu < NUM_CPUS ==> {
            let old_cache = pre.allc_4k_mp.spec_index(allocator_4k).cpu_caches.spec_index(cpu).view();
            let new_cache = mid.allc_4k_mp.spec_index(allocator_4k).cpu_caches.spec_index(cpu).view();
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
{
    reveal(merge_2m_commit_eol_loop_framing);
    cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source as usize).wf_implies_view_len_eq_len();
    mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source as usize).wf_implies_view_len_eq_len();
}

/// EOL closure of the merge loop: past the head, the region page `candidate.head + offset` became a Merged2m tail from `mid` to `post`
/// whose 4K permission `post_tail_perms` gained; at the head, its free-list node was taken.
pub proof fn merge_2m_commit_eol_step_pages(pre: KernelK, cur: KernelK, mid: KernelK, post: KernelK, allocator_4k: RwLockPageAllocatorPtr, candidate: Merge2mCandidate,
    offset: usize, source: u8, node_perm: PointsTo<Node<PagePtr>>, head_node_addr: usize, head_node_perm: Option<PointsTo<Node<PagePtr>>>, tail_perms: Map<usize, PagePerm4k>,
    post_head_node_addr: usize, post_head_node_perm: Option<PointsTo<Node<PagePtr>>>, post_tail_perms: Map<usize, PagePerm4k>)
    requires
        pre.inv(),
        pre.allc_4k_mp.dom().contains(allocator_4k),
        candidate.wf(),
        candidate.sources.len() == 512,
        page_index_2m_valid(candidate.head),
        forall|index: PageIndex| #![trigger pre.pg_arr.spec_index(index)] candidate.head <= index < candidate.head + 512 ==> {
            let source = candidate.sources.view().spec_index(index as int - candidate.head as int) as usize;
            &&& index_valid(NUM_PAGES, index)
            &&& pre.pg_arr.spec_index(index).view().view().state == PageState::Free4k { allocator_ptr: Ghost(allocator_4k), state:
                if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }
        },
        merge_2m_commit_eol_loop_framing(pre, cur, allocator_4k, candidate, offset, head_node_addr, head_node_perm, tail_perms),
        offset < 512,
        source == candidate.sources.view().spec_index(offset as int),
        cur.pg_arr.spec_index((candidate.head + offset) as usize) == pre.pg_arr.spec_index((candidate.head + offset) as usize),
        mid == (KernelK { allc_4k_mp: mid.allc_4k_mp, ..cur }),
        mid.allc_4k_mp.unchanged_except(&cur.allc_4k_mp, allocator_4k),
        PageAllocatorUnLockedMap::<ALLOCATOR_SIZE_4K>::merge_2m_remove_source_eof_transition_framing(cur.allc_4k_mp, mid.allc_4k_mp, allocator_4k, source,
            pre.pg_arr.spec_index((candidate.head + offset) as usize).view().view().free_list_node_storage.addr(), node_perm),
        forall|other: usize| #![trigger mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other)] other <= NUM_CPUS
            && LinkedList::<PagePtr, 233>::values_sorted(cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).view()) ==>
                LinkedList::<PagePtr, 233>::values_sorted(mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).view()),
        cur.allc_4k_mp.spec_index(allocator_4k).wf(),
        mid.allc_4k_mp.spec_index(allocator_4k).wf(),
        forall|other: usize, key: usize| #![trigger mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).map().dom().contains(key)]
            #![trigger cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).map().dom().contains(key)] other <= NUM_CPUS ==> {
            let before = cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).map();
            let after = mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).map();
            &&& after.dom().contains(key) == (before.dom().contains(key) && (other != source as usize || before.spec_index(key) != node_perm.value().view()))
            &&& after.dom().contains(key) ==> after.spec_index(key) == before.spec_index(key)
        },
        forall|other: usize, value: PagePtr| #![trigger mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).view().contains(value)]
            #![trigger cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).view().contains(value)] other <= NUM_CPUS ==>
            mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).view().contains(value)
                == (cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).view().contains(value) && (other != source as usize || value != node_perm.value().view())),
        forall|other: usize| #![trigger mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other)] other <= NUM_CPUS && other != source as usize ==>
            mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other) == cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other),
        post == (KernelK { pg_arr: post.pg_arr, ..mid }),
        offset == 0 ==> post.pg_arr == mid.pg_arr && post_head_node_addr == node_perm.addr() && post_head_node_perm == Some(node_perm) && post_tail_perms == tail_perms,
        offset > 0 ==> {
            let index = (candidate.head + offset) as usize;
            let mid_cell = mid.pg_arr.spec_index(index).view();
            let post_cell = post.pg_arr.spec_index(index).view();
            &&& post.pg_arr.entries_unchanged_except(&mid.pg_arr, index)
            &&& post_cell.is_init() == mid_cell.is_init()
            &&& post_cell.locking_thread() == mid_cell.locking_thread()
            &&& post_cell.view_rodata() == mid_cell.view_rodata()
            &&& post_cell.view_ghost() == mid_cell.view_ghost()
            &&& post_cell.control() == mid_cell.control()
            &&& post_cell.killer_info() == mid_cell.killer_info()
            &&& post.pg_arr.lock_id_by_index(index) == mid.pg_arr.lock_id_by_index(index)
            &&& merge_2m_tail_eof_transition_framing(mid_cell.view(), post_cell.view())
            &&& post_tail_perms == tail_perms.insert(offset, mid_cell.view().perm_4k.view().unwrap())
            &&& post_tail_perms.spec_index(offset).is_init()
            &&& post_tail_perms.spec_index(offset).addr() == (candidate.head + offset) * PAGE_SZ_4K
            &&& post_cell.view().perm_2m.view().is_none()
            &&& post_head_node_addr == head_node_addr
            &&& post_head_node_perm == head_node_perm
        },
    ensures
        (offset + 1) as usize <= 512,
        post == (KernelK { pg_arr: post.pg_arr, allc_4k_mp: post.allc_4k_mp, ..pre }),
        post_tail_perms.dom() == Set::<usize>::range(1, if (offset + 1) as usize == 0 { 1usize } else { (offset + 1) as usize }),
        post_head_node_perm.is_some() <==> (offset + 1) as usize > 0,
        (offset + 1) as usize > 0 ==> post_head_node_addr == pre.pg_arr.spec_index(candidate.head).view().view().free_list_node_storage.addr(),
        post_head_node_perm.is_some() ==> post_head_node_perm.unwrap().is_init() && post_head_node_perm.unwrap().addr() == post_head_node_addr && post_head_node_perm.unwrap().value().view() == spec_page_index2page_ptr(candidate.head),
        forall|i: usize| #![trigger post_tail_perms.spec_index(i)] 1 <= i < (offset + 1) as usize ==> {
            &&& post_tail_perms.spec_index(i) == pre.pg_arr.spec_index((candidate.head + i) as usize).view().view().perm_4k.view().unwrap()
            &&& post_tail_perms.spec_index(i).is_init()
            &&& post_tail_perms.spec_index(i).addr() == (candidate.head + i) * PAGE_SZ_4K
        },
        forall|index: PageIndex| #![trigger post.pg_arr.spec_index(index)] #![trigger pre.pg_arr.spec_index(index)]
            index_valid(NUM_PAGES, index) && !(candidate.head < index < candidate.head + offset + 1) ==> post.pg_arr.spec_index(index) == pre.pg_arr.spec_index(index),
        forall|index: PageIndex| #![trigger post.pg_arr.spec_index(index)] candidate.head < index < candidate.head + offset + 1 ==> {
            let old_page = pre.pg_arr.spec_index(index).view().view();
            let new_page = post.pg_arr.spec_index(index).view().view();
            &&& new_page.perm_2m.view().is_none()
            &&& new_page.state is Merged2m
            &&& new_page.perm_4k.view().is_none()
            &&& new_page.free_list_node_storage.is_init()
            &&& new_page.free_list_node_storage.addr() == old_page.free_list_node_storage.addr()
            &&& new_page == (Page { state: new_page.state, perm_4k: new_page.perm_4k, free_list_node_storage: new_page.free_list_node_storage, ..old_page })
            &&& post.pg_arr.spec_index(index).view().locking_thread() == pre.pg_arr.spec_index(index).view().locking_thread()
            &&& post.pg_arr.spec_index(index).view().is_init() == pre.pg_arr.spec_index(index).view().is_init()
            &&& post.pg_arr.spec_index(index).view().view_rodata() == pre.pg_arr.spec_index(index).view().view_rodata()
            &&& post.pg_arr.spec_index(index).view().view_ghost() == pre.pg_arr.spec_index(index).view().view_ghost()
            &&& post.pg_arr.spec_index(index).view().control() == pre.pg_arr.spec_index(index).view().control()
            &&& post.pg_arr.spec_index(index).view().killer_info() == pre.pg_arr.spec_index(index).view().killer_info()
            &&& post.pg_arr.lock_id_by_index(index) == pre.pg_arr.lock_id_by_index(index)
        },
{
    let index = (candidate.head + offset) as usize;
    reveal(merge_2m_commit_eol_loop_framing);
    assert(pre.pg_arr.spec_index(index).view().view().perm_4k.view().is_some()) by { page_array_wf_at(pre.pg_arr, index); };
    assert_sets_equal!(post_tail_perms.dom(), Set::<usize>::range(1, (offset + 1) as usize));
    allocator_perms_wf_map(pre.allc_4k_mp); allocator_perms_wf_at(pre.allc_4k_mp, allocator_4k);
    allocator_free_4k_pages_wf_at(pre.allc_4k_mp, pre.pg_arr, index);
}

/// The loop state before `offset + 1` after the region page `candidate.head + offset` left source list `source` from `cur` to `mid`
/// and, past the head, became a Merged2m tail from `mid` to `post` whose 4K permission `tail_perms` gained.
pub proof fn merge_2m_commit_eol_step(pre: KernelK, cur: KernelK, mid: KernelK, post: KernelK, allocator_4k: RwLockPageAllocatorPtr, candidate: Merge2mCandidate,
    offset: usize, source: u8, node_perm: PointsTo<Node<PagePtr>>, head_node_addr: usize, head_node_perm: Option<PointsTo<Node<PagePtr>>>, tail_perms: Map<usize, PagePerm4k>,
    post_head_node_addr: usize, post_head_node_perm: Option<PointsTo<Node<PagePtr>>>, post_tail_perms: Map<usize, PagePerm4k>)
    requires
        pre.inv(),
        pre.allc_4k_mp.dom().contains(allocator_4k),
        candidate.wf(),
        candidate.sources.len() == 512,
        page_index_2m_valid(candidate.head),
        forall|index: PageIndex| #![trigger pre.pg_arr.spec_index(index)] candidate.head <= index < candidate.head + 512 ==> {
            let source = candidate.sources.view().spec_index(index as int - candidate.head as int) as usize;
            &&& index_valid(NUM_PAGES, index)
            &&& pre.pg_arr.spec_index(index).view().view().state == PageState::Free4k { allocator_ptr: Ghost(allocator_4k), state:
                if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }
        },
        merge_2m_commit_eol_loop_framing(pre, cur, allocator_4k, candidate, offset, head_node_addr, head_node_perm, tail_perms),
        offset < 512,
        source == candidate.sources.view().spec_index(offset as int),
        cur.pg_arr.spec_index((candidate.head + offset) as usize) == pre.pg_arr.spec_index((candidate.head + offset) as usize),
        mid == (KernelK { allc_4k_mp: mid.allc_4k_mp, ..cur }),
        mid.allc_4k_mp.unchanged_except(&cur.allc_4k_mp, allocator_4k),
        PageAllocatorUnLockedMap::<ALLOCATOR_SIZE_4K>::merge_2m_remove_source_eof_transition_framing(cur.allc_4k_mp, mid.allc_4k_mp, allocator_4k, source,
            pre.pg_arr.spec_index((candidate.head + offset) as usize).view().view().free_list_node_storage.addr(), node_perm),
        forall|other: usize| #![trigger mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other)] other <= NUM_CPUS
            && LinkedList::<PagePtr, 233>::values_sorted(cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).view()) ==>
                LinkedList::<PagePtr, 233>::values_sorted(mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).view()),
        cur.allc_4k_mp.spec_index(allocator_4k).wf(),
        mid.allc_4k_mp.spec_index(allocator_4k).wf(),
        forall|other: usize, key: usize| #![trigger mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).map().dom().contains(key)]
            #![trigger cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).map().dom().contains(key)] other <= NUM_CPUS ==> {
            let before = cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).map();
            let after = mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).map();
            &&& after.dom().contains(key) == (before.dom().contains(key) && (other != source as usize || before.spec_index(key) != node_perm.value().view()))
            &&& after.dom().contains(key) ==> after.spec_index(key) == before.spec_index(key)
        },
        forall|other: usize, value: PagePtr| #![trigger mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).view().contains(value)]
            #![trigger cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).view().contains(value)] other <= NUM_CPUS ==>
            mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).view().contains(value)
                == (cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other).view().contains(value) && (other != source as usize || value != node_perm.value().view())),
        forall|other: usize| #![trigger mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other)] other <= NUM_CPUS && other != source as usize ==>
            mid.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other) == cur.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(other),
        post == (KernelK { pg_arr: post.pg_arr, ..mid }),
        offset == 0 ==> post.pg_arr == mid.pg_arr && post_head_node_addr == node_perm.addr() && post_head_node_perm == Some(node_perm) && post_tail_perms == tail_perms,
        offset > 0 ==> {
            let index = (candidate.head + offset) as usize;
            let mid_cell = mid.pg_arr.spec_index(index).view();
            let post_cell = post.pg_arr.spec_index(index).view();
            &&& post.pg_arr.entries_unchanged_except(&mid.pg_arr, index)
            &&& post_cell.is_init() == mid_cell.is_init()
            &&& post_cell.locking_thread() == mid_cell.locking_thread()
            &&& post_cell.view_rodata() == mid_cell.view_rodata()
            &&& post_cell.view_ghost() == mid_cell.view_ghost()
            &&& post_cell.control() == mid_cell.control()
            &&& post_cell.killer_info() == mid_cell.killer_info()
            &&& post.pg_arr.lock_id_by_index(index) == mid.pg_arr.lock_id_by_index(index)
            &&& merge_2m_tail_eof_transition_framing(mid_cell.view(), post_cell.view())
            &&& post_tail_perms == tail_perms.insert(offset, mid_cell.view().perm_4k.view().unwrap())
            &&& post_tail_perms.spec_index(offset).is_init()
            &&& post_tail_perms.spec_index(offset).addr() == (candidate.head + offset) * PAGE_SZ_4K
            &&& post_cell.view().perm_2m.view().is_none()
            &&& post_head_node_addr == head_node_addr
            &&& post_head_node_perm == head_node_perm
        },
    ensures
        merge_2m_commit_eol_loop_framing(pre, post, allocator_4k, candidate, (offset + 1) as usize, post_head_node_addr, post_head_node_perm, post_tail_perms),
{
    reveal(merge_2m_commit_eol_loop_framing);
    merge_2m_commit_eol_step_source_lists(pre, cur, mid, allocator_4k, candidate, offset, source, node_perm, head_node_addr, head_node_perm, tail_perms);
    merge_2m_commit_eol_step_caches(pre, cur, mid, allocator_4k, candidate, offset, source, node_perm, head_node_addr, head_node_perm, tail_perms);
    merge_2m_commit_eol_step_pages(pre, cur, mid, post, allocator_4k, candidate, offset, source, node_perm, head_node_addr, head_node_perm, tail_perms,
        post_head_node_addr, post_head_node_perm, post_tail_perms);
}

/// The loop state after the last region page gives what merging the head needs: the head page is unchanged, `tail_perms` holds the
/// 4K permissions of the 511 tails, and the head's free-list node is taken.
pub proof fn merge_2m_commit_eol_exit(pre: KernelK, cur: KernelK, allocator_4k: RwLockPageAllocatorPtr, candidate: Merge2mCandidate,
    head_node_addr: usize, head_node_perm: Option<PointsTo<Node<PagePtr>>>, tail_perms: Map<usize, PagePerm4k>)
    requires
        pre.inv(),
        page_index_2m_valid(candidate.head),
        forall|index: PageIndex| #![trigger pre.pg_arr.spec_index(index)] candidate.head <= index < candidate.head + 512 ==> {
            let source = candidate.sources.view().spec_index(index as int - candidate.head as int) as usize;
            &&& index_valid(NUM_PAGES, index)
            &&& pre.pg_arr.spec_index(index).view().view().state == PageState::Free4k { allocator_ptr: Ghost(allocator_4k), state:
                if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }
        },
        merge_2m_commit_eol_loop_framing(pre, cur, allocator_4k, candidate, 512, head_node_addr, head_node_perm, tail_perms),
    ensures
        cur.pg_arr.spec_index(candidate.head) == pre.pg_arr.spec_index(candidate.head),
        cur == (KernelK { pg_arr: cur.pg_arr, allc_4k_mp: cur.allc_4k_mp, ..pre }),
        tail_perms.dom() == Set::<usize>::range(1, 512),
        forall|i: usize| #![trigger tail_perms.spec_index(i)] 1 <= i < 512 ==> {
            &&& pre.pg_arr.spec_index((candidate.head + i) as usize).view().view().state is Free4k
            &&& pre.pg_arr.spec_index((candidate.head + i) as usize).view().view().perm_4k.view() == Some(tail_perms.spec_index(i))
            &&& tail_perms.spec_index(i).is_init()
            &&& tail_perms.spec_index(i).addr() == (candidate.head + i) * PAGE_SZ_4K
        },
        head_node_perm.is_some(),
        head_node_perm.unwrap().is_init(),
        head_node_perm.unwrap().addr() == head_node_addr,
        head_node_perm.unwrap().value().view() == spec_page_index2page_ptr(candidate.head),
        head_node_addr == pre.pg_arr.spec_index(candidate.head).view().view().free_list_node_storage.addr(),
{ reveal(merge_2m_commit_eol_loop_framing); reveal(page_array_wf); }
}
