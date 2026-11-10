#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::{assert_sets_equal, assert_sets_equal_internal};
use crate::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_scan::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_commit_spec::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_scanner_spec::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_set_folds::*;

verus! {
pub broadcast proof fn merge_2m_commit_eof_implies_region_page_left_source(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, candidate: Merge2mCandidate, source: usize, pointer: PagePtr)
    requires
        pre.inv(),
        pre.allc_4k_mp.dom().contains(allocator_4k),
        candidate.wf(),
        candidate.sources.len() == 512,
        forall|index: PageIndex| #![trigger pre.pg_arr.spec_index(index)] candidate.head <= index < candidate.head + 512 ==> {
            let source = candidate.sources.view().spec_index(index as int - candidate.head as int) as usize;
            &&& index_valid(NUM_PAGES, index)
            &&& pre.pg_arr.spec_index(index).view().view().state == PageState::Free4k { allocator_ptr: Ghost(allocator_4k), state:
                if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }
        },
        merge_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, candidate),
        source <= NUM_CPUS,
        Set::<PageIndex>::range(candidate.head, (candidate.head + 512) as usize).contains(spec_page_ptr2page_index(pointer)),
    ensures
        #![trigger merge_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, candidate),
            post.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source).view().contains(pointer)]
        !post.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source).view().contains(pointer),
{
    if pre.allc_4k_mp.spec_index(allocator_4k).merge_2m_source_list(source).view().contains(pointer) {
        if source < NUM_CPUS {
            allocator_free_page_ptrs_wf_cache_at(pre.allc_4k_mp, allocator_4k, source, pointer); allocator_free_4k_pages_wf_cache_at(pre.allc_4k_mp, pre.pg_arr, allocator_4k, source, pointer);
        } else {
            allocator_free_page_ptrs_wf_global_at(pre.allc_4k_mp, allocator_4k, pointer); allocator_free_4k_pages_wf_global_at(pre.allc_4k_mp, pre.pg_arr, allocator_4k, pointer);
        }
        page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
    }
}

pub proof fn merge_2m_commit_eof_implies_source_region_removed(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, candidate: Merge2mCandidate)
    requires
        pre.inv(),
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.thrd_mp.dom().contains(thread),
        candidate.wf(),
        candidate.sources.len() == 512,
        page_index_2m_valid(candidate.head),
        forall|index: PageIndex| #![trigger pre.pg_arr.spec_index(index)] candidate.head <= index < candidate.head + 512 ==> {
            let source = candidate.sources.view().spec_index(index as int - candidate.head as int) as usize;
            &&& index_valid(NUM_PAGES, index)
            &&& pre.pg_arr.spec_index(index).view().view().state == PageState::Free4k { allocator_ptr: Ghost(allocator_4k), state:
                if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }
        },
        merge_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, candidate),
    ensures
        merge_2m_source_pages(post.allc_4k_mp.spec_index(allocator_4k)) == merge_2m_source_pages(pre.allc_4k_mp.spec_index(allocator_4k))
            .filter(|pointer: PagePtr| !Set::<PageIndex>::range(candidate.head, (candidate.head + 512) as usize).contains(spec_page_ptr2page_index(pointer))),
{
    let before_allocator = pre.allc_4k_mp.spec_index(allocator_4k);
    let after_allocator = post.allc_4k_mp.spec_index(allocator_4k);
    let before_sets = Seq::new((NUM_CPUS + 1) as nat, |source: int| before_allocator.merge_2m_source_list(source as usize).view().to_set());
    let after_sets = Seq::new((NUM_CPUS + 1) as nat, |source: int| after_allocator.merge_2m_source_list(source as usize).view().to_set());
    let outside = |pointer: PagePtr| !Set::<PageIndex>::range(candidate.head, (candidate.head + 512) as usize).contains(spec_page_ptr2page_index(pointer));
    broadcast use Seq::to_set_ensures, merge_2m_commit_eof_implies_region_page_left_source;
    sequence_pointwise_filter_implies_union_fold_filter(before_sets, after_sets, outside);

}

pub proof fn merge_2m_commit_eof_implies_complete_head_removed(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, candidate: Merge2mCandidate)
    requires
        pre.inv(),
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.thrd_mp.dom().contains(thread),
        candidate.wf(),
        candidate.sources.len() == 512,
        merge_2m_complete_heads(merge_2m_source_pages(pre.allc_4k_mp.spec_index(allocator_4k))).contains(candidate.head),
        page_index_2m_valid(candidate.head),
        forall|index: PageIndex| #![trigger pre.pg_arr.spec_index(index)] candidate.head <= index < candidate.head + 512 ==> {
            let source = candidate.sources.view().spec_index(index as int - candidate.head as int) as usize;
            &&& index_valid(NUM_PAGES, index)
            &&& pre.pg_arr.spec_index(index).view().view().state == PageState::Free4k { allocator_ptr: Ghost(allocator_4k), state:
                if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }
        },
        merge_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, candidate),
    ensures
        merge_2m_complete_heads(merge_2m_source_pages(post.allc_4k_mp.spec_index(allocator_4k)))
            == merge_2m_complete_heads(merge_2m_source_pages(pre.allc_4k_mp.spec_index(allocator_4k))).remove(candidate.head),
        merge_2m_complete_heads(merge_2m_source_pages(post.allc_4k_mp.spec_index(allocator_4k))).len() + 1
            == merge_2m_complete_heads(merge_2m_source_pages(pre.allc_4k_mp.spec_index(allocator_4k))).len(),
{
    merge_2m_commit_eof_implies_source_region_removed(pre, post, thread, allocator_4k, allocator_2m, candidate);
    let before = merge_2m_source_pages(pre.allc_4k_mp.spec_index(allocator_4k));
    let after = merge_2m_source_pages(post.allc_4k_mp.spec_index(allocator_4k));
    page_index_roundtrip();
    assert_sets_equal!(merge_2m_complete_heads(after), merge_2m_complete_heads(before).remove(candidate.head), head => {
        if head != candidate.head && (merge_2m_complete_heads(after).contains(head) || merge_2m_complete_heads(before).contains(head)) {
            assert(head + 512 <= candidate.head || candidate.head + 512 <= head) by {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(head as int, 512);
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(candidate.head as int, 512);
            };
        }
    });
    vstd::set::lemma_set_remove_len(merge_2m_complete_heads(before), candidate.head);
}
}
