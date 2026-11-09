#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::{assert_seqs_equal, assert_seqs_equal_internal, assert_sets_equal, assert_sets_equal_internal};
use crate::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_cursor_queue::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_scanner::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_scanner_spec::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_sequence_folds::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_set_folds::*;

verus! {
pub proof fn merge_2m_scanner_constructor_eof_implies_wf(scanner: Merge2mScanner, krnl: &KernelK,
    allocator: RwLockPageAllocatorPtr, cursors: Seq<Merge2mCursor>)
    requires
        krnl.allc_4k_mp.dom().contains(allocator),
        scanner.queue.wf(),
        scanner.candidate.wf(),
        scanner.candidate.sources.len() == 0,
        scanner.initial_pages.view() == merge_2m_source_pages(krnl.allc_4k_mp.spec_index(allocator)),
        scanner.consumed_pages.view() == Set::<PagePtr>::empty(),
        scanner.returned_heads.view() == Set::<PageIndex>::empty(),
        cursors.len() == NUM_CPUS + 1,
        cursors.to_multiset() == scanner.queue.cursors.view().to_multiset(),
        forall|source: usize| #![trigger krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(source)] source <= NUM_CPUS ==>
            LinkedList::<PagePtr, 233>::values_sorted(krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(source).view()),
        forall|i: int| #![trigger cursors.spec_index(i)] 0 <= i < NUM_CPUS + 1 ==> {
            &&& Merge2mScanner::cursor_wf(krnl.allc_4k_mp.spec_index(allocator), cursors.spec_index(i))
            &&& cursors.spec_index(i).source == i
            &&& merge_2m_cursor_suffix(krnl.allc_4k_mp.spec_index(allocator), cursors.spec_index(i))
                == krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(i as usize).view().to_set()
        },
    ensures
        scanner.wf(krnl.allc_4k_mp.spec_index(allocator)),
{
    let queue = scanner.queue;
    sequence_multiset_equality_implies_mapped_multiset_equality(cursors, queue.cursors.view(), Merge2mCursor::source_value());
    sequence_index_identity_implies_range_set(cursors.map_values(Merge2mCursor::source_value()));
    sequence_multiset_equality_implies_set_and_distinctness(cursors.map_values(Merge2mCursor::source_value()), queue.cursors.view().map_values(Merge2mCursor::source_value()));
    let suffix = |cursor: Merge2mCursor| merge_2m_cursor_suffix(krnl.allc_4k_mp.spec_index(allocator), cursor);
    assert_seqs_equal!(cursors.map_values(suffix), Seq::new((NUM_CPUS + 1) as nat,
        |source: int| krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(source as usize).view().to_set()));
    sequence_multiset_equality_implies_mapped_multiset_equality(cursors, queue.cursors.view(), suffix);
    sequence_multiset_equality_implies_entry_predicate(cursors, queue.cursors.view(),
        |cursor: Merge2mCursor| Merge2mScanner::cursor_wf(krnl.allc_4k_mp.spec_index(allocator), cursor));
    sequence_multiset_equality_implies_union_fold_equality(cursors.map_values(suffix), queue.cursors.view().map_values(suffix));

    assert(scanner.initial_pages.view() == scanner.consumed_pages.view().union(scanner.unscanned_pages(krnl.allc_4k_mp.spec_index(allocator)))) by {
        assert_sets_equal!(scanner.initial_pages.view(), scanner.consumed_pages.view().union(scanner.unscanned_pages(krnl.allc_4k_mp.spec_index(allocator))));
    };

}
pub proof fn merge_2m_clear_candidate_eof_implies_scanner_wf(pre: Merge2mScanner, post: Merge2mScanner,
    krnl: &KernelK, allocator: RwLockPageAllocatorPtr)
    requires
        krnl.allc_4k_mp.dom().contains(allocator),
        pre.wf(krnl.allc_4k_mp.spec_index(allocator)),
        pre.candidate.sources.len() == 0 || pre.candidate.sources.len() == 512,
        pre.candidate.sources.len() == 512 ==> pre.returned_heads.view().contains(pre.candidate.head),
        post == (Merge2mScanner { candidate: post.candidate, ..pre }),
        post.candidate.wf(),
        post.candidate.sources.len() == 0,
    ensures
        post.wf(krnl.allc_4k_mp.spec_index(allocator)),
        post.candidate_prefix_valid(krnl, allocator),
        post.remaining_work(krnl.allc_4k_mp.spec_index(allocator)) == pre.remaining_work(krnl.allc_4k_mp.spec_index(allocator)),
        post.remaining_work(krnl.allc_4k_mp.spec_index(allocator)) >= 0,
{
    assert(post.remaining_work(krnl.allc_4k_mp.spec_index(allocator)) >= 0) by {
        sequence_nonnegative_entries_implies_sum_fold_nonnegative(post.queue.cursors.view(), Merge2mScanner::remaining_value(krnl.allc_4k_mp.spec_index(allocator)));
    };

}

pub proof fn merge_2m_scan_exhausted_eof_implies_all_complete_blocks_returned(pre: Merge2mScanner, post: Merge2mScanner,
    krnl: &KernelK, allocator: RwLockPageAllocatorPtr)
    requires
        krnl.allc_4k_mp.dom().contains(allocator),
        pre.wf(krnl.allc_4k_mp.spec_index(allocator)),
        pre.candidate.sources.len() < 512,
        pre.queue.cursors.view().spec_index(0).node is None,
        forall|i: int| #![trigger pre.queue.cursors.view().spec_index(i)] 0 <= i < NUM_CPUS + 1 ==> pre.queue.cursors.view().spec_index(i).node is None,
        forall|i: int| #![trigger pre.queue.cursors.view().spec_index(i)] 0 <= i < NUM_CPUS + 1 ==>
            pre.queue.cursors.view().spec_index(0).page <= pre.queue.cursors.view().spec_index(i).page,
        post == (Merge2mScanner { candidate: post.candidate, ..pre }),
        post.candidate.wf(),
        post.candidate.sources.len() == 0,
    ensures
        post.wf(krnl.allc_4k_mp.spec_index(allocator)),
        post.candidate_prefix_valid(krnl, allocator),
        merge_2m_complete_heads(post.initial_pages.view()).subset_of(post.returned_heads.view()),
{
    let cursors = pre.queue.cursors.view();
    let sets = cursors.map_values(|cursor: Merge2mCursor| merge_2m_cursor_suffix(krnl.allc_4k_mp.spec_index(allocator), cursor));
    sequence_entries_subset_implies_union_fold_subset(sets, Set::<PagePtr>::empty());

}

}
