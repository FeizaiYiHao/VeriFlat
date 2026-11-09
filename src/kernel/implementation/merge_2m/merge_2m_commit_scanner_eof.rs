#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::{assert_sets_equal, assert_sets_equal_internal, assert_seqs_equal, assert_seqs_equal_internal};
use crate::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_commit_spec::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_scanner::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_scanner_spec::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_cursor_queue::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_set_folds::*;

verus! {
pub broadcast proof fn merge_2m_commit_eof_implies_cursor_wf_and_suffix_unchanged(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, scanner: Merge2mScanner, i: int)
    requires
        pre.inv(),
        pre.allc_4k_mp.dom().contains(allocator_4k),
        scanner.wf(pre.allc_4k_mp.spec_index(allocator_4k)),
        scanner.candidate.sources.len() == 512,
        scanner.returned_heads.view().contains(scanner.candidate.head),
        merge_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, scanner.candidate),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
        0 <= i < scanner.queue.cursors.view().len(),
    ensures
        #![trigger merge_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, scanner.candidate),
            merge_2m_cursor_suffix(post.allc_4k_mp.spec_index(allocator_4k), scanner.queue.cursors.view().spec_index(i))]
        #![trigger merge_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, scanner.candidate),
            Merge2mScanner::cursor_wf(post.allc_4k_mp.spec_index(allocator_4k), scanner.queue.cursors.view().spec_index(i))]
        ({
            let cursor = scanner.queue.cursors.view().spec_index(i);
            &&& Merge2mScanner::cursor_wf(post.allc_4k_mp.spec_index(allocator_4k), cursor)
            &&& merge_2m_cursor_suffix(post.allc_4k_mp.spec_index(allocator_4k), cursor)
                == merge_2m_cursor_suffix(pre.allc_4k_mp.spec_index(allocator_4k), cursor)
        }),
{
    let cursors = scanner.queue.cursors.view();
    let before_allocator = pre.allc_4k_mp.spec_index(allocator_4k);
    let after_allocator = post.allc_4k_mp.spec_index(allocator_4k);
    let before_suffix = |cursor: Merge2mCursor| merge_2m_cursor_suffix(before_allocator, cursor);
    let after_suffix = |cursor: Merge2mCursor| merge_2m_cursor_suffix(after_allocator, cursor);
    let before_sets = cursors.map_values(before_suffix);
    let after_sets = cursors.map_values(after_suffix);
    let region = Set::<PageIndex>::range(scanner.candidate.head, (scanner.candidate.head + 512) as usize);
    sequence_union_fold_implies_entry_subset(before_sets, i);
    assert(before_sets.fold_left(Set::<PagePtr>::empty(), |pages: Set<PagePtr>, added: Set<PagePtr>| pages.union(added))
        == scanner.unscanned_pages(before_allocator)) by { reveal(Merge2mScanner::unscanned_pages); };
    page_ptr_roundtrip(); page_index_roundtrip();

    let cursor = cursors.spec_index(i);
    let before = before_allocator.merge_2m_source_list(cursor.source);
    let after = after_allocator.merge_2m_source_list(cursor.source);
    before.wf_implies_view_len_eq_len(); after.wf_implies_view_len_eq_len(); seq_no_duplicates_implies_index_of_roundtrip::<PagePtr>();
    if cursor.node is Some {
        let node = cursor.node.unwrap();
        let position = before.addr_list.view().index_of(node);
        assert(!region.contains(spec_page_ptr2page_index(cursor.page))) by {
            if region.contains(spec_page_ptr2page_index(cursor.page)) {
                scanner.scanner_wf_at(before_allocator, scanner.candidate.head, (spec_page_ptr2page_index(cursor.page) - scanner.candidate.head) as usize);
            }
        };
        before.wf_map_at(node); after.wf_map_at(node); after.wf_perms_at(node);
        let new_position = after.addr_list.view().index_of(node);
        after.addr_list.view().index_of_first_ensures(node);
        after.wf_value_list_at(new_position);
        assert_sets_equal!(after_sets.spec_index(i), before_sets.spec_index(i), pointer => {
            before.view().skip(position).to_set_ensures(); after.view().skip(new_position).to_set_ensures();
            if before.view().skip(position).contains(pointer) {
                before.view().skip(position).index_of_first_ensures(pointer);
                let old_index = before.view().skip(position).index_of(pointer);
                vstd::seq_lib::lemma_seq_skip_index(before.view(), position, old_index);
                vstd::seq_lib::lemma_seq_skip_contains(before.view(), position, pointer);
                reveal(KernelK::inv);
                if cursor.source < NUM_CPUS { allocator_free_page_ptrs_wf_cache_at(pre.allc_4k_mp, allocator_4k, cursor.source, pointer); }
                else { allocator_free_page_ptrs_wf_global_at(pre.allc_4k_mp, allocator_4k, pointer); }
                assert(!region.contains(spec_page_ptr2page_index(pointer))) by {
                    if region.contains(spec_page_ptr2page_index(pointer)) {
                        scanner.scanner_wf_at(before_allocator, scanner.candidate.head, (spec_page_ptr2page_index(pointer) - scanner.candidate.head) as usize);
                        scanner.consumed_unscanned_order_wf_at(before_allocator, pointer, cursor.page);
                    }
                };
                after.view().index_of_first_ensures(pointer);
                let new_index = after.view().index_of(pointer);
                after.view().lemma_index_contains(new_index);
                vstd::seq_lib::lemma_seq_skip_index(after.view(), new_position, new_index - new_position);
            }
            if after.view().skip(new_position).contains(pointer) {
                after.view().skip(new_position).index_of_first_ensures(pointer);
                let new_index = after.view().skip(new_position).index_of(pointer);
                vstd::seq_lib::lemma_seq_skip_index(after.view(), new_position, new_index);
                vstd::seq_lib::lemma_seq_skip_contains(after.view(), new_position, pointer);
                before.view().index_of_first_ensures(pointer);
                let old_index = before.view().index_of(pointer);
                before.view().lemma_index_contains(old_index);
                vstd::seq_lib::lemma_seq_skip_index(before.view(), position, old_index - position);
            }
        });
    }

    assert(Merge2mScanner::cursor_wf(after_allocator, cursors.spec_index(i))) by {
        let cursor = cursors.spec_index(i);
        if cursor.node is Some {
            let list = after_allocator.merge_2m_source_list(cursor.source);
            let position = list.addr_list.view().index_of(cursor.node.unwrap());
            list.view().skip(position).to_set_ensures();
            vstd::seq_lib::lemma_seq_skip_index(list.view(), position, 0);
            list.view().skip(position).lemma_index_contains(0);
        }
    };
}

pub proof fn merge_2m_commit_eof_implies_scanner_wf(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, scanner: Merge2mScanner)
    requires
        pre.inv(),
        pre.allc_4k_mp.dom().contains(allocator_4k),
        scanner.wf(pre.allc_4k_mp.spec_index(allocator_4k)),
        scanner.candidate.sources.len() == 512,
        scanner.returned_heads.view().contains(scanner.candidate.head),
        merge_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, scanner.candidate),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
    ensures
        scanner.wf(post.allc_4k_mp.spec_index(allocator_4k)),
{
    hide(KernelK::inv); hide(Merge2mScanner::unscanned_pages); hide(merge_2m_source_pages);
    let cursors = scanner.queue.cursors.view();
    let before_allocator = pre.allc_4k_mp.spec_index(allocator_4k);
    let after_allocator = post.allc_4k_mp.spec_index(allocator_4k);
    let before_suffix = |cursor: Merge2mCursor| merge_2m_cursor_suffix(before_allocator, cursor);
    let after_suffix = |cursor: Merge2mCursor| merge_2m_cursor_suffix(after_allocator, cursor);
    let before_sets = cursors.map_values(before_suffix);
    let after_sets = cursors.map_values(after_suffix);
    assert(before_sets.fold_left(Set::<PagePtr>::empty(), |pages: Set<PagePtr>, added: Set<PagePtr>| pages.union(added))
        == scanner.unscanned_pages(before_allocator)) by { reveal(Merge2mScanner::unscanned_pages); };
    page_ptr_roundtrip(); page_index_roundtrip();
    broadcast use merge_2m_commit_eof_implies_cursor_wf_and_suffix_unchanged;

    assert_seqs_equal!(after_sets, before_sets);
    assert(scanner.unscanned_pages(after_allocator) == scanner.unscanned_pages(before_allocator)) by {
        reveal(Merge2mScanner::unscanned_pages);
    };
    assert(scanner.wf(after_allocator)) by {
        broadcast use Seq::to_set_ensures;
        reveal(merge_2m_source_pages);
        sequence_pointwise_subset_implies_union_fold_subset(Seq::new((NUM_CPUS + 1) as nat, |source: int| before_allocator.merge_2m_source_list(source as usize).view().to_set()),
            Seq::new((NUM_CPUS + 1) as nat, |source: int| after_allocator.merge_2m_source_list(source as usize).view().to_set()));
    };
}
}
