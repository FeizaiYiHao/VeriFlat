#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::{assert_sets_equal, assert_sets_equal_internal, assert_seqs_equal, assert_seqs_equal_internal};
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
pub open spec fn merge_2m_scan_page_eof_transition_framing(pre: Merge2mScanner, post: Merge2mScanner,
    index: PageIndex, next: Merge2mCursor, complete: bool) -> bool {
    let cursor = pre.queue.cursors.view().spec_index(0);
    &&& post.initial_pages == pre.initial_pages
    &&& post.consumed_pages.view() == pre.consumed_pages.view().insert(cursor.page)
    &&& post.returned_heads.view() == if complete { pre.returned_heads.view().insert(post.candidate.head) } else { pre.returned_heads.view() }
    &&& post.queue.cursors.view().to_multiset() == pre.queue.cursors.view().update(0, next).to_multiset()
    &&& next.source == cursor.source
    &&& complete == (post.candidate.sources.len() == 512)
    &&& post.candidate.sources.len() > 0 ==> index == post.candidate.head + post.candidate.sources.len() - 1
    &&& post.candidate.sources.len() > 0 ==> post.candidate.sources.view().last() == cursor.source as u8
    &&& index % 512 == 0 ==> post.candidate.head == index && post.candidate.sources.view() == seq![cursor.source as u8]
    &&& index % 512 != 0 && pre.candidate.sources.len() > 0 && index == pre.candidate.head + pre.candidate.sources.len() ==>
        post.candidate.head == pre.candidate.head && post.candidate.sources.view() == pre.candidate.sources.view().push(cursor.source as u8)
    &&& index % 512 != 0 && !(pre.candidate.sources.len() > 0 && index == pre.candidate.head + pre.candidate.sources.len()) ==>
        post.candidate.sources.len() == 0
}

pub proof fn merge_2m_scan_page_eof_implies_cursor_queue_facts(pre: Merge2mScanner, post: Merge2mScanner, krnl: &KernelK,
    allocator: RwLockPageAllocatorPtr, index: PageIndex, next: Merge2mCursor, complete: bool)
    requires
        krnl.inv(),
        krnl.allc_4k_mp.dom().contains(allocator),
        pre.queue.wf(),
        pre.queue.cursors.view().map_values(Merge2mCursor::source_value()).no_duplicates(),
        forall|i: int| #![trigger pre.queue.cursors.view().spec_index(i)] 0 <= i < NUM_CPUS + 1 ==>
            Merge2mScanner::cursor_wf(krnl.allc_4k_mp.spec_index(allocator), pre.queue.cursors.view().spec_index(i)),
        pre.queue.cursors.view().spec_index(0).node is Some,
        forall|i: int| #![trigger pre.queue.cursors.view().spec_index(i)] 0 <= i < NUM_CPUS + 1 ==>
            pre.queue.cursors.view().spec_index(0).page <= pre.queue.cursors.view().spec_index(i).page,
        next.node is None <==> krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).addr_list.view().index_of(pre.queue.cursors.view().spec_index(0).node.unwrap()) + 1
            == krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).length,
        next.node is Some ==> krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).addr_list.view().index_of(next.node.unwrap())
            == krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).addr_list.view().index_of(pre.queue.cursors.view().spec_index(0).node.unwrap()) + 1,
        index == spec_page_ptr2page_index(pre.queue.cursors.view().spec_index(0).page),
        Merge2mScanner::cursor_wf(krnl.allc_4k_mp.spec_index(allocator), next),
        next.source == pre.queue.cursors.view().spec_index(0).source,
        next.node == krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).perms.view()
            .spec_index(pre.queue.cursors.view().spec_index(0).node.unwrap()).value().next,
        post.queue.wf(),
        next.source == pre.queue.cursors.view().spec_index(0).source,
        post.queue.cursors.view().to_multiset() == pre.queue.cursors.view().update(0, next).to_multiset(),
    ensures
        forall|i: int| #![trigger post.queue.cursors.view().spec_index(i)] 0 <= i < NUM_CPUS + 1 ==>
            Merge2mScanner::cursor_wf(krnl.allc_4k_mp.spec_index(allocator), post.queue.cursors.view().spec_index(i)),
        post.queue.cursors.view().map_values(Merge2mCursor::source_value()).no_duplicates(),
        post.queue.cursors.view().map_values(Merge2mCursor::source_value()).to_set()
            == pre.queue.cursors.view().map_values(Merge2mCursor::source_value()).to_set(),
        post.remaining_work(krnl.allc_4k_mp.spec_index(allocator)) + 1 == pre.remaining_work(krnl.allc_4k_mp.spec_index(allocator)),
        post.remaining_work(krnl.allc_4k_mp.spec_index(allocator)) >= 0,
{
    let before = pre.queue.cursors.view();
    let cursor = before.spec_index(0);
    let updated = before.update(0, next);
    let list = krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(cursor.source);
    let position = list.addr_list.view().index_of(cursor.node.unwrap());
    list.wf_implies_view_len_eq_len(); list.wf_perms_at(cursor.node.unwrap()); list.addr_list.view().index_of_first_ensures(cursor.node.unwrap());
    list.wf_map_at(cursor.node.unwrap()); list.wf_value_list_at(position);
    if position + 1 < list.length { list.wf_next_at(position); }
    list.view().lemma_index_contains(position);
    page_ptr_roundtrip(); page_index_roundtrip();
    sequence_multiset_equality_implies_entry_predicate(updated, post.queue.cursors.view(), |value: Merge2mCursor|
        Merge2mScanner::cursor_wf(krnl.allc_4k_mp.spec_index(allocator), value)
            && Merge2mScanner::cursor_remaining(krnl.allc_4k_mp.spec_index(allocator), value) >= 0);
    sequence_multiset_equality_implies_mapped_multiset_equality(updated, post.queue.cursors.view(), Merge2mCursor::source_value());

    assert_seqs_equal!(updated.map_values(Merge2mCursor::source_value()), before.map_values(Merge2mCursor::source_value()));
    sequence_multiset_equality_implies_set_and_distinctness(before.map_values(Merge2mCursor::source_value()),
        post.queue.cursors.view().map_values(Merge2mCursor::source_value()));
    let remaining = Merge2mScanner::remaining_value(krnl.allc_4k_mp.spec_index(allocator));

    assert(remaining(next) + 1 == remaining(cursor)) by { reveal(Merge2mScanner::cursor_remaining); };
    sequence_update_implies_sum_fold_delta(before, 0, next, remaining);
    vstd::seq_lib::lemma_fold_left_permutation(updated, post.queue.cursors.view(), sequence_sum_step(remaining), 0int);
    sequence_nonnegative_entries_implies_sum_fold_nonnegative(post.queue.cursors.view(), remaining);

}

pub broadcast proof fn merge_2m_scan_page_eof_implies_other_suffix_excludes_page(pre: Merge2mScanner, krnl: &KernelK, allocator: RwLockPageAllocatorPtr, i: int)
    requires
        krnl.inv(),
        krnl.allc_4k_mp.dom().contains(allocator),
        pre.queue.wf(),
        pre.queue.cursors.view().map_values(Merge2mCursor::source_value()).no_duplicates(),
        forall|i: int| #![trigger pre.queue.cursors.view().spec_index(i)] 0 <= i < NUM_CPUS + 1 ==>
            Merge2mScanner::cursor_wf(krnl.allc_4k_mp.spec_index(allocator), pre.queue.cursors.view().spec_index(i)),
        pre.queue.cursors.view().spec_index(0).node is Some,
        0 < i < NUM_CPUS + 1,
    ensures
        #![trigger merge_2m_cursor_suffix(krnl.allc_4k_mp.spec_index(allocator), pre.queue.cursors.view().spec_index(i))]
        !merge_2m_cursor_suffix(krnl.allc_4k_mp.spec_index(allocator), pre.queue.cursors.view().spec_index(i)).contains(pre.queue.cursors.view().spec_index(0).page),
{
    let before = pre.queue.cursors.view();
    let cursor = before.spec_index(0);
    let other = before.spec_index(i);
    let list = krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(cursor.source);
    list.wf_implies_view_len_eq_len(); list.view().lemma_index_contains(list.addr_list.view().index_of(cursor.node.unwrap()));
    assert(other.source != cursor.source) by {
        let sources = before.map_values(Merge2mCursor::source_value());
        sources.lemma_index_contains(0); sources.lemma_index_contains(i);
        assert_seqs_equal!(sources, Seq::new(before.len(), |index: int| before.spec_index(index).source));
    };
    let other_list = krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(other.source);
    other_list.wf_implies_view_len_eq_len();
    if merge_2m_cursor_suffix(krnl.allc_4k_mp.spec_index(allocator), other).contains(cursor.page) {
        let other_position = other_list.addr_list.view().index_of(other.node.unwrap());
        other_list.view().skip(other_position).to_set_ensures();
        vstd::seq_lib::lemma_seq_skip_contains(other_list.view(), other_position, cursor.page);
        if other.source < NUM_CPUS { allocator_free_4k_pages_wf_cache_at(krnl.allc_4k_mp, krnl.pg_arr, allocator, other.source, cursor.page); }
        else { allocator_free_4k_pages_wf_global_at(krnl.allc_4k_mp, krnl.pg_arr, allocator, cursor.page); }
        if cursor.source < NUM_CPUS { allocator_free_4k_pages_wf_cache_at(krnl.allc_4k_mp, krnl.pg_arr, allocator, cursor.source, cursor.page); }
        else { allocator_free_4k_pages_wf_global_at(krnl.allc_4k_mp, krnl.pg_arr, allocator, cursor.page); }
    }
}

pub broadcast proof fn merge_2m_scan_page_eof_implies_suffix_after_scanned_page(pre: Merge2mScanner, krnl: &KernelK, allocator: RwLockPageAllocatorPtr, i: int)
    requires
        forall|source: usize| #![trigger krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(source)] source <= NUM_CPUS ==>
            LinkedList::<PagePtr, 233>::values_sorted(krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(source).view()),
        forall|i: int| #![trigger pre.queue.cursors.view().spec_index(i)] 0 <= i < NUM_CPUS + 1 ==>
            Merge2mScanner::cursor_wf(krnl.allc_4k_mp.spec_index(allocator), pre.queue.cursors.view().spec_index(i)),
        forall|i: int| #![trigger pre.queue.cursors.view().spec_index(i)] 0 <= i < NUM_CPUS + 1 ==>
            pre.queue.cursors.view().spec_index(0).page <= pre.queue.cursors.view().spec_index(i).page,
        pre.queue.cursors.view().len() == NUM_CPUS + 1,
        0 <= i < NUM_CPUS + 1,
    ensures
        #![trigger merge_2m_cursor_suffix(krnl.allc_4k_mp.spec_index(allocator), pre.queue.cursors.view().spec_index(i))]
        merge_2m_cursor_suffix(krnl.allc_4k_mp.spec_index(allocator), pre.queue.cursors.view().spec_index(i))
            .subset_of(pre.unscanned_pages(krnl.allc_4k_mp.spec_index(allocator)).filter(|pointer: PagePtr| pre.queue.cursors.view().spec_index(0).page <= pointer)),
{
    let before = pre.queue.cursors.view();
    let suffix = |value: Merge2mCursor| merge_2m_cursor_suffix(krnl.allc_4k_mp.spec_index(allocator), value);
    let before_sets = before.map_values(suffix);
    let target = pre.unscanned_pages(krnl.allc_4k_mp.spec_index(allocator)).filter(|pointer: PagePtr| pre.queue.cursors.view().spec_index(0).page <= pointer);
    let value = before.spec_index(i);
    sequence_union_fold_implies_entry_subset(before_sets, i);
    if value.node is Some {
        let list = krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(value.source);
        let values = list.view();
        let position = list.addr_list.view().index_of(value.node.unwrap());
        list.wf_implies_view_len_eq_len(); list.wf_perms_at(value.node.unwrap()); list.addr_list.view().index_of_first_ensures(value.node.unwrap());
        list.wf_map_at(value.node.unwrap()); list.wf_value_list_at(position);
        values.skip(position).to_set_ensures();
        assert_sets_equal!(before_sets.spec_index(i), before_sets.spec_index(i).intersect(target), pointer => {
            if before_sets.spec_index(i).contains(pointer) { vstd::seq_lib::lemma_seq_skip_index(values, position, values.skip(position).index_of(pointer)); }
        });
    }
}

pub proof fn merge_2m_scan_page_eof_implies_cursor_sources(pre: Merge2mScanner, post: Merge2mScanner, krnl: &KernelK,
    allocator: RwLockPageAllocatorPtr, index: PageIndex, next: Merge2mCursor, complete: bool)
    requires
        krnl.inv(),
        krnl.allc_4k_mp.dom().contains(allocator),
        pre.queue.wf(),
        forall|source: usize| #![trigger krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(source)] source <= NUM_CPUS ==>
            LinkedList::<PagePtr, 233>::values_sorted(krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(source).view()),

        pre.queue.cursors.view().map_values(Merge2mCursor::source_value()).no_duplicates(),
        forall|i: int| #![trigger pre.queue.cursors.view().spec_index(i)] 0 <= i < NUM_CPUS + 1 ==>
            Merge2mScanner::cursor_wf(krnl.allc_4k_mp.spec_index(allocator), pre.queue.cursors.view().spec_index(i)),
        pre.queue.cursors.view().spec_index(0).node is Some,
        forall|i: int| #![trigger pre.queue.cursors.view().spec_index(i)] 0 <= i < NUM_CPUS + 1 ==>
            pre.queue.cursors.view().spec_index(0).page <= pre.queue.cursors.view().spec_index(i).page,
        next.node is None <==> krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).addr_list.view().index_of(pre.queue.cursors.view().spec_index(0).node.unwrap()) + 1
            == krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).length,
        next.node is Some ==> krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).addr_list.view().index_of(next.node.unwrap())
            == krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).addr_list.view().index_of(pre.queue.cursors.view().spec_index(0).node.unwrap()) + 1,
        index == spec_page_ptr2page_index(pre.queue.cursors.view().spec_index(0).page),
        Merge2mScanner::cursor_wf(krnl.allc_4k_mp.spec_index(allocator), next),
        next.source == pre.queue.cursors.view().spec_index(0).source,
        next.node == krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).perms.view()
            .spec_index(pre.queue.cursors.view().spec_index(0).node.unwrap()).value().next,
        post.queue.wf(),
        next.source == pre.queue.cursors.view().spec_index(0).source,
        post.queue.cursors.view().to_multiset() == pre.queue.cursors.view().update(0, next).to_multiset(),
    ensures
        post.unscanned_pages(krnl.allc_4k_mp.spec_index(allocator)) == pre.unscanned_pages(krnl.allc_4k_mp.spec_index(allocator)).remove(pre.queue.cursors.view().spec_index(0).page),
        pre.unscanned_pages(krnl.allc_4k_mp.spec_index(allocator)).contains(pre.queue.cursors.view().spec_index(0).page),
        forall|pointer: PagePtr| #![trigger pre.unscanned_pages(krnl.allc_4k_mp.spec_index(allocator)).contains(pointer)]
            pre.unscanned_pages(krnl.allc_4k_mp.spec_index(allocator)).contains(pointer) ==> pre.queue.cursors.view().spec_index(0).page <= pointer,
{
    let before = pre.queue.cursors.view();
    let cursor = before.spec_index(0);
    let updated = before.update(0, next);
    let list = krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(cursor.source);
    let position = list.addr_list.view().index_of(cursor.node.unwrap());
    list.wf_implies_view_len_eq_len(); list.wf_perms_at(cursor.node.unwrap()); list.addr_list.view().index_of_first_ensures(cursor.node.unwrap());
    list.wf_map_at(cursor.node.unwrap()); list.wf_value_list_at(position);
    if position + 1 < list.length { list.wf_next_at(position); }
    list.view().lemma_index_contains(position);
    page_ptr_roundtrip(); page_index_roundtrip();
    let suffix = |value: Merge2mCursor| merge_2m_cursor_suffix(krnl.allc_4k_mp.spec_index(allocator), value);
    let old_suffix = suffix(cursor);
    let next_suffix = suffix(next);

    assert(next_suffix == list.view().skip(position + 1).to_set()) by {
        if next.node is None { assert_seqs_equal!(list.view().skip(position + 1), Seq::<PagePtr>::empty()); }
    };
    seq![cursor.page].lemma_index_contains(0);
    assert(seq![cursor.page].to_set() =~= Set::<PagePtr>::empty().insert(cursor.page)) by {
        seq![cursor.page].to_set_ensures();
    };
    vstd::seq_lib::seq_to_set_distributes_over_add(seq![cursor.page], list.view().skip(position + 1));
    assert(old_suffix == next_suffix.insert(cursor.page)) by {
        assert_seqs_equal!(list.view().skip(position), seq![cursor.page] + list.view().skip(position + 1));
        assert_sets_equal!(old_suffix, next_suffix.insert(cursor.page));
    };
    assert(!next_suffix.contains(cursor.page)) by {
        list.view().skip(position + 1).to_set_ensures();
        if list.view().skip(position + 1).contains(cursor.page) {
            let index = list.view().skip(position + 1).index_of(cursor.page);
            vstd::seq_lib::lemma_seq_skip_index(list.view(), position + 1, index);
        }
    };
    let before_sets = before.map_values(suffix);
    let updated_sets = updated.map_values(suffix);

    broadcast use merge_2m_scan_page_eof_implies_other_suffix_excludes_page, merge_2m_scan_page_eof_implies_suffix_after_scanned_page;
    assert_seqs_equal!(updated_sets, before_sets.update(0, next_suffix));
    sequence_update_implies_union_fold_remove(before_sets, 0, next_suffix, cursor.page);
    sequence_multiset_equality_implies_mapped_multiset_equality(updated, post.queue.cursors.view(), suffix);
    sequence_multiset_equality_implies_union_fold_equality(updated_sets, post.queue.cursors.view().map_values(suffix));

    sequence_union_fold_implies_entry_subset(before_sets, 0);
    let target = pre.unscanned_pages(krnl.allc_4k_mp.spec_index(allocator)).filter(|pointer: PagePtr| pre.queue.cursors.view().spec_index(0).page <= pointer);
    sequence_entries_subset_implies_union_fold_subset(before_sets, target);

}

pub proof fn merge_2m_scan_page_eof_implies_cursor_coverage(pre: Merge2mScanner, post: Merge2mScanner, krnl: &KernelK,
    allocator: RwLockPageAllocatorPtr, index: PageIndex, next: Merge2mCursor, complete: bool)
    requires
        krnl.inv(),
        krnl.allc_4k_mp.dom().contains(allocator),
        pre.queue.wf(),
        forall|source: usize| #![trigger krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(source)] source <= NUM_CPUS ==>
            LinkedList::<PagePtr, 233>::values_sorted(krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(source).view()),

        pre.queue.cursors.view().map_values(Merge2mCursor::source_value()).no_duplicates(),
        forall|i: int| #![trigger pre.queue.cursors.view().spec_index(i)] 0 <= i < NUM_CPUS + 1 ==>
            Merge2mScanner::cursor_wf(krnl.allc_4k_mp.spec_index(allocator), pre.queue.cursors.view().spec_index(i)),
        pre.queue.cursors.view().spec_index(0).node is Some,
        forall|i: int| #![trigger pre.queue.cursors.view().spec_index(i)] 0 <= i < NUM_CPUS + 1 ==>
            pre.queue.cursors.view().spec_index(0).page <= pre.queue.cursors.view().spec_index(i).page,
        next.node is None <==> krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).addr_list.view().index_of(pre.queue.cursors.view().spec_index(0).node.unwrap()) + 1
            == krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).length,
        next.node is Some ==> krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).addr_list.view().index_of(next.node.unwrap())
            == krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).addr_list.view().index_of(pre.queue.cursors.view().spec_index(0).node.unwrap()) + 1,
        index == spec_page_ptr2page_index(pre.queue.cursors.view().spec_index(0).page),
        Merge2mScanner::cursor_wf(krnl.allc_4k_mp.spec_index(allocator), next),
        next.source == pre.queue.cursors.view().spec_index(0).source,
        next.node == krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).perms.view()
            .spec_index(pre.queue.cursors.view().spec_index(0).node.unwrap()).value().next,
        post.queue.wf(),
        next.source == pre.queue.cursors.view().spec_index(0).source,
        post.queue.cursors.view().to_multiset() == pre.queue.cursors.view().update(0, next).to_multiset(),
    ensures
        forall|i: int| #![trigger post.queue.cursors.view().spec_index(i)] 0 <= i < NUM_CPUS + 1 ==>
            Merge2mScanner::cursor_wf(krnl.allc_4k_mp.spec_index(allocator), post.queue.cursors.view().spec_index(i)),
        post.queue.cursors.view().map_values(Merge2mCursor::source_value()).no_duplicates(),
        post.queue.cursors.view().map_values(Merge2mCursor::source_value()).to_set()
            == pre.queue.cursors.view().map_values(Merge2mCursor::source_value()).to_set(),
        post.unscanned_pages(krnl.allc_4k_mp.spec_index(allocator)) == pre.unscanned_pages(krnl.allc_4k_mp.spec_index(allocator)).remove(pre.queue.cursors.view().spec_index(0).page),
        pre.unscanned_pages(krnl.allc_4k_mp.spec_index(allocator)).contains(pre.queue.cursors.view().spec_index(0).page),
        merge_2m_source_pages(krnl.allc_4k_mp.spec_index(allocator)).contains(pre.queue.cursors.view().spec_index(0).page),
        forall|pointer: PagePtr| #![trigger pre.unscanned_pages(krnl.allc_4k_mp.spec_index(allocator)).contains(pointer)]
            pre.unscanned_pages(krnl.allc_4k_mp.spec_index(allocator)).contains(pointer) ==> pre.queue.cursors.view().spec_index(0).page <= pointer,
        post.remaining_work(krnl.allc_4k_mp.spec_index(allocator)) + 1 == pre.remaining_work(krnl.allc_4k_mp.spec_index(allocator)),
        post.remaining_work(krnl.allc_4k_mp.spec_index(allocator)) >= 0,
{
    assert(merge_2m_source_pages(krnl.allc_4k_mp.spec_index(allocator)).contains(pre.queue.cursors.view().spec_index(0).page)) by {
        let cursor = pre.queue.cursors.view().spec_index(0);
        let list = krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(cursor.source);
        list.wf_implies_view_len_eq_len(); list.wf_perms_at(cursor.node.unwrap()); list.addr_list.view().index_of_first_ensures(cursor.node.unwrap());
        list.wf_map_at(cursor.node.unwrap()); list.wf_value_list_at(list.addr_list.view().index_of(cursor.node.unwrap()));
        let values = list.view();
        values.to_set_ensures(); values.lemma_index_contains(krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(cursor.source).addr_list.view().index_of(cursor.node.unwrap()));
        sequence_union_fold_implies_entry_subset(Seq::new((NUM_CPUS + 1) as nat,
            |i: int| krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(i as usize).view().to_set()), cursor.source as int);
    };
    merge_2m_scan_page_eof_implies_cursor_queue_facts(pre, post, krnl, allocator, index, next, complete);
    merge_2m_scan_page_eof_implies_cursor_sources(pre, post, krnl, allocator, index, next, complete);
}

pub proof fn merge_2m_scan_page_eof_implies_candidate_prefix(pre: Merge2mScanner, post: Merge2mScanner, krnl: &KernelK,
    allocator: RwLockPageAllocatorPtr, index: PageIndex, next: Merge2mCursor, complete: bool)
    requires
        krnl.inv(),
        krnl.allc_4k_mp.dom().contains(allocator),
        merge_2m_source_pages(krnl.allc_4k_mp.spec_index(allocator)).contains(pre.queue.cursors.view().spec_index(0).page),
        pre.wf(krnl.allc_4k_mp.spec_index(allocator)),
        pre.candidate_prefix_valid(krnl, allocator),
        pre.candidate.sources.len() < 512,
        pre.queue.cursors.view().spec_index(0).node is Some,
        forall|i: int| #![trigger pre.queue.cursors.view().spec_index(i)] 0 <= i < NUM_CPUS + 1 ==>
            pre.queue.cursors.view().spec_index(0).page <= pre.queue.cursors.view().spec_index(i).page,
        next.node is None <==> krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).addr_list.view().index_of(pre.queue.cursors.view().spec_index(0).node.unwrap()) + 1
            == krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).length,
        next.node is Some ==> krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).addr_list.view().index_of(next.node.unwrap())
            == krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).addr_list.view().index_of(pre.queue.cursors.view().spec_index(0).node.unwrap()) + 1,
        index == spec_page_ptr2page_index(pre.queue.cursors.view().spec_index(0).page),
        Merge2mScanner::cursor_wf(krnl.allc_4k_mp.spec_index(allocator), next),
        next.source == pre.queue.cursors.view().spec_index(0).source,
        next.node == krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).perms.view()
            .spec_index(pre.queue.cursors.view().spec_index(0).node.unwrap()).value().next,
        post.queue.wf(),
        post.candidate.wf(),
        merge_2m_scan_page_eof_transition_framing(pre, post, index, next, complete),
    ensures
        post.candidate_prefix_valid(krnl, allocator),
        post.returned_heads.view().subset_of(merge_2m_complete_heads(post.initial_pages.view())),
        complete ==> !pre.returned_heads.view().contains(post.candidate.head),
        complete ==> forall|head: PageIndex| #![trigger pre.returned_heads.view().contains(head)] pre.returned_heads.view().contains(head) ==> head < post.candidate.head,
{
    merge_2m_scan_page_eof_implies_cursor_coverage(pre, post, krnl, allocator, index, next, complete);
    let cursor = pre.queue.cursors.view().spec_index(0);
    let list = krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(cursor.source);
    list.wf_implies_view_len_eq_len();
    let position = list.addr_list.view().index_of(cursor.node.unwrap());
    list.view().lemma_index_contains(position);
    page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); page_index_roundtrip();
    if cursor.source < NUM_CPUS { allocator_free_4k_pages_wf_cache_at(krnl.allc_4k_mp, krnl.pg_arr, allocator, cursor.source, cursor.page); }
    else { allocator_free_4k_pages_wf_global_at(krnl.allc_4k_mp, krnl.pg_arr, allocator, cursor.page); }
    assert(post.candidate_prefix_valid(krnl, allocator)) by {
        reveal(Merge2mScanner::candidate_prefix_valid); reveal(allocator_free_4k_pages_wf);
        reveal(allocator_cpu_cache_4k_pages_wf); reveal(allocator_global_pool_4k_pages_wf);
    };
    assert(post.initial_pages.view() == post.consumed_pages.view().union(post.unscanned_pages(krnl.allc_4k_mp.spec_index(allocator)))) by {
        assert_sets_equal!(post.initial_pages.view(), post.consumed_pages.view().union(post.unscanned_pages(krnl.allc_4k_mp.spec_index(allocator))));
    };

}

pub broadcast proof fn merge_2m_scan_page_eof_implies_unreturned_page_remains(pre: Merge2mScanner, post: Merge2mScanner, krnl: &KernelK,
    allocator: RwLockPageAllocatorPtr, index: PageIndex, next: Merge2mCursor, complete: bool, head: PageIndex, page: PageIndex)
    requires
        krnl.inv(),
        krnl.allc_4k_mp.dom().contains(allocator),
        pre.wf(krnl.allc_4k_mp.spec_index(allocator)),
        pre.candidate_prefix_valid(krnl, allocator),
        pre.candidate.sources.len() < 512,
        pre.queue.cursors.view().spec_index(0).node is Some,
        forall|i: int| #![trigger pre.queue.cursors.view().spec_index(i)] 0 <= i < NUM_CPUS + 1 ==>
            pre.queue.cursors.view().spec_index(0).page <= pre.queue.cursors.view().spec_index(i).page,
        next.node is None <==> krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).addr_list.view().index_of(pre.queue.cursors.view().spec_index(0).node.unwrap()) + 1
            == krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).length,
        next.node is Some ==> krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).addr_list.view().index_of(next.node.unwrap())
            == krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).addr_list.view().index_of(pre.queue.cursors.view().spec_index(0).node.unwrap()) + 1,
        index == spec_page_ptr2page_index(pre.queue.cursors.view().spec_index(0).page),
        Merge2mScanner::cursor_wf(krnl.allc_4k_mp.spec_index(allocator), next),
        next.source == pre.queue.cursors.view().spec_index(0).source,
        next.node == krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).perms.view()
            .spec_index(pre.queue.cursors.view().spec_index(0).node.unwrap()).value().next,
        post.queue.wf(),
        post.candidate.wf(),
        merge_2m_scan_page_eof_transition_framing(pre, post, index, next, complete),
        merge_2m_complete_heads(post.initial_pages.view()).contains(head),
        !post.returned_heads.view().contains(head),
        head <= page < head + 512,
    ensures
        #![trigger merge_2m_scan_page_eof_transition_framing(pre, post, index, next, complete),
            post.unscanned_pages(krnl.allc_4k_mp.spec_index(allocator)).contains(spec_page_index2page_ptr(page)),
            merge_2m_complete_heads(post.initial_pages.view()).contains(head)]
        ({
            ||| post.unscanned_pages(krnl.allc_4k_mp.spec_index(allocator)).contains(spec_page_index2page_ptr(page))
            ||| head == post.candidate.head && page < head + post.candidate.sources.len()
                && post.consumed_pages.view().contains(spec_page_index2page_ptr(page))
        }),
{
    hide(Merge2mScanner::wf); hide(Merge2mScanner::candidate_prefix_valid); hide(Merge2mCursorQueue::wf);
    assert({
        &&& pre.queue.wf()
        &&& pre.queue.cursors.view().map_values(Merge2mCursor::source_value()).no_duplicates()
        &&& forall|i: int| #![trigger pre.queue.cursors.view().spec_index(i)] 0 <= i < NUM_CPUS + 1 ==>
            Merge2mScanner::cursor_wf(krnl.allc_4k_mp.spec_index(allocator), pre.queue.cursors.view().spec_index(i))
        &&& forall|source: usize| #![trigger krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(source)] source <= NUM_CPUS ==>
            LinkedList::<PagePtr, 233>::values_sorted(krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(source).view())
    }) by { reveal(Merge2mScanner::wf); };
    merge_2m_scan_page_eof_implies_cursor_coverage(pre, post, krnl, allocator, index, next, complete);
    let cursor = pre.queue.cursors.view().spec_index(0);
    let offset = (page - head) as usize;
    page_ptr_roundtrip(); page_index_roundtrip();
    let pointer = spec_page_index2page_ptr(page);

    pre.scanner_wf_at(krnl.allc_4k_mp.spec_index(allocator), head, offset);

    if head == pre.candidate.head && pre.candidate.sources.len() > 0 {
        let length = pre.candidate.sources.len();
        pre.scanner_wf_at(krnl.allc_4k_mp.spec_index(allocator), head, length);
        let upcoming = spec_page_index2page_ptr((head + length) as usize);
        let previous = spec_page_index2page_ptr((head + length - 1) as usize);

        pre.candidate_prefix_valid_wf_at(krnl, allocator, (head + length - 1) as usize);

        pre.consumed_unscanned_order_wf_at(krnl.allc_4k_mp.spec_index(allocator), previous, cursor.page);

    } else if pointer == cursor.page {
        pre.scanner_wf_at(krnl.allc_4k_mp.spec_index(allocator), head, 0);

    }
}

pub broadcast proof fn merge_2m_scan_page_eof_implies_unreturned_next_page_remains(pre: Merge2mScanner, post: Merge2mScanner,
    krnl: &KernelK, allocator: RwLockPageAllocatorPtr, index: PageIndex, next: Merge2mCursor, complete: bool, head: PageIndex)
    requires
        krnl.inv(),
        krnl.allc_4k_mp.dom().contains(allocator),
        pre.wf(krnl.allc_4k_mp.spec_index(allocator)),
        pre.candidate_prefix_valid(krnl, allocator),
        pre.candidate.sources.len() < 512,
        pre.queue.cursors.view().spec_index(0).node is Some,
        forall|i: int| #![trigger pre.queue.cursors.view().spec_index(i)] 0 <= i < NUM_CPUS + 1 ==>
            pre.queue.cursors.view().spec_index(0).page <= pre.queue.cursors.view().spec_index(i).page,
        next.node is None <==> krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).addr_list.view().index_of(pre.queue.cursors.view().spec_index(0).node.unwrap()) + 1
            == krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).length,
        next.node is Some ==> krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).addr_list.view().index_of(next.node.unwrap())
            == krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).addr_list.view().index_of(pre.queue.cursors.view().spec_index(0).node.unwrap()) + 1,
        index == spec_page_ptr2page_index(pre.queue.cursors.view().spec_index(0).page),
        Merge2mScanner::cursor_wf(krnl.allc_4k_mp.spec_index(allocator), next),
        next.source == pre.queue.cursors.view().spec_index(0).source,
        next.node == krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).perms.view()
            .spec_index(pre.queue.cursors.view().spec_index(0).node.unwrap()).value().next,
        post.queue.wf(),
        post.candidate.wf(),
        merge_2m_scan_page_eof_transition_framing(pre, post, index, next, complete),
        merge_2m_complete_heads(post.initial_pages.view()).contains(head),
        !post.returned_heads.view().contains(head),
    ensures
        #![trigger merge_2m_scan_page_eof_transition_framing(pre, post, index, next, complete),
            post.unscanned_pages(krnl.allc_4k_mp.spec_index(allocator)), merge_2m_complete_heads(post.initial_pages.view()).contains(head)]
        ({
            let progress = if head == post.candidate.head { post.candidate.sources.len() } else { 0usize };
            progress < 512 ==> post.unscanned_pages(krnl.allc_4k_mp.spec_index(allocator))
                .contains(spec_page_index2page_ptr((head + progress) as usize))
        }),
{
    let progress = if head == post.candidate.head { post.candidate.sources.len() } else { 0usize };
    if progress < 512 {
        merge_2m_scan_page_eof_implies_unreturned_page_remains(pre, post, krnl, allocator, index, next, complete, head, (head + progress) as usize);
    }
}

pub proof fn merge_2m_scan_page_eof_implies_complete_candidate_safety(krnl: &KernelK,
    allocator: RwLockPageAllocatorPtr, scanner: Merge2mScanner)
    requires
        krnl.inv(),
        krnl.allc_4k_mp.dom().contains(allocator),
        scanner.candidate.wf(),
        scanner.candidate.sources.len() == 512,
        scanner.candidate_prefix_valid(krnl, allocator),
    ensures
        scanner.candidate.head <= NUM_PAGES - 512,
        merge_2m_complete_heads(merge_2m_source_pages(krnl.allc_4k_mp.spec_index(allocator))).contains(scanner.candidate.head),
        forall|page: PageIndex| #![trigger krnl.pg_arr.lock_id_by_index(page)] scanner.candidate.head <= page < scanner.candidate.head + 512 ==>
            krnl.pg_arr.lock_id_by_index(page).major == FREE_PAGE_LOCK_MAJOR,
{
    hide(merge_2m_source_pages); hide(Merge2mScanner::unscanned_pages);
    scanner.candidate_prefix_valid_wf_at(krnl, allocator, (scanner.candidate.head + 511) as usize);
    reveal(page_array_wf); reveal(LockedArray::lock_id_by_index);
}

pub proof fn merge_2m_scan_page_eof_implies_scanner_wf(pre: Merge2mScanner, post: Merge2mScanner, krnl: &KernelK,
    allocator: RwLockPageAllocatorPtr, index: PageIndex, next: Merge2mCursor, complete: bool)
    requires
        krnl.inv(),
        krnl.allc_4k_mp.dom().contains(allocator),
        pre.wf(krnl.allc_4k_mp.spec_index(allocator)),
        pre.candidate_prefix_valid(krnl, allocator),
        pre.candidate.sources.len() < 512,
        pre.queue.cursors.view().spec_index(0).node is Some,
        forall|i: int| #![trigger pre.queue.cursors.view().spec_index(i)] 0 <= i < NUM_CPUS + 1 ==>
            pre.queue.cursors.view().spec_index(0).page <= pre.queue.cursors.view().spec_index(i).page,
        next.node is None <==> krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).addr_list.view().index_of(pre.queue.cursors.view().spec_index(0).node.unwrap()) + 1
            == krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).length,
        next.node is Some ==> krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).addr_list.view().index_of(next.node.unwrap())
            == krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).addr_list.view().index_of(pre.queue.cursors.view().spec_index(0).node.unwrap()) + 1,
        index == spec_page_ptr2page_index(pre.queue.cursors.view().spec_index(0).page),
        Merge2mScanner::cursor_wf(krnl.allc_4k_mp.spec_index(allocator), next),
        next.source == pre.queue.cursors.view().spec_index(0).source,
        next.node == krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(next.source).perms.view()
            .spec_index(pre.queue.cursors.view().spec_index(0).node.unwrap()).value().next,
        post.queue.wf(),
        post.candidate.wf(),
        merge_2m_scan_page_eof_transition_framing(pre, post, index, next, complete),
    ensures
        post.wf(krnl.allc_4k_mp.spec_index(allocator)),
        post.candidate_prefix_valid(krnl, allocator),
        complete ==> post.candidate.head <= NUM_PAGES - 512,
        complete ==> merge_2m_complete_heads(merge_2m_source_pages(krnl.allc_4k_mp.spec_index(allocator))).contains(post.candidate.head),
        complete ==> forall|page: PageIndex| #![trigger krnl.pg_arr.lock_id_by_index(page)] post.candidate.head <= page < post.candidate.head + 512 ==>
            krnl.pg_arr.lock_id_by_index(page).major == FREE_PAGE_LOCK_MAJOR,
        post.remaining_work(krnl.allc_4k_mp.spec_index(allocator)) + 1 == pre.remaining_work(krnl.allc_4k_mp.spec_index(allocator)),
        post.remaining_work(krnl.allc_4k_mp.spec_index(allocator)) >= 0,
        complete ==> !pre.returned_heads.view().contains(post.candidate.head),
        complete ==> forall|head: PageIndex| #![trigger pre.returned_heads.view().contains(head)] pre.returned_heads.view().contains(head) ==> head < post.candidate.head,
{
    hide(KernelK::inv); hide(Merge2mScanner::candidate_prefix_valid); hide(Merge2mScanner::unscanned_pages); hide(merge_2m_source_pages); hide(Merge2mCursorQueue::wf);
    merge_2m_scan_page_eof_implies_cursor_coverage(pre, post, krnl, allocator, index, next, complete);
    merge_2m_scan_page_eof_implies_candidate_prefix(pre, post, krnl, allocator, index, next, complete);
    assert(post.initial_pages.view() == post.consumed_pages.view().union(post.unscanned_pages(krnl.allc_4k_mp.spec_index(allocator)))) by {
        assert_sets_equal!(post.initial_pages.view(), post.consumed_pages.view().union(post.unscanned_pages(krnl.allc_4k_mp.spec_index(allocator))));
    };

    assert(post.wf(krnl.allc_4k_mp.spec_index(allocator))) by {
        broadcast use merge_2m_scan_page_eof_implies_unreturned_page_remains, merge_2m_scan_page_eof_implies_unreturned_next_page_remains;
    };

    if complete { merge_2m_scan_page_eof_implies_complete_candidate_safety(krnl, allocator, post); }
}
}
