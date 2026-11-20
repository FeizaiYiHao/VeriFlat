#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::{assert_seqs_equal, assert_seqs_equal_internal, assert_sets_equal, assert_sets_equal_internal};
use crate::*;
use super::merge_2m_cursor_queue::*;
use super::merge_2m_scan::*;
use super::merge_2m_sources::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_scanner_spec::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_sequence_folds::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_scanner_eof::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_scanner_advance_eof::*;

verus! {
pub struct Merge2mScanner {
    pub queue: Merge2mCursorQueue,
    pub candidate: Merge2mCandidate,
    pub initial_pages: Ghost<Set<PagePtr>>,
    pub consumed_pages: Ghost<Set<PagePtr>>,
    pub returned_heads: Ghost<Set<PageIndex>>,
}

impl Merge2mScanner {
    pub open spec fn cursor_wf(allocator_state: PageAllocator<ALLOCATOR_SIZE_4K>, cursor: Merge2mCursor) -> bool {
        let list = allocator_state.merge_2m_source_list(cursor.source);
        &&& cursor.wf()
        &&& list.wf()
        &&& cursor.node is Some ==> {
            &&& list.dom().contains(cursor.node.unwrap())
            &&& list.map().spec_index(cursor.node.unwrap()) == cursor.page
            &&& 0 <= list.addr_list.view().index_of(cursor.node.unwrap()) < list.length
            &&& list.view().spec_index(list.addr_list.view().index_of(cursor.node.unwrap())) == cursor.page
            &&& merge_2m_cursor_suffix(allocator_state, cursor).contains(cursor.page)
        }
    }

    pub open spec fn wf(&self, allocator_state: PageAllocator<ALLOCATOR_SIZE_4K>) -> bool {
        &&& self.queue.wf()
        &&& self.candidate.wf()
        &&& self.queue.cursors.view().map_values(Merge2mCursor::source_value()).no_duplicates()
        &&& self.queue.cursors.view().map_values(Merge2mCursor::source_value()).to_set() == Set::<usize>::range(0, (NUM_CPUS + 1) as usize)
        &&& forall|source: usize| #![trigger allocator_state.merge_2m_source_list(source)] source <= NUM_CPUS ==>
            LinkedList::<PagePtr, 233>::values_sorted(allocator_state.merge_2m_source_list(source).view())
        &&& forall|i: int| #![trigger self.queue.cursors.view().spec_index(i)] 0 <= i < NUM_CPUS + 1 ==>
            Self::cursor_wf(allocator_state, self.queue.cursors.view().spec_index(i))
        &&& self.initial_pages.view() == self.consumed_pages.view().union(self.unscanned_pages(allocator_state))
        &&& self.consumed_pages.view().disjoint(self.unscanned_pages(allocator_state))
        &&& merge_2m_source_pages(allocator_state).subset_of(self.initial_pages.view())
        &&& self.returned_heads.view().subset_of(merge_2m_complete_heads(self.initial_pages.view()))
        &&& forall|page: PagePtr, future: PagePtr| #![trigger self.consumed_pages.view().contains(page), self.unscanned_pages(allocator_state).contains(future)]
            self.consumed_pages.view().contains(page) && self.unscanned_pages(allocator_state).contains(future) ==> page < future
        &&& forall|head: PageIndex| #![trigger self.returned_heads.view().contains(head)] self.returned_heads.view().contains(head) ==> {
            &&& self.consumed_pages.view().contains(spec_page_index2page_ptr(head))
            &&& forall|page: PageIndex| #![trigger self.consumed_pages.view().contains(spec_page_index2page_ptr(page))]
                head <= page < head + 512 ==> self.consumed_pages.view().contains(spec_page_index2page_ptr(page))
        }
        &&& forall|head: PageIndex| #![trigger merge_2m_complete_heads(self.initial_pages.view()).contains(head)]
            merge_2m_complete_heads(self.initial_pages.view()).contains(head) && !self.returned_heads.view().contains(head) ==> {
            let progress = if head == self.candidate.head { self.candidate.sources.len() } else { 0usize };
            &&& progress < 512 ==> self.unscanned_pages(allocator_state).contains(spec_page_index2page_ptr((head + progress) as usize))
            &&& forall|page: PageIndex| #![trigger self.unscanned_pages(allocator_state).contains(spec_page_index2page_ptr(page))]
                head <= page < head + 512 ==> {
                    ||| self.unscanned_pages(allocator_state).contains(spec_page_index2page_ptr(page))
                    ||| head == self.candidate.head && page < head + self.candidate.sources.len()
                        && self.consumed_pages.view().contains(spec_page_index2page_ptr(page))
                }
        }
    }

    pub proof fn scanner_wf_at(&self, allocator_state: PageAllocator<ALLOCATOR_SIZE_4K>, head: PageIndex, offset: usize)
        requires
            self.wf(allocator_state),
            offset < 512,
        ensures
            self.returned_heads.view().contains(head) ==> self.consumed_pages.view().contains(spec_page_index2page_ptr((head + offset) as usize)),
            merge_2m_complete_heads(self.initial_pages.view()).contains(head) && !self.returned_heads.view().contains(head) ==> {
                ||| self.unscanned_pages(allocator_state).contains(spec_page_index2page_ptr((head + offset) as usize))
                ||| head == self.candidate.head && offset < self.candidate.sources.len()
                    && self.consumed_pages.view().contains(spec_page_index2page_ptr((head + offset) as usize))
            },
    {}

    pub open spec fn candidate_prefix_valid(&self, krnl: &KernelK, allocator: RwLockPageAllocatorPtr) -> bool {
        forall|index: PageIndex| #![trigger krnl.pg_arr.spec_index(index).view().view().state]
            #![trigger merge_2m_source_pages(krnl.allc_4k_mp.spec_index(allocator)).contains(spec_page_index2page_ptr(index))]
            #![trigger self.consumed_pages.view().contains(spec_page_index2page_ptr(index))]
            self.candidate.head <= index < self.candidate.head + self.candidate.sources.len() ==> {
            let source = self.candidate.sources.view().spec_index(index as int - self.candidate.head as int) as usize;
            let page = krnl.pg_arr.spec_index(index).view().view();
            &&& index_valid(NUM_PAGES, index)
            &&& self.consumed_pages.view().contains(spec_page_index2page_ptr(index))
            &&& merge_2m_source_pages(krnl.allc_4k_mp.spec_index(allocator)).contains(spec_page_index2page_ptr(index))
            &&& krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(source).view().contains(spec_page_index2page_ptr(index))
            &&& page.owning_container == krnl.allc_4k_mp.spec_index(allocator).owning_container
            &&& page.state == PageState::Free4k { allocator_ptr: Ghost(allocator), state:
                if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }
        }
    }

    pub proof fn candidate_prefix_valid_wf_at(&self, krnl: &KernelK, allocator: RwLockPageAllocatorPtr, index: PageIndex)
        requires
            self.candidate_prefix_valid(krnl, allocator),
            self.candidate.head <= index < self.candidate.head + self.candidate.sources.len(),
        ensures
            index_valid(NUM_PAGES, index),
            self.consumed_pages.view().contains(spec_page_index2page_ptr(index)),
    {}

    pub proof fn consumed_unscanned_order_wf_at(&self, allocator_state: PageAllocator<ALLOCATOR_SIZE_4K>, past: PagePtr, future: PagePtr)
        requires
            self.wf(allocator_state),
            self.consumed_pages.view().contains(past),
            self.unscanned_pages(allocator_state).contains(future),
        ensures
            past < future,
    {}

    pub open spec fn cursor_remaining(allocator_state: PageAllocator<ALLOCATOR_SIZE_4K>, cursor: Merge2mCursor) -> int {
        let list = allocator_state.merge_2m_source_list(cursor.source);
        if cursor.node is None { 0 } else { list.length as int - list.addr_list.view().index_of(cursor.node.unwrap()) }
    }

    pub open spec fn remaining_value(allocator_state: PageAllocator<ALLOCATOR_SIZE_4K>) -> spec_fn(Merge2mCursor) -> int {
        |cursor: Merge2mCursor| Self::cursor_remaining(allocator_state, cursor)
    }

    pub open spec fn remaining_work(&self, allocator_state: PageAllocator<ALLOCATOR_SIZE_4K>) -> int {
        sequence_sum_fold(self.queue.cursors.view(), Self::remaining_value(allocator_state))
    }

    pub open spec fn unscanned_pages(&self, allocator_state: PageAllocator<ALLOCATOR_SIZE_4K>) -> Set<PagePtr> {
        self.queue.cursors.view().map_values(|cursor: Merge2mCursor| merge_2m_cursor_suffix(allocator_state, cursor))
            .fold_left(Set::<PagePtr>::empty(), |pages: Set<PagePtr>, source: Set<PagePtr>| pages.union(source))
    }

    pub fn new(krnl: &KernelK, allocator: RwLockPageAllocatorPtr, Tracked(lctx): Tracked<&LocalContext>,
        Tracked(cache_perms): Tracked<&Map<CpuId, LockPerm>>, Tracked(pool_perm): Tracked<&LockPerm>) -> (ret: Self)
        requires
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            krnl.allc_4k_mp.dom().contains(allocator),
            forall|source: usize| #![trigger krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(source)] source <= NUM_CPUS ==>
                LinkedList::<PagePtr, 233>::values_sorted(krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(source).view()),
            forall|cpu: CpuId| #![trigger cache_perms.spec_index(cpu)] cpu < NUM_CPUS ==> {
                &&& cache_perms.dom().contains(cpu)
                &&& cache_perms.spec_index(cpu).state() is WriteLock
                &&& cache_perms.spec_index(cpu).thread_id() == lctx.thread_id()
                &&& krnl.allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu).view().locking_thread() is Write
                &&& cache_perms.spec_index(cpu).lock_id() == krnl.allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu).view().locking_thread()->Write_lock_id
                &&& typed_lock_map_contains_mode(lctx.allocator_cache_4k_lock_map(), (allocator, cpu), TypedLockMode::Write)
            },
            pool_perm.state() is WriteLock,
            pool_perm.thread_id() == lctx.thread_id(),
            krnl.allc_4k_mp.spec_index(allocator).global_pool.locking_thread() is Write,
            pool_perm.lock_id() == krnl.allc_4k_mp.spec_index(allocator).global_pool.locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(lctx.allocator_global_pool_4k_lock_map(), allocator, TypedLockMode::Write),
        ensures
            ret.wf(krnl.allc_4k_mp.spec_index(allocator)),
            ret.candidate.sources.len() == 0,
            ret.initial_pages.view() == merge_2m_source_pages(krnl.allc_4k_mp.spec_index(allocator)),
            ret.consumed_pages.view() == Set::<PagePtr>::empty(),
            ret.returned_heads.view() == Set::<PageIndex>::empty(),
    {
        let mut cursors: Array<Merge2mCursor, { NUM_CPUS + 1 }> = Array::new_with_init_value(Merge2mCursor { page: usize::MAX, node: None, source: 0 });
        let mut source = 0usize;
        while source < NUM_CPUS + 1
            invariant
                krnl.inv(),
                typed_lock_maps_aligned(krnl, lctx),
                krnl.allc_4k_mp.dom().contains(allocator),
                forall|source: usize| #![trigger krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(source)] source <= NUM_CPUS ==>
                    LinkedList::<PagePtr, 233>::values_sorted(krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(source).view()),
                forall|cpu: CpuId| #![trigger cache_perms.spec_index(cpu)] cpu < NUM_CPUS ==> {
                    &&& cache_perms.dom().contains(cpu)
                    &&& cache_perms.spec_index(cpu).state() is WriteLock
                    &&& cache_perms.spec_index(cpu).thread_id() == lctx.thread_id()
                    &&& krnl.allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu).view().locking_thread() is Write
                    &&& cache_perms.spec_index(cpu).lock_id() == krnl.allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu).view().locking_thread()->Write_lock_id
                    &&& typed_lock_map_contains_mode(lctx.allocator_cache_4k_lock_map(), (allocator, cpu), TypedLockMode::Write)
                },
                pool_perm.state() is WriteLock,
                pool_perm.thread_id() == lctx.thread_id(),
                krnl.allc_4k_mp.spec_index(allocator).global_pool.locking_thread() is Write,
                pool_perm.lock_id() == krnl.allc_4k_mp.spec_index(allocator).global_pool.locking_thread()->Write_lock_id,
                typed_lock_map_contains_mode(lctx.allocator_global_pool_4k_lock_map(), allocator, TypedLockMode::Write),
                source <= NUM_CPUS + 1,
                cursors.wf(),
                forall|i: int| #![trigger cursors.view().spec_index(i)] 0 <= i < source ==> Self::cursor_wf(krnl.allc_4k_mp.spec_index(allocator), cursors.view().spec_index(i)),
                forall|i: int| #![trigger cursors.view().spec_index(i)] 0 <= i < source ==> cursors.view().spec_index(i).source == i,
                forall|i: int| #![trigger cursors.view().spec_index(i)] 0 <= i < source ==>
                    merge_2m_cursor_suffix(krnl.allc_4k_mp.spec_index(allocator), cursors.view().spec_index(i))
                        == krnl.allc_4k_mp.spec_index(allocator).merge_2m_source_list(i as usize).view().to_set(),
            decreases NUM_CPUS + 1 - source,
        {
            let list = merge_2m_borrow_source(krnl, allocator, source, Tracked(lctx), Tracked(cache_perms), Tracked(pool_perm));
            proof { list.wf_implies_view_len_eq_len(); }
            let node = list.cursor_head();
            let page = if node.is_some() {
                let (page, _) = list.cursor_read(node.unwrap());
                assert(page_ptr_valid(page)) by {
                    if source < NUM_CPUS { allocator_free_page_ptrs_wf_cache_at(krnl.allc_4k_mp, allocator, source, page); }
                    else { allocator_free_page_ptrs_wf_global_at(krnl.allc_4k_mp, allocator, page); }
                };
                page
            } else { usize::MAX };
            let cursor = Merge2mCursor { page, node, source };
            assert(merge_2m_cursor_suffix(krnl.allc_4k_mp.spec_index(allocator), cursor) == list.view().to_set()) by {
                if node is Some { assert_seqs_equal!(list.view().skip(0), list.view()); }
                else { list.wf_implies_view_len_eq_len(); assert_seqs_equal!(list.view(), Seq::<PagePtr>::empty()); }
            };
            cursors.set(source, cursor);
            source += 1;
        }
        let queue = Merge2mCursorQueue::new(cursors);
        let scanner = Merge2mScanner { queue, candidate: Merge2mCandidate::new(), initial_pages: Ghost(merge_2m_source_pages(krnl.allc_4k_mp.spec_index(allocator))),
            consumed_pages: Ghost(Set::<PagePtr>::empty()), returned_heads: Ghost(Set::<PageIndex>::empty()) };
        proof { merge_2m_scanner_constructor_eof_implies_wf(scanner, krnl, allocator, cursors.view()); }
        scanner
    }

    pub fn next_candidate(&mut self, krnl: &KernelK, allocator: RwLockPageAllocatorPtr, Tracked(lctx): Tracked<&LocalContext>,
        Tracked(cache_perms): Tracked<&Map<CpuId, LockPerm>>, Tracked(pool_perm): Tracked<&LockPerm>) -> (ret: bool)
        requires
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            krnl.allc_4k_mp.dom().contains(allocator),
            old(self).wf(krnl.allc_4k_mp.spec_index(allocator)),
            old(self).candidate.sources.len() == 0 || old(self).candidate.sources.len() == 512,
            old(self).candidate.sources.len() == 512 ==> old(self).returned_heads.view().contains(old(self).candidate.head),
            forall|cpu: CpuId| #![trigger cache_perms.spec_index(cpu)] cpu < NUM_CPUS ==> {
                &&& cache_perms.dom().contains(cpu)
                &&& cache_perms.spec_index(cpu).state() is WriteLock
                &&& cache_perms.spec_index(cpu).thread_id() == lctx.thread_id()
                &&& krnl.allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu).view().locking_thread() is Write
                &&& cache_perms.spec_index(cpu).lock_id() == krnl.allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu).view().locking_thread()->Write_lock_id
                &&& typed_lock_map_contains_mode(lctx.allocator_cache_4k_lock_map(), (allocator, cpu), TypedLockMode::Write)
            },
            pool_perm.state() is WriteLock,
            pool_perm.thread_id() == lctx.thread_id(),
            krnl.allc_4k_mp.spec_index(allocator).global_pool.locking_thread() is Write,
            pool_perm.lock_id() == krnl.allc_4k_mp.spec_index(allocator).global_pool.locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(lctx.allocator_global_pool_4k_lock_map(), allocator, TypedLockMode::Write),
        ensures
            final(self).wf(krnl.allc_4k_mp.spec_index(allocator)),
            ret ==> final(self).candidate.sources.len() == 512 && final(self).candidate_prefix_valid(krnl, allocator),
            ret ==> final(self).candidate.head <= NUM_PAGES - 512,
            ret ==> merge_2m_complete_heads(merge_2m_source_pages(krnl.allc_4k_mp.spec_index(allocator))).contains(final(self).candidate.head),
            ret ==> forall|index: PageIndex| #![trigger krnl.pg_arr.lock_id_by_index(index)] final(self).candidate.head <= index < final(self).candidate.head + 512 ==>
                krnl.pg_arr.lock_id_by_index(index).major == FREE_PAGE_LOCK_MAJOR,
            !ret ==> final(self).queue.cursors.view().spec_index(0).node is None,
            final(self).initial_pages == old(self).initial_pages,
            ret ==> final(self).returned_heads.view() == old(self).returned_heads.view().insert(final(self).candidate.head)
                && !old(self).returned_heads.view().contains(final(self).candidate.head),
            ret ==> forall|head: PageIndex| #![trigger old(self).returned_heads.view().contains(head)] old(self).returned_heads.view().contains(head) ==> head < final(self).candidate.head,
            !ret ==> final(self).returned_heads == old(self).returned_heads
                && merge_2m_complete_heads(final(self).initial_pages.view()).subset_of(final(self).returned_heads.view()),
            !ret ==> final(self).candidate.sources.len() == 0,
    {
        let ghost before_clear = *self;
        self.candidate.clear();
        proof { merge_2m_clear_candidate_eof_implies_scanner_wf(before_clear, *self, krnl, allocator); }
        loop
            invariant
                krnl.inv(),
                typed_lock_maps_aligned(krnl, lctx),
                krnl.allc_4k_mp.dom().contains(allocator),
                forall|cpu: CpuId| #![trigger cache_perms.spec_index(cpu)] cpu < NUM_CPUS ==> {
                    &&& cache_perms.dom().contains(cpu)
                    &&& cache_perms.spec_index(cpu).state() is WriteLock
                    &&& cache_perms.spec_index(cpu).thread_id() == lctx.thread_id()
                    &&& krnl.allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu).view().locking_thread() is Write
                    &&& cache_perms.spec_index(cpu).lock_id() == krnl.allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu).view().locking_thread()->Write_lock_id
                    &&& typed_lock_map_contains_mode(lctx.allocator_cache_4k_lock_map(), (allocator, cpu), TypedLockMode::Write)
                },
                pool_perm.state() is WriteLock,
                pool_perm.thread_id() == lctx.thread_id(),
                krnl.allc_4k_mp.spec_index(allocator).global_pool.locking_thread() is Write,
                pool_perm.lock_id() == krnl.allc_4k_mp.spec_index(allocator).global_pool.locking_thread()->Write_lock_id,
                typed_lock_map_contains_mode(lctx.allocator_global_pool_4k_lock_map(), allocator, TypedLockMode::Write),
                self.wf(krnl.allc_4k_mp.spec_index(allocator)),
                self.remaining_work(krnl.allc_4k_mp.spec_index(allocator)) >= 0,
                self.candidate_prefix_valid(krnl, allocator),
                self.candidate.sources.len() < 512,
                self.initial_pages == old(self).initial_pages,
                self.returned_heads == old(self).returned_heads,
            decreases self.remaining_work(krnl.allc_4k_mp.spec_index(allocator)),
        {
            let ghost before = *self;
            let cursor = self.queue.peek_min();
            if cursor.node.is_none() {
                self.candidate.clear();
                proof { merge_2m_scan_exhausted_eof_implies_all_complete_blocks_returned(before, *self, krnl, allocator); }
                return false;
            }
            let list = merge_2m_borrow_source(krnl, allocator, cursor.source, Tracked(lctx), Tracked(cache_perms), Tracked(pool_perm));
            let (page, next) = list.cursor_read(cursor.node.unwrap());
            let next_page = if next.is_some() {
                let (next_page, _) = list.cursor_read(next.unwrap());
                assert(page_ptr_valid(next_page)) by {
                    if cursor.source < NUM_CPUS { allocator_free_page_ptrs_wf_cache_at(krnl.allc_4k_mp, allocator, cursor.source, next_page); }
                    else { allocator_free_page_ptrs_wf_global_at(krnl.allc_4k_mp, allocator, next_page); }
                };
                next_page
            } else { usize::MAX };
            proof { list.wf_implies_view_len_eq_len(); }
            self.queue.advance_min(next_page, next);
            self.consumed_pages = Ghost(self.consumed_pages.view().insert(page));
            let index = page_ptr2page_index(page);
            assert(index_valid(NUM_PAGES, index)) by { page_ptr_valid_imply_page_index_valid(); }
            assert(krnl.pg_arr.spec_index(index).view().view().state == (PageState::Free4k { allocator_ptr: Ghost(allocator), state:
                if cursor.source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: cursor.source } } else { FreePageAllocatorState::GlobalList } })) by {
                if cursor.source < NUM_CPUS { allocator_free_4k_pages_wf_cache_at(krnl.allc_4k_mp, krnl.pg_arr, allocator, cursor.source, page); }
                else { allocator_free_4k_pages_wf_global_at(krnl.allc_4k_mp, krnl.pg_arr, allocator, page); }
            };
            let complete = self.candidate.feed(index, cursor.source);
            if complete { self.returned_heads = Ghost(self.returned_heads.view().insert(self.candidate.head)); }
            proof {
                let replacement = Merge2mCursor { page: next_page, node: next, source: cursor.source };
                merge_2m_scan_page_eof_implies_scanner_wf(before, *self, krnl, allocator, index, replacement, complete);
            }
            if complete { return true; }
        }
    }
}
}
