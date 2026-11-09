#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_cursor_queue::*;

verus! {
pub open spec fn merge_2m_source_pages(allocator_state: PageAllocator<ALLOCATOR_SIZE_4K>) -> Set<PagePtr> {
    Seq::new((NUM_CPUS + 1) as nat, |source: int| allocator_state.merge_2m_source_list(source as usize).view().to_set())
        .fold_left(Set::<PagePtr>::empty(), |pages: Set<PagePtr>, source: Set<PagePtr>| pages.union(source))
}

pub open spec fn merge_2m_complete_heads(pages: Set<PagePtr>) -> Set<PageIndex> {
    Set::<PageIndex>::range(0, NUM_PAGES).filter(|head: PageIndex| page_index_2m_valid(head)
        && pages.contains(spec_page_index2page_ptr(head)) && forall|page: PageIndex| #![trigger spec_page_index2page_ptr(page)] head <= page < head + 512 ==>
            pages.contains(spec_page_index2page_ptr(page)))
}

pub open spec fn merge_2m_cursor_suffix(allocator_state: PageAllocator<ALLOCATOR_SIZE_4K>, cursor: Merge2mCursor) -> Set<PagePtr> {
    let list = allocator_state.merge_2m_source_list(cursor.source);
    if cursor.node is None { Set::<PagePtr>::empty() } else { list.view().skip(list.addr_list.view().index_of(cursor.node.unwrap())).to_set() }
}
}
