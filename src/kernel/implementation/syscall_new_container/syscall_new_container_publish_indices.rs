use vstd::assert_sets_equal;
use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::staged_4k_page_chain::page_ptrs_to_indices_excludes_distinct_valid_page;
use super::*;

verus! {
/// The two 2M staging-page head indices, with the facts that the funding chain avoids every staged page and that
/// the thread page is the only staging page lock left after the funding chain, the 2M tails, and the other staged pages.
pub(super) fn new_container_publish_staging_heads(
    pages_4k: &ArrayVec<PagePtr, 9>, container_page: PagePtr, pcid_allocator_page: PagePtr, Ghost(funding_pages): Ghost<Seq<PagePtr>>,
    Ghost(lock_dom): Ghost<Set<PageIndex>>,
) -> (ret: (PageIndex, PageIndex))
    requires
        pages_4k.wf(),
        pages_4k.len() == 9,
        pages_4k.view().no_duplicates(),
        page_ptr_valid(pages_4k.view().spec_index(0)),
        page_ptr_valid(pages_4k.view().spec_index(1)),
        page_ptr_valid(pages_4k.view().spec_index(2)),
        page_ptr_valid(pages_4k.view().spec_index(3)),
        page_ptr_valid(pages_4k.view().spec_index(4)),
        page_ptr_valid(pages_4k.view().spec_index(5)),
        page_ptr_valid(pages_4k.view().spec_index(6)),
        page_ptr_valid(pages_4k.view().spec_index(7)),
        page_ptr_valid(pages_4k.view().spec_index(8)),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        container_page != pcid_allocator_page,
        pages_4k.view().to_set().disjoint(page_2m_all_ptrs(page_ptr2page_index(container_page))),
        pages_4k.view().to_set().disjoint(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))),
        page_2m_all_ptrs(page_ptr2page_index(container_page)).disjoint(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))),
        page_2m_tail_indices(page_ptr2page_index(container_page)).disjoint(set![
            page_ptr2page_index(container_page), page_ptr2page_index(pcid_allocator_page), page_ptr2page_index(pages_4k.view().spec_index(0)),
            page_ptr2page_index(pages_4k.view().spec_index(1)), page_ptr2page_index(pages_4k.view().spec_index(2)),
            page_ptr2page_index(pages_4k.view().spec_index(3)), page_ptr2page_index(pages_4k.view().spec_index(4)),
            page_ptr2page_index(pages_4k.view().spec_index(5)), page_ptr2page_index(pages_4k.view().spec_index(6)),
            page_ptr2page_index(pages_4k.view().spec_index(7)), page_ptr2page_index(pages_4k.view().spec_index(8)),
        ]),
        page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)).disjoint(set![
            page_ptr2page_index(container_page), page_ptr2page_index(pcid_allocator_page), page_ptr2page_index(pages_4k.view().spec_index(0)),
            page_ptr2page_index(pages_4k.view().spec_index(1)), page_ptr2page_index(pages_4k.view().spec_index(2)),
            page_ptr2page_index(pages_4k.view().spec_index(3)), page_ptr2page_index(pages_4k.view().spec_index(4)),
            page_ptr2page_index(pages_4k.view().spec_index(5)), page_ptr2page_index(pages_4k.view().spec_index(6)),
            page_ptr2page_index(pages_4k.view().spec_index(7)), page_ptr2page_index(pages_4k.view().spec_index(8)),
        ]),
        lock_dom == page_ptrs_to_indices(pages_4k.view()).union(seq![page_ptr2page_index(container_page), page_ptr2page_index(pcid_allocator_page)].to_set())
            .union(page_ptrs_to_indices(funding_pages)).union(page_2m_tail_indices(page_ptr2page_index(container_page))).union(page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page))),
        lock_dom.contains(page_ptr2page_index(pages_4k.view().spec_index(7))),
        forall|i: int| #![trigger page_ptr_valid(funding_pages.spec_index(i))] 0 <= i < funding_pages.len() ==> page_ptr_valid(funding_pages.spec_index(i)),
        funding_pages.to_set().disjoint(pages_4k.view().to_set()),
        page_ptrs_to_indices(funding_pages).disjoint(page_2m_tail_indices(page_ptr2page_index(container_page))),
        page_ptrs_to_indices(funding_pages).disjoint(page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page))),
        funding_pages.to_set().disjoint(new_container_moved_pages(
            container_page, pcid_allocator_page, pages_4k.view().spec_index(0), pages_4k.view().spec_index(1),
            pages_4k.view().spec_index(2), pages_4k.view().spec_index(3), pages_4k.view().spec_index(8),
            pages_4k.view().spec_index(4), pages_4k.view().spec_index(5), pages_4k.view().spec_index(6),
        )),
    ensures
        ret == (page_ptr2page_index(container_page), page_ptr2page_index(pcid_allocator_page)),
        !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(container_page)),
        !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(pcid_allocator_page)),
        !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(pages_4k.view().spec_index(0))),
        !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(pages_4k.view().spec_index(1))),
        !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(pages_4k.view().spec_index(2))),
        !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(pages_4k.view().spec_index(3))),
        !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(pages_4k.view().spec_index(8))),
        !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(pages_4k.view().spec_index(4))),
        !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(pages_4k.view().spec_index(5))),
        !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(pages_4k.view().spec_index(6))),
        !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(pages_4k.view().spec_index(7))),
        lock_dom.difference(page_ptrs_to_indices(funding_pages)).difference(page_2m_tail_indices(ret.0).union(page_2m_tail_indices(ret.1)).union(set![
            page_ptr2page_index(pages_4k.view().spec_index(0)), page_ptr2page_index(pages_4k.view().spec_index(1)), page_ptr2page_index(pages_4k.view().spec_index(2)),
            page_ptr2page_index(pages_4k.view().spec_index(3)), page_ptr2page_index(pages_4k.view().spec_index(8)), page_ptr2page_index(pages_4k.view().spec_index(4)),
            page_ptr2page_index(pages_4k.view().spec_index(5)), page_ptr2page_index(pages_4k.view().spec_index(6)), ret.0, ret.1,
        ])) == set![page_ptr2page_index(pages_4k.view().spec_index(7))],
{
    hide(Seq::contains);
    let allocator_4k_page = *pages_4k.get(0);
    let allocator_2m_page = *pages_4k.get(1);
    let allocator_1g_page = *pages_4k.get(2);
    let scheduler_page = *pages_4k.get(3);
    let cpu_set_page = *pages_4k.get(8);
    let process_page = *pages_4k.get(4);
    let pagetable_page = *pages_4k.get(5);
    let l4_page = *pages_4k.get(6);
    let thread_page = *pages_4k.get(7);
    let container_head = page_ptr2page_index(container_page);
    let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
    proof {
        new_container_page_positions(pages_4k.view());
        assert(new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page).contains(container_page)
            && new_container_moved_pages(container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page).contains(pcid_allocator_page)) by {
            reveal(new_container_moved_pages); page_2m_all_ptrs_contains_head(container_head); page_2m_all_ptrs_contains_head(pcid_allocator_head); page_ptr_roundtrip();
        };
        assert({
            &&& !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(container_page))
            &&& !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(pcid_allocator_page))
            &&& !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(allocator_4k_page))
            &&& !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(allocator_2m_page))
            &&& !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(allocator_1g_page))
            &&& !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(scheduler_page))
            &&& !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(cpu_set_page))
            &&& !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(process_page))
            &&& !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(pagetable_page))
            &&& !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(l4_page))
            &&& !page_ptrs_to_indices(funding_pages).contains(page_ptr2page_index(thread_page))
        }) by {
            page_ptrs_to_indices_excludes_distinct_valid_page(funding_pages, container_page);
            page_ptrs_to_indices_excludes_distinct_valid_page(funding_pages, pcid_allocator_page);
            page_ptrs_to_indices_excludes_distinct_valid_page(funding_pages, allocator_4k_page);
            page_ptrs_to_indices_excludes_distinct_valid_page(funding_pages, allocator_2m_page);
            page_ptrs_to_indices_excludes_distinct_valid_page(funding_pages, allocator_1g_page);
            page_ptrs_to_indices_excludes_distinct_valid_page(funding_pages, scheduler_page);
            page_ptrs_to_indices_excludes_distinct_valid_page(funding_pages, cpu_set_page);
            page_ptrs_to_indices_excludes_distinct_valid_page(funding_pages, process_page);
            page_ptrs_to_indices_excludes_distinct_valid_page(funding_pages, pagetable_page);
            page_ptrs_to_indices_excludes_distinct_valid_page(funding_pages, l4_page);
            page_ptrs_to_indices_excludes_distinct_valid_page(funding_pages, thread_page);
        };
        assert_sets_equal!(
            lock_dom.difference(page_ptrs_to_indices(funding_pages)).difference(page_2m_tail_indices(container_head).union(page_2m_tail_indices(pcid_allocator_head)).union(set![
                page_ptr2page_index(allocator_4k_page), page_ptr2page_index(allocator_2m_page), page_ptr2page_index(allocator_1g_page),
                page_ptr2page_index(scheduler_page), page_ptr2page_index(cpu_set_page), page_ptr2page_index(process_page),
                page_ptr2page_index(pagetable_page), page_ptr2page_index(l4_page), container_head, pcid_allocator_head,
            ])) == set![page_ptr2page_index(thread_page)],
            page_index => { reveal(Seq::contains); page_ptr_roundtrip(); page_2m_all_ptrs_contains_head(container_head); page_2m_all_ptrs_contains_head(pcid_allocator_head); }
        );
    }
    (container_head, pcid_allocator_head)
}
} // verus!
