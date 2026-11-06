use vstd::prelude::*;
use crate::*;

verus! {
pub open spec fn page_2m_tail_indices(head: PageIndex) -> Set<PageIndex> {
    Set::range((head + 1) as usize, (head + 512) as usize)
}

pub open spec fn page_2m_ptr_prefix(head: PageIndex, count: nat) -> Set<PagePtr>
    decreases count,
{
    if count == 0 { Set::empty() } else { page_2m_ptr_prefix(head, (count - 1) as nat).insert(spec_page_index2page_ptr((head as int + count as int - 1) as usize)) }
}

pub open spec fn page_2m_all_ptrs(head: PageIndex) -> Set<PagePtr> {
    page_2m_ptr_prefix(head, 512)
}

proof fn page_2m_ptr_prefix_contains_head(head: PageIndex, count: nat)
    requires
        page_index_2m_valid(head),
        0 < count <= 512,
    ensures
        page_2m_ptr_prefix(head, count).contains(page_index2page_ptr(head)),
        page_2m_ptr_prefix(head, count).len() == count,
    decreases count,
{
    if count == 1 {} else {
        page_2m_ptr_prefix_contains_head(head, (count - 1) as nat);
        assert(!page_2m_ptr_prefix(head, (count - 1) as nat).contains(spec_page_index2page_ptr((head + count - 1) as usize))) by { broadcast use page_2m_ptr_prefix_member_bounds; page_index_roundtrip(); };
    }
}

pub proof fn page_2m_all_ptrs_contains_head(head: PageIndex)
    requires
        page_index_2m_valid(head),
    ensures
        page_2m_all_ptrs(head).contains(page_index2page_ptr(head)),
        page_2m_all_ptrs(head).len() == 512,
{
    page_2m_ptr_prefix_contains_head(head, 512);
}

proof fn page_2m_ptr_prefix_contains_index(head: PageIndex, count: nat, index: PageIndex)
    requires
        page_index_2m_valid(head),
        0 < count <= 512,
        head <= index < head + count,
    ensures
        page_2m_ptr_prefix(head, count).contains(page_index2page_ptr(index)),
    decreases count,
{
    let last = (head as int + count as int - 1) as usize;
    if index == last { } else { page_2m_ptr_prefix_contains_index(head, (count - 1) as nat, index); }
}

pub proof fn page_2m_all_ptrs_contains_index(head: PageIndex, index: PageIndex)
    requires
        page_index_2m_valid(head),
        head <= index < head + 512,
    ensures
        page_2m_all_ptrs(head).contains(page_index2page_ptr(index)),
{
    page_2m_ptr_prefix_contains_index(head, 512, index);
}

pub broadcast proof fn page_2m_ptr_prefix_member_bounds(head: PageIndex, count: nat, pg_ptr: PagePtr)
    requires
        page_index_2m_valid(head),
        count <= 512,
        #[trigger] page_2m_ptr_prefix(head, count).contains(pg_ptr),
    ensures
        page_ptr_valid(pg_ptr),
        head <= page_ptr2page_index(pg_ptr) < head + count,
        page_ptr2page_index(pg_ptr) == head || spec_page_index_merge_2m_valid(head, page_ptr2page_index(pg_ptr)),
        page_ptr2page_index(pg_ptr) == head || page_2m_tail_indices(head).contains(page_ptr2page_index(pg_ptr)),
    decreases count,
{
    assert(count > 0) by { if count == 0 { } };
    let last = (head as int + count as int - 1) as usize;
    if pg_ptr == spec_page_index2page_ptr(last) {
        page_index_valid_imply_page_ptr_valid();
        page_index_roundtrip();
    } else {
        page_2m_ptr_prefix_member_bounds(head, (count - 1) as nat, pg_ptr);
    }
}

pub broadcast proof fn page_ptr_sequence_index_in_mapped_set(page_ptrs: Seq<PagePtr>, i: int)
    requires
        0 <= i < page_ptrs.len(),
    ensures
        #[trigger] page_ptr_valid(page_ptrs.spec_index(i)) ==> {
            &&& index_valid(NUM_PAGES, page_ptr2page_index(page_ptrs.spec_index(i)))
            &&& page_ptrs.map_values(|pg_ptr: PagePtr| page_ptr2page_index(pg_ptr)).to_set().contains(page_ptr2page_index(page_ptrs.spec_index(i)))
        },
{
    page_ptr_valid_imply_page_index_valid();
    let mapped = page_ptrs.map_values(|pg_ptr: PagePtr| page_ptr2page_index(pg_ptr));
    mapped.lemma_index_contains(i);
    mapped.to_set_ensures();
}

pub broadcast proof fn page_ptr_sequence_index_in_equal_set(page_ptrs: Seq<PagePtr>, i: int)
    requires
        0 <= i < page_ptrs.len(),
    ensures
        page_ptrs.to_set().contains(#[trigger] page_ptrs.spec_index(i)),
{
    page_ptrs.lemma_index_contains(i);
    page_ptrs.to_set_ensures();
}

proof fn ordered_2m_heads_have_disjoint_all_ptrs(left: PageIndex, right: PageIndex)
    requires
        page_index_2m_valid(left),
        page_index_2m_valid(right),
        left + 512 <= right,
    ensures
        page_2m_all_ptrs(left).disjoint(page_2m_all_ptrs(right)),
{
    broadcast use page_2m_ptr_prefix_member_bounds;
}

pub proof fn distinct_2m_heads_have_disjoint_all_ptrs(left: PageIndex, right: PageIndex)
    requires
        page_index_2m_valid(left),
        page_index_2m_valid(right),
        left != right,
    ensures
        page_2m_all_ptrs(left).disjoint(page_2m_all_ptrs(right)),
{
    if left + 512usize <= right { ordered_2m_heads_have_disjoint_all_ptrs(left, right); } else { ordered_2m_heads_have_disjoint_all_ptrs(right, left); }
}

pub proof fn owned_2m_all_ptrs_belong_to_container(krnl: &KernelK, head: PageIndex, ctn_ptr: RwLockContainerPtr)
    requires
        krnl.inv(),
        page_index_2m_valid(head),
        krnl.pg_arr.spec_index(head).view().view().state is Owned2m || krnl.pg_arr.spec_index(head).view().view().state is Free2m,
        krnl.pg_arr.spec_index(head).view().view().owning_container == ctn_ptr,
    ensures
        page_2m_all_ptrs(head).subset_of(krnl.ctn_mp.spec_index(ctn_ptr).view().owned_pages.view()),
{
    assert(krnl.ctn_mp.dom().contains(ctn_ptr)) by { reveal(container_owned_pages_wf); };
    assert(page_2m_all_ptrs(head).subset_of(krnl.ctn_mp.spec_index(ctn_ptr).view().owned_pages.view())) by {
        reveal(hugepage_2m_wf); reveal(container_owned_pages_wf); broadcast use page_2m_ptr_prefix_member_bounds;
        page_ptr_roundtrip();
    };
}

pub proof fn owned_4k_page_not_in_2m_tail(krnl: &KernelK, pg_ptr: PagePtr, head: PageIndex)
    requires
        krnl.inv(),
        page_ptr_valid(pg_ptr),
        page_index_2m_valid(head),
        krnl.pg_arr.spec_index(head).view().view().state is Owned2m,
        krnl.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Owned4k,
    ensures
        !page_2m_tail_indices(head).contains(page_ptr2page_index(pg_ptr)),
{
    if page_2m_tail_indices(head).contains(page_ptr2page_index(pg_ptr)) { assert(krnl.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Merged2m) by { reveal(hugepage_2m_wf); }; }
}

pub proof fn owned_4k_page_not_in_2m_region(krnl: &KernelK, pg_ptr: PagePtr, head: PageIndex)
    requires
        krnl.inv(),
        page_ptr_valid(pg_ptr),
        page_index_2m_valid(head),
        krnl.pg_arr.spec_index(head).view().view().state is Owned2m,
        krnl.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Owned4k,
    ensures
        !page_2m_all_ptrs(head).contains(pg_ptr),
{
    if page_2m_all_ptrs(head).contains(pg_ptr) {
        page_2m_ptr_prefix_member_bounds(head, 512, pg_ptr);
        if page_ptr2page_index(pg_ptr) != head { owned_4k_page_not_in_2m_tail(krnl, pg_ptr, head); }
    }
}

pub proof fn page_ptr_2m_valid_imply_page_index_2m_valid(pg_ptr: PagePtr)
    requires
        page_ptr_2m_valid(pg_ptr),
    ensures
        page_index_2m_valid(page_ptr2page_index(pg_ptr)),
{
}
}
