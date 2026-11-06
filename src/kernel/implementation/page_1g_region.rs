use vstd::prelude::*;
use crate::*;

verus! {
/// The page indices of the merged tails of the 1G region at `head`.
pub open spec fn page_1g_tail_indices(head: PageIndex) -> Set<PageIndex> {
    Set::range((head + 1) as usize, (head + 262144) as usize)
}

/// The page pointers of the first `count` pages of the 1G region at `head`.
pub open spec fn page_1g_ptr_prefix(head: PageIndex, count: nat) -> Set<PagePtr>
    decreases count,
{
    if count == 0 { Set::empty() } else { page_1g_ptr_prefix(head, (count - 1) as nat).insert(spec_page_index2page_ptr((head as int + count as int - 1) as usize)) }
}

/// The page pointers of every page of the 1G region at `head`.
pub open spec fn page_1g_all_ptrs(head: PageIndex) -> Set<PagePtr> {
    page_1g_ptr_prefix(head, 262144)
}

proof fn page_1g_ptr_prefix_contains_head(head: PageIndex, count: nat)
    requires
        page_index_1g_valid(head),
        0 < count <= 262144,
    ensures
        page_1g_ptr_prefix(head, count).contains(page_index2page_ptr(head)),
        page_1g_ptr_prefix(head, count).len() == count,
    decreases count,
{
    if count == 1 {} else {
        page_1g_ptr_prefix_contains_head(head, (count - 1) as nat);
        assert(!page_1g_ptr_prefix(head, (count - 1) as nat).contains(spec_page_index2page_ptr((head + count - 1) as usize))) by { broadcast use page_1g_ptr_prefix_member_bounds; page_index_roundtrip(); };
    }
}

/// The 1G region at a 1G-aligned `head` lists its head and has 262144 page pointers.
pub proof fn page_1g_all_ptrs_contains_head(head: PageIndex)
    requires
        page_index_1g_valid(head),
    ensures
        page_1g_all_ptrs(head).contains(page_index2page_ptr(head)),
        page_1g_all_ptrs(head).len() == 262144,
{
    page_1g_ptr_prefix_contains_head(head, 262144);
}

proof fn page_1g_ptr_prefix_contains_index(head: PageIndex, count: nat, index: PageIndex)
    requires
        page_index_1g_valid(head),
        0 < count <= 262144,
        head <= index < head + count,
    ensures
        page_1g_ptr_prefix(head, count).contains(page_index2page_ptr(index)),
    decreases count,
{
    let last = (head as int + count as int - 1) as usize;
    if index == last { } else { page_1g_ptr_prefix_contains_index(head, (count - 1) as nat, index); }
}

/// The 1G region at `head` lists every page pointer whose index lies inside it.
pub proof fn page_1g_all_ptrs_contains_index(head: PageIndex, index: PageIndex)
    requires
        page_index_1g_valid(head),
        head <= index < head + 262144,
    ensures
        page_1g_all_ptrs(head).contains(page_index2page_ptr(index)),
{
    page_1g_ptr_prefix_contains_index(head, 262144, index);
}

/// A member of a 1G region prefix is a valid page pointer at the head or a merged tail index inside the region.
pub broadcast proof fn page_1g_ptr_prefix_member_bounds(head: PageIndex, count: nat, pg_ptr: PagePtr)
    requires
        page_index_1g_valid(head),
        count <= 262144,
        #[trigger] page_1g_ptr_prefix(head, count).contains(pg_ptr),
    ensures
        page_ptr_valid(pg_ptr),
        head <= page_ptr2page_index(pg_ptr) < head + count,
        page_ptr2page_index(pg_ptr) == head || spec_page_index_merge_1g_valid(head, page_ptr2page_index(pg_ptr)),
        page_ptr2page_index(pg_ptr) == head || page_1g_tail_indices(head).contains(page_ptr2page_index(pg_ptr)),
    decreases count,
{
    assert(count > 0) by { if count == 0 { } };
    let last = (head as int + count as int - 1) as usize;
    if pg_ptr == spec_page_index2page_ptr(last) {
        page_index_valid_imply_page_ptr_valid();
        page_index_roundtrip();
    } else {
        page_1g_ptr_prefix_member_bounds(head, (count - 1) as nat, pg_ptr);
    }
}

/// A container owning a free, owned or mapped 1G head lists every page pointer of that head's 1G region in its owned pages.
pub proof fn container_owned_1g_head_implies_owned_pages_contain_all_ptrs(krnl: &KernelK, head: PageIndex, ctn_ptr: RwLockContainerPtr)
    requires
        krnl.inv(),
        page_index_1g_valid(head),
        krnl.pg_arr.spec_index(head).view().view().state is Free1g || krnl.pg_arr.spec_index(head).view().view().state is Owned1g || krnl.pg_arr.spec_index(head).view().view().state is Mapped1g,
        krnl.pg_arr.spec_index(head).view().view().owning_container == ctn_ptr,
    ensures
        page_1g_all_ptrs(head).subset_of(krnl.ctn_mp.spec_index(ctn_ptr).view().owned_pages.view()),
{
    assert(krnl.ctn_mp.dom().contains(ctn_ptr)) by { reveal(container_owned_pages_wf); };
    assert(page_1g_all_ptrs(head).subset_of(krnl.ctn_mp.spec_index(ctn_ptr).view().owned_pages.view())) by {
        reveal(container_owned_pages_wf); broadcast use page_1g_ptr_prefix_member_bounds;
        page_ptr_roundtrip();
    };
}
}
