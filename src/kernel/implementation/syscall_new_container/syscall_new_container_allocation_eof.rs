use vstd::prelude::*;
use crate::*;

verus! {
/// Result facts of the new-container page allocation from the invariants after it: the staged 2M pages are 2M heads,
/// the staged 4K pages belong to the parent's owned pages, and the thread page is not yet a thread.
pub(super) proof fn allocate_new_container_pages_eof(
    post: KernelK, lctx: &LocalContext, pages_4k: Seq<PagePtr>, perms: Map<PagePtr, LockPerm>, container_page: PagePtr, pcid_allocator_page: PagePtr,
    thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
)
    requires
        post.inv(),
        pages_4k.len() == 9,
        perms.dom() == pages_4k.to_set(),
        allocated_4k_page_lock_perms_wf(perms, &post, lctx, thread_ptr, container_ptr),
        page_ptr_valid(container_page),
        page_ptr_valid(pcid_allocator_page),
        post.pg_arr.spec_index(page_ptr2page_index(container_page)).view().view().state == (PageState::Owned2m { thread_ptr }),
        post.pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().state == (PageState::Owned2m { thread_ptr }),
    ensures
        page_index_2m_valid(page_ptr2page_index(container_page)),
        page_index_2m_valid(page_ptr2page_index(pcid_allocator_page)),
        pages_4k.to_set().subset_of(post.ctn_mp.spec_index(container_ptr).view().owned_pages.view()),
        !post.thr_mp.dom().contains(pages_4k.spec_index(7)),
{
    page_ptr_roundtrip();
    assert(page_index_2m_valid(page_ptr2page_index(container_page)) && page_index_2m_valid(page_ptr2page_index(pcid_allocator_page))) by { reveal(hugepage_2m_wf); };
    assert(pages_4k.to_set().subset_of(post.ctn_mp.spec_index(container_ptr).view().owned_pages.view())) by { pages_4k.to_set_ensures(); reveal(container_page_owner_wf); };
    assert(!post.thr_mp.dom().contains(pages_4k.spec_index(7))) by {
        assert(perms.dom().contains(pages_4k.spec_index(7))) by { pages_4k.to_set_ensures(); };
        reveal(thread_pages_wf);
    };
}
} // verus!
