#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::*;

verus! {
pub open spec fn merge_2m_tail_eof_transition_framing(pre: Page, post: Page) -> bool {
    &&& post == (Page { state: PageState::Merged2m, perm_4k: post.perm_4k,
        free_list_node_storage: post.free_list_node_storage, ..pre })
    &&& post.perm_4k.view().is_none()
    &&& post.free_list_node_storage.is_init()
    &&& post.free_list_node_storage.addr() == pre.free_list_node_storage.addr()
}

pub proof fn merge_2m_tail_eof_implies_page_inv(pre: Page, post: Page)
    requires
        pre.inv(),
        pre.state is Free4k,
        merge_2m_tail_eof_transition_framing(pre, post),
    ensures
        post.inv(),
{
    assert(post.mappings_va_valid()) by { reveal(Page::mappings_va_valid); };
}

pub open spec fn merge_2m_head_eof_transition_framing(pre: Page, post: Page, allocator: RwLockPageAllocatorPtr) -> bool {
    &&& post == (Page { state: PageState::Free2m { allocator_ptr: Ghost(allocator), state: FreePageAllocatorState::GlobalList },
        perm_4k: post.perm_4k, perm_2m: post.perm_2m, ..pre })
    &&& post.perm_4k.view().is_none()
    &&& post.perm_2m.view().is_some()
    &&& post.perm_2m.view().unwrap().is_init()
    &&& post.perm_2m.view().unwrap().addr() == pre.addr
}

pub proof fn merge_2m_head_eof_implies_page_inv(pre: Page, post: Page, allocator: RwLockPageAllocatorPtr)
    requires
        pre.inv(),
        pre.state is Free4k,
        merge_2m_head_eof_transition_framing(pre, post, allocator),
    ensures
        post.inv(),
{
    assert(post.mappings_va_valid()) by { reveal(Page::mappings_va_valid); };
}
}
