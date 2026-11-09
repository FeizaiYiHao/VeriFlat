#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::*;

verus! {
pub open spec fn split_2m_head_eof_transition_framing(pre: Page, post: Page, allocator: RwLockPageAllocatorPtr) -> bool {
    &&& post == (Page { state: PageState::Free4k { allocator_ptr: Ghost(allocator), state: FreePageAllocatorState::GlobalList },
        perm_4k: post.perm_4k, perm_2m: post.perm_2m, ..pre })
    &&& post.perm_2m.view().is_none()
    &&& post.perm_4k.view().is_some()
    &&& post.perm_4k.view().unwrap().is_init()
    &&& post.perm_4k.view().unwrap().addr() == pre.addr
}

pub proof fn split_2m_head_eof_implies_page_inv(pre: Page, post: Page, allocator: RwLockPageAllocatorPtr)
    requires
        pre.inv(),
        pre.state is Free2m,
        split_2m_head_eof_transition_framing(pre, post, allocator),
    ensures
        post.inv(),
{
    assert(post.mappings_va_valid()) by { reveal(Page::mappings_va_valid); };
}

pub open spec fn split_2m_tail_eof_transition_framing(pre: Page, post: Page,
    allocator: RwLockPageAllocatorPtr, owner: RwLockContainerPtr) -> bool {
    &&& post == (Page { state: PageState::Free4k { allocator_ptr: Ghost(allocator), state: FreePageAllocatorState::GlobalList },
        perm_4k: post.perm_4k, owning_container: owner, free_list_node_storage: post.free_list_node_storage, ..pre })
    &&& post.perm_4k.view().is_some()
    &&& post.perm_4k.view().unwrap().is_init()
    &&& post.perm_4k.view().unwrap().addr() == pre.addr
    &&& !post.free_list_node_storage.is_init()
    &&& post.free_list_node_storage.addr() == pre.free_list_node_storage.addr()
}

pub proof fn split_2m_tail_eof_implies_page_inv(pre: Page, post: Page, allocator: RwLockPageAllocatorPtr, owner: RwLockContainerPtr)
    requires
        pre.inv(),
        pre.state is Merged2m,
        split_2m_tail_eof_transition_framing(pre, post, allocator, owner),
    ensures
        post.inv(),
{
    assert(post.mappings_va_valid()) by { reveal(Page::mappings_va_valid); };
}
}
