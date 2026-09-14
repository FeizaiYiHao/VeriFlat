use vstd::prelude::*;
use crate::*;

verus! {
#[verifier::opaque]
pub open spec fn transfer_staged_page_preserved_objects_transition_framing(
    pre: KernelK, post: KernelK, page_ptr: PagePtr,
    staging_thread_ptr: RwLockThreadPtr,
    parent: RwLockContainerPtr, child: RwLockContainerPtr,
) -> bool {
    let page_index = page_ptr2page_index(page_ptr);
    let old_page = pre.pg_arr.spec_index(page_index).view();
    let new_page = post.pg_arr.spec_index(page_index).view();
    &&& page_ptr_valid(page_ptr)
    &&& parent != child
    &&& pre.ctn_mp.dom().contains(parent)
    &&& pre.ctn_mp.dom().contains(child)
    &&& pre.ctn_mp.spec_index(parent).view().owned_pages.view().contains(page_ptr)
    &&& pre.ctn_mp.spec_index(child).view_rodata().view().parent == Some(parent)
    &&& pre.thr_mp.dom().contains(staging_thread_ptr)
    &&& pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr)
    &&& old_page.view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr })
    &&& old_page.view().owning_container == parent
    &&& post == (KernelK { pg_arr: post.pg_arr, ctn_mp: post.ctn_mp, ..pre })
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_index)
    &&& forall|j: PageIndex|
        #![trigger pre.pg_arr.spec_index(j).view().view().state]
        #![trigger post.pg_arr.spec_index(j).view().view().state]
        index_valid(NUM_PAGES, j) ==> {
            &&& post.pg_arr.spec_index(j).view().view().state == pre.pg_arr.spec_index(j).view().view().state
            &&& post.pg_arr.spec_index(j).view().view().mappings() == pre.pg_arr.spec_index(j).view().view().mappings()
            &&& (j != page_index ==> post.pg_arr.spec_index(j).view().view().owning_container == pre.pg_arr.spec_index(j).view().view().owning_container)
        }
    &&& new_page.is_init() == old_page.is_init()
    &&& new_page.view_rodata() == old_page.view_rodata()
    &&& new_page.view_ghost() == old_page.view_ghost()
    &&& new_page.locking_thread() == old_page.locking_thread()
    &&& new_page.being_killed() == old_page.being_killed()
    &&& new_page.view() == (Page { owning_container: child, ..old_page.view() })
    &&& post.ctn_mp.dom() == pre.ctn_mp.dom()
    &&& forall|c: RwLockContainerPtr|
        #![trigger pre.ctn_mp.spec_index(c)]
        #![trigger post.ctn_mp.spec_index(c)]
        pre.ctn_mp.dom().contains(c) ==> {
            let old_container = pre.ctn_mp.spec_index(c);
            let new_container = post.ctn_mp.spec_index(c);
            &&& post.ctn_mp.view().spec_index(c).is_init() == pre.ctn_mp.view().spec_index(c).is_init()
            &&& post.ctn_mp.view().spec_index(c).addr() == pre.ctn_mp.view().spec_index(c).addr()
            &&& (c != parent && c != child ==> new_container == old_container)
            &&& (c == parent || c == child ==> {
                &&& new_container.is_init() == old_container.is_init()
                &&& new_container.view_rodata() == old_container.view_rodata()
                &&& new_container.view_ghost() == old_container.view_ghost()
                &&& new_container.locking_thread() == old_container.locking_thread()
                &&& new_container.being_killed() == old_container.being_killed()
                &&& new_container.view() == (Container {
                    owned_pages: Ghost(if c == parent {
                        old_container.view().owned_pages.view().remove(page_ptr)
                    } else {
                        old_container.view().owned_pages.view().insert(page_ptr)
                    }),
                    ..old_container.view()
                })
            })
        }
}
}
