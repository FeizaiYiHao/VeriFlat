use vstd::prelude::*;
verus! {
use crate::*;

/// EOF closure of `retype_page_to_process_and_insert`: inserting the write-held process `page_ptr` keeps `process_perms_wf`.
pub(super) proof fn retype_page_to_process_and_insert_eof(pre: ProcessLockedMap, post: ProcessLockedMap, page_ptr: RwLockProcessPtr, process_value: Process, rodata: ReadOnlyNode<ProcessRO>, process_ghost: ProcessGhost)
    requires
        process_value.inv(),
        process_value.children.view().no_duplicates(),
        !process_value.children.view().contains(page_ptr),
        process_ghost.uppertree_seq.view().no_duplicates(),
        process_ghost.uppertree_seq.view().len() == rodata.view().depth,
        post.perms_wf(),
        post.dom() =~= pre.dom().insert(page_ptr),
        forall|ptr: RwLockProcessPtr|
            #![trigger post.spec_index(ptr)]
            #![trigger pre.spec_index(ptr)]
            #![trigger pre.dom().contains(ptr)]
            #![trigger post.dom().contains(ptr)]
            pre.dom().contains(ptr) ==> post.spec_index(ptr) == pre.spec_index(ptr),
        post.spec_index(page_ptr).is_init(),
        post.spec_index(page_ptr).locking_thread() is Write,
        post.spec_index(page_ptr).view() == process_value,
        post.spec_index(page_ptr).view_rodata() == rodata,
        post.spec_index(page_ptr).view_ghost() == process_ghost,
    ensures process_perms_wf(pre) ==> process_perms_wf(post),
{ reveal(process_perms_wf); }

/// EOF closure of `remove_process_and_reclaim_4k_page_perm`: removing process `process_ptr` keeps `process_perms_wf`.
pub(super) proof fn remove_process_and_reclaim_4k_page_perm_eof(pre: ProcessLockedMap, post: ProcessLockedMap, process_ptr: RwLockProcessPtr)
    requires
        post.perms_wf(),
        post.dom() =~= pre.dom().remove(process_ptr),
        forall|p: RwLockProcessPtr| #![trigger post.spec_index(p)] post.dom().contains(p) ==> post.spec_index(p) == pre.spec_index(p),
    ensures process_perms_wf(pre) ==> process_perms_wf(post),
{ reveal(process_perms_wf); }
} // verus!
