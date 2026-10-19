use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::transfer_staged_4k_page_eof::{transfer_staged_4k_page_to_child_container_eof_transition_framing, staged_4k_page_container_transfer_eof_inv};

verus! {
/// Moves one staged 4K page owned by `parent_container_ptr` to its child
/// container. Only the page owner and the two `owned_pages` sets change.
pub fn transfer_staged_4k_page_to_child_container(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, page_ptr: PagePtr, staging_thread_ptr: RwLockThreadPtr,
    parent_container_ptr: RwLockContainerPtr, child_container_ptr: RwLockContainerPtr, Tracked(page_lock_perm): Tracked<&LockPerm>,
    Tracked(parent_container_lock_perm): Tracked<&LockPerm>, Tracked(child_container_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), lctx),
        page_ptr_valid(page_ptr),
        parent_container_ptr != child_container_ptr,
        old(krnl).ctn_mp.dom().contains(parent_container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), parent_container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view().contains(page_ptr),
        parent_container_lock_perm.state() is WriteLock,
        parent_container_lock_perm.thread_id() == old(lctx).thread_id(),
        parent_container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(child_container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), child_container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(child_container_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata().view().parent == Some(parent_container_ptr),
        child_container_lock_perm.state() is WriteLock,
        child_container_lock_perm.thread_id() == old(lctx).thread_id(),
        child_container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(child_container_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(staging_thread_ptr),
        old(krnl).thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        !old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed(),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == parent_container_ptr,
        page_lock_perm.state() is WriteLock,
        page_lock_perm.thread_id() == old(lctx).thread_id(),
        page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        *final(lctx) == *old(lctx),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(page_ptr)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == child_container_ptr,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        !final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed(),
        page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
        final(krnl).ctn_mp.dom() == old(krnl).ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(c)]
            old(krnl).ctn_mp.dom().contains(c) && c != parent_container_ptr && c != child_container_ptr ==> final(krnl).ctn_mp.spec_index(c) == old(krnl).ctn_mp.spec_index(c),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).is_init() == old(krnl).ctn_mp.spec_index(parent_container_ptr).is_init(),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(parent_container_ptr).view_rodata(),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view_ghost() == old(krnl).ctn_mp.spec_index(parent_container_ptr).view_ghost(),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread() == old(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread(),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed() == old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).killer_info() == old(krnl).ctn_mp.spec_index(parent_container_ptr).killer_info(),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view() == (Container { owned_pages: final(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_pages, ..old(krnl).ctn_mp.spec_index(parent_container_ptr).view() }),
        final(krnl).ctn_mp.spec_index(child_container_ptr).is_init() == old(krnl).ctn_mp.spec_index(child_container_ptr).is_init(),
        final(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata(),
        final(krnl).ctn_mp.spec_index(child_container_ptr).view_ghost() == old(krnl).ctn_mp.spec_index(child_container_ptr).view_ghost(),
        final(krnl).ctn_mp.spec_index(child_container_ptr).locking_thread() == old(krnl).ctn_mp.spec_index(child_container_ptr).locking_thread(),
        final(krnl).ctn_mp.spec_index(child_container_ptr).being_killed() == old(krnl).ctn_mp.spec_index(child_container_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(child_container_ptr).killer_info() == old(krnl).ctn_mp.spec_index(child_container_ptr).killer_info(),
        final(krnl).ctn_mp.spec_index(child_container_ptr).view() == (Container { owned_pages: final(krnl).ctn_mp.spec_index(child_container_ptr).view().owned_pages, ..old(krnl).ctn_mp.spec_index(child_container_ptr).view() }),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view() =~= old(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view().remove(page_ptr),
        final(krnl).ctn_mp.spec_index(child_container_ptr).view().owned_pages.view() =~= old(krnl).ctn_mp.spec_index(child_container_ptr).view().owned_pages.view().insert(page_ptr),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), parent_container_ptr, TypedLockMode::Write),
        !final(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), child_container_ptr, TypedLockMode::Write),
        !final(krnl).ctn_mp.spec_index(child_container_ptr).being_killed(),
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, ctn_mp: final(krnl).ctn_mp, ..*old(krnl) }),
{
    let ghost pre = *krnl;
    let page_index = page_ptr2page_index(page_ptr);
    proof {
        assert(index_valid(NUM_PAGES, page_index)) by { page_ptr_valid_imply_page_index_valid(); };
        page_array_wf_map(krnl.pg_arr);
        page_array_wf_at(krnl.pg_arr, page_index);
        container_perms_wf_at(krnl.ctn_mp, parent_container_ptr); container_perms_wf_map(krnl.ctn_mp); container_perms_wf_at(krnl.ctn_mp, child_container_ptr);
    }
    let page = krnl.pg_arr.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(page_lock_perm));
    page.owning_container = child_container_ptr;
    let parent = krnl.ctn_mp.borrow_mut_typed(parent_container_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(parent_container_lock_perm));
    parent.owned_pages = Ghost(parent.owned_pages.view().remove(page_ptr));
    let child = krnl.ctn_mp.borrow_mut_typed(child_container_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(child_container_lock_perm));
    child.owned_pages = Ghost(child.owned_pages.view().insert(page_ptr));
    proof {
        assert(transfer_staged_4k_page_to_child_container_eof_transition_framing(pre, *krnl, page_ptr, staging_thread_ptr, parent_container_ptr, child_container_ptr)) by { reveal(transfer_staged_4k_page_to_child_container_eof_transition_framing); };
        staged_4k_page_container_transfer_eof_inv(pre, *krnl, page_ptr, staging_thread_ptr, parent_container_ptr, child_container_ptr);
    }
}
} // verus!
