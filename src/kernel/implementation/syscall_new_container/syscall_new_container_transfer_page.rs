use vstd::prelude::*;
use crate::*;
use super::syscall_new_container_transfer_eof::staged_4k_page_container_transfer_eof;
use super::syscall_new_container_transfer_spec::staged_4k_page_container_transfer_transition;
use super::*;

verus! {
#[verifier::rlimit(120)]
#[verifier::spinoff_prover]
pub(super) fn transfer_staged_thread_page_to_child(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, page_ptr: PagePtr,
    staging_thread_ptr: RwLockThreadPtr, parent_container_ptr: RwLockContainerPtr,
    child_container_ptr: RwLockContainerPtr, Tracked(page_lock_perm): Tracked<&LockPerm>,
    Tracked(parent_container_lock_perm): Tracked<&LockPerm>, Tracked(child_container_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        lctx.kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), lctx),
        lock_id_set_aligned(lctx),
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
        lock_id_set_aligned(final(lctx)),
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(page_ptr)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == child_container_ptr,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        !final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed(),
        page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
        final(krnl).ctn_mp.dom() == old(krnl).ctn_mp.dom(),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view() =~= old(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view().remove(page_ptr),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_processes == old(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_processes,
        final(krnl).ctn_mp.spec_index(child_container_ptr).view().owned_pages.view() =~= old(krnl).ctn_mp.spec_index(child_container_ptr).view().owned_pages.view().insert(page_ptr),
        final(krnl).ctn_mp.spec_index(child_container_ptr).view().owned_processes == old(krnl).ctn_mp.spec_index(child_container_ptr).view().owned_processes,
        final(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata().view().scheduler == old(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata().view().scheduler,
        final(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata().view().allocator_ptr_4k == old(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata().view().allocator_ptr_4k,
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), parent_container_ptr, TypedLockMode::Write),
        !final(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        parent_container_lock_perm.lock_id() == final(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), child_container_ptr, TypedLockMode::Write),
        !final(krnl).ctn_mp.spec_index(child_container_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata().view().parent == Some(parent_container_ptr),
        child_container_lock_perm.lock_id() == final(krnl).ctn_mp.spec_index(child_container_ptr).locking_thread()->Write_lock_id,
        *final(krnl) == (KernelK {
            pg_arr: final(krnl).pg_arr,
            ctn_mp: final(krnl).ctn_mp,
            ..*old(krnl)
        }),
{
    let ghost pre = *krnl;
    let page_index = page_ptr2page_index(page_ptr);
    proof {
        page_ptr_valid_imply_page_index_valid();
        assert(krnl.pg_arr.inv()) by { reveal(page_array_wf); };
        assert(krnl.pg_arr.spec_index(page_index).view().is_init()) by { reveal(page_array_wf); };
        assert(krnl.ctn_mp.perms_wf()) by { reveal(container_perms_wf); };
        assert(krnl.ctn_mp.spec_index(parent_container_ptr).is_init() && krnl.ctn_mp.spec_index(child_container_ptr).is_init()) by { reveal(container_perms_wf); };
        assert(old(krnl).pg_arr.spec_index(page_index).view().view().inv()) by { reveal(page_array_wf); };
        assert(old(krnl).ctn_mp.spec_index(parent_container_ptr).view().inv() && old(krnl).ctn_mp.spec_index(child_container_ptr).view().inv()) by {
            reveal(container_perms_wf);
            reveal(containers_inv);
        };
    }
    {
        let page = krnl.pg_arr.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(page_lock_perm));
        page.owning_container = child_container_ptr;
        proof {
            assert(page.inv()) by {
                assert(old(krnl).pg_arr.spec_index(page_index).view().view().inv()) by { reveal(page_array_wf); };
                reveal(Page::mappings_va_valid);
                reveal(Page::mappings_finite);
                reveal(Page::ref_count_inv);
                reveal(Page::mapped_state_inv);
                reveal(Page::node_storage_inv);
                reveal(Page::free_state_inv);
                reveal(Page::perm_inv);
            };
        }
    }
    {
        let parent = krnl.ctn_mp.borrow_mut_typed(parent_container_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(parent_container_lock_perm));
        parent.owned_pages = Ghost(parent.owned_pages.view().remove(page_ptr));
        proof {
            assert(parent.inv()) by {
                assert(old(krnl).ctn_mp.spec_index(parent_container_ptr).view().inv()) by {
                    reveal(container_perms_wf);
                    reveal(containers_inv);
                };
                reveal(Container::wf);
            };
        }
    }
    {
        proof {
            assert(krnl.ctn_mp.spec_index(child_container_ptr).is_init()) by { reveal(container_perms_wf); };
        }
        let child = krnl.ctn_mp.borrow_mut_typed(child_container_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(child_container_lock_perm));
        child.owned_pages = Ghost(child.owned_pages.view().insert(page_ptr));
        proof {
            assert(child.inv()) by {
                assert(old(krnl).ctn_mp.spec_index(child_container_ptr).view().inv()) by {
                    reveal(container_perms_wf);
                    reveal(containers_inv);
                };
                reveal(Container::wf);
            };
        }
    }
    proof {
        assert(staged_4k_page_container_transfer_transition(pre, *krnl, page_ptr, staging_thread_ptr, parent_container_ptr, child_container_ptr)) by {
            reveal(staged_4k_page_container_transfer_transition);
        };
        staged_4k_page_container_transfer_eof(pre, *krnl, page_ptr, staging_thread_ptr, parent_container_ptr, child_container_ptr);
    }

}


}
