use vstd::prelude::*;

verus! {
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_mmap_4k_spec::mmap_4k_progress_after_leaf;
#[cfg(verus_keep_ghost)]
use super::mmap_4k_map_owned_eof::{map_owned_4k_page_eof, map_owned_4k_page_eof_transition_framing};

    /// Publish one staged 4K page at a fresh virtual address whose L1 table
    /// already exists.
    ///
    /// The caller holds the page and owner-thread write locks, the target page
    /// table's big read lock, and the 2M window of `va`. The thread lock is
    /// needed because mapping consumes the page from its temporary allocation
    /// cache and charges its quota. Hidden page/thread metadata is updated while
    /// the krnl phase is Acquire; the published PTE store into the window half
    /// closes the section into Release. The caller later ends the krnl step,
    /// which observes the changed `PageTableU` and records exactly one
    /// non-stuttering transition.
    pub(super) fn map_owned_4k_page(
        krnl: &mut KernelK, page_ptr: PagePtr, thread_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr, Tracked(lctx): Tracked<&mut LocalContext>,
        page_lock_perm: Tracked<&LockPerm>, thread_lock_perm: Tracked<&LockPerm>, pagetable_lock_perm: Tracked<&LockPerm>,
    )
        requires
            old(krnl).inv(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(lctx).kernel_view_locking_state() is Acquire,
            page_ptr_valid(page_ptr),
            va_4k_valid(va),
            old(krnl).thr_mp.dom().contains(thread_ptr),
            old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
            !thread_is_dangling(old(krnl).thr_mp.spec_index(thread_ptr)),
            old(krnl).pt_mp.dom().contains(pagetable_ptr),
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_va2index(va).0,
            pei_valid(spec_va2index(va).0),
            pei_valid(spec_va2index(va).1),
            pei_valid(spec_va2index(va).2),
            pei_valid(spec_va2index(va).3),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr }),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container,
            old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable_ptr,
            old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr),
            old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k >= 1,
            typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
            page_lock_perm.view().state() is WriteLock,
            page_lock_perm.view().thread_id() == old(lctx).thread_id(),
            page_lock_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
            thread_lock_perm.view().state() is WriteLock,
            thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
            thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
            pagetable_lock_perm.view().state() is ReadLock,
            pagetable_lock_perm.view().thread_id() == old(lctx).thread_id(),
            old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.view().lock_id()),
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(va) == false,
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2) is Some,
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_locked_by_thread(spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2, old(lctx).thread_id()),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(page_ptr)), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write, }),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
            typed_lock_map_contains_mode(final(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
            final(krnl).thr_mp.lock_id_by_key(thread_ptr) == old(krnl).thr_mp.lock_id_by_key(thread_ptr),
            page_lock_perm.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
            thread_lock_perm.view().lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container,
            final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().is_io_page == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().is_io_page,
            final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().free_list_node_storage == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().free_list_node_storage,
            final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().free_list == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().free_list,
            final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            !thread_is_dangling(final(krnl).thr_mp.spec_index(thread_ptr)),
            final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread {
                temp_alloc_cache_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k,
                quota_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k,
                syscall_progress: final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress,
                ..old(krnl).thr_mp.spec_index(thread_ptr).view()
            }),
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().remove(page_ptr),
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k - 1,
            final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == mmap_4k_progress_after_leaf(old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()),
            final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
            !final(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
            final(krnl).pt_mp == old(krnl).pt_mp,
            final(krnl).pt_lower.view() == old(krnl).pt_lower.view().insert(pagetable_ptr, final(krnl).pt_lower.view().spec_index(pagetable_ptr)),
            final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(page_ptr)),
            final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, thread_ptr),
            *final(krnl) == (KernelK { pt_lower: final(krnl).pt_lower, pg_arr: final(krnl).pg_arr, thr_mp: final(krnl).thr_mp, ..*old(krnl) }),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == PageState::Mapped4k,
            final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().perm_4k.view() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().perm_4k.view(),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().mappings() == Set::empty().insert((pagetable_ptr, va)),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count == 1,
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k()
                == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().insert(va,
                    MapEntry { addr: page_ptr, present: true, write: true, execute_disable: false, owning_container: Ghost(final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container), }),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).page_closure() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).page_closure(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_lock == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.l2_lock,
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.window_stale_cpus == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.window_stale_cpus,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
                #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id)
                    == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_locked_by_thread(l4i, l3i, l2i, thread_id),
    {
        let page_index = page_ptr2page_index(page_ptr);
        let indices = va2index(va);
        assert(krnl.pt_mp.perms_wf() && krnl.pt_mp.spec_index(pagetable_ptr).inv() && krnl.pg_arr.inv() && krnl.pg_arr.spec_index(page_index).view().inv() && krnl.thr_mp.perms_wf()
            && krnl.thr_mp.spec_index(thread_ptr).inv()) by {
            pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); page_ptr_valid_imply_page_index_valid(); page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, page_index);
            thread_perms_wf_map(krnl.thr_mp); thread_perms_wf_at(krnl.thr_mp, thread_ptr);
        };
        proof {
            pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
            assert(spec_index2va(indices) == va) by { spec_va_4k_index_roundtrip_at(va, indices.0, indices.1, indices.2, indices.3); };
        }
        let target_l1_ptr;
        {
            let pagetable = krnl.pt_mp.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), pagetable_lock_perm);
            let tracked lower = krnl.pt_lower.borrow().tracked_borrow(pagetable_ptr);
            target_l1_ptr = pagetable.resolve_mapping_4k_l2(Tracked(lower), indices.0, indices.1, indices.2).0.unwrap().addr;
        }

        let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
        let page_owner;
        {
            let page = krnl.pg_arr.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), page_lock_perm);
            page_owner = page.owning_container;
            page.state = PageState::Mapped4k;
            page.mappings = Ghost(Set::empty().insert((pagetable_ptr, va)));
            page.ref_count = 1;
        } {
            let thread = krnl.thr_mp.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), thread_lock_perm);
            thread.temp_alloc_cache_4k = Ghost(thread.temp_alloc_cache_4k.view().remove(page_ptr));
            thread.quota_4k = thread.quota_4k - 1;
            thread.syscall_progress = Ghost(mmap_4k_progress_after_leaf(thread.syscall_progress.view()));
        }
        let target_entry = MapEntry { addr: page_ptr, present: true, write: true, execute_disable: false, owning_container: Ghost(page_owner) };
        pagetable_map_insert_4k(&krnl.pt_mp, Tracked(krnl.pt_lower.borrow_mut()), pagetable_ptr, indices, target_l1_ptr, &target_entry, Tracked(&mut *lctx), pagetable_lock_perm);
        proof {
            lctx.update_lock_id(KernelObjId::Page(page_index), old_page_lock_id, krnl.pg_arr.lock_id_by_index(page_index));
            assert(map_owned_4k_page_eof_transition_framing(*old(krnl), *krnl, page_ptr, thread_ptr, pagetable_ptr, va)) by { reveal(map_owned_4k_page_eof_transition_framing); };
            map_owned_4k_page_eof(*old(krnl), *krnl, page_ptr, thread_ptr, pagetable_ptr, va);
        }
    }
}
