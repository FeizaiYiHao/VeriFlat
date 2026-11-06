use vstd::prelude::*;

verus! {
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_mmap_2m_spec::mmap_2m_progress_after_leaf;
#[cfg(verus_keep_ghost)]
use super::syscall_mmap_2m_map_owned_eof::{map_owned_2m_page_eof, map_owned_2m_page_eof_transition_framing, map_owned_2m_page_eof_window_frames};

    /// Publish one staged 2M page at the 2M-aligned `va` whose window links no L1 table and holds no leaf.
    ///
    /// The caller holds the page and owner-thread write locks, the target page table's big read lock, and the 2M window of
    /// `va`. Hidden page/thread metadata is updated while the krnl phase is Acquire; the published L2 leaf store into the window
    /// half closes the section into Release. The caller later ends the krnl step, which observes the changed `PageTableU`.
    pub(super) fn map_owned_2m_page(
        krnl: &mut KernelK, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr, Tracked(lctx): Tracked<&mut LocalContext>,
        page_lock_perm: Tracked<&LockPerm>, thread_lock_perm: Tracked<&LockPerm>, pagetable_lock_perm: Tracked<&LockPerm>, window_perm: Tracked<&LockPerm>,
    )
        requires
            old(krnl).inv(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(lctx).kernel_view_locking_state() is Acquire,
            page_ptr_valid(pg_ptr),
            va_2m_valid(va),
            old(krnl).thrd_mp.dom().contains(thrd_ptr),
            old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == false,
            !old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
            !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
            old(krnl).pt_mp.dom().contains(pagetable_ptr),
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned2m { thread_ptr: thrd_ptr }),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_2m.view().contains(pg_ptr),
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_2m >= 1,
            typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write),
            page_lock_perm.view().state() is WriteLock,
            page_lock_perm.view().thread_id() == old(lctx).thread_id(),
            page_lock_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
            thread_lock_perm.view().state() is WriteLock,
            thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
            thread_lock_perm.view().lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
            pagetable_lock_perm.view().state() is ReadLock,
            pagetable_lock_perm.view().thread_id() == old(lctx).thread_id(),
            old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.view().lock_id()),
            !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m().dom().contains(va),
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some,
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_view(window_of(va)).l1_table is None,
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_view(window_of(va)).stale_cpus is None,
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_view(window_of(va)).lock_state
                == (RwLockState::Write { thread_id: window_perm.view().thread_id(), lock_id: window_perm.view().lock_id() }),
            window_perm.view().thread_id() == old(lctx).thread_id(),
            typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable_ptr, window_of(va)), TypedLockMode::Write),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(pg_ptr)), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(pg_ptr)), mode: TypedLockMode::Write }),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write),
            final(krnl).thrd_mp.lock_id_by_key(thrd_ptr) == old(krnl).thrd_mp.lock_id_by_key(thrd_ptr),
            page_lock_perm.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id,
            thread_lock_perm.view().lock_id() == final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
            final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == false,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
            !thread_is_dangling(final(krnl).thrd_mp.spec_index(thrd_ptr)),
            final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread {
                temp_alloc_cache_2m: final(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_2m, quota_2m: final(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_2m,
                syscall_progress: final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view()
            }),
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_2m.view() == old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_2m.view().remove(pg_ptr),
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_2m == old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_2m - 1,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == mmap_2m_progress_after_leaf(old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()),
            final(krnl).pt_mp == old(krnl).pt_mp,
            final(krnl).pt_lower.view() == old(krnl).pt_lower.view().insert(pagetable_ptr, final(krnl).pt_lower.view().spec_index(pagetable_ptr)),
            final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(pg_ptr)),
            final(krnl).thrd_mp.unchanged_except(&old(krnl).thrd_mp, thrd_ptr),
            *final(krnl) == (KernelK { pt_lower: final(krnl).pt_lower, pg_arr: final(krnl).pg_arr, thrd_mp: final(krnl).thrd_mp, ..*old(krnl) }),
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_2m()
                == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m().insert(va,
                    MapEntry { addr: pg_ptr, present: true, write: true, execute_disable: false, owning_container: Ghost(final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container) }),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container,
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k(),
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_1g() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g(),
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks,
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.window_stale_cpus == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.window_stale_cpus,
            forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_owner(p, i)]
                whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_owner(p, i) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.l2_owner(p, i),
            forall|w: WindowVa| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_view(w)]
                spec_va_2m_valid(w.va) && whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(w.va)
                    && whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> {
                    let pre_w = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_view(w);
                    let post_w = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_view(w);
                    &&& post_w.lock_state == pre_w.lock_state
                    &&& post_w.stale_cpus == pre_w.stale_cpus
                    &&& pre_w.l1_table is None ==> post_w.l1_table is None
                },
    {
        let pg_idx = page_ptr2page_index(pg_ptr);
        let indices = va2index(va);
        assert(krnl.pt_mp.perms_wf() && krnl.pt_mp.spec_index(pagetable_ptr).inv() && krnl.pg_arr.inv() && krnl.pg_arr.spec_index(pg_idx).view().inv() && krnl.thrd_mp.perms_wf()
            && krnl.thrd_mp.spec_index(thrd_ptr).inv()) by {
            pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); page_ptr_valid_imply_page_index_valid(); page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, pg_idx);
            thread_perms_wf_map(krnl.thrd_mp); thread_perms_wf_at(krnl.thrd_mp, thrd_ptr);
        };
        let ghost pre_pt = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
        proof {
            pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
            spec_va_2m_valid_index_roundtrip(va);
            hugepage_2m_wf_head_at(krnl.pg_arr, pg_idx);
            assert(page_ptr_2m_valid(pg_ptr)) by (nonlinear_arith) requires pg_ptr % 0x1000 == 0, (pg_ptr / 4096) % 512 == 0, pg_ptr / 4096 < NUM_PAGES;
            pre_pt.higher.wf_l4_at(indices.0);
            pre_pt.l3_links_l2_wf_at(pre_pt.spec_resolve_mapping_l4(indices.0)->0.addr, indices.1);
            pre_pt.higher.spec_resolve_mapping_l3_some_implies_spec_held_l3_eq(indices.0, indices.1);
            pre_pt.wf_l2_at(pre_pt.window_l2_page(indices.0, indices.1), indices.2);
            pre_pt.wf_mapping_2m_at(indices.0, indices.1, indices.2);
            assert(!pre_pt.page_closure().contains(pg_ptr)) by {
                if pre_pt.page_closure().contains(pg_ptr) { pagetable_pages_wf_closure_page_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pagetable_ptr, pg_ptr); }
            };
            pagetable_window_typed_lock_map_aligned_at(krnl.pt_mp, krnl.pt_lower.view(), lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr, window_of(va));
        }
        let target_l2_ptr;
        {
            let pagetable = krnl.pt_mp.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), pagetable_lock_perm);
            let l4_entry = pagetable.get_entry_l4(indices.0).unwrap();
            target_l2_ptr = pagetable.get_entry_l3(indices.0, indices.1, &l4_entry).unwrap().addr;
        }
        zero_2m_page(pg_ptr);
        let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(pg_idx);
        let page_owner;
        {
            let page = krnl.pg_arr.borrow_mut_typed(pg_idx, Ghost(lctx.page_lock_map()), Tracked(&*lctx), page_lock_perm);
            page_owner = page.owning_container;
            page.state = PageState::Mapped2m;
            page.mappings = Ghost(Set::empty().insert((pagetable_ptr, va)));
            page.ref_count = 1;
        } {
            let thread = krnl.thrd_mp.borrow_mut_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), thread_lock_perm);
            thread.temp_alloc_cache_2m = Ghost(thread.temp_alloc_cache_2m.view().remove(pg_ptr));
            thread.quota_2m = thread.quota_2m - 1;
            thread.syscall_progress = Ghost(mmap_2m_progress_after_leaf(thread.syscall_progress.view()));
        }
        let target_entry = MapEntry { addr: pg_ptr, present: true, write: true, execute_disable: false, owning_container: Ghost(page_owner) };
        pagetable_map_insert_2m(&krnl.pt_mp, Tracked(krnl.pt_lower.borrow_mut()), pagetable_ptr, (indices.0, indices.1, indices.2), target_l2_ptr, &target_entry, window_perm, Tracked(&mut *lctx),
            pagetable_lock_perm);
        proof {
            lctx.update_lock_id(KernelObjId::Page(pg_idx), old_page_lock_id, krnl.pg_arr.lock_id_by_index(pg_idx));
            pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
            assert(map_owned_2m_page_eof_transition_framing(*old(krnl), *krnl, pg_ptr, thrd_ptr, pagetable_ptr, va)) by { reveal(map_owned_2m_page_eof_transition_framing); };
            map_owned_2m_page_eof(*old(krnl), *krnl, pg_ptr, thrd_ptr, pagetable_ptr, va);
            map_owned_2m_page_eof_window_frames(*old(krnl), *krnl, pg_ptr, thrd_ptr, pagetable_ptr, va);
        }
    }
}
