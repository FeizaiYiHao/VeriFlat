use vstd::prelude::*;

verus! {
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_mmap_1g_spec::mmap_1g_progress_after_leaf;
#[cfg(verus_keep_ghost)]
use super::syscall_mmap_1g_map_owned_eof::{map_owned_1g_page_eof, map_owned_1g_page_eof_transition_framing};

    /// Publish one staged 1G page at the 1G-aligned `va` whose L3 entry links no L2 page and holds no leaf.
    ///
    /// The caller holds the page and owner-thread write locks and the target page table's big write lock. Hidden page/thread
    /// metadata is updated while the krnl phase is Acquire; the published L3 leaf store into the big-lock payload closes the
    /// section into Release. The caller later ends the krnl step, which observes the changed `PageTableU`.
    pub(super) fn map_owned_1g_page(
        krnl: &mut KernelK, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr, Tracked(lctx): Tracked<&mut LocalContext>,
        page_lock_perm: Tracked<&LockPerm>, thread_lock_perm: Tracked<&LockPerm>, pagetable_lock_perm: Tracked<&LockPerm>,
    )
        requires
            old(krnl).inv(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(lctx).kernel_view_locking_state() is Acquire,
            page_ptr_valid(pg_ptr),
            va_1g_valid(va),
            old(krnl).thrd_mp.dom().contains(thrd_ptr),
            old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == false,
            !old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
            !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
            old(krnl).pt_mp.dom().contains(pagetable_ptr),
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned1g { thread_ptr: thrd_ptr }),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g.view().contains(pg_ptr),
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_1g >= 1,
            typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write),
            page_lock_perm.view().state() is WriteLock,
            page_lock_perm.view().thread_id() == old(lctx).thread_id(),
            page_lock_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
            thread_lock_perm.view().state() is WriteLock,
            thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
            thread_lock_perm.view().lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            pagetable_lock_perm.view().state() is WriteLock,
            pagetable_lock_perm.view().thread_id() == old(lctx).thread_id(),
            pagetable_lock_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g().dom().contains(va),
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(spec_v2l4index(va)) is Some,
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_held_l3(spec_v2l4index(va), spec_v2l3index(va)) is None,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(krnl).inv(),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(pg_ptr)), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(pg_ptr)), mode: TypedLockMode::Write }),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write),
            page_lock_perm.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id,
            final(krnl).thrd_mp.lock_id_by_key(thrd_ptr) == old(krnl).thrd_mp.lock_id_by_key(thrd_ptr),
            thread_lock_perm.view().lock_id() == final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
            final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == false,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
            !thread_is_dangling(final(krnl).thrd_mp.spec_index(thrd_ptr)),
            final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread {
                temp_alloc_cache_1g: final(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g, quota_1g: final(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_1g,
                syscall_progress: final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view()
            }),
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g.view() == old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g.view().remove(pg_ptr),
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_1g == old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_1g - 1,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == mmap_1g_progress_after_leaf(old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()),
            *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pg_arr: final(krnl).pg_arr, thrd_mp: final(krnl).thrd_mp, ..*old(krnl) }),
            final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, pagetable_ptr),
            final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread() == old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).being_killed() == old(krnl).pt_mp.spec_index(pagetable_ptr).being_killed(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr == old(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().table_stale_cpus == old(krnl).pt_mp.spec_index(pagetable_ptr).view().table_stale_cpus,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().cr3 == old(krnl).pt_mp.spec_index(pagetable_ptr).view().cr3,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().pcid == old(krnl).pt_mp.spec_index(pagetable_ptr).view().pcid,
            final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(pg_ptr)),
            final(krnl).thrd_mp.unchanged_except(&old(krnl).thrd_mp, thrd_ptr),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container,
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_1g()
                == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g().insert(va,
                    MapEntry { addr: pg_ptr, present: true, write: true, execute_disable: false, owning_container: Ghost(final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container) }),
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k(),
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_2m() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m(),
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower,
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).page_closure() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).page_closure(),
            forall|l4i: L4Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(l4i)]
                whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i)
                    ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(l4i) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(l4i),
            forall|l4i: L4Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_l4(l4i)]
                whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i)
                    ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_l4(l4i) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_held_l4(l4i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i)]
                whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i)
                    ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_l3(l4i, l3i)]
                whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i)
                    ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_l3(l4i, l3i) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_held_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_1g_l3(l4i, l3i)]
                whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (spec_v2l4index(va), spec_v2l3index(va))
                    ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_1g_l3(l4i, l3i) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_held_1g_l3(l4i, l3i),
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some,
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr == pg_ptr,
    {
        let pg_idx = page_ptr2page_index(pg_ptr);
        let l4i = v2l4index(va);
        let l3i = v2l3index(va);
        assert(krnl.pt_mp.perms_wf() && krnl.pt_mp.spec_index(pagetable_ptr).inv() && krnl.pg_arr.inv() && krnl.pg_arr.spec_index(pg_idx).view().inv() && krnl.thrd_mp.perms_wf()
            && krnl.thrd_mp.spec_index(thrd_ptr).inv()) by {
            pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); page_ptr_valid_imply_page_index_valid(); page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, pg_idx);
            thread_perms_wf_map(krnl.thrd_mp); thread_perms_wf_at(krnl.thrd_mp, thrd_ptr);
        };
        let ghost pre_pt = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
        proof {
            spec_va_1g_valid_index_roundtrip(va);
            hugepage_1g_wf_head_at(krnl.pg_arr, pg_idx);
            assert(page_ptr_1g_valid(pg_ptr)) by (nonlinear_arith) requires pg_ptr % 0x1000 == 0, (pg_ptr / 4096) % 262144 == 0, pg_ptr / 4096 < NUM_PAGES;
            assert(!pre_pt.page_closure().contains(pg_ptr)) by {
                if pre_pt.page_closure().contains(pg_ptr) { pagetable_pages_wf_closure_page_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pagetable_ptr, pg_ptr); }
            };
        }
        let target_l3_ptr;
        {
            let pagetable = krnl.pt_mp.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), pagetable_lock_perm);
            target_l3_ptr = pagetable.get_entry_l4(l4i).unwrap().addr;
        }
        zero_1g_page(pg_ptr);
        let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(pg_idx);
        let page_owner;
        {
            let page = krnl.pg_arr.borrow_mut_typed(pg_idx, Ghost(lctx.page_lock_map()), Tracked(&*lctx), page_lock_perm);
            page_owner = page.owning_container;
            page.state = PageState::Mapped1g;
            page.mappings = Ghost(Set::empty().insert((pagetable_ptr, va)));
            page.ref_count = 1;
        } {
            let thread = krnl.thrd_mp.borrow_mut_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), thread_lock_perm);
            thread.temp_alloc_cache_1g = Ghost(thread.temp_alloc_cache_1g.view().remove(pg_ptr));
            thread.quota_1g = thread.quota_1g - 1;
            thread.syscall_progress = Ghost(mmap_1g_progress_after_leaf(thread.syscall_progress.view()));
        }
        let target_entry = MapEntry { addr: pg_ptr, present: true, write: true, execute_disable: false, owning_container: Ghost(page_owner) };
        pagetable_map_insert_1g(&mut krnl.pt_mp, Tracked(krnl.pt_lower.borrow()), pagetable_ptr, (l4i, l3i), target_l3_ptr, &target_entry, Tracked(&mut *lctx), pagetable_lock_perm);
        proof {
            lctx.update_lock_id(KernelObjId::Page(pg_idx), old_page_lock_id, krnl.pg_arr.lock_id_by_index(pg_idx));
            assert(map_owned_1g_page_eof_transition_framing(*old(krnl), *krnl, pg_ptr, thrd_ptr, pagetable_ptr, va)) by { reveal(map_owned_1g_page_eof_transition_framing); };
            map_owned_1g_page_eof(*old(krnl), *krnl, pg_ptr, thrd_ptr, pagetable_ptr, va);
        }
    }
}
