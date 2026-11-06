use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_mmap_1g_spec::mmap_1g_progress_after_leaf;

verus! {
/// Publishes the staged 1G page `pg_ptr` of `thrd_ptr` at `va` in the big-lock payload of `pagetable_ptr`: the page becomes mapped once, the thread consumes it from its 1G cache and quota and advances its mmap progress, the empty L3 entry of `va` becomes a present 1G leaf while every
/// other resolved or held entry and every other field of the table stay; every other kernel field is unchanged.
#[verifier::opaque]
pub(super) open spec fn map_owned_1g_page_eof_transition_framing(pre: KernelK, post: KernelK, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr) -> bool {
    let pg_idx = page_ptr2page_index(pg_ptr);
    let old_h = pre.pt_mp.spec_index(pagetable_ptr).view();
    let new_h = post.pt_mp.spec_index(pagetable_ptr).view();
    let old_pt = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr);
    let new_pt = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr);
    let old_page = pre.pg_arr.spec_index(pg_idx).view();
    let new_page = post.pg_arr.spec_index(pg_idx).view();
    let old_thread = pre.thrd_mp.spec_index(thrd_ptr);
    let new_thread = post.thrd_mp.spec_index(thrd_ptr);
    let target = (spec_v2l4index(va), spec_v2l3index(va));
    let leaf = PageEntry { addr: pg_ptr, perm: PageEntryPerm { present: true, ps: true, write: true, execute_disable: false, user: true, kernel_present: true } };
    &&& post == (KernelK { pt_mp: post.pt_mp, pg_arr: post.pg_arr, thrd_mp: post.thrd_mp, ..pre })
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr)
    &&& forall|p: RwLockPageTableRoot| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), p)]
        pre.pt_mp.dom().contains(p) && p != pagetable_ptr ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), p) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), p)
    &&& post.pt_mp.lock_id_by_key(pagetable_ptr) == pre.pt_mp.lock_id_by_key(pagetable_ptr)
    &&& post.pt_mp.spec_index(pagetable_ptr).locking_thread() == pre.pt_mp.spec_index(pagetable_ptr).locking_thread()
    &&& post.pt_mp.spec_index(pagetable_ptr).being_killed() == pre.pt_mp.spec_index(pagetable_ptr).being_killed()
    &&& post.pt_mp.spec_index(pagetable_ptr).view_ghost() == pre.pt_mp.spec_index(pagetable_ptr).view_ghost()
    &&& new_h.table_stale_cpus == old_h.table_stale_cpus && new_h.kernel_l4_end == old_h.kernel_l4_end && new_h.kernel_entries == old_h.kernel_entries
    &&& new_h.cr3 == old_h.cr3 && new_h.pcid == old_h.pcid && new_h.did == old_h.did && new_h.proc_ptr == old_h.proc_ptr
    &&& new_h.l4_table == old_h.l4_table && new_h.l3_rev_map == old_h.l3_rev_map && new_h.l2_rev_map == old_h.l2_rev_map
    &&& new_pt.mapping_4k() == old_pt.mapping_4k()
    &&& new_pt.mapping_2m() == old_pt.mapping_2m()
    &&& new_pt.page_closure() == old_pt.page_closure()
    &&& new_pt.mapping_1g() == old_pt.mapping_1g().insert(va, MapEntry { addr: pg_ptr, present: true, write: true, execute_disable: false, owning_container: Ghost(old_page.view().owning_container) })
    &&& forall|i4: L4Index| #![trigger new_pt.spec_resolve_mapping_l4(i4)] old_pt.kernel_l4_end() <= i4 && pei_valid(i4) ==> new_pt.spec_resolve_mapping_l4(i4) == old_pt.spec_resolve_mapping_l4(i4)
    &&& forall|i4: L4Index, i3: L3Index| #![trigger new_pt.spec_resolve_mapping_l3(i4, i3)]
        old_pt.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) ==> new_pt.spec_resolve_mapping_l3(i4, i3) == old_pt.spec_resolve_mapping_l3(i4, i3)
    &&& forall|i4: L4Index, i3: L3Index| #![trigger new_pt.spec_resolve_mapping_1g_l3(i4, i3)]
        old_pt.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && (i4, i3) != target ==> new_pt.spec_resolve_mapping_1g_l3(i4, i3) == old_pt.spec_resolve_mapping_1g_l3(i4, i3)
    &&& forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger new_pt.spec_resolve_mapping_l2(i4, i3, i2)]
        old_pt.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) ==> new_pt.spec_resolve_mapping_l2(i4, i3, i2) == old_pt.spec_resolve_mapping_l2(i4, i3, i2)
    &&& forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger new_pt.spec_resolve_mapping_2m_l2(i4, i3, i2)]
        old_pt.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) ==> new_pt.spec_resolve_mapping_2m_l2(i4, i3, i2) == old_pt.spec_resolve_mapping_2m_l2(i4, i3, i2)
    &&& forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger new_pt.spec_resolve_mapping_4k_l1(i4, i3, i2, i1)]
        old_pt.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1) ==> new_pt.spec_resolve_mapping_4k_l1(i4, i3, i2, i1) == old_pt.spec_resolve_mapping_4k_l1(i4, i3, i2, i1)
    &&& forall|i4: L4Index| #![trigger new_pt.spec_held_l4(i4)] old_pt.kernel_l4_end() <= i4 && pei_valid(i4) ==> new_pt.spec_held_l4(i4) == old_pt.spec_held_l4(i4)
    &&& forall|i4: L4Index, i3: L3Index| #![trigger new_pt.spec_held_l3(i4, i3)]
        old_pt.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) ==> new_pt.spec_held_l3(i4, i3) == old_pt.spec_held_l3(i4, i3)
    &&& forall|i4: L4Index, i3: L3Index| #![trigger new_pt.spec_held_1g_l3(i4, i3)]
        old_pt.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && (i4, i3) != target ==> new_pt.spec_held_1g_l3(i4, i3) == old_pt.spec_held_1g_l3(i4, i3)
    &&& forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger new_pt.spec_held_l2(i4, i3, i2)]
        old_pt.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) ==> new_pt.spec_held_l2(i4, i3, i2) == old_pt.spec_held_l2(i4, i3, i2)
    &&& forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger new_pt.spec_held_2m_l2(i4, i3, i2)]
        old_pt.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) ==> new_pt.spec_held_2m_l2(i4, i3, i2) == old_pt.spec_held_2m_l2(i4, i3, i2)
    &&& forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger new_pt.spec_held_4k_l1(i4, i3, i2, i1)]
        old_pt.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1) ==> new_pt.spec_held_4k_l1(i4, i3, i2, i1) == old_pt.spec_held_4k_l1(i4, i3, i2, i1)
    &&& new_pt.spec_resolve_mapping_1g_l3(target.0, target.1) == Some(leaf)
    &&& new_pt.spec_held_1g_l3(target.0, target.1) == Some(leaf)
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, pg_idx)
    &&& new_page.is_init()
    &&& new_page.locking_thread() == old_page.locking_thread()
    &&& new_page.being_killed() == old_page.being_killed()
    &&& new_page.view_rodata() == old_page.view_rodata()
    &&& new_page.view_ghost() == old_page.view_ghost()
    &&& new_page.view() == (Page { state: PageState::Mapped1g, mappings: new_page.view().mappings, ref_count: 1, ..old_page.view() })
    &&& new_page.view().mappings() == Set::empty().insert((pagetable_ptr, va))
    &&& post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr)
    &&& new_thread.is_init()
    &&& new_thread.locking_thread() == old_thread.locking_thread()
    &&& new_thread.being_killed() == old_thread.being_killed()
    &&& new_thread.killer_info() == old_thread.killer_info()
    &&& new_thread.view_rodata() == old_thread.view_rodata()
    &&& new_thread.view_ghost() == old_thread.view_ghost()
    &&& new_thread.view() == (Thread {
        temp_alloc_cache_1g: new_thread.view().temp_alloc_cache_1g, quota_1g: new_thread.view().quota_1g, syscall_progress: new_thread.view().syscall_progress, ..old_thread.view()
    })
    &&& new_thread.view().temp_alloc_cache_1g.view() == old_thread.view().temp_alloc_cache_1g.view().remove(pg_ptr)
    &&& new_thread.view().quota_1g == old_thread.view().quota_1g - 1
    &&& new_thread.view().syscall_progress.view() == mmap_1g_progress_after_leaf(old_thread.view().syscall_progress.view())
}

/// The published leaf keeps every subsystem well formed.
proof fn map_owned_1g_page_eof_subsystems_inv(pre: KernelK, post: KernelK, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        map_owned_1g_page_eof_transition_framing(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va),
        page_ptr_valid(pg_ptr),
        va_1g_valid(va),
        pre.thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(pre.thrd_mp.spec_index(thrd_ptr)),
        !pre.thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        pre.pt_mp.dom().contains(pagetable_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned1g { thread_ptr: thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == pre.thrd_mp.spec_index(thrd_ptr).view().owning_container,
        pre.thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g.view().contains(pg_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().quota_1g >= 1,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va)) is None,
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_table_stale_cpus_only_when_write_locked(post.pt_mp),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread() is Write,
        post.thrd_mp.perms_wf(),
        post.thrd_mp.spec_index(thrd_ptr).inv(),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() is Write,
    ensures post.subsystems_inv(),
{
    reveal(map_owned_1g_page_eof_transition_framing);
    let pg_idx = page_ptr2page_index(pg_ptr);
    assert(index_valid(NUM_PAGES, pg_idx)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(post.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
    assert(page_array_wf(post.pg_arr)) by { reveal(page_array_wf); reveal(Page::mappings_va_valid); };
    assert(thread_perms_wf(post.thrd_mp)) by {
        reveal(thread_perms_wf); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(thread_exited_only_when_wlocked);
        reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_ipc_transit_wf);
    };
}

/// Mapped 4K pages and the 4K leaves still agree: the 4K leaves, their held entries and every Mapped4k page stay.
proof fn map_owned_1g_page_eof_page_mappings_4k(pre: KernelK, post: KernelK, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        map_owned_1g_page_eof_transition_framing(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va),
        page_ptr_valid(pg_ptr),
        va_1g_valid(va),
        pre.thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(pre.thrd_mp.spec_index(thrd_ptr)),
        !pre.thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        pre.pt_mp.dom().contains(pagetable_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned1g { thread_ptr: thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == pre.thrd_mp.spec_index(thrd_ptr).view().owning_container,
        pre.thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g.view().contains(pg_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().quota_1g >= 1,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va)) is None,
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_table_stale_cpus_only_when_write_locked(post.pt_mp),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread() is Write,
        post.thrd_mp.perms_wf(),
        post.thrd_mp.spec_index(thrd_ptr).inv(),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() is Write,
    ensures mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
{
    reveal(map_owned_1g_page_eof_transition_framing);
    broadcast use {spec_va_4k_valid_index_roundtrip, spec_va_4k_index_roundtrip_at};
    pre.default_pagetable_wf_at(pagetable_ptr); reveal(pagetable_lower_wf); reveal(mapped_4k_page_pagetable_wf);
}

/// Mapped 2M pages and the 2M leaves still agree: the 2M leaves, their held entries and every Mapped2m page stay.
proof fn map_owned_1g_page_eof_page_mappings_2m(pre: KernelK, post: KernelK, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        map_owned_1g_page_eof_transition_framing(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va),
        page_ptr_valid(pg_ptr),
        va_1g_valid(va),
        pre.thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(pre.thrd_mp.spec_index(thrd_ptr)),
        !pre.thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        pre.pt_mp.dom().contains(pagetable_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned1g { thread_ptr: thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == pre.thrd_mp.spec_index(thrd_ptr).view().owning_container,
        pre.thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g.view().contains(pg_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().quota_1g >= 1,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va)) is None,
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_table_stale_cpus_only_when_write_locked(post.pt_mp),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread() is Write,
        post.thrd_mp.perms_wf(),
        post.thrd_mp.spec_index(thrd_ptr).inv(),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() is Write,
    ensures mapped_2m_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
{
    reveal(map_owned_1g_page_eof_transition_framing);
    broadcast use spec_va_2m_valid_index_roundtrip;
    pre.default_pagetable_wf_at(pagetable_ptr); reveal(pagetable_lower_wf); reveal(mapped_2m_page_pagetable_wf);
}

/// The consumed staged page becomes the Mapped1g page of the new 1G leaf, and every other 1G page and leaf agree as before.
proof fn map_owned_1g_page_eof_page_mappings_1g(pre: KernelK, post: KernelK, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        map_owned_1g_page_eof_transition_framing(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va),
        page_ptr_valid(pg_ptr),
        va_1g_valid(va),
        pre.thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(pre.thrd_mp.spec_index(thrd_ptr)),
        !pre.thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        pre.pt_mp.dom().contains(pagetable_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned1g { thread_ptr: thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == pre.thrd_mp.spec_index(thrd_ptr).view().owning_container,
        pre.thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g.view().contains(pg_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().quota_1g >= 1,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va)) is None,
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_table_stale_cpus_only_when_write_locked(post.pt_mp),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread() is Write,
        post.thrd_mp.perms_wf(),
        post.thrd_mp.spec_index(thrd_ptr).inv(),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() is Write,
    ensures mapped_1g_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
{
    reveal(map_owned_1g_page_eof_transition_framing);
    broadcast use spec_va_1g_valid_index_roundtrip;
    reveal(KernelK::default_pagetable_wf); reveal(pagetable_lower_wf); reveal(mapped_1g_page_pagetable_wf);
}

/// The published leaf, the consumed staged page and the charged quota keep every memory-management predicate.
proof fn map_owned_1g_page_eof_memory_management_inv(pre: KernelK, post: KernelK, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        map_owned_1g_page_eof_transition_framing(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va),
        page_ptr_valid(pg_ptr),
        va_1g_valid(va),
        pre.thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(pre.thrd_mp.spec_index(thrd_ptr)),
        !pre.thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        pre.pt_mp.dom().contains(pagetable_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned1g { thread_ptr: thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == pre.thrd_mp.spec_index(thrd_ptr).view().owning_container,
        pre.thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g.view().contains(pg_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().quota_1g >= 1,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va)) is None,
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_table_stale_cpus_only_when_write_locked(post.pt_mp),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread() is Write,
        post.thrd_mp.perms_wf(),
        post.thrd_mp.spec_index(thrd_ptr).inv(),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() is Write,
        page_array_wf(post.pg_arr),
    ensures post.memory_management_inv(),
{
    reveal(map_owned_1g_page_eof_transition_framing);
    let pg_idx = page_ptr2page_index(pg_ptr);
    assert(index_valid(NUM_PAGES, pg_idx)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        map_owned_1g_page_eof_page_mappings_4k(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va); map_owned_1g_page_eof_page_mappings_2m(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va);
        map_owned_1g_page_eof_page_mappings_1g(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va);
    };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { cpu_set_pages_wf_preserved_for_page_state_eq(pre.cpu_set_mp, post.cpu_set_mp, pre.pg_arr, post.pg_arr); };
    assert(allocator_pages_wf(post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp, post.pg_arr)) by {
        allocator_4k_pages_wf_preserved_for_page_state_eq(pre.allc_4k_mp, post.allc_4k_mp, pre.pg_arr, post.pg_arr);
        allocator_2m_pages_wf_preserved_for_page_state_eq(pre.allc_2m_mp, post.allc_2m_mp, pre.pg_arr, post.pg_arr);
        allocator_1g_pages_wf_preserved_for_page_state_eq(pre.allc_1g_mp, post.allc_1g_mp, pre.pg_arr, post.pg_arr);
    };
    assert(container_owned_pages_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(hugepage_1g_wf(post.pg_arr)) by { reveal(hugepage_1g_wf); };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by {
        process_thread_wf_thread_at(pre.prc_mp, pre.thrd_mp, thrd_ptr); reveal(process_pagetable_wf); reveal(container_owned_pages_wf); reveal(container_process_page_pagetable_wf);
    };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { page_array_wf_at(pre.pg_arr, pg_idx); reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); };
    assert(container_pages_wf(post.ctn_mp, post.pg_arr)) by { container_pages_wf_preserved_for_page_state_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(process_pages_wf(post.prc_mp, post.pg_arr)) by { process_pages_wf_preserved_for_page_state_eq(pre.prc_mp, post.prc_mp, pre.pg_arr, post.pg_arr); };
    assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
    assert(page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr)) by { reveal(page_object_owner_wf); reveal(container_owned_pages_wf); };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr); };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { iommu_table_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
    assert(pcid_allocator_pages_wf(post.pcid_allc_mp, post.pg_arr)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pcid_allc_mp, post.pcid_allc_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_pages_wf(post.thrd_mp, post.pg_arr)) by {
        thread_staged_4k_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr);
        thread_staged_2m_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr);
        reveal(thread_staged_1g_pages_wf);
    };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
    assert(process_pagetable_wf(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_wf); };
    assert(iommu_table_no_huge_leaf_wf(post.it_mp)) by { reveal(iommu_table_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by {
        reveal(process_emptied_tables_wf); reveal(process_pagetable_wf); process_thread_wf_thread_at(pre.prc_mp, pre.thrd_mp, thrd_ptr);
        process_perms_wf_at(pre.prc_mp, pre.thrd_mp.spec_index(thrd_ptr).view().owning_proc);
        process_emptied_threads_wf_at(pre.prc_mp, pre.thrd_mp, pre.thrd_mp.spec_index(thrd_ptr).view().owning_proc, thrd_ptr);
    };
    assert(pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp)) by { reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); };
    assert(container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(post.ctn_mp, post.prc_mp, pre.thrd_mp, post.thrd_mp, post.allc_4k_mp);
        container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(post.ctn_mp, post.prc_mp, pre.thrd_mp, post.thrd_mp, post.allc_2m_mp);
        container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(post.ctn_mp, post.prc_mp, pre.thrd_mp, post.thrd_mp, post.allc_1g_mp);
    };
    assert(allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(post.allc_4k_mp, pre.pg_arr, post.pg_arr, pg_idx); };
    assert(allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, pg_idx); };
    assert(allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, pg_idx); };
}

/// The thread changes only its 1G cache, quota and progress, which keeps every process-management predicate.
proof fn map_owned_1g_page_eof_process_management_inv(pre: KernelK, post: KernelK, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        map_owned_1g_page_eof_transition_framing(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va),
        page_ptr_valid(pg_ptr),
        va_1g_valid(va),
        pre.thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(pre.thrd_mp.spec_index(thrd_ptr)),
        !pre.thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        pre.pt_mp.dom().contains(pagetable_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned1g { thread_ptr: thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == pre.thrd_mp.spec_index(thrd_ptr).view().owning_container,
        pre.thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g.view().contains(pg_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().quota_1g >= 1,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va)) is None,
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_table_stale_cpus_only_when_write_locked(post.pt_mp),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread() is Write,
        post.thrd_mp.perms_wf(),
        post.thrd_mp.spec_index(thrd_ptr).inv(),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() is Write,
    ensures post.process_management_inv(),
{
    reveal(map_owned_1g_page_eof_transition_framing);
    assert(thread_caller_callee_wf(post.thrd_mp)) by { thread_caller_callee_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp); };
    assert(thread_dangling_chain_end_wf(post.thrd_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thrd_mp, post.thrd_mp); };
    assert(thread_endpoint_ref_counter_wf(post.thrd_mp, post.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp, post.ep_mp); };
    assert(thread_endpoint_queue_wf(post.thrd_mp, post.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp, post.ep_mp); };
    assert(container_thread_endpoint_wf(post.ctn_mp, post.thrd_mp, post.ep_mp)) by { container_thread_endpoint_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thrd_mp, post.thrd_mp, post.ep_mp); };
    assert(container_thread_scheduler_wf(post.ctn_mp, post.thrd_mp, post.sched_mp)) by { container_thread_scheduler_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thrd_mp, post.thrd_mp, post.sched_mp); };
    assert(container_thread_wf(post.ctn_mp, post.thrd_mp)) by { container_thread_wf_preserved_for_thread_process_management_fields(post.ctn_mp, pre.thrd_mp, post.thrd_mp); };
    assert(process_thread_wf(post.prc_mp, post.thrd_mp)) by { process_thread_wf_preserved_for_thread_process_management_fields(post.prc_mp, pre.thrd_mp, post.thrd_mp); };
    assert(thread_cpu_wf(post.thrd_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp, post.cpu_arr); };
    assert(process_emptied_threads_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_emptied_threads_wf); };
}

/// The new 1G leaf fills an L3 entry no translation was cached for: the CPU TLBs, the paging-structure caches and the dirty PCIDs stay consistent.
proof fn map_owned_1g_page_eof_tlb_caches(pre: KernelK, post: KernelK, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        map_owned_1g_page_eof_transition_framing(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va),
        page_ptr_valid(pg_ptr),
        va_1g_valid(va),
        pre.thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(pre.thrd_mp.spec_index(thrd_ptr)),
        !pre.thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        pre.pt_mp.dom().contains(pagetable_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned1g { thread_ptr: thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == pre.thrd_mp.spec_index(thrd_ptr).view().owning_container,
        pre.thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g.view().contains(pg_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().quota_1g >= 1,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va)) is None,
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_table_stale_cpus_only_when_write_locked(post.pt_mp),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread() is Write,
        post.thrd_mp.perms_wf(),
        post.thrd_mp.spec_index(thrd_ptr).inv(),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() is Write,
    ensures
        cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush),
        cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
        structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
{
    reveal(map_owned_1g_page_eof_transition_framing);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_pagetable_pcid_match); };
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by {
        broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip, spec_va_1g_valid_index_roundtrip; reveal(cpu_tlb_wf);
    };
    assert(structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(structure_cache_wf); };
}

/// The published 1G leaf, the consumed staged page, and the charged thread quota keep the kernel invariant.
pub(super) proof fn map_owned_1g_page_eof(pre: KernelK, post: KernelK, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        map_owned_1g_page_eof_transition_framing(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va),
        page_ptr_valid(pg_ptr),
        va_1g_valid(va),
        pre.thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(pre.thrd_mp.spec_index(thrd_ptr)),
        !pre.thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        pre.pt_mp.dom().contains(pagetable_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned1g { thread_ptr: thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == pre.thrd_mp.spec_index(thrd_ptr).view().owning_container,
        pre.thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g.view().contains(pg_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().quota_1g >= 1,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va),
        !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_1g().dom().contains(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(spec_v2l4index(va)) is Some,
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_table_stale_cpus_only_when_write_locked(post.pt_mp),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread() is Write,
        post.thrd_mp.perms_wf(),
        post.thrd_mp.spec_index(thrd_ptr).inv(),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() is Write,
    ensures post.inv(),
{
    reveal(map_owned_1g_page_eof_transition_framing);
    let old_pt = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr);
    assert(old_pt.spec_held_1g_l3(spec_v2l4index(va), spec_v2l3index(va)) is None) by {
        spec_va_1g_valid_index_roundtrip(va); pagetable_perms_wf_at(pre.pt_mp, pagetable_ptr);
        old_pt.higher.wf_mapping_1g_at(spec_v2l4index(va), spec_v2l3index(va)); old_pt.higher.spec_held_l4_resolves_implies_spec_held_1g_l3_eq_resolve(spec_v2l4index(va), spec_v2l3index(va));
    };
    map_owned_1g_page_eof_subsystems_inv(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va);
    map_owned_1g_page_eof_memory_management_inv(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va);
    map_owned_1g_page_eof_process_management_inv(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va);
    map_owned_1g_page_eof_tlb_caches(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va);
}
} // verus!
