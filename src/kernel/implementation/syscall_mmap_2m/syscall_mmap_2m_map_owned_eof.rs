use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_mmap_2m_spec::mmap_2m_progress_after_leaf;

verus! {
/// Publishes the staged 2M page `pg_ptr` of `thrd_ptr` at `va` in the window half of `pagetable_ptr`: the page becomes mapped
/// once, the thread consumes it from its 2M cache and quota and advances its mmap progress; every other kernel field is unchanged.
#[verifier::opaque]
pub(super) open spec fn map_owned_2m_page_eof_transition_framing(pre: KernelK, post: KernelK, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr) -> bool {
    let pg_idx = page_ptr2page_index(pg_ptr);
    let old_pt = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr);
    let new_pt = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr);
    let old_page = pre.pg_arr.spec_index(pg_idx).view();
    let new_page = post.pg_arr.spec_index(pg_idx).view();
    let old_thread = pre.thrd_mp.spec_index(thrd_ptr);
    let new_thread = post.thrd_mp.spec_index(thrd_ptr);
    &&& post == (KernelK { pt_lower: post.pt_lower, pg_arr: post.pg_arr, thrd_mp: post.thrd_mp, ..pre })
    &&& post.pt_lower.view() == pre.pt_lower.view().insert(pagetable_ptr, post.pt_lower.view().spec_index(pagetable_ptr))
    &&& forall|other_pagetable: RwLockPageTableRoot|
        #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), other_pagetable)]
        pre.pt_mp.dom().contains(other_pagetable) && other_pagetable != pagetable_ptr ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), other_pagetable) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), other_pagetable)
    &&& new_pt.wf()
    &&& new_pt.mapping_2m() == old_pt.mapping_2m().insert(va, MapEntry { addr: pg_ptr, present: true, write: true, execute_disable: false, owning_container: Ghost(old_page.view().owning_container) })
    &&& new_pt.mapping_4k() == old_pt.mapping_4k()
    &&& new_pt.mapping_1g() == old_pt.mapping_1g()
    &&& new_pt.page_closure() == old_pt.page_closure()
    &&& new_pt.lower.window_stale_cpus == old_pt.lower.window_stale_cpus
    &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_pt.lower.l2_owner(p, i)] new_pt.lower.l2_owner(p, i) == old_pt.lower.l2_owner(p, i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_pt.spec_resolve_mapping_l2(l4i, l3i, l2i)]
        pre.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_pt.spec_resolve_mapping_l2(l4i, l3i, l2i) == old_pt.spec_resolve_mapping_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_pt.spec_held_l2(l4i, l3i, l2i)]
        old_pt.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_pt.spec_held_l2(l4i, l3i, l2i) == old_pt.spec_held_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_pt.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        old_pt.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> new_pt.spec_held_4k_l1(l4i, l3i, l2i, l1i) == old_pt.spec_held_4k_l1(l4i, l3i, l2i, l1i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_pt.spec_held_2m_l2(l4i, l3i, l2i)]
        old_pt.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))
            ==> new_pt.spec_held_2m_l2(l4i, l3i, l2i) == old_pt.spec_held_2m_l2(l4i, l3i, l2i)
    &&& new_pt.spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some
    &&& new_pt.spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))->0.addr == pg_ptr
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, pg_idx)
    &&& new_page.is_init()
    &&& new_page.locking_thread() == old_page.locking_thread()
    &&& new_page.being_killed() == old_page.being_killed()
    &&& new_page.view_rodata() == old_page.view_rodata()
    &&& new_page.view_ghost() == old_page.view_ghost()
    &&& new_page.view() == (Page { state: PageState::Mapped2m, mappings: new_page.view().mappings, ref_count: 1, ..old_page.view() })
    &&& new_page.view().mappings() == Set::empty().insert((pagetable_ptr, va))
    &&& post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr)
    &&& new_thread.is_init()
    &&& new_thread.locking_thread() == old_thread.locking_thread()
    &&& new_thread.being_killed() == old_thread.being_killed()
    &&& new_thread.killer_info() == old_thread.killer_info()
    &&& new_thread.view_rodata() == old_thread.view_rodata()
    &&& new_thread.view_ghost() == old_thread.view_ghost()
    &&& new_thread.view() == (Thread {
        temp_alloc_cache_2m: new_thread.view().temp_alloc_cache_2m, quota_2m: new_thread.view().quota_2m, syscall_progress: new_thread.view().syscall_progress, ..old_thread.view()
    })
    &&& new_thread.view().temp_alloc_cache_2m.view() == old_thread.view().temp_alloc_cache_2m.view().remove(pg_ptr)
    &&& new_thread.view().quota_2m == old_thread.view().quota_2m - 1
    &&& new_thread.view().syscall_progress.view() == mmap_2m_progress_after_leaf(old_thread.view().syscall_progress.view())
}

/// The published leaf keeps every subsystem well formed.
proof fn map_owned_2m_page_eof_subsystems_inv(pre: KernelK, post: KernelK, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        map_owned_2m_page_eof_transition_framing(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va),
        page_ptr_valid(pg_ptr),
        va_2m_valid(va),
        pre.thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(pre.thrd_mp.spec_index(thrd_ptr)),
        !pre.thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        pre.pt_mp.dom().contains(pagetable_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned2m { thread_ptr: thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == pre.thrd_mp.spec_index(thrd_ptr).view().owning_container,
        pre.thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_2m.view().contains(pg_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().quota_2m >= 1,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m().dom().contains(va) == false,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is None,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some,
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread() is Write,
        post.thrd_mp.perms_wf(),
        post.thrd_mp.spec_index(thrd_ptr).inv(),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() is Write,
    ensures post.subsystems_inv(),
{
    reveal(map_owned_2m_page_eof_transition_framing);
    let pg_idx = page_ptr2page_index(pg_ptr);
    assert(index_valid(NUM_PAGES, pg_idx)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(post.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
    assert(page_array_wf(post.pg_arr)) by { reveal(page_array_wf); reveal(Page::mappings_va_valid); };
    assert(thread_perms_wf(post.thrd_mp)) by {
        reveal(thread_perms_wf); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked); reveal(thread_exited_only_when_wlocked);
        reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_ipc_transit_wf);
    };
}

/// Mapped 4K pages and the 4K leaves still agree: neither the 4K leaves nor any Mapped4k page change.
proof fn map_owned_2m_page_eof_page_mappings_4k(pre: KernelK, post: KernelK, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        map_owned_2m_page_eof_transition_framing(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va),
        page_ptr_valid(pg_ptr),
        va_2m_valid(va),
        pre.thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(pre.thrd_mp.spec_index(thrd_ptr)),
        !pre.thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        pre.pt_mp.dom().contains(pagetable_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned2m { thread_ptr: thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == pre.thrd_mp.spec_index(thrd_ptr).view().owning_container,
        pre.thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_2m.view().contains(pg_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().quota_2m >= 1,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m().dom().contains(va) == false,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is None,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some,
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread() is Write,
        post.thrd_mp.perms_wf(),
        post.thrd_mp.spec_index(thrd_ptr).inv(),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() is Write,
    ensures mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
{
    reveal(map_owned_2m_page_eof_transition_framing);
    broadcast use {spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip};
    page_ptr_valid_imply_page_index_valid(); reveal(KernelK::default_pagetable_wf);
    reveal(pagetable_lower_wf); reveal(mapped_4k_page_pagetable_wf);
}

/// The consumed staged page becomes the Mapped2m page of the new 2M leaf, and every other 2M page and leaf agree as before.
proof fn map_owned_2m_page_eof_page_mappings_2m(pre: KernelK, post: KernelK, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        map_owned_2m_page_eof_transition_framing(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va),
        page_ptr_valid(pg_ptr),
        va_2m_valid(va),
        pre.thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(pre.thrd_mp.spec_index(thrd_ptr)),
        !pre.thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        pre.pt_mp.dom().contains(pagetable_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned2m { thread_ptr: thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == pre.thrd_mp.spec_index(thrd_ptr).view().owning_container,
        pre.thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_2m.view().contains(pg_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().quota_2m >= 1,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m().dom().contains(va) == false,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is None,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some,
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread() is Write,
        post.thrd_mp.perms_wf(),
        post.thrd_mp.spec_index(thrd_ptr).inv(),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() is Write,
    ensures mapped_2m_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
{
    reveal(map_owned_2m_page_eof_transition_framing);
    let old_pt = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr);
    assert(old_pt.spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is None) by {
        reveal(KernelK::default_pagetable_wf); pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr); spec_va_2m_valid_index_roundtrip(va);
        old_pt.wf_mapping_2m_at(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va));
        old_pt.higher.spec_resolve_mapping_l3_some_implies_spec_held_l3_eq(spec_v2l4index(va), spec_v2l3index(va));
    };
    broadcast use {spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip};
    page_ptr_valid_imply_page_index_valid(); reveal(KernelK::default_pagetable_wf);
    reveal(pagetable_lower_wf); reveal(mapped_2m_page_pagetable_wf);
}

/// Mapped 1G pages and the 1G leaves still agree: neither changes.
proof fn map_owned_2m_page_eof_page_mappings_1g(pre: KernelK, post: KernelK, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        map_owned_2m_page_eof_transition_framing(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va),
        page_ptr_valid(pg_ptr),
        va_2m_valid(va),
        pre.thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(pre.thrd_mp.spec_index(thrd_ptr)),
        !pre.thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        pre.pt_mp.dom().contains(pagetable_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned2m { thread_ptr: thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == pre.thrd_mp.spec_index(thrd_ptr).view().owning_container,
        pre.thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_2m.view().contains(pg_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().quota_2m >= 1,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m().dom().contains(va) == false,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is None,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some,
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread() is Write,
        post.thrd_mp.perms_wf(),
        post.thrd_mp.spec_index(thrd_ptr).inv(),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() is Write,
    ensures mapped_1g_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
{
    reveal(map_owned_2m_page_eof_transition_framing);
    broadcast use {spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip};
    page_ptr_valid_imply_page_index_valid(); reveal(KernelK::default_pagetable_wf);
    reveal(pagetable_lower_wf); reveal(mapped_1g_page_pagetable_wf);
}

/// The published leaf, the consumed staged page and the charged quota keep every memory-management predicate.
proof fn map_owned_2m_page_eof_memory_management_inv(pre: KernelK, post: KernelK, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        map_owned_2m_page_eof_transition_framing(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va),
        page_ptr_valid(pg_ptr),
        va_2m_valid(va),
        pre.thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(pre.thrd_mp.spec_index(thrd_ptr)),
        !pre.thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        pre.pt_mp.dom().contains(pagetable_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned2m { thread_ptr: thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == pre.thrd_mp.spec_index(thrd_ptr).view().owning_container,
        pre.thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_2m.view().contains(pg_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().quota_2m >= 1,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m().dom().contains(va) == false,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is None,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some,
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread() is Write,
        post.thrd_mp.perms_wf(),
        post.thrd_mp.spec_index(thrd_ptr).inv(),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() is Write,
        page_array_wf(post.pg_arr),
    ensures post.memory_management_inv(),
{
    reveal(map_owned_2m_page_eof_transition_framing);
    let pg_idx = page_ptr2page_index(pg_ptr);
    assert(index_valid(NUM_PAGES, pg_idx)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        map_owned_2m_page_eof_page_mappings_4k(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va); map_owned_2m_page_eof_page_mappings_2m(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va);
        map_owned_2m_page_eof_page_mappings_1g(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va);
    };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { cpu_set_pages_wf_preserved_for_page_state_eq(pre.cpu_set_mp, post.cpu_set_mp, pre.pg_arr, post.pg_arr); };
    assert(allocator_pages_wf(post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp, post.pg_arr)) by {
        allocator_4k_pages_wf_preserved_for_page_state_eq(pre.allc_4k_mp, post.allc_4k_mp, pre.pg_arr, post.pg_arr);
        allocator_2m_pages_wf_preserved_for_page_state_eq(pre.allc_2m_mp, post.allc_2m_mp, pre.pg_arr, post.pg_arr);
        allocator_1g_pages_wf_preserved_for_page_state_eq(pre.allc_1g_mp, post.allc_1g_mp, pre.pg_arr, post.pg_arr);
    };
    assert(container_owned_pages_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(hugepage_2m_wf(post.pg_arr)) by { reveal(hugepage_2m_wf); };
    assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
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
        reveal(thread_staged_2m_pages_wf);
        thread_staged_1g_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr);
    };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
    assert(process_pagetable_wf(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_wf); };
    assert(pagetable_no_1g_leaf_wf(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_no_1g_leaf_wf); };
    assert(iommu_table_no_huge_leaf_wf(post.it_mp)) by { reveal(iommu_table_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by {
        reveal(process_emptied_tables_wf); reveal(process_pagetable_wf); process_thread_wf_thread_at(pre.prc_mp, pre.thrd_mp, thrd_ptr);
        process_perms_wf_at(pre.prc_mp, pre.thrd_mp.spec_index(thrd_ptr).view().owning_proc);
        process_emptied_threads_wf_at(pre.prc_mp, pre.thrd_mp, pre.thrd_mp.spec_index(thrd_ptr).view().owning_proc, thrd_ptr);
    };
    assert(container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(post.ctn_mp, post.prc_mp, pre.thrd_mp, post.thrd_mp, post.allc_4k_mp);
        container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(post.ctn_mp, post.prc_mp, pre.thrd_mp, post.thrd_mp, post.allc_2m_mp);
        container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(post.ctn_mp, post.prc_mp, pre.thrd_mp, post.thrd_mp, post.allc_1g_mp);
    };
    assert(allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(post.allc_4k_mp, pre.pg_arr, post.pg_arr, pg_idx); };
    assert(allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, pg_idx); };
    assert(allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, pg_idx); };
}

/// The thread changes only its 2M cache, quota and progress, which keeps every process-management predicate.
proof fn map_owned_2m_page_eof_process_management_inv(pre: KernelK, post: KernelK, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        map_owned_2m_page_eof_transition_framing(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va),
        page_ptr_valid(pg_ptr),
        va_2m_valid(va),
        pre.thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(pre.thrd_mp.spec_index(thrd_ptr)),
        !pre.thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        pre.pt_mp.dom().contains(pagetable_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned2m { thread_ptr: thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == pre.thrd_mp.spec_index(thrd_ptr).view().owning_container,
        pre.thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_2m.view().contains(pg_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().quota_2m >= 1,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m().dom().contains(va) == false,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is None,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some,
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread() is Write,
        post.thrd_mp.perms_wf(),
        post.thrd_mp.spec_index(thrd_ptr).inv(),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() is Write,
    ensures post.process_management_inv(),
{
    reveal(map_owned_2m_page_eof_transition_framing);
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

/// The new 2M leaf adds no cached translation: the CPU TLBs, the paging-structure caches and the dirty PCIDs stay consistent.
proof fn map_owned_2m_page_eof_tlb_caches(pre: KernelK, post: KernelK, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        map_owned_2m_page_eof_transition_framing(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va),
        page_ptr_valid(pg_ptr),
        va_2m_valid(va),
        pre.thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(pre.thrd_mp.spec_index(thrd_ptr)),
        !pre.thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        pre.pt_mp.dom().contains(pagetable_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned2m { thread_ptr: thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == pre.thrd_mp.spec_index(thrd_ptr).view().owning_container,
        pre.thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_2m.view().contains(pg_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().quota_2m >= 1,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m().dom().contains(va) == false,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is None,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some,
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
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
    reveal(map_owned_2m_page_eof_transition_framing);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_pagetable_pcid_match); };
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by {
        broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip;
        pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr); pagetable_lower_wf_at(post.pt_mp, post.pt_lower.view(), pagetable_ptr);
        reveal(cpu_tlb_wf); reveal(WholePageTable::wf_mapping_4k); reveal(WholePageTable::wf_mapping_2m);
    };
    assert(structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by {
        broadcast use spec_va_2m_valid_index_roundtrip;
        pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr);
        reveal(structure_cache_wf);
    };
}
/// The published 2M leaf, the consumed staged page, and the charged thread quota keep the kernel invariant.
pub(super) proof fn map_owned_2m_page_eof(pre: KernelK, post: KernelK, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        map_owned_2m_page_eof_transition_framing(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va),
        page_ptr_valid(pg_ptr),
        va_2m_valid(va),
        pre.thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(pre.thrd_mp.spec_index(thrd_ptr)),
        !pre.thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        pre.pt_mp.dom().contains(pagetable_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned2m { thread_ptr: thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == pre.thrd_mp.spec_index(thrd_ptr).view().owning_container,
        pre.thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        pre.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_2m.view().contains(pg_ptr),
        pre.thrd_mp.spec_index(thrd_ptr).view().quota_2m >= 1,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m().dom().contains(va) == false,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is None,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some,
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread() is Write,
        post.thrd_mp.perms_wf(),
        post.thrd_mp.spec_index(thrd_ptr).inv(),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() is Write,
    ensures post.inv(),
{
    reveal(map_owned_2m_page_eof_transition_framing);
    map_owned_2m_page_eof_subsystems_inv(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va);
    map_owned_2m_page_eof_memory_management_inv(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va);
    map_owned_2m_page_eof_process_management_inv(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va);
    map_owned_2m_page_eof_tlb_caches(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va);
}
/// Every window under a resolved L3 entry of `pagetable_ptr` keeps its lock state and stale CPUs across the published leaf,
/// and a window that linked no L1 table still links none.
pub(super) proof fn map_owned_2m_page_eof_window_frames(pre: KernelK, post: KernelK, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires map_owned_2m_page_eof_transition_framing(pre, post, pg_ptr, thrd_ptr, pagetable_ptr, va),
    ensures
        forall|w: WindowVa| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).window_view(w)]
            spec_va_2m_valid(w.va) && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(w.va)
                && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> {
                let pre_w = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).window_view(w);
                let post_w = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).window_view(w);
                &&& post_w.lock_state == pre_w.lock_state
                &&& post_w.stale_cpus == pre_w.stale_cpus
                &&& pre_w.l1_table is None ==> post_w.l1_table is None
            },
{
    reveal(map_owned_2m_page_eof_transition_framing);
    let old_pt = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr);
    let new_pt = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr);
    assert forall|w: WindowVa| #![trigger new_pt.window_view(w)]
        spec_va_2m_valid(w.va) && old_pt.kernel_l4_end() <= spec_v2l4index(w.va) && old_pt.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
        implies new_pt.window_view(w).lock_state == old_pt.window_view(w).lock_state && new_pt.window_view(w).stale_cpus == old_pt.window_view(w).stale_cpus
            && (old_pt.window_view(w).l1_table is None ==> new_pt.window_view(w).l1_table is None) by {
        spec_va_2m_valid_index_roundtrip(w.va);
        old_pt.higher.spec_resolve_mapping_l3_some_implies_spec_held_l3_eq(spec_v2l4index(w.va), spec_v2l3index(w.va));
        assert(new_pt.spec_held_l2(spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va)) == old_pt.spec_held_l2(spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va)));
    };
}
} // verus!
