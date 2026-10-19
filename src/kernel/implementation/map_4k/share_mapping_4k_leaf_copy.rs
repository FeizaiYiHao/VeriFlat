use vstd::prelude::*;
use crate::*;
use super::share_mapping_4k::share_mapping_4k_leaf_ready;
#[cfg(verus_keep_ghost)]
use super::share_mapping_4k_eof::*;

verus! {
/// Copies the ready source 4K leaf `source_va` into `target_pagetable` at `target_va` and records the new mapping on the shared page under that page's own lock.
pub(super) fn share_one_mapping_4k_copy_leaf(
    krnl: &mut KernelK, target_thread: RwLockThreadPtr, target_process: RwLockProcessPtr, target_container: RwLockContainerPtr, source_pagetable: RwLockPageTableRoot,
    target_pagetable: RwLockPageTableRoot, source_va: VAddr, target_va: VAddr, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>,
    Tracked(target_pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(krnl).pg_arr.lock_id_by_index(held_page).major < MAPPED_PAGE_LOCK_MAJOR,
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        source_pagetable != target_pagetable,
        old(krnl).thr_mp.dom().contains(target_thread),
        !thread_is_dangling(old(krnl).thr_mp.spec_index(target_thread)),
        old(krnl).prc_mp.dom().contains(target_process),
        old(krnl).prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container,
        (old(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process && old(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable
            && old(krnl).thr_mp.spec_index(target_thread).view().syscall_progress.view() != Some(SyscallProgress::ThreadExitZombie))
            || (!old(krnl).prc_mp.spec_index(target_process).view().zombie && !(old(krnl).prc_mp.spec_index(target_process).view().state.view() is TablesEmptied)),
        old(krnl).pt_mp.dom().contains(source_pagetable),
        old(krnl).pt_mp.dom().contains(target_pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
        old(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_pagetable_lock_perm.state() is WriteLock,
        source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        source_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
        target_pagetable_lock_perm.state() is WriteLock,
        target_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        target_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        share_mapping_4k_leaf_ready(old(krnl), source_pagetable, target_pagetable, target_container, source_va, target_va),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pg_arr: final(krnl).pg_arr, ..*old(krnl) }),
        final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, target_pagetable),
        final(krnl).pt_mp.spec_index(target_pagetable).locking_thread() == old(krnl).pt_mp.spec_index(target_pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k() == old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k().insert(target_va, old(krnl).pt_mp.spec_index(source_pagetable).view().mapping_4k().spec_index(source_va)),
        final(krnl).pt_mp.spec_index(target_pagetable).view().user_view(LockStateU::Unlocked).mapping_4k == old(krnl).pt_mp.spec_index(target_pagetable).view().user_view(LockStateU::Unlocked).mapping_4k.insert(target_va,
            old(krnl).pt_mp.spec_index(source_pagetable).view().user_view(LockStateU::Unlocked).mapping_4k.spec_index(source_va)),
        final(krnl).pt_mp.spec_index(target_pagetable).view().mapping_2m() == old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_2m(),
        final(krnl).pt_mp.spec_index(target_pagetable).view().mapping_1g() == old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_1g(),
        final(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end,
        final(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == old(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr,
        held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
{
    let source_indices = va2index(source_va);
    proof { pagetable_perms_wf_at(krnl.pt_mp, source_pagetable); pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, target_pagetable); }
    let target_indices = va2index(target_va);
    assert({
        &&& spec_index2va(source_indices) == source_va
        &&& krnl.pt_mp.spec_index(source_pagetable).view().spec_resolve_mapping_4k_l1(source_indices.0, source_indices.1, source_indices.2, source_indices.3) is Some
    }) by { spec_va_4k_index_roundtrip_at(source_va, source_indices.0, source_indices.1, source_indices.2, source_indices.3); reveal(PageTable::wf_mapping_4k); };
    let source_entry;
    {
        let source = krnl.pt_mp.borrow_typed(source_pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(source_pagetable_lock_perm));
        source_entry = source.resolve_mapping_4k_l1(source_indices.0, source_indices.1, source_indices.2, source_indices.3).2.unwrap();
    }
    let page_ptr = source_entry.addr;
    let page_index = page_ptr2page_index(page_ptr);
    let target_l1_ptr;
    {
        let target = krnl.pt_mp.borrow_typed(target_pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(target_pagetable_lock_perm));
        target_l1_ptr = target.resolve_mapping_4k_l2(target_indices.0, target_indices.1, target_indices.2).0.unwrap().addr;
    }
    proof {
        assert({
            &&& index_valid(NUM_PAGES, page_index)
            &&& krnl.pg_arr.spec_index(page_index).view().view().state is Mapped4k
            &&& !lctx.page_lock_map().dom().contains(page_index)
            &&& krnl.pg_arr.lock_id_by_index(page_index).major == MAPPED_PAGE_LOCK_MAJOR
        }) by { page_ptr_valid_imply_page_index_valid(); mapped_4k_page_pagetable_wf_pagetable_at(krnl.pt_mp, krnl.pg_arr, source_pagetable, source_va); };
    }
    let Tracked(page_lock_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));
    let ghost locked_k = *krnl;
    proof {
        assert({
            &&& krnl.pg_arr.inv()
            &&& krnl.pg_arr.spec_index(page_index).view().inv()
        }) by { page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, page_index); };
        assert({
            &&& !krnl.pg_arr.spec_index(page_index).view().view().mappings().contains((target_pagetable, target_va))
            &&& krnl.pg_arr.spec_index(page_index).view().view().ref_count < usize::MAX
        }) by { mapped_4k_page_pagetable_wf_page_at(krnl.pt_mp, krnl.pg_arr, page_index, target_pagetable, target_va); mapped_4k_page_ref_count_lt_usize_max(krnl.pt_mp, krnl.pg_arr, page_index); };
    }
    page_array_add_4k_mapping(&mut krnl.pg_arr, page_index, target_pagetable, target_va, Tracked(&*lctx), Tracked(&page_lock_perm));
    proof { assert(spec_index2va(target_indices) == target_va) by { spec_va_4k_index_roundtrip_at(target_va, target_indices.0, target_indices.1, target_indices.2, target_indices.3); }; }
    pagetable_map_insert_4k(&mut krnl.pt_mp, target_pagetable, target_indices, target_l1_ptr, &source_entry, Tracked(&mut *lctx), Tracked(target_pagetable_lock_perm));
    proof {
        assert(share_one_mapping_4k_eof_transition_framing(locked_k, *krnl, page_index, source_pagetable, source_va, target_pagetable, target_va)) by { reveal(share_one_mapping_4k_eof_transition_framing); };
        share_one_mapping_4k_eof(locked_k, *krnl, page_index, source_pagetable, source_va, target_pagetable, target_va, target_process, target_container, target_thread);
    }
    krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_lock_perm));
    proof {
        assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
            map_insert_remove_absent_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
        };
        assert(krnl.pt_mp.spec_index(target_pagetable).view().user_view(LockStateU::Unlocked).mapping_4k =~= old(krnl).pt_mp.spec_index(target_pagetable).view().user_view(LockStateU::Unlocked).mapping_4k.insert(target_va,
            old(krnl).pt_mp.spec_index(source_pagetable).view().user_view(LockStateU::Unlocked).mapping_4k.spec_index(source_va)));
    }
}
}
