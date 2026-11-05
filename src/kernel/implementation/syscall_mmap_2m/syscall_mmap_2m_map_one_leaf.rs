use vstd::prelude::*;
use crate::*;
use super::syscall_mmap_2m_map_owned::map_owned_2m_page;
use super::syscall_mmap_2m_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_mmap_2m_trace::mmap_2m_leaf_step_from_u;

verus! {
/// Map `va`, page `mapped` of `range`, under the pagetable's big read lock and the 2M window of `va` held through `window_perm`,
/// a window that links no L1 table and holds no leaf: allocate a 2M page and publish its present, writable, executable leaf as
/// one leaf step. Inside the held windows only the 2M leaf of `va` changes.
pub(super) fn mmap_2m_page(
    krnl: &mut KernelK, thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr, cpu_id: CpuId, pagetable_ptr: RwLockPageTableRoot, va: VAddr,
    Ghost(range): Ghost<VaRange2M>, Ghost(mapped): Ghost<usize>, Ghost(phase): Ghost<Mmap2mPhase>, Ghost(flushed): Ghost<bool>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    Tracked(thread_lock_perm): Tracked<&LockPerm>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>, Tracked(window_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k() == *old(krnl),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).prc_mp.dom().contains(prc_ptr),
        old(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr,
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_2m >= 1,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap2m { range, mapped, directory: Mmap2mDirectory::None, phase, flushed }),
        !(phase is Fill),
        mapped < range.len,
        range.view()[mapped as int] == va,
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        pagetable_lock_perm.state() is ReadLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        va_2m_valid(va),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va),
        typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable_ptr, window_of(va)), TypedLockMode::Write),
        window_perm.thread_id() == old(lctx).thread_id(),
        ({
            let table = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr);
            &&& table.window_view(window_of(va)).lock_state == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() })
            &&& table.spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some
            &&& table.window_view(window_of(va)).l1_table is None
            &&& table.window_view(window_of(va)).stale_cpus is None
            &&& !table.mapping_2m().dom().contains(va)
        }),
    ensures
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        held_locks_order_below(final(krnl), final(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view().len() == old(steps).view().len() + 1,
        final(steps).view().drop_last() == old(steps).view(),
        mmap_2m_leaf_step_pre(final(steps).view().last().old_u, cpu_id),
        mmap_2m_leaf_step(final(steps).view().last().old_u, final(steps).view().last().new_u, cpu_id),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
        final(krnl).cpu_op.view().view()[cpu_id as int] == old(krnl).cpu_op.view().view()[cpu_id as int],
        final(krnl).prc_mp.dom().contains(prc_ptr),
        final(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr,
        final(krnl).thrd_mp.dom().contains(thrd_ptr),
        !final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        !thread_is_dangling(final(krnl).thrd_mp.spec_index(thrd_ptr)),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr && final(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().state == old(krnl).thrd_mp.spec_index(thrd_ptr).view().state,
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_4k == old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_4k,
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_2m == old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_2m - 1,
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap2m { range, mapped: (mapped + 1) as usize, directory: Mmap2mDirectory::None, phase, flushed }),
        thread_lock_perm.lock_id() == final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        final(krnl).pt_mp.dom().contains(pagetable_ptr),
        final(krnl).pt_mp.spec_index(pagetable_ptr).view() == old(krnl).pt_mp.spec_index(pagetable_ptr).view(),
        final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        ({
            let post = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr);
            &&& post.mapping_2m().dom().contains(va)
            &&& post.mapping_2m().spec_index(va).present
            &&& post.mapping_2m().spec_index(va).write
            &&& !post.mapping_2m().spec_index(va).execute_disable
        }),
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) ==> {
            let pre = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr);
            let post = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr);
            &&& post.window_view(w).lock_state == pre.window_view(w).lock_state
            &&& post.window_view(w).stale_cpus == pre.window_view(w).stale_cpus
            &&& spec_va_2m_valid(w.va) && pre.kernel_l4_end() <= spec_v2l4index(w.va) && pre.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                && pre.window_view(w).l1_table is None ==> post.window_view(w).l1_table is None
            &&& w.va != va ==> post.mapping_2m().dom().contains(w.va) == pre.mapping_2m().dom().contains(w.va)
            &&& w.va != va && pre.mapping_2m().dom().contains(w.va) ==> post.mapping_2m().spec_index(w.va) == pre.mapping_2m().spec_index(w.va)
        },
        forall|w: WindowVa, u: VAddr|
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u)]
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u)]
            old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) && spec_v2l4index(u) == spec_v2l4index(w.va) && spec_v2l3index(u) == spec_v2l3index(w.va)
                && spec_v2l2index(u) == spec_v2l2index(w.va) ==> {
                &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u)
                &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u)
                    ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(u) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(u)
            },
{
    let ghost entry_steps = steps.view();
    proof {
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl);
        thread_perms_wf_at(krnl.thrd_mp, thrd_ptr); spec_va_2m_valid_index_roundtrip(va);
    }
    let (pg_ptr, Tracked(page_lock_perm)) = allocate_free_2m_page(krnl, thrd_ptr, ctn_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm));
    let pg_idx = page_ptr2page_index(pg_ptr);
    let ghost staged_lctx = *lctx;
    let ghost staged_page_lock_id = krnl.pg_arr.lock_id_by_index(pg_idx);
    let ghost section_start = *krnl;
    proof {
        assert(krnl.cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view());
        thread_cpu_wf_cpu_at(krnl.thrd_mp, krnl.cpu_arr, cpu_id); process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr);
    }
    map_owned_2m_page(krnl, pg_ptr, thrd_ptr, pagetable_ptr, va, Tracked(&mut *lctx), Tracked(&page_lock_perm), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm),
        Tracked(window_perm));
    let ghost leaf_k = *krnl;
    krnl.wunlock_page(pg_idx, Tracked(&mut *lctx), Tracked(page_lock_perm));
    proof {
        let unlocked_k = *krnl;
        let unlocked_lctx = *lctx;
        assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
            map_insert_overwrite_lemma(old(lctx).page_lock_map(), pg_idx, TypedHeldLock { lock_id: staged_page_lock_id, mode: TypedLockMode::Write },
                TypedHeldLock { lock_id: leaf_k.pg_arr.lock_id_by_index(pg_idx), mode: TypedLockMode::Write });
            map_insert_remove_absent_lemma(old(lctx).page_lock_map(), pg_idx, TypedHeldLock { lock_id: leaf_k.pg_arr.lock_id_by_index(pg_idx), mode: TypedLockMode::Write });
        };
        assert(kernel_process_2m_mapping_changed(&steps.snapshot_k(), &*krnl, prc_ptr, pagetable_ptr, va)) by {
            process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); reveal(kernel_process_2m_mapping_changed);
        };
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr);
        krnl.kernel_step_boundary_process_2m_mapping_changed_windowed(&mut *lctx, &mut *steps, prc_ptr, pagetable_ptr, va, prc_ptr, pagetable_ptr, thrd_ptr, thrd_ptr);
        assert(mmap_2m_leaf_step_pre(steps.view().last().old_u, cpu_id) && mmap_2m_leaf_step(steps.view().last().old_u, steps.view().last().new_u, cpu_id)) by {
            kernel_thread_quota_2m_progress_and_2m_mapping_added_pagetable_rlocked_implies_u_step(&section_start, &unlocked_k, &unlocked_lctx, cpu_id, thrd_ptr, prc_ptr, pagetable_ptr, va);
            mmap_2m_leaf_step_from_u(kernel_k_to_kernel_u(section_start), kernel_k_to_kernel_u(unlocked_k), cpu_id, prc_ptr, thrd_ptr, va,
                whole_pagetable(unlocked_k.pt_mp, unlocked_k.pt_lower.view(), pagetable_ptr).mapping_2m().spec_index(va));
        };
        assert(krnl.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_2m.view() =~= Set::empty());
        assert forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w))
            implies whole_pagetable(leaf_k.pt_mp, leaf_k.pt_lower.view(), pagetable_ptr).window_view(w) == whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).window_view(w)
                && whole_pagetable(section_start.pt_mp, section_start.pt_lower.view(), pagetable_ptr).window_view(w) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_view(w)
                && whole_pagetable(section_start.pt_mp, section_start.pt_lower.view(), pagetable_ptr).mapping_2m().dom().contains(w.va) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m().dom().contains(w.va)
                && whole_pagetable(leaf_k.pt_mp, leaf_k.pt_lower.view(), pagetable_ptr).mapping_2m().dom().contains(w.va) == whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_2m().dom().contains(w.va)
                && (whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m().dom().contains(w.va)
                    ==> whole_pagetable(section_start.pt_mp, section_start.pt_lower.view(), pagetable_ptr).mapping_2m().spec_index(w.va) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m().spec_index(w.va))
                && (whole_pagetable(leaf_k.pt_mp, leaf_k.pt_lower.view(), pagetable_ptr).mapping_2m().dom().contains(w.va)
                    ==> whole_pagetable(leaf_k.pt_mp, leaf_k.pt_lower.view(), pagetable_ptr).mapping_2m().spec_index(w.va) == whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_2m().spec_index(w.va)) by {
            assert(staged_lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) && unlocked_lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, w)));
        };
        assert forall|w: WindowVa, u: VAddr|
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u)]
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u)]
            old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) && spec_v2l4index(u) == spec_v2l4index(w.va) && spec_v2l3index(u) == spec_v2l3index(w.va)
                && spec_v2l2index(u) == spec_v2l2index(w.va) implies whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u)
                && (whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u)
                    ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(u) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(u)) by {
            assert(staged_lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) && unlocked_lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, w)));
            assert(whole_pagetable(section_start.pt_mp, section_start.pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u)
                == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u));
            assert(whole_pagetable(leaf_k.pt_mp, leaf_k.pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u)
                == whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u));
        };
    }
}
} // verus!
