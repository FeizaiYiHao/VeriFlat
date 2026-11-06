use vstd::prelude::*;
use crate::*;
use super::syscall_mmap_1g_map_owned::map_owned_1g_page;
#[cfg(verus_keep_ghost)]
use super::syscall_mmap_1g_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_mmap_1g_map_trace::mmap_1g_leaf_step_from_k;
#[cfg(feature = "split-crates")]
use veriflat_alloc_page::allocate_free_1g_page::allocate_free_1g_page::allocate_free_1g_page;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::allocate_free_1g_page::allocate_free_1g_page::allocate_free_1g_page;

verus! {
/// Map `va`, page `mapped` of `range`, under the big write lock of `pagetable`, whose L3 entry for `va` links no L2 page and holds no leaf below a present root entry: allocate a 1G page and publish its present, writable, executable leaf as one leaf step. Only the 1G leaf of `va` changes
/// in the table.
pub(super) fn mmap_1g_map_one_leaf(
    krnl: &mut KernelK, thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr, cpu_id: CpuId, pagetable: RwLockPageTableRoot, va: VAddr,
    Ghost(range): Ghost<VaRange1G>, Ghost(mapped): Ghost<usize>, Ghost(directory): Ghost<bool>, Ghost(hidden): Ghost<bool>, Ghost(flushed): Ghost<bool>,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, thread_perm: Tracked<&LockPerm>, pagetable_perm: Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k() == *old(krnl),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        !old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_1g >= 1,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap1g { range, mapped, directory, hidden, flushed }),
        mapped < range.len,
        range.view()[mapped as int] == va,
        old(krnl).pt_mp.dom().contains(pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        va_1g_valid(va),
        ({
            let table = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            &&& table.kernel_l4_end() <= spec_v2l4index(va)
            &&& !table.mapping_1g().dom().contains(va)
            &&& table.spec_resolve_mapping_l4(spec_v2l4index(va)) is Some
            &&& table.spec_held_l3(spec_v2l4index(va), spec_v2l3index(va)) is None
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
        final(steps).view() == old(steps).view().push(final(steps).view().last()),
        mmap_1g_leaf_step_pre(final(steps).view().last().old_u, cpu_id),
        mmap_1g_leaf_step(final(steps).view().last().old_u, final(steps).view().last().new_u, cpu_id),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        final(krnl).cpu_op.view().view()[cpu_id as int] == old(krnl).cpu_op.view().view()[cpu_id as int],
        final(krnl).thrd_mp.dom().contains(thrd_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread {
            quota_1g: final(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_1g, syscall_progress: final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress,
            ..old(krnl).thrd_mp.spec_index(thrd_ptr).view()
        }),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_1g == old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_1g - 1,
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap1g { range, mapped: (mapped + 1) as usize, directory: false, hidden, flushed }),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        !final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        final(krnl).pt_mp.spec_index(pagetable).view().proc_ptr == old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr,
        final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end,
        final(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus == old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus,
        final(krnl).pt_mp.spec_index(pagetable).view().cr3 == old(krnl).pt_mp.spec_index(pagetable).view().cr3,
        final(krnl).pt_mp.spec_index(pagetable).view().pcid == old(krnl).pt_mp.spec_index(pagetable).view().pcid,
        ({
            let pre = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            let post = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable);
            &&& post.mapping_1g() == pre.mapping_1g().insert(va, post.mapping_1g().spec_index(va))
            &&& post.mapping_1g().spec_index(va).present
            &&& post.mapping_1g().spec_index(va).write
            &&& !post.mapping_1g().spec_index(va).execute_disable
            &&& post.mapping_4k() == pre.mapping_4k()
            &&& post.mapping_2m() == pre.mapping_2m()
            &&& post.lower == pre.lower
        }),
        forall|l4i: L4Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).kernel_l4_end() <= l4i && pei_valid(l4i)
                ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i),
        forall|l4i: L4Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_l4(l4i)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).kernel_l4_end() <= l4i && pei_valid(l4i)
                ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_l4(l4i) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_l4(l4i),
        forall|l4i: L4Index, l3i: L3Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l3(l4i, l3i)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i)
                ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l3(l4i, l3i) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l3(l4i, l3i),
        forall|l4i: L4Index, l3i: L3Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_l3(l4i, l3i)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i)
                ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_l3(l4i, l3i) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_l3(l4i, l3i),
{
    proof {
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl);
        spec_va_1g_valid_index_roundtrip(va);
        krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
        krnl.thrd_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thrd_ptr);
        pagetable_lower_backup_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
    }
    let (pg_ptr, Tracked(page_lock_perm)) = allocate_free_1g_page(krnl, thrd_ptr, ctn_ptr, Tracked(&mut *lctx), Tracked(&mut *steps), thread_perm);
    let pg_idx = page_ptr2page_index(pg_ptr);
    let ghost staged_lctx = *lctx;
    let ghost staged_page_lock_id = krnl.pg_arr.lock_id_by_index(pg_idx);
    let ghost section_start = *krnl;
    assert(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable)) by {
        pagetable_lower_backup_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
    };
    proof {
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr);
    }
    map_owned_1g_page(krnl, pg_ptr, thrd_ptr, pagetable, va, Tracked(&mut *lctx), Tracked(&page_lock_perm), thread_perm, pagetable_perm);
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
        pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        assert(krnl.pt_lower.view() =~= section_start.pt_lower.view().insert(pagetable, krnl.pt_lower.view().spec_index(pagetable)));
        assert(kernel_process_1g_mapping_changed(&steps.snapshot_k(), &*krnl, prc_ptr, pagetable, va)) by { reveal(kernel_process_1g_mapping_changed); };
        krnl.kernel_step_boundary_process_1g_mapping_changed(&mut *lctx, &mut *steps, prc_ptr, pagetable, va);
        mmap_1g_leaf_step_from_k(&section_start, &unlocked_k, &unlocked_lctx, cpu_id, thrd_ptr, prc_ptr, pagetable, va, range, mapped, directory, hidden, flushed);
        assert(krnl.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g.view() =~= old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g.view());
        krnl.thrd_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thrd_ptr);
        krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    }
}
} // verus!
