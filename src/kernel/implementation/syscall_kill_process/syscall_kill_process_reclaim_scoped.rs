use vstd::prelude::*;
use crate::*;
use super::syscall_kill_process_spec::*;
use super::syscall_kill_process_trace::*;
use super::syscall_kill_process_walk::{KillScope, kill_scope_progress};
use super::syscall_kill_process_reclaim_scoped_last::{kill_reclaim_last_4k_mapping_scoped, kill_reclaim_last_iommu_4k_mapping_scoped};
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_reclaim_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_reclaim_scoped_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_reclaim_scoped_eof::*;

verus! {
/// Remove the final mapping of the page `page_ptr`, the hidden 4K leaf at `va` of the write-held page table `pagetable`,
/// and return the page through the write-held cache shard `cpu_id` of the 4K allocator `allocator_ptr` of its owner
/// `owner`, crediting that allocator's write-held quota by one.
pub(crate) fn kill_reclaim_last_4k_mapping_scoped_to_cache(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, pagetable: RwLockPageTableRoot, va: VAddr, page_ptr: PagePtr, owner: RwLockContainerPtr,
    allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, Tracked(pagetable_perm): Tracked<&LockPerm>, Tracked(page_perm): Tracked<&LockPerm>,
    Tracked(cache_perm): Tracked<&LockPerm>, Tracked(quota_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(va).0,
        old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va),
        !old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).present,
        old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).addr == page_ptr,
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pagetable, old(krnl).pt_mp.spec_index(pagetable).view()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.state() is WriteLock,
        pagetable_perm.thread_id() == old(lctx).thread_id(),
        pagetable_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        page_ptr_valid(page_ptr),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count == 1,
        !old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().is_io_page,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == owner,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        page_perm.state() is WriteLock,
        page_perm.thread_id() == old(lctx).thread_id(),
        page_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).ctn_mp.dom().contains(owner),
        old(krnl).ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        old(krnl).allc_4k_mp.dom().contains(allocator_ptr),
        old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().len() < ALLOCATOR_MAX_WATERMARK,
        typed_lock_map_contains_mode(old(lctx).allocator_cache_4k_lock_map(), (allocator_ptr, cpu_id), TypedLockMode::Write),
        cache_perm.state() is WriteLock,
        cache_perm.thread_id() == old(lctx).thread_id(),
        cache_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).allocator_quota_4k_lock_map(), allocator_ptr, TypedLockMode::Write),
        quota_perm.state() is WriteLock,
        quota_perm.thread_id() == old(lctx).thread_id(),
        quota_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(page_ptr)),
            TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write }),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pg_arr: final(krnl).pg_arr, allc_4k_mp: final(krnl).allc_4k_mp, ..*old(krnl) }),
        final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, pagetable),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().remove(va),
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_2m() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_2m(),
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_1g() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_1g(),
        final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end,
        pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pagetable, final(krnl).pt_mp.spec_index(pagetable).view()),
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(page_ptr)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread(),
        final(krnl).allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
        final(krnl).allc_4k_mp.unchanged_except(&old(krnl).allc_4k_mp, allocator_ptr),
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.view().view() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.view().view() + 1,
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.locking_thread() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.locking_thread(),
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
{
    proof { lemma_container_allocator_4k_quota_bounded(krnl, owner); }
    let page_index = page_ptr2page_index(page_ptr);
    let indices = va2index(va);
    assert(krnl.pt_mp.perms_wf() && krnl.pt_mp.spec_index(pagetable).inv() && spec_index2va(indices) == va) by { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); spec_va_4k_index_roundtrip_at(va, indices.0, indices.1, indices.2, indices.3); };
    let l1_ptr;
    {
        let pt = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_perm));
        assert(pt.spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some) by { reveal(PageTable::wf_mapping_4k); };
        let l4 = pt.get_entry_l4(indices.0).unwrap();
        let l3 = pt.get_entry_l3(indices.0, indices.1, &l4).unwrap();
        let l2 = pt.get_entry_l2(indices.0, indices.1, indices.2, &l3).unwrap();
        l1_ptr = l2.addr;
    }
    assert(krnl.pg_arr.spec_index(page_index).view().view().addr == page_ptr && index_valid(NUM_PAGES, page_index) && krnl.pg_arr.spec_index(page_index).view().is_init()
        && krnl.pg_arr.spec_index(page_index).view().view().state is Mapped4k && krnl.pg_arr.spec_index(page_index).view().view().mappings().contains((pagetable, va))) by {
        page_ptr_valid_imply_page_index_valid(); page_array_wf_at(krnl.pg_arr, page_index); mapped_4k_page_pagetable_wf_pagetable_at(krnl.pt_mp, krnl.pg_arr, pagetable, va); page_ptr_roundtrip();
    };
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
    assert(krnl.allc_4k_mp.perms_wf() && krnl.allc_4k_mp.spec_index(allocator_ptr).wf() && krnl.allc_4k_mp.spec_index(allocator_ptr).quota.is_init() && !krnl.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().contains(page_ptr)) by {
        allocator_perms_wf_map(krnl.allc_4k_mp); allocator_perms_wf_at(krnl.allc_4k_mp, allocator_ptr); container_allocator_free_4k_page_wf_cache_at(krnl.allc_4k_mp, krnl.pg_arr, allocator_ptr, cpu_id, page_ptr);
    };
    let (node_addr, node_perm) = page_array_remove_last_4k_mapping_to_cache(&mut krnl.pg_arr, page_index, pagetable, va, allocator_ptr, cpu_id, Tracked(&*lctx), Tracked(page_perm));
    krnl.allc_4k_mp.push_cache_page_typed(allocator_ptr, cpu_id, node_addr, node_perm, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
        Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(cache_perm));
    {
        let quota = krnl.allc_4k_mp.borrow_mut_quota_typed(allocator_ptr, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
            Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(quota_perm));
        quota.value = quota.value + 1;
    }
    pagetable_map_unmap_4k_kernel(&mut krnl.pt_mp, pagetable, indices, l1_ptr, Tracked(&mut *lctx), Tracked(pagetable_perm));
    proof {
        lctx.update_lock_id(KernelObjId::Page(page_index), old_page_lock_id, krnl.pg_arr.lock_id_by_index(page_index));
        assert(typed_lock_maps_inserted(old(lctx), lctx, KernelObjId::Page(page_index), TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write })) by {
            map_insert_overwrite_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: old_page_lock_id, mode: TypedLockMode::Write },
                TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
        };
        assert(kill_reclaim_unmapped_4k_page_scoped_eof_transition_framing(*old(krnl), *krnl, pagetable, va, page_ptr, allocator_ptr, cpu_id, node_addr)) by {
            reveal(kill_reclaim_unmapped_4k_page_scoped_eof_transition_framing);
        };
        kill_reclaim_unmapped_4k_page_scoped_eof(*old(krnl), *krnl, pagetable, va, page_ptr, owner, allocator_ptr, cpu_id, node_addr);
    }
}

/// Unmap the hidden 4K leaf at `va` of the write-held page table `pagetable` of the target, freeing its page when no other
/// mapping remains and crediting the page's 4K quota to its owner, the target's container or one of its ancestors, in one
/// step that extends the kill's partial trace.
pub(crate) fn kill_reclaim_unmapped_4k_page_scoped(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, pagetable: RwLockPageTableRoot, va: VAddr, Tracked(pagetable_perm): Tracked<&LockPerm>, Ghost(stage): Ghost<KillStage>,
    Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(steps).snapshot_k() == *old(krnl),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).page_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_MAJOR),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)]
            old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), target, TypedLockMode::Write),
        old(krnl).prc_mp.dom().contains(target),
        old(krnl).prc_mp.spec_index(target).being_killed(),
        old(krnl).prc_mp.spec_index(target).view().pagetable == pagetable,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_scope_progress(scope, target, stage),
        scope matches KillScope::Container { container } ==> old(krnl).ctn_mp.dom().contains(container) && typed_lock_map_contains_mode(old(lctx).container_lock_map(), container, TypedLockMode::Write),
        old(krnl).pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(va).0,
        old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va),
        !old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(va).present,
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pagetable, old(krnl).pt_mp.spec_index(pagetable).view()),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.state() is WriteLock,
        pagetable_perm.thread_id() == old(lctx).thread_id(),
        pagetable_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_threads_unchanged(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().remove(va),
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_2m() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_2m(),
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_1g() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_1g(),
        final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end,
        pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pagetable, final(krnl).pt_mp.spec_index(pagetable).view()),
{
    let ghost entry_lctx = *lctx;
    let indices = va2index(va);
    proof {
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, target);
        assert(spec_index2va(indices) == va) by { spec_va_4k_index_roundtrip_at(va, indices.0, indices.1, indices.2, indices.3); };
    }
    let pt = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_perm));
    let l4 = pt.get_entry_l4(indices.0).unwrap();
    let l3 = pt.get_entry_l3(indices.0, indices.1, &l4).unwrap();
    let l2 = pt.get_entry_l2(indices.0, indices.1, indices.2, &l3).unwrap();
    let page_ptr = pt.get_entry_l1(indices.0, indices.1, indices.2, indices.3, &l2).unwrap().addr;
    let page_index = page_ptr2page_index(page_ptr);
    proof { mapped_4k_page_pagetable_wf_pagetable_at(krnl.pt_mp, krnl.pg_arr, pagetable, va); }
    let Tracked(page_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));
    proof { page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, page_index); }
    let (ref_count, is_io_page, owner) = {
        let page = krnl.pg_arr.borrow_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(&page_perm));
        (page.ref_count, page.is_io_page, page.owning_container)
    };
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
    if ref_count > 1 || is_io_page {
        remove_4k_mapping_without_free(krnl, pagetable, va, page_ptr, Tracked(&mut *lctx), Tracked(pagetable_perm), Tracked(&page_perm));
        krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_perm));
        proof {
            assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
                map_insert_overwrite_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: old_page_lock_id, mode: TypedLockMode::Write },
                    TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
                map_insert_remove_absent_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
            };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl);
            krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
        }
    } else {
        kill_reclaim_last_4k_mapping_scoped(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, pagetable, va, page_ptr, owner,
            Tracked(pagetable_perm), Tracked(page_perm), Ghost(stage), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx), Ghost(entry_lctx));
    }
}

/// Remove the final mapping of the page `page_ptr`, the hidden 4K leaf at `indices` of the write-held IOMMU table
/// `iommu_table`, and return the page through the write-held cache shard `cpu_id` of the 4K allocator `allocator_ptr` of its owner
/// `owner`, crediting that allocator's write-held quota by one.
pub(crate) fn kill_reclaim_last_iommu_4k_mapping_scoped_to_cache(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, iommu_table: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index, L1Index), page_ptr: PagePtr, owner: RwLockContainerPtr,
    allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, Tracked(iommu_perm): Tracked<&LockPerm>, Tracked(page_perm): Tracked<&LockPerm>,
    Tracked(cache_perm): Tracked<&LockPerm>, Tracked(quota_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).it_mp.dom().contains(iommu_table),
        pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va(indices)),
        !old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(spec_index2va(indices)).present,
        old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(spec_index2va(indices)).addr == page_ptr,
        typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table, TypedLockMode::Write),
        iommu_perm.state() is WriteLock,
        iommu_perm.thread_id() == old(lctx).thread_id(),
        iommu_perm.lock_id() == old(krnl).it_mp.spec_index(iommu_table).locking_thread()->Write_lock_id,
        page_ptr_valid(page_ptr),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count == 1,
        !old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().is_io_page,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == owner,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        page_perm.state() is WriteLock,
        page_perm.thread_id() == old(lctx).thread_id(),
        page_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).ctn_mp.dom().contains(owner),
        old(krnl).ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        old(krnl).allc_4k_mp.dom().contains(allocator_ptr),
        old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().len() < ALLOCATOR_MAX_WATERMARK,
        typed_lock_map_contains_mode(old(lctx).allocator_cache_4k_lock_map(), (allocator_ptr, cpu_id), TypedLockMode::Write),
        cache_perm.state() is WriteLock,
        cache_perm.thread_id() == old(lctx).thread_id(),
        cache_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).allocator_quota_4k_lock_map(), allocator_ptr, TypedLockMode::Write),
        quota_perm.state() is WriteLock,
        quota_perm.thread_id() == old(lctx).thread_id(),
        quota_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(page_ptr)),
            TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write }),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { it_mp: final(krnl).it_mp, pg_arr: final(krnl).pg_arr, allc_4k_mp: final(krnl).allc_4k_mp, ..*old(krnl) }),
        final(krnl).it_mp.unchanged_except(&old(krnl).it_mp, iommu_table),
        final(krnl).it_mp.spec_index(iommu_table).locking_thread() == old(krnl).it_mp.spec_index(iommu_table).locking_thread(),
        final(krnl).it_mp.spec_index(iommu_table).being_killed() == old(krnl).it_mp.spec_index(iommu_table).being_killed(),
        final(krnl).it_mp.spec_index(iommu_table).view().mapping_4k() == old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().remove(spec_index2va(indices)),
        final(krnl).it_mp.spec_index(iommu_table).view().mapping_2m() == old(krnl).it_mp.spec_index(iommu_table).view().mapping_2m(),
        final(krnl).it_mp.spec_index(iommu_table).view().mapping_1g() == old(krnl).it_mp.spec_index(iommu_table).view().mapping_1g(),
        final(krnl).it_mp.spec_index(iommu_table).view().kernel_l4_end == old(krnl).it_mp.spec_index(iommu_table).view().kernel_l4_end,
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(page_ptr)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread(),
        final(krnl).allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
        final(krnl).allc_4k_mp.unchanged_except(&old(krnl).allc_4k_mp, allocator_ptr),
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.view().view() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.view().view() + 1,
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.locking_thread() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.locking_thread(),
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
{
    proof { lemma_container_allocator_4k_quota_bounded(krnl, owner); }
    let page_index = page_ptr2page_index(page_ptr);
    let iova = index2va(indices);
    proof { iommu_table_perms_wf_map(krnl.it_mp); iommu_table_perms_wf_at(krnl.it_mp, iommu_table); iommu_table_perms_wf_kernel_l4_end_at(krnl.it_mp, iommu_table); }
    let l1_ptr;
    {
        let it = krnl.it_mp.borrow_typed(iommu_table, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), Tracked(iommu_perm));
        assert(it.spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some) by { reveal(PageTable::wf_mapping_4k); };
        let l4 = it.get_entry_l4(indices.0).unwrap();
        let l3 = it.get_entry_l3(indices.0, indices.1, &l4).unwrap();
        let l2 = it.get_entry_l2(indices.0, indices.1, indices.2, &l3).unwrap();
        l1_ptr = l2.addr;
    }
    assert(krnl.pg_arr.spec_index(page_index).view().view().addr == page_ptr && index_valid(NUM_PAGES, page_index) && krnl.pg_arr.spec_index(page_index).view().is_init()
        && krnl.pg_arr.spec_index(page_index).view().view().state is Mapped4k && krnl.pg_arr.spec_index(page_index).view().view().iommu_mappings().contains((iommu_table, iova))) by {
        page_ptr_valid_imply_page_index_valid(); page_array_wf_at(krnl.pg_arr, page_index); page_iommu_table_wf_table_at(krnl.ctn_mp, krnl.prc_mp, krnl.it_mp, krnl.pg_arr, iommu_table, iova); page_ptr_roundtrip();
    };
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
    assert(krnl.allc_4k_mp.perms_wf() && krnl.allc_4k_mp.spec_index(allocator_ptr).wf() && krnl.allc_4k_mp.spec_index(allocator_ptr).quota.is_init() && !krnl.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().contains(page_ptr)) by {
        allocator_perms_wf_map(krnl.allc_4k_mp); allocator_perms_wf_at(krnl.allc_4k_mp, allocator_ptr); container_allocator_free_4k_page_wf_cache_at(krnl.allc_4k_mp, krnl.pg_arr, allocator_ptr, cpu_id, page_ptr);
    };
    let (node_addr, node_perm) = page_array_remove_last_4k_iommu_mapping_to_cache(&mut krnl.pg_arr, page_index, iommu_table, iova, allocator_ptr, cpu_id, Tracked(&*lctx), Tracked(page_perm));
    krnl.allc_4k_mp.push_cache_page_typed(allocator_ptr, cpu_id, node_addr, node_perm, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
        Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(cache_perm));
    {
        let quota = krnl.allc_4k_mp.borrow_mut_quota_typed(allocator_ptr, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
            Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(quota_perm));
        quota.value = quota.value + 1;
    }
    iommu_table_map_unmap_4k_kernel(&mut krnl.it_mp, iommu_table, indices, l1_ptr, Tracked(&mut *lctx), Tracked(iommu_perm));
    proof {
        lctx.update_lock_id(KernelObjId::Page(page_index), old_page_lock_id, krnl.pg_arr.lock_id_by_index(page_index));
        assert(typed_lock_maps_inserted(old(lctx), lctx, KernelObjId::Page(page_index), TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write })) by {
            map_insert_overwrite_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: old_page_lock_id, mode: TypedLockMode::Write },
                TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
        };
        old(krnl).it_mp.typed_lock_map_aligned_write_at(old(lctx).iommu_table_lock_map(), old(lctx).thread_id(), iommu_table);
        assert(kill_reclaim_unmapped_iommu_4k_page_scoped_eof_transition_framing(*old(krnl), *krnl, iommu_table, indices, page_ptr, allocator_ptr, cpu_id, node_addr)) by {
            reveal(kill_reclaim_unmapped_iommu_4k_page_scoped_eof_transition_framing);
        };
        kill_reclaim_unmapped_iommu_4k_page_scoped_eof(*old(krnl), *krnl, iommu_table, indices, page_ptr, owner, allocator_ptr, cpu_id, node_addr);
    }
}

/// Unmap the hidden 4K leaf at `indices` of the write-held IOMMU table `iommu_table` of the target, freeing its page when no other
/// mapping remains and crediting the page's 4K quota to its owner, the target's container or one of its ancestors, in one
/// step that extends the kill's partial trace.
pub(crate) fn kill_reclaim_unmapped_iommu_4k_page_scoped(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, iommu_table: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index, L1Index), Tracked(iommu_perm): Tracked<&LockPerm>, Ghost(stage): Ghost<KillStage>,
    Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(steps).snapshot_k() == *old(krnl),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).page_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_MAJOR),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)]
            old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), target, TypedLockMode::Write),
        old(krnl).prc_mp.dom().contains(target),
        old(krnl).prc_mp.spec_index(target).being_killed(),
        old(krnl).prc_mp.spec_index(target).view().iommu_table == Some(iommu_table),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_scope_progress(scope, target, stage),
        scope matches KillScope::Container { container } ==> old(krnl).ctn_mp.dom().contains(container) && typed_lock_map_contains_mode(old(lctx).container_lock_map(), container, TypedLockMode::Write),
        old(krnl).it_mp.dom().contains(iommu_table),
        pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va(indices)),
        !old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(spec_index2va(indices)).present,
        typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table, TypedLockMode::Write),
        iommu_perm.state() is WriteLock,
        iommu_perm.thread_id() == old(lctx).thread_id(),
        iommu_perm.lock_id() == old(krnl).it_mp.spec_index(iommu_table).locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_threads_unchanged(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx)),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        final(krnl).it_mp.dom().contains(iommu_table),
        final(krnl).it_mp.spec_index(iommu_table).locking_thread() == old(krnl).it_mp.spec_index(iommu_table).locking_thread(),
        final(krnl).it_mp.spec_index(iommu_table).being_killed() == old(krnl).it_mp.spec_index(iommu_table).being_killed(),
        final(krnl).it_mp.spec_index(iommu_table).view().mapping_4k() == old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().remove(spec_index2va(indices)),
        final(krnl).it_mp.spec_index(iommu_table).view().mapping_2m() == old(krnl).it_mp.spec_index(iommu_table).view().mapping_2m(),
        final(krnl).it_mp.spec_index(iommu_table).view().mapping_1g() == old(krnl).it_mp.spec_index(iommu_table).view().mapping_1g(),
        final(krnl).it_mp.spec_index(iommu_table).view().kernel_l4_end == old(krnl).it_mp.spec_index(iommu_table).view().kernel_l4_end,
{
    let ghost entry_lctx = *lctx;
    let iova = index2va(indices);
    proof {
        iommu_table_perms_wf_map(krnl.it_mp); iommu_table_perms_wf_at(krnl.it_mp, iommu_table); iommu_table_perms_wf_kernel_l4_end_at(krnl.it_mp, iommu_table);
        process_iommu_table_match_process_at(krnl.prc_mp, krnl.it_mp, target);
    }
    let it = krnl.it_mp.borrow_typed(iommu_table, Ghost(lctx.iommu_table_lock_map()), Tracked(&*lctx), Tracked(iommu_perm));
    assert(it.spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some) by { reveal(PageTable::wf_mapping_4k); };
    let l4 = it.get_entry_l4(indices.0).unwrap();
    let l3 = it.get_entry_l3(indices.0, indices.1, &l4).unwrap();
    let l2 = it.get_entry_l2(indices.0, indices.1, indices.2, &l3).unwrap();
    let page_ptr = it.get_entry_l1(indices.0, indices.1, indices.2, indices.3, &l2).unwrap().addr;
    let page_index = page_ptr2page_index(page_ptr);
    proof { assert(krnl.pg_arr.lock_id_by_index(page_index).major == MAPPED_PAGE_LOCK_MAJOR) by { page_iommu_table_wf_table_at(krnl.ctn_mp, krnl.prc_mp, krnl.it_mp, krnl.pg_arr, iommu_table, iova); }; }
    let Tracked(page_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));
    proof { page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, page_index); }
    let (ref_count, is_io_page, owner) = {
        let page = krnl.pg_arr.borrow_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(&page_perm));
        (page.ref_count, page.is_io_page, page.owning_container)
    };
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
    if ref_count > 1 || is_io_page {
        remove_iommu_4k_mapping_without_free(krnl, iommu_table, indices, page_ptr, Tracked(&mut *lctx), Tracked(iommu_perm), Tracked(&page_perm));
        krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_perm));
        proof {
            assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
                map_insert_overwrite_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: old_page_lock_id, mode: TypedLockMode::Write },
                    TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
                map_insert_remove_absent_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
            };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl);
            krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
        }
    } else {
        kill_reclaim_last_iommu_4k_mapping_scoped(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, iommu_table, indices, page_ptr,
            owner, Tracked(iommu_perm), Tracked(page_perm), Ghost(stage), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx), Ghost(entry_lctx));
    }
}
}
