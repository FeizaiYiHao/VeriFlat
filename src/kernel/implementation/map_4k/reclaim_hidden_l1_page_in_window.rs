use vstd::prelude::*;
use crate::*;
use super::unmap_4k_reclaim_last_cache::reclaim_last_lock_4k_cache_with_room;
#[cfg(verus_keep_ghost)]
use super::reclaim_hidden_l1_page_in_window_eof::*;

verus! {
/// Unlink the L1 page `l1_ptr` that the held window of `va` in the read-held `pagetable` hides and that no CPU lists stale,
/// and return it through the write-held cache shard `cpu_id` of the 4K allocator `allc_ptr` of its owner `owner`, crediting
/// that allocator's write-held quota by one.
fn reclaim_hidden_l1_page_to_cache(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, pagetable: RwLockPageTableRoot, va: VAddr, l2_ptr: PageMapPtr, l1_ptr: PagePtr, owner: RwLockContainerPtr,
    allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, pagetable_perm: Tracked<&LockPerm>, Tracked(window_perm): Tracked<&LockPerm>, Tracked(page_perm): Tracked<&LockPerm>,
    Tracked(cache_perm): Tracked<&LockPerm>, Tracked(quota_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(va).0,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_va2index(va).0, spec_va2index(va).1) is Some,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_va2index(va).0, spec_va2index(va).1)->0.addr == l2_ptr,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_entry_hides_l1(l2_ptr, spec_va2index(va).2),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_entry(l2_ptr, spec_va2index(va).2).addr == l1_ptr,
        forall|l1i: L1Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l1_page(l2_ptr, spec_va2index(va).2).spec_index(l1i)]
            pei_valid(l1i) ==> !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l1_page(l2_ptr, spec_va2index(va).2).spec_index(l1i).perm.kernel_present,
        !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains((l2_ptr, spec_va2index(va).2)),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).page_closure().contains(l1_ptr),
        page_ptr_valid(l1_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Read),
        pagetable_perm.view().state() is ReadLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_perm.view().lock_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, window_of(va)), TypedLockMode::Write),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(l2_ptr, spec_va2index(va).2) == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(l1_ptr), TypedLockMode::Write),
        page_perm.state() is WriteLock,
        page_perm.thread_id() == old(lctx).thread_id(),
        page_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(l1_ptr)).view().locking_thread()->Write_lock_id,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l1_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: pagetable, table_type: PT_TYPE } }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l1_ptr)).view().view().owning_container == owner,
        old(krnl).ctn_mp.dom().contains(owner),
        old(krnl).ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allc_ptr,
        old(krnl).allc_4k_mp.dom().contains(allc_ptr),
        old(krnl).allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().len() < ALLOCATOR_MAX_WATERMARK,
        typed_lock_map_contains_mode(old(lctx).allocator_cache_4k_lock_map(), (allc_ptr, cpu_id), TypedLockMode::Write),
        cache_perm.state() is WriteLock,
        cache_perm.thread_id() == old(lctx).thread_id(),
        cache_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).allocator_quota_4k_lock_map(), allc_ptr, TypedLockMode::Write),
        quota_perm.state() is WriteLock,
        quota_perm.thread_id() == old(lctx).thread_id(),
        quota_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allc_ptr).quota.locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(l1_ptr)),
            TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(l1_ptr)), mode: TypedLockMode::Write }),
        final(krnl).allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { pt_lower: final(krnl).pt_lower, pg_arr: final(krnl).pg_arr, allc_4k_mp: final(krnl).allc_4k_mp, ..*old(krnl) }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        final(krnl).pt_lower.view() == old(krnl).pt_lower.view().insert(pagetable, final(krnl).pt_lower.view().spec_index(pagetable)),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.pagetable_window_locks == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.pagetable_window_locks,
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(window_of(va)) == (PageTableWindowView {
            l2_entry: whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(window_of(va)).l2_entry, l1_table: None,
            ..whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(window_of(va))
        }),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(window_of(va)).l2_entry.is_empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m(),
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) && w != window_of(va)
            ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w),
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(l1_ptr)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(l1_ptr)).view().locking_thread() == old(krnl).pg_arr.spec_index(page_ptr2page_index(l1_ptr)).view().locking_thread(),
        final(krnl).allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
        final(krnl).allc_4k_mp.unchanged_except(&old(krnl).allc_4k_mp, allc_ptr),
        final(krnl).allc_4k_mp.spec_index(allc_ptr).quota.view().view() == old(krnl).allc_4k_mp.spec_index(allc_ptr).quota.view().view() + 1,
        final(krnl).allc_4k_mp.spec_index(allc_ptr).quota.locking_thread() == old(krnl).allc_4k_mp.spec_index(allc_ptr).quota.locking_thread(),
        final(krnl).allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread() == old(krnl).allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread(),
{
    let pg_idx = page_ptr2page_index(l1_ptr);
    let indices = va2index(va);
    proof {
        spec_va_4k_index_roundtrip_at(va, indices.0, indices.1, indices.2, indices.3);
        spec_va_4k_index_roundtrip_at(window_of(va).va, indices.0, indices.1, indices.2, 0usize);
        page_ptr_valid_imply_page_index_valid();
        page_array_wf_at(krnl.pg_arr, pg_idx);
        allocator_perms_wf_map(krnl.allc_4k_mp); allocator_perms_wf_at(krnl.allc_4k_mp, allc_ptr);
        assert(!krnl.allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().contains(l1_ptr)) by { allocator_free_4k_pages_wf_cache_at(krnl.allc_4k_mp, krnl.pg_arr, allc_ptr, cpu_id, l1_ptr); };
        lemma_container_allocator_4k_quota_bounded(&*krnl, owner);
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        pagetable_window_typed_lock_map_aligned_at(krnl.pt_mp, krnl.pt_lower.view(), lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id(), pagetable, window_of(va));
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).higher.spec_resolve_mapping_l3_some_implies_spec_held_l3_eq(indices.0, indices.1);
    }
    let ghost pre = *krnl;
    let Tracked(page_map_perm) = pagetable_map_unlink_hidden_l1_page_rlocked(&krnl.pt_mp, Tracked(krnl.pt_lower.borrow_mut()), pagetable, (indices.0, indices.1, indices.2), l2_ptr, l1_ptr,
        Tracked(window_perm), Tracked(&mut *lctx), pagetable_perm, Ghost(pre));
    let Tracked(page_4k_perm) = page_map_to_page_perm(l1_ptr, Tracked(page_map_perm), &krnl.cpu_tlb, &krnl.cpu_arr, &krnl.pcid_needflush);
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(pg_idx);
    let (node_addr, node_perm) = page_array_retire_kernel_object_4k_to_cache(&mut krnl.pg_arr, pg_idx, Tracked(page_4k_perm), allc_ptr, cpu_id, Tracked(&*lctx), Tracked(page_perm));
    proof { lctx.update_lock_id(KernelObjId::Page(pg_idx), old_page_lock_id, krnl.pg_arr.lock_id_by_index(pg_idx)); }
    krnl.allc_4k_mp.push_cache_page_typed(allc_ptr, cpu_id, node_addr, node_perm, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
        Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(cache_perm));
    {
        let quota = krnl.allc_4k_mp.borrow_mut_quota_typed(allc_ptr, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
            Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(quota_perm));
        quota.value = quota.value + 1;
    }
    proof {
        assert(reclaim_hidden_l1_page_to_cache_eof_transition_framing(pre, *krnl, pagetable, va, l2_ptr, l1_ptr, allc_ptr, cpu_id, node_addr)) by {
            reveal(reclaim_hidden_l1_page_to_cache_eof_transition_framing);
        };
        reclaim_hidden_l1_page_to_cache_eof(pre, *krnl, pagetable, va, l2_ptr, l1_ptr, owner, allc_ptr, cpu_id, node_addr);
        reclaim_hidden_l1_page_to_cache_eof_held_windows(pre, *krnl, pagetable, va, l2_ptr, l1_ptr, allc_ptr, cpu_id, node_addr, *old(lctx));
        assert(krnl.pt_lower.view() =~= old(krnl).pt_lower.view().insert(pagetable, krnl.pt_lower.view().spec_index(pagetable)));
    }
}

/// Free the L1 page `l1_ptr` that the held window of `va` in the read-held `pagetable`, whose L2 page is `l2_ptr`, hides
/// after every CPU flushed it: lock the page, its owner's 4K cache shard `cpu_id` (draining a full shard first) and quota,
/// return the page to the cache, credit the owner's 4K quota by one, and unlock. The credit is the one recorded step; the
/// window keeps its L2 entry and no longer owns an L1 page. Returns the owner.
pub fn reclaim_hidden_l1_page_in_window(
    krnl: &mut KernelK, pagetable: RwLockPageTableRoot, va: VAddr, l2_ptr: PageMapPtr, l1_ptr: PageMapPtr, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>, pagetable_perm: Tracked<&LockPerm>, Tracked(window_perm): Tracked<&LockPerm>,
) -> (ret: RwLockContainerPtr)
    requires
        old(steps).snapshot_k() == *old(krnl),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).page_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        index_valid(NUM_CPUS, cpu_id),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
        old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()),
        old(krnl).pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(va).0,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_va2index(va).0, spec_va2index(va).1) is Some,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_va2index(va).0, spec_va2index(va).1)->0.addr == l2_ptr,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_entry_hides_l1(l2_ptr, spec_va2index(va).2),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_entry(l2_ptr, spec_va2index(va).2).addr == l1_ptr,
        forall|l1i: L1Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l1_page(l2_ptr, spec_va2index(va).2).spec_index(l1i)]
            pei_valid(l1i) ==> !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l1_page(l2_ptr, spec_va2index(va).2).spec_index(l1i).perm.kernel_present,
        !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains((l2_ptr, spec_va2index(va).2)),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Read),
        pagetable_perm.view().state() is ReadLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_perm.view().lock_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, window_of(va)), TypedLockMode::Write),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(l2_ptr, spec_va2index(va).2) == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
    ensures
        final(steps).view().len() == old(steps).view().len() + 1,
        final(steps).view().drop_last() == old(steps).view(),
        ({
            let cpu = old(lctx).cpu_id();
            let thrd_ptr = old(krnl).cpu_arr.spec_index(cpu).view().view().view().current_thread->Some_0;
            index_valid(NUM_CPUS, cpu) && typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu, TypedLockMode::Write) && old(krnl).cpu_arr.spec_index(cpu).view().view().view().state is Running
                && typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write) && old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable ==> {
                let old_u = final(steps).view().last().old_u;
                &&& mmap_4k_locked(old_u, cpu)
                &&& old_u.cpu_array[cpu as int].current_thread == Some(thrd_ptr)
                &&& old_u.thread_map[thrd_ptr].owning_container == old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container
                &&& old_u.thread_map[thrd_ptr].syscall_progress == old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()
            }
        }),
        kernel_u_container_quota_4k_increased(final(steps).view().last().old_u, final(steps).view().last().new_u, ret),
        final(steps).snapshot_k() == *final(krnl),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] == old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int],
        ret == old(krnl).pg_arr.spec_index(page_ptr2page_index(l1_ptr)).view().view().owning_container,
        ret == old(krnl).prc_mp.spec_index(old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr).view_rodata().view().owning_container,
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_threads_unchanged(old(krnl).thrd_mp, final(krnl).thrd_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(window_of(va)) == (PageTableWindowView {
            l2_entry: whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(window_of(va)).l2_entry, l1_table: None,
            ..whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(window_of(va))
        }),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(window_of(va)).l2_entry.is_empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(window_of(va).va)
            == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(window_of(va).va),
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) && w != window_of(va) ==> {
            let pre = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            let post = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable);
            &&& post.window_view(w) == pre.window_view(w)
            &&& post.mapping_2m().dom().contains(w.va) == pre.mapping_2m().dom().contains(w.va)
        },
        forall|w: WindowVa, v: VAddr|
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
            old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va)
                && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
                &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                    ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(v) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(v)
            },
{
    proof {
        let c = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        spec_va_4k_index_roundtrip_at(va, spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2, spec_va2index(va).3);
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        c.higher.wf_l4_at(spec_va2index(va).0);
        c.l3_links_l2_wf_at(c.spec_resolve_mapping_l4(spec_va2index(va).0)->0.addr, spec_va2index(va).1);
        c.wf_l2_at(l2_ptr, spec_va2index(va).2);
        pagetable_pages_wf_closure_page_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pagetable, l1_ptr);
        page_ptr_valid_imply_page_index_valid();
        process_object_pages_owner_wf_at(krnl.prc_mp, krnl.pt_mp, krnl.it_mp, krnl.pg_arr, page_ptr2page_index(l1_ptr));
    }
    let pg_idx = page_ptr2page_index(l1_ptr);
    let Tracked(page_perm) = krnl.wlock_page(pg_idx, Tracked(&mut *lctx));
    let ghost page_lctx = *lctx;
    proof { page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, pg_idx); }
    let owner = krnl.pg_arr.borrow_typed(pg_idx, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(&page_perm)).owning_container;
    proof {
        assert(krnl.ctn_mp.dom().contains(owner)) by { container_owned_pages_wf_backward_at(krnl.ctn_mp, krnl.pg_arr, pg_idx); };
        container_perms_wf_at(krnl.ctn_mp, owner);
    }
    let allc_ptr = krnl.ctn_mp.borrow_rodata(owner).borrow().allocator_ptr_4k;
    proof {
        container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, owner);
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl);
        steps.rebase_snapshot_k_if_unchanged(&*krnl);
    }
    let ghost cache_pre = *krnl;
    let Tracked(cache_perm) = reclaim_last_lock_4k_cache_with_room(krnl, allc_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps));
    proof {
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl);
        krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
    }
    let ghost mid = *krnl;
    proof {
        let cpu = old(lctx).cpu_id();
        let thrd_ptr = old(krnl).cpu_arr.spec_index(cpu).view().view().view().current_thread->Some_0;
        if index_valid(NUM_CPUS, cpu) && typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu, TypedLockMode::Write) && old(krnl).cpu_arr.spec_index(cpu).view().view().view().state is Running
            && typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write) && old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable {
            let prc_ptr = krnl.thrd_mp.spec_index(thrd_ptr).view().owning_proc;
            assert(krnl.cpu_arr.spec_index(cpu).view().view() == old(krnl).cpu_arr.spec_index(cpu).view().view() && krnl.thrd_mp.spec_index(thrd_ptr).view() == old(krnl).thrd_mp.spec_index(thrd_ptr).view());
            thread_perms_wf_at(krnl.thrd_mp, thrd_ptr); thread_cpu_wf_cpu_at(krnl.thrd_mp, krnl.cpu_arr, cpu);
            process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr);
            kernel_write_held_context_projection(&*krnl, &*lctx, cpu, prc_ptr, thrd_ptr, None);
            krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
            kernel_pagetable_mappings_projection_at(&*krnl, prc_ptr);
            assert(mmap_4k_locked(kernel_k_to_kernel_u(*krnl), cpu));
        }
    }
    proof {
        let w = window_of(va);
        let c0 = whole_pagetable(cache_pre.pt_mp, cache_pre.pt_lower.view(), pagetable);
        let c1 = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        spec_va_4k_index_roundtrip_at(w.va, spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2, 0usize);
        assert(c1.window_view(w) == c0.window_view(w) && c1.higher == c0.higher);
        assert(c0 == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable));
        assert(c1.lower.l1_page(l2_ptr, spec_va2index(va).2) == c0.lower.l1_page(l2_ptr, spec_va2index(va).2));
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        c1.higher.wf_l4_at(spec_va2index(va).0); c1.l3_links_l2_wf_at(c1.spec_resolve_mapping_l4(spec_va2index(va).0)->0.addr, spec_va2index(va).1);
        c1.wf_l2_at(l2_ptr, spec_va2index(va).2);
        assert(c1.lower.l2_entry(l2_ptr, spec_va2index(va).2).addr == l1_ptr && c1.lower.l2_page(l2_ptr).entry_lock(spec_va2index(va).2).l1() is Some);
        assert(c1.page_closure().contains(l1_ptr));
        pagetable_pages_wf_closure_page_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pagetable, l1_ptr);
        page_array_wf_at(krnl.pg_arr, pg_idx);
        assert(krnl.ctn_mp.dom().contains(owner)) by { container_owned_pages_wf_backward_at(krnl.ctn_mp, krnl.pg_arr, pg_idx); };
    }
    let Tracked(quota_perm) = krnl.wlock_allocator_quota_4k(allc_ptr, Tracked(&mut *lctx));
    let ghost locked_lctx = *lctx;
    let ghost helper_pre = *krnl;
    reclaim_hidden_l1_page_to_cache(krnl, Tracked(&mut *lctx), pagetable, va, l2_ptr, l1_ptr, owner, allc_ptr, cpu_id, pagetable_perm, Tracked(window_perm), Tracked(&page_perm),
        Tracked(&cache_perm), Tracked(&quota_perm));
    krnl.wunlock_allocator_quota_4k(allc_ptr, Tracked(&mut *lctx), Tracked(quota_perm));
    krnl.wunlock_allocator_cache_4k(allc_ptr, cpu_id, Tracked(&mut *lctx), Tracked(cache_perm));
    krnl.wunlock_page(pg_idx, Tracked(&mut *lctx), Tracked(page_perm));
    proof {
        assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
            assert(lctx.page_lock_map() =~= old(lctx).page_lock_map() && lctx.allocator_cache_4k_lock_map() =~= old(lctx).allocator_cache_4k_lock_map()
                && lctx.allocator_quota_4k_lock_map() =~= old(lctx).allocator_quota_4k_lock_map());
        };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(krnl.pt_lower.view() =~= steps.snapshot_k().pt_lower.view().insert(pagetable, krnl.pt_lower.view().spec_index(pagetable)));
        assert(whole_pagetable(cache_pre.pt_mp, cache_pre.pt_lower.view(), pagetable) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable));
        assert(page_lctx.pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map() && locked_lctx.pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map());
        kernel_page_freed_to_owner_quota_implies_u_step(&steps.snapshot_k(), &*krnl, false, pagetable, owner, allc_ptr, owner);
        assert(steps.snapshot_k() == mid);
        krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
    }
    owner
}
}
