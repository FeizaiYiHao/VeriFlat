use vstd::prelude::*;
use crate::*;
use super::syscall_kill_process_spec::*;
use super::syscall_kill_process_trace::*;
use super::syscall_kill_process_walk_spec::KillScope;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_walk_spec::kill_scope_progress;
#[cfg(feature = "split-crates")]
use veriflat_map_4k::map_4k::reclaim_held_2m_page::remove_held_2m_mapping_without_free;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::map_4k::reclaim_held_2m_page::remove_held_2m_mapping_without_free;
#[cfg(feature = "split-crates")]
use veriflat_alloc_page::free_2m_page::drain_2m_cache_batch;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::free_2m_page::drain_2m_cache_batch;
#[cfg(all(verus_keep_ghost, feature = "split-crates"))]
use veriflat_alloc_page::free_4k_page::kill_container_quota_fold::lemma_container_allocator_2m_quota_bounded;
#[cfg(all(verus_keep_ghost, not(feature = "split-crates")))]
use crate::kernel::implementation::free_4k_page::kill_container_quota_fold::lemma_container_allocator_2m_quota_bounded;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_reclaim_scoped_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_reclaim_scoped_2m_eof::*;

verus! {
/// Write-lock the cache shard `cpu_id` of the 2M allocator `allc_ptr`, first moving a batch of a shard at its 2M watermark to
/// the allocator's global pool; the lock changes nothing the projection shows and keeps every held object, and a step boundary
/// follows.
fn kill_reclaim_lock_cache_2m(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    Ghost(pg_idx): Ghost<PageIndex>,
) -> (ret: Tracked<LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).allc_2m_mp.dom().contains(allc_ptr),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_2M_MAJOR),
        index_valid(NUM_PAGES, pg_idx),
        old(lctx).page_lock_map().dom().contains(pg_idx),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
        old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::AllocatorCache(PageSize::SZ2m, allc_ptr, cpu_id), final(lctx).allocator_cache_2m_lock_map()[(allc_ptr, cpu_id)]),
        typed_lock_map_contains_mode(final(lctx).allocator_cache_2m_lock_map(), (allc_ptr, cpu_id), TypedLockMode::Write),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).view() == old(steps).view(),
        final(steps).snapshot_k() == *final(krnl),
        ret.view().state() is WriteLock,
        ret.view().thread_id() == final(lctx).thread_id(),
        ret.view().lock_id() == final(krnl).allc_2m_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        final(krnl).allc_2m_mp.dom().contains(allc_ptr),
        final(krnl).allc_2m_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().len() < ALLOCATOR_MAX_WATERMARK,
        final(krnl).ctn_mp.dom().contains(old(krnl).pg_arr.spec_index(pg_idx).view().view().owning_container),
        final(krnl).ctn_mp.spec_index(old(krnl).pg_arr.spec_index(pg_idx).view().view().owning_container).view_rodata() == old(krnl).ctn_mp.spec_index(old(krnl).pg_arr.spec_index(pg_idx).view().view().owning_container).view_rodata(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] == old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int],
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_threads_unchanged(old(krnl).thrd_mp, final(krnl).thrd_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        forall|p: RwLockPageTableRoot| #![trigger old(lctx).pagetable_lock_map().dom().contains(p)] typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), p, TypedLockMode::Write)
            ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), p) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), p),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
{
    proof { container_owned_pages_wf_backward_at(krnl.ctn_mp, krnl.pg_arr, pg_idx); held_kernel_objects_unchanged_reflexive(&*krnl, &*lctx); }
    let Tracked(cache_perm) = krnl.wlock_allocator_cache_2m(allc_ptr, cpu_id, Tracked(&mut *lctx));
    let len = krnl.allc_2m_mp.borrow_cache_typed(allc_ptr, cpu_id, Ghost(lctx.allocator_cache_2m_lock_map()), Tracked(&*lctx), Tracked(&cache_perm)).linked_list.len();
    if len >= ALLOCATOR_MAX_WATERMARK_2M {
        let Tracked(pool_perm) = krnl.wlock_allocator_global_pool_2m(allc_ptr, Tracked(&mut *lctx));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(old(krnl), &*krnl);
        }
        drain_2m_cache_batch(krnl, allc_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&cache_perm), Tracked(&pool_perm));
        krnl.wunlock_allocator_global_pool_2m(allc_ptr, Tracked(&mut *lctx), Tracked(pool_perm));
        proof {
            assert(lctx.allocator_global_pool_2m_lock_map() =~= old(lctx).allocator_global_pool_2m_lock_map());
            kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl);
            krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
        }
    } else {
        proof {
            enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
            kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl);
            krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
        }
    }
    Tracked(cache_perm)
}

/// Remove the final mapping of the 2M page `pg_ptr`, the held 2M leaf at `va` of the write-held page table `pagetable`, which
/// lists no cpu stale and whose user root entries no longer resolve, clear the leaf, and return the page through the
/// write-held cache shard `cpu_id` of the 2M allocator `allc_ptr` of its owner `owner`, crediting that allocator's write-held
/// quota by one.
fn kill_reclaim_last_held_2m_mapping_scoped_to_cache(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, owner: RwLockContainerPtr,
    allc_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, Tracked(pagetable_perm): Tracked<&LockPerm>, Tracked(page_perm): Tracked<&LockPerm>,
    Tracked(cache_perm): Tracked<&LockPerm>, Tracked(quota_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).pt_mp.dom().contains(pagetable),
        va_2m_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_v2l4index(va),
        forall|l4i: L4Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i) is None,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))->0.addr == pg_ptr,
        old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.state() is WriteLock,
        pagetable_perm.thread_id() == old(lctx).thread_id(),
        pagetable_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        page_ptr_valid(pg_ptr),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Mapped2m,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().mappings().contains((pagetable, va)),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().ref_count == 1,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == owner,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write),
        page_perm.state() is WriteLock,
        page_perm.thread_id() == old(lctx).thread_id(),
        page_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id,
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).ctn_mp.dom().contains(owner),
        old(krnl).ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_2m == allc_ptr,
        old(krnl).allc_2m_mp.dom().contains(allc_ptr),
        old(krnl).allc_2m_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().len() < ALLOCATOR_MAX_WATERMARK,
        typed_lock_map_contains_mode(old(lctx).allocator_cache_2m_lock_map(), (allc_ptr, cpu_id), TypedLockMode::Write),
        cache_perm.state() is WriteLock,
        cache_perm.thread_id() == old(lctx).thread_id(),
        cache_perm.lock_id() == old(krnl).allc_2m_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).allocator_quota_2m_lock_map(), allc_ptr, TypedLockMode::Write),
        quota_perm.state() is WriteLock,
        quota_perm.thread_id() == old(lctx).thread_id(),
        quota_perm.lock_id() == old(krnl).allc_2m_mp.spec_index(allc_ptr).quota.locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(pg_ptr)),
            TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(pg_ptr)), mode: TypedLockMode::Write }),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, pg_arr: final(krnl).pg_arr, allc_2m_mp: final(krnl).allc_2m_mp, ..*old(krnl) }),
        final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, pagetable),
        final(krnl).pt_lower.view() == old(krnl).pt_lower.view().insert(pagetable, final(krnl).pt_lower.view().spec_index(pagetable)),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        ({
            let old_c = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            let new_c = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable);
            &&& new_c.higher == old_c.higher && new_c.mapping_4k() == old_c.mapping_4k() && new_c.mapping_2m() == old_c.mapping_2m() && new_c.page_closure() == old_c.page_closure()
            &&& new_c.lower.l2_perms.dom() == old_c.lower.l2_perms.dom() && new_c.lower.pagetable_window_locks == old_c.lower.pagetable_window_locks && new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
            &&& old_c.lower.hidden_l1_tables_in_locked_windows() ==> new_c.lower.hidden_l1_tables_in_locked_windows()
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_entry(p, i)] (p, i) != (old_c.spec_held_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr, spec_v2l2index(va)) ==> new_c.lower.l2_entry(p, i) == old_c.lower.l2_entry(p, i)
            &&& new_c.lower.l2_entry(old_c.spec_held_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr, spec_v2l2index(va)).is_empty()
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_owner(p, i)] new_c.lower.l2_owner(p, i) == old_c.lower.l2_owner(p, i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_l2(l4i, l3i, l2i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_l2(l4i, l3i, l2i) == old_c.spec_held_l2(l4i, l3i, l2i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_2m_l2(l4i, l3i, l2i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))
                    ==> new_c.spec_held_2m_l2(l4i, l3i, l2i) == old_c.spec_held_2m_l2(l4i, l3i, l2i)
            &&& new_c.spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is None
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)
        }),
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(pg_ptr)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread(),
        final(krnl).allc_2m_mp.dom() == old(krnl).allc_2m_mp.dom(),
        final(krnl).allc_2m_mp.unchanged_except(&old(krnl).allc_2m_mp, allc_ptr),
        final(krnl).allc_2m_mp.spec_index(allc_ptr).quota.view().view() == old(krnl).allc_2m_mp.spec_index(allc_ptr).quota.view().view() + 1,
        final(krnl).allc_2m_mp.spec_index(allc_ptr).quota.locking_thread() == old(krnl).allc_2m_mp.spec_index(allc_ptr).quota.locking_thread(),
        final(krnl).allc_2m_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread() == old(krnl).allc_2m_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
{
    proof { lemma_container_allocator_2m_quota_bounded(krnl, owner); }
    let pg_idx = page_ptr2page_index(pg_ptr);
    let indices = va2index(va);
    proof {
        spec_va_2m_valid_index_roundtrip(va); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).wf_mapping_2m_at(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va));
        krnl.default_pagetable_wf_at(pagetable);
        assert(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_resolve_mapping_l4(spec_v2l4index(va)) is None);
    }
    assert(krnl.pg_arr.spec_index(pg_idx).view().view().addr == pg_ptr && index_valid(NUM_PAGES, pg_idx) && krnl.pg_arr.spec_index(pg_idx).view().is_init()) by { page_ptr_valid_imply_page_index_valid(); page_array_wf_at(krnl.pg_arr, pg_idx); page_ptr_roundtrip(); };
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(pg_idx);
    assert(krnl.allc_2m_mp.perms_wf() && krnl.allc_2m_mp.spec_index(allc_ptr).wf() && krnl.allc_2m_mp.spec_index(allc_ptr).quota.is_init() && !krnl.allc_2m_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().contains(pg_ptr)) by {
        allocator_perms_wf_map(krnl.allc_2m_mp); allocator_perms_wf_at(krnl.allc_2m_mp, allc_ptr); allocator_free_2m_pages_wf_cache_at(krnl.allc_2m_mp, krnl.pg_arr, allc_ptr, cpu_id, pg_ptr);
    };
    let (node_addr, node_perm) = page_array_remove_last_2m_mapping_to_cache(&mut krnl.pg_arr, pg_idx, pagetable, va, allc_ptr, cpu_id, Tracked(&*lctx), Tracked(page_perm));
    krnl.allc_2m_mp.push_cache_page_typed(allc_ptr, cpu_id, node_addr, node_perm, Ghost(lctx.allocator_quota_2m_lock_map()), Ghost(lctx.allocator_cache_2m_lock_map()),
        Ghost(lctx.allocator_global_pool_2m_lock_map()), Tracked(&*lctx), Tracked(cache_perm));
    {
        let quota = krnl.allc_2m_mp.borrow_mut_quota_typed(allc_ptr, Ghost(lctx.allocator_quota_2m_lock_map()), Ghost(lctx.allocator_cache_2m_lock_map()),
            Ghost(lctx.allocator_global_pool_2m_lock_map()), Tracked(&*lctx), Tracked(quota_perm));
        quota.value = quota.value + 1;
    }
    pagetable_map_clear_held_2m_leaf(&mut krnl.pt_mp, Tracked(krnl.pt_lower.borrow_mut()), pagetable, (indices.0, indices.1, indices.2), Tracked(&mut *lctx), Tracked(pagetable_perm));
    proof {
        lctx.update_lock_id(KernelObjId::Page(pg_idx), old_page_lock_id, krnl.pg_arr.lock_id_by_index(pg_idx));
        assert(typed_lock_maps_inserted(old(lctx), lctx, KernelObjId::Page(pg_idx), TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(pg_idx), mode: TypedLockMode::Write })) by {
            map_insert_overwrite_lemma(old(lctx).page_lock_map(), pg_idx, TypedHeldLock { lock_id: old_page_lock_id, mode: TypedLockMode::Write },
                TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(pg_idx), mode: TypedLockMode::Write });
        };
        assert(kill_reclaim_held_2m_page_scoped_eof_transition_framing(*old(krnl), *krnl, pagetable, va, pg_ptr, allc_ptr, cpu_id, node_addr)) by { reveal(kill_reclaim_held_2m_page_scoped_eof_transition_framing); };
        kill_reclaim_held_2m_page_scoped_eof(*old(krnl), *krnl, pagetable, va, pg_ptr, owner, allc_ptr, cpu_id, node_addr);
    }
}

/// Free the 2M page `pg_ptr` whose last mapping is the held 2M leaf at `va` of the write-held page table `pagetable` of the
/// target, which lists no cpu stale and whose user root entries no longer resolve: clear the leaf, return the page through the
/// cache shard `cpu_id` of its owner `owner`'s 2M allocator, credit that allocator's quota by one, and release the
/// write-held page, in one step that extends the kill's partial trace. The killer held `entry_lctx` before it write-locked
/// the page.
fn kill_reclaim_last_held_2m_mapping_scoped(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, target: RwLockProcessPtr, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, owner: RwLockContainerPtr,
    Tracked(pagetable_perm): Tracked<&LockPerm>, Tracked(page_perm): Tracked<LockPerm>, Ghost(stage): Ghost<KillStage>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
    Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>, Ghost(entry_lctx): Ghost<LocalContext>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        *old(krnl) == (KernelK { pg_arr: old(krnl).pg_arr, ..old(steps).snapshot_k() }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        old(krnl).pg_arr.unchanged_except(&old(steps).snapshot_k().pg_arr, page_ptr2page_index(pg_ptr)),
        !entry_lctx.page_lock_map().dom().contains(page_ptr2page_index(pg_ptr)),
        lock_ensures(&entry_lctx, old(lctx), old(steps).snapshot_k().pg_arr.lock_id_by_index(page_ptr2page_index(pg_ptr)), KernelObjId::Page(page_ptr2page_index(pg_ptr))),
        entry_lctx.page_lock_map().dom().is_empty(),
        held_locks_order_below(&old(steps).snapshot_k(), &entry_lctx, ALLOCATOR_CACHE_2M_MAJOR),
        entry_lctx.scheduler_lock_map().dom().is_empty(),
        entry_lctx.cpu_offline_flag_lock_map().dom().is_empty(),
        entry_lctx.cpu_set_lock_map().dom().is_empty(),
        entry_lctx.pcid_needflush_lock_map().dom().is_empty(),
        entry_lctx.allocator_quota_4k_lock_map().dom().is_empty(),
        entry_lctx.allocator_quota_2m_lock_map().dom().is_empty(),
        entry_lctx.allocator_quota_1g_lock_map().dom().is_empty(),
        forall|held_cpu_id: CpuId| #![trigger entry_lctx.cpu_lock_map().dom().contains(held_cpu_id)]
            entry_lctx.cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(entry_lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(entry_lctx.process_lock_map(), prc_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(entry_lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(entry_lctx.process_lock_map(), target, TypedLockMode::Write),
        old(krnl).prc_mp.dom().contains(target),
        old(krnl).prc_mp.spec_index(target).being_killed(),
        old(krnl).prc_mp.spec_index(target).view().pagetable == pagetable,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == kill_scope_progress(scope, target, stage),
        scope matches KillScope::Container { container } ==> old(krnl).ctn_mp.dom().contains(container) && typed_lock_map_contains_mode(entry_lctx.container_lock_map(), container, TypedLockMode::Write),
        scope is Subtree ==> old(krnl).prc_mp.spec_index(target).view_rodata().view().owning_container == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        scope matches KillScope::Container { container } ==> old(krnl).prc_mp.spec_index(target).view_rodata().view().owning_container == container
            && old(krnl).ctn_mp.spec_index(container).view_ghost().uppertree_seq.view().contains(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container),
        old(krnl).pt_mp.dom().contains(pagetable),
        va_2m_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_v2l4index(va),
        forall|l4i: L4Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i) is None,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))->0.addr == pg_ptr,
        old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        typed_lock_map_contains_mode(entry_lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.state() is WriteLock,
        pagetable_perm.thread_id() == entry_lctx.thread_id(),
        pagetable_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        page_ptr_valid(pg_ptr),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Mapped2m,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().mappings().contains((pagetable, va)),
        !(old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().ref_count > 1),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == owner,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write),
        page_perm.state() is WriteLock,
        page_perm.thread_id() == old(lctx).thread_id(),
        page_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id,
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
        old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(&entry_lctx, final(lctx)),
        final(lctx).cpu_id() == entry_lctx.cpu_id(),
        final(lctx).thread_id() == entry_lctx.thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        index_valid(NUM_CPUS, entry_lctx.cpu_id()) ==> final(krnl).cpu_hw_cr3_pcid[entry_lctx.cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[entry_lctx.cpu_id() as int].view(),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, &entry_lctx),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, &entry_lctx),
        held_threads_unchanged(old(krnl).thrd_mp, final(krnl).thrd_mp, &entry_lctx),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, &entry_lctx),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, &entry_lctx),
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        ({
            let old_c = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            let new_c = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable);
            &&& new_c.higher == old_c.higher && new_c.mapping_4k() == old_c.mapping_4k() && new_c.mapping_2m() == old_c.mapping_2m() && new_c.page_closure() == old_c.page_closure()
            &&& new_c.lower.l2_perms.dom() == old_c.lower.l2_perms.dom() && new_c.lower.pagetable_window_locks == old_c.lower.pagetable_window_locks && new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
            &&& old_c.lower.hidden_l1_tables_in_locked_windows() ==> new_c.lower.hidden_l1_tables_in_locked_windows()
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_entry(p, i)] (p, i) != (old_c.spec_held_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr, spec_v2l2index(va)) ==> new_c.lower.l2_entry(p, i) == old_c.lower.l2_entry(p, i)
            &&& new_c.lower.l2_entry(old_c.spec_held_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr, spec_v2l2index(va)).is_empty()
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_owner(p, i)] new_c.lower.l2_owner(p, i) == old_c.lower.l2_owner(p, i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_l2(l4i, l3i, l2i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_l2(l4i, l3i, l2i) == old_c.spec_held_l2(l4i, l3i, l2i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_2m_l2(l4i, l3i, l2i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))
                    ==> new_c.spec_held_2m_l2(l4i, l3i, l2i) == old_c.spec_held_2m_l2(l4i, l3i, l2i)
            &&& new_c.spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is None
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)
        }),
{
    hide(Set::is_empty);
    let pg_idx = page_ptr2page_index(pg_ptr);
    let ghost origin = krnl.prc_mp.spec_index(target).view_rodata().view().owning_container;
    proof {
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, target);
        page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, pg_idx);
    }
    let ghost held_lctx = *lctx;
    proof {
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl);
        krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
        assert(held_lctx.page_lock_map().dom().contains(pg_idx) && krnl.ctn_mp.dom().contains(owner)) by { container_owned_pages_wf_backward_at(krnl.ctn_mp, krnl.pg_arr, pg_idx); };
        container_perms_wf_at(krnl.ctn_mp, owner); container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, owner);
    }
    let allc_ptr = krnl.ctn_mp.borrow_rodata(owner).borrow().allocator_ptr_2m;
    let ghost cache_lctx = *lctx;
    let Tracked(cache_perm) = kill_reclaim_lock_cache_2m(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), allc_ptr, cpu_id, Ghost(pg_idx));
    let ghost snap = *krnl;
    let ghost snap_lctx = *lctx;
    proof {
        assert(held_lctx.page_lock_map().dom().contains(pg_idx) && held_lctx.pagetable_lock_map().dom().contains(pagetable) && held_lctx.process_lock_map().dom().contains(target));
        assert(cache_lctx.page_lock_map().dom().contains(pg_idx) && cache_lctx.pagetable_lock_map().dom().contains(pagetable) && cache_lctx.process_lock_map().dom().contains(target));
        assert(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable));
        assert(krnl.pg_arr.spec_index(pg_idx).view().view().mappings().contains((pagetable, va)) && krnl.pg_arr.spec_index(pg_idx).view().view().state is Mapped2m);
        container_process_page_pagetable_wf_at(krnl.ctn_mp, krnl.prc_mp, krnl.pt_mp, krnl.pg_arr, pg_idx, pagetable, va);
        container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, target);
        assert(krnl.ctn_mp.dom().contains(origin) && krnl.ctn_mp.dom().contains(owner));
        container_subtree_uppertree_agree_wf_at(krnl.rt_ctn, krnl.ctn_mp, owner, origin);
    }
    let ghost before = steps.view();
    let Tracked(quota_perm) = krnl.wlock_allocator_quota_2m(allc_ptr, Tracked(&mut *lctx));
    kill_reclaim_last_held_2m_mapping_scoped_to_cache(krnl, Tracked(&mut *lctx), pagetable, va, pg_ptr, owner, allc_ptr, cpu_id, Tracked(pagetable_perm), Tracked(&page_perm),
        Tracked(&cache_perm), Tracked(&quota_perm));
    krnl.wunlock_allocator_quota_2m(allc_ptr, Tracked(&mut *lctx), Tracked(quota_perm));
    krnl.wunlock_allocator_cache_2m(allc_ptr, cpu_id, Tracked(&mut *lctx), Tracked(cache_perm));
    krnl.wunlock_page(pg_idx, Tracked(&mut *lctx), Tracked(page_perm));
    proof {
        assert(lctx.page_lock_map() =~= entry_lctx.page_lock_map() && lctx.allocator_cache_2m_lock_map() =~= entry_lctx.allocator_cache_2m_lock_map() && lctx.allocator_quota_2m_lock_map() =~= entry_lctx.allocator_quota_2m_lock_map());
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&snap, &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        kill_scoped_credit_2m_step_from_k(&snap, &*krnl, pagetable, owner, allc_ptr, origin);
        let post_u = kernel_k_to_kernel_u(*krnl);
        krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
        kill_trace_from_scoped_credit(&*steps, before, start, pre, post_u, &snap, &snap_lctx, cpu_id, ctx, prc_ptr, thrd_ptr, target, stage, scope);
    }
}

/// Reclaim the 2M page `pg_ptr` of the held 2M leaf at `va` of the target's write-held page table `pagetable`, which lists no
/// cpu stale and whose user root entries no longer resolve, and clear the leaf: drop the leaf's record from the page, or free the
/// page behind its last mapping and credit its 2M quota to its owner, the target's container or one of its ancestors, in one
/// step that extends the kill's partial trace.
pub(crate) fn kill_reclaim_held_2m_page_scoped(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, target: RwLockProcessPtr, pagetable: RwLockPageTableRoot, va: VAddr, pg_ptr: PagePtr, Tracked(pagetable_perm): Tracked<&LockPerm>,
    Ghost(stage): Ghost<KillStage>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(steps).snapshot_k() == *old(krnl),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).page_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_2M_MAJOR),
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
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), prc_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), target, TypedLockMode::Write),
        old(krnl).prc_mp.dom().contains(target),
        old(krnl).prc_mp.spec_index(target).being_killed(),
        !old(krnl).prc_mp.spec_index(target).view().zombie,
        old(krnl).prc_mp.spec_index(target).view().pagetable == pagetable,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == kill_scope_progress(scope, target, stage),
        scope matches KillScope::Container { container } ==> old(krnl).ctn_mp.dom().contains(container) && typed_lock_map_contains_mode(old(lctx).container_lock_map(), container, TypedLockMode::Write),
        scope is Subtree ==> old(krnl).prc_mp.spec_index(target).view_rodata().view().owning_container == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        scope matches KillScope::Container { container } ==> old(krnl).prc_mp.spec_index(target).view_rodata().view().owning_container == container
            && old(krnl).ctn_mp.spec_index(container).view_ghost().uppertree_seq.view().contains(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container),
        old(krnl).pt_mp.dom().contains(pagetable),
        va_2m_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_v2l4index(va),
        forall|l4i: L4Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i)]
            KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i) is None,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))->0.addr == pg_ptr,
        old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.state() is WriteLock,
        pagetable_perm.thread_id() == old(lctx).thread_id(),
        pagetable_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(lctx).pagetable_lock_map().dom() =~= set![pagetable],
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        page_ptr_valid(pg_ptr),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state is Mapped2m,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().mappings().contains((pagetable, va)),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
        old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()),
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
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_threads_unchanged(old(krnl).thrd_mp, final(krnl).thrd_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        ({
            let old_c = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            let new_c = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable);
            &&& new_c.higher == old_c.higher && new_c.mapping_4k() == old_c.mapping_4k() && new_c.mapping_2m() == old_c.mapping_2m() && new_c.page_closure() == old_c.page_closure()
            &&& new_c.lower.l2_perms.dom() == old_c.lower.l2_perms.dom() && new_c.lower.pagetable_window_locks == old_c.lower.pagetable_window_locks && new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
            &&& old_c.lower.hidden_l1_tables_in_locked_windows() ==> new_c.lower.hidden_l1_tables_in_locked_windows()
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_entry(p, i)] (p, i) != (old_c.spec_held_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr, spec_v2l2index(va)) ==> new_c.lower.l2_entry(p, i) == old_c.lower.l2_entry(p, i)
            &&& new_c.lower.l2_entry(old_c.spec_held_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr, spec_v2l2index(va)).is_empty()
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_owner(p, i)] new_c.lower.l2_owner(p, i) == old_c.lower.l2_owner(p, i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_l2(l4i, l3i, l2i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_l2(l4i, l3i, l2i) == old_c.spec_held_l2(l4i, l3i, l2i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_2m_l2(l4i, l3i, l2i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))
                    ==> new_c.spec_held_2m_l2(l4i, l3i, l2i) == old_c.spec_held_2m_l2(l4i, l3i, l2i)
            &&& new_c.spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is None
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)
        }),
{
    let pg_idx = page_ptr2page_index(pg_ptr);
    proof {
        krnl.default_pagetable_wf_at(pagetable); spec_va_2m_valid_index_roundtrip(va);
        assert(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(spec_v2l4index(va)) is None);
        page_ptr_valid_imply_page_index_valid();
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, target);
    }
    let ghost entry_lctx = *lctx;
    let Tracked(page_perm) = krnl.wlock_page(pg_idx, Tracked(&mut *lctx));
    proof { page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, pg_idx); }
    let (ref_count, owner) = {
        let page = krnl.pg_arr.borrow_typed(pg_idx, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(&page_perm));
        (page.ref_count, page.owning_container)
    };
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(pg_idx);
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    if ref_count > 1 {
        remove_held_2m_mapping_without_free(krnl, pagetable, va, pg_ptr, Tracked(&mut *lctx), Tracked(pagetable_perm), Tracked(&page_perm));
        krnl.wunlock_page(pg_idx, Tracked(&mut *lctx), Tracked(page_perm));
        proof {
            assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
                map_insert_overwrite_lemma(old(lctx).page_lock_map(), pg_idx, TypedHeldLock { lock_id: old_page_lock_id, mode: TypedLockMode::Write },
                    TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(pg_idx), mode: TypedLockMode::Write });
                map_insert_remove_absent_lemma(old(lctx).page_lock_map(), pg_idx, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(pg_idx), mode: TypedLockMode::Write });
            };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl);
            krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
        }
    } else {
        kill_reclaim_last_held_2m_mapping_scoped(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, thrd_ptr, target, pagetable, va, pg_ptr, owner,
            Tracked(pagetable_perm), Tracked(page_perm), Ghost(stage), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx), Ghost(entry_lctx));
    }
}
}
