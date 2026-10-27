use vstd::prelude::*;
use crate::*;
#[cfg(all(verus_keep_ghost, feature = "split-crates"))]
use veriflat_alloc_page::free_4k_page::kill_container_quota_fold::{lemma_container_allocator_quota_eq_total_free_without_users, lemma_container_allocator_2m_quota_bounded};
#[cfg(all(verus_keep_ghost, not(feature = "split-crates")))]
use crate::kernel::implementation::free_4k_page::kill_container_quota_fold::{lemma_container_allocator_quota_eq_total_free_without_users, lemma_container_allocator_2m_quota_bounded};
use super::syscall_kill_container_retire_objects::*;
use super::syscall_kill_container_retire_free::{kill_container_retire_pages_4k_to_pool, kill_container_retire_head_2m_to_pool};
use super::super::syscall_kill_process::syscall_kill_process_retire_pages_lock::wunlock_kill_retire_pages;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_retire_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_retire_eof::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_retire_eof_entry::kill_container_retire_eof_target_empty;

verus! {
/// With every lock `kill_container_retire_held_locks` names write-held, retire the marked childless container
/// `container_ptr`, which owns no process or thread and whose quotas, scheduler queues, and allocator caches are
/// empty: it leaves its parent `parent_ptr`, the killer's container `owner_ptr` takes over its pages, its kernel
/// objects leave their maps, their pages join `owner_ptr`'s global pools with their quota, and every lock taken for it
/// is released. The caller ends the step.
pub(crate) fn kill_container_retire_commit(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, container_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr,
    Tracked(container_perm): Tracked<LockPerm>, Tracked(parent_perm): Tracked<&LockPerm>, Tracked(owner_perm): Tracked<&LockPerm>, Tracked(cpu_set_perm): Tracked<LockPerm>,
    Tracked(flag_perms): Tracked<Map<CpuId, LockPerm>>, Tracked(pcid_perm): Tracked<LockPerm>, Tracked(shard_perms): Tracked<Map<CpuId, LockPerm>>,
    Tracked(caches_4k): Tracked<Map<CpuId, LockPerm>>, Tracked(caches_2m): Tracked<Map<CpuId, LockPerm>>, Tracked(caches_1g): Tracked<Map<CpuId, LockPerm>>,
    Tracked(pools_4k): Tracked<Map<RwLockPageAllocatorPtr, LockPerm>>, Tracked(pools_2m): Tracked<Map<RwLockPageAllocatorPtr, LockPerm>>, Tracked(pool_1g): Tracked<LockPerm>,
    Tracked(quotas_4k): Tracked<Map<RwLockPageAllocatorPtr, LockPerm>>, Tracked(quotas_2m): Tracked<Map<RwLockPageAllocatorPtr, LockPerm>>, Tracked(quota_1g): Tracked<LockPerm>,
    Tracked(page_perms): Tracked<Map<PageIndex, LockPerm>>, Tracked(tails_container): Tracked<Map<PageIndex, LockPerm>>, Tracked(tails_pcid): Tracked<Map<PageIndex, LockPerm>>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        kill_container_retire_held_locks(*old(krnl), *old(lctx), container_ptr, owner_ptr, cpu_set_perm, flag_perms, pcid_perm, shard_perms, caches_4k, caches_2m, caches_1g, pools_4k,
            pools_2m, pool_1g, quotas_4k, quotas_2m, quota_1g, page_perms, tails_container, tails_pcid),
        ({
            let target = old(krnl).ctn_mp.spec_index(container_ptr);
            let ro = target.view_rodata().view();
            &&& owner_ptr != container_ptr
            &&& target.view_ghost().retire_ready
            &&& ro.parent == Some(parent_ptr)
            &&& target.view_ghost().uppertree_seq.view().contains(owner_ptr)
            &&& old(krnl).cpu_set_mp.spec_index(ro.cpu_set).being_killed()
            &&& old(krnl).cpu_set_mp.spec_index(ro.cpu_set).view().owned_cpus.view().is_empty()
            &&& forall|i: CpuId| #![trigger old(krnl).sched_mp.spec_index(ro.scheduler).shards.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> old(krnl).sched_mp.spec_index(ro.scheduler).shards.spec_index(i).view().view().queue.view().len() == 0
        }),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        container_perm.state() is WriteLock && container_perm.thread_id() == old(lctx).thread_id(),
        container_perm.lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(parent_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), parent_ptr, TypedLockMode::Write),
        parent_perm.state() is WriteLock && parent_perm.thread_id() == old(lctx).thread_id(),
        parent_perm.lock_id() == old(krnl).ctn_mp.spec_index(parent_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), owner_ptr, TypedLockMode::Write),
        owner_perm.state() is WriteLock && owner_perm.thread_id() == old(lctx).thread_id(),
        owner_perm.lock_id() == old(krnl).ctn_mp.spec_index(owner_ptr).locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).container_lock_map() == old(lctx).container_lock_map().remove(container_ptr),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map().remove(old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).page_lock_map().dom().is_empty(),
        final(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        final(lctx).scheduler_lock_map().dom().is_empty(),
        final(lctx).pcid_allocator_lock_map().dom().is_empty(),
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        final(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        final(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        *final(krnl) == (KernelK { ctn_mp: final(krnl).ctn_mp, sched_mp: final(krnl).sched_mp, cpu_set_mp: final(krnl).cpu_set_mp, pcid_allc_mp: final(krnl).pcid_allc_mp,
            cpu_offline_mp: final(krnl).cpu_offline_mp, allc_4k_mp: final(krnl).allc_4k_mp, allc_2m_mp: final(krnl).allc_2m_mp, allc_1g_mp: final(krnl).allc_1g_mp,
            pg_arr: final(krnl).pg_arr, ..*old(krnl) }),
        final(krnl).ctn_mp.dom() == old(krnl).ctn_mp.dom().remove(container_ptr),
        forall|c: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(c)] final(krnl).ctn_mp.dom().contains(c) ==> {
            let old_c = old(krnl).ctn_mp.spec_index(c);
            let new_c = final(krnl).ctn_mp.spec_index(c);
            let target = old(krnl).ctn_mp.spec_index(container_ptr);
            &&& new_c.view_rodata() == old_c.view_rodata()
            &&& new_c.locking_thread() == old_c.locking_thread()
            &&& new_c.control() == old_c.control()
            &&& new_c.view().zombie == old_c.view().zombie
            &&& new_c.view().root_process == old_c.view().root_process
            &&& new_c.view().children.view() == if c == parent_ptr { old_c.view().children.view().remove_value(container_ptr) } else { old_c.view().children.view() }
            &&& new_c.view().owned_pages.view() == if c == owner_ptr { old_c.view().owned_pages.view().union(target.view().owned_pages.view()) } else { old_c.view().owned_pages.view() }
            &&& new_c.view_ghost().uppertree_seq == old_c.view_ghost().uppertree_seq
            &&& new_c.view_ghost().subtree_set.view() == if target.view_ghost().uppertree_seq.view().contains(c) {
                old_c.view_ghost().subtree_set.view().remove(container_ptr)
            } else { old_c.view_ghost().subtree_set.view() }
            &&& new_c.view_ghost().owned_processes == old_c.view_ghost().owned_processes
            &&& new_c.view_ghost().owned_threads == old_c.view_ghost().owned_threads
            &&& new_c.view_ghost().owned_endpoints == old_c.view_ghost().owned_endpoints
        },
        ({
            let ro = old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view();
            let owner_ro = old(krnl).ctn_mp.spec_index(owner_ptr).view_rodata().view();
            &&& final(krnl).sched_mp.dom() == old(krnl).sched_mp.dom().remove(ro.scheduler)
            &&& forall|s: RwLockSchedulerPtr| #![trigger final(krnl).sched_mp.spec_index(s)] final(krnl).sched_mp.dom().contains(s) ==> final(krnl).sched_mp.spec_index(s) == old(krnl).sched_mp.spec_index(s)
            &&& final(krnl).cpu_set_mp.dom() == old(krnl).cpu_set_mp.dom().remove(ro.cpu_set)
            &&& forall|s: RwLockCpuSetPtr| #![trigger final(krnl).cpu_set_mp.spec_index(s)] final(krnl).cpu_set_mp.dom().contains(s) ==> final(krnl).cpu_set_mp.spec_index(s) == old(krnl).cpu_set_mp.spec_index(s)
            &&& final(krnl).cpu_offline_mp.dom() == old(krnl).cpu_offline_mp.dom().remove(cpu_offline_flags_ptr(container_ptr))
            &&& forall|f: RwLockCpuOfflineFlagsPtr| #![trigger final(krnl).cpu_offline_mp.spec_index(f)]
                final(krnl).cpu_offline_mp.dom().contains(f) ==> final(krnl).cpu_offline_mp.spec_index(f) == old(krnl).cpu_offline_mp.spec_index(f)
            &&& final(krnl).pcid_allc_mp.dom() == old(krnl).pcid_allc_mp.dom().remove(ro.pcid_allocator)
            &&& forall|a: RwLockPcidAllocatorPtr| #![trigger final(krnl).pcid_allc_mp.spec_index(a)]
                final(krnl).pcid_allc_mp.dom().contains(a) ==> final(krnl).pcid_allc_mp.spec_index(a) == old(krnl).pcid_allc_mp.spec_index(a)
            &&& final(krnl).allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom().remove(ro.allocator_ptr_4k)
            &&& forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_4k_mp.spec_index(a)]
                final(krnl).allc_4k_mp.dom().contains(a) && a != owner_ro.allocator_ptr_4k ==> final(krnl).allc_4k_mp.spec_index(a).quota.view() == old(krnl).allc_4k_mp.spec_index(a).quota.view()
            &&& old(krnl).allc_4k_mp.spec_index(owner_ro.allocator_ptr_4k).quota.view().view() < final(krnl).allc_4k_mp.spec_index(owner_ro.allocator_ptr_4k).quota.view().view()
            &&& final(krnl).allc_2m_mp.dom() == old(krnl).allc_2m_mp.dom().remove(ro.allocator_ptr_2m)
            &&& forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_2m_mp.spec_index(a)]
                final(krnl).allc_2m_mp.dom().contains(a) && a != owner_ro.allocator_ptr_2m ==> final(krnl).allc_2m_mp.spec_index(a).quota.view() == old(krnl).allc_2m_mp.spec_index(a).quota.view()
            &&& old(krnl).allc_2m_mp.spec_index(owner_ro.allocator_ptr_2m).quota.view().view() < final(krnl).allc_2m_mp.spec_index(owner_ro.allocator_ptr_2m).quota.view().view()
            &&& final(krnl).allc_1g_mp.dom() == old(krnl).allc_1g_mp.dom().remove(ro.allocator_ptr_1g)
            &&& forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_1g_mp.spec_index(a)]
                final(krnl).allc_1g_mp.dom().contains(a) ==> final(krnl).allc_1g_mp.spec_index(a).quota.view() == old(krnl).allc_1g_mp.spec_index(a).quota.view()
        }),
{
    let ghost entry = *krnl;
    let ghost ro = krnl.ctn_mp.spec_index(container_ptr).view_rodata().view();
    let ghost owner_ro = krnl.ctn_mp.spec_index(owner_ptr).view_rodata().view();
    proof {
        container_kill_retire_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr);
        lemma_container_allocator_4k_quota_bounded(&*krnl, owner_ptr); lemma_container_allocator_2m_quota_bounded(&*krnl, owner_ptr);
        page_array_wf_map(krnl.pg_arr); page_ptr_roundtrip();
        scheduler_pages_wf_at(krnl.sched_mp, krnl.pg_arr, ro.scheduler); cpu_set_pages_wf_at(krnl.cpu_set_mp, krnl.pg_arr, ro.cpu_set);
        allocator_4k_pages_wf_at(krnl.pg_arr, krnl.allc_4k_mp, ro.allocator_ptr_4k); allocator_2m_pages_wf_at(krnl.pg_arr, krnl.allc_2m_mp, ro.allocator_ptr_2m);
        allocator_1g_pages_wf_at(krnl.pg_arr, krnl.allc_1g_mp, ro.allocator_ptr_1g); pcid_allocator_pages_wf_at(krnl.pg_arr, krnl.pcid_allc_mp, ro.pcid_allocator);
        hugepage_2m_wf_head_at(krnl.pg_arr, page_ptr2page_index(ro.pcid_allocator));
        container_allocator_free_4k_page_wf_global_at(krnl.allc_4k_mp, krnl.pg_arr, owner_ro.allocator_ptr_4k, ro.scheduler);
        container_allocator_free_4k_page_wf_global_at(krnl.allc_4k_mp, krnl.pg_arr, owner_ro.allocator_ptr_4k, ro.cpu_set);
        container_allocator_free_4k_page_wf_global_at(krnl.allc_4k_mp, krnl.pg_arr, owner_ro.allocator_ptr_4k, ro.allocator_ptr_4k);
        container_allocator_free_4k_page_wf_global_at(krnl.allc_4k_mp, krnl.pg_arr, owner_ro.allocator_ptr_4k, ro.allocator_ptr_2m);
        container_allocator_free_4k_page_wf_global_at(krnl.allc_4k_mp, krnl.pg_arr, owner_ro.allocator_ptr_4k, ro.allocator_ptr_1g);
        container_allocator_free_2m_page_wf_global_at(krnl.allc_2m_mp, krnl.pg_arr, owner_ro.allocator_ptr_2m, container_ptr);
        container_allocator_free_2m_page_wf_global_at(krnl.allc_2m_mp, krnl.pg_arr, owner_ro.allocator_ptr_2m, ro.pcid_allocator);
        container_perms_wf_at(krnl.ctn_mp, container_ptr); container_perms_wf_at(krnl.ctn_mp, owner_ptr);
        container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr);
        container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, owner_ptr);
        container_pages_backward_at(krnl.pg_arr, krnl.ctn_mp, container_ptr);
        container_scheduler_wf_at(krnl.ctn_mp, krnl.sched_mp, container_ptr); container_cpu_set_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, container_ptr);
        container_pcid_allocator_wf_container_at(krnl.ctn_mp, krnl.pcid_allc_mp, container_ptr);
        allocator_perms_wf_map(krnl.allc_4k_mp); allocator_perms_wf_map(krnl.allc_2m_mp);
        allocator_perms_wf_at(krnl.allc_4k_mp, owner_ro.allocator_ptr_4k); allocator_perms_wf_at(krnl.allc_2m_mp, owner_ro.allocator_ptr_2m);
        let (ps, hs) = (kill_container_retire_pages_4k(ro), kill_container_retire_heads(container_ptr, ro));
        assert(page_perms.dom().contains(hs[0]) && page_perms.dom().contains(hs[1]));
        assert(page_perms.dom().contains(ps[0]) && page_perms.dom().contains(ps[1]) && page_perms.dom().contains(ps[2]) && page_perms.dom().contains(ps[3]) && page_perms.dom().contains(ps[4]));
    }
    let a4 = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().allocator_ptr_4k;
    let a2 = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().allocator_ptr_2m;
    let a1 = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().allocator_ptr_1g;
    let scheduler_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().scheduler;
    let cpu_set_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().cpu_set;
    let pcid_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().pcid_allocator;
    let o4 = krnl.ctn_mp.borrow_rodata(owner_ptr).borrow().allocator_ptr_4k;
    let o2 = krnl.ctn_mp.borrow_rodata(owner_ptr).borrow().allocator_ptr_2m;
    let tracked mut pools_4k = pools_4k;
    let tracked mut pools_2m = pools_2m;
    let tracked mut quotas_4k = quotas_4k;
    let tracked mut quotas_2m = quotas_2m;
    let Tracked(objects) = kill_container_retire_detach(krnl, Tracked(&mut *lctx), container_ptr, parent_ptr, owner_ptr, Tracked(container_perm), Tracked(parent_perm), Tracked(owner_perm),
        Tracked(cpu_set_perm), Tracked(flag_perms), Tracked(pcid_perm), Tracked(shard_perms), Tracked(caches_4k), Tracked(caches_2m), Tracked(caches_1g), Tracked(&mut pools_4k),
        Tracked(&mut pools_2m), Tracked(pool_1g), Tracked(&mut quotas_4k), Tracked(&mut quotas_2m), Tracked(quota_1g), Tracked(&page_perms), Tracked(&tails_container), Tracked(&tails_pcid));
    let tracked (container_page, pcid_page, page_objects) = objects;
    proof {
        assert(lctx.allocator_global_pool_4k_lock_map().dom() =~= set![o4] && lctx.allocator_quota_4k_lock_map().dom() =~= set![o4]);
        assert(lctx.allocator_global_pool_2m_lock_map().dom() =~= set![o2] && lctx.allocator_quota_2m_lock_map().dom() =~= set![o2]);
    }
    // Their pages join the killer's container's global pools with their quota.
    let mut pages = ArrayVec::<PageIndex, 5>::new();
    pages.push(page_ptr2page_index(scheduler_ptr));
    pages.push(page_ptr2page_index(cpu_set_ptr));
    pages.push(page_ptr2page_index(a4));
    pages.push(page_ptr2page_index(a2));
    pages.push(page_ptr2page_index(a1));
    proof { assert(pages.view() =~= kill_container_retire_pages_4k(ro)); }
    let container_head = page_ptr2page_index(container_ptr);
    let pcid_head = page_ptr2page_index(pcid_ptr);
    kill_container_retire_fill_pools(krnl, Tracked(&mut *lctx), o4, o2, owner_ptr, &pages, Tracked(page_objects), container_head, Tracked(container_page), pcid_head, Tracked(pcid_page),
        Tracked(&page_perms), Tracked(&tails_container), Tracked(&tails_pcid), Tracked(pools_4k.tracked_borrow(o4)), Tracked(quotas_4k.tracked_borrow(o4)), Tracked(pools_2m.tracked_borrow(o2)),
        Tracked(quotas_2m.tracked_borrow(o2)));
    let ghost mid = *krnl;
    proof {
        assert(kill_container_retire_eof_transition_framing(entry, mid, container_ptr, parent_ptr, owner_ptr)) by { reveal(kill_container_retire_eof_transition_framing); };
        assert(kill_container_retire_eof_target_empty(entry, container_ptr, parent_ptr, owner_ptr));
        kill_container_retire_eof(entry, mid, container_ptr, parent_ptr, owner_ptr);
    }
    kill_container_retire_unlock(krnl, Tracked(&mut *lctx), o4, o2, container_head, pcid_head, &pages, Tracked(pools_4k), Tracked(pools_2m), Tracked(quotas_4k),
        Tracked(quotas_2m), Tracked(page_perms), Tracked(tails_container), Tracked(tails_pcid));
    proof { reveal(kill_container_retire_eof_transition_framing); }
}

/// With every lock `kill_container_retire_held_locks` names write-held, detach the marked childless container
/// `container_ptr` from its parent `parent_ptr` and every ancestor's subtree, hand the pages it owns to the killer's
/// container `owner_ptr`, and retire its kernel objects, whose locks leave `lctx` and whose pages it returns: its
/// container and PCID allocator pages and its five 4K object pages.
fn kill_container_retire_detach(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, container_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr,
    Tracked(container_perm): Tracked<LockPerm>, Tracked(parent_perm): Tracked<&LockPerm>, Tracked(owner_perm): Tracked<&LockPerm>, Tracked(cpu_set_perm): Tracked<LockPerm>,
    Tracked(flag_perms): Tracked<Map<CpuId, LockPerm>>, Tracked(pcid_perm): Tracked<LockPerm>, Tracked(shard_perms): Tracked<Map<CpuId, LockPerm>>,
    Tracked(caches_4k): Tracked<Map<CpuId, LockPerm>>, Tracked(caches_2m): Tracked<Map<CpuId, LockPerm>>, Tracked(caches_1g): Tracked<Map<CpuId, LockPerm>>,
    Tracked(pools_4k): Tracked<&mut Map<RwLockPageAllocatorPtr, LockPerm>>, Tracked(pools_2m): Tracked<&mut Map<RwLockPageAllocatorPtr, LockPerm>>, Tracked(pool_1g): Tracked<LockPerm>,
    Tracked(quotas_4k): Tracked<&mut Map<RwLockPageAllocatorPtr, LockPerm>>, Tracked(quotas_2m): Tracked<&mut Map<RwLockPageAllocatorPtr, LockPerm>>, Tracked(quota_1g): Tracked<LockPerm>,
    Tracked(page_perms): Tracked<&Map<PageIndex, LockPerm>>, Tracked(tails_container): Tracked<&Map<PageIndex, LockPerm>>, Tracked(tails_pcid): Tracked<&Map<PageIndex, LockPerm>>,
) -> (ret: Tracked<(PagePerm2m, PagePerm2m, Map<PageIndex, PagePerm4k>)>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        kill_container_retire_held_locks(*old(krnl), *old(lctx), container_ptr, owner_ptr, cpu_set_perm, flag_perms, pcid_perm, shard_perms, caches_4k, caches_2m, caches_1g,
            *old(pools_4k), *old(pools_2m), pool_1g, *old(quotas_4k), *old(quotas_2m), quota_1g, *page_perms, *tails_container, *tails_pcid),
        ({
            let target = old(krnl).ctn_mp.spec_index(container_ptr);
            let ro = target.view_rodata().view();
            &&& owner_ptr != container_ptr
            &&& target.being_killed()
            &&& target.view().children.view().len() == 0
            &&& target.view_ghost().owned_processes.view() == Set::<RwLockProcessPtr>::empty()
            &&& target.view_ghost().owned_threads.view() == Set::<RwLockThreadPtr>::empty()
            &&& target.view_ghost().owned_indirect_threads.view() == Set::<RwLockThreadPtr>::empty()
            &&& ro.parent == Some(parent_ptr)
            &&& target.view_ghost().uppertree_seq.view().contains(owner_ptr)
            &&& old(krnl).cpu_set_mp.spec_index(ro.cpu_set).being_killed()
            &&& old(krnl).allc_4k_mp.spec_index(ro.allocator_ptr_4k).quota.view().value == 0
            &&& old(krnl).allc_2m_mp.spec_index(ro.allocator_ptr_2m).quota.view().value == 0
            &&& old(krnl).allc_1g_mp.spec_index(ro.allocator_ptr_1g).quota.view().value == 0
            &&& forall|i: CpuId| #![trigger old(krnl).sched_mp.spec_index(ro.scheduler).shards.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> old(krnl).sched_mp.spec_index(ro.scheduler).shards.spec_index(i).view().view().queue.view().len() == 0
            &&& forall|i: CpuId| #![trigger old(krnl).allc_4k_mp.spec_index(ro.allocator_ptr_4k).cpu_caches.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> old(krnl).allc_4k_mp.spec_index(ro.allocator_ptr_4k).cpu_caches.spec_index(i).view().view().linked_list.view().len() == 0
            &&& forall|i: CpuId| #![trigger old(krnl).allc_2m_mp.spec_index(ro.allocator_ptr_2m).cpu_caches.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> old(krnl).allc_2m_mp.spec_index(ro.allocator_ptr_2m).cpu_caches.spec_index(i).view().view().linked_list.view().len() == 0
            &&& forall|i: CpuId| #![trigger old(krnl).allc_1g_mp.spec_index(ro.allocator_ptr_1g).cpu_caches.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> old(krnl).allc_1g_mp.spec_index(ro.allocator_ptr_1g).cpu_caches.spec_index(i).view().view().linked_list.view().len() == 0
        }),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        container_perm.state() is WriteLock && container_perm.thread_id() == old(lctx).thread_id(),
        container_perm.lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(parent_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), parent_ptr, TypedLockMode::Write),
        parent_perm.state() is WriteLock && parent_perm.thread_id() == old(lctx).thread_id(),
        parent_perm.lock_id() == old(krnl).ctn_mp.spec_index(parent_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), owner_ptr, TypedLockMode::Write),
        owner_perm.state() is WriteLock && owner_perm.thread_id() == old(lctx).thread_id(),
        owner_perm.lock_id() == old(krnl).ctn_mp.spec_index(owner_ptr).locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map().remove(container_ptr),
        final(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        final(lctx).scheduler_lock_map().dom().is_empty(),
        final(lctx).pcid_allocator_lock_map().dom().is_empty(),
        final(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        *final(krnl) == (KernelK { ctn_mp: final(krnl).ctn_mp, sched_mp: final(krnl).sched_mp, cpu_set_mp: final(krnl).cpu_set_mp, pcid_allc_mp: final(krnl).pcid_allc_mp,
            cpu_offline_mp: final(krnl).cpu_offline_mp, allc_4k_mp: final(krnl).allc_4k_mp, allc_2m_mp: final(krnl).allc_2m_mp, allc_1g_mp: final(krnl).allc_1g_mp, ..*old(krnl) }),
        ({
            let target = old(krnl).ctn_mp.spec_index(container_ptr);
            let ro = target.view_rodata().view();
            let (a4, a2) = (ro.allocator_ptr_4k, ro.allocator_ptr_2m);
            &&& final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map().remove(ro.cpu_set)
            &&& final(lctx).allocator_quota_4k_lock_map() == old(lctx).allocator_quota_4k_lock_map().remove(a4)
            &&& final(lctx).allocator_global_pool_4k_lock_map() == old(lctx).allocator_global_pool_4k_lock_map().remove(a4)
            &&& final(lctx).allocator_cache_4k_lock_map().dom().is_empty()
            &&& final(lctx).allocator_quota_2m_lock_map() == old(lctx).allocator_quota_2m_lock_map().remove(a2)
            &&& final(lctx).allocator_global_pool_2m_lock_map() == old(lctx).allocator_global_pool_2m_lock_map().remove(a2)
            &&& final(lctx).allocator_cache_2m_lock_map().dom().is_empty()
            &&& *final(pools_4k) == old(pools_4k).remove(a4) && *final(quotas_4k) == old(quotas_4k).remove(a4)
            &&& *final(pools_2m) == old(pools_2m).remove(a2) && *final(quotas_2m) == old(quotas_2m).remove(a2)
            &&& ret.view().0.is_init() && ret.view().0.addr() == container_ptr
            &&& ret.view().1.is_init() && ret.view().1.addr() == ro.pcid_allocator
            &&& forall|k: int| #![trigger kill_container_retire_pages_4k(ro)[k]] 0 <= k < 5 ==> {
                &&& ret.view().2.dom().contains(kill_container_retire_pages_4k(ro)[k])
                &&& ret.view().2[kill_container_retire_pages_4k(ro)[k]].is_init()
                &&& ret.view().2[kill_container_retire_pages_4k(ro)[k]].addr() == page_index2page_ptr(kill_container_retire_pages_4k(ro)[k])
            }
            &&& final(krnl).ctn_mp.perms_wf()
            &&& final(krnl).ctn_mp.dom() == old(krnl).ctn_mp.dom().remove(container_ptr)
            &&& final(krnl).ctn_mp.spec_index(parent_ptr).view().inv() && final(krnl).ctn_mp.spec_index(parent_ptr).view().children.view().no_duplicates()
            &&& forall|c: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(c)] final(krnl).ctn_mp.dom().contains(c) ==> {
                let old_c = old(krnl).ctn_mp.spec_index(c);
                let new_c = final(krnl).ctn_mp.spec_index(c);
                &&& new_c.is_init() == old_c.is_init()
                &&& new_c.view_rodata() == old_c.view_rodata()
                &&& new_c.locking_thread() == old_c.locking_thread()
                &&& new_c.control() == old_c.control()
                &&& final(krnl).ctn_mp.lock_id_by_key(c) == old(krnl).ctn_mp.lock_id_by_key(c)
                &&& new_c.view() == (Container { children: new_c.view().children, owned_pages: new_c.view().owned_pages, ..old_c.view() })
                &&& c != parent_ptr ==> new_c.view().children == old_c.view().children
                &&& new_c.view().owned_pages.view() == if c == owner_ptr { old_c.view().owned_pages.view().union(target.view().owned_pages.view()) } else { old_c.view().owned_pages.view() }
                &&& new_c.view_ghost() == (ContainerGhost { subtree_set: new_c.view_ghost().subtree_set, ..old_c.view_ghost() })
                &&& new_c.view_ghost().subtree_set.view()
                    == if target.view_ghost().uppertree_seq.view().contains(c) { old_c.view_ghost().subtree_set.view().remove(container_ptr) } else { old_c.view_ghost().subtree_set.view() }
            }
            &&& final(krnl).ctn_mp.spec_index(parent_ptr).view().children.view() == old(krnl).ctn_mp.spec_index(parent_ptr).view().children.view().remove_value(container_ptr)
            &&& final(krnl).ctn_mp.spec_index(parent_ptr).view().children.map() == old(krnl).ctn_mp.spec_index(parent_ptr).view().children.map().remove(target.view().parent_linkedlist_node.addr())
            &&& final(krnl).sched_mp.perms_wf()
            &&& final(krnl).sched_mp.dom() == old(krnl).sched_mp.dom().remove(ro.scheduler)
            &&& forall|s: RwLockSchedulerPtr| #![trigger final(krnl).sched_mp.spec_index(s)] final(krnl).sched_mp.dom().contains(s) ==> final(krnl).sched_mp.spec_index(s) == old(krnl).sched_mp.spec_index(s)
            &&& final(krnl).cpu_set_mp.perms_wf()
            &&& final(krnl).cpu_set_mp.dom() == old(krnl).cpu_set_mp.dom().remove(ro.cpu_set)
            &&& forall|s: RwLockCpuSetPtr| #![trigger final(krnl).cpu_set_mp.spec_index(s)] final(krnl).cpu_set_mp.dom().contains(s) ==> final(krnl).cpu_set_mp.spec_index(s) == old(krnl).cpu_set_mp.spec_index(s)
            &&& forall|s: RwLockCpuSetPtr| #![trigger final(krnl).cpu_set_mp.lock_id_by_key(s)] final(krnl).cpu_set_mp.dom().contains(s) ==> final(krnl).cpu_set_mp.lock_id_by_key(s) == old(krnl).cpu_set_mp.lock_id_by_key(s)
            &&& final(krnl).pcid_allc_mp.perms_wf()
            &&& final(krnl).pcid_allc_mp.dom() == old(krnl).pcid_allc_mp.dom().remove(ro.pcid_allocator)
            &&& forall|a: RwLockPcidAllocatorPtr| #![trigger final(krnl).pcid_allc_mp.spec_index(a)] final(krnl).pcid_allc_mp.dom().contains(a) ==> final(krnl).pcid_allc_mp.spec_index(a) == old(krnl).pcid_allc_mp.spec_index(a)
            &&& final(krnl).cpu_offline_mp.perms_wf()
            &&& final(krnl).cpu_offline_mp.dom() == old(krnl).cpu_offline_mp.dom().remove(cpu_offline_flags_ptr(container_ptr))
            &&& forall|f: RwLockCpuOfflineFlagsPtr| #![trigger final(krnl).cpu_offline_mp.spec_index(f)]
                final(krnl).cpu_offline_mp.dom().contains(f) ==> final(krnl).cpu_offline_mp.spec_index(f) == old(krnl).cpu_offline_mp.spec_index(f)
            &&& final(krnl).allc_4k_mp.perms_wf()
            &&& final(krnl).allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom().remove(ro.allocator_ptr_4k)
            &&& forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_4k_mp.spec_index(a)] final(krnl).allc_4k_mp.dom().contains(a) ==> final(krnl).allc_4k_mp.spec_index(a) == old(krnl).allc_4k_mp.spec_index(a)
            &&& final(krnl).allc_2m_mp.perms_wf()
            &&& final(krnl).allc_2m_mp.dom() == old(krnl).allc_2m_mp.dom().remove(ro.allocator_ptr_2m)
            &&& forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_2m_mp.spec_index(a)] final(krnl).allc_2m_mp.dom().contains(a) ==> final(krnl).allc_2m_mp.spec_index(a) == old(krnl).allc_2m_mp.spec_index(a)
            &&& final(krnl).allc_1g_mp.perms_wf()
            &&& final(krnl).allc_1g_mp.dom() == old(krnl).allc_1g_mp.dom().remove(ro.allocator_ptr_1g)
            &&& forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_1g_mp.spec_index(a)] final(krnl).allc_1g_mp.dom().contains(a) ==> final(krnl).allc_1g_mp.spec_index(a) == old(krnl).allc_1g_mp.spec_index(a)
        }),
{
    let ghost entry = *krnl;
    let ghost ro = krnl.ctn_mp.spec_index(container_ptr).view_rodata().view();
    let ghost owner_ro = krnl.ctn_mp.spec_index(owner_ptr).view_rodata().view();
    let ghost ancestors = krnl.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view();
    proof {
        container_perms_wf_map(krnl.ctn_mp); container_perms_wf_at(krnl.ctn_mp, container_ptr); container_perms_wf_at(krnl.ctn_mp, owner_ptr);
        container_uppertree_seq_wf_at(krnl.rt_ctn, krnl.ctn_mp, container_ptr, owner_ptr); container_uppertree_seq_in_dom(krnl.rt_ctn, krnl.ctn_mp, container_ptr);
        container_root_wf_at(krnl.rt_ctn, krnl.ctn_mp, container_ptr); containers_linkedlist_wf_at(krnl.rt_ctn, krnl.ctn_mp, container_ptr);
        container_perms_wf_at(krnl.ctn_mp, parent_ptr);
        container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr);
        container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, owner_ptr);
        container_scheduler_wf_at(krnl.ctn_mp, krnl.sched_mp, container_ptr); container_cpu_set_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, container_ptr);
        container_pcid_allocator_wf_container_at(krnl.ctn_mp, krnl.pcid_allc_mp, container_ptr); container_cpu_offline_flags_wf_container_at(krnl.ctn_mp, krnl.cpu_offline_mp, container_ptr);
        container_pages_backward_at(krnl.pg_arr, krnl.ctn_mp, container_ptr);
        scheduler_perms_wf_map(krnl.sched_mp); cpu_set_perms_wf_map(krnl.cpu_set_mp); cpu_set_perms_wf_at(krnl.cpu_set_mp, ro.cpu_set); pcid_allocator_perms_wf_map(krnl.pcid_allc_mp);
        pcid_allocator_perms_wf_at(krnl.pcid_allc_mp, ro.pcid_allocator); cpu_offline_flags_wf_map(krnl.cpu_offline_mp, krnl.cpu_arr);
        allocator_perms_wf_map(krnl.allc_4k_mp); allocator_perms_wf_map(krnl.allc_2m_mp); allocator_perms_wf_map(krnl.allc_1g_mp);
        allocator_perms_wf_at(krnl.allc_4k_mp, ro.allocator_ptr_4k); allocator_perms_wf_at(krnl.allc_2m_mp, ro.allocator_ptr_2m); allocator_perms_wf_at(krnl.allc_1g_mp, ro.allocator_ptr_1g);
        allocator_perms_wf_at(krnl.allc_4k_mp, owner_ro.allocator_ptr_4k); allocator_perms_wf_at(krnl.allc_2m_mp, owner_ro.allocator_ptr_2m);
        lemma_container_allocator_quota_eq_total_free_without_users(*krnl, container_ptr);
        krnl.allc_4k_mp.spec_index(ro.allocator_ptr_4k).global_pool.view().linked_list.lemma_len_view();
        krnl.allc_2m_mp.spec_index(ro.allocator_ptr_2m).global_pool.view().linked_list.lemma_len_view();
        krnl.allc_1g_mp.spec_index(ro.allocator_ptr_1g).global_pool.view().linked_list.lemma_len_view();
        lemma_cache_len_fold_nonneg(krnl.allc_4k_mp.spec_index(ro.allocator_ptr_4k).cpu_caches.view());
        lemma_cache_len_fold_nonneg(krnl.allc_2m_mp.spec_index(ro.allocator_ptr_2m).cpu_caches.view());
        lemma_cache_len_fold_nonneg(krnl.allc_1g_mp.spec_index(ro.allocator_ptr_1g).cpu_caches.view());
        page_array_wf_map(krnl.pg_arr);
        scheduler_pages_wf_at(krnl.sched_mp, krnl.pg_arr, ro.scheduler); cpu_set_pages_wf_at(krnl.cpu_set_mp, krnl.pg_arr, ro.cpu_set);
        allocator_4k_pages_wf_at(krnl.pg_arr, krnl.allc_4k_mp, ro.allocator_ptr_4k); allocator_2m_pages_wf_at(krnl.pg_arr, krnl.allc_2m_mp, ro.allocator_ptr_2m);
        allocator_1g_pages_wf_at(krnl.pg_arr, krnl.allc_1g_mp, ro.allocator_ptr_1g);
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
    }
    let a4 = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().allocator_ptr_4k;
    let a2 = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().allocator_ptr_2m;
    let a1 = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().allocator_ptr_1g;
    let scheduler_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().scheduler;
    let cpu_set_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().cpu_set;
    let pcid_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().pcid_allocator;
    // The container leaves its parent and every ancestor's subtree, and the killer's container takes over its pages.
    let Tracked(node_perm) = container_map_unlink_child(&mut krnl.ctn_mp, parent_ptr, container_ptr, Ghost(ancestors), Tracked(&*lctx), Tracked(parent_perm), Tracked(&container_perm));
    proof { container_perms_wf_at(krnl.ctn_mp, parent_ptr); }
    {
        let owner = krnl.ctn_mp.borrow_mut_typed(owner_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(owner_perm));
        owner.owned_pages = Ghost(owner.owned_pages.view().union(entry.ctn_mp.spec_index(container_ptr).view().owned_pages.view()));
    }
    // Its kernel objects leave their maps.
    let Tracked(container_page) = kill_container_retire_container_object(krnl, Tracked(&mut *lctx), container_ptr, Tracked(node_perm), Tracked(container_perm), Tracked(flag_perms));
    let Tracked(scheduler_page) = kill_container_retire_scheduler_object(krnl, Tracked(&mut *lctx), scheduler_ptr, Tracked(shard_perms));
    let Tracked(cpu_set_page) = kill_container_retire_cpu_set_object(krnl, Tracked(&mut *lctx), cpu_set_ptr, Tracked(cpu_set_perm));
    let Tracked(pcid_page) = kill_container_retire_pcid_allocator_object(krnl, Tracked(&mut *lctx), pcid_ptr, Tracked(pcid_perm));
    let tracked pool = pools_4k.tracked_remove(a4);
    let tracked quota = quotas_4k.tracked_remove(a4);
    let Tracked(a4_page) = kill_container_retire_allocator_4k_object(krnl, Tracked(&mut *lctx), a4, Tracked(caches_4k), Tracked(pool), Tracked(quota));
    let tracked pool = pools_2m.tracked_remove(a2);
    let tracked quota = quotas_2m.tracked_remove(a2);
    let Tracked(a2_page) = kill_container_retire_allocator_2m_object(krnl, Tracked(&mut *lctx), a2, Tracked(caches_2m), Tracked(pool), Tracked(quota));
    let Tracked(a1_page) = kill_container_retire_allocator_1g_object(krnl, Tracked(&mut *lctx), a1, Tracked(caches_1g), Tracked(pool_1g), Tracked(quota_1g));
    let tracked mut page_objects: Map<PageIndex, PagePerm4k> = Map::tracked_empty();
    proof {
        page_objects.tracked_insert(page_ptr2page_index(scheduler_ptr), scheduler_page); page_objects.tracked_insert(page_ptr2page_index(cpu_set_ptr), cpu_set_page);
        page_objects.tracked_insert(page_ptr2page_index(a4), a4_page); page_objects.tracked_insert(page_ptr2page_index(a2), a2_page); page_objects.tracked_insert(page_ptr2page_index(a1), a1_page);
    }
    Tracked((container_page, pcid_page, page_objects))
}

/// In a released view, return the five 4K object pages `pages` to the 4K global pool `o4` and the 2M heads
/// `container_head` and `pcid_head` to the 2M global pool `o2` of the killer's container `owner_ptr`, which takes them
/// and the heads' tails over, and raise both allocators' quotas by the pages returned.
fn kill_container_retire_fill_pools(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, o4: RwLockPageAllocatorPtr, o2: RwLockPageAllocatorPtr, owner_ptr: RwLockContainerPtr,
    pages: &ArrayVec<PageIndex, 5>, Tracked(page_objects): Tracked<Map<PageIndex, PagePerm4k>>, container_head: PageIndex, Tracked(container_page): Tracked<PagePerm2m>,
    pcid_head: PageIndex, Tracked(pcid_page): Tracked<PagePerm2m>, Tracked(page_perms): Tracked<&Map<PageIndex, LockPerm>>, Tracked(tails_container): Tracked<&Map<PageIndex, LockPerm>>,
    Tracked(tails_pcid): Tracked<&Map<PageIndex, LockPerm>>, Tracked(pool_4k): Tracked<&LockPerm>, Tracked(quota_4k): Tracked<&LockPerm>, Tracked(pool_2m): Tracked<&LockPerm>,
    Tracked(quota_2m): Tracked<&LockPerm>,
)
    requires
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        page_array_wf(old(krnl).pg_arr),
        old(krnl).allc_4k_mp.perms_wf(),
        old(krnl).allc_4k_mp.dom().contains(o4),
        old(krnl).allc_4k_mp.spec_index(o4).wf(),
        old(krnl).allc_4k_mp.spec_index(o4).quota.is_init(),
        old(krnl).allc_4k_mp.spec_index(o4).total_free_pages.view() + 5 < usize::MAX,
        old(krnl).allc_4k_mp.spec_index(o4).quota.view().value <= old(krnl).allc_4k_mp.spec_index(o4).total_free_pages.view(),
        typed_lock_map_contains_mode(old(lctx).allocator_global_pool_4k_lock_map(), o4, TypedLockMode::Write),
        pool_4k.state() is WriteLock && pool_4k.thread_id() == old(lctx).thread_id(),
        pool_4k.lock_id() == old(krnl).allc_4k_mp.spec_index(o4).global_pool.locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).allocator_quota_4k_lock_map(), o4, TypedLockMode::Write),
        quota_4k.state() is WriteLock && quota_4k.thread_id() == old(lctx).thread_id(),
        quota_4k.lock_id() == old(krnl).allc_4k_mp.spec_index(o4).quota.locking_thread()->Write_lock_id,
        old(krnl).allc_2m_mp.perms_wf(),
        old(krnl).allc_2m_mp.dom().contains(o2),
        old(krnl).allc_2m_mp.spec_index(o2).wf(),
        old(krnl).allc_2m_mp.spec_index(o2).quota.is_init(),
        old(krnl).allc_2m_mp.spec_index(o2).total_free_pages.view() + 2 < usize::MAX,
        old(krnl).allc_2m_mp.spec_index(o2).quota.view().value <= old(krnl).allc_2m_mp.spec_index(o2).total_free_pages.view(),
        typed_lock_map_contains_mode(old(lctx).allocator_global_pool_2m_lock_map(), o2, TypedLockMode::Write),
        pool_2m.state() is WriteLock && pool_2m.thread_id() == old(lctx).thread_id(),
        pool_2m.lock_id() == old(krnl).allc_2m_mp.spec_index(o2).global_pool.locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).allocator_quota_2m_lock_map(), o2, TypedLockMode::Write),
        quota_2m.state() is WriteLock && quota_2m.thread_id() == old(lctx).thread_id(),
        quota_2m.lock_id() == old(krnl).allc_2m_mp.spec_index(o2).quota.locking_thread()->Write_lock_id,
        pages.wf(),
        pages.view().len() == 5,
        pages.view().no_duplicates(),
        forall|k: int| #![trigger pages.view()[k]] 0 <= k < pages.view().len() ==> {
            let page_index = pages.view()[k];
            &&& index_valid(NUM_PAGES, page_index)
            &&& old(krnl).pg_arr.spec_index(page_index).view().view().state is Allocated4k
            &&& !old(krnl).allc_4k_mp.spec_index(o4).global_pool.view().view().contains(page_index2page_ptr(page_index))
        },
        forall|k: int| #![trigger pages.view()[k]] 0 <= k < pages.view().len() ==> {
            let page_index = pages.view()[k];
            &&& typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_index, TypedLockMode::Write)
            &&& page_perms.dom().contains(page_index)
            &&& page_perms[page_index].state() is WriteLock && page_perms[page_index].thread_id() == old(lctx).thread_id()
            &&& page_perms[page_index].lock_id() == old(krnl).pg_arr.spec_index(page_index).view().locking_thread()->Write_lock_id
        },
        forall|k: int| #![trigger pages.view()[k]] 0 <= k < pages.view().len() ==> {
            &&& page_objects.dom().contains(pages.view()[k])
            &&& page_objects[pages.view()[k]].is_init() && page_objects[pages.view()[k]].addr() == page_index2page_ptr(pages.view()[k])
        },
        page_index_2m_valid(container_head),
        old(krnl).pg_arr.spec_index(container_head).view().view().state is Allocated2m,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), container_head, TypedLockMode::Write),
        page_perms.dom().contains(container_head),
        page_perms[container_head].state() is WriteLock && page_perms[container_head].thread_id() == old(lctx).thread_id(),
        page_perms[container_head].lock_id() == old(krnl).pg_arr.spec_index(container_head).view().locking_thread()->Write_lock_id,
        !old(krnl).allc_2m_mp.spec_index(o2).global_pool.view().view().contains(page_index2page_ptr(container_head)),
        owned_2m_tail_lock_perms_wf(*tails_container, old(krnl).pg_arr, old(lctx), container_head),
        page_index_2m_valid(pcid_head),
        old(krnl).pg_arr.spec_index(pcid_head).view().view().state is Allocated2m,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), pcid_head, TypedLockMode::Write),
        page_perms.dom().contains(pcid_head),
        page_perms[pcid_head].state() is WriteLock && page_perms[pcid_head].thread_id() == old(lctx).thread_id(),
        page_perms[pcid_head].lock_id() == old(krnl).pg_arr.spec_index(pcid_head).view().locking_thread()->Write_lock_id,
        !old(krnl).allc_2m_mp.spec_index(o2).global_pool.view().view().contains(page_index2page_ptr(pcid_head)),
        owned_2m_tail_lock_perms_wf(*tails_pcid, old(krnl).pg_arr, old(lctx), pcid_head),
        container_head != pcid_head,
        container_page.is_init() && container_page.addr() == page_index2page_ptr(container_head),
        pcid_page.is_init() && pcid_page.addr() == page_index2page_ptr(pcid_head),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom(),
        forall|p: PageIndex| #![trigger final(lctx).page_lock_map().index(p)]
            old(lctx).page_lock_map().dom().contains(p) ==> final(lctx).page_lock_map().index(p).mode == old(lctx).page_lock_map().index(p).mode,
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        owned_2m_tail_lock_perms_wf(*tails_container, final(krnl).pg_arr, final(lctx), container_head),
        owned_2m_tail_lock_perms_wf(*tails_pcid, final(krnl).pg_arr, final(lctx), pcid_head),
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, allc_4k_mp: final(krnl).allc_4k_mp, allc_2m_mp: final(krnl).allc_2m_mp, ..*old(krnl) }),
        ({
            let heads = seq![container_head, pcid_head];
            let tails = kill_container_retire_tails(heads);
            &&& final(krnl).allc_4k_mp.perms_wf()
            &&& final(krnl).allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom()
            &&& forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_4k_mp.spec_index(a)]
                final(krnl).allc_4k_mp.dom().contains(a) && a != o4 ==> final(krnl).allc_4k_mp.spec_index(a) == old(krnl).allc_4k_mp.spec_index(a)
            &&& ({
                let pre_allocator = old(krnl).allc_4k_mp.spec_index(o4);
                let post_allocator = final(krnl).allc_4k_mp.spec_index(o4);
                let pre_pool = pre_allocator.global_pool.view();
                let post_pool = post_allocator.global_pool.view();
                &&& post_allocator.wf()
                &&& post_allocator.total_free_pages.view() == pre_allocator.total_free_pages.view() + 5
                &&& post_allocator.quota.view() == (AllocatorQuota { value: (pre_allocator.quota.view().value + 5) as usize, ..pre_allocator.quota.view() })
                &&& post_allocator.quota.locking_thread() == pre_allocator.quota.locking_thread()
                &&& post_allocator.quota.is_init()
                &&& post_pool.view().len() == pre_pool.view().len() + 5
                &&& forall|p: PagePtr| #![trigger post_pool.view().contains(p)] post_pool.view().contains(p) == (pre_pool.view().contains(p) || pages.view().contains(page_ptr2page_index(p)) && page_ptr_valid(p))
                &&& forall|a: usize| #![trigger pre_pool.map().dom().contains(a)] pre_pool.map().dom().contains(a) ==> post_pool.map().dom().contains(a) && post_pool.map().spec_index(a) == pre_pool.map().spec_index(a)
                &&& forall|k: int| #![trigger pages.view()[k]] 0 <= k < 5 ==> {
                    let node = old(krnl).pg_arr.spec_index(pages.view()[k]).view().view().free_list_node_storage.addr();
                    &&& post_pool.map().dom().contains(node)
                    &&& post_pool.map().spec_index(node) == page_index2page_ptr(pages.view()[k])
                }
                &&& post_allocator.global_pool.locking_thread() == pre_allocator.global_pool.locking_thread()
                &&& post_allocator.cpu_caches == pre_allocator.cpu_caches
                &&& post_allocator.owning_container == pre_allocator.owning_container
            })
            &&& final(krnl).allc_2m_mp.perms_wf()
            &&& final(krnl).allc_2m_mp.dom() == old(krnl).allc_2m_mp.dom()
            &&& forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_2m_mp.spec_index(a)]
                final(krnl).allc_2m_mp.dom().contains(a) && a != o2 ==> final(krnl).allc_2m_mp.spec_index(a) == old(krnl).allc_2m_mp.spec_index(a)
            &&& ({
                let pre_allocator = old(krnl).allc_2m_mp.spec_index(o2);
                let post_allocator = final(krnl).allc_2m_mp.spec_index(o2);
                let pre_pool = pre_allocator.global_pool.view();
                let post_pool = post_allocator.global_pool.view();
                &&& post_allocator.wf()
                &&& post_allocator.total_free_pages.view() == pre_allocator.total_free_pages.view() + 2
                &&& post_allocator.quota.view() == (AllocatorQuota { value: (pre_allocator.quota.view().value + 2) as usize, ..pre_allocator.quota.view() })
                &&& post_allocator.quota.locking_thread() == pre_allocator.quota.locking_thread()
                &&& post_allocator.quota.is_init()
                &&& post_pool.view().len() == pre_pool.view().len() + 2
                &&& post_pool.view() == pre_pool.view().insert(0, page_index2page_ptr(heads[0])).insert(0, page_index2page_ptr(heads[1]))
                &&& forall|a: usize| #![trigger pre_pool.map().dom().contains(a)] pre_pool.map().dom().contains(a) ==> post_pool.map().dom().contains(a) && post_pool.map().spec_index(a) == pre_pool.map().spec_index(a)
                &&& forall|k: int| #![trigger heads[k]] 0 <= k < 2 ==> {
                    let node = old(krnl).pg_arr.spec_index(heads[k]).view().view().free_list_node_storage.addr();
                    &&& post_pool.map().dom().contains(node)
                    &&& post_pool.map().spec_index(node) == page_index2page_ptr(heads[k])
                }
                &&& post_allocator.global_pool.locking_thread() == pre_allocator.global_pool.locking_thread()
                &&& post_allocator.cpu_caches == pre_allocator.cpu_caches
                &&& post_allocator.owning_container == pre_allocator.owning_container
            })
            &&& page_array_wf(final(krnl).pg_arr)
            &&& forall|i: PageIndex| #![trigger final(krnl).pg_arr.spec_index(i)]
                index_valid(NUM_PAGES, i) && !pages.view().contains(i) && !heads.contains(i) && !tails.contains(i) ==> final(krnl).pg_arr.spec_index(i) == old(krnl).pg_arr.spec_index(i)
            &&& forall|k: int| #![trigger pages.view()[k]] 0 <= k < 5 ==> {
                let pre_page = old(krnl).pg_arr.spec_index(pages.view()[k]).view();
                let post_page = final(krnl).pg_arr.spec_index(pages.view()[k]).view();
                &&& post_page.is_init() == pre_page.is_init()
                &&& post_page.locking_thread() == pre_page.locking_thread()
                &&& post_page.view().free_list_node_storage.addr() == pre_page.view().free_list_node_storage.addr()
                &&& post_page.view() == (Page { state: PageState::Free4k { allocator_ptr: Ghost(o4), state: FreePageAllocatorState::GlobalList },
                    owning_container: owner_ptr, free_list_node_storage: post_page.view().free_list_node_storage, perm_4k: post_page.view().perm_4k, ..pre_page.view() })
            }
            &&& forall|k: int| #![trigger heads[k]] 0 <= k < 2 ==> {
                let pre_page = old(krnl).pg_arr.spec_index(heads[k]).view();
                let post_page = final(krnl).pg_arr.spec_index(heads[k]).view();
                &&& post_page.is_init() == pre_page.is_init()
                &&& post_page.locking_thread() == pre_page.locking_thread()
                &&& post_page.view().free_list_node_storage.addr() == pre_page.view().free_list_node_storage.addr()
                &&& post_page.view() == (Page { state: PageState::Free2m { allocator_ptr: Ghost(o2), state: FreePageAllocatorState::GlobalList },
                    owning_container: owner_ptr, free_list_node_storage: post_page.view().free_list_node_storage, perm_2m: post_page.view().perm_2m, ..pre_page.view() })
            }
            &&& forall|i: PageIndex| #![trigger final(krnl).pg_arr.spec_index(i)] tails.contains(i) ==> {
                &&& final(krnl).pg_arr.spec_index(i).view().view() == (Page { owning_container: owner_ptr, ..old(krnl).pg_arr.spec_index(i).view().view() })
                &&& final(krnl).pg_arr.spec_index(i).view().is_init() == old(krnl).pg_arr.spec_index(i).view().is_init()
                &&& final(krnl).pg_arr.spec_index(i).view().locking_thread() == old(krnl).pg_arr.spec_index(i).view().locking_thread()
            }
        }),
{
    kill_container_retire_pages_4k_to_pool(krnl, pages, Tracked(page_objects), o4, owner_ptr, Tracked(&mut *lctx), Tracked(page_perms), Tracked(pool_4k));
    kill_container_retire_head_2m_to_pool(krnl, container_head, Tracked(container_page), o2, owner_ptr, Tracked(&mut *lctx), Tracked(page_perms.tracked_borrow(container_head)),
        Tracked(tails_container), Tracked(pool_2m));
    kill_container_retire_head_2m_to_pool(krnl, pcid_head, Tracked(pcid_page), o2, owner_ptr, Tracked(&mut *lctx), Tracked(page_perms.tracked_borrow(pcid_head)), Tracked(tails_pcid),
        Tracked(pool_2m));
    {
        let quota = krnl.allc_4k_mp.borrow_mut_quota_typed(o4, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
            Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(quota_4k));
        quota.value = quota.value + 5;
    }
    {
        let quota = krnl.allc_2m_mp.borrow_mut_quota_typed(o2, Ghost(lctx.allocator_quota_2m_lock_map()), Ghost(lctx.allocator_cache_2m_lock_map()),
            Ghost(lctx.allocator_global_pool_2m_lock_map()), Tracked(&*lctx), Tracked(quota_2m));
        quota.value = quota.value + 2;
    }
    proof { page_ptr_roundtrip(); page_index_roundtrip(); page_index_valid_imply_page_ptr_valid(); }
}

/// With the transition committed and every kernel invariant restored, release the global pools and quotas `o4` and
/// `o2` of the killer's container's allocators, the five 4K pages `pages`, the 2M heads `container_head` and
/// `pcid_head`, and their tails.
fn kill_container_retire_unlock(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, o4: RwLockPageAllocatorPtr, o2: RwLockPageAllocatorPtr, container_head: PageIndex, pcid_head: PageIndex,
    pages: &ArrayVec<PageIndex, 5>, Tracked(pools_4k): Tracked<Map<RwLockPageAllocatorPtr, LockPerm>>, Tracked(pools_2m): Tracked<Map<RwLockPageAllocatorPtr, LockPerm>>,
    Tracked(quotas_4k): Tracked<Map<RwLockPageAllocatorPtr, LockPerm>>, Tracked(quotas_2m): Tracked<Map<RwLockPageAllocatorPtr, LockPerm>>, Tracked(page_perms): Tracked<Map<PageIndex, LockPerm>>,
    Tracked(tails_container): Tracked<Map<PageIndex, LockPerm>>, Tracked(tails_pcid): Tracked<Map<PageIndex, LockPerm>>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        old(krnl).allc_4k_mp.dom().contains(o4),
        old(krnl).allc_2m_mp.dom().contains(o2),
        old(lctx).allocator_global_pool_4k_lock_map().dom() == set![o4],
        old(lctx).allocator_quota_4k_lock_map().dom() == set![o4],
        old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_2m_lock_map().dom() == set![o2],
        old(lctx).allocator_quota_2m_lock_map().dom() == set![o2],
        old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        pools_4k.dom().contains(o4) && quotas_4k.dom().contains(o4) && pools_2m.dom().contains(o2) && quotas_2m.dom().contains(o2),
        typed_lock_map_contains_mode(old(lctx).allocator_global_pool_4k_lock_map(), o4, TypedLockMode::Write),
        pools_4k[o4].state() is WriteLock && pools_4k[o4].thread_id() == old(lctx).thread_id(),
        pools_4k[o4].lock_id() == old(krnl).allc_4k_mp.spec_index(o4).global_pool.locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).allocator_quota_4k_lock_map(), o4, TypedLockMode::Write),
        quotas_4k[o4].state() is WriteLock && quotas_4k[o4].thread_id() == old(lctx).thread_id(),
        quotas_4k[o4].lock_id() == old(krnl).allc_4k_mp.spec_index(o4).quota.locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).allocator_global_pool_2m_lock_map(), o2, TypedLockMode::Write),
        pools_2m[o2].state() is WriteLock && pools_2m[o2].thread_id() == old(lctx).thread_id(),
        pools_2m[o2].lock_id() == old(krnl).allc_2m_mp.spec_index(o2).global_pool.locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).allocator_quota_2m_lock_map(), o2, TypedLockMode::Write),
        quotas_2m[o2].state() is WriteLock && quotas_2m[o2].thread_id() == old(lctx).thread_id(),
        quotas_2m[o2].lock_id() == old(krnl).allc_2m_mp.spec_index(o2).quota.locking_thread()->Write_lock_id,
        pages.wf(),
        pages.view().len() == 5,
        pages.view().no_duplicates(),
        forall|k: int| #![trigger pages.view()[k]] 0 <= k < pages.view().len() ==> index_valid(NUM_PAGES, pages.view()[k]),
        page_index_2m_valid(container_head),
        page_index_2m_valid(pcid_head),
        container_head != pcid_head,
        !pages.view().contains(container_head) && !pages.view().contains(pcid_head),
        page_perms.dom() == pages.view().to_set().insert(container_head).insert(pcid_head),
        forall|p: PageIndex| #![trigger page_perms.dom().contains(p)] page_perms.dom().contains(p) ==> {
            &&& typed_lock_map_contains_mode(old(lctx).page_lock_map(), p, TypedLockMode::Write)
            &&& page_perms[p].state() is WriteLock && page_perms[p].thread_id() == old(lctx).thread_id()
            &&& page_perms[p].lock_id() == old(krnl).pg_arr.spec_index(p).view().locking_thread()->Write_lock_id
        },
        old(lctx).page_lock_map().dom() == page_perms.dom() + page_2m_tail_indices(container_head) + page_2m_tail_indices(pcid_head),
        forall|k: int| #![trigger pages.view()[k]] 0 <= k < pages.view().len() ==> old(krnl).pg_arr.spec_index(pages.view()[k]).view().view().state is Free4k,
        old(krnl).pg_arr.spec_index(container_head).view().view().state is Free2m,
        old(krnl).pg_arr.spec_index(pcid_head).view().view().state is Free2m,
        owned_2m_tail_lock_perms_wf(tails_container, old(krnl).pg_arr, old(lctx), container_head),
        owned_2m_tail_lock_perms_wf(tails_pcid, old(krnl).pg_arr, old(lctx), pcid_head),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).page_lock_map().dom().is_empty(),
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        final(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        final(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, allc_4k_mp: final(krnl).allc_4k_mp, allc_2m_mp: final(krnl).allc_2m_mp, ..*old(krnl) }),
        final(krnl).allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
        forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_4k_mp.spec_index(a)]
            final(krnl).allc_4k_mp.dom().contains(a) ==> final(krnl).allc_4k_mp.spec_index(a).quota.view() == old(krnl).allc_4k_mp.spec_index(a).quota.view(),
        final(krnl).allc_2m_mp.dom() == old(krnl).allc_2m_mp.dom(),
        forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_2m_mp.spec_index(a)]
            final(krnl).allc_2m_mp.dom().contains(a) ==> final(krnl).allc_2m_mp.spec_index(a).quota.view() == old(krnl).allc_2m_mp.spec_index(a).quota.view(),
{
    let tracked mut pools_4k = pools_4k;
    let tracked mut pools_2m = pools_2m;
    let tracked mut quotas_4k = quotas_4k;
    let tracked mut quotas_2m = quotas_2m;
    let tracked mut page_perms = page_perms;
    let ghost entry = *krnl;
    wunlock_owned_2m_page_tails(krnl, container_head, Tracked(&mut *lctx), Tracked(tails_container));
    wunlock_owned_2m_page_tails(krnl, pcid_head, Tracked(&mut *lctx), Tracked(tails_pcid));
    let tracked perm = quotas_4k.tracked_remove(o4);
    krnl.wunlock_allocator_quota_4k(o4, Tracked(&mut *lctx), Tracked(perm));
    let tracked perm = quotas_2m.tracked_remove(o2);
    krnl.wunlock_allocator_quota_2m(o2, Tracked(&mut *lctx), Tracked(perm));
    let tracked perm = pools_4k.tracked_remove(o4);
    krnl.wunlock_allocator_global_pool_4k(o4, Tracked(&mut *lctx), Tracked(perm));
    let tracked perm = pools_2m.tracked_remove(o2);
    krnl.wunlock_allocator_global_pool_2m(o2, Tracked(&mut *lctx), Tracked(perm));
    proof {
        assert(lctx.allocator_quota_4k_lock_map().dom() =~= Set::<RwLockPageAllocatorPtr>::empty() && lctx.allocator_global_pool_4k_lock_map().dom() =~= Set::<RwLockPageAllocatorPtr>::empty());
        assert(lctx.allocator_quota_2m_lock_map().dom() =~= Set::<RwLockPageAllocatorPtr>::empty() && lctx.allocator_global_pool_2m_lock_map().dom() =~= Set::<RwLockPageAllocatorPtr>::empty());
    }
    let ghost unlocked = *krnl;
    let tracked perm = page_perms.tracked_remove(container_head);
    krnl.wunlock_page(container_head, Tracked(&mut *lctx), Tracked(perm));
    let tracked perm = page_perms.tracked_remove(pcid_head);
    krnl.wunlock_page(pcid_head, Tracked(&mut *lctx), Tracked(perm));
    proof { assert(page_perms.dom() =~= pages.view().to_set()); }
    wunlock_kill_retire_pages(krnl, pages, Tracked(&mut *lctx), Tracked(page_perms));
    proof { assert(lctx.page_lock_map().dom() =~= Set::<PageIndex>::empty()); }
}
} // verus!
