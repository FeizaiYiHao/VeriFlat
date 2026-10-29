use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::reclaim_dangling_thread_eof::reclaim_dangling_thread_eof_fields;
use super::reclaim_dangling_thread_helpers::{reclaim_dangling_thread_commit, reclaim_dangling_thread_drain_full_cache};

verus! {
/// Reclaim the write-held killed dangling thread `dangling_ptr`: take its page, the 4K allocator cache on `cpu_id` of the page's owner
/// (draining it first when full, which ends the step), and that allocator's quota; then remove the dangling thread from the thread
/// map and its containers' thread sets, return its page to the cache, grow the quota by one, and release those locks.
/// The caller ends the reclaim step.
pub fn reclaim_dangling_thread(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, dangling_ptr: RwLockThreadPtr,
    Tracked(dangling_lock_perm): Tracked<LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        old(steps).snapshot_k() == *old(krnl),
        killed_thread_reclaim_lock_context(*old(krnl), *old(lctx)),
        old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
        old(krnl).thr_mp.dom().contains(dangling_ptr),
        old(krnl).thr_mp.spec_index(dangling_ptr).view().state is KILLED,
        old(krnl).thr_mp.spec_index(dangling_ptr).view().proc_linkedlist_node.is_init(),
        old(krnl).thr_mp.spec_index(dangling_ptr).view().caller is None,
        old(krnl).thr_mp.spec_index(dangling_ptr).view().callee is None,
        forall|j: int| #![trigger old(krnl).thr_mp.spec_index(dangling_ptr).view().endpoint_descriptors.view().spec_index(j)]
            0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==> old(krnl).thr_mp.spec_index(dangling_ptr).view().endpoint_descriptors.view().spec_index(j) is None,
        old(krnl).thr_mp.spec_index(dangling_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(dangling_ptr).view().quota_4k == 0,
        old(krnl).thr_mp.spec_index(dangling_ptr).view().quota_2m == 0,
        old(krnl).thr_mp.spec_index(dangling_ptr).view().quota_1g == 0,
        old(krnl).thr_mp.spec_index(dangling_ptr).view().free_quota_pending_clean(),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), dangling_ptr, TypedLockMode::Write),
        dangling_lock_perm.state() is WriteLock,
        dangling_lock_perm.thread_id() == old(lctx).thread_id(),
        dangling_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(dangling_ptr).locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Thread(dangling_ptr)),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).view() == old(steps).view(),
        final(steps).nonlock_view() == old(steps).nonlock_view(),
        kernel_dangling_thread_reclaimed_fields(&final(steps).snapshot_k(), final(krnl), dangling_ptr),
        final(krnl).cpu_arr == final(steps).snapshot_k().cpu_arr,
        final(krnl).cpu_op == final(steps).snapshot_k().cpu_op,
        final(krnl).prc_mp == final(steps).snapshot_k().prc_mp,
        final(krnl).thr_mp.dom() == final(steps).snapshot_k().thr_mp.dom().remove(dangling_ptr),
        forall|t: RwLockThreadPtr| #![trigger final(krnl).thr_mp.spec_index(t)]
            final(krnl).thr_mp.dom().contains(t) ==> final(krnl).thr_mp.spec_index(t) == final(steps).snapshot_k().thr_mp.spec_index(t),
        final(krnl).ctn_mp.dom() == final(steps).snapshot_k().ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(c)] final(krnl).ctn_mp.dom().contains(c) ==> {
            &&& final(krnl).ctn_mp.spec_index(c).view() == final(steps).snapshot_k().ctn_mp.spec_index(c).view()
            &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == final(steps).snapshot_k().ctn_mp.spec_index(c).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == final(steps).snapshot_k().ctn_mp.spec_index(c).locking_thread()
            &&& final(krnl).ctn_mp.spec_index(c).being_killed() == final(steps).snapshot_k().ctn_mp.spec_index(c).being_killed()
            &&& final(krnl).ctn_mp.spec_index(c).killer_info() == final(steps).snapshot_k().ctn_mp.spec_index(c).killer_info()
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq == final(steps).snapshot_k().ctn_mp.spec_index(c).view_ghost().uppertree_seq
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set == final(steps).snapshot_k().ctn_mp.spec_index(c).view_ghost().subtree_set
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes == final(steps).snapshot_k().ctn_mp.spec_index(c).view_ghost().owned_processes
        },
        held_containers_unchanged(old(krnl).ctn_mp, final(steps).snapshot_k().ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(steps).snapshot_k().prc_mp, old(lctx)),
        held_threads_unchanged(old(krnl).thr_mp, final(steps).snapshot_k().thr_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(steps).snapshot_k().cpu_arr, old(lctx)),
        held_threads_unchanged_except(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx), set![dangling_ptr]),
        killed_thread_reclaim_lock_context(*final(krnl), *final(lctx)),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] == old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int],
{
    proof {
        held_kernel_objects_unchanged_reflexive(&*krnl, &*lctx);
        thread_perms_wf_at(krnl.thr_mp, dangling_ptr); page_ptr_valid_imply_page_index_valid();
        assert(page_ptr_valid(dangling_ptr) && krnl.pg_arr.spec_index(page_ptr2page_index(dangling_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsThread })) by { thread_pages_wf_at(krnl.thr_mp, krnl.pg_arr, dangling_ptr); };
    }
    let page_index = page_ptr2page_index(dangling_ptr);
    let Tracked(page_lock_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));
    proof { page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, page_index); }
    let owner = krnl.pg_arr.borrow_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(&page_lock_perm)).owning_container;
    proof { assert(krnl.ctn_mp.dom().contains(owner)) by { container_page_owner_backward_at(krnl.ctn_mp, krnl.pg_arr, page_index); }; container_perms_wf_at(krnl.ctn_mp, owner); }
    let allocator_ptr = krnl.ctn_mp.borrow_rodata(owner).borrow().allocator_ptr_4k;
    proof { assert(krnl.allc_4k_mp.dom().contains(allocator_ptr)) by { container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, owner); }; }
    let Tracked(cache_lock_perm) = krnl.wlock_allocator_cache_4k(allocator_ptr, cpu_id, Tracked(&mut *lctx));
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    reclaim_dangling_thread_drain_full_cache(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, allocator_ptr, Tracked(&cache_lock_perm));
    proof {
        assert(krnl.ctn_mp.dom().contains(owner) && krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr) by {
            container_page_owner_backward_at(krnl.ctn_mp, krnl.pg_arr, page_index);
        };
        assert(krnl.allc_4k_mp.spec_index(allocator_ptr).wf()) by { allocator_perms_wf_at(krnl.allc_4k_mp, allocator_ptr); };
    }
    let Tracked(quota_lock_perm) = krnl.wlock_allocator_quota_4k(allocator_ptr, Tracked(&mut *lctx));
    let ghost start = steps.snapshot_k();
    let ghost entry = *krnl;
    proof { assert(kernel_container_nonlock_fields_and_quotas_unchanged(&start, &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; }; }
    let (cache_node_addr, _removed_lctx) = reclaim_dangling_thread_commit(krnl, Tracked(&mut *lctx), cpu_id, dangling_ptr, page_index, owner, allocator_ptr, Tracked(dangling_lock_perm),
        Tracked(&page_lock_perm), Tracked(&cache_lock_perm), Tracked(&quota_lock_perm));
    let ghost mid = *krnl;
    krnl.wunlock_allocator_quota_4k(allocator_ptr, Tracked(&mut *lctx), Tracked(quota_lock_perm));
    krnl.wunlock_allocator_cache_4k(allocator_ptr, cpu_id, Tracked(&mut *lctx), Tracked(cache_lock_perm));
    krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_lock_perm));
    proof {
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&mid, &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        reclaim_dangling_thread_eof_fields(start, entry, mid, *krnl, cpu_id, dangling_ptr, owner, allocator_ptr, cache_node_addr);
        assert(lctx.page_lock_map() =~= old(lctx).page_lock_map());
        assert(lctx.allocator_quota_4k_lock_map() =~= old(lctx).allocator_quota_4k_lock_map());
        assert(lctx.allocator_cache_4k_lock_map() =~= old(lctx).allocator_cache_4k_lock_map());
        assert(lctx.allocator_global_pool_4k_lock_map() =~= old(lctx).allocator_global_pool_4k_lock_map());
        assert(killed_thread_reclaim_lock_context(*krnl, *lctx)) by { thread_cpu_wf_cpu_at(old(krnl).thr_mp, old(krnl).cpu_arr, old(lctx).cpu_id()); };
    }
}
} // verus!
