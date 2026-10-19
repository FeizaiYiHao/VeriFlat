use vstd::prelude::*;
use crate::*;
use super::super::free_4k_page::drain_4k_cache_batch;
#[cfg(verus_keep_ghost)]
use super::reclaim_dangling_thread_spec::reclaim_dangling_thread_eof_transition_framing;
#[cfg(verus_keep_ghost)]
use super::reclaim_dangling_thread_eof::{reclaim_dangling_thread_eof, reclaim_dangling_thread_eof_fields};

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
        },
        held_containers_unchanged(old(krnl).ctn_mp, final(steps).snapshot_k().ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(steps).snapshot_k().prc_mp, old(lctx)),
        held_threads_unchanged(old(krnl).thr_mp, final(steps).snapshot_k().thr_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(steps).snapshot_k().cpu_arr, old(lctx)),
        held_threads_unchanged_except(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx), set![dangling_ptr]),
        killed_thread_reclaim_lock_context(*final(krnl), *final(lctx)),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
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
    let cache = krnl.allc_4k_mp.borrow_cache_typed(allocator_ptr, cpu_id, Ghost(lctx.allocator_cache_4k_lock_map()), Tracked(&*lctx), Tracked(&cache_lock_perm));
    if cache.linked_list.len() == ALLOCATOR_MAX_WATERMARK {
        let Tracked(pool_lock_perm) = krnl.wlock_allocator_global_pool_4k(allocator_ptr, Tracked(&mut *lctx));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl);
        }
        drain_4k_cache_batch(krnl, allocator_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&cache_lock_perm), Tracked(&pool_lock_perm));
        krnl.wunlock_allocator_global_pool_4k(allocator_ptr, Tracked(&mut *lctx), Tracked(pool_lock_perm));
        proof {
            kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl);
            krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
        }
    }
    proof {
        assert(krnl.ctn_mp.dom().contains(owner) && krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr) by {
            container_page_owner_backward_at(krnl.ctn_mp, krnl.pg_arr, page_index);
        };
        assert(krnl.allc_4k_mp.spec_index(allocator_ptr).wf()) by { allocator_perms_wf_at(krnl.allc_4k_mp, allocator_ptr); };
    }
    let Tracked(quota_lock_perm) = krnl.wlock_allocator_quota_4k(allocator_ptr, Tracked(&mut *lctx));
    let ghost start = steps.snapshot_k();
    let ghost entry = *krnl;
    let ghost container_ptr = krnl.thr_mp.spec_index(dangling_ptr).view().owning_container;
    let ghost uppers = krnl.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view();
    proof {
        container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, dangling_ptr); container_perms_wf_map(krnl.ctn_mp); container_perms_wf_at(krnl.ctn_mp, container_ptr);
        assert(uppers.to_set().subset_of(krnl.ctn_mp.dom()) && !uppers.to_set().contains(container_ptr)) by {
            uppers.to_set_ensures(); container_uppertree_seq_in_dom(krnl.rt_ctn, krnl.ctn_mp, container_ptr); container_uppertree_seq_not_self(krnl.rt_ctn, krnl.ctn_mp, container_ptr);
        };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&start, &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        thread_perms_wf_map(krnl.thr_mp);
        thread_perms_wf_at(krnl.thr_mp, dangling_ptr); page_array_wf_at(krnl.pg_arr, page_index);
        krnl.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), dangling_ptr);
        lemma_container_allocator_4k_quota_bounded(&*krnl, owner);
        allocator_perms_wf_at(krnl.allc_4k_mp, allocator_ptr);
        assert(!krnl.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().contains(dangling_ptr)) by { container_allocator_free_4k_page_wf_cache_at(krnl.allc_4k_mp, krnl.pg_arr, allocator_ptr, cpu_id, dangling_ptr); };
        lctx.enter_kernel_view_release();
    }
    let Tracked(proc_node_perm) = {
        let dangling_mut = krnl.thr_mp.borrow_mut_typed(dangling_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&dangling_lock_perm));
        dangling_mut.take_proc_node()
    };
    let Tracked(page_perm) = krnl.remove_thread_and_reclaim_4k_page_perm(dangling_ptr, Tracked(proc_node_perm), Tracked(dangling_lock_perm), Tracked(&mut *lctx));
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
    let (cache_node_addr, cache_node_perm) = page_array_retire_kernel_object_4k_to_cache(&mut krnl.pg_arr, page_index, Tracked(page_perm), allocator_ptr, cpu_id, Tracked(&*lctx), Tracked(&page_lock_perm));
    proof { lctx.update_lock_id(KernelObjId::Page(page_index), old_page_lock_id, krnl.pg_arr.lock_id_by_index(page_index)); }
    krnl.allc_4k_mp.push_cache_page_typed(allocator_ptr, cpu_id, cache_node_addr, cache_node_perm, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
        Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(&cache_lock_perm));
    {
        let quota = krnl.allc_4k_mp.borrow_mut_quota_typed(allocator_ptr, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
            Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(&quota_lock_perm));
        quota.value = quota.value + 1;
    }
    proof { remove_thread_from_container_sets(&mut krnl.ctn_mp, container_ptr, dangling_ptr, uppers, lctx.container_lock_map(), lctx.thread_id()); }
    let ghost mid = *krnl;
    proof {
        assert(reclaim_dangling_thread_eof_transition_framing(entry, mid, cpu_id, dangling_ptr, owner, allocator_ptr, cache_node_addr)) by { reveal(reclaim_dangling_thread_eof_transition_framing); };
        reclaim_dangling_thread_eof(entry, mid, cpu_id, dangling_ptr, owner, allocator_ptr, cache_node_addr);
    }
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
