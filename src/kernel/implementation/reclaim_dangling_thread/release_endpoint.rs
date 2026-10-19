use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::release_endpoint_spec::release_endpoint_eof_transition_framing;
#[cfg(verus_keep_ghost)]
use super::release_endpoint_eof::{release_endpoint_eof, release_endpoint_eof_fields};

verus! {
/// Release the write-held endpoint `endpoint_ptr` whose only reference is descriptor `index` of the write-held thread
/// `thread_ptr`: take its page and the global 4K pool and quota of the page owner's allocator; then clear the descriptor,
/// remove the endpoint from the endpoint map and its owner's endpoint set, return its page to the pool, grow the quota by
/// one, and release those locks.
pub fn release_endpoint_last_reference(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, index: EndpointIdx,
    Tracked(thread_lock_perm): Tracked<&LockPerm>, Tracked(endpoint_lock_perm): Tracked<LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        forall|t: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(t)] old(lctx).thread_lock_map().dom().contains(t) ==> {
            let state = old(krnl).thr_mp.spec_index(t).view().state;
            !(state.is_endpoint_waiting() || state.is_reply_waiting() || state is IPC_ENDPOINT_TRANSIT || state is SCHEDULED)
        },
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state is RUNNING || old(krnl).thr_mp.spec_index(thread_ptr).view().state is KILLED,
        old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[index as int] == Some(endpoint_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).ep_mp.dom().contains(endpoint_ptr),
        old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_threads.view() == set![(thread_ptr, index)],
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
        endpoint_lock_perm.state() is WriteLock,
        endpoint_lock_perm.thread_id() == old(lctx).thread_id(),
        endpoint_lock_perm.lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Endpoint(endpoint_ptr)),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.view() == Seq::<RwLockThreadPtr>::empty(),
        *final(krnl) == (KernelK { ctn_mp: final(krnl).ctn_mp, thr_mp: final(krnl).thr_mp, ep_mp: final(krnl).ep_mp, pg_arr: final(krnl).pg_arr, allc_4k_mp: final(krnl).allc_4k_mp, ..*old(krnl) }),
        final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { endpoint_descriptors: final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view().update(index as int, None),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).thr_mp.lock_id_by_key(thread_ptr) == old(krnl).thr_mp.lock_id_by_key(thread_ptr),
        final(krnl).ep_mp.dom() == old(krnl).ep_mp.dom().remove(endpoint_ptr),
        forall|e: RwLockEndpointPtr| #![trigger final(krnl).ep_mp.spec_index(e)] final(krnl).ep_mp.dom().contains(e) ==> final(krnl).ep_mp.spec_index(e) == old(krnl).ep_mp.spec_index(e),
        final(krnl).ctn_mp.dom() == old(krnl).ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(c)]
            old(krnl).ctn_mp.dom().contains(c) ==> {
                let a = old(krnl).ctn_mp.spec_index(c);
                let b = final(krnl).ctn_mp.spec_index(c);
                &&& b.view() == a.view()
                &&& b.view_rodata() == a.view_rodata()
                &&& b.locking_thread() == a.locking_thread()
                &&& b.being_killed() == a.being_killed()
                &&& b.view_ghost() == if c == old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container {
                        ContainerGhost { owned_endpoints: Ghost(a.view_ghost().owned_endpoints.view().remove(endpoint_ptr)), ..a.view_ghost() }
                    } else { a.view_ghost() }
                &&& final(krnl).allc_4k_mp.spec_index(a.view_rodata().view().allocator_ptr_4k).quota.view().view() as int
                    == old(krnl).allc_4k_mp.spec_index(a.view_rodata().view().allocator_ptr_4k).quota.view().view() as int + if a.view().owned_pages.view().contains(endpoint_ptr) { 1int } else { 0int }
            },
{
    proof {
        page_ptr_valid_imply_page_index_valid();
        endpoint_pages_wf_page_at(krnl.ep_mp, krnl.pg_arr, endpoint_ptr);
    }
    let page_index = page_ptr2page_index(endpoint_ptr);
    let Tracked(page_lock_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));
    proof { page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, page_index); }
    let owner = krnl.pg_arr.borrow_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(&page_lock_perm)).owning_container;
    proof { assert(krnl.ctn_mp.dom().contains(owner)) by { container_page_owner_backward_at(krnl.ctn_mp, krnl.pg_arr, page_index); }; container_perms_wf_at(krnl.ctn_mp, owner); }
    let allocator_ptr = krnl.ctn_mp.borrow_rodata(owner).borrow().allocator_ptr_4k;
    proof { assert(krnl.allc_4k_mp.dom().contains(allocator_ptr)) by { container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, owner); }; }
    let Tracked(pool_lock_perm) = krnl.wlock_allocator_global_pool_4k(allocator_ptr, Tracked(&mut *lctx));
    let Tracked(quota_lock_perm) = krnl.wlock_allocator_quota_4k(allocator_ptr, Tracked(&mut *lctx));
    let ghost entry = *krnl;
    let ghost endpoint_owner = krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container;
    proof {
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &entry)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        assert(krnl.ctn_mp.dom().contains(owner) && krnl.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr) by {
            container_page_owner_backward_at(krnl.ctn_mp, krnl.pg_arr, page_index);
        };
        thread_perms_wf_map(krnl.thr_mp); thread_perms_wf_at(krnl.thr_mp, thread_ptr);
        endpoint_perms_wf_map(krnl.ep_mp); endpoint_perms_wf_at(krnl.ep_mp, endpoint_ptr);
        container_perms_wf_map(krnl.ctn_mp);
        assert(krnl.ctn_mp.dom().contains(endpoint_owner)) by { container_endpoint_wf_at(krnl.ctn_mp, krnl.ep_mp, endpoint_ptr); };
        page_array_wf_at(krnl.pg_arr, page_index);
        allocator_perms_wf_map(krnl.allc_4k_mp); allocator_perms_wf_at(krnl.allc_4k_mp, allocator_ptr);
        lemma_container_allocator_4k_quota_bounded(&*krnl, owner);
        assert(!krnl.allc_4k_mp.spec_index(allocator_ptr).global_pool.view().view().contains(endpoint_ptr)) by {
            container_allocator_free_4k_page_wf_global_at(krnl.allc_4k_mp, krnl.pg_arr, allocator_ptr, endpoint_ptr); page_ptr_roundtrip();
        };
        assert(krnl.ep_mp.spec_index(endpoint_ptr).view().queue.view() == Seq::<RwLockThreadPtr>::empty()) by {
            let queue = krnl.ep_mp.spec_index(endpoint_ptr).view().queue.view();
            if queue.len() > 0 {
                let waiter = queue[0];
                thread_endpoint_queue_wf_endpoint_at(krnl.thr_mp, krnl.ep_mp, endpoint_ptr, waiter);
                thread_perms_wf_at(krnl.thr_mp, waiter);
                thread_endpoint_ref_counter_wf_thread_at(krnl.thr_mp, krnl.ep_mp, waiter, krnl.thr_mp.spec_index(waiter).view().blocking_endpoint_index.unwrap());
            }
        };
        lctx.enter_kernel_view_release();
    }
    let Tracked(page_perm) = krnl.remove_endpoint_and_reclaim_4k_page_perm(endpoint_ptr, Tracked(endpoint_lock_perm), Tracked(&mut *lctx));
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
    let (node_addr, node_perm) = page_array_retire_kernel_object_4k_to_cache(&mut krnl.pg_arr, page_index, Tracked(page_perm), allocator_ptr, cpu_id, Tracked(&*lctx), Tracked(&page_lock_perm));
    proof { lctx.update_lock_id(KernelObjId::Page(page_index), old_page_lock_id, krnl.pg_arr.lock_id_by_index(page_index)); }
    page_array_move_free_4k_to_global_list(&mut krnl.pg_arr, page_index, allocator_ptr, cpu_id, Tracked(&*lctx), Tracked(&page_lock_perm));
    krnl.allc_4k_mp.push_global_pool_page_typed(allocator_ptr, node_addr, node_perm, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
        Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(&pool_lock_perm));
    {
        let quota = krnl.allc_4k_mp.borrow_mut_quota_typed(allocator_ptr, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
            Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(&quota_lock_perm));
        quota.value = quota.value + 1;
    }
    {
        let thread_mut = krnl.thr_mp.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(thread_lock_perm));
        thread_mut.endpoint_descriptors.set(index, None);
    }
    proof { remove_endpoint_from_container_set(&mut krnl.ctn_mp, endpoint_owner, endpoint_ptr, lctx.container_lock_map(), lctx.thread_id()); }
    let ghost mid = *krnl;
    proof {
        assert(typed_lock_maps_aligned(krnl, lctx) && krnl.thr_mp.lock_id_by_key(thread_ptr) == entry.thr_mp.lock_id_by_key(thread_ptr)) by {
            lock_id_fields_eq_imply_eq(); reveal(LockedMap::typed_lock_map_aligned);
        };
        assert(release_endpoint_eof_transition_framing(entry, mid, thread_ptr, endpoint_ptr, index, allocator_ptr, node_addr)) by { reveal(release_endpoint_eof_transition_framing); };
        release_endpoint_eof(entry, mid, thread_ptr, endpoint_ptr, index, owner, allocator_ptr, node_addr);
    }
    krnl.wunlock_allocator_quota_4k(allocator_ptr, Tracked(&mut *lctx), Tracked(quota_lock_perm));
    krnl.wunlock_allocator_global_pool_4k(allocator_ptr, Tracked(&mut *lctx), Tracked(pool_lock_perm));
    krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_lock_perm));
    proof {
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&mid, &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        release_endpoint_eof_fields(*old(krnl), entry, mid, *krnl, thread_ptr, endpoint_ptr, index, owner, allocator_ptr, node_addr);
        assert(lctx.page_lock_map() =~= old(lctx).page_lock_map());
        assert(lctx.allocator_quota_4k_lock_map() =~= old(lctx).allocator_quota_4k_lock_map());
        assert(lctx.allocator_global_pool_4k_lock_map() =~= old(lctx).allocator_global_pool_4k_lock_map());
    }
}
} // verus!
