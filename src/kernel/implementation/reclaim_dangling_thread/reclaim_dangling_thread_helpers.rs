use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::reclaim_dangling_thread_spec::reclaim_dangling_thread_eof_transition_framing;
#[cfg(verus_keep_ghost)]
use super::reclaim_dangling_thread_eof::reclaim_dangling_thread_eof;

verus! {
/// With the killed dangling thread `dangling_ptr`, its page `page_index`, and the cache on `cpu_id` and quota of the 4K
/// allocator `allocator_ptr` of the page's owner `owner` write-held, and that cache not full: removes the dangling thread from
/// the thread map and its containers' thread sets, returns its page through the returned free-list node address to the cache,
/// and grows the quota by one. The returned context is the one right after the thread lock is dropped.
pub(super) fn reclaim_dangling_thread_commit(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, dangling_ptr: RwLockThreadPtr, page_index: PageIndex, owner: RwLockContainerPtr,
    allocator_ptr: RwLockPageAllocatorPtr, Tracked(dangling_lock_perm): Tracked<LockPerm>, Tracked(page_lock_perm): Tracked<&LockPerm>, Tracked(cache_lock_perm): Tracked<&LockPerm>,
    Tracked(quota_lock_perm): Tracked<&LockPerm>,
) -> (ret: (usize, Ghost<LocalContext>))
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        page_ptr_valid(dangling_ptr),
        page_index == page_ptr2page_index(dangling_ptr),
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
        old(krnl).pg_arr.spec_index(page_index).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsThread }),
        old(krnl).pg_arr.spec_index(page_index).view().view().owning_container == owner,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_index, TypedLockMode::Write),
        page_lock_perm.state() is WriteLock,
        page_lock_perm.thread_id() == old(lctx).thread_id(),
        page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_index).view().locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(owner),
        old(krnl).ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        old(krnl).allc_4k_mp.perms_wf(),
        old(krnl).allc_4k_mp.dom().contains(allocator_ptr),
        old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().len() < ALLOCATOR_MAX_WATERMARK,
        typed_lock_map_contains_mode(old(lctx).allocator_cache_4k_lock_map(), (allocator_ptr, cpu_id), TypedLockMode::Write),
        cache_lock_perm.state() is WriteLock,
        cache_lock_perm.thread_id() == old(lctx).thread_id(),
        cache_lock_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).allocator_quota_4k_lock_map(), allocator_ptr, TypedLockMode::Write),
        quota_lock_perm.state() is WriteLock,
        quota_lock_perm.thread_id() == old(lctx).thread_id(),
        quota_lock_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_removed(old(lctx), &ret.1.view(), KernelObjId::Thread(dangling_ptr)),
        typed_lock_maps_inserted(&ret.1.view(), final(lctx), KernelObjId::Page(page_index), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write }),
        reclaim_dangling_thread_eof_transition_framing(*old(krnl), *final(krnl), cpu_id, dangling_ptr, owner, allocator_ptr, ret.0),
        *final(krnl) == (KernelK { ctn_mp: final(krnl).ctn_mp, thr_mp: final(krnl).thr_mp, pg_arr: final(krnl).pg_arr, allc_4k_mp: final(krnl).allc_4k_mp, ..*old(krnl) }),
        final(krnl).pg_arr.spec_index(page_index).view().locking_thread() == old(krnl).pg_arr.spec_index(page_index).view().locking_thread(),
        final(krnl).allc_4k_mp.dom().contains(allocator_ptr),
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread(),
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.locking_thread() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.locking_thread(),
        old(krnl).thr_mp.spec_index(dangling_ptr).locking_thread() is Write,
        old(krnl).ctn_mp.dom().contains(old(krnl).thr_mp.spec_index(dangling_ptr).view().owning_container),
        old(krnl).pg_arr.spec_index(page_index).view().view().free_list_node_storage.addr() == ret.0,
        !old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(ret.0),
{
    let ghost entry = *krnl;
    let ghost container_ptr = krnl.thr_mp.spec_index(dangling_ptr).view().owning_container;
    let ghost uppers = krnl.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view();
    proof {
        container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, dangling_ptr); container_perms_wf_map(krnl.ctn_mp); container_perms_wf_at(krnl.ctn_mp, container_ptr);
        assert(uppers.to_set().subset_of(krnl.ctn_mp.dom()) && !uppers.to_set().contains(container_ptr)) by {
            uppers.to_set_ensures(); container_uppertree_seq_in_dom(krnl.rt_ctn, krnl.ctn_mp, container_ptr); container_uppertree_seq_not_self(krnl.rt_ctn, krnl.ctn_mp, container_ptr);
        };
        thread_perms_wf_map(krnl.thr_mp);
        thread_perms_wf_at(krnl.thr_mp, dangling_ptr); page_ptr_valid_imply_page_index_valid(); page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, page_index);
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
    let ghost removed_lctx = *lctx;
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
    let (cache_node_addr, cache_node_perm) = page_array_retire_kernel_object_4k_to_cache(&mut krnl.pg_arr, page_index, Tracked(page_perm), allocator_ptr, cpu_id, Tracked(&*lctx), Tracked(page_lock_perm));
    proof { lctx.update_lock_id(KernelObjId::Page(page_index), old_page_lock_id, krnl.pg_arr.lock_id_by_index(page_index)); }
    krnl.allc_4k_mp.push_cache_page_typed(allocator_ptr, cpu_id, cache_node_addr, cache_node_perm, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
        Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(cache_lock_perm));
    {
        let quota = krnl.allc_4k_mp.borrow_mut_quota_typed(allocator_ptr, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
            Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(quota_lock_perm));
        quota.value = quota.value + 1;
    }
    proof {
        remove_thread_from_container_sets(&mut krnl.ctn_mp, container_ptr, dangling_ptr, uppers, lctx.container_lock_map(), lctx.thread_id());
        assert(reclaim_dangling_thread_eof_transition_framing(entry, *krnl, cpu_id, dangling_ptr, owner, allocator_ptr, cache_node_addr)) by { reveal(reclaim_dangling_thread_eof_transition_framing); };
        reclaim_dangling_thread_eof(entry, *krnl, cpu_id, dangling_ptr, owner, allocator_ptr, cache_node_addr);
    }
    (cache_node_addr, Ghost(removed_lctx))
}
} // verus!
