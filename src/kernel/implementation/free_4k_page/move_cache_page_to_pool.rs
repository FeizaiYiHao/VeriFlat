use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::move_cache_page_to_pool_eof::{move_cache_page_to_pool_eof, move_cache_page_to_pool_eof_transition_framing};

verus! {
pub fn move_cache_page_to_pool(krnl: &mut KernelK, allocator: RwLockPageAllocatorPtr, cpu_id: CpuId, page_ptr: PagePtr, Tracked(lctx): Tracked<&mut LocalContext>, cache_perm: Tracked<&LockPerm>, pool_perm: Tracked<&LockPerm>, page_perm: Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).allc_4k_mp.dom().contains(allocator),
        index_valid(NUM_CPUS, cpu_id),
        page_ptr_valid(page_ptr),
        old(krnl).allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().view().view().len() > 0,
        old(krnl).allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().view().view().spec_index(0) == page_ptr,
        typed_lock_map_contains_mode(old(lctx).allocator_cache_4k_lock_map(), (allocator, cpu_id), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).allocator_global_pool_4k_lock_map(), allocator, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        cache_perm.view().state() is WriteLock,
        cache_perm.view().thread_id() == old(lctx).thread_id(),
        cache_perm.view().lock_id() == old(krnl).allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        pool_perm.view().state() is WriteLock,
        pool_perm.view().thread_id() == old(lctx).thread_id(),
        pool_perm.view().lock_id() == old(krnl).allc_4k_mp.spec_index(allocator).global_pool.locking_thread()->Write_lock_id,
        page_perm.view().state() is WriteLock,
        page_perm.view().thread_id() == old(lctx).thread_id(),
        page_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, allc_4k_mp: final(krnl).allc_4k_mp, ..*old(krnl) }),
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(page_ptr)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view() == (Page { state: PageState::Free4k { allocator_ptr: Ghost(allocator), state: FreePageAllocatorState::GlobalList }, ..old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view() }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread(),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed(),
        final(krnl).allc_4k_mp.unchanged_except(&old(krnl).allc_4k_mp, allocator),
        final(krnl).allc_4k_mp.spec_index(allocator).total_free_pages == old(krnl).allc_4k_mp.spec_index(allocator).total_free_pages,
        final(krnl).allc_4k_mp.spec_index(allocator).quota == old(krnl).allc_4k_mp.spec_index(allocator).quota,
        final(krnl).allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().view().view() == old(krnl).allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().view().view().skip(1),
        final(krnl).allc_4k_mp.spec_index(allocator).global_pool.view().view() == old(krnl).allc_4k_mp.spec_index(allocator).global_pool.view().view().insert(0, page_ptr),
        final(krnl).allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().locking_thread() == old(krnl).allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().locking_thread(),
        final(krnl).allc_4k_mp.spec_index(allocator).global_pool.locking_thread() == old(krnl).allc_4k_mp.spec_index(allocator).global_pool.locking_thread(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
{
    let page_index = page_ptr2page_index(page_ptr);
    assert(index_valid(NUM_PAGES, page_index) && krnl.pg_arr.inv() && krnl.pg_arr.spec_index(page_index).view().inv() && krnl.allc_4k_mp.perms_wf() && krnl.allc_4k_mp.spec_index(allocator).wf()) by {
        page_ptr_valid_imply_page_index_valid(); page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, page_index); allocator_perms_wf_map(krnl.allc_4k_mp); allocator_perms_wf_at(krnl.allc_4k_mp, allocator);
    };
    assert(krnl.pg_arr.spec_index(page_index).view().view().state == (PageState::Free4k { allocator_ptr: Ghost(allocator), state: FreePageAllocatorState::PreCpuCache { cpu_id } })
        && !krnl.allc_4k_mp.spec_index(allocator).global_pool.view().view().contains(page_ptr)) by {
        container_allocator_free_4k_page_wf_cache_at(krnl.allc_4k_mp, krnl.pg_arr, allocator, cpu_id, page_ptr); container_allocator_free_4k_page_wf_global_at(krnl.allc_4k_mp, krnl.pg_arr, allocator, page_ptr);
    };
    let (node_addr, Tracked(node_perm)) = krnl.allc_4k_mp.pop_cache_page_typed(allocator, cpu_id, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()), Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), cache_perm);
    assert(node_addr == krnl.pg_arr.spec_index(page_index).view().view().free_list_node_storage.addr()) by {
        container_allocator_free_4k_page_wf_at(old(krnl).allc_4k_mp, old(krnl).pg_arr, page_index);
        old(krnl).allc_4k_mp.spec_index(allocator).cpu_caches.spec_index(cpu_id).view().view().linked_list.lemma_value_addr_unique(node_addr, krnl.pg_arr.spec_index(page_index).view().view().free_list_node_storage.addr());
    };
    krnl.allc_4k_mp.push_global_pool_page_typed(allocator, node_addr, Tracked(node_perm), Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()), Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), pool_perm);
    page_array_move_free_4k_to_global_list(&mut krnl.pg_arr, page_index, allocator, cpu_id, Tracked(&*lctx), page_perm);
    proof {
        assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), krnl)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
        lctx.enter_kernel_view_release();
        assert(move_cache_page_to_pool_eof_transition_framing(*old(krnl), *krnl, allocator, cpu_id, page_ptr, node_addr)) by { reveal(move_cache_page_to_pool_eof_transition_framing); };
        move_cache_page_to_pool_eof(*old(krnl), *krnl, allocator, cpu_id, page_ptr, node_addr);
    }
}
}
