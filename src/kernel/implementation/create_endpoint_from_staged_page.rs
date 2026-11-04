use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::create_endpoint_from_staged_page_eof::{create_endpoint_from_staged_page_eof_transition_framing, create_endpoint_from_staged_page_eof_inv};
verus! {
/// Consume a staged page to create an empty receive endpoint of `ctn_ptr` held at descriptor
/// `ep_idx` of `staging_thrd_ptr`.
pub fn create_endpoint_from_staged_page(
    krnl: &mut KernelK, pg_ptr: PagePtr, ctn_ptr: RwLockContainerPtr, staging_thrd_ptr: RwLockThreadPtr, ep_idx: EndpointIdx,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(page_lock_perm): Tracked<&LockPerm>, Tracked(container_lock_perm): Tracked<&LockPerm>,
    Tracked(staging_thread_lock_perm): Tracked<&LockPerm>,
) -> (ret: Tracked<LockPerm>)
    requires
        old(krnl).inv(),
        page_ptr_valid(pg_ptr),
        old(krnl).ctn_mp.dom().contains(ctn_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), ctn_ptr, TypedLockMode::Write),
        container_lock_perm.state() is WriteLock,
        container_lock_perm.thread_id() == old(lctx).thread_id(),
        container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(ctn_ptr).locking_thread()->Write_lock_id,
        old(krnl).thrd_mp.dom().contains(staging_thrd_ptr),
        old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().owning_container == ctn_ptr,
        !old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().state.is_endpoint_waiting(),
        !(old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().state is DANGLING),
        edp_idx_valid(ep_idx),
        old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().endpoint_descriptors.view()[ep_idx as int] is None,
        old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().temp_alloc_cache_4k.view() =~= Set::<PagePtr>::empty().insert(pg_ptr),
        old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().temp_alloc_cache_2m.view().len() == 0,
        old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().temp_alloc_cache_1g.view().len() == 0,
        old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().quota_4k >= 1,
        old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().free_quota_pending_clean(),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), staging_thrd_ptr, TypedLockMode::Write),
        staging_thread_lock_perm.state() is WriteLock,
        staging_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        staging_thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(staging_thrd_ptr).locking_thread()->Write_lock_id,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().being_killed() == false,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thrd_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == ctn_ptr,
        page_lock_perm.state() is WriteLock,
        page_lock_perm.thread_id() == old(lctx).thread_id(),
        page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        ret.view().state() is WriteLock,
        ret.view().thread_id() == final(lctx).thread_id(),
        ret.view().lock_id() == final(krnl).ep_mp.spec_index(pg_ptr).locking_thread()->Write_lock_id,
        !old(krnl).ep_mp.dom().contains(pg_ptr),
        final(krnl).ep_mp.dom() =~= old(krnl).ep_mp.dom().insert(pg_ptr),
        forall|e: RwLockEndpointPtr| #![trigger final(krnl).ep_mp.spec_index(e)] old(krnl).ep_mp.dom().contains(e) ==> final(krnl).ep_mp.spec_index(e) == old(krnl).ep_mp.spec_index(e),
        typed_lock_map_contains_mode(final(lctx).endpoint_lock_map(), pg_ptr, TypedLockMode::Write),
        kernel_new_endpoint_fields(old(krnl), final(krnl), ctn_ptr, staging_thrd_ptr, ep_idx, pg_ptr,
            old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().syscall_progress.view()),
        final(krnl).thrd_mp.dom().contains(staging_thrd_ptr),
        final(krnl).thrd_mp.unchanged_except(&old(krnl).thrd_mp, staging_thrd_ptr),
        final(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().temp_alloc_clean(),
        final(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().free_quota_pending_clean(),
        final(krnl).thrd_mp.spec_index(staging_thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().syscall_progress == old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().syscall_progress,
        final(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().state == old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().state,
        final(krnl).thrd_mp.spec_index(staging_thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(staging_thrd_ptr).being_killed(),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), staging_thrd_ptr, TypedLockMode::Write),
        staging_thread_lock_perm.lock_id() == final(krnl).thrd_mp.spec_index(staging_thrd_ptr).locking_thread()->Write_lock_id,
        final(krnl).thrd_mp.lock_id_by_key(staging_thrd_ptr) == old(krnl).thrd_mp.lock_id_by_key(staging_thrd_ptr),
        final(krnl).ctn_mp.unchanged_except(&old(krnl).ctn_mp, ctn_ptr),
        final(krnl).ctn_mp.spec_index(ctn_ptr).being_killed() == old(krnl).ctn_mp.spec_index(ctn_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(ctn_ptr).killer_info() == old(krnl).ctn_mp.spec_index(ctn_ptr).killer_info(),
        final(krnl).ctn_mp.spec_index(ctn_ptr).view() == old(krnl).ctn_mp.spec_index(ctn_ptr).view(),
        final(krnl).ctn_mp.spec_index(ctn_ptr).view_ghost() == (ContainerGhost {
            owned_endpoints: Ghost(old(krnl).ctn_mp.spec_index(ctn_ptr).view_ghost().owned_endpoints.view().insert(pg_ptr)), ..old(krnl).ctn_mp.spec_index(ctn_ptr).view_ghost()
        }),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), ctn_ptr, TypedLockMode::Write),
        container_lock_perm.lock_id() == final(krnl).ctn_mp.spec_index(ctn_ptr).locking_thread()->Write_lock_id,
        final(krnl).ctn_mp.lock_id_by_key(ctn_ptr) == old(krnl).ctn_mp.lock_id_by_key(ctn_ptr),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().being_killed() == false,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write),
        page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id,
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(pg_ptr)),
        final(lctx).page_lock_map() == old(lctx).page_lock_map().insert(page_ptr2page_index(pg_ptr), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(pg_ptr)), mode: TypedLockMode::Write }),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map().insert(pg_ptr, TypedHeldLock { lock_id: final(krnl).ep_mp.lock_id_by_key(pg_ptr), mode: TypedLockMode::Write }),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
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
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, ctn_mp: final(krnl).ctn_mp, thrd_mp: final(krnl).thrd_mp, ep_mp: final(krnl).ep_mp, ..*old(krnl) }),
{
    let pg_idx = page_ptr2page_index(pg_ptr);
    proof {
        assert(krnl.ctn_mp.perms_wf() && krnl.ctn_mp.spec_index(ctn_ptr).inv()) by { container_perms_wf_map(krnl.ctn_mp); container_perms_wf_at(krnl.ctn_mp, ctn_ptr); };
        assert(krnl.ep_mp.perms_wf() && !krnl.ep_mp.dom().contains(pg_ptr)) by { endpoint_perms_wf_map(krnl.ep_mp); endpoint_pages_wf_page_at(krnl.ep_mp, krnl.pg_arr, pg_ptr); };
        assert(krnl.pg_arr.spec_index(pg_idx).view().view().addr == pg_ptr) by { page_array_wf_at(krnl.pg_arr, pg_idx); };
    }
    let ghost page_locks = lctx.page_lock_map();
    let Tracked(page_perm) = page_array_retype_owned_4k(&mut krnl.pg_arr, pg_idx, PageState::Allocated4k { state: Allocated4KPageState::AsEndpoint }, Ghost(page_locks), Tracked(&*lctx), Tracked(page_lock_perm));
    thread_map_consume_staged_4k(&mut krnl.thrd_mp, staging_thrd_ptr, pg_ptr, Tracked(&*lctx), Tracked(staging_thread_lock_perm));
    thread_map_set_endpoint_descriptor(&mut krnl.thrd_mp, staging_thrd_ptr, ep_idx, Some(pg_ptr), Tracked(&*lctx), Tracked(staging_thread_lock_perm));
    proof { insert_endpoint_into_container_set(&mut krnl.ctn_mp, ctn_ptr, pg_ptr, lctx.container_lock_map(), lctx.thread_id()); }
    let endpoint_value = Endpoint::new_held(pg_ptr, ctn_ptr, staging_thrd_ptr, ep_idx);
    let endpoint_lock_perm = endpoint_map_insert_new_4k(&mut krnl.ep_mp, pg_ptr, endpoint_value, Tracked(page_perm), Tracked(&mut *lctx));
    proof {
        lctx.enter_kernel_view_release();
        lctx.update_lock_id(KernelObjId::Page(pg_idx), page_locks.index(pg_idx).lock_id, krnl.pg_arr.lock_id_by_index(pg_idx));
        assert(create_endpoint_from_staged_page_eof_transition_framing(*old(krnl), *krnl, pg_ptr, ctn_ptr, staging_thrd_ptr, ep_idx)) by {
            reveal(create_endpoint_from_staged_page_eof_transition_framing);
        };
        create_endpoint_from_staged_page_eof_inv(*old(krnl), *krnl, pg_ptr, ctn_ptr, staging_thrd_ptr, ep_idx);
        assert(kernel_new_endpoint_fields(old(krnl), krnl, ctn_ptr, staging_thrd_ptr, ep_idx, pg_ptr,
            old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().syscall_progress.view())) by {
            reveal(kernel_new_endpoint_fields); reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged);
        };
    }
    endpoint_lock_perm
}
}
