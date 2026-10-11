use vstd::prelude::*;
use crate::*;
verus! {
/// Consume a staged page to create an empty receive endpoint of `container_ptr` held at descriptor
/// `endpoint_index` of `staging_thread_ptr`.
pub fn create_endpoint_from_staged_page(
    krnl: &mut KernelK, page_ptr: PagePtr, container_ptr: RwLockContainerPtr, staging_thread_ptr: RwLockThreadPtr, endpoint_index: EndpointIdx,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(page_lock_perm): Tracked<&LockPerm>, Tracked(container_lock_perm): Tracked<&LockPerm>,
    Tracked(staging_thread_lock_perm): Tracked<&LockPerm>,
) -> (ret: Tracked<LockPerm>)
    requires
        old(krnl).inv(),
        page_ptr_valid(page_ptr),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        container_lock_perm.state() is WriteLock,
        container_lock_perm.thread_id() == old(lctx).thread_id(),
        container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(staging_thread_ptr),
        old(krnl).thr_mp.spec_index(staging_thread_ptr).view().owning_container == container_ptr,
        !old(krnl).thr_mp.spec_index(staging_thread_ptr).view().state.is_endpoint_waiting(),
        edp_idx_valid(endpoint_index),
        old(krnl).thr_mp.spec_index(staging_thread_ptr).view().endpoint_descriptors.view()[endpoint_index as int] is None,
        old(krnl).thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= Set::<PagePtr>::empty().insert(page_ptr),
        old(krnl).thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_2m.view().len() == 0,
        old(krnl).thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_1g.view().len() == 0,
        old(krnl).thr_mp.spec_index(staging_thread_ptr).view().quota_4k >= 1,
        old(krnl).thr_mp.spec_index(staging_thread_ptr).view().free_quota_pending_clean(),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), staging_thread_ptr, TypedLockMode::Write),
        staging_thread_lock_perm.state() is WriteLock,
        staging_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        staging_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(staging_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed() == false,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        page_lock_perm.state() is WriteLock,
        page_lock_perm.thread_id() == old(lctx).thread_id(),
        page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        ret.view().state() is WriteLock,
        ret.view().thread_id() == final(lctx).thread_id(),
        ret.view().lock_id() == final(krnl).ep_mp.spec_index(page_ptr).locking_thread()->Write_lock_id,
        !old(krnl).ep_mp.dom().contains(page_ptr),
        final(krnl).ep_mp.dom() =~= old(krnl).ep_mp.dom().insert(page_ptr),
        forall|e: RwLockEndpointPtr| #![trigger final(krnl).ep_mp.spec_index(e)] old(krnl).ep_mp.dom().contains(e) ==> final(krnl).ep_mp.spec_index(e) == old(krnl).ep_mp.spec_index(e),
        typed_lock_map_contains_mode(final(lctx).endpoint_lock_map(), page_ptr, TypedLockMode::Write),
        kernel_new_endpoint_fields(old(krnl), final(krnl), container_ptr, staging_thread_ptr, endpoint_index, page_ptr,
            old(krnl).thr_mp.spec_index(staging_thread_ptr).view().syscall_progress.view()),
        final(krnl).thr_mp.dom().contains(staging_thread_ptr),
        final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, staging_thread_ptr),
        final(krnl).thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(staging_thread_ptr).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(staging_thread_ptr).view().syscall_progress == old(krnl).thr_mp.spec_index(staging_thread_ptr).view().syscall_progress,
        final(krnl).thr_mp.spec_index(staging_thread_ptr).view().state == old(krnl).thr_mp.spec_index(staging_thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(staging_thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(staging_thread_ptr).being_killed(),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), staging_thread_ptr, TypedLockMode::Write),
        staging_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(staging_thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).thr_mp.lock_id_by_key(staging_thread_ptr) == old(krnl).thr_mp.lock_id_by_key(staging_thread_ptr),
        final(krnl).ctn_mp.unchanged_except(&old(krnl).ctn_mp, container_ptr),
        final(krnl).ctn_mp.spec_index(container_ptr).being_killed() == old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(container_ptr).view_ghost() == old(krnl).ctn_mp.spec_index(container_ptr).view_ghost(),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        container_lock_perm.lock_id() == final(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        final(krnl).ctn_mp.lock_id_by_key(container_ptr) == old(krnl).ctn_mp.lock_id_by_key(container_ptr),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed() == false,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(page_ptr)),
        final(lctx).page_lock_map() == old(lctx).page_lock_map().insert(page_ptr2page_index(page_ptr), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write }),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map().insert(page_ptr, TypedHeldLock { lock_id: final(krnl).ep_mp.lock_id_by_key(page_ptr), mode: TypedLockMode::Write }),
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
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, ctn_mp: final(krnl).ctn_mp, thr_mp: final(krnl).thr_mp, ep_mp: final(krnl).ep_mp, ..*old(krnl) }),
{
    let page_index = page_ptr2page_index(page_ptr);
    proof {
        assert(krnl.ctn_mp.perms_wf() && krnl.ctn_mp.spec_index(container_ptr).inv()) by { container_perms_wf_at(krnl.ctn_mp, container_ptr); };
        assert(krnl.ep_mp.perms_wf() && !krnl.ep_mp.dom().contains(page_ptr)) by { reveal(endpoint_perms_wf); reveal(endpoint_pages_wf); };
        assert(krnl.pg_arr.spec_index(page_index).view().view().addr == page_ptr) by { page_array_wf_at(krnl.pg_arr, page_index); };
    }
    let Tracked(page_perm) = page_array_retype_owned_4k(&mut krnl.pg_arr, page_index, PageState::Allocated4k { state: Allocated4KPageState::AsEndpoint }, Tracked(&mut *lctx), Tracked(page_lock_perm));
    thread_map_consume_staged_4k(&mut krnl.thr_mp, staging_thread_ptr, page_ptr, Tracked(&*lctx), Tracked(staging_thread_lock_perm));
    thread_map_set_endpoint_descriptor(&mut krnl.thr_mp, staging_thread_ptr, endpoint_index, Some(page_ptr), Tracked(&*lctx), Tracked(staging_thread_lock_perm));
    container_map_add_owned_endpoint(&mut krnl.ctn_mp, container_ptr, page_ptr, Tracked(&*lctx), Tracked(container_lock_perm));
    let endpoint_value = Endpoint::new_held(page_ptr, container_ptr, staging_thread_ptr, endpoint_index);
    let endpoint_lock_perm = endpoint_map_insert_new_4k(&mut krnl.ep_mp, page_ptr, endpoint_value, Tracked(page_perm), Tracked(&mut *lctx));
    proof {
        assert(create_endpoint_from_staged_page_kernel_state_framing(*old(krnl), *krnl, page_ptr, container_ptr, staging_thread_ptr, endpoint_index)) by {
            reveal(create_endpoint_from_staged_page_kernel_state_framing);
        };
        eof_create_endpoint_inv(*old(krnl), *krnl, page_ptr, container_ptr, staging_thread_ptr, endpoint_index);
        assert(kernel_new_endpoint_fields(old(krnl), krnl, container_ptr, staging_thread_ptr, endpoint_index, page_ptr,
            old(krnl).thr_mp.spec_index(staging_thread_ptr).view().syscall_progress.view())) by {
            reveal(kernel_new_endpoint_fields); reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged);
        };
    }
    endpoint_lock_perm
}

/// Complete kernel-state summary of `create_endpoint_from_staged_page`.
#[verifier::opaque]
pub open spec fn create_endpoint_from_staged_page_kernel_state_framing(
    pre: KernelK, post: KernelK, page_ptr: PagePtr, container_ptr: RwLockContainerPtr, staging_thread_ptr: RwLockThreadPtr, endpoint_index: EndpointIdx,
) -> bool {
    let page_index = page_ptr2page_index(page_ptr);
    let pre_page = pre.pg_arr.spec_index(page_index).view();
    let post_page = post.pg_arr.spec_index(page_index).view();
    let pre_container = pre.ctn_mp.spec_index(container_ptr);
    let post_container = post.ctn_mp.spec_index(container_ptr);
    let pre_staging = pre.thr_mp.spec_index(staging_thread_ptr);
    let post_staging = post.thr_mp.spec_index(staging_thread_ptr);
    let endpoint = post.ep_mp.spec_index(page_ptr);
    &&& post == (KernelK { pg_arr: post.pg_arr, ctn_mp: post.ctn_mp, thr_mp: post.thr_mp, ep_mp: post.ep_mp, ..pre })
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_index)
    &&& post_page.view() == (Page { state: PageState::Allocated4k { state: Allocated4KPageState::AsEndpoint }, perm_4k: post_page.view().perm_4k, ..pre_page.view() })
    &&& post_page.view().perm_4k.view().is_none()
    &&& post_page.view_rodata() == pre_page.view_rodata()
    &&& post_page.view_ghost() == pre_page.view_ghost()
    &&& post_page.locking_thread() == pre_page.locking_thread()
    &&& post_page.being_killed() == pre_page.being_killed()
    &&& post.ctn_mp.unchanged_except(&pre.ctn_mp, container_ptr)
    &&& post_container.view() == (Container { owned_endpoints: Ghost(pre_container.view().owned_endpoints.view().insert(page_ptr)), ..pre_container.view() })
    &&& post_container.view_rodata() == pre_container.view_rodata()
    &&& post_container.view_ghost() == pre_container.view_ghost()
    &&& post_container.locking_thread() == pre_container.locking_thread()
    &&& post_container.being_killed() == pre_container.being_killed()
    &&& post.thr_mp.unchanged_except(&pre.thr_mp, staging_thread_ptr)
    &&& post_staging.view() == (Thread {
        quota_4k: post_staging.view().quota_4k, temp_alloc_cache_4k: post_staging.view().temp_alloc_cache_4k,
        endpoint_descriptors: post_staging.view().endpoint_descriptors, ..pre_staging.view()
    })
    &&& post_staging.view().temp_alloc_cache_4k.view() == pre_staging.view().temp_alloc_cache_4k.view().remove(page_ptr)
    &&& post_staging.view().quota_4k == pre_staging.view().quota_4k - 1
    &&& post_staging.view().endpoint_descriptors.view() == pre_staging.view().endpoint_descriptors.view().update(endpoint_index as int, Some(page_ptr))
    &&& post_staging.locking_thread() == pre_staging.locking_thread()
    &&& post_staging.being_killed() == pre_staging.being_killed()
    &&& post.ep_mp.dom() == pre.ep_mp.dom().insert(page_ptr)
    &&& forall|e: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(e)] pre.ep_mp.dom().contains(e) ==> post.ep_mp.spec_index(e) == pre.ep_mp.spec_index(e)
    &&& endpoint.is_init()
    &&& !endpoint.being_killed()
    &&& endpoint.view().queue.view() == Seq::<RwLockThreadPtr>::empty()
    &&& endpoint.view().queue_state == EndpointState::RECEIVE
    &&& endpoint.view().owning_threads.view() == set![(staging_thread_ptr, endpoint_index)]
    &&& endpoint.view().owning_container == container_ptr
}

#[verifier::spinoff_prover]
proof fn eof_create_endpoint_memory_management_inv(
    pre: KernelK, post: KernelK, page_ptr: PagePtr, container_ptr: RwLockContainerPtr, staging_thread_ptr: RwLockThreadPtr, endpoint_index: EndpointIdx,
)
    requires
        pre.inv(),
        page_ptr_valid(page_ptr),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= Set::<PagePtr>::empty().insert(page_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        create_endpoint_from_staged_page_kernel_state_framing(pre, post, page_ptr, container_ptr, staging_thread_ptr, endpoint_index),
        page_array_wf(post.pg_arr),
        container_perms_wf(post.ctn_mp),
        thread_perms_wf(post.thr_mp),
        endpoint_perms_wf(post.ep_mp),
    ensures
        post.memory_management_inv(),
{
    reveal(create_endpoint_from_staged_page_kernel_state_framing);
    let page_index = page_ptr2page_index(page_ptr);
    assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        allocator_4k_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_4k_mp, post.allc_4k_mp);
        allocator_2m_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_2m_mp, post.allc_2m_mp);
        allocator_1g_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_1g_mp, post.allc_1g_mp);
    };
    assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(page_pagetable_wf(post.pt_mp, post.pg_arr)) by { page_pagetable_wf_preserved_for_nonmapped_page_change(pre.pt_mp, post.pt_mp, pre.pg_arr, post.pg_arr, page_index); };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.ctn_mp, post.ctn_mp); };
    assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { process_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.prc_mp, post.prc_mp); };
    assert(pagetable_pages_wf(post.pt_mp, post.pg_arr)) by { reveal(pagetable_pages_wf); };
    assert(pagetable_pages_wf(post.it_mp, post.pg_arr)) by { reveal(pagetable_pages_wf); };
    assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
    assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by { reveal(pcid_allocator_pages_wf); };
    assert(thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_4k_wf); };
    assert(thread_staged_pages_2m_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_2m_wf); };
    assert(thread_staged_pages_1g_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_1g_wf); };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { reveal(endpoint_pages_wf); };
    assert(container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp)) by {
            reveal(container_process_allocator_quota_4k_wf); reveal(container_thread_wf);
            lemma_thread_effective_quota_4k_fold_sum_eq_forall();
            lemma_thread_pending_4k_folds_eq_forall(post.ctn_mp, pre.thr_mp, post.thr_mp);
        };
        assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_2m_mp)) by {
            reveal(container_process_allocator_quota_2m_wf); reveal(container_thread_wf);
            lemma_thread_effective_quota_2m_fold_sum_eq_forall();
            lemma_thread_pending_2m_folds_eq_forall(post.ctn_mp, pre.thr_mp, post.thr_mp);
        };
        assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_1g_mp)) by {
            reveal(container_process_allocator_quota_1g_wf); reveal(container_thread_wf);
            lemma_thread_effective_quota_1g_fold_sum_eq_forall();
            lemma_thread_pending_1g_folds_eq_forall(post.ctn_mp, pre.thr_mp, post.thr_mp);
        };
    };
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_allocator_wf); };
    assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(post.allc_4k_mp, pre.pg_arr, post.pg_arr, page_index); };
    assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, page_index); };
    assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, page_index); };
}

#[verifier::spinoff_prover]
proof fn eof_create_endpoint_ref_counter_wf(
    pre: KernelK, post: KernelK, page_ptr: PagePtr, container_ptr: RwLockContainerPtr, staging_thread_ptr: RwLockThreadPtr, endpoint_index: EndpointIdx,
)
    requires
        thread_endpoint_ref_counter_wf(pre.thr_mp, pre.ep_mp),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().endpoint_descriptors.wf(),
        edp_idx_valid(endpoint_index),
        pre.thr_mp.spec_index(staging_thread_ptr).view().endpoint_descriptors.view()[endpoint_index as int] is None,
        create_endpoint_from_staged_page_kernel_state_framing(pre, post, page_ptr, container_ptr, staging_thread_ptr, endpoint_index),
    ensures
        thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp),
{
    reveal(create_endpoint_from_staged_page_kernel_state_framing); reveal(thread_endpoint_ref_counter_wf);
}

#[verifier::spinoff_prover]
proof fn eof_create_endpoint_process_management_inv(
    pre: KernelK, post: KernelK, page_ptr: PagePtr, container_ptr: RwLockContainerPtr, staging_thread_ptr: RwLockThreadPtr, endpoint_index: EndpointIdx,
)
    requires
        pre.inv(),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().owning_container == container_ptr,
        edp_idx_valid(endpoint_index),
        pre.thr_mp.spec_index(staging_thread_ptr).view().endpoint_descriptors.view()[endpoint_index as int] is None,
        !pre.ep_mp.dom().contains(page_ptr),
        create_endpoint_from_staged_page_kernel_state_framing(pre, post, page_ptr, container_ptr, staging_thread_ptr, endpoint_index),
        container_perms_wf(post.ctn_mp),
        thread_perms_wf(post.thr_mp),
        endpoint_perms_wf(post.ep_mp),
    ensures
        post.process_management_inv(),
{
    reveal(create_endpoint_from_staged_page_kernel_state_framing);
    assert(container_tree_wf(post.rt_ctn, post.ctn_mp)) by { container_no_change_to_tree_fields_imply_wf(pre.rt_ctn, pre.ctn_mp, post.ctn_mp); };
    assert(post.ctn_mp.spec_index(post.rt_ctn).view_ghost().owned_processes.view().contains(post.ctn_mp.spec_index(post.rt_ctn).view().root_process)) by { reveal(container_root_wf); };
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_process_wf); };
    assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by { reveal(per_container_process_tree_wf); };
    assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by { reveal(container_endpoint_wf); };
    assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by { reveal(container_cpu_wf); };
    assert(thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp)) by {
        thread_perms_wf_at(pre.thr_mp, staging_thread_ptr); eof_create_endpoint_ref_counter_wf(pre, post, page_ptr, container_ptr, staging_thread_ptr, endpoint_index);
    };
    assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_queue_wf); };
    assert(thread_caller_callee_wf(post.thr_mp)) by { reveal(thread_caller_callee_wf); };
    assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(container_thread_endpoint_wf); };
    assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by { reveal(container_scheduler_wf); };
    assert(container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
    assert(container_cpu_offline_flags_wf(post.ctn_mp, post.cpu_offline_mp)) by { reveal(container_cpu_offline_flags_wf); };
    assert(container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp)) by { reveal(container_pcid_allocator_wf); };
    assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { reveal(process_pcid_allocator_wf); };
    assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by { reveal(container_thread_wf); reveal(container_thread_scheduler_wf); };
    assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { reveal(container_thread_wf); };
    assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { reveal(process_thread_wf); };
    assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { reveal(thread_cpu_wf); };
}

#[verifier::spinoff_prover]
proof fn eof_create_endpoint_inv(
    pre: KernelK, post: KernelK, page_ptr: PagePtr, container_ptr: RwLockContainerPtr, staging_thread_ptr: RwLockThreadPtr, endpoint_index: EndpointIdx,
)
    requires
        pre.inv(),
        page_ptr_valid(page_ptr),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().owning_container == container_ptr,
        edp_idx_valid(endpoint_index),
        pre.thr_mp.spec_index(staging_thread_ptr).view().endpoint_descriptors.view()[endpoint_index as int] is None,
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= Set::<PagePtr>::empty().insert(page_ptr),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        !pre.ep_mp.dom().contains(page_ptr),
        create_endpoint_from_staged_page_kernel_state_framing(pre, post, page_ptr, container_ptr, staging_thread_ptr, endpoint_index),
        page_array_wf(post.pg_arr),
        container_perms_wf(post.ctn_mp),
        thread_perms_wf(post.thr_mp),
        endpoint_perms_wf(post.ep_mp),
    ensures
        post.inv(),
{
    eof_create_endpoint_memory_management_inv(pre, post, page_ptr, container_ptr, staging_thread_ptr, endpoint_index);
    eof_create_endpoint_process_management_inv(pre, post, page_ptr, container_ptr, staging_thread_ptr, endpoint_index);
    reveal(create_endpoint_from_staged_page_kernel_state_framing);
    assert(post.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(container_cpu_wf);
    };
}
}
