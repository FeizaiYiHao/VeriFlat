use vstd::prelude::*;
use vstd::assert_seqs_equal;
use crate::*;
verus! {
/// Consume a staged page to create a scheduled thread in `process_ptr`.
pub fn create_thread_from_staged_page_merged(
    krnl: &mut KernelK, page_ptr: PagePtr, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, scheduler_ptr: RwLockSchedulerPtr, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(page_lock_perm): Tracked<&LockPerm>, Tracked(process_lock_perm): Tracked<&LockPerm>,
    Tracked(staging_thread_lock_perm): Tracked<&LockPerm>, Tracked(scheduler_lock_perm): Tracked<&LockPerm>, initial_regs: &Registers,
) -> (ret: (RwLockThreadPtr, Tracked<LockPerm>))
    requires
        old(krnl).inv(),
        page_ptr_valid(page_ptr),
        old(krnl).prc_mp.dom().contains(process_ptr),
        !old(krnl).prc_mp.spec_index(process_ptr).view().zombie,
        old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        old(krnl).thr_mp.dom().contains(staging_thread_ptr),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
        old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        process_lock_perm.state() is WriteLock,
        process_lock_perm.thread_id() == old(lctx).thread_id(),
        process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        old(krnl).sched_mp.dom().contains(scheduler_ptr),
        old(krnl).sched_mp.spec_index(scheduler_ptr).being_killed() == false,
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), scheduler_ptr, TypedLockMode::Write),
        scheduler_lock_perm.state() is WriteLock,
        scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
        scheduler_lock_perm.lock_id() == old(krnl).sched_mp.spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
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
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == container_ptr,
        page_lock_perm.state() is WriteLock,
        page_lock_perm.thread_id() == old(lctx).thread_id(),
        page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        ret.0 == page_ptr,
        ret.0 != staging_thread_ptr,
        ret.1.view().state() is WriteLock,
        ret.1.view().thread_id() == final(lctx).thread_id(),
        ret.1.view().lock_id() == final(krnl).thr_mp.spec_index(page_ptr).locking_thread()->Write_lock_id,
        final(krnl).thr_mp.spec_index(page_ptr).is_init(),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), page_ptr, TypedLockMode::Write),
        final(krnl).thr_mp.dom() =~= old(krnl).thr_mp.dom().insert(page_ptr),
        forall|t: RwLockThreadPtr| #![trigger final(krnl).thr_mp.spec_index(t)]
            old(krnl).thr_mp.dom().contains(t) && t != staging_thread_ptr ==> final(krnl).thr_mp.spec_index(t) == old(krnl).thr_mp.spec_index(t),
        final(krnl).thr_mp.spec_index(page_ptr).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(page_ptr).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(page_ptr).view().syscall_progress.view() is None,
        final(krnl).thr_mp.spec_index(page_ptr).view().state is SCHEDULED,
        final(krnl).thr_mp.spec_index(page_ptr).view().trap_frame.is_some(),
        *final(krnl).thr_mp.spec_index(page_ptr).view().trap_frame.get_some_0() == *initial_regs,
        final(krnl).thr_mp.spec_index(page_ptr).view().owning_container == container_ptr,
        final(krnl).thr_mp.spec_index(page_ptr).view().owning_proc == process_ptr,
        final(krnl).thr_mp.spec_index(page_ptr).view().endpoint_descriptors.spec_index(0) is None,
        final(krnl).thr_mp.spec_index(page_ptr).view().endpoint_descriptors.wf(),
        final(krnl).thr_mp.spec_index(page_ptr).being_killed() == false,
        final(krnl).prc_mp.dom().contains(process_ptr),
        final(krnl).prc_mp.dom() == old(krnl).prc_mp.dom(),
        final(krnl).prc_mp.spec_index(process_ptr).view_rodata() == old(krnl).prc_mp.spec_index(process_ptr).view_rodata(),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        final(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
        final(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view() == old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().push(page_ptr),
        final(krnl).prc_mp.spec_index(process_ptr).view().quota_4k == old(krnl).prc_mp.spec_index(process_ptr).view().quota_4k,
        forall|p: RwLockProcessPtr|
            #![trigger final(krnl).prc_mp.spec_index(p).locking_thread()]
            old(krnl).prc_mp.dom().contains(p) && p != process_ptr ==> final(krnl).prc_mp.spec_index(p).locking_thread() == old(krnl).prc_mp.spec_index(p).locking_thread(),
        forall|p: RwLockProcessPtr|
            #![trigger final(krnl).prc_mp.spec_index(p).being_killed()]
            old(krnl).prc_mp.dom().contains(p) && p != process_ptr ==> final(krnl).prc_mp.spec_index(p).being_killed() == old(krnl).prc_mp.spec_index(p).being_killed(),
        forall|p: RwLockProcessPtr|
            #![trigger final(krnl).prc_mp.spec_index(p).view().owned_threads]
            old(krnl).prc_mp.dom().contains(p) && p != process_ptr ==> final(krnl).prc_mp.spec_index(p).view().owned_threads == old(krnl).prc_mp.spec_index(p).view().owned_threads,
        final(krnl).thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(staging_thread_ptr).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(staging_thread_ptr).view().syscall_progress == old(krnl).thr_mp.spec_index(staging_thread_ptr).view().syscall_progress,
        final(krnl).thr_mp.spec_index(staging_thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(staging_thread_ptr).view().quota_4k - 1,
        final(krnl).thr_mp.spec_index(staging_thread_ptr).view().state == old(krnl).thr_mp.spec_index(staging_thread_ptr).view().state,
        final(krnl).thr_mp.dom().contains(staging_thread_ptr),
        final(krnl).thr_mp.spec_index(staging_thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(staging_thread_ptr).being_killed(),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), staging_thread_ptr, TypedLockMode::Write),
        staging_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(staging_thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).thr_mp.lock_id_by_key(staging_thread_ptr) == old(krnl).thr_mp.lock_id_by_key(staging_thread_ptr),
        kernel_new_thread_fields(old(krnl), final(krnl), process_ptr, staging_thread_ptr, container_ptr, page_ptr, *initial_regs, None,
            old(krnl).thr_mp.spec_index(staging_thread_ptr).view().syscall_progress.view()),
        process_lock_perm.lock_id() == final(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        final(krnl).prc_mp.lock_id_by_key(process_ptr) == old(krnl).prc_mp.lock_id_by_key(process_ptr),
        final(krnl).sched_mp.dom().contains(scheduler_ptr),
        typed_lock_map_contains_mode(final(lctx).scheduler_lock_map(), scheduler_ptr, TypedLockMode::Write),
        final(krnl).sched_mp.spec_index(scheduler_ptr).being_killed() == false,
        scheduler_lock_perm.lock_id() == final(krnl).sched_mp.spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
        final(krnl).sched_mp.lock_id_by_key(scheduler_ptr) == old(krnl).sched_mp.lock_id_by_key(scheduler_ptr),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed() == false,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(page_ptr)),
        final(lctx).page_lock_map() == old(lctx).page_lock_map().insert(page_ptr2page_index(page_ptr), TypedHeldLock {
            lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write,
        }),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map().insert(page_ptr, TypedHeldLock {
            lock_id: final(krnl).thr_mp.lock_id_by_key(page_ptr), mode: TypedLockMode::Write,
        }),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        *final(krnl) == (KernelK {
            pg_arr: final(krnl).pg_arr,
            ctn_mp: final(krnl).ctn_mp,
            sched_mp: final(krnl).sched_mp,
            prc_mp: final(krnl).prc_mp,
            thr_mp: final(krnl).thr_mp,
            ..*old(krnl)
        }),
        final(krnl).ctn_mp.dom() == old(krnl).ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(c)]
            old(krnl).ctn_mp.dom().contains(c) ==> {
                &&& final(krnl).ctn_mp.spec_index(c).view() == old(krnl).ctn_mp.spec_index(c).view()
                &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
                &&& final(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
                &&& final(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
                &&& final(krnl).ctn_mp.spec_index(c).view_ghost().owned_threads.view()
                    == if c == container_ptr { old(krnl).ctn_mp.spec_index(c).view_ghost().owned_threads.view().insert(page_ptr) }
                        else { old(krnl).ctn_mp.spec_index(c).view_ghost().owned_threads.view() }
                &&& final(krnl).ctn_mp.spec_index(c).being_killed() == old(krnl).ctn_mp.spec_index(c).being_killed()
            },
        final(krnl).ctn_mp.spec_index(container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata(),
        final(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes,
        forall|c: RwLockContainerPtr|
            #![trigger final(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes]
            old(krnl).ctn_mp.dom().contains(c) ==> final(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes,
        forall|c: RwLockContainerPtr|
            #![trigger final(krnl).ctn_mp.spec_index(c).being_killed()]
            old(krnl).ctn_mp.dom().contains(c) ==> final(krnl).ctn_mp.spec_index(c).being_killed() == old(krnl).ctn_mp.spec_index(c).being_killed(),
        forall|c: RwLockContainerPtr|
            #![trigger final(krnl).ctn_mp.spec_index(c).locking_thread()]
            old(krnl).ctn_mp.dom().contains(c) ==> final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread(),
        forall|c_ptr: RwLockContainerPtr|
            #![trigger final(krnl).ctn_mp.spec_index(c_ptr).view_ghost().subtree_set]
            old(krnl).ctn_mp.dom().contains(c_ptr) ==> final(krnl).ctn_mp.spec_index(c_ptr).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c_ptr).view_ghost().subtree_set,
        forall|c_ptr: RwLockContainerPtr|
            #![trigger final(krnl).ctn_mp.spec_index(c_ptr).view_ghost().uppertree_seq]
            old(krnl).ctn_mp.dom().contains(c_ptr) ==> final(krnl).ctn_mp.spec_index(c_ptr).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c_ptr).view_ghost().uppertree_seq,
{
    let ghost uppers = krnl.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view();
    proof {
        process_perms_wf_at(krnl.prc_mp, process_ptr);
        container_perms_wf_at(krnl.ctn_mp, container_ptr);
        scheduler_perms_wf_at(krnl.sched_mp, scheduler_ptr);
        thread_perms_wf_at(krnl.thr_mp, staging_thread_ptr);
        assert(krnl.sched_mp.spec_index(scheduler_ptr).view().owning_container == container_ptr) by { reveal(container_scheduler_wf); };
        assert(krnl.prc_mp.spec_index(process_ptr).view_rodata().view().container_depth == krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().depth) by { reveal(container_process_wf); };
        assert(krnl.prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == krnl.prc_mp.spec_index(process_ptr).view().pagetable) by { reveal(process_pagetable_match); };
        assert(!krnl.thr_mp.dom().contains(page_ptr)) by { reveal(thread_pages_wf); };
        assert(page_ptr != staging_thread_ptr) by { reveal(thread_pages_wf); };
        assert(uppers.to_set().subset_of(krnl.ctn_mp.dom()) && !uppers.to_set().contains(container_ptr)) by {
            uppers.to_set_ensures();
            reveal(container_uppertree_seq_wf);
        };
        assert({
            &&& krnl.prc_mp.spec_index(process_ptr).view().owned_threads.view().len() < usize::MAX
            &&& !krnl.prc_mp.spec_index(process_ptr).view().owned_threads.view().contains(page_ptr)
        }) by {
            let threads = krnl.prc_mp.spec_index(process_ptr).view().owned_threads.view();
            reveal(process_thread_wf);
            lemma_kernel_object_ptr_seq_len_bounded(&*krnl, threads);
        };
        assert({
            &&& !krnl.sched_mp.spec_index(scheduler_ptr).view().queue.view().contains(page_ptr)
            &&& krnl.sched_mp.spec_index(scheduler_ptr).view().queue.length != usize::MAX
        }) by {
            reveal(container_thread_scheduler_wf);
            scheduler_queue_len_bounded(&*krnl, scheduler_ptr);
            assert(NUM_PAGES < usize::MAX) by (compute);
        };
        let page_index = page_ptr2page_index(page_ptr);
        assert(index_valid(NUM_PAGES, page_index)) by { page_ptr_valid_imply_page_index_valid(); };
        page_array_wf_at(krnl.pg_arr, page_index);
        assert(krnl.pg_arr.spec_index(page_index).view().view().perm_4k.view().is_some()
            && krnl.pg_arr.spec_index(page_index).view().view().addr == page_ptr) by { page_ptr_roundtrip(); };
    }
    let container_rodata = krnl.ctn_mp.borrow_rodata(container_ptr);
    let container_ro = container_rodata.borrow();
    let container_depth = container_ro.depth;
    let process_rodata = krnl.prc_mp.borrow_rodata(process_ptr);
    let process_ro = process_rodata.borrow();
    let process_depth = process_ro.depth;
    let proc_pagetable = process_ro.pagetable;
    let (thread_value, sched_node_addr, sched_node_perm, node_addr, node_perm) = Thread::new_scheduled(
        page_ptr, container_ptr, container_depth, process_ptr, process_depth, proc_pagetable, Ghost(uppers), initial_regs,
    );
    let page_index = page_ptr2page_index(page_ptr);
    let Tracked(page_perm) = page_array_retype_owned_4k(
        &mut krnl.pg_arr, page_index, PageState::Allocated4k { state: Allocated4KPageState::AsThread },
        Tracked(&mut *lctx), Tracked(page_lock_perm),
    );
    let Tracked(thread_perm) = process_subsystem_create_scheduled_thread(
        &krnl.ctn_mp, &mut krnl.prc_mp, &mut krnl.thr_mp, &mut krnl.sched_mp, page_ptr, process_ptr,
        staging_thread_ptr, container_ptr, scheduler_ptr, thread_value, sched_node_addr, sched_node_perm,
        node_addr, node_perm, Tracked(page_perm), Tracked(&mut *lctx), Tracked(process_lock_perm),
        Tracked(staging_thread_lock_perm), Tracked(scheduler_lock_perm),
    );
    proof {
        add_thread_to_container_sets(
            &mut krnl.ctn_mp, container_ptr, page_ptr, uppers, krnl.thr_mp, krnl.sched_mp,
            lctx.container_lock_map(), lctx.thread_id(),
        );
        assert(create_thread_from_staged_page_kernel_state_framing(
            *old(krnl), *krnl, page_ptr, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, node_addr, sched_node_addr,
        )) by { reveal(create_thread_from_staged_page_kernel_state_framing); reveal(process_subsystem_create_scheduled_thread_transition_framing); };
        eof_create_thread_inv(
            *old(krnl), *krnl, page_ptr, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, node_addr, sched_node_addr,
        );
    }
    proof {
        assert_seqs_equal!(
            Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat, |i: int| None::<RwLockEndpointPtr>)
                == Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat, |i: int| if i == 0 { None } else { None }),
            i => {}
        );
        assert(kernel_new_thread_fields(
            old(krnl), krnl, process_ptr, staging_thread_ptr, container_ptr, page_ptr, *initial_regs, None,
            old(krnl).thr_mp.spec_index(staging_thread_ptr).view().syscall_progress.view(),
        )) by { reveal(kernel_new_thread_fields); reveal(container_scheduler_wf); };
    }
    (page_ptr, Tracked(thread_perm))
}

/// Complete kernel-state summary of `create_thread_from_staged_page_merged`.
#[verifier::opaque]
pub open spec fn create_thread_from_staged_page_kernel_state_framing(
    pre: KernelK, post: KernelK, page_ptr: PagePtr, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, scheduler_ptr: RwLockSchedulerPtr, process_node_addr: usize, sched_node_addr: usize,
) -> bool {
    let page_index = page_ptr2page_index(page_ptr);
    let uppers = pre.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view();
    let pre_page = pre.pg_arr.spec_index(page_index).view();
    let post_page = post.pg_arr.spec_index(page_index).view();
    let pre_process = pre.prc_mp.spec_index(process_ptr);
    let post_process = post.prc_mp.spec_index(process_ptr);
    let pre_staging = pre.thr_mp.spec_index(staging_thread_ptr);
    let post_staging = post.thr_mp.spec_index(staging_thread_ptr);
    let pre_scheduler = pre.sched_mp.spec_index(scheduler_ptr);
    let post_scheduler = post.sched_mp.spec_index(scheduler_ptr);
    let thread = post.thr_mp.spec_index(page_ptr).view();
    &&& post == (KernelK { pg_arr: post.pg_arr, ctn_mp: post.ctn_mp, sched_mp: post.sched_mp, prc_mp: post.prc_mp, thr_mp: post.thr_mp, ..pre })
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_index)
    &&& post_page.view() == (Page {
        state: PageState::Allocated4k { state: Allocated4KPageState::AsThread }, perm_4k: post_page.view().perm_4k, ..pre_page.view()
    })
    &&& post_page.view().perm_4k.view().is_none()
    &&& post_page.view_rodata() == pre_page.view_rodata()
    &&& post_page.view_ghost() == pre_page.view_ghost()
    &&& post_page.locking_thread() == pre_page.locking_thread()
    &&& post_page.being_killed() == pre_page.being_killed()
    &&& post.ctn_mp.dom() == pre.ctn_mp.dom()
    &&& forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)]
        pre.ctn_mp.dom().contains(c) ==> {
            let pre_ghost = pre.ctn_mp.spec_index(c).view_ghost();
            &&& post.ctn_mp.spec_index(c).view() == pre.ctn_mp.spec_index(c).view()
            &&& post.ctn_mp.spec_index(c).view_rodata() == pre.ctn_mp.spec_index(c).view_rodata()
            &&& post.ctn_mp.spec_index(c).locking_thread() == pre.ctn_mp.spec_index(c).locking_thread()
            &&& post.ctn_mp.spec_index(c).being_killed() == pre.ctn_mp.spec_index(c).being_killed()
            &&& post.ctn_mp.spec_index(c).view_ghost() == (ContainerGhost {
                uppertree_seq: pre_ghost.uppertree_seq, subtree_set: pre_ghost.subtree_set, owned_processes: pre_ghost.owned_processes,
                owned_threads: if c == container_ptr { Ghost(pre_ghost.owned_threads.view().insert(page_ptr)) } else { pre_ghost.owned_threads },
                owned_indirect_threads: if uppers.to_set().contains(c) {
                    Ghost(pre_ghost.owned_indirect_threads.view().insert(page_ptr))
                } else { pre_ghost.owned_indirect_threads },
            })
        }
    &&& post.prc_mp.dom() == pre.prc_mp.dom()
    &&& post.prc_mp.unchanged_except(&pre.prc_mp, process_ptr)
    &&& forall|p: RwLockProcessPtr, f: PciBdf| #![trigger post.prc_mp.spec_index(p).view().owned_pci_functions.view().contains(f)]
        pre.prc_mp.dom().contains(p) ==> post.prc_mp.spec_index(p).view().owned_pci_functions.view().contains(f) == pre.prc_mp.spec_index(p).view().owned_pci_functions.view().contains(f)
    &&& post_process.view() == (Process { owned_threads: post_process.view().owned_threads, ..pre_process.view() })
    &&& post_process.view().owned_threads.view() == pre_process.view().owned_threads.view().push(page_ptr)
    &&& post_process.view().owned_threads.dom() == pre_process.view().owned_threads.dom().insert(process_node_addr)
    &&& post_process.view().owned_threads.map() == pre_process.view().owned_threads.map().insert(process_node_addr, page_ptr)
    &&& !pre_process.view().owned_threads.dom().contains(process_node_addr)
    &&& !pre_process.view().owned_threads.map().dom().contains(process_node_addr)
    &&& post_process.view_rodata() == pre_process.view_rodata()
    &&& post_process.view_ghost() == pre_process.view_ghost()
    &&& post_process.locking_thread() == pre_process.locking_thread()
    &&& post_process.being_killed() == pre_process.being_killed()
    &&& post.thr_mp.dom() =~= pre.thr_mp.dom().insert(page_ptr)
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)]
        pre.thr_mp.dom().contains(t) && t != staging_thread_ptr ==> post.thr_mp.spec_index(t) == pre.thr_mp.spec_index(t)
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)]
        pre.thr_mp.dom().contains(t) ==> post.thr_mp.spec_index(t).view().endpoint_descriptors == pre.thr_mp.spec_index(t).view().endpoint_descriptors
    &&& forall|t: RwLockThreadPtr, p: PagePtr| #![trigger post.thr_mp.spec_index(t).view().temp_alloc_cache_2m.view().contains(p)]
        pre.thr_mp.dom().contains(t) ==> post.thr_mp.spec_index(t).view().temp_alloc_cache_2m.view().contains(p) == pre.thr_mp.spec_index(t).view().temp_alloc_cache_2m.view().contains(p)
    &&& forall|t: RwLockThreadPtr, p: PagePtr| #![trigger post.thr_mp.spec_index(t).view().temp_alloc_cache_1g.view().contains(p)]
        pre.thr_mp.dom().contains(t) ==> post.thr_mp.spec_index(t).view().temp_alloc_cache_1g.view().contains(p) == pre.thr_mp.spec_index(t).view().temp_alloc_cache_1g.view().contains(p)
    &&& post_staging.view() == (Thread {
        quota_4k: post_staging.view().quota_4k, temp_alloc_cache_4k: post_staging.view().temp_alloc_cache_4k, ..pre_staging.view()
    })
    &&& post_staging.view().temp_alloc_cache_4k.view() == pre_staging.view().temp_alloc_cache_4k.view().remove(page_ptr)
    &&& post_staging.view().quota_4k == pre_staging.view().quota_4k - 1
    &&& post_staging.locking_thread() == pre_staging.locking_thread()
    &&& post_staging.being_killed() == pre_staging.being_killed()
    &&& post.thr_mp.spec_index(page_ptr).is_init()
    &&& !post.thr_mp.spec_index(page_ptr).being_killed()
    &&& thread.inv()
    &&& thread.state is SCHEDULED
    &&& thread.owning_container == container_ptr
    &&& thread.container_depth == pre.ctn_mp.spec_index(container_ptr).view_rodata().view().depth
    &&& thread.owning_proc == process_ptr
    &&& thread.process_depth == pre_process.view_rodata().view().depth
    &&& thread.proc_pagetable_ptr == pre_process.view().pagetable
    &&& thread.upper_container_seq.view() == uppers
    &&& thread.caller is None
    &&& thread.callee is None
    &&& thread.scheduler_linkedlist_node.addr() == sched_node_addr
    &&& thread.proc_linkedlist_node.addr() == process_node_addr
    &&& thread.blocking_endpoint_ptr is None
    &&& thread.blocking_endpoint_index is None
    &&& thread.endpoint_descriptors.view() == Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat, |i: int| None::<RwLockEndpointPtr>)
    &&& thread.ipc_payload is Empty
    &&& thread.error_code is None
    &&& thread.free_quota_pending_clean()
    &&& thread.syscall_progress.view() is None
    &&& thread.temp_alloc_clean()
    &&& thread.quota_4k == 0
    &&& thread.quota_2m == 0
    &&& thread.quota_1g == 0
    &&& post.sched_mp.dom() == pre.sched_mp.dom()
    &&& post.sched_mp.unchanged_except(&pre.sched_mp, scheduler_ptr)
    &&& post_scheduler.view() == (Scheduler { queue: post_scheduler.view().queue, ..pre_scheduler.view() })
    &&& post_scheduler.view().queue.view() == pre_scheduler.view().queue.view().push(page_ptr)
    &&& post_scheduler.view().queue.dom() == pre_scheduler.view().queue.dom().insert(sched_node_addr)
    &&& post_scheduler.view().queue.map() == pre_scheduler.view().queue.map().insert(sched_node_addr, page_ptr)
    &&& !pre_scheduler.view().queue.dom().contains(sched_node_addr)
    &&& !pre_scheduler.view().queue.map().dom().contains(sched_node_addr)
    &&& post_scheduler.locking_thread() == pre_scheduler.locking_thread()
    &&& post_scheduler.being_killed() == pre_scheduler.being_killed()
}

#[verifier::spinoff_prover]
proof fn eof_create_thread_memory_management_inv(
    pre: KernelK, post: KernelK, page_ptr: PagePtr, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, scheduler_ptr: RwLockSchedulerPtr, process_node_addr: usize, sched_node_addr: usize,
)
    requires
        pre.inv(),
        page_ptr_valid(page_ptr),
        pre.prc_mp.dom().contains(process_ptr),
        !pre.prc_mp.spec_index(process_ptr).view().zombie,
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        pre.thr_mp.dom().contains(staging_thread_ptr),
        !pre.thr_mp.dom().contains(page_ptr),
        page_ptr != staging_thread_ptr,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
        pre.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view().to_set().subset_of(pre.ctn_mp.dom()),
        pre.sched_mp.dom().contains(scheduler_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= Set::<PagePtr>::empty().insert(page_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_2m.view().len() == 0,
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_1g.view().len() == 0,
        pre.thr_mp.spec_index(staging_thread_ptr).view().free_quota_pending_clean(),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == container_ptr,
        create_thread_from_staged_page_kernel_state_framing(
            pre, post, page_ptr, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, process_node_addr, sched_node_addr,
        ),
        page_array_wf(post.pg_arr),
        container_perms_wf(post.ctn_mp),
        process_perms_wf(post.prc_mp),
        thread_perms_wf(post.thr_mp),
        scheduler_perms_wf(post.sched_mp),
        process_thread_wf(post.prc_mp, post.thr_mp),
        container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp),
    ensures
        post.memory_management_inv(),
{
    reveal(create_thread_from_staged_page_kernel_state_framing);
    let page_index = page_ptr2page_index(page_ptr);
    assert(index_valid(NUM_PAGES, page_index)) by { page_ptr_valid_imply_page_index_valid(); };
    assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        allocator_4k_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_4k_mp, post.allc_4k_mp);
        allocator_2m_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_2m_mp, post.allc_2m_mp);
        allocator_1g_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_1g_mp, post.allc_1g_mp);
    };
    assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by {
        container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr);
    };
    assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(page_pagetable_wf(post.pt_mp, post.pg_arr)) by {
        page_pagetable_wf_preserved_for_nonmapped_page_change(pre.pt_mp, post.pt_mp, pre.pg_arr, post.pg_arr, page_index);
    };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.ctn_mp, post.ctn_mp); };
    assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { process_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.prc_mp, post.prc_mp); };
    assert(pagetable_pages_wf(post.pt_mp, post.pg_arr)) by { reveal(pagetable_pages_wf); };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { reveal(iommu_table_pages_wf); };
    assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_pages_wf); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by {
        scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr);
    };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
    assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by { reveal(pcid_allocator_pages_wf); };
    assert(thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_4k_wf); };
    assert(thread_staged_pages_2m_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_2m_wf); };
    assert(thread_staged_pages_1g_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_1g_wf); };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
    assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { lemma_process_pagetable_match_preserved_for_process_pagetable_fields_forall(); };
    assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by { lemma_process_iommu_table_match_preserved_for_process_iommu_table_fields_forall(); };
    assert(container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        pre.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view().to_set_ensures();
        lemma_container_process_thread_quota_folds_insert_zero_forall(
            pre.rt_ctn, pre.ctn_mp, post.ctn_mp, pre.prc_mp, post.prc_mp, pre.thr_mp, post.thr_mp, container_ptr, page_ptr,
        );
        assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp)) by {
            reveal(container_process_allocator_quota_4k_wf);
        };
        assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_2m_mp)) by {
            reveal(container_process_allocator_quota_2m_wf);
        };
        assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_1g_mp)) by {
            reveal(container_process_allocator_quota_1g_wf);
        };
    };
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_allocator_wf); };
    assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by {
        container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(post.allc_4k_mp, pre.pg_arr, post.pg_arr, page_index);
    };
    assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by {
        container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, page_index);
    };
    assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by {
        container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, page_index);
    };
}

#[verifier::spinoff_prover]
proof fn eof_create_thread_endpoint_ref_counter_wf(
    pre: KernelK, post: KernelK, page_ptr: PagePtr, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, scheduler_ptr: RwLockSchedulerPtr, process_node_addr: usize, sched_node_addr: usize,
)
    requires
        thread_endpoint_ref_counter_wf(pre.thr_mp, pre.ep_mp),
        create_thread_from_staged_page_kernel_state_framing(
            pre, post, page_ptr, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, process_node_addr, sched_node_addr,
        ),
    ensures
        thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp),
{
    reveal(create_thread_from_staged_page_kernel_state_framing); reveal(thread_endpoint_ref_counter_wf);
}

#[verifier::spinoff_prover]
proof fn eof_create_thread_process_management_inv(
    pre: KernelK, post: KernelK, page_ptr: PagePtr, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, scheduler_ptr: RwLockSchedulerPtr, process_node_addr: usize, sched_node_addr: usize,
)
    requires
        pre.inv(),
        page_ptr_valid(page_ptr),
        pre.prc_mp.dom().contains(process_ptr),
        !pre.prc_mp.spec_index(process_ptr).view().zombie,
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        pre.thr_mp.dom().contains(staging_thread_ptr),
        !pre.thr_mp.dom().contains(page_ptr),
        page_ptr != staging_thread_ptr,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
        pre.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view().to_set().subset_of(pre.ctn_mp.dom()),
        pre.sched_mp.dom().contains(scheduler_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= Set::<PagePtr>::empty().insert(page_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_2m.view().len() == 0,
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_1g.view().len() == 0,
        pre.thr_mp.spec_index(staging_thread_ptr).view().free_quota_pending_clean(),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == container_ptr,
        create_thread_from_staged_page_kernel_state_framing(
            pre, post, page_ptr, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, process_node_addr, sched_node_addr,
        ),
        page_array_wf(post.pg_arr),
        container_perms_wf(post.ctn_mp),
        process_perms_wf(post.prc_mp),
        thread_perms_wf(post.thr_mp),
        scheduler_perms_wf(post.sched_mp),
        process_thread_wf(post.prc_mp, post.thr_mp),
        container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp),
    ensures
        post.process_management_inv(),
{
    reveal(create_thread_from_staged_page_kernel_state_framing);
    assert(container_tree_wf(post.rt_ctn, post.ctn_mp)) by { container_no_change_to_tree_fields_imply_wf(pre.rt_ctn, pre.ctn_mp, post.ctn_mp); };
    assert(post.ctn_mp.spec_index(post.rt_ctn).view_ghost().owned_processes.view().contains(post.ctn_mp.spec_index(post.rt_ctn).view().root_process)) by { reveal(container_root_wf); };
    assert(container_process_wf(post.ctn_mp, pre.prc_mp)) by { reveal(container_process_wf); };
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { lemma_container_process_wf_preserved_for_process_rodata_forall(); };
    assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by {
        assert(per_container_process_tree_wf(post.ctn_mp, pre.prc_mp)) by { reveal(per_container_process_tree_wf); };
        per_container_process_tree_wf_preserved_for_tree_fields_eq(post.ctn_mp, pre.prc_mp, post.prc_mp);
    };
    assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by { reveal(container_endpoint_wf); };
    assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by { reveal(container_cpu_wf); };
    eof_create_thread_endpoint_ref_counter_wf(pre, post, page_ptr, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, process_node_addr, sched_node_addr);
    assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_queue_wf); };
    assert(thread_caller_callee_wf(post.thr_mp)) by { reveal(thread_caller_callee_wf); };
    assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by {
        reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(container_thread_endpoint_wf);
    };
    assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by { reveal(container_scheduler_wf); };
    assert(container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
    assert(container_cpu_offline_flags_wf(post.ctn_mp, post.cpu_offline_mp)) by { reveal(container_cpu_offline_flags_wf); };
    assert(container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp)) by { reveal(container_pcid_allocator_wf); };
    assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { reveal(process_pcid_allocator_wf); };
    assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { reveal(container_thread_wf); pre.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view().to_set_ensures(); };
    assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { lemma_process_cpu_wf_preserved_for_process_pagetable_fields_forall(); };
    assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { reveal(thread_cpu_wf); };
}

#[verifier::spinoff_prover]
proof fn eof_create_thread_inv(
    pre: KernelK, post: KernelK, page_ptr: PagePtr, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, scheduler_ptr: RwLockSchedulerPtr, process_node_addr: usize, sched_node_addr: usize,
)
    requires
        pre.inv(),
        page_ptr_valid(page_ptr),
        pre.prc_mp.dom().contains(process_ptr),
        !pre.prc_mp.spec_index(process_ptr).view().zombie,
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        pre.thr_mp.dom().contains(staging_thread_ptr),
        !pre.thr_mp.dom().contains(page_ptr),
        page_ptr != staging_thread_ptr,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
        pre.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view().to_set().subset_of(pre.ctn_mp.dom()),
        pre.sched_mp.dom().contains(scheduler_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= Set::<PagePtr>::empty().insert(page_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_2m.view().len() == 0,
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_1g.view().len() == 0,
        pre.thr_mp.spec_index(staging_thread_ptr).view().free_quota_pending_clean(),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == container_ptr,
        create_thread_from_staged_page_kernel_state_framing(
            pre, post, page_ptr, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, process_node_addr, sched_node_addr,
        ),
        page_array_wf(post.pg_arr),
        container_perms_wf(post.ctn_mp),
        process_perms_wf(post.prc_mp),
        thread_perms_wf(post.thr_mp),
        scheduler_perms_wf(post.sched_mp),
        process_thread_wf(post.prc_mp, post.thr_mp),
        container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp),
    ensures
        post.inv(),
{
    eof_create_thread_memory_management_inv(pre, post, page_ptr, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, process_node_addr, sched_node_addr);
    eof_create_thread_process_management_inv(pre, post, page_ptr, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, process_node_addr, sched_node_addr);
    reveal(create_thread_from_staged_page_kernel_state_framing);
    assert(post.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
    assert(iommu_root_table_process_wf(&post.irt, post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(process_pci_function_ownership_wf(&post.irt, post.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, &post.irt, post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf_spec); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_dirty_map_proc_pcid_match); reveal(container_cpu_wf);
    };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
}

/// One staging-thread quota funds a new scheduled thread, and the staging thread's progress becomes `staging_progress`.
#[verifier::opaque]
pub open spec fn kernel_u_new_thread_changed(
    old_u: KernelU, new_u: KernelU, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, new_thread_ptr: RwLockThreadPtr,
    initial_regs: Registers, endpoint_ptr: Option<RwLockEndpointPtr>, staging_progress: Option<SyscallProgress>,
) -> bool {
    let old_staging = old_u.thread_map.spec_index(staging_thread_ptr);
    let new_thread = new_u.thread_map.spec_index(new_thread_ptr);
    &&& match endpoint_ptr {
        Some(e) => old_u.endpoint_map.dom().contains(e) && new_u.endpoint_map == old_u.endpoint_map.insert(e, EndpointU {
            owning_threads: old_u.endpoint_map.spec_index(e).owning_threads.insert((new_thread_ptr, 0usize)),
            ..old_u.endpoint_map.spec_index(e)
        }),
        None => new_u.endpoint_map == old_u.endpoint_map,
    }
    &&& new_u.iommu_root_table == old_u.iommu_root_table
    &&& new_u.cpu_tlb == old_u.cpu_tlb
    &&& new_u.iommu_tlb == old_u.iommu_tlb
    &&& new_u.kernel_l4_end == old_u.kernel_l4_end
    &&& new_u.cpu_array == old_u.cpu_array
    &&& old_u.container_map.dom().contains(container_ptr)
    &&& new_u.container_map == old_u.container_map.insert(container_ptr, ContainerU {
        owned_threads: old_u.container_map.spec_index(container_ptr).owned_threads.insert(new_thread_ptr),
        scheduler: old_u.container_map.spec_index(container_ptr).scheduler.push(new_thread_ptr),
        ..old_u.container_map.spec_index(container_ptr)
    })
    &&& old_u.process_map.dom().contains(process_ptr)
    &&& old_u.thread_map.dom().contains(staging_thread_ptr)
    &&& !old_u.thread_map.dom().contains(new_thread_ptr)
    &&& old_staging.quota_4k > 0
    &&& new_thread == (ThreadU {
        lock_state: LockStateU::Unlocked,
        state: ThreadState::SCHEDULED,
        caller: None,
        callee: None,
        owning_container: container_ptr,
        owning_proc: process_ptr,
        quota_4k: 0,
        quota_2m: 0,
        quota_1g: 0,
        endpoint_descriptors: Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat, |i: int| if i == 0 { endpoint_ptr } else { None }),
        blocking_endpoint_ptr: None,
        ipc_payload: IPCPayLoad::Empty,
        error_code: None,
        trap_frame: Some(initial_regs),
        syscall_progress: None,
        killed: false,
    })
    &&& new_u.thread_map == old_u.thread_map.insert(staging_thread_ptr, ThreadU {
        quota_4k: (old_staging.quota_4k as int - 1) as usize, syscall_progress: staging_progress, ..old_staging
    }).insert(new_thread_ptr, new_thread)
    &&& new_u.process_map == old_u.process_map.insert(process_ptr, ProcessU {
        owned_threads: old_u.process_map.spec_index(process_ptr).owned_threads.push(new_thread_ptr), ..old_u.process_map.spec_index(process_ptr)
    })
}
}
