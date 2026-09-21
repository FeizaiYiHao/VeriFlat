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
        lock_id_set_aligned(old(lctx)),
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
        final(krnl).thr_mp.spec_index(page_ptr).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(page_ptr).view().temp_alloc_clean(),
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
        final(krnl).thr_mp.spec_index(staging_thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(staging_thread_ptr).view().quota_4k - 1,
        final(krnl).thr_mp.spec_index(staging_thread_ptr).view().state == old(krnl).thr_mp.spec_index(staging_thread_ptr).view().state,
        final(krnl).thr_mp.dom().contains(staging_thread_ptr),
        final(krnl).thr_mp.spec_index(staging_thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(staging_thread_ptr).being_killed(),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), staging_thread_ptr, TypedLockMode::Write),
        staging_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(staging_thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).thr_mp.lock_id_by_key(staging_thread_ptr) == old(krnl).thr_mp.lock_id_by_key(staging_thread_ptr),
        kernel_u_new_thread_changed(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), process_ptr),
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
        lock_id_set_aligned(final(lctx)),
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
        final(krnl).ctn_mp.spec_index(container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata(),
        final(krnl).ctn_mp.spec_index(container_ptr).view().owned_processes == old(krnl).ctn_mp.spec_index(container_ptr).view().owned_processes,
        forall|c: RwLockContainerPtr|
            #![trigger final(krnl).ctn_mp.spec_index(c).view().owned_processes]
            old(krnl).ctn_mp.dom().contains(c) ==> final(krnl).ctn_mp.spec_index(c).view().owned_processes == old(krnl).ctn_mp.spec_index(c).view().owned_processes,
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
        final(lctx).lock_id_set() == old(lctx).lock_id_set()
            .remove((old(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), KernelObjId::Page(page_ptr2page_index(page_ptr))))
            .insert((final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), KernelObjId::Page(page_ptr2page_index(page_ptr))))
            .insert((final(krnl).thr_mp.lock_id_by_key(page_ptr), KernelObjId::Thread(page_ptr))),
{
    let ghost uppers = krnl.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view();
    proof {
        process_perms_wf_at(krnl.prc_mp, process_ptr);
        container_perms_wf_at(krnl.ctn_mp, container_ptr);
        scheduler_perms_wf_at(krnl.sched_mp, scheduler_ptr);
        thread_perms_wf_at(krnl.thr_mp, staging_thread_ptr);
        assert(!krnl.thr_mp.dom().contains(page_ptr)) by { reveal(thread_pages_wf); };
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
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
    let page_mut = krnl.pg_arr.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(page_lock_perm));
    let Tracked(page_perm) = take_perm_4k(page_mut);
    page_mut.state = PageState::Allocated4k { state: Allocated4KPageState::AsThread };
    proof { lctx.update_lock_id(KernelObjId::Page(page_index), old_page_lock_id, krnl.pg_arr.lock_id_by_index(page_index)); }
    let Tracked(thread_perm) = krnl.retype_page_to_thread_and_insert(page_ptr, thread_value, Tracked(page_perm), Tracked(&mut *lctx));
    let staging_thread_mut = krnl.thr_mp.borrow_mut_typed(staging_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(staging_thread_lock_perm));
    staging_thread_mut.consume_staged_4k(page_ptr);
    let process_mut = krnl.prc_mp.borrow_mut_typed(process_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(process_lock_perm));
    process_mut.add_owned_thread(page_ptr, node_addr, node_perm);
    {
        let scheduler_mut = krnl.sched_mp.borrow_mut_typed(scheduler_ptr, Ghost(lctx.scheduler_lock_map()), Tracked(&*lctx), Tracked(scheduler_lock_perm));
        scheduler_mut.enqueue_scheduled_thread(page_ptr, sched_node_addr, sched_node_perm);
    }
    proof {
        add_thread_to_container_sets(
            &mut krnl.ctn_mp, container_ptr, page_ptr, uppers, lctx.container_lock_map(), lctx.thread_id(),
        );
        let ghost old_owned_threads = old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view();
        let ghost new_owned_threads = krnl.prc_mp.spec_index(process_ptr).view().owned_threads.view();
        assert_seqs_equal!(
            new_owned_threads.subrange(0, old_owned_threads.len() as int) == old_owned_threads,
            i => { seq_subrange_split_lemma::<RwLockThreadPtr>(); }
        );
        assert(kernel_u_new_thread_changed(
            kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), process_ptr,
        )) by {
            reveal(kernel_k_to_kernel_u);
        };
        assert(krnl.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
        assert(page_array_wf(krnl.pg_arr)) by { reveal(page_array_wf); };
        assert(process_perms_wf(krnl.prc_mp)) by { reveal(process_perms_wf); };
        assert(thread_perms_wf(krnl.thr_mp)) by {
            reveal(thread_perms_wf);
            reveal(thread_free_quota_pending_empty_unless_wlocked);
            reveal(thread_temp_alloc_empty_unless_wlocked);
        };
        assert(scheduler_perms_wf(krnl.sched_mp)) by { reveal(scheduler_perms_wf); reveal(LinkedList::wf_value_list); };
        assert(krnl.memory_management_inv()) by {
            allocator_4k_pages_wf_preserved_for_page_state_eq(
                old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_4k_mp, krnl.allc_4k_mp,
            );
            allocator_2m_pages_wf_preserved_for_page_state_eq(
                old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_2m_mp, krnl.allc_2m_mp,
            );
            allocator_1g_pages_wf_preserved_for_page_state_eq(
                old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_1g_mp, krnl.allc_1g_mp,
            );
            container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(
                old(krnl).ctn_mp, krnl.ctn_mp, old(krnl).pg_arr, krnl.pg_arr,
            );
            hugepage_2m_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr);
            hugepage_1g_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr);
            page_pagetable_wf_preserved_for_nonmapped_page_change(
                old(krnl).pt_mp, krnl.pt_mp, old(krnl).pg_arr, krnl.pg_arr, page_index,
            );
            container_pages_wf_preserved_for_page_state_eq(
                old(krnl).pg_arr, krnl.pg_arr, old(krnl).ctn_mp, krnl.ctn_mp,
            );
            process_pages_wf_preserved_for_page_state_eq(
                old(krnl).pg_arr, krnl.pg_arr, old(krnl).prc_mp, krnl.prc_mp,
            );
            assert(container_process_page_pagetable_wf(krnl.ctn_mp, krnl.prc_mp, krnl.pt_mp, krnl.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
            assert(pagetable_pages_wf(krnl.pt_mp, krnl.pg_arr)) by { reveal(pagetable_pages_wf); };
            assert(iommu_table_pages_wf(krnl.it_mp, krnl.pg_arr)) by { reveal(iommu_table_pages_wf); };
            assert(thread_pages_wf(krnl.thr_mp, krnl.pg_arr)) by { reveal(thread_pages_wf); };
            assert(scheduler_pages_wf(krnl.sched_mp, krnl.pg_arr)) by {
                scheduler_pages_wf_preserved_for_page_state_eq(
                    old(krnl).sched_mp, krnl.sched_mp, old(krnl).pg_arr, krnl.pg_arr,
                );
            };
            assert(cpu_set_pages_wf(krnl.cpu_set_mp, krnl.pg_arr)) by { reveal(cpu_set_pages_wf); };
            assert(pcid_allocator_pages_wf(krnl.pg_arr, krnl.pcid_allc_mp)) by { reveal(pcid_allocator_pages_wf); };
            assert(thread_staged_pages_4k_wf(krnl.thr_mp, krnl.pg_arr)) by { reveal(thread_staged_pages_4k_wf); };
            assert(thread_staged_pages_2m_wf(krnl.thr_mp, krnl.pg_arr)) by { reveal(thread_staged_pages_2m_wf); };
            assert(thread_staged_pages_1g_wf(krnl.thr_mp, krnl.pg_arr)) by { reveal(thread_staged_pages_1g_wf); };
            endpoint_pages_wf_preserved_for_page_state_eq(
                old(krnl).ep_mp, krnl.ep_mp, old(krnl).pg_arr, krnl.pg_arr,
            );
            assert(process_pagetable_match(krnl.prc_mp, krnl.pt_mp)) by { lemma_process_pagetable_match_preserved_for_process_pagetable_fields_forall(); };
            assert(process_iommu_table_match(krnl.prc_mp, krnl.it_mp)) by { lemma_process_iommu_table_match_preserved_for_process_iommu_table_fields_forall(); };
            old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view().to_set_ensures();
            lemma_container_process_thread_quota_folds_insert_zero_forall(
                old(krnl).rt_ctn, old(krnl).ctn_mp, krnl.ctn_mp, old(krnl).prc_mp, krnl.prc_mp,
                old(krnl).thr_mp, krnl.thr_mp, container_ptr, page_ptr,
            );
            assert(container_process_allocator_quota_4k_wf(
                krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_4k_mp,
            )) by { reveal(container_process_allocator_quota_4k_wf); };
            assert(container_process_allocator_quota_2m_wf(
                krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_2m_mp,
            )) by { reveal(container_process_allocator_quota_2m_wf); };
            assert(container_process_allocator_quota_1g_wf(
                krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_1g_mp,
            )) by { reveal(container_process_allocator_quota_1g_wf); };
            assert(container_allocator_wf(
                krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp,
            )) by { reveal(container_allocator_wf); };
            container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(
                krnl.allc_4k_mp, old(krnl).pg_arr, krnl.pg_arr, page_index,
            );
            container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(
                krnl.allc_2m_mp, old(krnl).pg_arr, krnl.pg_arr, page_index,
            );
            container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(
                krnl.allc_1g_mp, old(krnl).pg_arr, krnl.pg_arr, page_index,
            );
        };
        container_no_change_to_tree_fields_imply_wf(krnl.rt_ctn, old(krnl).ctn_mp, krnl.ctn_mp);
        assert(krnl.process_management_inv()) by {
            assert(old(krnl).ctn_mp.dom().contains(old(krnl).rt_ctn)) by { reveal(container_root_wf); };
            assert(container_process_wf(krnl.ctn_mp, old(krnl).prc_mp)) by { reveal(container_process_wf); };
            assert(container_process_wf(krnl.ctn_mp, krnl.prc_mp)) by { lemma_container_process_wf_preserved_for_process_rodata_forall(); };
            assert(per_container_process_tree_wf(krnl.ctn_mp, old(krnl).prc_mp)) by { reveal(per_container_process_tree_wf); };
            per_container_process_tree_wf_preserved_for_tree_fields_eq(krnl.ctn_mp, old(krnl).prc_mp, krnl.prc_mp);
            assert(container_endpoint_wf(krnl.ctn_mp, krnl.ep_mp)) by { reveal(container_endpoint_wf); };
            assert(container_cpu_wf(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr)) by { reveal(container_cpu_wf); };
            assert(thread_endpoint_ref_counter_wf(krnl.thr_mp, krnl.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); };
            assert(thread_endpoint_queue_wf(krnl.thr_mp, krnl.ep_mp)) by { reveal(thread_endpoint_queue_wf); };
            assert(thread_caller_callee_wf(krnl.thr_mp)) by { reveal(thread_caller_callee_wf); };
            assert(container_thread_endpoint_wf(krnl.ctn_mp, krnl.thr_mp, krnl.ep_mp)) by {
                reveal(container_endpoint_wf);
                reveal(thread_endpoint_ref_counter_wf);
                reveal(container_thread_endpoint_wf);
            };
            assert(container_scheduler_wf(krnl.ctn_mp, krnl.sched_mp)) by { reveal(container_scheduler_wf); };
            assert(container_cpu_set_wf(krnl.ctn_mp, krnl.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
            assert(container_pcid_allocator_wf(krnl.ctn_mp, krnl.pcid_allc_mp)) by { reveal(container_pcid_allocator_wf); };
            assert(process_pcid_allocator_wf(krnl.ctn_mp, krnl.prc_mp, krnl.pcid_allc_mp)) by { reveal(process_pcid_allocator_wf); };
            assert(container_thread_wf(krnl.ctn_mp, krnl.thr_mp)) by { reveal(container_thread_wf); };
            assert(container_thread_scheduler_wf(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp)) by {
                reveal(container_thread_scheduler_wf);
                reveal(container_thread_wf);
                reveal(container_scheduler_wf);
                seq_push_lemma::<RwLockThreadPtr>();
            };
            assert(process_cpu_wf(krnl.prc_mp, krnl.cpu_arr)) by { lemma_process_cpu_wf_preserved_for_process_pagetable_fields_forall(); };
            assert(process_thread_wf(krnl.prc_mp, krnl.thr_mp)) by {
                reveal(container_process_wf);
                reveal(process_pagetable_match);
                reveal(process_thread_wf);
                reveal(process_empty_lists_wlocked);
                seq_push_lemma::<RwLockThreadPtr>();
            };
            assert(thread_cpu_wf(krnl.thr_mp, krnl.cpu_arr)) by { reveal(thread_cpu_wf); };
        };
        assert(iommu_root_table_process_wf(&krnl.irt, krnl.prc_mp, krnl.it_mp)) by { reveal(iommu_root_table_process_wf); };
        assert(process_pci_function_ownership_wf(&krnl.irt, krnl.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
        assert(iommu_tlb_wf_spec(krnl.iommu_tlb, &krnl.irt, krnl.prc_mp, krnl.it_mp)) by { reveal(iommu_tlb_wf_spec); };
        assert(cpu_dirty_map_wf(
            krnl.ctn_mp, krnl.cpu_set_mp, krnl.prc_mp, krnl.cpu_arr, krnl.cpu_tlb, krnl.pt_mp, krnl.pcid_needflush,
        )) by {
            reveal(cpu_dirty_map_contains_container_processes);
            reveal(cpu_dirty_map_proc_pcid_match);
            reveal(container_cpu_wf);
        };
        assert(tlb_wf_spec(krnl.cpu_tlb, krnl.pt_mp, krnl.cpu_arr, krnl.pcid_needflush)) by { reveal(tlb_wf_spec); };
    }
    (page_ptr, Tracked(thread_perm))
}

/// Publish a thread in its direct container and all ancestor containers.
proof fn add_thread_to_container_sets(
    tracked container_map: &mut ContainerLockedMap, direct_container_ptr: RwLockContainerPtr, t_ptr: RwLockThreadPtr,
    uppers: Seq<RwLockContainerPtr>, held_locks: Map<RwLockContainerPtr, TypedHeldLock>, thread_id: LockThreadId,
)
    requires
        old(container_map).perms_wf(),
        old(container_map).dom().contains(direct_container_ptr),
        uppers.to_set().subset_of(old(container_map).dom()),
        uppers.no_duplicates(),
        !uppers.to_set().contains(direct_container_ptr),
        old(container_map).typed_lock_map_aligned(held_locks, thread_id),
    ensures
        final(container_map).perms_wf(),
        final(container_map).dom() == old(container_map).dom(),
        container_perms_wf(*old(container_map)) ==> container_perms_wf(*final(container_map)),
        final(container_map).typed_lock_map_aligned(held_locks, thread_id),
        forall|c: RwLockContainerPtr|
            #![trigger final(container_map).spec_index(c)]
            old(container_map).dom().contains(c) ==> {
                &&& final(container_map).spec_index(c).view() == old(container_map).spec_index(c).view()
                &&& final(container_map).spec_index(c).view_rodata() == old(container_map).spec_index(c).view_rodata()
                &&& final(container_map).spec_index(c).locking_thread() == old(container_map).spec_index(c).locking_thread()
                &&& final(container_map).spec_index(c).being_killed() == old(container_map).spec_index(c).being_killed()
                &&& final(container_map).spec_index(c).view_ghost() == ContainerGhost {
                    uppertree_seq: old(container_map).spec_index(c).view_ghost().uppertree_seq,
                    subtree_set: old(container_map).spec_index(c).view_ghost().subtree_set,
                    owned_threads: if c == direct_container_ptr {
                        Ghost(old(container_map).spec_index(c).view_ghost().owned_threads.view().insert(t_ptr))
                    } else {
                        old(container_map).spec_index(c).view_ghost().owned_threads
                    },
                    owned_indirect_threads: if uppers.to_set().contains(c) {
                        Ghost(old(container_map).spec_index(c).view_ghost().owned_indirect_threads.view().insert(t_ptr))
                    } else {
                        old(container_map).spec_index(c).view_ghost().owned_indirect_threads
                    },
                }
            },
    decreases uppers.len(),
{
    if uppers.len() > 0 {
        let c0 = uppers.spec_index(0);
        assert(uppers.to_set().contains(c0)) by { uppers.to_set_ensures(); };
        assert(uppers.drop_first().to_set().subset_of(container_map.dom())) by {
            uppers.to_set_ensures();
            uppers.drop_first().to_set_ensures();
            broadcast use vstd::seq_lib::lemma_seq_subrange_elements;
        };
        assert(!uppers.drop_first().to_set().contains(direct_container_ptr)) by {
            uppers.to_set_ensures();
            uppers.drop_first().to_set_ensures();
            broadcast use vstd::seq_lib::lemma_seq_subrange_elements;
        };
        add_thread_to_container_sets(container_map, direct_container_ptr, t_ptr, uppers.drop_first(), held_locks, thread_id);
        container_map.update_ghost(c0, ContainerGhost {
            uppertree_seq: container_map.spec_index(c0).view_ghost().uppertree_seq,
            subtree_set: container_map.spec_index(c0).view_ghost().subtree_set,
            owned_threads: container_map.spec_index(c0).view_ghost().owned_threads,
            owned_indirect_threads: Ghost(container_map.spec_index(c0).view_ghost().owned_indirect_threads.view().insert(t_ptr)),
        });
        assert(container_map.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
        assert({
            &&& !uppers.drop_first().to_set().contains(c0)
            &&& uppers.to_set() =~= uppers.drop_first().to_set().insert(c0)
        }) by { broadcast use vstd::seq_lib::lemma_seq_subrange_elements; };
    } else {
        container_map.update_ghost(direct_container_ptr, ContainerGhost {
            uppertree_seq: container_map.spec_index(direct_container_ptr).view_ghost().uppertree_seq,
            subtree_set: container_map.spec_index(direct_container_ptr).view_ghost().subtree_set,
            owned_threads: Ghost(container_map.spec_index(direct_container_ptr).view_ghost().owned_threads.view().insert(t_ptr)),
            owned_indirect_threads: container_map.spec_index(direct_container_ptr).view_ghost().owned_indirect_threads,
        });
        assert(container_map.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
    assert(container_perms_wf(*old(container_map)) ==> container_perms_wf(*container_map)) by {
        reveal(container_perms_wf);
        reveal(container_tree_fields_wf);
    };
}

pub open spec fn kernel_u_new_thread_changed(old_u: KernelU, new_u: KernelU, process_ptr: RwLockProcessPtr) -> bool {
    &&& new_u.cpu_array == old_u.cpu_array
    &&& new_u.process_map.dom() == old_u.process_map.dom()
    &&& old_u.process_map.dom().contains(process_ptr)
    &&& new_u.process_map.spec_index(process_ptr).quota_4k == old_u.process_map.spec_index(process_ptr).quota_4k
    &&& new_u.process_map.spec_index(process_ptr).owned_threads.len() == old_u.process_map.spec_index(process_ptr).owned_threads.len() + 1
    &&& new_u.process_map.spec_index(process_ptr).owned_threads.subrange(
        0, old_u.process_map.spec_index(process_ptr).owned_threads.len() as int,
    ) == old_u.process_map.spec_index(process_ptr).owned_threads
    &&& new_u.process_map.spec_index(process_ptr).zombie == old_u.process_map.spec_index(process_ptr).zombie
    &&& new_u.process_map.spec_index(process_ptr).pagetable == old_u.process_map.spec_index(process_ptr).pagetable
    &&& new_u.process_map.spec_index(process_ptr).iommu_table == old_u.process_map.spec_index(process_ptr).iommu_table
    &&& new_u.process_map.spec_index(process_ptr).quota_2m == old_u.process_map.spec_index(process_ptr).quota_2m
    &&& new_u.process_map.spec_index(process_ptr).quota_1g == old_u.process_map.spec_index(process_ptr).quota_1g
    &&& new_u.process_map.spec_index(process_ptr).parent == old_u.process_map.spec_index(process_ptr).parent
    &&& new_u.process_map.spec_index(process_ptr).children == old_u.process_map.spec_index(process_ptr).children
    &&& new_u.process_map.spec_index(process_ptr).depth == old_u.process_map.spec_index(process_ptr).depth
    &&& new_u.process_map.spec_index(process_ptr).uppertree_seq == old_u.process_map.spec_index(process_ptr).uppertree_seq
    &&& new_u.process_map.spec_index(process_ptr).subtree_set == old_u.process_map.spec_index(process_ptr).subtree_set
    &&& new_u.process_map.spec_index(process_ptr).killed == old_u.process_map.spec_index(process_ptr).killed
    &&& forall|p: RwLockProcessPtr|
        #![trigger new_u.process_map.spec_index(p)]
        old_u.process_map.dom().contains(p) && p != process_ptr ==> new_u.process_map.spec_index(p) == old_u.process_map.spec_index(p)
}
}
