use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::create_thread_from_staged_page_eof::{create_thread_from_staged_page_eof_transition_framing, create_thread_from_staged_page_eof_inv, create_thread_from_staged_page_eof_new_thread_fields};
verus! {
/// Consume a staged page to create a scheduled thread in `prc_ptr`.
pub fn create_thread_from_staged_page_merged(
    krnl: &mut KernelK, pg_ptr: PagePtr, prc_ptr: RwLockProcessPtr, staging_thrd_ptr: RwLockThreadPtr,
    ctn_ptr: RwLockContainerPtr, sched_ptr: RwLockSchedulerPtr, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(page_lock_perm): Tracked<&LockPerm>, Tracked(process_lock_perm): Tracked<&LockPerm>,
    Tracked(staging_thread_lock_perm): Tracked<&LockPerm>, Tracked(scheduler_lock_perm): Tracked<&LockPerm>, initial_regs: &Registers,
) -> (ret: (RwLockThreadPtr, Tracked<LockPerm>))
    requires
        old(krnl).inv(),
        page_ptr_valid(pg_ptr),
        old(krnl).prc_mp.dom().contains(prc_ptr),
        old(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is Creating || old(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is Running,
        old(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container == ctn_ptr,
        old(krnl).thrd_mp.dom().contains(staging_thrd_ptr),
        old(krnl).ctn_mp.dom().contains(ctn_ptr),
        old(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata().view().scheduler == sched_ptr,
        old(krnl).prc_mp.spec_index(prc_ptr).being_killed() == false,
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), prc_ptr, TypedLockMode::Write),
        process_lock_perm.state() is WriteLock,
        process_lock_perm.thread_id() == old(lctx).thread_id(),
        process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(prc_ptr).locking_thread()->Write_lock_id,
        old(krnl).sched_mp.dom().contains(sched_ptr),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (sched_ptr, cpu_id), TypedLockMode::Write),
        scheduler_lock_perm.state() is WriteLock,
        scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
        scheduler_lock_perm.lock_id() == old(krnl).sched_mp.spec_index(sched_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
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
        ret.0 == pg_ptr,
        ret.0 != staging_thrd_ptr,
        ret.1.view().state() is WriteLock,
        ret.1.view().thread_id() == final(lctx).thread_id(),
        ret.1.view().lock_id() == final(krnl).thrd_mp.spec_index(pg_ptr).locking_thread()->Write_lock_id,
        final(krnl).thrd_mp.spec_index(pg_ptr).is_init(),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), pg_ptr, TypedLockMode::Write),
        final(krnl).thrd_mp.dom() =~= old(krnl).thrd_mp.dom().insert(pg_ptr),
        forall|t: RwLockThreadPtr| #![trigger final(krnl).thrd_mp.spec_index(t)]
            old(krnl).thrd_mp.dom().contains(t) && t != staging_thrd_ptr ==> final(krnl).thrd_mp.spec_index(t) == old(krnl).thrd_mp.spec_index(t),
        final(krnl).thrd_mp.spec_index(pg_ptr).view().free_quota_pending_clean(),
        final(krnl).thrd_mp.spec_index(pg_ptr).view().temp_alloc_clean(),
        final(krnl).thrd_mp.spec_index(pg_ptr).view().syscall_progress.view() is None,
        !final(krnl).thrd_mp.spec_index(pg_ptr).view_ghost().exited,
        final(krnl).thrd_mp.spec_index(pg_ptr).view().state == (ThreadState::SCHEDULED { cpu_id }),
        final(krnl).thrd_mp.spec_index(pg_ptr).view().trap_frame.is_some(),
        *final(krnl).thrd_mp.spec_index(pg_ptr).view().trap_frame.get_some_0() == *initial_regs,
        final(krnl).thrd_mp.spec_index(pg_ptr).view().owning_container == ctn_ptr,
        final(krnl).thrd_mp.spec_index(pg_ptr).view().owning_proc == prc_ptr,
        final(krnl).thrd_mp.spec_index(pg_ptr).view().endpoint_descriptors.spec_index(0) is None,
        final(krnl).thrd_mp.spec_index(pg_ptr).view().endpoint_descriptors.wf(),
        final(krnl).thrd_mp.spec_index(pg_ptr).being_killed() == false,
        final(krnl).prc_mp.dom().contains(prc_ptr),
        final(krnl).prc_mp.dom() == old(krnl).prc_mp.dom(),
        final(krnl).prc_mp.spec_index(prc_ptr).view_rodata() == old(krnl).prc_mp.spec_index(prc_ptr).view_rodata(),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), prc_ptr, TypedLockMode::Write),
        final(krnl).prc_mp.spec_index(prc_ptr).being_killed() == false,
        final(krnl).prc_mp.spec_index(prc_ptr).view().owned_threads.view() == old(krnl).prc_mp.spec_index(prc_ptr).view().owned_threads.view().push(pg_ptr),
        final(krnl).prc_mp.spec_index(prc_ptr).view().state.view() == ProcessState::Running,
        final(krnl).prc_mp.spec_index(prc_ptr).view().quota_4k == old(krnl).prc_mp.spec_index(prc_ptr).view().quota_4k,
        forall|p: RwLockProcessPtr|
            #![trigger final(krnl).prc_mp.spec_index(p).locking_thread()]
            old(krnl).prc_mp.dom().contains(p) && p != prc_ptr ==> final(krnl).prc_mp.spec_index(p).locking_thread() == old(krnl).prc_mp.spec_index(p).locking_thread(),
        forall|p: RwLockProcessPtr|
            #![trigger final(krnl).prc_mp.spec_index(p).being_killed()]
            old(krnl).prc_mp.dom().contains(p) && p != prc_ptr ==> final(krnl).prc_mp.spec_index(p).being_killed() == old(krnl).prc_mp.spec_index(p).being_killed(),
        forall|p: RwLockProcessPtr|
            #![trigger final(krnl).prc_mp.spec_index(p).killer_info()]
            old(krnl).prc_mp.dom().contains(p) && p != prc_ptr ==> final(krnl).prc_mp.spec_index(p).killer_info() == old(krnl).prc_mp.spec_index(p).killer_info(),
        forall|p: RwLockProcessPtr|
            #![trigger final(krnl).prc_mp.spec_index(p).view().state]
            old(krnl).prc_mp.dom().contains(p) && p != prc_ptr ==> final(krnl).prc_mp.spec_index(p).view().state == old(krnl).prc_mp.spec_index(p).view().state,
        forall|p: RwLockProcessPtr|
            #![trigger final(krnl).prc_mp.spec_index(p).view().owned_threads]
            old(krnl).prc_mp.dom().contains(p) && p != prc_ptr ==> final(krnl).prc_mp.spec_index(p).view().owned_threads == old(krnl).prc_mp.spec_index(p).view().owned_threads,
        final(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().temp_alloc_clean(),
        final(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().free_quota_pending_clean(),
        final(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().syscall_progress == old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().syscall_progress,
        final(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().quota_4k == old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().quota_4k - 1,
        final(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().state == old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().state,
        final(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().owning_container == old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().owning_container,
        final(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().endpoint_descriptors == old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().endpoint_descriptors,
        final(krnl).thrd_mp.dom().contains(staging_thrd_ptr),
        final(krnl).thrd_mp.spec_index(staging_thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(staging_thrd_ptr).being_killed(),
        final(krnl).thrd_mp.spec_index(staging_thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view_ghost(),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), staging_thrd_ptr, TypedLockMode::Write),
        staging_thread_lock_perm.lock_id() == final(krnl).thrd_mp.spec_index(staging_thrd_ptr).locking_thread()->Write_lock_id,
        final(krnl).thrd_mp.lock_id_by_key(staging_thrd_ptr) == old(krnl).thrd_mp.lock_id_by_key(staging_thrd_ptr),
        kernel_new_thread_fields(old(krnl), final(krnl), prc_ptr, staging_thrd_ptr, ctn_ptr, cpu_id, pg_ptr, *initial_regs, None,
            old(krnl).thrd_mp.spec_index(staging_thrd_ptr).view().syscall_progress.view()),
        process_lock_perm.lock_id() == final(krnl).prc_mp.spec_index(prc_ptr).locking_thread()->Write_lock_id,
        final(krnl).prc_mp.lock_id_by_key(prc_ptr) == old(krnl).prc_mp.lock_id_by_key(prc_ptr),
        final(krnl).sched_mp.dom().contains(sched_ptr),
        typed_lock_map_contains_mode(final(lctx).scheduler_lock_map(), (sched_ptr, cpu_id), TypedLockMode::Write),
        scheduler_lock_perm.lock_id() == final(krnl).sched_mp.spec_index(sched_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        final(krnl).sched_mp.spec_index(sched_ptr).shards.lock_id_by_index(cpu_id) == old(krnl).sched_mp.spec_index(sched_ptr).shards.lock_id_by_index(cpu_id),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().being_killed() == false,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write),
        page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id,
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(pg_ptr)),
        final(lctx).page_lock_map() == old(lctx).page_lock_map().insert(page_ptr2page_index(pg_ptr), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(pg_ptr)), mode: TypedLockMode::Write }),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map().insert(pg_ptr, TypedHeldLock { lock_id: final(krnl).thrd_mp.lock_id_by_key(pg_ptr), mode: TypedLockMode::Write }),
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
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, ctn_mp: final(krnl).ctn_mp, sched_mp: final(krnl).sched_mp, prc_mp: final(krnl).prc_mp, thrd_mp: final(krnl).thrd_mp, ..*old(krnl) }),
        final(krnl).ctn_mp.dom() == old(krnl).ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(c)]
            old(krnl).ctn_mp.dom().contains(c) ==> {
                &&& final(krnl).ctn_mp.spec_index(c).view() == old(krnl).ctn_mp.spec_index(c).view()
                &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
                &&& final(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
                &&& final(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
                &&& final(krnl).ctn_mp.spec_index(c).view_ghost().owned_endpoints == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_endpoints
                &&& final(krnl).ctn_mp.spec_index(c).view_ghost().owned_threads.view() == if c == ctn_ptr { old(krnl).ctn_mp.spec_index(c).view_ghost().owned_threads.view().insert(pg_ptr) }
                        else { old(krnl).ctn_mp.spec_index(c).view_ghost().owned_threads.view() }
                &&& final(krnl).ctn_mp.spec_index(c).control() == old(krnl).ctn_mp.spec_index(c).control()
            },
        forall|c: RwLockContainerPtr|
            #![trigger final(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes]
            old(krnl).ctn_mp.dom().contains(c) ==> final(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes,
        forall|c: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(c).locking_thread()] old(krnl).ctn_mp.dom().contains(c) ==> final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread(),
{
    let ghost uppers = krnl.ctn_mp.spec_index(ctn_ptr).view_ghost().uppertree_seq.view();
    proof {
        process_perms_wf_at(krnl.prc_mp, prc_ptr);
        container_perms_wf_map(krnl.ctn_mp);
        container_perms_wf_at(krnl.ctn_mp, ctn_ptr);
        assert(krnl.sched_mp.spec_index(sched_ptr).owning_container == ctn_ptr) by { container_scheduler_wf_container_at(krnl.ctn_mp, krnl.sched_mp, ctn_ptr); };
        assert(krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().container_depth == krnl.ctn_mp.spec_index(ctn_ptr).view_rodata().view().depth) by { container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, prc_ptr); };
        assert(krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == krnl.prc_mp.spec_index(prc_ptr).view().pagetable) by { process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr); };
        assert(!krnl.thrd_mp.dom().contains(pg_ptr)) by { thread_pages_wf_page_at(krnl.thrd_mp, krnl.pg_arr, pg_ptr); };
        assert(uppers.to_set().subset_of(krnl.ctn_mp.dom()) && !uppers.to_set().contains(ctn_ptr)) by {
            uppers.to_set_ensures(); container_uppertree_seq_wf_implies_ancestors_in_dom(krnl.rt_ctn, krnl.ctn_mp, ctn_ptr); container_uppertree_seq_not_self(krnl.rt_ctn, krnl.ctn_mp, ctn_ptr);
        };
        assert({
            &&& krnl.prc_mp.spec_index(prc_ptr).view().owned_threads.view().len() < usize::MAX
            &&& !krnl.prc_mp.spec_index(prc_ptr).view().owned_threads.view().contains(pg_ptr)
        }) by {
            let threads = krnl.prc_mp.spec_index(prc_ptr).view().owned_threads.view();
            process_thread_wf_implies_owned_threads_in_map(krnl.prc_mp, krnl.thrd_mp, prc_ptr);
            lemma_kernel_object_ptr_seq_len_bounded(&*krnl, threads);
        };
        assert({
            &&& !krnl.sched_mp.spec_index(sched_ptr).shard(cpu_id).queue.view().contains(pg_ptr)
            &&& krnl.sched_mp.spec_index(sched_ptr).shard(cpu_id).queue.length != usize::MAX
        }) by { container_thread_scheduler_wf_shard_at(krnl.ctn_mp, krnl.thrd_mp, krnl.sched_mp, sched_ptr, cpu_id, pg_ptr); scheduler_queue_len_bounded(&*krnl, sched_ptr, cpu_id); };
        let pg_idx = page_ptr2page_index(pg_ptr);
        page_array_wf_at(krnl.pg_arr, pg_idx);
    }
    let container_rodata = krnl.ctn_mp.borrow_rodata(ctn_ptr);
    let container_ro = container_rodata.borrow();
    let container_depth = container_ro.depth;
    let process_rodata = krnl.prc_mp.borrow_rodata(prc_ptr);
    let process_ro = process_rodata.borrow();
    let process_depth = process_ro.depth;
    let proc_pagetable = process_ro.pagetable;
    let thread_value = Thread::new_fresh(ctn_ptr, container_depth, prc_ptr, process_depth, proc_pagetable, Ghost(uppers));
    let pg_idx = page_ptr2page_index(pg_ptr);
    let ghost page_locks = lctx.page_lock_map();
    let Tracked(page_perm) = page_array_retype_owned_4k(&mut krnl.pg_arr, pg_idx, PageState::Allocated4k { state: Allocated4KPageState::AsThread }, Ghost(page_locks), Tracked(&*lctx), Tracked(page_lock_perm));
    let (Tracked(thread_perm), sched_node_addr, node_addr) = process_subsystem_create_scheduled_thread(
        &krnl.ctn_mp, &mut krnl.prc_mp, &mut krnl.thrd_mp, &mut krnl.sched_mp, pg_ptr, prc_ptr,
        staging_thrd_ptr, ctn_ptr, sched_ptr, cpu_id, thread_value, initial_regs, Tracked(page_perm),
        Tracked(&mut *lctx), Tracked(process_lock_perm), Tracked(staging_thread_lock_perm), Tracked(scheduler_lock_perm),
    );
    proof {
        lctx.update_lock_id(KernelObjId::Page(pg_idx), page_locks.index(pg_idx).lock_id, krnl.pg_arr.lock_id_by_index(pg_idx));
        add_thread_to_container_sets(&mut krnl.ctn_mp, ctn_ptr, pg_ptr, uppers, krnl.thrd_mp, krnl.sched_mp, lctx.container_lock_map(), lctx.thread_id());
        assert(create_thread_from_staged_page_eof_transition_framing(
            *old(krnl), *krnl, pg_ptr, prc_ptr, staging_thrd_ptr, ctn_ptr, sched_ptr, cpu_id, node_addr, sched_node_addr,
        )) by { reveal(create_thread_from_staged_page_eof_transition_framing); };
        create_thread_from_staged_page_eof_inv(*old(krnl), *krnl, pg_ptr, prc_ptr, staging_thrd_ptr, ctn_ptr, sched_ptr, cpu_id, node_addr, sched_node_addr);
        create_thread_from_staged_page_eof_new_thread_fields(*old(krnl), *krnl, pg_ptr, prc_ptr, staging_thrd_ptr, ctn_ptr, sched_ptr, cpu_id, node_addr, sched_node_addr, *initial_regs);
    }
    (pg_ptr, Tracked(thread_perm))
}
}
