use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::create_thread_from_staged_page_eof::{create_thread_from_staged_page_eof_transition_framing, eof_create_thread_inv, eof_create_thread_new_thread_fields};
verus! {
/// Consume a staged page to create a scheduled thread in `process_ptr`.
pub fn create_thread_from_staged_page_merged(
    krnl: &mut KernelK, page_ptr: PagePtr, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, scheduler_ptr: RwLockSchedulerPtr, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(page_lock_perm): Tracked<&LockPerm>, Tracked(process_lock_perm): Tracked<&LockPerm>,
    Tracked(staging_thread_lock_perm): Tracked<&LockPerm>, Tracked(scheduler_lock_perm): Tracked<&LockPerm>, initial_regs: &Registers,
) -> (ret: (RwLockThreadPtr, Tracked<LockPerm>))
    requires
        old(krnl).inv(),
        page_ptr_valid(page_ptr),
        old(krnl).prc_mp.dom().contains(process_ptr),
        old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Creating || old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Running,
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
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (scheduler_ptr, cpu_id), TypedLockMode::Write),
        scheduler_lock_perm.state() is WriteLock,
        scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
        scheduler_lock_perm.lock_id() == old(krnl).sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
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
        old(lctx).kernel_view_locking_state() is Acquire,
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
        final(krnl).thr_mp.spec_index(page_ptr).view().state == (ThreadState::SCHEDULED { cpu_id }),
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
        final(krnl).prc_mp.spec_index(process_ptr).view().state.view() == ProcessState::Running,
        final(krnl).prc_mp.spec_index(process_ptr).view().quota_4k == old(krnl).prc_mp.spec_index(process_ptr).view().quota_4k,
        forall|p: RwLockProcessPtr|
            #![trigger final(krnl).prc_mp.spec_index(p).locking_thread()]
            old(krnl).prc_mp.dom().contains(p) && p != process_ptr ==> final(krnl).prc_mp.spec_index(p).locking_thread() == old(krnl).prc_mp.spec_index(p).locking_thread(),
        forall|p: RwLockProcessPtr|
            #![trigger final(krnl).prc_mp.spec_index(p).being_killed()]
            old(krnl).prc_mp.dom().contains(p) && p != process_ptr ==> final(krnl).prc_mp.spec_index(p).being_killed() == old(krnl).prc_mp.spec_index(p).being_killed(),
        forall|p: RwLockProcessPtr|
            #![trigger final(krnl).prc_mp.spec_index(p).killer_info()]
            old(krnl).prc_mp.dom().contains(p) && p != process_ptr ==> final(krnl).prc_mp.spec_index(p).killer_info() == old(krnl).prc_mp.spec_index(p).killer_info(),
        forall|p: RwLockProcessPtr|
            #![trigger final(krnl).prc_mp.spec_index(p).view().state]
            old(krnl).prc_mp.dom().contains(p) && p != process_ptr ==> final(krnl).prc_mp.spec_index(p).view().state == old(krnl).prc_mp.spec_index(p).view().state,
        forall|p: RwLockProcessPtr|
            #![trigger final(krnl).prc_mp.spec_index(p).view().owned_threads]
            old(krnl).prc_mp.dom().contains(p) && p != process_ptr ==> final(krnl).prc_mp.spec_index(p).view().owned_threads == old(krnl).prc_mp.spec_index(p).view().owned_threads,
        final(krnl).thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(staging_thread_ptr).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(staging_thread_ptr).view().syscall_progress == old(krnl).thr_mp.spec_index(staging_thread_ptr).view().syscall_progress,
        final(krnl).thr_mp.spec_index(staging_thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(staging_thread_ptr).view().quota_4k - 1,
        final(krnl).thr_mp.spec_index(staging_thread_ptr).view().state == old(krnl).thr_mp.spec_index(staging_thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(staging_thread_ptr).view().owning_container == old(krnl).thr_mp.spec_index(staging_thread_ptr).view().owning_container,
        final(krnl).thr_mp.spec_index(staging_thread_ptr).view().endpoint_descriptors == old(krnl).thr_mp.spec_index(staging_thread_ptr).view().endpoint_descriptors,
        final(krnl).thr_mp.dom().contains(staging_thread_ptr),
        final(krnl).thr_mp.spec_index(staging_thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(staging_thread_ptr).being_killed(),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), staging_thread_ptr, TypedLockMode::Write),
        staging_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(staging_thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).thr_mp.lock_id_by_key(staging_thread_ptr) == old(krnl).thr_mp.lock_id_by_key(staging_thread_ptr),
        kernel_new_thread_fields(old(krnl), final(krnl), process_ptr, staging_thread_ptr, container_ptr, cpu_id, page_ptr, *initial_regs, None,
            old(krnl).thr_mp.spec_index(staging_thread_ptr).view().syscall_progress.view()),
        process_lock_perm.lock_id() == final(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        final(krnl).prc_mp.lock_id_by_key(process_ptr) == old(krnl).prc_mp.lock_id_by_key(process_ptr),
        final(krnl).sched_mp.dom().contains(scheduler_ptr),
        typed_lock_map_contains_mode(final(lctx).scheduler_lock_map(), (scheduler_ptr, cpu_id), TypedLockMode::Write),
        scheduler_lock_perm.lock_id() == final(krnl).sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        final(krnl).sched_mp.spec_index(scheduler_ptr).shards.lock_id_by_index(cpu_id) == old(krnl).sched_mp.spec_index(scheduler_ptr).shards.lock_id_by_index(cpu_id),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed() == false,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(page_ptr)),
        final(lctx).page_lock_map() == old(lctx).page_lock_map().insert(page_ptr2page_index(page_ptr), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write }),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map().insert(page_ptr, TypedHeldLock { lock_id: final(krnl).thr_mp.lock_id_by_key(page_ptr), mode: TypedLockMode::Write }),
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
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, ctn_mp: final(krnl).ctn_mp, sched_mp: final(krnl).sched_mp, prc_mp: final(krnl).prc_mp, thr_mp: final(krnl).thr_mp, ..*old(krnl) }),
        final(krnl).ctn_mp.dom() == old(krnl).ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(c)]
            old(krnl).ctn_mp.dom().contains(c) ==> {
                &&& final(krnl).ctn_mp.spec_index(c).view() == old(krnl).ctn_mp.spec_index(c).view()
                &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
                &&& final(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
                &&& final(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
                &&& final(krnl).ctn_mp.spec_index(c).view_ghost().owned_threads.view() == if c == container_ptr { old(krnl).ctn_mp.spec_index(c).view_ghost().owned_threads.view().insert(page_ptr) }
                        else { old(krnl).ctn_mp.spec_index(c).view_ghost().owned_threads.view() }
                &&& final(krnl).ctn_mp.spec_index(c).being_killed() == old(krnl).ctn_mp.spec_index(c).being_killed()
            },
        forall|c: RwLockContainerPtr|
            #![trigger final(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes]
            old(krnl).ctn_mp.dom().contains(c) ==> final(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes,
        forall|c: RwLockContainerPtr|
            #![trigger final(krnl).ctn_mp.spec_index(c).locking_thread()]
            old(krnl).ctn_mp.dom().contains(c) ==> final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread(),
{
    let ghost uppers = krnl.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view();
    proof {
        process_perms_wf_at(krnl.prc_mp, process_ptr);
        container_perms_wf_map(krnl.ctn_mp);
        container_perms_wf_at(krnl.ctn_mp, container_ptr);
        assert(krnl.sched_mp.spec_index(scheduler_ptr).owning_container == container_ptr) by { container_scheduler_wf_at(krnl.ctn_mp, krnl.sched_mp, container_ptr); };
        assert(krnl.prc_mp.spec_index(process_ptr).view_rodata().view().container_depth == krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().depth) by { container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, process_ptr); };
        assert(krnl.prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == krnl.prc_mp.spec_index(process_ptr).view().pagetable) by { process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, process_ptr); };
        assert(!krnl.thr_mp.dom().contains(page_ptr)) by { thread_pages_wf_page_at(krnl.thr_mp, krnl.pg_arr, page_ptr); };
        assert(uppers.to_set().subset_of(krnl.ctn_mp.dom()) && !uppers.to_set().contains(container_ptr)) by {
            uppers.to_set_ensures(); container_uppertree_seq_in_dom(krnl.rt_ctn, krnl.ctn_mp, container_ptr); container_uppertree_seq_not_self(krnl.rt_ctn, krnl.ctn_mp, container_ptr);
        };
        assert({
            &&& krnl.prc_mp.spec_index(process_ptr).view().owned_threads.view().len() < usize::MAX
            &&& !krnl.prc_mp.spec_index(process_ptr).view().owned_threads.view().contains(page_ptr)
        }) by {
            let threads = krnl.prc_mp.spec_index(process_ptr).view().owned_threads.view();
            process_thread_wf_owned_threads_dom_at(krnl.prc_mp, krnl.thr_mp, process_ptr);
            lemma_kernel_object_ptr_seq_len_bounded(&*krnl, threads);
        };
        assert({
            &&& !krnl.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.view().contains(page_ptr)
            &&& krnl.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.length != usize::MAX
        }) by { container_thread_scheduler_wf_at(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp, scheduler_ptr, cpu_id, page_ptr); scheduler_queue_len_bounded(&*krnl, scheduler_ptr, cpu_id); };
        let page_index = page_ptr2page_index(page_ptr);
        page_array_wf_at(krnl.pg_arr, page_index);
    }
    let container_rodata = krnl.ctn_mp.borrow_rodata(container_ptr);
    let container_ro = container_rodata.borrow();
    let container_depth = container_ro.depth;
    let process_rodata = krnl.prc_mp.borrow_rodata(process_ptr);
    let process_ro = process_rodata.borrow();
    let process_depth = process_ro.depth;
    let proc_pagetable = process_ro.pagetable;
    let thread_value = Thread::new_fresh(container_ptr, container_depth, process_ptr, process_depth, proc_pagetable, Ghost(uppers));
    let page_index = page_ptr2page_index(page_ptr);
    let ghost page_locks = lctx.page_lock_map();
    let Tracked(page_perm) = page_array_retype_owned_4k(&mut krnl.pg_arr, page_index, PageState::Allocated4k { state: Allocated4KPageState::AsThread }, Ghost(page_locks), Tracked(&*lctx), Tracked(page_lock_perm));
    let (Tracked(thread_perm), sched_node_addr, node_addr) = process_subsystem_create_scheduled_thread(
        &krnl.ctn_mp, &mut krnl.prc_mp, &mut krnl.thr_mp, &mut krnl.sched_mp, page_ptr, process_ptr,
        staging_thread_ptr, container_ptr, scheduler_ptr, cpu_id, thread_value, initial_regs, Tracked(page_perm),
        Tracked(&mut *lctx), Tracked(process_lock_perm), Tracked(staging_thread_lock_perm), Tracked(scheduler_lock_perm),
    );
    proof {
        lctx.update_lock_id(KernelObjId::Page(page_index), page_locks.index(page_index).lock_id, krnl.pg_arr.lock_id_by_index(page_index));
        add_thread_to_container_sets(&mut krnl.ctn_mp, container_ptr, page_ptr, uppers, krnl.thr_mp, krnl.sched_mp, lctx.container_lock_map(), lctx.thread_id());
        assert(create_thread_from_staged_page_eof_transition_framing(
            *old(krnl), *krnl, page_ptr, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, cpu_id, node_addr, sched_node_addr,
        )) by { reveal(create_thread_from_staged_page_eof_transition_framing); };
        eof_create_thread_inv(*old(krnl), *krnl, page_ptr, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, cpu_id, node_addr, sched_node_addr);
        eof_create_thread_new_thread_fields(*old(krnl), *krnl, page_ptr, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, cpu_id, node_addr, sched_node_addr, *initial_regs);
    }
    (page_ptr, Tracked(thread_perm))
}

/// One staging-thread quota funds a new thread scheduled on shard `cpu_id`, and the staging thread's progress becomes `staging_progress`.
#[verifier::opaque]
pub open spec fn kernel_u_new_thread_changed(
    old_u: KernelU, new_u: KernelU, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, cpu_id: CpuId, new_thread_ptr: RwLockThreadPtr,
    initial_regs: Registers, endpoint_ptr: Option<RwLockEndpointPtr>, staging_progress: Option<SyscallProgress>,
) -> bool {
    let old_staging = old_u.thread_map.spec_index(staging_thread_ptr);
    let new_thread = new_u.thread_map.spec_index(new_thread_ptr);
    &&& match endpoint_ptr {
        Some(e) => old_u.endpoint_map.dom().contains(e) && new_u.endpoint_map == old_u.endpoint_map.insert(e, EndpointU {
            owning_threads: old_u.endpoint_map.spec_index(e).owning_threads.insert((new_thread_ptr, 0usize)), ..old_u.endpoint_map.spec_index(e)
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
        scheduler: old_u.container_map.spec_index(container_ptr).scheduler.update(cpu_id as int, old_u.container_map.spec_index(container_ptr).scheduler[cpu_id as int].push(new_thread_ptr)),
        ..old_u.container_map.spec_index(container_ptr)
    })
    &&& old_u.process_map.dom().contains(process_ptr)
    &&& old_u.thread_map.dom().contains(staging_thread_ptr)
    &&& !old_u.thread_map.dom().contains(new_thread_ptr)
    &&& old_staging.quota_4k > 0
    &&& new_thread == (ThreadU {
        lock_state: LockStateU::Unlocked, state: ThreadState::SCHEDULED { cpu_id }, caller: None, callee: None, owning_container: container_ptr,
        owning_proc: process_ptr, last_cpu: cpu_id, quota_4k: 0, quota_2m: 0, quota_1g: 0,
        endpoint_descriptors: Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat, |i: int| if i == 0 { endpoint_ptr } else { None }),
        blocking_endpoint_ptr: None, ipc_payload: IPCPayLoad::Empty, error_code: None, trap_frame: Some(initial_regs), syscall_progress: None,
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
