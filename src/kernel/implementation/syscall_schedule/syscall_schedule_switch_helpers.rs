use vstd::prelude::*;
use crate::*;
use super::syscall_schedule_spec::*;

verus! {
/// Reads the process, page table, CR3, PCID, and depth that `cpu_id` loads to run `next_thread`, the write-locked head of shard
/// `cpu_id` of `scheduler_ptr`.
pub(super) fn schedule_switch_read_target(
    krnl: &KernelK, Tracked(lctx): Tracked<&LocalContext>, cpu_id: CpuId, scheduler_ptr: RwLockSchedulerPtr, next_thread: RwLockThreadPtr,
    Tracked(scheduler_lock_perm): Tracked<&LockPerm>, Tracked(next_lock_perm): Tracked<&LockPerm>,
) -> (ret: (RwLockProcessPtr, RwLockPageTableRoot, PageTableRoot, Pcid, usize))
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(krnl, lctx),
        krnl.sched_mp.dom().contains(scheduler_ptr),
        typed_lock_map_contains_mode(lctx.scheduler_lock_map(), (scheduler_ptr, cpu_id), TypedLockMode::Write),
        scheduler_lock_perm.state() is WriteLock,
        scheduler_lock_perm.thread_id() == lctx.thread_id(),
        scheduler_lock_perm.lock_id() == krnl.sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        krnl.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.view().len() > 0,
        krnl.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.view()[0] == next_thread,
        krnl.thr_mp.dom().contains(next_thread),
        krnl.thr_mp.spec_index(next_thread).view().state is SCHEDULED,
        krnl.thr_mp.spec_index(next_thread).view().owning_container == krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        krnl.ctn_mp.dom().contains(krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container),
        krnl.ctn_mp.spec_index(krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container).view_rodata().view().scheduler == scheduler_ptr,
        typed_lock_map_contains_mode(lctx.thread_lock_map(), next_thread, TypedLockMode::Write),
        next_lock_perm.state() is WriteLock,
        next_lock_perm.thread_id() == lctx.thread_id(),
        next_lock_perm.lock_id() == krnl.thr_mp.spec_index(next_thread).locking_thread()->Write_lock_id,
    ensures
        ret.0 == krnl.thr_mp.spec_index(next_thread).view().owning_proc,
        krnl.prc_mp.dom().contains(ret.0),
        ret.1 == krnl.prc_mp.spec_index(ret.0).view_rodata().view().pagetable,
        ret.2 == krnl.prc_mp.spec_index(ret.0).view_rodata().view().cr3,
        ret.3 == krnl.prc_mp.spec_index(ret.0).view_rodata().view().pcid,
        ret.4 == krnl.prc_mp.spec_index(ret.0).view_rodata().view().depth,
        page_ptr_valid(ret.2),
        pcid_valid(ret.3),
        ret.3 != KERNEL_DEFAULT_PCID,
        krnl.sched_mp.spec_index(scheduler_ptr).owning_container == krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        krnl.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.head.unwrap() == krnl.thr_mp.spec_index(next_thread).view().scheduler_linkedlist_node.addr(),
{
    proof {
        assert({
            &&& krnl.sched_mp.perms_wf()
            &&& krnl.sched_mp.spec_index(scheduler_ptr).inv()
            &&& krnl.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.wf()
            &&& krnl.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.view().len() == krnl.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.len()
            &&& krnl.sched_mp.spec_index(scheduler_ptr).owning_container == krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container
        }) by { scheduler_perms_wf_map(krnl.sched_mp); scheduler_perms_wf_at(krnl.sched_mp, scheduler_ptr); container_thread_scheduler_wf_at(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp, scheduler_ptr, cpu_id, next_thread); reveal(LinkedList::wf_value_list); };
        thread_perms_wf_map(krnl.thr_mp); thread_perms_wf_at(krnl.thr_mp, next_thread);
    }
    let thread = krnl.thr_mp.borrow_typed(next_thread, Ghost(lctx.thread_lock_map()), Tracked(lctx), Tracked(next_lock_perm));
    let next_process = thread.owning_proc;
    assert({
        &&& krnl.prc_mp.dom().contains(next_process)
        &&& !krnl.prc_mp.spec_index(next_process).view().zombie
        &&& krnl.prc_mp.spec_index(next_process).is_init()
        &&& krnl.prc_mp.view().spec_index(next_process).is_init()
        &&& krnl.prc_mp.view().spec_index(next_process).addr() == next_process
    }) by { process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, next_thread); process_perms_wf_at(krnl.prc_mp, next_process); };
    let process = krnl.prc_mp.borrow_rodata(next_process).borrow();
    let next_pagetable = process.pagetable;
    let cr3 = process.cr3;
    let pcid = process.pcid;
    let depth = process.depth;
    assert(page_ptr_valid(cr3) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID) by {
        process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, next_process); process_perms_wf_at(krnl.prc_mp, next_process); pagetable_perms_wf_at(krnl.pt_mp, next_pagetable); process_pcid_allocator_wf_process_at(krnl.ctn_mp, krnl.prc_mp, krnl.pcid_allc_mp, next_process);
        krnl.pt_mp.spec_index(next_pagetable).view().table_pages_wf_cr3_at();
    };
    let shard = krnl.sched_mp.borrow_shard_typed(scheduler_ptr, cpu_id, Ghost(lctx.scheduler_lock_map()), Tracked(lctx), Tracked(scheduler_lock_perm));
    let (next_node, _) = shard.queue.peek_head();
    assert(next_node == krnl.thr_mp.spec_index(next_thread).view().scheduler_linkedlist_node.addr()) by {
        container_thread_scheduler_wf_at(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp, scheduler_ptr, cpu_id, next_thread); container_thread_scheduler_wf_thread_at(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp, next_thread);
        reveal(LinkedList::value_list_unique);
        krnl.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.lemma_value_addr_unique(next_node, krnl.thr_mp.spec_index(next_thread).view().scheduler_linkedlist_node.addr());
    };
    (next_process, next_pagetable, cr3, pcid, depth)
}

/// Switches `cpu_id`, with its `(cpu_id, pcid)` needflush cell write-held, from `current_thread`, if any, to `next_thread`, the
/// head of shard `cpu_id` of `scheduler_ptr`: loads the target address space, requeues the previous thread at the shard
/// tail with `pt_regs` as its trap frame, and resumes `next_thread` into `pt_regs`.
pub(super) fn schedule_switch_commit(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, pt_regs: &mut Registers, scheduler_ptr: RwLockSchedulerPtr,
    next_thread: RwLockThreadPtr, current_thread: Option<RwLockThreadPtr>, next_process: RwLockProcessPtr, next_pagetable: RwLockPageTableRoot,
    cr3: PageTableRoot, pcid: Pcid, depth: usize, current_thread_lock_perm: &Option<Tracked<LockPerm>>, Tracked(scheduler_lock_perm): Tracked<&LockPerm>,
    Tracked(next_lock_perm): Tracked<&LockPerm>, Tracked(cpu_lock_perm): Tracked<&LockPerm>, Tracked(needflush_perm): Tracked<&LockPerm>,
) -> (syscall_return: Option<RetValueType>)
    requires
        old(krnl).inv(),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        !(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Off),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == current_thread,
        old(krnl).cpu_published[cpu_id as int].owner_cpu() == cpu_id,
        old(lctx).pcid_needflush_lock_map().dom() =~= set![(cpu_id, pcid)],
        typed_lock_map_contains_mode(old(lctx).pcid_needflush_lock_map(), (cpu_id, pcid), TypedLockMode::Write),
        old(krnl).pcid_needflush.spec_index(cpu_id, pcid).inv(),
        needflush_perm.state() is WriteLock,
        needflush_perm.thread_id() == old(lctx).thread_id(),
        needflush_perm.lock_id() == old(krnl).pcid_needflush.spec_index(cpu_id, pcid).locking_thread()->Write_lock_id,
        next_process == old(krnl).thr_mp.spec_index(next_thread).view().owning_proc,
        old(krnl).prc_mp.dom().contains(next_process),
        next_pagetable == old(krnl).prc_mp.spec_index(next_process).view_rodata().view().pagetable,
        cr3 == old(krnl).prc_mp.spec_index(next_process).view_rodata().view().cr3,
        pcid == old(krnl).prc_mp.spec_index(next_process).view_rodata().view().pcid,
        depth == old(krnl).prc_mp.spec_index(next_process).view_rodata().view().depth,
        page_ptr_valid(cr3),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        old(krnl).sched_mp.dom().contains(scheduler_ptr),
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (scheduler_ptr, cpu_id), TypedLockMode::Write),
        scheduler_lock_perm.state() is WriteLock,
        scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
        scheduler_lock_perm.lock_id() == old(krnl).sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.view().len() > 0,
        old(krnl).sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.view()[0] == next_thread,
        old(krnl).sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.head.unwrap() == old(krnl).thr_mp.spec_index(next_thread).view().scheduler_linkedlist_node.addr(),
        old(krnl).thr_mp.dom().contains(next_thread),
        !old(krnl).thr_mp.spec_index(next_thread).being_killed(),
        old(krnl).thr_mp.spec_index(next_thread).view().state is SCHEDULED,
        old(krnl).thr_mp.spec_index(next_thread).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(next_thread).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(next_thread).view().syscall_progress.view() is None,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), next_thread, TypedLockMode::Write),
        next_lock_perm.state() is WriteLock,
        next_lock_perm.thread_id() == old(lctx).thread_id(),
        next_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(next_thread).locking_thread()->Write_lock_id,
        current_thread is Some == current_thread_lock_perm is Some,
        current_thread is Some ==> {
            let thread_ptr = current_thread.unwrap();
            let perm = current_thread_lock_perm.unwrap().view();
            &&& thread_ptr != next_thread
            &&& old(krnl).thr_mp.dom().contains(thread_ptr)
            &&& !old(krnl).thr_mp.spec_index(thread_ptr).being_killed()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id })
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None
            &&& !old(krnl).sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.view().contains(thread_ptr)
            &&& typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write)
            &&& perm.state() is WriteLock
            &&& perm.thread_id() == old(lctx).thread_id()
            &&& perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id
        },
    ensures
        scheduler_context_switch_eof_transition_framing(*old(krnl), *final(krnl), cpu_id, scheduler_ptr, next_thread, *old(pt_regs)),
        *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, pcid_needflush: final(krnl).pcid_needflush, cpu_published: final(krnl).cpu_published, sched_mp: final(krnl).sched_mp, thr_mp: final(krnl).thr_mp, cpu_tlb: final(krnl).cpu_tlb, ..*old(krnl) }),
        final(krnl).cpu_arr.inv(),
        final(krnl).cpu_tlb.inv(),
        final(krnl).cpu_published[cpu_id as int].inv(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().tlb_dirty_bitmap.inv(),
        final(krnl).sched_mp.perms_wf(),
        final(krnl).sched_mp.spec_index(scheduler_ptr).shards.inv(),
        final(krnl).sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.wf(),
        final(krnl).thr_mp.dom() == old(krnl).thr_mp.dom(),
        final(krnl).sched_mp.dom().contains(scheduler_ptr),
        !final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
        final(krnl).cpu_published[cpu_id as int].view() == (final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, pcid),
        !final(krnl).thr_mp.spec_index(next_thread).being_killed(),
        final(krnl).thr_mp.spec_index(next_thread).view().state == (ThreadState::RUNNING { cpu_id }),
        final(krnl).thr_mp.spec_index(next_thread).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(next_thread).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(next_thread).view().syscall_progress.view() is None,
        current_thread is Some ==> {
            let thread_ptr = current_thread.unwrap();
            let queue_before = old(krnl).sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().view().queue;
            &&& !queue_before.map().remove(old(krnl).thr_mp.spec_index(next_thread).view().scheduler_linkedlist_node.addr()).dom().contains(old(krnl).thr_mp.spec_index(thread_ptr).view().scheduler_linkedlist_node.addr())
            &&& !final(krnl).thr_mp.spec_index(thread_ptr).being_killed()
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::SCHEDULED { cpu_id })
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean()
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean()
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None
            &&& typed_lock_map_contains_mode(final(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write)
            &&& current_thread_lock_perm.unwrap().view().lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id
        },
        *final(pt_regs) == *old(krnl).thr_mp.spec_index(next_thread).view().trap_frame.get_some_0(),
        syscall_return == old(krnl).thr_mp.spec_index(next_thread).view().error_code,
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).cpu_lock_map().dom() == old(lctx).cpu_lock_map().dom(),
        final(lctx).thread_lock_map().dom() == old(lctx).thread_lock_map().dom(),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
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
        typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), next_thread, TypedLockMode::Write),
        cpu_lock_perm.lock_id() == final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        needflush_perm.lock_id() == final(krnl).pcid_needflush.spec_index(cpu_id, pcid).locking_thread()->Write_lock_id,
        scheduler_lock_perm.lock_id() == final(krnl).sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        next_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(next_thread).locking_thread()->Write_lock_id,
{
    proof {
        assert({
            &&& krnl.sched_mp.perms_wf()
            &&& krnl.sched_mp.spec_index(scheduler_ptr).inv()
            &&& krnl.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.wf()
            &&& krnl.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.view().len() == krnl.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.len()
        }) by { scheduler_perms_wf_map(krnl.sched_mp); scheduler_perms_wf_at(krnl.sched_mp, scheduler_ptr); reveal(LinkedList::wf_value_list); };
        thread_perms_wf_map(krnl.thr_mp); thread_perms_wf_at(krnl.thr_mp, next_thread);
        if current_thread is Some { thread_perms_wf_at(krnl.thr_mp, current_thread.unwrap()); }
        assert(krnl.cpu_arr.inv()) by { cpu_array_wf_map(krnl.cpu_arr, krnl.dflt_pt.view()); };
        assert({
            &&& krnl.cpu_arr.spec_index(cpu_id).view().is_init()
            &&& krnl.cpu_arr.spec_index(cpu_id).view().view().wf()
        }) by { cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), cpu_id); };
    }
    krnl.cpu_arr.switch_to_thread(cpu_id, next_process, next_thread, next_pagetable, cr3, pcid, depth, &mut krnl.cpu_tlb, &mut krnl.pcid_needflush, &mut krnl.cpu_published, Tracked(needflush_perm), Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof { lctx.update_lock_id(KernelObjId::Cpu(cpu_id), old(krnl).cpu_arr.lock_id_by_index(cpu_id), krnl.cpu_arr.lock_id_by_index(cpu_id)); }
    let shard = krnl.sched_mp.borrow_mut_shard_typed(scheduler_ptr, cpu_id, Ghost(lctx.scheduler_lock_map()), Tracked(&*lctx), Tracked(scheduler_lock_perm));
    let (_, node_perm) = shard.queue.pop_head();
    if let Some(prev) = current_thread {
        let ghost old_prev_lock_id = krnl.thr_mp.lock_id_by_key(prev);
        let prev_perm = current_thread_lock_perm.as_ref().unwrap();
        let previous = krnl.thr_mp.borrow_mut_typed(prev, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(prev_perm.borrow()));
        let (addr, perm) = previous.running_to_scheduled(prev, cpu_id, pt_regs);
        let shard = krnl.sched_mp.borrow_mut_shard_typed(scheduler_ptr, cpu_id, Ghost(lctx.scheduler_lock_map()), Tracked(&*lctx), Tracked(scheduler_lock_perm));
        shard.queue.push_tail(addr, perm);
        proof { lctx.update_lock_id(KernelObjId::Thread(prev), old_prev_lock_id, krnl.thr_mp.lock_id_by_key(prev)); }
    };
    let target = krnl.thr_mp.borrow_mut_typed(next_thread, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(next_lock_perm));
    let syscall_return = target.scheduled_to_running(cpu_id, node_perm, pt_regs);
    proof {
        lctx.update_lock_id(KernelObjId::Thread(next_thread), old(krnl).thr_mp.lock_id_by_key(next_thread), krnl.thr_mp.lock_id_by_key(next_thread));
        assert(scheduler_context_switch_eof_transition_framing(*old(krnl), *krnl, cpu_id, scheduler_ptr, next_thread, *old(pt_regs))) by { reveal(scheduler_context_switch_eof_transition_framing); };
    }
    syscall_return
}
} // verus!
