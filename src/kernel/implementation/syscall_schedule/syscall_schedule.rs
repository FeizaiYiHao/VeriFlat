use vstd::prelude::*;
use crate::*;
use super::syscall_schedule_spec::*;
use super::syscall_schedule_trace::*;
use super::syscall_schedule_helpers::schedule_switch_unlock_and_record;
use super::syscall_schedule_lock_helpers::{schedule_lock_current_and_shard, schedule_lock_queue_head, schedule_continue};

verus! {
pub enum ScheduleResult {
    Off,
    Idle,
    Continue,
    /// The trap-return layer encodes this pending IPC result in the restored registers.
    Switched { thread_ptr: RwLockThreadPtr, syscall_return: Option<RetValueType> },
}

pub(crate) proof fn schedule_current_cpu_references_wf(krnl: &KernelK, cpu_id: CpuId)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
    ensures
        {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
            let container_ptr = cpu.owning_container;
            let current_process = cpu.current_process;
            let current_thread = cpu.current_thread;
            &&& krnl.ctn_mp.dom().contains(container_ptr)
            &&& krnl.ctn_mp.spec_index(container_ptr).is_init()
            &&& krnl.ctn_mp.view().spec_index(container_ptr).is_init()
            &&& krnl.ctn_mp.view().spec_index(container_ptr).addr() == container_ptr
            &&& (current_process is Some ==> krnl.prc_mp.dom().contains(current_process.unwrap()))
            &&& (current_process is Some == current_thread is Some)
            &&& (current_process is Some ==> cpu.state is Running)
            &&& (current_process is Some ==> krnl.prc_mp.spec_index(current_process.unwrap()).view_rodata().view().owning_container == container_ptr)
            &&& (current_process is Some ==> {
                &&& krnl.prc_mp.spec_index(current_process.unwrap()).view_rodata().view().container_depth == cpu.container_depth
                &&& krnl.prc_mp.spec_index(current_process.unwrap()).view_rodata().view().depth == cpu.process_depth
            })
            &&& (current_thread is Some ==> {
                let ptr = current_thread.unwrap();
                &&& krnl.thr_mp.dom().contains(ptr)
                &&& krnl.thr_mp.spec_index(ptr).view().container_depth == cpu.container_depth
                &&& krnl.thr_mp.spec_index(ptr).view().process_depth == cpu.process_depth
                &&& krnl.thr_mp.spec_index(ptr).view().state == (ThreadState::RUNNING { cpu_id })
                &&& krnl.thr_mp.spec_index(ptr).view().owning_proc == current_process.unwrap()
                &&& krnl.thr_mp.spec_index(ptr).view().owning_container == container_ptr
                &&& krnl.prc_mp.spec_index(current_process.unwrap()).view().owned_threads.view().contains(ptr)
            })
        },
{
    let cpu = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
    cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), cpu_id); container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id);
    container_perms_wf_at(krnl.ctn_mp, cpu.owning_container); thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id);
    if cpu.current_thread is Some { process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, cpu.current_thread.unwrap()); }
    if cpu.current_process is Some { container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, cpu.current_process.unwrap()); }
}

#[verifier::spinoff_prover]
fn schedule_switch_to_queue_head(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, pt_regs: &mut Registers,
    scheduler_ptr: RwLockSchedulerPtr, next_thread: RwLockThreadPtr, current_process: Option<RwLockProcessPtr>,
    current_thread: Option<RwLockThreadPtr>, process_lock_perm: Option<Tracked<LockPerm>>, current_thread_lock_perm: Option<Tracked<LockPerm>>,
    scheduler_lock_perm: Tracked<LockPerm>, next_lock_perm: Tracked<LockPerm>, cpu_lock_perm: Tracked<LockPerm>,
) -> (syscall_return: Option<RetValueType>)
    requires
        old(krnl).inv(),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, prc_mp: old(krnl).prc_mp, thr_mp: old(krnl).thr_mp, sched_mp: old(krnl).sched_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        old(krnl).sched_mp.unchanged_except(&old(steps).snapshot_k().sched_mp, scheduler_ptr),
        scheduler_shards_of(old(krnl).sched_mp.spec_index(scheduler_ptr)) == scheduler_shards_of(old(steps).snapshot_k().sched_mp.spec_index(scheduler_ptr)),
        forall|p: RwLockProcessPtr| #![trigger old(krnl).prc_mp.spec_index(p)]
            old(steps).snapshot_k().prc_mp.dom().contains(p) ==> if current_process == Some(p) {
                old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).prc_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() },
        forall|t: RwLockThreadPtr| #![trigger old(krnl).thr_mp.spec_index(t)]
            old(steps).snapshot_k().thr_mp.dom().contains(t) ==> if current_thread == Some(t) || t == next_thread {
                old(steps).snapshot_k().thr_mp.spec_index(t).locking_thread() is None
            } else { old(krnl).thr_mp.spec_index(t).locking_thread() == old(steps).snapshot_k().thr_mp.spec_index(t).locking_thread() },
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).nonlock_view().len() == 0,
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        old(krnl).irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
        old(krnl).irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
        old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
        old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom() =~= match current_process {
            Some(ptr) => set![ptr],
            None => Set::empty(),
        },
        old(lctx).thread_lock_map().dom() =~= match current_thread {
            Some(ptr) => set![ptr, next_thread],
            None => set![next_thread],
        },
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom() =~= set![(scheduler_ptr, cpu_id)],
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        cpu_lock_perm.view().state() is WriteLock,
        cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        {
            let cpu = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            &&& !(cpu.state is Off)
            &&& cpu.current_process == current_process
            &&& cpu.current_thread == current_thread
            &&& old(krnl).ctn_mp.dom().contains(cpu.owning_container)
            &&& old(krnl).ctn_mp.spec_index(cpu.owning_container).view_rodata().view().scheduler == scheduler_ptr
        },
        current_process is Some == current_thread is Some,
        current_process is Some == process_lock_perm is Some,
        current_thread is Some == current_thread_lock_perm is Some,
        current_thread is Some ==> current_thread.unwrap() != next_thread,
        old(krnl).sched_mp.dom().contains(scheduler_ptr),
        current_process is Some ==> {
            let process_ptr = current_process.unwrap();
            let perm = process_lock_perm.unwrap().view();
            &&& old(krnl).prc_mp.dom().contains(process_ptr)
            &&& !old(krnl).prc_mp.spec_index(process_ptr).being_killed()
            &&& old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Running || old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Zombie
            &&& typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write)
            &&& perm.state() is WriteLock
            &&& perm.thread_id() == old(lctx).thread_id()
            &&& perm.lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id
        },
        current_thread is Some ==> {
            let thread_ptr = current_thread.unwrap();
            let perm = current_thread_lock_perm.unwrap().view();
            &&& old(krnl).thr_mp.dom().contains(thread_ptr)
            &&& !old(krnl).thr_mp.spec_index(thread_ptr).being_killed()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id })
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == current_process.unwrap()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None
            &&& typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write)
            &&& perm.state() is WriteLock
            &&& perm.thread_id() == old(lctx).thread_id()
            &&& perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id
        },
        current_thread is Some ==> {
            &&& !old(krnl).sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.view().contains(current_thread.unwrap())
            &&& old(krnl).prc_mp.spec_index(current_process.unwrap()).view().owned_threads.view().contains(current_thread.unwrap())
        },
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (scheduler_ptr, cpu_id), TypedLockMode::Write),
        scheduler_lock_perm.view().state() is WriteLock,
        scheduler_lock_perm.view().thread_id() == old(lctx).thread_id(),
        scheduler_lock_perm.view().lock_id() == old(krnl).sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.view().len() > 0,
        old(krnl).sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.view()[0] == next_thread,
        old(krnl).thr_mp.dom().contains(next_thread),
        !old(krnl).thr_mp.spec_index(next_thread).being_killed(),
        old(krnl).thr_mp.spec_index(next_thread).view().state is SCHEDULED,
        old(krnl).thr_mp.spec_index(next_thread).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(next_thread).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(next_thread).view().syscall_progress.view() is None,
        old(krnl).thr_mp.spec_index(next_thread).view().owning_container == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), next_thread, TypedLockMode::Write),
        next_lock_perm.view().state() is WriteLock,
        next_lock_perm.view().thread_id() == old(lctx).thread_id(),
        next_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(next_thread).locking_thread()->Write_lock_id,
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(old(steps).snapshot_k()), new_u: kernel_k_to_kernel_u(*final(krnl)) }),
        schedule_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()),
            kernel_k_to_kernel_u(*final(krnl)), cpu_id, *old(pt_regs), true, schedule_flushed_pcid(*old(krnl), cpu_id, next_thread)),
        final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep { old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*final(krnl)) }),
        schedule_step_pre(final(steps).nonlock_view().last().old_u, cpu_id),
        schedule_step(final(steps).nonlock_view().last().old_u, final(steps).nonlock_view().last().new_u, cpu_id, *old(pt_regs), schedule_flushed_pcid(*old(krnl), cpu_id, next_thread)),
        forall|other_cpu: CpuId| #![trigger final(krnl).cpu_arr.spec_index(other_cpu)]
            index_valid(NUM_CPUS, other_cpu) && other_cpu != cpu_id ==> final(krnl).cpu_arr.spec_index(other_cpu).view().view().view() == old(krnl).cpu_arr.spec_index(other_cpu).view().view().view(),
        {
            let next_process = old(krnl).thr_mp.spec_index(next_thread).view().owning_proc;
            let cpu = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            let shards = scheduler_shards_of(old(krnl).sched_mp.spec_index(scheduler_ptr));
            let queue = shards[cpu_id as int];
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(next_process)
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(next_thread)
            &&& final(krnl).thr_mp.spec_index(next_thread).view().state == (ThreadState::RUNNING { cpu_id })
            &&& *final(pt_regs) == *old(krnl).thr_mp.spec_index(next_thread).view().trap_frame.get_some_0()
            &&& syscall_return == old(krnl).thr_mp.spec_index(next_thread).view().error_code
            &&& final(krnl).thr_mp.spec_index(next_thread).view().error_code is None
            &&& scheduler_shards_of(final(krnl).sched_mp.spec_index(scheduler_ptr)) == shards.update(cpu_id as int, match current_thread { Some(ptr) => queue.skip(1).push(ptr), None => queue.skip(1) })
            &&& (current_thread is Some ==> {
                let prev = current_thread.unwrap();
                &&& final(krnl).thr_mp.spec_index(prev).view().state == (ThreadState::SCHEDULED { cpu_id })
                &&& *final(krnl).thr_mp.spec_index(prev).view().trap_frame.get_some_0() == *old(pt_regs)
            })
        },
{
    let tracked scheduler_lock_perm = scheduler_lock_perm.get();
    let tracked next_lock_perm = next_lock_perm.get();
    let tracked cpu_lock_perm = cpu_lock_perm.get();
    proof {
        kernel_scheduler_shards_projection_at(old(krnl).sched_mp.spec_index(scheduler_ptr), cpu_id);
        assert({
            &&& krnl.sched_mp.perms_wf()
            &&& krnl.sched_mp.spec_index(scheduler_ptr).inv()
            &&& krnl.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.wf()
            &&& krnl.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.view().len() == krnl.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.len()
            &&& krnl.sched_mp.spec_index(scheduler_ptr).owning_container == krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container
            &&& (current_thread is Some ==> !krnl.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.view().contains(current_thread.unwrap()))
        }) by { scheduler_perms_wf_map(krnl.sched_mp); scheduler_perms_wf_at(krnl.sched_mp, scheduler_ptr); container_thread_scheduler_wf_at(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp, scheduler_ptr, cpu_id, next_thread); reveal(LinkedList::wf_value_list); };
        thread_perms_wf_map(krnl.thr_mp); thread_perms_wf_at(krnl.thr_mp, next_thread);
        if current_thread is Some { thread_perms_wf_at(krnl.thr_mp, current_thread.unwrap()); }
        assert(krnl.cpu_arr.inv()) by { cpu_array_wf_map(krnl.cpu_arr, krnl.dflt_pt.view()); };
    }
    let thread = krnl.thr_mp.borrow_typed(next_thread, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&next_lock_perm));
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
    let shard = krnl.sched_mp.borrow_shard_typed(scheduler_ptr, cpu_id, Ghost(lctx.scheduler_lock_map()), Tracked(&*lctx), Tracked(&scheduler_lock_perm));
    let (next_node, queue_head) = shard.queue.peek_head();
    assert(next_node == krnl.thr_mp.spec_index(next_thread).view().scheduler_linkedlist_node.addr()) by {
        container_thread_scheduler_wf_at(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp, scheduler_ptr, cpu_id, next_thread); container_thread_scheduler_wf_thread_at(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp, next_thread);
        reveal(LinkedList::value_list_unique);
        krnl.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.lemma_value_addr_unique(next_node, krnl.thr_mp.spec_index(next_thread).view().scheduler_linkedlist_node.addr());
    };
    let Tracked(needflush_perm) = krnl.wlock_pcid_needflush(cpu_id, pcid, Tracked(&mut *lctx));
    let ghost before_switch = *krnl;
    proof {
        assert({
            &&& krnl.cpu_arr.spec_index(cpu_id).view().is_init()
            &&& krnl.cpu_arr.spec_index(cpu_id).view().view().wf()
        }) by { cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), cpu_id); };
    }
    krnl.cpu_arr.switch_to_thread(cpu_id, next_process, next_thread, next_pagetable, cr3, pcid, depth, &mut krnl.cpu_tlb, &mut krnl.pcid_needflush, &mut krnl.cpu_published, Tracked(&needflush_perm), Tracked(&mut *lctx), Tracked(&cpu_lock_perm));
    proof { lctx.update_lock_id(KernelObjId::Cpu(cpu_id), before_switch.cpu_arr.lock_id_by_index(cpu_id), krnl.cpu_arr.lock_id_by_index(cpu_id)); }
    let shard = krnl.sched_mp.borrow_mut_shard_typed(scheduler_ptr, cpu_id, Ghost(lctx.scheduler_lock_map()), Tracked(&*lctx), Tracked(&scheduler_lock_perm));
    let (_, node_perm) = shard.queue.pop_head();
    if let Some(prev) = current_thread {
        let ghost old_prev_lock_id = krnl.thr_mp.lock_id_by_key(prev);
        let prev_perm = current_thread_lock_perm.as_ref().unwrap();
        let previous = krnl.thr_mp.borrow_mut_typed(prev, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(prev_perm.borrow()));
        let (addr, perm) = previous.running_to_scheduled(prev, cpu_id, pt_regs);
        let shard = krnl.sched_mp.borrow_mut_shard_typed(scheduler_ptr, cpu_id, Ghost(lctx.scheduler_lock_map()), Tracked(&*lctx), Tracked(&scheduler_lock_perm));
        shard.queue.push_tail(addr, perm);
        proof { lctx.update_lock_id(KernelObjId::Thread(prev), old_prev_lock_id, krnl.thr_mp.lock_id_by_key(prev)); }
    };
    let target = krnl.thr_mp.borrow_mut_typed(next_thread, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&next_lock_perm));
    let syscall_return = target.scheduled_to_running(cpu_id, node_perm, pt_regs);
    proof {
        lctx.update_lock_id(KernelObjId::Thread(next_thread), before_switch.thr_mp.lock_id_by_key(next_thread), krnl.thr_mp.lock_id_by_key(next_thread));
        assert(scheduler_context_switch_eof_transition_framing(before_switch, *krnl, cpu_id, scheduler_ptr, next_thread, *old(pt_regs))) by { reveal(scheduler_context_switch_eof_transition_framing); };
    }
    schedule_switch_unlock_and_record(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, scheduler_ptr, next_thread, current_process, current_thread, pcid,
        process_lock_perm, current_thread_lock_perm, Tracked(scheduler_lock_perm), Tracked(next_lock_perm), Tracked(cpu_lock_perm), Tracked(needflush_perm),
        Ghost(*old(krnl)), Ghost(before_switch), Ghost(*old(pt_regs)));
    syscall_return
}

/// Timer entry for a user context or the idle loop. Kernel execution is not
/// preemptible; the entry layer binds `lctx` to this CPU and restores `pt_regs`.
#[verifier::spinoff_prover]
pub fn syscall_schedule(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, pt_regs: &mut Registers) -> (ret: ScheduleResult)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).nonlock_view().len() == 0,
        old(steps).snapshot_k() == *old(krnl),
    ensures
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        schedule_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, *old(pt_regs), ret is Switched,
            if ret is Switched { schedule_flushed_pcid(*old(krnl), cpu_id, ret->Switched_thread_ptr) } else { None }),
        final(steps).nonlock_view().len() == if ret is Switched { 1nat } else { 0nat },
        ret == schedule_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id),
        (ret is Off) == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Off),
        (ret is Switched) == {
            let cpu = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            let scheduler_ptr = old(krnl).ctn_mp.spec_index(cpu.owning_container).view_rodata().view().scheduler;
            let queue = scheduler_shards_of(old(krnl).sched_mp.spec_index(scheduler_ptr))[cpu_id as int];
            &&& !(cpu.state is Off)
            &&& !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed()
            &&& (cpu.current_process is Some ==> !old(krnl).prc_mp.spec_index(cpu.current_process.unwrap()).being_killed() && !old(krnl).thr_mp.spec_index(cpu.current_thread.unwrap()).being_killed())
            &&& queue.len() > 0
            &&& !old(krnl).thr_mp.spec_index(queue[0]).being_killed()
        },
        ret is Idle ==> final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Idle || old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        ret is Continue ==> final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        !(ret is Switched) ==> {
            &&& *final(pt_regs) == *old(pt_regs)
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view()
        },
        !(ret is Switched) ==> kernel_k_to_nonlock_kernel_u(*final(krnl)) == kernel_k_to_nonlock_kernel_u(*old(krnl)),
        ret is Switched ==> final(steps).nonlock_view()[0].old_u == kernel_k_to_nonlock_kernel_u(*old(krnl)) && final(steps).nonlock_view()[0].new_u == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        ret is Switched ==> {
            let step = final(steps).nonlock_view()[0];
            &&& schedule_step_pre(step.old_u, cpu_id)
            &&& schedule_step(step.old_u, step.new_u, cpu_id, *old(pt_regs), schedule_flushed_pcid(*old(krnl), cpu_id, ret->Switched_thread_ptr))
        },
        forall|other_cpu: CpuId| #![trigger final(krnl).cpu_arr.spec_index(other_cpu)]
            index_valid(NUM_CPUS, other_cpu) && other_cpu != cpu_id ==> final(krnl).cpu_arr.spec_index(other_cpu).view().view().view() == old(krnl).cpu_arr.spec_index(other_cpu).view().view().view(),
        ret is Switched ==> {
            let next = ret->Switched_thread_ptr;
            let cpu = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            let scheduler_ptr = old(krnl).ctn_mp.spec_index(cpu.owning_container).view_rodata().view().scheduler;
            let shards = scheduler_shards_of(old(krnl).sched_mp.spec_index(scheduler_ptr));
            let queue = shards[cpu_id as int];
            &&& next == queue[0]
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(next)
            &&& final(krnl).thr_mp.spec_index(next).view().state == (ThreadState::RUNNING { cpu_id })
            &&& *final(pt_regs) == *old(krnl).thr_mp.spec_index(next).view().trap_frame.get_some_0()
            &&& ret->Switched_syscall_return == old(krnl).thr_mp.spec_index(next).view().error_code
            &&& final(krnl).thr_mp.spec_index(next).view().error_code is None
            &&& scheduler_shards_of(final(krnl).sched_mp.spec_index(scheduler_ptr)) == shards.update(cpu_id as int, match cpu.current_thread { Some(ptr) => queue.skip(1).push(ptr), None => queue.skip(1) })
            &&& (cpu.current_thread is Some ==> {
                let prev = cpu.current_thread.unwrap();
                &&& final(krnl).thr_mp.spec_index(prev).view().state == (ThreadState::SCHEDULED { cpu_id })
                &&& *final(krnl).thr_mp.spec_index(prev).view().trap_frame.get_some_0() == *old(pt_regs)
            })
        },
{
    hide(Set::is_empty);
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    proof { steps.rebase_snapshot_k_if_unchanged(&*krnl); }

    let cpu_lock_res = krnl.wlock_cpu(cpu_id, Tracked(&mut *lctx));
    if cpu_lock_res.is_none() {
        proof {
            no_locks_held_imply_all_objects_unlocked(&*krnl, &*lctx); enter_kernel_view_release_preserving_lock_alignments(&*krnl, lctx);
            schedule_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, *old(pt_regs));
            assert(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running) by { thread_cpu_wf_killed_cpu_at(old(krnl).thr_mp, old(krnl).cpu_arr, cpu_id); };
            schedule_result_from_k(old(krnl), cpu_id, ScheduleResult::Idle);
        }
        return ScheduleResult::Idle;
    }
    let Tracked(cpu_lock_perm) = cpu_lock_res.unwrap();
    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    let state = cpu.state();
    let container_ptr = cpu.owning_container();
    let current_process = cpu.current_process();
    let current_thread = cpu.current_thread();
    if let CpuState::Off = state {
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, None, None, None, None, None);
            schedule_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, *old(pt_regs));
            schedule_result_from_k(old(krnl), cpu_id, ScheduleResult::Off);
        }
        return ScheduleResult::Off;
    }
    proof { schedule_current_cpu_references_wf(&*krnl, cpu_id); }
    let scheduler_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().scheduler;
    let locked = schedule_lock_current_and_shard(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, scheduler_ptr, current_process, current_thread, Tracked(cpu_lock_perm), Ghost(*old(pt_regs)));
    if locked.is_none() {
        proof { schedule_result_from_k(old(krnl), cpu_id, ScheduleResult::Continue); }
        return ScheduleResult::Continue;
    }
    let (process_lock_perm, current_thread_lock_perm, scheduler_lock_perm, cpu_lock_perm) = locked.unwrap();
    let Tracked(scheduler_lock_perm) = scheduler_lock_perm;
    let Tracked(cpu_lock_perm) = cpu_lock_perm;
    proof { kernel_scheduler_shards_projection_at(old(krnl).sched_mp.spec_index(scheduler_ptr), cpu_id); }
    let head = schedule_lock_queue_head(krnl, Tracked(&mut *lctx), cpu_id, scheduler_ptr, current_process, current_thread, Tracked(&scheduler_lock_perm));
    if let Some((next_thread, next_perm)) = head {
        proof { assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; }; }
        proof { assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; }; }
        let syscall_return = schedule_switch_to_queue_head(
            krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, pt_regs, scheduler_ptr, next_thread, current_process, current_thread,
            process_lock_perm, current_thread_lock_perm, Tracked(scheduler_lock_perm), next_perm, Tracked(cpu_lock_perm),
        );
        proof { schedule_result_from_k(old(krnl), cpu_id, ScheduleResult::Switched { thread_ptr: next_thread, syscall_return }); }
        return ScheduleResult::Switched { thread_ptr: next_thread, syscall_return };
    }
    let ret = if let CpuState::Idle = state { ScheduleResult::Idle } else { ScheduleResult::Continue };
    proof { assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; }; }
    proof { assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; }; }
    schedule_continue(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, scheduler_ptr, current_process, current_thread, process_lock_perm, current_thread_lock_perm,
        Tracked(scheduler_lock_perm), Tracked(cpu_lock_perm), Ghost(*old(pt_regs)));
    proof { schedule_result_from_k(old(krnl), cpu_id, ret); }
    ret
}
}
