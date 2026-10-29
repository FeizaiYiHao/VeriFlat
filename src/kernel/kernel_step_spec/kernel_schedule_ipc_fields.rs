use vstd::prelude::*;
use crate::*;

verus! {
/// Switching `cpu_id` to `next_thread` flushes the `(cpu_id, pcid)` TLB entry of its process's PCID when a flush is pending or
/// the entry is dirty for another process or page table.
pub open spec fn context_switch_flushed_pcid(pre: KernelK, cpu_id: CpuId, next_thread: RwLockThreadPtr) -> Option<Pcid> {
    let next_process = pre.thr_mp.spec_index(next_thread).view().owning_proc;
    let target = pre.prc_mp.spec_index(next_process).view_rodata().view();
    let pcid = target.pcid;
    let dirty = pre.cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid);
    if pre.pcid_needflush.spec_index(cpu_id, pcid).view().needflush || (dirty is Some && (dirty.unwrap().process_ptr != next_process || dirty.unwrap().pagetable_ptr != target.pagetable)) { Some(pcid) } else { None }
}

#[verifier::opaque]
/// The live head `next_thread` of shard `cpu_id` of the CPU's container replaces the live thread running on
/// `cpu_id`, which is requeued at the tail of that shard, and at most the `(cpu_id, flushed_pcid)` TLB entry is flushed.
pub open spec fn kernel_context_switch_fields(pre: &KernelK, post: &KernelK, cpu_id: CpuId, next_thread: RwLockThreadPtr, entry_regs: Registers, flushed_pcid: Option<Pcid>) -> bool {
    let cpu = pre.cpu_arr.spec_index(cpu_id).value.view().view();
    let previous = cpu.current_thread;
    let next = pre.thr_mp.spec_index(next_thread);
    let next_process = next.view().owning_proc;
    let run_queue = scheduler_shards_of(pre.sched_mp.spec_index(pre.ctn_mp.spec_index(cpu.owning_container).view_rodata().view().scheduler))[cpu_id as int];
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& pre.cpu_op.view().view().len() == NUM_CPUS
    &&& post.cpu_op.view().view() == pre.cpu_op.view().view().update(cpu_id as int, CpuOpState::Trap)
    &&& forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)]
        pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).locking_thread() == pre.ctn_mp.spec_index(p).locking_thread()
    &&& forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
        pre.prc_mp.dom().contains(p) ==> post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread()
    &&& forall|p: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(p)]
        pre.thr_mp.dom().contains(p) ==> post.thr_mp.spec_index(p).locking_thread() == pre.thr_mp.spec_index(p).locking_thread()
    &&& forall|p: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(p)]
        pre.ep_mp.dom().contains(p) ==> post.ep_mp.spec_index(p).locking_thread() == pre.ep_mp.spec_index(p).locking_thread()
    &&& forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
        pre.pt_mp.dom().contains(p) ==> post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread()
    &&& forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
        pre.it_mp.dom().contains(p) ==> post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread()
    &&& forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
        index_valid(NUM_CPUS, i) ==> post.cpu_arr.spec_index(i).value.locking_thread() == pre.cpu_arr.spec_index(i).value.locking_thread()
    &&& kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view())
    &&& kernel_iommu_table_nonlock_fields_unchanged(pre.it_mp, post.it_mp)
    &&& kernel_process_nonlock_fields_unchanged(pre.prc_mp, post.prc_mp)
    &&& kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp)
    &&& post.irt.view().owners() == pre.irt.view().owners()
    &&& post.irt.view().iommu_roots() == pre.irt.view().iommu_roots()
    &&& post.iommu_tlb.view() == pre.iommu_tlb.view()
    &&& post.dflt_pt == pre.dflt_pt
    &&& post.cpu_offline_mp == pre.cpu_offline_mp
    &&& post.cpu_set_mp == pre.cpu_set_mp
    &&& post.cpu_tlb.view() == match flushed_pcid {
        Some(pcid) => pre.cpu_tlb.view().insert((cpu_id, pcid), post.cpu_tlb.spec_index((cpu_id, pcid))),
        None => pre.cpu_tlb.view(),
    }
    &&& flushed_pcid matches Some(pcid) ==> cpu_tlb_within_may_cache(*post, cpu_id, pcid, post.cpu_tlb.spec_index((cpu_id, pcid)))
    &&& pre.cpu_arr.spec_index(cpu_id).value.locking_thread() is None
    &&& !(cpu.state is Off)
    &&& pre.ctn_mp.dom().contains(cpu.owning_container)
    &&& run_queue.len() > 0
    &&& run_queue[0] == next_thread
    &&& pre.thr_mp.dom().contains(next_thread)
    &&& next.locking_thread() is None
    &&& !next.being_killed()
    &&& next.view().state is SCHEDULED
    &&& next.view().owning_container == cpu.owning_container
    &&& pre.prc_mp.dom().contains(next_process)
    &&& previous != Some(next_thread)
    &&& cpu.current_process is Some == previous is Some
    &&& (previous is Some ==> {
        let prev = pre.thr_mp.spec_index(previous.unwrap());
        let process_ptr = cpu.current_process.unwrap();
        &&& pre.thr_mp.dom().contains(previous.unwrap())
        &&& prev.locking_thread() is None
        &&& !prev.being_killed()
        &&& prev.view().state == (ThreadState::RUNNING { cpu_id })
        &&& prev.view().owning_proc == process_ptr
        &&& pre.prc_mp.dom().contains(process_ptr)
        &&& pre.prc_mp.spec_index(process_ptr).locking_thread() is None
        &&& !pre.prc_mp.spec_index(process_ptr).being_killed()
    })
    &&& forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
        index_valid(NUM_CPUS, i) ==> {
            let a = pre.cpu_arr.spec_index(i).value.view().view();
            let b = post.cpu_arr.spec_index(i).value.view().view();
            &&& b.owning_container == a.owning_container
            &&& b.state == if i == cpu_id { CpuState::Running } else { a.state }
            &&& b.current_process == if i == cpu_id { Some(next_process) } else { a.current_process }
            &&& b.current_thread == if i == cpu_id { Some(next_thread) } else { a.current_thread }
            &&& post.cpu_arr.spec_index(i).value.killer_info() == pre.cpu_arr.spec_index(i).value.killer_info()
        }
    &&& post.ctn_mp.dom() == pre.ctn_mp.dom()
    &&& forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)]
        pre.ctn_mp.dom().contains(c) ==> {
            let a = pre.ctn_mp.spec_index(c);
            let b = post.ctn_mp.spec_index(c);
            let a_ro = a.view_rodata().view();
            let b_ro = b.view_rodata().view();
            &&& b.view().children.view() == a.view().children.view()
            &&& b.view_ghost().uppertree_seq.view() == a.view_ghost().uppertree_seq.view()
            &&& b.view_ghost().subtree_set.view() == a.view_ghost().subtree_set.view()
            &&& b.view().root_process == a.view().root_process
            &&& b.view().zombie == a.view().zombie
            &&& b.view_ghost().owned_processes.view() == a.view_ghost().owned_processes.view()
            &&& b.view_ghost().owned_threads.view() == a.view_ghost().owned_threads.view()
            &&& b.view_ghost().owned_endpoints.view() == a.view_ghost().owned_endpoints.view()
            &&& b.view().owned_pages.view() == a.view().owned_pages.view()
            &&& b_ro.parent == a_ro.parent
            &&& b_ro.depth == a_ro.depth
            &&& b_ro.scheduler == a_ro.scheduler
            &&& b_ro.cpu_set == a_ro.cpu_set
            &&& b.being_killed() == a.being_killed()
        }
    &&& forall|s: RwLockSchedulerPtr| #![trigger post.sched_mp.spec_index(s)]
        post.sched_mp.dom().contains(s) ==> {
            let queue = scheduler_shards_of(pre.sched_mp.spec_index(s));
            scheduler_shards_of(post.sched_mp.spec_index(s)) == if s == pre.ctn_mp.spec_index(cpu.owning_container).view_rodata().view().scheduler {
                queue.update(cpu_id as int, match previous { Some(prev) => queue[cpu_id as int].skip(1).push(prev), None => queue[cpu_id as int].skip(1) })
            } else { queue }
        }
    &&& forall|c: RwLockContainerPtr| #![trigger post.pcid_allc_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator)]
        pre.ctn_mp.dom().contains(c) ==> PcidAllocator::free_pcids(post.pcid_allc_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator).view().ref_counters.view())
            == PcidAllocator::free_pcids(pre.pcid_allc_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator).view().ref_counters.view())
    &&& forall|c: RwLockContainerPtr| #![trigger post.allc_4k_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k)]
        pre.ctn_mp.dom().contains(c) ==> post.allc_4k_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k).quota.view().view()
            == pre.allc_4k_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k).quota.view().view()
    &&& forall|c: RwLockContainerPtr| #![trigger post.allc_2m_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_2m)]
        pre.ctn_mp.dom().contains(c) ==> post.allc_2m_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_2m).quota.view().view()
            == pre.allc_2m_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_2m).quota.view().view()
    &&& forall|c: RwLockContainerPtr| #![trigger post.allc_1g_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g)]
        pre.ctn_mp.dom().contains(c) ==> post.allc_1g_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g).quota.view().view()
            == pre.allc_1g_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g).quota.view().view()
    &&& post.thr_mp.dom() == pre.thr_mp.dom()
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)]
        pre.thr_mp.dom().contains(t) ==> {
            let a = pre.thr_mp.spec_index(t).view();
            let b = post.thr_mp.spec_index(t).view();
            &&& b.state == if t == next_thread { ThreadState::RUNNING { cpu_id } } else if previous == Some(t) { ThreadState::SCHEDULED { cpu_id } } else { a.state }
            &&& b.caller == a.caller
            &&& b.callee == a.callee
            &&& b.owning_container == a.owning_container
            &&& b.owning_proc == a.owning_proc
            &&& b.last_cpu == if t == next_thread { cpu_id } else { a.last_cpu }
            &&& b.quota_4k == a.quota_4k
            &&& b.quota_2m == a.quota_2m
            &&& b.quota_1g == a.quota_1g
            &&& b.endpoint_descriptors.view() == a.endpoint_descriptors.view()
            &&& b.blocking_endpoint_ptr == a.blocking_endpoint_ptr
            &&& b.ipc_payload == a.ipc_payload
            &&& b.error_code == if t == next_thread || previous == Some(t) { None } else { a.error_code }
            &&& (t == next_thread ==> b.trap_frame.is_none())
            &&& (previous == Some(t) ==> b.trap_frame.is_some() && *b.trap_frame.get_some_0() == entry_regs)
            &&& (t != next_thread && previous != Some(t) ==> b.trap_frame == a.trap_frame)
            &&& b.syscall_progress.view() == a.syscall_progress.view()
            &&& post.thr_mp.spec_index(t).being_killed() == pre.thr_mp.spec_index(t).being_killed()
        }
}

#[verifier::opaque]
/// The Idle cpu `cpu_id`, whose own shard is empty, takes the live head `thread` of shard `victim`, the lowest
/// other nonempty shard of its container's scheduler, onto shard `cpu_id`; every lock is released again.
pub open spec fn kernel_rebalance_pull_fields(pre: &KernelK, post: &KernelK, cpu_id: CpuId, victim: CpuId, thread: RwLockThreadPtr) -> bool {
    let cpu = pre.cpu_arr.spec_index(cpu_id).value.view().view();
    let queues = scheduler_shards_of(pre.sched_mp.spec_index(pre.ctn_mp.spec_index(cpu.owning_container).view_rodata().view().scheduler));
    let t = pre.thr_mp.spec_index(thread);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& index_valid(NUM_CPUS, victim)
    &&& victim != cpu_id
    &&& *post == (KernelK { cpu_arr: post.cpu_arr, cpu_op: post.cpu_op, thr_mp: post.thr_mp, sched_mp: post.sched_mp, ..*pre })
    &&& post.cpu_op.view().view() == pre.cpu_op.view().view()
    &&& pre.cpu_arr.spec_index(cpu_id).value.locking_thread() is None
    &&& cpu.state is Idle
    &&& pre.ctn_mp.dom().contains(cpu.owning_container)
    &&& queues[cpu_id as int].len() == 0
    &&& first_nonempty_shard(queues, 0, cpu_id) == Some(victim)
    &&& queues[victim as int].len() > 0
    &&& queues[victim as int][0] == thread
    &&& pre.thr_mp.dom().contains(thread)
    &&& t.locking_thread() is None
    &&& !t.being_killed()
    &&& t.view().state == (ThreadState::SCHEDULED { cpu_id: victim })
    &&& t.view().owning_container == cpu.owning_container
    &&& forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
        index_valid(NUM_CPUS, i) ==> {
            &&& post.cpu_arr.spec_index(i).value.locking_thread() == pre.cpu_arr.spec_index(i).value.locking_thread()
            &&& post.cpu_arr.spec_index(i).value.view().view() == pre.cpu_arr.spec_index(i).value.view().view()
            &&& post.cpu_arr.spec_index(i).value.killer_info() == pre.cpu_arr.spec_index(i).value.killer_info()
        }
    &&& forall|s: RwLockSchedulerPtr| #![trigger post.sched_mp.spec_index(s)]
        post.sched_mp.dom().contains(s) ==> {
            let q = scheduler_shards_of(pre.sched_mp.spec_index(s));
            scheduler_shards_of(post.sched_mp.spec_index(s)) == if s == pre.ctn_mp.spec_index(cpu.owning_container).view_rodata().view().scheduler {
                q.update(victim as int, q[victim as int].skip(1)).update(cpu_id as int, q[cpu_id as int].push(thread))
            } else { q }
        }
    &&& post.thr_mp.dom() == pre.thr_mp.dom()
    &&& forall|p: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(p)]
        pre.thr_mp.dom().contains(p) ==> {
            &&& post.thr_mp.spec_index(p).locking_thread() == pre.thr_mp.spec_index(p).locking_thread()
            &&& post.thr_mp.spec_index(p).being_killed() == pre.thr_mp.spec_index(p).being_killed()
            &&& post.thr_mp.spec_index(p).view() == if p == thread {
                Thread { state: ThreadState::SCHEDULED { cpu_id }, ..pre.thr_mp.spec_index(p).view() }
            } else { pre.thr_mp.spec_index(p).view() }
        }
}

#[verifier::opaque]
/// The live thread running on `cpu_id` blocks on the live endpoint at `endpoint_index`, the CPU goes
/// idle, and at most the `(cpu_id, KERNEL_DEFAULT_PCID)` TLB entry is flushed.
pub open spec fn kernel_ipc_block_fields(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    waiting_state: ThreadState, payload: IPCPayLoad, regs: Registers, flushed_default_pcid: bool,
) -> bool {
    let cpu = pre.cpu_arr.spec_index(cpu_id).value.view().view();
    let thread = pre.thr_mp.spec_index(thread_ptr);
    let endpoint = pre.ep_mp.spec_index(endpoint_ptr);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& pre.cpu_op.view().view().len() == NUM_CPUS
    &&& post.cpu_op.view().view() == pre.cpu_op.view().view().update(cpu_id as int, CpuOpState::Idle)
    &&& forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)]
        pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).locking_thread() == pre.ctn_mp.spec_index(p).locking_thread()
    &&& forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
        pre.prc_mp.dom().contains(p) ==> post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread()
    &&& forall|p: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(p)]
        pre.thr_mp.dom().contains(p) ==> post.thr_mp.spec_index(p).locking_thread() == pre.thr_mp.spec_index(p).locking_thread()
    &&& forall|p: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(p)]
        pre.ep_mp.dom().contains(p) ==> post.ep_mp.spec_index(p).locking_thread() == pre.ep_mp.spec_index(p).locking_thread()
    &&& forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
        pre.pt_mp.dom().contains(p) ==> post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread()
    &&& forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
        pre.it_mp.dom().contains(p) ==> post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread()
    &&& forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
        index_valid(NUM_CPUS, i) ==> post.cpu_arr.spec_index(i).value.locking_thread() == pre.cpu_arr.spec_index(i).value.locking_thread()
    &&& kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view())
    &&& kernel_iommu_table_nonlock_fields_unchanged(pre.it_mp, post.it_mp)
    &&& kernel_process_nonlock_fields_unchanged(pre.prc_mp, post.prc_mp)
    &&& kernel_container_nonlock_fields_and_quotas_unchanged(pre, post)
    &&& post.irt.view().owners() == pre.irt.view().owners()
    &&& post.irt.view().iommu_roots() == pre.irt.view().iommu_roots()
    &&& post.iommu_tlb.view() == pre.iommu_tlb.view()
    &&& post.dflt_pt == pre.dflt_pt
    &&& post.cpu_tlb.view() == if flushed_default_pcid {
        pre.cpu_tlb.view().insert((cpu_id, KERNEL_DEFAULT_PCID), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })
    } else { pre.cpu_tlb.view() }
    &&& pre.cpu_arr.spec_index(cpu_id).value.locking_thread() is None
    &&& cpu.state is Running
    &&& cpu.current_thread == Some(thread_ptr)
    &&& cpu.current_process == Some(thread.view().owning_proc)
    &&& pre.prc_mp.dom().contains(thread.view().owning_proc)
    &&& pre.ctn_mp.dom().contains(thread.view().owning_container)
    &&& pre.thr_mp.dom().contains(thread_ptr)
    &&& thread.locking_thread() is None
    &&& thread.view().syscall_progress.view() is None
    &&& !thread.being_killed()
    &&& thread.view().state == (ThreadState::RUNNING { cpu_id })
    &&& edp_idx_valid(endpoint_index)
    &&& thread.view().endpoint_descriptors.view()[endpoint_index as int] == Some(endpoint_ptr)
    &&& pre.ep_mp.dom().contains(endpoint_ptr)
    &&& endpoint.locking_thread() is None
    &&& !endpoint.view().queue.view().contains(thread_ptr)
    &&& waiting_state.is_endpoint_waiting()
    &&& endpoint.view().queue.view().len() == 0 || (endpoint.view().queue_state is SEND) == waiting_state.is_endpoint_send_waiting()
    &&& forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
        index_valid(NUM_CPUS, i) ==> {
            let a = pre.cpu_arr.spec_index(i).value.view().view();
            let b = post.cpu_arr.spec_index(i).value.view().view();
            &&& b.owning_container == a.owning_container
            &&& b.state == if i == cpu_id { CpuState::Idle } else { a.state }
            &&& b.current_process == if i == cpu_id { None } else { a.current_process }
            &&& b.current_thread == if i == cpu_id { None } else { a.current_thread }
            &&& post.cpu_arr.spec_index(i).value.killer_info() == pre.cpu_arr.spec_index(i).value.killer_info()
        }
    &&& post.thr_mp.dom() == pre.thr_mp.dom()
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)]
        pre.thr_mp.dom().contains(t) ==> {
            let a = pre.thr_mp.spec_index(t).view();
            let b = post.thr_mp.spec_index(t).view();
            &&& b.state == if t == thread_ptr { waiting_state } else { a.state }
            &&& b.caller == a.caller
            &&& b.callee == a.callee
            &&& b.owning_container == a.owning_container
            &&& b.owning_proc == a.owning_proc
            &&& b.last_cpu == a.last_cpu
            &&& b.quota_4k == a.quota_4k
            &&& b.quota_2m == a.quota_2m
            &&& b.quota_1g == a.quota_1g
            &&& b.endpoint_descriptors.view() == a.endpoint_descriptors.view()
            &&& b.blocking_endpoint_ptr == if t == thread_ptr { Some(endpoint_ptr) } else { a.blocking_endpoint_ptr }
            &&& b.ipc_payload == if t == thread_ptr { payload } else { a.ipc_payload }
            &&& b.error_code == a.error_code
            &&& (t == thread_ptr ==> b.trap_frame.is_some() && *b.trap_frame.get_some_0() == regs)
            &&& (t != thread_ptr ==> b.trap_frame == a.trap_frame)
            &&& b.syscall_progress.view() == a.syscall_progress.view()
            &&& post.thr_mp.spec_index(t).being_killed() == pre.thr_mp.spec_index(t).being_killed()
        }
    &&& post.ep_mp.dom() == pre.ep_mp.dom()
    &&& forall|e: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(e)]
        pre.ep_mp.dom().contains(e) ==> {
            let a = pre.ep_mp.spec_index(e);
            let b = post.ep_mp.spec_index(e);
            &&& b.view().queue.view() == if e == endpoint_ptr { a.view().queue.view().push(thread_ptr) } else { a.view().queue.view() }
            &&& b.view().queue_state == if e == endpoint_ptr && a.view().queue.view().len() == 0 {
                match waiting_state { ThreadState::SENDING | ThreadState::CALLING => EndpointState::SEND, _ => EndpointState::RECEIVE }
            } else { a.view().queue_state }
            &&& b.view().owning_threads.view() == a.view().owning_threads.view()
            &&& b.view().owning_container == a.view().owning_container
            &&& b.being_killed() == a.being_killed()
        }
}

#[verifier::opaque]
/// The live caller running on `cpu_id` hands its CPU to the live head `callee_ptr` of the endpoint at
/// `endpoint_index`, a receive-call waiter of its container: the callee is dequeued, records the caller, and
/// runs on `cpu_id` with its saved frame restored; the caller saves `regs` and waits for the reply; the
/// callee's process PCID entry `flushed_pcid` is flushed.
pub open spec fn kernel_ipc_call_handoff_fields(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, caller_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    callee_ptr: RwLockThreadPtr, regs: Registers, flushed_pcid: Option<Pcid>,
) -> bool {
    let cpu = pre.cpu_arr.spec_index(cpu_id).value.view().view();
    let caller = pre.thr_mp.spec_index(caller_ptr);
    let callee = pre.thr_mp.spec_index(callee_ptr);
    let endpoint = pre.ep_mp.spec_index(endpoint_ptr);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& post.cpu_op.view().view() == pre.cpu_op.view().view()
    &&& forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)]
        pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).locking_thread() == pre.ctn_mp.spec_index(p).locking_thread()
    &&& forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
        pre.prc_mp.dom().contains(p) ==> post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread()
    &&& forall|p: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(p)]
        pre.thr_mp.dom().contains(p) ==> post.thr_mp.spec_index(p).locking_thread() == pre.thr_mp.spec_index(p).locking_thread()
    &&& forall|p: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(p)]
        pre.ep_mp.dom().contains(p) ==> post.ep_mp.spec_index(p).locking_thread() == pre.ep_mp.spec_index(p).locking_thread()
    &&& forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
        pre.pt_mp.dom().contains(p) ==> post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread()
    &&& forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
        pre.it_mp.dom().contains(p) ==> post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread()
    &&& forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
        index_valid(NUM_CPUS, i) ==> post.cpu_arr.spec_index(i).value.locking_thread() == pre.cpu_arr.spec_index(i).value.locking_thread()
    &&& kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view())
    &&& kernel_iommu_table_nonlock_fields_unchanged(pre.it_mp, post.it_mp)
    &&& kernel_process_nonlock_fields_unchanged(pre.prc_mp, post.prc_mp)
    &&& kernel_container_nonlock_fields_and_quotas_unchanged(pre, post)
    &&& post.irt.view().owners() == pre.irt.view().owners()
    &&& post.irt.view().iommu_roots() == pre.irt.view().iommu_roots()
    &&& post.iommu_tlb.view() == pre.iommu_tlb.view()
    &&& post.dflt_pt == pre.dflt_pt
    &&& post.cpu_tlb.view() == match flushed_pcid {
        Some(pcid) => pre.cpu_tlb.view().insert((cpu_id, pcid), post.cpu_tlb.spec_index((cpu_id, pcid))),
        None => pre.cpu_tlb.view(),
    }
    &&& flushed_pcid matches Some(pcid) ==> cpu_tlb_within_may_cache(*post, cpu_id, pcid, post.cpu_tlb.spec_index((cpu_id, pcid)))
    &&& pre.cpu_arr.spec_index(cpu_id).value.locking_thread() is None
    &&& cpu.state is Running
    &&& cpu.current_thread == Some(caller_ptr)
    &&& cpu.current_process == Some(caller.view().owning_proc)
    &&& pre.prc_mp.dom().contains(caller.view().owning_proc)
    &&& pre.ctn_mp.dom().contains(caller.view().owning_container)
    &&& pre.thr_mp.dom().contains(caller_ptr)
    &&& caller.locking_thread() is None
    &&& caller.view().syscall_progress.view() is None
    &&& !caller.being_killed()
    &&& caller.view().state == (ThreadState::RUNNING { cpu_id })
    &&& caller.view().callee is None
    &&& edp_idx_valid(endpoint_index)
    &&& caller.view().endpoint_descriptors.view()[endpoint_index as int] == Some(endpoint_ptr)
    &&& pre.ep_mp.dom().contains(endpoint_ptr)
    &&& endpoint.locking_thread() is None
    &&& !endpoint.view().queue.view().contains(caller_ptr)
    &&& endpoint.view().queue.view().len() > 0
    &&& endpoint.view().queue.view()[0] == callee_ptr
    &&& endpoint.view().queue_state is RECEIVE
    &&& callee_ptr != caller_ptr
    &&& pre.thr_mp.dom().contains(callee_ptr)
    &&& callee.locking_thread() is None
    &&& !callee.being_killed()
    &&& callee.view().state is RECEIVING_CALL
    &&& callee.view().caller is None
    &&& callee.view().callee is None
    &&& callee.view().blocking_endpoint_ptr == Some(endpoint_ptr)
    &&& callee.view().owning_container == caller.view().owning_container
    &&& pre.prc_mp.dom().contains(callee.view().owning_proc)
    &&& forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
        index_valid(NUM_CPUS, i) ==> {
            let a = pre.cpu_arr.spec_index(i).value.view().view();
            let b = post.cpu_arr.spec_index(i).value.view().view();
            &&& b.owning_container == a.owning_container
            &&& b.state == a.state
            &&& b.current_process == if i == cpu_id { Some(callee.view().owning_proc) } else { a.current_process }
            &&& b.current_thread == if i == cpu_id { Some(callee_ptr) } else { a.current_thread }
            &&& post.cpu_arr.spec_index(i).value.killer_info() == pre.cpu_arr.spec_index(i).value.killer_info()
        }
    &&& post.thr_mp.dom() == pre.thr_mp.dom()
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)]
        pre.thr_mp.dom().contains(t) ==> {
            let a = pre.thr_mp.spec_index(t).view();
            let b = post.thr_mp.spec_index(t).view();
            &&& b.state == if t == callee_ptr { ThreadState::RUNNING { cpu_id } } else if t == caller_ptr { ThreadState::WAITING_REPLY } else { a.state }
            &&& b.caller == if t == callee_ptr { Some(caller_ptr) } else { a.caller }
            &&& b.callee == if t == caller_ptr { Some(callee_ptr) } else { a.callee }
            &&& b.owning_container == a.owning_container
            &&& b.owning_proc == a.owning_proc
            &&& b.last_cpu == if t == callee_ptr { cpu_id } else { a.last_cpu }
            &&& b.quota_4k == a.quota_4k
            &&& b.quota_2m == a.quota_2m
            &&& b.quota_1g == a.quota_1g
            &&& b.endpoint_descriptors.view() == a.endpoint_descriptors.view()
            &&& b.blocking_endpoint_ptr == if t == callee_ptr { None } else { a.blocking_endpoint_ptr }
            &&& b.ipc_payload == a.ipc_payload
            &&& b.error_code == a.error_code
            &&& (t == callee_ptr ==> b.trap_frame.is_none())
            &&& (t == caller_ptr ==> b.trap_frame.is_some() && *b.trap_frame.get_some_0() == regs)
            &&& (t != callee_ptr && t != caller_ptr ==> b.trap_frame == a.trap_frame)
            &&& b.syscall_progress.view() == a.syscall_progress.view()
            &&& post.thr_mp.spec_index(t).being_killed() == pre.thr_mp.spec_index(t).being_killed()
        }
    &&& post.ep_mp.dom() == pre.ep_mp.dom()
    &&& forall|e: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(e)]
        pre.ep_mp.dom().contains(e) ==> {
            let a = pre.ep_mp.spec_index(e);
            let b = post.ep_mp.spec_index(e);
            &&& b.view().queue.view() == if e == endpoint_ptr { a.view().queue.view().skip(1) } else { a.view().queue.view() }
            &&& b.view().queue_state == a.view().queue_state
            &&& b.view().owning_threads.view() == a.view().owning_threads.view()
            &&& b.view().owning_container == a.view().owning_container
            &&& b.being_killed() == a.being_killed()
        }
}

#[verifier::opaque]
/// The live receive-call thread running on `cpu_id` accepts the live calling head `caller_ptr` of the endpoint
/// at `endpoint_index`, a caller of its container: the caller is dequeued and waits for the reply with the
/// callee recorded, and the callee records the caller and keeps running.
pub open spec fn kernel_ipc_accept_call_fields(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    caller_ptr: RwLockThreadPtr,
) -> bool {
    let cpu = pre.cpu_arr.spec_index(cpu_id).value.view().view();
    let callee = pre.thr_mp.spec_index(callee_ptr);
    let caller = pre.thr_mp.spec_index(caller_ptr);
    let endpoint = pre.ep_mp.spec_index(endpoint_ptr);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& *post == (KernelK { cpu_arr: post.cpu_arr, cpu_op: post.cpu_op, thr_mp: post.thr_mp, ep_mp: post.ep_mp, ..*pre })
    &&& post.cpu_op.view().view() == pre.cpu_op.view().view()
    &&& forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
        index_valid(NUM_CPUS, i) ==> post.cpu_arr.spec_index(i).value.locking_thread() == pre.cpu_arr.spec_index(i).value.locking_thread()
    &&& forall|p: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(p)]
        pre.thr_mp.dom().contains(p) ==> post.thr_mp.spec_index(p).locking_thread() == pre.thr_mp.spec_index(p).locking_thread()
    &&& forall|p: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(p)]
        pre.ep_mp.dom().contains(p) ==> post.ep_mp.spec_index(p).locking_thread() == pre.ep_mp.spec_index(p).locking_thread()
    &&& forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
        index_valid(NUM_CPUS, i) ==> {
            let a = pre.cpu_arr.spec_index(i).value.view().view();
            let b = post.cpu_arr.spec_index(i).value.view().view();
            &&& b.owning_container == a.owning_container
            &&& b.state == a.state
            &&& b.current_process == a.current_process
            &&& b.current_thread == a.current_thread
            &&& post.cpu_arr.spec_index(i).value.killer_info() == pre.cpu_arr.spec_index(i).value.killer_info()
        }
    &&& pre.cpu_arr.spec_index(cpu_id).value.locking_thread() is None
    &&& cpu.state is Running
    &&& cpu.current_thread == Some(callee_ptr)
    &&& cpu.current_process == Some(callee.view().owning_proc)
    &&& pre.prc_mp.dom().contains(callee.view().owning_proc)
    &&& pre.ctn_mp.dom().contains(callee.view().owning_container)
    &&& pre.thr_mp.dom().contains(callee_ptr)
    &&& callee.locking_thread() is None
    &&& callee.view().syscall_progress.view() is None
    &&& !callee.being_killed()
    &&& callee.view().state == (ThreadState::RUNNING { cpu_id })
    &&& callee.view().caller is None
    &&& callee.view().callee is None
    &&& edp_idx_valid(endpoint_index)
    &&& callee.view().endpoint_descriptors.view()[endpoint_index as int] == Some(endpoint_ptr)
    &&& pre.ep_mp.dom().contains(endpoint_ptr)
    &&& endpoint.locking_thread() is None
    &&& !endpoint.view().queue.view().contains(callee_ptr)
    &&& endpoint.view().queue.view().len() > 0
    &&& endpoint.view().queue.view()[0] == caller_ptr
    &&& endpoint.view().queue_state is SEND
    &&& caller_ptr != callee_ptr
    &&& pre.thr_mp.dom().contains(caller_ptr)
    &&& caller.locking_thread() is None
    &&& !caller.being_killed()
    &&& caller.view().state is CALLING
    &&& caller.view().callee is None
    &&& caller.view().blocking_endpoint_ptr == Some(endpoint_ptr)
    &&& caller.view().owning_container == callee.view().owning_container
    &&& post.thr_mp.dom() == pre.thr_mp.dom()
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)]
        pre.thr_mp.dom().contains(t) ==> {
            let a = pre.thr_mp.spec_index(t).view();
            let b = post.thr_mp.spec_index(t).view();
            &&& b.state == if t == caller_ptr { ThreadState::WAITING_REPLY } else { a.state }
            &&& b.caller == if t == callee_ptr { Some(caller_ptr) } else { a.caller }
            &&& b.callee == if t == caller_ptr { Some(callee_ptr) } else { a.callee }
            &&& b.owning_container == a.owning_container
            &&& b.owning_proc == a.owning_proc
            &&& b.last_cpu == a.last_cpu
            &&& b.quota_4k == a.quota_4k
            &&& b.quota_2m == a.quota_2m
            &&& b.quota_1g == a.quota_1g
            &&& b.endpoint_descriptors.view() == a.endpoint_descriptors.view()
            &&& b.blocking_endpoint_ptr == if t == caller_ptr { None } else { a.blocking_endpoint_ptr }
            &&& b.ipc_payload == a.ipc_payload
            &&& b.error_code == a.error_code
            &&& b.trap_frame == a.trap_frame
            &&& b.syscall_progress.view() == a.syscall_progress.view()
            &&& post.thr_mp.spec_index(t).being_killed() == pre.thr_mp.spec_index(t).being_killed()
        }
    &&& post.ep_mp.dom() == pre.ep_mp.dom()
    &&& forall|e: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(e)]
        pre.ep_mp.dom().contains(e) ==> {
            let a = pre.ep_mp.spec_index(e);
            let b = post.ep_mp.spec_index(e);
            &&& b.view().queue.view() == if e == endpoint_ptr { a.view().queue.view().skip(1) } else { a.view().queue.view() }
            &&& b.view().queue_state == a.view().queue_state
            &&& b.view().owning_threads.view() == a.view().owning_threads.view()
            &&& b.view().owning_container == a.view().owning_container
            &&& b.being_killed() == a.being_killed()
        }
}

#[verifier::opaque]
/// The live callee running on `cpu_id` replies to its recorded live caller `caller_ptr` and hands it the CPU:
/// the caller resumes with its saved frame on `cpu_id`, the callee saves `regs`, drops the caller, and waits
/// for the next call on the endpoint at `endpoint_index`; the caller's process PCID entry `flushed_pcid` is
/// flushed.
pub open spec fn kernel_ipc_reply_handoff_fields(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    caller_ptr: RwLockThreadPtr, regs: Registers, flushed_pcid: Option<Pcid>,
) -> bool {
    let cpu = pre.cpu_arr.spec_index(cpu_id).value.view().view();
    let callee = pre.thr_mp.spec_index(callee_ptr);
    let caller = pre.thr_mp.spec_index(caller_ptr);
    let endpoint = pre.ep_mp.spec_index(endpoint_ptr);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& post.cpu_op.view().view() == pre.cpu_op.view().view()
    &&& forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)]
        pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).locking_thread() == pre.ctn_mp.spec_index(p).locking_thread()
    &&& forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
        pre.prc_mp.dom().contains(p) ==> post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread()
    &&& forall|p: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(p)]
        pre.thr_mp.dom().contains(p) ==> post.thr_mp.spec_index(p).locking_thread() == pre.thr_mp.spec_index(p).locking_thread()
    &&& forall|p: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(p)]
        pre.ep_mp.dom().contains(p) ==> post.ep_mp.spec_index(p).locking_thread() == pre.ep_mp.spec_index(p).locking_thread()
    &&& forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
        pre.pt_mp.dom().contains(p) ==> post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread()
    &&& forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
        pre.it_mp.dom().contains(p) ==> post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread()
    &&& forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
        index_valid(NUM_CPUS, i) ==> post.cpu_arr.spec_index(i).value.locking_thread() == pre.cpu_arr.spec_index(i).value.locking_thread()
    &&& kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view())
    &&& kernel_iommu_table_nonlock_fields_unchanged(pre.it_mp, post.it_mp)
    &&& kernel_process_nonlock_fields_unchanged(pre.prc_mp, post.prc_mp)
    &&& kernel_container_nonlock_fields_and_quotas_unchanged(pre, post)
    &&& post.irt.view().owners() == pre.irt.view().owners()
    &&& post.irt.view().iommu_roots() == pre.irt.view().iommu_roots()
    &&& post.iommu_tlb.view() == pre.iommu_tlb.view()
    &&& post.dflt_pt == pre.dflt_pt
    &&& post.cpu_tlb.view() == match flushed_pcid {
        Some(pcid) => pre.cpu_tlb.view().insert((cpu_id, pcid), post.cpu_tlb.spec_index((cpu_id, pcid))),
        None => pre.cpu_tlb.view(),
    }
    &&& flushed_pcid matches Some(pcid) ==> cpu_tlb_within_may_cache(*post, cpu_id, pcid, post.cpu_tlb.spec_index((cpu_id, pcid)))
    &&& pre.cpu_arr.spec_index(cpu_id).value.locking_thread() is None
    &&& cpu.state is Running
    &&& cpu.current_thread == Some(callee_ptr)
    &&& cpu.current_process == Some(callee.view().owning_proc)
    &&& pre.prc_mp.dom().contains(callee.view().owning_proc)
    &&& pre.ctn_mp.dom().contains(callee.view().owning_container)
    &&& pre.thr_mp.dom().contains(callee_ptr)
    &&& callee.locking_thread() is None
    &&& callee.view().syscall_progress.view() is None
    &&& !callee.being_killed()
    &&& callee.view().state == (ThreadState::RUNNING { cpu_id })
    &&& callee.view().caller == Some(caller_ptr)
    &&& callee.view().callee is None
    &&& edp_idx_valid(endpoint_index)
    &&& callee.view().endpoint_descriptors.view()[endpoint_index as int] == Some(endpoint_ptr)
    &&& pre.ep_mp.dom().contains(endpoint_ptr)
    &&& endpoint.locking_thread() is None
    &&& !endpoint.view().queue.view().contains(callee_ptr)
    &&& endpoint.view().queue.view().len() == 0 || endpoint.view().queue_state is RECEIVE
    &&& caller_ptr != callee_ptr
    &&& pre.thr_mp.dom().contains(caller_ptr)
    &&& caller.locking_thread() is None
    &&& !caller.being_killed()
    &&& caller.view().state is WAITING_REPLY
    &&& caller.view().callee == Some(callee_ptr)
    &&& caller.view().owning_container == callee.view().owning_container
    &&& pre.prc_mp.dom().contains(caller.view().owning_proc)
    &&& forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
        index_valid(NUM_CPUS, i) ==> {
            let a = pre.cpu_arr.spec_index(i).value.view().view();
            let b = post.cpu_arr.spec_index(i).value.view().view();
            &&& b.owning_container == a.owning_container
            &&& b.state == a.state
            &&& b.current_process == if i == cpu_id { Some(caller.view().owning_proc) } else { a.current_process }
            &&& b.current_thread == if i == cpu_id { Some(caller_ptr) } else { a.current_thread }
            &&& post.cpu_arr.spec_index(i).value.killer_info() == pre.cpu_arr.spec_index(i).value.killer_info()
        }
    &&& post.thr_mp.dom() == pre.thr_mp.dom()
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)]
        pre.thr_mp.dom().contains(t) ==> {
            let a = pre.thr_mp.spec_index(t).view();
            let b = post.thr_mp.spec_index(t).view();
            &&& b.state == if t == caller_ptr { ThreadState::RUNNING { cpu_id } } else if t == callee_ptr { ThreadState::RECEIVING_CALL } else { a.state }
            &&& b.caller == if t == callee_ptr { None } else { a.caller }
            &&& b.callee == if t == caller_ptr { None } else { a.callee }
            &&& b.owning_container == a.owning_container
            &&& b.owning_proc == a.owning_proc
            &&& b.last_cpu == if t == caller_ptr { cpu_id } else { a.last_cpu }
            &&& b.quota_4k == a.quota_4k
            &&& b.quota_2m == a.quota_2m
            &&& b.quota_1g == a.quota_1g
            &&& b.endpoint_descriptors.view() == a.endpoint_descriptors.view()
            &&& b.blocking_endpoint_ptr == if t == callee_ptr { Some(endpoint_ptr) } else { a.blocking_endpoint_ptr }
            &&& b.ipc_payload == if t == callee_ptr { IPCPayLoad::Empty } else { a.ipc_payload }
            &&& b.error_code == a.error_code
            &&& (t == caller_ptr ==> b.trap_frame.is_none())
            &&& (t == callee_ptr ==> b.trap_frame.is_some() && *b.trap_frame.get_some_0() == regs)
            &&& (t != caller_ptr && t != callee_ptr ==> b.trap_frame == a.trap_frame)
            &&& b.syscall_progress.view() == a.syscall_progress.view()
            &&& post.thr_mp.spec_index(t).being_killed() == pre.thr_mp.spec_index(t).being_killed()
        }
    &&& post.ep_mp.dom() == pre.ep_mp.dom()
    &&& forall|e: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(e)]
        pre.ep_mp.dom().contains(e) ==> {
            let a = pre.ep_mp.spec_index(e);
            let b = post.ep_mp.spec_index(e);
            &&& b.view().queue.view() == if e == endpoint_ptr { a.view().queue.view().push(callee_ptr) } else { a.view().queue.view() }
            &&& b.view().queue_state == if e == endpoint_ptr && a.view().queue.view().len() == 0 { EndpointState::RECEIVE } else { a.view().queue_state }
            &&& b.view().owning_threads.view() == a.view().owning_threads.view()
            &&& b.view().owning_container == a.view().owning_container
            &&& b.being_killed() == a.being_killed()
        }
}

#[verifier::opaque]
/// The live head `peer_thread_ptr` of the endpoint at `endpoint_index`, waiting opposite to the live caller
/// running on `cpu_id`, is dequeued and scheduled with `peer_result`; with `cpu_transfer == Some((cpu, receiver))`
/// that Off CPU also moves to the receiver's container, and with `pci_transfer == Some((bdf, sender, receiver))`
/// that PCI function moves from the sender to the receiver process, detached, while every other function stays attached
/// exactly when it was; the sender's IOMMU table is unlocked at the start when the function is attached. Detaching an attached function empties
/// the sender table's old DID domain; detaching its anchor re-anchors the table as `pci_handoff_table_did` states.
/// Only that table's DID changes; every IOMMU table keeps its present mappings.
pub open spec fn kernel_ipc_rendezvous_fields(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, caller_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, peer_thread_ptr: RwLockThreadPtr, peer_result: RetValueType,
    cpu_transfer: Option<(CpuId, RwLockThreadPtr)>, pci_transfer: Option<(PciBdf, RwLockProcessPtr, RwLockProcessPtr)>,
) -> bool {
    let cpu = pre.cpu_arr.spec_index(cpu_id).value.view().view();
    let caller = pre.thr_mp.spec_index(caller_thread_ptr);
    let peer = pre.thr_mp.spec_index(peer_thread_ptr);
    let endpoint = pre.ep_mp.spec_index(endpoint_ptr);
    let peer_container = peer.view().owning_container;
    let wake_cpu = if peer_container == caller.view().owning_container { cpu_id } else { peer.view().last_cpu };
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& pre.cpu_arr.spec_index(cpu_id).value.locking_thread() is None
    &&& cpu.state is Running
    &&& cpu.current_thread == Some(caller_thread_ptr)
    &&& cpu.current_process == Some(caller.view().owning_proc)
    &&& pre.prc_mp.dom().contains(caller.view().owning_proc)
    &&& pre.thr_mp.dom().contains(caller_thread_ptr)
    &&& caller.locking_thread() is None
    &&& caller.view().syscall_progress.view() is None
    &&& !caller.being_killed()
    &&& caller.view().state == (ThreadState::RUNNING { cpu_id })
    &&& edp_idx_valid(endpoint_index)
    &&& caller.view().endpoint_descriptors.view()[endpoint_index as int] == Some(endpoint_ptr)
    &&& pre.ep_mp.dom().contains(endpoint_ptr)
    &&& endpoint.locking_thread() is None
    &&& !endpoint.view().queue.view().contains(caller_thread_ptr)
    &&& waiting_state.is_endpoint_waiting()
    &&& endpoint.view().queue.view().len() > 0
    &&& endpoint.view().queue.view()[0] == peer_thread_ptr
    &&& (endpoint.view().queue_state is SEND) != waiting_state.is_endpoint_send_waiting()
    &&& pre.thr_mp.dom().contains(peer_thread_ptr)
    &&& peer_thread_ptr != caller_thread_ptr
    &&& peer.locking_thread() is None
    &&& !peer.being_killed()
    &&& peer.view().state.is_endpoint_waiting()
    &&& peer.view().blocking_endpoint_ptr == Some(endpoint_ptr)
    &&& pre.ctn_mp.dom().contains(peer_container)
    &&& pre.ctn_mp.dom().contains(caller.view().owning_container)
    &&& (cpu_transfer is Some ==> index_valid(NUM_CPUS, cpu_transfer.unwrap().0) && pre.thr_mp.dom().contains(cpu_transfer.unwrap().1))
    &&& cpu_transfer is Some ==> pre.cpu_arr.spec_index(cpu_transfer.unwrap().0).value.locking_thread() is None
    &&& kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view())
    &&& pci_transfer is None ==> {
        &&& kernel_iommu_table_nonlock_fields_unchanged(pre.it_mp, post.it_mp)
        &&& kernel_process_nonlock_fields_unchanged(pre.prc_mp, post.prc_mp)
        &&& post.irt.view().owners() == pre.irt.view().owners()
        &&& post.irt.view().iommu_roots() == pre.irt.view().iommu_roots()
        &&& post.iommu_tlb.view() == pre.iommu_tlb.view()
    }
    &&& pci_transfer matches Some((bdf, sender, receiver)) ==> {
        let sender_table = pre.prc_mp.spec_index(sender).view().iommu_table;
        let attached = iommu_roots_attached(pre.irt.view().iommu_roots());
        let old_did = match sender_table { Some(t) => pre.it_mp.spec_index(t).view().did, None => None };
        &&& pci_bdf_valid(bdf.0, bdf.1, bdf.2)
        &&& pre.prc_mp.dom().contains(sender)
        &&& pre.prc_mp.dom().contains(receiver)
        &&& sender != receiver
        &&& !pre.prc_mp.spec_index(sender).view().zombie
        &&& sender_table matches Some(t) ==> attached[bdf.0 as int][bdf.1 as int][bdf.2 as int] ==> pre.it_mp.dom().contains(t) && pre.it_mp.spec_index(t).locking_thread() is None
        &&& post.irt.view().owners() == seq3_update(pre.irt.view().owners(), bdf.0 as int, bdf.1 as int, bdf.2 as int, receiver)
        &&& forall|b: usize, d: usize, f: usize| #![trigger post.irt.view().spec_index_iommu_root(b, d, f)] pci_bdf_valid(b, d, f)
            ==> (post.irt.view().spec_index_iommu_root(b, d, f) is Some) == ((b, d, f) != bdf && pre.irt.view().spec_index_iommu_root(b, d, f) is Some)
        &&& post.iommu_tlb.view() == if attached[bdf.0 as int][bdf.1 as int][bdf.2 as int] && old_did is Some {
            pre.iommu_tlb.view().insert(old_did->Some_0, post.iommu_tlb.spec_index(old_did->Some_0))
        } else { pre.iommu_tlb.view() }
        &&& attached[bdf.0 as int][bdf.1 as int][bdf.2 as int] && old_did is Some ==> iommu_tlb_within_may_cache(*post, old_did->Some_0, post.iommu_tlb.spec_index(old_did->Some_0))
        &&& sender_table matches Some(t) ==> pci_handoff_table_did(pre.irt.view().owners(), attached, sender, bdf, old_did, post.it_mp.spec_index(t).view().did)
        &&& post.it_mp.dom() == pre.it_mp.dom()
        &&& forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
            pre.it_mp.dom().contains(p) ==> {
                let before = pre.it_mp.spec_index(p).view();
                let after = post.it_mp.spec_index(p).view();
                &&& sender_table != Some(p) ==> after.did == before.did
                &&& after.mapping_4k().filter_keys(|va: VAddr| after.mapping_4k().spec_index(va).present) == before.mapping_4k().filter_keys(|va: VAddr| before.mapping_4k().spec_index(va).present)
                &&& after.mapping_2m().filter_keys(|va: VAddr| after.mapping_2m().spec_index(va).present) == before.mapping_2m().filter_keys(|va: VAddr| before.mapping_2m().spec_index(va).present)
                &&& after.mapping_1g().filter_keys(|va: VAddr| after.mapping_1g().spec_index(va).present) == before.mapping_1g().filter_keys(|va: VAddr| before.mapping_1g().spec_index(va).present)
            }
        &&& post.prc_mp.dom() == pre.prc_mp.dom()
        &&& forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) ==> {
                let a = pre.prc_mp.spec_index(p);
                let b = post.prc_mp.spec_index(p);
                let pci = a.view_ghost().owned_pci_functions.view();
                &&& b.view().zombie == a.view().zombie
                &&& b.view().pagetable == a.view().pagetable
                &&& b.view().iommu_table == a.view().iommu_table
                &&& b.view_ghost().owned_pci_functions.view() == if p == sender { pci.remove(bdf) } else if p == receiver { pci.insert(bdf) } else { pci }
                &&& b.view().quota_4k == a.view().quota_4k
                &&& b.view().quota_2m == a.view().quota_2m
                &&& b.view().quota_1g == a.view().quota_1g
                &&& b.view().children.view() == a.view().children.view()
                &&& b.view_rodata().view().parent == a.view_rodata().view().parent
                &&& b.view_rodata().view().depth == a.view_rodata().view().depth
                &&& b.view_rodata().view().pcid == a.view_rodata().view().pcid
                &&& b.view_rodata().view().owning_container == a.view_rodata().view().owning_container
                &&& b.view_ghost().uppertree_seq.view() == a.view_ghost().uppertree_seq.view()
                &&& b.view_ghost().subtree_set.view() == a.view_ghost().subtree_set.view()
                &&& b.being_killed() == a.being_killed()
                &&& b.view().owned_threads.view() == a.view().owned_threads.view()
            }
    }
    &&& post.cpu_tlb.view() == pre.cpu_tlb.view()
    &&& post.dflt_pt == pre.dflt_pt
    &&& forall|c: RwLockContainerPtr| #![trigger post.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(c))]
        pre.ctn_mp.dom().contains(c) ==> cpu_offline_requests_of(post.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(c))) == cpu_offline_requests_of(pre.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(c)))
    &&& forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
        index_valid(NUM_CPUS, i) ==> {
            let a = pre.cpu_arr.spec_index(i).value.view().view();
            let b = post.cpu_arr.spec_index(i).value.view().view();
            &&& b.owning_container == if cpu_transfer is Some && i == cpu_transfer.unwrap().0 {
                pre.thr_mp.spec_index(cpu_transfer.unwrap().1).view().owning_container
            } else { a.owning_container }
            &&& b.state == a.state
            &&& b.current_process == a.current_process
            &&& b.current_thread == a.current_thread
            &&& post.cpu_arr.spec_index(i).value.killer_info() == pre.cpu_arr.spec_index(i).value.killer_info()
        }
    &&& post.ctn_mp.dom() == pre.ctn_mp.dom()
    &&& forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)]
        pre.ctn_mp.dom().contains(c) ==> {
            let a = pre.ctn_mp.spec_index(c);
            let b = post.ctn_mp.spec_index(c);
            let a_ro = a.view_rodata().view();
            let b_ro = b.view_rodata().view();
            &&& b.view().children.view() == a.view().children.view()
            &&& b.view_ghost().uppertree_seq.view() == a.view_ghost().uppertree_seq.view()
            &&& b.view_ghost().subtree_set.view() == a.view_ghost().subtree_set.view()
            &&& b.view().root_process == a.view().root_process
            &&& b.view().zombie == a.view().zombie
            &&& b.view_ghost().owned_processes.view() == a.view_ghost().owned_processes.view()
            &&& b.view_ghost().owned_threads.view() == a.view_ghost().owned_threads.view()
            &&& b.view_ghost().owned_endpoints.view() == a.view_ghost().owned_endpoints.view()
            &&& b.view().owned_pages.view() == a.view().owned_pages.view()
            &&& b_ro.parent == a_ro.parent
            &&& b_ro.depth == a_ro.depth
            &&& b_ro.scheduler == a_ro.scheduler
            &&& b_ro.cpu_set == a_ro.cpu_set
            &&& b.being_killed() == a.being_killed()
        }
    &&& forall|c: RwLockContainerPtr| #![trigger post.sched_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().scheduler)]
        pre.ctn_mp.dom().contains(c) ==> {
            let queue = scheduler_shards_of(pre.sched_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().scheduler));
            scheduler_shards_of(post.sched_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().scheduler)) == if c == peer_container { queue.update(wake_cpu as int, queue[wake_cpu as int].push(peer_thread_ptr)) } else { queue }
        }
    &&& forall|c: RwLockContainerPtr| #![trigger post.pcid_allc_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator)]
        pre.ctn_mp.dom().contains(c) ==> PcidAllocator::free_pcids(post.pcid_allc_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator).view().ref_counters.view())
            == PcidAllocator::free_pcids(pre.pcid_allc_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator).view().ref_counters.view())
    &&& forall|c: RwLockContainerPtr| #![trigger post.allc_4k_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k)]
        pre.ctn_mp.dom().contains(c) ==> post.allc_4k_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k).quota.view().view()
            == pre.allc_4k_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k).quota.view().view()
    &&& forall|c: RwLockContainerPtr| #![trigger post.allc_2m_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_2m)]
        pre.ctn_mp.dom().contains(c) ==> post.allc_2m_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_2m).quota.view().view()
            == pre.allc_2m_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_2m).quota.view().view()
    &&& forall|c: RwLockContainerPtr| #![trigger post.allc_1g_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g)]
        pre.ctn_mp.dom().contains(c) ==> post.allc_1g_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g).quota.view().view()
            == pre.allc_1g_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g).quota.view().view()
    &&& post.thr_mp.dom() == pre.thr_mp.dom()
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)]
        pre.thr_mp.dom().contains(t) ==> {
            let a = pre.thr_mp.spec_index(t).view();
            let b = post.thr_mp.spec_index(t).view();
            &&& b.state == if t == peer_thread_ptr { ThreadState::SCHEDULED { cpu_id: wake_cpu } } else { a.state }
            &&& b.caller == a.caller
            &&& b.callee == a.callee
            &&& b.owning_container == a.owning_container
            &&& b.owning_proc == a.owning_proc
            &&& b.last_cpu == a.last_cpu
            &&& b.quota_4k == a.quota_4k
            &&& b.quota_2m == a.quota_2m
            &&& b.quota_1g == a.quota_1g
            &&& b.endpoint_descriptors.view() == a.endpoint_descriptors.view()
            &&& b.blocking_endpoint_ptr == if t == peer_thread_ptr { None } else { a.blocking_endpoint_ptr }
            &&& b.ipc_payload == if t == peer_thread_ptr { IPCPayLoad::Empty } else { a.ipc_payload }
            &&& b.error_code == if t == peer_thread_ptr { Some(peer_result) } else { a.error_code }
            &&& b.trap_frame == a.trap_frame
            &&& b.syscall_progress.view() == a.syscall_progress.view()
            &&& post.thr_mp.spec_index(t).being_killed() == pre.thr_mp.spec_index(t).being_killed()
        }
    &&& post.ep_mp.dom() == pre.ep_mp.dom()
    &&& forall|e: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(e)]
        pre.ep_mp.dom().contains(e) ==> {
            let a = pre.ep_mp.spec_index(e);
            let b = post.ep_mp.spec_index(e);
            &&& b.view().queue.view() == if e == endpoint_ptr { a.view().queue.view().skip(1) } else { a.view().queue.view() }
            &&& b.view().queue_state == a.view().queue_state
            &&& b.view().owning_threads.view() == a.view().owning_threads.view()
            &&& b.view().owning_container == a.view().owning_container
            &&& b.being_killed() == a.being_killed()
        }
}
} // verus!
