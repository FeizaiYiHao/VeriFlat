use vstd::prelude::*;
use crate::*;

verus! {
#[verifier::opaque]
pub open spec fn kernel_endpoint_nonlock_fields_unchanged(pre: EndpointLockedMap, post: EndpointLockedMap) -> bool {
    &&& post.dom() == pre.dom()
    &&& forall|e: RwLockEndpointPtr| #![trigger post.spec_index(e)]
        pre.dom().contains(e) ==> {
            let a = pre.spec_index(e);
            let b = post.spec_index(e);
            &&& b.view().queue.view() == a.view().queue.view()
            &&& b.view().queue_state == a.view().queue_state
            &&& b.view().owning_threads.view() == a.view().owning_threads.view()
            &&& b.view().owning_container == a.view().owning_container
            &&& b.being_killed() == a.being_killed()
        }
}

/// The live process running on `cpu_id` takes `delta` 4K quota from its live container without overflow.
#[verifier::opaque]
pub open spec fn kernel_u_only_process_quota_4k_changed(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, delta: int) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let container = old_u.container_map.spec_index(container_ptr);
    let process = old_u.process_map.spec_index(process_ptr);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& cpu.current_process == Some(process_ptr)
    &&& cpu.owning_container == container_ptr
    &&& old_u.container_map.dom().contains(container_ptr)
    &&& !container.killed
    &&& !container.zombie
    &&& container.quota_4k >= delta
    &&& old_u.process_map.dom().contains(process_ptr)
    &&& !process.killed
    &&& process.quota_4k + delta <= usize::MAX
    &&& delta > 0
    &&& new_u == (KernelU {
        container_map: old_u.container_map.insert(container_ptr, ContainerU { quota_4k: (container.quota_4k as int - delta) as usize, ..container }),
        process_map: old_u.process_map.insert(process_ptr, ProcessU { quota_4k: (process.quota_4k as int + delta) as usize, ..process }),
        ..old_u
    })
}

/// The live process running on `cpu_id` moves `delta` 4K quota to its live running thread without overflow.
#[verifier::opaque]
pub open spec fn kernel_u_only_process2thread_quota_4k_changed(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, delta: int) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let process = old_u.process_map.spec_index(process_ptr);
    let thread = old_u.thread_map.spec_index(thread_ptr);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& cpu.current_process == Some(process_ptr)
    &&& cpu.current_thread == Some(thread_ptr)
    &&& old_u.process_map.dom().contains(process_ptr)
    &&& !process.killed
    &&& process.quota_4k >= delta
    &&& old_u.thread_map.dom().contains(thread_ptr)
    &&& !thread.killed
    &&& thread.quota_4k + delta <= usize::MAX
    &&& delta > 0
    &&& new_u == (KernelU {
        process_map: old_u.process_map.insert(process_ptr, ProcessU { quota_4k: (process.quota_4k as int - delta) as usize, ..process }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { quota_4k: (thread.quota_4k as int + delta) as usize, ..thread }),
        ..old_u
    })
}

/// The live process running on `cpu_id` takes `delta` 2M quota from its live container without overflow.
#[verifier::opaque]
pub open spec fn kernel_u_only_process_quota_2m_changed(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, delta: int) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let container = old_u.container_map.spec_index(container_ptr);
    let process = old_u.process_map.spec_index(process_ptr);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& cpu.current_process == Some(process_ptr)
    &&& cpu.owning_container == container_ptr
    &&& old_u.container_map.dom().contains(container_ptr)
    &&& !container.killed
    &&& !container.zombie
    &&& container.quota_2m >= delta
    &&& old_u.process_map.dom().contains(process_ptr)
    &&& !process.killed
    &&& process.quota_2m + delta <= usize::MAX
    &&& delta > 0
    &&& new_u == (KernelU {
        container_map: old_u.container_map.insert(container_ptr, ContainerU { quota_2m: (container.quota_2m as int - delta) as usize, ..container }),
        process_map: old_u.process_map.insert(process_ptr, ProcessU { quota_2m: (process.quota_2m as int + delta) as usize, ..process }),
        ..old_u
    })
}

/// The live process running on `cpu_id` moves `delta` 2M quota to its live running thread without overflow.
#[verifier::opaque]
pub open spec fn kernel_u_only_process2thread_quota_2m_changed(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, delta: int) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let process = old_u.process_map.spec_index(process_ptr);
    let thread = old_u.thread_map.spec_index(thread_ptr);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& cpu.current_process == Some(process_ptr)
    &&& cpu.current_thread == Some(thread_ptr)
    &&& old_u.process_map.dom().contains(process_ptr)
    &&& !process.killed
    &&& process.quota_2m >= delta
    &&& old_u.thread_map.dom().contains(thread_ptr)
    &&& !thread.killed
    &&& thread.quota_2m + delta <= usize::MAX
    &&& delta > 0
    &&& new_u == (KernelU {
        process_map: old_u.process_map.insert(process_ptr, ProcessU { quota_2m: (process.quota_2m as int - delta) as usize, ..process }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { quota_2m: (thread.quota_2m as int + delta) as usize, ..thread }),
        ..old_u
    })
}

#[verifier::opaque]
pub open spec fn kernel_pagetable_nonlock_fields_unchanged<const TABLE_TYPE: PTType>(pre: PageTableLockedMapOf<TABLE_TYPE>, post: PageTableLockedMapOf<TABLE_TYPE>) -> bool {
    &&& post.dom() == pre.dom()
    &&& forall|p: RwLockPageTableRoot| #![trigger post.spec_index(p)]
        pre.dom().contains(p) ==> {
            let before = pre.spec_index(p).view();
            let after = post.spec_index(p).view();
            &&& after.mapping_4k().filter_keys(|va: VAddr| after.mapping_4k().spec_index(va).present) == before.mapping_4k().filter_keys(|va: VAddr| before.mapping_4k().spec_index(va).present)
            &&& after.mapping_2m().filter_keys(|va: VAddr| after.mapping_2m().spec_index(va).present) == before.mapping_2m().filter_keys(|va: VAddr| before.mapping_2m().spec_index(va).present)
            &&& after.mapping_1g().filter_keys(|va: VAddr| after.mapping_1g().spec_index(va).present) == before.mapping_1g().filter_keys(|va: VAddr| before.mapping_1g().spec_index(va).present)
        }
}

#[verifier::opaque]
pub open spec fn kernel_cpu_nonlock_fields_unchanged(pre: CpuLockedArray, post: CpuLockedArray) -> bool {
    &&& forall|i: CpuId| #![trigger post.spec_index(i)]
        index_valid(NUM_CPUS, i) ==> {
            &&& post.spec_index(i).value.view().view().owning_container == pre.spec_index(i).value.view().view().owning_container
            &&& post.spec_index(i).value.view().view().state == pre.spec_index(i).value.view().view().state
            &&& post.spec_index(i).value.view().view().current_process == pre.spec_index(i).value.view().view().current_process
            &&& post.spec_index(i).value.view().view().current_thread == pre.spec_index(i).value.view().view().current_thread
            &&& post.spec_index(i).value.killer_info() == pre.spec_index(i).value.killer_info()
        }
}

#[verifier::opaque]
pub open spec fn kernel_process_nonlock_fields_unchanged(pre: ProcessLockedMap, post: ProcessLockedMap) -> bool {
    &&& post.dom() == pre.dom()
    &&& forall|p: RwLockProcessPtr| #![trigger post.spec_index(p)]
        pre.dom().contains(p) ==> {
            &&& post.spec_index(p).view().zombie == pre.spec_index(p).view().zombie
            &&& post.spec_index(p).view().pagetable == pre.spec_index(p).view().pagetable
            &&& post.spec_index(p).view().iommu_table == pre.spec_index(p).view().iommu_table
            &&& post.spec_index(p).view_ghost().owned_pci_functions.view() == pre.spec_index(p).view_ghost().owned_pci_functions.view()
            &&& post.spec_index(p).view().quota_4k == pre.spec_index(p).view().quota_4k
            &&& post.spec_index(p).view().quota_2m == pre.spec_index(p).view().quota_2m
            &&& post.spec_index(p).view().quota_1g == pre.spec_index(p).view().quota_1g
            &&& post.spec_index(p).view().children.view() == pre.spec_index(p).view().children.view()
            &&& post.spec_index(p).view_rodata().view().parent == pre.spec_index(p).view_rodata().view().parent
            &&& post.spec_index(p).view_rodata().view().depth == pre.spec_index(p).view_rodata().view().depth
            &&& post.spec_index(p).view_rodata().view().pcid == pre.spec_index(p).view_rodata().view().pcid
            &&& post.spec_index(p).view_rodata().view().owning_container == pre.spec_index(p).view_rodata().view().owning_container
            &&& post.spec_index(p).view_ghost().uppertree_seq.view() == pre.spec_index(p).view_ghost().uppertree_seq.view()
            &&& post.spec_index(p).view_ghost().subtree_set.view() == pre.spec_index(p).view_ghost().subtree_set.view()
            &&& post.spec_index(p).being_killed() == pre.spec_index(p).being_killed()
            &&& post.spec_index(p).view().owned_threads.view() == pre.spec_index(p).view().owned_threads.view()
        }
}

#[verifier::opaque]
pub open spec fn kernel_thread_nonlock_fields_unchanged(pre: ThreadLockedMap, post: ThreadLockedMap) -> bool {
    &&& post.dom() == pre.dom()
    &&& forall|t: RwLockThreadPtr| #![trigger post.spec_index(t)]
        pre.dom().contains(t) ==> {
            &&& post.spec_index(t).view().state == pre.spec_index(t).view().state
            &&& post.spec_index(t).view().caller == pre.spec_index(t).view().caller
            &&& post.spec_index(t).view().callee == pre.spec_index(t).view().callee
            &&& post.spec_index(t).view().owning_container == pre.spec_index(t).view().owning_container
            &&& post.spec_index(t).view().owning_proc == pre.spec_index(t).view().owning_proc
            &&& post.spec_index(t).view().last_cpu == pre.spec_index(t).view().last_cpu
            &&& post.spec_index(t).view().quota_4k == pre.spec_index(t).view().quota_4k
            &&& post.spec_index(t).view().quota_2m == pre.spec_index(t).view().quota_2m
            &&& post.spec_index(t).view().quota_1g == pre.spec_index(t).view().quota_1g
            &&& post.spec_index(t).view().endpoint_descriptors.view() == pre.spec_index(t).view().endpoint_descriptors.view()
            &&& post.spec_index(t).view().blocking_endpoint_ptr == pre.spec_index(t).view().blocking_endpoint_ptr
            &&& post.spec_index(t).view().ipc_payload == pre.spec_index(t).view().ipc_payload
            &&& post.spec_index(t).view().error_code == pre.spec_index(t).view().error_code
            &&& post.spec_index(t).view().trap_frame == pre.spec_index(t).view().trap_frame
            &&& post.spec_index(t).view().syscall_progress == pre.spec_index(t).view().syscall_progress
            &&& post.spec_index(t).being_killed() == pre.spec_index(t).being_killed()
        }
}

#[verifier::opaque]
pub open spec fn kernel_cpu_process_thread_nonlock_fields_unchanged(pre: &KernelK, post: &KernelK) -> bool {
    &&& kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, post.pt_mp)
    &&& kernel_pagetable_nonlock_fields_unchanged(pre.it_mp, post.it_mp)
    &&& kernel_cpu_nonlock_fields_unchanged(pre.cpu_arr, post.cpu_arr)
    &&& kernel_process_nonlock_fields_unchanged(pre.prc_mp, post.prc_mp)
    &&& kernel_thread_nonlock_fields_unchanged(pre.thr_mp, post.thr_mp)
    &&& post.dflt_pt == pre.dflt_pt
}

/// Every container field other than its own lock mode is unchanged, including the lock mode of its cpu set.
#[verifier::opaque]
pub open spec fn kernel_container_nonlock_fields_and_quotas_unchanged(pre: &KernelK, post: &KernelK) -> bool {
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
            &&& b.view().owned_endpoints.view() == a.view().owned_endpoints.view()
            &&& b.view().owned_pages.view() == a.view().owned_pages.view()
            &&& b_ro.parent == a_ro.parent
            &&& b_ro.depth == a_ro.depth
            &&& b_ro.scheduler == a_ro.scheduler
            &&& b_ro.cpu_set == a_ro.cpu_set
            &&& b.being_killed() == a.being_killed()
        }
    &&& forall|c: RwLockContainerPtr| #![trigger post.sched_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().scheduler)]
        pre.ctn_mp.dom().contains(c) ==> scheduler_shards_of(post.sched_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().scheduler))
            == scheduler_shards_of(pre.sched_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().scheduler))
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
    &&& forall|c: RwLockContainerPtr| #![trigger post.cpu_set_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().cpu_set)]
        pre.ctn_mp.dom().contains(c) ==> post.cpu_set_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().cpu_set).lock_state_u() == pre.cpu_set_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().cpu_set).lock_state_u()
    &&& forall|c: RwLockContainerPtr| #![trigger post.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(c))]
        pre.ctn_mp.dom().contains(c) ==> cpu_offline_requests_of(post.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(c))) == cpu_offline_requests_of(pre.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(c)))
}

#[verifier::opaque]
pub open spec fn kernel_container_quota_4k_changed(pre: &KernelK, post: &KernelK, container_ptr: RwLockContainerPtr, delta: int) -> bool {
    &&& *post == (KernelK { thr_mp: post.thr_mp, allc_4k_mp: post.allc_4k_mp, ..*pre })
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)] pre.thr_mp.dom().contains(t) ==>
        post.thr_mp.spec_index(t).locking_thread() == pre.thr_mp.spec_index(t).locking_thread()
    &&& kernel_thread_nonlock_fields_unchanged(pre.thr_mp, post.thr_mp)
    &&& pre.ctn_mp.dom().contains(container_ptr)
    &&& forall|c: RwLockContainerPtr| #![trigger post.allc_4k_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k)]
        pre.ctn_mp.dom().contains(c) ==> post.allc_4k_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k).quota.view().view() as int
            == pre.allc_4k_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k).quota.view().view() as int + if c == container_ptr { delta } else { 0 }
}

/// One staging-thread quota funds a new scheduled thread of `process_ptr` and `container_ptr`,
/// and the staging thread's progress becomes `staging_progress`.
#[verifier::opaque]
pub open spec fn kernel_new_thread_fields(
    pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, cpu_id: CpuId, new_thread_ptr: RwLockThreadPtr, initial_regs: Registers,
    initial_endpoint: Option<RwLockEndpointPtr>, staging_progress: Option<SyscallProgress>,
) -> bool {
    &&& post.irt.view().owners() == pre.irt.view().owners()
    &&& post.irt.view().iommu_roots() == pre.irt.view().iommu_roots()
    &&& post.cpu_tlb.view() == pre.cpu_tlb.view()
    &&& post.iommu_tlb.view() == pre.iommu_tlb.view()
    &&& post.ep_mp.dom() == pre.ep_mp.dom()
    &&& initial_endpoint.is_some() ==> pre.ep_mp.dom().contains(initial_endpoint.unwrap())
    &&& forall|e: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(e)]
        pre.ep_mp.dom().contains(e) ==> {
            let a = pre.ep_mp.spec_index(e);
            let b = post.ep_mp.spec_index(e);
            &&& b.view().queue.view() == a.view().queue.view()
            &&& b.view().queue_state == a.view().queue_state
            &&& b.view().owning_threads.view() == if initial_endpoint == Some(e) {
                a.view().owning_threads.view().insert((new_thread_ptr, 0usize))
            } else { a.view().owning_threads.view() }
            &&& b.view().owning_container == a.view().owning_container
            &&& b.being_killed() == a.being_killed()
        }
    &&& pre.prc_mp.dom().contains(process_ptr)
    &&& pre.ctn_mp.dom().contains(container_ptr)
    &&& pre.thr_mp.dom().contains(staging_thread_ptr)
    &&& !pre.thr_mp.dom().contains(new_thread_ptr)
    &&& pre.thr_mp.spec_index(staging_thread_ptr).view().quota_4k > 0
    &&& post.ctn_mp.dom() == pre.ctn_mp.dom()
    &&& forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)]
        pre.ctn_mp.dom().contains(c) ==> {
            &&& post.ctn_mp.spec_index(c).view() == pre.ctn_mp.spec_index(c).view()
            &&& post.ctn_mp.spec_index(c).view_rodata() == pre.ctn_mp.spec_index(c).view_rodata()
            &&& PcidAllocator::free_pcids(post.pcid_allc_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator).view().ref_counters.view())
                == PcidAllocator::free_pcids(pre.pcid_allc_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator).view().ref_counters.view())
            &&& post.ctn_mp.spec_index(c).view_ghost().uppertree_seq == pre.ctn_mp.spec_index(c).view_ghost().uppertree_seq
            &&& post.ctn_mp.spec_index(c).view_ghost().subtree_set == pre.ctn_mp.spec_index(c).view_ghost().subtree_set
            &&& post.ctn_mp.spec_index(c).view_ghost().owned_processes == pre.ctn_mp.spec_index(c).view_ghost().owned_processes
            &&& post.ctn_mp.spec_index(c).view_ghost().owned_threads.view() == if c == container_ptr { pre.ctn_mp.spec_index(c).view_ghost().owned_threads.view().insert(new_thread_ptr) }
                    else { pre.ctn_mp.spec_index(c).view_ghost().owned_threads.view() }
            &&& post.ctn_mp.spec_index(c).being_killed() == pre.ctn_mp.spec_index(c).being_killed()
        }
    &&& forall|s: RwLockSchedulerPtr| #![trigger post.sched_mp.spec_index(s)]
        post.sched_mp.dom().contains(s) ==> scheduler_shards_of(post.sched_mp.spec_index(s)) == if s == pre.ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler {
            scheduler_shards_of(pre.sched_mp.spec_index(s)).update(cpu_id as int, scheduler_shards_of(pre.sched_mp.spec_index(s))[cpu_id as int].push(new_thread_ptr))
        } else { scheduler_shards_of(pre.sched_mp.spec_index(s)) }
    &&& post.allc_4k_mp == pre.allc_4k_mp
    &&& post.allc_2m_mp == pre.allc_2m_mp
    &&& post.allc_1g_mp == pre.allc_1g_mp
    &&& post.cpu_offline_mp == pre.cpu_offline_mp
    &&& post.cpu_set_mp == pre.cpu_set_mp
    &&& post.dflt_pt == pre.dflt_pt
    &&& post.pt_mp.dom() == pre.pt_mp.dom()
    &&& forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
        pre.pt_mp.dom().contains(p) ==> {
            &&& post.pt_mp.spec_index(p).view().mapping_4k() == pre.pt_mp.spec_index(p).view().mapping_4k()
            &&& post.pt_mp.spec_index(p).view().mapping_2m() == pre.pt_mp.spec_index(p).view().mapping_2m()
            &&& post.pt_mp.spec_index(p).view().mapping_1g() == pre.pt_mp.spec_index(p).view().mapping_1g()
        }
    &&& post.it_mp.dom() == pre.it_mp.dom()
    &&& forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
        pre.it_mp.dom().contains(p) ==> {
            &&& post.it_mp.spec_index(p).view().mapping_4k() == pre.it_mp.spec_index(p).view().mapping_4k()
            &&& post.it_mp.spec_index(p).view().mapping_2m() == pre.it_mp.spec_index(p).view().mapping_2m()
            &&& post.it_mp.spec_index(p).view().mapping_1g() == pre.it_mp.spec_index(p).view().mapping_1g()
        }
    &&& forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
        index_valid(NUM_CPUS, i) ==> {
            &&& post.cpu_arr.spec_index(i).value.view().view().owning_container == pre.cpu_arr.spec_index(i).value.view().view().owning_container
            &&& post.cpu_arr.spec_index(i).value.view().view().state == pre.cpu_arr.spec_index(i).value.view().view().state
            &&& post.cpu_arr.spec_index(i).value.view().view().current_process == pre.cpu_arr.spec_index(i).value.view().view().current_process
            &&& post.cpu_arr.spec_index(i).value.view().view().current_thread == pre.cpu_arr.spec_index(i).value.view().view().current_thread
            &&& post.cpu_arr.spec_index(i).value.killer_info() == pre.cpu_arr.spec_index(i).value.killer_info()
        }
    &&& post.prc_mp.dom() == pre.prc_mp.dom()
    &&& forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
        pre.prc_mp.dom().contains(p) ==> {
            &&& post.prc_mp.spec_index(p).view().zombie == pre.prc_mp.spec_index(p).view().zombie
            &&& post.prc_mp.spec_index(p).view().pagetable == pre.prc_mp.spec_index(p).view().pagetable
            &&& post.prc_mp.spec_index(p).view().iommu_table == pre.prc_mp.spec_index(p).view().iommu_table
            &&& post.prc_mp.spec_index(p).view_ghost().owned_pci_functions.view() == pre.prc_mp.spec_index(p).view_ghost().owned_pci_functions.view()
            &&& post.prc_mp.spec_index(p).view().quota_4k == pre.prc_mp.spec_index(p).view().quota_4k
            &&& post.prc_mp.spec_index(p).view().quota_2m == pre.prc_mp.spec_index(p).view().quota_2m
            &&& post.prc_mp.spec_index(p).view().quota_1g == pre.prc_mp.spec_index(p).view().quota_1g
            &&& post.prc_mp.spec_index(p).view().children.view() == pre.prc_mp.spec_index(p).view().children.view()
            &&& post.prc_mp.spec_index(p).view_rodata().view().parent == pre.prc_mp.spec_index(p).view_rodata().view().parent
            &&& post.prc_mp.spec_index(p).view_rodata().view().depth == pre.prc_mp.spec_index(p).view_rodata().view().depth
            &&& post.prc_mp.spec_index(p).view_rodata().view().pcid == pre.prc_mp.spec_index(p).view_rodata().view().pcid
            &&& post.prc_mp.spec_index(p).view_rodata().view().owning_container == pre.prc_mp.spec_index(p).view_rodata().view().owning_container
            &&& post.prc_mp.spec_index(p).view_ghost().uppertree_seq.view() == pre.prc_mp.spec_index(p).view_ghost().uppertree_seq.view()
            &&& post.prc_mp.spec_index(p).view_ghost().subtree_set.view() == pre.prc_mp.spec_index(p).view_ghost().subtree_set.view()
            &&& post.prc_mp.spec_index(p).being_killed() == pre.prc_mp.spec_index(p).being_killed()
            &&& post.prc_mp.spec_index(p).view().owned_threads.view() == if p == process_ptr { pre.prc_mp.spec_index(p).view().owned_threads.view().push(new_thread_ptr) } else { pre.prc_mp.spec_index(p).view().owned_threads.view() }
        }
    &&& post.thr_mp.dom() == pre.thr_mp.dom().insert(new_thread_ptr)
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)]
        pre.thr_mp.dom().contains(t) ==> {
            &&& post.thr_mp.spec_index(t).view().state == pre.thr_mp.spec_index(t).view().state
            &&& post.thr_mp.spec_index(t).view().caller == pre.thr_mp.spec_index(t).view().caller
            &&& post.thr_mp.spec_index(t).view().callee == pre.thr_mp.spec_index(t).view().callee
            &&& post.thr_mp.spec_index(t).view().owning_container == pre.thr_mp.spec_index(t).view().owning_container
            &&& post.thr_mp.spec_index(t).view().owning_proc == pre.thr_mp.spec_index(t).view().owning_proc
            &&& post.thr_mp.spec_index(t).view().last_cpu == pre.thr_mp.spec_index(t).view().last_cpu
            &&& post.thr_mp.spec_index(t).view().quota_4k == if t == staging_thread_ptr { pre.thr_mp.spec_index(t).view().quota_4k - 1 } else { pre.thr_mp.spec_index(t).view().quota_4k as int }
            &&& post.thr_mp.spec_index(t).view().quota_2m == pre.thr_mp.spec_index(t).view().quota_2m
            &&& post.thr_mp.spec_index(t).view().quota_1g == pre.thr_mp.spec_index(t).view().quota_1g
            &&& post.thr_mp.spec_index(t).view().endpoint_descriptors.view() == pre.thr_mp.spec_index(t).view().endpoint_descriptors.view()
            &&& post.thr_mp.spec_index(t).view().blocking_endpoint_ptr == pre.thr_mp.spec_index(t).view().blocking_endpoint_ptr
            &&& post.thr_mp.spec_index(t).view().ipc_payload == pre.thr_mp.spec_index(t).view().ipc_payload
            &&& post.thr_mp.spec_index(t).view().error_code == pre.thr_mp.spec_index(t).view().error_code
            &&& post.thr_mp.spec_index(t).view().trap_frame == pre.thr_mp.spec_index(t).view().trap_frame
            &&& post.thr_mp.spec_index(t).view().syscall_progress.view() == if t == staging_thread_ptr { staging_progress } else { pre.thr_mp.spec_index(t).view().syscall_progress.view() }
            &&& post.thr_mp.spec_index(t).being_killed() == pre.thr_mp.spec_index(t).being_killed()
        }
    &&& post.thr_mp.spec_index(new_thread_ptr).view().state == (ThreadState::SCHEDULED { cpu_id })
    &&& post.thr_mp.spec_index(new_thread_ptr).view().last_cpu == cpu_id
    &&& post.thr_mp.spec_index(new_thread_ptr).view().caller == None
    &&& post.thr_mp.spec_index(new_thread_ptr).view().callee == None
    &&& post.thr_mp.spec_index(new_thread_ptr).view().owning_container == container_ptr
    &&& post.thr_mp.spec_index(new_thread_ptr).view().owning_proc == process_ptr
    &&& post.thr_mp.spec_index(new_thread_ptr).view().quota_4k == 0
    &&& post.thr_mp.spec_index(new_thread_ptr).view().quota_2m == 0
    &&& post.thr_mp.spec_index(new_thread_ptr).view().quota_1g == 0
    &&& post.thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.view() == Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat, |i: int| if i == 0 { initial_endpoint } else { None })
    &&& post.thr_mp.spec_index(new_thread_ptr).view().blocking_endpoint_ptr == None
    &&& post.thr_mp.spec_index(new_thread_ptr).view().ipc_payload == IPCPayLoad::Empty
    &&& post.thr_mp.spec_index(new_thread_ptr).view().error_code == None
    &&& post.thr_mp.spec_index(new_thread_ptr).view().syscall_progress.view() is None
    &&& post.thr_mp.spec_index(new_thread_ptr).view().trap_frame.is_some()
    &&& *post.thr_mp.spec_index(new_thread_ptr).view().trap_frame.get_some_0() == initial_regs
    &&& !post.thr_mp.spec_index(new_thread_ptr).being_killed()
}

#[verifier::opaque]
pub open spec fn kernel_thread_state_changed(pre: &KernelK, post: &KernelK, thread_ptr: RwLockThreadPtr) -> bool {
    &&& pre.thr_mp.dom().contains(thread_ptr)
    &&& post.thr_mp.dom().contains(thread_ptr)
    &&& pre.thr_mp.spec_index(thread_ptr).view().state != post.thr_mp.spec_index(thread_ptr).view().state
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
    &&& kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, post.pt_mp)
    &&& kernel_pagetable_nonlock_fields_unchanged(pre.it_mp, post.it_mp)
    &&& kernel_process_nonlock_fields_unchanged(pre.prc_mp, post.prc_mp)
    &&& kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp)
    &&& post.irt.view().owners() == pre.irt.view().owners()
    &&& post.irt.view().iommu_roots() == pre.irt.view().iommu_roots()
    &&& post.iommu_tlb.view() == pre.iommu_tlb.view()
    &&& post.dflt_pt == pre.dflt_pt
    &&& post.cpu_offline_mp == pre.cpu_offline_mp
    &&& post.cpu_set_mp == pre.cpu_set_mp
    &&& post.cpu_tlb.view() == match flushed_pcid {
        Some(pcid) => pre.cpu_tlb.view().insert((cpu_id, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }),
        None => pre.cpu_tlb.view(),
    }
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
            &&& b.view().owned_endpoints.view() == a.view().owned_endpoints.view()
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

/// The live head `next_thread` of shard `cpu_id` replaces the live thread running on `cpu_id`, which is requeued at
/// the tail of that shard.
#[verifier::opaque]
pub open spec fn kernel_u_context_switch_changed(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, next_thread: RwLockThreadPtr, entry_regs: Registers, flushed_pcid: Option<Pcid>) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let container = old_u.container_map.spec_index(cpu.owning_container);
    let next = old_u.thread_map.spec_index(next_thread);
    let requeued = match cpu.current_thread {
        Some(prev) => old_u.thread_map.insert(prev, ThreadU {
            state: ThreadState::SCHEDULED { cpu_id }, error_code: None, trap_frame: Some(entry_regs), ..old_u.thread_map.spec_index(prev)
        }),
        None => old_u.thread_map,
    };
    let run_queue = container.scheduler[cpu_id as int];
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& !(cpu.state is Off)
    &&& old_u.container_map.dom().contains(cpu.owning_container)
    &&& run_queue.len() > 0
    &&& run_queue[0] == next_thread
    &&& old_u.thread_map.dom().contains(next_thread)
    &&& !next.killed
    &&& next.state is SCHEDULED
    &&& next.owning_container == cpu.owning_container
    &&& old_u.process_map.dom().contains(next.owning_proc)
    &&& cpu.current_thread != Some(next_thread)
    &&& cpu.current_process is Some == cpu.current_thread is Some
    &&& (cpu.current_thread is Some ==> {
        let prev = old_u.thread_map.spec_index(cpu.current_thread.unwrap());
        &&& old_u.thread_map.dom().contains(cpu.current_thread.unwrap())
        &&& !prev.killed
        &&& prev.state == (ThreadState::RUNNING { cpu_id })
        &&& prev.owning_proc == cpu.current_process.unwrap()
        &&& old_u.process_map.dom().contains(cpu.current_process.unwrap())
        &&& !old_u.process_map.spec_index(cpu.current_process.unwrap()).killed
    })
    &&& new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU {
            state: CpuState::Running, current_process: Some(next.owning_proc), current_thread: Some(next_thread), ..cpu
        }),
        container_map: old_u.container_map.insert(cpu.owning_container, ContainerU {
            scheduler: container.scheduler.update(cpu_id as int, match cpu.current_thread { Some(prev) => run_queue.skip(1).push(prev), None => run_queue.skip(1) }),
            ..container
        }),
        thread_map: requeued.insert(next_thread, ThreadU { state: ThreadState::RUNNING { cpu_id }, last_cpu: cpu_id, error_code: None, trap_frame: None, ..next }),
        cpu_tlb: match flushed_pcid {
            Some(pcid) => old_u.cpu_tlb.insert((cpu_id, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }),
            None => old_u.cpu_tlb,
        },
        ..old_u
    })
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
    &&& *post == (KernelK { cpu_arr: post.cpu_arr, thr_mp: post.thr_mp, sched_mp: post.sched_mp, ..*pre })
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

/// The Idle cpu `cpu_id`, whose own shard is empty, takes the live head `thread` of shard `victim`, the lowest
/// other nonempty shard of its container's scheduler, onto shard `cpu_id`.
#[verifier::opaque]
pub open spec fn kernel_u_rebalance_pull_changed(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, victim: CpuId, thread: RwLockThreadPtr) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let container = old_u.container_map.spec_index(cpu.owning_container);
    let queues = container.scheduler;
    let t = old_u.thread_map.spec_index(thread);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& index_valid(NUM_CPUS, victim)
    &&& victim != cpu_id
    &&& cpu.state is Idle
    &&& old_u.container_map.dom().contains(cpu.owning_container)
    &&& queues[cpu_id as int].len() == 0
    &&& first_nonempty_shard(queues, 0, cpu_id) == Some(victim)
    &&& queues[victim as int].len() > 0
    &&& queues[victim as int][0] == thread
    &&& old_u.thread_map.dom().contains(thread)
    &&& !t.killed
    &&& t.state == (ThreadState::SCHEDULED { cpu_id: victim })
    &&& t.owning_container == cpu.owning_container
    &&& new_u == (KernelU {
        container_map: old_u.container_map.insert(cpu.owning_container, ContainerU {
            scheduler: queues.update(victim as int, queues[victim as int].skip(1)).update(cpu_id as int, queues[cpu_id as int].push(thread)),
            ..container
        }),
        thread_map: old_u.thread_map.insert(thread, ThreadU { state: ThreadState::SCHEDULED { cpu_id }, ..t }),
        ..old_u
    })
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
    &&& kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, post.pt_mp)
    &&& kernel_pagetable_nonlock_fields_unchanged(pre.it_mp, post.it_mp)
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

/// The live thread running on `cpu_id` blocks on the live endpoint at `endpoint_index` and the CPU goes idle.
#[verifier::opaque]
pub open spec fn kernel_u_ipc_block_changed(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    waiting_state: ThreadState, payload: IPCPayLoad, regs: Registers, flushed_default_pcid: bool,
) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& cpu.current_thread == Some(thread_ptr)
    &&& cpu.current_process == Some(thread.owning_proc)
    &&& old_u.process_map.dom().contains(thread.owning_proc)
    &&& old_u.thread_map.dom().contains(thread_ptr)
    &&& !thread.killed
    &&& thread.state == (ThreadState::RUNNING { cpu_id })
    &&& edp_idx_valid(endpoint_index)
    &&& thread.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
    &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
    &&& !endpoint.queue.contains(thread_ptr)
    &&& waiting_state.is_endpoint_waiting()
    &&& endpoint.queue.len() == 0 || (endpoint.queue_state is SEND) == waiting_state.is_endpoint_send_waiting()
    &&& new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { state: CpuState::Idle, current_process: None, current_thread: None, ..cpu }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU {
            state: waiting_state, blocking_endpoint_ptr: Some(endpoint_ptr), ipc_payload: payload, trap_frame: Some(regs), ..thread
        }),
        endpoint_map: old_u.endpoint_map.insert(endpoint_ptr, EndpointU {
            queue: endpoint.queue.push(thread_ptr),
            queue_state: if endpoint.queue.len() == 0 {
                match waiting_state { ThreadState::SENDING | ThreadState::CALLING => EndpointState::SEND, _ => EndpointState::RECEIVE }
            } else { endpoint.queue_state },
            ..endpoint
        }),
        cpu_tlb: if flushed_default_pcid {
            old_u.cpu_tlb.insert((cpu_id, KERNEL_DEFAULT_PCID), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })
        } else { old_u.cpu_tlb },
        ..old_u
    })
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
    &&& kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, post.pt_mp)
    &&& kernel_pagetable_nonlock_fields_unchanged(pre.it_mp, post.it_mp)
    &&& kernel_process_nonlock_fields_unchanged(pre.prc_mp, post.prc_mp)
    &&& kernel_container_nonlock_fields_and_quotas_unchanged(pre, post)
    &&& post.irt.view().owners() == pre.irt.view().owners()
    &&& post.irt.view().iommu_roots() == pre.irt.view().iommu_roots()
    &&& post.iommu_tlb.view() == pre.iommu_tlb.view()
    &&& post.dflt_pt == pre.dflt_pt
    &&& post.cpu_tlb.view() == match flushed_pcid {
        Some(pcid) => pre.cpu_tlb.view().insert((cpu_id, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }),
        None => pre.cpu_tlb.view(),
    }
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

/// The live caller running on `cpu_id` hands its CPU to the live receive-call head `callee_ptr` of the
/// endpoint at `endpoint_index`, which records the caller and runs; the caller saves `regs` and waits for the
/// reply.
#[verifier::opaque]
pub open spec fn kernel_u_ipc_call_handoff_changed(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, caller_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    callee_ptr: RwLockThreadPtr, regs: Registers, flushed_pcid: Option<Pcid>,
) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let caller = old_u.thread_map.spec_index(caller_ptr);
    let callee = old_u.thread_map.spec_index(callee_ptr);
    let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& cpu.current_thread == Some(caller_ptr)
    &&& cpu.current_process == Some(caller.owning_proc)
    &&& old_u.process_map.dom().contains(caller.owning_proc)
    &&& old_u.thread_map.dom().contains(caller_ptr)
    &&& !caller.killed
    &&& caller.state == (ThreadState::RUNNING { cpu_id })
    &&& caller.callee is None
    &&& edp_idx_valid(endpoint_index)
    &&& caller.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
    &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
    &&& !endpoint.queue.contains(caller_ptr)
    &&& endpoint.queue.len() > 0
    &&& endpoint.queue[0] == callee_ptr
    &&& endpoint.queue_state is RECEIVE
    &&& callee_ptr != caller_ptr
    &&& old_u.thread_map.dom().contains(callee_ptr)
    &&& !callee.killed
    &&& callee.state is RECEIVING_CALL
    &&& callee.caller is None
    &&& callee.callee is None
    &&& callee.blocking_endpoint_ptr == Some(endpoint_ptr)
    &&& callee.owning_container == caller.owning_container
    &&& old_u.process_map.dom().contains(callee.owning_proc)
    &&& new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { current_process: Some(callee.owning_proc), current_thread: Some(callee_ptr), ..cpu }),
        thread_map: old_u.thread_map.insert(caller_ptr, ThreadU { state: ThreadState::WAITING_REPLY, callee: Some(callee_ptr), trap_frame: Some(regs), ..caller })
            .insert(callee_ptr, ThreadU { state: ThreadState::RUNNING { cpu_id }, caller: Some(caller_ptr), last_cpu: cpu_id, blocking_endpoint_ptr: None, trap_frame: None, ..callee }),
        endpoint_map: old_u.endpoint_map.insert(endpoint_ptr, EndpointU { queue: endpoint.queue.skip(1), ..endpoint }),
        cpu_tlb: match flushed_pcid {
            Some(pcid) => old_u.cpu_tlb.insert((cpu_id, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }),
            None => old_u.cpu_tlb,
        },
        ..old_u
    })
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
    &&& *post == (KernelK { cpu_arr: post.cpu_arr, thr_mp: post.thr_mp, ep_mp: post.ep_mp, ..*pre })
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

/// The live receive-call thread running on `cpu_id` accepts the live calling head `caller_ptr` of the endpoint
/// at `endpoint_index`: the caller is dequeued and waits for the reply, and the callee records it.
#[verifier::opaque]
pub open spec fn kernel_u_ipc_accept_call_changed(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    caller_ptr: RwLockThreadPtr,
) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let callee = old_u.thread_map.spec_index(callee_ptr);
    let caller = old_u.thread_map.spec_index(caller_ptr);
    let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& cpu.current_thread == Some(callee_ptr)
    &&& cpu.current_process == Some(callee.owning_proc)
    &&& old_u.process_map.dom().contains(callee.owning_proc)
    &&& old_u.thread_map.dom().contains(callee_ptr)
    &&& !callee.killed
    &&& callee.state == (ThreadState::RUNNING { cpu_id })
    &&& callee.caller is None
    &&& callee.callee is None
    &&& edp_idx_valid(endpoint_index)
    &&& callee.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
    &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
    &&& !endpoint.queue.contains(callee_ptr)
    &&& endpoint.queue.len() > 0
    &&& endpoint.queue[0] == caller_ptr
    &&& endpoint.queue_state is SEND
    &&& caller_ptr != callee_ptr
    &&& old_u.thread_map.dom().contains(caller_ptr)
    &&& !caller.killed
    &&& caller.state is CALLING
    &&& caller.callee is None
    &&& caller.blocking_endpoint_ptr == Some(endpoint_ptr)
    &&& caller.owning_container == callee.owning_container
    &&& new_u == (KernelU {
        thread_map: old_u.thread_map.insert(callee_ptr, ThreadU { caller: Some(caller_ptr), ..callee }).insert(caller_ptr, ThreadU { state: ThreadState::WAITING_REPLY, callee: Some(callee_ptr), blocking_endpoint_ptr: None, ..caller }),
        endpoint_map: old_u.endpoint_map.insert(endpoint_ptr, EndpointU { queue: endpoint.queue.skip(1), ..endpoint }),
        ..old_u
    })
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
    &&& kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, post.pt_mp)
    &&& kernel_pagetable_nonlock_fields_unchanged(pre.it_mp, post.it_mp)
    &&& kernel_process_nonlock_fields_unchanged(pre.prc_mp, post.prc_mp)
    &&& kernel_container_nonlock_fields_and_quotas_unchanged(pre, post)
    &&& post.irt.view().owners() == pre.irt.view().owners()
    &&& post.irt.view().iommu_roots() == pre.irt.view().iommu_roots()
    &&& post.iommu_tlb.view() == pre.iommu_tlb.view()
    &&& post.dflt_pt == pre.dflt_pt
    &&& post.cpu_tlb.view() == match flushed_pcid {
        Some(pcid) => pre.cpu_tlb.view().insert((cpu_id, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }),
        None => pre.cpu_tlb.view(),
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

/// The live callee running on `cpu_id` replies to its recorded caller `caller_ptr`, which resumes on `cpu_id`,
/// and waits with `regs` for the next call on the endpoint at `endpoint_index`.
#[verifier::opaque]
pub open spec fn kernel_u_ipc_reply_handoff_changed(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    caller_ptr: RwLockThreadPtr, regs: Registers, flushed_pcid: Option<Pcid>,
) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let callee = old_u.thread_map.spec_index(callee_ptr);
    let caller = old_u.thread_map.spec_index(caller_ptr);
    let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& cpu.current_thread == Some(callee_ptr)
    &&& cpu.current_process == Some(callee.owning_proc)
    &&& old_u.process_map.dom().contains(callee.owning_proc)
    &&& old_u.thread_map.dom().contains(callee_ptr)
    &&& !callee.killed
    &&& callee.state == (ThreadState::RUNNING { cpu_id })
    &&& callee.caller == Some(caller_ptr)
    &&& callee.callee is None
    &&& edp_idx_valid(endpoint_index)
    &&& callee.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
    &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
    &&& !endpoint.queue.contains(callee_ptr)
    &&& endpoint.queue.len() == 0 || endpoint.queue_state is RECEIVE
    &&& caller_ptr != callee_ptr
    &&& old_u.thread_map.dom().contains(caller_ptr)
    &&& !caller.killed
    &&& caller.state is WAITING_REPLY
    &&& caller.callee == Some(callee_ptr)
    &&& caller.owning_container == callee.owning_container
    &&& old_u.process_map.dom().contains(caller.owning_proc)
    &&& new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { current_process: Some(caller.owning_proc), current_thread: Some(caller_ptr), ..cpu }),
        thread_map: old_u.thread_map.insert(callee_ptr, ThreadU {
            state: ThreadState::RECEIVING_CALL, caller: None, blocking_endpoint_ptr: Some(endpoint_ptr), ipc_payload: IPCPayLoad::Empty, trap_frame: Some(regs), ..callee
        }).insert(caller_ptr, ThreadU { state: ThreadState::RUNNING { cpu_id }, callee: None, last_cpu: cpu_id, trap_frame: None, ..caller }),
        endpoint_map: old_u.endpoint_map.insert(endpoint_ptr, EndpointU {
            queue: endpoint.queue.push(callee_ptr), queue_state: if endpoint.queue.len() == 0 { EndpointState::RECEIVE } else { endpoint.queue_state }, ..endpoint
        }),
        cpu_tlb: match flushed_pcid {
            Some(pcid) => old_u.cpu_tlb.insert((cpu_id, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }),
            None => old_u.cpu_tlb,
        },
        ..old_u
    })
}

#[verifier::opaque]
/// The live head `peer_thread_ptr` of the endpoint at `endpoint_index`, waiting opposite to the live caller
/// running on `cpu_id`, is dequeued and scheduled with `peer_result`; with `cpu_transfer == Some((cpu, receiver))`
/// that Off CPU also moves to the receiver's container, and with `pci_transfer == Some((bdf, sender, receiver))`
/// that PCI function moves from the sender to the receiver process, detached and with its IOTLB domain flushed.
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
    &&& kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, post.pt_mp)
    &&& kernel_pagetable_nonlock_fields_unchanged(pre.it_mp, post.it_mp)
    &&& pci_transfer is None ==> {
        &&& kernel_process_nonlock_fields_unchanged(pre.prc_mp, post.prc_mp)
        &&& post.irt.view().owners() == pre.irt.view().owners()
        &&& post.irt.view().iommu_roots() == pre.irt.view().iommu_roots()
        &&& post.iommu_tlb.view() == pre.iommu_tlb.view()
    }
    &&& pci_transfer matches Some((bdf, sender, receiver)) ==> {
        &&& pci_bdf_valid(bdf.0, bdf.1, bdf.2)
        &&& pre.prc_mp.dom().contains(sender)
        &&& pre.prc_mp.dom().contains(receiver)
        &&& sender != receiver
        &&& post.irt.view().owners() == seq3_update(pre.irt.view().owners(), bdf.0 as int, bdf.1 as int, bdf.2 as int, receiver)
        &&& post.irt.view().iommu_roots() == seq3_update(pre.irt.view().iommu_roots(), bdf.0 as int, bdf.1 as int, bdf.2 as int, None)
        &&& post.iommu_tlb.view() == pre.iommu_tlb.view().insert(pci_bdf_did(bdf.0, bdf.1, bdf.2), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })
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
            &&& b.view().owned_endpoints.view() == a.view().owned_endpoints.view()
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

/// The live endpoint head waiting opposite to the live caller running on `cpu_id` is dequeued and scheduled
/// with `peer_result` on shard `cpu_id` of a same-container peer, else on the peer's `last_cpu` shard; an Off
/// CPU may move to the receiver's container, and a detached PCI function with a flushed IOTLB domain may move
/// to the receiver process.
#[verifier::opaque]
pub open spec fn kernel_u_ipc_rendezvous_changed(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, caller_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, peer_thread_ptr: RwLockThreadPtr, peer_result: RetValueType,
    cpu_transfer: Option<(CpuId, RwLockThreadPtr)>, pci_transfer: Option<(PciBdf, RwLockProcessPtr, RwLockProcessPtr)>,
) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let caller = old_u.thread_map.spec_index(caller_thread_ptr);
    let peer = old_u.thread_map.spec_index(peer_thread_ptr);
    let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
    let container = old_u.container_map.spec_index(peer.owning_container);
    let wake_cpu = if peer.owning_container == caller.owning_container { cpu_id } else { peer.last_cpu };
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& cpu.current_thread == Some(caller_thread_ptr)
    &&& cpu.current_process == Some(caller.owning_proc)
    &&& old_u.process_map.dom().contains(caller.owning_proc)
    &&& old_u.thread_map.dom().contains(caller_thread_ptr)
    &&& !caller.killed
    &&& caller.state == (ThreadState::RUNNING { cpu_id })
    &&& edp_idx_valid(endpoint_index)
    &&& caller.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
    &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
    &&& !endpoint.queue.contains(caller_thread_ptr)
    &&& waiting_state.is_endpoint_waiting()
    &&& endpoint.queue.len() > 0
    &&& endpoint.queue[0] == peer_thread_ptr
    &&& (endpoint.queue_state is SEND) != waiting_state.is_endpoint_send_waiting()
    &&& old_u.thread_map.dom().contains(peer_thread_ptr)
    &&& peer_thread_ptr != caller_thread_ptr
    &&& !peer.killed
    &&& peer.state.is_endpoint_waiting()
    &&& peer.blocking_endpoint_ptr == Some(endpoint_ptr)
    &&& old_u.container_map.dom().contains(peer.owning_container)
    &&& (cpu_transfer is Some ==> index_valid(NUM_CPUS, cpu_transfer.unwrap().0) && old_u.thread_map.dom().contains(cpu_transfer.unwrap().1))
    &&& pci_transfer matches Some((bdf, sender, receiver)) ==> {
        &&& pci_bdf_valid(bdf.0, bdf.1, bdf.2)
        &&& old_u.process_map.dom().contains(sender)
        &&& old_u.process_map.dom().contains(receiver)
        &&& sender != receiver
    }
    &&& new_u == (KernelU {
        cpu_array: match cpu_transfer {
            Some((transfer_cpu, receiver)) => old_u.cpu_array.update(transfer_cpu as int, CpuU {
                owning_container: old_u.thread_map.spec_index(receiver).owning_container, ..old_u.cpu_array[transfer_cpu as int]
            }),
            None => old_u.cpu_array,
        },
        container_map: old_u.container_map.insert(peer.owning_container, ContainerU {
            scheduler: container.scheduler.update(wake_cpu as int, container.scheduler[wake_cpu as int].push(peer_thread_ptr)), ..container
        }),
        thread_map: old_u.thread_map.insert(peer_thread_ptr, ThreadU {
            state: ThreadState::SCHEDULED { cpu_id: wake_cpu }, blocking_endpoint_ptr: None, ipc_payload: IPCPayLoad::Empty, error_code: Some(peer_result), ..peer
        }),
        endpoint_map: old_u.endpoint_map.insert(endpoint_ptr, EndpointU { queue: endpoint.queue.skip(1), ..endpoint }),
        process_map: match pci_transfer {
            Some((bdf, sender, receiver)) => {
                let s = old_u.process_map.spec_index(sender);
                let r = old_u.process_map.spec_index(receiver);
                old_u.process_map.insert(sender, ProcessU { owned_pci_functions: s.owned_pci_functions.remove(bdf), ..s }).insert(receiver, ProcessU { owned_pci_functions: r.owned_pci_functions.insert(bdf), ..r })
            },
            None => old_u.process_map,
        },
        iommu_root_table: match pci_transfer {
            Some((bdf, _, receiver)) => IommuRootTableU {
                owners: seq3_update(old_u.iommu_root_table.owners, bdf.0 as int, bdf.1 as int, bdf.2 as int, receiver),
                attached: seq3_update(old_u.iommu_root_table.attached, bdf.0 as int, bdf.1 as int, bdf.2 as int, false),
            },
            None => old_u.iommu_root_table,
        },
        iommu_tlb: match pci_transfer {
            Some((bdf, _, _)) => old_u.iommu_tlb.insert(pci_bdf_did(bdf.0, bdf.1, bdf.2), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }),
            None => old_u.iommu_tlb,
        },
        ..old_u
    })
}

/// The caller's result of meeting the queue head of the endpoint at `endpoint_index`, decided from the two
/// payloads as the implementation does. Empty payloads in opposite directions succeed. A CPU handover needs
/// different containers and an Off CPU of the sender's container; an endpoint transfer needs the sender's
/// source descriptor and a free receiver target descriptor; a pages transfer needs equal lengths and different
/// processes; a PCI handover needs the same function named on both sides, different processes, and a sender
/// process that owns the function. Any other pairing is a type mismatch. Success on Endpoint and Pages
/// payloads starts their multi-step transfer. A calling or receive-call caller only reaches this error step:
/// CallAcrossContainers when the head waits in the matching call state, else a type mismatch.
pub open spec fn ipc_rendezvous_result(old_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad) -> RetValueType {
    let caller = old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0];
    let peer = old_u.thread_map[old_u.endpoint_map[caller.endpoint_descriptors[endpoint_index as int]->Some_0].queue[0]];
    let sends = waiting_state.is_endpoint_send_waiting();
    let sender = if sends { caller } else { peer };
    let receiver = if sends { peer } else { caller };
    let sent = if sends { payload } else { peer.ipc_payload };
    let received = if sends { peer.ipc_payload } else { payload };
    if waiting_state is CALLING || waiting_state is RECEIVING_CALL {
        if peer.state == (if sends { ThreadState::RECEIVING_CALL } else { ThreadState::CALLING }) { RetValueType::ErrorCallAcrossContainers } else { RetValueType::ErrorIpcTypeMismatch }
    } else if peer.state != (if sends { ThreadState::RECEIVING } else { ThreadState::SENDING }) { RetValueType::ErrorIpcTypeMismatch } else {
        match (sent, received) {
            (IPCPayLoad::Empty, IPCPayLoad::Empty) => RetValueType::Success,
            (IPCPayLoad::Cpu { cpu_id: transfer }, IPCPayLoad::ReceiveCpu) => {
                let cpu = old_u.cpu_array[transfer as int];
                if sender.owning_container == receiver.owning_container { RetValueType::ErrorIpcSameContainer }
                else if !index_valid(NUM_CPUS, transfer) || cpu.owning_container != sender.owning_container { RetValueType::ErrorIpcCpuOwnerMismatch }
                else if !(cpu.state is Off) { RetValueType::ErrorIpcCpuNotOff }
                else if sends { RetValueType::Success } else { RetValueType::SuccessUsize { value: transfer } }
            },
            (IPCPayLoad::Endpoint { endpoint_index: source }, IPCPayLoad::Endpoint { endpoint_index: target }) => {
                if sender.endpoint_descriptors[source as int] is None { RetValueType::ErrorIpcEndpointSourceInvalid }
                else if receiver.endpoint_descriptors[target as int] is Some { RetValueType::ErrorIpcEndpointTargetInUse }
                else { RetValueType::Success }
            },
            (IPCPayLoad::Pages { va_range: source }, IPCPayLoad::Pages { va_range: target }) => {
                if source.len != target.len { RetValueType::ErrorIpcTypeMismatch }
                else if sender.owning_proc == receiver.owning_proc { RetValueType::ErrorIpcSameProcess }
                else { RetValueType::Success }
            },
            (IPCPayLoad::Pci { bus: sent_bus, dev: sent_dev, fun: sent_fun }, IPCPayLoad::Pci { bus: received_bus, dev: received_dev, fun: received_fun }) => {
                if sent_bus != received_bus || sent_dev != received_dev || sent_fun != received_fun { RetValueType::ErrorIpcTypeMismatch }
                else if sender.owning_proc == receiver.owning_proc { RetValueType::ErrorIpcSameProcess }
                else if !old_u.process_map[sender.owning_proc].owned_pci_functions.contains((sent_bus as usize, sent_dev as usize, sent_fun as usize)) { RetValueType::ErrorIpcPciOwnerMismatch }
                else { RetValueType::Success }
            },
            _ => RetValueType::ErrorIpcTypeMismatch,
        }
    }
}

#[verifier::opaque]
pub open spec fn kernel_thread_quota_4k_changed(pre: &KernelK, post: &KernelK, thread_ptr: RwLockThreadPtr, delta: int) -> bool {
    &&& pre.thr_mp.dom().contains(thread_ptr)
    &&& post.thr_mp.dom().contains(thread_ptr)
    &&& post.thr_mp.spec_index(thread_ptr).view().state == pre.thr_mp.spec_index(thread_ptr).view().state
    &&& post.thr_mp.spec_index(thread_ptr).view().caller == pre.thr_mp.spec_index(thread_ptr).view().caller
    &&& post.thr_mp.spec_index(thread_ptr).view().callee == pre.thr_mp.spec_index(thread_ptr).view().callee
    &&& post.thr_mp.spec_index(thread_ptr).view().owning_container == pre.thr_mp.spec_index(thread_ptr).view().owning_container
    &&& post.thr_mp.spec_index(thread_ptr).view().owning_proc == pre.thr_mp.spec_index(thread_ptr).view().owning_proc
    &&& post.thr_mp.spec_index(thread_ptr).view().last_cpu == pre.thr_mp.spec_index(thread_ptr).view().last_cpu
    &&& post.thr_mp.spec_index(thread_ptr).view().quota_4k as int == pre.thr_mp.spec_index(thread_ptr).view().quota_4k as int + delta
    &&& post.thr_mp.spec_index(thread_ptr).view().quota_2m == pre.thr_mp.spec_index(thread_ptr).view().quota_2m
    &&& post.thr_mp.spec_index(thread_ptr).view().quota_1g == pre.thr_mp.spec_index(thread_ptr).view().quota_1g
    &&& post.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view() == pre.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()
    &&& post.thr_mp.spec_index(thread_ptr).view().blocking_endpoint_ptr == pre.thr_mp.spec_index(thread_ptr).view().blocking_endpoint_ptr
    &&& post.thr_mp.spec_index(thread_ptr).view().ipc_payload == pre.thr_mp.spec_index(thread_ptr).view().ipc_payload
    &&& post.thr_mp.spec_index(thread_ptr).view().error_code == pre.thr_mp.spec_index(thread_ptr).view().error_code
    &&& post.thr_mp.spec_index(thread_ptr).view().trap_frame == pre.thr_mp.spec_index(thread_ptr).view().trap_frame
    &&& post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed()
}

#[verifier::opaque]
pub open spec fn kernel_process_quota_4k_changed(pre: &KernelK, post: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, delta: int) -> bool {
    let cpu = pre.cpu_arr.spec_index(cpu_id).value.view().view();
    let container = pre.ctn_mp.spec_index(container_ptr);
    let process = pre.prc_mp.spec_index(process_ptr);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& pre.cpu_arr.spec_index(cpu_id).value.locking_thread() is None
    &&& cpu.state is Running
    &&& cpu.current_process == Some(process_ptr)
    &&& cpu.owning_container == container_ptr
    &&& container.locking_thread() is None
    &&& !container.being_killed()
    &&& !container.view().zombie
    &&& pre.allc_4k_mp.spec_index(container.view_rodata().view().allocator_ptr_4k).quota.view().view() >= delta
    &&& process.locking_thread() is None
    &&& !process.being_killed()
    &&& process.view().quota_4k + delta <= usize::MAX
    &&& delta > 0
    &&& kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp)
    &&& forall|e: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(e)]
        pre.ep_mp.dom().contains(e) ==> post.ep_mp.spec_index(e).locking_thread() == pre.ep_mp.spec_index(e).locking_thread()
    &&& post.irt.view().owners() == pre.irt.view().owners()
    &&& post.irt.view().iommu_roots() == pre.irt.view().iommu_roots()
    &&& post.cpu_tlb.view() == pre.cpu_tlb.view()
    &&& post.iommu_tlb.view() == pre.iommu_tlb.view()
    &&& post.dflt_pt == pre.dflt_pt
    &&& post.cpu_offline_mp == pre.cpu_offline_mp
    &&& post.cpu_set_mp == pre.cpu_set_mp
    &&& pre.prc_mp.dom().contains(process_ptr)
    &&& pre.ctn_mp.dom().contains(container_ptr)
    &&& post.ctn_mp.dom() == pre.ctn_mp.dom()
    &&& forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)]
        pre.ctn_mp.dom().contains(c) ==> {
            let a = pre.ctn_mp.spec_index(c);
            let b = post.ctn_mp.spec_index(c);
            let a_ro = a.view_rodata().view();
            let b_ro = b.view_rodata().view();
            &&& b.locking_thread() == a.locking_thread()
            &&& b.view().children.view() == a.view().children.view()
            &&& b.view_ghost().uppertree_seq.view() == a.view_ghost().uppertree_seq.view()
            &&& b.view_ghost().subtree_set.view() == a.view_ghost().subtree_set.view()
            &&& b.view().root_process == a.view().root_process
            &&& b.view().zombie == a.view().zombie
            &&& b.view_ghost().owned_processes.view() == a.view_ghost().owned_processes.view()
            &&& b.view_ghost().owned_threads.view() == a.view_ghost().owned_threads.view()
            &&& b.view().owned_endpoints.view() == a.view().owned_endpoints.view()
            &&& b.view().owned_pages.view() == a.view().owned_pages.view()
            &&& b_ro.parent == a_ro.parent
            &&& b_ro.depth == a_ro.depth
            &&& b_ro.cpu_set == a_ro.cpu_set
            &&& b_ro.scheduler == a_ro.scheduler
            &&& b.being_killed() == a.being_killed()
        }
    &&& forall|c: RwLockContainerPtr| #![trigger post.sched_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().scheduler)]
        pre.ctn_mp.dom().contains(c) ==> scheduler_shards_of(post.sched_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().scheduler))
            == scheduler_shards_of(pre.sched_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().scheduler))
    &&& forall|c: RwLockContainerPtr| #![trigger post.allc_4k_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k)]
        pre.ctn_mp.dom().contains(c) ==> post.allc_4k_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k).quota.view().view() as int
            == pre.allc_4k_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k).quota.view().view() as int - if c == container_ptr { delta } else { 0 }
    &&& forall|c: RwLockContainerPtr| #![trigger post.pcid_allc_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator)]
        pre.ctn_mp.dom().contains(c) ==> PcidAllocator::free_pcids(post.pcid_allc_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator).view().ref_counters.view())
            == PcidAllocator::free_pcids(pre.pcid_allc_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator).view().ref_counters.view())
    &&& forall|c: RwLockContainerPtr| #![trigger post.allc_2m_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_2m)]
        pre.ctn_mp.dom().contains(c) ==> post.allc_2m_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_2m).quota.view().view()
            == pre.allc_2m_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_2m).quota.view().view()
    &&& forall|c: RwLockContainerPtr| #![trigger post.allc_1g_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g)]
        pre.ctn_mp.dom().contains(c) ==> post.allc_1g_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g).quota.view().view()
            == pre.allc_1g_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g).quota.view().view()
    &&& post.pt_mp.dom() == pre.pt_mp.dom()
    &&& forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
        pre.pt_mp.dom().contains(p) ==> {
            let before = pre.pt_mp.spec_index(p).view();
            let after = post.pt_mp.spec_index(p).view();
            &&& post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread()
            &&& after.mapping_4k().filter_keys(|va: VAddr| after.mapping_4k().spec_index(va).present) == before.mapping_4k().filter_keys(|va: VAddr| before.mapping_4k().spec_index(va).present)
            &&& after.mapping_2m().filter_keys(|va: VAddr| after.mapping_2m().spec_index(va).present) == before.mapping_2m().filter_keys(|va: VAddr| before.mapping_2m().spec_index(va).present)
            &&& after.mapping_1g().filter_keys(|va: VAddr| after.mapping_1g().spec_index(va).present) == before.mapping_1g().filter_keys(|va: VAddr| before.mapping_1g().spec_index(va).present)
        }
    &&& post.it_mp.dom() == pre.it_mp.dom()
    &&& forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
        pre.it_mp.dom().contains(p) ==> {
            let before = pre.it_mp.spec_index(p).view();
            let after = post.it_mp.spec_index(p).view();
            &&& post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread()
            &&& after.mapping_4k().filter_keys(|va: VAddr| after.mapping_4k().spec_index(va).present) == before.mapping_4k().filter_keys(|va: VAddr| before.mapping_4k().spec_index(va).present)
            &&& after.mapping_2m().filter_keys(|va: VAddr| after.mapping_2m().spec_index(va).present) == before.mapping_2m().filter_keys(|va: VAddr| before.mapping_2m().spec_index(va).present)
            &&& after.mapping_1g().filter_keys(|va: VAddr| after.mapping_1g().spec_index(va).present) == before.mapping_1g().filter_keys(|va: VAddr| before.mapping_1g().spec_index(va).present)
        }
    &&& forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
        index_valid(NUM_CPUS, i) ==> {
            &&& post.cpu_arr.spec_index(i).value.locking_thread() == pre.cpu_arr.spec_index(i).value.locking_thread()
            &&& post.cpu_arr.spec_index(i).value.view().view().owning_container == pre.cpu_arr.spec_index(i).value.view().view().owning_container
            &&& post.cpu_arr.spec_index(i).value.view().view().state == pre.cpu_arr.spec_index(i).value.view().view().state
            &&& post.cpu_arr.spec_index(i).value.view().view().current_process == pre.cpu_arr.spec_index(i).value.view().view().current_process
            &&& post.cpu_arr.spec_index(i).value.view().view().current_thread == pre.cpu_arr.spec_index(i).value.view().view().current_thread
            &&& post.cpu_arr.spec_index(i).value.killer_info() == pre.cpu_arr.spec_index(i).value.killer_info()
        }
    &&& post.prc_mp.dom() == pre.prc_mp.dom()
    &&& forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
        pre.prc_mp.dom().contains(p) ==> {
            &&& post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread()
            &&& post.prc_mp.spec_index(p).view().zombie == pre.prc_mp.spec_index(p).view().zombie
            &&& post.prc_mp.spec_index(p).view().pagetable == pre.prc_mp.spec_index(p).view().pagetable
            &&& post.prc_mp.spec_index(p).view().iommu_table == pre.prc_mp.spec_index(p).view().iommu_table
            &&& post.prc_mp.spec_index(p).view_ghost().owned_pci_functions.view() == pre.prc_mp.spec_index(p).view_ghost().owned_pci_functions.view()
            &&& post.prc_mp.spec_index(p).view().quota_4k as int == pre.prc_mp.spec_index(p).view().quota_4k as int + if p == process_ptr { delta } else { 0 }
            &&& post.prc_mp.spec_index(p).view().quota_2m == pre.prc_mp.spec_index(p).view().quota_2m
            &&& post.prc_mp.spec_index(p).view().quota_1g == pre.prc_mp.spec_index(p).view().quota_1g
            &&& post.prc_mp.spec_index(p).view().children.view() == pre.prc_mp.spec_index(p).view().children.view()
            &&& post.prc_mp.spec_index(p).view_rodata().view().parent == pre.prc_mp.spec_index(p).view_rodata().view().parent
            &&& post.prc_mp.spec_index(p).view_rodata().view().depth == pre.prc_mp.spec_index(p).view_rodata().view().depth
            &&& post.prc_mp.spec_index(p).view_rodata().view().pcid == pre.prc_mp.spec_index(p).view_rodata().view().pcid
            &&& post.prc_mp.spec_index(p).view_rodata().view().owning_container == pre.prc_mp.spec_index(p).view_rodata().view().owning_container
            &&& post.prc_mp.spec_index(p).view_ghost().uppertree_seq.view() == pre.prc_mp.spec_index(p).view_ghost().uppertree_seq.view()
            &&& post.prc_mp.spec_index(p).view_ghost().subtree_set.view() == pre.prc_mp.spec_index(p).view_ghost().subtree_set.view()
            &&& post.prc_mp.spec_index(p).being_killed() == pre.prc_mp.spec_index(p).being_killed()
            &&& post.prc_mp.spec_index(p).view().owned_threads.view() == pre.prc_mp.spec_index(p).view().owned_threads.view()
        }
    &&& post.thr_mp.dom() == pre.thr_mp.dom()
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)]
        pre.thr_mp.dom().contains(t) ==> {
            &&& post.thr_mp.spec_index(t).locking_thread() == pre.thr_mp.spec_index(t).locking_thread()
            &&& post.thr_mp.spec_index(t).view().state == pre.thr_mp.spec_index(t).view().state
            &&& post.thr_mp.spec_index(t).view().caller == pre.thr_mp.spec_index(t).view().caller
            &&& post.thr_mp.spec_index(t).view().callee == pre.thr_mp.spec_index(t).view().callee
            &&& post.thr_mp.spec_index(t).view().owning_container == pre.thr_mp.spec_index(t).view().owning_container
            &&& post.thr_mp.spec_index(t).view().owning_proc == pre.thr_mp.spec_index(t).view().owning_proc
            &&& post.thr_mp.spec_index(t).view().last_cpu == pre.thr_mp.spec_index(t).view().last_cpu
            &&& post.thr_mp.spec_index(t).view().quota_4k == pre.thr_mp.spec_index(t).view().quota_4k
            &&& post.thr_mp.spec_index(t).view().quota_2m == pre.thr_mp.spec_index(t).view().quota_2m
            &&& post.thr_mp.spec_index(t).view().quota_1g == pre.thr_mp.spec_index(t).view().quota_1g
            &&& post.thr_mp.spec_index(t).view().endpoint_descriptors.view() == pre.thr_mp.spec_index(t).view().endpoint_descriptors.view()
            &&& post.thr_mp.spec_index(t).view().blocking_endpoint_ptr == pre.thr_mp.spec_index(t).view().blocking_endpoint_ptr
            &&& post.thr_mp.spec_index(t).view().ipc_payload == pre.thr_mp.spec_index(t).view().ipc_payload
            &&& post.thr_mp.spec_index(t).view().error_code == pre.thr_mp.spec_index(t).view().error_code
            &&& post.thr_mp.spec_index(t).view().trap_frame == pre.thr_mp.spec_index(t).view().trap_frame
            &&& post.thr_mp.spec_index(t).view().syscall_progress == pre.thr_mp.spec_index(t).view().syscall_progress
            &&& post.thr_mp.spec_index(t).being_killed() == pre.thr_mp.spec_index(t).being_killed()
        }
}

/// The live process running on `cpu_id` takes `delta` 2M quota from its live container; the container's 2M
/// allocator quota and the process's `quota_2m` change and every other user field is preserved.
#[verifier::opaque]
pub open spec fn kernel_process_quota_2m_changed(pre: &KernelK, post: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, delta: int) -> bool {
    let cpu = pre.cpu_arr.spec_index(cpu_id).value.view().view();
    let container = pre.ctn_mp.spec_index(container_ptr);
    let process = pre.prc_mp.spec_index(process_ptr);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& pre.cpu_arr.spec_index(cpu_id).value.locking_thread() is None
    &&& cpu.state is Running
    &&& cpu.current_process == Some(process_ptr)
    &&& cpu.owning_container == container_ptr
    &&& container.locking_thread() is None
    &&& !container.being_killed()
    &&& !container.view().zombie
    &&& pre.allc_2m_mp.spec_index(container.view_rodata().view().allocator_ptr_2m).quota.view().view() >= delta
    &&& process.locking_thread() is None
    &&& !process.being_killed()
    &&& process.view().quota_2m + delta <= usize::MAX
    &&& delta > 0
    &&& kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp)
    &&& forall|e: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(e)]
        pre.ep_mp.dom().contains(e) ==> post.ep_mp.spec_index(e).locking_thread() == pre.ep_mp.spec_index(e).locking_thread()
    &&& post.irt.view().owners() == pre.irt.view().owners()
    &&& post.irt.view().iommu_roots() == pre.irt.view().iommu_roots()
    &&& post.cpu_tlb.view() == pre.cpu_tlb.view()
    &&& post.iommu_tlb.view() == pre.iommu_tlb.view()
    &&& post.dflt_pt == pre.dflt_pt
    &&& post.cpu_offline_mp == pre.cpu_offline_mp
    &&& post.cpu_set_mp == pre.cpu_set_mp
    &&& pre.prc_mp.dom().contains(process_ptr)
    &&& pre.ctn_mp.dom().contains(container_ptr)
    &&& post.ctn_mp.dom() == pre.ctn_mp.dom()
    &&& forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)]
        pre.ctn_mp.dom().contains(c) ==> {
            let a = pre.ctn_mp.spec_index(c);
            let b = post.ctn_mp.spec_index(c);
            let a_ro = a.view_rodata().view();
            let b_ro = b.view_rodata().view();
            &&& b.locking_thread() == a.locking_thread()
            &&& b.view().children.view() == a.view().children.view()
            &&& b.view_ghost().uppertree_seq.view() == a.view_ghost().uppertree_seq.view()
            &&& b.view_ghost().subtree_set.view() == a.view_ghost().subtree_set.view()
            &&& b.view().root_process == a.view().root_process
            &&& b.view().zombie == a.view().zombie
            &&& b.view_ghost().owned_processes.view() == a.view_ghost().owned_processes.view()
            &&& b.view_ghost().owned_threads.view() == a.view_ghost().owned_threads.view()
            &&& b.view().owned_endpoints.view() == a.view().owned_endpoints.view()
            &&& b.view().owned_pages.view() == a.view().owned_pages.view()
            &&& b_ro.parent == a_ro.parent
            &&& b_ro.depth == a_ro.depth
            &&& b_ro.cpu_set == a_ro.cpu_set
            &&& b_ro.scheduler == a_ro.scheduler
            &&& b.being_killed() == a.being_killed()
        }
    &&& forall|c: RwLockContainerPtr| #![trigger post.sched_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().scheduler)]
        pre.ctn_mp.dom().contains(c) ==> scheduler_shards_of(post.sched_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().scheduler))
            == scheduler_shards_of(pre.sched_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().scheduler))
    &&& forall|c: RwLockContainerPtr| #![trigger post.allc_4k_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k)]
        pre.ctn_mp.dom().contains(c) ==> post.allc_4k_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k).quota.view().view()
            == pre.allc_4k_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k).quota.view().view()
    &&& forall|c: RwLockContainerPtr| #![trigger post.pcid_allc_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator)]
        pre.ctn_mp.dom().contains(c) ==> PcidAllocator::free_pcids(post.pcid_allc_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator).view().ref_counters.view())
            == PcidAllocator::free_pcids(pre.pcid_allc_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator).view().ref_counters.view())
    &&& forall|c: RwLockContainerPtr| #![trigger post.allc_2m_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_2m)]
        pre.ctn_mp.dom().contains(c) ==> post.allc_2m_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_2m).quota.view().view() as int
            == pre.allc_2m_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_2m).quota.view().view() as int - if c == container_ptr { delta } else { 0 }
    &&& forall|c: RwLockContainerPtr| #![trigger post.allc_1g_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g)]
        pre.ctn_mp.dom().contains(c) ==> post.allc_1g_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g).quota.view().view()
            == pre.allc_1g_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g).quota.view().view()
    &&& post.pt_mp.dom() == pre.pt_mp.dom()
    &&& forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
        pre.pt_mp.dom().contains(p) ==> {
            let before = pre.pt_mp.spec_index(p).view();
            let after = post.pt_mp.spec_index(p).view();
            &&& post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread()
            &&& after.mapping_4k().filter_keys(|va: VAddr| after.mapping_4k().spec_index(va).present) == before.mapping_4k().filter_keys(|va: VAddr| before.mapping_4k().spec_index(va).present)
            &&& after.mapping_2m().filter_keys(|va: VAddr| after.mapping_2m().spec_index(va).present) == before.mapping_2m().filter_keys(|va: VAddr| before.mapping_2m().spec_index(va).present)
            &&& after.mapping_1g().filter_keys(|va: VAddr| after.mapping_1g().spec_index(va).present) == before.mapping_1g().filter_keys(|va: VAddr| before.mapping_1g().spec_index(va).present)
        }
    &&& post.it_mp.dom() == pre.it_mp.dom()
    &&& forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
        pre.it_mp.dom().contains(p) ==> {
            let before = pre.it_mp.spec_index(p).view();
            let after = post.it_mp.spec_index(p).view();
            &&& post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread()
            &&& after.mapping_4k().filter_keys(|va: VAddr| after.mapping_4k().spec_index(va).present) == before.mapping_4k().filter_keys(|va: VAddr| before.mapping_4k().spec_index(va).present)
            &&& after.mapping_2m().filter_keys(|va: VAddr| after.mapping_2m().spec_index(va).present) == before.mapping_2m().filter_keys(|va: VAddr| before.mapping_2m().spec_index(va).present)
            &&& after.mapping_1g().filter_keys(|va: VAddr| after.mapping_1g().spec_index(va).present) == before.mapping_1g().filter_keys(|va: VAddr| before.mapping_1g().spec_index(va).present)
        }
    &&& forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
        index_valid(NUM_CPUS, i) ==> {
            &&& post.cpu_arr.spec_index(i).value.locking_thread() == pre.cpu_arr.spec_index(i).value.locking_thread()
            &&& post.cpu_arr.spec_index(i).value.view().view().owning_container == pre.cpu_arr.spec_index(i).value.view().view().owning_container
            &&& post.cpu_arr.spec_index(i).value.view().view().state == pre.cpu_arr.spec_index(i).value.view().view().state
            &&& post.cpu_arr.spec_index(i).value.view().view().current_process == pre.cpu_arr.spec_index(i).value.view().view().current_process
            &&& post.cpu_arr.spec_index(i).value.view().view().current_thread == pre.cpu_arr.spec_index(i).value.view().view().current_thread
            &&& post.cpu_arr.spec_index(i).value.killer_info() == pre.cpu_arr.spec_index(i).value.killer_info()
        }
    &&& post.prc_mp.dom() == pre.prc_mp.dom()
    &&& forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
        pre.prc_mp.dom().contains(p) ==> {
            &&& post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread()
            &&& post.prc_mp.spec_index(p).view().zombie == pre.prc_mp.spec_index(p).view().zombie
            &&& post.prc_mp.spec_index(p).view().pagetable == pre.prc_mp.spec_index(p).view().pagetable
            &&& post.prc_mp.spec_index(p).view().iommu_table == pre.prc_mp.spec_index(p).view().iommu_table
            &&& post.prc_mp.spec_index(p).view_ghost().owned_pci_functions.view() == pre.prc_mp.spec_index(p).view_ghost().owned_pci_functions.view()
            &&& post.prc_mp.spec_index(p).view().quota_4k == pre.prc_mp.spec_index(p).view().quota_4k
            &&& post.prc_mp.spec_index(p).view().quota_2m as int == pre.prc_mp.spec_index(p).view().quota_2m as int + if p == process_ptr { delta } else { 0 }
            &&& post.prc_mp.spec_index(p).view().quota_1g == pre.prc_mp.spec_index(p).view().quota_1g
            &&& post.prc_mp.spec_index(p).view().children.view() == pre.prc_mp.spec_index(p).view().children.view()
            &&& post.prc_mp.spec_index(p).view_rodata().view().parent == pre.prc_mp.spec_index(p).view_rodata().view().parent
            &&& post.prc_mp.spec_index(p).view_rodata().view().depth == pre.prc_mp.spec_index(p).view_rodata().view().depth
            &&& post.prc_mp.spec_index(p).view_rodata().view().pcid == pre.prc_mp.spec_index(p).view_rodata().view().pcid
            &&& post.prc_mp.spec_index(p).view_rodata().view().owning_container == pre.prc_mp.spec_index(p).view_rodata().view().owning_container
            &&& post.prc_mp.spec_index(p).view_ghost().uppertree_seq.view() == pre.prc_mp.spec_index(p).view_ghost().uppertree_seq.view()
            &&& post.prc_mp.spec_index(p).view_ghost().subtree_set.view() == pre.prc_mp.spec_index(p).view_ghost().subtree_set.view()
            &&& post.prc_mp.spec_index(p).being_killed() == pre.prc_mp.spec_index(p).being_killed()
            &&& post.prc_mp.spec_index(p).view().owned_threads.view() == pre.prc_mp.spec_index(p).view().owned_threads.view()
        }
    &&& post.thr_mp.dom() == pre.thr_mp.dom()
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)]
        pre.thr_mp.dom().contains(t) ==> {
            &&& post.thr_mp.spec_index(t).locking_thread() == pre.thr_mp.spec_index(t).locking_thread()
            &&& post.thr_mp.spec_index(t).view().state == pre.thr_mp.spec_index(t).view().state
            &&& post.thr_mp.spec_index(t).view().caller == pre.thr_mp.spec_index(t).view().caller
            &&& post.thr_mp.spec_index(t).view().callee == pre.thr_mp.spec_index(t).view().callee
            &&& post.thr_mp.spec_index(t).view().owning_container == pre.thr_mp.spec_index(t).view().owning_container
            &&& post.thr_mp.spec_index(t).view().owning_proc == pre.thr_mp.spec_index(t).view().owning_proc
            &&& post.thr_mp.spec_index(t).view().last_cpu == pre.thr_mp.spec_index(t).view().last_cpu
            &&& post.thr_mp.spec_index(t).view().quota_4k == pre.thr_mp.spec_index(t).view().quota_4k
            &&& post.thr_mp.spec_index(t).view().quota_2m == pre.thr_mp.spec_index(t).view().quota_2m
            &&& post.thr_mp.spec_index(t).view().quota_1g == pre.thr_mp.spec_index(t).view().quota_1g
            &&& post.thr_mp.spec_index(t).view().endpoint_descriptors.view() == pre.thr_mp.spec_index(t).view().endpoint_descriptors.view()
            &&& post.thr_mp.spec_index(t).view().blocking_endpoint_ptr == pre.thr_mp.spec_index(t).view().blocking_endpoint_ptr
            &&& post.thr_mp.spec_index(t).view().ipc_payload == pre.thr_mp.spec_index(t).view().ipc_payload
            &&& post.thr_mp.spec_index(t).view().error_code == pre.thr_mp.spec_index(t).view().error_code
            &&& post.thr_mp.spec_index(t).view().trap_frame == pre.thr_mp.spec_index(t).view().trap_frame
            &&& post.thr_mp.spec_index(t).view().syscall_progress == pre.thr_mp.spec_index(t).view().syscall_progress
            &&& post.thr_mp.spec_index(t).being_killed() == pre.thr_mp.spec_index(t).being_killed()
        }
}

/// The live process running on `cpu_id` moves `delta` 4K quota to its live running thread; only the cpu,
/// process, and thread maps change, and each changed entry keeps its lock state and every other user field.
#[verifier::opaque]
pub open spec fn kernel_process2thread_quota_4k_changed(pre: &KernelK, post: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, delta: int) -> bool {
    let cpu = pre.cpu_arr.spec_index(cpu_id).value.view().view();
    let process = pre.prc_mp.spec_index(process_ptr);
    let thread = pre.thr_mp.spec_index(thread_ptr);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& pre.cpu_arr.spec_index(cpu_id).value.locking_thread() is None
    &&& cpu.state is Running
    &&& cpu.current_process == Some(process_ptr)
    &&& cpu.current_thread == Some(thread_ptr)
    &&& process.locking_thread() is None
    &&& !process.being_killed()
    &&& process.view().quota_4k >= delta
    &&& thread.locking_thread() is None
    &&& !thread.being_killed()
    &&& thread.view().quota_4k + delta <= usize::MAX
    &&& delta > 0
    &&& *post == (KernelK { cpu_arr: post.cpu_arr, prc_mp: post.prc_mp, thr_mp: post.thr_mp, ..*pre })
    &&& pre.prc_mp.dom().contains(process_ptr)
    &&& pre.thr_mp.dom().contains(thread_ptr)
    &&& forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
        index_valid(NUM_CPUS, i) ==> {
            &&& post.cpu_arr.spec_index(i).value.locking_thread() == pre.cpu_arr.spec_index(i).value.locking_thread()
            &&& post.cpu_arr.spec_index(i).value.view().view().owning_container == pre.cpu_arr.spec_index(i).value.view().view().owning_container
            &&& post.cpu_arr.spec_index(i).value.view().view().state == pre.cpu_arr.spec_index(i).value.view().view().state
            &&& post.cpu_arr.spec_index(i).value.view().view().current_process == pre.cpu_arr.spec_index(i).value.view().view().current_process
            &&& post.cpu_arr.spec_index(i).value.view().view().current_thread == pre.cpu_arr.spec_index(i).value.view().view().current_thread
            &&& post.cpu_arr.spec_index(i).value.killer_info() == pre.cpu_arr.spec_index(i).value.killer_info()
        }
    &&& post.prc_mp.dom() == pre.prc_mp.dom()
    &&& forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
        pre.prc_mp.dom().contains(p) ==> {
            &&& post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread()
            &&& post.prc_mp.spec_index(p).view().zombie == pre.prc_mp.spec_index(p).view().zombie
            &&& post.prc_mp.spec_index(p).view().pagetable == pre.prc_mp.spec_index(p).view().pagetable
            &&& post.prc_mp.spec_index(p).view().iommu_table == pre.prc_mp.spec_index(p).view().iommu_table
            &&& post.prc_mp.spec_index(p).view_ghost().owned_pci_functions.view() == pre.prc_mp.spec_index(p).view_ghost().owned_pci_functions.view()
            &&& post.prc_mp.spec_index(p).view().quota_4k as int == pre.prc_mp.spec_index(p).view().quota_4k as int - if p == process_ptr { delta } else { 0 }
            &&& post.prc_mp.spec_index(p).view().quota_2m == pre.prc_mp.spec_index(p).view().quota_2m
            &&& post.prc_mp.spec_index(p).view().quota_1g == pre.prc_mp.spec_index(p).view().quota_1g
            &&& post.prc_mp.spec_index(p).view().children.view() == pre.prc_mp.spec_index(p).view().children.view()
            &&& post.prc_mp.spec_index(p).view_rodata().view().parent == pre.prc_mp.spec_index(p).view_rodata().view().parent
            &&& post.prc_mp.spec_index(p).view_rodata().view().depth == pre.prc_mp.spec_index(p).view_rodata().view().depth
            &&& post.prc_mp.spec_index(p).view_rodata().view().pcid == pre.prc_mp.spec_index(p).view_rodata().view().pcid
            &&& post.prc_mp.spec_index(p).view_rodata().view().owning_container == pre.prc_mp.spec_index(p).view_rodata().view().owning_container
            &&& post.prc_mp.spec_index(p).view_ghost().uppertree_seq.view() == pre.prc_mp.spec_index(p).view_ghost().uppertree_seq.view()
            &&& post.prc_mp.spec_index(p).view_ghost().subtree_set.view() == pre.prc_mp.spec_index(p).view_ghost().subtree_set.view()
            &&& post.prc_mp.spec_index(p).being_killed() == pre.prc_mp.spec_index(p).being_killed()
            &&& post.prc_mp.spec_index(p).view().owned_threads.view() == pre.prc_mp.spec_index(p).view().owned_threads.view()
        }
    &&& post.thr_mp.dom() == pre.thr_mp.dom()
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)]
        pre.thr_mp.dom().contains(t) ==> {
            &&& post.thr_mp.spec_index(t).locking_thread() == pre.thr_mp.spec_index(t).locking_thread()
            &&& post.thr_mp.spec_index(t).view().state == pre.thr_mp.spec_index(t).view().state
            &&& post.thr_mp.spec_index(t).view().caller == pre.thr_mp.spec_index(t).view().caller
            &&& post.thr_mp.spec_index(t).view().callee == pre.thr_mp.spec_index(t).view().callee
            &&& post.thr_mp.spec_index(t).view().owning_container == pre.thr_mp.spec_index(t).view().owning_container
            &&& post.thr_mp.spec_index(t).view().owning_proc == pre.thr_mp.spec_index(t).view().owning_proc
            &&& post.thr_mp.spec_index(t).view().last_cpu == pre.thr_mp.spec_index(t).view().last_cpu
            &&& post.thr_mp.spec_index(t).view().quota_4k as int == pre.thr_mp.spec_index(t).view().quota_4k as int + if t == thread_ptr { delta } else { 0 }
            &&& post.thr_mp.spec_index(t).view().quota_2m == pre.thr_mp.spec_index(t).view().quota_2m
            &&& post.thr_mp.spec_index(t).view().quota_1g == pre.thr_mp.spec_index(t).view().quota_1g
            &&& post.thr_mp.spec_index(t).view().endpoint_descriptors.view() == pre.thr_mp.spec_index(t).view().endpoint_descriptors.view()
            &&& post.thr_mp.spec_index(t).view().blocking_endpoint_ptr == pre.thr_mp.spec_index(t).view().blocking_endpoint_ptr
            &&& post.thr_mp.spec_index(t).view().ipc_payload == pre.thr_mp.spec_index(t).view().ipc_payload
            &&& post.thr_mp.spec_index(t).view().error_code == pre.thr_mp.spec_index(t).view().error_code
            &&& post.thr_mp.spec_index(t).view().trap_frame == pre.thr_mp.spec_index(t).view().trap_frame
            &&& post.thr_mp.spec_index(t).view().syscall_progress == pre.thr_mp.spec_index(t).view().syscall_progress
            &&& post.thr_mp.spec_index(t).being_killed() == pre.thr_mp.spec_index(t).being_killed()
        }
}

/// The live process running on `cpu_id` moves `delta` 2M quota to its live running thread; only the cpu,
/// process, and thread maps change, and each changed entry keeps its lock state and every other user field.
#[verifier::opaque]
pub open spec fn kernel_process2thread_quota_2m_changed(pre: &KernelK, post: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, delta: int) -> bool {
    let cpu = pre.cpu_arr.spec_index(cpu_id).value.view().view();
    let process = pre.prc_mp.spec_index(process_ptr);
    let thread = pre.thr_mp.spec_index(thread_ptr);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& pre.cpu_arr.spec_index(cpu_id).value.locking_thread() is None
    &&& cpu.state is Running
    &&& cpu.current_process == Some(process_ptr)
    &&& cpu.current_thread == Some(thread_ptr)
    &&& process.locking_thread() is None
    &&& !process.being_killed()
    &&& process.view().quota_2m >= delta
    &&& thread.locking_thread() is None
    &&& !thread.being_killed()
    &&& thread.view().quota_2m + delta <= usize::MAX
    &&& delta > 0
    &&& *post == (KernelK { cpu_arr: post.cpu_arr, prc_mp: post.prc_mp, thr_mp: post.thr_mp, ..*pre })
    &&& pre.prc_mp.dom().contains(process_ptr)
    &&& pre.thr_mp.dom().contains(thread_ptr)
    &&& forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
        index_valid(NUM_CPUS, i) ==> {
            &&& post.cpu_arr.spec_index(i).value.locking_thread() == pre.cpu_arr.spec_index(i).value.locking_thread()
            &&& post.cpu_arr.spec_index(i).value.view().view().owning_container == pre.cpu_arr.spec_index(i).value.view().view().owning_container
            &&& post.cpu_arr.spec_index(i).value.view().view().state == pre.cpu_arr.spec_index(i).value.view().view().state
            &&& post.cpu_arr.spec_index(i).value.view().view().current_process == pre.cpu_arr.spec_index(i).value.view().view().current_process
            &&& post.cpu_arr.spec_index(i).value.view().view().current_thread == pre.cpu_arr.spec_index(i).value.view().view().current_thread
            &&& post.cpu_arr.spec_index(i).value.killer_info() == pre.cpu_arr.spec_index(i).value.killer_info()
        }
    &&& post.prc_mp.dom() == pre.prc_mp.dom()
    &&& forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
        pre.prc_mp.dom().contains(p) ==> {
            &&& post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread()
            &&& post.prc_mp.spec_index(p).view().zombie == pre.prc_mp.spec_index(p).view().zombie
            &&& post.prc_mp.spec_index(p).view().pagetable == pre.prc_mp.spec_index(p).view().pagetable
            &&& post.prc_mp.spec_index(p).view().iommu_table == pre.prc_mp.spec_index(p).view().iommu_table
            &&& post.prc_mp.spec_index(p).view_ghost().owned_pci_functions.view() == pre.prc_mp.spec_index(p).view_ghost().owned_pci_functions.view()
            &&& post.prc_mp.spec_index(p).view().quota_4k == pre.prc_mp.spec_index(p).view().quota_4k
            &&& post.prc_mp.spec_index(p).view().quota_2m as int == pre.prc_mp.spec_index(p).view().quota_2m as int - if p == process_ptr { delta } else { 0 }
            &&& post.prc_mp.spec_index(p).view().quota_1g == pre.prc_mp.spec_index(p).view().quota_1g
            &&& post.prc_mp.spec_index(p).view().children.view() == pre.prc_mp.spec_index(p).view().children.view()
            &&& post.prc_mp.spec_index(p).view_rodata().view().parent == pre.prc_mp.spec_index(p).view_rodata().view().parent
            &&& post.prc_mp.spec_index(p).view_rodata().view().depth == pre.prc_mp.spec_index(p).view_rodata().view().depth
            &&& post.prc_mp.spec_index(p).view_rodata().view().pcid == pre.prc_mp.spec_index(p).view_rodata().view().pcid
            &&& post.prc_mp.spec_index(p).view_rodata().view().owning_container == pre.prc_mp.spec_index(p).view_rodata().view().owning_container
            &&& post.prc_mp.spec_index(p).view_ghost().uppertree_seq.view() == pre.prc_mp.spec_index(p).view_ghost().uppertree_seq.view()
            &&& post.prc_mp.spec_index(p).view_ghost().subtree_set.view() == pre.prc_mp.spec_index(p).view_ghost().subtree_set.view()
            &&& post.prc_mp.spec_index(p).being_killed() == pre.prc_mp.spec_index(p).being_killed()
            &&& post.prc_mp.spec_index(p).view().owned_threads.view() == pre.prc_mp.spec_index(p).view().owned_threads.view()
        }
    &&& post.thr_mp.dom() == pre.thr_mp.dom()
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)]
        pre.thr_mp.dom().contains(t) ==> {
            &&& post.thr_mp.spec_index(t).locking_thread() == pre.thr_mp.spec_index(t).locking_thread()
            &&& post.thr_mp.spec_index(t).view().state == pre.thr_mp.spec_index(t).view().state
            &&& post.thr_mp.spec_index(t).view().caller == pre.thr_mp.spec_index(t).view().caller
            &&& post.thr_mp.spec_index(t).view().callee == pre.thr_mp.spec_index(t).view().callee
            &&& post.thr_mp.spec_index(t).view().owning_container == pre.thr_mp.spec_index(t).view().owning_container
            &&& post.thr_mp.spec_index(t).view().owning_proc == pre.thr_mp.spec_index(t).view().owning_proc
            &&& post.thr_mp.spec_index(t).view().last_cpu == pre.thr_mp.spec_index(t).view().last_cpu
            &&& post.thr_mp.spec_index(t).view().quota_4k == pre.thr_mp.spec_index(t).view().quota_4k
            &&& post.thr_mp.spec_index(t).view().quota_2m as int == pre.thr_mp.spec_index(t).view().quota_2m as int + if t == thread_ptr { delta } else { 0 }
            &&& post.thr_mp.spec_index(t).view().quota_1g == pre.thr_mp.spec_index(t).view().quota_1g
            &&& post.thr_mp.spec_index(t).view().endpoint_descriptors.view() == pre.thr_mp.spec_index(t).view().endpoint_descriptors.view()
            &&& post.thr_mp.spec_index(t).view().blocking_endpoint_ptr == pre.thr_mp.spec_index(t).view().blocking_endpoint_ptr
            &&& post.thr_mp.spec_index(t).view().ipc_payload == pre.thr_mp.spec_index(t).view().ipc_payload
            &&& post.thr_mp.spec_index(t).view().error_code == pre.thr_mp.spec_index(t).view().error_code
            &&& post.thr_mp.spec_index(t).view().trap_frame == pre.thr_mp.spec_index(t).view().trap_frame
            &&& post.thr_mp.spec_index(t).view().syscall_progress == pre.thr_mp.spec_index(t).view().syscall_progress
            &&& post.thr_mp.spec_index(t).being_killed() == pre.thr_mp.spec_index(t).being_killed()
        }
}

#[verifier::opaque]
pub open spec fn kernel_process_added(pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr) -> bool {
    &&& !pre.prc_mp.dom().contains(process_ptr)
    &&& post.prc_mp.dom().contains(process_ptr)
}

#[verifier::opaque]
pub open spec fn kernel_process_4k_mapping_changed(pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr) -> bool {
    &&& pre.prc_mp.dom().contains(process_ptr)
    &&& post.prc_mp.dom().contains(process_ptr)
    &&& !pre.prc_mp.spec_index(process_ptr).view().zombie
    &&& !post.prc_mp.spec_index(process_ptr).view().zombie
    &&& pre.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr
    &&& post.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr
    &&& pre.pt_mp.dom().contains(pagetable_ptr)
    &&& post.pt_mp.dom().contains(pagetable_ptr)
    &&& pre.pt_mp.spec_index(pagetable_ptr).view().mapping_4k().filter_keys(|v: VAddr| pre.pt_mp.spec_index(pagetable_ptr).view().mapping_4k().spec_index(v).present).dom().contains(va)
        != post.pt_mp.spec_index(pagetable_ptr).view().mapping_4k().filter_keys(|v: VAddr| post.pt_mp.spec_index(pagetable_ptr).view().mapping_4k().spec_index(v).present).dom().contains(va)
}
#[verifier::opaque]
pub open spec fn kernel_u_cpu_tlb_cleared(pre: KernelU, post: KernelU, pcid: Pcid) -> bool {
    let changed = post.cpu_tlb.dom().filter(|key: (CpuId, Pcid)| !pre.cpu_tlb.dom().contains(key) || pre.cpu_tlb[key] != post.cpu_tlb[key]);
    &&& pre.cpu_tlb.dom().subset_of(post.cpu_tlb.dom())
    &&& changed.len() == 1
    &&& forall|key: (CpuId, Pcid)| #![trigger changed.contains(key)] changed.contains(key) ==> {
        &&& index_valid(NUM_CPUS, key.0)
        &&& key.1 == pcid
        &&& post.cpu_tlb[key] == (SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })
    }
    &&& post == (KernelU { cpu_tlb: post.cpu_tlb, ..pre })
}

#[verifier::opaque]
pub open spec fn kernel_u_container_quota_4k_increased(pre: KernelU, post: KernelU, container: RwLockContainerPtr) -> bool {
    let changed = pre.container_map.dom().filter(|c: RwLockContainerPtr| pre.container_map[c] != post.container_map[c]);
    &&& pre.container_map.dom().contains(container)
    &&& post.container_map != pre.container_map
    &&& post.container_map.dom() == pre.container_map.dom()
    &&& changed.len() == 1
    &&& forall|c: RwLockContainerPtr| #![trigger changed.contains(c)] #![trigger post.container_map[c]] changed.contains(c) ==> {
        &&& c == container || pre.container_map[container].uppertree_seq.contains(c)
        &&& post.container_map[c].quota_4k > pre.container_map[c].quota_4k
        &&& post.container_map[c] == (ContainerU { quota_4k: post.container_map[c].quota_4k, ..pre.container_map[c] })
    }
    &&& post == (KernelU { container_map: post.container_map, ..pre })
}

#[verifier::opaque]
pub open spec fn kernel_u_container_root_published(
    pre: KernelU, post: KernelU, parent: RwLockContainerPtr, child: RwLockContainerPtr,
    process: RwLockProcessPtr, thread: RwLockThreadPtr, transfer_cpu: CpuId, funding: usize, process_quota: usize,
    moved: Set<PagePtr>, thread_page: PagePtr, progress: Option<SyscallProgress>,
) -> bool {
    let actual_moved = pre.container_map[parent].owned_pages.difference(post.container_map[parent].owned_pages);
    let ancestors = pre.container_map[parent].uppertree_seq.push(parent);
    &&& pre.container_map.dom().contains(parent)
    &&& !pre.container_map.dom().contains(child)
    &&& !pre.process_map.dom().contains(process)
    &&& pre.thread_map.dom().contains(thread)
    &&& funding >= process_quota
    &&& pre.thread_map[thread].quota_4k >= 8 + funding
    &&& pre.thread_map[thread].quota_2m >= 2
    &&& pre.cpu_array[transfer_cpu as int].state is Off
    &&& pre.cpu_array[transfer_cpu as int].owning_container == parent
    &&& post.container_map.dom() == pre.container_map.dom().insert(child)
    &&& forall|c: RwLockContainerPtr| #![trigger post.container_map[c]] pre.container_map.dom().contains(c) ==> post.container_map[c] == (ContainerU {
            children: if c == parent { pre.container_map[c].children.push(child) } else { pre.container_map[c].children },
            subtree_set: if ancestors.contains(c) { pre.container_map[c].subtree_set.insert(child) } else { pre.container_map[c].subtree_set },
            owned_pages: if c == parent { post.container_map[parent].owned_pages } else { pre.container_map[c].owned_pages },
            ..pre.container_map[c]
        })
    &&& post.container_map[parent].owned_pages.subset_of(pre.container_map[parent].owned_pages)
    &&& actual_moved == moved
    &&& !moved.contains(thread_page)
    &&& post.container_map[parent].owned_pages.contains(thread_page)
    &&& moved.contains(child) && moved.contains(process) && moved.contains(post.container_map[child].cpu_set)
    &&& post.container_map[child] == (ContainerU {
        lock_state: LockStateU::WriteLocked, zombie: false, children: Seq::empty(), uppertree_seq: ancestors, subtree_set: Set::empty(),
        root_process: process, owned_processes: set![process], owned_threads: Set::empty(), owned_endpoints: Set::empty(), owned_pages: moved,
        parent: Some(parent), depth: (pre.container_map[parent].depth + 1) as usize, scheduler: Seq::new(NUM_CPUS as nat, |i: int| Seq::<RwLockThreadPtr>::empty()),
        cpu_set: post.container_map[child].cpu_set, cpu_set_lock: LockStateU::WriteLocked,
        cpu_offline_requests: Seq::new(NUM_CPUS as nat, |i: int| false), free_pcids: Set::range(1usize, PCID_MAX).remove(1usize),
        quota_4k: (funding - process_quota) as usize, quota_2m: 0, quota_1g: 0, killed: false,
    })
    &&& post == (KernelU {
        cpu_array: pre.cpu_array.update(transfer_cpu as int, CpuU { lock_state: LockStateU::WriteLocked, ..pre.cpu_array[transfer_cpu as int] }),
        container_map: post.container_map,
        process_map: pre.process_map.insert(process, ProcessU {
            lock_state: LockStateU::WriteLocked, zombie: false,
            pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, mapping_4k: Map::empty(), mapping_2m: Map::empty(), mapping_1g: Map::empty() }),
            iommu_table: None, pcid: post.process_map[process].pcid, owning_container: child, owned_pci_functions: Set::empty(), quota_4k: process_quota, quota_2m: 0, quota_1g: 0,
            parent: None, children: Seq::empty(), depth: 0, uppertree_seq: Seq::empty(), subtree_set: Set::empty(), owned_threads: Seq::empty(), killed: false,
        }),
        thread_map: pre.thread_map.insert(thread, ThreadU {
            quota_4k: (pre.thread_map[thread].quota_4k - 8 - funding) as usize, quota_2m: (pre.thread_map[thread].quota_2m - 2) as usize,
            syscall_progress: progress, ..pre.thread_map[thread]
        }),
        ..pre
    })
}

#[verifier::opaque]
pub open spec fn kernel_u_cpu_and_page_owner_changed(pre: KernelU, post: KernelU, cpu: CpuId, source: RwLockContainerPtr, target: RwLockContainerPtr, page: PagePtr) -> bool {
    post == (KernelU {
        cpu_array: pre.cpu_array.update(cpu as int, CpuU { lock_state: LockStateU::Unlocked, owning_container: target, ..pre.cpu_array[cpu as int] }),
        container_map: pre.container_map.insert(source, ContainerU {
            cpu_set_lock: LockStateU::Unlocked, owned_pages: pre.container_map[source].owned_pages.remove(page), ..pre.container_map[source]
        }).insert(target, ContainerU { cpu_set_lock: LockStateU::Unlocked, owned_pages: pre.container_map[target].owned_pages.insert(page), ..pre.container_map[target] }),
        ..pre
    })
}

#[verifier::opaque]
pub open spec fn kernel_u_container_root_created(
    pre: KernelU, post: KernelU, parent: RwLockContainerPtr, child: RwLockContainerPtr, process: RwLockProcessPtr,
    thread: RwLockThreadPtr, transfer_cpu: CpuId, funding: usize, process_quota: usize, progress: Option<SyscallProgress>,
) -> bool {
    let moved = pre.container_map[parent].owned_pages.difference(post.container_map[parent].owned_pages);
    let ancestors = pre.container_map[parent].uppertree_seq.push(parent);
    &&& pre.container_map.dom().contains(parent)
    &&& !pre.container_map.dom().contains(child)
    &&& !pre.process_map.dom().contains(process)
    &&& pre.thread_map.dom().contains(thread)
    &&& funding >= process_quota
    &&& pre.thread_map[thread].quota_4k >= 8 + funding
    &&& pre.thread_map[thread].quota_2m >= 2
    &&& pre.cpu_array[transfer_cpu as int].state is Off
    &&& pre.cpu_array[transfer_cpu as int].owning_container == parent
    &&& post.container_map.dom() == pre.container_map.dom().insert(child)
    &&& forall|c: RwLockContainerPtr| #![trigger post.container_map[c]] pre.container_map.dom().contains(c) ==> post.container_map[c] == (ContainerU {
            children: if c == parent { pre.container_map[c].children.push(child) } else { pre.container_map[c].children },
            subtree_set: if ancestors.contains(c) { pre.container_map[c].subtree_set.insert(child) } else { pre.container_map[c].subtree_set },
            owned_pages: if c == parent { post.container_map[parent].owned_pages } else { pre.container_map[c].owned_pages },
            cpu_set_lock: if c == parent { LockStateU::Unlocked } else { pre.container_map[c].cpu_set_lock },
            ..pre.container_map[c]
        })
    &&& post.container_map[parent].owned_pages.subset_of(pre.container_map[parent].owned_pages)
    &&& moved.len() == 2 * 512 + 9 + funding
    &&& moved.contains(child) && moved.contains(process) && moved.contains(post.container_map[child].cpu_set)
    &&& post.container_map[child] == (ContainerU {
        lock_state: LockStateU::WriteLocked, zombie: false, children: Seq::empty(), uppertree_seq: ancestors, subtree_set: Set::empty(),
        root_process: process, owned_processes: set![process], owned_threads: Set::empty(), owned_endpoints: Set::empty(), owned_pages: moved,
        parent: Some(parent), depth: (pre.container_map[parent].depth + 1) as usize, scheduler: Seq::new(NUM_CPUS as nat, |i: int| Seq::<RwLockThreadPtr>::empty()),
        cpu_set: post.container_map[child].cpu_set, cpu_set_lock: LockStateU::Unlocked,
        cpu_offline_requests: Seq::new(NUM_CPUS as nat, |i: int| false), free_pcids: Set::range(1usize, PCID_MAX).remove(1usize),
        quota_4k: (funding - process_quota) as usize, quota_2m: 0, quota_1g: 0, killed: false,
    })
    &&& post == (KernelU {
        cpu_array: pre.cpu_array.update(transfer_cpu as int, CpuU { lock_state: LockStateU::Unlocked, owning_container: child, ..pre.cpu_array[transfer_cpu as int] }),
        container_map: post.container_map,
        process_map: pre.process_map.insert(process, ProcessU {
            lock_state: LockStateU::WriteLocked, zombie: false,
            pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, mapping_4k: Map::empty(), mapping_2m: Map::empty(), mapping_1g: Map::empty() }),
            iommu_table: None, pcid: post.process_map[process].pcid, owning_container: child, owned_pci_functions: Set::empty(), quota_4k: process_quota, quota_2m: 0, quota_1g: 0,
            parent: None, children: Seq::empty(), depth: 0, uppertree_seq: Seq::empty(), subtree_set: Set::empty(), owned_threads: Seq::empty(), killed: false,
        }),
        thread_map: pre.thread_map.insert(thread, ThreadU {
            quota_4k: (pre.thread_map[thread].quota_4k - 8 - funding) as usize, quota_2m: (pre.thread_map[thread].quota_2m - 2) as usize,
            syscall_progress: progress, ..pre.thread_map[thread]
        }),
        ..pre
    })
}

/// The objects a share names: the thread whose process is the source, the target process, the
/// thread whose quota pays for target directory pages, the container that owns the target, and the
/// container that hands over directory pages.
pub ghost struct Share4kObjects {
    pub source_thread: RwLockThreadPtr,
    pub target: RwLockProcessPtr,
    pub quota_thread: RwLockThreadPtr,
    pub target_container: RwLockContainerPtr,
    pub transfer_source: Option<RwLockContainerPtr>,
}

/// The objects of the share recorded by the thread running on `cpu_id`: a new process shares into
/// its recorded child, a new container into its recorded child container's root process, and a
/// pages rendezvous from the sender into the receiver, which is the recorded peer exactly when the
/// peer is receiving.
pub open spec fn share_4k_objects(u: KernelU, cpu_id: CpuId) -> Share4kObjects {
    let caller = u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = u.thread_map[caller];
    match thread.syscall_progress->Some_0->Share4k_origin {
        Share4kOrigin::NewProcess(record) => Share4kObjects {
            source_thread: caller, target: record.child->Some_0, quota_thread: caller, target_container: thread.owning_container, transfer_source: None,
        },
        Share4kOrigin::NewContainer(record) => Share4kObjects {
            source_thread: caller, target: u.container_map[record.child_container->Some_0].root_process, quota_thread: caller,
            target_container: record.child_container->Some_0, transfer_source: Some(thread.owning_container),
        },
        Share4kOrigin::IpcPages { peer } => {
            let receiver = if u.thread_map[peer].state is RECEIVING { peer } else { caller };
            Share4kObjects {
                source_thread: if u.thread_map[peer].state is RECEIVING { caller } else { peer }, target: u.thread_map[receiver].owning_proc,
                quota_thread: receiver, target_container: u.thread_map[receiver].owning_container, transfer_source: None,
            }
        },
    }
}

/// The cpu and its running thread are write-locked while the thread records a share, and so is the peer of a
/// pages rendezvous.
pub open spec fn share_4k_locked(u: KernelU, cpu_id: CpuId) -> bool {
    let caller = u.cpu_array[cpu_id as int].current_thread->Some_0;
    let origin = u.thread_map[caller].syscall_progress->Some_0->Share4k_origin;
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& u.cpu_array[cpu_id as int].lock_state is WriteLocked
    &&& u.cpu_array[cpu_id as int].current_thread is Some
    &&& u.thread_map.dom().contains(caller)
    &&& u.thread_map[caller].lock_state is WriteLocked
    &&& u.thread_map[caller].syscall_progress is Some
    &&& u.thread_map[caller].syscall_progress->Some_0 is Share4k
    &&& origin is IpcPages ==> u.thread_map.dom().contains(origin->IpcPages_peer) && u.thread_map[origin->IpcPages_peer].lock_state is WriteLocked
}

/// `share_4k_objects` read from the kernel objects it projects from.
#[verifier::opaque]
pub open spec fn share_4k_objects_k(krnl: KernelK, cpu_id: CpuId) -> Share4kObjects {
    let caller = krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0;
    let thread = krnl.thr_mp.spec_index(caller).view();
    match thread.syscall_progress.view()->Some_0->Share4k_origin {
        Share4kOrigin::NewProcess(record) => Share4kObjects {
            source_thread: caller, target: record.child->Some_0, quota_thread: caller, target_container: thread.owning_container, transfer_source: None,
        },
        Share4kOrigin::NewContainer(record) => Share4kObjects {
            source_thread: caller, target: krnl.ctn_mp.spec_index(record.child_container->Some_0).view().root_process, quota_thread: caller,
            target_container: record.child_container->Some_0, transfer_source: Some(thread.owning_container),
        },
        Share4kOrigin::IpcPages { peer } => {
            let receiver = if krnl.thr_mp.spec_index(peer).view().state is RECEIVING { peer } else { caller };
            Share4kObjects {
                source_thread: if krnl.thr_mp.spec_index(peer).view().state is RECEIVING { caller } else { peer },
                target: krnl.thr_mp.spec_index(receiver).view().owning_proc, quota_thread: receiver,
                target_container: krnl.thr_mp.spec_index(receiver).view().owning_container, transfer_source: None,
            }
        },
    }
}

/// `container_ptr`, the running thread's container or a direct child of that live, non-zombie container, records an
/// offline request for `target`, a non-Off cpu it owns whose request bit is clear.
#[verifier::opaque]
pub open spec fn kernel_u_cpu_offline_request_changed(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, container_ptr: RwLockContainerPtr, target: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let container = old_u.container_map[container_ptr];
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& old_u.container_map.dom().contains(container_ptr)
    &&& cpu.owning_container == container_ptr || (container.parent == Some(cpu.owning_container) && old_u.container_map.dom().contains(cpu.owning_container)
        && !old_u.container_map[cpu.owning_container].killed && !old_u.container_map[cpu.owning_container].zombie)
    &&& index_valid(NUM_CPUS, target)
    &&& old_u.cpu_array[target as int].owning_container == container_ptr
    &&& !(old_u.cpu_array[target as int].state is Off)
    &&& container.cpu_offline_requests.len() == NUM_CPUS
    &&& !container.cpu_offline_requests[target as int]
    &&& new_u == (KernelU {
        container_map: old_u.container_map.insert(container_ptr, ContainerU { cpu_offline_requests: container.cpu_offline_requests.update(target as int, true), ..container }),
        ..old_u
    })
}

/// `target`, an Off cpu owned by `container_ptr`, the running thread's container or a direct child of that
/// live, non-zombie container, becomes Idle.
#[verifier::opaque]
pub open spec fn kernel_u_cpu_online_changed(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, container_ptr: RwLockContainerPtr, target: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let target_cpu = old_u.cpu_array[target as int];
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& old_u.container_map.dom().contains(container_ptr)
    &&& cpu.owning_container == container_ptr || (old_u.container_map[container_ptr].parent == Some(cpu.owning_container) && old_u.container_map.dom().contains(cpu.owning_container)
        && !old_u.container_map[cpu.owning_container].killed && !old_u.container_map[cpu.owning_container].zombie)
    &&& index_valid(NUM_CPUS, target)
    &&& old_u.cpu_array.len() == NUM_CPUS
    &&& target_cpu.owning_container == container_ptr
    &&& target_cpu.state is Off
    &&& new_u == (KernelU { cpu_array: old_u.cpu_array.update(target as int, CpuU { state: CpuState::Idle, ..target_cpu }), ..old_u })
}

/// The running process, a live owner of `(bus, device, function)` with an IOMMU table, attaches DMA
/// translation to that function; nothing else changes.
#[verifier::opaque]
pub open spec fn kernel_u_pci_attach_changed(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, bus: usize, device: usize, function: usize) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let process = old_u.process_map[cpu.current_process.unwrap()];
    let attached = old_u.iommu_root_table.attached;
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& cpu.current_process is Some
    &&& old_u.process_map.dom().contains(cpu.current_process.unwrap())
    &&& !process.killed
    &&& pci_bdf_valid(bus, device, function)
    &&& process.owned_pci_functions.contains((bus, device, function))
    &&& process.iommu_table is Some
    &&& !attached[bus as int][device as int][function as int]
    &&& new_u == (KernelU {
        iommu_root_table: IommuRootTableU { attached: seq3_update(attached, bus as int, device as int, function as int, true), ..old_u.iommu_root_table },
        ..old_u
    })
}

/// `syscall_cpu_offline_request` and `syscall_cpu_offline_request_child` with every lock released again:
/// only the `target` request bit of the table of `container_ptr`, the caller's container or a direct child
/// of that live, non-zombie container, is set. On the child path the caller's container was locked and released.
#[verifier::opaque]
pub open spec fn kernel_cpu_offline_request_changed(pre: &KernelK, post: &KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, target: CpuId) -> bool {
    let cpu = pre.cpu_arr.spec_index(cpu_id).value.view().view();
    let caller = pre.ctn_mp.spec_index(cpu.owning_container);
    let cpu_set_ptr = pre.ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set;
    let flags_ptr = cpu_offline_flags_ptr(container_ptr);
    &&& pre.inv()
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& pre.cpu_arr.spec_index(cpu_id).value.locking_thread() is None
    &&& cpu.state is Running
    &&& pre.ctn_mp.dom().contains(container_ptr)
    &&& pre.ctn_mp.dom().contains(cpu.owning_container)
    &&& cpu.owning_container == container_ptr || (pre.ctn_mp.spec_index(container_ptr).view_rodata().view().parent == Some(cpu.owning_container) && caller.locking_thread() is None
        && !caller.being_killed() && !caller.view().zombie)
    &&& pre.cpu_set_mp.spec_index(cpu_set_ptr).locking_thread() is None
    &&& index_valid(NUM_CPUS, target)
    &&& pre.cpu_arr.spec_index(target).value.view().view().owning_container == container_ptr
    &&& !(pre.cpu_arr.spec_index(target).value.view().view().state is Off)
    &&& !pre.cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(target).view().view().requested
    &&& *post == (KernelK { cpu_arr: post.cpu_arr, cpu_set_mp: post.cpu_set_mp, cpu_offline_mp: post.cpu_offline_mp, ctn_mp: post.ctn_mp, ..*pre })
    &&& post.cpu_arr.unchanged_except(&pre.cpu_arr, cpu_id)
    &&& post.cpu_arr.spec_index(cpu_id).value.locking_thread() is None
    &&& post.cpu_arr.spec_index(cpu_id).value.killer_info() == pre.cpu_arr.spec_index(cpu_id).value.killer_info()
    &&& post.ctn_mp.unchanged_except(&pre.ctn_mp, cpu.owning_container)
    &&& post.ctn_mp.spec_index(cpu.owning_container).view() == caller.view()
    &&& post.ctn_mp.spec_index(cpu.owning_container).view_rodata() == caller.view_rodata()
    &&& post.ctn_mp.spec_index(cpu.owning_container).view_ghost() == caller.view_ghost()
    &&& post.ctn_mp.spec_index(cpu.owning_container).being_killed() == caller.being_killed()
    &&& post.ctn_mp.spec_index(cpu.owning_container).locking_thread() == caller.locking_thread()
    &&& post.cpu_set_mp.unchanged_except(&pre.cpu_set_mp, cpu_set_ptr)
    &&& post.cpu_set_mp.spec_index(cpu_set_ptr).locking_thread() is None
    &&& post.cpu_offline_mp.unchanged_except(&pre.cpu_offline_mp, flags_ptr)
    &&& cpu_offline_requests_of(post.cpu_offline_mp.spec_index(flags_ptr)) == cpu_offline_requests_of(pre.cpu_offline_mp.spec_index(flags_ptr)).update(target as int, true)
}

/// `syscall_cpu_online` and `syscall_cpu_online_child` with every lock released again: `target` left Off
/// for Idle and was reopened in the cpu set of `container_ptr`, the caller's container or a direct child of
/// that live, non-zombie container. On the child path the caller's container was locked and released.
#[verifier::opaque]
pub open spec fn kernel_cpu_online_changed(pre: &KernelK, post: &KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, target: CpuId) -> bool {
    let cpu = pre.cpu_arr.spec_index(cpu_id).value.view().view();
    let caller = pre.ctn_mp.spec_index(cpu.owning_container);
    let target_cpu = pre.cpu_arr.spec_index(target).value.view().view();
    let cpu_set_ptr = pre.ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set;
    &&& pre.inv()
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& pre.cpu_arr.spec_index(cpu_id).value.locking_thread() is None
    &&& cpu.state is Running
    &&& pre.ctn_mp.dom().contains(container_ptr)
    &&& pre.ctn_mp.dom().contains(cpu.owning_container)
    &&& cpu.owning_container == container_ptr || (pre.ctn_mp.spec_index(container_ptr).view_rodata().view().parent == Some(cpu.owning_container) && caller.locking_thread() is None
        && !caller.being_killed() && !caller.view().zombie)
    &&& pre.cpu_set_mp.spec_index(cpu_set_ptr).locking_thread() is None
    &&& index_valid(NUM_CPUS, target)
    &&& pre.cpu_arr.spec_index(target).value.locking_thread() is None
    &&& target_cpu.owning_container == container_ptr
    &&& target_cpu.state is Off
    &&& *post == (KernelK { cpu_arr: post.cpu_arr, cpu_set_mp: post.cpu_set_mp, ctn_mp: post.ctn_mp, ..*pre })
    &&& forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)] index_valid(NUM_CPUS, i) && i != cpu_id && i != target ==> post.cpu_arr.spec_index(i) == pre.cpu_arr.spec_index(i)
    &&& post.cpu_arr.spec_index(cpu_id).value.view() == pre.cpu_arr.spec_index(cpu_id).value.view()
    &&& post.cpu_arr.spec_index(cpu_id).value.locking_thread() is None
    &&& post.cpu_arr.spec_index(cpu_id).value.killer_info() == pre.cpu_arr.spec_index(cpu_id).value.killer_info()
    &&& post.cpu_arr.spec_index(target).value.view().view() == (CpuView { state: CpuState::Idle, ..target_cpu })
    &&& post.cpu_arr.spec_index(target).value.locking_thread() is None
    &&& post.cpu_arr.spec_index(target).value.killer_info() == pre.cpu_arr.spec_index(target).value.killer_info()
    &&& post.ctn_mp.unchanged_except(&pre.ctn_mp, cpu.owning_container)
    &&& post.ctn_mp.spec_index(cpu.owning_container).view() == caller.view()
    &&& post.ctn_mp.spec_index(cpu.owning_container).view_rodata() == caller.view_rodata()
    &&& post.ctn_mp.spec_index(cpu.owning_container).view_ghost() == caller.view_ghost()
    &&& post.ctn_mp.spec_index(cpu.owning_container).being_killed() == caller.being_killed()
    &&& post.ctn_mp.spec_index(cpu.owning_container).locking_thread() == caller.locking_thread()
    &&& post.cpu_set_mp.unchanged_except(&pre.cpu_set_mp, cpu_set_ptr)
    &&& post.cpu_set_mp.spec_index(cpu_set_ptr).locking_thread() is None
}

/// `cpu_id`'s TLB entries after it went Off: the default-PCID entry is flushed when `flushed_default_pcid`,
/// then every non-default PCID entry of the cpu is empty.
pub open spec fn cpu_tlb_after_cpu_went_off(tlb: Map<(CpuId, Pcid), SingleTLB>, cpu_id: CpuId, flushed_default_pcid: bool) -> Map<(CpuId, Pcid), SingleTLB> {
    let empty = SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() };
    let after_default = if flushed_default_pcid { tlb.insert((cpu_id, KERNEL_DEFAULT_PCID), empty) } else { tlb };
    Map::new(after_default.dom(), |key: (CpuId, Pcid)| if key.0 == cpu_id && key.1 != KERNEL_DEFAULT_PCID { empty } else { after_default[key] })
}

/// The non-Off cpu `cpu_id`, whose container `C` has a pending request for it, goes Off: its running
/// thread, if any, is requeued at the tail of shard `cpu_id` of `C`'s scheduler with `regs`, `C`'s request bit for the cpu is
/// cleared, and the cpu's TLB entries are flushed except an unflushed default-PCID entry.
#[verifier::opaque]
pub open spec fn kernel_u_cpu_went_off_changed(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, regs: Registers, flushed_default_pcid: bool) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let container_ptr = cpu.owning_container;
    let container = old_u.container_map.spec_index(container_ptr);
    let requeued = match cpu.current_thread {
        Some(prev) => old_u.thread_map.insert(prev, ThreadU { state: ThreadState::SCHEDULED { cpu_id }, error_code: None, trap_frame: Some(regs), ..old_u.thread_map.spec_index(prev) }),
        None => old_u.thread_map,
    };
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& old_u.cpu_array.len() == NUM_CPUS
    &&& !(cpu.state is Off)
    &&& old_u.container_map.dom().contains(container_ptr)
    &&& container.cpu_offline_requests.len() == NUM_CPUS
    &&& container.cpu_offline_requests[cpu_id as int]
    &&& cpu.current_process is Some == cpu.current_thread is Some
    &&& (cpu.current_thread is Some ==> {
        let prev = old_u.thread_map.spec_index(cpu.current_thread.unwrap());
        &&& old_u.thread_map.dom().contains(cpu.current_thread.unwrap())
        &&& !prev.killed
        &&& prev.state == (ThreadState::RUNNING { cpu_id })
        &&& prev.owning_proc == cpu.current_process.unwrap()
        &&& old_u.process_map.dom().contains(cpu.current_process.unwrap())
        &&& !old_u.process_map.spec_index(cpu.current_process.unwrap()).killed
    })
    &&& new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { state: CpuState::Off, current_process: None, current_thread: None, ..cpu }),
        container_map: old_u.container_map.insert(container_ptr, ContainerU {
            scheduler: match cpu.current_thread {
                Some(prev) => container.scheduler.update(cpu_id as int, container.scheduler[cpu_id as int].push(prev)),
                None => container.scheduler,
            },
            cpu_offline_requests: container.cpu_offline_requests.update(cpu_id as int, false),
            ..container
        }),
        thread_map: requeued,
        cpu_tlb: cpu_tlb_after_cpu_went_off(old_u.cpu_tlb, cpu_id, flushed_default_pcid),
        ..old_u
    })
}

#[verifier::opaque]
/// `cpu_offline_check` with every lock released again: the non-Off cpu `cpu_id`, with a pending request of
/// its container, went Off, its live running thread (if any) was requeued at the tail of shard `cpu_id` with `regs`, the
/// request bit was cleared, and the cpu's TLB entries were flushed.
pub open spec fn kernel_cpu_went_off_fields(pre: &KernelK, post: &KernelK, cpu_id: CpuId, regs: Registers, flushed_default_pcid: bool) -> bool {
    let cpu = pre.cpu_arr.spec_index(cpu_id).value.view().view();
    let previous = cpu.current_thread;
    let container_ptr = cpu.owning_container;
    &&& index_valid(NUM_CPUS, cpu_id)
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
    &&& post.cpu_set_mp.dom() == pre.cpu_set_mp.dom()
    &&& forall|p: RwLockCpuSetPtr| #![trigger post.cpu_set_mp.spec_index(p)]
        pre.cpu_set_mp.dom().contains(p) ==> post.cpu_set_mp.spec_index(p).locking_thread() == pre.cpu_set_mp.spec_index(p).locking_thread()
    &&& kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, post.pt_mp)
    &&& kernel_pagetable_nonlock_fields_unchanged(pre.it_mp, post.it_mp)
    &&& kernel_process_nonlock_fields_unchanged(pre.prc_mp, post.prc_mp)
    &&& kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp)
    &&& post.irt.view().owners() == pre.irt.view().owners()
    &&& post.irt.view().iommu_roots() == pre.irt.view().iommu_roots()
    &&& post.iommu_tlb.view() == pre.iommu_tlb.view()
    &&& post.dflt_pt == pre.dflt_pt
    &&& post.cpu_tlb.view() == cpu_tlb_after_cpu_went_off(pre.cpu_tlb.view(), cpu_id, flushed_default_pcid)
    &&& pre.cpu_arr.spec_index(cpu_id).value.locking_thread() is None
    &&& !(cpu.state is Off)
    &&& pre.ctn_mp.dom().contains(container_ptr)
    &&& pre.cpu_set_mp.spec_index(pre.ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set).locking_thread() is None
    &&& pre.cpu_offline_mp.dom().contains(cpu_offline_flags_ptr(container_ptr))
    &&& cpu_offline_requests_of(pre.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(container_ptr)))[cpu_id as int]
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
            &&& b.state == if i == cpu_id { CpuState::Off } else { a.state }
            &&& b.current_process == if i == cpu_id { None } else { a.current_process }
            &&& b.current_thread == if i == cpu_id { None } else { a.current_thread }
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
            &&& b.view().owned_endpoints.view() == a.view().owned_endpoints.view()
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
            scheduler_shards_of(post.sched_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().scheduler)) == if c == container_ptr {
                match previous { Some(prev) => queue.update(cpu_id as int, queue[cpu_id as int].push(prev)), None => queue }
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
    &&& forall|c: RwLockContainerPtr| #![trigger post.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(c))]
        pre.ctn_mp.dom().contains(c) ==> cpu_offline_requests_of(post.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(c))) == if c == container_ptr {
            cpu_offline_requests_of(pre.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(c))).update(cpu_id as int, false)
        } else { cpu_offline_requests_of(pre.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(c))) }
    &&& post.thr_mp.dom() == pre.thr_mp.dom()
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)]
        pre.thr_mp.dom().contains(t) ==> {
            let a = pre.thr_mp.spec_index(t).view();
            let b = post.thr_mp.spec_index(t).view();
            &&& b.state == if previous == Some(t) { ThreadState::SCHEDULED { cpu_id } } else { a.state }
            &&& b.caller == a.caller
            &&& b.callee == a.callee
            &&& b.owning_container == a.owning_container
            &&& b.owning_proc == a.owning_proc
            &&& b.last_cpu == a.last_cpu
            &&& b.quota_4k == a.quota_4k
            &&& b.quota_2m == a.quota_2m
            &&& b.quota_1g == a.quota_1g
            &&& b.endpoint_descriptors.view() == a.endpoint_descriptors.view()
            &&& b.blocking_endpoint_ptr == a.blocking_endpoint_ptr
            &&& b.ipc_payload == a.ipc_payload
            &&& b.error_code == if previous == Some(t) { None } else { a.error_code }
            &&& (previous == Some(t) ==> b.trap_frame.is_some() && *b.trap_frame.get_some_0() == regs)
            &&& (previous != Some(t) ==> b.trap_frame == a.trap_frame)
            &&& b.syscall_progress.view() == a.syscall_progress.view()
            &&& post.thr_mp.spec_index(t).being_killed() == pre.thr_mp.spec_index(t).being_killed()
        }
}

/// One staging-thread quota funds a new empty receive endpoint of `container_ptr` held only at descriptor
/// `endpoint_index` of the staging thread, whose progress becomes `staging_progress`.
#[verifier::opaque]
pub open spec fn kernel_new_endpoint_fields(
    pre: &KernelK, post: &KernelK, container_ptr: RwLockContainerPtr, staging_thread_ptr: RwLockThreadPtr, endpoint_index: EndpointIdx,
    new_endpoint_ptr: RwLockEndpointPtr, staging_progress: Option<SyscallProgress>,
) -> bool {
    let new_endpoint = post.ep_mp.spec_index(new_endpoint_ptr);
    &&& post.irt.view().owners() == pre.irt.view().owners()
    &&& post.irt.view().iommu_roots() == pre.irt.view().iommu_roots()
    &&& post.cpu_tlb.view() == pre.cpu_tlb.view()
    &&& post.iommu_tlb.view() == pre.iommu_tlb.view()
    &&& pre.ctn_mp.dom().contains(container_ptr)
    &&& pre.thr_mp.dom().contains(staging_thread_ptr)
    &&& !pre.ep_mp.dom().contains(new_endpoint_ptr)
    &&& edp_idx_valid(endpoint_index)
    &&& pre.thr_mp.spec_index(staging_thread_ptr).view().quota_4k > 0
    &&& pre.thr_mp.spec_index(staging_thread_ptr).view().endpoint_descriptors.view()[endpoint_index as int] is None
    &&& post.thr_mp.spec_index(staging_thread_ptr).view().endpoint_descriptors.view()[endpoint_index as int] == Some(new_endpoint_ptr)
    &&& post.ep_mp.dom() == pre.ep_mp.dom().insert(new_endpoint_ptr)
    &&& forall|e: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(e)]
        pre.ep_mp.dom().contains(e) ==> {
            let a = pre.ep_mp.spec_index(e);
            let b = post.ep_mp.spec_index(e);
            &&& b.view().queue.view() == a.view().queue.view()
            &&& b.view().queue_state == a.view().queue_state
            &&& b.view().owning_threads.view() == a.view().owning_threads.view()
            &&& b.view().owning_container == a.view().owning_container
            &&& b.being_killed() == a.being_killed()
        }
    &&& new_endpoint.view().queue.view() == Seq::<RwLockThreadPtr>::empty()
    &&& new_endpoint.view().queue_state == EndpointState::RECEIVE
    &&& new_endpoint.view().owning_threads.view() == set![(staging_thread_ptr, endpoint_index)]
    &&& new_endpoint.view().owning_container == container_ptr
    &&& !new_endpoint.being_killed()
    &&& post.ctn_mp.dom() == pre.ctn_mp.dom()
    &&& forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)]
        pre.ctn_mp.dom().contains(c) ==> {
            &&& post.ctn_mp.spec_index(c).view() == if c == container_ptr {
                    Container { owned_endpoints: Ghost(pre.ctn_mp.spec_index(c).view().owned_endpoints.view().insert(new_endpoint_ptr)), ..pre.ctn_mp.spec_index(c).view() }
                } else { pre.ctn_mp.spec_index(c).view() }
            &&& post.ctn_mp.spec_index(c).view_rodata() == pre.ctn_mp.spec_index(c).view_rodata()
            &&& post.ctn_mp.spec_index(c).view_ghost() == pre.ctn_mp.spec_index(c).view_ghost()
            &&& post.ctn_mp.spec_index(c).being_killed() == pre.ctn_mp.spec_index(c).being_killed()
        }
    &&& post.sched_mp == pre.sched_mp
    &&& post.pcid_allc_mp == pre.pcid_allc_mp
    &&& post.allc_4k_mp == pre.allc_4k_mp
    &&& post.allc_2m_mp == pre.allc_2m_mp
    &&& post.allc_1g_mp == pre.allc_1g_mp
    &&& post.cpu_offline_mp == pre.cpu_offline_mp
    &&& post.cpu_set_mp == pre.cpu_set_mp
    &&& post.dflt_pt == pre.dflt_pt
    &&& post.pt_mp == pre.pt_mp
    &&& post.it_mp == pre.it_mp
    &&& kernel_cpu_nonlock_fields_unchanged(pre.cpu_arr, post.cpu_arr)
    &&& kernel_process_nonlock_fields_unchanged(pre.prc_mp, post.prc_mp)
    &&& post.thr_mp.dom() == pre.thr_mp.dom()
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)]
        pre.thr_mp.dom().contains(t) ==> {
            let a = pre.thr_mp.spec_index(t).view();
            let b = post.thr_mp.spec_index(t).view();
            &&& b.state == a.state
            &&& b.caller == a.caller
            &&& b.callee == a.callee
            &&& b.owning_container == a.owning_container
            &&& b.owning_proc == a.owning_proc
            &&& b.last_cpu == a.last_cpu
            &&& b.quota_4k == if t == staging_thread_ptr { a.quota_4k - 1 } else { a.quota_4k as int }
            &&& b.quota_2m == a.quota_2m
            &&& b.quota_1g == a.quota_1g
            &&& b.endpoint_descriptors.view() == if t == staging_thread_ptr {
                    a.endpoint_descriptors.view().update(endpoint_index as int, Some(new_endpoint_ptr))
                } else { a.endpoint_descriptors.view() }
            &&& b.blocking_endpoint_ptr == a.blocking_endpoint_ptr
            &&& b.ipc_payload == a.ipc_payload
            &&& b.error_code == a.error_code
            &&& b.trap_frame == a.trap_frame
            &&& b.syscall_progress.view() == if t == staging_thread_ptr { staging_progress } else { a.syscall_progress.view() }
            &&& post.thr_mp.spec_index(t).being_killed() == pre.thr_mp.spec_index(t).being_killed()
        }
}

/// One quota of `thread_ptr` funds a new empty, unlocked receive endpoint `endpoint_ptr` of `container_ptr`,
/// installed at the thread's empty descriptor `endpoint_index`; the thread's progress is cleared.
#[verifier::opaque]
pub open spec fn kernel_u_new_endpoint_changed(
    old_u: KernelU, new_u: KernelU, container_ptr: RwLockContainerPtr, thread_ptr: RwLockThreadPtr, endpoint_index: EndpointIdx, endpoint_ptr: RwLockEndpointPtr,
) -> bool {
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let container = old_u.container_map.spec_index(container_ptr);
    &&& old_u.container_map.dom().contains(container_ptr)
    &&& old_u.thread_map.dom().contains(thread_ptr)
    &&& !old_u.endpoint_map.dom().contains(endpoint_ptr)
    &&& edp_idx_valid(endpoint_index)
    &&& thread.quota_4k > 0
    &&& thread.endpoint_descriptors[endpoint_index as int] is None
    &&& new_u == (KernelU {
        endpoint_map: old_u.endpoint_map.insert(endpoint_ptr, EndpointU {
            lock_state: LockStateU::Unlocked, queue: Seq::empty(), queue_state: EndpointState::RECEIVE, owning_threads: set![(thread_ptr, endpoint_index)],
            owning_container: container_ptr, killed: false,
        }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU {
            quota_4k: (thread.quota_4k as int - 1) as usize, endpoint_descriptors: thread.endpoint_descriptors.update(endpoint_index as int, Some(endpoint_ptr)),
            syscall_progress: None, ..thread
        }),
        container_map: old_u.container_map.insert(container_ptr, ContainerU { owned_endpoints: container.owned_endpoints.insert(endpoint_ptr), ..container }),
        ..old_u
    })
}

/// The running thread `thread_ptr` exits from `cpu_id`, which goes idle. The thread leaves the thread map and its
/// container's thread set; its process drops it, absorbs its quota, and becomes a zombie without threads; a zombie
/// releases its PCID to its container; a zombie root process makes its container a zombie; the container owning the
/// thread's page regains one 4K quota; and at most the `(cpu_id, KERNEL_DEFAULT_PCID)` TLB entry is flushed.
#[verifier::opaque]
pub open spec fn kernel_thread_exit_fields(pre: &KernelK, post: &KernelK, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, flushed_default_pcid: bool) -> bool {
    let thread = pre.thr_mp.spec_index(thread_ptr).view();
    let process_ptr = thread.owning_proc;
    let container_ptr = thread.owning_container;
    let pre_process = pre.prc_mp.spec_index(process_ptr);
    let post_process = post.prc_mp.spec_index(process_ptr);
    let zombie = pre_process.view().owned_threads.view().remove_value(thread_ptr).len() == 0;
    let pre_cpu = pre.cpu_arr.spec_index(cpu_id).value.view().view();
    let post_cpu = post.cpu_arr.spec_index(cpu_id).value.view().view();
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& pre.thr_mp.dom().contains(thread_ptr)
    &&& pre.prc_mp.dom().contains(process_ptr)
    &&& !pre_process.view().zombie
    &&& pre.ctn_mp.dom().contains(container_ptr)
    &&& post.irt.view().owners() == pre.irt.view().owners()
    &&& post.irt.view().iommu_roots() == pre.irt.view().iommu_roots()
    &&& post.iommu_tlb.view() == pre.iommu_tlb.view()
    &&& post.cpu_tlb.view() == if flushed_default_pcid {
        pre.cpu_tlb.view().insert((cpu_id, KERNEL_DEFAULT_PCID), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })
    } else { pre.cpu_tlb.view() }
    &&& post.dflt_pt == pre.dflt_pt
    &&& post.pt_mp == pre.pt_mp
    &&& post.it_mp == pre.it_mp
    &&& post.ep_mp == pre.ep_mp
    &&& post.sched_mp == pre.sched_mp
    &&& forall|c: RwLockContainerPtr| #![trigger post.pcid_allc_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator)]
        pre.ctn_mp.dom().contains(c) ==> {
            let free = PcidAllocator::free_pcids(pre.pcid_allc_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator).view().ref_counters.view());
            PcidAllocator::free_pcids(post.pcid_allc_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator).view().ref_counters.view())
                == if zombie && c == container_ptr { free.insert(pre_process.view_rodata().view().pcid) } else { free }
        }
    &&& post.cpu_set_mp == pre.cpu_set_mp
    &&& post.cpu_offline_mp == pre.cpu_offline_mp
    &&& post.allc_2m_mp == pre.allc_2m_mp
    &&& post.allc_1g_mp == pre.allc_1g_mp
    &&& forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)] index_valid(NUM_CPUS, i) && i != cpu_id ==> post.cpu_arr.spec_index(i) == pre.cpu_arr.spec_index(i)
    &&& post_cpu.owning_container == pre_cpu.owning_container
    &&& post_cpu.state == CpuState::Idle
    &&& post_cpu.current_process is None
    &&& post_cpu.current_thread is None
    &&& post.cpu_arr.spec_index(cpu_id).value.killer_info() == pre.cpu_arr.spec_index(cpu_id).value.killer_info()
    &&& post.ctn_mp.dom() == pre.ctn_mp.dom()
    &&& forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)]
        pre.ctn_mp.dom().contains(c) ==> {
            let a = pre.ctn_mp.spec_index(c);
            let b = post.ctn_mp.spec_index(c);
            let quota = pre.allc_4k_mp.spec_index(a.view_rodata().view().allocator_ptr_4k).quota.view().view() as int;
            &&& b.view() == if c == container_ptr { Container { zombie: a.view().zombie || (zombie && a.view().root_process == process_ptr), ..a.view() } } else { a.view() }
            &&& b.view_rodata() == a.view_rodata()
            &&& b.view_ghost().uppertree_seq == a.view_ghost().uppertree_seq
            &&& b.view_ghost().subtree_set == a.view_ghost().subtree_set
            &&& b.view_ghost().owned_processes == a.view_ghost().owned_processes
            &&& b.view_ghost().owned_threads.view() == if c == container_ptr { a.view_ghost().owned_threads.view().remove(thread_ptr) } else { a.view_ghost().owned_threads.view() }
            &&& b.being_killed() == a.being_killed()
            &&& post.allc_4k_mp.spec_index(a.view_rodata().view().allocator_ptr_4k).quota.view().view() as int == quota + if a.view().owned_pages.view().contains(thread_ptr) { 1int } else { 0int }
        }
    &&& post.prc_mp.dom() == pre.prc_mp.dom()
    &&& forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)] pre.prc_mp.dom().contains(p) && p != process_ptr ==> post.prc_mp.spec_index(p) == pre.prc_mp.spec_index(p)
    &&& post_process.view() == (Process {
        zombie, state: post_process.view().state, quota_4k: (pre_process.view().quota_4k + thread.quota_4k) as usize, quota_2m: (pre_process.view().quota_2m + thread.quota_2m) as usize,
        quota_1g: (pre_process.view().quota_1g + thread.quota_1g) as usize, owned_threads: post_process.view().owned_threads, ..pre_process.view()
    })
    &&& post_process.view().owned_threads.view() == pre_process.view().owned_threads.view().remove_value(thread_ptr)
    &&& post_process.view_rodata() == pre_process.view_rodata()
    &&& post_process.view_ghost() == pre_process.view_ghost()
    &&& post_process.being_killed() == pre_process.being_killed()
    &&& post.thr_mp.dom() == pre.thr_mp.dom().remove(thread_ptr)
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)] post.thr_mp.dom().contains(t) ==> post.thr_mp.spec_index(t) == pre.thr_mp.spec_index(t)
}

/// The running thread `thread_ptr` exits from `cpu_id`, which goes idle. The thread leaves the thread map and its
/// container's thread set; its process drops it, absorbs its quota, and becomes a zombie without threads; a zombie
/// returns its PCID to its container's free set; a zombie root process makes its container a zombie; the container
/// owning the thread's page regains one 4K quota; and at most the `(cpu_id, KERNEL_DEFAULT_PCID)` TLB entry is flushed.
#[verifier::opaque]
pub open spec fn kernel_u_thread_exit_changed(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, flushed_default_pcid: bool) -> bool {
    let thread = old_u.thread_map.spec_index(thread_ptr);
    let process_ptr = thread.owning_proc;
    let container_ptr = thread.owning_container;
    let process = old_u.process_map.spec_index(process_ptr);
    let threads = process.owned_threads.remove_value(thread_ptr);
    let zombie = threads.len() == 0;
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& old_u.thread_map.dom().contains(thread_ptr)
    &&& old_u.process_map.dom().contains(process_ptr)
    &&& old_u.container_map.dom().contains(container_ptr)
    &&& new_u.container_map.dom() == old_u.container_map.dom()
    &&& forall|c: RwLockContainerPtr| #![trigger new_u.container_map.spec_index(c)]
        old_u.container_map.dom().contains(c) ==> {
            let container = old_u.container_map.spec_index(c);
            let quota_4k = if container.owned_pages.contains(thread_ptr) { (container.quota_4k + 1) as usize } else { container.quota_4k };
            new_u.container_map.spec_index(c) == if c == container_ptr {
                ContainerU {
                    zombie: container.zombie || (zombie && container.root_process == process_ptr), owned_threads: container.owned_threads.remove(thread_ptr), quota_4k,
                    free_pcids: if zombie { container.free_pcids.insert(process.pcid) } else { container.free_pcids }, ..container
                }
            } else { ContainerU { quota_4k, ..container } }
        }
    &&& new_u == (KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { state: CpuState::Idle, current_process: None, current_thread: None, ..old_u.cpu_array[cpu_id as int] }),
        container_map: new_u.container_map,
        process_map: old_u.process_map.insert(process_ptr, ProcessU {
            zombie, pagetable: if zombie { None } else { process.pagetable }, iommu_table: if zombie { None } else { process.iommu_table },
            quota_4k: (process.quota_4k + thread.quota_4k) as usize, quota_2m: (process.quota_2m + thread.quota_2m) as usize,
            quota_1g: (process.quota_1g + thread.quota_1g) as usize, owned_threads: threads, ..process
        }),
        thread_map: old_u.thread_map.remove(thread_ptr),
        cpu_tlb: if flushed_default_pcid {
            old_u.cpu_tlb.insert((cpu_id, KERNEL_DEFAULT_PCID), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })
        } else { old_u.cpu_tlb },
        ..old_u
    })
}

/// Exit of a process's last thread returns the thread's and the process's whole `size` quota to their container's
/// allocator; besides that only the thread's progress changes.
#[verifier::opaque]
pub open spec fn kernel_thread_exit_quota_returned(pre: &KernelK, post: &KernelK, thread_ptr: RwLockThreadPtr, size: PageSize) -> bool {
    let thread = pre.thr_mp.spec_index(thread_ptr);
    let process_ptr = thread.view().owning_proc;
    let process = pre.prc_mp.spec_index(process_ptr);
    let container_ptr = thread.view().owning_container;
    let progress = post.thr_mp.spec_index(thread_ptr).view().syscall_progress;
    &&& pre.thr_mp.dom().contains(thread_ptr)
    &&& pre.prc_mp.dom().contains(process_ptr)
    &&& pre.ctn_mp.dom().contains(container_ptr)
    &&& *post == (KernelK { prc_mp: post.prc_mp, thr_mp: post.thr_mp, allc_4k_mp: post.allc_4k_mp, allc_2m_mp: post.allc_2m_mp, allc_1g_mp: post.allc_1g_mp, ..*pre })
    &&& post.thr_mp.dom() == pre.thr_mp.dom()
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)] pre.thr_mp.dom().contains(t) && t != thread_ptr ==> post.thr_mp.spec_index(t) == pre.thr_mp.spec_index(t)
    &&& post.thr_mp.spec_index(thread_ptr).view() == match size {
        PageSize::SZ4k => Thread { quota_4k: 0, syscall_progress: progress, ..thread.view() },
        PageSize::SZ2m => Thread { quota_2m: 0, syscall_progress: progress, ..thread.view() },
        PageSize::SZ1g => Thread { quota_1g: 0, syscall_progress: progress, ..thread.view() },
    }
    &&& post.thr_mp.spec_index(thread_ptr).locking_thread() == thread.locking_thread()
    &&& post.thr_mp.spec_index(thread_ptr).being_killed() == thread.being_killed()
    &&& post.prc_mp.dom() == pre.prc_mp.dom()
    &&& forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)] pre.prc_mp.dom().contains(p) && p != process_ptr ==> post.prc_mp.spec_index(p) == pre.prc_mp.spec_index(p)
    &&& post.prc_mp.spec_index(process_ptr).view() == match size {
        PageSize::SZ4k => Process { quota_4k: 0, ..process.view() },
        PageSize::SZ2m => Process { quota_2m: 0, ..process.view() },
        PageSize::SZ1g => Process { quota_1g: 0, ..process.view() },
    }
    &&& post.prc_mp.spec_index(process_ptr).view_rodata() == process.view_rodata()
    &&& post.prc_mp.spec_index(process_ptr).view_ghost() == process.view_ghost()
    &&& post.prc_mp.spec_index(process_ptr).locking_thread() == process.locking_thread()
    &&& post.prc_mp.spec_index(process_ptr).being_killed() == process.being_killed()
    &&& forall|c: RwLockContainerPtr| #![trigger post.allc_4k_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k)]
        pre.ctn_mp.dom().contains(c) ==> post.allc_4k_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k).quota.view().view() as int
            == pre.allc_4k_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k).quota.view().view() as int + if c == container_ptr && size is SZ4k { process.view().quota_4k + thread.view().quota_4k } else { 0 }
    &&& forall|c: RwLockContainerPtr| #![trigger post.allc_2m_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_2m)]
        pre.ctn_mp.dom().contains(c) ==> post.allc_2m_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_2m).quota.view().view() as int
            == pre.allc_2m_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_2m).quota.view().view() as int + if c == container_ptr && size is SZ2m { process.view().quota_2m + thread.view().quota_2m } else { 0 }
    &&& forall|c: RwLockContainerPtr| #![trigger post.allc_1g_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g)]
        pre.ctn_mp.dom().contains(c) ==> post.allc_1g_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g).quota.view().view() as int
            == pre.allc_1g_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g).quota.view().view() as int + if c == container_ptr && size is SZ1g { process.view().quota_1g + thread.view().quota_1g } else { 0 }
}

/// The killed dangling thread `dangling_ptr`, write-held and linked to no thread, leaves the thread map and its container's
/// thread set, and its page returns to a 4K allocator: the allocator of the container owning the page regains one quota.
#[verifier::opaque]
pub open spec fn kernel_dangling_thread_reclaimed_fields(pre: &KernelK, post: &KernelK, dangling_ptr: RwLockThreadPtr) -> bool {
    let dangling = pre.thr_mp.spec_index(dangling_ptr);
    &&& pre.thr_mp.dom().contains(dangling_ptr)
    &&& dangling.view().state is KILLED
    &&& dangling.locking_thread() is Write
    &&& dangling.view().caller is None
    &&& dangling.view().callee is None
    &&& *post == (KernelK { ctn_mp: post.ctn_mp, thr_mp: post.thr_mp, pg_arr: post.pg_arr, allc_4k_mp: post.allc_4k_mp, ..*pre })
    &&& post.ctn_mp.dom() == pre.ctn_mp.dom()
    &&& forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)]
        pre.ctn_mp.dom().contains(c) ==> {
            let a = pre.ctn_mp.spec_index(c);
            let b = post.ctn_mp.spec_index(c);
            &&& b.view() == a.view()
            &&& b.view_rodata() == a.view_rodata()
            &&& b.view_ghost().uppertree_seq == a.view_ghost().uppertree_seq
            &&& b.view_ghost().subtree_set == a.view_ghost().subtree_set
            &&& b.view_ghost().owned_processes == a.view_ghost().owned_processes
            &&& b.view_ghost().owned_threads.view() == if c == dangling.view().owning_container { a.view_ghost().owned_threads.view().remove(dangling_ptr) } else { a.view_ghost().owned_threads.view() }
            &&& b.locking_thread() == a.locking_thread()
            &&& b.being_killed() == a.being_killed()
            &&& post.allc_4k_mp.spec_index(a.view_rodata().view().allocator_ptr_4k).quota.view().view() as int == pre.allc_4k_mp.spec_index(a.view_rodata().view().allocator_ptr_4k).quota.view().view() as int + if a.view().owned_pages.view().contains(dangling_ptr) { 1int } else { 0int }
        }
    &&& post.thr_mp.dom() == pre.thr_mp.dom().remove(dangling_ptr)
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)] post.thr_mp.dom().contains(t) ==> post.thr_mp.spec_index(t) == pre.thr_mp.spec_index(t)
}

/// One killed dangling thread, write-locked and linked to no thread, leaves the thread map and its container's thread
/// set, and the container owning its page regains one 4K quota; the kernel chooses the dangling thread (R1).
#[verifier::opaque]
pub open spec fn kernel_u_dangling_thread_reclaimed(old_u: KernelU, new_u: KernelU) -> bool {
    let removed = old_u.thread_map.dom().difference(new_u.thread_map.dom());
    &&& new_u.thread_map.dom().subset_of(old_u.thread_map.dom())
    &&& removed.len() == 1
    &&& forall|dangling_ptr: RwLockThreadPtr| #![trigger removed.contains(dangling_ptr)]
        removed.contains(dangling_ptr) ==> {
            let dangling = old_u.thread_map.spec_index(dangling_ptr);
            &&& dangling.state is KILLED
            &&& dangling.lock_state is WriteLocked
            &&& dangling.caller is None
            &&& dangling.callee is None
            &&& new_u == (KernelU {
                container_map: Map::new(old_u.container_map.dom(), |c: RwLockContainerPtr| {
                    let container = old_u.container_map[c];
                    ContainerU {
                        owned_threads: if c == dangling.owning_container { container.owned_threads.remove(dangling_ptr) } else { container.owned_threads },
                        quota_4k: if container.owned_pages.contains(dangling_ptr) { (container.quota_4k + 1) as usize } else { container.quota_4k }, ..container
                    }
                }),
                thread_map: old_u.thread_map.remove(dangling_ptr),
                ..old_u
            })
        }
}

/// One write-locked killed thread releases one descriptor: the descriptor is cleared and its unlocked endpoint drops the
/// reference; the kernel chooses the thread and the descriptor (R1).
#[verifier::opaque]
pub open spec fn kernel_u_killed_descriptor_dropped(old_u: KernelU, new_u: KernelU) -> bool {
    let changed = old_u.thread_map.dom().filter(|t: RwLockThreadPtr| new_u.thread_map[t] != old_u.thread_map[t]);
    &&& changed.len() == 1
    &&& forall|thread_ptr: RwLockThreadPtr| #![trigger changed.contains(thread_ptr)] changed.contains(thread_ptr) ==> {
        let thread = old_u.thread_map[thread_ptr];
        let dropped = Set::<int>::range(0, MAX_NUM_ENDPOINT_DESCRIPTORS as int).filter(|j: int| new_u.thread_map[thread_ptr].endpoint_descriptors[j] != thread.endpoint_descriptors[j]);
        &&& thread.state is KILLED
        &&& thread.lock_state is WriteLocked
        &&& dropped.len() == 1
        &&& forall|index: int| #![trigger dropped.contains(index)] dropped.contains(index) ==> {
            let endpoint_ptr = thread.endpoint_descriptors[index]->Some_0;
            let endpoint = old_u.endpoint_map[endpoint_ptr];
            &&& thread.endpoint_descriptors[index] is Some
            &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
            &&& endpoint.lock_state is Unlocked
            &&& new_u == (KernelU {
                thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { endpoint_descriptors: thread.endpoint_descriptors.update(index, None), ..thread }),
                endpoint_map: old_u.endpoint_map.insert(endpoint_ptr, EndpointU { owning_threads: endpoint.owning_threads.remove((thread_ptr, index as EndpointIdx)), ..endpoint }),
                ..old_u
            })
        }
    }
}

/// The unlocked caller of one write-locked killed thread, waiting for its reply, is scheduled on shard `cpu_id` of its
/// container with `ErrorIpcCalleeExited`, and the killed thread drops its caller; the kernel chooses the killed thread
/// (R1).
#[verifier::opaque]
pub open spec fn kernel_u_killed_caller_woken(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let woken = old_u.thread_map.dom().filter(|t: RwLockThreadPtr| old_u.thread_map[t].state is WAITING_REPLY && new_u.thread_map[t].state is SCHEDULED);
    &&& woken.len() == 1
    &&& forall|caller_ptr: RwLockThreadPtr| #![trigger woken.contains(caller_ptr)] woken.contains(caller_ptr) ==> {
        let caller = old_u.thread_map[caller_ptr];
        let thread_ptr = caller.callee->Some_0;
        let thread = old_u.thread_map[thread_ptr];
        let container = old_u.container_map[caller.owning_container];
        &&& caller.callee is Some
        &&& old_u.thread_map.dom().contains(thread_ptr)
        &&& thread.state is KILLED
        &&& thread.lock_state is WriteLocked
        &&& thread.caller == Some(caller_ptr)
        &&& caller.lock_state is Unlocked
        &&& new_u == (KernelU {
            container_map: old_u.container_map.insert(caller.owning_container, ContainerU {
                scheduler: container.scheduler.update(cpu_id as int, container.scheduler[cpu_id as int].push(caller_ptr)), ..container
            }),
            thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { caller: None, ..thread }).insert(caller_ptr, ThreadU {
                state: ThreadState::SCHEDULED { cpu_id }, callee: None, error_code: Some(RetValueType::ErrorIpcCalleeExited), ..caller
            }),
            ..old_u
        })
    }
}

/// The unlocked dangling thread of the killed caller of one write-locked killed thread is taken over as a write-locked killed thread
/// without a callee, and the killed thread drops its caller; the kernel chooses the killed thread (R1).
#[verifier::opaque]
pub open spec fn kernel_u_killed_caller_taken_over(old_u: KernelU, new_u: KernelU) -> bool {
    let taken = old_u.thread_map.dom().filter(|t: RwLockThreadPtr| old_u.thread_map[t].state is DANGLING && new_u.thread_map[t].state is KILLED);
    &&& taken.len() == 1
    &&& forall|caller_ptr: RwLockThreadPtr| #![trigger taken.contains(caller_ptr)] taken.contains(caller_ptr) ==> {
        let caller = old_u.thread_map[caller_ptr];
        let thread_ptr = caller.callee->Some_0;
        let thread = old_u.thread_map[thread_ptr];
        &&& caller.callee is Some
        &&& old_u.thread_map.dom().contains(thread_ptr)
        &&& thread.state is KILLED
        &&& thread.lock_state is WriteLocked
        &&& thread.caller == Some(caller_ptr)
        &&& caller.lock_state is Unlocked
        &&& new_u == (KernelU {
            thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { caller: None, ..thread }) .insert(caller_ptr, ThreadU { state: ThreadState::KILLED, callee: None, lock_state: LockStateU::WriteLocked, ..caller }),
            ..old_u
        })
    }
}

/// One step of reclaiming write-locked killed threads: releasing a descriptor, waking a caller waiting for a reply,
/// taking over the dangling thread of a killed caller, or reclaiming a killed dangling thread.
pub open spec fn kernel_u_killed_thread_reclaim_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    ||| kernel_u_killed_descriptor_dropped(old_u, new_u)
    ||| kernel_u_killed_caller_woken(old_u, new_u, cpu_id)
    ||| kernel_u_killed_caller_taken_over(old_u, new_u)
    ||| kernel_u_dangling_thread_reclaimed(old_u, new_u)
}
} // verus!
