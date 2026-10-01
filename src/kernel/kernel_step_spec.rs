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
pub open spec fn kernel_u_only_process_quota_4k_changed(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, delta: int,
) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let container = old_u.container_map.spec_index(container_ptr);
    let process = old_u.process_map.spec_index(process_ptr);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& cpu.current_process == Some(process_ptr)
    &&& cpu.owning_container == container_ptr
    &&& old_u.container_map.dom().contains(container_ptr)
    &&& !container.killed
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

#[verifier::opaque]
pub open spec fn kernel_pagetable_nonlock_fields_unchanged(pre: PageTableLockedMap, post: PageTableLockedMap) -> bool {
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
pub open spec fn kernel_iommu_table_nonlock_fields_unchanged(pre: IommuTableLockedMap, post: IommuTableLockedMap) -> bool {
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
            &&& post.spec_index(p).view().owned_pci_functions.view() == pre.spec_index(p).view().owned_pci_functions.view()
            &&& post.spec_index(p).view().quota_4k == pre.spec_index(p).view().quota_4k
            &&& post.spec_index(p).view().quota_2m == pre.spec_index(p).view().quota_2m
            &&& post.spec_index(p).view().quota_1g == pre.spec_index(p).view().quota_1g
            &&& post.spec_index(p).view().children.view() == pre.spec_index(p).view().children.view()
            &&& post.spec_index(p).view_rodata().view().parent == pre.spec_index(p).view_rodata().view().parent
            &&& post.spec_index(p).view_rodata().view().depth == pre.spec_index(p).view_rodata().view().depth
            &&& post.spec_index(p).view_rodata().view().pcid == pre.spec_index(p).view_rodata().view().pcid
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
    &&& kernel_iommu_table_nonlock_fields_unchanged(pre.it_mp, post.it_mp)
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
        pre.ctn_mp.dom().contains(c) ==> post.sched_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().scheduler).view().queue.view()
            == pre.sched_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().scheduler).view().queue.view()
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
        pre.ctn_mp.dom().contains(c) ==> post.cpu_set_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().cpu_set).lock_state_u()
            == pre.cpu_set_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().cpu_set).lock_state_u()
}

#[verifier::opaque]
pub open spec fn kernel_container_quota_4k_changed(
    pre: &KernelK, post: &KernelK, container_ptr: RwLockContainerPtr, delta: int,
) -> bool {
    &&& *post == (KernelK { thr_mp: post.thr_mp, allc_4k_mp: post.allc_4k_mp, ..*pre })
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)] pre.thr_mp.dom().contains(t) ==>
        post.thr_mp.spec_index(t).locking_thread() == pre.thr_mp.spec_index(t).locking_thread()
    &&& kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp)
    &&& post.irt.owners() == pre.irt.owners()
    &&& post.irt.iommu_roots() == pre.irt.iommu_roots()
    &&& post.cpu_tlb.view() == pre.cpu_tlb.view()
    &&& post.iommu_tlb.view() == pre.iommu_tlb.view()
    &&& kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post)
    &&& pre.ctn_mp.dom().contains(container_ptr)
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
        pre.ctn_mp.dom().contains(c) ==> post.sched_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().scheduler).view().queue.view()
            == pre.sched_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().scheduler).view().queue.view()
    &&& forall|c: RwLockContainerPtr| #![trigger post.allc_4k_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k)]
        pre.ctn_mp.dom().contains(c) ==> post.allc_4k_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k).quota.view().view() as int
            == pre.allc_4k_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k).quota.view().view() as int + if c == container_ptr { delta } else { 0 }
    &&& forall|c: RwLockContainerPtr| #![trigger post.pcid_allc_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator)]
        pre.ctn_mp.dom().contains(c) ==> PcidAllocator::free_pcids(post.pcid_allc_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator).view().ref_counters.view())
            == PcidAllocator::free_pcids(pre.pcid_allc_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator).view().ref_counters.view())
    &&& forall|c: RwLockContainerPtr| #![trigger post.allc_2m_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_2m)]
        pre.ctn_mp.dom().contains(c) ==> post.allc_2m_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_2m).quota.view().view()
            == pre.allc_2m_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_2m).quota.view().view()
    &&& forall|c: RwLockContainerPtr| #![trigger post.allc_1g_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g)]
        pre.ctn_mp.dom().contains(c) ==> post.allc_1g_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g).quota.view().view()
            == pre.allc_1g_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_1g).quota.view().view()
}

/// One staging-thread quota funds a new scheduled thread of `process_ptr` and `container_ptr`,
/// and the staging thread's progress becomes `staging_progress`.
#[verifier::opaque]
pub open spec fn kernel_new_thread_fields(
    pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, new_thread_ptr: RwLockThreadPtr, initial_regs: Registers,
    initial_endpoint: Option<RwLockEndpointPtr>, staging_progress: Option<SyscallProgress>,
) -> bool {
    &&& post.irt.owners() == pre.irt.owners()
    &&& post.irt.iommu_roots() == pre.irt.iommu_roots()
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
            &&& post.sched_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().scheduler).view().queue.view()
                == if c == container_ptr {
                    pre.sched_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().scheduler).view().queue.view().push(new_thread_ptr)
                } else { pre.sched_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().scheduler).view().queue.view() }
            &&& PcidAllocator::free_pcids(post.pcid_allc_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator).view().ref_counters.view())
                == PcidAllocator::free_pcids(pre.pcid_allc_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator).view().ref_counters.view())
            &&& post.ctn_mp.spec_index(c).view_ghost().uppertree_seq == pre.ctn_mp.spec_index(c).view_ghost().uppertree_seq
            &&& post.ctn_mp.spec_index(c).view_ghost().subtree_set == pre.ctn_mp.spec_index(c).view_ghost().subtree_set
            &&& post.ctn_mp.spec_index(c).view_ghost().owned_processes == pre.ctn_mp.spec_index(c).view_ghost().owned_processes
            &&& post.ctn_mp.spec_index(c).view_ghost().owned_threads.view()
                == if c == container_ptr { pre.ctn_mp.spec_index(c).view_ghost().owned_threads.view().insert(new_thread_ptr) }
                    else { pre.ctn_mp.spec_index(c).view_ghost().owned_threads.view() }
            &&& post.ctn_mp.spec_index(c).being_killed() == pre.ctn_mp.spec_index(c).being_killed()
        }
    &&& post.allc_4k_mp == pre.allc_4k_mp
    &&& post.allc_2m_mp == pre.allc_2m_mp
    &&& post.allc_1g_mp == pre.allc_1g_mp
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
        }
    &&& post.prc_mp.dom() == pre.prc_mp.dom()
    &&& forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
        pre.prc_mp.dom().contains(p) ==> {
            &&& post.prc_mp.spec_index(p).view().zombie == pre.prc_mp.spec_index(p).view().zombie
            &&& post.prc_mp.spec_index(p).view().pagetable == pre.prc_mp.spec_index(p).view().pagetable
            &&& post.prc_mp.spec_index(p).view().iommu_table == pre.prc_mp.spec_index(p).view().iommu_table
            &&& post.prc_mp.spec_index(p).view().owned_pci_functions.view() == pre.prc_mp.spec_index(p).view().owned_pci_functions.view()
            &&& post.prc_mp.spec_index(p).view().quota_4k == pre.prc_mp.spec_index(p).view().quota_4k
            &&& post.prc_mp.spec_index(p).view().quota_2m == pre.prc_mp.spec_index(p).view().quota_2m
            &&& post.prc_mp.spec_index(p).view().quota_1g == pre.prc_mp.spec_index(p).view().quota_1g
            &&& post.prc_mp.spec_index(p).view().children.view() == pre.prc_mp.spec_index(p).view().children.view()
            &&& post.prc_mp.spec_index(p).view_rodata().view().parent == pre.prc_mp.spec_index(p).view_rodata().view().parent
            &&& post.prc_mp.spec_index(p).view_rodata().view().depth == pre.prc_mp.spec_index(p).view_rodata().view().depth
            &&& post.prc_mp.spec_index(p).view_rodata().view().pcid == pre.prc_mp.spec_index(p).view_rodata().view().pcid
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
            &&& post.thr_mp.spec_index(t).view().quota_4k == if t == staging_thread_ptr { pre.thr_mp.spec_index(t).view().quota_4k - 1 } else { pre.thr_mp.spec_index(t).view().quota_4k as int }
            &&& post.thr_mp.spec_index(t).view().quota_2m == pre.thr_mp.spec_index(t).view().quota_2m
            &&& post.thr_mp.spec_index(t).view().quota_1g == pre.thr_mp.spec_index(t).view().quota_1g
            &&& post.thr_mp.spec_index(t).view().endpoint_descriptors.view() == pre.thr_mp.spec_index(t).view().endpoint_descriptors.view()
            &&& post.thr_mp.spec_index(t).view().blocking_endpoint_ptr == pre.thr_mp.spec_index(t).view().blocking_endpoint_ptr
            &&& post.thr_mp.spec_index(t).view().ipc_payload == pre.thr_mp.spec_index(t).view().ipc_payload
            &&& post.thr_mp.spec_index(t).view().error_code == pre.thr_mp.spec_index(t).view().error_code
            &&& post.thr_mp.spec_index(t).view().trap_frame == pre.thr_mp.spec_index(t).view().trap_frame
            &&& post.thr_mp.spec_index(t).view().syscall_progress.view()
                == if t == staging_thread_ptr { staging_progress } else { pre.thr_mp.spec_index(t).view().syscall_progress.view() }
            &&& post.thr_mp.spec_index(t).being_killed() == pre.thr_mp.spec_index(t).being_killed()
        }
    &&& post.thr_mp.spec_index(new_thread_ptr).view().state == ThreadState::SCHEDULED
    &&& post.thr_mp.spec_index(new_thread_ptr).view().caller == None
    &&& post.thr_mp.spec_index(new_thread_ptr).view().callee == None
    &&& post.thr_mp.spec_index(new_thread_ptr).view().owning_container == container_ptr
    &&& post.thr_mp.spec_index(new_thread_ptr).view().owning_proc == process_ptr
    &&& post.thr_mp.spec_index(new_thread_ptr).view().quota_4k == 0
    &&& post.thr_mp.spec_index(new_thread_ptr).view().quota_2m == 0
    &&& post.thr_mp.spec_index(new_thread_ptr).view().quota_1g == 0
    &&& post.thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.view()
        == Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat, |i: int| if i == 0 { initial_endpoint } else { None })
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
/// The live scheduler head `next_thread` of the CPU's container replaces the live thread running on
/// `cpu_id`, which is requeued at the tail, and at most the `(cpu_id, flushed_pcid)` TLB entry is flushed.
pub open spec fn kernel_context_switch_fields(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, next_thread: RwLockThreadPtr, entry_regs: Registers, flushed_pcid: Option<Pcid>,
) -> bool {
    let cpu = pre.cpu_arr.spec_index(cpu_id).value.view().view();
    let previous = cpu.current_thread;
    let next = pre.thr_mp.spec_index(next_thread);
    let next_process = next.view().owning_proc;
    let run_queue = pre.sched_mp.spec_index(pre.ctn_mp.spec_index(cpu.owning_container).view_rodata().view().scheduler).view().queue.view();
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
    &&& kernel_iommu_table_nonlock_fields_unchanged(pre.it_mp, post.it_mp)
    &&& kernel_process_nonlock_fields_unchanged(pre.prc_mp, post.prc_mp)
    &&& kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp)
    &&& post.irt.owners() == pre.irt.owners()
    &&& post.irt.iommu_roots() == pre.irt.iommu_roots()
    &&& post.iommu_tlb.view() == pre.iommu_tlb.view()
    &&& post.dflt_pt == pre.dflt_pt
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
            let queue = pre.sched_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().scheduler).view().queue.view();
            post.sched_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().scheduler).view().queue.view() == if c == cpu.owning_container {
                match previous { Some(prev) => queue.skip(1).push(prev), None => queue.skip(1) }
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
            &&& b.state == if t == next_thread { ThreadState::RUNNING { cpu_id } } else if previous == Some(t) { ThreadState::SCHEDULED } else { a.state }
            &&& b.caller == a.caller
            &&& b.callee == a.callee
            &&& b.owning_container == a.owning_container
            &&& b.owning_proc == a.owning_proc
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

/// The live scheduler head `next_thread` replaces the live thread running on `cpu_id`, which is requeued at the tail.
#[verifier::opaque]
pub open spec fn kernel_u_context_switch_changed(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, next_thread: RwLockThreadPtr, entry_regs: Registers, flushed_pcid: Option<Pcid>,
) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let container = old_u.container_map.spec_index(cpu.owning_container);
    let next = old_u.thread_map.spec_index(next_thread);
    let requeued = match cpu.current_thread {
        Some(prev) => old_u.thread_map.insert(prev, ThreadU {
            state: ThreadState::SCHEDULED, error_code: None, trap_frame: Some(entry_regs), ..old_u.thread_map.spec_index(prev)
        }),
        None => old_u.thread_map,
    };
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& !(cpu.state is Off)
    &&& old_u.container_map.dom().contains(cpu.owning_container)
    &&& container.scheduler.len() > 0
    &&& container.scheduler[0] == next_thread
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
            scheduler: match cpu.current_thread { Some(prev) => container.scheduler.skip(1).push(prev), None => container.scheduler.skip(1) },
            ..container
        }),
        thread_map: requeued.insert(next_thread, ThreadU { state: ThreadState::RUNNING { cpu_id }, error_code: None, trap_frame: None, ..next }),
        cpu_tlb: match flushed_pcid {
            Some(pcid) => old_u.cpu_tlb.insert((cpu_id, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }),
            None => old_u.cpu_tlb,
        },
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
    &&& kernel_iommu_table_nonlock_fields_unchanged(pre.it_mp, post.it_mp)
    &&& kernel_process_nonlock_fields_unchanged(pre.prc_mp, post.prc_mp)
    &&& kernel_container_nonlock_fields_and_quotas_unchanged(pre, post)
    &&& post.irt.owners() == pre.irt.owners()
    &&& post.irt.iommu_roots() == pre.irt.iommu_roots()
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
    &&& pre.prc_mp.spec_index(thread.view().owning_proc).locking_thread() is None
    &&& !pre.prc_mp.spec_index(thread.view().owning_proc).being_killed()
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
    &&& !old_u.process_map.spec_index(thread.owning_proc).killed
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
/// The live head `peer_thread_ptr` of the endpoint at `endpoint_index`, waiting opposite to the live caller
/// running on `cpu_id`, is dequeued and scheduled with `peer_result`; with `cpu_transfer == Some((cpu, receiver))`
/// that Off CPU also moves to the receiver's container.
pub open spec fn kernel_ipc_rendezvous_fields(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, caller_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, peer_thread_ptr: RwLockThreadPtr, peer_result: RetValueType,
    cpu_transfer: Option<(CpuId, RwLockThreadPtr)>,
) -> bool {
    let cpu = pre.cpu_arr.spec_index(cpu_id).value.view().view();
    let caller = pre.thr_mp.spec_index(caller_thread_ptr);
    let peer = pre.thr_mp.spec_index(peer_thread_ptr);
    let endpoint = pre.ep_mp.spec_index(endpoint_ptr);
    let peer_container = peer.view().owning_container;
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& pre.cpu_arr.spec_index(cpu_id).value.locking_thread() is None
    &&& cpu.state is Running
    &&& cpu.current_thread == Some(caller_thread_ptr)
    &&& cpu.current_process == Some(caller.view().owning_proc)
    &&& pre.prc_mp.dom().contains(caller.view().owning_proc)
    &&& pre.prc_mp.spec_index(caller.view().owning_proc).locking_thread() is None
    &&& !pre.prc_mp.spec_index(caller.view().owning_proc).being_killed()
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
    &&& waiting_state is SENDING || waiting_state is RECEIVING
    &&& endpoint.view().queue.view().len() > 0
    &&& endpoint.view().queue.view()[0] == peer_thread_ptr
    &&& (endpoint.view().queue_state is SEND) != (waiting_state is SENDING)
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
    &&& kernel_iommu_table_nonlock_fields_unchanged(pre.it_mp, post.it_mp)
    &&& kernel_process_nonlock_fields_unchanged(pre.prc_mp, post.prc_mp)
    &&& post.irt.owners() == pre.irt.owners()
    &&& post.irt.iommu_roots() == pre.irt.iommu_roots()
    &&& post.cpu_tlb.view() == pre.cpu_tlb.view()
    &&& post.iommu_tlb.view() == pre.iommu_tlb.view()
    &&& post.dflt_pt == pre.dflt_pt
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
            let queue = pre.sched_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().scheduler).view().queue.view();
            post.sched_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().scheduler).view().queue.view() == if c == peer_container { queue.push(peer_thread_ptr) } else { queue }
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
            &&& b.state == if t == peer_thread_ptr { ThreadState::SCHEDULED } else { a.state }
            &&& b.caller == a.caller
            &&& b.callee == a.callee
            &&& b.owning_container == a.owning_container
            &&& b.owning_proc == a.owning_proc
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
/// with `peer_result`; an Off CPU may move to the receiver's container.
#[verifier::opaque]
pub open spec fn kernel_u_ipc_rendezvous_changed(
    old_u: KernelU, new_u: KernelU, cpu_id: CpuId, caller_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, peer_thread_ptr: RwLockThreadPtr, peer_result: RetValueType,
    cpu_transfer: Option<(CpuId, RwLockThreadPtr)>,
) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let caller = old_u.thread_map.spec_index(caller_thread_ptr);
    let peer = old_u.thread_map.spec_index(peer_thread_ptr);
    let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
    let container = old_u.container_map.spec_index(peer.owning_container);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& cpu.current_thread == Some(caller_thread_ptr)
    &&& cpu.current_process == Some(caller.owning_proc)
    &&& old_u.process_map.dom().contains(caller.owning_proc)
    &&& !old_u.process_map.spec_index(caller.owning_proc).killed
    &&& old_u.thread_map.dom().contains(caller_thread_ptr)
    &&& !caller.killed
    &&& caller.state == (ThreadState::RUNNING { cpu_id })
    &&& edp_idx_valid(endpoint_index)
    &&& caller.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
    &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
    &&& !endpoint.queue.contains(caller_thread_ptr)
    &&& waiting_state is SENDING || waiting_state is RECEIVING
    &&& endpoint.queue.len() > 0
    &&& endpoint.queue[0] == peer_thread_ptr
    &&& (endpoint.queue_state is SEND) != (waiting_state is SENDING)
    &&& old_u.thread_map.dom().contains(peer_thread_ptr)
    &&& peer_thread_ptr != caller_thread_ptr
    &&& !peer.killed
    &&& peer.state.is_endpoint_waiting()
    &&& peer.blocking_endpoint_ptr == Some(endpoint_ptr)
    &&& old_u.container_map.dom().contains(peer.owning_container)
    &&& (cpu_transfer is Some ==> index_valid(NUM_CPUS, cpu_transfer.unwrap().0) && old_u.thread_map.dom().contains(cpu_transfer.unwrap().1))
    &&& new_u == (KernelU {
        cpu_array: match cpu_transfer {
            Some((transfer_cpu, receiver)) => old_u.cpu_array.update(transfer_cpu as int, CpuU {
                owning_container: old_u.thread_map.spec_index(receiver).owning_container, ..old_u.cpu_array[transfer_cpu as int]
            }),
            None => old_u.cpu_array,
        },
        container_map: old_u.container_map.insert(peer.owning_container, ContainerU { scheduler: container.scheduler.push(peer_thread_ptr), ..container }),
        thread_map: old_u.thread_map.insert(peer_thread_ptr, ThreadU {
            state: ThreadState::SCHEDULED, blocking_endpoint_ptr: None, ipc_payload: IPCPayLoad::Empty, error_code: Some(peer_result), ..peer
        }),
        endpoint_map: old_u.endpoint_map.insert(endpoint_ptr, EndpointU { queue: endpoint.queue.skip(1), ..endpoint }),
        ..old_u
    })
}

/// The caller's result of meeting the queue head of the endpoint at `endpoint_index`, decided from the two
/// payloads as the implementation does. Empty payloads in opposite directions succeed. A CPU handover needs
/// different containers and an Off CPU of the sender's container; an endpoint transfer needs the sender's
/// source descriptor and a free receiver target descriptor; a pages transfer needs equal lengths and different
/// processes. Any other pairing is a type mismatch. Success on Endpoint and Pages payloads starts their
/// multi-step transfer.
pub open spec fn ipc_rendezvous_result(old_u: KernelU, cpu_id: CpuId, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad) -> RetValueType {
    let caller = old_u.thread_map[old_u.cpu_array[cpu_id as int].current_thread->Some_0];
    let peer = old_u.thread_map[old_u.endpoint_map[caller.endpoint_descriptors[endpoint_index as int]->Some_0].queue[0]];
    let sends = waiting_state is SENDING;
    let sender = if sends { caller } else { peer };
    let receiver = if sends { peer } else { caller };
    let sent = if sends { payload } else { peer.ipc_payload };
    let received = if sends { peer.ipc_payload } else { payload };
    if peer.state != (if sends { ThreadState::RECEIVING } else { ThreadState::SENDING }) { RetValueType::ErrorIpcTypeMismatch } else {
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
            _ => RetValueType::ErrorIpcTypeMismatch,
        }
    }
}

#[verifier::opaque]
pub open spec fn kernel_thread_quota_4k_changed(
    pre: &KernelK, post: &KernelK, thread_ptr: RwLockThreadPtr, delta: int,
) -> bool {
    &&& pre.thr_mp.dom().contains(thread_ptr)
    &&& post.thr_mp.dom().contains(thread_ptr)
    &&& post.thr_mp.spec_index(thread_ptr).view().state == pre.thr_mp.spec_index(thread_ptr).view().state
    &&& post.thr_mp.spec_index(thread_ptr).view().caller == pre.thr_mp.spec_index(thread_ptr).view().caller
    &&& post.thr_mp.spec_index(thread_ptr).view().callee == pre.thr_mp.spec_index(thread_ptr).view().callee
    &&& post.thr_mp.spec_index(thread_ptr).view().owning_container == pre.thr_mp.spec_index(thread_ptr).view().owning_container
    &&& post.thr_mp.spec_index(thread_ptr).view().owning_proc == pre.thr_mp.spec_index(thread_ptr).view().owning_proc
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
pub open spec fn kernel_process_quota_4k_changed(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, delta: int,
) -> bool {
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
    &&& pre.allc_4k_mp.spec_index(container.view_rodata().view().allocator_ptr_4k).quota.view().view() >= delta
    &&& process.locking_thread() is None
    &&& !process.being_killed()
    &&& process.view().quota_4k + delta <= usize::MAX
    &&& delta > 0
    &&& kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp)
    &&& forall|e: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(e)]
        pre.ep_mp.dom().contains(e) ==> post.ep_mp.spec_index(e).locking_thread() == pre.ep_mp.spec_index(e).locking_thread()
    &&& post.irt.owners() == pre.irt.owners()
    &&& post.irt.iommu_roots() == pre.irt.iommu_roots()
    &&& post.cpu_tlb.view() == pre.cpu_tlb.view()
    &&& post.iommu_tlb.view() == pre.iommu_tlb.view()
    &&& post.dflt_pt == pre.dflt_pt
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
        pre.ctn_mp.dom().contains(c) ==> post.sched_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().scheduler).view().queue.view()
            == pre.sched_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().scheduler).view().queue.view()
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
        }
    &&& post.prc_mp.dom() == pre.prc_mp.dom()
    &&& forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
        pre.prc_mp.dom().contains(p) ==> {
            &&& post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread()
            &&& post.prc_mp.spec_index(p).view().zombie == pre.prc_mp.spec_index(p).view().zombie
            &&& post.prc_mp.spec_index(p).view().pagetable == pre.prc_mp.spec_index(p).view().pagetable
            &&& post.prc_mp.spec_index(p).view().iommu_table == pre.prc_mp.spec_index(p).view().iommu_table
            &&& post.prc_mp.spec_index(p).view().owned_pci_functions.view() == pre.prc_mp.spec_index(p).view().owned_pci_functions.view()
            &&& post.prc_mp.spec_index(p).view().quota_4k as int
                == pre.prc_mp.spec_index(p).view().quota_4k as int + if p == process_ptr { delta } else { 0 }
            &&& post.prc_mp.spec_index(p).view().quota_2m == pre.prc_mp.spec_index(p).view().quota_2m
            &&& post.prc_mp.spec_index(p).view().quota_1g == pre.prc_mp.spec_index(p).view().quota_1g
            &&& post.prc_mp.spec_index(p).view().children.view() == pre.prc_mp.spec_index(p).view().children.view()
            &&& post.prc_mp.spec_index(p).view_rodata().view().parent == pre.prc_mp.spec_index(p).view_rodata().view().parent
            &&& post.prc_mp.spec_index(p).view_rodata().view().depth == pre.prc_mp.spec_index(p).view_rodata().view().depth
            &&& post.prc_mp.spec_index(p).view_rodata().view().pcid == pre.prc_mp.spec_index(p).view_rodata().view().pcid
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

#[verifier::opaque]
pub open spec fn kernel_process_added(pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr) -> bool {
    &&& !pre.prc_mp.dom().contains(process_ptr)
    &&& post.prc_mp.dom().contains(process_ptr)
}

#[verifier::opaque]
pub open spec fn kernel_process_4k_mapping_changed(
    pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr,
) -> bool {
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
    &&& forall|c: RwLockContainerPtr| #![trigger changed.contains(c)] changed.contains(c) ==> {
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
    &&& forall|c: RwLockContainerPtr| #![trigger post.container_map[c]] pre.container_map.dom().contains(c) ==>
        post.container_map[c] == (ContainerU {
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
        lock_state: LockStateU::WriteLocked, children: Seq::empty(), uppertree_seq: ancestors, subtree_set: Set::empty(),
        root_process: process, owned_processes: set![process], owned_threads: Set::empty(), owned_endpoints: Set::empty(), owned_pages: moved,
        parent: Some(parent), depth: (pre.container_map[parent].depth + 1) as usize, scheduler: Seq::empty(),
        cpu_set: post.container_map[child].cpu_set, cpu_set_lock: LockStateU::WriteLocked, free_pcids: Set::range(1usize, PCID_MAX).remove(1usize),
        quota_4k: (funding - process_quota) as usize, quota_2m: 0, quota_1g: 0, killed: false,
    })
    &&& post == (KernelU {
        cpu_array: pre.cpu_array.update(transfer_cpu as int, CpuU { lock_state: LockStateU::WriteLocked, ..pre.cpu_array[transfer_cpu as int] }),
        container_map: post.container_map,
        process_map: pre.process_map.insert(process, ProcessU {
            lock_state: LockStateU::WriteLocked, zombie: false,
            pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, mapping_4k: Map::empty(), mapping_2m: Map::empty(), mapping_1g: Map::empty() }),
            iommu_table: None, pcid: post.process_map[process].pcid, owned_pci_functions: Set::empty(), quota_4k: process_quota, quota_2m: 0, quota_1g: 0,
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
pub open spec fn kernel_u_cpu_and_page_owner_changed(
    pre: KernelU, post: KernelU, cpu: CpuId, source: RwLockContainerPtr, target: RwLockContainerPtr, page: PagePtr,
) -> bool {
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
    &&& forall|c: RwLockContainerPtr| #![trigger post.container_map[c]] pre.container_map.dom().contains(c) ==>
        post.container_map[c] == (ContainerU {
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
        lock_state: LockStateU::WriteLocked, children: Seq::empty(), uppertree_seq: ancestors, subtree_set: Set::empty(),
        root_process: process, owned_processes: set![process], owned_threads: Set::empty(), owned_endpoints: Set::empty(), owned_pages: moved,
        parent: Some(parent), depth: (pre.container_map[parent].depth + 1) as usize, scheduler: Seq::empty(),
        cpu_set: post.container_map[child].cpu_set, cpu_set_lock: LockStateU::Unlocked, free_pcids: Set::range(1usize, PCID_MAX).remove(1usize),
        quota_4k: (funding - process_quota) as usize, quota_2m: 0, quota_1g: 0, killed: false,
    })
    &&& post == (KernelU {
        cpu_array: pre.cpu_array.update(transfer_cpu as int, CpuU { lock_state: LockStateU::Unlocked, owning_container: child, ..pre.cpu_array[transfer_cpu as int] }),
        container_map: post.container_map,
        process_map: pre.process_map.insert(process, ProcessU {
            lock_state: LockStateU::WriteLocked, zombie: false,
            pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, mapping_4k: Map::empty(), mapping_2m: Map::empty(), mapping_1g: Map::empty() }),
            iommu_table: None, pcid: post.process_map[process].pcid, owned_pci_functions: Set::empty(), quota_4k: process_quota, quota_2m: 0, quota_1g: 0,
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

}
