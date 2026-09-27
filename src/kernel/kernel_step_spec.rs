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
            &&& post.spec_index(p).view().user_view(LockStateU::Unlocked) == pre.spec_index(p).view().user_view(LockStateU::Unlocked)
        }
}

#[verifier::opaque]
pub open spec fn kernel_iommu_table_nonlock_fields_unchanged(pre: IommuTableLockedMap, post: IommuTableLockedMap) -> bool {
    &&& post.dom() == pre.dom()
    &&& forall|p: RwLockPageTableRoot| #![trigger post.spec_index(p)]
        pre.dom().contains(p) ==> {
            &&& post.spec_index(p).view().user_view(LockStateU::Unlocked) == pre.spec_index(p).view().user_view(LockStateU::Unlocked)
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
}

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
            &&& b.view().owned_processes.view() == a.view().owned_processes.view()
            &&& b.view_ghost().owned_threads.view() == a.view_ghost().owned_threads.view()
            &&& b.view().owned_endpoints.view() == a.view().owned_endpoints.view()
            &&& b.view().owned_pages.view() == a.view().owned_pages.view()
            &&& b_ro.parent == a_ro.parent
            &&& b_ro.depth == a_ro.depth
            &&& b_ro.scheduler == a_ro.scheduler
            &&& post.sched_mp.spec_index(b_ro.scheduler).view().queue.view() == pre.sched_mp.spec_index(a_ro.scheduler).view().queue.view()
            &&& b_ro.cpu_set == a_ro.cpu_set
            &&& PcidAllocator::free_pcids(post.pcid_allc_mp.spec_index(b_ro.pcid_allocator).view().ref_counters.view())
                == PcidAllocator::free_pcids(pre.pcid_allc_mp.spec_index(a_ro.pcid_allocator).view().ref_counters.view())
            &&& post.allc_4k_mp.spec_index(b_ro.allocator_ptr_4k).quota.view().view()
                == pre.allc_4k_mp.spec_index(a_ro.allocator_ptr_4k).quota.view().view()
            &&& post.allc_2m_mp.spec_index(b_ro.allocator_ptr_2m).quota.view().view()
                == pre.allc_2m_mp.spec_index(a_ro.allocator_ptr_2m).quota.view().view()
            &&& post.allc_1g_mp.spec_index(b_ro.allocator_ptr_1g).quota.view().view()
                == pre.allc_1g_mp.spec_index(a_ro.allocator_ptr_1g).quota.view().view()
            &&& b.being_killed() == a.being_killed()
        }
}

#[verifier::opaque]
pub open spec fn kernel_container_quota_4k_changed(
    pre: &KernelK, post: &KernelK, container_ptr: RwLockContainerPtr, delta: int,
) -> bool {
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
            &&& b.view().owned_processes.view() == a.view().owned_processes.view()
            &&& b.view_ghost().owned_threads.view() == a.view_ghost().owned_threads.view()
            &&& b.view().owned_endpoints.view() == a.view().owned_endpoints.view()
            &&& b.view().owned_pages.view() == a.view().owned_pages.view()
            &&& b_ro.parent == a_ro.parent
            &&& b_ro.depth == a_ro.depth
            &&& b_ro.cpu_set == a_ro.cpu_set
            &&& b_ro.scheduler == a_ro.scheduler
            &&& b.being_killed() == a.being_killed()
            &&& post.sched_mp.spec_index(b_ro.scheduler).view().queue.view() == pre.sched_mp.spec_index(a_ro.scheduler).view().queue.view()
            &&& post.allc_4k_mp.spec_index(b_ro.allocator_ptr_4k).quota.view().view() as int
                == pre.allc_4k_mp.spec_index(a_ro.allocator_ptr_4k).quota.view().view() as int + if c == container_ptr { delta } else { 0 }
            &&& PcidAllocator::free_pcids(post.pcid_allc_mp.spec_index(b_ro.pcid_allocator).view().ref_counters.view())
                == PcidAllocator::free_pcids(pre.pcid_allc_mp.spec_index(a_ro.pcid_allocator).view().ref_counters.view())
            &&& post.allc_2m_mp.spec_index(b_ro.allocator_ptr_2m).quota.view().view()
                == pre.allc_2m_mp.spec_index(a_ro.allocator_ptr_2m).quota.view().view()
            &&& post.allc_1g_mp.spec_index(b_ro.allocator_ptr_1g).quota.view().view()
                == pre.allc_1g_mp.spec_index(a_ro.allocator_ptr_1g).quota.view().view()
        }
}

#[verifier::opaque]
pub open spec fn kernel_new_thread_fields(
    pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, new_thread_ptr: RwLockThreadPtr, initial_regs: Registers,
    initial_endpoint: Option<RwLockEndpointPtr>,
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
            &&& post.ctn_mp.spec_index(c).view_ghost().owned_threads.view()
                == if c == container_ptr { pre.ctn_mp.spec_index(c).view_ghost().owned_threads.view().insert(new_thread_ptr) }
                    else { pre.ctn_mp.spec_index(c).view_ghost().owned_threads.view() }
            &&& post.ctn_mp.spec_index(c).being_killed() == pre.ctn_mp.spec_index(c).being_killed()
        }
    &&& post.allc_4k_mp == pre.allc_4k_mp
    &&& post.allc_2m_mp == pre.allc_2m_mp
    &&& post.allc_1g_mp == pre.allc_1g_mp
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
            &&& post.thr_mp.spec_index(t).view().syscall_progress == pre.thr_mp.spec_index(t).view().syscall_progress
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
    &&& kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, post.pt_mp)
    &&& kernel_iommu_table_nonlock_fields_unchanged(pre.it_mp, post.it_mp)
    &&& kernel_process_nonlock_fields_unchanged(pre.prc_mp, post.prc_mp)
    &&& kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp)
    &&& post.irt.owners() == pre.irt.owners()
    &&& post.irt.iommu_roots() == pre.irt.iommu_roots()
    &&& post.iommu_tlb.view() == pre.iommu_tlb.view()
    &&& post.cpu_tlb.view() == match flushed_pcid {
        Some(pcid) => pre.cpu_tlb.view().insert((cpu_id, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }),
        None => pre.cpu_tlb.view(),
    }
    &&& !(cpu.state is Off)
    &&& pre.ctn_mp.dom().contains(cpu.owning_container)
    &&& run_queue.len() > 0
    &&& run_queue[0] == next_thread
    &&& pre.thr_mp.dom().contains(next_thread)
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
        &&& !prev.being_killed()
        &&& prev.view().state == (ThreadState::RUNNING { cpu_id })
        &&& prev.view().owning_proc == process_ptr
        &&& pre.prc_mp.dom().contains(process_ptr)
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
            let queue = pre.sched_mp.spec_index(a_ro.scheduler).view().queue.view();
            &&& b.view().children.view() == a.view().children.view()
            &&& b.view_ghost().uppertree_seq.view() == a.view_ghost().uppertree_seq.view()
            &&& b.view_ghost().subtree_set.view() == a.view_ghost().subtree_set.view()
            &&& b.view().root_process == a.view().root_process
            &&& b.view().owned_processes.view() == a.view().owned_processes.view()
            &&& b.view_ghost().owned_threads.view() == a.view_ghost().owned_threads.view()
            &&& b.view().owned_endpoints.view() == a.view().owned_endpoints.view()
            &&& b.view().owned_pages.view() == a.view().owned_pages.view()
            &&& b_ro.parent == a_ro.parent
            &&& b_ro.depth == a_ro.depth
            &&& b_ro.scheduler == a_ro.scheduler
            &&& post.sched_mp.spec_index(b_ro.scheduler).view().queue.view() == if c == cpu.owning_container {
                match previous { Some(prev) => queue.skip(1).push(prev), None => queue.skip(1) }
            } else { queue }
            &&& b_ro.cpu_set == a_ro.cpu_set
            &&& PcidAllocator::free_pcids(post.pcid_allc_mp.spec_index(b_ro.pcid_allocator).view().ref_counters.view())
                == PcidAllocator::free_pcids(pre.pcid_allc_mp.spec_index(a_ro.pcid_allocator).view().ref_counters.view())
            &&& post.allc_4k_mp.spec_index(b_ro.allocator_ptr_4k).quota.view().view() == pre.allc_4k_mp.spec_index(a_ro.allocator_ptr_4k).quota.view().view()
            &&& post.allc_2m_mp.spec_index(b_ro.allocator_ptr_2m).quota.view().view() == pre.allc_2m_mp.spec_index(a_ro.allocator_ptr_2m).quota.view().view()
            &&& post.allc_1g_mp.spec_index(b_ro.allocator_ptr_1g).quota.view().view() == pre.allc_1g_mp.spec_index(a_ro.allocator_ptr_1g).quota.view().view()
            &&& b.being_killed() == a.being_killed()
        }
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
    &&& kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, post.pt_mp)
    &&& kernel_iommu_table_nonlock_fields_unchanged(pre.it_mp, post.it_mp)
    &&& kernel_process_nonlock_fields_unchanged(pre.prc_mp, post.prc_mp)
    &&& kernel_container_nonlock_fields_and_quotas_unchanged(pre, post)
    &&& post.irt.owners() == pre.irt.owners()
    &&& post.irt.iommu_roots() == pre.irt.iommu_roots()
    &&& post.iommu_tlb.view() == pre.iommu_tlb.view()
    &&& post.cpu_tlb.view() == if flushed_default_pcid {
        pre.cpu_tlb.view().insert((cpu_id, KERNEL_DEFAULT_PCID), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })
    } else { pre.cpu_tlb.view() }
    &&& cpu.state is Running
    &&& cpu.current_thread == Some(thread_ptr)
    &&& cpu.current_process == Some(thread.view().owning_proc)
    &&& pre.prc_mp.dom().contains(thread.view().owning_proc)
    &&& !pre.prc_mp.spec_index(thread.view().owning_proc).being_killed()
    &&& pre.thr_mp.dom().contains(thread_ptr)
    &&& !thread.being_killed()
    &&& thread.view().state == (ThreadState::RUNNING { cpu_id })
    &&& edp_idx_valid(endpoint_index)
    &&& thread.view().endpoint_descriptors.view()[endpoint_index as int] == Some(endpoint_ptr)
    &&& pre.ep_mp.dom().contains(endpoint_ptr)
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
    &&& cpu.state is Running
    &&& cpu.current_thread == Some(caller_thread_ptr)
    &&& cpu.current_process == Some(caller.view().owning_proc)
    &&& pre.prc_mp.dom().contains(caller.view().owning_proc)
    &&& !pre.prc_mp.spec_index(caller.view().owning_proc).being_killed()
    &&& pre.thr_mp.dom().contains(caller_thread_ptr)
    &&& !caller.being_killed()
    &&& caller.view().state == (ThreadState::RUNNING { cpu_id })
    &&& edp_idx_valid(endpoint_index)
    &&& caller.view().endpoint_descriptors.view()[endpoint_index as int] == Some(endpoint_ptr)
    &&& pre.ep_mp.dom().contains(endpoint_ptr)
    &&& !endpoint.view().queue.view().contains(caller_thread_ptr)
    &&& waiting_state is SENDING || waiting_state is RECEIVING
    &&& endpoint.view().queue.view().len() > 0
    &&& endpoint.view().queue.view()[0] == peer_thread_ptr
    &&& (endpoint.view().queue_state is SEND) != (waiting_state is SENDING)
    &&& pre.thr_mp.dom().contains(peer_thread_ptr)
    &&& peer_thread_ptr != caller_thread_ptr
    &&& !peer.being_killed()
    &&& peer.view().state.is_endpoint_waiting()
    &&& peer.view().blocking_endpoint_ptr == Some(endpoint_ptr)
    &&& pre.ctn_mp.dom().contains(peer_container)
    &&& (cpu_transfer is Some ==> index_valid(NUM_CPUS, cpu_transfer.unwrap().0) && pre.thr_mp.dom().contains(cpu_transfer.unwrap().1))
    &&& kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, post.pt_mp)
    &&& kernel_iommu_table_nonlock_fields_unchanged(pre.it_mp, post.it_mp)
    &&& kernel_process_nonlock_fields_unchanged(pre.prc_mp, post.prc_mp)
    &&& post.irt.owners() == pre.irt.owners()
    &&& post.irt.iommu_roots() == pre.irt.iommu_roots()
    &&& post.cpu_tlb.view() == pre.cpu_tlb.view()
    &&& post.iommu_tlb.view() == pre.iommu_tlb.view()
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
            let queue = pre.sched_mp.spec_index(a_ro.scheduler).view().queue.view();
            &&& b.view().children.view() == a.view().children.view()
            &&& b.view_ghost().uppertree_seq.view() == a.view_ghost().uppertree_seq.view()
            &&& b.view_ghost().subtree_set.view() == a.view_ghost().subtree_set.view()
            &&& b.view().root_process == a.view().root_process
            &&& b.view().owned_processes.view() == a.view().owned_processes.view()
            &&& b.view_ghost().owned_threads.view() == a.view_ghost().owned_threads.view()
            &&& b.view().owned_endpoints.view() == a.view().owned_endpoints.view()
            &&& b.view().owned_pages.view() == a.view().owned_pages.view()
            &&& b_ro.parent == a_ro.parent
            &&& b_ro.depth == a_ro.depth
            &&& b_ro.scheduler == a_ro.scheduler
            &&& post.sched_mp.spec_index(b_ro.scheduler).view().queue.view() == if c == peer_container { queue.push(peer_thread_ptr) } else { queue }
            &&& b_ro.cpu_set == a_ro.cpu_set
            &&& PcidAllocator::free_pcids(post.pcid_allc_mp.spec_index(b_ro.pcid_allocator).view().ref_counters.view())
                == PcidAllocator::free_pcids(pre.pcid_allc_mp.spec_index(a_ro.pcid_allocator).view().ref_counters.view())
            &&& post.allc_4k_mp.spec_index(b_ro.allocator_ptr_4k).quota.view().view() == pre.allc_4k_mp.spec_index(a_ro.allocator_ptr_4k).quota.view().view()
            &&& post.allc_2m_mp.spec_index(b_ro.allocator_ptr_2m).quota.view().view() == pre.allc_2m_mp.spec_index(a_ro.allocator_ptr_2m).quota.view().view()
            &&& post.allc_1g_mp.spec_index(b_ro.allocator_ptr_1g).quota.view().view() == pre.allc_1g_mp.spec_index(a_ro.allocator_ptr_1g).quota.view().view()
            &&& b.being_killed() == a.being_killed()
        }
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
    &&& cpu.state is Running
    &&& cpu.current_process == Some(process_ptr)
    &&& cpu.owning_container == container_ptr
    &&& !container.being_killed()
    &&& pre.allc_4k_mp.spec_index(container.view_rodata().view().allocator_ptr_4k).quota.view().view() >= delta
    &&& !process.being_killed()
    &&& process.view().quota_4k + delta <= usize::MAX
    &&& delta > 0
    &&& kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp)
    &&& post.irt.owners() == pre.irt.owners()
    &&& post.irt.iommu_roots() == pre.irt.iommu_roots()
    &&& post.cpu_tlb.view() == pre.cpu_tlb.view()
    &&& post.iommu_tlb.view() == pre.iommu_tlb.view()
    &&& pre.prc_mp.dom().contains(process_ptr)
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
            &&& b.view().owned_processes.view() == a.view().owned_processes.view()
            &&& b.view_ghost().owned_threads.view() == a.view_ghost().owned_threads.view()
            &&& b.view().owned_endpoints.view() == a.view().owned_endpoints.view()
            &&& b.view().owned_pages.view() == a.view().owned_pages.view()
            &&& b_ro.parent == a_ro.parent
            &&& b_ro.depth == a_ro.depth
            &&& b_ro.cpu_set == a_ro.cpu_set
            &&& b_ro.scheduler == a_ro.scheduler
            &&& b.being_killed() == a.being_killed()
            &&& post.sched_mp.spec_index(b_ro.scheduler).view().queue.view() == pre.sched_mp.spec_index(a_ro.scheduler).view().queue.view()
            &&& post.allc_4k_mp.spec_index(b_ro.allocator_ptr_4k).quota.view().view() as int
                == pre.allc_4k_mp.spec_index(a_ro.allocator_ptr_4k).quota.view().view() as int - if c == container_ptr { delta } else { 0 }
            &&& PcidAllocator::free_pcids(post.pcid_allc_mp.spec_index(b_ro.pcid_allocator).view().ref_counters.view())
                == PcidAllocator::free_pcids(pre.pcid_allc_mp.spec_index(a_ro.pcid_allocator).view().ref_counters.view())
            &&& post.allc_2m_mp.spec_index(b_ro.allocator_ptr_2m).quota.view().view()
                == pre.allc_2m_mp.spec_index(a_ro.allocator_ptr_2m).quota.view().view()
            &&& post.allc_1g_mp.spec_index(b_ro.allocator_ptr_1g).quota.view().view()
                == pre.allc_1g_mp.spec_index(a_ro.allocator_ptr_1g).quota.view().view()
        }
    &&& post.pt_mp.dom() == pre.pt_mp.dom()
    &&& forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
        pre.pt_mp.dom().contains(p) ==>
            post.pt_mp.spec_index(p).view().user_view(LockStateU::Unlocked) == pre.pt_mp.spec_index(p).view().user_view(LockStateU::Unlocked)
    &&& post.it_mp.dom() == pre.it_mp.dom()
    &&& forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
        pre.it_mp.dom().contains(p) ==>
            post.it_mp.spec_index(p).view().user_view(LockStateU::Unlocked) == pre.it_mp.spec_index(p).view().user_view(LockStateU::Unlocked)
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
            &&& post.prc_mp.spec_index(p).view().quota_4k as int
                == pre.prc_mp.spec_index(p).view().quota_4k as int + if p == process_ptr { delta } else { 0 }
            &&& post.prc_mp.spec_index(p).view().quota_2m == pre.prc_mp.spec_index(p).view().quota_2m
            &&& post.prc_mp.spec_index(p).view().quota_1g == pre.prc_mp.spec_index(p).view().quota_1g
            &&& post.prc_mp.spec_index(p).view().children.view() == pre.prc_mp.spec_index(p).view().children.view()
            &&& post.prc_mp.spec_index(p).view_rodata().view().parent == pre.prc_mp.spec_index(p).view_rodata().view().parent
            &&& post.prc_mp.spec_index(p).view_rodata().view().depth == pre.prc_mp.spec_index(p).view_rodata().view().depth
            &&& post.prc_mp.spec_index(p).view_ghost().uppertree_seq.view() == pre.prc_mp.spec_index(p).view_ghost().uppertree_seq.view()
            &&& post.prc_mp.spec_index(p).view_ghost().subtree_set.view() == pre.prc_mp.spec_index(p).view_ghost().subtree_set.view()
            &&& post.prc_mp.spec_index(p).being_killed() == pre.prc_mp.spec_index(p).being_killed()
            &&& post.prc_mp.spec_index(p).view().owned_threads.view() == pre.prc_mp.spec_index(p).view().owned_threads.view()
        }
    &&& post.thr_mp.dom() == pre.thr_mp.dom()
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)]
        pre.thr_mp.dom().contains(t) ==> {
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
    &&& pre.pt_mp.spec_index(pagetable_ptr).view().user_view(LockStateU::Unlocked).mapping_4k.dom().contains(va)
        != post.pt_mp.spec_index(pagetable_ptr).view().user_view(LockStateU::Unlocked).mapping_4k.dom().contains(va)
}
}
