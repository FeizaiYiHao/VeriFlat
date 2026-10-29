use vstd::prelude::*;
use crate::*;

/// User-level step relations: how one recorded step changes the user projection `KernelU`.
pub mod kernel_u_steps;
/// Kernel-level field relations of the context-switch, rebalance, and IPC steps.
pub mod kernel_schedule_ipc_fields;

pub use kernel_u_steps::*;
pub use kernel_schedule_ipc_fields::*;

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

#[verifier::opaque]
pub open spec fn kernel_pagetable_nonlock_fields_unchanged(pre_pt: PageTableLockedMap, pre_lower: PageTableLowerMap, post_pt: PageTableLockedMap, post_lower: PageTableLowerMap) -> bool {
    &&& post_pt.dom() == pre_pt.dom()
    &&& forall|p: RwLockPageTableRoot| #![trigger pagetable_c(post_pt, post_lower, p)]
        pre_pt.dom().contains(p) ==> {
            let before = pagetable_c(pre_pt, pre_lower, p);
            let after = pagetable_c(post_pt, post_lower, p);
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
            &&& after.did == before.did
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
    &&& kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view())
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
        pre.ctn_mp.dom().contains(c) ==> {
            let b = post.cpu_set_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().cpu_set);
            let a = pre.cpu_set_mp.spec_index(pre.ctn_mp.spec_index(c).view_rodata().view().cpu_set);
            &&& b.lock_state_u() == a.lock_state_u()
            &&& b.being_killed() == a.being_killed()
        }
    &&& forall|c: RwLockContainerPtr| #![trigger post.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(c))]
        pre.ctn_mp.dom().contains(c) ==> cpu_offline_requests_of(post.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(c))) == cpu_offline_requests_of(pre.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(c)))
}

#[verifier::opaque]
pub open spec fn kernel_container_quota_4k_changed(pre: &KernelK, post: &KernelK, container_ptr: RwLockContainerPtr, delta: int) -> bool {
    &&& *post == (KernelK { cpu_op: post.cpu_op, thr_mp: post.thr_mp, allc_4k_mp: post.allc_4k_mp, ..*pre })
    &&& post.cpu_op.view().view() == pre.cpu_op.view().view()
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
            &&& post.ctn_mp.spec_index(c).view_ghost().owned_endpoints == pre.ctn_mp.spec_index(c).view_ghost().owned_endpoints
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
    &&& kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view())
    &&& post.it_mp.dom() == pre.it_mp.dom()
    &&& forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
        pre.it_mp.dom().contains(p) ==> {
            &&& post.it_mp.spec_index(p).view().did == pre.it_mp.spec_index(p).view().did
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
    &&& post.cpu_op.view().view() == pre.cpu_op.view().view()
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
            &&& b.view_ghost().owned_endpoints.view() == a.view_ghost().owned_endpoints.view()
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
            let before = pagetable_c(pre.pt_mp, pre.pt_lower.view(), p);
            let after = pagetable_c(post.pt_mp, post.pt_lower.view(), p);
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
            &&& after.did == before.did
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
    &&& post.cpu_op.view().view() == pre.cpu_op.view().view()
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
            &&& b.view_ghost().owned_endpoints.view() == a.view_ghost().owned_endpoints.view()
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
            let before = pagetable_c(pre.pt_mp, pre.pt_lower.view(), p);
            let after = pagetable_c(post.pt_mp, post.pt_lower.view(), p);
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
            &&& after.did == before.did
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
    &&& *post == (KernelK { cpu_arr: post.cpu_arr, cpu_op: post.cpu_op, prc_mp: post.prc_mp, thr_mp: post.thr_mp, ..*pre })
    &&& post.cpu_op.view().view() == pre.cpu_op.view().view()
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
    &&& *post == (KernelK { cpu_arr: post.cpu_arr, cpu_op: post.cpu_op, prc_mp: post.prc_mp, thr_mp: post.thr_mp, ..*pre })
    &&& post.cpu_op.view().view() == pre.cpu_op.view().view()
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
    &&& pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k().filter_keys(|v: VAddr| pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(v).present).dom().contains(va)
        != pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k().filter_keys(|v: VAddr| pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(v).present).dom().contains(va)
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
            let receiver = if krnl.thr_mp.spec_index(peer).view().state->IPC_TRANSIT_wait is Receive { peer } else { caller };
            Share4kObjects {
                source_thread: if krnl.thr_mp.spec_index(peer).view().state->IPC_TRANSIT_wait is Receive { caller } else { peer },
                target: krnl.thr_mp.spec_index(receiver).view().owning_proc, quota_thread: receiver,
                target_container: krnl.thr_mp.spec_index(receiver).view().owning_container, transfer_source: None,
            }
        },
    }
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
    &&& *post == (KernelK { cpu_arr: post.cpu_arr, cpu_op: post.cpu_op, cpu_set_mp: post.cpu_set_mp, cpu_offline_mp: post.cpu_offline_mp, ctn_mp: post.ctn_mp, ..*pre })
    &&& post.cpu_op.view().view() == pre.cpu_op.view().view()
    &&& post.cpu_arr.entries_unchanged_except(&pre.cpu_arr, cpu_id)
    &&& post.cpu_arr.spec_index(cpu_id).value.view().view() == pre.cpu_arr.spec_index(cpu_id).value.view().view()
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
    &&& post.cpu_set_mp.spec_index(cpu_set_ptr).being_killed() == pre.cpu_set_mp.spec_index(cpu_set_ptr).being_killed()
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
    &&& *post == (KernelK { cpu_arr: post.cpu_arr, cpu_op: post.cpu_op, cpu_set_mp: post.cpu_set_mp, ctn_mp: post.ctn_mp, ..*pre })
    &&& pre.cpu_op.view().view().len() == NUM_CPUS
    &&& post.cpu_op.view().view() == pre.cpu_op.view().view().update(target as int, CpuOpState::Idle)
    &&& forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)] index_valid(NUM_CPUS, i) && i != cpu_id && i != target ==> post.cpu_arr.spec_index(i) == pre.cpu_arr.spec_index(i)
    &&& post.cpu_arr.spec_index(cpu_id).value.view().view() == pre.cpu_arr.spec_index(cpu_id).value.view().view()
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
    &&& post.cpu_set_mp.spec_index(cpu_set_ptr).being_killed() == pre.cpu_set_mp.spec_index(cpu_set_ptr).being_killed()
}

/// `cpu_id`'s TLB entries after it went Off: the default-PCID entry is flushed when `flushed_default_pcid`,
/// then every non-default PCID entry of the cpu is empty.
pub open spec fn cpu_tlb_after_cpu_went_off(tlb: Map<(CpuId, Pcid), SingleTLB>, cpu_id: CpuId, flushed_default_pcid: bool) -> Map<(CpuId, Pcid), SingleTLB> {
    let empty = SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() };
    let after_default = if flushed_default_pcid { tlb.insert((cpu_id, KERNEL_DEFAULT_PCID), empty) } else { tlb };
    Map::new(after_default.dom(), |key: (CpuId, Pcid)| if key.0 == cpu_id && key.1 != KERNEL_DEFAULT_PCID { empty } else { after_default[key] })
}

#[verifier::opaque]
/// `cpu_offline_check` with every lock released again: the non-Off cpu `cpu_id`, with a pending request of
/// its container, went Off and unlocked, its live running thread (if any) was requeued at the tail of shard `cpu_id` with
/// `regs`, the request bit was cleared, and the cpu's TLB entries were flushed. The cpu may be write-held at `pre`; every
/// other cpu keeps its lock mode.
pub open spec fn kernel_cpu_went_off_fields(pre: &KernelK, post: &KernelK, cpu_id: CpuId, regs: Registers, flushed_default_pcid: bool) -> bool {
    let cpu = pre.cpu_arr.spec_index(cpu_id).value.view().view();
    let previous = cpu.current_thread;
    let container_ptr = cpu.owning_container;
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& pre.cpu_op.view().view().len() == NUM_CPUS
    &&& post.cpu_op.view().view() == pre.cpu_op.view().view().update(cpu_id as int, CpuOpState::Off)
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
        index_valid(NUM_CPUS, i) && i != cpu_id ==> post.cpu_arr.spec_index(i).value.locking_thread() == pre.cpu_arr.spec_index(i).value.locking_thread()
    &&& post.cpu_set_mp.dom() == pre.cpu_set_mp.dom()
    &&& forall|p: RwLockCpuSetPtr| #![trigger post.cpu_set_mp.spec_index(p)]
        pre.cpu_set_mp.dom().contains(p) ==> post.cpu_set_mp.spec_index(p).locking_thread() == pre.cpu_set_mp.spec_index(p).locking_thread() && post.cpu_set_mp.spec_index(p).being_killed() == pre.cpu_set_mp.spec_index(p).being_killed()
    &&& kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view())
    &&& kernel_iommu_table_nonlock_fields_unchanged(pre.it_mp, post.it_mp)
    &&& kernel_process_nonlock_fields_unchanged(pre.prc_mp, post.prc_mp)
    &&& kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp)
    &&& post.irt.view().owners() == pre.irt.view().owners()
    &&& post.irt.view().iommu_roots() == pre.irt.view().iommu_roots()
    &&& post.iommu_tlb.view() == pre.iommu_tlb.view()
    &&& post.dflt_pt == pre.dflt_pt
    &&& post.cpu_tlb.view() == cpu_tlb_after_cpu_went_off(pre.cpu_tlb.view(), cpu_id, flushed_default_pcid)
    &&& post.cpu_arr.spec_index(cpu_id).value.locking_thread() is None
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
            &&& post.ctn_mp.spec_index(c).view() == pre.ctn_mp.spec_index(c).view()
            &&& post.ctn_mp.spec_index(c).view_rodata() == pre.ctn_mp.spec_index(c).view_rodata()
            &&& post.ctn_mp.spec_index(c).view_ghost() == if c == container_ptr {
                    ContainerGhost { owned_endpoints: Ghost(pre.ctn_mp.spec_index(c).view_ghost().owned_endpoints.view().insert(new_endpoint_ptr)), ..pre.ctn_mp.spec_index(c).view_ghost() }
                } else { pre.ctn_mp.spec_index(c).view_ghost() }
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
    &&& post.pt_lower == pre.pt_lower
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
    &&& pre.cpu_op.view().view().len() == NUM_CPUS
    &&& post.cpu_op.view().view() == pre.cpu_op.view().view().update(cpu_id as int, CpuOpState::Idle)
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
    &&& post.pt_lower == pre.pt_lower
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
            &&& b.view_ghost().owned_endpoints == a.view_ghost().owned_endpoints
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
    &&& *post == (KernelK { cpu_op: post.cpu_op, prc_mp: post.prc_mp, thr_mp: post.thr_mp, allc_4k_mp: post.allc_4k_mp, allc_2m_mp: post.allc_2m_mp, allc_1g_mp: post.allc_1g_mp, ..*pre })
    &&& post.cpu_op.view().view() == pre.cpu_op.view().view()
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
    &&& *post == (KernelK { cpu_op: post.cpu_op, ctn_mp: post.ctn_mp, thr_mp: post.thr_mp, pg_arr: post.pg_arr, allc_4k_mp: post.allc_4k_mp, ..*pre })
    &&& post.cpu_op.view().view() == pre.cpu_op.view().view()
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
            &&& b.view_ghost().owned_endpoints == a.view_ghost().owned_endpoints
            &&& b.view_ghost().owned_threads.view() == if c == dangling.view().owning_container { a.view_ghost().owned_threads.view().remove(dangling_ptr) } else { a.view_ghost().owned_threads.view() }
            &&& b.locking_thread() == a.locking_thread()
            &&& b.being_killed() == a.being_killed()
            &&& b.control() == a.control()
            &&& post.allc_4k_mp.spec_index(a.view_rodata().view().allocator_ptr_4k).quota.view().view() as int == pre.allc_4k_mp.spec_index(a.view_rodata().view().allocator_ptr_4k).quota.view().view() as int + if a.view().owned_pages.view().contains(dangling_ptr) { 1int } else { 0int }
        }
    &&& post.thr_mp.dom() == pre.thr_mp.dom().remove(dangling_ptr)
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)] post.thr_mp.dom().contains(t) ==> post.thr_mp.spec_index(t) == pre.thr_mp.spec_index(t)
}
} // verus!
