use vstd::prelude::*;
use crate::*;

verus! {
/// The projected map domains and scalar fields of the nonlock user projection, without unfolding any projected entry.
pub proof fn kernel_u_nonlock_domains_projection(krnl: &KernelK)
    ensures
        kernel_k_to_nonlock_kernel_u(*krnl).cpu_array.len() == NUM_CPUS,
        kernel_k_to_nonlock_kernel_u(*krnl).container_map.dom() == krnl.ctn_mp.dom(),
        kernel_k_to_nonlock_kernel_u(*krnl).process_map.dom() == krnl.prc_mp.dom(),
        kernel_k_to_nonlock_kernel_u(*krnl).thread_map.dom() == krnl.thr_mp.dom(),
        kernel_k_to_nonlock_kernel_u(*krnl).endpoint_map.dom() == krnl.ep_mp.dom(),
        kernel_k_to_nonlock_kernel_u(*krnl).iommu_root_table == krnl.irt.view().user_view(),
        kernel_k_to_nonlock_kernel_u(*krnl).cpu_tlb == krnl.cpu_tlb.view(),
        kernel_k_to_nonlock_kernel_u(*krnl).iommu_tlb == krnl.iommu_tlb.view(),
        kernel_k_to_nonlock_kernel_u(*krnl).kernel_l4_end == krnl.dflt_pt.view().kernel_l4_end,
{ reveal(kernel_k_to_nonlock_kernel_u); }

/// One cpu slot of the nonlock user projection, without unfolding the other projected maps.
pub proof fn kernel_cpu_nonlock_projection_at(krnl: &KernelK, cpu_id: CpuId)
    requires index_valid(NUM_CPUS, cpu_id),
    ensures
        kernel_k_to_nonlock_kernel_u(*krnl).cpu_array.len() == NUM_CPUS,
        ({
            let c = krnl.cpu_arr.spec_index(cpu_id).value.view().view();
            kernel_k_to_nonlock_kernel_u(*krnl).cpu_array[cpu_id as int] == (CpuU {
                lock_state: LockStateU::Unlocked, owning_container: c.owning_container, state: c.state,
                current_process: c.current_process, current_thread: c.current_thread, killed: krnl.cpu_arr.spec_index(cpu_id).value.being_killed(),
            })
        }),
{ reveal(kernel_k_to_nonlock_kernel_u); }

/// One container entry of the nonlock user projection, without unfolding the other projected maps.
pub proof fn kernel_container_nonlock_projection_at(krnl: &KernelK, ptr: RwLockContainerPtr)
    requires krnl.ctn_mp.dom().contains(ptr),
    ensures
        kernel_k_to_nonlock_kernel_u(*krnl).container_map.dom().contains(ptr),
        ({
            let c = krnl.ctn_mp.spec_index(ptr).view();
            let c_ghost = krnl.ctn_mp.spec_index(ptr).view_ghost();
            let c_ro = krnl.ctn_mp.spec_index(ptr).view_rodata().view();
            kernel_k_to_nonlock_kernel_u(*krnl).container_map[ptr] == (ContainerU {
                lock_state: LockStateU::Unlocked, zombie: c.zombie,
                children: c.children.view(), uppertree_seq: c_ghost.uppertree_seq.view(), subtree_set: c_ghost.subtree_set.view(),
                root_process: c.root_process, owned_processes: c_ghost.owned_processes.view(), owned_threads: c_ghost.owned_threads.view(),
                owned_endpoints: c_ghost.owned_endpoints.view(), owned_pages: c.owned_pages.view(),
                parent: c_ro.parent, depth: c_ro.depth, cpu_set: c_ro.cpu_set, cpu_set_lock: LockStateU::Unlocked,
                cpu_offline_requests: cpu_offline_requests_of(krnl.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(ptr))),
                scheduler: scheduler_shards_of(krnl.sched_mp.spec_index(c_ro.scheduler)),
                free_pcids: PcidAllocator::free_pcids(krnl.pcid_allc_mp.spec_index(c_ro.pcid_allocator).view().ref_counters.view()),
                quota_4k: krnl.allc_4k_mp.spec_index(c_ro.allocator_ptr_4k).quota.view().view(),
                quota_2m: krnl.allc_2m_mp.spec_index(c_ro.allocator_ptr_2m).quota.view().view(),
                quota_1g: krnl.allc_1g_mp.spec_index(c_ro.allocator_ptr_1g).quota.view().view(),
                killed: krnl.ctn_mp.spec_index(ptr).being_killed(),
            })
        }),
{ reveal(kernel_k_to_nonlock_kernel_u); }

/// One endpoint entry of the nonlock user projection, without unfolding the other projected maps.
pub proof fn kernel_endpoint_nonlock_projection_at(krnl: &KernelK, ptr: RwLockEndpointPtr)
    requires krnl.ep_mp.dom().contains(ptr),
    ensures
        kernel_k_to_nonlock_kernel_u(*krnl).endpoint_map.dom().contains(ptr),
        ({
            let e = krnl.ep_mp.spec_index(ptr);
            kernel_k_to_nonlock_kernel_u(*krnl).endpoint_map[ptr] == (EndpointU {
                lock_state: LockStateU::Unlocked, queue: e.view().queue.view(), queue_state: e.view().queue_state,
                owning_threads: e.view().owning_threads.view(), owning_container: e.view().owning_container, killed: e.being_killed(),
            })
        }),
{ reveal(kernel_k_to_nonlock_kernel_u); }
} // verus!
