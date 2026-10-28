use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal};
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
                op: cpu_op_after_step(c.state),
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
                lock_state: LockStateU::Unlocked, lock_process_owner: None, zombie: c.zombie,
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
                cpu_set_killed: krnl.cpu_set_mp.spec_index(c_ro.cpu_set).being_killed(),
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

/// The projected map domains and scalar fields of the lock-selectable user projection, without unfolding any projected entry.
pub proof fn kernel_u_user_domains_projection(krnl: &KernelK, include_lock_state: bool)
    ensures
        kernel_k_user_projection(*krnl, include_lock_state).cpu_array.len() == NUM_CPUS,
        kernel_k_user_projection(*krnl, include_lock_state).container_map.dom() == krnl.ctn_mp.dom(),
        kernel_k_user_projection(*krnl, include_lock_state).process_map.dom() == krnl.prc_mp.dom(),
        kernel_k_user_projection(*krnl, include_lock_state).thread_map.dom() == krnl.thr_mp.dom(),
        kernel_k_user_projection(*krnl, include_lock_state).endpoint_map.dom() == krnl.ep_mp.dom(),
        kernel_k_user_projection(*krnl, include_lock_state).iommu_root_table == krnl.irt.view().user_view(),
        kernel_k_user_projection(*krnl, include_lock_state).cpu_tlb == krnl.cpu_tlb.view(),
        kernel_k_user_projection(*krnl, include_lock_state).iommu_tlb == krnl.iommu_tlb.view(),
        kernel_k_user_projection(*krnl, include_lock_state).kernel_l4_end == krnl.dflt_pt.view().kernel_l4_end,
{}

/// One cpu slot of the lock-selectable user projection, without unfolding the other projected maps.
pub proof fn kernel_cpu_user_projection_at(krnl: &KernelK, include_lock_state: bool, cpu_id: CpuId)
    requires index_valid(NUM_CPUS, cpu_id),
    ensures
        kernel_k_user_projection(*krnl, include_lock_state).cpu_array.len() == NUM_CPUS,
        ({
            let c = krnl.cpu_arr.spec_index(cpu_id).value.view().view();
            kernel_k_user_projection(*krnl, include_lock_state).cpu_array[cpu_id as int] == (CpuU {
                lock_state: if include_lock_state { krnl.cpu_arr.spec_index(cpu_id).value.lock_state_u() } else { LockStateU::Unlocked },
                owning_container: c.owning_container, state: c.state, current_process: c.current_process, current_thread: c.current_thread,
                killed: krnl.cpu_arr.spec_index(cpu_id).value.being_killed(),
                op: if include_lock_state { krnl.cpu_op.view().view()[cpu_id as int] } else { cpu_op_after_step(c.state) },
            })
        }),
{}

/// One container entry of the lock-selectable user projection, without unfolding the other projected maps.
pub proof fn kernel_container_user_projection_at(krnl: &KernelK, include_lock_state: bool, ptr: RwLockContainerPtr)
    requires krnl.ctn_mp.dom().contains(ptr),
    ensures
        kernel_k_user_projection(*krnl, include_lock_state).container_map.dom().contains(ptr),
        ({
            let c = krnl.ctn_mp.spec_index(ptr).view();
            let c_ghost = krnl.ctn_mp.spec_index(ptr).view_ghost();
            let c_ro = krnl.ctn_mp.spec_index(ptr).view_rodata().view();
            kernel_k_user_projection(*krnl, include_lock_state).container_map[ptr] == (ContainerU {
                lock_state: if include_lock_state { krnl.ctn_mp.spec_index(ptr).lock_state_u() } else { LockStateU::Unlocked },
                lock_process_owner: if include_lock_state { krnl.ctn_mp.spec_index(ptr).lock_process_owner_u() } else { None }, zombie: c.zombie,
                children: c.children.view(), uppertree_seq: c_ghost.uppertree_seq.view(), subtree_set: c_ghost.subtree_set.view(),
                root_process: c.root_process, owned_processes: c_ghost.owned_processes.view(), owned_threads: c_ghost.owned_threads.view(),
                owned_endpoints: c_ghost.owned_endpoints.view(), owned_pages: c.owned_pages.view(),
                parent: c_ro.parent, depth: c_ro.depth, cpu_set: c_ro.cpu_set,
                cpu_set_lock: if include_lock_state { krnl.cpu_set_mp.spec_index(c_ro.cpu_set).lock_state_u() } else { LockStateU::Unlocked },
                cpu_offline_requests: cpu_offline_requests_of(krnl.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(ptr))),
                scheduler: scheduler_shards_of(krnl.sched_mp.spec_index(c_ro.scheduler)),
                free_pcids: PcidAllocator::free_pcids(krnl.pcid_allc_mp.spec_index(c_ro.pcid_allocator).view().ref_counters.view()),
                quota_4k: krnl.allc_4k_mp.spec_index(c_ro.allocator_ptr_4k).quota.view().view(),
                quota_2m: krnl.allc_2m_mp.spec_index(c_ro.allocator_ptr_2m).quota.view().view(),
                quota_1g: krnl.allc_1g_mp.spec_index(c_ro.allocator_ptr_1g).quota.view().view(),
                killed: krnl.ctn_mp.spec_index(ptr).being_killed(),
                cpu_set_killed: krnl.cpu_set_mp.spec_index(c_ro.cpu_set).being_killed(),
            })
        }),
{}

/// One process entry of the lock-selectable user projection, without unfolding the other projected maps.
pub proof fn kernel_process_user_projection_at(krnl: &KernelK, include_lock_state: bool, ptr: RwLockProcessPtr)
    requires krnl.prc_mp.dom().contains(ptr),
    ensures
        kernel_k_user_projection(*krnl, include_lock_state).process_map.dom().contains(ptr),
        ({
            let p = krnl.prc_mp.spec_index(ptr).view();
            let p_ghost = krnl.prc_mp.spec_index(ptr).view_ghost();
            let p_ro = krnl.prc_mp.spec_index(ptr).view_rodata().view();
            kernel_k_user_projection(*krnl, include_lock_state).process_map[ptr] == (ProcessU {
                lock_state: if include_lock_state { krnl.prc_mp.spec_index(ptr).lock_state_u() } else { LockStateU::Unlocked }, zombie: p.zombie,
                pagetable: if p.zombie { None } else {
                    let t = pagetable_map_user_view(krnl.pt_mp, krnl.pt_lower.view()).spec_index(p.pagetable);
                    Some(if include_lock_state { t } else { PageTableU { lock_state: LockStateU::Unlocked, ..t } })
                },
                iommu_table: match (p.zombie, p.iommu_table) {
                    (false, Some(iommu_table)) => {
                        let t = iommu_table_map_user_view(krnl.it_mp).spec_index(iommu_table);
                        Some(if include_lock_state { t } else { PageTableU { lock_state: LockStateU::Unlocked, ..t } })
                    },
                    _ => None,
                },
                pcid: p_ro.pcid, owning_container: p_ro.owning_container, owned_pci_functions: p_ghost.owned_pci_functions.view(), quota_4k: p.quota_4k, quota_2m: p.quota_2m, quota_1g: p.quota_1g,
                parent: p_ro.parent, children: p.children.view(), depth: p_ro.depth, uppertree_seq: p_ghost.uppertree_seq.view(),
                subtree_set: p_ghost.subtree_set.view(), owned_threads: p.owned_threads.view(), killed: krnl.prc_mp.spec_index(ptr).being_killed(),
            })
        }),
{}

/// One thread entry of the lock-selectable user projection, without unfolding the other projected maps.
pub proof fn kernel_thread_user_projection_at(krnl: &KernelK, include_lock_state: bool, ptr: RwLockThreadPtr)
    requires krnl.thr_mp.dom().contains(ptr),
    ensures
        kernel_k_user_projection(*krnl, include_lock_state).thread_map.dom().contains(ptr),
        ({
            let thread = krnl.thr_mp.spec_index(ptr);
            let t = thread.view();
            kernel_k_user_projection(*krnl, include_lock_state).thread_map[ptr] == (ThreadU {
                lock_state: if include_lock_state { thread.lock_state_u() } else { LockStateU::Unlocked }, state: t.state, caller: t.caller, callee: t.callee,
                owning_container: t.owning_container, owning_proc: t.owning_proc, last_cpu: t.last_cpu,
                quota_4k: t.quota_4k, quota_2m: t.quota_2m, quota_1g: t.quota_1g,
                endpoint_descriptors: t.endpoint_descriptors.view(), blocking_endpoint_ptr: t.blocking_endpoint_ptr,
                ipc_payload: t.ipc_payload, error_code: t.error_code,
                trap_frame: if t.trap_frame.is_some() { Some(*t.trap_frame.get_some_0()) } else { None },
                syscall_progress: t.syscall_progress.view(), killed: thread.being_killed(),
            })
        }),
{}

/// One endpoint entry of the lock-selectable user projection, without unfolding the other projected maps.
pub proof fn kernel_endpoint_user_projection_at(krnl: &KernelK, include_lock_state: bool, ptr: RwLockEndpointPtr)
    requires krnl.ep_mp.dom().contains(ptr),
    ensures
        kernel_k_user_projection(*krnl, include_lock_state).endpoint_map.dom().contains(ptr),
        ({
            let e = krnl.ep_mp.spec_index(ptr);
            kernel_k_user_projection(*krnl, include_lock_state).endpoint_map[ptr] == (EndpointU {
                lock_state: if include_lock_state { e.lock_state_u() } else { LockStateU::Unlocked }, queue: e.view().queue.view(), queue_state: e.view().queue_state,
                owning_threads: e.view().owning_threads.view(), owning_container: e.view().owning_container, killed: e.being_killed(),
            })
        }),
{}

/// Locking or unlocking a 2M window of `root` changes only that table's window half and keeps its three mapping families,
/// so neither the complete nor the nonlock projection changes.
pub proof fn kernel_pagetable_window_lock_changed_implies_u_eq(pre: &KernelK, post: &KernelK, root: RwLockPageTableRoot)
    requires
        *post == (KernelK { pt_lower: post.pt_lower, ..*pre }),
        post.pt_lower.view() == pre.pt_lower.view().insert(root, post.pt_lower.view().spec_index(root)),
        pagetable_c(post.pt_mp, post.pt_lower.view(), root).mapping_4k() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), root).mapping_4k(),
        pagetable_c(post.pt_mp, post.pt_lower.view(), root).mapping_2m() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), root).mapping_2m(),
        pagetable_c(post.pt_mp, post.pt_lower.view(), root).mapping_1g() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), root).mapping_1g(),
    ensures
        kernel_k_to_kernel_u(*post) == kernel_k_to_kernel_u(*pre),
        kernel_k_to_nonlock_kernel_u(*post) == kernel_k_to_nonlock_kernel_u(*pre),
{
    hide(kernel_k_user_projection);
    assert_maps_equal!(pagetable_map_user_view(post.pt_mp, post.pt_lower.view()), pagetable_map_user_view(pre.pt_mp, pre.pt_lower.view()), r => {
        let a = pagetable_c(post.pt_mp, post.pt_lower.view(), r).user_view(post.pt_mp.spec_index(r).lock_state_u());
        let b = pagetable_c(pre.pt_mp, pre.pt_lower.view(), r).user_view(pre.pt_mp.spec_index(r).lock_state_u());
        assert_maps_equal!(a.mapping_4k, b.mapping_4k); assert_maps_equal!(a.mapping_2m, b.mapping_2m); assert_maps_equal!(a.mapping_1g, b.mapping_1g);
    });
    kernel_u_user_domains_projection(pre, true); kernel_u_user_domains_projection(post, true);
    kernel_u_user_domains_projection(pre, false); kernel_u_user_domains_projection(post, false);
    let pre_u = kernel_k_user_projection(*pre, true);
    let post_u = kernel_k_user_projection(*post, true);
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, true, i as usize); kernel_cpu_user_projection_at(post, true, i as usize); } });
    assert_maps_equal!(post_u.container_map, pre_u.container_map, c => { if pre.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(pre, true, c); kernel_container_user_projection_at(post, true, c); } });
    assert_maps_equal!(post_u.process_map, pre_u.process_map, p => { if pre.prc_mp.dom().contains(p) { kernel_process_user_projection_at(pre, true, p); kernel_process_user_projection_at(post, true, p); } });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map, t => { if pre.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(pre, true, t); kernel_thread_user_projection_at(post, true, t); } });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => { if pre.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(pre, true, e); kernel_endpoint_user_projection_at(post, true, e); } });
    let pre_n = kernel_k_user_projection(*pre, false);
    let post_n = kernel_k_user_projection(*post, false);
    assert_seqs_equal!(post_n.cpu_array == pre_n.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, false, i as usize); kernel_cpu_user_projection_at(post, false, i as usize); } });
    assert_maps_equal!(post_n.container_map, pre_n.container_map, c => { if pre.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(pre, false, c); kernel_container_user_projection_at(post, false, c); } });
    assert_maps_equal!(post_n.process_map, pre_n.process_map, p => { if pre.prc_mp.dom().contains(p) { kernel_process_user_projection_at(pre, false, p); kernel_process_user_projection_at(post, false, p); } });
    assert_maps_equal!(post_n.thread_map, pre_n.thread_map, t => { if pre.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(pre, false, t); kernel_thread_user_projection_at(post, false, t); } });
    assert_maps_equal!(post_n.endpoint_map, pre_n.endpoint_map, e => { if pre.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(pre, false, e); kernel_endpoint_user_projection_at(post, false, e); } });
    reveal(kernel_k_to_kernel_u); reveal(kernel_k_to_nonlock_kernel_u);
}
} // verus!
