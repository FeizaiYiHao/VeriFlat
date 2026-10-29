use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal};
use crate::*;

verus! {
pub proof fn kernel_container_ancestry_projection_at(krnl: &KernelK, container: RwLockContainerPtr)
    requires krnl.ctn_mp.dom().contains(container),
    ensures
        kernel_k_to_kernel_u(*krnl).container_map.dom().contains(container),
        kernel_k_to_kernel_u(*krnl).container_map[container].uppertree_seq == krnl.ctn_mp.spec_index(container).view_ghost().uppertree_seq.view(),
{ reveal(kernel_k_to_kernel_u); }

pub proof fn kernel_thread_nonlock_projection_at(krnl: &KernelK, thread_ptr: RwLockThreadPtr)
    requires krnl.thr_mp.dom().contains(thread_ptr),
    ensures
        kernel_k_to_nonlock_kernel_u(*krnl).thread_map.dom().contains(thread_ptr),
        ({
            let thread = krnl.thr_mp.spec_index(thread_ptr);
            let t = thread.view();
            kernel_k_to_nonlock_kernel_u(*krnl).thread_map.spec_index(thread_ptr) == (ThreadU {
                lock_state: LockStateU::Unlocked, state: t.state, caller: t.caller, callee: t.callee,
                owning_container: t.owning_container, owning_proc: t.owning_proc, last_cpu: t.last_cpu,
                quota_4k: t.quota_4k, quota_2m: t.quota_2m, quota_1g: t.quota_1g,
                endpoint_descriptors: t.endpoint_descriptors.view(), blocking_endpoint_ptr: t.blocking_endpoint_ptr,
                ipc_payload: t.ipc_payload, error_code: t.error_code,
                trap_frame: if t.trap_frame.is_some() { Some(*t.trap_frame.get_some_0()) } else { None },
                syscall_progress: t.syscall_progress.view(), killed: thread.being_killed(),
            })
        }),
{ reveal(kernel_k_to_nonlock_kernel_u); }

pub proof fn kernel_process_nonlock_projection_at(krnl: &KernelK, ptr: RwLockProcessPtr)
    requires krnl.prc_mp.dom().contains(ptr),
    ensures
        kernel_k_to_nonlock_kernel_u(*krnl).process_map.dom().contains(ptr),
        ({
            let p = krnl.prc_mp.spec_index(ptr).view();
            let p_ghost = krnl.prc_mp.spec_index(ptr).view_ghost();
            let p_ro = krnl.prc_mp.spec_index(ptr).view_rodata().view();
            kernel_k_to_nonlock_kernel_u(*krnl).process_map[ptr] == (ProcessU {
                lock_state: LockStateU::Unlocked, zombie: p.zombie,
                pagetable: if p.zombie { None } else {
                    let t = pagetable_map_user_view(krnl.pt_mp, krnl.pt_lower.view()).spec_index(p.pagetable);
                    Some(PageTableU { lock_state: LockStateU::Unlocked, ..t })
                },
                iommu_table: match (p.zombie, p.iommu_table) {
                    (false, Some(iommu_table)) => {
                        let t = iommu_table_map_user_view(krnl.it_mp).spec_index(iommu_table);
                        Some(PageTableU { lock_state: LockStateU::Unlocked, ..t })
                    },
                    _ => None,
                },
                pcid: p_ro.pcid, owning_container: p_ro.owning_container, owned_pci_functions: p_ghost.owned_pci_functions.view(), quota_4k: p.quota_4k, quota_2m: p.quota_2m, quota_1g: p.quota_1g,
                parent: p_ro.parent, children: p.children.view(), depth: p_ro.depth, uppertree_seq: p_ghost.uppertree_seq.view(),
                subtree_set: p_ghost.subtree_set.view(), owned_threads: p.owned_threads.view(), killed: krnl.prc_mp.spec_index(ptr).being_killed(),
            })
        }),
{ reveal(kernel_k_to_nonlock_kernel_u); }

/// The projected map domains and scalar fields of the user projection, without unfolding any projected entry.
pub proof fn kernel_u_domains_projection(krnl: &KernelK)
    ensures
        kernel_k_to_kernel_u(*krnl).cpu_array.len() == NUM_CPUS,
        kernel_k_to_kernel_u(*krnl).container_map.dom() == krnl.ctn_mp.dom(),
        kernel_k_to_kernel_u(*krnl).process_map.dom() == krnl.prc_mp.dom(),
        kernel_k_to_kernel_u(*krnl).thread_map.dom() == krnl.thr_mp.dom(),
        kernel_k_to_kernel_u(*krnl).endpoint_map.dom() == krnl.ep_mp.dom(),
        kernel_k_to_kernel_u(*krnl).iommu_root_table == krnl.irt.view().user_view(),
        kernel_k_to_kernel_u(*krnl).cpu_tlb == krnl.cpu_tlb.view(),
        kernel_k_to_kernel_u(*krnl).iommu_tlb == krnl.iommu_tlb.view(),
        kernel_k_to_kernel_u(*krnl).kernel_l4_end == krnl.dflt_pt.view().kernel_l4_end,
{ reveal(kernel_k_to_kernel_u); }

/// One cpu slot of the user projection, without unfolding the other projected maps.
pub proof fn kernel_cpu_projection_at(krnl: &KernelK, cpu_id: CpuId)
    requires index_valid(NUM_CPUS, cpu_id),
    ensures
        kernel_k_to_kernel_u(*krnl).cpu_array.len() == NUM_CPUS,
        ({
            let c = krnl.cpu_arr.spec_index(cpu_id).value.view().view();
            kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int] == (CpuU {
                lock_state: krnl.cpu_arr.spec_index(cpu_id).value.lock_state_u(), owning_container: c.owning_container, state: c.state,
                current_process: c.current_process, current_thread: c.current_thread, killed: krnl.cpu_arr.spec_index(cpu_id).value.being_killed(),
                op: krnl.cpu_op.view().view()[cpu_id as int],
            })
        }),
{ reveal(kernel_k_to_kernel_u); }

/// One container entry of the user projection, without unfolding the other projected maps.
pub proof fn kernel_container_projection_at(krnl: &KernelK, ptr: RwLockContainerPtr)
    requires krnl.ctn_mp.dom().contains(ptr),
    ensures
        kernel_k_to_kernel_u(*krnl).container_map.dom().contains(ptr),
        ({
            let c = krnl.ctn_mp.spec_index(ptr).view();
            let c_ghost = krnl.ctn_mp.spec_index(ptr).view_ghost();
            let c_ro = krnl.ctn_mp.spec_index(ptr).view_rodata().view();
            kernel_k_to_kernel_u(*krnl).container_map[ptr] == (ContainerU {
                lock_state: krnl.ctn_mp.spec_index(ptr).lock_state_u(), lock_process_owner: krnl.ctn_mp.spec_index(ptr).lock_process_owner_u(), zombie: c.zombie,
                children: c.children.view(), uppertree_seq: c_ghost.uppertree_seq.view(), subtree_set: c_ghost.subtree_set.view(),
                root_process: c.root_process, owned_processes: c_ghost.owned_processes.view(), owned_threads: c_ghost.owned_threads.view(),
                owned_endpoints: c_ghost.owned_endpoints.view(), owned_pages: c.owned_pages.view(),
                parent: c_ro.parent, depth: c_ro.depth, cpu_set: c_ro.cpu_set,
                cpu_set_lock: krnl.cpu_set_mp.spec_index(c_ro.cpu_set).lock_state_u(),
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
{ reveal(kernel_k_to_kernel_u); }

/// Shard `cpu_id` of a scheduler's user projection is that shard's run queue.
pub proof fn kernel_scheduler_shards_projection_at(scheduler: Scheduler, cpu_id: CpuId)
    requires index_valid(NUM_CPUS, cpu_id),
    ensures
        scheduler_shards_of(scheduler).len() == NUM_CPUS,
        scheduler_shards_of(scheduler)[cpu_id as int] == scheduler.shard(cpu_id).queue.view(),
{ reveal(scheduler_shards_of); }

/// One process entry of the user projection, without unfolding the other projected maps.
pub proof fn kernel_process_projection_at(krnl: &KernelK, ptr: RwLockProcessPtr)
    requires krnl.prc_mp.dom().contains(ptr),
    ensures
        kernel_k_to_kernel_u(*krnl).process_map.dom().contains(ptr),
        ({
            let p = krnl.prc_mp.spec_index(ptr).view();
            let p_ghost = krnl.prc_mp.spec_index(ptr).view_ghost();
            let p_ro = krnl.prc_mp.spec_index(ptr).view_rodata().view();
            kernel_k_to_kernel_u(*krnl).process_map[ptr] == (ProcessU {
                lock_state: krnl.prc_mp.spec_index(ptr).lock_state_u(), zombie: p.zombie,
                pagetable: if p.zombie { None } else { Some(pagetable_map_user_view(krnl.pt_mp, krnl.pt_lower.view()).spec_index(p.pagetable)) },
                iommu_table: match (p.zombie, p.iommu_table) {
                    (false, Some(iommu_table)) => Some(iommu_table_map_user_view(krnl.it_mp).spec_index(iommu_table)),
                    _ => None,
                },
                pcid: p_ro.pcid, owning_container: p_ro.owning_container, owned_pci_functions: p_ghost.owned_pci_functions.view(), quota_4k: p.quota_4k, quota_2m: p.quota_2m, quota_1g: p.quota_1g,
                parent: p_ro.parent, children: p.children.view(), depth: p_ro.depth, uppertree_seq: p_ghost.uppertree_seq.view(),
                subtree_set: p_ghost.subtree_set.view(), owned_threads: p.owned_threads.view(), killed: krnl.prc_mp.spec_index(ptr).being_killed(),
            })
        }),
{ reveal(kernel_k_to_kernel_u); }

/// One B/D/F slot of the user projection's root table, without unfolding the other projected maps.
pub proof fn kernel_iommu_root_table_projection_at(krnl: &KernelK, bus: usize, device: usize, function: usize)
    requires pci_bdf_valid(bus, device, function),
    ensures kernel_k_to_kernel_u(*krnl).iommu_root_table.attached[bus as int][device as int][function as int] == (krnl.irt.view().spec_index_iommu_root(bus, device, function) is Some),
{ reveal(kernel_k_to_kernel_u); reveal(IommuRootTable::user_view); }

/// One thread entry of the user projection, without unfolding the other projected maps.
pub proof fn kernel_thread_projection_at(krnl: &KernelK, ptr: RwLockThreadPtr)
    requires krnl.thr_mp.dom().contains(ptr),
    ensures
        kernel_k_to_kernel_u(*krnl).thread_map.dom().contains(ptr),
        ({
            let thread = krnl.thr_mp.spec_index(ptr);
            let t = thread.view();
            kernel_k_to_kernel_u(*krnl).thread_map[ptr] == (ThreadU {
                lock_state: thread.lock_state_u(), state: t.state, caller: t.caller, callee: t.callee,
                owning_container: t.owning_container, owning_proc: t.owning_proc, last_cpu: t.last_cpu,
                quota_4k: t.quota_4k, quota_2m: t.quota_2m, quota_1g: t.quota_1g,
                endpoint_descriptors: t.endpoint_descriptors.view(), blocking_endpoint_ptr: t.blocking_endpoint_ptr,
                ipc_payload: t.ipc_payload, error_code: t.error_code,
                trap_frame: if t.trap_frame.is_some() { Some(*t.trap_frame.get_some_0()) } else { None },
                syscall_progress: t.syscall_progress.view(), killed: thread.being_killed(),
            })
        }),
{ reveal(kernel_k_to_kernel_u); }

/// One endpoint entry of the user projection, without unfolding the other projected maps.
pub proof fn kernel_endpoint_projection_at(krnl: &KernelK, ptr: RwLockEndpointPtr)
    requires krnl.ep_mp.dom().contains(ptr),
    ensures
        kernel_k_to_kernel_u(*krnl).endpoint_map.dom().contains(ptr),
        ({
            let e = krnl.ep_mp.spec_index(ptr);
            kernel_k_to_kernel_u(*krnl).endpoint_map[ptr] == (EndpointU {
                lock_state: e.lock_state_u(), queue: e.view().queue.view(), queue_state: e.view().queue_state,
                owning_threads: e.view().owning_threads.view(), owning_container: e.view().owning_container, killed: e.being_killed(),
            })
        }),
{ reveal(kernel_k_to_kernel_u); }

pub proof fn kernel_endpoint_queue_projection_at(krnl: &KernelK, endpoint: RwLockEndpointPtr)
    requires krnl.ep_mp.dom().contains(endpoint),
    ensures kernel_k_to_kernel_u(*krnl).endpoint_map[endpoint].queue == krnl.ep_mp.spec_index(endpoint).view().queue.view(),
{ reveal(kernel_k_to_kernel_u); }

pub proof fn kernel_write_held_context_projection(krnl: &KernelK, lctx: &LocalContext, cpu: CpuId, process: RwLockProcessPtr, thread: RwLockThreadPtr, endpoint: Option<RwLockEndpointPtr>)
    requires
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process, TypedLockMode::Write) || krnl.prc_mp.dom().contains(process),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread, TypedLockMode::Write),
        endpoint matches Some(e) ==> krnl.ep_mp.dom().contains(e) && typed_lock_map_contains_mode(lctx.endpoint_lock_map(), e, TypedLockMode::Write),
    ensures
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu as int].lock_state is WriteLocked,
        typed_lock_map_contains_mode(lctx.process_lock_map(), process, TypedLockMode::Write) ==> kernel_k_to_kernel_u(*krnl).process_map[process].lock_state is WriteLocked,
        kernel_k_to_kernel_u(*krnl).thread_map[thread].lock_state is WriteLocked,
        endpoint matches Some(e) ==> kernel_k_to_kernel_u(*krnl).endpoint_map.dom().contains(e) && kernel_k_to_kernel_u(*krnl).endpoint_map[e].lock_state is WriteLocked,
        kernel_k_to_kernel_u(*krnl).process_map.dom().contains(process),
        kernel_k_to_kernel_u(*krnl).thread_map.dom().contains(thread),
        kernel_k_to_kernel_u(*krnl).thread_map[thread].owning_container == krnl.thr_mp.spec_index(thread).view().owning_container,
        kernel_k_to_kernel_u(*krnl).thread_map[thread].owning_proc == krnl.thr_mp.spec_index(thread).view().owning_proc,
        kernel_k_to_kernel_u(*krnl).thread_map[thread].syscall_progress == krnl.thr_mp.spec_index(thread).view().syscall_progress.view(),
        kernel_k_to_kernel_u(*krnl).cpu_array[cpu as int].current_thread == krnl.cpu_arr.spec_index(cpu).view().view().view().current_thread,
        kernel_k_to_kernel_u(*krnl).process_map[process].pcid == krnl.prc_mp.spec_index(process).view_rodata().view().pcid,
        !krnl.prc_mp.spec_index(process).view().zombie && typed_lock_map_contains_mode(lctx.pagetable_lock_map(), krnl.prc_mp.spec_index(process).view().pagetable, TypedLockMode::Write) ==> {
            &&& kernel_k_to_kernel_u(*krnl).process_map[process].pagetable is Some
            &&& kernel_k_to_kernel_u(*krnl).process_map[process].pagetable->Some_0.lock_state is WriteLocked
        },
        typed_lock_map_contains_mode(lctx.container_lock_map(), krnl.thr_mp.spec_index(thread).view().owning_container, TypedLockMode::Write) ==> {
            &&& kernel_k_to_kernel_u(*krnl).container_map.dom().contains(krnl.thr_mp.spec_index(thread).view().owning_container)
            &&& kernel_k_to_kernel_u(*krnl).container_map[krnl.thr_mp.spec_index(thread).view().owning_container].lock_state is WriteLocked
        },
        ({
            let container = krnl.thr_mp.spec_index(thread).view().owning_container;
            typed_lock_map_contains_mode(lctx.container_lock_map(), container, TypedLockMode::Write)
                && typed_lock_map_contains_mode(lctx.cpu_set_lock_map(), krnl.ctn_mp.spec_index(container).view_rodata().view().cpu_set, TypedLockMode::Write)
                ==> kernel_k_to_kernel_u(*krnl).container_map[container].cpu_set_lock is WriteLocked
        }),
        ({
            let owner = krnl.thr_mp.spec_index(thread).view().owning_proc;
            krnl.prc_mp.dom().contains(owner) && !krnl.prc_mp.spec_index(owner).view().zombie
                && typed_lock_map_contains_mode(lctx.pagetable_lock_map(), krnl.prc_mp.spec_index(owner).view().pagetable, TypedLockMode::Write) ==> {
                &&& kernel_k_to_kernel_u(*krnl).process_map.dom().contains(owner)
                &&& kernel_k_to_kernel_u(*krnl).process_map[owner].pagetable is Some
                &&& kernel_k_to_kernel_u(*krnl).process_map[owner].pagetable->Some_0.lock_state is WriteLocked
            }
        }),
        krnl.prc_mp.spec_index(process).view().iommu_table is None ==> kernel_k_to_kernel_u(*krnl).process_map[process].iommu_table is None,
        krnl.prc_mp.spec_index(process).view().iommu_table matches Some(t) && !krnl.prc_mp.spec_index(process).view().zombie
            && typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), t, TypedLockMode::Write) ==> {
            &&& kernel_k_to_kernel_u(*krnl).process_map[process].iommu_table is Some
            &&& kernel_k_to_kernel_u(*krnl).process_map[process].iommu_table->Some_0.lock_state is WriteLocked
        },
{
    reveal(kernel_k_to_kernel_u); reveal(LockedArray::typed_lock_map_aligned);
    if typed_lock_map_contains_mode(lctx.process_lock_map(), process, TypedLockMode::Write) { krnl.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), process); }
    krnl.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread);
    if let Some(e) = endpoint { krnl.ep_mp.typed_lock_map_aligned_write_at(lctx.endpoint_lock_map(), lctx.thread_id(), e); }
    let pagetable = krnl.prc_mp.spec_index(process).view().pagetable;
    let container = krnl.thr_mp.spec_index(thread).view().owning_container;
    if typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write) { krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable); }
    if typed_lock_map_contains_mode(lctx.container_lock_map(), container, TypedLockMode::Write) { krnl.ctn_mp.typed_lock_map_aligned_write_at(lctx.container_lock_map(), lctx.thread_id(), container); }
    let cpu_set = krnl.ctn_mp.spec_index(container).view_rodata().view().cpu_set;
    if typed_lock_map_contains_mode(lctx.cpu_set_lock_map(), cpu_set, TypedLockMode::Write) { krnl.cpu_set_mp.typed_lock_map_aligned_write_at(lctx.cpu_set_lock_map(), lctx.thread_id(), cpu_set); }
    let owner_table = krnl.prc_mp.spec_index(krnl.thr_mp.spec_index(thread).view().owning_proc).view().pagetable;
    if typed_lock_map_contains_mode(lctx.pagetable_lock_map(), owner_table, TypedLockMode::Write) { krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), owner_table); }
    if let Some(t) = krnl.prc_mp.spec_index(process).view().iommu_table {
        if typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), t, TypedLockMode::Write) { krnl.it_mp.typed_lock_map_aligned_write_at(lctx.iommu_table_lock_map(), lctx.thread_id(), t); }
    }
}

/// Expose concrete entries of the user projection without unfolding every projected map at the caller.
pub proof fn kernel_cpu_thread_projection_at(krnl: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, endpoint_ptr: Option<RwLockEndpointPtr>)
    requires
        index_valid(NUM_CPUS, cpu_id),
        krnl.prc_mp.dom().contains(process_ptr),
        krnl.thr_mp.dom().contains(thread_ptr),
        endpoint_ptr is Some ==> krnl.ep_mp.dom().contains(endpoint_ptr->Some_0),
    ensures
        kernel_k_to_kernel_u(*krnl).cpu_array.len() == NUM_CPUS,
        kernel_k_to_kernel_u(*krnl).container_map.dom() == krnl.ctn_mp.dom(),
        kernel_k_to_kernel_u(*krnl).process_map.dom() == krnl.prc_mp.dom(),
        kernel_k_to_kernel_u(*krnl).thread_map.dom() == krnl.thr_mp.dom(),
        kernel_k_to_kernel_u(*krnl).endpoint_map.dom() == krnl.ep_mp.dom(),
        ({
            let cpu = krnl.cpu_arr.spec_index(cpu_id).value;
            let c = cpu.view().view();
            kernel_k_to_kernel_u(*krnl).cpu_array[cpu_id as int] == (CpuU {
                lock_state: cpu.lock_state_u(), owning_container: c.owning_container, state: c.state,
                current_process: c.current_process, current_thread: c.current_thread, killed: cpu.being_killed(),
                op: krnl.cpu_op.view().view()[cpu_id as int],
            })
        }),
        kernel_k_to_kernel_u(*krnl).process_map.spec_index(process_ptr).lock_state == krnl.prc_mp.spec_index(process_ptr).lock_state_u(),
        kernel_k_to_kernel_u(*krnl).process_map.spec_index(process_ptr).killed == krnl.prc_mp.spec_index(process_ptr).being_killed(),
        ({
            let thread = krnl.thr_mp.spec_index(thread_ptr);
            let t = thread.view();
            kernel_k_to_kernel_u(*krnl).thread_map.spec_index(thread_ptr) == (ThreadU {
                lock_state: thread.lock_state_u(), state: t.state, caller: t.caller, callee: t.callee,
                owning_container: t.owning_container, owning_proc: t.owning_proc, last_cpu: t.last_cpu,
                quota_4k: t.quota_4k, quota_2m: t.quota_2m, quota_1g: t.quota_1g,
                endpoint_descriptors: t.endpoint_descriptors.view(), blocking_endpoint_ptr: t.blocking_endpoint_ptr,
                ipc_payload: t.ipc_payload, error_code: t.error_code,
                trap_frame: if t.trap_frame.is_some() { Some(*t.trap_frame.get_some_0()) } else { None },
                syscall_progress: t.syscall_progress.view(), killed: thread.being_killed(),
            })
        }),
        endpoint_ptr is Some ==> {
            let e = krnl.ep_mp.spec_index(endpoint_ptr->Some_0);
            kernel_k_to_kernel_u(*krnl).endpoint_map.spec_index(endpoint_ptr->Some_0) == (EndpointU {
                lock_state: e.lock_state_u(), queue: e.view().queue.view(), queue_state: e.view().queue_state,
                owning_threads: e.view().owning_threads.view(), owning_container: e.view().owning_container, killed: e.being_killed(),
            })
        },
        ({
            let c = krnl.thr_mp.spec_index(thread_ptr).view().owning_container;
            krnl.ctn_mp.dom().contains(c)
                ==> kernel_k_to_kernel_u(*krnl).container_map[c].free_pcids == PcidAllocator::free_pcids(krnl.pcid_allc_mp.spec_index(krnl.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator).view().ref_counters.view())
        }),
{ reveal(kernel_k_to_kernel_u); }

/// Every pagetable's first user L4 index is the projected user-VA bound.
pub proof fn kernel_l4_end_projection_at(krnl: &KernelK, pagetable_ptr: RwLockPageTableRoot)
    requires
        krnl.inv(),
        krnl.pt_mp.dom().contains(pagetable_ptr),
    ensures
        kernel_k_to_kernel_u(*krnl).kernel_l4_end == pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).kernel_l4_end(),
{ reveal(kernel_k_to_kernel_u); reveal(KernelK::default_pagetable_wf); }

/// A live process's projected page table carries its page table's lock mode, and shows the whole 4K, 2M, and 1G
/// mappings when every leaf is present.
pub proof fn kernel_pagetable_mappings_projection_at(krnl: &KernelK, process: RwLockProcessPtr)
    requires
        krnl.prc_mp.dom().contains(process),
        !krnl.prc_mp.spec_index(process).view().zombie,
        krnl.pt_mp.dom().contains(krnl.prc_mp.spec_index(process).view().pagetable),
    ensures
        ({
            let root = krnl.prc_mp.spec_index(process).view().pagetable;
            let table = pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), root);
            let u = kernel_k_to_kernel_u(*krnl).process_map[process].pagetable;
            &&& kernel_k_to_kernel_u(*krnl).process_map.dom().contains(process)
            &&& u is Some
            &&& u->Some_0.lock_state == krnl.pt_mp.spec_index(root).lock_state_u()
            &&& table.leaves_present() ==> {
                &&& u->Some_0.mapping_4k == table.mapping_4k()
                &&& u->Some_0.mapping_2m == table.mapping_2m()
                &&& u->Some_0.mapping_1g == table.mapping_1g()
            }
        }),
{
    reveal(kernel_k_to_kernel_u);
    let table = pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), krnl.prc_mp.spec_index(process).view().pagetable);
    let u = kernel_k_to_kernel_u(*krnl).process_map[process].pagetable->Some_0;
    if table.leaves_present() {
        assert_maps_equal!(u.mapping_4k, table.mapping_4k(), va => {});
        assert_maps_equal!(u.mapping_2m, table.mapping_2m(), va => {});
        assert_maps_equal!(u.mapping_1g, table.mapping_1g(), va => {});
    }
}

/// A live process's projected page table shows no valid user 4K mapping once every user index path of its page table
/// at or above its kernel L4 end names no present 4K entry.
pub proof fn kernel_pagetable_user_4k_unmapped_projection_at(krnl: &KernelK, process: RwLockProcessPtr)
    requires
        krnl.inv(),
        krnl.prc_mp.dom().contains(process),
        !krnl.prc_mp.spec_index(process).view().zombie,
        krnl.pt_mp.dom().contains(krnl.prc_mp.spec_index(process).view().pagetable),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
            #![trigger pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), krnl.prc_mp.spec_index(process).view().pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && KERNEL_MEM_END_L4INDEX <= l4i
                && pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), krnl.prc_mp.spec_index(process).view().pagetable).kernel_l4_end() <= l4i
                && pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), krnl.prc_mp.spec_index(process).view().pagetable).mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                ==> !pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), krnl.prc_mp.spec_index(process).view().pagetable).mapping_4k().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present,
    ensures
        kernel_k_to_kernel_u(*krnl).process_map.dom().contains(process),
        kernel_k_to_kernel_u(*krnl).process_map[process].pagetable is Some,
        forall|va: VAddr| #![trigger kernel_k_to_kernel_u(*krnl).process_map[process].pagetable->Some_0.mapping_4k.dom().contains(va)]
            spec_va_4k_valid(va) && kernel_k_to_kernel_u(*krnl).kernel_l4_end <= spec_v2l4index(va) ==> !kernel_k_to_kernel_u(*krnl).process_map[process].pagetable->Some_0.mapping_4k.dom().contains(va),
{
    broadcast use spec_va_4k_valid_index_roundtrip;
    let pagetable = krnl.prc_mp.spec_index(process).view().pagetable;
    kernel_l4_end_projection_at(krnl, pagetable); kernel_pagetable_mappings_projection_at(krnl, process); reveal(kernel_k_to_kernel_u);
}

/// A live process's projected IOMMU table carries its IOMMU table's lock mode, and shows the whole 4K, 2M, and 1G
/// mappings when every leaf is present.
pub proof fn kernel_iommu_table_mappings_projection_at(krnl: &KernelK, process: RwLockProcessPtr)
    requires
        krnl.prc_mp.dom().contains(process),
        !krnl.prc_mp.spec_index(process).view().zombie,
        krnl.prc_mp.spec_index(process).view().iommu_table is Some,
        krnl.it_mp.dom().contains(krnl.prc_mp.spec_index(process).view().iommu_table->Some_0),
    ensures
        ({
            let table = krnl.it_mp.spec_index(krnl.prc_mp.spec_index(process).view().iommu_table->Some_0);
            let u = kernel_k_to_kernel_u(*krnl).process_map[process].iommu_table;
            &&& kernel_k_to_kernel_u(*krnl).process_map.dom().contains(process)
            &&& u is Some
            &&& u->Some_0.lock_state == table.lock_state_u()
            &&& table.view().leaves_present() ==> {
                &&& u->Some_0.mapping_4k == table.view().mapping_4k()
                &&& u->Some_0.mapping_2m == table.view().mapping_2m()
                &&& u->Some_0.mapping_1g == table.view().mapping_1g()
            }
        }),
{
    reveal(kernel_k_to_kernel_u);
    let table = krnl.it_mp.spec_index(krnl.prc_mp.spec_index(process).view().iommu_table->Some_0).view();
    let u = kernel_k_to_kernel_u(*krnl).process_map[process].iommu_table->Some_0;
    if table.leaves_present() {
        assert_maps_equal!(u.mapping_4k, table.mapping_4k(), va => {});
        assert_maps_equal!(u.mapping_2m, table.mapping_2m(), va => {});
        assert_maps_equal!(u.mapping_1g, table.mapping_1g(), va => {});
    }
}

/// A live process's projected IOMMU table shows no 4K mapping once no index path of its IOMMU table names a 4K entry.
pub proof fn kernel_iommu_table_4k_unmapped_projection_at(krnl: &KernelK, process: RwLockProcessPtr)
    requires
        krnl.inv(),
        krnl.prc_mp.dom().contains(process),
        !krnl.prc_mp.spec_index(process).view().zombie,
        krnl.prc_mp.spec_index(process).view().iommu_table is Some,
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
            #![trigger krnl.it_mp.spec_index(krnl.prc_mp.spec_index(process).view().iommu_table->Some_0).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                ==> !krnl.it_mp.spec_index(krnl.prc_mp.spec_index(process).view().iommu_table->Some_0).view().mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))),
    ensures
        kernel_k_to_kernel_u(*krnl).process_map.dom().contains(process),
        kernel_k_to_kernel_u(*krnl).process_map[process].iommu_table is Some,
        forall|iova: VAddr| #![trigger kernel_k_to_kernel_u(*krnl).process_map[process].iommu_table->Some_0.mapping_4k.dom().contains(iova)]
            !kernel_k_to_kernel_u(*krnl).process_map[process].iommu_table->Some_0.mapping_4k.dom().contains(iova),
{
    let iommu_table = krnl.prc_mp.spec_index(process).view().iommu_table->Some_0;
    assert(krnl.it_mp.dom().contains(iommu_table)) by { process_iommu_table_match_process_at(krnl.prc_mp, krnl.it_mp, process); };
    iommu_table_perms_wf_at(krnl.it_mp, iommu_table);
    let table = krnl.it_mp.spec_index(iommu_table).view();
    assert forall|iova: VAddr| #![trigger table.mapping_4k().dom().contains(iova)] !table.mapping_4k().dom().contains(iova) by {
        if table.mapping_4k().dom().contains(iova) {
            let l4i = spec_v2l4index(iova);
            let l3i = spec_v2l3index(iova);
            let l2i = spec_v2l2index(iova);
            let l1i = spec_v2l1index(iova);
            assert(iova_4k_valid(iova));
            assert(iova_4k_valid(iova) && spec_v2l4index(iova) == l4i && spec_v2l3index(iova) == l3i && spec_v2l2index(iova) == l2i && spec_v2l1index(iova) == l1i
                ==> pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_index2va((l4i, l3i, l2i, l1i)) == iova) by (bit_vector);
            assert(!table.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))));
        }
    };
    kernel_process_projection_at(krnl, process);
}

/// Project the cpu and its running thread while the thread records a share, the objects that share
/// names, the source thread's process, and the target page table's write lock.
pub proof fn kernel_share_4k_objects_projection(krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId)
    requires
        typed_lock_maps_aligned(krnl, lctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread is Some,
        typed_lock_map_contains_mode(lctx.thread_lock_map(), krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0, TypedLockMode::Write),
        krnl.thr_mp.spec_index(krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0).view().syscall_progress.view() matches Some(SyscallProgress::Share4k { .. }),
        ({
            let caller = krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0;
            krnl.thr_mp.spec_index(caller).view().syscall_progress.view()->Some_0->Share4k_origin matches Share4kOrigin::IpcPages { peer }
                ==> krnl.thr_mp.spec_index(peer).view().state is IPC_TRANSIT && krnl.thr_mp.spec_index(peer).view().state->IPC_TRANSIT_partner == caller
        }),
        krnl.thr_mp.dom().contains(share_4k_objects_k(*krnl, cpu_id).source_thread),
        krnl.thr_mp.dom().contains(share_4k_objects_k(*krnl, cpu_id).quota_thread),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), share_4k_objects_k(*krnl, cpu_id).source_thread, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), share_4k_objects_k(*krnl, cpu_id).quota_thread, TypedLockMode::Write),
        krnl.ctn_mp.dom().contains(share_4k_objects_k(*krnl, cpu_id).target_container),
    ensures
        ({
            let u = kernel_k_to_kernel_u(*krnl);
            let caller = krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0;
            let objects = share_4k_objects_k(*krnl, cpu_id);
            let target = krnl.prc_mp.spec_index(objects.target);
            &&& share_4k_locked(u, cpu_id)
            &&& u.cpu_array[cpu_id as int].current_thread == Some(caller)
            &&& u.thread_map[caller].syscall_progress == krnl.thr_mp.spec_index(caller).view().syscall_progress.view()
            &&& share_4k_objects(u, cpu_id) == objects
            &&& u.container_map.dom().contains(objects.target_container)
            &&& typed_lock_map_contains_mode(lctx.container_lock_map(), objects.target_container, TypedLockMode::Write) ==> u.container_map[objects.target_container].lock_state is WriteLocked
            &&& objects.transfer_source is Some && typed_lock_map_contains_mode(lctx.container_lock_map(), objects.transfer_source->Some_0, TypedLockMode::Write) ==> {
                &&& u.container_map.dom().contains(objects.transfer_source->Some_0)
                &&& u.container_map[objects.transfer_source->Some_0].lock_state is WriteLocked
            }
            &&& u.thread_map.dom().contains(objects.source_thread)
            &&& u.thread_map[objects.source_thread].owning_proc == krnl.thr_mp.spec_index(objects.source_thread).view().owning_proc
            &&& u.container_map[objects.target_container].parent == krnl.ctn_mp.spec_index(objects.target_container).view_rodata().view().parent
            &&& krnl.prc_mp.dom().contains(objects.target) ==> u.process_map[objects.target].owning_container == target.view_rodata().view().owning_container
            &&& krnl.prc_mp.dom().contains(objects.target) && !target.view().zombie && typed_lock_map_contains_mode(lctx.pagetable_lock_map(), target.view().pagetable, TypedLockMode::Write) ==> {
                &&& u.process_map.dom().contains(objects.target)
                &&& u.process_map[objects.target].pagetable is Some
                &&& u.process_map[objects.target].pagetable->Some_0.lock_state is WriteLocked
            }
        }),
{
    reveal(kernel_k_to_kernel_u); reveal(LockedArray::typed_lock_map_aligned); reveal(share_4k_objects_k);
    let caller = krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0;
    krnl.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), caller);
    krnl.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), share_4k_objects_k(*krnl, cpu_id).source_thread);
    krnl.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), share_4k_objects_k(*krnl, cpu_id).quota_thread);
    let pagetable = krnl.prc_mp.spec_index(share_4k_objects_k(*krnl, cpu_id).target).view().pagetable;
    if typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write) { krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable); }
    let container = share_4k_objects_k(*krnl, cpu_id).target_container;
    if typed_lock_map_contains_mode(lctx.container_lock_map(), container, TypedLockMode::Write) { krnl.ctn_mp.typed_lock_map_aligned_write_at(lctx.container_lock_map(), lctx.thread_id(), container); }
    if let Some(source) = share_4k_objects_k(*krnl, cpu_id).transfer_source {
        if typed_lock_map_contains_mode(lctx.container_lock_map(), source, TypedLockMode::Write) { krnl.ctn_mp.typed_lock_map_aligned_write_at(lctx.container_lock_map(), lctx.thread_id(), source); }
    }
}

} // verus!
