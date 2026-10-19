use vstd::prelude::*;
use crate::*;

verus! {
    pub open spec fn pagetable_map_user_view<const TABLE_TYPE: PTType>(pagetable_map: PageTableLockedMapOf<TABLE_TYPE>) -> Map<RwLockPageTableRoot, PageTableU> {
        Map::new(pagetable_map.dom(), |ptr: RwLockPageTableRoot| pagetable_map.spec_index(ptr).view().user_view(pagetable_map.spec_index(ptr).lock_state_u()))
    }

    /// Kernel projection sampled at atomic-section boundaries. Object lock modes
    /// are visible; ownership tokens, reader counts, and allocator internals are not.
    pub ghost struct KernelU{
        pub cpu_array: Seq<CpuU>,
        pub container_map: Map<RwLockContainerPtr, ContainerU>,
        pub process_map: Map<RwLockProcessPtr, ProcessU>,
        pub thread_map: Map<RwLockThreadPtr, ThreadU>,
        pub endpoint_map: Map<RwLockEndpointPtr, EndpointU>,
        pub iommu_root_table: IommuRootTableU,
        pub cpu_tlb: Map<(CpuId, Pcid), SingleTLB>,
        pub iommu_tlb: Map<VtdDomainId, SingleTLB>,
        pub kernel_l4_end: usize,
    }

    /// The range starts at or above the first user L4 index, compared as the implementation's prechecks do.
    pub open spec fn user_va_range(u: KernelU, range: VaRange4K) -> bool { spec_v2l4index(range.start) >= u.kernel_l4_end }

    /// Business-field projection used only to classify steps and state business contracts.
    /// Stored snapshots and step recording always use the complete `KernelU`.
    #[verifier::opaque]
    pub open spec fn kernel_u_nonlock_fields(u: KernelU) -> KernelU {
        KernelU {
            cpu_array: u.cpu_array.map_values(|c: CpuU| CpuU { lock_state: LockStateU::Unlocked, ..c }),
            container_map: Map::new(u.container_map.dom(), |k: RwLockContainerPtr| ContainerU { lock_state: LockStateU::Unlocked, cpu_set_lock: LockStateU::Unlocked, ..u.container_map.spec_index(k) }),
            process_map: Map::new(u.process_map.dom(), |k: RwLockProcessPtr| {
                let p = u.process_map.spec_index(k);
                ProcessU {
                    lock_state: LockStateU::Unlocked,
                    pagetable: match p.pagetable { Some(t) => Some(PageTableU { lock_state: LockStateU::Unlocked, ..t }), None => None },
                    iommu_table: match p.iommu_table { Some(t) => Some(PageTableU { lock_state: LockStateU::Unlocked, ..t }), None => None },
                    ..p
                }
            }),
            thread_map: Map::new(u.thread_map.dom(), |k: RwLockThreadPtr| ThreadU { lock_state: LockStateU::Unlocked, ..u.thread_map.spec_index(k) }),
            endpoint_map: Map::new(u.endpoint_map.dom(), |k: RwLockEndpointPtr| EndpointU { lock_state: LockStateU::Unlocked, ..u.endpoint_map.spec_index(k) }),
            ..u
        }
    }

    /// Project a `KernelK` into its user-visible `KernelU`. This is the
    /// spec-level mapping used at every kernel boundary.  The boundary
    /// compares this projection with the preceding snapshot; only a changed
    /// projection is recorded as a user-visible step.
    #[verifier::opaque]
    pub open spec fn kernel_k_to_kernel_u(krnl: KernelK) -> KernelU { kernel_k_user_projection(krnl, true) }

    /// Direct form of `kernel_u_nonlock_fields(kernel_k_to_kernel_u(krnl))`.
    #[verifier::opaque]
    pub open spec fn kernel_k_to_nonlock_kernel_u(krnl: KernelK) -> KernelU { kernel_k_user_projection(krnl, false) }

    pub open spec fn kernel_k_user_projection(krnl: KernelK, include_lock_state: bool) -> KernelU {
        KernelU {
            iommu_root_table: krnl.irt.view().user_view(), cpu_tlb: krnl.cpu_tlb.view(), iommu_tlb: krnl.iommu_tlb.view(), kernel_l4_end: krnl.dflt_pt.view().kernel_l4_end,
            endpoint_map: Map::new(krnl.ep_mp.dom(), |ptr: RwLockEndpointPtr| {
                let e = krnl.ep_mp.spec_index(ptr);
                EndpointU {
                    lock_state: if include_lock_state { e.lock_state_u() } else { LockStateU::Unlocked },
                    queue: e.view().queue.view(), queue_state: e.view().queue_state,
                    owning_threads: e.view().owning_threads.view(), owning_container: e.view().owning_container,
                    killed: e.being_killed(),
                }
            }),
            cpu_array: Seq::new(NUM_CPUS as nat, |i: int| {
                let c = krnl.cpu_arr.spec_index(i as usize).value.view().view();
                CpuU {
                    lock_state: if include_lock_state { krnl.cpu_arr.spec_index(i as usize).value.lock_state_u() } else { LockStateU::Unlocked },
                    owning_container: c.owning_container, state: c.state, current_process: c.current_process, current_thread: c.current_thread,
                    killed: krnl.cpu_arr.spec_index(i as usize).value.being_killed(),
                }
            }),
            container_map: Map::new(krnl.ctn_mp.dom(), |ptr: RwLockContainerPtr| {
                let c = krnl.ctn_mp.spec_index(ptr).view();
                let c_ghost = krnl.ctn_mp.spec_index(ptr).view_ghost();
                let c_ro = krnl.ctn_mp.spec_index(ptr).view_rodata().view();
                ContainerU {
                    lock_state: if include_lock_state { krnl.ctn_mp.spec_index(ptr).lock_state_u() } else { LockStateU::Unlocked }, zombie: c.zombie,
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
                }
            }),
            process_map: Map::new(krnl.prc_mp.dom(), |ptr: RwLockProcessPtr| {
                let p = krnl.prc_mp.spec_index(ptr).view();
                let p_ghost = krnl.prc_mp.spec_index(ptr).view_ghost();
                let p_ro = krnl.prc_mp.spec_index(ptr).view_rodata().view();
                ProcessU {
                    lock_state: if include_lock_state { krnl.prc_mp.spec_index(ptr).lock_state_u() } else { LockStateU::Unlocked },
                    zombie: p.zombie,
                    pagetable: if p.zombie { None } else {
                        let t = pagetable_map_user_view(krnl.pt_mp).spec_index(p.pagetable);
                        Some(if include_lock_state { t } else { PageTableU { lock_state: LockStateU::Unlocked, ..t } })
                    },
                    iommu_table: match (p.zombie, p.iommu_table) {
                        (false, Some(iommu_table)) => {
                            let t = pagetable_map_user_view(krnl.it_mp).spec_index(iommu_table);
                            Some(if include_lock_state { t } else { PageTableU { lock_state: LockStateU::Unlocked, ..t } })
                        },
                        _ => None,
                    },
                    pcid: p_ro.pcid, owning_container: p_ro.owning_container, owned_pci_functions: p_ghost.owned_pci_functions.view(),
                    quota_4k: p.quota_4k, quota_2m: p.quota_2m, quota_1g: p.quota_1g, parent: p_ro.parent, children: p.children.view(), depth: p_ro.depth,
                    uppertree_seq: p_ghost.uppertree_seq.view(), subtree_set: p_ghost.subtree_set.view(), owned_threads: p.owned_threads.view(),
                    killed: krnl.prc_mp.spec_index(ptr).being_killed(),
                }
            }),
            thread_map: Map::new(krnl.thr_mp.dom(), |ptr: RwLockThreadPtr| {
                let t = krnl.thr_mp.spec_index(ptr).view();
                ThreadU {
                    lock_state: if include_lock_state { krnl.thr_mp.spec_index(ptr).lock_state_u() } else { LockStateU::Unlocked },
                    state: t.state, caller: t.caller, callee: t.callee, owning_container: t.owning_container, owning_proc: t.owning_proc, last_cpu: t.last_cpu,
                    quota_4k: t.quota_4k, quota_2m: t.quota_2m, quota_1g: t.quota_1g, endpoint_descriptors: t.endpoint_descriptors.view(),
                    blocking_endpoint_ptr: t.blocking_endpoint_ptr, ipc_payload: t.ipc_payload, error_code: t.error_code,
                    trap_frame: if t.trap_frame.is_some() { Some(*t.trap_frame.get_some_0()) } else { None },
                    syscall_progress: t.syscall_progress.view(), killed: krnl.thr_mp.spec_index(ptr).being_killed(),
                }
            }),
        }
    }
}
