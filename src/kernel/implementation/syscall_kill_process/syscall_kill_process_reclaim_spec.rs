use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_walk::kill_chain_state;

verus! {
/// The killer at `stage` on `chain`, as in `kill_chain_state`, reclaims the empty live target, the last process of the
/// chain, which owns no PCI function. Besides its cpu, its process, itself, and the chain, it write-holds exactly the target's page table
/// `pagetable` with `pagetable_perm` and the target's IOMMU table `iommu_table`, if any, with `iommu_perm`.
pub open spec fn kill_reclaim_state(
    k: KernelK, lctx: LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, chain: Seq<RwLockProcessPtr>, stage: KillStage,
    cpu_perm: LockPerm, process_perm: LockPerm, thread_perm: LockPerm, chain_perms: Map<RwLockProcessPtr, LockPerm>, pagetable: RwLockPageTableRoot,
    iommu_table: Option<RwLockPageTableRoot>, pagetable_perm: LockPerm, iommu_perm: Option<LockPerm>,
) -> bool {
    let cpu = k.cpu_arr.spec_index(cpu_id).view().view().view();
    let target = k.prc_mp.spec_index(chain[chain.len() - 1]);
    &&& 0 < chain.len()
    &&& kill_chain_state(k, lctx, cpu_id, process_ptr, thread_ptr, chain, stage, cpu_perm, process_perm, thread_perm, chain_perms)
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& forall|c: CpuId| #![trigger lctx.cpu_lock_map().dom().contains(c)] lctx.cpu_lock_map().dom().contains(c) <==> c == cpu_id
    &&& typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write)
    &&& cpu.state is Running
    &&& cpu.current_process == Some(process_ptr)
    &&& cpu.current_thread == Some(thread_ptr)
    &&& typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write)
    &&& forall|t: RwLockThreadPtr| #![trigger lctx.thread_lock_map().dom().contains(t)] lctx.thread_lock_map().dom().contains(t) <==> t == thread_ptr
    &&& typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write)
    &&& lctx.page_lock_map().dom().is_empty()
    &&& lctx.pcid_needflush_lock_map().dom().is_empty()
    &&& lctx.cpu_offline_flag_lock_map().dom().is_empty()
    &&& lctx.container_lock_map().dom().is_empty()
    &&& lctx.endpoint_lock_map().dom().is_empty()
    &&& lctx.scheduler_lock_map().dom().is_empty()
    &&& lctx.pcid_allocator_lock_map().dom().is_empty()
    &&& lctx.cpu_set_lock_map().dom().is_empty()
    &&& lctx.iommu_root_table_lock_map().dom().is_empty()
    &&& lctx.allocator_quota_4k_lock_map().dom().is_empty()
    &&& lctx.allocator_cache_4k_lock_map().dom().is_empty()
    &&& lctx.allocator_global_pool_4k_lock_map().dom().is_empty()
    &&& lctx.allocator_quota_2m_lock_map().dom().is_empty()
    &&& lctx.allocator_cache_2m_lock_map().dom().is_empty()
    &&& lctx.allocator_global_pool_2m_lock_map().dom().is_empty()
    &&& lctx.allocator_quota_1g_lock_map().dom().is_empty()
    &&& lctx.allocator_cache_1g_lock_map().dom().is_empty()
    &&& lctx.allocator_global_pool_1g_lock_map().dom().is_empty()
    &&& lctx.pagetable_lock_map().dom() =~= set![pagetable]
    &&& typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write)
    &&& lctx.iommu_table_lock_map().dom() =~= match iommu_table { Some(it) => set![it], None => Set::empty() }
    &&& iommu_table is Some ==> typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), iommu_table->Some_0, TypedLockMode::Write)
    &&& !target.view().zombie
    &&& target.view().pagetable == pagetable
    &&& target.view().iommu_table == iommu_table
    &&& target.view().children.view().len() == 0
    &&& target.view().owned_threads.view().len() == 0
    &&& target.view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty()
    &&& k.pt_mp.dom().contains(pagetable)
    &&& k.pt_mp.spec_index(pagetable).view().proc_ptr == chain[chain.len() - 1]
    &&& pagetable_perm.state() is WriteLock
    &&& pagetable_perm.thread_id() == lctx.thread_id()
    &&& pagetable_perm.lock_id() == k.pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id
    &&& (iommu_perm is Some) == (iommu_table is Some)
    &&& iommu_table is Some ==> {
        let it = k.it_mp.spec_index(iommu_table->Some_0);
        &&& k.it_mp.dom().contains(iommu_table->Some_0)
        &&& it.view().proc_ptr == chain[chain.len() - 1]
        &&& iommu_perm->Some_0.state() is WriteLock
        &&& iommu_perm->Some_0.thread_id() == lctx.thread_id()
        &&& iommu_perm->Some_0.lock_id() == it.locking_thread()->Write_lock_id
    }
}

/// Reassigning the PCI functions of the empty target `target` to the killer's process `owner` under the root-table lock:
/// every function `target` owns moves to `owner` detached and with its IOTLB domain emptied, and `owner`'s reverse set
/// absorbs `target`'s. Lock owners, lock ids, and every other object stay.
#[verifier::opaque]
pub open spec fn kill_reassign_transition(pre: KernelK, post: KernelK, target: RwLockProcessPtr, owner: RwLockProcessPtr) -> bool {
    let empty_tlb = SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() };
    &&& post == (KernelK { irt: post.irt, iommu_tlb: post.iommu_tlb, prc_mp: post.prc_mp, ..pre })
    &&& pre.prc_mp.dom().contains(target)
    &&& pre.prc_mp.dom().contains(owner)
    &&& target != owner
    &&& post.irt.locking_thread() == pre.irt.locking_thread()
    &&& post.irt.view().table_base() == pre.irt.view().table_base()
    &&& forall|b: usize, d: usize, f: usize| #![trigger post.irt.view().spec_index_owner(b, d, f)] #![trigger post.irt.view().spec_index_iommu_root(b, d, f)] pci_bdf_valid(b, d, f) ==> {
        &&& post.irt.view().spec_index_owner(b, d, f) == if pre.irt.view().spec_index_owner(b, d, f) == target { owner } else { pre.irt.view().spec_index_owner(b, d, f) }
        &&& post.irt.view().spec_index_iommu_root(b, d, f) == if pre.irt.view().spec_index_owner(b, d, f) == target { None } else { pre.irt.view().spec_index_iommu_root(b, d, f) }
    }
    &&& post.iommu_tlb.view().dom() == pre.iommu_tlb.view().dom()
    &&& forall|b: usize, d: usize, f: usize| #![trigger post.iommu_tlb.view()[pci_bdf_did(b, d, f)]] pci_bdf_valid(b, d, f)
        ==> post.iommu_tlb.view()[pci_bdf_did(b, d, f)] == if pre.irt.view().spec_index_owner(b, d, f) == target { empty_tlb } else { pre.iommu_tlb.view()[pci_bdf_did(b, d, f)] }
    &&& post.prc_mp.dom() == pre.prc_mp.dom()
    &&& forall|p: RwLockProcessPtr| #![trigger pre.prc_mp.spec_index(p)] #![trigger post.prc_mp.spec_index(p)] pre.prc_mp.dom().contains(p) ==> {
        let before = pre.prc_mp.spec_index(p);
        let after = post.prc_mp.spec_index(p);
        let pci = before.view_ghost().owned_pci_functions.view();
        &&& after.is_init() == before.is_init()
        &&& after.view() == before.view()
        &&& after.view_rodata() == before.view_rodata()
        &&& after.locking_thread() == before.locking_thread()
        &&& after.being_killed() == before.being_killed()
        &&& after.killer_info() == before.killer_info()
        &&& after.view_ghost() == (ProcessGhost { owned_pci_functions: after.view_ghost().owned_pci_functions, ..before.view_ghost() })
        &&& after.view_ghost().owned_pci_functions.view() == if p == target { Set::empty() } else if p == owner { pci.union(pre.prc_mp.spec_index(target).view_ghost().owned_pci_functions.view()) } else { pci }
    }
}

/// Returning the whole `size` quota of the target `process_ptr` to the write-held `size` allocator `allocator_ptr` of its
/// container, which has room for it: the target drops its `size` quota, which the allocator regains. Lock owners, lock
/// ids, and every other object stay.
#[verifier::opaque]
pub open spec fn kill_quota_transition(pre: KernelK, post: KernelK, process_ptr: RwLockProcessPtr, allocator_ptr: RwLockPageAllocatorPtr, size: PageSize) -> bool {
    let process = pre.prc_mp.spec_index(process_ptr);
    let pre_allocators = match size { PageSize::SZ4k => pre.allc_4k_mp, PageSize::SZ2m => pre.allc_2m_mp, PageSize::SZ1g => pre.allc_1g_mp };
    let post_allocators = match size { PageSize::SZ4k => post.allc_4k_mp, PageSize::SZ2m => post.allc_2m_mp, PageSize::SZ1g => post.allc_1g_mp };
    let allocator = pre_allocators.spec_index(allocator_ptr);
    let returned = match size { PageSize::SZ4k => process.view().quota_4k, PageSize::SZ2m => process.view().quota_2m, PageSize::SZ1g => process.view().quota_1g };
    let container = pre.ctn_mp.spec_index(process.view_rodata().view().owning_container).view_rodata().view();
    &&& pre.prc_mp.dom().contains(process_ptr)
    &&& allocator_ptr == match size { PageSize::SZ4k => container.allocator_ptr_4k, PageSize::SZ2m => container.allocator_ptr_2m, PageSize::SZ1g => container.allocator_ptr_1g }
    &&& allocator.quota.view().value + returned <= usize::MAX
    &&& post == (KernelK { prc_mp: post.prc_mp, allc_4k_mp: post.allc_4k_mp, allc_2m_mp: post.allc_2m_mp, allc_1g_mp: post.allc_1g_mp, ..pre })
    &&& !(size is SZ4k) ==> post.allc_4k_mp == pre.allc_4k_mp
    &&& !(size is SZ2m) ==> post.allc_2m_mp == pre.allc_2m_mp
    &&& !(size is SZ1g) ==> post.allc_1g_mp == pre.allc_1g_mp
    &&& post_allocators.perms_wf()
    &&& post_allocators.unchanged_except(&pre_allocators, allocator_ptr)
    &&& post_allocators.spec_index(allocator_ptr).quota.view() == (AllocatorQuota { value: (allocator.quota.view().value + returned) as usize, ..allocator.quota.view() })
    &&& post_allocators.spec_index(allocator_ptr).quota.is_init()
    &&& post_allocators.spec_index(allocator_ptr).quota.view_rodata() == allocator.quota.view_rodata()
    &&& post_allocators.spec_index(allocator_ptr).quota.view_ghost() == allocator.quota.view_ghost()
    &&& post_allocators.spec_index(allocator_ptr).quota.locking_thread() == allocator.quota.locking_thread()
    &&& post_allocators.spec_index(allocator_ptr).quota.being_killed() == allocator.quota.being_killed()
    &&& post_allocators.spec_index(allocator_ptr) == (PageAllocator { quota: post_allocators.spec_index(allocator_ptr).quota, ..allocator })
    &&& post.prc_mp.perms_wf()
    &&& post.prc_mp.unchanged_except(&pre.prc_mp, process_ptr)
    &&& post.prc_mp.spec_index(process_ptr).is_init()
    &&& post.prc_mp.spec_index(process_ptr).view() == match size {
        PageSize::SZ4k => Process { quota_4k: 0, ..process.view() },
        PageSize::SZ2m => Process { quota_2m: 0, ..process.view() },
        PageSize::SZ1g => Process { quota_1g: 0, ..process.view() },
    }
    &&& post.prc_mp.spec_index(process_ptr).view_rodata() == process.view_rodata()
    &&& post.prc_mp.spec_index(process_ptr).view_ghost() == process.view_ghost()
    &&& post.prc_mp.spec_index(process_ptr).locking_thread() == process.locking_thread()
    &&& post.prc_mp.spec_index(process_ptr).being_killed() == process.being_killed()
    &&& post.prc_mp.spec_index(process_ptr).killer_info() == process.killer_info()
}

/// Marking the reclaimed target `process_ptr`, whose tables map nothing and which owns no thread, as having emptied its
/// tables while it and its tables are still write-held. Lock owners, lock ids, and every other object stay.
#[verifier::opaque]
pub open spec fn kill_tables_emptied_transition(pre: KernelK, post: KernelK, process_ptr: RwLockProcessPtr) -> bool {
    let process = pre.prc_mp.spec_index(process_ptr);
    &&& post == (KernelK { prc_mp: post.prc_mp, ..pre })
    &&& pre.prc_mp.dom().contains(process_ptr)
    &&& !process.view().zombie
    &&& process.view().owned_threads.view().len() == 0
    &&& pre.pt_mp.spec_index(process.view().pagetable).view().mapping_4k().dom() =~= Set::<VAddr>::empty()
    &&& process.view().iommu_table is Some ==> pre.it_mp.spec_index(process.view().iommu_table->Some_0).view().mapping_4k().dom() =~= Set::<VAddr>::empty()
    &&& post.prc_mp.dom() == pre.prc_mp.dom()
    &&& post.prc_mp.perms_wf()
    &&& post.prc_mp.unchanged_except(&pre.prc_mp, process_ptr)
    &&& post.prc_mp.spec_index(process_ptr).is_init()
    &&& post.prc_mp.spec_index(process_ptr).view() == (Process { state: Ghost(ProcessState::TablesEmptied), ..process.view() })
    &&& post.prc_mp.spec_index(process_ptr).view_rodata() == process.view_rodata()
    &&& post.prc_mp.spec_index(process_ptr).view_ghost() == process.view_ghost()
    &&& post.prc_mp.spec_index(process_ptr).locking_thread() == process.locking_thread()
    &&& post.prc_mp.spec_index(process_ptr).being_killed() == process.being_killed()
    &&& post.prc_mp.spec_index(process_ptr).killer_info() == process.killer_info()
}

/// Making the reclaimed target `process_ptr` a zombie: it keeps every field but becomes a zombie, and the write-held PCID
/// allocator `pcid_allocator_ptr` of its container releases its PCID. Lock owners, lock ids, and every other object stay.
#[verifier::opaque]
pub open spec fn kill_zombify_transition(pre: KernelK, post: KernelK, process_ptr: RwLockProcessPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr) -> bool {
    let process = pre.prc_mp.spec_index(process_ptr);
    let pcid = process.view().pcid;
    let pre_allocator = pre.pcid_allc_mp.spec_index(pcid_allocator_ptr);
    let post_allocator = post.pcid_allc_mp.spec_index(pcid_allocator_ptr);
    &&& post == (KernelK { prc_mp: post.prc_mp, pcid_allc_mp: post.pcid_allc_mp, ..pre })
    &&& pre.prc_mp.dom().contains(process_ptr)
    &&& process.view().state.view() is TablesEmptied
    &&& process.view().owned_threads.view().len() == 0
    &&& process.view().quota_4k == 0
    &&& process.view().quota_2m == 0
    &&& process.view().quota_1g == 0
    &&& pcid_allocator_ptr == pre.ctn_mp.spec_index(process.view_rodata().view().owning_container).view_rodata().view().pcid_allocator
    &&& post.prc_mp.dom() == pre.prc_mp.dom()
    &&& post.prc_mp.perms_wf()
    &&& post.prc_mp.unchanged_except(&pre.prc_mp, process_ptr)
    &&& post.prc_mp.spec_index(process_ptr).is_init()
    &&& post.prc_mp.spec_index(process_ptr).view() == (Process { zombie: true, state: Ghost(ProcessState::Zombie), ..process.view() })
    &&& post.prc_mp.spec_index(process_ptr).view_rodata() == process.view_rodata()
    &&& post.prc_mp.spec_index(process_ptr).view_ghost() == process.view_ghost()
    &&& post.prc_mp.spec_index(process_ptr).locking_thread() == process.locking_thread()
    &&& post.prc_mp.spec_index(process_ptr).being_killed() == process.being_killed()
    &&& post.prc_mp.spec_index(process_ptr).killer_info() == process.killer_info()
    &&& pre.pcid_allc_mp.dom().contains(pcid_allocator_ptr)
    &&& post.pcid_allc_mp.dom() == pre.pcid_allc_mp.dom()
    &&& post.pcid_allc_mp.unchanged_except(&pre.pcid_allc_mp, pcid_allocator_ptr)
    &&& pcid_valid(pcid)
    &&& pcid != KERNEL_DEFAULT_PCID
    &&& pre_allocator.view().id_to_proc.view().spec_index(pcid as int).contains(process_ptr)
    &&& post_allocator.view().release_ensures(&pre_allocator.view(), process_ptr, pcid)
    &&& post_allocator.locking_thread() == pre_allocator.locking_thread()
    &&& post_allocator.being_killed() == pre_allocator.being_killed()
}
} // verus!
