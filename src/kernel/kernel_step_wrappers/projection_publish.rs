use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal, assert_sets_equal};
use crate::*;
#[cfg(verus_keep_ghost)]
use crate::kernel::implementation::create_thread_from_staged_page::kernel_u_new_thread_changed;

verus! {
pub proof fn kernel_process_published_and_parent_unlocked_implies_u_step(
    before: &KernelK, after: &KernelK, lctx: &LocalContext, parent: RwLockProcessPtr, child: RwLockProcessPtr, thread: RwLockThreadPtr, container: RwLockContainerPtr,
    table: RwLockPageTableRoot, iommu: Option<RwLockPageTableRoot>, pcid_allocator: RwLockPcidAllocatorPtr, pcid: Pcid, progress: Option<SyscallProgress>,
)
    requires
        before.inv(),
        typed_lock_maps_aligned(after, lctx),
        *after == (KernelK { pg_arr: after.pg_arr, prc_mp: after.prc_mp, thr_mp: after.thr_mp, ctn_mp: after.ctn_mp,
            pt_mp: after.pt_mp, pt_lower: after.pt_lower, it_mp: after.it_mp, pcid_allc_mp: after.pcid_allc_mp, ..*before }),
        before.prc_mp.dom().contains(parent),
        !before.prc_mp.dom().contains(child),
        after.prc_mp.dom() == before.prc_mp.dom().insert(child),
        forall|p: RwLockProcessPtr| #![trigger after.prc_mp.spec_index(p)] before.prc_mp.dom().contains(p) ==> {
            &&& after.prc_mp.spec_index(p).view_rodata() == before.prc_mp.spec_index(p).view_rodata()
            &&& after.prc_mp.spec_index(p).view_ghost().uppertree_seq == before.prc_mp.spec_index(p).view_ghost().uppertree_seq
            &&& after.prc_mp.spec_index(p).view_ghost().owned_pci_functions == before.prc_mp.spec_index(p).view_ghost().owned_pci_functions
            &&& after.prc_mp.spec_index(p).view_ghost().subtree_set.view() == if before.prc_mp.spec_index(parent).view_ghost().uppertree_seq.view().push(parent).contains(p) {
                before.prc_mp.spec_index(p).view_ghost().subtree_set.view().insert(child)
            } else { before.prc_mp.spec_index(p).view_ghost().subtree_set.view() }
            &&& after.prc_mp.spec_index(p).view() == (Process { children: after.prc_mp.spec_index(p).view().children, ..before.prc_mp.spec_index(p).view() })
            &&& after.prc_mp.spec_index(p).view().children.view() == if p == parent { before.prc_mp.spec_index(p).view().children.view().push(child) } else { before.prc_mp.spec_index(p).view().children.view() }
            &&& after.prc_mp.spec_index(p).being_killed() == before.prc_mp.spec_index(p).being_killed()
            &&& if p == parent { after.prc_mp.spec_index(p).locking_thread() is None } else { after.prc_mp.spec_index(p).locking_thread() == before.prc_mp.spec_index(p).locking_thread() }
        },
        typed_lock_map_contains_mode(lctx.process_lock_map(), child, TypedLockMode::Write),
        !after.prc_mp.spec_index(child).being_killed(),
        !after.prc_mp.spec_index(child).view().zombie,
        after.prc_mp.spec_index(child).view().pagetable == table,
        after.prc_mp.spec_index(child).view().iommu_table == iommu,
        after.prc_mp.spec_index(child).view_ghost().owned_pci_functions.view().is_empty(),
        after.prc_mp.spec_index(child).view().quota_4k == 0,
        after.prc_mp.spec_index(child).view().quota_2m == 0,
        after.prc_mp.spec_index(child).view().quota_1g == 0,
        after.prc_mp.spec_index(child).view_rodata().view().parent == Some(parent),
        after.prc_mp.spec_index(child).view_rodata().view().owning_container == container,
        after.prc_mp.spec_index(child).view_rodata().view().depth == before.prc_mp.spec_index(parent).view_rodata().view().depth + 1,
        after.prc_mp.spec_index(child).view().children.view() == Seq::<RwLockProcessPtr>::empty(),
        after.prc_mp.spec_index(child).view().owned_threads.view() == Seq::<RwLockThreadPtr>::empty(),
        after.prc_mp.spec_index(child).view_ghost().uppertree_seq.view() == before.prc_mp.spec_index(parent).view_ghost().uppertree_seq.view().push(parent),
        after.prc_mp.spec_index(child).view_ghost().subtree_set.view().is_empty(),
        before.thr_mp.spec_index(thread).view().quota_4k >= if iommu is Some { 5usize } else { 3usize },
        after.thr_mp.unchanged_except(&before.thr_mp, thread),
        kernel_thread_quota_4k_changed(before, after, thread, if iommu is Some { -5 } else { -3 }),
        after.thr_mp.spec_index(thread).view().syscall_progress.view() == progress,
        after.thr_mp.spec_index(thread).locking_thread() == before.thr_mp.spec_index(thread).locking_thread(),
        after.ctn_mp.unchanged_except(&before.ctn_mp, container),
        after.ctn_mp.spec_index(container).view_rodata() == before.ctn_mp.spec_index(container).view_rodata(),
        after.ctn_mp.spec_index(container).view_ghost() == (ContainerGhost { owned_processes: after.ctn_mp.spec_index(container).view_ghost().owned_processes, ..before.ctn_mp.spec_index(container).view_ghost() }),
        after.ctn_mp.spec_index(container).being_killed() == before.ctn_mp.spec_index(container).being_killed(),
        after.ctn_mp.spec_index(container).locking_thread() == before.ctn_mp.spec_index(container).locking_thread(),
        after.ctn_mp.spec_index(container).lock_process_owner_u() == before.ctn_mp.spec_index(container).lock_process_owner_u(),
        after.ctn_mp.spec_index(container).view() == before.ctn_mp.spec_index(container).view(),
        after.ctn_mp.spec_index(container).view_ghost().owned_processes.view() == before.ctn_mp.spec_index(container).view_ghost().owned_processes.view().insert(child),
        before.ctn_mp.spec_index(container).view_rodata().view().pcid_allocator == pcid_allocator,
        after.pcid_allc_mp.unchanged_except(&before.pcid_allc_mp, pcid_allocator),
        PcidAllocator::free_pcids(before.pcid_allc_mp.spec_index(pcid_allocator).view().ref_counters.view()).contains(pcid),
        after.pcid_allc_mp.spec_index(pcid_allocator).view().alloc_ensures(&before.pcid_allc_mp.spec_index(pcid_allocator).view(), child, pcid),
        after.pt_mp.dom() == before.pt_mp.dom().insert(table),
        forall|p: RwLockPageTableRoot| #![trigger after.pt_mp.spec_index(p)] before.pt_mp.dom().contains(p) ==> after.pt_mp.spec_index(p) == before.pt_mp.spec_index(p) && after.pt_lower.view().spec_index(p) == before.pt_lower.view().spec_index(p),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), table, TypedLockMode::Write),
        pagetable_c(after.pt_mp, after.pt_lower.view(), table).is_empty(),
        iommu is None ==> after.it_mp == before.it_mp,
        iommu matches Some(t) ==> {
            &&& after.it_mp.dom() == before.it_mp.dom().insert(t)
            &&& forall|p: RwLockPageTableRoot| #![trigger after.it_mp.spec_index(p)] before.it_mp.dom().contains(p) ==> after.it_mp.spec_index(p) == before.it_mp.spec_index(p)
            &&& typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), t, TypedLockMode::Write)
            &&& after.it_mp.spec_index(t).view().is_empty()
            &&& after.it_mp.spec_index(t).view().did is None
        },
    ensures
        forall|c: CpuId| #![trigger kernel_k_to_kernel_u(*before).cpu_array[c as int]] index_valid(NUM_CPUS, c) ==> kernel_k_to_kernel_u(*before).cpu_array[c as int] == (CpuU {
            lock_state: before.cpu_arr.spec_index(c).value.lock_state_u(), owning_container: before.cpu_arr.spec_index(c).value.view().view().owning_container,
            state: before.cpu_arr.spec_index(c).value.view().view().state, current_process: before.cpu_arr.spec_index(c).value.view().view().current_process,
            current_thread: before.cpu_arr.spec_index(c).value.view().view().current_thread, killed: before.cpu_arr.spec_index(c).value.being_killed(),
            op: before.cpu_op.view().view()[c as int],
        }),
        ({
            let entry = before.thr_mp.spec_index(thread);
            let t = entry.view();
            kernel_k_to_kernel_u(*before).thread_map[thread] == (ThreadU {
                lock_state: entry.lock_state_u(), state: t.state, caller: t.caller, callee: t.callee, owning_container: t.owning_container, owning_proc: t.owning_proc,
                last_cpu: t.last_cpu, quota_4k: t.quota_4k, quota_2m: t.quota_2m, quota_1g: t.quota_1g, endpoint_descriptors: t.endpoint_descriptors.view(),
                blocking_endpoint_ptr: t.blocking_endpoint_ptr, ipc_payload: t.ipc_payload, error_code: t.error_code,
                trap_frame: if t.trap_frame.is_some() { Some(*t.trap_frame.get_some_0()) } else { None }, syscall_progress: t.syscall_progress.view(), killed: entry.being_killed(),
            })
        }),
        ({
            let pre = kernel_k_to_kernel_u(*before);
            let post = kernel_k_to_kernel_u(*after);
            let ancestors = pre.process_map[parent].uppertree_seq.push(parent);
            let empty_table = PageTableU { lock_state: LockStateU::WriteLocked, did: None, mapping_4k: Map::empty(), mapping_2m: Map::empty(), mapping_1g: Map::empty(), pagetable_window_locks: Map::empty() };
            let cost: usize = if (iommu is Some) { 5 } else { 3 };
            &&& pre.process_map.dom().contains(parent)
            &&& !pre.process_map.dom().contains(child)
            &&& pre.thread_map.dom().contains(thread)
            &&& pre.thread_map[thread].syscall_progress == before.thr_mp.spec_index(thread).view().syscall_progress.view()
            &&& pre.container_map.dom().contains(container)
            &&& pre.thread_map[thread].quota_4k >= cost
            &&& post.container_map[container].free_pcids.subset_of(pre.container_map[container].free_pcids)
            &&& pre.container_map[container].free_pcids.difference(post.container_map[container].free_pcids).len() == 1
            &&& post.process_map.dom() == pre.process_map.dom().insert(child)
            &&& forall|p: RwLockProcessPtr| #![trigger post.process_map[p]] pre.process_map.dom().contains(p) ==> post.process_map[p] == (ProcessU {
                lock_state: if p == parent { LockStateU::Unlocked } else { pre.process_map[p].lock_state },
                children: if p == parent { pre.process_map[p].children.push(child) } else { pre.process_map[p].children },
                subtree_set: if ancestors.contains(p) { pre.process_map[p].subtree_set.insert(child) } else { pre.process_map[p].subtree_set },
                ..pre.process_map[p]
            })
            &&& post.process_map[child] == (ProcessU {
                lock_state: LockStateU::WriteLocked, zombie: false, pagetable: Some(empty_table),
                iommu_table: if (iommu is Some) { Some(empty_table) } else { None }, pcid: post.process_map[child].pcid, owning_container: container, owned_pci_functions: Set::empty(),
                quota_4k: 0, quota_2m: 0, quota_1g: 0, parent: Some(parent), children: Seq::empty(),
                depth: (pre.process_map[parent].depth + 1) as usize, uppertree_seq: ancestors,
                subtree_set: Set::empty(), owned_threads: Seq::empty(), killed: false,
            })
            &&& post == (KernelU {
                process_map: post.process_map,
                container_map: pre.container_map.insert(container, ContainerU {
                    owned_processes: pre.container_map[container].owned_processes.insert(child),
                    free_pcids: post.container_map[container].free_pcids, ..pre.container_map[container]
                }),
                thread_map: pre.thread_map.insert(thread, ThreadU { quota_4k: (pre.thread_map[thread].quota_4k - cost) as usize, syscall_progress: progress, ..pre.thread_map[thread] }),
                ..pre
            })
        }),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after); kernel_u_cpu_array_projection(before); kernel_thread_projection_at(before, thread);
    after.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), child);
    after.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), table);
    if let Some(t) = iommu { after.it_mp.typed_lock_map_aligned_write_at(lctx.iommu_table_lock_map(), lctx.thread_id(), t); }
    kernel_cpu_array_unchanged_implies_u_cpu_array(before, after);
    kernel_endpoint_map_unchanged_implies_u_endpoint_map(before, after);
    kernel_process_published_and_parent_unlocked_implies_u_thread_map(before, after, thread, iommu, progress);
    kernel_process_published_and_parent_unlocked_implies_u_container_map(before, after, child, container, pcid_allocator, pcid);
    kernel_process_published_and_parent_unlocked_implies_u_process_map(before, after, parent, child, container, table, iommu);
}

/// Publishing a process projects to the thread map with only `thread` charged the publication cost and given `progress`.
proof fn kernel_process_published_and_parent_unlocked_implies_u_thread_map(
    before: &KernelK, after: &KernelK, thread: RwLockThreadPtr, iommu: Option<RwLockPageTableRoot>, progress: Option<SyscallProgress>,
)
    requires
        before.thr_mp.spec_index(thread).view().quota_4k >= if iommu is Some { 5usize } else { 3usize },
        after.thr_mp.unchanged_except(&before.thr_mp, thread),
        kernel_thread_quota_4k_changed(before, after, thread, if iommu is Some { -5 } else { -3 }),
        after.thr_mp.spec_index(thread).view().syscall_progress.view() == progress,
        after.thr_mp.spec_index(thread).locking_thread() == before.thr_mp.spec_index(thread).locking_thread(),
    ensures
        ({
            let pre = kernel_k_to_kernel_u(*before);
            let cost: usize = if (iommu is Some) { 5 } else { 3 };
            kernel_k_to_kernel_u(*after).thread_map == pre.thread_map.insert(thread, ThreadU { quota_4k: (pre.thread_map[thread].quota_4k - cost) as usize, syscall_progress: progress, ..pre.thread_map[thread] })
        }),
{
    reveal(kernel_thread_quota_4k_changed); kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    let cost: usize = if iommu is Some { 5 } else { 3 };
    assert_maps_equal!(post.thread_map, pre.thread_map.insert(thread, ThreadU {
        quota_4k: (pre.thread_map[thread].quota_4k - cost) as usize, syscall_progress: progress, ..pre.thread_map[thread]
    }), t => { if before.thr_mp.dom().contains(t) { kernel_thread_projection_at(before, t); kernel_thread_projection_at(after, t); } });
}

/// Publishing a process projects to the container map with only `container` owning `child` and giving up the pcid.
proof fn kernel_process_published_and_parent_unlocked_implies_u_container_map(
    before: &KernelK, after: &KernelK, child: RwLockProcessPtr, container: RwLockContainerPtr, pcid_allocator: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        container_pcid_allocator_wf(before.ctn_mp, before.pcid_allc_mp),
        pcid_allocator_perms_wf(before.pcid_allc_mp),
        *after == (KernelK { pg_arr: after.pg_arr, prc_mp: after.prc_mp, thr_mp: after.thr_mp, ctn_mp: after.ctn_mp,
            pt_mp: after.pt_mp, pt_lower: after.pt_lower, it_mp: after.it_mp, pcid_allc_mp: after.pcid_allc_mp, ..*before }),
        after.ctn_mp.unchanged_except(&before.ctn_mp, container),
        after.ctn_mp.spec_index(container).view_rodata() == before.ctn_mp.spec_index(container).view_rodata(),
        after.ctn_mp.spec_index(container).view_ghost() == (ContainerGhost { owned_processes: after.ctn_mp.spec_index(container).view_ghost().owned_processes, ..before.ctn_mp.spec_index(container).view_ghost() }),
        after.ctn_mp.spec_index(container).being_killed() == before.ctn_mp.spec_index(container).being_killed(),
        after.ctn_mp.spec_index(container).locking_thread() == before.ctn_mp.spec_index(container).locking_thread(),
        after.ctn_mp.spec_index(container).lock_process_owner_u() == before.ctn_mp.spec_index(container).lock_process_owner_u(),
        after.ctn_mp.spec_index(container).view() == before.ctn_mp.spec_index(container).view(),
        after.ctn_mp.spec_index(container).view_ghost().owned_processes.view() == before.ctn_mp.spec_index(container).view_ghost().owned_processes.view().insert(child),
        before.ctn_mp.spec_index(container).view_rodata().view().pcid_allocator == pcid_allocator,
        after.pcid_allc_mp.unchanged_except(&before.pcid_allc_mp, pcid_allocator),
        PcidAllocator::free_pcids(before.pcid_allc_mp.spec_index(pcid_allocator).view().ref_counters.view()).contains(pcid),
        after.pcid_allc_mp.spec_index(pcid_allocator).view().alloc_ensures(&before.pcid_allc_mp.spec_index(pcid_allocator).view(), child, pcid),
    ensures
        ({
            let pre = kernel_k_to_kernel_u(*before);
            let post = kernel_k_to_kernel_u(*after);
            &&& post.container_map[container].free_pcids.subset_of(pre.container_map[container].free_pcids)
            &&& pre.container_map[container].free_pcids.difference(post.container_map[container].free_pcids).len() == 1
            &&& post.container_map == pre.container_map.insert(container, ContainerU {
                owned_processes: pre.container_map[container].owned_processes.insert(child), free_pcids: post.container_map[container].free_pcids, ..pre.container_map[container]
            })
        }),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after); kernel_container_projection_at(before, container); kernel_container_projection_at(after, container);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    assert_maps_equal!(post.container_map, pre.container_map.insert(container, ContainerU {
        owned_processes: pre.container_map[container].owned_processes.insert(child), free_pcids: post.container_map[container].free_pcids, ..pre.container_map[container]
    }), c => { if before.ctn_mp.dom().contains(c) { kernel_container_projection_at(before, c); kernel_container_projection_at(after, c); reveal(container_pcid_allocator_wf); } });
    assert(post.container_map[container].free_pcids =~= pre.container_map[container].free_pcids.remove(pcid)) by { pcid_allocator_perms_wf_at(before.pcid_allc_mp, pcid_allocator); };
    assert_sets_equal!(pre.container_map[container].free_pcids.difference(post.container_map[container].free_pcids), set![pcid]);
}

/// Publishing a process projects to the process map with `child` added write-locked under `parent`, `parent` unlocked,
/// and `child` recorded in every ancestor's subtree.
proof fn kernel_process_published_and_parent_unlocked_implies_u_process_map(
    before: &KernelK, after: &KernelK, parent: RwLockProcessPtr, child: RwLockProcessPtr, container: RwLockContainerPtr, table: RwLockPageTableRoot,
    iommu: Option<RwLockPageTableRoot>,
)
    requires
        process_pagetable_match(before.prc_mp, before.pt_mp),
        process_iommu_table_match(before.prc_mp, before.it_mp),
        before.prc_mp.dom().contains(parent),
        !before.prc_mp.dom().contains(child),
        after.prc_mp.dom() == before.prc_mp.dom().insert(child),
        forall|p: RwLockProcessPtr| #![trigger after.prc_mp.spec_index(p)] before.prc_mp.dom().contains(p) ==> {
            &&& after.prc_mp.spec_index(p).view_rodata() == before.prc_mp.spec_index(p).view_rodata()
            &&& after.prc_mp.spec_index(p).view_ghost().uppertree_seq == before.prc_mp.spec_index(p).view_ghost().uppertree_seq
            &&& after.prc_mp.spec_index(p).view_ghost().owned_pci_functions == before.prc_mp.spec_index(p).view_ghost().owned_pci_functions
            &&& after.prc_mp.spec_index(p).view_ghost().subtree_set.view() == if before.prc_mp.spec_index(parent).view_ghost().uppertree_seq.view().push(parent).contains(p) {
                before.prc_mp.spec_index(p).view_ghost().subtree_set.view().insert(child)
            } else { before.prc_mp.spec_index(p).view_ghost().subtree_set.view() }
            &&& after.prc_mp.spec_index(p).view() == (Process { children: after.prc_mp.spec_index(p).view().children, ..before.prc_mp.spec_index(p).view() })
            &&& after.prc_mp.spec_index(p).view().children.view() == if p == parent { before.prc_mp.spec_index(p).view().children.view().push(child) } else { before.prc_mp.spec_index(p).view().children.view() }
            &&& after.prc_mp.spec_index(p).being_killed() == before.prc_mp.spec_index(p).being_killed()
            &&& if p == parent { after.prc_mp.spec_index(p).locking_thread() is None } else { after.prc_mp.spec_index(p).locking_thread() == before.prc_mp.spec_index(p).locking_thread() }
        },
        after.prc_mp.spec_index(child).locking_thread() is Write,
        !after.prc_mp.spec_index(child).being_killed(),
        !after.prc_mp.spec_index(child).view().zombie,
        after.prc_mp.spec_index(child).view().pagetable == table,
        after.prc_mp.spec_index(child).view().iommu_table == iommu,
        after.prc_mp.spec_index(child).view_ghost().owned_pci_functions.view().is_empty(),
        after.prc_mp.spec_index(child).view().quota_4k == 0,
        after.prc_mp.spec_index(child).view().quota_2m == 0,
        after.prc_mp.spec_index(child).view().quota_1g == 0,
        after.prc_mp.spec_index(child).view_rodata().view().parent == Some(parent),
        after.prc_mp.spec_index(child).view_rodata().view().owning_container == container,
        after.prc_mp.spec_index(child).view_rodata().view().depth == before.prc_mp.spec_index(parent).view_rodata().view().depth + 1,
        after.prc_mp.spec_index(child).view().children.view() == Seq::<RwLockProcessPtr>::empty(),
        after.prc_mp.spec_index(child).view().owned_threads.view() == Seq::<RwLockThreadPtr>::empty(),
        after.prc_mp.spec_index(child).view_ghost().uppertree_seq.view() == before.prc_mp.spec_index(parent).view_ghost().uppertree_seq.view().push(parent),
        after.prc_mp.spec_index(child).view_ghost().subtree_set.view().is_empty(),
        after.pt_mp.dom() == before.pt_mp.dom().insert(table),
        forall|p: RwLockPageTableRoot| #![trigger after.pt_mp.spec_index(p)] before.pt_mp.dom().contains(p) ==> after.pt_mp.spec_index(p) == before.pt_mp.spec_index(p) && after.pt_lower.view().spec_index(p) == before.pt_lower.view().spec_index(p),
        after.pt_mp.spec_index(table).locking_thread() is Write,
        pagetable_c(after.pt_mp, after.pt_lower.view(), table).is_empty(),
        iommu is None ==> after.it_mp == before.it_mp,
        iommu matches Some(t) ==> {
            &&& after.it_mp.dom() == before.it_mp.dom().insert(t)
            &&& forall|p: RwLockPageTableRoot| #![trigger after.it_mp.spec_index(p)] before.it_mp.dom().contains(p) ==> after.it_mp.spec_index(p) == before.it_mp.spec_index(p)
            &&& after.it_mp.spec_index(t).locking_thread() is Write
            &&& after.it_mp.spec_index(t).view().is_empty()
            &&& after.it_mp.spec_index(t).view().did is None
        },
    ensures
        ({
            let pre = kernel_k_to_kernel_u(*before);
            let post = kernel_k_to_kernel_u(*after);
            let ancestors = pre.process_map[parent].uppertree_seq.push(parent);
            let empty_table = PageTableU { lock_state: LockStateU::WriteLocked, did: None, mapping_4k: Map::empty(), mapping_2m: Map::empty(), mapping_1g: Map::empty(), pagetable_window_locks: Map::empty() };
            &&& post.process_map.dom() == pre.process_map.dom().insert(child)
            &&& forall|p: RwLockProcessPtr| #![trigger post.process_map[p]] pre.process_map.dom().contains(p) ==> post.process_map[p] == (ProcessU {
                lock_state: if p == parent { LockStateU::Unlocked } else { pre.process_map[p].lock_state },
                children: if p == parent { pre.process_map[p].children.push(child) } else { pre.process_map[p].children },
                subtree_set: if ancestors.contains(p) { pre.process_map[p].subtree_set.insert(child) } else { pre.process_map[p].subtree_set },
                ..pre.process_map[p]
            })
            &&& post.process_map[child] == (ProcessU {
                lock_state: LockStateU::WriteLocked, zombie: false, pagetable: Some(empty_table),
                iommu_table: if (iommu is Some) { Some(empty_table) } else { None }, pcid: post.process_map[child].pcid, owning_container: container, owned_pci_functions: Set::empty(),
                quota_4k: 0, quota_2m: 0, quota_1g: 0, parent: Some(parent), children: Seq::empty(),
                depth: (pre.process_map[parent].depth + 1) as usize, uppertree_seq: ancestors,
                subtree_set: Set::empty(), owned_threads: Seq::empty(), killed: false,
            })
        }),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after); kernel_process_projection_at(before, parent); kernel_process_projection_at(after, child);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    let ancestors = pre.process_map[parent].uppertree_seq.push(parent);
    assert_maps_equal!(post.process_map, Map::new(pre.process_map.dom(), |p: RwLockProcessPtr| ProcessU {
        lock_state: if p == parent { LockStateU::Unlocked } else { pre.process_map[p].lock_state },
        children: if p == parent { pre.process_map[p].children.push(child) } else { pre.process_map[p].children },
        subtree_set: if ancestors.contains(p) { pre.process_map[p].subtree_set.insert(child) } else { pre.process_map[p].subtree_set }, ..pre.process_map[p]
    }).insert(child, post.process_map[child]), p => {
        if before.prc_mp.dom().contains(p) {
            kernel_process_projection_at(before, p); kernel_process_projection_at(after, p);
            process_pagetable_match_process_at(before.prc_mp, before.pt_mp, p); process_iommu_table_match_process_at(before.prc_mp, before.it_mp, p);
        }
    });
    assert_maps_equal!(post.process_map[child].pagetable->Some_0.mapping_4k, Map::empty(), va => {});
    assert_maps_equal!(post.process_map[child].pagetable->Some_0.mapping_2m, Map::empty(), va => {});
    assert_maps_equal!(post.process_map[child].pagetable->Some_0.mapping_1g, Map::empty(), va => {});
    if iommu is Some {
        assert_maps_equal!(post.process_map[child].iommu_table->Some_0.mapping_4k, Map::empty(), va => {});
        assert_maps_equal!(post.process_map[child].iommu_table->Some_0.mapping_2m, Map::empty(), va => {});
        assert_maps_equal!(post.process_map[child].iommu_table->Some_0.mapping_1g, Map::empty(), va => {});
    }
}

pub proof fn kernel_thread_quota_and_page_owner_changed_implies_u_step(pre: &KernelK, post: &KernelK, lctx: &LocalContext, thread: RwLockThreadPtr, source: RwLockContainerPtr, target: RwLockContainerPtr, page: PagePtr, table: RwLockPageTableRoot)
    requires
        process_pagetable_match(pre.prc_mp, pre.pt_mp),
        pre.thr_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        post.thr_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread, TypedLockMode::Write),
        *post == (KernelK { pg_arr: post.pg_arr, ctn_mp: post.ctn_mp, thr_mp: post.thr_mp, pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..*pre }),
        source != target,
        pre.ctn_mp.dom().contains(source),
        pre.ctn_mp.dom().contains(target),
        pre.ctn_mp.spec_index(source).view().owned_pages.view().contains(page),
        post.ctn_mp.dom() == pre.ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)] pre.ctn_mp.dom().contains(c) ==> {
            &&& post.ctn_mp.spec_index(c).view_rodata() == pre.ctn_mp.spec_index(c).view_rodata()
            &&& post.ctn_mp.spec_index(c).view_ghost() == pre.ctn_mp.spec_index(c).view_ghost()
            &&& post.ctn_mp.spec_index(c).locking_thread() == pre.ctn_mp.spec_index(c).locking_thread()
            &&& post.ctn_mp.spec_index(c).lock_process_owner_u() == pre.ctn_mp.spec_index(c).lock_process_owner_u()
            &&& post.ctn_mp.spec_index(c).being_killed() == pre.ctn_mp.spec_index(c).being_killed()
            &&& post.ctn_mp.spec_index(c).view() == (Container { owned_pages: post.ctn_mp.spec_index(c).view().owned_pages, ..pre.ctn_mp.spec_index(c).view() })
            &&& post.ctn_mp.spec_index(c).view().owned_pages.view() == if c == source { pre.ctn_mp.spec_index(c).view().owned_pages.view().remove(page) }
                else if c == target { pre.ctn_mp.spec_index(c).view().owned_pages.view().insert(page) } else { pre.ctn_mp.spec_index(c).view().owned_pages.view() }
        },
        post.thr_mp.unchanged_except(&pre.thr_mp, thread),
        kernel_thread_quota_4k_changed(pre, post, thread, -1),
        post.thr_mp.spec_index(thread).view().syscall_progress == pre.thr_mp.spec_index(thread).view().syscall_progress,
        post.pt_mp.unchanged_except(&pre.pt_mp, table),
        post.pt_lower.view() == pre.pt_lower.view().insert(table, post.pt_lower.view().spec_index(table)),
        pre.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        post.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), table, TypedLockMode::Write),
        pagetable_c(post.pt_mp, post.pt_lower.view(), table).mapping_4k() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), table).mapping_4k(),
        pagetable_c(post.pt_mp, post.pt_lower.view(), table).mapping_2m() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), table).mapping_2m(),
        pagetable_c(post.pt_mp, post.pt_lower.view(), table).mapping_1g() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), table).mapping_1g(),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let b = kernel_k_to_kernel_u(*post);
            let owner = pre.pt_mp.spec_index(table).view().proc_ptr;
            &&& a.thread_map.dom().contains(thread)
            &&& a.thread_map[thread].lock_state is WriteLocked
            &&& a.thread_map[thread].quota_4k > 0
            &&& a.container_map.dom().contains(source) && a.container_map.dom().contains(target)
            &&& a.container_map[source].owned_pages.difference(b.container_map[source].owned_pages).len() == 1
            &&& b.container_map[source].owned_pages.subset_of(a.container_map[source].owned_pages)
            &&& b.container_map[target].owned_pages == a.container_map[target].owned_pages.union(a.container_map[source].owned_pages.difference(b.container_map[source].owned_pages))
            &&& b == (KernelU {
                thread_map: a.thread_map.insert(thread, ThreadU { quota_4k: (a.thread_map[thread].quota_4k - 1) as usize, ..a.thread_map[thread] }),
                container_map: a.container_map.insert(source, ContainerU { owned_pages: a.container_map[source].owned_pages.remove(page), ..a.container_map[source] })
                    .insert(target, ContainerU { owned_pages: a.container_map[target].owned_pages.insert(page), ..a.container_map[target] }),
                process_map: if a.process_map.dom().contains(owner) && a.process_map[owner].pagetable is Some {
                    a.process_map.insert(owner, ProcessU {
                        pagetable: Some(PageTableU { pagetable_window_locks: pagetable_c(post.pt_mp, post.pt_lower.view(), table).lower.pagetable_window_locks, ..a.process_map[owner].pagetable->Some_0 }),
                        ..a.process_map[owner]
                    })
                } else { a.process_map },
                ..a
            })
        }),
{
    pre.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread);
    kernel_thread_quota_and_page_owner_changed_implies_u_process_map(pre, post, lctx, table);
    kernel_thread_quota_and_page_owner_changed_implies_u_thread_map(pre, post, lctx, thread);
    kernel_thread_quota_and_page_owner_changed_implies_u_container_map(pre, post, source, target, page);
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post); reveal(kernel_thread_quota_4k_changed);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    if pre.thr_mp.dom().contains(thread) { kernel_thread_projection_at(pre, thread); }
    if pre.ctn_mp.dom().contains(source) { kernel_container_projection_at(pre, source); }
    assert_seqs_equal!(b.cpu_array == a.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); } });
    assert_maps_equal!(b.endpoint_map, a.endpoint_map, p => {
        if pre.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(pre, p); } if post.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(post, p); }
    });
    assert_sets_equal!(a.container_map[source].owned_pages.difference(b.container_map[source].owned_pages), set![page]);
    assert_sets_equal!(b.container_map[target].owned_pages, a.container_map[target].owned_pages.union(a.container_map[source].owned_pages.difference(b.container_map[source].owned_pages)));
}

/// Copying one present source entry into an absent target address, with both tables held in either mode, and replacing
/// `progress_thread`'s progress changes only the target pagetable's 4K mapping and that thread's progress.
pub proof fn kernel_4k_mapping_copied_implies_u_step(
    pre: &KernelK, post: &KernelK, lctx: &LocalContext, source: RwLockProcessPtr, target: RwLockProcessPtr,
    source_table: RwLockPageTableRoot, target_table: RwLockPageTableRoot, source_va: VAddr, target_va: VAddr, progress_thread: RwLockThreadPtr,
)
    requires
        process_pagetable_match(pre.prc_mp, pre.pt_mp),
        typed_lock_maps_aligned(pre, lctx),
        source != target,
        pre.prc_mp.dom().contains(source),
        pre.prc_mp.dom().contains(target),
        !pre.prc_mp.spec_index(source).view().zombie,
        !pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(source).view().pagetable == source_table,
        pre.prc_mp.spec_index(target).view().pagetable == target_table,
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), source_table, TypedLockMode::Read) || typed_lock_map_contains_mode(lctx.pagetable_lock_map(), source_table, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), target_table, TypedLockMode::Read) || typed_lock_map_contains_mode(lctx.pagetable_lock_map(), target_table, TypedLockMode::Write),
        pagetable_c(pre.pt_mp, pre.pt_lower.view(), source_table).mapping_4k().dom().contains(source_va),
        pagetable_c(pre.pt_mp, pre.pt_lower.view(), source_table).mapping_4k()[source_va].present,
        !pagetable_c(pre.pt_mp, pre.pt_lower.view(), target_table).mapping_4k().dom().contains(target_va) || !pagetable_c(pre.pt_mp, pre.pt_lower.view(), target_table).mapping_4k()[target_va].present,
        *post == (KernelK { pg_arr: post.pg_arr, pt_mp: post.pt_mp, pt_lower: post.pt_lower, thr_mp: post.thr_mp, ..*pre }),
        pre.thr_mp.dom().contains(progress_thread),
        post.thr_mp.unchanged_except(&pre.thr_mp, progress_thread),
        post.thr_mp.spec_index(progress_thread).view() == (Thread { syscall_progress: post.thr_mp.spec_index(progress_thread).view().syscall_progress, ..pre.thr_mp.spec_index(progress_thread).view() }),
        post.thr_mp.spec_index(progress_thread).locking_thread() == pre.thr_mp.spec_index(progress_thread).locking_thread(),
        post.thr_mp.spec_index(progress_thread).being_killed() == pre.thr_mp.spec_index(progress_thread).being_killed(),
        post.pt_mp.unchanged_except(&pre.pt_mp, target_table),
        post.pt_mp.spec_index(target_table).locking_thread() == pre.pt_mp.spec_index(target_table).locking_thread(),
        post.pt_lower.view() == pre.pt_lower.view().insert(target_table, post.pt_lower.view().spec_index(target_table)),
        pagetable_c(post.pt_mp, post.pt_lower.view(), target_table).lower.pagetable_window_locks == pagetable_c(pre.pt_mp, pre.pt_lower.view(), target_table).lower.pagetable_window_locks,
        pagetable_c(post.pt_mp, post.pt_lower.view(), target_table).mapping_4k() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), target_table).mapping_4k().insert(target_va, pagetable_c(pre.pt_mp, pre.pt_lower.view(), source_table).mapping_4k()[source_va]),
        pagetable_c(post.pt_mp, post.pt_lower.view(), target_table).mapping_2m() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), target_table).mapping_2m(),
        pagetable_c(post.pt_mp, post.pt_lower.view(), target_table).mapping_1g() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), target_table).mapping_1g(),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let b = kernel_k_to_kernel_u(*post);
            &&& a.process_map.dom().contains(source) && a.process_map.dom().contains(target)
            &&& a.process_map[source].pagetable is Some && a.process_map[target].pagetable is Some
            &&& (a.process_map[source].pagetable->Some_0.lock_state is ReadLocked || a.process_map[source].pagetable->Some_0.lock_state is WriteLocked)
            &&& (a.process_map[target].pagetable->Some_0.lock_state is ReadLocked || a.process_map[target].pagetable->Some_0.lock_state is WriteLocked)
            &&& a.process_map[source].pagetable->Some_0.mapping_4k.dom().contains(source_va)
            &&& !a.process_map[target].pagetable->Some_0.mapping_4k.dom().contains(target_va)
            &&& a.thread_map.dom().contains(progress_thread)
            &&& a.thread_map[progress_thread].syscall_progress == pre.thr_mp.spec_index(progress_thread).view().syscall_progress.view()
            &&& b == (KernelU {
                thread_map: a.thread_map.insert(progress_thread, ThreadU {
                    syscall_progress: post.thr_mp.spec_index(progress_thread).view().syscall_progress.view(), ..a.thread_map[progress_thread]
                }),
                process_map: a.process_map.insert(target, ProcessU {
                    pagetable: Some(PageTableU { mapping_4k: a.process_map[target].pagetable->Some_0.mapping_4k.insert(target_va, a.process_map[source].pagetable->Some_0.mapping_4k[source_va]),
                        ..a.process_map[target].pagetable->Some_0 }), ..a.process_map[target]
                }),
                ..a
            })
        }),
{
    if typed_lock_map_contains_mode(lctx.pagetable_lock_map(), source_table, TypedLockMode::Write) { pre.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), source_table); }
    else { pre.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), source_table); }
    if typed_lock_map_contains_mode(lctx.pagetable_lock_map(), target_table, TypedLockMode::Write) { pre.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), target_table); }
    else { pre.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), target_table); }
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    if pre.prc_mp.dom().contains(source) { kernel_process_projection_at(pre, source); }
    if pre.prc_mp.dom().contains(target) { kernel_process_projection_at(pre, target); }
    if pre.thr_mp.dom().contains(progress_thread) { kernel_thread_projection_at(pre, progress_thread); }
    assert_seqs_equal!(b.cpu_array == a.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); } });
    assert_maps_equal!(b.container_map, a.container_map, p => {
        if pre.ctn_mp.dom().contains(p) { kernel_container_projection_at(pre, p); } if post.ctn_mp.dom().contains(p) { kernel_container_projection_at(post, p); }
    });
    assert_maps_equal!(b.thread_map, a.thread_map.insert(progress_thread, ThreadU {
        syscall_progress: post.thr_mp.spec_index(progress_thread).view().syscall_progress.view(), ..a.thread_map[progress_thread]
    }), t => { if pre.thr_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thr_mp.dom().contains(t) { kernel_thread_projection_at(post, t); } });
    assert_maps_equal!(b.endpoint_map, a.endpoint_map, p => {
        if pre.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(pre, p); } if post.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(post, p); }
    });
    assert_maps_equal!(b.process_map, a.process_map.insert(target, ProcessU {
        pagetable: Some(PageTableU { mapping_4k: a.process_map[target].pagetable->Some_0.mapping_4k.insert(target_va, a.process_map[source].pagetable->Some_0.mapping_4k[source_va]),
            ..a.process_map[target].pagetable->Some_0 }), ..a.process_map[target]
    }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); }
        reveal(process_pagetable_match);
        if p == target {
            assert_maps_equal!(b.process_map[target].pagetable->Some_0.mapping_4k,
                a.process_map[target].pagetable->Some_0.mapping_4k.insert(target_va, a.process_map[source].pagetable->Some_0.mapping_4k[source_va]), va => {});
        }
    });
}

/// Project thread publication together with releasing the caller's observable locks; with a released source process,
/// the source's and `process_ptr`'s page tables take their window lock states from `post`.
#[verifier::spinoff_prover]
pub proof fn kernel_new_thread_fields_and_unlocks_implies_u_step(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, new_thread_ptr: RwLockThreadPtr, initial_regs: Registers,
    endpoint_ptr: Option<RwLockEndpointPtr>, release_source_process: Option<RwLockProcessPtr>, staging_progress: Option<SyscallProgress>,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        container_scheduler_wf(post.ctn_mp, post.sched_mp),
        release_source_process matches Some(source) ==> source != process_ptr && pre.prc_mp.dom().contains(source) && !pre.prc_mp.spec_index(source).view().zombie && !pre.prc_mp.spec_index(process_ptr).view().zombie,
        index_valid(NUM_CPUS, cpu_id),
        kernel_new_thread_fields(pre, post, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress),
        pre.thr_mp.spec_index(thread_ptr).view().owning_proc == match release_source_process { Some(source) => source, None => process_ptr },
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)]
            pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).locking_thread() == pre.ctn_mp.spec_index(p).locking_thread() && post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) ==> if p == process_ptr { post.prc_mp.spec_index(p).locking_thread() is None } else { post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread() },
        forall|p: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(p)]
            pre.thr_mp.dom().contains(p) ==> if p == thread_ptr { post.thr_mp.spec_index(p).locking_thread() is None } else { post.thr_mp.spec_index(p).locking_thread() == pre.thr_mp.spec_index(p).locking_thread() },
        forall|p: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(p)]
            pre.ep_mp.dom().contains(p) ==> if endpoint_ptr == Some(p) { post.ep_mp.spec_index(p).locking_thread() is None } else { post.ep_mp.spec_index(p).locking_thread() == pre.ep_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) ==> if release_source_process is Some && (p == pre.prc_mp.spec_index(process_ptr).view().pagetable || p == pre.prc_mp.spec_index(release_source_process->Some_0).view().pagetable)
                { post.pt_mp.spec_index(p).locking_thread() is None }
                else { post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
            pre.it_mp.dom().contains(p) ==> if release_source_process is Some && pre.prc_mp.spec_index(process_ptr).view().iommu_table == Some(p) { post.it_mp.spec_index(p).locking_thread() is None }
                else { post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread() },
        forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> if i == cpu_id { post.cpu_arr.spec_index(i).value.locking_thread() is None } else { post.cpu_arr.spec_index(i).value.locking_thread() == pre.cpu_arr.spec_index(i).value.locking_thread() },
        forall|i: CpuId| #![trigger post.cpu_op.view().view()[i as int]] index_valid(NUM_CPUS, i) && i != cpu_id ==> post.cpu_op.view().view()[i as int] == pre.cpu_op.view().view()[i as int],
        post.thr_mp.spec_index(new_thread_ptr).locking_thread() is None,
    ensures
        ({
            let c = pre.cpu_arr.spec_index(cpu_id).value.view().view();
            kernel_k_to_kernel_u(*pre).cpu_array[cpu_id as int] == (CpuU {
                lock_state: pre.cpu_arr.spec_index(cpu_id).value.lock_state_u(), owning_container: c.owning_container, state: c.state,
                current_process: c.current_process, current_thread: c.current_thread, killed: pre.cpu_arr.spec_index(cpu_id).value.being_killed(),
                op: pre.cpu_op.view().view()[cpu_id as int],
            })
        }),
        pre.thr_mp.dom().contains(thread_ptr) ==> {
            &&& kernel_k_to_kernel_u(*pre).thread_map[thread_ptr].syscall_progress == pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()
            &&& kernel_k_to_kernel_u(*pre).thread_map[thread_ptr].endpoint_descriptors == pre.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()
            &&& kernel_k_to_kernel_u(*pre).thread_map[thread_ptr].owning_proc == pre.thr_mp.spec_index(thread_ptr).view().owning_proc
            &&& kernel_k_to_kernel_u(*pre).thread_map[thread_ptr].owning_container == pre.thr_mp.spec_index(thread_ptr).view().owning_container
        },
        kernel_k_to_kernel_u(*post).process_map.spec_index(process_ptr).owned_threads.last() == new_thread_ptr,
        release_source_process matches Some(source) ==> {
            &&& kernel_k_to_kernel_u(*pre).process_map[source].pagetable->Some_0.pagetable_window_locks == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pre.prc_mp.spec_index(source).view().pagetable).lower.pagetable_window_locks
            &&& kernel_k_to_kernel_u(*pre).process_map[process_ptr].pagetable->Some_0.pagetable_window_locks == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pre.prc_mp.spec_index(process_ptr).view().pagetable).lower.pagetable_window_locks
        },
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let mode = LockStateU::Unlocked;
            kernel_u_new_thread_changed(KernelU {
                cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, op: post.cpu_op.view().view()[cpu_id as int], ..old_u.cpu_array[cpu_id as int] }),
                process_map: match release_source_process {
                    Some(source) => old_u.process_map.insert(source, ProcessU {
                        pagetable: Some(PageTableU {
                            lock_state: mode, pagetable_window_locks: pagetable_c(post.pt_mp, post.pt_lower.view(), pre.prc_mp.spec_index(source).view().pagetable).lower.pagetable_window_locks,
                            ..old_u.process_map[source].pagetable->Some_0
                        }), ..old_u.process_map[source]
                    }).insert(process_ptr, ProcessU {
                        lock_state: mode, pagetable: Some(PageTableU {
                            lock_state: mode, pagetable_window_locks: pagetable_c(post.pt_mp, post.pt_lower.view(), pre.prc_mp.spec_index(process_ptr).view().pagetable).lower.pagetable_window_locks,
                            ..old_u.process_map[process_ptr].pagetable->Some_0
                        }),
                        iommu_table: match old_u.process_map[process_ptr].iommu_table { Some(t) => Some(PageTableU { lock_state: mode, ..t }), None => None },
                        ..old_u.process_map[process_ptr]
                    }),
                    None => old_u.process_map.insert(process_ptr, ProcessU { lock_state: mode, ..old_u.process_map[process_ptr] }),
                },
                thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: mode, ..old_u.thread_map.spec_index(thread_ptr) }),
                endpoint_map: match endpoint_ptr {
                    Some(e) => old_u.endpoint_map.insert(e, EndpointU { lock_state: mode, ..old_u.endpoint_map.spec_index(e) }),
                    None => old_u.endpoint_map,
                },
                ..old_u
            }, kernel_k_to_kernel_u(*post), process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress)
        }),
{
    kernel_u_domains_projection(post); kernel_u_domains_projection(pre);
    let old_u = kernel_k_to_kernel_u(*pre);
    let mode = LockStateU::Unlocked;
    let pre_u = KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, op: post.cpu_op.view().view()[cpu_id as int], ..old_u.cpu_array[cpu_id as int] }),
        process_map: match release_source_process {
            Some(source) => old_u.process_map.insert(source, ProcessU {
                pagetable: Some(PageTableU {
                    lock_state: mode, pagetable_window_locks: pagetable_c(post.pt_mp, post.pt_lower.view(), pre.prc_mp.spec_index(source).view().pagetable).lower.pagetable_window_locks,
                    ..old_u.process_map[source].pagetable->Some_0
                }), ..old_u.process_map[source]
            }).insert(process_ptr, ProcessU {
                lock_state: mode, pagetable: Some(PageTableU {
                    lock_state: mode, pagetable_window_locks: pagetable_c(post.pt_mp, post.pt_lower.view(), pre.prc_mp.spec_index(process_ptr).view().pagetable).lower.pagetable_window_locks,
                    ..old_u.process_map[process_ptr].pagetable->Some_0
                }),
                iommu_table: match old_u.process_map[process_ptr].iommu_table { Some(t) => Some(PageTableU { lock_state: mode, ..t }), None => None },
                ..old_u.process_map[process_ptr]
            }),
            None => old_u.process_map.insert(process_ptr, ProcessU { lock_state: mode, ..old_u.process_map[process_ptr] }),
        },
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: mode, ..old_u.thread_map.spec_index(thread_ptr) }),
        endpoint_map: match endpoint_ptr {
            Some(e) => old_u.endpoint_map.insert(e, EndpointU { lock_state: mode, ..old_u.endpoint_map.spec_index(e) }),
            None => old_u.endpoint_map,
        },
        ..old_u
    };
    let post_u = kernel_k_to_kernel_u(*post);
    kernel_cpu_projection_at(post, cpu_id); kernel_cpu_projection_at(pre, cpu_id);
    if post.prc_mp.dom().contains(process_ptr) { kernel_process_projection_at(post, process_ptr); }
    if let Some(source) = release_source_process {
        if post.prc_mp.dom().contains(source) { kernel_process_projection_at(post, source); } kernel_process_projection_at(pre, source);
        assert(pre.prc_mp.dom().contains(process_ptr) && pre.pt_mp.dom().contains(pre.prc_mp.spec_index(process_ptr).view().pagetable)
            && pre.pt_mp.dom().contains(pre.prc_mp.spec_index(source).view().pagetable)) by { reveal(kernel_new_thread_fields); process_pagetable_match_process_at(post.prc_mp, post.pt_mp, process_ptr); process_pagetable_match_process_at(post.prc_mp, post.pt_mp, source); };
        kernel_process_projection_at(pre, process_ptr);
    }
    if pre.thr_mp.dom().contains(thread_ptr) { kernel_thread_projection_at(pre, thread_ptr); }
    if post.thr_mp.dom().contains(new_thread_ptr) { kernel_thread_projection_at(post, new_thread_ptr); }
    if let Some(e) = endpoint_ptr { if post.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(post, e); } if pre.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(pre, e); } }
    assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { reveal(kernel_new_thread_fields); pre.irt.view().user_view_unfold(); post.irt.view().user_view_unfold(); };
    assert(post_u.process_map.spec_index(process_ptr).owned_threads.last() == new_thread_ptr
        && kernel_u_new_thread_changed(pre_u, post_u, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress)) by {
        kernel_new_thread_fields_and_unlocks_implies_u_cpu_array(pre, post, cpu_id, process_ptr, thread_ptr, container_ptr, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress);
        kernel_new_thread_fields_and_unlocks_implies_u_thread_map(pre, post, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress);
        kernel_new_thread_fields_and_unlocks_implies_u_endpoint_map(pre, post, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress);
        kernel_new_thread_fields_and_unlocks_implies_u_container_map(pre, post, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress, None);
        kernel_new_thread_fields_and_unlocks_implies_u_process_map(pre, post, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress, release_source_process);
        reveal(kernel_new_thread_fields); reveal(kernel_u_new_thread_changed);
        assert_seqs_equal!(post_u.thread_map.spec_index(new_thread_ptr).endpoint_descriptors == Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat, |i: int| if i == 0 { endpoint_ptr } else { None }));
    };
}

#[verifier::spinoff_prover]
pub proof fn kernel_new_thread_fields_and_parent_unlocks_implies_u_step(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    new_thread_ptr: RwLockThreadPtr, initial_regs: Registers, endpoint_ptr: Option<RwLockEndpointPtr>, release_source_process: RwLockProcessPtr,
    release_source_container: RwLockContainerPtr, staging_progress: Option<SyscallProgress>,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        container_scheduler_wf(post.ctn_mp, post.sched_mp),
        pre.prc_mp.spec_index(process_ptr).view().iommu_table is None,
        release_source_container != container_ptr && pre.ctn_mp.dom().contains(release_source_container),
        release_source_process != process_ptr && pre.prc_mp.dom().contains(release_source_process) && !pre.prc_mp.spec_index(release_source_process).view().zombie && !pre.prc_mp.spec_index(process_ptr).view().zombie,
        index_valid(NUM_CPUS, cpu_id),
        kernel_new_thread_fields(pre, post, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress),
        pre.thr_mp.spec_index(thread_ptr).view().owning_proc == release_source_process,
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)]
            pre.ctn_mp.dom().contains(p) ==> if p == container_ptr || release_source_container == p { post.ctn_mp.spec_index(p).locking_thread() is None } else {
                post.ctn_mp.spec_index(p).locking_thread() == pre.ctn_mp.spec_index(p).locking_thread() && post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u()
            },
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) ==> if p == process_ptr || release_source_process == p { post.prc_mp.spec_index(p).locking_thread() is None } else { post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread() },
        forall|p: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(p)]
            pre.thr_mp.dom().contains(p) ==> if p == thread_ptr { post.thr_mp.spec_index(p).locking_thread() is None } else { post.thr_mp.spec_index(p).locking_thread() == pre.thr_mp.spec_index(p).locking_thread() },
        forall|p: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(p)]
            pre.ep_mp.dom().contains(p) ==> if endpoint_ptr == Some(p) { post.ep_mp.spec_index(p).locking_thread() is None } else { post.ep_mp.spec_index(p).locking_thread() == pre.ep_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) ==> if (p == pre.prc_mp.spec_index(process_ptr).view().pagetable || p == pre.prc_mp.spec_index(release_source_process).view().pagetable)
                { post.pt_mp.spec_index(p).locking_thread() is None }
                else { post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
            pre.it_mp.dom().contains(p) ==> post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread(),
        forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> if i == cpu_id { post.cpu_arr.spec_index(i).value.locking_thread() is None } else { post.cpu_arr.spec_index(i).value.locking_thread() == pre.cpu_arr.spec_index(i).value.locking_thread() },
        forall|i: CpuId| #![trigger post.cpu_op.view().view()[i as int]] index_valid(NUM_CPUS, i) && i != cpu_id ==> post.cpu_op.view().view()[i as int] == pre.cpu_op.view().view()[i as int],
        post.thr_mp.spec_index(new_thread_ptr).locking_thread() is None,
    ensures
        ({
            let c = pre.cpu_arr.spec_index(cpu_id).value.view().view();
            kernel_k_to_kernel_u(*pre).cpu_array[cpu_id as int] == (CpuU {
                lock_state: pre.cpu_arr.spec_index(cpu_id).value.lock_state_u(), owning_container: c.owning_container, state: c.state,
                current_process: c.current_process, current_thread: c.current_thread, killed: pre.cpu_arr.spec_index(cpu_id).value.being_killed(),
                op: pre.cpu_op.view().view()[cpu_id as int],
            })
        }),
        pre.thr_mp.dom().contains(thread_ptr) ==> {
            &&& kernel_k_to_kernel_u(*pre).thread_map[thread_ptr].syscall_progress == pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()
            &&& kernel_k_to_kernel_u(*pre).thread_map[thread_ptr].endpoint_descriptors == pre.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()
            &&& kernel_k_to_kernel_u(*pre).thread_map[thread_ptr].owning_proc == pre.thr_mp.spec_index(thread_ptr).view().owning_proc
            &&& kernel_k_to_kernel_u(*pre).thread_map[thread_ptr].owning_container == pre.thr_mp.spec_index(thread_ptr).view().owning_container
        },
        kernel_k_to_kernel_u(*pre).process_map.spec_index(process_ptr).iommu_table is None,
        kernel_k_to_kernel_u(*post).process_map.spec_index(process_ptr).owned_threads.last() == new_thread_ptr,
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let mode = LockStateU::Unlocked;
            kernel_u_new_thread_changed(KernelU {
                cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, op: post.cpu_op.view().view()[cpu_id as int], ..old_u.cpu_array[cpu_id as int] }),
                container_map: old_u.container_map.insert(release_source_container, ContainerU { lock_state: mode, lock_process_owner: None, ..old_u.container_map[release_source_container] })
                    .insert(container_ptr, ContainerU { lock_state: mode, lock_process_owner: None, ..old_u.container_map[container_ptr] }),
                process_map: old_u.process_map.insert(release_source_process, ProcessU {
                    lock_state: mode, pagetable: Some(PageTableU {
                        lock_state: mode, pagetable_window_locks: pagetable_c(post.pt_mp, post.pt_lower.view(), pre.prc_mp.spec_index(release_source_process).view().pagetable).lower.pagetable_window_locks,
                        ..old_u.process_map[release_source_process].pagetable->Some_0
                    }), ..old_u.process_map[release_source_process]
                }).insert(process_ptr, ProcessU {
                    lock_state: mode, pagetable: Some(PageTableU {
                        lock_state: mode, pagetable_window_locks: pagetable_c(post.pt_mp, post.pt_lower.view(), pre.prc_mp.spec_index(process_ptr).view().pagetable).lower.pagetable_window_locks,
                        ..old_u.process_map[process_ptr].pagetable->Some_0
                    }),
                    iommu_table: None,
                    ..old_u.process_map[process_ptr]
                }),
                thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: mode, ..old_u.thread_map.spec_index(thread_ptr) }),
                endpoint_map: match endpoint_ptr {
                    Some(e) => old_u.endpoint_map.insert(e, EndpointU { lock_state: mode, ..old_u.endpoint_map.spec_index(e) }),
                    None => old_u.endpoint_map,
                },
                ..old_u
            }, kernel_k_to_kernel_u(*post), process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress)
        }),
{
    reveal(kernel_new_thread_fields); kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let old_u = kernel_k_to_kernel_u(*pre);
    let mode = LockStateU::Unlocked;
    let pre_u = KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, op: post.cpu_op.view().view()[cpu_id as int], ..old_u.cpu_array[cpu_id as int] }),
        container_map: old_u.container_map.insert(release_source_container, ContainerU { lock_state: mode, lock_process_owner: None, ..old_u.container_map[release_source_container] })
            .insert(container_ptr, ContainerU { lock_state: mode, lock_process_owner: None, ..old_u.container_map[container_ptr] }),
        process_map: old_u.process_map.insert(release_source_process, ProcessU {
            lock_state: mode, pagetable: Some(PageTableU {
                lock_state: mode, pagetable_window_locks: pagetable_c(post.pt_mp, post.pt_lower.view(), pre.prc_mp.spec_index(release_source_process).view().pagetable).lower.pagetable_window_locks,
                ..old_u.process_map[release_source_process].pagetable->Some_0
            }), ..old_u.process_map[release_source_process]
        }).insert(process_ptr, ProcessU {
            lock_state: mode, pagetable: Some(PageTableU {
                lock_state: mode, pagetable_window_locks: pagetable_c(post.pt_mp, post.pt_lower.view(), pre.prc_mp.spec_index(process_ptr).view().pagetable).lower.pagetable_window_locks,
                ..old_u.process_map[process_ptr].pagetable->Some_0
            }),
            iommu_table: None,
            ..old_u.process_map[process_ptr]
        }),
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: mode, ..old_u.thread_map.spec_index(thread_ptr) }),
        endpoint_map: match endpoint_ptr {
            Some(e) => old_u.endpoint_map.insert(e, EndpointU { lock_state: mode, ..old_u.endpoint_map.spec_index(e) }),
            None => old_u.endpoint_map,
        },
        ..old_u
    };
    let post_u = kernel_k_to_kernel_u(*post);
    kernel_cpu_projection_at(pre, cpu_id); kernel_cpu_projection_at(post, cpu_id);
    if pre.prc_mp.dom().contains(process_ptr) { kernel_process_projection_at(pre, process_ptr); } if post.prc_mp.dom().contains(process_ptr) { kernel_process_projection_at(post, process_ptr); }
    if pre.prc_mp.dom().contains(release_source_process) { kernel_process_projection_at(pre, release_source_process); }
    if pre.thr_mp.dom().contains(thread_ptr) { kernel_thread_projection_at(pre, thread_ptr); }
    if post.thr_mp.dom().contains(new_thread_ptr) { kernel_thread_projection_at(post, new_thread_ptr); }
    if let Some(e) = endpoint_ptr { if post.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(post, e); } if pre.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(pre, e); } }
    assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { reveal(IommuRootTable::user_view); };
    assert(post_u.process_map.spec_index(process_ptr).owned_threads.last() == new_thread_ptr && old_u.process_map[process_ptr].iommu_table is None
        && kernel_u_new_thread_changed(pre_u, post_u, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress)) by {
        kernel_new_thread_fields_and_unlocks_implies_u_cpu_array(pre, post, cpu_id, process_ptr, thread_ptr, container_ptr, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress);
        kernel_new_thread_fields_and_unlocks_implies_u_thread_map(pre, post, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress);
        kernel_new_thread_fields_and_unlocks_implies_u_endpoint_map(pre, post, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress);
        kernel_new_thread_fields_and_unlocks_implies_u_container_map(pre, post, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress, Some(release_source_container));
        kernel_new_thread_fields_and_parent_unlocks_implies_u_process_map(pre, post, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress, release_source_process);
        reveal(kernel_u_new_thread_changed);
        assert_seqs_equal!(post_u.thread_map.spec_index(new_thread_ptr).endpoint_descriptors == Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat, |i: int| if i == 0 { endpoint_ptr } else { None }));
    };
}

/// Thread publication with the caller's cpu released projects to the cpu array with only that cpu unlocked and its running
/// state taken from `post`.
#[verifier::spinoff_prover]
pub proof fn kernel_new_thread_fields_and_unlocks_implies_u_cpu_array(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    new_thread_ptr: RwLockThreadPtr, initial_regs: Registers, endpoint_ptr: Option<RwLockEndpointPtr>, staging_progress: Option<SyscallProgress>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        kernel_new_thread_fields(pre, post, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress),
        forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> if i == cpu_id { post.cpu_arr.spec_index(i).value.locking_thread() is None } else { post.cpu_arr.spec_index(i).value.locking_thread() == pre.cpu_arr.spec_index(i).value.locking_thread() },
        forall|i: CpuId| #![trigger post.cpu_op.view().view()[i as int]] index_valid(NUM_CPUS, i) && i != cpu_id ==> post.cpu_op.view().view()[i as int] == pre.cpu_op.view().view()[i as int],
    ensures
        kernel_k_to_kernel_u(*post).cpu_array == kernel_k_to_kernel_u(*pre).cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: post.cpu_op.view().view()[cpu_id as int], ..kernel_k_to_kernel_u(*pre).cpu_array[cpu_id as int] }),
{
    kernel_u_domains_projection(post); kernel_u_domains_projection(pre);
    let old_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    assert_seqs_equal!(post_u.cpu_array == old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: post.cpu_op.view().view()[cpu_id as int], ..old_u.cpu_array[cpu_id as int] }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(post, i as usize); kernel_cpu_projection_at(pre, i as usize); } reveal(kernel_new_thread_fields);
    });
}

/// Thread publication with the caller's thread released projects to the unlocked staging thread paying one quota and
/// recording `staging_progress`, plus the new thread.
#[verifier::spinoff_prover]
pub proof fn kernel_new_thread_fields_and_unlocks_implies_u_thread_map(
    pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    cpu_id: CpuId, new_thread_ptr: RwLockThreadPtr, initial_regs: Registers, endpoint_ptr: Option<RwLockEndpointPtr>, staging_progress: Option<SyscallProgress>,
)
    requires
        kernel_new_thread_fields(pre, post, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress),
        forall|p: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(p)]
            pre.thr_mp.dom().contains(p) ==> if p == thread_ptr { post.thr_mp.spec_index(p).locking_thread() is None } else { post.thr_mp.spec_index(p).locking_thread() == pre.thr_mp.spec_index(p).locking_thread() },
    ensures
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let unlocked = old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, ..old_u.thread_map.spec_index(thread_ptr) });
            let staging = unlocked.spec_index(thread_ptr);
            kernel_k_to_kernel_u(*post).thread_map == unlocked.insert(thread_ptr, ThreadU {
                quota_4k: (staging.quota_4k as int - 1) as usize, syscall_progress: staging_progress, ..staging
            }).insert(new_thread_ptr, kernel_k_to_kernel_u(*post).thread_map.spec_index(new_thread_ptr))
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let old_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let unlocked = old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, ..old_u.thread_map.spec_index(thread_ptr) });
    let staging = unlocked.spec_index(thread_ptr);
    reveal(kernel_new_thread_fields);
    assert_maps_equal!(post_u.thread_map, unlocked.insert(thread_ptr, ThreadU {
        quota_4k: (staging.quota_4k as int - 1) as usize, syscall_progress: staging_progress, ..staging
    }).insert(new_thread_ptr, post_u.thread_map.spec_index(new_thread_ptr)), p => {
        if pre.thr_mp.dom().contains(p) { kernel_thread_projection_at(pre, p); } if post.thr_mp.dom().contains(p) { kernel_thread_projection_at(post, p); }
    });
}

/// Thread publication with its initial endpoint released projects to that endpoint, unlocked, owning the new thread's
/// first descriptor; without one the endpoint map is unchanged.
#[verifier::spinoff_prover]
pub proof fn kernel_new_thread_fields_and_unlocks_implies_u_endpoint_map(
    pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    cpu_id: CpuId, new_thread_ptr: RwLockThreadPtr, initial_regs: Registers, endpoint_ptr: Option<RwLockEndpointPtr>, staging_progress: Option<SyscallProgress>,
)
    requires
        kernel_new_thread_fields(pre, post, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress),
        forall|p: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(p)]
            pre.ep_mp.dom().contains(p) ==> if endpoint_ptr == Some(p) { post.ep_mp.spec_index(p).locking_thread() is None } else { post.ep_mp.spec_index(p).locking_thread() == pre.ep_mp.spec_index(p).locking_thread() },
    ensures
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let unlocked = match endpoint_ptr {
                Some(e) => old_u.endpoint_map.insert(e, EndpointU { lock_state: LockStateU::Unlocked, ..old_u.endpoint_map.spec_index(e) }),
                None => old_u.endpoint_map,
            };
            match endpoint_ptr {
                Some(e) => kernel_k_to_kernel_u(*post).endpoint_map == unlocked.insert(e, EndpointU {
                    owning_threads: unlocked.spec_index(e).owning_threads.insert((new_thread_ptr, 0usize)), ..unlocked.spec_index(e)
                }),
                None => kernel_k_to_kernel_u(*post).endpoint_map == unlocked,
            }
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let old_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    match endpoint_ptr {
        Some(e) => {
            let unlocked = old_u.endpoint_map.insert(e, EndpointU { lock_state: LockStateU::Unlocked, ..old_u.endpoint_map.spec_index(e) });
            assert_maps_equal!(post_u.endpoint_map, unlocked.insert(e, EndpointU {
                owning_threads: unlocked.spec_index(e).owning_threads.insert((new_thread_ptr, 0usize)), ..unlocked.spec_index(e)
            }), ptr => {
                if pre.ep_mp.dom().contains(ptr) { kernel_endpoint_projection_at(pre, ptr); } if post.ep_mp.dom().contains(ptr) { kernel_endpoint_projection_at(post, ptr); }
                reveal(kernel_new_thread_fields);
            });
        },
        None => { assert_maps_equal!(post_u.endpoint_map, old_u.endpoint_map, ptr => {
            if pre.ep_mp.dom().contains(ptr) { kernel_endpoint_projection_at(pre, ptr); } if post.ep_mp.dom().contains(ptr) { kernel_endpoint_projection_at(post, ptr); }
            reveal(kernel_new_thread_fields);
        }); },
    }
}

/// Thread publication projects to its container owning and scheduling the new thread; with a released source
/// container, that container and the new thread's container are both unlocked.
#[verifier::spinoff_prover]
pub proof fn kernel_new_thread_fields_and_unlocks_implies_u_container_map(
    pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    cpu_id: CpuId, new_thread_ptr: RwLockThreadPtr, initial_regs: Registers, endpoint_ptr: Option<RwLockEndpointPtr>, staging_progress: Option<SyscallProgress>,
    released_container: Option<RwLockContainerPtr>,
)
    requires
        container_scheduler_wf(post.ctn_mp, post.sched_mp),
        kernel_new_thread_fields(pre, post, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress),
        released_container matches Some(source) ==> pre.ctn_mp.dom().contains(source),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)]
            pre.ctn_mp.dom().contains(p) ==> if released_container is Some && (p == container_ptr || released_container == Some(p)) { post.ctn_mp.spec_index(p).locking_thread() is None }
                else { post.ctn_mp.spec_index(p).locking_thread() == pre.ctn_mp.spec_index(p).locking_thread() && post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u() },
    ensures
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let unlocked = match released_container {
                Some(source) => old_u.container_map.insert(source, ContainerU { lock_state: LockStateU::Unlocked, lock_process_owner: None, ..old_u.container_map[source] })
                    .insert(container_ptr, ContainerU { lock_state: LockStateU::Unlocked, lock_process_owner: None, ..old_u.container_map[container_ptr] }),
                None => old_u.container_map,
            };
            kernel_k_to_kernel_u(*post).container_map == unlocked.insert(container_ptr, ContainerU {
                owned_threads: unlocked.spec_index(container_ptr).owned_threads.insert(new_thread_ptr),
                scheduler: unlocked.spec_index(container_ptr).scheduler.update(cpu_id as int, unlocked.spec_index(container_ptr).scheduler[cpu_id as int].push(new_thread_ptr)),
                ..unlocked.spec_index(container_ptr)
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let old_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let unlocked = match released_container {
        Some(source) => old_u.container_map.insert(source, ContainerU { lock_state: LockStateU::Unlocked, lock_process_owner: None, ..old_u.container_map[source] })
            .insert(container_ptr, ContainerU { lock_state: LockStateU::Unlocked, lock_process_owner: None, ..old_u.container_map[container_ptr] }),
        None => old_u.container_map,
    };
    let new_c = ContainerU {
        owned_threads: unlocked.spec_index(container_ptr).owned_threads.insert(new_thread_ptr),
        scheduler: unlocked.spec_index(container_ptr).scheduler.update(cpu_id as int, unlocked.spec_index(container_ptr).scheduler[cpu_id as int].push(new_thread_ptr)),
        ..unlocked.spec_index(container_ptr)
    };
    reveal(kernel_new_thread_fields);
    assert(post_u.container_map[container_ptr] == new_c) by {
        kernel_container_projection_at(pre, container_ptr); kernel_container_projection_at(post, container_ptr); container_scheduler_wf_at(post.ctn_mp, post.sched_mp, container_ptr);
    };
    assert_maps_equal!(post_u.container_map, unlocked.insert(container_ptr, new_c), p => {
        if pre.ctn_mp.dom().contains(p) && p != container_ptr {
            kernel_container_projection_at(pre, p); kernel_container_projection_at(post, p); reveal(container_scheduler_wf);
        }
    });
}

/// Thread publication with its process released projects to that process recording the new thread; with a released
/// source process, both page tables and the process's iommu table are unlocked too and both page tables take their window
/// lock states from `post`.
#[verifier::spinoff_prover]
pub proof fn kernel_new_thread_fields_and_unlocks_implies_u_process_map(
    pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    cpu_id: CpuId, new_thread_ptr: RwLockThreadPtr, initial_regs: Registers, endpoint_ptr: Option<RwLockEndpointPtr>, staging_progress: Option<SyscallProgress>,
    release_source_process: Option<RwLockProcessPtr>,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        release_source_process matches Some(source) ==> source != process_ptr && pre.prc_mp.dom().contains(source) && !pre.prc_mp.spec_index(source).view().zombie && !pre.prc_mp.spec_index(process_ptr).view().zombie,
        kernel_new_thread_fields(pre, post, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress),
        pre.thr_mp.spec_index(thread_ptr).view().owning_proc == match release_source_process { Some(source) => source, None => process_ptr },
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) ==> if p == process_ptr { post.prc_mp.spec_index(p).locking_thread() is None } else { post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) ==> if release_source_process is Some && (p == pre.prc_mp.spec_index(process_ptr).view().pagetable || p == pre.prc_mp.spec_index(release_source_process->Some_0).view().pagetable)
                { post.pt_mp.spec_index(p).locking_thread() is None }
                else { post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
            pre.it_mp.dom().contains(p) ==> if release_source_process is Some && pre.prc_mp.spec_index(process_ptr).view().iommu_table == Some(p) { post.it_mp.spec_index(p).locking_thread() is None }
                else { post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread() },
    ensures
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let mode = LockStateU::Unlocked;
            let unlocked = match release_source_process {
                Some(source) => old_u.process_map.insert(source, ProcessU {
                    pagetable: Some(PageTableU {
                        lock_state: mode, pagetable_window_locks: pagetable_c(post.pt_mp, post.pt_lower.view(), pre.prc_mp.spec_index(source).view().pagetable).lower.pagetable_window_locks,
                        ..old_u.process_map[source].pagetable->Some_0
                    }), ..old_u.process_map[source]
                }).insert(process_ptr, ProcessU {
                    lock_state: mode, pagetable: Some(PageTableU {
                        lock_state: mode, pagetable_window_locks: pagetable_c(post.pt_mp, post.pt_lower.view(), pre.prc_mp.spec_index(process_ptr).view().pagetable).lower.pagetable_window_locks,
                        ..old_u.process_map[process_ptr].pagetable->Some_0
                    }),
                    iommu_table: match old_u.process_map[process_ptr].iommu_table { Some(t) => Some(PageTableU { lock_state: mode, ..t }), None => None },
                    ..old_u.process_map[process_ptr]
                }),
                None => old_u.process_map.insert(process_ptr, ProcessU { lock_state: mode, ..old_u.process_map[process_ptr] }),
            };
            let process = unlocked.spec_index(process_ptr);
            kernel_k_to_kernel_u(*post).process_map == unlocked.insert(process_ptr, ProcessU { owned_threads: process.owned_threads.push(new_thread_ptr), ..process })
        }),
{
    hide(Map::filter_keys); kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let old_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let mode = LockStateU::Unlocked;
    let unlocked = match release_source_process {
        Some(source) => old_u.process_map.insert(source, ProcessU {
            pagetable: Some(PageTableU {
                lock_state: mode, pagetable_window_locks: pagetable_c(post.pt_mp, post.pt_lower.view(), pre.prc_mp.spec_index(source).view().pagetable).lower.pagetable_window_locks,
                ..old_u.process_map[source].pagetable->Some_0
            }), ..old_u.process_map[source]
        }).insert(process_ptr, ProcessU {
            lock_state: mode, pagetable: Some(PageTableU {
                lock_state: mode, pagetable_window_locks: pagetable_c(post.pt_mp, post.pt_lower.view(), pre.prc_mp.spec_index(process_ptr).view().pagetable).lower.pagetable_window_locks,
                ..old_u.process_map[process_ptr].pagetable->Some_0
            }),
            iommu_table: match old_u.process_map[process_ptr].iommu_table { Some(t) => Some(PageTableU { lock_state: mode, ..t }), None => None },
            ..old_u.process_map[process_ptr]
        }),
        None => old_u.process_map.insert(process_ptr, ProcessU { lock_state: mode, ..old_u.process_map[process_ptr] }),
    };
    let process = unlocked.spec_index(process_ptr);
    assert_maps_equal!(post_u.process_map, unlocked.insert(process_ptr, ProcessU { owned_threads: process.owned_threads.push(new_thread_ptr), ..process }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); }
        reveal(kernel_new_thread_fields); reveal(kernel_pagetable_nonlock_fields_unchanged);
        process_pagetable_match_process_at(post.prc_mp, post.pt_mp, p); process_iommu_table_match_process_at(post.prc_mp, post.it_mp, p);
        process_pagetable_match_process_at(post.prc_mp, post.pt_mp, process_ptr); process_iommu_table_match_process_at(post.prc_mp, post.it_mp, process_ptr);
        assert(post.prc_mp.spec_index(process_ptr).view().pagetable == pre.prc_mp.spec_index(process_ptr).view().pagetable);
        if let Some(source) = release_source_process {
            assert(post.prc_mp.spec_index(source).view().pagetable == pre.prc_mp.spec_index(source).view().pagetable);
            process_pagetable_match_process_at(post.prc_mp, post.pt_mp, source);
        }
    });
}

/// Thread publication into a child process projects to the child recording the new thread, with the child and the
/// parent process and both of their page tables unlocked and taking their window lock states from `post`.
#[verifier::spinoff_prover]
pub proof fn kernel_new_thread_fields_and_parent_unlocks_implies_u_process_map(
    pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    cpu_id: CpuId, new_thread_ptr: RwLockThreadPtr, initial_regs: Registers, endpoint_ptr: Option<RwLockEndpointPtr>, staging_progress: Option<SyscallProgress>,
    release_source_process: RwLockProcessPtr,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        pre.prc_mp.spec_index(process_ptr).view().iommu_table is None,
        release_source_process != process_ptr && pre.prc_mp.dom().contains(release_source_process) && !pre.prc_mp.spec_index(release_source_process).view().zombie && !pre.prc_mp.spec_index(process_ptr).view().zombie,
        kernel_new_thread_fields(pre, post, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, staging_progress),
        pre.thr_mp.spec_index(thread_ptr).view().owning_proc == release_source_process,
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) ==> if p == process_ptr || release_source_process == p { post.prc_mp.spec_index(p).locking_thread() is None } else { post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) ==> if (p == pre.prc_mp.spec_index(process_ptr).view().pagetable || p == pre.prc_mp.spec_index(release_source_process).view().pagetable)
                { post.pt_mp.spec_index(p).locking_thread() is None }
                else { post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
            pre.it_mp.dom().contains(p) ==> post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread(),
    ensures
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let mode = LockStateU::Unlocked;
            let unlocked = old_u.process_map.insert(release_source_process, ProcessU {
                lock_state: mode, pagetable: Some(PageTableU {
                    lock_state: mode, pagetable_window_locks: pagetable_c(post.pt_mp, post.pt_lower.view(), pre.prc_mp.spec_index(release_source_process).view().pagetable).lower.pagetable_window_locks,
                    ..old_u.process_map[release_source_process].pagetable->Some_0
                }), ..old_u.process_map[release_source_process]
            }).insert(process_ptr, ProcessU {
                lock_state: mode, pagetable: Some(PageTableU {
                    lock_state: mode, pagetable_window_locks: pagetable_c(post.pt_mp, post.pt_lower.view(), pre.prc_mp.spec_index(process_ptr).view().pagetable).lower.pagetable_window_locks,
                    ..old_u.process_map[process_ptr].pagetable->Some_0
                }),
                iommu_table: None,
                ..old_u.process_map[process_ptr]
            });
            let process = unlocked.spec_index(process_ptr);
            kernel_k_to_kernel_u(*post).process_map == unlocked.insert(process_ptr, ProcessU { owned_threads: process.owned_threads.push(new_thread_ptr), ..process })
        }),
{
    hide(Map::filter_keys);
    reveal(kernel_new_thread_fields); kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let old_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let mode = LockStateU::Unlocked;
    let unlocked = old_u.process_map.insert(release_source_process, ProcessU {
        lock_state: mode, pagetable: Some(PageTableU {
            lock_state: mode, pagetable_window_locks: pagetable_c(post.pt_mp, post.pt_lower.view(), pre.prc_mp.spec_index(release_source_process).view().pagetable).lower.pagetable_window_locks,
            ..old_u.process_map[release_source_process].pagetable->Some_0
        }), ..old_u.process_map[release_source_process]
    }).insert(process_ptr, ProcessU {
        lock_state: mode, pagetable: Some(PageTableU {
            lock_state: mode, pagetable_window_locks: pagetable_c(post.pt_mp, post.pt_lower.view(), pre.prc_mp.spec_index(process_ptr).view().pagetable).lower.pagetable_window_locks,
            ..old_u.process_map[process_ptr].pagetable->Some_0
        }),
        iommu_table: None,
        ..old_u.process_map[process_ptr]
    });
    let process = unlocked.spec_index(process_ptr);
    assert_maps_equal!(post_u.process_map, unlocked.insert(process_ptr, ProcessU { owned_threads: process.owned_threads.push(new_thread_ptr), ..process }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); }
        reveal(process_pagetable_match); reveal(process_iommu_table_match); reveal(kernel_pagetable_nonlock_fields_unchanged);
        assert(post.prc_mp.spec_index(process_ptr).view().pagetable == pre.prc_mp.spec_index(process_ptr).view().pagetable);
        assert(post.prc_mp.spec_index(release_source_process).view().pagetable == pre.prc_mp.spec_index(release_source_process).view().pagetable);
    });
}

} // verus!
