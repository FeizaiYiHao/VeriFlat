use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal};
use crate::*;

verus! {
/// A global IOTLB flush that empties every domain and changes no other kernel field changes only the IOTLB projection,
/// which keeps its domains and empties every valid one; the projections change exactly when the IOTLB view does.
pub proof fn kernel_iommu_tlb_flushed_implies_u_step(pre: &KernelK, post: &KernelK)
    requires
        *post == (KernelK { iommu_tlb: post.iommu_tlb, ..*pre }),
        post.iommu_tlb.view().dom() == pre.iommu_tlb.view().dom(),
        forall|did: VtdDomainId| #![trigger post.iommu_tlb.spec_index(did)] vtd_domain_id_valid(did) ==> post.iommu_tlb.spec_index(did).is_empty(),
    ensures
        kernel_k_to_kernel_u(*post) == (KernelU { iommu_tlb: kernel_k_to_kernel_u(*post).iommu_tlb, ..kernel_k_to_kernel_u(*pre) }),
        kernel_k_to_kernel_u(*post).iommu_tlb.dom() == kernel_k_to_kernel_u(*pre).iommu_tlb.dom(),
        forall|did: VtdDomainId| #![trigger kernel_k_to_kernel_u(*post).iommu_tlb[did]] vtd_domain_id_valid(did)
            ==> kernel_k_to_kernel_u(*post).iommu_tlb[did] == post.iommu_tlb.spec_index(did) && kernel_k_to_kernel_u(*post).iommu_tlb[did].is_empty(),
        pre.iommu_tlb.view() != post.iommu_tlb.view() ==> kernel_k_to_kernel_u(*pre) != kernel_k_to_kernel_u(*post) && kernel_k_to_nonlock_kernel_u(*pre) != kernel_k_to_nonlock_kernel_u(*post),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post); kernel_u_nonlock_domains_projection(pre); kernel_u_nonlock_domains_projection(post);
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_container_maps_unchanged_implies_u_container_map(pre, post);
    kernel_process_maps_unchanged_implies_u_process_map(pre, post); kernel_thread_map_unchanged_implies_u_thread_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}

/// Emptying the valid IOTLB domain `did`, with the K-only context cache free to change and no other kernel field changed,
/// empties only that domain of the IOTLB projection and keeps every other domain; the complete and lock-free projections
/// change exactly when the IOTLB view does, i.e. when that domain was nonempty.
pub proof fn kernel_iommu_tlb_domain_invalidated_implies_u_step(pre: &KernelK, post: &KernelK, did: VtdDomainId)
    requires
        pre.iommu_tlb.inv(),
        vtd_domain_id_valid(did),
        *post == (KernelK { iommu_tlb: post.iommu_tlb, ..*pre }),
        post.iommu_tlb.view() == pre.iommu_tlb.view().insert(did, SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }),
    ensures
        kernel_k_to_kernel_u(*post) == (KernelU {
            iommu_tlb: kernel_k_to_kernel_u(*pre).iommu_tlb.insert(did, SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }), ..kernel_k_to_kernel_u(*pre)
        }),
        kernel_k_to_kernel_u(*post).iommu_tlb.dom() == kernel_k_to_kernel_u(*pre).iommu_tlb.dom(),
        forall|d: VtdDomainId| #![trigger kernel_k_to_kernel_u(*post).iommu_tlb[d]] d != did ==> kernel_k_to_kernel_u(*post).iommu_tlb[d] == kernel_k_to_kernel_u(*pre).iommu_tlb[d],
        (kernel_k_to_kernel_u(*pre) == kernel_k_to_kernel_u(*post)) == (pre.iommu_tlb.view() == post.iommu_tlb.view()),
        (kernel_k_to_nonlock_kernel_u(*pre) == kernel_k_to_nonlock_kernel_u(*post)) == (pre.iommu_tlb.view() == post.iommu_tlb.view()),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post); kernel_u_nonlock_domains_projection(pre); kernel_u_nonlock_domains_projection(post);
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_container_maps_unchanged_implies_u_container_map(pre, post);
    kernel_process_maps_unchanged_implies_u_process_map(pre, post); kernel_thread_map_unchanged_implies_u_thread_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
    assert(pre.iommu_tlb.view().dom().contains(did)) by { reveal(IommuTLB::inv); };
    kernel_nonlock_projection_is_u_nonlock_fields(*pre); kernel_nonlock_projection_is_u_nonlock_fields(*post);
}

/// Removing one present 4K entry `iova` of an IOMMU table, together with page bookkeeping, 4K-allocator bookkeeping that keeps
/// every container quota, and K-only bookkeeping of the thread `thread_ptr`, removes that IOVA from the owning process's user
/// IOMMU mapping and changes nothing else in the complete projection.
pub proof fn kernel_iommu_table_4k_mapping_removed_implies_u_step(pre: &KernelK, post: &KernelK, iommu_table: RwLockPageTableRoot, iova: VAddr, thread_ptr: RwLockThreadPtr)
    requires
        process_iommu_table_match(pre.prc_mp, pre.it_mp),
        pre.it_mp.dom().contains(iommu_table),
        *post == (KernelK { it_mp: post.it_mp, pg_arr: post.pg_arr, thr_mp: post.thr_mp, allc_4k_mp: post.allc_4k_mp, ..*pre }),
        post.it_mp.unchanged_except(&pre.it_mp, iommu_table),
        post.it_mp.spec_index(iommu_table).locking_thread() == pre.it_mp.spec_index(iommu_table).locking_thread(),
        post.it_mp.spec_index(iommu_table).view().proc_ptr == pre.it_mp.spec_index(iommu_table).view().proc_ptr,
        post.it_mp.spec_index(iommu_table).view().did == pre.it_mp.spec_index(iommu_table).view().did,
        pre.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(iova),
        pre.it_mp.spec_index(iommu_table).view().mapping_4k()[iova].present,
        post.it_mp.spec_index(iommu_table).view().mapping_4k() == pre.it_mp.spec_index(iommu_table).view().mapping_4k().remove(iova),
        post.it_mp.spec_index(iommu_table).view().mapping_2m() == pre.it_mp.spec_index(iommu_table).view().mapping_2m(),
        post.it_mp.spec_index(iommu_table).view().mapping_1g() == pre.it_mp.spec_index(iommu_table).view().mapping_1g(),
        !pre.prc_mp.spec_index(pre.it_mp.spec_index(iommu_table).view().proc_ptr).view().zombie,
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).locking_thread() == pre.thr_mp.spec_index(thread_ptr).locking_thread(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, &KernelK { it_mp: pre.it_mp, ..*post }),
        kernel_container_nonlock_fields_and_quotas_unchanged(pre, post),
    ensures
        ({
            let before = kernel_k_to_kernel_u(*pre);
            let process = pre.it_mp.spec_index(iommu_table).view().proc_ptr;
            &&& before.process_map.dom().contains(process)
            &&& before.process_map[process].iommu_table is Some
            &&& before.process_map[process].iommu_table->Some_0.mapping_4k.dom().contains(iova)
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                process_map: before.process_map.insert(process, ProcessU {
                    iommu_table: Some(PageTableU { mapping_4k: before.process_map[process].iommu_table->Some_0.mapping_4k.remove(iova), ..before.process_map[process].iommu_table->Some_0 }),
                    ..before.process_map[process]
                }),
                ..before
            })
        }),
        kernel_k_to_kernel_u(*pre) != kernel_k_to_kernel_u(*post),
        kernel_k_to_nonlock_kernel_u(*pre) != kernel_k_to_nonlock_kernel_u(*post),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post); reveal(process_iommu_table_match);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    let process = pre.it_mp.spec_index(iommu_table).view().proc_ptr;
    kernel_process_projection_at(pre, process); kernel_process_projection_at(post, process);
    assert_maps_equal!(after.process_map[process].iommu_table->Some_0.mapping_4k, before.process_map[process].iommu_table->Some_0.mapping_4k.remove(iova), a => {});
    assert_maps_equal!(after.process_map, before.process_map.insert(process, ProcessU {
        iommu_table: Some(PageTableU { mapping_4k: before.process_map[process].iommu_table->Some_0.mapping_4k.remove(iova), ..before.process_map[process].iommu_table->Some_0 }),
        ..before.process_map[process]
    }), p => { if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); } });
    assert_maps_equal!(after.thread_map, before.thread_map, t => {
        if pre.thr_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thr_mp.dom().contains(t) { kernel_thread_projection_at(post, t); }
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
    });
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
    assert_maps_equal!(after.container_map, before.container_map, c => {
        if pre.ctn_mp.dom().contains(c) { kernel_container_projection_at(pre, c); kernel_container_projection_at(post, c); } reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
    });
    assert(after.process_map[process].iommu_table->Some_0.mapping_4k.dom().contains(iova) != before.process_map[process].iommu_table->Some_0.mapping_4k.dom().contains(iova)
        && kernel_k_to_nonlock_kernel_u(*pre).process_map[process].iommu_table->Some_0.mapping_4k.dom().contains(iova)
        != kernel_k_to_nonlock_kernel_u(*post).process_map[process].iommu_table->Some_0.mapping_4k.dom().contains(iova)) by { kernel_process_nonlock_projection_at(pre, process); kernel_process_nonlock_projection_at(post, process); };
}

/// Publishing one present 4K entry at an unmapped IOVA of an IOMMU table, together with page bookkeeping, inserts that
/// entry into the owning process's user IOMMU mapping and changes nothing else in the complete projection.
pub proof fn kernel_iommu_table_4k_mapping_added_implies_u_step(pre: &KernelK, post: &KernelK, iommu_table: RwLockPageTableRoot, iova: VAddr, entry: MapEntry)
    requires
        process_iommu_table_match(pre.prc_mp, pre.it_mp),
        pre.it_mp.dom().contains(iommu_table),
        *post == (KernelK { it_mp: post.it_mp, pg_arr: post.pg_arr, ..*pre }),
        post.it_mp.unchanged_except(&pre.it_mp, iommu_table),
        post.it_mp.spec_index(iommu_table).locking_thread() == pre.it_mp.spec_index(iommu_table).locking_thread(),
        post.it_mp.spec_index(iommu_table).view().proc_ptr == pre.it_mp.spec_index(iommu_table).view().proc_ptr,
        !pre.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(iova),
        entry.present,
        post.it_mp.spec_index(iommu_table).view().mapping_4k() == pre.it_mp.spec_index(iommu_table).view().mapping_4k().insert(iova, entry),
        post.it_mp.spec_index(iommu_table).view().mapping_2m() == pre.it_mp.spec_index(iommu_table).view().mapping_2m(),
        post.it_mp.spec_index(iommu_table).view().mapping_1g() == pre.it_mp.spec_index(iommu_table).view().mapping_1g(),
        post.it_mp.spec_index(iommu_table).view().did == pre.it_mp.spec_index(iommu_table).view().did,
        !pre.prc_mp.spec_index(pre.it_mp.spec_index(iommu_table).view().proc_ptr).view().zombie,
    ensures
        ({
            let before = kernel_k_to_kernel_u(*pre);
            let process = pre.it_mp.spec_index(iommu_table).view().proc_ptr;
            &&& before.process_map.dom().contains(process)
            &&& before.process_map[process].iommu_table is Some
            &&& !before.process_map[process].iommu_table->Some_0.mapping_4k.dom().contains(iova)
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                process_map: before.process_map.insert(process, ProcessU {
                    iommu_table: Some(PageTableU { mapping_4k: before.process_map[process].iommu_table->Some_0.mapping_4k.insert(iova, entry), ..before.process_map[process].iommu_table->Some_0 }),
                    ..before.process_map[process]
                }),
                ..before
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post); reveal(process_iommu_table_match);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    let process = pre.it_mp.spec_index(iommu_table).view().proc_ptr;
    kernel_process_projection_at(pre, process); kernel_process_projection_at(post, process);
    assert_maps_equal!(after.process_map[process].iommu_table->Some_0.mapping_4k, before.process_map[process].iommu_table->Some_0.mapping_4k.insert(iova, entry), a => {});
    assert_maps_equal!(after.process_map, before.process_map.insert(process, ProcessU {
        iommu_table: Some(PageTableU { mapping_4k: before.process_map[process].iommu_table->Some_0.mapping_4k.insert(iova, entry), ..before.process_map[process].iommu_table->Some_0 }),
        ..before.process_map[process]
    }), p => { if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); } });
    assert_maps_equal!(after.thread_map, before.thread_map, t => {
        if pre.thr_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thr_mp.dom().contains(t) { kernel_thread_projection_at(post, t); }
    });
    assert_seqs_equal!(after.cpu_array == before.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); } });
    assert_maps_equal!(after.container_map, before.container_map, p => {
        if pre.ctn_mp.dom().contains(p) { kernel_container_projection_at(pre, p); } if post.ctn_mp.dom().contains(p) { kernel_container_projection_at(post, p); }
    });
    assert_maps_equal!(after.endpoint_map, before.endpoint_map, p => {
        if pre.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(pre, p); } if post.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(post, p); }
    });
}
/// Setting the lock modes of the cpu, the live process `process_ptr`, the thread `thread_ptr`, the process's page table, and
/// its IOMMU table and replacing the thread's progress changes only those lock states and that progress in the complete
/// projection; the page table may rewrite its lower half without changing its mappings.
pub proof fn kernel_cpu_process_thread_pagetable_iommu_table_lock_states_and_progress_changed_implies_u_step(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, iommu_table_ptr: RwLockPageTableRoot,
)
    requires
        process_pagetable_match(pre.prc_mp, pre.pt_mp),
        process_iommu_table_match(pre.prc_mp, pre.it_mp),
        index_valid(NUM_CPUS, cpu_id),
        *post == (KernelK { cpu_arr: post.cpu_arr, prc_mp: post.prc_mp, thr_mp: post.thr_mp, pt_mp: post.pt_mp, pt_lower: post.pt_lower, it_mp: post.it_mp, ..*pre }),
        post.cpu_arr.unchanged_except(&pre.cpu_arr, cpu_id),
        post.cpu_arr.spec_index(cpu_id).view().view() == pre.cpu_arr.spec_index(cpu_id).view().view(),
        post.cpu_arr.spec_index(cpu_id).value.being_killed() == pre.cpu_arr.spec_index(cpu_id).value.being_killed(),
        pre.prc_mp.dom().contains(process_ptr),
        !pre.prc_mp.spec_index(process_ptr).view().zombie,
        pre.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr,
        pre.prc_mp.spec_index(process_ptr).view().iommu_table == Some(iommu_table_ptr),
        post.prc_mp.unchanged_except(&pre.prc_mp, process_ptr),
        post.prc_mp.spec_index(process_ptr).view() == pre.prc_mp.spec_index(process_ptr).view(),
        post.prc_mp.spec_index(process_ptr).view_rodata() == pre.prc_mp.spec_index(process_ptr).view_rodata(),
        post.prc_mp.spec_index(process_ptr).view_ghost() == pre.prc_mp.spec_index(process_ptr).view_ghost(),
        post.prc_mp.spec_index(process_ptr).being_killed() == pre.prc_mp.spec_index(process_ptr).being_killed(),
        pre.thr_mp.dom().contains(thread_ptr),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..pre.thr_mp.spec_index(thread_ptr).view() }),
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        post.pt_mp.spec_index(pagetable_ptr).view() == pre.pt_mp.spec_index(pagetable_ptr).view(),
        post.pt_lower.view() == pre.pt_lower.view().insert(pagetable_ptr, post.pt_lower.view().spec_index(pagetable_ptr)),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k(),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_2m() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m(),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_1g(),
        post.it_mp.unchanged_except(&pre.it_mp, iommu_table_ptr),
        post.it_mp.spec_index(iommu_table_ptr).view() == pre.it_mp.spec_index(iommu_table_ptr).view(),
    ensures
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let process = pre_u.process_map.spec_index(process_ptr);
            &&& pre_u.thread_map.dom().contains(thread_ptr)
            &&& pre_u.process_map.dom().contains(process_ptr)
            &&& process.pagetable is Some
            &&& process.iommu_table is Some
        }),
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let process = pre_u.process_map.spec_index(process_ptr);
            kernel_k_to_kernel_u(*post) == (KernelU {
                cpu_array: pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state: post.cpu_arr.spec_index(cpu_id).value.lock_state_u(), ..pre_u.cpu_array[cpu_id as int] }),
                process_map: pre_u.process_map.insert(process_ptr, ProcessU {
                    lock_state: post.prc_mp.spec_index(process_ptr).lock_state_u(),
                    pagetable: Some(PageTableU { lock_state: post.pt_mp.spec_index(pagetable_ptr).lock_state_u(), ..process.pagetable->Some_0 }),
                    iommu_table: Some(PageTableU { lock_state: post.it_mp.spec_index(iommu_table_ptr).lock_state_u(), ..process.iommu_table->Some_0 }), ..process
                }),
                thread_map: pre_u.thread_map.insert(thread_ptr, ThreadU {
                    lock_state: post.thr_mp.spec_index(thread_ptr).lock_state_u(), syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(),
                    ..pre_u.thread_map.spec_index(thread_ptr)
                }),
                ..pre_u
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let process = pre_u.process_map.spec_index(process_ptr);
    assert(pre.pt_mp.dom().contains(pagetable_ptr) && pre.it_mp.dom().contains(iommu_table_ptr)) by { reveal(process_pagetable_match); reveal(process_iommu_table_match); };
    kernel_thread_projection_at(pre, thread_ptr); kernel_thread_projection_at(post, thread_ptr);
    kernel_process_projection_at(pre, process_ptr); kernel_process_projection_at(post, process_ptr);
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state: post.cpu_arr.spec_index(cpu_id).value.lock_state_u(), ..pre_u.cpu_array[cpu_id as int] }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); }
    });
    assert_maps_equal!(post_u.container_map, pre_u.container_map, c => {
        if pre.ctn_mp.dom().contains(c) { kernel_container_projection_at(pre, c); } if post.ctn_mp.dom().contains(c) { kernel_container_projection_at(post, c); }
    });
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(process_ptr, ProcessU {
        lock_state: post.prc_mp.spec_index(process_ptr).lock_state_u(),
        pagetable: Some(PageTableU { lock_state: post.pt_mp.spec_index(pagetable_ptr).lock_state_u(), ..process.pagetable->Some_0 }),
        iommu_table: Some(PageTableU { lock_state: post.it_mp.spec_index(iommu_table_ptr).lock_state_u(), ..process.iommu_table->Some_0 }), ..process
    }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); }
        reveal(process_pagetable_match); reveal(process_iommu_table_match);
    });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thread_ptr, ThreadU {
        lock_state: post.thr_mp.spec_index(thread_ptr).lock_state_u(), syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(), ..pre_u.thread_map.spec_index(thread_ptr)
    }), t => { if pre.thr_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thr_mp.dom().contains(t) { kernel_thread_projection_at(post, t); } });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => {
        if pre.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(pre, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(post, e); }
    });
}

/// Setting the lock modes of the cpu, the container `container_ptr`, the live process `process_ptr`, the thread
/// `thread_ptr`, and the process's IOMMU table and replacing the thread's progress changes only those lock states and that
/// progress in the complete projection.
pub proof fn kernel_cpu_container_process_thread_iommu_table_lock_states_and_progress_changed_implies_u_step(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, iommu_table_ptr: RwLockPageTableRoot,
)
    requires
        process_iommu_table_match(pre.prc_mp, pre.it_mp),
        index_valid(NUM_CPUS, cpu_id),
        *post == (KernelK { cpu_arr: post.cpu_arr, ctn_mp: post.ctn_mp, prc_mp: post.prc_mp, thr_mp: post.thr_mp, it_mp: post.it_mp, ..*pre }),
        post.cpu_arr.unchanged_except(&pre.cpu_arr, cpu_id),
        post.cpu_arr.spec_index(cpu_id).view().view() == pre.cpu_arr.spec_index(cpu_id).view().view(),
        post.cpu_arr.spec_index(cpu_id).value.being_killed() == pre.cpu_arr.spec_index(cpu_id).value.being_killed(),
        pre.ctn_mp.dom().contains(container_ptr),
        post.ctn_mp.unchanged_except(&pre.ctn_mp, container_ptr),
        post.ctn_mp.spec_index(container_ptr).view() == pre.ctn_mp.spec_index(container_ptr).view(),
        post.ctn_mp.spec_index(container_ptr).view_rodata() == pre.ctn_mp.spec_index(container_ptr).view_rodata(),
        post.ctn_mp.spec_index(container_ptr).view_ghost() == pre.ctn_mp.spec_index(container_ptr).view_ghost(),
        post.ctn_mp.spec_index(container_ptr).being_killed() == pre.ctn_mp.spec_index(container_ptr).being_killed(),
        pre.prc_mp.dom().contains(process_ptr),
        !pre.prc_mp.spec_index(process_ptr).view().zombie,
        pre.prc_mp.spec_index(process_ptr).view().iommu_table == Some(iommu_table_ptr),
        post.prc_mp.unchanged_except(&pre.prc_mp, process_ptr),
        post.prc_mp.spec_index(process_ptr).view() == pre.prc_mp.spec_index(process_ptr).view(),
        post.prc_mp.spec_index(process_ptr).view_rodata() == pre.prc_mp.spec_index(process_ptr).view_rodata(),
        post.prc_mp.spec_index(process_ptr).view_ghost() == pre.prc_mp.spec_index(process_ptr).view_ghost(),
        post.prc_mp.spec_index(process_ptr).being_killed() == pre.prc_mp.spec_index(process_ptr).being_killed(),
        pre.thr_mp.dom().contains(thread_ptr),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..pre.thr_mp.spec_index(thread_ptr).view() }),
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
        post.it_mp.unchanged_except(&pre.it_mp, iommu_table_ptr),
        post.it_mp.spec_index(iommu_table_ptr).view() == pre.it_mp.spec_index(iommu_table_ptr).view(),
    ensures
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            &&& pre_u.container_map.dom().contains(container_ptr)
            &&& pre_u.thread_map.dom().contains(thread_ptr)
            &&& pre_u.process_map.dom().contains(process_ptr)
            &&& pre_u.process_map.spec_index(process_ptr).iommu_table is Some
        }),
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let process = pre_u.process_map.spec_index(process_ptr);
            kernel_k_to_kernel_u(*post) == (KernelU {
                cpu_array: pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state: post.cpu_arr.spec_index(cpu_id).value.lock_state_u(), ..pre_u.cpu_array[cpu_id as int] }),
                container_map: pre_u.container_map.insert(container_ptr, ContainerU {
                    lock_state: post.ctn_mp.spec_index(container_ptr).lock_state_u(), lock_process_owner: post.ctn_mp.spec_index(container_ptr).lock_process_owner_u(),
                    ..pre_u.container_map.spec_index(container_ptr)
                }),
                process_map: pre_u.process_map.insert(process_ptr, ProcessU {
                    lock_state: post.prc_mp.spec_index(process_ptr).lock_state_u(),
                    iommu_table: Some(PageTableU { lock_state: post.it_mp.spec_index(iommu_table_ptr).lock_state_u(), ..process.iommu_table->Some_0 }), ..process
                }),
                thread_map: pre_u.thread_map.insert(thread_ptr, ThreadU {
                    lock_state: post.thr_mp.spec_index(thread_ptr).lock_state_u(), syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(),
                    ..pre_u.thread_map.spec_index(thread_ptr)
                }),
                ..pre_u
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let process = pre_u.process_map.spec_index(process_ptr);
    assert(pre.it_mp.dom().contains(iommu_table_ptr)) by { reveal(process_iommu_table_match); };
    kernel_thread_projection_at(pre, thread_ptr); kernel_thread_projection_at(post, thread_ptr);
    kernel_process_projection_at(pre, process_ptr); kernel_process_projection_at(post, process_ptr);
    kernel_container_projection_at(pre, container_ptr); kernel_container_projection_at(post, container_ptr);
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state: post.cpu_arr.spec_index(cpu_id).value.lock_state_u(), ..pre_u.cpu_array[cpu_id as int] }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); }
    });
    assert_maps_equal!(post_u.container_map, pre_u.container_map.insert(container_ptr, ContainerU {
        lock_state: post.ctn_mp.spec_index(container_ptr).lock_state_u(), lock_process_owner: post.ctn_mp.spec_index(container_ptr).lock_process_owner_u(),
        ..pre_u.container_map.spec_index(container_ptr)
    }), c => { if pre.ctn_mp.dom().contains(c) { kernel_container_projection_at(pre, c); } if post.ctn_mp.dom().contains(c) { kernel_container_projection_at(post, c); } });
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(process_ptr, ProcessU {
        lock_state: post.prc_mp.spec_index(process_ptr).lock_state_u(),
        iommu_table: Some(PageTableU { lock_state: post.it_mp.spec_index(iommu_table_ptr).lock_state_u(), ..process.iommu_table->Some_0 }), ..process
    }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); }
        reveal(process_iommu_table_match);
    });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thread_ptr, ThreadU {
        lock_state: post.thr_mp.spec_index(thread_ptr).lock_state_u(), syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(), ..pre_u.thread_map.spec_index(thread_ptr)
    }), t => { if pre.thr_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thr_mp.dom().contains(t) { kernel_thread_projection_at(post, t); } });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => {
        if pre.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(pre, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(post, e); }
    });
}

/// Replacing one thread's quota, temporary cache, and progress and rewriting the structure of the IOMMU table
/// `iommu_table_ptr` without changing its lock mode or mappings, with page bookkeeping, changes only that thread's quota
/// and progress in the complete projection.
pub proof fn kernel_thread_quota_4k_progress_and_iommu_table_structure_changed_implies_u_step(pre: &KernelK, post: &KernelK, thread_ptr: RwLockThreadPtr, iommu_table_ptr: RwLockPageTableRoot)
    requires
        process_iommu_table_match(pre.prc_mp, pre.it_mp),
        *post == (KernelK { it_mp: post.it_mp, pg_arr: post.pg_arr, thr_mp: post.thr_mp, ..*pre }),
        pre.thr_mp.dom().contains(thread_ptr),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread {
            quota_4k: post.thr_mp.spec_index(thread_ptr).view().quota_4k, temp_alloc_cache_4k: post.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k,
            syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..pre.thr_mp.spec_index(thread_ptr).view()
        }),
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
        post.thr_mp.spec_index(thread_ptr).locking_thread() == pre.thr_mp.spec_index(thread_ptr).locking_thread(),
        post.it_mp.unchanged_except(&pre.it_mp, iommu_table_ptr),
        post.it_mp.spec_index(iommu_table_ptr).locking_thread() == pre.it_mp.spec_index(iommu_table_ptr).locking_thread(),
        post.it_mp.spec_index(iommu_table_ptr).view().mapping_4k() == pre.it_mp.spec_index(iommu_table_ptr).view().mapping_4k(),
        post.it_mp.spec_index(iommu_table_ptr).view().mapping_2m() == pre.it_mp.spec_index(iommu_table_ptr).view().mapping_2m(),
        post.it_mp.spec_index(iommu_table_ptr).view().mapping_1g() == pre.it_mp.spec_index(iommu_table_ptr).view().mapping_1g(),
        post.it_mp.spec_index(iommu_table_ptr).view().did == pre.it_mp.spec_index(iommu_table_ptr).view().did,
    ensures
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let thread = pre.thr_mp.spec_index(thread_ptr).view();
            &&& pre_u.thread_map.dom().contains(thread_ptr)
            &&& pre_u.thread_map.spec_index(thread_ptr).quota_4k == thread.quota_4k
            &&& pre_u.thread_map.spec_index(thread_ptr).syscall_progress == thread.syscall_progress.view()
        }),
        kernel_k_to_kernel_u(*post) == (KernelU {
            thread_map: kernel_k_to_kernel_u(*pre).thread_map.insert(thread_ptr, ThreadU {
                quota_4k: post.thr_mp.spec_index(thread_ptr).view().quota_4k, syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(),
                ..kernel_k_to_kernel_u(*pre).thread_map.spec_index(thread_ptr)
            }),
            ..kernel_k_to_kernel_u(*pre)
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    kernel_thread_projection_at(pre, thread_ptr); kernel_thread_projection_at(post, thread_ptr);
    assert_maps_equal!(post_u.process_map, pre_u.process_map, p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); }
        reveal(process_iommu_table_match);
    });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thread_ptr, ThreadU {
        quota_4k: post.thr_mp.spec_index(thread_ptr).view().quota_4k, syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(), ..pre_u.thread_map[thread_ptr]
    }), t => { if pre.thr_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thr_mp.dom().contains(t) { kernel_thread_projection_at(post, t); } });
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); } });
    assert_maps_equal!(post_u.container_map, pre_u.container_map, c => {
        if pre.ctn_mp.dom().contains(c) { kernel_container_projection_at(pre, c); } if post.ctn_mp.dom().contains(c) { kernel_container_projection_at(post, c); }
    });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => {
        if pre.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(pre, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(post, e); }
    });
}
} // verus!
