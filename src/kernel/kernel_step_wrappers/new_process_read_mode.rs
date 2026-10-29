//! K->U lemmas of the new-process and new-container steps that hold the parent page table in read mode.
use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal};
use crate::*;
#[cfg(verus_keep_ghost)]
use crate::kernel::implementation::create_thread_from_staged_page::kernel_u_new_thread_changed;

verus! {
/// Read-mode creation entry: the cpu, the process, the thread, the optional endpoint, and the optional container with its
/// optional cpu set become write-held while the process pagetable becomes read-held; window locks may rewrite the table's
/// lower half without changing its present mappings. `lctx` is aligned with `post`.
pub proof fn kernel_cpu_process_thread_endpoint_wlocked_pagetable_rlocked_implies_u_step(
    pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    endpoint_ptr: Option<RwLockEndpointPtr>, container: Option<RwLockContainerPtr>, cpu_set_unlocked: Option<KernelK>,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        typed_lock_maps_aligned(post, lctx),
        index_valid(NUM_CPUS, cpu_id),
        *post == (KernelK {
            cpu_arr: post.cpu_arr, cpu_op: post.cpu_op, prc_mp: post.prc_mp, thr_mp: post.thr_mp, ep_mp: post.ep_mp, sched_mp: post.sched_mp, ctn_mp: post.ctn_mp, pt_mp: post.pt_mp,
            pt_lower: post.pt_lower, pcid_allc_mp: post.pcid_allc_mp, cpu_set_mp: post.cpu_set_mp, ..*pre
        }),
        match container {
            Some(c) => pre.ctn_mp.dom().contains(c) && post.ctn_mp.unchanged_except(&pre.ctn_mp, c) && typed_lock_map_contains_mode(lctx.container_lock_map(), c, TypedLockMode::Write),
            None => post.ctn_mp == pre.ctn_mp,
        },
        ({
            let table = post.prc_mp.spec_index(process_ptr).view().pagetable;
            &&& !post.prc_mp.spec_index(process_ptr).view().zombie
            &&& post.pt_mp.unchanged_except(&pre.pt_mp, table)
            &&& typed_lock_map_contains_mode(lctx.pagetable_lock_map(), table, TypedLockMode::Read)
        }),
        post.cpu_arr.entries_unchanged_except(&pre.cpu_arr, cpu_id),
        forall|i: CpuId| #![trigger post.cpu_op.view().view()[i as int]] index_valid(NUM_CPUS, i) && i != cpu_id ==> post.cpu_op.view().view()[i as int] == pre.cpu_op.view().view()[i as int],
        post.prc_mp.unchanged_except(&pre.prc_mp, process_ptr),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        match endpoint_ptr { Some(e) => post.ep_mp.unchanged_except(&pre.ep_mp, e), None => post.ep_mp == pre.ep_mp },
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        endpoint_ptr is Some ==> typed_lock_map_contains_mode(lctx.endpoint_lock_map(), endpoint_ptr->Some_0, TypedLockMode::Write),
        match cpu_set_unlocked {
            Some(mid) => {
                let s = post.ctn_mp.spec_index(container->Some_0).view_rodata().view().cpu_set;
                &&& container is Some
                &&& container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)
                &&& *post == (KernelK { cpu_set_mp: post.cpu_set_mp, ..mid })
                &&& post.cpu_set_mp.unchanged_except(&mid.cpu_set_mp, s)
                &&& post.cpu_set_mp.spec_index(s).being_killed() == mid.cpu_set_mp.spec_index(s).being_killed()
                &&& typed_lock_map_contains_mode(lctx.cpu_set_lock_map(), s, TypedLockMode::Write)
                &&& kernel_container_nonlock_fields_and_quotas_unchanged(pre, &mid)
            },
            None => kernel_container_nonlock_fields_and_quotas_unchanged(pre, post),
        },
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
    ensures
        forall|c: CpuId| #![trigger kernel_k_to_kernel_u(*pre).cpu_array[c as int]] index_valid(NUM_CPUS, c) ==> kernel_k_to_kernel_u(*pre).cpu_array[c as int] == (CpuU {
            lock_state: pre.cpu_arr.spec_index(c).value.lock_state_u(), owning_container: pre.cpu_arr.spec_index(c).value.view().view().owning_container,
            state: pre.cpu_arr.spec_index(c).value.view().view().state, current_process: pre.cpu_arr.spec_index(c).value.view().view().current_process,
            current_thread: pre.cpu_arr.spec_index(c).value.view().view().current_thread, killed: pre.cpu_arr.spec_index(c).value.being_killed(),
            op: pre.cpu_op.view().view()[c as int],
        }),
        post.inv() ==> kernel_k_to_kernel_u(*pre).kernel_l4_end == post.pt_mp.spec_index(post.prc_mp.spec_index(process_ptr).view().pagetable).view().kernel_l4_end,
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let mode = LockStateU::WriteLocked;
            kernel_k_to_kernel_u(*post) == (KernelU {
                cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, op: post.cpu_op.view().view()[cpu_id as int], ..old_u.cpu_array[cpu_id as int] }),
                container_map: match container {
                    Some(c) => old_u.container_map.insert(c, ContainerU {
                        lock_state: mode, lock_process_owner: post.ctn_mp.spec_index(c).lock_process_owner_u(),
                        cpu_set_lock: if cpu_set_unlocked is Some { mode } else { old_u.container_map[c].cpu_set_lock }, ..old_u.container_map[c]
                    }),
                    None => old_u.container_map,
                },
                process_map: old_u.process_map.insert(process_ptr, ProcessU {
                    lock_state: mode, pagetable: Some(PageTableU { lock_state: LockStateU::ReadLocked, ..old_u.process_map[process_ptr].pagetable->Some_0 }), ..old_u.process_map[process_ptr]
                }),
                thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: mode, ..old_u.thread_map.spec_index(thread_ptr) }),
                endpoint_map: match endpoint_ptr {
                    Some(e) => old_u.endpoint_map.insert(e, EndpointU { lock_state: mode, ..old_u.endpoint_map.spec_index(e) }),
                    None => old_u.endpoint_map,
                },
                ..old_u
            })
        }),
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let c = post.cpu_arr.spec_index(cpu_id).value.view().view();
            let thread = post.thr_mp.spec_index(thread_ptr);
            let t = thread.view();
            let table = post.prc_mp.spec_index(process_ptr).view().pagetable;
            &&& old_u.cpu_array[cpu_id as int] == (CpuU {
                lock_state: pre.cpu_arr.spec_index(cpu_id).value.lock_state_u(), owning_container: c.owning_container, state: c.state,
                current_process: c.current_process, current_thread: c.current_thread, killed: post.cpu_arr.spec_index(cpu_id).value.being_killed(),
                op: pre.cpu_op.view().view()[cpu_id as int],
            })
            &&& old_u.cpu_array.len() == NUM_CPUS
            &&& old_u.container_map.dom() == post.ctn_mp.dom()
            &&& old_u.process_map.dom() == post.prc_mp.dom()
            &&& old_u.thread_map.dom() == post.thr_mp.dom()
            &&& old_u.endpoint_map.dom() == post.ep_mp.dom()
            &&& old_u.process_map.spec_index(process_ptr).lock_state == pre.prc_mp.spec_index(process_ptr).lock_state_u()
            &&& old_u.process_map.spec_index(process_ptr).killed == post.prc_mp.spec_index(process_ptr).being_killed()
            &&& old_u.thread_map.spec_index(thread_ptr) == (ThreadU {
                lock_state: pre.thr_mp.spec_index(thread_ptr).lock_state_u(), state: t.state, caller: t.caller, callee: t.callee,
                owning_container: t.owning_container, owning_proc: t.owning_proc, last_cpu: t.last_cpu, quota_4k: t.quota_4k, quota_2m: t.quota_2m, quota_1g: t.quota_1g,
                endpoint_descriptors: t.endpoint_descriptors.view(), blocking_endpoint_ptr: t.blocking_endpoint_ptr, ipc_payload: t.ipc_payload,
                error_code: t.error_code, trap_frame: if t.trap_frame.is_some() { Some(*t.trap_frame.get_some_0()) } else { None },
                syscall_progress: t.syscall_progress.view(), killed: thread.being_killed(),
            })
            &&& endpoint_ptr is Some ==> old_u.endpoint_map.spec_index(endpoint_ptr->Some_0).lock_state == pre.ep_mp.spec_index(endpoint_ptr->Some_0).lock_state_u()
            &&& container matches Some(c) ==> {
                &&& old_u.container_map[c].lock_state == pre.ctn_mp.spec_index(c).lock_state_u()
                &&& cpu_set_unlocked is Some ==> old_u.container_map[c].cpu_set_lock == pre.cpu_set_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().cpu_set).lock_state_u()
                &&& old_u.container_map[c].killed == post.ctn_mp.spec_index(c).being_killed()
                &&& old_u.container_map[c].zombie == post.ctn_mp.spec_index(c).view().zombie
                &&& old_u.container_map[c].depth == post.ctn_mp.spec_index(c).view_rodata().view().depth
                &&& old_u.container_map[c].free_pcids == PcidAllocator::free_pcids(post.pcid_allc_mp.spec_index(post.ctn_mp.spec_index(c).view_rodata().view().pcid_allocator).view().ref_counters.view())
            }
            &&& old_u.process_map.spec_index(process_ptr).pagetable is Some
            &&& old_u.process_map.spec_index(process_ptr).pagetable->Some_0.lock_state == pre.pt_mp.spec_index(table).lock_state_u()
            &&& old_u.process_map.spec_index(process_ptr).pagetable->Some_0.mapping_4k == pagetable_c(post.pt_mp, post.pt_lower.view(), table).user_view(LockStateU::Unlocked).mapping_4k
        }),
{
    kernel_u_cpu_array_projection(pre);
    let table = post.prc_mp.spec_index(process_ptr).view().pagetable;
    if post.inv() { reveal(KernelK::default_pagetable_wf); }
    if let Some(c) = container { post.ctn_mp.typed_lock_map_aligned_write_at(lctx.container_lock_map(), lctx.thread_id(), c); }
    if cpu_set_unlocked is Some {
        post.cpu_set_mp.typed_lock_map_aligned_write_at(lctx.cpu_set_lock_map(), lctx.thread_id(), post.ctn_mp.spec_index(container->Some_0).view_rodata().view().cpu_set);
    }
    post.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), table);
    post.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), process_ptr);
    post.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr);
    if endpoint_ptr is Some { post.ep_mp.typed_lock_map_aligned_write_at(lctx.endpoint_lock_map(), lctx.thread_id(), endpoint_ptr->Some_0); }
    assert(post.cpu_arr.spec_index(cpu_id).value.locking_thread() is Write) by { reveal(LockedArray::typed_lock_map_aligned); };
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post); reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
    reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
    reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
    let mode = LockStateU::WriteLocked;
    kernel_cpu_lock_mode_changed_implies_u_cpu_array(pre, post, cpu_id, mode);
    kernel_container_lock_mode_changed_implies_u_container_map(pre, post, container, mode, cpu_set_unlocked);
    kernel_thread_lock_mode_changed_implies_u_thread_map(pre, post, thread_ptr, mode);
    kernel_endpoint_lock_mode_changed_implies_u_endpoint_map(pre, post, endpoint_ptr, mode);
    let old_u = kernel_k_to_kernel_u(*pre);
    let new_u = kernel_k_to_kernel_u(*post);
    assert_maps_equal!(new_u.process_map, old_u.process_map.insert(process_ptr, ProcessU {
        lock_state: mode, pagetable: Some(PageTableU { lock_state: LockStateU::ReadLocked, ..old_u.process_map[process_ptr].pagetable->Some_0 }), ..old_u.process_map[process_ptr]
    }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); }
        reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(process_pagetable_match);
    });
    kernel_cpu_projection_at(pre, cpu_id);
    if pre.prc_mp.dom().contains(process_ptr) { kernel_process_projection_at(pre, process_ptr); } if post.prc_mp.dom().contains(process_ptr) { kernel_process_projection_at(post, process_ptr); }
    if pre.thr_mp.dom().contains(thread_ptr) { kernel_thread_projection_at(pre, thread_ptr); }
    if let Some(c) = container { if pre.ctn_mp.dom().contains(c) { kernel_container_projection_at(pre, c); } }
    if pre.ep_mp.dom().contains(endpoint_ptr->Some_0) { kernel_endpoint_projection_at(pre, endpoint_ptr->Some_0); }
    assert(old_u.process_map.spec_index(process_ptr).pagetable->Some_0.mapping_4k == pagetable_c(post.pt_mp, post.pt_lower.view(), table).user_view(LockStateU::Unlocked).mapping_4k) by {
        reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(process_pagetable_match);
    };
}

/// Read-mode new-process finish: the child's first thread is published while the cpu, the thread, the child, its tables,
/// and the endpoint are released and the thread's read hold on the parent's page table is dropped (other readers may remain).
pub proof fn kernel_new_thread_fields_and_unlocks_source_runlocked_implies_u_step(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    new_thread_ptr: RwLockThreadPtr, initial_regs: Registers, endpoint_ptr: Option<RwLockEndpointPtr>, source: RwLockProcessPtr,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        container_scheduler_wf(post.ctn_mp, post.sched_mp),
        source != process_ptr && pre.prc_mp.dom().contains(source) && !pre.prc_mp.spec_index(source).view().zombie && !pre.prc_mp.spec_index(process_ptr).view().zombie,
        index_valid(NUM_CPUS, cpu_id),
        kernel_new_thread_fields(pre, post, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, None),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)]
            pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).locking_thread() == pre.ctn_mp.spec_index(p).locking_thread() && post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) ==> if p == process_ptr { post.prc_mp.spec_index(p).locking_thread() is None } else { post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread() },
        forall|p: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(p)]
            pre.thr_mp.dom().contains(p) ==> if p == thread_ptr { post.thr_mp.spec_index(p).locking_thread() is None } else { post.thr_mp.spec_index(p).locking_thread() == pre.thr_mp.spec_index(p).locking_thread() },
        forall|p: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(p)]
            pre.ep_mp.dom().contains(p) ==> if endpoint_ptr == Some(p) { post.ep_mp.spec_index(p).locking_thread() is None } else { post.ep_mp.spec_index(p).locking_thread() == pre.ep_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) ==> if p == pre.prc_mp.spec_index(process_ptr).view().pagetable { post.pt_mp.spec_index(p).locking_thread() is None }
                else if p == pre.prc_mp.spec_index(source).view().pagetable { !(post.pt_mp.spec_index(p).locking_thread() is Write) }
                else { post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
            pre.it_mp.dom().contains(p) ==> if pre.prc_mp.spec_index(process_ptr).view().iommu_table == Some(p) { post.it_mp.spec_index(p).locking_thread() is None }
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
        ({
            let lock = kernel_k_to_kernel_u(*post).process_map[source].pagetable->Some_0.lock_state;
            lock is Unlocked || lock is ReadLocked
        }),
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let mode = LockStateU::Unlocked;
            let lock = kernel_k_to_kernel_u(*post).process_map[source].pagetable->Some_0.lock_state;
            kernel_u_new_thread_changed(KernelU {
                cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, op: post.cpu_op.view().view()[cpu_id as int], ..old_u.cpu_array[cpu_id as int] }),
                process_map: old_u.process_map.insert(source, ProcessU {
                    pagetable: Some(PageTableU { lock_state: lock, ..old_u.process_map[source].pagetable->Some_0 }), ..old_u.process_map[source]
                }).insert(process_ptr, ProcessU {
                    lock_state: mode, pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[process_ptr].pagetable->Some_0 }),
                    iommu_table: match old_u.process_map[process_ptr].iommu_table { Some(t) => Some(PageTableU { lock_state: mode, ..t }), None => None },
                    ..old_u.process_map[process_ptr]
                }),
                thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: mode, ..old_u.thread_map.spec_index(thread_ptr) }),
                endpoint_map: match endpoint_ptr {
                    Some(e) => old_u.endpoint_map.insert(e, EndpointU { lock_state: mode, ..old_u.endpoint_map.spec_index(e) }),
                    None => old_u.endpoint_map,
                },
                ..old_u
            }, kernel_k_to_kernel_u(*post), process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, None)
        }),
{
    kernel_u_domains_projection(post); kernel_u_domains_projection(pre);
    let old_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let mode = LockStateU::Unlocked;
    let lock = post_u.process_map[source].pagetable->Some_0.lock_state;
    let unlocked = old_u.process_map.insert(source, ProcessU {
        pagetable: Some(PageTableU { lock_state: lock, ..old_u.process_map[source].pagetable->Some_0 }), ..old_u.process_map[source]
    }).insert(process_ptr, ProcessU {
        lock_state: mode, pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[process_ptr].pagetable->Some_0 }),
        iommu_table: match old_u.process_map[process_ptr].iommu_table { Some(t) => Some(PageTableU { lock_state: mode, ..t }), None => None },
        ..old_u.process_map[process_ptr]
    });
    let pre_u = KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, op: post.cpu_op.view().view()[cpu_id as int], ..old_u.cpu_array[cpu_id as int] }),
        process_map: unlocked,
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: mode, ..old_u.thread_map.spec_index(thread_ptr) }),
        endpoint_map: match endpoint_ptr {
            Some(e) => old_u.endpoint_map.insert(e, EndpointU { lock_state: mode, ..old_u.endpoint_map.spec_index(e) }),
            None => old_u.endpoint_map,
        },
        ..old_u
    };
    kernel_cpu_projection_at(post, cpu_id); kernel_cpu_projection_at(pre, cpu_id);
    if post.prc_mp.dom().contains(process_ptr) { kernel_process_projection_at(post, process_ptr); }
    if post.prc_mp.dom().contains(source) { kernel_process_projection_at(post, source); }
    if pre.thr_mp.dom().contains(thread_ptr) { kernel_thread_projection_at(pre, thread_ptr); }
    if post.thr_mp.dom().contains(new_thread_ptr) { kernel_thread_projection_at(post, new_thread_ptr); }
    if let Some(e) = endpoint_ptr { if post.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(post, e); } if pre.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(pre, e); } }
    assert(lock is Unlocked || lock is ReadLocked) by {
        reveal(kernel_new_thread_fields); process_pagetable_match_process_at(post.prc_mp, post.pt_mp, source);
        assert(post.prc_mp.spec_index(source).view().pagetable == pre.prc_mp.spec_index(source).view().pagetable);
    };
    assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { reveal(kernel_new_thread_fields); pre.irt.view().user_view_unfold(); post.irt.view().user_view_unfold(); };
    kernel_new_thread_fields_and_unlocks_source_runlocked_implies_u_process_map(pre, post, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, source);
    assert(post_u.process_map.spec_index(process_ptr).owned_threads.last() == new_thread_ptr
        && kernel_u_new_thread_changed(pre_u, post_u, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, None)) by {
        kernel_new_thread_fields_and_unlocks_implies_u_cpu_array(pre, post, cpu_id, process_ptr, thread_ptr, container_ptr, new_thread_ptr, initial_regs, endpoint_ptr, None);
        kernel_new_thread_fields_and_unlocks_implies_u_thread_map(pre, post, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, None);
        kernel_new_thread_fields_and_unlocks_implies_u_endpoint_map(pre, post, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, None);
        kernel_new_thread_fields_and_unlocks_implies_u_container_map(pre, post, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, None, None);
        reveal(kernel_new_thread_fields); reveal(kernel_u_new_thread_changed);
        assert_seqs_equal!(post_u.thread_map.spec_index(new_thread_ptr).endpoint_descriptors == Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat, |i: int| if i == 0 { endpoint_ptr } else { None }));
    };
}
/// Read-mode new-container finish: the child root's first thread is published while the cpu, both containers, the parent
/// and root processes, the root's page table, the thread, and the endpoint are released and the thread's read hold on the
/// parent's page table is dropped (other readers may remain).
pub proof fn kernel_new_thread_fields_and_parent_unlocks_source_runlocked_implies_u_step(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    new_thread_ptr: RwLockThreadPtr, initial_regs: Registers, endpoint_ptr: Option<RwLockEndpointPtr>, source: RwLockProcessPtr, source_container: RwLockContainerPtr,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        container_scheduler_wf(post.ctn_mp, post.sched_mp),
        pre.prc_mp.spec_index(process_ptr).view().iommu_table is None,
        source_container != container_ptr && pre.ctn_mp.dom().contains(source_container),
        source != process_ptr && pre.prc_mp.dom().contains(source) && !pre.prc_mp.spec_index(source).view().zombie && !pre.prc_mp.spec_index(process_ptr).view().zombie,
        index_valid(NUM_CPUS, cpu_id),
        kernel_new_thread_fields(pre, post, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, None),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)]
            pre.ctn_mp.dom().contains(p) ==> if p == container_ptr || source_container == p { post.ctn_mp.spec_index(p).locking_thread() is None } else {
                post.ctn_mp.spec_index(p).locking_thread() == pre.ctn_mp.spec_index(p).locking_thread() && post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u()
            },
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) ==> if p == process_ptr || source == p { post.prc_mp.spec_index(p).locking_thread() is None } else { post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread() },
        forall|p: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(p)]
            pre.thr_mp.dom().contains(p) ==> if p == thread_ptr { post.thr_mp.spec_index(p).locking_thread() is None } else { post.thr_mp.spec_index(p).locking_thread() == pre.thr_mp.spec_index(p).locking_thread() },
        forall|p: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(p)]
            pre.ep_mp.dom().contains(p) ==> if endpoint_ptr == Some(p) { post.ep_mp.spec_index(p).locking_thread() is None } else { post.ep_mp.spec_index(p).locking_thread() == pre.ep_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) ==> if p == pre.prc_mp.spec_index(process_ptr).view().pagetable { post.pt_mp.spec_index(p).locking_thread() is None }
                else if p == pre.prc_mp.spec_index(source).view().pagetable { !(post.pt_mp.spec_index(p).locking_thread() is Write) }
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
            let lock = kernel_k_to_kernel_u(*post).process_map[source].pagetable->Some_0.lock_state;
            lock is Unlocked || lock is ReadLocked
        }),
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let mode = LockStateU::Unlocked;
            let lock = kernel_k_to_kernel_u(*post).process_map[source].pagetable->Some_0.lock_state;
            kernel_u_new_thread_changed(KernelU {
                cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, op: post.cpu_op.view().view()[cpu_id as int], ..old_u.cpu_array[cpu_id as int] }),
                container_map: old_u.container_map.insert(source_container, ContainerU { lock_state: mode, lock_process_owner: None, ..old_u.container_map[source_container] })
                    .insert(container_ptr, ContainerU { lock_state: mode, lock_process_owner: None, ..old_u.container_map[container_ptr] }),
                process_map: old_u.process_map.insert(source, ProcessU {
                    lock_state: mode, pagetable: Some(PageTableU { lock_state: lock, ..old_u.process_map[source].pagetable->Some_0 }), ..old_u.process_map[source]
                }).insert(process_ptr, ProcessU {
                    lock_state: mode, pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[process_ptr].pagetable->Some_0 }), iommu_table: None, ..old_u.process_map[process_ptr]
                }),
                thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: mode, ..old_u.thread_map.spec_index(thread_ptr) }),
                endpoint_map: match endpoint_ptr {
                    Some(e) => old_u.endpoint_map.insert(e, EndpointU { lock_state: mode, ..old_u.endpoint_map.spec_index(e) }),
                    None => old_u.endpoint_map,
                },
                ..old_u
            }, kernel_k_to_kernel_u(*post), process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, None)
        }),
{
    reveal(kernel_new_thread_fields); kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let old_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let mode = LockStateU::Unlocked;
    let lock = post_u.process_map[source].pagetable->Some_0.lock_state;
    let unlocked = old_u.process_map.insert(source, ProcessU {
        lock_state: mode, pagetable: Some(PageTableU { lock_state: lock, ..old_u.process_map[source].pagetable->Some_0 }), ..old_u.process_map[source]
    }).insert(process_ptr, ProcessU {
        lock_state: mode, pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[process_ptr].pagetable->Some_0 }), iommu_table: None, ..old_u.process_map[process_ptr]
    });
    let pre_u = KernelU {
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, op: post.cpu_op.view().view()[cpu_id as int], ..old_u.cpu_array[cpu_id as int] }),
        container_map: old_u.container_map.insert(source_container, ContainerU { lock_state: mode, lock_process_owner: None, ..old_u.container_map[source_container] })
            .insert(container_ptr, ContainerU { lock_state: mode, lock_process_owner: None, ..old_u.container_map[container_ptr] }),
        process_map: unlocked,
        thread_map: old_u.thread_map.insert(thread_ptr, ThreadU { lock_state: mode, ..old_u.thread_map.spec_index(thread_ptr) }),
        endpoint_map: match endpoint_ptr {
            Some(e) => old_u.endpoint_map.insert(e, EndpointU { lock_state: mode, ..old_u.endpoint_map.spec_index(e) }),
            None => old_u.endpoint_map,
        },
        ..old_u
    };
    kernel_cpu_projection_at(pre, cpu_id); kernel_cpu_projection_at(post, cpu_id);
    if pre.prc_mp.dom().contains(process_ptr) { kernel_process_projection_at(pre, process_ptr); } if post.prc_mp.dom().contains(process_ptr) { kernel_process_projection_at(post, process_ptr); }
    kernel_process_projection_at(pre, source); if post.prc_mp.dom().contains(source) { kernel_process_projection_at(post, source); }
    if pre.thr_mp.dom().contains(thread_ptr) { kernel_thread_projection_at(pre, thread_ptr); }
    if post.thr_mp.dom().contains(new_thread_ptr) { kernel_thread_projection_at(post, new_thread_ptr); }
    if let Some(e) = endpoint_ptr { if post.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(post, e); } if pre.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(pre, e); } }
    assert(lock is Unlocked || lock is ReadLocked) by { process_pagetable_match_process_at(post.prc_mp, post.pt_mp, source); };
    assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { reveal(IommuRootTable::user_view); };
    let process = unlocked.spec_index(process_ptr);
    assert(post_u.process_map == unlocked.insert(process_ptr, ProcessU { owned_threads: process.owned_threads.push(new_thread_ptr), ..process })) by {
        assert_maps_equal!(post_u.process_map, unlocked.insert(process_ptr, ProcessU { owned_threads: process.owned_threads.push(new_thread_ptr), ..process }), p => {
            if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); }
            reveal(process_pagetable_match); reveal(process_iommu_table_match); reveal(kernel_pagetable_nonlock_fields_unchanged);
            assert(post.prc_mp.spec_index(process_ptr).view().pagetable == pre.prc_mp.spec_index(process_ptr).view().pagetable);
            assert(post.prc_mp.spec_index(source).view().pagetable == pre.prc_mp.spec_index(source).view().pagetable);
        });
    };
    assert(post_u.process_map.spec_index(process_ptr).owned_threads.last() == new_thread_ptr && old_u.process_map[process_ptr].iommu_table is None
        && kernel_u_new_thread_changed(pre_u, post_u, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, None)) by {
        kernel_new_thread_fields_and_unlocks_implies_u_cpu_array(pre, post, cpu_id, process_ptr, thread_ptr, container_ptr, new_thread_ptr, initial_regs, endpoint_ptr, None);
        kernel_new_thread_fields_and_unlocks_implies_u_thread_map(pre, post, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, None);
        kernel_new_thread_fields_and_unlocks_implies_u_endpoint_map(pre, post, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, None);
        kernel_new_thread_fields_and_unlocks_implies_u_container_map(pre, post, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, None, Some(source_container));
        reveal(kernel_u_new_thread_changed);
        assert_seqs_equal!(post_u.thread_map.spec_index(new_thread_ptr).endpoint_descriptors == Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat, |i: int| if i == 0 { endpoint_ptr } else { None }));
    };
}

/// Read-mode new-process finish projects to the child process recording the new thread, with the child, its tables,
/// and the parent's page table released to `lock`, the parent page table's remaining hold.
proof fn kernel_new_thread_fields_and_unlocks_source_runlocked_implies_u_process_map(
    pre: &KernelK, post: &KernelK, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, cpu_id: CpuId,
    new_thread_ptr: RwLockThreadPtr, initial_regs: Registers, endpoint_ptr: Option<RwLockEndpointPtr>, source: RwLockProcessPtr,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        source != process_ptr && pre.prc_mp.dom().contains(source) && !pre.prc_mp.spec_index(source).view().zombie && !pre.prc_mp.spec_index(process_ptr).view().zombie,
        kernel_new_thread_fields(pre, post, process_ptr, thread_ptr, container_ptr, cpu_id, new_thread_ptr, initial_regs, endpoint_ptr, None),
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) ==> if p == process_ptr { post.prc_mp.spec_index(p).locking_thread() is None } else { post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) ==> if p == pre.prc_mp.spec_index(process_ptr).view().pagetable { post.pt_mp.spec_index(p).locking_thread() is None }
                else if p == pre.prc_mp.spec_index(source).view().pagetable { !(post.pt_mp.spec_index(p).locking_thread() is Write) }
                else { post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
            pre.it_mp.dom().contains(p) ==> if pre.prc_mp.spec_index(process_ptr).view().iommu_table == Some(p) { post.it_mp.spec_index(p).locking_thread() is None }
                else { post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread() },
    ensures
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let post_u = kernel_k_to_kernel_u(*post);
            let mode = LockStateU::Unlocked;
            let lock = post_u.process_map[source].pagetable->Some_0.lock_state;
            let unlocked = old_u.process_map.insert(source, ProcessU {
                pagetable: Some(PageTableU { lock_state: lock, ..old_u.process_map[source].pagetable->Some_0 }), ..old_u.process_map[source]
            }).insert(process_ptr, ProcessU {
                lock_state: mode, pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[process_ptr].pagetable->Some_0 }),
                iommu_table: match old_u.process_map[process_ptr].iommu_table { Some(t) => Some(PageTableU { lock_state: mode, ..t }), None => None },
                ..old_u.process_map[process_ptr]
            });
            let process = unlocked.spec_index(process_ptr);
            post_u.process_map == unlocked.insert(process_ptr, ProcessU { owned_threads: process.owned_threads.push(new_thread_ptr), ..process })
        }),
{
    kernel_u_domains_projection(post); kernel_u_domains_projection(pre);
    let old_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let mode = LockStateU::Unlocked;
    let lock = post_u.process_map[source].pagetable->Some_0.lock_state;
    let unlocked = old_u.process_map.insert(source, ProcessU {
        pagetable: Some(PageTableU { lock_state: lock, ..old_u.process_map[source].pagetable->Some_0 }), ..old_u.process_map[source]
    }).insert(process_ptr, ProcessU {
        lock_state: mode, pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[process_ptr].pagetable->Some_0 }),
        iommu_table: match old_u.process_map[process_ptr].iommu_table { Some(t) => Some(PageTableU { lock_state: mode, ..t }), None => None },
        ..old_u.process_map[process_ptr]
    });
    let process = unlocked.spec_index(process_ptr);
    assert_maps_equal!(post_u.process_map, unlocked.insert(process_ptr, ProcessU { owned_threads: process.owned_threads.push(new_thread_ptr), ..process }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); }
        reveal(kernel_new_thread_fields); reveal(kernel_pagetable_nonlock_fields_unchanged);
        process_pagetable_match_process_at(post.prc_mp, post.pt_mp, p); process_iommu_table_match_process_at(post.prc_mp, post.it_mp, p);
        process_pagetable_match_process_at(post.prc_mp, post.pt_mp, process_ptr); process_iommu_table_match_process_at(post.prc_mp, post.it_mp, process_ptr);
        process_pagetable_match_process_at(post.prc_mp, post.pt_mp, source);
        assert(post.prc_mp.spec_index(process_ptr).view().pagetable == pre.prc_mp.spec_index(process_ptr).view().pagetable);
        assert(post.prc_mp.spec_index(source).view().pagetable == pre.prc_mp.spec_index(source).view().pagetable);
    });
}
} // verus!
