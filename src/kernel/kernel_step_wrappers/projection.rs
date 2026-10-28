use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal, assert_sets_equal};
use crate::*;
#[cfg(verus_keep_ghost)]
use crate::kernel::implementation::create_thread_from_staged_page::kernel_u_new_thread_changed;

verus! {
/// The lock-free projection of a kernel state is the nonlock-field view of its full projection.
pub proof fn kernel_nonlock_projection_is_u_nonlock_fields(krnl: KernelK)
    ensures kernel_k_to_nonlock_kernel_u(krnl) == kernel_u_nonlock_fields(kernel_k_to_kernel_u(krnl)),
{
    reveal(kernel_k_to_kernel_u); reveal(kernel_k_to_nonlock_kernel_u); reveal(kernel_u_nonlock_fields);
    assert_seqs_equal!(kernel_k_to_nonlock_kernel_u(krnl).cpu_array == kernel_u_nonlock_fields(kernel_k_to_kernel_u(krnl)).cpu_array);
    assert_maps_equal!(kernel_k_to_nonlock_kernel_u(krnl).container_map, kernel_u_nonlock_fields(kernel_k_to_kernel_u(krnl)).container_map, p => {});
    assert_maps_equal!(kernel_k_to_nonlock_kernel_u(krnl).process_map, kernel_u_nonlock_fields(kernel_k_to_kernel_u(krnl)).process_map, p => {});
    assert_maps_equal!(kernel_k_to_nonlock_kernel_u(krnl).thread_map, kernel_u_nonlock_fields(kernel_k_to_kernel_u(krnl)).thread_map, p => {});
    assert_maps_equal!(kernel_k_to_nonlock_kernel_u(krnl).endpoint_map, kernel_u_nonlock_fields(kernel_k_to_kernel_u(krnl)).endpoint_map, p => {});
}

#[verifier::spinoff_prover]
pub proof fn kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(pre: &KernelK, post: &KernelK)
    requires
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        post.irt.view().owners() == pre.irt.view().owners(),
        post.irt.view().iommu_roots() == pre.irt.view().iommu_roots(),
        post.cpu_tlb.view() == pre.cpu_tlb.view(),
        post.iommu_tlb.view() == pre.iommu_tlb.view(),
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post),
        kernel_container_nonlock_fields_and_quotas_unchanged(pre, post),
    ensures
        kernel_k_to_nonlock_kernel_u(*pre) == kernel_k_to_nonlock_kernel_u(*post),
{
    reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(kernel_endpoint_nonlock_fields_unchanged);
    reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
    reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
    kernel_u_nonlock_domains_projection(pre); kernel_u_nonlock_domains_projection(post);
    let pre_u = kernel_k_to_nonlock_kernel_u(*pre);
    let post_u = kernel_k_to_nonlock_kernel_u(*post);
    assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { reveal(IommuRootTable::user_view); };
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_nonlock_projection_at(pre, i as usize); kernel_cpu_nonlock_projection_at(post, i as usize); } });
    assert_maps_equal!(post_u.container_map, pre_u.container_map, c => { if pre.ctn_mp.dom().contains(c) { kernel_container_nonlock_projection_at(pre, c); } if post.ctn_mp.dom().contains(c) { kernel_container_nonlock_projection_at(post, c); } });
    assert_maps_equal!(post_u.process_map, pre_u.process_map, p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_nonlock_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_nonlock_projection_at(post, p); }
        reveal(process_pagetable_match); reveal(process_iommu_table_match);
    });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map, t => { if pre.thr_mp.dom().contains(t) { kernel_thread_nonlock_projection_at(pre, t); } if post.thr_mp.dom().contains(t) { kernel_thread_nonlock_projection_at(post, t); } });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => { if pre.ep_mp.dom().contains(e) { kernel_endpoint_nonlock_projection_at(pre, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_nonlock_projection_at(post, e); } });
}

/// A section that write-holds one thread throughout, changes no non-lock field, and moves
/// lock modes only on pages and allocator objects leaves the complete projection unchanged.
pub proof fn kernel_thread_write_held_section_implies_u_eq(pre: &KernelK, post: &KernelK, pre_lctx: &LocalContext, post_lctx: &LocalContext, thread_ptr: RwLockThreadPtr)
    requires
        post.inv(),
        pre.thr_mp.typed_lock_map_aligned(pre_lctx.thread_lock_map(), pre_lctx.thread_id()),
        post.thr_mp.typed_lock_map_aligned(post_lctx.thread_lock_map(), post_lctx.thread_id()),
        typed_lock_map_contains_mode(pre_lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(post_lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        *post == (KernelK { pg_arr: post.pg_arr, thr_mp: post.thr_mp, allc_4k_mp: post.allc_4k_mp, allc_2m_mp: post.allc_2m_mp, allc_1g_mp: post.allc_1g_mp, ..*pre }),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post),
        kernel_container_nonlock_fields_and_quotas_unchanged(pre, post),
    ensures
        kernel_k_to_kernel_u(*post) == kernel_k_to_kernel_u(*pre),
{
    broadcast use kernel_endpoint_nonlock_fields_unchanged_for_equal;
    pre.thr_mp.typed_lock_map_aligned_write_at(pre_lctx.thread_lock_map(), pre_lctx.thread_id(), thread_ptr);
    post.thr_mp.typed_lock_map_aligned_write_at(post_lctx.thread_lock_map(), post_lctx.thread_id(), thread_ptr);
    kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(pre, post);
}

/// Unchanged non-lock fields and user-visible lock modes leave the complete projection unchanged.
pub proof fn kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(pre: &KernelK, post: &KernelK)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        post.irt.view().owners() == pre.irt.view().owners(),
        post.irt.view().iommu_roots() == pre.irt.view().iommu_roots(),
        post.cpu_tlb.view() == pre.cpu_tlb.view(),
        post.iommu_tlb.view() == pre.iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(pre, post),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)]
            post.ctn_mp.dom().contains(p) && pre.ctn_mp.dom().contains(p) ==> {
                let before = pre.ctn_mp.spec_index(p).locking_thread();
                let after = post.ctn_mp.spec_index(p).locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
                &&& post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u()
            },
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
            post.prc_mp.dom().contains(p) && pre.prc_mp.dom().contains(p) ==> {
                let before = pre.prc_mp.spec_index(p).locking_thread();
                let after = post.prc_mp.spec_index(p).locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
            },
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
            post.pt_mp.dom().contains(p) && pre.pt_mp.dom().contains(p) ==> {
                let before = pre.pt_mp.spec_index(p).locking_thread();
                let after = post.pt_mp.spec_index(p).locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
            },
        forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
            post.it_mp.dom().contains(p) && pre.it_mp.dom().contains(p) ==> {
                let before = pre.it_mp.spec_index(p).locking_thread();
                let after = post.it_mp.spec_index(p).locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
            },
        forall|p: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(p)]
            post.thr_mp.dom().contains(p) && pre.thr_mp.dom().contains(p) ==> {
                let before = pre.thr_mp.spec_index(p).locking_thread();
                let after = post.thr_mp.spec_index(p).locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
            },
        forall|p: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(p)]
            post.ep_mp.dom().contains(p) && pre.ep_mp.dom().contains(p) ==> {
                let before = pre.ep_mp.spec_index(p).locking_thread();
                let after = post.ep_mp.spec_index(p).locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
            },
        forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> {
                let before = pre.cpu_arr.spec_index(i).value.locking_thread();
                let after = post.cpu_arr.spec_index(i).value.locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
            },
    ensures
        kernel_k_to_kernel_u(*pre) == kernel_k_to_kernel_u(*post),
{ kernel_lock_states_unchanged_except_tables_of_implies_u_eq(pre, post, None); }

/// Unchanged non-lock fields and user-visible lock modes, except on the page table and IOMMU table of the zombie process
/// `zombie`, if any, which the projection hides, leave the complete projection unchanged.
#[verifier::spinoff_prover]
pub proof fn kernel_lock_states_unchanged_except_tables_of_implies_u_eq(pre: &KernelK, post: &KernelK, zombie: Option<RwLockProcessPtr>)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        zombie is Some ==> post.prc_mp.dom().contains(zombie->Some_0),
        zombie is Some ==> post.prc_mp.spec_index(zombie->Some_0).view().zombie,
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        post.irt.view().owners() == pre.irt.view().owners(),
        post.irt.view().iommu_roots() == pre.irt.view().iommu_roots(),
        post.cpu_tlb.view() == pre.cpu_tlb.view(),
        post.iommu_tlb.view() == pre.iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(pre, post),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)]
            post.ctn_mp.dom().contains(p) && pre.ctn_mp.dom().contains(p) ==> {
                let before = pre.ctn_mp.spec_index(p).locking_thread();
                let after = post.ctn_mp.spec_index(p).locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
                &&& post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u()
            },
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
            post.prc_mp.dom().contains(p) && pre.prc_mp.dom().contains(p) ==> {
                let before = pre.prc_mp.spec_index(p).locking_thread();
                let after = post.prc_mp.spec_index(p).locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
            },
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
            post.pt_mp.dom().contains(p) && pre.pt_mp.dom().contains(p) && (zombie is Some ==> p != post.prc_mp.spec_index(zombie->Some_0).view().pagetable) ==> {
                let before = pre.pt_mp.spec_index(p).locking_thread();
                let after = post.pt_mp.spec_index(p).locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
            },
        forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
            post.it_mp.dom().contains(p) && pre.it_mp.dom().contains(p) && (zombie is Some ==> Some(p) != post.prc_mp.spec_index(zombie->Some_0).view().iommu_table) ==> {
                let before = pre.it_mp.spec_index(p).locking_thread();
                let after = post.it_mp.spec_index(p).locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
            },
        forall|p: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(p)]
            post.thr_mp.dom().contains(p) && pre.thr_mp.dom().contains(p) ==> {
                let before = pre.thr_mp.spec_index(p).locking_thread();
                let after = post.thr_mp.spec_index(p).locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
            },
        forall|p: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(p)]
            post.ep_mp.dom().contains(p) && pre.ep_mp.dom().contains(p) ==> {
                let before = pre.ep_mp.spec_index(p).locking_thread();
                let after = post.ep_mp.spec_index(p).locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
            },
        forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> {
                let before = pre.cpu_arr.spec_index(i).value.locking_thread();
                let after = post.cpu_arr.spec_index(i).value.locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
            },
    ensures
        kernel_k_to_kernel_u(*pre) == kernel_k_to_kernel_u(*post),
{
    kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(pre, post);
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post); reveal(kernel_k_to_nonlock_kernel_u);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    assert_seqs_equal!(before.cpu_array == after.cpu_array, i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); }
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
    });
    assert_maps_equal!(before.container_map, after.container_map, p => {
        if pre.ctn_mp.dom().contains(p) { kernel_container_projection_at(pre, p); } if post.ctn_mp.dom().contains(p) { kernel_container_projection_at(post, p); }
        reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
    });
    assert_maps_equal!(before.process_map, after.process_map, p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); }
        process_pagetable_match_process_at(post.prc_mp, post.pt_mp, p); process_iommu_table_match_process_at(post.prc_mp, post.it_mp, p);
        if zombie is Some { process_pagetable_match_process_at(post.prc_mp, post.pt_mp, zombie->Some_0); process_iommu_table_match_process_at(post.prc_mp, post.it_mp, zombie->Some_0); }
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged);
        reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
    });
    assert_maps_equal!(before.thread_map, after.thread_map, p => {
        if pre.thr_mp.dom().contains(p) { kernel_thread_projection_at(pre, p); } if post.thr_mp.dom().contains(p) { kernel_thread_projection_at(post, p); }
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
    });
    assert_maps_equal!(before.endpoint_map, after.endpoint_map, p => {
        if pre.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(pre, p); } if post.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(post, p); }
        reveal(kernel_endpoint_nonlock_fields_unchanged);
    });
}

#[verifier::spinoff_prover]
pub(super) proof fn kernel_context_switch_fields_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId, next_thread: RwLockThreadPtr, entry_regs: Registers, flushed_pcid: Option<Pcid>, include_lock_state: bool)
    requires
        post.inv(),
        kernel_context_switch_fields(pre, post, cpu_id, next_thread, entry_regs, flushed_pcid),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)] pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
    ensures
        kernel_u_context_switch_changed(kernel_k_user_projection(*pre, include_lock_state), kernel_k_user_projection(*post, include_lock_state), cpu_id, next_thread, entry_regs, flushed_pcid),
{
    hide(kernel_k_user_projection);
    reveal(kernel_u_context_switch_changed); kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    let cpu = pre_u.cpu_array[cpu_id as int];
    let container = pre_u.container_map.spec_index(cpu.owning_container);
    let next = pre_u.thread_map.spec_index(next_thread);
    let run_queue = container.scheduler[cpu_id as int];
    let requeued = match cpu.current_thread {
        Some(prev) => pre_u.thread_map.insert(prev, ThreadU {
            state: ThreadState::SCHEDULED { cpu_id }, error_code: None, trap_frame: Some(entry_regs), ..pre_u.thread_map.spec_index(prev)
        }),
        None => pre_u.thread_map,
    };
    assert({
        &&& index_valid(NUM_CPUS, cpu_id)
        &&& !(cpu.state is Off)
        &&& pre_u.container_map.dom().contains(cpu.owning_container)
        &&& run_queue.len() > 0
        &&& run_queue[0] == next_thread
        &&& pre_u.thread_map.dom().contains(next_thread)
        &&& !next.killed
        &&& next.state is SCHEDULED
        &&& next.owning_container == cpu.owning_container
        &&& pre_u.process_map.dom().contains(next.owning_proc)
        &&& cpu.current_thread != Some(next_thread)
        &&& cpu.current_process is Some == cpu.current_thread is Some
        &&& (cpu.current_thread is Some ==> {
            let prev = pre_u.thread_map.spec_index(cpu.current_thread.unwrap());
            &&& pre_u.thread_map.dom().contains(cpu.current_thread.unwrap())
            &&& !prev.killed
            &&& prev.state == (ThreadState::RUNNING { cpu_id })
            &&& prev.owning_proc == cpu.current_process.unwrap()
            &&& pre_u.process_map.dom().contains(cpu.current_process.unwrap())
            &&& !pre_u.process_map.spec_index(cpu.current_process.unwrap()).killed
        })
    }) by {
        reveal(kernel_context_switch_fields); kernel_cpu_user_projection_at(pre, include_lock_state, cpu_id);
        if pre.ctn_mp.dom().contains(pre.cpu_arr.spec_index(cpu_id).value.view().view().owning_container) { kernel_container_user_projection_at(pre, include_lock_state, pre.cpu_arr.spec_index(cpu_id).value.view().view().owning_container); }
        if pre.thr_mp.dom().contains(next_thread) { kernel_thread_user_projection_at(pre, include_lock_state, next_thread); }
        if pre.prc_mp.dom().contains(pre.thr_mp.spec_index(next_thread).view().owning_proc) { kernel_process_user_projection_at(pre, include_lock_state, pre.thr_mp.spec_index(next_thread).view().owning_proc); }
        if let Some(t) = pre.cpu_arr.spec_index(cpu_id).value.view().view().current_thread { if pre.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(pre, include_lock_state, t); } }
        if let Some(p) = pre.cpu_arr.spec_index(cpu_id).value.view().view().current_process { if pre.prc_mp.dom().contains(p) { kernel_process_user_projection_at(pre, include_lock_state, p); } }
    };
    kernel_context_switch_fields_implies_u_cpu_array(pre, post, cpu_id, next_thread, entry_regs, flushed_pcid, include_lock_state);
    kernel_context_switch_fields_implies_u_thread_map(pre, post, cpu_id, next_thread, entry_regs, flushed_pcid, include_lock_state);
    kernel_context_switch_fields_implies_u_process_map(pre, post, cpu_id, next_thread, entry_regs, flushed_pcid, include_lock_state);
    kernel_context_switch_fields_implies_u_container_map(pre, post, cpu_id, next_thread, entry_regs, flushed_pcid, include_lock_state);
    assert(post_u == (KernelU {
        cpu_array: pre_u.cpu_array.update(cpu_id as int, CpuU {
            state: CpuState::Running, current_process: Some(next.owning_proc), current_thread: Some(next_thread), ..cpu
        }),
        container_map: pre_u.container_map.insert(cpu.owning_container, ContainerU {
            scheduler: container.scheduler.update(cpu_id as int, match cpu.current_thread { Some(prev) => run_queue.skip(1).push(prev), None => run_queue.skip(1) }),
            ..container
        }),
        thread_map: requeued.insert(next_thread, ThreadU { state: ThreadState::RUNNING { cpu_id }, last_cpu: cpu_id, error_code: None, trap_frame: None, ..next }),
        cpu_tlb: match flushed_pcid {
            Some(pcid) => pre_u.cpu_tlb.insert((cpu_id, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }),
            None => pre_u.cpu_tlb,
        },
        ..pre_u
    })) by {
        reveal(kernel_context_switch_fields); reveal(kernel_endpoint_nonlock_fields_unchanged);
        assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { reveal(IommuRootTable::user_view); };
        assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => { if pre.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(pre, include_lock_state, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(post, include_lock_state, e); } });
    };
}

/// The context-switch fields project to the cpu array with only `cpu_id` running `next_thread`.
proof fn kernel_context_switch_fields_implies_u_cpu_array(pre: &KernelK, post: &KernelK, cpu_id: CpuId, next_thread: RwLockThreadPtr, entry_regs: Registers, flushed_pcid: Option<Pcid>, include_lock_state: bool)
    requires kernel_context_switch_fields(pre, post, cpu_id, next_thread, entry_regs, flushed_pcid),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let post_u = kernel_k_user_projection(*post, include_lock_state);
            let cpu = pre_u.cpu_array[cpu_id as int];
            post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU {
                state: CpuState::Running, current_process: Some(pre_u.thread_map.spec_index(next_thread).owning_proc), current_thread: Some(next_thread), ..cpu
            })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_context_switch_fields);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    if pre.thr_mp.dom().contains(next_thread) { kernel_thread_user_projection_at(pre, include_lock_state, next_thread); } if index_valid(NUM_CPUS, cpu_id) { kernel_cpu_user_projection_at(pre, include_lock_state, cpu_id); }
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    let cpu = pre_u.cpu_array[cpu_id as int];
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU {
        state: CpuState::Running, current_process: Some(pre_u.thread_map.spec_index(next_thread).owning_proc), current_thread: Some(next_thread), ..cpu
    }), i => { if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, include_lock_state, i as usize); kernel_cpu_user_projection_at(post, include_lock_state, i as usize); } });
}

/// The context-switch fields project to the thread map with the previous thread requeued and `next_thread` running.
proof fn kernel_context_switch_fields_implies_u_thread_map(pre: &KernelK, post: &KernelK, cpu_id: CpuId, next_thread: RwLockThreadPtr, entry_regs: Registers, flushed_pcid: Option<Pcid>, include_lock_state: bool)
    requires kernel_context_switch_fields(pre, post, cpu_id, next_thread, entry_regs, flushed_pcid),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let post_u = kernel_k_user_projection(*post, include_lock_state);
            let next = pre_u.thread_map.spec_index(next_thread);
            let requeued = match pre_u.cpu_array[cpu_id as int].current_thread {
                Some(prev) => pre_u.thread_map.insert(prev, ThreadU {
                    state: ThreadState::SCHEDULED { cpu_id }, error_code: None, trap_frame: Some(entry_regs), ..pre_u.thread_map.spec_index(prev)
                }),
                None => pre_u.thread_map,
            };
            post_u.thread_map == requeued.insert(next_thread, ThreadU { state: ThreadState::RUNNING { cpu_id }, last_cpu: cpu_id, error_code: None, trap_frame: None, ..next })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_context_switch_fields); kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    kernel_cpu_user_projection_at(pre, include_lock_state, cpu_id); if pre.thr_mp.dom().contains(next_thread) { kernel_thread_user_projection_at(pre, include_lock_state, next_thread); }
    if let Some(prev) = pre.cpu_arr.spec_index(cpu_id).value.view().view().current_thread { if pre.thr_mp.dom().contains(prev) { kernel_thread_user_projection_at(pre, include_lock_state, prev); } }
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    let next = pre_u.thread_map.spec_index(next_thread);
    let requeued = match pre_u.cpu_array[cpu_id as int].current_thread {
        Some(prev) => pre_u.thread_map.insert(prev, ThreadU {
            state: ThreadState::SCHEDULED { cpu_id }, error_code: None, trap_frame: Some(entry_regs), ..pre_u.thread_map.spec_index(prev)
        }),
        None => pre_u.thread_map,
    };
    assert_maps_equal!(post_u.thread_map, requeued.insert(next_thread, ThreadU {
        state: ThreadState::RUNNING { cpu_id }, last_cpu: cpu_id, error_code: None, trap_frame: None, ..next
    }), t => { if pre.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(pre, include_lock_state, t); } if post.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(post, include_lock_state, t); } });
}

/// The context-switch fields leave the process map projection unchanged.
proof fn kernel_context_switch_fields_implies_u_process_map(pre: &KernelK, post: &KernelK, cpu_id: CpuId, next_thread: RwLockThreadPtr, entry_regs: Registers, flushed_pcid: Option<Pcid>, include_lock_state: bool)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        kernel_context_switch_fields(pre, post, cpu_id, next_thread, entry_regs, flushed_pcid),
    ensures kernel_k_user_projection(*post, include_lock_state).process_map == kernel_k_user_projection(*pre, include_lock_state).process_map,
{
    hide(kernel_k_user_projection);
    reveal(kernel_context_switch_fields); reveal(kernel_process_nonlock_fields_unchanged); kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    assert_maps_equal!(post_u.process_map, pre_u.process_map, p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_user_projection_at(pre, include_lock_state, p); } if post.prc_mp.dom().contains(p) { kernel_process_user_projection_at(post, include_lock_state, p); }
        reveal(process_pagetable_match); reveal(process_iommu_table_match); reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
    });
}

/// The context-switch fields project to the container map with only the cpu's own shard rotated.
proof fn kernel_context_switch_fields_implies_u_container_map(pre: &KernelK, post: &KernelK, cpu_id: CpuId, next_thread: RwLockThreadPtr, entry_regs: Registers, flushed_pcid: Option<Pcid>, include_lock_state: bool)
    requires
        container_scheduler_wf(post.ctn_mp, post.sched_mp),
        kernel_context_switch_fields(pre, post, cpu_id, next_thread, entry_regs, flushed_pcid),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)] pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let post_u = kernel_k_user_projection(*post, include_lock_state);
            let cpu = pre_u.cpu_array[cpu_id as int];
            let container = pre_u.container_map.spec_index(cpu.owning_container);
            let run_queue = container.scheduler[cpu_id as int];
            post_u.container_map == pre_u.container_map.insert(cpu.owning_container, ContainerU {
                scheduler: container.scheduler.update(cpu_id as int, match cpu.current_thread { Some(prev) => run_queue.skip(1).push(prev), None => run_queue.skip(1) }),
                ..container
            })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_context_switch_fields); kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    kernel_cpu_user_projection_at(pre, include_lock_state, cpu_id);
    if pre.ctn_mp.dom().contains(pre.cpu_arr.spec_index(cpu_id).value.view().view().owning_container) { kernel_container_user_projection_at(pre, include_lock_state, pre.cpu_arr.spec_index(cpu_id).value.view().view().owning_container); }
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    let cpu = pre_u.cpu_array[cpu_id as int];
    let container = pre_u.container_map.spec_index(cpu.owning_container);
    let run_queue = container.scheduler[cpu_id as int];
    let new_c = ContainerU {
        scheduler: container.scheduler.update(cpu_id as int, match cpu.current_thread { Some(prev) => run_queue.skip(1).push(prev), None => run_queue.skip(1) }),
        ..container
    };
    assert(post_u.container_map[cpu.owning_container] == new_c) by { kernel_container_user_projection_at(post, include_lock_state, cpu.owning_container); reveal(container_scheduler_wf); };
    assert_maps_equal!(post_u.container_map, pre_u.container_map.insert(cpu.owning_container, new_c), c => {
        if pre.ctn_mp.dom().contains(c) && c != cpu.owning_container {
            kernel_container_user_projection_at(pre, include_lock_state, c); kernel_container_user_projection_at(post, include_lock_state, c); reveal(container_scheduler_wf);
        }
    });
}

#[verifier::spinoff_prover]
pub(super) proof fn kernel_rebalance_pull_fields_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId, victim: CpuId, thread: RwLockThreadPtr, include_lock_state: bool)
    requires
        container_scheduler_wf(post.ctn_mp, post.sched_mp),
        kernel_rebalance_pull_fields(pre, post, cpu_id, victim, thread),
    ensures
        kernel_u_rebalance_pull_changed(kernel_k_user_projection(*pre, include_lock_state), kernel_k_user_projection(*post, include_lock_state), cpu_id, victim, thread),
{
    hide(kernel_k_user_projection);
    reveal(kernel_u_rebalance_pull_changed); kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    assert(kernel_u_rebalance_pull_changed(pre_u, post_u, cpu_id, victim, thread)) by {
        reveal(kernel_rebalance_pull_fields); kernel_cpu_user_projection_at(pre, include_lock_state, cpu_id); kernel_cpu_user_projection_at(pre, include_lock_state, victim);
        if pre.ctn_mp.dom().contains(pre.cpu_arr.spec_index(cpu_id).value.view().view().owning_container) { kernel_container_user_projection_at(pre, include_lock_state, pre.cpu_arr.spec_index(cpu_id).value.view().view().owning_container); }
        if pre.thr_mp.dom().contains(thread) { kernel_thread_user_projection_at(pre, include_lock_state, thread); }
        let cpu = pre_u.cpu_array[cpu_id as int];
        let container = pre_u.container_map.spec_index(cpu.owning_container);
        let queues = container.scheduler;
        assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, include_lock_state, i as usize); kernel_cpu_user_projection_at(post, include_lock_state, i as usize); } });
        assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => { if pre.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(pre, include_lock_state, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(post, include_lock_state, e); } });
        assert_maps_equal!(post_u.process_map, pre_u.process_map, p => { if pre.prc_mp.dom().contains(p) { kernel_process_user_projection_at(pre, include_lock_state, p); } if post.prc_mp.dom().contains(p) { kernel_process_user_projection_at(post, include_lock_state, p); } });
        assert_maps_equal!(post_u.container_map, pre_u.container_map.insert(cpu.owning_container, ContainerU {
            scheduler: queues.update(victim as int, queues[victim as int].skip(1)).update(cpu_id as int, queues[cpu_id as int].push(thread)), ..container
        }), c => { if pre.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(pre, include_lock_state, c); } if post.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(post, include_lock_state, c); } reveal(container_scheduler_wf); });
        assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thread, ThreadU {
            state: ThreadState::SCHEDULED { cpu_id }, ..pre_u.thread_map.spec_index(thread)
        }), t => { if pre.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(pre, include_lock_state, t); } if post.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(post, include_lock_state, t); } });
    };
}

/// Write-locking or unlocking a process's page table and IOMMU table, changing the root table and the IOTLB, replacing
/// one thread's progress, and changing the process's K-only state changes exactly those parts of the complete projection.
pub proof fn kernel_process_tables_lock_state_and_progress_changed_implies_u_step(
    pre: &KernelK, post: &KernelK, lctx: &LocalContext, process: RwLockProcessPtr, pagetable: RwLockPageTableRoot, thread: RwLockThreadPtr, lock: bool,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        typed_lock_maps_aligned(post, lctx),
        pre.prc_mp.dom().contains(process),
        !pre.prc_mp.spec_index(process).view().zombie,
        pre.prc_mp.spec_index(process).view().pagetable == pagetable,
        *post == (KernelK { pt_mp: post.pt_mp, it_mp: post.it_mp, irt: post.irt, iommu_tlb: post.iommu_tlb, prc_mp: post.prc_mp, thr_mp: post.thr_mp, ..*pre }),
        post.prc_mp.unchanged_except(&pre.prc_mp, process),
        post.prc_mp.spec_index(process).view() == (Process { state: post.prc_mp.spec_index(process).view().state, ..pre.prc_mp.spec_index(process).view() }),
        post.prc_mp.spec_index(process).view_rodata() == pre.prc_mp.spec_index(process).view_rodata(),
        post.prc_mp.spec_index(process).view_ghost() == pre.prc_mp.spec_index(process).view_ghost(),
        post.prc_mp.spec_index(process).locking_thread() == pre.prc_mp.spec_index(process).locking_thread(),
        post.prc_mp.spec_index(process).being_killed() == pre.prc_mp.spec_index(process).being_killed(),
        post.pt_mp.dom() == pre.pt_mp.dom(),
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)] pre.pt_mp.dom().contains(p) ==> {
            &&& post.pt_mp.spec_index(p).view() == pre.pt_mp.spec_index(p).view()
            &&& p != pagetable ==> post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread()
        },
        lock ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        !lock ==> post.pt_mp.spec_index(pagetable).locking_thread() is None,
        post.it_mp.dom() == pre.it_mp.dom(),
        forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)] pre.it_mp.dom().contains(p) ==> {
            &&& post.it_mp.spec_index(p).view() == pre.it_mp.spec_index(p).view()
            &&& Some(p) != pre.prc_mp.spec_index(process).view().iommu_table ==> post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread()
        },
        pre.prc_mp.spec_index(process).view().iommu_table is Some && lock
            ==> typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), pre.prc_mp.spec_index(process).view().iommu_table->Some_0, TypedLockMode::Write),
        pre.prc_mp.spec_index(process).view().iommu_table is Some && !lock ==> post.it_mp.spec_index(pre.prc_mp.spec_index(process).view().iommu_table->Some_0).locking_thread() is None,
        pre.thr_mp.dom().contains(thread),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread),
        post.thr_mp.spec_index(thread).view() == (Thread { syscall_progress: post.thr_mp.spec_index(thread).view().syscall_progress, ..pre.thr_mp.spec_index(thread).view() }),
        post.thr_mp.spec_index(thread).locking_thread() == pre.thr_mp.spec_index(thread).locking_thread(),
        post.thr_mp.spec_index(thread).being_killed() == pre.thr_mp.spec_index(thread).being_killed(),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let process_u = a.process_map[process];
            let state = if lock { LockStateU::WriteLocked } else { LockStateU::Unlocked };
            &&& a.thread_map.dom().contains(thread)
            &&& a.process_map.dom().contains(process)
            &&& process_u.pagetable is Some
            &&& (process_u.iommu_table is Some) == (pre.prc_mp.spec_index(process).view().iommu_table is Some)
            &&& a.iommu_root_table == pre.irt.view().user_view()
            &&& a.iommu_tlb == pre.iommu_tlb.view()
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                thread_map: a.thread_map.insert(thread, ThreadU { syscall_progress: post.thr_mp.spec_index(thread).view().syscall_progress.view(), ..a.thread_map[thread] }),
                process_map: a.process_map.insert(process, ProcessU {
                    pagetable: Some(PageTableU { lock_state: state, ..process_u.pagetable->Some_0 }),
                    iommu_table: match process_u.iommu_table { Some(t) => Some(PageTableU { lock_state: state, ..t }), None => None },
                    ..process_u
                }),
                iommu_root_table: post.irt.view().user_view(),
                iommu_tlb: post.iommu_tlb.view(),
                ..a
            })
        }),
{
    if lock {
        post.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
        if pre.prc_mp.spec_index(process).view().iommu_table is Some {
            post.it_mp.typed_lock_map_aligned_write_at(lctx.iommu_table_lock_map(), lctx.thread_id(), pre.prc_mp.spec_index(process).view().iommu_table->Some_0);
        }
    }
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    kernel_thread_projection_at(pre, thread); kernel_process_projection_at(pre, process);
    kernel_thread_progress_changed_implies_u_thread_map(pre, post, thread);
    kernel_process_tables_lock_state_changed_implies_u_process_map(pre, post, process, pagetable, lock);
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_container_maps_unchanged_implies_u_container_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}

pub proof fn kernel_restored_locks_implies_u_eq(pre: &KernelK, post: &KernelK, cpu: CpuId, container: Option<RwLockContainerPtr>, process: Option<RwLockProcessPtr>, thread: Option<RwLockThreadPtr>, endpoint: Option<RwLockEndpointPtr>, table: Option<RwLockPageTableRoot>)
    requires
        post.inv(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        post.irt.view().owners() == pre.irt.view().owners(),
        post.irt.view().iommu_roots() == pre.irt.view().iommu_roots(),
        post.cpu_tlb.view() == pre.cpu_tlb.view(),
        post.iommu_tlb.view() == pre.iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(pre, post),
        post.cpu_arr.unchanged_except(&pre.cpu_arr, cpu),
        (post.cpu_arr.spec_index(cpu).value.locking_thread() is Write) == (pre.cpu_arr.spec_index(cpu).value.locking_thread() is Write),
        (post.cpu_arr.spec_index(cpu).value.locking_thread() is Read) == (pre.cpu_arr.spec_index(cpu).value.locking_thread() is Read),
        post.it_mp == pre.it_mp,
        match container {
            Some(p) => {
                &&& post.ctn_mp.unchanged_except(&pre.ctn_mp, p)
                &&& (post.ctn_mp.spec_index(p).locking_thread() is Write) == (pre.ctn_mp.spec_index(p).locking_thread() is Write)
                &&& (post.ctn_mp.spec_index(p).locking_thread() is Read) == (pre.ctn_mp.spec_index(p).locking_thread() is Read)
                &&& post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u()
            },
            None => post.ctn_mp == pre.ctn_mp,
        },
        match process {
            Some(p) => {
                &&& post.prc_mp.unchanged_except(&pre.prc_mp, p)
                &&& (post.prc_mp.spec_index(p).locking_thread() is Write) == (pre.prc_mp.spec_index(p).locking_thread() is Write)
                &&& (post.prc_mp.spec_index(p).locking_thread() is Read) == (pre.prc_mp.spec_index(p).locking_thread() is Read)
            },
            None => post.prc_mp == pre.prc_mp,
        },
        match thread {
            Some(p) => {
                &&& post.thr_mp.unchanged_except(&pre.thr_mp, p)
                &&& (post.thr_mp.spec_index(p).locking_thread() is Write) == (pre.thr_mp.spec_index(p).locking_thread() is Write)
                &&& (post.thr_mp.spec_index(p).locking_thread() is Read) == (pre.thr_mp.spec_index(p).locking_thread() is Read)
            },
            None => post.thr_mp == pre.thr_mp,
        },
        match endpoint {
            Some(p) => {
                &&& post.ep_mp.unchanged_except(&pre.ep_mp, p)
                &&& (post.ep_mp.spec_index(p).locking_thread() is Write) == (pre.ep_mp.spec_index(p).locking_thread() is Write)
                &&& (post.ep_mp.spec_index(p).locking_thread() is Read) == (pre.ep_mp.spec_index(p).locking_thread() is Read)
            },
            None => post.ep_mp == pre.ep_mp,
        },
        match table {
            Some(p) => {
                &&& post.pt_mp.unchanged_except(&pre.pt_mp, p)
                &&& (post.pt_mp.spec_index(p).locking_thread() is Write) == (pre.pt_mp.spec_index(p).locking_thread() is Write)
                &&& (post.pt_mp.spec_index(p).locking_thread() is Read) == (pre.pt_mp.spec_index(p).locking_thread() is Read)
            },
            None => post.pt_mp == pre.pt_mp,
        },
    ensures kernel_k_to_kernel_u(*post) == kernel_k_to_kernel_u(*pre),
{ kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(pre, post); }

pub proof fn kernel_container_root_published_implies_u_step(
    before: &KernelK, after: &KernelK, parent: RwLockContainerPtr, child: RwLockContainerPtr, process: RwLockProcessPtr, thread: RwLockThreadPtr,
    transfer_cpu: CpuId, funding: usize, process_quota: usize, moved: Set<PagePtr>, thread_page: PagePtr, pcid_allocator: RwLockPcidAllocatorPtr,
    progress: Option<SyscallProgress>,
)
    requires
        before.inv(),
        before.ctn_mp.dom().contains(parent),
        !before.ctn_mp.dom().contains(child),
        !before.prc_mp.dom().contains(process),
        index_valid(NUM_CPUS, transfer_cpu),
        before.cpu_arr.spec_index(transfer_cpu).value.view().view().state is Off,
        before.cpu_arr.spec_index(transfer_cpu).value.view().view().owning_container == parent,
        kernel_cpu_nonlock_fields_unchanged(before.cpu_arr, after.cpu_arr),
        after.cpu_arr.spec_index(transfer_cpu).value.locking_thread() is Write,
        forall|i: CpuId| #![trigger after.cpu_arr.spec_index(i)] index_valid(NUM_CPUS, i) && i != transfer_cpu ==>
            after.cpu_arr.spec_index(i).value.locking_thread() == before.cpu_arr.spec_index(i).value.locking_thread(),
        after.ep_mp == before.ep_mp,
        after.it_mp == before.it_mp,
        after.irt == before.irt,
        after.cpu_tlb == before.cpu_tlb,
        after.iommu_tlb == before.iommu_tlb,
        after.dflt_pt == before.dflt_pt,
        after.cpu_offline_mp.dom().contains(cpu_offline_flags_ptr(child)),
        cpu_offline_requests_of(after.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(child))) == Seq::new(NUM_CPUS as nat, |i: int| false),
        forall|c: RwLockContainerPtr| #![trigger after.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(c))] before.ctn_mp.dom().contains(c) ==>
            after.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(c)) == before.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(c)),
        forall|p: RwLockCpuSetPtr| #![trigger after.cpu_set_mp.spec_index(p)] before.cpu_set_mp.dom().contains(p) ==>
            after.cpu_set_mp.spec_index(p).locking_thread() == before.cpu_set_mp.spec_index(p).locking_thread() && after.cpu_set_mp.spec_index(p).being_killed() == before.cpu_set_mp.spec_index(p).being_killed(),
        before.thr_mp.spec_index(thread).view().quota_4k >= 8 + funding,
        after.thr_mp.unchanged_except(&before.thr_mp, thread),
        after.thr_mp.spec_index(thread).being_killed() == before.thr_mp.spec_index(thread).being_killed(),
        after.thr_mp.spec_index(thread).locking_thread() == before.thr_mp.spec_index(thread).locking_thread(),
        after.thr_mp.spec_index(thread).view().state == before.thr_mp.spec_index(thread).view().state,
        after.thr_mp.spec_index(thread).view().caller == before.thr_mp.spec_index(thread).view().caller,
        after.thr_mp.spec_index(thread).view().callee == before.thr_mp.spec_index(thread).view().callee,
        after.thr_mp.spec_index(thread).view().owning_container == before.thr_mp.spec_index(thread).view().owning_container,
        after.thr_mp.spec_index(thread).view().owning_proc == before.thr_mp.spec_index(thread).view().owning_proc,
        after.thr_mp.spec_index(thread).view().last_cpu == before.thr_mp.spec_index(thread).view().last_cpu,
        after.thr_mp.spec_index(thread).view().quota_4k == before.thr_mp.spec_index(thread).view().quota_4k - 8 - funding,
        after.thr_mp.spec_index(thread).view().quota_2m == before.thr_mp.spec_index(thread).view().quota_2m - 2,
        after.thr_mp.spec_index(thread).view().quota_1g == before.thr_mp.spec_index(thread).view().quota_1g,
        after.thr_mp.spec_index(thread).view().endpoint_descriptors.view() == before.thr_mp.spec_index(thread).view().endpoint_descriptors.view(),
        after.thr_mp.spec_index(thread).view().blocking_endpoint_ptr == before.thr_mp.spec_index(thread).view().blocking_endpoint_ptr,
        after.thr_mp.spec_index(thread).view().ipc_payload == before.thr_mp.spec_index(thread).view().ipc_payload,
        after.thr_mp.spec_index(thread).view().error_code == before.thr_mp.spec_index(thread).view().error_code,
        after.thr_mp.spec_index(thread).view().trap_frame == before.thr_mp.spec_index(thread).view().trap_frame,
        after.thr_mp.spec_index(thread).view().syscall_progress.view() == progress,
        after.ctn_mp.dom() == before.ctn_mp.dom().insert(child),
        forall|c: RwLockContainerPtr| #![trigger after.ctn_mp.spec_index(c)] before.ctn_mp.dom().contains(c) ==> {
            &&& after.ctn_mp.spec_index(c).view_rodata() == before.ctn_mp.spec_index(c).view_rodata()
            &&& after.ctn_mp.spec_index(c).view_ghost().uppertree_seq == before.ctn_mp.spec_index(c).view_ghost().uppertree_seq
            &&& after.ctn_mp.spec_index(c).view_ghost().owned_threads == before.ctn_mp.spec_index(c).view_ghost().owned_threads
            &&& after.ctn_mp.spec_index(c).view_ghost().owned_processes == before.ctn_mp.spec_index(c).view_ghost().owned_processes
            &&& after.ctn_mp.spec_index(c).view_ghost().owned_endpoints == before.ctn_mp.spec_index(c).view_ghost().owned_endpoints
            &&& after.ctn_mp.spec_index(c).view_ghost().subtree_set.view() == if before.ctn_mp.spec_index(parent).view_ghost().uppertree_seq.view().push(parent).contains(c) {
                before.ctn_mp.spec_index(c).view_ghost().subtree_set.view().insert(child)
            } else { before.ctn_mp.spec_index(c).view_ghost().subtree_set.view() }
            &&& after.ctn_mp.spec_index(c).view() == (Container { children: after.ctn_mp.spec_index(c).view().children,
                owned_pages: after.ctn_mp.spec_index(c).view().owned_pages, ..before.ctn_mp.spec_index(c).view() })
            &&& after.ctn_mp.spec_index(c).view().children.view() == if c == parent { before.ctn_mp.spec_index(c).view().children.view().push(child) } else { before.ctn_mp.spec_index(c).view().children.view() }
            &&& c != parent ==> after.ctn_mp.spec_index(c).view().owned_pages == before.ctn_mp.spec_index(c).view().owned_pages
            &&& after.ctn_mp.spec_index(c).locking_thread() == before.ctn_mp.spec_index(c).locking_thread()
            &&& after.ctn_mp.spec_index(c).lock_process_owner_u() == before.ctn_mp.spec_index(c).lock_process_owner_u()
            &&& after.ctn_mp.spec_index(c).being_killed() == before.ctn_mp.spec_index(c).being_killed()
        },
        after.ctn_mp.spec_index(parent).view().owned_pages.view().subset_of(before.ctn_mp.spec_index(parent).view().owned_pages.view()),
        moved.subset_of(before.ctn_mp.spec_index(parent).view().owned_pages.view()),
        after.ctn_mp.spec_index(parent).view().owned_pages.view() == before.ctn_mp.spec_index(parent).view().owned_pages.view().difference(moved),
        after.ctn_mp.spec_index(parent).view().owned_pages.view().contains(thread_page),
        moved.contains(child),
        moved.contains(process),
        moved.contains(after.ctn_mp.spec_index(child).view_rodata().view().cpu_set),
        after.cpu_set_mp.spec_index(after.ctn_mp.spec_index(child).view_rodata().view().cpu_set).locking_thread() is Write,
        !after.cpu_set_mp.spec_index(after.ctn_mp.spec_index(child).view_rodata().view().cpu_set).being_killed(),
        after.ctn_mp.spec_index(child).locking_thread() is Write,
        after.ctn_mp.spec_index(child).lock_process_owner_u() == Some(LockOwnerId::Some(0)),
        !after.ctn_mp.spec_index(child).being_killed(),
        !after.ctn_mp.spec_index(child).view().zombie,
        after.ctn_mp.spec_index(child).view().children.view().len() == 0,
        after.ctn_mp.spec_index(child).view_ghost().uppertree_seq.view() == before.ctn_mp.spec_index(parent).view_ghost().uppertree_seq.view().push(parent),
        after.ctn_mp.spec_index(child).view_ghost().subtree_set.view().is_empty(),
        after.ctn_mp.spec_index(child).view().root_process == process,
        after.ctn_mp.spec_index(child).view_ghost().owned_processes.view() == set![process],
        after.ctn_mp.spec_index(child).view_ghost().owned_threads.view().is_empty(),
        after.ctn_mp.spec_index(child).view_ghost().owned_endpoints.view().is_empty(),
        after.ctn_mp.spec_index(child).view().owned_pages.view() == moved,
        after.ctn_mp.spec_index(child).view_rodata().view().parent == Some(parent),
        after.ctn_mp.spec_index(child).view_rodata().view().depth == before.ctn_mp.spec_index(parent).view_rodata().view().depth + 1,
        scheduler_shards_of(after.sched_mp.spec_index(after.ctn_mp.spec_index(child).view_rodata().view().scheduler)) == Seq::new(NUM_CPUS as nat, |i: int| Seq::<RwLockThreadPtr>::empty()),
        after.ctn_mp.spec_index(child).view_rodata().view().pcid_allocator == pcid_allocator,
        after.pcid_allc_mp.spec_index(pcid_allocator).view().ref_counters.spec_index(1usize) == 1,
        forall|pcid: Pcid| #![trigger after.pcid_allc_mp.spec_index(pcid_allocator).view().ref_counters.spec_index(pcid)]
            pcid_valid(pcid) && pcid != 1usize ==> after.pcid_allc_mp.spec_index(pcid_allocator).view().ref_counters.spec_index(pcid) == 0,
        after.allc_4k_mp.spec_index(after.ctn_mp.spec_index(child).view_rodata().view().allocator_ptr_4k).quota.view().view() == funding - process_quota,
        after.allc_2m_mp.spec_index(after.ctn_mp.spec_index(child).view_rodata().view().allocator_ptr_2m).quota.view().view() == 0,
        after.allc_1g_mp.spec_index(after.ctn_mp.spec_index(child).view_rodata().view().allocator_ptr_1g).quota.view().view() == 0,
        forall|p: RwLockSchedulerPtr| #![trigger after.sched_mp.spec_index(p)] before.sched_mp.dom().contains(p) ==>
            scheduler_shards_of(after.sched_mp.spec_index(p)) == scheduler_shards_of(before.sched_mp.spec_index(p)),
        forall|p: RwLockPcidAllocatorPtr| #![trigger after.pcid_allc_mp.spec_index(p)] before.pcid_allc_mp.dom().contains(p) ==>
            after.pcid_allc_mp.spec_index(p).view().ref_counters.view() == before.pcid_allc_mp.spec_index(p).view().ref_counters.view(),
        before.allc_4k_mp.dom().subset_of(after.allc_4k_mp.dom()),
        forall|p: RwLockPageAllocatorPtr| #![trigger after.allc_4k_mp.spec_index(p)] before.allc_4k_mp.dom().contains(p) ==>
            after.allc_4k_mp.spec_index(p).quota.view().view() == before.allc_4k_mp.spec_index(p).quota.view().view(),
        before.allc_2m_mp.dom().subset_of(after.allc_2m_mp.dom()),
        forall|p: RwLockPageAllocatorPtr| #![trigger after.allc_2m_mp.spec_index(p)] before.allc_2m_mp.dom().contains(p) ==>
            after.allc_2m_mp.spec_index(p).quota.view().view() == before.allc_2m_mp.spec_index(p).quota.view().view(),
        forall|p: RwLockPageAllocatorPtr| #![trigger after.allc_1g_mp.spec_index(p)] before.allc_1g_mp.dom().contains(p) ==>
            after.allc_1g_mp.spec_index(p).quota.view().view() == before.allc_1g_mp.spec_index(p).quota.view().view(),
        after.prc_mp.dom() == before.prc_mp.dom().insert(process),
        forall|p: RwLockProcessPtr| #![trigger after.prc_mp.spec_index(p)] before.prc_mp.dom().contains(p) ==> after.prc_mp.spec_index(p) == before.prc_mp.spec_index(p),
        after.prc_mp.spec_index(process).locking_thread() is Write,
        !after.prc_mp.spec_index(process).being_killed(),
        !after.prc_mp.spec_index(process).view().zombie,
        after.prc_mp.spec_index(process).view().iommu_table is None,
        after.prc_mp.spec_index(process).view_ghost().owned_pci_functions.view().is_empty(),
        after.prc_mp.spec_index(process).view().quota_4k == process_quota,
        after.prc_mp.spec_index(process).view().quota_2m == 0,
        after.prc_mp.spec_index(process).view().quota_1g == 0,
        after.prc_mp.spec_index(process).view_rodata().view().parent is None,
        after.prc_mp.spec_index(process).view_rodata().view().owning_container == child,
        after.prc_mp.spec_index(process).view_rodata().view().depth == 0,
        after.prc_mp.spec_index(process).view().children.view().len() == 0,
        after.prc_mp.spec_index(process).view().owned_threads.view().len() == 0,
        after.prc_mp.spec_index(process).view_ghost().uppertree_seq.view().len() == 0,
        after.prc_mp.spec_index(process).view_ghost().subtree_set.view().is_empty(),
        before.pt_mp.dom().subset_of(after.pt_mp.dom()),
        forall|p: RwLockPageTableRoot| #![trigger after.pt_mp.spec_index(p)] before.pt_mp.dom().contains(p) ==> after.pt_mp.spec_index(p) == before.pt_mp.spec_index(p) && after.pt_lower.view().spec_index(p) == before.pt_lower.view().spec_index(p),
        after.pt_mp.dom().contains(after.prc_mp.spec_index(process).view().pagetable),
        after.pt_mp.spec_index(after.prc_mp.spec_index(process).view().pagetable).locking_thread() is Write,
        pagetable_c(after.pt_mp, after.pt_lower.view(), after.prc_mp.spec_index(process).view().pagetable).is_empty(),
    ensures
        kernel_k_to_kernel_u(*before).thread_map.dom().contains(thread),
        kernel_k_to_kernel_u(*before).thread_map[thread].syscall_progress == before.thr_mp.spec_index(thread).view().syscall_progress.view(),
        kernel_u_container_root_published(kernel_k_to_kernel_u(*before), kernel_k_to_kernel_u(*after), parent, child, process, thread, transfer_cpu, funding, process_quota, moved, thread_page, progress),
{
    reveal(kernel_u_container_root_published); reveal(kernel_k_to_kernel_u);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    let ancestors = pre.container_map[parent].uppertree_seq.push(parent);
    assert(forall|c: RwLockContainerPtr| #![trigger post.container_map[c]] pre.container_map.dom().contains(c) ==>
        (ContainerU { children: pre.container_map[c].children, subtree_set: pre.container_map[c].subtree_set,
            owned_pages: pre.container_map[c].owned_pages, ..post.container_map[c] }) == pre.container_map[c]) by {
        reveal(container_scheduler_wf); reveal(container_pcid_allocator_wf); reveal(container_allocator_wf); reveal(container_cpu_set_wf);
    };
    assert_maps_equal!(post.process_map[process].pagetable->Some_0.mapping_1g, Map::empty());
    reveal(kernel_cpu_nonlock_fields_unchanged);
    assert_seqs_equal!(post.cpu_array == pre.cpu_array.update(transfer_cpu as int, CpuU { lock_state: LockStateU::WriteLocked, ..pre.cpu_array[transfer_cpu as int] }));
    assert_maps_equal!(post.thread_map, pre.thread_map.insert(thread, ThreadU {
        quota_4k: (pre.thread_map[thread].quota_4k - 8 - funding) as usize, quota_2m: (pre.thread_map[thread].quota_2m - 2) as usize,
        syscall_progress: progress, ..pre.thread_map[thread]
    }), p => {});
    assert_seqs_equal!(post.process_map[process].children == Seq::empty());
    assert_seqs_equal!(post.process_map[process].uppertree_seq == Seq::empty());
    assert_seqs_equal!(post.process_map[process].owned_threads == Seq::empty());
    assert_seqs_equal!(post.container_map[child].children == Seq::empty());
    assert_sets_equal!(post.container_map[child].owned_pages, moved);
    assert_sets_equal!(pre.container_map[parent].owned_pages.difference(post.container_map[parent].owned_pages), moved);
    assert_sets_equal!(post.container_map[child].free_pcids, Set::range(1usize, PCID_MAX).remove(1usize));
    reveal(process_pagetable_match);
    assert_maps_equal!(post.process_map, pre.process_map.insert(process, ProcessU {
        lock_state: LockStateU::WriteLocked, zombie: false,
        pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, did: None, mapping_4k: Map::empty(), mapping_2m: Map::empty(), mapping_1g: Map::empty() }),
        iommu_table: None, pcid: post.process_map[process].pcid, owning_container: child, owned_pci_functions: Set::empty(), quota_4k: process_quota, quota_2m: 0, quota_1g: 0,
        parent: None, children: Seq::empty(), depth: 0, uppertree_seq: Seq::empty(), subtree_set: Set::empty(), owned_threads: Seq::empty(), killed: false,
    }));
}

pub proof fn kernel_cpu_and_page_owner_changed_implies_u_step(before: &KernelK, after: &KernelK, cpu: CpuId, source: RwLockContainerPtr, target: RwLockContainerPtr, page: PagePtr)
    requires
        before.inv(),
        after.inv(),
        index_valid(NUM_CPUS, cpu),
        *after == (KernelK { pg_arr: after.pg_arr, ctn_mp: after.ctn_mp, cpu_arr: after.cpu_arr,
            cpu_set_mp: after.cpu_set_mp, sched_mp: after.sched_mp, ..*before }),
        after.cpu_arr.entries_unchanged_except(&before.cpu_arr, cpu),
        after.cpu_arr.spec_index(cpu).value.view().view().owning_container == target,
        after.cpu_arr.spec_index(cpu).value.view().view().state == before.cpu_arr.spec_index(cpu).value.view().view().state,
        after.cpu_arr.spec_index(cpu).value.view().view().current_process == before.cpu_arr.spec_index(cpu).value.view().view().current_process,
        after.cpu_arr.spec_index(cpu).value.view().view().current_thread == before.cpu_arr.spec_index(cpu).value.view().view().current_thread,
        after.cpu_arr.spec_index(cpu).value.locking_thread() is None,
        after.cpu_arr.spec_index(cpu).value.being_killed() == before.cpu_arr.spec_index(cpu).value.being_killed(),
        forall|s: RwLockSchedulerPtr| #![trigger after.sched_mp.spec_index(s)] before.sched_mp.dom().contains(s) ==>
            scheduler_shards_of(after.sched_mp.spec_index(s)) == scheduler_shards_of(before.sched_mp.spec_index(s)),
        source != target,
        before.ctn_mp.dom().contains(source),
        before.ctn_mp.dom().contains(target),
        before.ctn_mp.spec_index(source).view().owned_pages.view().contains(page),
        after.cpu_set_mp.spec_index(before.ctn_mp.spec_index(source).view_rodata().view().cpu_set).locking_thread() is None,
        after.cpu_set_mp.spec_index(before.ctn_mp.spec_index(target).view_rodata().view().cpu_set).locking_thread() is None,
        forall|p: RwLockCpuSetPtr| #![trigger after.cpu_set_mp.spec_index(p)] before.cpu_set_mp.dom().contains(p) && p != before.ctn_mp.spec_index(source).view_rodata().view().cpu_set
            && p != before.ctn_mp.spec_index(target).view_rodata().view().cpu_set ==> after.cpu_set_mp.spec_index(p).locking_thread() == before.cpu_set_mp.spec_index(p).locking_thread(),
        forall|p: RwLockCpuSetPtr| #![trigger after.cpu_set_mp.spec_index(p)] before.cpu_set_mp.dom().contains(p) ==> after.cpu_set_mp.spec_index(p).being_killed() == before.cpu_set_mp.spec_index(p).being_killed(),
        after.ctn_mp.dom() == before.ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger after.ctn_mp.spec_index(c)] before.ctn_mp.dom().contains(c) ==> {
            &&& after.ctn_mp.spec_index(c).view_rodata() == before.ctn_mp.spec_index(c).view_rodata()
            &&& after.ctn_mp.spec_index(c).view_ghost() == before.ctn_mp.spec_index(c).view_ghost()
            &&& after.ctn_mp.spec_index(c).locking_thread() == before.ctn_mp.spec_index(c).locking_thread()
            &&& after.ctn_mp.spec_index(c).lock_process_owner_u() == before.ctn_mp.spec_index(c).lock_process_owner_u()
            &&& after.ctn_mp.spec_index(c).being_killed() == before.ctn_mp.spec_index(c).being_killed()
            &&& after.ctn_mp.spec_index(c).view() == (Container { owned_pages: after.ctn_mp.spec_index(c).view().owned_pages, ..before.ctn_mp.spec_index(c).view() })
            &&& after.ctn_mp.spec_index(c).view().owned_pages.view() == if c == source { before.ctn_mp.spec_index(c).view().owned_pages.view().remove(page) }
                else if c == target { before.ctn_mp.spec_index(c).view().owned_pages.view().insert(page) } else { before.ctn_mp.spec_index(c).view().owned_pages.view() }
        },
    ensures
        kernel_u_cpu_and_page_owner_changed(kernel_k_to_kernel_u(*before), kernel_k_to_kernel_u(*after), cpu, source, target, page),
{
    reveal(kernel_u_cpu_and_page_owner_changed);
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    kernel_cpu_owner_changed_implies_u_cpu_array(before, after, cpu, target);
    kernel_page_owner_changed_implies_u_container_map(before, after, source, target, page);
    kernel_process_maps_unchanged_implies_u_process_map(before, after); kernel_thread_map_unchanged_implies_u_thread_map(before, after); kernel_endpoint_map_unchanged_implies_u_endpoint_map(before, after);
}

pub proof fn kernel_peer_scheduled_and_locks_released_implies_u_step(
    before: &KernelK, after: &KernelK, cpu_id: CpuId, caller: RwLockThreadPtr, peer: RwLockThreadPtr,
    wake_cpu: CpuId, endpoint: RwLockEndpointPtr, result: RetValueType, dequeue: bool, descriptor: Option<(RwLockThreadPtr, EndpointIdx)>,
)
    requires
        after.inv(),
        index_valid(NUM_CPUS, cpu_id),
        index_valid(NUM_CPUS, wake_cpu),
        before.thr_mp.dom().contains(caller),
        before.thr_mp.dom().contains(peer),
        caller != peer,
        before.ep_mp.dom().contains(endpoint),
        !(before.thr_mp.spec_index(peer).view().state is SCHEDULED),
        descriptor matches Some((receiver, index)) ==> (receiver == caller || receiver == peer) && edp_idx_valid(index),
        *after == (KernelK { cpu_arr: after.cpu_arr, prc_mp: after.prc_mp, thr_mp: after.thr_mp, ep_mp: after.ep_mp, sched_mp: after.sched_mp, ..*before }),
        kernel_cpu_nonlock_fields_unchanged(before.cpu_arr, after.cpu_arr),
        kernel_process_nonlock_fields_unchanged(before.prc_mp, after.prc_mp),
        after.cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        forall|i: CpuId| #![trigger after.cpu_arr.spec_index(i)] index_valid(NUM_CPUS, i) && i != cpu_id ==>
            after.cpu_arr.spec_index(i).value.locking_thread() == before.cpu_arr.spec_index(i).value.locking_thread(),
        forall|p: RwLockProcessPtr| #![trigger after.prc_mp.spec_index(p)] before.prc_mp.dom().contains(p) ==>
            after.prc_mp.spec_index(p).locking_thread() == before.prc_mp.spec_index(p).locking_thread(),
        after.thr_mp.dom() == before.thr_mp.dom(),
        forall|t: RwLockThreadPtr| #![trigger after.thr_mp.spec_index(t)] before.thr_mp.dom().contains(t) ==> {
            &&& after.thr_mp.spec_index(t).view().state == if t == peer { ThreadState::SCHEDULED { cpu_id: wake_cpu } } else { before.thr_mp.spec_index(t).view().state }
            &&& after.thr_mp.spec_index(t).view().caller == before.thr_mp.spec_index(t).view().caller
            &&& after.thr_mp.spec_index(t).view().callee == before.thr_mp.spec_index(t).view().callee
            &&& after.thr_mp.spec_index(t).view().owning_container == before.thr_mp.spec_index(t).view().owning_container
            &&& after.thr_mp.spec_index(t).view().owning_proc == before.thr_mp.spec_index(t).view().owning_proc
            &&& after.thr_mp.spec_index(t).view().last_cpu == before.thr_mp.spec_index(t).view().last_cpu
            &&& after.thr_mp.spec_index(t).view().quota_4k == before.thr_mp.spec_index(t).view().quota_4k
            &&& after.thr_mp.spec_index(t).view().quota_2m == before.thr_mp.spec_index(t).view().quota_2m
            &&& after.thr_mp.spec_index(t).view().quota_1g == before.thr_mp.spec_index(t).view().quota_1g
            &&& after.thr_mp.spec_index(t).view().endpoint_descriptors.view() == if descriptor is Some && t == descriptor->Some_0.0 {
                before.thr_mp.spec_index(t).view().endpoint_descriptors.view().update(descriptor->Some_0.1 as int, Some(endpoint))
            } else { before.thr_mp.spec_index(t).view().endpoint_descriptors.view() }
            &&& after.thr_mp.spec_index(t).view().blocking_endpoint_ptr == if t == peer { None } else { before.thr_mp.spec_index(t).view().blocking_endpoint_ptr }
            &&& after.thr_mp.spec_index(t).view().ipc_payload == if t == peer { IPCPayLoad::Empty } else { before.thr_mp.spec_index(t).view().ipc_payload }
            &&& after.thr_mp.spec_index(t).view().error_code == if t == peer { Some(result) } else { before.thr_mp.spec_index(t).view().error_code }
            &&& after.thr_mp.spec_index(t).view().trap_frame == before.thr_mp.spec_index(t).view().trap_frame
            &&& t != caller ==> after.thr_mp.spec_index(t).view().syscall_progress == before.thr_mp.spec_index(t).view().syscall_progress
            &&& after.thr_mp.spec_index(t).being_killed() == before.thr_mp.spec_index(t).being_killed()
            &&& if t == caller || t == peer { after.thr_mp.spec_index(t).locking_thread() is None }
                else { after.thr_mp.spec_index(t).locking_thread() == before.thr_mp.spec_index(t).locking_thread() }
        },
        after.ep_mp.dom() == before.ep_mp.dom(),
        forall|e: RwLockEndpointPtr| #![trigger after.ep_mp.spec_index(e)] before.ep_mp.dom().contains(e) ==> {
            &&& after.ep_mp.spec_index(e).view().queue.view() == if e == endpoint && dequeue { before.ep_mp.spec_index(e).view().queue.view().skip(1) } else { before.ep_mp.spec_index(e).view().queue.view() }
            &&& after.ep_mp.spec_index(e).view().queue_state == before.ep_mp.spec_index(e).view().queue_state
            &&& after.ep_mp.spec_index(e).view().owning_container == before.ep_mp.spec_index(e).view().owning_container
            &&& after.ep_mp.spec_index(e).view().owning_threads.view() == if e == endpoint && descriptor is Some { before.ep_mp.spec_index(e).view().owning_threads.view().insert(descriptor->Some_0) } else { before.ep_mp.spec_index(e).view().owning_threads.view() }
            &&& after.ep_mp.spec_index(e).being_killed() == before.ep_mp.spec_index(e).being_killed()
            &&& if e == endpoint { after.ep_mp.spec_index(e).locking_thread() is None } else { after.ep_mp.spec_index(e).locking_thread() == before.ep_mp.spec_index(e).locking_thread() }
        },
        after.sched_mp.dom() == before.sched_mp.dom(),
        forall|s: RwLockSchedulerPtr| #![trigger after.sched_mp.spec_index(s)] before.sched_mp.dom().contains(s) ==>
            scheduler_shards_of(after.sched_mp.spec_index(s)) == if s == before.ctn_mp.spec_index(before.thr_mp.spec_index(peer).view().owning_container).view_rodata().view().scheduler {
                scheduler_shards_of(before.sched_mp.spec_index(s)).update(wake_cpu as int, scheduler_shards_of(before.sched_mp.spec_index(s))[wake_cpu as int].push(peer))
            } else { scheduler_shards_of(before.sched_mp.spec_index(s)) },
    ensures
        kernel_k_to_kernel_u(*before) != kernel_k_to_kernel_u(*after),
        kernel_k_to_kernel_u(*before).thread_map.dom().contains(caller),
        kernel_k_to_kernel_u(*before).thread_map[caller].syscall_progress == before.thr_mp.spec_index(caller).view().syscall_progress.view(),
        ({
            let pre = kernel_k_to_kernel_u(*before);
            let post = kernel_k_to_kernel_u(*after);
            let threads = match descriptor {
                Some((receiver, index)) => pre.thread_map.insert(receiver, ThreadU { endpoint_descriptors: pre.thread_map[receiver].endpoint_descriptors.update(index as int, Some(endpoint)), ..pre.thread_map[receiver] }),
                None => pre.thread_map,
            };
            let container = pre.thread_map[peer].owning_container;
            post == (KernelU {
                cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..pre.cpu_array[cpu_id as int] }),
                container_map: pre.container_map.insert(container, ContainerU {
                    scheduler: pre.container_map[container].scheduler.update(wake_cpu as int, pre.container_map[container].scheduler[wake_cpu as int].push(peer)),
                    ..pre.container_map[container]
                }),
                thread_map: threads.insert(caller, ThreadU {
                    lock_state: LockStateU::Unlocked, syscall_progress: after.thr_mp.spec_index(caller).view().syscall_progress.view(), ..threads[caller]
                }).insert(peer, ThreadU {
                    lock_state: LockStateU::Unlocked, state: ThreadState::SCHEDULED { cpu_id: wake_cpu }, blocking_endpoint_ptr: None, ipc_payload: IPCPayLoad::Empty, error_code: Some(result), ..threads[peer]
                }),
                endpoint_map: pre.endpoint_map.insert(endpoint, EndpointU { lock_state: LockStateU::Unlocked,
                    queue: if dequeue { pre.endpoint_map[endpoint].queue.skip(1) } else { pre.endpoint_map[endpoint].queue },
                    owning_threads: if descriptor is Some { pre.endpoint_map[endpoint].owning_threads.insert(descriptor->Some_0) } else { pre.endpoint_map[endpoint].owning_threads }, ..pre.endpoint_map[endpoint]
                }),
                ..pre
            })
        }),
{
    kernel_peer_scheduled_and_locks_released_implies_u_cpu_array(before, after, cpu_id, caller, peer, wake_cpu, endpoint, result, dequeue, descriptor);
    kernel_peer_scheduled_and_locks_released_implies_u_process_map(before, after, cpu_id, caller, peer, wake_cpu, endpoint, result, dequeue, descriptor);
    kernel_peer_scheduled_and_locks_released_implies_u_container_map(before, after, cpu_id, caller, peer, wake_cpu, endpoint, result, dequeue, descriptor);
    kernel_peer_scheduled_and_locks_released_implies_u_thread_map(before, after, cpu_id, caller, peer, wake_cpu, endpoint, result, dequeue, descriptor);
    reveal(kernel_k_to_kernel_u);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    assert_maps_equal!(post.endpoint_map, pre.endpoint_map.insert(endpoint, EndpointU { lock_state: LockStateU::Unlocked,
        queue: if dequeue { pre.endpoint_map[endpoint].queue.skip(1) } else { pre.endpoint_map[endpoint].queue },
        owning_threads: if descriptor is Some { pre.endpoint_map[endpoint].owning_threads.insert(descriptor->Some_0) } else { pre.endpoint_map[endpoint].owning_threads }, ..pre.endpoint_map[endpoint]
    }), e => {});
}

/// The peer-scheduled transition projects to the cpu array with only `cpu_id` unlocked.
proof fn kernel_peer_scheduled_and_locks_released_implies_u_cpu_array(
    before: &KernelK, after: &KernelK, cpu_id: CpuId, caller: RwLockThreadPtr, peer: RwLockThreadPtr,
    wake_cpu: CpuId, endpoint: RwLockEndpointPtr, result: RetValueType, dequeue: bool, descriptor: Option<(RwLockThreadPtr, EndpointIdx)>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        kernel_cpu_nonlock_fields_unchanged(before.cpu_arr, after.cpu_arr),
        after.cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        forall|i: CpuId| #![trigger after.cpu_arr.spec_index(i)] index_valid(NUM_CPUS, i) && i != cpu_id ==>
            after.cpu_arr.spec_index(i).value.locking_thread() == before.cpu_arr.spec_index(i).value.locking_thread(),
    ensures
        ({
            let pre = kernel_k_to_kernel_u(*before);
            kernel_k_to_kernel_u(*after).cpu_array == pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..pre.cpu_array[cpu_id as int] })
        }),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after); reveal(kernel_cpu_nonlock_fields_unchanged);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    assert_seqs_equal!(post.cpu_array == pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..pre.cpu_array[cpu_id as int] }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(before, i as usize); kernel_cpu_projection_at(after, i as usize); }
    });
}

/// The peer-scheduled transition leaves the process map projection unchanged.
proof fn kernel_peer_scheduled_and_locks_released_implies_u_process_map(
    before: &KernelK, after: &KernelK, cpu_id: CpuId, caller: RwLockThreadPtr, peer: RwLockThreadPtr,
    wake_cpu: CpuId, endpoint: RwLockEndpointPtr, result: RetValueType, dequeue: bool, descriptor: Option<(RwLockThreadPtr, EndpointIdx)>,
)
    requires
        *after == (KernelK { cpu_arr: after.cpu_arr, prc_mp: after.prc_mp, thr_mp: after.thr_mp, ep_mp: after.ep_mp, sched_mp: after.sched_mp, ..*before }),
        kernel_process_nonlock_fields_unchanged(before.prc_mp, after.prc_mp),
        forall|p: RwLockProcessPtr| #![trigger after.prc_mp.spec_index(p)] before.prc_mp.dom().contains(p) ==>
            after.prc_mp.spec_index(p).locking_thread() == before.prc_mp.spec_index(p).locking_thread(),
    ensures kernel_k_to_kernel_u(*after).process_map == kernel_k_to_kernel_u(*before).process_map,
{
    reveal(kernel_k_to_kernel_u); reveal(kernel_process_nonlock_fields_unchanged);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    assert_maps_equal!(post.process_map, pre.process_map, p => {});
}

/// The peer-scheduled transition projects to the container map with `peer` pushed on shard `wake_cpu` of its container's scheduler.
proof fn kernel_peer_scheduled_and_locks_released_implies_u_container_map(
    before: &KernelK, after: &KernelK, cpu_id: CpuId, caller: RwLockThreadPtr, peer: RwLockThreadPtr,
    wake_cpu: CpuId, endpoint: RwLockEndpointPtr, result: RetValueType, dequeue: bool, descriptor: Option<(RwLockThreadPtr, EndpointIdx)>,
)
    requires
        container_thread_wf(after.ctn_mp, after.thr_mp),
        container_scheduler_wf(after.ctn_mp, after.sched_mp),
        index_valid(NUM_CPUS, wake_cpu),
        before.thr_mp.dom().contains(peer),
        *after == (KernelK { cpu_arr: after.cpu_arr, prc_mp: after.prc_mp, thr_mp: after.thr_mp, ep_mp: after.ep_mp, sched_mp: after.sched_mp, ..*before }),
        after.thr_mp.dom() == before.thr_mp.dom(),
        after.thr_mp.spec_index(peer).view().owning_container == before.thr_mp.spec_index(peer).view().owning_container,
        after.sched_mp.dom() == before.sched_mp.dom(),
        forall|s: RwLockSchedulerPtr| #![trigger after.sched_mp.spec_index(s)] before.sched_mp.dom().contains(s) ==>
            scheduler_shards_of(after.sched_mp.spec_index(s)) == if s == before.ctn_mp.spec_index(before.thr_mp.spec_index(peer).view().owning_container).view_rodata().view().scheduler {
                scheduler_shards_of(before.sched_mp.spec_index(s)).update(wake_cpu as int, scheduler_shards_of(before.sched_mp.spec_index(s))[wake_cpu as int].push(peer))
            } else { scheduler_shards_of(before.sched_mp.spec_index(s)) },
    ensures
        ({
            let pre = kernel_k_to_kernel_u(*before);
            let container = pre.thread_map[peer].owning_container;
            kernel_k_to_kernel_u(*after).container_map == pre.container_map.insert(container, ContainerU {
                scheduler: pre.container_map[container].scheduler.update(wake_cpu as int, pre.container_map[container].scheduler[wake_cpu as int].push(peer)), ..pre.container_map[container]
            })
        }),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after); kernel_thread_projection_at(before, peer);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    let container = pre.thread_map[peer].owning_container;
    assert_maps_equal!(post.container_map, pre.container_map.insert(container, ContainerU {
        scheduler: pre.container_map[container].scheduler.update(wake_cpu as int, pre.container_map[container].scheduler[wake_cpu as int].push(peer)), ..pre.container_map[container]
    }), p => {
        if before.ctn_mp.dom().contains(p) { kernel_container_projection_at(before, p); kernel_container_projection_at(after, p); }
        if before.ctn_mp.dom().contains(container) { kernel_container_projection_at(before, container); }
        reveal(container_thread_wf); reveal(container_scheduler_wf);
    });
}

/// The peer-scheduled transition projects to the thread map with the descriptor installed, `caller` unlocked, and `peer` scheduled on `wake_cpu`.
proof fn kernel_peer_scheduled_and_locks_released_implies_u_thread_map(
    before: &KernelK, after: &KernelK, cpu_id: CpuId, caller: RwLockThreadPtr, peer: RwLockThreadPtr,
    wake_cpu: CpuId, endpoint: RwLockEndpointPtr, result: RetValueType, dequeue: bool, descriptor: Option<(RwLockThreadPtr, EndpointIdx)>,
)
    requires
        before.thr_mp.dom().contains(caller),
        before.thr_mp.dom().contains(peer),
        caller != peer,
        descriptor matches Some((receiver, index)) ==> (receiver == caller || receiver == peer) && edp_idx_valid(index),
        after.thr_mp.dom() == before.thr_mp.dom(),
        forall|t: RwLockThreadPtr| #![trigger after.thr_mp.spec_index(t)] before.thr_mp.dom().contains(t) ==> {
            &&& after.thr_mp.spec_index(t).view().state == if t == peer { ThreadState::SCHEDULED { cpu_id: wake_cpu } } else { before.thr_mp.spec_index(t).view().state }
            &&& after.thr_mp.spec_index(t).view().caller == before.thr_mp.spec_index(t).view().caller
            &&& after.thr_mp.spec_index(t).view().callee == before.thr_mp.spec_index(t).view().callee
            &&& after.thr_mp.spec_index(t).view().owning_container == before.thr_mp.spec_index(t).view().owning_container
            &&& after.thr_mp.spec_index(t).view().owning_proc == before.thr_mp.spec_index(t).view().owning_proc
            &&& after.thr_mp.spec_index(t).view().last_cpu == before.thr_mp.spec_index(t).view().last_cpu
            &&& after.thr_mp.spec_index(t).view().quota_4k == before.thr_mp.spec_index(t).view().quota_4k
            &&& after.thr_mp.spec_index(t).view().quota_2m == before.thr_mp.spec_index(t).view().quota_2m
            &&& after.thr_mp.spec_index(t).view().quota_1g == before.thr_mp.spec_index(t).view().quota_1g
            &&& after.thr_mp.spec_index(t).view().endpoint_descriptors.view() == if descriptor is Some && t == descriptor->Some_0.0 {
                before.thr_mp.spec_index(t).view().endpoint_descriptors.view().update(descriptor->Some_0.1 as int, Some(endpoint))
            } else { before.thr_mp.spec_index(t).view().endpoint_descriptors.view() }
            &&& after.thr_mp.spec_index(t).view().blocking_endpoint_ptr == if t == peer { None } else { before.thr_mp.spec_index(t).view().blocking_endpoint_ptr }
            &&& after.thr_mp.spec_index(t).view().ipc_payload == if t == peer { IPCPayLoad::Empty } else { before.thr_mp.spec_index(t).view().ipc_payload }
            &&& after.thr_mp.spec_index(t).view().error_code == if t == peer { Some(result) } else { before.thr_mp.spec_index(t).view().error_code }
            &&& after.thr_mp.spec_index(t).view().trap_frame == before.thr_mp.spec_index(t).view().trap_frame
            &&& t != caller ==> after.thr_mp.spec_index(t).view().syscall_progress == before.thr_mp.spec_index(t).view().syscall_progress
            &&& after.thr_mp.spec_index(t).being_killed() == before.thr_mp.spec_index(t).being_killed()
            &&& if t == caller || t == peer { after.thr_mp.spec_index(t).locking_thread() is None }
                else { after.thr_mp.spec_index(t).locking_thread() == before.thr_mp.spec_index(t).locking_thread() }
        },
    ensures
        ({
            let pre = kernel_k_to_kernel_u(*before);
            let threads = match descriptor {
                Some((receiver, index)) => pre.thread_map.insert(receiver, ThreadU { endpoint_descriptors: pre.thread_map[receiver].endpoint_descriptors.update(index as int, Some(endpoint)), ..pre.thread_map[receiver] }),
                None => pre.thread_map,
            };
            kernel_k_to_kernel_u(*after).thread_map == threads.insert(caller, ThreadU {
                lock_state: LockStateU::Unlocked, syscall_progress: after.thr_mp.spec_index(caller).view().syscall_progress.view(), ..threads[caller]
            }).insert(peer, ThreadU {
                lock_state: LockStateU::Unlocked, state: ThreadState::SCHEDULED { cpu_id: wake_cpu }, blocking_endpoint_ptr: None, ipc_payload: IPCPayLoad::Empty, error_code: Some(result), ..threads[peer]
            })
        }),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    let threads = match descriptor {
        Some((receiver, index)) => pre.thread_map.insert(receiver, ThreadU { endpoint_descriptors: pre.thread_map[receiver].endpoint_descriptors.update(index as int, Some(endpoint)), ..pre.thread_map[receiver] }),
        None => pre.thread_map,
    };
    assert_maps_equal!(post.thread_map, threads.insert(caller, ThreadU {
        lock_state: LockStateU::Unlocked, syscall_progress: after.thr_mp.spec_index(caller).view().syscall_progress.view(), ..threads[caller]
    }).insert(peer, ThreadU {
        lock_state: LockStateU::Unlocked, state: ThreadState::SCHEDULED { cpu_id: wake_cpu }, blocking_endpoint_ptr: None, ipc_payload: IPCPayLoad::Empty, error_code: Some(result), ..threads[peer]
    }), t => { if before.thr_mp.dom().contains(t) { kernel_thread_projection_at(before, t); kernel_thread_projection_at(after, t); } });
}

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

/// Dequeuing under held cpu/process/thread locks leaves the container projection unchanged.
#[verifier::spinoff_prover]
proof fn kernel_thread_dequeued_implies_u_container_map(before: &KernelK, entry: &KernelK, after: &KernelK)
    requires
        kernel_container_nonlock_fields_and_quotas_unchanged(before, entry),
        *after == (KernelK { thr_mp: after.thr_mp, ep_mp: after.ep_mp, ..*entry }),
        forall|p: RwLockContainerPtr| #![trigger after.ctn_mp.spec_index(p)] before.ctn_mp.dom().contains(p) && after.ctn_mp.dom().contains(p) ==> {
            &&& after.ctn_mp.spec_index(p).locking_thread() == before.ctn_mp.spec_index(p).locking_thread()
            &&& after.ctn_mp.spec_index(p).lock_process_owner_u() == before.ctn_mp.spec_index(p).lock_process_owner_u()
        },
    ensures kernel_k_to_kernel_u(*after).container_map == kernel_k_to_kernel_u(*before).container_map,
{
    kernel_u_domains_projection(after); kernel_u_domains_projection(before);
    assert_maps_equal!(kernel_k_to_kernel_u(*after).container_map, kernel_k_to_kernel_u(*before).container_map, p => {
        if after.ctn_mp.dom().contains(p) { kernel_container_projection_at(after, p); } if before.ctn_mp.dom().contains(p) { kernel_container_projection_at(before, p); }
        reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
    });
}

/// A process map with unchanged nonlock fields and lock states projects to the same process map.
#[verifier::spinoff_prover]
proof fn kernel_thread_dequeued_implies_u_process_map(before: &KernelK, entry: &KernelK, after: &KernelK, lctx: &LocalContext)
    requires
        process_pagetable_match(after.prc_mp, after.pt_mp),
        process_iommu_table_match(after.prc_mp, after.it_mp),
        typed_lock_maps_aligned(after, lctx),
        kernel_cpu_process_thread_nonlock_fields_unchanged(before, entry),
        *after == (KernelK { thr_mp: after.thr_mp, ep_mp: after.ep_mp, ..*entry }),
        forall|p: RwLockProcessPtr| #![trigger after.prc_mp.spec_index(p)] before.prc_mp.dom().contains(p) && after.prc_mp.dom().contains(p) ==>
            after.prc_mp.spec_index(p).locking_thread() == before.prc_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger after.pt_mp.spec_index(p)] before.pt_mp.dom().contains(p) && after.pt_mp.dom().contains(p) ==>
            after.pt_mp.spec_index(p).locking_thread() == before.pt_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger after.it_mp.spec_index(p)] before.it_mp.dom().contains(p) && after.it_mp.dom().contains(p) ==>
            after.it_mp.spec_index(p).locking_thread() == before.it_mp.spec_index(p).locking_thread(),
    ensures
        kernel_k_to_kernel_u(*after).process_map == kernel_k_to_kernel_u(*before).process_map,
{
    kernel_u_domains_projection(after); kernel_u_domains_projection(before);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    assert_maps_equal!(post.process_map, pre.process_map, p => {
        if after.prc_mp.dom().contains(p) { kernel_process_projection_at(after, p); } if before.prc_mp.dom().contains(p) { kernel_process_projection_at(before, p); }
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged);
        reveal(process_pagetable_match); reveal(process_iommu_table_match); reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
    });
}

/// Write-locking the cpu and both threads and dequeuing the channel head into transit with the running thread projects to that user
/// step; the channel ends write-locked exactly when `channel_held`.
#[verifier::spinoff_prover]
pub proof fn kernel_thread_dequeued_and_locks_changed_implies_u_step(
    before: &KernelK, entry: &KernelK, after: &KernelK, lctx: &LocalContext, cpu_id: CpuId,
    current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr, channel_endpoint_ptr: RwLockEndpointPtr, channel_held: bool,
)
    requires
        after.inv(),
        typed_lock_maps_aligned(after, lctx),
        before.cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        entry.thr_mp.dom().contains(current_thread_ptr),
        entry.thr_mp.dom().contains(peer_thread_ptr),
        current_thread_ptr != peer_thread_ptr,
        kernel_cpu_process_thread_nonlock_fields_unchanged(before, entry),
        kernel_container_nonlock_fields_and_quotas_unchanged(before, entry),
        kernel_endpoint_nonlock_fields_unchanged(before.ep_mp, entry.ep_mp),
        before.irt.view().owners() == entry.irt.view().owners(),
        before.irt.view().iommu_roots() == entry.irt.view().iommu_roots(),
        before.cpu_tlb.view() == entry.cpu_tlb.view(),
        before.iommu_tlb.view() == entry.iommu_tlb.view(),
        *after == (KernelK { thr_mp: after.thr_mp, ep_mp: after.ep_mp, ..*entry }),
        after.thr_mp.dom() == entry.thr_mp.dom(),
        forall|t: RwLockThreadPtr| #![trigger after.thr_mp.spec_index(t)] entry.thr_mp.dom().contains(t) && t != current_thread_ptr && t != peer_thread_ptr ==>
            after.thr_mp.spec_index(t) == entry.thr_mp.spec_index(t),
        after.thr_mp.spec_index(current_thread_ptr).view() == (Thread {
            syscall_progress: after.thr_mp.spec_index(current_thread_ptr).view().syscall_progress, ..entry.thr_mp.spec_index(current_thread_ptr).view()
        }),
        after.thr_mp.spec_index(current_thread_ptr).being_killed() == entry.thr_mp.spec_index(current_thread_ptr).being_killed(),
        after.thr_mp.spec_index(peer_thread_ptr).view().non_ipc_fields_unchanged(&entry.thr_mp.spec_index(peer_thread_ptr).view()),
        after.thr_mp.spec_index(peer_thread_ptr).view().state == (ThreadState::IPC_TRANSIT { partner: current_thread_ptr, wait: if entry.thr_mp.spec_index(peer_thread_ptr).view().state is SENDING { IpcWait::Send } else { IpcWait::Receive } }),
        after.thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr is None,
        after.thr_mp.spec_index(peer_thread_ptr).view().caller == entry.thr_mp.spec_index(peer_thread_ptr).view().caller,
        after.thr_mp.spec_index(peer_thread_ptr).view().callee == entry.thr_mp.spec_index(peer_thread_ptr).view().callee,
        after.thr_mp.spec_index(peer_thread_ptr).view().ipc_payload == entry.thr_mp.spec_index(peer_thread_ptr).view().ipc_payload,
        after.thr_mp.spec_index(peer_thread_ptr).view().error_code == entry.thr_mp.spec_index(peer_thread_ptr).view().error_code,
        after.thr_mp.spec_index(peer_thread_ptr).view().trap_frame == entry.thr_mp.spec_index(peer_thread_ptr).view().trap_frame,
        after.thr_mp.spec_index(peer_thread_ptr).view().syscall_progress == entry.thr_mp.spec_index(peer_thread_ptr).view().syscall_progress,
        after.thr_mp.spec_index(peer_thread_ptr).being_killed() == entry.thr_mp.spec_index(peer_thread_ptr).being_killed(),
        after.ep_mp.unchanged_except(&entry.ep_mp, channel_endpoint_ptr),
        after.ep_mp.spec_index(channel_endpoint_ptr).view() == (Endpoint { queue: after.ep_mp.spec_index(channel_endpoint_ptr).view().queue, ..entry.ep_mp.spec_index(channel_endpoint_ptr).view() }),
        after.ep_mp.spec_index(channel_endpoint_ptr).view().queue.view() == entry.ep_mp.spec_index(channel_endpoint_ptr).view().queue.view().skip(1),
        after.ep_mp.spec_index(channel_endpoint_ptr).being_killed() == entry.ep_mp.spec_index(channel_endpoint_ptr).being_killed(),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        forall|p: RwLockContainerPtr| #![trigger after.ctn_mp.spec_index(p)] before.ctn_mp.dom().contains(p) && after.ctn_mp.dom().contains(p) ==> {
            &&& after.ctn_mp.spec_index(p).locking_thread() == before.ctn_mp.spec_index(p).locking_thread()
            &&& after.ctn_mp.spec_index(p).lock_process_owner_u() == before.ctn_mp.spec_index(p).lock_process_owner_u()
        },
        forall|p: RwLockProcessPtr| #![trigger after.prc_mp.spec_index(p)] before.prc_mp.dom().contains(p) && after.prc_mp.dom().contains(p) ==>
            after.prc_mp.spec_index(p).locking_thread() == before.prc_mp.spec_index(p).locking_thread(),
        forall|p: RwLockThreadPtr| #![trigger after.thr_mp.spec_index(p)] before.thr_mp.dom().contains(p) && after.thr_mp.dom().contains(p) && p != current_thread_ptr && p != peer_thread_ptr ==>
            after.thr_mp.spec_index(p).locking_thread() == before.thr_mp.spec_index(p).locking_thread(),
        forall|p: RwLockEndpointPtr| #![trigger after.ep_mp.spec_index(p)] before.ep_mp.dom().contains(p) && after.ep_mp.dom().contains(p) && !(channel_held && p == channel_endpoint_ptr) ==>
            after.ep_mp.spec_index(p).locking_thread() == before.ep_mp.spec_index(p).locking_thread(),
        channel_held ==> typed_lock_map_contains_mode(lctx.endpoint_lock_map(), channel_endpoint_ptr, TypedLockMode::Write),
        forall|p: RwLockPageTableRoot| #![trigger after.pt_mp.spec_index(p)] before.pt_mp.dom().contains(p) && after.pt_mp.dom().contains(p) ==>
            after.pt_mp.spec_index(p).locking_thread() == before.pt_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger after.it_mp.spec_index(p)] before.it_mp.dom().contains(p) && after.it_mp.dom().contains(p) ==>
            after.it_mp.spec_index(p).locking_thread() == before.it_mp.spec_index(p).locking_thread(),
        forall|i: CpuId| #![trigger after.cpu_arr.spec_index(i)] index_valid(NUM_CPUS, i) && i != cpu_id ==>
            after.cpu_arr.spec_index(i).value.locking_thread() == before.cpu_arr.spec_index(i).value.locking_thread(),
    ensures
        kernel_k_to_kernel_u(*before) != kernel_k_to_kernel_u(*after),
        kernel_k_to_kernel_u(*before).thread_map.dom().contains(current_thread_ptr),
        kernel_k_to_kernel_u(*before).thread_map[current_thread_ptr].syscall_progress == entry.thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view(),
        ({
            let pre = kernel_k_to_kernel_u(*before);
            let post = kernel_k_to_kernel_u(*after);
            post == (KernelU {
                cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, ..pre.cpu_array[cpu_id as int] }),
                thread_map: pre.thread_map.insert(current_thread_ptr, ThreadU {
                    lock_state: LockStateU::WriteLocked, syscall_progress: after.thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view(), ..pre.thread_map[current_thread_ptr]
                }).insert(peer_thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, blocking_endpoint_ptr: None,
                    state: ThreadState::IPC_TRANSIT { partner: current_thread_ptr, wait: if pre.thread_map[peer_thread_ptr].state is SENDING { IpcWait::Send } else { IpcWait::Receive } }, ..pre.thread_map[peer_thread_ptr] }),
                endpoint_map: pre.endpoint_map.insert(channel_endpoint_ptr, EndpointU {
                    lock_state: if channel_held { LockStateU::WriteLocked } else { pre.endpoint_map[channel_endpoint_ptr].lock_state }, queue: pre.endpoint_map[channel_endpoint_ptr].queue.skip(1),
                    ..pre.endpoint_map[channel_endpoint_ptr]
                }),
                ..pre
            })
        }),
{
    assert(entry.dflt_pt == before.dflt_pt) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    if before.thr_mp.dom().contains(current_thread_ptr) { kernel_thread_projection_at(before, current_thread_ptr); }
    if before.thr_mp.dom().contains(peer_thread_ptr) { kernel_thread_projection_at(before, peer_thread_ptr); }
    if before.ep_mp.dom().contains(channel_endpoint_ptr) { kernel_endpoint_projection_at(before, channel_endpoint_ptr); }
    if index_valid(NUM_CPUS, cpu_id) { kernel_cpu_projection_at(before, cpu_id); }
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    after.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), current_thread_ptr);
    after.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), peer_thread_ptr);
    if channel_held { after.ep_mp.typed_lock_map_aligned_write_at(lctx.endpoint_lock_map(), lctx.thread_id(), channel_endpoint_ptr); }
    reveal(LockedArray::typed_lock_map_aligned);
    assert(post.iommu_root_table == pre.iommu_root_table) by { reveal(IommuRootTable::user_view); };
    assert(pre.thread_map.dom().contains(current_thread_ptr) && pre.thread_map[current_thread_ptr].syscall_progress == entry.thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view()) by {
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
    };
    assert_seqs_equal!(post.cpu_array == pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, ..pre.cpu_array[cpu_id as int] }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(before, i as usize); kernel_cpu_projection_at(after, i as usize); }
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
    });
    assert_maps_equal!(post.thread_map, pre.thread_map.insert(current_thread_ptr, ThreadU {
        lock_state: LockStateU::WriteLocked, syscall_progress: after.thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view(), ..pre.thread_map[current_thread_ptr]
    }).insert(peer_thread_ptr, ThreadU { lock_state: LockStateU::WriteLocked, blocking_endpoint_ptr: None,
        state: ThreadState::IPC_TRANSIT { partner: current_thread_ptr, wait: if pre.thread_map[peer_thread_ptr].state is SENDING { IpcWait::Send } else { IpcWait::Receive } }, ..pre.thread_map[peer_thread_ptr] }), p => {
        if before.thr_mp.dom().contains(p) { kernel_thread_projection_at(before, p); } if after.thr_mp.dom().contains(p) { kernel_thread_projection_at(after, p); }
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
    });
    assert_maps_equal!(post.endpoint_map, pre.endpoint_map.insert(channel_endpoint_ptr, EndpointU {
        lock_state: if channel_held { LockStateU::WriteLocked } else { pre.endpoint_map[channel_endpoint_ptr].lock_state }, queue: pre.endpoint_map[channel_endpoint_ptr].queue.skip(1),
        ..pre.endpoint_map[channel_endpoint_ptr]
    }), p => {
        if before.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(before, p); } if after.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(after, p); }
        reveal(kernel_endpoint_nonlock_fields_unchanged);
    });
    kernel_thread_dequeued_implies_u_container_map(before, entry, after);
    kernel_thread_dequeued_implies_u_process_map(before, entry, after, lctx);
}

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
            let empty_table = PageTableU { lock_state: LockStateU::WriteLocked, did: None, mapping_4k: Map::empty(), mapping_2m: Map::empty(), mapping_1g: Map::empty() };
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
    reveal(kernel_k_to_kernel_u);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    let ancestors = pre.process_map[parent].uppertree_seq.push(parent);
    let cost: usize = if iommu is Some { 5 } else { 3 };
    after.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), child);
    after.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), table);
    if let Some(t) = iommu { after.it_mp.typed_lock_map_aligned_write_at(lctx.iommu_table_lock_map(), lctx.thread_id(), t); }
    assert_seqs_equal!(post.cpu_array == pre.cpu_array);
    assert_maps_equal!(post.endpoint_map, pre.endpoint_map, p => {});
    assert_maps_equal!(post.thread_map, pre.thread_map.insert(thread, ThreadU {
        quota_4k: (pre.thread_map[thread].quota_4k - cost) as usize, syscall_progress: progress, ..pre.thread_map[thread]
    }), p => { reveal(kernel_thread_quota_4k_changed); });
    assert_maps_equal!(post.container_map, pre.container_map.insert(container, ContainerU {
        owned_processes: pre.container_map[container].owned_processes.insert(child), free_pcids: post.container_map[container].free_pcids, ..pre.container_map[container]
    }), p => { reveal(container_pcid_allocator_wf); });
    assert_maps_equal!(post.process_map, Map::new(pre.process_map.dom(), |p: RwLockProcessPtr| ProcessU {
        lock_state: if p == parent { LockStateU::Unlocked } else { pre.process_map[p].lock_state },
        children: if p == parent { pre.process_map[p].children.push(child) } else { pre.process_map[p].children },
        subtree_set: if ancestors.contains(p) { pre.process_map[p].subtree_set.insert(child) } else { pre.process_map[p].subtree_set }, ..pre.process_map[p]
    }).insert(child, post.process_map[child]), p => { process_pagetable_match_process_at(before.prc_mp, before.pt_mp, p); process_iommu_table_match_process_at(before.prc_mp, before.it_mp, p); });
    assert(post.container_map[container].free_pcids =~= pre.container_map[container].free_pcids.remove(pcid)) by { pcid_allocator_perms_wf_at(before.pcid_allc_mp, pcid_allocator); };
    assert_sets_equal!(pre.container_map[container].free_pcids.difference(post.container_map[container].free_pcids), set![pcid]);
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

pub proof fn kernel_process_map_unchanged_implies_u_map(pre: &KernelK, post: &KernelK, lctx: &LocalContext)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        post.prc_mp.typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id()),
        kernel_process_nonlock_fields_unchanged(pre.prc_mp, post.prc_mp),
        kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view()),
        kernel_iommu_table_nonlock_fields_unchanged(pre.it_mp, post.it_mp),
        forall|p: RwLockProcessPtr| #![trigger pre.prc_mp.spec_index(p)] #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) && post.prc_mp.dom().contains(p) ==> post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger pre.it_mp.spec_index(p)] #![trigger post.it_mp.spec_index(p)]
            pre.it_mp.dom().contains(p) && post.it_mp.dom().contains(p) ==> post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger pre.pt_mp.spec_index(p)] #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) && post.pt_mp.dom().contains(p) ==> post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread(),
    ensures
        ({
            let before = kernel_k_to_kernel_u(*pre);
            let after = kernel_k_to_kernel_u(*post);
            after.process_map == before.process_map
        }),
{
    reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
    reveal(process_pagetable_match); reveal(process_iommu_table_match);
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    assert_maps_equal!(after.process_map, before.process_map, p => {
        if post.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); kernel_process_projection_at(post, p); }
    });
}

#[verifier::spinoff_prover]
pub proof fn kernel_pagetable_pair_lock_modes_changed_implies_u_map(pre: &KernelK, post: &KernelK, lctx: &LocalContext, source: RwLockProcessPtr, target: RwLockProcessPtr)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        post.prc_mp.typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id()),
        post.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        kernel_process_nonlock_fields_unchanged(pre.prc_mp, post.prc_mp),
        kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view()),
        kernel_iommu_table_nonlock_fields_unchanged(pre.it_mp, post.it_mp),
        forall|p: RwLockProcessPtr| #![trigger pre.prc_mp.spec_index(p)] #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) && post.prc_mp.dom().contains(p) ==> post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger pre.it_mp.spec_index(p)] #![trigger post.it_mp.spec_index(p)]
            pre.it_mp.dom().contains(p) && post.it_mp.dom().contains(p) ==> post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger pre.pt_mp.spec_index(p)] #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) && post.pt_mp.dom().contains(p) && (p != pre.prc_mp.spec_index(source).view().pagetable && p != pre.prc_mp.spec_index(target).view().pagetable) ==> post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread(),
        source != target,
        pre.prc_mp.dom().contains(source),
        pre.prc_mp.dom().contains(target),
        !pre.prc_mp.spec_index(source).view().zombie,
        !pre.prc_mp.spec_index(target).view().zombie,
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pre.prc_mp.spec_index(source).view().pagetable, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pre.prc_mp.spec_index(target).view().pagetable, TypedLockMode::Write),
    ensures
        ({
            let before = kernel_k_to_kernel_u(*pre);
            let after = kernel_k_to_kernel_u(*post);
            let processes = before.process_map;
            let locked_processes = processes.insert(source, ProcessU {
                pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..processes[source].pagetable->Some_0 }), ..processes[source]
            }).insert(target, ProcessU {
                pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..processes[target].pagetable->Some_0 }), ..processes[target]
            });
            after.process_map == locked_processes
        }),
{
    post.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pre.prc_mp.spec_index(source).view().pagetable);
    post.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pre.prc_mp.spec_index(target).view().pagetable);
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    let processes = before.process_map;
    let locked_processes = processes.insert(source, ProcessU {
        pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..processes[source].pagetable->Some_0 }), ..processes[source]
    }).insert(target, ProcessU {
        pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..processes[target].pagetable->Some_0 }), ..processes[target]
    });
    reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
    reveal(process_pagetable_match); reveal(process_iommu_table_match);
    assert_maps_equal!(after.process_map, locked_processes, p => {
        if post.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); kernel_process_projection_at(post, p); }
    });
}

#[verifier::spinoff_prover]
pub proof fn kernel_cpu_and_two_threads_lock_modes_changed_implies_u_step(
    pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu: CpuId,
    caller: RwLockThreadPtr, peer: RwLockThreadPtr, endpoint: RwLockEndpointPtr, tables: Option<(RwLockProcessPtr, RwLockProcessPtr)>,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        typed_lock_maps_aligned(post, lctx),
        index_valid(NUM_CPUS, cpu),
        pre.thr_mp.dom().contains(caller),
        pre.thr_mp.dom().contains(peer),
        pre.ep_mp.dom().contains(endpoint),
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post),
        kernel_container_nonlock_fields_and_quotas_unchanged(pre, post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        pre.irt.view().owners() == post.irt.view().owners(),
        pre.irt.view().iommu_roots() == post.irt.view().iommu_roots(),
        pre.cpu_tlb.view() == post.cpu_tlb.view(),
        pre.iommu_tlb.view() == post.iommu_tlb.view(),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), caller, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), peer, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.endpoint_lock_map(), endpoint, TypedLockMode::Write),
        tables matches Some((source, target)) ==> {
            &&& source != target
            &&& pre.prc_mp.dom().contains(source) && pre.prc_mp.dom().contains(target)
            &&& !pre.prc_mp.spec_index(source).view().zombie && !pre.prc_mp.spec_index(target).view().zombie
            &&& typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pre.prc_mp.spec_index(source).view().pagetable, TypedLockMode::Write)
            &&& typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pre.prc_mp.spec_index(target).view().pagetable, TypedLockMode::Write)
        },
        forall|i: CpuId| #![trigger pre.cpu_arr.spec_index(i)] #![trigger post.cpu_arr.spec_index(i)] index_valid(NUM_CPUS, i) && i != cpu ==>
            post.cpu_arr.spec_index(i).value.locking_thread() == pre.cpu_arr.spec_index(i).value.locking_thread(),
        forall|p: RwLockContainerPtr| #![trigger pre.ctn_mp.spec_index(p)] #![trigger post.ctn_mp.spec_index(p)]
            pre.ctn_mp.dom().contains(p) && post.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).locking_thread() == pre.ctn_mp.spec_index(p).locking_thread() && post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
        forall|p: RwLockProcessPtr| #![trigger pre.prc_mp.spec_index(p)] #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) && post.prc_mp.dom().contains(p) ==> post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread(),
        forall|p: RwLockThreadPtr| #![trigger pre.thr_mp.spec_index(p)] #![trigger post.thr_mp.spec_index(p)]
            pre.thr_mp.dom().contains(p) && post.thr_mp.dom().contains(p) && p != caller && p != peer ==> post.thr_mp.spec_index(p).locking_thread() == pre.thr_mp.spec_index(p).locking_thread(),
        forall|p: RwLockEndpointPtr| #![trigger pre.ep_mp.spec_index(p)] #![trigger post.ep_mp.spec_index(p)]
            pre.ep_mp.dom().contains(p) && post.ep_mp.dom().contains(p) && p != endpoint ==> post.ep_mp.spec_index(p).locking_thread() == pre.ep_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger pre.it_mp.spec_index(p)] #![trigger post.it_mp.spec_index(p)]
            pre.it_mp.dom().contains(p) && post.it_mp.dom().contains(p) ==> post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger pre.pt_mp.spec_index(p)] #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) && post.pt_mp.dom().contains(p) && (tables is None || p != pre.prc_mp.spec_index(tables->Some_0.0).view().pagetable && p != pre.prc_mp.spec_index(tables->Some_0.1).view().pagetable)
                ==> post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread(),
    ensures
        kernel_k_to_kernel_u(*pre).thread_map[caller].owning_proc == pre.thr_mp.spec_index(caller).view().owning_proc,
        kernel_k_to_kernel_u(*pre).thread_map[peer].owning_proc == pre.thr_mp.spec_index(peer).view().owning_proc,
        kernel_k_to_kernel_u(*pre).thread_map[caller].owning_container == pre.thr_mp.spec_index(caller).view().owning_container,
        kernel_k_to_kernel_u(*pre).thread_map[peer].owning_container == pre.thr_mp.spec_index(peer).view().owning_container,
        pre.cpu_arr.spec_index(cpu).value.locking_thread() is None ==> kernel_k_to_kernel_u(*pre).cpu_array[cpu as int].lock_state is Unlocked,
        kernel_k_to_kernel_u(*post).cpu_array[cpu as int].lock_state is WriteLocked,
        ({
            let before = kernel_k_to_kernel_u(*pre);
            let processes = before.process_map;
            let locked_processes = match tables {
                None => processes,
                Some((source, target)) => processes.insert(source, ProcessU {
                    pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..processes[source].pagetable->Some_0 }), ..processes[source]
                }).insert(target, ProcessU {
                    pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..processes[target].pagetable->Some_0 }), ..processes[target]
                }),
            };
            kernel_k_to_kernel_u(*post) == (KernelU {
                cpu_array: before.cpu_array.update(cpu as int, CpuU { lock_state: LockStateU::WriteLocked, ..before.cpu_array[cpu as int] }),
                process_map: locked_processes,
                thread_map: before.thread_map.insert(caller, ThreadU { lock_state: LockStateU::WriteLocked, ..before.thread_map[caller] }).insert(peer, ThreadU { lock_state: LockStateU::WriteLocked, ..before.thread_map[peer] }),
                endpoint_map: before.endpoint_map.insert(endpoint, EndpointU { lock_state: LockStateU::WriteLocked, ..before.endpoint_map[endpoint] }),
                ..before
            })
        }),
{
    assert(post.dflt_pt == pre.dflt_pt) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
    post.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), caller);
    post.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), peer);
    post.ep_mp.typed_lock_map_aligned_write_at(lctx.endpoint_lock_map(), lctx.thread_id(), endpoint);
    assert(post.cpu_arr.spec_index(cpu).value.locking_thread() is Write) by { reveal(LockedArray::typed_lock_map_aligned); };
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    let processes = before.process_map;
    let locked_processes = match tables {
        None => processes,
        Some((source, target)) => processes.insert(source, ProcessU {
            pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..processes[source].pagetable->Some_0 }), ..processes[source]
        }).insert(target, ProcessU {
            pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..processes[target].pagetable->Some_0 }), ..processes[target]
        }),
    };
    if index_valid(NUM_CPUS, cpu) { kernel_cpu_projection_at(pre, cpu); } if index_valid(NUM_CPUS, cpu) { kernel_cpu_projection_at(post, cpu); }
    if pre.thr_mp.dom().contains(caller) { kernel_thread_projection_at(pre, caller); } if post.thr_mp.dom().contains(caller) { kernel_thread_projection_at(post, caller); }
    if pre.thr_mp.dom().contains(peer) { kernel_thread_projection_at(pre, peer); } if post.thr_mp.dom().contains(peer) { kernel_thread_projection_at(post, peer); }
    if pre.ep_mp.dom().contains(endpoint) { kernel_endpoint_projection_at(pre, endpoint); }
    assert_seqs_equal!(after.cpu_array == before.cpu_array.update(cpu as int, CpuU { lock_state: LockStateU::WriteLocked, ..before.cpu_array[cpu as int] }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); }
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
    });
    assert(after.process_map == locked_processes) by {
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
        match tables {
            Some((source, target)) => kernel_pagetable_pair_lock_modes_changed_implies_u_map(pre, post, lctx, source, target),
            None => kernel_process_map_unchanged_implies_u_map(pre, post, lctx),
        }
    };
    assert_maps_equal!(after.container_map, before.container_map, p => {
        if pre.ctn_mp.dom().contains(p) { kernel_container_projection_at(pre, p); } if post.ctn_mp.dom().contains(p) { kernel_container_projection_at(post, p); }
        reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
    });
    assert_maps_equal!(after.thread_map, before.thread_map.insert(caller, ThreadU { lock_state: LockStateU::WriteLocked, ..before.thread_map[caller] })
        .insert(peer, ThreadU { lock_state: LockStateU::WriteLocked, ..before.thread_map[peer] }), p => {
            if pre.thr_mp.dom().contains(p) { kernel_thread_projection_at(pre, p); } if post.thr_mp.dom().contains(p) { kernel_thread_projection_at(post, p); }
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
        });
    assert_maps_equal!(after.endpoint_map, before.endpoint_map.insert(endpoint, EndpointU { lock_state: LockStateU::WriteLocked, ..before.endpoint_map[endpoint] }), p => {
        if pre.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(pre, p); } if post.ep_mp.dom().contains(p) { kernel_endpoint_projection_at(post, p); }
        reveal(kernel_endpoint_nonlock_fields_unchanged);
    });
    assert(after.iommu_root_table == before.iommu_root_table) by { reveal(IommuRootTable::user_view); };
}

#[verifier::spinoff_prover]
pub proof fn kernel_cpu_process_thread_endpoint_lock_modes_changed_implies_u_step(
    pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    endpoint_ptr: Option<RwLockEndpointPtr>, write_locked: bool, container: Option<RwLockContainerPtr>, pagetable: bool, cpu_set_unlocked: Option<KernelK>,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        typed_lock_maps_aligned(post, lctx),
        index_valid(NUM_CPUS, cpu_id),
        *post == (KernelK { cpu_arr: post.cpu_arr, prc_mp: post.prc_mp, thr_mp: post.thr_mp, ep_mp: post.ep_mp, sched_mp: post.sched_mp, ctn_mp: post.ctn_mp, pt_mp: post.pt_mp, pcid_allc_mp: post.pcid_allc_mp, cpu_set_mp: post.cpu_set_mp, ..*pre }),
        match container {
            Some(c) => {
                &&& pre.ctn_mp.dom().contains(c)
                &&& post.ctn_mp.unchanged_except(&pre.ctn_mp, c)
                &&& if write_locked { typed_lock_map_contains_mode(lctx.container_lock_map(), c, TypedLockMode::Write) } else { post.ctn_mp.spec_index(c).locking_thread() is None }
            },
            None => post.ctn_mp == pre.ctn_mp,
        },
        if pagetable {
            let table = post.prc_mp.spec_index(process_ptr).view().pagetable;
            &&& !post.prc_mp.spec_index(process_ptr).view().zombie
            &&& post.pt_mp.unchanged_except(&pre.pt_mp, table)
            &&& if write_locked { typed_lock_map_contains_mode(lctx.pagetable_lock_map(), table, TypedLockMode::Write) } else { post.pt_mp.spec_index(table).locking_thread() is None }
        } else { post.pt_mp == pre.pt_mp },
        post.cpu_arr.unchanged_except(&pre.cpu_arr, cpu_id),
        post.prc_mp.unchanged_except(&pre.prc_mp, process_ptr),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        match endpoint_ptr { Some(e) => post.ep_mp.unchanged_except(&pre.ep_mp, e), None => post.ep_mp == pre.ep_mp },
        if write_locked { typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write) } else { post.cpu_arr.spec_index(cpu_id).value.locking_thread() is None },
        if write_locked { typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write) } else { post.prc_mp.spec_index(process_ptr).locking_thread() is None },
        if write_locked { typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write) } else { post.thr_mp.spec_index(thread_ptr).locking_thread() is None },
        endpoint_ptr is Some ==> if write_locked { typed_lock_map_contains_mode(lctx.endpoint_lock_map(), endpoint_ptr->Some_0, TypedLockMode::Write) } else { post.ep_mp.spec_index(endpoint_ptr->Some_0).locking_thread() is None },
        match cpu_set_unlocked {
            Some(mid) => {
                let s = post.ctn_mp.spec_index(container->Some_0).view_rodata().view().cpu_set;
                &&& container is Some
                &&& container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)
                &&& *post == (KernelK { cpu_set_mp: post.cpu_set_mp, ..mid })
                &&& post.cpu_set_mp.unchanged_except(&mid.cpu_set_mp, s)
                &&& post.cpu_set_mp.spec_index(s).being_killed() == mid.cpu_set_mp.spec_index(s).being_killed()
                &&& if write_locked { typed_lock_map_contains_mode(lctx.cpu_set_lock_map(), s, TypedLockMode::Write) } else { post.cpu_set_mp.spec_index(s).locking_thread() is None }
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
        }),
        pagetable && post.inv() ==> kernel_k_to_kernel_u(*pre).kernel_l4_end == post.pt_mp.spec_index(post.prc_mp.spec_index(process_ptr).view().pagetable).view().kernel_l4_end,
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let mode = if write_locked { LockStateU::WriteLocked } else { LockStateU::Unlocked };
            kernel_k_to_kernel_u(*post) == (KernelU {
                cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, ..old_u.cpu_array[cpu_id as int] }),
                container_map: match container {
                    Some(c) => old_u.container_map.insert(c, ContainerU {
                        lock_state: mode, lock_process_owner: if write_locked { post.ctn_mp.spec_index(c).lock_process_owner_u() } else { None },
                        cpu_set_lock: if cpu_set_unlocked is Some { mode } else { old_u.container_map[c].cpu_set_lock }, ..old_u.container_map[c]
                    }),
                    None => old_u.container_map,
                },
                process_map: old_u.process_map.insert(process_ptr, ProcessU {
                    lock_state: mode,
                    pagetable: if pagetable { Some(PageTableU { lock_state: mode, ..old_u.process_map[process_ptr].pagetable->Some_0 }) } else { old_u.process_map[process_ptr].pagetable },
                    ..old_u.process_map[process_ptr]
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
            &&& old_u.cpu_array[cpu_id as int] == (CpuU {
                lock_state: pre.cpu_arr.spec_index(cpu_id).value.lock_state_u(), owning_container: c.owning_container, state: c.state,
                current_process: c.current_process, current_thread: c.current_thread, killed: post.cpu_arr.spec_index(cpu_id).value.being_killed(),
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
            &&& pagetable ==> {
                let table = post.prc_mp.spec_index(process_ptr).view().pagetable;
                &&& old_u.process_map.spec_index(process_ptr).pagetable is Some
                &&& old_u.process_map.spec_index(process_ptr).pagetable->Some_0.lock_state == pre.pt_mp.spec_index(table).lock_state_u()
                &&& old_u.process_map.spec_index(process_ptr).pagetable->Some_0.mapping_4k == pagetable_c(post.pt_mp, post.pt_lower.view(), table).user_view(LockStateU::Unlocked).mapping_4k
            }
        }),
{
    kernel_u_cpu_array_projection(pre);
    if pagetable && post.inv() { reveal(KernelK::default_pagetable_wf); }
    if write_locked {
        if let Some(c) = container { post.ctn_mp.typed_lock_map_aligned_write_at(lctx.container_lock_map(), lctx.thread_id(), c); }
        if cpu_set_unlocked is Some {
            post.cpu_set_mp.typed_lock_map_aligned_write_at(lctx.cpu_set_lock_map(), lctx.thread_id(), post.ctn_mp.spec_index(container->Some_0).view_rodata().view().cpu_set);
        }
        if pagetable { post.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), post.prc_mp.spec_index(process_ptr).view().pagetable); }
        post.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), process_ptr);
        post.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr);
        if endpoint_ptr is Some { post.ep_mp.typed_lock_map_aligned_write_at(lctx.endpoint_lock_map(), lctx.thread_id(), endpoint_ptr->Some_0); }
        assert(post.cpu_arr.spec_index(cpu_id).value.locking_thread() is Write) by { reveal(LockedArray::typed_lock_map_aligned); };
    }
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post); reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
    reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
    reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
    let mode = if write_locked { LockStateU::WriteLocked } else { LockStateU::Unlocked };
    kernel_cpu_lock_mode_changed_implies_u_cpu_array(pre, post, cpu_id, mode);
    kernel_container_lock_mode_changed_implies_u_container_map(pre, post, container, mode, cpu_set_unlocked);
    kernel_process_lock_mode_changed_implies_u_process_map(pre, post, process_ptr, mode, pagetable);
    kernel_thread_lock_mode_changed_implies_u_thread_map(pre, post, thread_ptr, mode);
    kernel_endpoint_lock_mode_changed_implies_u_endpoint_map(pre, post, endpoint_ptr, mode);
    if index_valid(NUM_CPUS, cpu_id) { kernel_cpu_projection_at(pre, cpu_id); }
    if pre.prc_mp.dom().contains(process_ptr) { kernel_process_projection_at(pre, process_ptr); } if post.prc_mp.dom().contains(process_ptr) { kernel_process_projection_at(post, process_ptr); }
    if pre.thr_mp.dom().contains(thread_ptr) { kernel_thread_projection_at(pre, thread_ptr); }
    if let Some(c) = container { if pre.ctn_mp.dom().contains(c) { kernel_container_projection_at(pre, c); } }
    if pre.ep_mp.dom().contains(endpoint_ptr->Some_0) { kernel_endpoint_projection_at(pre, endpoint_ptr->Some_0); }
}

#[verifier::spinoff_prover]
pub(super) proof fn kernel_ipc_block_fields_implies_u_step(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    waiting_state: ThreadState, payload: IPCPayLoad, regs: Registers, flushed_default_pcid: bool, include_lock_state: bool,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        kernel_ipc_block_fields(pre, post, cpu_id, thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, regs, flushed_default_pcid),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)] pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
    ensures
        kernel_u_ipc_block_changed(kernel_k_user_projection(*pre, include_lock_state), kernel_k_user_projection(*post, include_lock_state),
            cpu_id, thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, regs, flushed_default_pcid),
{
    hide(kernel_k_user_projection);
    reveal(kernel_u_ipc_block_changed); reveal(kernel_ipc_block_fields); kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    kernel_cpu_user_projection_at(pre, include_lock_state, cpu_id); if pre.thr_mp.dom().contains(thread_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, thread_ptr); }
    if pre.ep_mp.dom().contains(endpoint_ptr) { kernel_endpoint_user_projection_at(pre, include_lock_state, endpoint_ptr); }
    if pre.prc_mp.dom().contains(pre.thr_mp.spec_index(thread_ptr).view().owning_proc) { kernel_process_user_projection_at(pre, include_lock_state, pre.thr_mp.spec_index(thread_ptr).view().owning_proc); }
    kernel_cpu_state_set_and_current_cleared_implies_u_cpu_array(pre, post, cpu_id, CpuState::Idle, include_lock_state);
    kernel_container_nonlock_fields_and_locks_unchanged_implies_u_container_map(pre, post, include_lock_state);
    kernel_process_nonlock_fields_and_locks_unchanged_implies_u_process_map(pre, post, include_lock_state);
    kernel_ipc_block_fields_implies_u_thread_map(pre, post, cpu_id, thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, regs, flushed_default_pcid, include_lock_state);
    kernel_ipc_block_fields_implies_u_endpoint_map(pre, post, cpu_id, thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, regs, flushed_default_pcid, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { pre.irt.view().user_view_unfold(); post.irt.view().user_view_unfold(); };
}

#[verifier::spinoff_prover]
pub(super) proof fn kernel_ipc_call_handoff_fields_implies_u_step(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, caller_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    callee_ptr: RwLockThreadPtr, regs: Registers, flushed_pcid: Option<Pcid>, include_lock_state: bool,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        kernel_ipc_call_handoff_fields(pre, post, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, regs, flushed_pcid),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)] pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
    ensures
        kernel_u_ipc_call_handoff_changed(kernel_k_user_projection(*pre, include_lock_state), kernel_k_user_projection(*post, include_lock_state),
            cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, regs, flushed_pcid),
{
    hide(kernel_k_user_projection);
    reveal(kernel_u_ipc_call_handoff_changed); reveal(kernel_ipc_call_handoff_fields);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    kernel_cpu_user_projection_at(pre, include_lock_state, cpu_id);
    if pre.thr_mp.dom().contains(caller_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, caller_ptr); } if pre.thr_mp.dom().contains(callee_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, callee_ptr); }
    if pre.ep_mp.dom().contains(endpoint_ptr) { kernel_endpoint_user_projection_at(pre, include_lock_state, endpoint_ptr); }
    if pre.prc_mp.dom().contains(pre.thr_mp.spec_index(caller_ptr).view().owning_proc) { kernel_process_user_projection_at(pre, include_lock_state, pre.thr_mp.spec_index(caller_ptr).view().owning_proc); }
    kernel_ipc_call_handoff_fields_implies_u_cpu_array(pre, post, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, regs, flushed_pcid, include_lock_state);
    kernel_container_nonlock_fields_and_locks_unchanged_implies_u_container_map(pre, post, include_lock_state);
    kernel_process_nonlock_fields_and_locks_unchanged_implies_u_process_map(pre, post, include_lock_state);
    kernel_ipc_call_handoff_fields_implies_u_thread_map(pre, post, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, regs, flushed_pcid, include_lock_state);
    kernel_ipc_call_handoff_fields_implies_u_endpoint_map(pre, post, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, regs, flushed_pcid, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { pre.irt.view().user_view_unfold(); post.irt.view().user_view_unfold(); };
}

#[verifier::spinoff_prover]
pub(super) proof fn kernel_ipc_accept_call_fields_implies_u_step(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    caller_ptr: RwLockThreadPtr, include_lock_state: bool,
)
    requires
        kernel_ipc_accept_call_fields(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr),
    ensures
        kernel_u_ipc_accept_call_changed(kernel_k_user_projection(*pre, include_lock_state), kernel_k_user_projection(*post, include_lock_state),
            cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr),
{
    hide(kernel_k_user_projection);
    reveal(kernel_u_ipc_accept_call_changed);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    reveal(kernel_ipc_accept_call_fields); kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    kernel_cpu_user_projection_at(pre, include_lock_state, cpu_id); if pre.thr_mp.dom().contains(callee_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, callee_ptr); }
    if pre.thr_mp.dom().contains(caller_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, caller_ptr); }
    if pre.ep_mp.dom().contains(endpoint_ptr) { kernel_endpoint_user_projection_at(pre, include_lock_state, endpoint_ptr); }
    if pre.prc_mp.dom().contains(pre.thr_mp.spec_index(callee_ptr).view().owning_proc) { kernel_process_user_projection_at(pre, include_lock_state, pre.thr_mp.spec_index(callee_ptr).view().owning_proc); }
    let callee = pre_u.thread_map.spec_index(callee_ptr);
    let caller = pre_u.thread_map.spec_index(caller_ptr);
    let endpoint = pre_u.endpoint_map.spec_index(endpoint_ptr);
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, include_lock_state, i as usize); kernel_cpu_user_projection_at(post, include_lock_state, i as usize); } });
    assert_maps_equal!(post_u.container_map, pre_u.container_map, c => { if pre.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(pre, include_lock_state, c); } if post.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(post, include_lock_state, c); } });
    assert_maps_equal!(post_u.process_map, pre_u.process_map, p => { if pre.prc_mp.dom().contains(p) { kernel_process_user_projection_at(pre, include_lock_state, p); } if post.prc_mp.dom().contains(p) { kernel_process_user_projection_at(post, include_lock_state, p); } });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(callee_ptr, ThreadU { caller: Some(caller_ptr), ..callee }).insert(caller_ptr, ThreadU {
        state: ThreadState::WAITING_REPLY, callee: Some(callee_ptr), blocking_endpoint_ptr: None, ..caller
    }), t => { if pre.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(pre, include_lock_state, t); } if post.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(post, include_lock_state, t); } });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map.insert(endpoint_ptr, EndpointU { queue: endpoint.queue.skip(1), ..endpoint }), e => {
        if pre.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(pre, include_lock_state, e); }
        if post.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(post, include_lock_state, e); }
    });
}

#[verifier::spinoff_prover]
pub(super) proof fn kernel_ipc_reply_handoff_fields_implies_u_step(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    caller_ptr: RwLockThreadPtr, regs: Registers, flushed_pcid: Option<Pcid>, include_lock_state: bool,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        kernel_ipc_reply_handoff_fields(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)] pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
    ensures
        kernel_u_ipc_reply_handoff_changed(kernel_k_user_projection(*pre, include_lock_state), kernel_k_user_projection(*post, include_lock_state),
            cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid),
{
    hide(kernel_k_user_projection);
    reveal(kernel_u_ipc_reply_handoff_changed); kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    kernel_ipc_reply_handoff_fields_implies_u_cpu_array(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid, include_lock_state);
    kernel_ipc_reply_handoff_fields_implies_u_thread_map(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid, include_lock_state);
    kernel_ipc_reply_handoff_fields_implies_u_process_map(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid, include_lock_state);
    kernel_ipc_reply_handoff_fields_implies_u_container_map(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid, include_lock_state);
    reveal(kernel_ipc_reply_handoff_fields);
    kernel_cpu_user_projection_at(pre, include_lock_state, cpu_id); if pre.thr_mp.dom().contains(callee_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, callee_ptr); }
    if pre.thr_mp.dom().contains(caller_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, caller_ptr); }
    if pre.ep_mp.dom().contains(endpoint_ptr) { kernel_endpoint_user_projection_at(pre, include_lock_state, endpoint_ptr); }
    if pre.prc_mp.dom().contains(pre.thr_mp.spec_index(callee_ptr).view().owning_proc) { kernel_process_user_projection_at(pre, include_lock_state, pre.thr_mp.spec_index(callee_ptr).view().owning_proc); }
    let endpoint = pre_u.endpoint_map.spec_index(endpoint_ptr);
    assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { pre.irt.view().user_view_unfold(); post.irt.view().user_view_unfold(); };
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map.insert(endpoint_ptr, EndpointU {
        queue: endpoint.queue.push(callee_ptr), queue_state: if endpoint.queue.len() == 0 { EndpointState::RECEIVE } else { endpoint.queue_state }, ..endpoint
    }), e => { if pre.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(pre, include_lock_state, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(post, include_lock_state, e); } });
}

/// The reply-handoff fields project to the cpu array with only `cpu_id` switched to the caller.
proof fn kernel_ipc_reply_handoff_fields_implies_u_cpu_array(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    caller_ptr: RwLockThreadPtr, regs: Registers, flushed_pcid: Option<Pcid>, include_lock_state: bool,
)
    requires kernel_ipc_reply_handoff_fields(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let post_u = kernel_k_user_projection(*post, include_lock_state);
            let cpu = pre_u.cpu_array[cpu_id as int];
            post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU { current_process: Some(pre_u.thread_map.spec_index(caller_ptr).owning_proc), current_thread: Some(caller_ptr), ..cpu })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_ipc_reply_handoff_fields);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    if pre.thr_mp.dom().contains(caller_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, caller_ptr); } if index_valid(NUM_CPUS, cpu_id) { kernel_cpu_user_projection_at(pre, include_lock_state, cpu_id); }
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    let cpu = pre_u.cpu_array[cpu_id as int];
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU {
        current_process: Some(pre_u.thread_map.spec_index(caller_ptr).owning_proc), current_thread: Some(caller_ptr), ..cpu
    }), i => { if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, include_lock_state, i as usize); kernel_cpu_user_projection_at(post, include_lock_state, i as usize); } });
}

/// The reply-handoff fields project to the thread map with the callee waiting on the endpoint and the caller running.
proof fn kernel_ipc_reply_handoff_fields_implies_u_thread_map(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    caller_ptr: RwLockThreadPtr, regs: Registers, flushed_pcid: Option<Pcid>, include_lock_state: bool,
)
    requires kernel_ipc_reply_handoff_fields(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let post_u = kernel_k_user_projection(*post, include_lock_state);
            let callee = pre_u.thread_map.spec_index(callee_ptr);
            let caller = pre_u.thread_map.spec_index(caller_ptr);
            post_u.thread_map == pre_u.thread_map.insert(callee_ptr, ThreadU {
                state: ThreadState::RECEIVING_CALL, caller: None, blocking_endpoint_ptr: Some(endpoint_ptr), ipc_payload: IPCPayLoad::Empty, trap_frame: Some(regs), ..callee
            }).insert(caller_ptr, ThreadU { state: ThreadState::RUNNING { cpu_id }, callee: None, last_cpu: cpu_id, trap_frame: None, ..caller })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_ipc_reply_handoff_fields); kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    if pre.thr_mp.dom().contains(callee_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, callee_ptr); } if pre.thr_mp.dom().contains(caller_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, caller_ptr); }
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    let callee = pre_u.thread_map.spec_index(callee_ptr);
    let caller = pre_u.thread_map.spec_index(caller_ptr);
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(callee_ptr, ThreadU {
        state: ThreadState::RECEIVING_CALL, caller: None, blocking_endpoint_ptr: Some(endpoint_ptr), ipc_payload: IPCPayLoad::Empty, trap_frame: Some(regs), ..callee
    }).insert(caller_ptr, ThreadU { state: ThreadState::RUNNING { cpu_id }, callee: None, last_cpu: cpu_id, trap_frame: None, ..caller }), t => {
        if pre.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(pre, include_lock_state, t); }
        if post.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(post, include_lock_state, t); }
    });
}

/// The reply-handoff fields leave the process map projection unchanged.
proof fn kernel_ipc_reply_handoff_fields_implies_u_process_map(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    caller_ptr: RwLockThreadPtr, regs: Registers, flushed_pcid: Option<Pcid>, include_lock_state: bool,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        kernel_ipc_reply_handoff_fields(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid),
    ensures kernel_k_user_projection(*post, include_lock_state).process_map == kernel_k_user_projection(*pre, include_lock_state).process_map,
{
    hide(kernel_k_user_projection);
    reveal(kernel_ipc_reply_handoff_fields); reveal(kernel_process_nonlock_fields_unchanged); kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    assert_maps_equal!(post_u.process_map, pre_u.process_map, p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_user_projection_at(pre, include_lock_state, p); } if post.prc_mp.dom().contains(p) { kernel_process_user_projection_at(post, include_lock_state, p); }
        reveal(process_pagetable_match); reveal(process_iommu_table_match); reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
    });
}

/// The reply-handoff fields leave the container map projection unchanged.
proof fn kernel_ipc_reply_handoff_fields_implies_u_container_map(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    caller_ptr: RwLockThreadPtr, regs: Registers, flushed_pcid: Option<Pcid>, include_lock_state: bool,
)
    requires
        kernel_ipc_reply_handoff_fields(pre, post, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)] pre.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
    ensures kernel_k_user_projection(*post, include_lock_state).container_map == kernel_k_user_projection(*pre, include_lock_state).container_map,
{
    hide(kernel_k_user_projection);
    reveal(kernel_ipc_reply_handoff_fields); reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    assert_maps_equal!(post_u.container_map, pre_u.container_map, c => { if pre.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(pre, include_lock_state, c); } if post.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(post, include_lock_state, c); } });
}

#[verifier::spinoff_prover]
pub(super) proof fn kernel_ipc_rendezvous_fields_implies_u_step(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, caller_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, peer_thread_ptr: RwLockThreadPtr, peer_result: RetValueType,
    cpu_transfer: Option<(CpuId, RwLockThreadPtr)>, pci_transfer: Option<(PciBdf, RwLockProcessPtr, RwLockProcessPtr)>, include_lock_state: bool,
)
    requires
        container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp),
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        kernel_ipc_rendezvous_fields(pre, post, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)]
            pre.ctn_mp.dom().contains(p) && post.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).locking_thread() == pre.ctn_mp.spec_index(p).locking_thread() && post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) && post.prc_mp.dom().contains(p) ==> post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread(),
        forall|p: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(p)]
            pre.thr_mp.dom().contains(p) && post.thr_mp.dom().contains(p) ==> post.thr_mp.spec_index(p).locking_thread() == pre.thr_mp.spec_index(p).locking_thread(),
        forall|p: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(p)]
            pre.ep_mp.dom().contains(p) && post.ep_mp.dom().contains(p) ==> post.ep_mp.spec_index(p).locking_thread() == pre.ep_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) && post.pt_mp.dom().contains(p) ==> post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
            pre.it_mp.dom().contains(p) && post.it_mp.dom().contains(p) ==> post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread(),
        forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> post.cpu_arr.spec_index(i).value.locking_thread() == pre.cpu_arr.spec_index(i).value.locking_thread(),
        post.cpu_set_mp.dom() == pre.cpu_set_mp.dom(),
        forall|p: RwLockCpuSetPtr| #![trigger post.cpu_set_mp.spec_index(p)]
            pre.cpu_set_mp.dom().contains(p) ==> post.cpu_set_mp.spec_index(p).locking_thread() == pre.cpu_set_mp.spec_index(p).locking_thread() && post.cpu_set_mp.spec_index(p).being_killed() == pre.cpu_set_mp.spec_index(p).being_killed(),
    ensures
        kernel_u_ipc_rendezvous_changed(kernel_k_user_projection(*pre, include_lock_state), kernel_k_user_projection(*post, include_lock_state),
            cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer),
{
    hide(kernel_k_user_projection);
    reveal(kernel_u_ipc_rendezvous_changed); reveal(kernel_ipc_rendezvous_fields); kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    kernel_cpu_user_projection_at(pre, include_lock_state, cpu_id); if pre.thr_mp.dom().contains(caller_thread_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, caller_thread_ptr); }
    if pre.thr_mp.dom().contains(peer_thread_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, peer_thread_ptr); }
    if pre.ep_mp.dom().contains(endpoint_ptr) { kernel_endpoint_user_projection_at(pre, include_lock_state, endpoint_ptr); }
    if pre.prc_mp.dom().contains(pre.thr_mp.spec_index(caller_thread_ptr).view().owning_proc) { kernel_process_user_projection_at(pre, include_lock_state, pre.thr_mp.spec_index(caller_thread_ptr).view().owning_proc); }
    if pre.ctn_mp.dom().contains(pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container) { kernel_container_user_projection_at(pre, include_lock_state, pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container); }
    if let Some((transfer, receiver)) = cpu_transfer { kernel_cpu_user_projection_at(pre, include_lock_state, transfer); if pre.thr_mp.dom().contains(receiver) { kernel_thread_user_projection_at(pre, include_lock_state, receiver); } }
    if let Some((_, sender, receiver)) = pci_transfer {
        if pre.prc_mp.dom().contains(sender) {
            kernel_process_user_projection_at(pre, include_lock_state, sender); kernel_process_user_projection_at(post, include_lock_state, sender); process_iommu_table_match_process_at(post.prc_mp, post.it_mp, sender);
        }
        if pre.prc_mp.dom().contains(receiver) { kernel_process_user_projection_at(pre, include_lock_state, receiver); }
        pre.irt.view().user_view_unfold();
    }
    kernel_ipc_rendezvous_fields_implies_u_cpu_array(pre, post, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer, include_lock_state);
    kernel_ipc_rendezvous_fields_implies_u_container_map(pre, post, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer, include_lock_state);
    kernel_ipc_rendezvous_fields_implies_u_process_map(pre, post, pci_transfer, include_lock_state);
    kernel_ipc_rendezvous_fields_implies_u_iommu_root_table(pre, post, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer, include_lock_state);
    kernel_ipc_rendezvous_fields_implies_u_thread_map(pre, post, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer, include_lock_state);
    kernel_ipc_rendezvous_fields_implies_u_endpoint_map(pre, post, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer, include_lock_state);
}

/// The rendezvous fields project to the cpu array with only a handed-over cpu moved to the receiver's container.
#[verifier::spinoff_prover]
proof fn kernel_ipc_rendezvous_fields_implies_u_cpu_array(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, caller_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, peer_thread_ptr: RwLockThreadPtr, peer_result: RetValueType,
    cpu_transfer: Option<(CpuId, RwLockThreadPtr)>, pci_transfer: Option<(PciBdf, RwLockProcessPtr, RwLockProcessPtr)>, include_lock_state: bool,
)
    requires
        kernel_ipc_rendezvous_fields(pre, post, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer),
        forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> post.cpu_arr.spec_index(i).value.locking_thread() == pre.cpu_arr.spec_index(i).value.locking_thread(),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let post_u = kernel_k_user_projection(*post, include_lock_state);
            post_u.cpu_array == match cpu_transfer {
                Some((transfer_cpu, receiver)) => pre_u.cpu_array.update(transfer_cpu as int, CpuU {
                    owning_container: pre_u.thread_map.spec_index(receiver).owning_container, ..pre_u.cpu_array[transfer_cpu as int]
                }),
                None => pre_u.cpu_array,
            }
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_ipc_rendezvous_fields);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    match cpu_transfer {
        Some((transfer_cpu, receiver)) => {
            if pre.thr_mp.dom().contains(receiver) { kernel_thread_user_projection_at(pre, include_lock_state, receiver); } if index_valid(NUM_CPUS, transfer_cpu) { kernel_cpu_user_projection_at(pre, include_lock_state, transfer_cpu); }
            assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(transfer_cpu as int, CpuU {
                owning_container: pre_u.thread_map.spec_index(receiver).owning_container, ..pre_u.cpu_array[transfer_cpu as int]
            }), i => { if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, include_lock_state, i as usize); kernel_cpu_user_projection_at(post, include_lock_state, i as usize); } });
        },
        None => { assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_user_projection_at(pre, include_lock_state, i as usize); kernel_cpu_user_projection_at(post, include_lock_state, i as usize); } }); },
    }
}

/// The rendezvous fields project to the container map with only the peer pushed onto its wake cpu's scheduler queue.
#[verifier::spinoff_prover]
proof fn kernel_ipc_rendezvous_fields_implies_u_container_map(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, caller_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, peer_thread_ptr: RwLockThreadPtr, peer_result: RetValueType,
    cpu_transfer: Option<(CpuId, RwLockThreadPtr)>, pci_transfer: Option<(PciBdf, RwLockProcessPtr, RwLockProcessPtr)>, include_lock_state: bool,
)
    requires
        container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp),
        kernel_ipc_rendezvous_fields(pre, post, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)]
            pre.ctn_mp.dom().contains(p) && post.ctn_mp.dom().contains(p) ==> post.ctn_mp.spec_index(p).locking_thread() == pre.ctn_mp.spec_index(p).locking_thread() && post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u(),
        post.cpu_set_mp.dom() == pre.cpu_set_mp.dom(),
        forall|p: RwLockCpuSetPtr| #![trigger post.cpu_set_mp.spec_index(p)]
            pre.cpu_set_mp.dom().contains(p) ==> post.cpu_set_mp.spec_index(p).locking_thread() == pre.cpu_set_mp.spec_index(p).locking_thread() && post.cpu_set_mp.spec_index(p).being_killed() == pre.cpu_set_mp.spec_index(p).being_killed(),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let post_u = kernel_k_user_projection(*post, include_lock_state);
            let peer = pre_u.thread_map.spec_index(peer_thread_ptr);
            let caller = pre_u.thread_map.spec_index(caller_thread_ptr);
            let wake_cpu = if peer.owning_container == caller.owning_container { cpu_id } else { peer.last_cpu };
            let container = pre_u.container_map.spec_index(peer.owning_container);
            post_u.container_map == pre_u.container_map.insert(peer.owning_container, ContainerU {
                scheduler: container.scheduler.update(wake_cpu as int, container.scheduler[wake_cpu as int].push(peer_thread_ptr)), ..container
            })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_ipc_rendezvous_fields); kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    if pre.thr_mp.dom().contains(peer_thread_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, peer_thread_ptr); } if pre.thr_mp.dom().contains(caller_thread_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, caller_thread_ptr); }
    if pre.ctn_mp.dom().contains(pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container) { kernel_container_user_projection_at(pre, include_lock_state, pre.thr_mp.spec_index(peer_thread_ptr).view().owning_container); }
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    let peer = pre_u.thread_map.spec_index(peer_thread_ptr);
    let container = pre_u.container_map.spec_index(peer.owning_container);
    let caller = pre_u.thread_map.spec_index(caller_thread_ptr);
    let wake_cpu = if peer.owning_container == caller.owning_container { cpu_id } else { peer.last_cpu };
    assert_maps_equal!(post_u.container_map, pre_u.container_map.insert(peer.owning_container, ContainerU {
        scheduler: container.scheduler.update(wake_cpu as int, container.scheduler[wake_cpu as int].push(peer_thread_ptr)), ..container
    }), c => { if pre.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(pre, include_lock_state, c); } if post.ctn_mp.dom().contains(c) { kernel_container_user_projection_at(post, include_lock_state, c); } reveal(container_cpu_set_wf); });
}

/// The rendezvous fields project to the process map with only a handed-over PCI function moved from the sender to the
/// receiver process.
proof fn kernel_ipc_rendezvous_fields_implies_u_process_map(
    pre: &KernelK, post: &KernelK, pci_transfer: Option<(PciBdf, RwLockProcessPtr, RwLockProcessPtr)>, include_lock_state: bool,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view()),
        pci_transfer is None ==> kernel_iommu_table_nonlock_fields_unchanged(pre.it_mp, post.it_mp),
        pci_transfer is None ==> kernel_process_nonlock_fields_unchanged(pre.prc_mp, post.prc_mp),
        pci_transfer matches Some((bdf, sender, receiver)) ==> {
            &&& pre.prc_mp.dom().contains(sender)
            &&& pre.prc_mp.dom().contains(receiver)
            &&& sender != receiver
            &&& post.it_mp.dom() == pre.it_mp.dom()
            &&& forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
                pre.it_mp.dom().contains(p) ==> {
                    let before = pre.it_mp.spec_index(p).view();
                    let after = post.it_mp.spec_index(p).view();
                    &&& pre.prc_mp.spec_index(sender).view().iommu_table != Some(p) ==> after.did == before.did
                    &&& after.mapping_4k().filter_keys(|va: VAddr| after.mapping_4k().spec_index(va).present) == before.mapping_4k().filter_keys(|va: VAddr| before.mapping_4k().spec_index(va).present)
                    &&& after.mapping_2m().filter_keys(|va: VAddr| after.mapping_2m().spec_index(va).present) == before.mapping_2m().filter_keys(|va: VAddr| before.mapping_2m().spec_index(va).present)
                    &&& after.mapping_1g().filter_keys(|va: VAddr| after.mapping_1g().spec_index(va).present) == before.mapping_1g().filter_keys(|va: VAddr| before.mapping_1g().spec_index(va).present)
                }
            &&& post.prc_mp.dom() == pre.prc_mp.dom()
            &&& forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
                pre.prc_mp.dom().contains(p) ==> {
                    let a = pre.prc_mp.spec_index(p);
                    let b = post.prc_mp.spec_index(p);
                    let pci = a.view_ghost().owned_pci_functions.view();
                    &&& b.view().zombie == a.view().zombie
                    &&& b.view().pagetable == a.view().pagetable
                    &&& b.view().iommu_table == a.view().iommu_table
                    &&& b.view_ghost().owned_pci_functions.view() == if p == sender { pci.remove(bdf) } else if p == receiver { pci.insert(bdf) } else { pci }
                    &&& b.view().quota_4k == a.view().quota_4k
                    &&& b.view().quota_2m == a.view().quota_2m
                    &&& b.view().quota_1g == a.view().quota_1g
                    &&& b.view().children.view() == a.view().children.view()
                    &&& b.view_rodata().view().parent == a.view_rodata().view().parent
                    &&& b.view_rodata().view().depth == a.view_rodata().view().depth
                    &&& b.view_rodata().view().pcid == a.view_rodata().view().pcid
                    &&& b.view_rodata().view().owning_container == a.view_rodata().view().owning_container
                    &&& b.view_ghost().uppertree_seq.view() == a.view_ghost().uppertree_seq.view()
                    &&& b.view_ghost().subtree_set.view() == a.view_ghost().subtree_set.view()
                    &&& b.being_killed() == a.being_killed()
                    &&& b.view().owned_threads.view() == a.view().owned_threads.view()
                }
        },
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) && post.prc_mp.dom().contains(p) ==> post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) && post.pt_mp.dom().contains(p) ==> post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
            pre.it_mp.dom().contains(p) && post.it_mp.dom().contains(p) ==> post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread(),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let post_u = kernel_k_user_projection(*post, include_lock_state);
            &&& post_u.process_map == match pci_transfer {
                Some((bdf, sender, receiver)) => {
                    let s = pre_u.process_map.spec_index(sender);
                    let r = pre_u.process_map.spec_index(receiver);
                    let s_table = match s.iommu_table { Some(t) => Some(PageTableU { did: post_u.process_map.spec_index(sender).iommu_table->Some_0.did, ..t }), None => None };
                    pre_u.process_map.insert(sender, ProcessU { iommu_table: s_table, owned_pci_functions: s.owned_pci_functions.remove(bdf), ..s })
                        .insert(receiver, ProcessU { owned_pci_functions: r.owned_pci_functions.insert(bdf), ..r })
                },
                None => pre_u.process_map,
            }
        }),
{
    match pci_transfer {
        Some((bdf, sender, receiver)) => { kernel_ipc_rendezvous_fields_implies_u_process_map_pci_moved(pre, post, bdf, sender, receiver, include_lock_state); },
        None => { kernel_process_nonlock_fields_and_locks_unchanged_implies_u_process_map(pre, post, include_lock_state); },
    }
}

/// Process fields equal except the PCI function `bdf` moved from `sender` to `receiver` project to that process-map update.
proof fn kernel_ipc_rendezvous_fields_implies_u_process_map_pci_moved(
    pre: &KernelK, post: &KernelK, bdf: PciBdf, sender: RwLockProcessPtr, receiver: RwLockProcessPtr, include_lock_state: bool,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view()),
        post.it_mp.dom() == pre.it_mp.dom(),
        forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
            pre.it_mp.dom().contains(p) ==> {
                let before = pre.it_mp.spec_index(p).view();
                let after = post.it_mp.spec_index(p).view();
                &&& pre.prc_mp.spec_index(sender).view().iommu_table != Some(p) ==> after.did == before.did
                &&& after.mapping_4k().filter_keys(|va: VAddr| after.mapping_4k().spec_index(va).present) == before.mapping_4k().filter_keys(|va: VAddr| before.mapping_4k().spec_index(va).present)
                &&& after.mapping_2m().filter_keys(|va: VAddr| after.mapping_2m().spec_index(va).present) == before.mapping_2m().filter_keys(|va: VAddr| before.mapping_2m().spec_index(va).present)
                &&& after.mapping_1g().filter_keys(|va: VAddr| after.mapping_1g().spec_index(va).present) == before.mapping_1g().filter_keys(|va: VAddr| before.mapping_1g().spec_index(va).present)
            },
        pre.prc_mp.dom().contains(sender),
        pre.prc_mp.dom().contains(receiver),
        sender != receiver,
        post.prc_mp.dom() == pre.prc_mp.dom(),
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) ==> {
                let a = pre.prc_mp.spec_index(p);
                let b = post.prc_mp.spec_index(p);
                let pci = a.view_ghost().owned_pci_functions.view();
                &&& b.view().zombie == a.view().zombie
                &&& b.view().pagetable == a.view().pagetable
                &&& b.view().iommu_table == a.view().iommu_table
                &&& b.view_ghost().owned_pci_functions.view() == if p == sender { pci.remove(bdf) } else if p == receiver { pci.insert(bdf) } else { pci }
                &&& b.view().quota_4k == a.view().quota_4k
                &&& b.view().quota_2m == a.view().quota_2m
                &&& b.view().quota_1g == a.view().quota_1g
                &&& b.view().children.view() == a.view().children.view()
                &&& b.view_rodata().view().parent == a.view_rodata().view().parent
                &&& b.view_rodata().view().depth == a.view_rodata().view().depth
                &&& b.view_rodata().view().pcid == a.view_rodata().view().pcid
                &&& b.view_rodata().view().owning_container == a.view_rodata().view().owning_container
                &&& b.view_ghost().uppertree_seq.view() == a.view_ghost().uppertree_seq.view()
                &&& b.view_ghost().subtree_set.view() == a.view_ghost().subtree_set.view()
                &&& b.being_killed() == a.being_killed()
                &&& b.view().owned_threads.view() == a.view().owned_threads.view()
            },
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) && post.prc_mp.dom().contains(p) ==> post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) && post.pt_mp.dom().contains(p) ==> post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread(),
        forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
            pre.it_mp.dom().contains(p) && post.it_mp.dom().contains(p) ==> post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread(),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let post_u = kernel_k_user_projection(*post, include_lock_state);
            let s = pre_u.process_map.spec_index(sender);
            let r = pre_u.process_map.spec_index(receiver);
            let s_table = match s.iommu_table { Some(t) => Some(PageTableU { did: post_u.process_map.spec_index(sender).iommu_table->Some_0.did, ..t }), None => None };
            &&& post_u.process_map == pre_u.process_map.insert(sender, ProcessU { iommu_table: s_table, owned_pci_functions: s.owned_pci_functions.remove(bdf), ..s })
                .insert(receiver, ProcessU { owned_pci_functions: r.owned_pci_functions.insert(bdf), ..r })
        }),
{
    hide(kernel_k_user_projection);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    let s = pre_u.process_map.spec_index(sender);
    let r = pre_u.process_map.spec_index(receiver);
    let s_table = match s.iommu_table { Some(t) => Some(PageTableU { did: post_u.process_map.spec_index(sender).iommu_table->Some_0.did, ..t }), None => None };
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(sender, ProcessU { iommu_table: s_table, owned_pci_functions: s.owned_pci_functions.remove(bdf), ..s })
        .insert(receiver, ProcessU { owned_pci_functions: r.owned_pci_functions.insert(bdf), ..r }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_user_projection_at(pre, include_lock_state, p); } if post.prc_mp.dom().contains(p) { kernel_process_user_projection_at(post, include_lock_state, p); }
        process_pagetable_match_process_at(post.prc_mp, post.pt_mp, p); process_iommu_table_match_process_at(post.prc_mp, post.it_mp, p); process_iommu_table_match_process_at(post.prc_mp, post.it_mp, sender);
        reveal(kernel_pagetable_nonlock_fields_unchanged);
    });
}

/// The rendezvous fields project to the root table with only a handed-over PCI function owned, detached, by the receiver.
proof fn kernel_ipc_rendezvous_fields_implies_u_iommu_root_table(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, caller_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, peer_thread_ptr: RwLockThreadPtr, peer_result: RetValueType,
    cpu_transfer: Option<(CpuId, RwLockThreadPtr)>, pci_transfer: Option<(PciBdf, RwLockProcessPtr, RwLockProcessPtr)>, include_lock_state: bool,
)
    requires
        kernel_ipc_rendezvous_fields(pre, post, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let post_u = kernel_k_user_projection(*post, include_lock_state);
            post_u.iommu_root_table == match pci_transfer {
                Some((bdf, _, receiver)) => IommuRootTableU {
                    owners: seq3_update(pre_u.iommu_root_table.owners, bdf.0 as int, bdf.1 as int, bdf.2 as int, receiver),
                    attached: seq3_update(pre_u.iommu_root_table.attached, bdf.0 as int, bdf.1 as int, bdf.2 as int, false),
                },
                None => pre_u.iommu_root_table,
            }
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_ipc_rendezvous_fields); kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    pre.irt.view().user_view_unfold(); post.irt.view().user_view_unfold();
    if let Some((bdf, _, receiver)) = pci_transfer {
        let attached = seq3_update(pre_u.iommu_root_table.attached, bdf.0 as int, bdf.1 as int, bdf.2 as int, false);
        assert_seqs_equal!(post_u.iommu_root_table.attached == attached, b => {
            assert_seqs_equal!(post_u.iommu_root_table.attached[b] == attached[b], d => {
                assert_seqs_equal!(post_u.iommu_root_table.attached[b][d] == attached[b][d], f => {
                    assert((post.irt.view().spec_index_iommu_root(b as usize, d as usize, f as usize) is Some) == attached[b][d][f]);
                });
            });
        });
    }
}

/// The rendezvous fields project to the thread map with only the peer scheduled on its wake cpu with `peer_result`.
#[verifier::spinoff_prover]
proof fn kernel_ipc_rendezvous_fields_implies_u_thread_map(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, caller_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, peer_thread_ptr: RwLockThreadPtr, peer_result: RetValueType,
    cpu_transfer: Option<(CpuId, RwLockThreadPtr)>, pci_transfer: Option<(PciBdf, RwLockProcessPtr, RwLockProcessPtr)>, include_lock_state: bool,
)
    requires
        kernel_ipc_rendezvous_fields(pre, post, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer),
        forall|p: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(p)]
            pre.thr_mp.dom().contains(p) && post.thr_mp.dom().contains(p) ==> post.thr_mp.spec_index(p).locking_thread() == pre.thr_mp.spec_index(p).locking_thread(),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let post_u = kernel_k_user_projection(*post, include_lock_state);
            let peer = pre_u.thread_map.spec_index(peer_thread_ptr);
            let caller = pre_u.thread_map.spec_index(caller_thread_ptr);
            let wake_cpu = if peer.owning_container == caller.owning_container { cpu_id } else { peer.last_cpu };
            post_u.thread_map == pre_u.thread_map.insert(peer_thread_ptr, ThreadU {
                state: ThreadState::SCHEDULED { cpu_id: wake_cpu }, blocking_endpoint_ptr: None, ipc_payload: IPCPayLoad::Empty, error_code: Some(peer_result), ..peer
            })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_ipc_rendezvous_fields);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    if pre.thr_mp.dom().contains(caller_thread_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, caller_thread_ptr); } if pre.thr_mp.dom().contains(peer_thread_ptr) { kernel_thread_user_projection_at(pre, include_lock_state, peer_thread_ptr); }
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    let peer = pre_u.thread_map.spec_index(peer_thread_ptr);
    let caller = pre_u.thread_map.spec_index(caller_thread_ptr);
    let wake_cpu = if peer.owning_container == caller.owning_container { cpu_id } else { peer.last_cpu };
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(peer_thread_ptr, ThreadU {
        state: ThreadState::SCHEDULED { cpu_id: wake_cpu }, blocking_endpoint_ptr: None, ipc_payload: IPCPayLoad::Empty, error_code: Some(peer_result), ..peer
    }), t => { if pre.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(pre, include_lock_state, t); } if post.thr_mp.dom().contains(t) { kernel_thread_user_projection_at(post, include_lock_state, t); } });
}

/// The rendezvous fields project to the endpoint map with only the peer dequeued from the endpoint.
#[verifier::spinoff_prover]
proof fn kernel_ipc_rendezvous_fields_implies_u_endpoint_map(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, caller_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, peer_thread_ptr: RwLockThreadPtr, peer_result: RetValueType,
    cpu_transfer: Option<(CpuId, RwLockThreadPtr)>, pci_transfer: Option<(PciBdf, RwLockProcessPtr, RwLockProcessPtr)>, include_lock_state: bool,
)
    requires
        kernel_ipc_rendezvous_fields(pre, post, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer),
        forall|p: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(p)]
            pre.ep_mp.dom().contains(p) && post.ep_mp.dom().contains(p) ==> post.ep_mp.spec_index(p).locking_thread() == pre.ep_mp.spec_index(p).locking_thread(),
    ensures
        ({
            let pre_u = kernel_k_user_projection(*pre, include_lock_state);
            let post_u = kernel_k_user_projection(*post, include_lock_state);
            let endpoint = pre_u.endpoint_map.spec_index(endpoint_ptr);
            post_u.endpoint_map == pre_u.endpoint_map.insert(endpoint_ptr, EndpointU { queue: endpoint.queue.skip(1), ..endpoint })
        }),
{
    hide(kernel_k_user_projection);
    reveal(kernel_ipc_rendezvous_fields);
    kernel_u_user_domains_projection(pre, include_lock_state); kernel_u_user_domains_projection(post, include_lock_state);
    if pre.ep_mp.dom().contains(endpoint_ptr) { kernel_endpoint_user_projection_at(pre, include_lock_state, endpoint_ptr); }
    let pre_u = kernel_k_user_projection(*pre, include_lock_state);
    let post_u = kernel_k_user_projection(*post, include_lock_state);
    let endpoint = pre_u.endpoint_map.spec_index(endpoint_ptr);
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map.insert(endpoint_ptr, EndpointU { queue: endpoint.queue.skip(1), ..endpoint }), e => {
        if pre.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(pre, include_lock_state, e); }
        if post.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(post, include_lock_state, e); }
    });
}

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

/// Project thread publication together with releasing the caller's observable locks.
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
        post.thr_mp.spec_index(new_thread_ptr).locking_thread() is None,
    ensures
        ({
            let c = pre.cpu_arr.spec_index(cpu_id).value.view().view();
            kernel_k_to_kernel_u(*pre).cpu_array[cpu_id as int] == (CpuU {
                lock_state: pre.cpu_arr.spec_index(cpu_id).value.lock_state_u(), owning_container: c.owning_container, state: c.state,
                current_process: c.current_process, current_thread: c.current_thread, killed: pre.cpu_arr.spec_index(cpu_id).value.being_killed(),
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
            let old_u = kernel_k_to_kernel_u(*pre);
            let mode = LockStateU::Unlocked;
            kernel_u_new_thread_changed(KernelU {
                cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, ..old_u.cpu_array[cpu_id as int] }),
                process_map: match release_source_process {
                    Some(source) => old_u.process_map.insert(source, ProcessU {
                        pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[source].pagetable->Some_0 }), ..old_u.process_map[source]
                    }).insert(process_ptr, ProcessU {
                        lock_state: mode, pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[process_ptr].pagetable->Some_0 }),
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
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, ..old_u.cpu_array[cpu_id as int] }),
        process_map: match release_source_process {
            Some(source) => old_u.process_map.insert(source, ProcessU {
                pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[source].pagetable->Some_0 }), ..old_u.process_map[source]
            }).insert(process_ptr, ProcessU {
                lock_state: mode, pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[process_ptr].pagetable->Some_0 }),
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
    if index_valid(NUM_CPUS, cpu_id) { kernel_cpu_projection_at(post, cpu_id); } if index_valid(NUM_CPUS, cpu_id) { kernel_cpu_projection_at(pre, cpu_id); }
    if post.prc_mp.dom().contains(process_ptr) { kernel_process_projection_at(post, process_ptr); }
    if let Some(source) = release_source_process { if post.prc_mp.dom().contains(source) { kernel_process_projection_at(post, source); } }
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
        post.thr_mp.spec_index(new_thread_ptr).locking_thread() is None,
    ensures
        ({
            let c = pre.cpu_arr.spec_index(cpu_id).value.view().view();
            kernel_k_to_kernel_u(*pre).cpu_array[cpu_id as int] == (CpuU {
                lock_state: pre.cpu_arr.spec_index(cpu_id).value.lock_state_u(), owning_container: c.owning_container, state: c.state,
                current_process: c.current_process, current_thread: c.current_thread, killed: pre.cpu_arr.spec_index(cpu_id).value.being_killed(),
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
                cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, ..old_u.cpu_array[cpu_id as int] }),
                container_map: old_u.container_map.insert(release_source_container, ContainerU { lock_state: mode, lock_process_owner: None, ..old_u.container_map[release_source_container] })
                    .insert(container_ptr, ContainerU { lock_state: mode, lock_process_owner: None, ..old_u.container_map[container_ptr] }),
                process_map: old_u.process_map.insert(release_source_process, ProcessU {
                    lock_state: mode,
                    pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[release_source_process].pagetable->Some_0 }), ..old_u.process_map[release_source_process]
                }).insert(process_ptr, ProcessU {
                    lock_state: mode, pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[process_ptr].pagetable->Some_0 }),
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
        cpu_array: old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: mode, ..old_u.cpu_array[cpu_id as int] }),
        container_map: old_u.container_map.insert(release_source_container, ContainerU { lock_state: mode, lock_process_owner: None, ..old_u.container_map[release_source_container] })
            .insert(container_ptr, ContainerU { lock_state: mode, lock_process_owner: None, ..old_u.container_map[container_ptr] }),
        process_map: old_u.process_map.insert(release_source_process, ProcessU {
            lock_state: mode,
            pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[release_source_process].pagetable->Some_0 }), ..old_u.process_map[release_source_process]
        }).insert(process_ptr, ProcessU {
            lock_state: mode, pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[process_ptr].pagetable->Some_0 }),
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
    if index_valid(NUM_CPUS, cpu_id) { kernel_cpu_projection_at(pre, cpu_id); } if index_valid(NUM_CPUS, cpu_id) { kernel_cpu_projection_at(post, cpu_id); }
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

/// Thread publication with the caller's cpu released projects to the cpu array with only that cpu unlocked.
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
    ensures
        kernel_k_to_kernel_u(*post).cpu_array == kernel_k_to_kernel_u(*pre).cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..kernel_k_to_kernel_u(*pre).cpu_array[cpu_id as int] }),
{
    kernel_u_domains_projection(post); kernel_u_domains_projection(pre);
    let old_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    assert_seqs_equal!(post_u.cpu_array == old_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..old_u.cpu_array[cpu_id as int] }), i => {
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
/// source process, both page tables and the process's iommu table are unlocked too.
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
                    pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[source].pagetable->Some_0 }), ..old_u.process_map[source]
                }).insert(process_ptr, ProcessU {
                    lock_state: mode, pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[process_ptr].pagetable->Some_0 }),
                    iommu_table: match old_u.process_map[process_ptr].iommu_table { Some(t) => Some(PageTableU { lock_state: mode, ..t }), None => None },
                    ..old_u.process_map[process_ptr]
                }),
                None => old_u.process_map.insert(process_ptr, ProcessU { lock_state: mode, ..old_u.process_map[process_ptr] }),
            };
            let process = unlocked.spec_index(process_ptr);
            kernel_k_to_kernel_u(*post).process_map == unlocked.insert(process_ptr, ProcessU { owned_threads: process.owned_threads.push(new_thread_ptr), ..process })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let old_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let mode = LockStateU::Unlocked;
    let unlocked = match release_source_process {
        Some(source) => old_u.process_map.insert(source, ProcessU {
            pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[source].pagetable->Some_0 }), ..old_u.process_map[source]
        }).insert(process_ptr, ProcessU {
            lock_state: mode, pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[process_ptr].pagetable->Some_0 }),
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
/// parent process and both of their page tables unlocked.
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
                lock_state: mode,
                pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[release_source_process].pagetable->Some_0 }), ..old_u.process_map[release_source_process]
            }).insert(process_ptr, ProcessU {
                lock_state: mode, pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[process_ptr].pagetable->Some_0 }),
                iommu_table: None,
                ..old_u.process_map[process_ptr]
            });
            let process = unlocked.spec_index(process_ptr);
            kernel_k_to_kernel_u(*post).process_map == unlocked.insert(process_ptr, ProcessU { owned_threads: process.owned_threads.push(new_thread_ptr), ..process })
        }),
{
    reveal(kernel_new_thread_fields); kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let old_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let mode = LockStateU::Unlocked;
    let unlocked = old_u.process_map.insert(release_source_process, ProcessU {
        lock_state: mode,
        pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[release_source_process].pagetable->Some_0 }), ..old_u.process_map[release_source_process]
    }).insert(process_ptr, ProcessU {
        lock_state: mode, pagetable: Some(PageTableU { lock_state: mode, ..old_u.process_map[process_ptr].pagetable->Some_0 }),
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
