use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal, assert_sets_equal};
use crate::*;

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
        post.cpu_op.view().view() == pre.cpu_op.view().view(),
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
        post.cpu_op.view().view() == pre.cpu_op.view().view(),
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
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    assert(post.irt.view().user_view() == pre.irt.view().user_view() && post.dflt_pt == pre.dflt_pt) by {
        reveal(IommuRootTable::user_view); reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
    };
    kernel_lock_states_unchanged_implies_u_cpu_array(pre, post);
    kernel_lock_states_unchanged_implies_u_container_map(pre, post);
    kernel_lock_states_unchanged_except_tables_of_implies_u_process_map(pre, post, zombie);
    kernel_lock_states_unchanged_implies_u_thread_map(pre, post);
    kernel_lock_states_unchanged_implies_u_endpoint_map(pre, post);
}

/// Unchanged cpu non-lock fields, operation states, and cpu lock modes leave the projected cpu array unchanged.
proof fn kernel_lock_states_unchanged_implies_u_cpu_array(pre: &KernelK, post: &KernelK)
    requires
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post),
        post.cpu_op.view().view() == pre.cpu_op.view().view(),
        forall|i: CpuId| #![trigger post.cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> {
                let before = pre.cpu_arr.spec_index(i).value.locking_thread();
                let after = post.cpu_arr.spec_index(i).value.locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
            },
    ensures kernel_k_to_kernel_u(*pre).cpu_array == kernel_k_to_kernel_u(*post).cpu_array,
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    assert_seqs_equal!(before.cpu_array == after.cpu_array, i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); }
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
    });
}

/// Unchanged container non-lock fields, quotas, lock modes, and lock owners leave the projected container map unchanged.
pub(super) proof fn kernel_lock_states_unchanged_implies_u_container_map(pre: &KernelK, post: &KernelK)
    requires
        kernel_container_nonlock_fields_and_quotas_unchanged(pre, post),
        forall|p: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(p)]
            post.ctn_mp.dom().contains(p) && pre.ctn_mp.dom().contains(p) ==> {
                let before = pre.ctn_mp.spec_index(p).locking_thread();
                let after = post.ctn_mp.spec_index(p).locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
                &&& post.ctn_mp.spec_index(p).lock_process_owner_u() == pre.ctn_mp.spec_index(p).lock_process_owner_u()
            },
    ensures kernel_k_to_kernel_u(*pre).container_map == kernel_k_to_kernel_u(*post).container_map,
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    assert_maps_equal!(before.container_map, after.container_map, p => {
        if pre.ctn_mp.dom().contains(p) { kernel_container_projection_at(pre, p); } if post.ctn_mp.dom().contains(p) { kernel_container_projection_at(post, p); }
        reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
    });
}

/// Unchanged process, page-table, and IOMMU-table non-lock fields and lock modes, except on the tables of the zombie
/// process `zombie`, if any, leave the projected process map unchanged.
proof fn kernel_lock_states_unchanged_except_tables_of_implies_u_process_map(pre: &KernelK, post: &KernelK, zombie: Option<RwLockProcessPtr>)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        zombie is Some ==> post.prc_mp.dom().contains(zombie->Some_0),
        zombie is Some ==> post.prc_mp.spec_index(zombie->Some_0).view().zombie,
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post),
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
    ensures kernel_k_to_kernel_u(*pre).process_map == kernel_k_to_kernel_u(*post).process_map,
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    assert_maps_equal!(before.process_map, after.process_map, p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); }
        process_pagetable_match_process_at(post.prc_mp, post.pt_mp, p); process_iommu_table_match_process_at(post.prc_mp, post.it_mp, p);
        if zombie is Some { process_pagetable_match_process_at(post.prc_mp, post.pt_mp, zombie->Some_0); process_iommu_table_match_process_at(post.prc_mp, post.it_mp, zombie->Some_0); }
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged);
        reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
    });
}

/// Unchanged thread non-lock fields and lock modes leave the projected thread map unchanged.
proof fn kernel_lock_states_unchanged_implies_u_thread_map(pre: &KernelK, post: &KernelK)
    requires
        kernel_cpu_process_thread_nonlock_fields_unchanged(pre, post),
        forall|p: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(p)]
            post.thr_mp.dom().contains(p) && pre.thr_mp.dom().contains(p) ==> {
                let before = pre.thr_mp.spec_index(p).locking_thread();
                let after = post.thr_mp.spec_index(p).locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
            },
    ensures kernel_k_to_kernel_u(*pre).thread_map == kernel_k_to_kernel_u(*post).thread_map,
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    assert_maps_equal!(before.thread_map, after.thread_map, p => {
        if pre.thr_mp.dom().contains(p) { kernel_thread_projection_at(pre, p); } if post.thr_mp.dom().contains(p) { kernel_thread_projection_at(post, p); }
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
    });
}

/// Unchanged endpoint non-lock fields and lock modes leave the projected endpoint map unchanged.
proof fn kernel_lock_states_unchanged_implies_u_endpoint_map(pre: &KernelK, post: &KernelK)
    requires
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        forall|p: RwLockEndpointPtr| #![trigger post.ep_mp.spec_index(p)]
            post.ep_mp.dom().contains(p) && pre.ep_mp.dom().contains(p) ==> {
                let before = pre.ep_mp.spec_index(p).locking_thread();
                let after = post.ep_mp.spec_index(p).locking_thread();
                &&& (after is Write) == (before is Write)
                &&& (after is Read) == (before is Read)
            },
    ensures kernel_k_to_kernel_u(*pre).endpoint_map == kernel_k_to_kernel_u(*post).endpoint_map,
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
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
            state: CpuState::Running, op: CpuOpState::Trap, current_process: Some(next.owning_proc), current_thread: Some(next_thread), ..cpu
        }),
        container_map: pre_u.container_map.insert(cpu.owning_container, ContainerU {
            scheduler: container.scheduler.update(cpu_id as int, match cpu.current_thread { Some(prev) => run_queue.skip(1).push(prev), None => run_queue.skip(1) }),
            ..container
        }),
        thread_map: requeued.insert(next_thread, ThreadU { state: ThreadState::RUNNING { cpu_id }, last_cpu: cpu_id, error_code: None, trap_frame: None, ..next }),
        cpu_tlb: match flushed_pcid {
            Some(pcid) => pre_u.cpu_tlb.insert((cpu_id, pcid), post_u.cpu_tlb[(cpu_id, pcid)]),
            None => pre_u.cpu_tlb,
        },
        ..pre_u
    })) by {
        reveal(kernel_context_switch_fields); reveal(kernel_endpoint_nonlock_fields_unchanged);
        assert(post_u.iommu_root_table == pre_u.iommu_root_table) by { reveal(IommuRootTable::user_view); };
        assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => { if pre.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(pre, include_lock_state, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_user_projection_at(post, include_lock_state, e); } });
    };
    if let Some(pcid) = flushed_pcid {
        assert(cpu_tlb_within_may_cache(*post, cpu_id, pcid, post.cpu_tlb.spec_index((cpu_id, pcid)))) by { reveal(kernel_context_switch_fields); };
        kernel_cpu_tlb_within_may_cache_projection(post, include_lock_state, cpu_id, pcid, post.cpu_tlb.spec_index((cpu_id, pcid)));
    }
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
                state: CpuState::Running, op: CpuOpState::Trap, current_process: Some(pre_u.thread_map.spec_index(next_thread).owning_proc), current_thread: Some(next_thread), ..cpu
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
        state: CpuState::Running, op: CpuOpState::Trap, current_process: Some(pre_u.thread_map.spec_index(next_thread).owning_proc), current_thread: Some(next_thread), ..cpu
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
        post.cpu_arr.entries_unchanged_except(&pre.cpu_arr, cpu),
        post.cpu_op.view().view() == pre.cpu_op.view().view(),
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
        after.cpu_op.view().view() == before.cpu_op.view().view(),
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
        *after == (KernelK { cpu_arr: after.cpu_arr, cpu_op: after.cpu_op, prc_mp: after.prc_mp, thr_mp: after.thr_mp, ep_mp: after.ep_mp, sched_mp: after.sched_mp, ..*before }),
        kernel_cpu_nonlock_fields_unchanged(before.cpu_arr, after.cpu_arr),
        forall|i: CpuId| #![trigger after.cpu_op.view().view()[i as int]] index_valid(NUM_CPUS, i) && i != cpu_id ==> after.cpu_op.view().view()[i as int] == before.cpu_op.view().view()[i as int],
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
                cpu_array: pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: after.cpu_op.view().view()[cpu_id as int], ..pre.cpu_array[cpu_id as int] }),
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
        forall|i: CpuId| #![trigger after.cpu_op.view().view()[i as int]] index_valid(NUM_CPUS, i) && i != cpu_id ==> after.cpu_op.view().view()[i as int] == before.cpu_op.view().view()[i as int],
        after.cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        forall|i: CpuId| #![trigger after.cpu_arr.spec_index(i)] index_valid(NUM_CPUS, i) && i != cpu_id ==>
            after.cpu_arr.spec_index(i).value.locking_thread() == before.cpu_arr.spec_index(i).value.locking_thread(),
    ensures
        ({
            let pre = kernel_k_to_kernel_u(*before);
            kernel_k_to_kernel_u(*after).cpu_array == pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: after.cpu_op.view().view()[cpu_id as int], ..pre.cpu_array[cpu_id as int] })
        }),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after); reveal(kernel_cpu_nonlock_fields_unchanged);
    let pre = kernel_k_to_kernel_u(*before);
    let post = kernel_k_to_kernel_u(*after);
    assert_seqs_equal!(post.cpu_array == pre.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: after.cpu_op.view().view()[cpu_id as int], ..pre.cpu_array[cpu_id as int] }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(before, i as usize); kernel_cpu_projection_at(after, i as usize); }
    });
}

/// The peer-scheduled transition leaves the process map projection unchanged.
proof fn kernel_peer_scheduled_and_locks_released_implies_u_process_map(
    before: &KernelK, after: &KernelK, cpu_id: CpuId, caller: RwLockThreadPtr, peer: RwLockThreadPtr,
    wake_cpu: CpuId, endpoint: RwLockEndpointPtr, result: RetValueType, dequeue: bool, descriptor: Option<(RwLockThreadPtr, EndpointIdx)>,
)
    requires
        *after == (KernelK { cpu_arr: after.cpu_arr, cpu_op: after.cpu_op, prc_mp: after.prc_mp, thr_mp: after.thr_mp, ep_mp: after.ep_mp, sched_mp: after.sched_mp, ..*before }),
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
        *after == (KernelK { cpu_arr: after.cpu_arr, cpu_op: after.cpu_op, prc_mp: after.prc_mp, thr_mp: after.thr_mp, ep_mp: after.ep_mp, sched_mp: after.sched_mp, ..*before }),
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

} // verus!
