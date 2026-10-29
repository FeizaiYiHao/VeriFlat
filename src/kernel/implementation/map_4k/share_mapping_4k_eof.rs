use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::share_mapping_4k::{share_mapping_4k_leaf_owner_compatible, share_mapping_4k_target_map_with_shared_prefix, share_mapping_4k_target_range_empty_from, prove_share_mapping_4k_iteration_target_partition};
#[cfg(verus_keep_ghost)]
use super::share_mapping_4k_spec::{share_4k_range_step, share_4k_leaf_step_pre, share_4k_leaf_step};
#[cfg(verus_keep_ghost)]
use super::share_mapping_4k_trace::share_4k_range_steps_from_leaf;

verus! {
/// Copies the source 4K leaf `source_va` into `target_pagetable` at `target_va` and records `(target_pagetable, target_va)` on
/// the shared page `page_index`; the target, held in either mode, keeps its higher half and stale-CPU ledger, a write-held
/// target backs up the new lower half; every other kernel field is unchanged.
#[verifier::opaque]
pub(super) open spec fn share_one_mapping_4k_eof_transition_framing(
    pre: KernelK, post: KernelK, page_index: PageIndex, source_pagetable: RwLockPageTableRoot, source_va: VAddr, target_pagetable: RwLockPageTableRoot, target_va: VAddr,
) -> bool {
    let old_pt = pagetable_c(pre.pt_mp, pre.pt_lower.view(), target_pagetable);
    let new_pt = pagetable_c(post.pt_mp, post.pt_lower.view(), target_pagetable);
    let old_page = pre.pg_arr.spec_index(page_index).view();
    let new_page = post.pg_arr.spec_index(page_index).view();
    &&& post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, pg_arr: post.pg_arr, ..pre })
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, target_pagetable)
    &&& post.pt_lower.view() == pre.pt_lower.view().insert(target_pagetable, post.pt_lower.view().spec_index(target_pagetable))
    &&& forall|p: RwLockPageTableRoot| #![trigger pagetable_c(post.pt_mp, post.pt_lower.view(), p)]
        pre.pt_mp.dom().contains(p) && p != target_pagetable ==> pagetable_c(post.pt_mp, post.pt_lower.view(), p) == pagetable_c(pre.pt_mp, pre.pt_lower.view(), p)
    &&& post.pt_mp.spec_index(target_pagetable).locking_thread() == pre.pt_mp.spec_index(target_pagetable).locking_thread()
    &&& post.pt_mp.spec_index(target_pagetable).being_killed() == pre.pt_mp.spec_index(target_pagetable).being_killed()
    &&& post.pt_mp.spec_index(target_pagetable).view() == pre.pt_mp.spec_index(target_pagetable).view()
    &&& post.pt_mp.spec_index(target_pagetable).view_ghost()
        == if pre.pt_mp.spec_index(target_pagetable).wlocked() { post.pt_lower.view().spec_index(target_pagetable) } else { pre.pt_mp.spec_index(target_pagetable).view_ghost() }
    &&& new_pt.mapping_4k() == old_pt.mapping_4k().insert(target_va, pagetable_c(pre.pt_mp, pre.pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_va))
    &&& new_pt.mapping_2m() == old_pt.mapping_2m()
    &&& new_pt.mapping_1g() == old_pt.mapping_1g()
    &&& new_pt.page_closure() == old_pt.page_closure()
    &&& new_pt.lower.window_stale_cpus == old_pt.lower.window_stale_cpus
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_index)
    &&& new_page.locking_thread() == old_page.locking_thread()
    &&& new_page.being_killed() == old_page.being_killed()
    &&& new_page.view().mappings() == old_page.view().mappings().insert((target_pagetable, target_va))
    &&& new_page.view().iommu_mappings() == old_page.view().iommu_mappings()
    &&& new_page.view().ref_count == old_page.view().ref_count + 1
    &&& new_page.view().addr == old_page.view().addr
    &&& new_page.view().state == old_page.view().state
    &&& new_page.view().is_io_page == old_page.view().is_io_page
    &&& new_page.view().owning_container == old_page.view().owning_container
    &&& new_page.view().free_list_node_storage == old_page.view().free_list_node_storage
    &&& new_page.view().free_list == old_page.view().free_list
    &&& new_page.view().perm_4k.view() == old_page.view().perm_4k.view()
    &&& new_page.view().perm_2m.view() == old_page.view().perm_2m.view()
    &&& new_page.view().perm_1g.view() == old_page.view().perm_1g.view()
}

pub(super) proof fn share_one_mapping_4k_eof(
    pre: KernelK, post: KernelK, page_index: PageIndex, source_pagetable: RwLockPageTableRoot, source_va: VAddr, target_pagetable: RwLockPageTableRoot, target_va: VAddr,
    target_process: RwLockProcessPtr, target_container: RwLockContainerPtr, target_thread: RwLockThreadPtr,
)
    requires
        pre.inv(),
        share_one_mapping_4k_eof_transition_framing(pre, post, page_index, source_pagetable, source_va, target_pagetable, target_va),
        pre.pt_mp.dom().contains(source_pagetable),
        pre.pt_mp.dom().contains(target_pagetable),
        source_pagetable != target_pagetable,
        pagetable_c(pre.pt_mp, pre.pt_lower.view(), source_pagetable).mapping_4k().dom().contains(source_va),
        page_ptr_valid(pagetable_c(pre.pt_mp, pre.pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_va).addr),
        page_index == page_ptr2page_index(pagetable_c(pre.pt_mp, pre.pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_va).addr),
        index_valid(NUM_PAGES, page_index),
        pre.pg_arr.spec_index(page_index).view().view().state is Mapped4k,
        va_4k_valid(target_va),
        !pagetable_c(pre.pt_mp, pre.pt_lower.view(), target_pagetable).mapping_4k().dom().contains(target_va),
        pre.pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        pre.prc_mp.dom().contains(target_process),
        pre.prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container,
        share_mapping_4k_leaf_owner_compatible(&pre, source_pagetable, target_container, source_va),
        pre.thr_mp.dom().contains(target_thread),
        !thread_is_dangling(pre.thr_mp.spec_index(target_thread)),
        (pre.thr_mp.spec_index(target_thread).view().owning_proc == target_process && pre.thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable
            && !pre.thr_mp.spec_index(target_thread).view_ghost().exited)
            || (!pre.prc_mp.spec_index(target_process).view().zombie && !(pre.prc_mp.spec_index(target_process).view().state.view() is TablesEmptied)),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        page_array_wf(post.pg_arr),
        hugepage_2m_wf(post.pg_arr),
        hugepage_1g_wf(post.pg_arr),
    ensures post.inv(),
{
    reveal(share_one_mapping_4k_eof_transition_framing);
    let page_ptr = pagetable_c(pre.pt_mp, pre.pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_va).addr;
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by {
        assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { cpu_set_pages_wf_preserved_for_page_state_eq(pre.cpu_set_mp, post.cpu_set_mp, pre.pg_arr, post.pg_arr); };
        assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
            allocator_4k_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_4k_mp, post.allc_4k_mp);
            allocator_2m_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_2m_mp, post.allc_2m_mp);
            allocator_1g_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_1g_mp, post.allc_1g_mp);
        };
        assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
        assert(page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
            assert({
                let target_entry = pagetable_c(post.pt_mp, post.pt_lower.view(), target_pagetable).mapping_4k().spec_index(target_va);
                target_entry.owning_container.view() == post.pg_arr.spec_index(page_index).view().view().owning_container
            }) by { reveal(mapped_4k_page_pagetable_wf); };
            page_pagetable_wf_preserved_for_4k_mapping_insert(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr, target_pagetable, page_ptr, target_va);
        };
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by {
            assert({
                let owner = post.pg_arr.spec_index(page_index).view().view().owning_container;
                let mapping_process = post.pt_mp.spec_index(target_pagetable).view().proc_ptr;
                let mapping_container = post.prc_mp.spec_index(mapping_process).view_rodata().view().owning_container;
                &&& post.prc_mp.dom().contains(mapping_process)
                &&& post.ctn_mp.dom().contains(owner)
                &&& (mapping_container == owner || post.ctn_mp.spec_index(owner).view_ghost().subtree_set.view().contains(mapping_container))
            }) by { reveal(mapped_4k_page_pagetable_wf); reveal(container_uppertree_seq_wf); };
            container_process_page_pagetable_wf_preserved_for_4k_mapping_insert(post.ctn_mp, post.prc_mp, pre.pt_mp, post.pt_mp, pre.pg_arr, post.pg_arr, target_pagetable, page_ptr, target_va);
        };
        assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { page_iommu_table_wf_preserved_for_page_iommu_fields_eq(post.ctn_mp, post.prc_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
        assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.ctn_mp, post.ctn_mp); };
        assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { process_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.prc_mp, post.prc_mp); };
        assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
        assert(page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thr_mp)) by { reveal(page_object_owner_wf); reveal(container_page_owner_wf); };
        assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
            pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr);
        };
        assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { iommu_table_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
        assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
        assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
        assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.pcid_allc_mp, post.pcid_allc_mp); };
        assert(thread_staged_pages_wf(post.thr_mp, post.pg_arr)) by {
            thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
            thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
            thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        };
        assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
        assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_match); };
        assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
        assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp)) by {
            reveal(process_emptied_tables_wf); reveal(process_pagetable_match); process_thread_wf_at(pre.prc_mp, pre.thr_mp, target_thread);
            process_perms_wf_at(pre.prc_mp, target_process); process_emptied_threads_wf_at(pre.prc_mp, pre.thr_mp, target_process, target_thread);
        };
        assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(post.allc_4k_mp, pre.pg_arr, post.pg_arr, page_index); };
        assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, page_index); };
        assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, page_index); };
    };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_contains_pagetable_pcid_match); };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by {
        tlb_wf_spec_preserved_for_4k_mapping_insert(post.cpu_tlb, post.cpu_arr, pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), target_pagetable, target_va, post.pcid_needflush);
    };
}

/// Loop state of `share_mapping_4k_build_and_share` after its first `i` leaves: the trace grew by `i` share range steps, the last one
/// recorded the final source window and funding-thread state; held kernel objects and every held window's lock state are unchanged; the
/// source and funding threads changed only their syscall progress; the source table keeps its held windows; every held target window holds the
/// entry mapping with the first `i` source leaves shared and keeps its L2 resolution; a write-held target holds that whole mapping.
#[verifier::opaque]
pub(super) open spec fn share_mapping_4k_build_and_share_eol_loop_framing(
    pre: KernelK, post: KernelK, pre_lctx: &LocalContext, pre_steps: &KernelSteps, post_steps: &KernelSteps, i: nat, source_range: &VaRange4K, target_range: &VaRange4K,
    source_thread: RwLockThreadPtr, quota_thread: RwLockThreadPtr, progress_thread: RwLockThreadPtr, target_process: RwLockProcessPtr, target_container: RwLockContainerPtr, cpu_id: CpuId,
    source_pagetable: RwLockPageTableRoot, target_pagetable: RwLockPageTableRoot, source_write_held: bool, target_write_held: bool,
) -> bool {
    let old_source = pagetable_c(pre.pt_mp, pre.pt_lower.view(), source_pagetable);
    let new_source = pagetable_c(post.pt_mp, post.pt_lower.view(), source_pagetable);
    let old_target = pagetable_c(pre.pt_mp, pre.pt_lower.view(), target_pagetable);
    let new_target = pagetable_c(post.pt_mp, post.pt_lower.view(), target_pagetable);
    let source_process = pre.pt_mp.spec_index(source_pagetable).view().proc_ptr;
    let expected = share_mapping_4k_target_map_with_shared_prefix(old_source.mapping_4k(), old_target.mapping_4k(), source_range, target_range, i);
    &&& forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, pre_steps.view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, post_steps.view())
    &&& post_steps.view().len() == pre_steps.view().len() + i
    &&& forall|j: int| #![trigger post_steps.view()[j]] 0 <= j < pre_steps.view().len() ==> post_steps.view()[j] == pre_steps.view()[j]
    &&& forall|j: int| #![trigger post_steps.view()[j]] pre_steps.view().len() <= j < post_steps.view().len() ==> share_4k_range_step(post_steps.view()[j], cpu_id)
    &&& i > 0 ==> {
        &&& post_steps.view().last().new_u.process_map.dom().contains(source_process) && post_steps.view().last().new_u.process_map.spec_index(source_process).pagetable is Some
        &&& kernel_k_to_kernel_u(post).process_map.dom().contains(source_process) && kernel_k_to_kernel_u(post).process_map.spec_index(source_process).pagetable is Some
        &&& post_steps.view().last().new_u.process_map.spec_index(source_process).pagetable->Some_0.lock_state == kernel_k_to_kernel_u(post).process_map.spec_index(source_process).pagetable->Some_0.lock_state
    }
    &&& index_valid(NUM_CPUS, pre_lctx.cpu_id()) ==> post.cpu_hw_cr3_pcid[pre_lctx.cpu_id() as int].view() == pre.cpu_hw_cr3_pcid[pre_lctx.cpu_id() as int].view()
    &&& post.ctn_mp.spec_index(target_container).view_rodata() == pre.ctn_mp.spec_index(target_container).view_rodata()
    &&& held_containers_unchanged(pre.ctn_mp, post.ctn_mp, pre_lctx)
    &&& held_processes_unchanged(pre.prc_mp, post.prc_mp, pre_lctx)
    &&& held_endpoints_unchanged(pre.ep_mp, post.ep_mp, pre_lctx)
    &&& held_iommu_tables_unchanged(pre.it_mp, post.it_mp, pre_lctx)
    &&& held_cpus_unchanged(pre.cpu_arr, post.cpu_arr, pre_lctx)
    &&& held_pages_unchanged(pre.pg_arr, post.pg_arr, pre_lctx)
    &&& post.thr_mp.spec_index(source_thread).view() == (Thread { syscall_progress: post.thr_mp.spec_index(source_thread).view().syscall_progress, ..pre.thr_mp.spec_index(source_thread).view() })
    &&& post.thr_mp.spec_index(quota_thread).view() == (Thread { syscall_progress: post.thr_mp.spec_index(quota_thread).view().syscall_progress, ..pre.thr_mp.spec_index(quota_thread).view() })
    &&& progress_thread != source_thread ==> post.thr_mp.spec_index(source_thread).view() == pre.thr_mp.spec_index(source_thread).view()
    &&& progress_thread != quota_thread ==> post.thr_mp.spec_index(quota_thread).view() == pre.thr_mp.spec_index(quota_thread).view()
    &&& post.thr_mp.spec_index(source_thread).view_ghost() == pre.thr_mp.spec_index(source_thread).view_ghost()
    &&& post.thr_mp.spec_index(quota_thread).view_ghost() == pre.thr_mp.spec_index(quota_thread).view_ghost()
    &&& post.thr_mp.lock_id_by_key(quota_thread) == pre.thr_mp.lock_id_by_key(quota_thread)
    &&& source_write_held ==> new_source == old_source
    &&& !source_write_held ==> {
        &&& post.pt_mp.spec_index(source_pagetable).rlocked_by_thread(pre_lctx.thread_id())
        &&& post.pt_mp.spec_index(source_pagetable).being_killed() == pre.pt_mp.spec_index(source_pagetable).being_killed()
        &&& post.pt_mp.spec_index(source_pagetable).locking_thread()->Read_reader_map.spec_index(pre_lctx.thread_id())
            == pre.pt_mp.spec_index(source_pagetable).locking_thread()->Read_reader_map.spec_index(pre_lctx.thread_id())
    }
    &&& forall|w: WindowVa| #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((source_pagetable, w))]
        pre_lctx.pagetable_window_lock_map().dom().contains((source_pagetable, w)) ==> {
            &&& new_source.window_view(w) == old_source.window_view(w)
            &&& new_source.mapping_2m().dom().contains(w.va) == old_source.mapping_2m().dom().contains(w.va)
            &&& old_source.mapping_2m().dom().contains(w.va) ==> new_source.mapping_2m().spec_index(w.va) == old_source.mapping_2m().spec_index(w.va)
        }
    &&& forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger pagetable_c(post.pt_mp, post.pt_lower.view(), p).window_view(w)]
        pre_lctx.pagetable_window_lock_map().dom().contains((p, w)) && (p == source_pagetable || p == target_pagetable) ==> {
            &&& pagetable_c(post.pt_mp, post.pt_lower.view(), p).window_view(w).lock_state == pagetable_c(pre.pt_mp, pre.pt_lower.view(), p).window_view(w).lock_state
            &&& pagetable_c(post.pt_mp, post.pt_lower.view(), p).window_view(w).stale_cpus == pagetable_c(pre.pt_mp, pre.pt_lower.view(), p).window_view(w).stale_cpus
            &&& pagetable_c(pre.pt_mp, pre.pt_lower.view(), p).window_leaves_present(w) ==> pagetable_c(post.pt_mp, post.pt_lower.view(), p).window_leaves_present(w)
        }
    &&& forall|w: WindowVa, v: VAddr|
        #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((source_pagetable, w)), pagetable_c(post.pt_mp, post.pt_lower.view(), source_pagetable).mapping_4k().dom().contains(v)]
        pre_lctx.pagetable_window_lock_map().dom().contains((source_pagetable, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
            &&& new_source.mapping_4k().dom().contains(v) == old_source.mapping_4k().dom().contains(v)
            &&& old_source.mapping_4k().dom().contains(v) ==> new_source.mapping_4k().spec_index(v) == old_source.mapping_4k().spec_index(v)
        }
    &&& forall|w: WindowVa, v: VAddr|
        #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((target_pagetable, w)), pagetable_c(post.pt_mp, post.pt_lower.view(), target_pagetable).mapping_4k().dom().contains(v)]
        pre_lctx.pagetable_window_lock_map().dom().contains((target_pagetable, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
            &&& new_target.mapping_4k().dom().contains(v) == expected.dom().contains(v)
            &&& new_target.mapping_4k().dom().contains(v) ==> new_target.mapping_4k().spec_index(v) == expected.spec_index(v)
        }
    &&& forall|w: WindowVa| #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((target_pagetable, w))]
        pre_lctx.pagetable_window_lock_map().dom().contains((target_pagetable, w)) && pre.pt_mp.spec_index(target_pagetable).view().kernel_l4_end <= spec_v2l4index(w.va)
            && pei_valid(spec_v2l4index(w.va)) && pei_valid(spec_v2l3index(w.va)) && pei_valid(spec_v2l2index(w.va))
            ==> new_target.spec_resolve_mapping_l2(spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va)) == old_target.spec_resolve_mapping_l2(spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va))
    &&& share_mapping_4k_target_range_empty_from(expected, target_range, i as int)
    &&& i < source_range.len ==> !expected.dom().contains(target_range.view().spec_index(i as int))
    &&& target_write_held ==> {
        &&& new_target.mapping_2m() == old_target.mapping_2m()
        &&& new_target.mapping_1g() == old_target.mapping_1g()
        &&& old_target.leaves_present() ==> new_target.leaves_present()
        &&& new_target.lower.l2_lock == old_target.lower.l2_lock
        &&& new_target.lower.window_stale_cpus == old_target.lower.window_stale_cpus
        &&& new_target.mapping_4k() == expected
        &&& new_target.user_view(LockStateU::Unlocked).mapping_4k
            == share_mapping_4k_target_map_with_shared_prefix(old_source.user_view(LockStateU::Unlocked).mapping_4k, old_target.user_view(LockStateU::Unlocked).mapping_4k, source_range, target_range, i)
    }
}

/// Loop state after leaf `i + 1` of `share_mapping_4k_build_and_share`, from the state after leaf `i` and the effect of
/// `share_one_mapping_4k` on source leaf `source_va` and target slot `target_va`.
pub(super) proof fn share_mapping_4k_build_and_share_eol_step(
    pre: KernelK, mid: KernelK, post: KernelK, pre_lctx: &LocalContext, mid_lctx: &LocalContext, pre_steps: &KernelSteps, mid_steps: &KernelSteps, post_steps: &KernelSteps,
    i: usize, source_range: &VaRange4K, target_range: &VaRange4K, source_thread: RwLockThreadPtr, quota_thread: RwLockThreadPtr, progress_thread: RwLockThreadPtr,
    target_process: RwLockProcessPtr, target_container: RwLockContainerPtr, cpu_id: CpuId, source_pagetable: RwLockPageTableRoot, target_pagetable: RwLockPageTableRoot,
    source_write_held: bool, target_write_held: bool, source_va: VAddr, target_va: VAddr,
)
    requires
        share_mapping_4k_build_and_share_eol_loop_framing(pre, mid, pre_lctx, pre_steps, mid_steps, i as nat, source_range, target_range, source_thread, quota_thread,
            progress_thread, target_process, target_container, cpu_id, source_pagetable, target_pagetable, source_write_held, target_write_held),
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        i < source_range.len,
        source_va == source_range.view().spec_index(i as int),
        target_va == target_range.view().spec_index(i as int),
        typed_lock_maps_unchanged(pre_lctx, mid_lctx),
        mid_lctx.cpu_id() == pre_lctx.cpu_id(),
        mid_lctx.thread_id() == pre_lctx.thread_id(),
        progress_thread == source_thread || progress_thread == quota_thread,
        mid.pt_mp.spec_index(source_pagetable).view() == pre.pt_mp.spec_index(source_pagetable).view(),
        mid.pt_mp.spec_index(target_pagetable).view() == pre.pt_mp.spec_index(target_pagetable).view(),
        pagetable_c(pre.pt_mp, pre.pt_lower.view(), source_pagetable).mapping_4k().dom().contains(source_va),
        pagetable_c(pre.pt_mp, pre.pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_va).present,
        pagetable_c(mid.pt_mp, mid.pt_lower.view(), source_pagetable).mapping_4k().dom().contains(source_va),
        pagetable_c(mid.pt_mp, mid.pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_va) == pagetable_c(pre.pt_mp, pre.pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_va),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, mid_steps.view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, post_steps.view()),
        post_steps.view() == mid_steps.view().push(post_steps.view().last()),
        share_4k_leaf_step_pre(post_steps.view().last().old_u, cpu_id),
        share_4k_leaf_step(post_steps.view().last().old_u, post_steps.view().last().new_u, cpu_id),
        index_valid(NUM_CPUS, mid_lctx.cpu_id()) ==> post.cpu_hw_cr3_pcid[mid_lctx.cpu_id() as int].view() == mid.cpu_hw_cr3_pcid[mid_lctx.cpu_id() as int].view(),
        {
            let source_process = mid.pt_mp.spec_index(source_pagetable).view().proc_ptr;
            &&& post_steps.view().last().new_u.process_map.dom().contains(source_process) && post_steps.view().last().new_u.process_map.spec_index(source_process).pagetable is Some
            &&& kernel_k_to_kernel_u(post).process_map.dom().contains(source_process) && kernel_k_to_kernel_u(post).process_map.spec_index(source_process).pagetable is Some
            &&& post_steps.view().last().new_u.process_map.spec_index(source_process).pagetable->Some_0.lock_state == kernel_k_to_kernel_u(post).process_map.spec_index(source_process).pagetable->Some_0.lock_state
        },
        held_pages_unchanged(mid.pg_arr, post.pg_arr, mid_lctx),
        held_containers_unchanged(mid.ctn_mp, post.ctn_mp, mid_lctx),
        held_processes_unchanged(mid.prc_mp, post.prc_mp, mid_lctx),
        held_endpoints_unchanged(mid.ep_mp, post.ep_mp, mid_lctx),
        held_iommu_tables_unchanged(mid.it_mp, post.it_mp, mid_lctx),
        held_cpus_unchanged(mid.cpu_arr, post.cpu_arr, mid_lctx),
        post.thr_mp.lock_id_by_key(quota_thread) == mid.thr_mp.lock_id_by_key(quota_thread),
        post.thr_mp.spec_index(progress_thread).view() == (Thread { syscall_progress: post.thr_mp.spec_index(progress_thread).view().syscall_progress, ..mid.thr_mp.spec_index(progress_thread).view() }),
        post.thr_mp.spec_index(quota_thread).view_ghost() == mid.thr_mp.spec_index(quota_thread).view_ghost(),
        post.thr_mp.spec_index(source_thread).view_ghost() == mid.thr_mp.spec_index(source_thread).view_ghost(),
        progress_thread != quota_thread ==> post.thr_mp.spec_index(quota_thread).view() == mid.thr_mp.spec_index(quota_thread).view(),
        progress_thread != source_thread ==> post.thr_mp.spec_index(source_thread).view() == mid.thr_mp.spec_index(source_thread).view(),
        post.ctn_mp.spec_index(target_container).view_rodata() == mid.ctn_mp.spec_index(target_container).view_rodata(),
        source_write_held ==> pagetable_c(post.pt_mp, post.pt_lower.view(), source_pagetable) == pagetable_c(mid.pt_mp, mid.pt_lower.view(), source_pagetable),
        !source_write_held ==> {
            &&& post.pt_mp.spec_index(source_pagetable).rlocked_by_thread(mid_lctx.thread_id())
            &&& post.pt_mp.spec_index(source_pagetable).being_killed() == mid.pt_mp.spec_index(source_pagetable).being_killed()
            &&& post.pt_mp.spec_index(source_pagetable).locking_thread()->Read_reader_map.spec_index(mid_lctx.thread_id())
                == mid.pt_mp.spec_index(source_pagetable).locking_thread()->Read_reader_map.spec_index(mid_lctx.thread_id())
        },
        forall|w: WindowVa| #![trigger mid_lctx.pagetable_window_lock_map().dom().contains((source_pagetable, w))]
            mid_lctx.pagetable_window_lock_map().dom().contains((source_pagetable, w)) ==> {
                &&& pagetable_c(post.pt_mp, post.pt_lower.view(), source_pagetable).window_view(w) == pagetable_c(mid.pt_mp, mid.pt_lower.view(), source_pagetable).window_view(w)
                &&& pagetable_c(post.pt_mp, post.pt_lower.view(), source_pagetable).mapping_2m().dom().contains(w.va) == pagetable_c(mid.pt_mp, mid.pt_lower.view(), source_pagetable).mapping_2m().dom().contains(w.va)
                &&& pagetable_c(mid.pt_mp, mid.pt_lower.view(), source_pagetable).mapping_2m().dom().contains(w.va)
                    ==> pagetable_c(post.pt_mp, post.pt_lower.view(), source_pagetable).mapping_2m().spec_index(w.va) == pagetable_c(mid.pt_mp, mid.pt_lower.view(), source_pagetable).mapping_2m().spec_index(w.va)
            },
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger pagetable_c(post.pt_mp, post.pt_lower.view(), p).window_view(w)]
            mid_lctx.pagetable_window_lock_map().dom().contains((p, w)) && (p == source_pagetable || p == target_pagetable) ==> {
                &&& pagetable_c(post.pt_mp, post.pt_lower.view(), p).window_view(w).lock_state == pagetable_c(mid.pt_mp, mid.pt_lower.view(), p).window_view(w).lock_state
                &&& pagetable_c(post.pt_mp, post.pt_lower.view(), p).window_view(w).stale_cpus == pagetable_c(mid.pt_mp, mid.pt_lower.view(), p).window_view(w).stale_cpus
                &&& pagetable_c(mid.pt_mp, mid.pt_lower.view(), p).window_leaves_present(w) ==> pagetable_c(post.pt_mp, post.pt_lower.view(), p).window_leaves_present(w)
            },
        forall|w: WindowVa, v: VAddr|
            #![trigger mid_lctx.pagetable_window_lock_map().dom().contains((source_pagetable, w)), pagetable_c(post.pt_mp, post.pt_lower.view(), source_pagetable).mapping_4k().dom().contains(v)]
            mid_lctx.pagetable_window_lock_map().dom().contains((source_pagetable, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
                &&& pagetable_c(post.pt_mp, post.pt_lower.view(), source_pagetable).mapping_4k().dom().contains(v) == pagetable_c(mid.pt_mp, mid.pt_lower.view(), source_pagetable).mapping_4k().dom().contains(v)
                &&& pagetable_c(mid.pt_mp, mid.pt_lower.view(), source_pagetable).mapping_4k().dom().contains(v)
                    ==> pagetable_c(post.pt_mp, post.pt_lower.view(), source_pagetable).mapping_4k().spec_index(v) == pagetable_c(mid.pt_mp, mid.pt_lower.view(), source_pagetable).mapping_4k().spec_index(v)
            },
        forall|w: WindowVa, v: VAddr|
            #![trigger mid_lctx.pagetable_window_lock_map().dom().contains((target_pagetable, w)), pagetable_c(post.pt_mp, post.pt_lower.view(), target_pagetable).mapping_4k().dom().contains(v)]
            mid_lctx.pagetable_window_lock_map().dom().contains((target_pagetable, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
                let shared = pagetable_c(mid.pt_mp, mid.pt_lower.view(), target_pagetable).mapping_4k().insert(target_va, pagetable_c(mid.pt_mp, mid.pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_va));
                &&& pagetable_c(post.pt_mp, post.pt_lower.view(), target_pagetable).mapping_4k().dom().contains(v) == shared.dom().contains(v)
                &&& pagetable_c(post.pt_mp, post.pt_lower.view(), target_pagetable).mapping_4k().dom().contains(v) ==> pagetable_c(post.pt_mp, post.pt_lower.view(), target_pagetable).mapping_4k().spec_index(v) == shared.spec_index(v)
            },
        forall|w: WindowVa|
            #![trigger mid_lctx.pagetable_window_lock_map().dom().contains((target_pagetable, w))]
            mid_lctx.pagetable_window_lock_map().dom().contains((target_pagetable, w)) && mid.pt_mp.spec_index(target_pagetable).view().kernel_l4_end <= spec_v2l4index(w.va)
                && pei_valid(spec_v2l4index(w.va)) && pei_valid(spec_v2l3index(w.va)) && pei_valid(spec_v2l2index(w.va))
                ==> pagetable_c(post.pt_mp, post.pt_lower.view(), target_pagetable).spec_resolve_mapping_l2(spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va))
                    == pagetable_c(mid.pt_mp, mid.pt_lower.view(), target_pagetable).spec_resolve_mapping_l2(spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va)),
        target_write_held ==> {
            &&& pagetable_c(post.pt_mp, post.pt_lower.view(), target_pagetable).mapping_4k()
                == pagetable_c(mid.pt_mp, mid.pt_lower.view(), target_pagetable).mapping_4k().insert(target_va, pagetable_c(mid.pt_mp, mid.pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_va))
            &&& pagetable_c(post.pt_mp, post.pt_lower.view(), target_pagetable).user_view(LockStateU::Unlocked).mapping_4k
                == pagetable_c(mid.pt_mp, mid.pt_lower.view(), target_pagetable).user_view(LockStateU::Unlocked).mapping_4k.insert(target_va,
                    pagetable_c(mid.pt_mp, mid.pt_lower.view(), source_pagetable).user_view(LockStateU::Unlocked).mapping_4k.spec_index(source_va))
            &&& pagetable_c(post.pt_mp, post.pt_lower.view(), target_pagetable).mapping_2m() == pagetable_c(mid.pt_mp, mid.pt_lower.view(), target_pagetable).mapping_2m()
            &&& pagetable_c(post.pt_mp, post.pt_lower.view(), target_pagetable).mapping_1g() == pagetable_c(mid.pt_mp, mid.pt_lower.view(), target_pagetable).mapping_1g()
            &&& pagetable_c(post.pt_mp, post.pt_lower.view(), target_pagetable).lower.l2_lock == pagetable_c(mid.pt_mp, mid.pt_lower.view(), target_pagetable).lower.l2_lock
            &&& pagetable_c(post.pt_mp, post.pt_lower.view(), target_pagetable).lower.window_stale_cpus == pagetable_c(mid.pt_mp, mid.pt_lower.view(), target_pagetable).lower.window_stale_cpus
        },
    ensures
        share_mapping_4k_build_and_share_eol_loop_framing(pre, post, pre_lctx, pre_steps, post_steps, (i + 1) as nat, source_range, target_range, source_thread, quota_thread,
            progress_thread, target_process, target_container, cpu_id, source_pagetable, target_pagetable, source_write_held, target_write_held),
{
    reveal(share_mapping_4k_build_and_share_eol_loop_framing);
    share_4k_range_steps_from_leaf(post_steps, mid_steps.view(), pre_steps.view().len() as int, cpu_id);
    prove_share_mapping_4k_iteration_target_partition(pagetable_c(pre.pt_mp, pre.pt_lower.view(), source_pagetable).mapping_4k(), pagetable_c(pre.pt_mp, pre.pt_lower.view(), target_pagetable).mapping_4k(),
        source_range, target_range, i, pre_lctx.pagetable_window_lock_map().dom(), target_pagetable, pagetable_c(mid.pt_mp, mid.pt_lower.view(), target_pagetable).mapping_4k(),
        pagetable_c(post.pt_mp, post.pt_lower.view(), target_pagetable).mapping_4k(), pagetable_c(mid.pt_mp, mid.pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_va));
    if target_write_held {
        assert(pagetable_c(post.pt_mp, post.pt_lower.view(), target_pagetable).user_view(LockStateU::Unlocked).mapping_4k == share_mapping_4k_target_map_with_shared_prefix(
            pagetable_c(pre.pt_mp, pre.pt_lower.view(), source_pagetable).user_view(LockStateU::Unlocked).mapping_4k,
            pagetable_c(pre.pt_mp, pre.pt_lower.view(), target_pagetable).user_view(LockStateU::Unlocked).mapping_4k, source_range, target_range, (i + 1) as nat)) by {
            assert(pagetable_c(mid.pt_mp, mid.pt_lower.view(), source_pagetable).user_view(LockStateU::Unlocked).mapping_4k.spec_index(source_va)
                == pagetable_c(pre.pt_mp, pre.pt_lower.view(), source_pagetable).user_view(LockStateU::Unlocked).mapping_4k.spec_index(source_va));
            reveal(share_mapping_4k_target_map_with_shared_prefix);
        };
    }
}
}
