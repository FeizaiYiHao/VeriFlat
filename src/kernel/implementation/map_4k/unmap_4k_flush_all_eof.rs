use vstd::prelude::*;
use crate::*;

verus! {
/// A cpu outside the cpu set of the container `ctn_ptr` holds nothing for `pcid` of the process `prc_ptr` of
/// that container that a flush would remove: its TLB and its paging-structure cache for `pcid` are each empty, marked for
/// a flush while it runs another PCID, or dirty for another page table.
pub(super) proof fn cpu_outside_container_implies_no_tlb_of_container_pagetable(krnl: &KernelK, ctn_ptr: RwLockContainerPtr, prc_ptr: RwLockProcessPtr, cpu_id: CpuId, pcid: Pcid)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        krnl.ctn_mp.dom().contains(ctn_ptr),
        krnl.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view().contains(prc_ptr),
        !krnl.cpu_set_mp.spec_index(krnl.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).view().owned_cpus.view().contains(cpu_id),
    ensures
        krnl.cpu_tlb.spec_index((cpu_id, pcid)).is_empty()
            || (krnl.pcid_needflush.spec_index(cpu_id, pcid).view().needflush && krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid)
            || (krnl.cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some
                && krnl.cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr != krnl.prc_mp.spec_index(prc_ptr).view().pagetable),
        krnl.cpu_tlb.structure_cache((cpu_id, pcid)).is_empty()
            || (krnl.pcid_needflush.spec_index(cpu_id, pcid).view().needflush && krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid)
            || (krnl.cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some
                && krnl.cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr != krnl.prc_mp.spec_index(prc_ptr).view().pagetable),
{
    let cpu = krnl.cpu_arr.spec_index(cpu_id).view().view();
    container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id);
    if (!krnl.cpu_tlb.spec_index((cpu_id, pcid)).is_empty() || !krnl.cpu_tlb.structure_cache((cpu_id, pcid)).is_empty())
        && !(krnl.pcid_needflush.spec_index(cpu_id, pcid).view().needflush && cpu.view().current_pcid != pcid) {
        reveal(cpu_dirty_map_covers_nonempty_tlb); reveal(cpu_dirty_map_process_in_cpu_container); reveal(cpu_dirty_map_proc_pcid_match);
        let dirty = cpu.tlb_dirty_bitmap().spec_index(pcid).unwrap();
        container_process_wf_container_at(krnl.ctn_mp, krnl.prc_mp, ctn_ptr, prc_ptr); container_process_wf_container_at(krnl.ctn_mp, krnl.prc_mp, cpu.view().owning_container, dirty.process_ptr);
        process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, dirty.process_ptr);
    }
}

/// Loop state of `flush_pagetable_tlbs` after its first `flushed` cpus: the trace grew by at most one step per cpu, each
/// read-locking the cpu set of container `ctn_ptr` and clearing at most one cpu's TLB for `pcid` while the thread
/// `thrd_ptr`, its process `pre` names, and the process and container locks `held` keeps stay as in `pre`; the containers,
/// IOMMU tables, pages, and cpus `held` holds, and the lock and kill state of cpu `local_cpu`, are unchanged; table
/// `pagetable` keeps its kill mark, the reader entry of `held`'s cpu, and, unless `table_write_held`, its higher half; every window
/// of it that `held` holds keeps its lock state, L1 table, L2 entry, and 2M and 4K mappings.
#[verifier::opaque]
pub(super) open spec fn flush_pagetable_tlbs_eol_loop_framing(pre: KernelK, cur: KernelK, held: &LocalContext, pre_steps: &KernelSteps, cur_steps: &KernelSteps, snaps: Seq<KernelK>, flushed: nat,
    pagetable: RwLockPageTableRoot, pcid: Pcid, local_cpu: CpuId, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, table_write_held: bool) -> bool
{
    let old_table = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let new_table = whole_pagetable(cur.pt_mp, cur.pt_lower.view(), pagetable);
    &&& pre_steps.view().len() <= cur_steps.view().len() <= pre_steps.view().len() + flushed
    &&& forall|j: int| #![trigger cur_steps.view()[j]] 0 <= j < pre_steps.view().len() ==> cur_steps.view()[j] == pre_steps.view()[j]
    &&& cur_steps.view().len() == pre_steps.view().len() + snaps.len()
    &&& forall|k: int| #![trigger snaps[k]] 0 <= k < snaps.len() ==> {
        let s = snaps[k];
        let step = cur_steps.view()[pre_steps.view().len() + k];
        &&& step.old_u == kernel_k_to_kernel_u(s)
        &&& unmap_4k_tlb_flush_step(step.old_u, step.new_u, local_cpu)
        &&& s.inv()
        &&& held_threads_unchanged(pre.thrd_mp, s.thrd_mp, held)
        &&& held_processes_unchanged(pre.prc_mp, s.prc_mp, held)
        &&& held_containers_unchanged(pre.ctn_mp, s.ctn_mp, held)
        &&& s.ctn_mp.dom().contains(ctn_ptr)
        &&& s.cpu_arr.spec_index(local_cpu).view().locking_thread() == pre.cpu_arr.spec_index(local_cpu).view().locking_thread()
        &&& s.cpu_arr.spec_index(local_cpu).view().view().view().current_thread == Some(thrd_ptr)
        &&& s.cpu_op.view().view()[local_cpu as int] == pre.cpu_op.view().view()[local_cpu as int]
        &&& pre.cpu_trap_frame.view().view().dom().contains(local_cpu) ==> s.cpu_trap_frame.view().view()[local_cpu] == pre.cpu_trap_frame.view().view()[local_cpu]
        &&& s.pt_mp.dom().contains(pagetable)
        &&& s.pt_mp.spec_index(pagetable).view().higher == (PageTableHigher { table_stale_cpus: s.pt_mp.spec_index(pagetable).view().higher.table_stale_cpus,
            ..pre.pt_mp.spec_index(pagetable).view().higher })
        &&& s.pt_mp.spec_index(pagetable).locked_by_thread(held.thread_id())
        &&& !(s.cpu_set_mp.spec_index(s.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).lock_state_u() is WriteLocked)
        &&& typed_lock_map_contains_mode(held.pagetable_lock_map(), pagetable, TypedLockMode::Write) ==> {
            &&& s.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread()
            &&& whole_pagetable(s.pt_mp, s.pt_lower.view(), pagetable).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k()
            &&& whole_pagetable(s.pt_mp, s.pt_lower.view(), pagetable).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m()
            &&& whole_pagetable(s.pt_mp, s.pt_lower.view(), pagetable).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_1g()
            &&& whole_pagetable(s.pt_mp, s.pt_lower.view(), pagetable).lower.pagetable_window_locks == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.pagetable_window_locks
            &&& s.pt_mp.spec_index(pagetable).view().higher.pci.mapping_counts() == pre.pt_mp.spec_index(pagetable).view().higher.pci.mapping_counts()
        }
    }
    &&& held_containers_unchanged(pre.ctn_mp, cur.ctn_mp, held)
    &&& held_iommu_tables_unchanged(pre.it_mp, cur.it_mp, held)
    &&& held_pages_unchanged(pre.pg_arr, cur.pg_arr, held)
    &&& forall|held_cpu_id: CpuId| #![trigger held.cpu_lock_map().dom().contains(held_cpu_id)]
        held.cpu_lock_map().dom().contains(held_cpu_id) ==> cur.cpu_arr.spec_index(held_cpu_id).view().view() == pre.cpu_arr.spec_index(held_cpu_id).view().view()
    &&& cur.cpu_arr.spec_index(local_cpu).view().locking_thread() == pre.cpu_arr.spec_index(local_cpu).view().locking_thread()
    &&& cur.cpu_arr.spec_index(local_cpu).view().being_killed() == pre.cpu_arr.spec_index(local_cpu).view().being_killed()
    &&& cur.cpu_arr.spec_index(local_cpu).view().killer_info() == pre.cpu_arr.spec_index(local_cpu).view().killer_info()
    &&& !table_write_held ==> cur.pt_mp.spec_index(pagetable).view() == pre.pt_mp.spec_index(pagetable).view()
    &&& cur.pt_mp.spec_index(pagetable).being_killed() == pre.pt_mp.spec_index(pagetable).being_killed()
    &&& typed_lock_map_contains_mode(held.pagetable_lock_map(), pagetable, TypedLockMode::Read) ==> cur.pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.spec_index(held.thread_id())
        == pre.pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.spec_index(held.thread_id())
    &&& forall|w: WindowVa| #![trigger held.pagetable_window_lock_map().dom().contains((pagetable, w))] held.pagetable_window_lock_map().dom().contains((pagetable, w)) ==> {
        &&& new_table.window_view(w).lock_state == old_table.window_view(w).lock_state
        &&& new_table.window_view(w).l1_table == old_table.window_view(w).l1_table
        &&& new_table.window_view(w).l2_entry == old_table.window_view(w).l2_entry
        &&& new_table.mapping_2m().dom().contains(w.va) == old_table.mapping_2m().dom().contains(w.va)
        &&& old_table.mapping_2m().dom().contains(w.va) ==> new_table.mapping_2m().spec_index(w.va) == old_table.mapping_2m().spec_index(w.va)
    }
    &&& forall|w: WindowVa, v: VAddr|
        #![trigger held.pagetable_window_lock_map().dom().contains((pagetable, w)), whole_pagetable(cur.pt_mp, cur.pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
        #![trigger held.pagetable_window_lock_map().dom().contains((pagetable, w)), whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
        held.pagetable_window_lock_map().dom().contains((pagetable, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
            &&& new_table.mapping_4k().dom().contains(v) == old_table.mapping_4k().dom().contains(v)
            &&& old_table.mapping_4k().dom().contains(v) ==> new_table.mapping_4k().spec_index(v) == old_table.mapping_4k().spec_index(v)
        }
}

/// Loop state of `flush_pagetable_tlbs` after cpu `cpu_id`, from the state before it and the effect of
/// `flush_pagetable_tlb_on_cpu` on that cpu under the typed lock maps of `held`.
pub(super) proof fn flush_pagetable_tlbs_eol_flush_step(pre: KernelK, mid: KernelK, post: KernelK, held: &LocalContext, mid_lctx: &LocalContext, pre_steps: &KernelSteps,
    mid_steps: &KernelSteps, post_steps: &KernelSteps, snaps: Seq<KernelK>, rec: Seq<KernelK>, cpu_id: usize, pagetable: RwLockPageTableRoot, pcid: Pcid, local_cpu: CpuId,
    thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, table_write_held: bool)
    requires
        flush_pagetable_tlbs_eol_loop_framing(pre, mid, held, pre_steps, mid_steps, snaps, cpu_id as nat, pagetable, pcid, local_cpu, thrd_ptr, ctn_ptr, table_write_held),
        typed_lock_maps_unchanged(held, mid_lctx),
        mid_lctx.thread_id() == held.thread_id(),
        mid_steps.view().len() <= post_steps.view().len() <= mid_steps.view().len() + 1,
        forall|j: int| #![trigger post_steps.view()[j]] 0 <= j < mid_steps.view().len() ==> post_steps.view()[j] == mid_steps.view()[j],
        post_steps.view().len() == mid_steps.view().len() + rec.len(),
        forall|k: int| #![trigger rec[k]] 0 <= k < rec.len() ==> {
            let s = rec[k];
            let step = post_steps.view()[mid_steps.view().len() + k];
            &&& step.old_u == kernel_k_to_kernel_u(s)
            &&& unmap_4k_tlb_flush_step(step.old_u, step.new_u, local_cpu)
            &&& s.inv()
            &&& held_threads_unchanged(pre.thrd_mp, s.thrd_mp, held)
            &&& held_processes_unchanged(pre.prc_mp, s.prc_mp, held)
            &&& held_containers_unchanged(pre.ctn_mp, s.ctn_mp, held)
            &&& s.ctn_mp.dom().contains(ctn_ptr)
            &&& s.cpu_arr.spec_index(local_cpu).view().locking_thread() == pre.cpu_arr.spec_index(local_cpu).view().locking_thread()
            &&& s.cpu_arr.spec_index(local_cpu).view().view().view().current_thread == Some(thrd_ptr)
            &&& s.cpu_op.view().view()[local_cpu as int] == pre.cpu_op.view().view()[local_cpu as int]
            &&& pre.cpu_trap_frame.view().view().dom().contains(local_cpu) ==> s.cpu_trap_frame.view().view()[local_cpu] == pre.cpu_trap_frame.view().view()[local_cpu]
            &&& s.pt_mp.dom().contains(pagetable)
            &&& s.pt_mp.spec_index(pagetable).view().higher == (PageTableHigher { table_stale_cpus: s.pt_mp.spec_index(pagetable).view().higher.table_stale_cpus,
                ..pre.pt_mp.spec_index(pagetable).view().higher })
            &&& s.pt_mp.spec_index(pagetable).locked_by_thread(held.thread_id())
            &&& !(s.cpu_set_mp.spec_index(s.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).lock_state_u() is WriteLocked)
            &&& typed_lock_map_contains_mode(held.pagetable_lock_map(), pagetable, TypedLockMode::Write) ==> {
                &&& s.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread()
                &&& whole_pagetable(s.pt_mp, s.pt_lower.view(), pagetable).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k()
                &&& whole_pagetable(s.pt_mp, s.pt_lower.view(), pagetable).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m()
                &&& whole_pagetable(s.pt_mp, s.pt_lower.view(), pagetable).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_1g()
                &&& whole_pagetable(s.pt_mp, s.pt_lower.view(), pagetable).lower.pagetable_window_locks == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.pagetable_window_locks
                &&& s.pt_mp.spec_index(pagetable).view().higher.pci.mapping_counts() == pre.pt_mp.spec_index(pagetable).view().higher.pci.mapping_counts()
            }
        },
        forall|held_cpu_id: CpuId| #![trigger mid_lctx.cpu_lock_map().dom().contains(held_cpu_id)]
            mid_lctx.cpu_lock_map().dom().contains(held_cpu_id) ==> post.cpu_arr.spec_index(held_cpu_id).view().view() == mid.cpu_arr.spec_index(held_cpu_id).view().view(),
        post.cpu_arr.spec_index(local_cpu).view().locking_thread() == mid.cpu_arr.spec_index(local_cpu).view().locking_thread(),
        post.cpu_arr.spec_index(local_cpu).view().being_killed() == mid.cpu_arr.spec_index(local_cpu).view().being_killed(),
        post.cpu_arr.spec_index(local_cpu).view().killer_info() == mid.cpu_arr.spec_index(local_cpu).view().killer_info(),
        held_containers_unchanged(mid.ctn_mp, post.ctn_mp, mid_lctx),
        held_iommu_tables_unchanged(mid.it_mp, post.it_mp, mid_lctx),
        held_pages_unchanged(mid.pg_arr, post.pg_arr, mid_lctx),
        !table_write_held ==> post.pt_mp.spec_index(pagetable).view() == mid.pt_mp.spec_index(pagetable).view(),
        post.pt_mp.spec_index(pagetable).being_killed() == mid.pt_mp.spec_index(pagetable).being_killed(),
        typed_lock_map_contains_mode(mid_lctx.pagetable_lock_map(), pagetable, TypedLockMode::Read) ==> post.pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.spec_index(mid_lctx.thread_id())
            == mid.pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.spec_index(mid_lctx.thread_id()),
        forall|w: WindowVa| #![trigger mid_lctx.pagetable_window_lock_map().dom().contains((pagetable, w))] mid_lctx.pagetable_window_lock_map().dom().contains((pagetable, w)) ==> {
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).window_view(w).lock_state == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).window_view(w).lock_state
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).window_view(w).l1_table == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).window_view(w).l1_table
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).window_view(w).l2_entry == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).window_view(w).l2_entry
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).window_view(w).stale_cpus is None
                || (cpu_id + 1 < NUM_CPUS && whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).window_view(w).stale_cpus == Some(Set::range((cpu_id + 1) as usize, NUM_CPUS)))
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va) == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va)
            &&& whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va)
                ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_2m().spec_index(w.va) == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).mapping_2m().spec_index(w.va)
        },
        forall|w: WindowVa, v: VAddr|
            #![trigger mid_lctx.pagetable_window_lock_map().dom().contains((pagetable, w)), whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
            #![trigger mid_lctx.pagetable_window_lock_map().dom().contains((pagetable, w)), whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
            mid_lctx.pagetable_window_lock_map().dom().contains((pagetable, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
                &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k().dom().contains(v) == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                &&& whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                    ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k().spec_index(v) == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).mapping_4k().spec_index(v)
            },
    ensures
        flush_pagetable_tlbs_eol_loop_framing(pre, post, held, pre_steps, post_steps, snaps + rec, (cpu_id + 1) as nat, pagetable, pcid, local_cpu, thrd_ptr, ctn_ptr, table_write_held),
{
    reveal(flush_pagetable_tlbs_eol_loop_framing);
}

/// Loop state of `flush_pagetable_tlbs` after cpu `cpu_id`, from the state before it and the effect of `drop_stale_cpu`
/// on that cpu under the typed lock maps of `held`; the trace is unchanged.
pub(super) proof fn flush_pagetable_tlbs_eol_drop_step(pre: KernelK, mid: KernelK, post: KernelK, held: &LocalContext, lctx: &LocalContext, pre_steps: &KernelSteps,
    steps: &KernelSteps, snaps: Seq<KernelK>, cpu_id: usize, pagetable: RwLockPageTableRoot, pcid: Pcid, local_cpu: CpuId, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr,
    table_write_held: bool)
    requires
        flush_pagetable_tlbs_eol_loop_framing(pre, mid, held, pre_steps, steps, snaps, cpu_id as nat, pagetable, pcid, local_cpu, thrd_ptr, ctn_ptr, table_write_held),
        typed_lock_maps_unchanged(held, lctx),
        post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..mid }),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).lower == (PageTableLower { window_stale_cpus: whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).lower.window_stale_cpus,
            ..whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).lower }),
        post.pt_mp.spec_index(pagetable).locking_thread() == mid.pt_mp.spec_index(pagetable).locking_thread(),
        post.pt_mp.spec_index(pagetable).being_killed() == mid.pt_mp.spec_index(pagetable).being_killed(),
        !table_write_held ==> post.pt_mp.spec_index(pagetable).view() == mid.pt_mp.spec_index(pagetable).view(),
        forall|w: WindowVa| #![trigger lctx.pagetable_window_lock_map().dom().contains((pagetable, w))] lctx.pagetable_window_lock_map().dom().contains((pagetable, w)) ==> {
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).window_view(w).lock_state == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).window_view(w).lock_state
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).window_view(w).l1_table == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).window_view(w).l1_table
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).window_view(w).l2_entry == whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable).window_view(w).l2_entry
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).window_view(w).stale_cpus is None
                || (cpu_id + 1 < NUM_CPUS && whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).window_view(w).stale_cpus == Some(Set::range((cpu_id + 1) as usize, NUM_CPUS)))
        },
    ensures
        flush_pagetable_tlbs_eol_loop_framing(pre, post, held, pre_steps, steps, snaps, (cpu_id + 1) as nat, pagetable, pcid, local_cpu, thrd_ptr, ctn_ptr, table_write_held),
{
    reveal(flush_pagetable_tlbs_eol_loop_framing);
}

/// The containers `held` holds and the lock of cpu `local_cpu` keep their `pre` state in the loop state `cur` of
/// `flush_pagetable_tlbs`.
pub(super) proof fn flush_pagetable_tlbs_eol_held_objects(pre: KernelK, cur: KernelK, held: &LocalContext, pre_steps: &KernelSteps, cur_steps: &KernelSteps, snaps: Seq<KernelK>,
    flushed: nat, pagetable: RwLockPageTableRoot, pcid: Pcid, local_cpu: CpuId, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, table_write_held: bool)
    requires flush_pagetable_tlbs_eol_loop_framing(pre, cur, held, pre_steps, cur_steps, snaps, flushed, pagetable, pcid, local_cpu, thrd_ptr, ctn_ptr, table_write_held),
    ensures
        held_containers_unchanged(pre.ctn_mp, cur.ctn_mp, held),
        cur.cpu_arr.spec_index(local_cpu).view().locking_thread() == pre.cpu_arr.spec_index(local_cpu).view().locking_thread(),
{ reveal(flush_pagetable_tlbs_eol_loop_framing); }

/// The ensures of `flush_pagetable_tlbs` on the trace, the held objects, cpu `local_cpu`, and table `pagetable` and the windows
/// of it that `pre_lctx` holds, from its loop state once every cpu is visited, the held processes and threads it keeps, and
/// the release of the cpu-set read hold `cpu_set_entry` that `held` adds to `pre_lctx`, which changes only the cpu-set map.
pub(super) proof fn flush_pagetable_tlbs_eol_exit(pre: KernelK, cur: KernelK, post: KernelK, pre_lctx: &LocalContext, held: &LocalContext, pre_steps: &KernelSteps,
    steps: &KernelSteps, snaps: Seq<KernelK>, cpu_id: usize, pagetable: RwLockPageTableRoot, pcid: Pcid, local_cpu: CpuId, thrd_ptr: RwLockThreadPtr, cpu_set_ptr: RwLockCpuSetPtr,
    cpu_set_entry: TypedHeldLock, table_write_held: bool)
    requires
        flush_pagetable_tlbs_eol_loop_framing(pre, cur, held, pre_steps, steps, snaps, cpu_id as nat, pagetable, pcid, local_cpu, thrd_ptr, pre.thrd_mp.spec_index(thrd_ptr).view().owning_container, table_write_held),
        cpu_id == NUM_CPUS,
        typed_lock_maps_inserted(pre_lctx, held, KernelObjId::CpuSet(cpu_set_ptr), cpu_set_entry),
        held.thread_id() == pre_lctx.thread_id(),
        held_processes_unchanged(pre.prc_mp, cur.prc_mp, held),
        held_threads_unchanged(pre.thrd_mp, cur.thrd_mp, held),
        forall|w: WindowVa| #![trigger held.pagetable_window_lock_map().dom().contains((pagetable, w))] held.pagetable_window_lock_map().dom().contains((pagetable, w))
            ==> whole_pagetable(cur.pt_mp, cur.pt_lower.view(), pagetable).window_view(w).stale_cpus is None
                || (cpu_id < NUM_CPUS && whole_pagetable(cur.pt_mp, cur.pt_lower.view(), pagetable).window_view(w).stale_cpus == Some(Set::range(cpu_id, NUM_CPUS))),
        post == (KernelK { cpu_set_mp: post.cpu_set_mp, ..cur }),
    ensures
        pre_steps.view().len() <= steps.view().len() <= pre_steps.view().len() + NUM_CPUS,
        forall|j: int| #![trigger steps.view()[j]] 0 <= j < pre_steps.view().len() ==> steps.view()[j] == pre_steps.view()[j],
        steps.view().len() == pre_steps.view().len() + snaps.len(),
        forall|k: int| #![trigger snaps[k]] 0 <= k < snaps.len() ==> {
            let s = snaps[k];
            let step = steps.view()[pre_steps.view().len() + k];
            let ctn_ptr = pre.thrd_mp.spec_index(thrd_ptr).view().owning_container;
            &&& step.old_u == kernel_k_to_kernel_u(s)
            &&& unmap_4k_tlb_flush_step(step.old_u, step.new_u, local_cpu)
            &&& s.inv()
            &&& held_threads_unchanged(pre.thrd_mp, s.thrd_mp, pre_lctx)
            &&& held_processes_unchanged(pre.prc_mp, s.prc_mp, pre_lctx)
            &&& held_containers_unchanged(pre.ctn_mp, s.ctn_mp, pre_lctx)
            &&& s.ctn_mp.dom().contains(ctn_ptr)
            &&& s.cpu_arr.spec_index(local_cpu).view().locking_thread() == pre.cpu_arr.spec_index(local_cpu).view().locking_thread()
            &&& s.cpu_arr.spec_index(local_cpu).view().view().view().current_thread == Some(thrd_ptr)
            &&& s.cpu_op.view().view()[local_cpu as int] == pre.cpu_op.view().view()[local_cpu as int]
            &&& pre.cpu_trap_frame.view().view().dom().contains(local_cpu) ==> s.cpu_trap_frame.view().view()[local_cpu] == pre.cpu_trap_frame.view().view()[local_cpu]
            &&& s.pt_mp.dom().contains(pagetable)
            &&& s.pt_mp.spec_index(pagetable).view().higher == (PageTableHigher { table_stale_cpus: s.pt_mp.spec_index(pagetable).view().higher.table_stale_cpus,
                ..pre.pt_mp.spec_index(pagetable).view().higher })
            &&& s.pt_mp.spec_index(pagetable).locked_by_thread(pre_lctx.thread_id())
            &&& !(s.cpu_set_mp.spec_index(s.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).lock_state_u() is WriteLocked)
            &&& typed_lock_map_contains_mode(pre_lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write) ==> {
                &&& s.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread()
                &&& whole_pagetable(s.pt_mp, s.pt_lower.view(), pagetable).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k()
                &&& whole_pagetable(s.pt_mp, s.pt_lower.view(), pagetable).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m()
                &&& whole_pagetable(s.pt_mp, s.pt_lower.view(), pagetable).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_1g()
                &&& whole_pagetable(s.pt_mp, s.pt_lower.view(), pagetable).lower.pagetable_window_locks == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.pagetable_window_locks
                &&& s.pt_mp.spec_index(pagetable).view().higher.pci.mapping_counts() == pre.pt_mp.spec_index(pagetable).view().higher.pci.mapping_counts()
            }
        },
        forall|held_cpu_id: CpuId| #![trigger pre_lctx.cpu_lock_map().dom().contains(held_cpu_id)]
            pre_lctx.cpu_lock_map().dom().contains(held_cpu_id) ==> post.cpu_arr.spec_index(held_cpu_id).view().view() == pre.cpu_arr.spec_index(held_cpu_id).view().view(),
        held_containers_unchanged(pre.ctn_mp, post.ctn_mp, pre_lctx),
        held_processes_unchanged(pre.prc_mp, post.prc_mp, pre_lctx),
        held_threads_unchanged(pre.thrd_mp, post.thrd_mp, pre_lctx),
        held_iommu_tables_unchanged(pre.it_mp, post.it_mp, pre_lctx),
        held_pages_unchanged(pre.pg_arr, post.pg_arr, pre_lctx),
        post.cpu_arr.spec_index(local_cpu).view().locking_thread() == pre.cpu_arr.spec_index(local_cpu).view().locking_thread(),
        post.cpu_arr.spec_index(local_cpu).view().being_killed() == pre.cpu_arr.spec_index(local_cpu).view().being_killed(),
        post.cpu_arr.spec_index(local_cpu).view().killer_info() == pre.cpu_arr.spec_index(local_cpu).view().killer_info(),
        !table_write_held ==> post.pt_mp.spec_index(pagetable).view() == pre.pt_mp.spec_index(pagetable).view(),
        post.pt_mp.spec_index(pagetable).being_killed() == pre.pt_mp.spec_index(pagetable).being_killed(),
        typed_lock_map_contains_mode(pre_lctx.pagetable_lock_map(), pagetable, TypedLockMode::Read) ==> post.pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.spec_index(pre_lctx.thread_id())
            == pre.pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.spec_index(pre_lctx.thread_id()),
        forall|w: WindowVa| #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((pagetable, w))] pre_lctx.pagetable_window_lock_map().dom().contains((pagetable, w)) ==> {
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).window_view(w).lock_state == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).window_view(w).lock_state
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).window_view(w).l1_table == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).window_view(w).l1_table
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).window_view(w).l2_entry == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).window_view(w).l2_entry
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).window_view(w).stale_cpus is None
            &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va)
            &&& whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va)
                ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_2m().spec_index(w.va) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().spec_index(w.va)
        },
        forall|w: WindowVa, v: VAddr|
            #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((pagetable, w)), whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
            #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((pagetable, w)), whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
            pre_lctx.pagetable_window_lock_map().dom().contains((pagetable, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
                &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k().dom().contains(v) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                &&& whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                    ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k().spec_index(v) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().spec_index(v)
            },
{
    reveal(flush_pagetable_tlbs_eol_loop_framing);
}

/// EOL closure of `flush_pagetable_tlbs` at loop exit: only the stale-CPU set of `pagetable` changed in its big-lock payload, so
/// every non-empty and resolved root and L3 entry of the table is as before.
pub(super) proof fn flush_pagetable_tlbs_eol_exit_nonempty_entries(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot)
    requires
        post.pt_mp.spec_index(pagetable).view().higher == (PageTableHigher { table_stale_cpus: post.pt_mp.spec_index(pagetable).view().higher.table_stale_cpus, ..pre.pt_mp.spec_index(pagetable).view().higher }),
    ensures
        ({
            let old_h = pre.pt_mp.spec_index(pagetable).view().higher;
            let new_h = post.pt_mp.spec_index(pagetable).view().higher;
            &&& forall|l4i: L4Index| #![trigger new_h.spec_nonempty_l4(l4i)] new_h.spec_nonempty_l4(l4i) == old_h.spec_nonempty_l4(l4i) && new_h.spec_resolve_mapping_l4(l4i) == old_h.spec_resolve_mapping_l4(l4i)
            &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_h.spec_nonempty_l3(l4i, l3i)]
                new_h.spec_nonempty_l3(l4i, l3i) == old_h.spec_nonempty_l3(l4i, l3i) && new_h.spec_resolve_mapping_l3(l4i, l3i) == old_h.spec_resolve_mapping_l3(l4i, l3i)
        }),
{}

/// EOL closure of `flush_pagetable_tlbs` at loop exit under a table write hold: only the table and window stale-CPU sets of
/// `pagetable` changed, so every non-empty 4K and 2M leaf of the table is as before.
pub(super) proof fn flush_pagetable_tlbs_eol_exit_nonempty_leaves(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot)
    requires
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).higher
            == (PageTableHigher { table_stale_cpus: whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).higher.table_stale_cpus, ..whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).higher }),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).lower
            == (PageTableLower { window_stale_cpus: whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).lower.window_stale_cpus, ..whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower }),
    ensures
        ({
            let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
            let new_c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_nonempty_4k_l1(l4i, l3i, l2i, l1i)] new_c.spec_nonempty_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_nonempty_4k_l1(l4i, l3i, l2i, l1i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_nonempty_2m_l2(l4i, l3i, l2i)] new_c.spec_nonempty_2m_l2(l4i, l3i, l2i) == old_c.spec_nonempty_2m_l2(l4i, l3i, l2i)
        }),
{}
}
