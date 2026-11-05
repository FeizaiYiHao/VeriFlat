use vstd::prelude::*;
use crate::*;

verus! {
/// Flushes the TLB of `(cpu_id, pcid)`, which keeps at most what the cpu may cache in `pre`, and clears its needflush bit;
/// every other kernel field is unchanged.
#[verifier::opaque]
pub(super) open spec fn flush_remote_pcid_and_clear_eof_transition_framing(pre: KernelK, post: KernelK, cpu_id: CpuId, pcid: Pcid) -> bool {
    let old_entry = pre.pcid_needflush.spec_index(cpu_id, pcid);
    let new_entry = post.pcid_needflush.spec_index(cpu_id, pcid);
    &&& post == (KernelK { cpu_tlb: post.cpu_tlb, pcid_needflush: post.pcid_needflush, ..pre })
    &&& post.cpu_tlb.view() == pre.cpu_tlb.view().insert((cpu_id, pcid), post.cpu_tlb.spec_index((cpu_id, pcid)))
    &&& post.cpu_tlb.structure_caches.view() == pre.cpu_tlb.structure_caches.view().insert((cpu_id, pcid), post.cpu_tlb.structure_cache((cpu_id, pcid)))
    &&& cpu_tlb_within_may_cache(pre, cpu_id, pcid, post.cpu_tlb.spec_index((cpu_id, pcid)), post.cpu_tlb.structure_cache((cpu_id, pcid)))
    &&& forall|c: CpuId, p: Pcid| #![trigger post.cpu_tlb.spec_index((c, p))] #![trigger pre.cpu_tlb.spec_index((c, p))] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid)
        ==> post.cpu_tlb.spec_index((c, p)) == pre.cpu_tlb.spec_index((c, p))
    &&& new_entry.view() == (PcidNeedFlush { needflush: false, ..old_entry.view() })
    &&& new_entry.is_init()
    &&& new_entry.locking_thread() == old_entry.locking_thread()
    &&& new_entry.view_ghost() == old_entry.view_ghost()
    &&& new_entry.view_rodata() == old_entry.view_rodata()
    &&& new_entry.being_killed() == old_entry.being_killed()
    &&& forall|c: CpuId, p: Pcid| #![trigger post.pcid_needflush.spec_index(c, p)] #![trigger pre.pcid_needflush.spec_index(c, p)] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid)
        ==> post.pcid_needflush.spec_index(c, p) == pre.pcid_needflush.spec_index(c, p)
}

pub(super) proof fn flush_remote_pcid_and_clear_eof(pre: KernelK, post: KernelK, cpu_id: CpuId, pcid: Pcid)
    requires
        pre.inv(),
        flush_remote_pcid_and_clear_eof_transition_framing(pre, post, cpu_id, pcid),
        index_valid(NUM_CPUS, cpu_id),
        pcid_valid(pcid),
        post.cpu_tlb.inv(),
        pcid_needflush_wf(post.pcid_needflush),
    ensures post.inv(),
{
    reveal(flush_remote_pcid_and_clear_eof_transition_framing);
    assert(post.subsystems_inv()) by { reveal(cpu_hw_cr3_pcid_wf); reveal(KernelK::default_pagetable_wf); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_process_in_cpu_container); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_pagetable_pcid_match);
        reveal(cpu_dirty_map_covers_nonempty_tlb); cpu_array_wf_at(pre.cpu_arr, pre.dflt_pt.view(), cpu_id); process_cpu_wf_at(pre.prc_mp, pre.cpu_arr, cpu_id);
    };
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by {
        reveal(cpu_tlb_wf); reveal(cpu_dirty_map_pagetable_pcid_match); cpu_array_wf_at(pre.cpu_arr, pre.dflt_pt.view(), cpu_id); process_cpu_wf_at(pre.prc_mp, pre.cpu_arr, cpu_id);
    };
    flush_remote_pcid_and_clear_eof_structure_cache_wf(pre, post, cpu_id, pcid);
}

/// EOF closure of `flush_remote_pcid_and_clear` for the paging-structure invariant: the refilled cache of `(cpu_id, pcid)`
/// holds only present entries of the table the cpu runs under `pcid`, or nothing; every other cache is unchanged.
proof fn flush_remote_pcid_and_clear_eof_structure_cache_wf(pre: KernelK, post: KernelK, cpu_id: CpuId, pcid: Pcid)
    requires
        pre.inv(),
        flush_remote_pcid_and_clear_eof_transition_framing(pre, post, cpu_id, pcid),
        index_valid(NUM_CPUS, cpu_id),
        pcid_valid(pcid),
    ensures structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
{
    reveal(flush_remote_pcid_and_clear_eof_transition_framing);
    reveal(structure_cache_wf); reveal(cpu_dirty_map_pagetable_pcid_match); cpu_array_wf_at(pre.cpu_arr, pre.dflt_pt.view(), cpu_id); process_cpu_wf_at(pre.prc_mp, pre.cpu_arr, cpu_id);
}

/// Flushes the calling cpu's current TLB for `pcid`, which keeps at most what the cpu may cache in `pre`, and clears its
/// needflush bit; the cpu entry keeps its value and every other kernel field is unchanged.
#[verifier::opaque]
pub(super) open spec fn flush_local_pcid_and_clear_eof_transition_framing(pre: KernelK, post: KernelK, cpu_id: CpuId, pcid: Pcid) -> bool {
    let old_cpu = pre.cpu_arr.spec_index(cpu_id).view();
    let new_cpu = post.cpu_arr.spec_index(cpu_id).view();
    let old_entry = pre.pcid_needflush.spec_index(cpu_id, pcid);
    let new_entry = post.pcid_needflush.spec_index(cpu_id, pcid);
    &&& post == (KernelK { cpu_arr: post.cpu_arr, cpu_tlb: post.cpu_tlb, pcid_needflush: post.pcid_needflush, ..pre })
    &&& post.cpu_arr.entries_unchanged_except(&pre.cpu_arr, cpu_id)
    &&& post.cpu_arr.lock_id_by_index(cpu_id) == pre.cpu_arr.lock_id_by_index(cpu_id)
    &&& new_cpu.is_init()
    &&& new_cpu.view() == old_cpu.view()
    &&& new_cpu.locking_thread() == old_cpu.locking_thread()
    &&& new_cpu.being_killed() == old_cpu.being_killed()
    &&& new_cpu.killer_info() == old_cpu.killer_info()
    &&& new_cpu.view_rodata() == old_cpu.view_rodata()
    &&& new_cpu.view_ghost() == old_cpu.view_ghost()
    &&& post.cpu_tlb.view() == pre.cpu_tlb.view().insert((cpu_id, pcid), post.cpu_tlb.spec_index((cpu_id, pcid)))
    &&& post.cpu_tlb.structure_caches.view() == pre.cpu_tlb.structure_caches.view().insert((cpu_id, pcid), post.cpu_tlb.structure_cache((cpu_id, pcid)))
    &&& cpu_tlb_within_may_cache(pre, cpu_id, pcid, post.cpu_tlb.spec_index((cpu_id, pcid)), post.cpu_tlb.structure_cache((cpu_id, pcid)))
    &&& forall|c: CpuId, p: Pcid| #![trigger post.cpu_tlb.spec_index((c, p))] #![trigger pre.cpu_tlb.spec_index((c, p))] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid)
        ==> post.cpu_tlb.spec_index((c, p)) == pre.cpu_tlb.spec_index((c, p))
    &&& new_entry.view() == (PcidNeedFlush { needflush: false, ..old_entry.view() })
    &&& new_entry.is_init()
    &&& new_entry.locking_thread() == old_entry.locking_thread()
    &&& new_entry.view_ghost() == old_entry.view_ghost()
    &&& new_entry.view_rodata() == old_entry.view_rodata()
    &&& new_entry.being_killed() == old_entry.being_killed()
    &&& forall|c: CpuId, p: Pcid| #![trigger post.pcid_needflush.spec_index(c, p)] #![trigger pre.pcid_needflush.spec_index(c, p)] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid)
        ==> post.pcid_needflush.spec_index(c, p) == pre.pcid_needflush.spec_index(c, p)
}

proof fn flush_local_pcid_and_clear_eof_subsystems_inv(pre: KernelK, post: KernelK, cpu_id: CpuId, pcid: Pcid)
    requires
        pre.inv(),
        flush_local_pcid_and_clear_eof_transition_framing(pre, post, cpu_id, pcid),
        index_valid(NUM_CPUS, cpu_id),
        pcid_valid(pcid),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
        post.cpu_arr.inv(),
        post.cpu_tlb.inv(),
        pcid_needflush_wf(post.pcid_needflush),
    ensures post.subsystems_inv(),
{
    reveal(flush_local_pcid_and_clear_eof_transition_framing);
    reveal(cpu_array_wf); reveal(cpu_hw_cr3_pcid_wf); reveal(cpu_offline_flags_wf); reveal(cpu_op_wf); reveal(KernelK::default_pagetable_wf);
}

proof fn flush_local_pcid_and_clear_eof_process_management_inv(pre: KernelK, post: KernelK, cpu_id: CpuId, pcid: Pcid)
    requires
        pre.inv(),
        flush_local_pcid_and_clear_eof_transition_framing(pre, post, cpu_id, pcid),
        index_valid(NUM_CPUS, cpu_id),
        pcid_valid(pcid),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
        post.cpu_arr.inv(),
        post.cpu_tlb.inv(),
        pcid_needflush_wf(post.pcid_needflush),
    ensures post.process_management_inv(),
{
    reveal(flush_local_pcid_and_clear_eof_transition_framing);
    reveal(container_cpu_wf); reveal(process_cpu_wf); reveal(thread_cpu_wf);
}

proof fn flush_local_pcid_and_clear_eof_cpu_dirty_map_wf(pre: KernelK, post: KernelK, cpu_id: CpuId, pcid: Pcid)
    requires
        pre.inv(),
        flush_local_pcid_and_clear_eof_transition_framing(pre, post, cpu_id, pcid),
        index_valid(NUM_CPUS, cpu_id),
        pcid_valid(pcid),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
        post.cpu_arr.inv(),
        post.cpu_tlb.inv(),
        pcid_needflush_wf(post.pcid_needflush),
    ensures cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush),
{
    reveal(flush_local_pcid_and_clear_eof_transition_framing);
    reveal(cpu_dirty_map_process_in_cpu_container); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_pagetable_pcid_match);
    reveal(cpu_dirty_map_covers_nonempty_tlb); cpu_array_wf_at(pre.cpu_arr, pre.dflt_pt.view(), cpu_id); process_cpu_wf_at(pre.prc_mp, pre.cpu_arr, cpu_id);
}

proof fn flush_local_pcid_and_clear_eof_tlb_wf(pre: KernelK, post: KernelK, cpu_id: CpuId, pcid: Pcid)
    requires
        pre.inv(),
        flush_local_pcid_and_clear_eof_transition_framing(pre, post, cpu_id, pcid),
        index_valid(NUM_CPUS, cpu_id),
        pcid_valid(pcid),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
        post.cpu_arr.inv(),
        post.cpu_tlb.inv(),
        pcid_needflush_wf(post.pcid_needflush),
    ensures cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
{
    reveal(flush_local_pcid_and_clear_eof_transition_framing);
    reveal(cpu_tlb_wf); reveal(cpu_dirty_map_pagetable_pcid_match); cpu_array_wf_at(pre.cpu_arr, pre.dflt_pt.view(), cpu_id); process_cpu_wf_at(pre.prc_mp, pre.cpu_arr, cpu_id);
}

/// EOF closure of `flush_local_pcid_and_clear` for the paging-structure invariant: the refilled cache of `(cpu_id, pcid)`
/// holds only present entries of the table the calling cpu runs, or nothing; every other cache is unchanged.
proof fn flush_local_pcid_and_clear_eof_structure_cache_wf(pre: KernelK, post: KernelK, cpu_id: CpuId, pcid: Pcid)
    requires
        pre.inv(),
        flush_local_pcid_and_clear_eof_transition_framing(pre, post, cpu_id, pcid),
        index_valid(NUM_CPUS, cpu_id),
        pcid_valid(pcid),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
    ensures structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
{
    reveal(flush_local_pcid_and_clear_eof_transition_framing);
    reveal(structure_cache_wf); reveal(cpu_dirty_map_pagetable_pcid_match); cpu_array_wf_at(pre.cpu_arr, pre.dflt_pt.view(), cpu_id); process_cpu_wf_at(pre.prc_mp, pre.cpu_arr, cpu_id);
}

pub(super) proof fn flush_local_pcid_and_clear_eof(pre: KernelK, post: KernelK, cpu_id: CpuId, pcid: Pcid)
    requires
        pre.inv(),
        flush_local_pcid_and_clear_eof_transition_framing(pre, post, cpu_id, pcid),
        index_valid(NUM_CPUS, cpu_id),
        pcid_valid(pcid),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
        post.cpu_arr.inv(),
        post.cpu_tlb.inv(),
        pcid_needflush_wf(post.pcid_needflush),
    ensures post.inv(),
{
    reveal(flush_local_pcid_and_clear_eof_transition_framing);
    flush_local_pcid_and_clear_eof_subsystems_inv(pre, post, cpu_id, pcid);
    flush_local_pcid_and_clear_eof_process_management_inv(pre, post, cpu_id, pcid);
    flush_local_pcid_and_clear_eof_cpu_dirty_map_wf(pre, post, cpu_id, pcid);
    flush_local_pcid_and_clear_eof_tlb_wf(pre, post, cpu_id, pcid);
    flush_local_pcid_and_clear_eof_structure_cache_wf(pre, post, cpu_id, pcid);
}

/// Flushes the `count` pages from `va`, 4K or 2M apart by `stride_2m`, under `pcid` on the calling cpu, which runs `pcid`,
/// keeping in its TLB the untouched translations of `pre` and present leaves of its table, and clears the needflush bit of
/// the pair; every other kernel field is unchanged.
#[verifier::opaque]
pub(super) open spec fn flush_local_va_range_and_clear_eof_transition_framing(pre: KernelK, post: KernelK, cpu_id: CpuId, pcid: Pcid, va: VAddr, count: usize, stride_2m: bool) -> bool {
    let old_entry = pre.pcid_needflush.spec_index(cpu_id, pcid);
    let new_entry = post.pcid_needflush.spec_index(cpu_id, pcid);
    &&& post == (KernelK { cpu_tlb: post.cpu_tlb, pcid_needflush: post.pcid_needflush, ..pre })
    &&& pre.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid
    &&& post.cpu_tlb.view() == pre.cpu_tlb.view().insert((cpu_id, pcid), post.cpu_tlb.spec_index((cpu_id, pcid)))
    &&& post.cpu_tlb.structure_caches.view() == pre.cpu_tlb.structure_caches.view().insert((cpu_id, pcid), post.cpu_tlb.structure_cache((cpu_id, pcid)))
    &&& cpu_tlb_va_range_flushed(pre, cpu_id, pcid, va, count, stride_2m, pre.cpu_tlb.spec_index((cpu_id, pcid)), post.cpu_tlb.spec_index((cpu_id, pcid)), post.cpu_tlb.structure_cache((cpu_id, pcid)))
    &&& forall|c: CpuId, p: Pcid| #![trigger post.cpu_tlb.spec_index((c, p))] #![trigger pre.cpu_tlb.spec_index((c, p))] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid)
        ==> post.cpu_tlb.spec_index((c, p)) == pre.cpu_tlb.spec_index((c, p))
    &&& new_entry.view() == (PcidNeedFlush { needflush: false, ..old_entry.view() })
    &&& new_entry.is_init()
    &&& new_entry.locking_thread() == old_entry.locking_thread()
    &&& new_entry.view_ghost() == old_entry.view_ghost()
    &&& new_entry.view_rodata() == old_entry.view_rodata()
    &&& new_entry.being_killed() == old_entry.being_killed()
    &&& forall|c: CpuId, p: Pcid| #![trigger post.pcid_needflush.spec_index(c, p)] #![trigger pre.pcid_needflush.spec_index(c, p)] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid)
        ==> post.pcid_needflush.spec_index(c, p) == pre.pcid_needflush.spec_index(c, p)
}

pub(super) proof fn flush_local_va_range_and_clear_eof(pre: KernelK, post: KernelK, cpu_id: CpuId, pcid: Pcid, va: VAddr, count: usize, stride_2m: bool)
    requires
        pre.inv(),
        flush_local_va_range_and_clear_eof_transition_framing(pre, post, cpu_id, pcid, va, count, stride_2m),
        index_valid(NUM_CPUS, cpu_id),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        post.cpu_tlb.inv(),
        pcid_needflush_wf(post.pcid_needflush),
    ensures post.inv(),
{
    reveal(flush_local_va_range_and_clear_eof_transition_framing);
    assert(post.subsystems_inv()) by { reveal(cpu_hw_cr3_pcid_wf); reveal(KernelK::default_pagetable_wf); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_process_in_cpu_container); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_pagetable_pcid_match);
        reveal(cpu_dirty_map_covers_nonempty_tlb); cpu_array_wf_at(pre.cpu_arr, pre.dflt_pt.view(), cpu_id); process_cpu_wf_at(pre.prc_mp, pre.cpu_arr, cpu_id);
    };
    flush_va_range_eof_tlb_wf(pre, post, cpu_id, pcid, va, count, stride_2m);
    assert(structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by {
        reveal(structure_cache_wf); reveal(cpu_dirty_map_pagetable_pcid_match); cpu_array_wf_at(pre.cpu_arr, pre.dflt_pt.view(), cpu_id); process_cpu_wf_at(pre.prc_mp, pre.cpu_arr, cpu_id);
    };
}

/// Flushes the `count` pages from `va`, 4K or 2M apart by `stride_2m`, under `pcid` on the remote cpu `cpu_id`, keeping in
/// its TLB the untouched translations of `pre` and, while it runs `pcid`, present leaves of its table; the needflush entry
/// of the pair keeps its bit, lock, and holder cpu of `pre`; every other kernel field is unchanged.
#[verifier::opaque]
pub(super) open spec fn flush_remote_va_range_and_restore_needflush_eof_transition_framing(pre: KernelK, post: KernelK, cpu_id: CpuId, pcid: Pcid, va: VAddr, count: usize, stride_2m: bool) -> bool {
    let old_entry = pre.pcid_needflush.spec_index(cpu_id, pcid);
    let new_entry = post.pcid_needflush.spec_index(cpu_id, pcid);
    &&& post == (KernelK { cpu_tlb: post.cpu_tlb, pcid_needflush: post.pcid_needflush, ..pre })
    &&& post.cpu_tlb.view() == pre.cpu_tlb.view().insert((cpu_id, pcid), post.cpu_tlb.spec_index((cpu_id, pcid)))
    &&& post.cpu_tlb.structure_caches.view() == pre.cpu_tlb.structure_caches.view().insert((cpu_id, pcid), post.cpu_tlb.structure_cache((cpu_id, pcid)))
    &&& cpu_tlb_va_range_flushed(pre, cpu_id, pcid, va, count, stride_2m, pre.cpu_tlb.spec_index((cpu_id, pcid)), post.cpu_tlb.spec_index((cpu_id, pcid)), post.cpu_tlb.structure_cache((cpu_id, pcid)))
    &&& forall|c: CpuId, p: Pcid| #![trigger post.cpu_tlb.spec_index((c, p))] #![trigger pre.cpu_tlb.spec_index((c, p))] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid)
        ==> post.cpu_tlb.spec_index((c, p)) == pre.cpu_tlb.spec_index((c, p))
    &&& new_entry.view().needflush == old_entry.view().needflush
    &&& new_entry.locking_thread() == old_entry.locking_thread()
    &&& new_entry.view_ghost() == old_entry.view_ghost()
    &&& forall|c: CpuId, p: Pcid| #![trigger post.pcid_needflush.spec_index(c, p)] #![trigger pre.pcid_needflush.spec_index(c, p)] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid)
        ==> post.pcid_needflush.spec_index(c, p) == pre.pcid_needflush.spec_index(c, p)
}

pub(super) proof fn flush_remote_va_range_and_restore_needflush_eof(pre: KernelK, post: KernelK, cpu_id: CpuId, pcid: Pcid, va: VAddr, count: usize, stride_2m: bool)
    requires
        pre.inv(),
        flush_remote_va_range_and_restore_needflush_eof_transition_framing(pre, post, cpu_id, pcid, va, count, stride_2m),
        index_valid(NUM_CPUS, cpu_id),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        post.cpu_tlb.inv(),
        pcid_needflush_wf(post.pcid_needflush),
    ensures post.inv(),
{
    reveal(flush_remote_va_range_and_restore_needflush_eof_transition_framing);
    assert(post.subsystems_inv()) by { reveal(cpu_hw_cr3_pcid_wf); reveal(KernelK::default_pagetable_wf); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_process_in_cpu_container); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_pagetable_pcid_match);
        reveal(cpu_dirty_map_covers_nonempty_tlb); cpu_array_wf_at(pre.cpu_arr, pre.dflt_pt.view(), cpu_id); process_cpu_wf_at(pre.prc_mp, pre.cpu_arr, cpu_id);
        let cpu = pre.cpu_arr.spec_index(cpu_id).view().view().view();
        let tlb = post.cpu_tlb.spec_index((cpu_id, pcid));
        if pre.cpu_tlb.spec_index((cpu_id, pcid)).is_empty() && !(cpu.current_pcid == pcid && cpu.current_pagetable is Some) {
            assert(tlb.tlb_4k().dom() =~= Set::<VAddr>::empty()); assert(tlb.tlb_2m().dom() =~= Set::<VAddr>::empty()); assert(tlb.tlb_1g().dom() =~= Set::<VAddr>::empty());
        }
    };
    flush_va_range_eof_tlb_wf(pre, post, cpu_id, pcid, va, count, stride_2m);
    assert(structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by {
        reveal(structure_cache_wf); reveal(cpu_dirty_map_pagetable_pcid_match); cpu_array_wf_at(pre.cpu_arr, pre.dflt_pt.view(), cpu_id); process_cpu_wf_at(pre.prc_mp, pre.cpu_arr, cpu_id);
    };
}

/// EOF closure of `flush_local_va_range_and_clear` and `flush_remote_va_range_and_restore_needflush` for the TLB invariant:
/// the flushed pair keeps translations its non-exempt TLB of `pre` held and refills present leaves of the table it runs, or
/// stays exempt until its activation flush; every other TLB and the page tables are unchanged.
proof fn flush_va_range_eof_tlb_wf(pre: KernelK, post: KernelK, cpu_id: CpuId, pcid: Pcid, va: VAddr, count: usize, stride_2m: bool)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        post == (KernelK { cpu_tlb: post.cpu_tlb, pcid_needflush: post.pcid_needflush, ..pre }),
        post.cpu_tlb.view() == pre.cpu_tlb.view().insert((cpu_id, pcid), post.cpu_tlb.spec_index((cpu_id, pcid))),
        cpu_tlb_va_range_flushed(pre, cpu_id, pcid, va, count, stride_2m, pre.cpu_tlb.spec_index((cpu_id, pcid)), post.cpu_tlb.spec_index((cpu_id, pcid)), post.cpu_tlb.structure_cache((cpu_id, pcid))),
        forall|c: CpuId, p: Pcid| #![trigger post.cpu_tlb.spec_index((c, p))] #![trigger pre.cpu_tlb.spec_index((c, p))] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid)
            ==> post.cpu_tlb.spec_index((c, p)) == pre.cpu_tlb.spec_index((c, p)),
        forall|c: CpuId, p: Pcid| #![trigger post.pcid_needflush.spec_index(c, p)] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid)
            ==> post.pcid_needflush.spec_index(c, p).view().needflush == pre.pcid_needflush.spec_index(c, p).view().needflush,
        post.pcid_needflush.spec_index(cpu_id, pcid).view().needflush ==> pre.pcid_needflush.spec_index(cpu_id, pcid).view().needflush,
        !post.pcid_needflush.spec_index(cpu_id, pcid).view().needflush ==> !pre.pcid_needflush.spec_index(cpu_id, pcid).view().needflush || pre.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
    ensures cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
{
    reveal(cpu_tlb_wf); reveal(cpu_dirty_map_pagetable_pcid_match); cpu_array_wf_at(pre.cpu_arr, pre.dflt_pt.view(), cpu_id); process_cpu_wf_at(pre.prc_mp, pre.cpu_arr, cpu_id);
    let cpu = pre.cpu_arr.spec_index(cpu_id).view().view().view();
    let tlb = post.cpu_tlb.spec_index((cpu_id, pcid));
    if pre.cpu_tlb.spec_index((cpu_id, pcid)).is_empty() && !(cpu.current_pcid == pcid && cpu.current_pagetable is Some) {
        assert(tlb.tlb_4k().dom() =~= Set::<VAddr>::empty()); assert(tlb.tlb_2m().dom() =~= Set::<VAddr>::empty()); assert(tlb.tlb_1g().dom() =~= Set::<VAddr>::empty());
    }
}
}
