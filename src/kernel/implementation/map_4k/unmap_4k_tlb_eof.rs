use vstd::prelude::*;
use crate::*;

verus! {
/// Empties the TLB of `(cpu_id, pcid)` and clears its needflush bit; every other kernel field is unchanged.
#[verifier::opaque]
pub(super) open spec fn flush_remote_pcid_and_clear_eof_transition_framing(pre: KernelK, post: KernelK, cpu_id: CpuId, pcid: Pcid) -> bool {
    let old_entry = pre.pcid_needflush.spec_index(cpu_id, pcid);
    let new_entry = post.pcid_needflush.spec_index(cpu_id, pcid);
    &&& post == (KernelK { cpu_tlb: post.cpu_tlb, pcid_needflush: post.pcid_needflush, ..pre })
    &&& post.cpu_tlb.view() == pre.cpu_tlb.view().insert((cpu_id, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })
    &&& post.cpu_tlb.spec_index((cpu_id, pcid)).is_empty()
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
    assert(post.subsystems_inv()) by { reveal(cpu_published_wf); reveal(KernelK::default_pagetable_wf); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match);
        reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
    };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
}

/// Flushes the calling cpu's current TLB for `pcid` and clears its needflush bit; the cpu entry keeps its value and
/// every other kernel field is unchanged.
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
    &&& post.cpu_tlb.view() == pre.cpu_tlb.view().insert((cpu_id, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })
    &&& post.cpu_tlb.spec_index((cpu_id, pcid)).is_empty()
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
    assert(post.subsystems_inv()) by { reveal(cpu_array_wf); reveal(cpu_published_wf); reveal(cpu_offline_flags_wf); reveal(KernelK::default_pagetable_wf); };
    assert(post.process_management_inv()) by { reveal(container_cpu_wf); reveal(process_cpu_wf); reveal(thread_cpu_wf); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match);
        reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
    };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
}
}
