use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::unmap_4k_tlb_eof::*;

verus! {
pub fn mark_pcid_needflush_and_load(krnl: &mut KernelK, cpu_id: CpuId, pcid: Pcid, Tracked(lctx): Tracked<&mut LocalContext>, needflush_perm: Tracked<&LockPerm>) -> (ret: (PageTableRoot, Pcid))
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        typed_lock_map_contains_mode(old(lctx).pcid_needflush_lock_map(), (cpu_id, pcid), TypedLockMode::Write),
        needflush_perm.view().state() is WriteLock,
        needflush_perm.view().thread_id() == old(lctx).thread_id(),
        needflush_perm.view().lock_id() == old(krnl).pcid_needflush.spec_index(cpu_id, pcid).locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { pcid_needflush: final(krnl).pcid_needflush, ..*old(krnl) }),
        ret == final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        page_ptr_valid(ret.0),
        pcid_valid(ret.1),
        cpu_id != final(lctx).cpu_id() && final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid ==> ret == (final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, pcid),
        final(krnl).pcid_needflush.spec_index(cpu_id, pcid).view().needflush,
        final(krnl).pcid_needflush.lock_id_by_index(cpu_id, pcid) == old(krnl).pcid_needflush.lock_id_by_index(cpu_id, pcid),
        final(krnl).pcid_needflush.spec_index(cpu_id, pcid).locking_thread() == old(krnl).pcid_needflush.spec_index(cpu_id, pcid).locking_thread(),
        final(krnl).pcid_needflush.spec_index(cpu_id, pcid).view_ghost() == old(krnl).pcid_needflush.spec_index(cpu_id, pcid).view_ghost(),
        forall|c: CpuId, p: Pcid| #![trigger final(krnl).pcid_needflush.spec_index(c, p)] #![trigger old(krnl).pcid_needflush.spec_index(c, p)] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid)
            ==> final(krnl).pcid_needflush.spec_index(c, p) == old(krnl).pcid_needflush.spec_index(c, p),
{
    krnl.mark_pcid_needflush(cpu_id, pcid, Tracked(&*lctx), needflush_perm);
    assert(krnl.pcid_needflush.lock_id_by_index(cpu_id, pcid) == old(krnl).pcid_needflush.lock_id_by_index(cpu_id, pcid)) by { pcid_needflush_wf_at(old(krnl).pcid_needflush, cpu_id, pcid); pcid_needflush_wf_at(krnl.pcid_needflush, cpu_id, pcid); };
    krnl.load_hw_cr3_pcid(cpu_id, Tracked(&mut *lctx))
}

pub fn flush_remote_pcid_and_clear(krnl: &mut KernelK, cpu_id: CpuId, pcid: Pcid, Tracked(lctx): Tracked<&LocalContext>, needflush_perm: Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), lctx),
        lctx.kernel_view_locking_state() is Release,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id != lctx.cpu_id(),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        typed_lock_map_contains_mode(lctx.pcid_needflush_lock_map(), (cpu_id, pcid), TypedLockMode::Write),
        needflush_perm.view().state() is WriteLock,
        needflush_perm.view().thread_id() == lctx.thread_id(),
        needflush_perm.view().lock_id() == old(krnl).pcid_needflush.spec_index(cpu_id, pcid).locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        typed_lock_maps_aligned(final(krnl), lctx),
        *final(krnl) == (KernelK { cpu_tlb: final(krnl).cpu_tlb, pcid_needflush: final(krnl).pcid_needflush, ..*old(krnl) }),
        final(krnl).cpu_tlb.view() == old(krnl).cpu_tlb.view().insert((cpu_id, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }),
        final(krnl).cpu_tlb.spec_index((cpu_id, pcid)).is_empty(),
        forall|c: CpuId, p: Pcid| #![trigger final(krnl).cpu_tlb.spec_index((c, p))] #![trigger old(krnl).cpu_tlb.spec_index((c, p))] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid) ==> final(krnl).cpu_tlb.spec_index((c, p)) == old(krnl).cpu_tlb.spec_index((c, p)),
        !final(krnl).pcid_needflush.spec_index(cpu_id, pcid).view().needflush,
        final(krnl).pcid_needflush.lock_id_by_index(cpu_id, pcid) == old(krnl).pcid_needflush.lock_id_by_index(cpu_id, pcid),
        final(krnl).pcid_needflush.spec_index(cpu_id, pcid).locking_thread() == old(krnl).pcid_needflush.spec_index(cpu_id, pcid).locking_thread(),
        final(krnl).pcid_needflush.spec_index(cpu_id, pcid).view_ghost() == old(krnl).pcid_needflush.spec_index(cpu_id, pcid).view_ghost(),
        forall|c: CpuId, p: Pcid| #![trigger final(krnl).pcid_needflush.spec_index(c, p)] #![trigger old(krnl).pcid_needflush.spec_index(c, p)] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid)
            ==> final(krnl).pcid_needflush.spec_index(c, p) == old(krnl).pcid_needflush.spec_index(c, p),
{
    krnl.cpu_tlb.flush_remote_pcid(cpu_id, pcid, Tracked(lctx));
    pcid_needflush_array_clear(&mut krnl.pcid_needflush, cpu_id, pcid, Tracked(lctx), needflush_perm);
    proof {
        assert(flush_remote_pcid_and_clear_eof_transition_framing(*old(krnl), *krnl, cpu_id, pcid)) by { reveal(flush_remote_pcid_and_clear_eof_transition_framing); };
        flush_remote_pcid_and_clear_eof(*old(krnl), *krnl, cpu_id, pcid);
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
    }
}

pub fn flush_local_pcid_and_clear(krnl: &mut KernelK, cpu_id: CpuId, pcid: Pcid, cr3: PageTableRoot, Tracked(lctx): Tracked<&LocalContext>, needflush_perm: Tracked<&LockPerm>, cpu_perm: Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), lctx),
        lctx.kernel_view_locking_state() is Release,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == lctx.cpu_id(),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        page_ptr_valid(cr3),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_perm.view().state() is WriteLock,
        cpu_perm.view().thread_id() == lctx.thread_id(),
        cpu_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(lctx.pcid_needflush_lock_map(), (cpu_id, pcid), TypedLockMode::Write),
        needflush_perm.view().state() is WriteLock,
        needflush_perm.view().thread_id() == lctx.thread_id(),
        needflush_perm.view().lock_id() == old(krnl).pcid_needflush.spec_index(cpu_id, pcid).locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        typed_lock_maps_aligned(final(krnl), lctx),
        *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, cpu_tlb: final(krnl).cpu_tlb, pcid_needflush: final(krnl).pcid_needflush, ..*old(krnl) }),
        final(krnl).cpu_arr.entries_unchanged_except(&old(krnl).cpu_arr, cpu_id),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().killer_info() == old(krnl).cpu_arr.spec_index(cpu_id).view().killer_info(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view_rodata() == old(krnl).cpu_arr.spec_index(cpu_id).view().view_rodata(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view_ghost() == old(krnl).cpu_arr.spec_index(cpu_id).view().view_ghost(),
        final(krnl).cpu_tlb.view() == old(krnl).cpu_tlb.view().insert((cpu_id, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }),
        final(krnl).cpu_tlb.spec_index((cpu_id, pcid)).is_empty(),
        forall|c: CpuId, p: Pcid| #![trigger final(krnl).cpu_tlb.spec_index((c, p))] #![trigger old(krnl).cpu_tlb.spec_index((c, p))] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid) ==> final(krnl).cpu_tlb.spec_index((c, p)) == old(krnl).cpu_tlb.spec_index((c, p)),
        !final(krnl).pcid_needflush.spec_index(cpu_id, pcid).view().needflush,
        final(krnl).pcid_needflush.lock_id_by_index(cpu_id, pcid) == old(krnl).pcid_needflush.lock_id_by_index(cpu_id, pcid),
        final(krnl).pcid_needflush.spec_index(cpu_id, pcid).locking_thread() == old(krnl).pcid_needflush.spec_index(cpu_id, pcid).locking_thread(),
        final(krnl).pcid_needflush.spec_index(cpu_id, pcid).view_ghost() == old(krnl).pcid_needflush.spec_index(cpu_id, pcid).view_ghost(),
        forall|c: CpuId, p: Pcid| #![trigger final(krnl).pcid_needflush.spec_index(c, p)] #![trigger old(krnl).pcid_needflush.spec_index(c, p)] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid)
            ==> final(krnl).pcid_needflush.spec_index(c, p) == old(krnl).pcid_needflush.spec_index(c, p),
{
    assert(krnl.cpu_arr.inv() && krnl.cpu_arr.spec_index(cpu_id).view().is_init()) by { cpu_array_wf_map(krnl.cpu_arr, krnl.dflt_pt.view()); cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), cpu_id); };
    cpu_array_flush_current_tlb(&mut krnl.cpu_arr, &mut krnl.cpu_tlb, cpu_id, cr3, pcid, Tracked(lctx), cpu_perm);
    pcid_needflush_array_clear(&mut krnl.pcid_needflush, cpu_id, pcid, Tracked(lctx), needflush_perm);
    proof {
        assert(flush_local_pcid_and_clear_eof_transition_framing(*old(krnl), *krnl, cpu_id, pcid)) by { reveal(flush_local_pcid_and_clear_eof_transition_framing); };
        flush_local_pcid_and_clear_eof(*old(krnl), *krnl, cpu_id, pcid);
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
    }
}
}
