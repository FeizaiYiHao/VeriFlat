use vstd::prelude::*;
use crate::*;

verus! {
pub fn pcid_needflush_array_clear(
    needflush: &mut PcidNeedFlushArray, cpu_id: CpuId, pcid: Pcid,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(needflush_lock_perm): Tracked<&LockPerm>,
)
    requires
        pcid_needflush_wf(*old(needflush)),
        index_valid(NUM_CPUS, cpu_id),
        pcid_valid(pcid),
        old(needflush).typed_lock_map_aligned(lctx.pcid_needflush_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.pcid_needflush_lock_map(), (cpu_id, pcid), TypedLockMode::Write),
        needflush_lock_perm.state() is WriteLock,
        needflush_lock_perm.thread_id() == lctx.thread_id(),
        needflush_lock_perm.lock_id() == old(needflush).spec_index(cpu_id, pcid).locking_thread()->Write_lock_id,
    ensures
        pcid_needflush_wf(*final(needflush)),
        final(needflush).typed_lock_map_aligned(lctx.pcid_needflush_lock_map(), lctx.thread_id()),
        final(needflush).lock_id_by_index(cpu_id, pcid) == old(needflush).lock_id_by_index(cpu_id, pcid),
        final(needflush).spec_index(cpu_id, pcid).view() == (PcidNeedFlush { needflush: false, ..old(needflush).spec_index(cpu_id, pcid).view() }),
        final(needflush).spec_index(cpu_id, pcid).is_init(),
        final(needflush).spec_index(cpu_id, pcid).locking_thread() == old(needflush).spec_index(cpu_id, pcid).locking_thread(),
        final(needflush).spec_index(cpu_id, pcid).view_ghost() == old(needflush).spec_index(cpu_id, pcid).view_ghost(),
        final(needflush).spec_index(cpu_id, pcid).view_rodata() == old(needflush).spec_index(cpu_id, pcid).view_rodata(),
        final(needflush).spec_index(cpu_id, pcid).being_killed() == old(needflush).spec_index(cpu_id, pcid).being_killed(),
        forall|c: CpuId, p: Pcid| #![trigger final(needflush).spec_index(c, p)] #![trigger old(needflush).spec_index(c, p)] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid) ==> final(needflush).spec_index(c, p) == old(needflush).spec_index(c, p),
        forall|c: CpuId, p: Pcid| #![trigger typed_lock_map_contains_mode(lctx.pcid_needflush_lock_map(), (c, p), TypedLockMode::Write)] typed_lock_map_contains_mode(lctx.pcid_needflush_lock_map(), (c, p), TypedLockMode::Write) ==> final(needflush).spec_index(c, p).view_ghost() == old(needflush).spec_index(c, p).view_ghost(),
{
    assert(needflush.spec_index(cpu_id, pcid).is_init()) by { reveal(pcid_needflush_wf); };
    let entry = needflush.borrow_mut_typed(cpu_id, pcid, Ghost(lctx.pcid_needflush_lock_map()), Tracked(lctx), Tracked(needflush_lock_perm));
    entry.set(false);
    proof {
        assert(pcid_needflush_wf(*needflush) && needflush.lock_id_by_index(cpu_id, pcid) == old(needflush).lock_id_by_index(cpu_id, pcid)) by { reveal(pcid_needflush_wf); };
        assert(needflush.typed_lock_map_aligned(lctx.pcid_needflush_lock_map(), lctx.thread_id()) && forall|c: CpuId, p: Pcid| #![trigger typed_lock_map_contains_mode(lctx.pcid_needflush_lock_map(), (c, p), TypedLockMode::Write)] typed_lock_map_contains_mode(lctx.pcid_needflush_lock_map(), (c, p), TypedLockMode::Write) ==> needflush.spec_index(c, p).view_ghost() == old(needflush).spec_index(c, p).view_ghost()) by { reveal(LockedArray2D::typed_lock_map_aligned); };
    }
}

pub fn cpu_array_flush_current_tlb(
    cpu_array: &mut CpuLockedArray, cpu_tlb: &mut CpuTLB, cpu_id: CpuId, cr3: PageTableRoot, pcid: Pcid,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(cpu_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(cpu_array).inv(),
        index_valid(NUM_CPUS, cpu_id),
        old(cpu_array).spec_index(cpu_id).view().is_init(),
        old(cpu_array).typed_lock_map_aligned(lctx.cpu_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == lctx.thread_id(),
        cpu_lock_perm.lock_id() == old(cpu_array).spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(cpu_tlb).inv(),
        cpu_id == lctx.cpu_id(),
        page_ptr_valid(cr3),
        pcid_valid(pcid),
        old(cpu_array).spec_index(cpu_id).view().view().view().current_cr3 == cr3,
        old(cpu_array).spec_index(cpu_id).view().view().view().current_pcid == pcid,
        lctx.kernel_view_locking_state() is Release,
    ensures
        final(cpu_array).inv(),
        final(cpu_array).entries_unchanged_except(old(cpu_array), cpu_id),
        final(cpu_array).typed_lock_map_aligned(lctx.cpu_lock_map(), lctx.thread_id()),
        final(cpu_array).lock_id_by_index(cpu_id) == old(cpu_array).lock_id_by_index(cpu_id),
        final(cpu_array).spec_index(cpu_id).view().is_init(),
        final(cpu_array).spec_index(cpu_id).view().wlocked_by(lctx),
        final(cpu_array).spec_index(cpu_id).view().view() == old(cpu_array).spec_index(cpu_id).view().view(),
        final(cpu_array).spec_index(cpu_id).view().locking_thread() == old(cpu_array).spec_index(cpu_id).view().locking_thread(),
        final(cpu_array).spec_index(cpu_id).view().being_killed() == old(cpu_array).spec_index(cpu_id).view().being_killed(),
        final(cpu_array).spec_index(cpu_id).view().view_rodata() == old(cpu_array).spec_index(cpu_id).view().view_rodata(),
        final(cpu_array).spec_index(cpu_id).view().view_ghost() == old(cpu_array).spec_index(cpu_id).view().view_ghost(),
        final(cpu_tlb).inv(),
        final(cpu_tlb).view() == old(cpu_tlb).view().insert((cpu_id, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }),
        final(cpu_tlb).spec_index((cpu_id, pcid)).is_empty(),
        forall|c: CpuId, p: Pcid| #![trigger final(cpu_tlb).spec_index((c, p))] #![trigger old(cpu_tlb).spec_index((c, p))] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid) ==> final(cpu_tlb).spec_index((c, p)) == old(cpu_tlb).spec_index((c, p)),
{
    let cpu = cpu_array.borrow_mut_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(lctx), Tracked(cpu_lock_perm));
    cpu.flush_current_tlb(cpu_id, cr3, pcid, cpu_tlb, Tracked(lctx));
    proof { assert(cpu_array.typed_lock_map_aligned(lctx.cpu_lock_map(), lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); }; }
}
}
