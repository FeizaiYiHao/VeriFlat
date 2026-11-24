//! The store-buffer invariant `store_buffers_covered`, kept by every step and so true at every index of every behaviour, its
//! corollaries, and the classification of the bytes a step changes.
use vstd::prelude::*;
use crate::*;
use crate::pcid::*;

verus! {
/// Cpu `c` is neither inside a kernel step nor off, and `s` goes through a writable translation of its current process's
/// PCID, which is not the default PCID, and lies inside its page.
pub open spec fn store_covered(u: KernelU, c: CpuId, s: PendingStore) -> bool {
    let cpu = u.cpu_array[c as int];
    &&& !(cpu.op is InStep) && !(cpu.op is Off)
    &&& cpu.current_process is Some && u.process_map[cpu.current_process->Some_0].pcid == s.pcid
    &&& s.pcid != KERNEL_DEFAULT_PCID
    &&& tlb_writable_at(u.cpu_tlb[(c, s.pcid)], s.size, s.base_va, s.frame)
    &&& 0 < s.bytes.len() && s.offset + s.bytes.len() <= page_size_bytes(s.size)
}

/// There is one buffer per cpu, and every buffered store is covered on its cpu.
pub open spec fn store_buffers_covered(st: MemState) -> bool {
    &&& st.bufs.len() == NUM_CPUS
    &&& forall|c: CpuId, j: int| #![trigger st.bufs[c as int][j]] index_valid(NUM_CPUS, c) && 0 <= j < st.bufs[c as int].len() ==> store_covered(st.u, c, st.bufs[c as int][j])
}

/// A store covered on cpu `c` stays covered across a step that keeps the mode, the current process, and the TLBs of `c`
/// and the PCID of every process alive before and after it, between well-formed states.
pub proof fn cpu_view_kept_implies_store_covered(u: KernelU, u2: KernelU, c: CpuId, s: PendingStore)
    requires
        kernel_u_ownership_wf(u), kernel_u_ownership_wf(u2), index_valid(NUM_CPUS, c), store_covered(u, c, s), cpu_view_kept(u, u2, c), process_pcids_kept(u, u2),
    ensures store_covered(u2, c, s),
{
    reveal(kernel_u_cpu_ownership_wf);
    let p = u.cpu_array[c as int].current_process->Some_0;
    assert(u.process_map.dom().contains(p) && u2.process_map.dom().contains(p));
    assert(u2.cpu_tlb[(c, s.pcid)] == u.cpu_tlb[(c, s.pcid)]);
}

/// A CPU TLB fill that keeps the translations its TLB caches keeps a writable translation it caches under a non-default
/// PCID.
pub proof fn fill_keeps_cached_translations_implies_writable_kept(u: KernelU, l: StepLabel, s: PendingStore, c: CpuId)
    requires
        l is CpuTlbFilled, cpu_tlb_fill_keeps_cached_translations(u, l), s.pcid != KERNEL_DEFAULT_PCID, tlb_writable_at(u.cpu_tlb[(c, s.pcid)], s.size, s.base_va, s.frame),
    ensures
        tlb_writable_at(u.cpu_tlb.insert((l->CpuTlbFilled_cpu_id, l->CpuTlbFilled_pcid), single_tlb_union(u.cpu_tlb[(l->CpuTlbFilled_cpu_id, l->CpuTlbFilled_pcid)], l->CpuTlbFilled_added))[(c, s.pcid)],
            s.size, s.base_va, s.frame),
{
    let key = (l->CpuTlbFilled_cpu_id, l->CpuTlbFilled_pcid);
    let added = l->CpuTlbFilled_added;
    if (c, s.pcid) == key {
        let old = u.cpu_tlb[key];
        let va = s.base_va;
        match s.size {
            PageSize::SZ4k => { if added.tlb_4k.dom().contains(va) { assert(added.tlb_4k[va] == old.tlb_4k[va]); } },
            PageSize::SZ2m => { if added.tlb_2m.dom().contains(va) { assert(added.tlb_2m[va] == old.tlb_2m[va]); } },
            PageSize::SZ1g => { if added.tlb_1g.dom().contains(va) { assert(added.tlb_1g[va] == old.tlb_1g[va]); } },
        }
    }
}

/// A CPU TLB fill from a state whose current TLBs agree with the present leaves of their tables keeps the translations its
/// TLB caches: under a non-default PCID it adds only present leaves of the table of the filling cpu's current process, and
/// only under that process's PCID.
pub proof fn current_tlb_matches_present_implies_fill_keeps_cached_translations(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_current_tlb_matches_present_wf(u), labeled_step(l, u, u2, d),
    ensures cpu_tlb_fill_keeps_cached_translations(u, l),
{
    if l is CpuTlbFilled && l->CpuTlbFilled_pcid != KERNEL_DEFAULT_PCID {
        let (c, pcid, added) = (l->CpuTlbFilled_cpu_id, l->CpuTlbFilled_pcid, l->CpuTlbFilled_added);
        let p = u.cpu_array[c as int].current_process;
        let tlb = u.cpu_tlb[(c, pcid)];
        reveal(kernel_u_cpu_tlb_filled_step);
        reveal(kernel_u_current_tlb_matches_present_wf);
        if p is Some && u.process_map.dom().contains(p->Some_0) && u.process_map[p->Some_0].pcid == pcid && u.process_map[p->Some_0].pagetable is Some {
            assert forall|va: VAddr| #![trigger added.tlb_4k[va]] tlb.tlb_4k.dom().contains(va) && added.tlb_4k.dom().contains(va) implies added.tlb_4k[va] == tlb.tlb_4k[va] by {
                assert(added.tlb_4k().dom().contains(va)); assert(spec_tlb_entry_equal_to_map_entry(tlb.tlb_4k[va], u.process_map[p->Some_0].pagetable->Some_0.mapping_4k[va]));
            };
            assert forall|va: VAddr| #![trigger added.tlb_2m[va]] tlb.tlb_2m.dom().contains(va) && added.tlb_2m.dom().contains(va) implies added.tlb_2m[va] == tlb.tlb_2m[va] by {
                assert(added.tlb_2m().dom().contains(va)); assert(spec_tlb_entry_equal_to_map_entry(tlb.tlb_2m[va], u.process_map[p->Some_0].pagetable->Some_0.mapping_2m[va]));
            };
            assert forall|va: VAddr| #![trigger added.tlb_1g[va]] tlb.tlb_1g.dom().contains(va) && added.tlb_1g.dom().contains(va) implies added.tlb_1g[va] == tlb.tlb_1g[va] by {
                assert(added.tlb_1g().dom().contains(va)); assert(spec_tlb_entry_equal_to_map_entry(tlb.tlb_1g[va], u.process_map[p->Some_0].pagetable->Some_0.mapping_1g[va]));
            };
        }
    }
}

/// A kernel step keeps the invariant.
pub proof fn kernel_step_implies_store_buffers_covered(old: MemState, new: MemState, l: StepLabel, d: CpuId)
    requires
        store_buffers_covered(old), kernel_u_ownership_wf(old.u), kernel_u_ownership_wf(new.u), cpu_tlb_fill_keeps_cached_translations(old.u, l), kernel_mem_step(old, new, l, d),
    ensures store_buffers_covered(new),
{
    if hardware_label(l) {
        hardware_step_implies_cpus_kept(l, old.u, new.u, d);
        reveal(kernel_u_cpu_ownership_wf);
        assert(new.bufs =~= old.bufs);
        assert forall|c: CpuId, j: int| #![trigger new.bufs[c as int][j]] index_valid(NUM_CPUS, c) && 0 <= j < new.bufs[c as int].len() implies store_covered(new.u, c, new.bufs[c as int][j]) by {
            let s = old.bufs[c as int][j];
            assert(store_covered(old.u, c, s));
            assert(new.u.cpu_array[c as int].current_process == old.u.cpu_array[c as int].current_process);
            if l is CpuTlbFilled { fill_keeps_cached_translations_implies_writable_kept(old.u, l, s, c); }
        };
    } else {
        kernel_step_implies_process_pcids_kept(l, old.u, new.u, d);
        assert forall|c: CpuId, j: int| #![trigger new.bufs[c as int][j]] index_valid(NUM_CPUS, c) && 0 <= j < new.bufs[c as int].len() implies store_covered(new.u, c, new.bufs[c as int][j]) by {
            assert(!drained(l, old.u, new.u, d, c));
            assert(new.bufs[c as int] == old.bufs[c as int]);
            cpu_view_kept_implies_store_covered(old.u, new.u, c, old.bufs[c as int][j]);
        };
    }
}

/// Every step keeps the invariant.
pub proof fn mem_step_implies_store_buffers_covered(old: MemState, new: MemState, label: MemLabel, c: CpuId)
    requires
        store_buffers_covered(old), kernel_u_ownership_wf(old.u), kernel_u_ownership_wf(new.u), kernel_u_current_tlb_matches_present_wf(old.u), mem_step(old, new, label, c),
    ensures store_buffers_covered(new),
{
    match label {
        MemLabel::Kernel { label: l } => {
            current_tlb_matches_present_implies_fill_keeps_cached_translations(old.u, new.u, l, c);
            kernel_step_implies_store_buffers_covered(old, new, l, c);
        },
        MemLabel::StoreIssued { s } => {
            assert forall|x: CpuId, j: int| #![trigger new.bufs[x as int][j]] index_valid(NUM_CPUS, x) && 0 <= j < new.bufs[x as int].len() implies store_covered(new.u, x, new.bufs[x as int][j]) by {
                if x == c && j == old.bufs[c as int].len() { assert(new.bufs[x as int][j] == s); } else { assert(new.bufs[x as int][j] == old.bufs[x as int][j]); }
            };
        },
        MemLabel::StoreCommitted => {
            let buf = old.bufs[c as int];
            assert forall|x: CpuId, j: int| #![trigger new.bufs[x as int][j]] index_valid(NUM_CPUS, x) && 0 <= j < new.bufs[x as int].len() implies store_covered(new.u, x, new.bufs[x as int][j]) by {
                if x == c { assert(new.bufs[x as int][j] == old.bufs[x as int][j + 1]); } else { assert(new.bufs[x as int][j] == old.bufs[x as int][j]); }
            };
        },
        _ => {},
    }
}

/// The invariant holds at every index of a behaviour.
pub proof fn mem_behavior_implies_store_buffers_covered(b: Execution<MemSnap>, i: nat)
    requires mem_behavior(b),
    ensures store_buffers_covered(b(i).st),
    decreases i,
{
    if i == 0 {
        assert forall|c: CpuId, j: int| #![trigger b(0).st.bufs[c as int][j]] index_valid(NUM_CPUS, c) && 0 <= j < b(0).st.bufs[c as int].len() implies store_covered(b(0).st.u, c, b(0).st.bufs[c as int][j]) by {
            assert(b(0).st.bufs[c as int].len() == 0);
        };
    } else {
        let k = (i - 1) as nat;
        mem_behavior_implies_store_buffers_covered(b, k);
        assert(behavior_step(b, k));
        mem_step_implies_store_buffers_covered(b(k).st, b(i).st, b(k).label, b(k).cpu);
    }
}

/// A cpu inside a kernel step or off has an empty buffer.
pub proof fn store_buffers_covered_implies_kernel_or_off_buffer_empty(st: MemState, c: CpuId)
    requires store_buffers_covered(st), index_valid(NUM_CPUS, c), st.u.cpu_array[c as int].op is InStep || st.u.cpu_array[c as int].op is Off,
    ensures st.bufs[c as int].len() == 0,
{ if st.bufs[c as int].len() > 0 { assert(store_covered(st.u, c, st.bufs[c as int][0])); } }

/// A commit writes the oldest store of its cpu, which goes through a writable translation of that cpu's current process's
/// PCID and lies inside its page.
pub proof fn commit_step_implies_store_through_writable_translation(old: MemState, new: MemState, c: CpuId)
    requires store_buffers_covered(old), mem_step(old, new, MemLabel::StoreCommitted, c),
    ensures store_covered(old.u, c, old.bufs[c as int][0]), new.mem == mem_after_store(old.mem, old.bufs[c as int][0]),
{ assert(store_covered(old.u, c, old.bufs[c as int][0])); }

/// Every store a kernel step drains goes through a writable translation of its cpu's current process's PCID and lies inside
/// its page.
pub proof fn kernel_step_implies_drained_store_through_writable_translation(old: MemState, new: MemState, l: StepLabel, d: CpuId, c: CpuId, j: int)
    requires store_buffers_covered(old), kernel_mem_step(old, new, l, d), index_valid(NUM_CPUS, c), drained(l, old.u, new.u, d, c), 0 <= j < old.bufs[c as int].len(),
    ensures store_covered(old.u, c, old.bufs[c as int][j]),
{}

/// A device write goes through a writable 4K IOTLB translation of its domain and stays inside that page.
pub proof fn dma_step_implies_write_through_writable_iotlb_entry(old: MemState, new: MemState, did: VtdDomainId, iova: VAddr, frame: PAddr, offset: nat, bytes: Seq<u8>, c: CpuId)
    requires mem_step(old, new, MemLabel::DmaWritten { did, iova, frame, offset, bytes }, c),
    ensures tlb_writable_at(old.u.iommu_tlb[did], PageSize::SZ4k, iova, frame), offset + bytes.len() <= 0x1000, new.mem == mem_overwrite(old.mem, frame + offset, bytes),
{}

/// Some store of a cpu of the drain set of the step `l` of `d` covers the byte `a`, and it is covered on its cpu.
pub open spec fn drain_wrote_byte(old: MemState, new: MemState, l: StepLabel, d: CpuId, a: PAddr) -> bool {
    exists|x: CpuId, j: int| #![trigger old.bufs[x as int][j], drained(l, old.u, new.u, d, x)]
        index_valid(NUM_CPUS, x) && drained(l, old.u, new.u, d, x) && 0 <= j < old.bufs[x as int].len() && store_covers(old.bufs[x as int][j], a) && store_covered(old.u, x, old.bufs[x as int][j])
}

/// The byte `a` lies in the frame an mmap leaf step installs.
pub open spec fn leaf_zeroed_byte(old: MemState, new: MemState, l: StepLabel, d: CpuId, a: PAddr) -> bool {
    let leaf = mmap_leaf_frame(l, old.u, new.u, d);
    leaf is Some && leaf->Some_0.0 <= a < leaf->Some_0.0 + leaf->Some_0.1
}

/// Why the byte `a` may change across the step: (a) a commit or drain of a store covered on its cpu that writes it, (b) a
/// device write through a writable IOTLB translation of its domain that writes it, or (c) the zeroing of an mmap leaf step
/// whose frame contains it.
pub open spec fn byte_change_explained(old: MemState, new: MemState, label: MemLabel, c: CpuId, a: PAddr) -> bool {
    match label {
        MemLabel::StoreCommitted => store_covers(old.bufs[c as int][0], a) && store_covered(old.u, c, old.bufs[c as int][0]),
        MemLabel::Kernel { label: l } => drain_wrote_byte(old, new, l, c, a) || leaf_zeroed_byte(old, new, l, c, a),
        MemLabel::DmaWritten { did, iova, frame, offset, bytes } => frame + offset <= a < frame + offset + bytes.len() && tlb_writable_at(old.u.iommu_tlb[did], PageSize::SZ4k, iova, frame),
        _ => false,
    }
}

/// A byte that writing the drain set in a drain order changes is covered by a store of a drained cpu.
pub proof fn drain_order_changed_byte_implies_drained_store(mem: IMap<PAddr, u8>, bufs: Seq<Seq<PendingStore>>, order: Seq<(CpuId, int)>, l: StepLabel, u: KernelU, u2: KernelU,
    d: CpuId, a: PAddr) -> (w: (CpuId, int))
    requires drain_order(order, bufs, l, u, u2, d), mem_after_stores(mem, stores_in_order(bufs, order))[a] != mem[a],
    ensures index_valid(NUM_CPUS, w.0), drained(l, u, u2, d, w.0), 0 <= w.1 < bufs[w.0 as int].len(), store_covers(bufs[w.0 as int][w.1], a),
{
    let k = mem_after_stores_changed_implies_covering_store(mem, stores_in_order(bufs, order), a);
    assert(0 <= k < order.len());
    order[k]
}

/// Byte-change classification: across any step from a state satisfying the invariant, a byte changes only by a commit or
/// drain of a covered store, by a device write, or by the zeroing of an mmap leaf step.
pub proof fn mem_step_implies_byte_change_explained(old: MemState, new: MemState, label: MemLabel, c: CpuId, a: PAddr)
    requires store_buffers_covered(old), mem_step(old, new, label, c), new.mem[a] != old.mem[a],
    ensures byte_change_explained(old, new, label, c, a),
{
    match label {
        MemLabel::Kernel { label: l } => {
            let order = choose|order: Seq<(CpuId, int)>| #![trigger drain_order(order, old.bufs, l, old.u, new.u, c)]
                drain_order(order, old.bufs, l, old.u, new.u, c) && new.mem == leaf_zeroed_memory(mem_after_stores(old.mem, stores_in_order(old.bufs, order)), l, old.u, new.u, c);
            let mem1 = mem_after_stores(old.mem, stores_in_order(old.bufs, order));
            let leaf = mmap_leaf_frame(l, old.u, new.u, c);
            if !leaf_zeroed_byte(old, new, l, c, a) {
                if leaf is Some { mem_overwrite_index_implies_byte(mem1, leaf->Some_0.0 as int, Seq::new(leaf->Some_0.1, |i: int| 0u8), a); }
                assert(mem1[a] != old.mem[a]);
                let w = drain_order_changed_byte_implies_drained_store(old.mem, old.bufs, order, l, old.u, new.u, c, a);
                assert(store_covered(old.u, w.0, old.bufs[w.0 as int][w.1]));
            }
        },
        MemLabel::StoreCommitted => {
            let s = old.bufs[c as int][0];
            mem_overwrite_index_implies_byte(old.mem, store_base(s), s.bytes, a);
            assert(store_covered(old.u, c, s));
        },
        MemLabel::DmaWritten { did, iova, frame, offset, bytes } => { mem_overwrite_index_implies_byte(old.mem, frame + offset, bytes, a); },
        _ => {},
    }
}

/// Right after an mmap leaf step every byte of the installed frame is zero.
pub proof fn mmap_leaf_step_implies_frame_zero(old: MemState, new: MemState, l: StepLabel, d: CpuId, a: PAddr)
    requires mem_step(old, new, MemLabel::Kernel { label: l }, d), leaf_zeroed_byte(old, new, l, d, a),
    ensures new.mem[a] == 0,
{
    let leaf = mmap_leaf_frame(l, old.u, new.u, d)->Some_0;
    let order = choose|order: Seq<(CpuId, int)>| #![trigger drain_order(order, old.bufs, l, old.u, new.u, d)]
        drain_order(order, old.bufs, l, old.u, new.u, d) && new.mem == leaf_zeroed_memory(mem_after_stores(old.mem, stores_in_order(old.bufs, order)), l, old.u, new.u, d);
    let mem1 = mem_after_stores(old.mem, stores_in_order(old.bufs, order));
    mem_overwrite_index_implies_byte(mem1, leaf.0 as int, Seq::new(leaf.1, |i: int| 0u8), a);
}
} // verus!
