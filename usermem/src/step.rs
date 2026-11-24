//! The step relation `mem_step`: the kernel step with its drain set, written in an unspecified order, and the zeroing of
//! fresh mmap leaves, and the user and device steps.
use vstd::prelude::*;
use crate::*;

verus! {
/// The eight hardware labels: trap enter, return, and divert, register and return-value writes, and the CPU TLB, IOTLB,
/// and context-cache fills. None of them drains a buffer.
pub open spec fn hardware_label(l: StepLabel) -> bool {
    ||| l is TrapEnter || l is TrapReturn || l is TrapDivert || l is RegsChanged || l is TrapReturnValuesWritten
    ||| l is CpuTlbFilled || l is IommuTlbFilled || l is IommuContextCacheFilled
}

/// Every TLB key of cpu `c` is present in `u2` exactly when in `u`, and every present one holds in `u2` what it holds in `u`.
pub open spec fn cpu_tlbs_kept(u: KernelU, u2: KernelU, c: CpuId) -> bool {
    forall|p: Pcid| #![trigger u2.cpu_tlb.dom().contains((c, p))] #![trigger u.cpu_tlb.dom().contains((c, p))]
        u2.cpu_tlb.dom().contains((c, p)) == u.cpu_tlb.dom().contains((c, p)) && (u.cpu_tlb.dom().contains((c, p)) ==> u2.cpu_tlb[(c, p)] == u.cpu_tlb[(c, p)])
}

/// Cpu `c` keeps its TLBs, its mode, and its current process across the step.
pub open spec fn cpu_view_kept(u: KernelU, u2: KernelU, c: CpuId) -> bool {
    &&& cpu_tlbs_kept(u, u2, c)
    &&& u2.cpu_array[c as int].op == u.cpu_array[c as int].op
    &&& u2.cpu_array[c as int].current_process == u.cpu_array[c as int].current_process
}

/// Cpu `c` is in the drain set of the step `l` of cpu `d` from `u` to `u2`: `l` is no hardware label, and `c` is `d` or
/// the step changes a TLB, the mode, or the current process of `c`.
pub open spec fn drained(l: StepLabel, u: KernelU, u2: KernelU, d: CpuId, c: CpuId) -> bool { !hardware_label(l) && (c == d || !cpu_view_kept(u, u2, c)) }

/// `bufs` with the buffer of every cpu of the drain set emptied.
pub open spec fn drained_buffers(bufs: Seq<Seq<PendingStore>>, l: StepLabel, u: KernelU, u2: KernelU, d: CpuId) -> Seq<Seq<PendingStore>> {
    Seq::new(bufs.len(), |c: int| if drained(l, u, u2, d, c as CpuId) { Seq::<PendingStore>::empty() } else { bufs[c] })
}

/// The stores at the source positions `order` of `bufs`, in that order: position `(c, j)` is store `j` of cpu `c`'s buffer.
pub open spec fn stores_in_order(bufs: Seq<Seq<PendingStore>>, order: Seq<(CpuId, int)>) -> Seq<PendingStore> { Seq::new(order.len(), |k: int| bufs[order[k].0 as int][order[k].1]) }

/// `order` is an order in which the drain set of the step `l` of cpu `d` from `u` to `u2` writes its buffers `bufs`: it lists
/// every store of every drained cpu exactly once, only those, and each cpu's stores oldest first. It fixes no order between
/// different cpus.
pub open spec fn drain_order(order: Seq<(CpuId, int)>, bufs: Seq<Seq<PendingStore>>, l: StepLabel, u: KernelU, u2: KernelU, d: CpuId) -> bool {
    &&& forall|k: int| #![trigger order[k]] 0 <= k < order.len() ==> index_valid(NUM_CPUS, order[k].0) && drained(l, u, u2, d, order[k].0) && 0 <= order[k].1 < bufs[order[k].0 as int].len()
    &&& forall|k1: int, k2: int| #![trigger order[k1], order[k2]] 0 <= k1 < k2 < order.len() && order[k1].0 == order[k2].0 ==> order[k1].1 < order[k2].1
    &&& forall|c: CpuId, j: int| #![trigger order.contains((c, j))] index_valid(NUM_CPUS, c) && drained(l, u, u2, d, c) && 0 <= j < bufs[c as int].len() ==> order.contains((c, j))
}

/// `mem` after the buffers of the cpus `0..n` of the drain set are written, cpu by cpu in increasing id, each oldest first:
/// one admissible drain order (`increasing_cpu_drain_implies_kernel_mem_step`).
pub open spec fn drained_memory(mem: IMap<PAddr, u8>, bufs: Seq<Seq<PendingStore>>, l: StepLabel, u: KernelU, u2: KernelU, d: CpuId, n: nat) -> IMap<PAddr, u8>
    decreases n,
{
    if n == 0 { mem } else {
        let prev = drained_memory(mem, bufs, l, u, u2, d, (n - 1) as nat);
        if drained(l, u, u2, d, (n - 1) as CpuId) { mem_after_stores(prev, bufs[n - 1]) } else { prev }
    }
}

/// The source positions of the drained buffers of the cpus `0..n`, cpu by cpu in increasing id, each oldest first.
pub open spec fn increasing_cpu_drain_order(bufs: Seq<Seq<PendingStore>>, l: StepLabel, u: KernelU, u2: KernelU, d: CpuId, n: nat) -> Seq<(CpuId, int)>
    decreases n,
{
    if n == 0 { Seq::empty() } else {
        let prev = increasing_cpu_drain_order(bufs, l, u, u2, d, (n - 1) as nat);
        if drained(l, u, u2, d, (n - 1) as CpuId) { prev + Seq::new(bufs[n - 1].len(), |j: int| ((n - 1) as CpuId, j)) } else { prev }
    }
}

/// The frame and byte size of the leaf an mmap leaf step of cpu `d` installs: the entry of `u2` at the VA the progress
/// of `d`'s thread in `u` names, in the table of that thread's process. `None` for every other label.
pub open spec fn mmap_leaf_frame(l: StepLabel, u: KernelU, u2: KernelU, d: CpuId) -> Option<(PAddr, nat)> {
    let thread = u.thread_map[u.cpu_array[d as int].current_thread->Some_0];
    let progress = thread.syscall_progress->Some_0;
    let table = u2.process_map[thread.owning_proc].pagetable->Some_0;
    match l {
        StepLabel::Mmap4kLeaf => Some((table.mapping_4k[progress->Mmap4k_range.view()[progress->Mmap4k_mapped as int]].addr, 0x1000nat)),
        StepLabel::Mmap2mLeaf => Some((table.mapping_2m[progress->Mmap2m_range.view()[progress->Mmap2m_mapped as int]].addr, 0x200000nat)),
        StepLabel::Mmap1gLeaf => Some((table.mapping_1g[progress->Mmap1g_range.view()[progress->Mmap1g_mapped as int]].addr, 0x40000000nat)),
        _ => None,
    }
}

/// `mem` with the `size` bytes from `addr` on set to zero.
pub open spec fn mem_zeroed(mem: IMap<PAddr, u8>, addr: PAddr, size: nat) -> IMap<PAddr, u8> { mem_overwrite(mem, addr as int, Seq::new(size, |i: int| 0u8)) }

/// `mem` with the fresh frame of an mmap leaf step `l` of cpu `d` from `u` to `u2` zeroed; `mem` for every other label.
pub open spec fn leaf_zeroed_memory(mem: IMap<PAddr, u8>, l: StepLabel, u: KernelU, u2: KernelU, d: CpuId) -> IMap<PAddr, u8> {
    match mmap_leaf_frame(l, u, u2, d) {
        Some(leaf) => mem_zeroed(mem, leaf.0, leaf.1),
        None => mem,
    }
}

/// The kernel step `l` of cpu `d`: the step of `labeled_step`, the drain set written in some drain order and emptied, then the
/// fresh frame of an mmap leaf step zeroed.
pub open spec fn kernel_mem_step(old: MemState, new: MemState, l: StepLabel, d: CpuId) -> bool {
    &&& labeled_step(l, old.u, new.u, d)
    &&& new.bufs == drained_buffers(old.bufs, l, old.u, new.u, d)
    &&& exists|order: Seq<(CpuId, int)>| #![trigger drain_order(order, old.bufs, l, old.u, new.u, d)]
        drain_order(order, old.bufs, l, old.u, new.u, d) && new.mem == leaf_zeroed_memory(mem_after_stores(old.mem, stores_in_order(old.bufs, order)), l, old.u, new.u, d)
}

/// Cpu `c` runs in user mode and `s` goes through a writable translation of its current process's PCID, which is not the
/// default PCID and keys a TLB of `c`, and lies inside its page.
pub open spec fn store_issued_pre(u: KernelU, c: CpuId, s: PendingStore) -> bool {
    let cpu = u.cpu_array[c as int];
    &&& index_valid(NUM_CPUS, c)
    &&& cpu.op is User
    &&& cpu.current_process is Some && u.process_map.dom().contains(cpu.current_process->Some_0) && u.process_map[cpu.current_process->Some_0].pcid == s.pcid
    &&& s.pcid != KERNEL_DEFAULT_PCID
    &&& u.cpu_tlb.dom().contains((c, s.pcid)) && tlb_writable_at(u.cpu_tlb[(c, s.pcid)], s.size, s.base_va, s.frame)
    &&& 0 < s.bytes.len() && s.offset + s.bytes.len() <= page_size_bytes(s.size)
}

/// Cpu `c` runs in user mode and reads `len` bytes from byte `offset` of the page of size `size` that a translation of its
/// current process's PCID at `va` names, whose frame is `frame`.
pub open spec fn load_pre(u: KernelU, c: CpuId, size: PageSize, frame: PAddr, va: VAddr, offset: nat, len: nat) -> bool {
    let cpu = u.cpu_array[c as int];
    let tlb = tlb_of_size(u.cpu_tlb[(c, u.process_map[cpu.current_process->Some_0].pcid)], size);
    &&& index_valid(NUM_CPUS, c)
    &&& cpu.op is User
    &&& cpu.current_process is Some && u.process_map.dom().contains(cpu.current_process->Some_0)
    &&& tlb.dom().contains(va) && tlb[va].addr == frame
    &&& 0 < len && offset + len <= page_size_bytes(size)
}

/// The IOTLB holds domain `did`, caches a writable 4K translation of it at `iova` naming `frame`, and the write stays inside
/// that page.
pub open spec fn dma_pre(u: KernelU, did: VtdDomainId, iova: VAddr, frame: PAddr, offset: nat, bytes: Seq<u8>) -> bool {
    &&& u.iommu_tlb.dom().contains(did)
    &&& tlb_writable_at(u.iommu_tlb[did], PageSize::SZ4k, iova, frame)
    &&& offset + bytes.len() <= 0x1000
}

/// One step of cpu `c` from `old` to `new` with label `label`.
pub open spec fn mem_step(old: MemState, new: MemState, label: MemLabel, c: CpuId) -> bool {
    match label {
        MemLabel::Kernel { label: l } => kernel_mem_step(old, new, l, c),
        MemLabel::StoreIssued { s } => store_issued_pre(old.u, c, s) && new == (MemState { bufs: old.bufs.update(c as int, old.bufs[c as int].push(s)), ..old }),
        MemLabel::StoreCommitted => {
            let buf = old.bufs[c as int];
            &&& index_valid(NUM_CPUS, c)
            &&& buf.len() > 0
            &&& new == (MemState { mem: mem_after_store(old.mem, buf[0]), bufs: old.bufs.update(c as int, buf.subrange(1, buf.len() as int)), ..old })
        },
        MemLabel::Load { size, frame, va, offset, value } => {
            &&& load_pre(old.u, c, size, frame, va, offset, value.len())
            &&& new == old
            &&& forall|i: int| #![trigger value[i]] 0 <= i < value.len() ==> value[i] == forwarded_byte(old.bufs[c as int], (frame + offset + i) as PAddr, old.mem[(frame + offset + i) as PAddr])
        },
        MemLabel::DmaWritten { did, iova, frame, offset, bytes } => dma_pre(old.u, did, iova, frame, offset, bytes) && new == (MemState { mem: mem_overwrite(old.mem, frame + offset, bytes), ..old }),
    }
}

/// A CPU TLB fill under a non-default PCID never replaces a translation that TLB already caches with a different one; it
/// follows from `kernel_u_current_tlb_matches_present_wf` (`current_tlb_matches_present_implies_fill_keeps_cached_translations`).
pub open spec fn cpu_tlb_fill_keeps_cached_translations(u: KernelU, l: StepLabel) -> bool {
    l is CpuTlbFilled && l->CpuTlbFilled_pcid != KERNEL_DEFAULT_PCID ==> {
        let tlb = u.cpu_tlb[(l->CpuTlbFilled_cpu_id, l->CpuTlbFilled_pcid)];
        let added = l->CpuTlbFilled_added;
        &&& forall|va: VAddr| #![trigger added.tlb_4k[va]] tlb.tlb_4k.dom().contains(va) && added.tlb_4k.dom().contains(va) ==> added.tlb_4k[va] == tlb.tlb_4k[va]
        &&& forall|va: VAddr| #![trigger added.tlb_2m[va]] tlb.tlb_2m.dom().contains(va) && added.tlb_2m.dom().contains(va) ==> added.tlb_2m[va] == tlb.tlb_2m[va]
        &&& forall|va: VAddr| #![trigger added.tlb_1g[va]] tlb.tlb_1g.dom().contains(va) && added.tlb_1g.dom().contains(va) ==> added.tlb_1g[va] == tlb.tlb_1g[va]
    }
}

/// Every buffer is empty and there is one per cpu.
pub open spec fn buffers_empty(st: MemState) -> bool { st.bufs.len() == NUM_CPUS && forall|c: int| #![trigger st.bufs[c]] 0 <= c < NUM_CPUS ==> st.bufs[c].len() == 0 }

/// The step from index `i` of `b`: a machine step between well-formed user states.
pub open spec fn behavior_step(b: Execution<MemSnap>, i: nat) -> bool {
    &&& mem_step(b(i).st, b(i + 1).st, b(i).label, b(i).cpu)
    &&& kernel_u_ownership_wf(b(i).st.u)
    &&& kernel_u_ownership_wf(b(i + 1).st.u)
    &&& kernel_u_current_tlb_matches_present_wf(b(i).st.u)
}

/// A behaviour of the machine from empty buffers.
pub open spec fn mem_behavior(b: Execution<MemSnap>) -> bool { buffers_empty(b(0).st) && forall|i: nat| #[trigger] behavior_step(b, i) }

/// The source positions of the drained buffers of the cpus `0..n` in increasing cpu id list only stores of drained cpus below
/// `n`, each cpu's stores oldest first, and writing them in that order is `drained_memory`.
pub proof fn increasing_cpu_drain_order_implies_drain_order_prefix(mem: IMap<PAddr, u8>, bufs: Seq<Seq<PendingStore>>, l: StepLabel, u: KernelU, u2: KernelU, d: CpuId, n: nat)
    requires n <= NUM_CPUS,
    ensures
        ({
            let order = increasing_cpu_drain_order(bufs, l, u, u2, d, n);
            &&& mem_after_stores(mem, stores_in_order(bufs, order)) == drained_memory(mem, bufs, l, u, u2, d, n)
            &&& forall|k: int| #![trigger order[k]] 0 <= k < order.len() ==> order[k].0 < n && drained(l, u, u2, d, order[k].0) && 0 <= order[k].1 < bufs[order[k].0 as int].len()
            &&& forall|k1: int, k2: int| #![trigger order[k1], order[k2]] 0 <= k1 < k2 < order.len() && order[k1].0 == order[k2].0 ==> order[k1].1 < order[k2].1
        }),
    decreases n,
{
    if n > 0 {
        let m = (n - 1) as nat;
        let prev = increasing_cpu_drain_order(bufs, l, u, u2, d, m);
        increasing_cpu_drain_order_implies_drain_order_prefix(mem, bufs, l, u, u2, d, m);
        if drained(l, u, u2, d, m as CpuId) {
            let seg = Seq::new(bufs[m as int].len(), |j: int| (m as CpuId, j));
            let order = prev + seg;
            assert(stores_in_order(bufs, order) =~= stores_in_order(bufs, prev) + bufs[m as int]);
            stores_concat_implies_mem_after_stores_sequential(mem, stores_in_order(bufs, prev), bufs[m as int]);
            assert forall|k: int| #![trigger order[k]] 0 <= k < order.len() implies order[k].0 < n && drained(l, u, u2, d, order[k].0) && 0 <= order[k].1 < bufs[order[k].0 as int].len() by {
                if k < prev.len() { assert(order[k] == prev[k]); } else { assert(order[k] == seg[k - prev.len()]); }
            };
            assert forall|k1: int, k2: int| #![trigger order[k1], order[k2]] 0 <= k1 < k2 < order.len() && order[k1].0 == order[k2].0 implies order[k1].1 < order[k2].1 by {
                if k2 < prev.len() { assert(order[k1] == prev[k1] && order[k2] == prev[k2]); } else if k1 < prev.len() { assert(order[k1] == prev[k1] && order[k2] == seg[k2 - prev.len()]); } else {
                    assert(order[k1] == seg[k1 - prev.len()] && order[k2] == seg[k2 - prev.len()]);
                }
            };
        }
    }
}

/// Store `j` of a drained cpu `c` below `n` sits in the increasing-id order of the cpus `0..n` right after the stores of the
/// cpus below `c`.
pub proof fn drained_store_implies_increasing_cpu_drain_order_position(bufs: Seq<Seq<PendingStore>>, l: StepLabel, u: KernelU, u2: KernelU, d: CpuId, n: nat, c: CpuId, j: int)
    requires n <= NUM_CPUS, c < n, drained(l, u, u2, d, c), 0 <= j < bufs[c as int].len(),
    ensures
        ({
            let order = increasing_cpu_drain_order(bufs, l, u, u2, d, n);
            let k = increasing_cpu_drain_order(bufs, l, u, u2, d, c as nat).len() + j;
            0 <= k < order.len() && order[k] == (c, j)
        }),
    decreases n,
{
    let m = (n - 1) as nat;
    let prev = increasing_cpu_drain_order(bufs, l, u, u2, d, m);
    let k = increasing_cpu_drain_order(bufs, l, u, u2, d, c as nat).len() + j;
    if c < m {
        drained_store_implies_increasing_cpu_drain_order_position(bufs, l, u, u2, d, m, c, j);
        if drained(l, u, u2, d, m as CpuId) { assert((prev + Seq::new(bufs[m as int].len(), |j: int| (m as CpuId, j)))[k] == prev[k]); }
    } else { assert((prev + Seq::new(bufs[m as int].len(), |j: int| (m as CpuId, j)))[k] == (c, j)); }
}

/// Writing the drain set cpu by cpu in increasing id, each oldest first, is one admissible drain order: a step of the fixed
/// increasing-id drain is a kernel step, so the relation holds wherever the fixed-order one did.
pub proof fn increasing_cpu_drain_implies_kernel_mem_step(old: MemState, new: MemState, l: StepLabel, d: CpuId)
    requires
        labeled_step(l, old.u, new.u, d), new.bufs == drained_buffers(old.bufs, l, old.u, new.u, d),
        new.mem == leaf_zeroed_memory(drained_memory(old.mem, old.bufs, l, old.u, new.u, d, NUM_CPUS as nat), l, old.u, new.u, d),
    ensures kernel_mem_step(old, new, l, d),
{
    let order = increasing_cpu_drain_order(old.bufs, l, old.u, new.u, d, NUM_CPUS as nat);
    increasing_cpu_drain_order_implies_drain_order_prefix(old.mem, old.bufs, l, old.u, new.u, d, NUM_CPUS as nat);
    assert forall|c: CpuId, j: int| #![trigger order.contains((c, j))] index_valid(NUM_CPUS, c) && drained(l, old.u, new.u, d, c) && 0 <= j < old.bufs[c as int].len() implies order.contains((c, j)) by {
        drained_store_implies_increasing_cpu_drain_order_position(old.bufs, l, old.u, new.u, d, NUM_CPUS as nat, c, j);
        assert(order[increasing_cpu_drain_order(old.bufs, l, old.u, new.u, d, c as nat).len() + j] == (c, j));
    };
    assert(drain_order(order, old.bufs, l, old.u, new.u, d));
}
} // verus!
