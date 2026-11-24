//! The state of the user-memory machine, its labels, and the byte-level helpers: overwriting a byte range, memory after a
//! sequence of stores, and the byte a cpu's own loads see.
use vstd::prelude::*;
use crate::*;

verus! {
/// A store a cpu issued and has not yet written to memory: `bytes` at byte `offset` of the page of size `size` that the
/// translation at `base_va` under `pcid` names, whose frame is `frame`.
pub ghost struct PendingStore { pub pcid: Pcid, pub size: PageSize, pub base_va: VAddr, pub frame: PAddr, pub offset: nat, pub bytes: Seq<u8> }

/// The kernel's user state, one byte per physical address, and each cpu's pending stores, oldest first, indexed by cpu id.
pub ghost struct MemState { pub u: KernelU, pub mem: IMap<PAddr, u8>, pub bufs: Seq<Seq<PendingStore>> }

/// One step of the machine: a kernel step, or a user store, commit, or load, or a device write.
pub ghost enum MemLabel {
    Kernel { label: StepLabel },
    StoreIssued { s: PendingStore },
    StoreCommitted,
    Load { size: PageSize, frame: PAddr, va: VAddr, offset: nat, value: Seq<u8> },
    DmaWritten { did: VtdDomainId, iova: VAddr, frame: PAddr, offset: nat, bytes: Seq<u8> },
}

/// A state of a behaviour with the label and cpu of the step taken from it.
pub ghost struct MemSnap { pub st: MemState, pub label: MemLabel, pub cpu: CpuId }

/// An infinite execution.
pub type Execution<T> = spec_fn(nat) -> T;

/// The number of bytes of a page of size `size`.
pub open spec fn page_size_bytes(size: PageSize) -> nat {
    match size {
        PageSize::SZ4k => 0x1000,
        PageSize::SZ2m => 0x200000,
        PageSize::SZ1g => 0x40000000,
    }
}

/// The translations of size `size` that `tlb` caches.
pub open spec fn tlb_of_size(tlb: SingleTLB, size: PageSize) -> Map<VAddr, TLBEntry> {
    match size {
        PageSize::SZ4k => tlb.tlb_4k,
        PageSize::SZ2m => tlb.tlb_2m,
        PageSize::SZ1g => tlb.tlb_1g,
    }
}

/// `tlb` caches a writable translation of size `size` at `va` naming the frame `frame`.
pub open spec fn tlb_writable_at(tlb: SingleTLB, size: PageSize, va: VAddr, frame: PAddr) -> bool {
    tlb_of_size(tlb, size).dom().contains(va) && tlb_of_size(tlb, size)[va].write && tlb_of_size(tlb, size)[va].addr == frame
}

/// The physical address of the first byte `s` writes.
pub open spec fn store_base(s: PendingStore) -> int { s.frame + s.offset }

/// `s` writes the physical byte `a`.
pub open spec fn store_covers(s: PendingStore, a: PAddr) -> bool { store_base(s) <= a < store_base(s) + s.bytes.len() }

/// `mem` with `bytes` written from the physical address `base` on.
pub open spec fn mem_overwrite(mem: IMap<PAddr, u8>, base: int, bytes: Seq<u8>) -> IMap<PAddr, u8> {
    IMap::total(|a: PAddr| if base <= a < base + bytes.len() { bytes[a - base] } else { mem[a] })
}

/// `mem` with `s` written.
pub open spec fn mem_after_store(mem: IMap<PAddr, u8>, s: PendingStore) -> IMap<PAddr, u8> { mem_overwrite(mem, store_base(s), s.bytes) }

/// `mem` after the stores of `stores` are written in order, first to last.
pub open spec fn mem_after_stores(mem: IMap<PAddr, u8>, stores: Seq<PendingStore>) -> IMap<PAddr, u8>
    decreases stores.len(),
{
    if stores.len() == 0 { mem } else { mem_after_store(mem_after_stores(mem, stores.drop_last()), stores.last()) }
}

/// The physical byte `a` as loads of the cpu with buffer `buf` see it: the youngest store of `buf` covering it, else
/// `mem_byte`.
pub open spec fn forwarded_byte(buf: Seq<PendingStore>, a: PAddr, mem_byte: u8) -> u8
    decreases buf.len(),
{
    if buf.len() == 0 { mem_byte } else if store_covers(buf.last(), a) { buf.last().bytes[a - store_base(buf.last())] } else { forwarded_byte(buf.drop_last(), a, mem_byte) }
}

/// Byte `a` of `mem_overwrite(mem, base, bytes)`.
pub proof fn mem_overwrite_index_implies_byte(mem: IMap<PAddr, u8>, base: int, bytes: Seq<u8>, a: PAddr)
    ensures mem_overwrite(mem, base, bytes)[a] == if base <= a < base + bytes.len() { bytes[a - base] } else { mem[a] },
{ assert(ISet::<PAddr>::full().contains(a)); }

/// A byte that `mem_after_stores` changes is covered by one of the stores.
pub proof fn mem_after_stores_changed_implies_covering_store(mem: IMap<PAddr, u8>, stores: Seq<PendingStore>, a: PAddr) -> (j: int)
    requires mem_after_stores(mem, stores)[a] != mem[a],
    ensures 0 <= j < stores.len(), store_covers(stores[j], a),
    decreases stores.len(),
{
    let prev = mem_after_stores(mem, stores.drop_last());
    mem_overwrite_index_implies_byte(prev, store_base(stores.last()), stores.last().bytes, a);
    if store_covers(stores.last(), a) { (stores.len() - 1) as int } else {
        let j = mem_after_stores_changed_implies_covering_store(mem, stores.drop_last(), a);
        j
    }
}

/// Writing no stores keeps memory.
pub proof fn no_stores_implies_mem_kept(mem: IMap<PAddr, u8>)
    ensures mem_after_stores(mem, Seq::<PendingStore>::empty()) == mem,
{}
} // verus!
