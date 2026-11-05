use vstd::prelude::*;
use crate::*;

// Platform implementation: send an NMI, invalidate the specified non-global
// PCID, or `count` addresses of it 4K or 2M apart by `stride_2m` from `va`, on the
// target CPU without taking locks, and wait for completion; the local forms run
// INVPCID on this CPU.
unsafe extern "C" {
    fn veriflat_remote_flush_pcid(cpu_id: usize, pcid: usize);
    fn veriflat_local_flush_all_pcids();
    fn veriflat_local_flush_va_range(pcid: usize, va: usize, count: usize, stride_2m: bool);
    fn veriflat_remote_flush_va_range(cpu_id: usize, pcid: usize, va: usize, count: usize, stride_2m: bool);
}

verus! {
impl CpuTLB {
    /// The remote cpu may refill the TLB and paging-structure cache of `(cpu_id, pcid)` at once with what it may cache in `k`,
    /// the kernel state whose TLB this is.
    #[verifier::external_body]
    pub fn flush_remote_pcid(&mut self, cpu_id: CpuId, pcid: Pcid, Ghost(k): Ghost<KernelK>, Tracked(lctx): Tracked<&LocalContext>)
        requires
            old(self).inv(),
            k.cpu_tlb == *old(self),
            index_valid(NUM_CPUS, cpu_id),
            cpu_id != lctx.cpu_id(),
            pcid_valid(pcid),
            pcid != KERNEL_DEFAULT_PCID,
            lctx.kernel_view_locking_state() is Release,
        ensures
            final(self).inv(),
            final(self).view() == old(self).view().insert((cpu_id, pcid), final(self).spec_index((cpu_id, pcid))),
            final(self).structure_caches.view() == old(self).structure_caches.view().insert((cpu_id, pcid), final(self).structure_cache((cpu_id, pcid))),
            cpu_tlb_within_may_cache(k, cpu_id, pcid, final(self).spec_index((cpu_id, pcid)), final(self).structure_cache((cpu_id, pcid))),
            forall|c: CpuId, p: Pcid|
                #![trigger final(self).spec_index((c, p))] #![trigger old(self).spec_index((c, p))] #![trigger final(self).structure_cache((c, p))] #![trigger old(self).structure_cache((c, p))]
                index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid)
                    ==> final(self).spec_index((c, p)) == old(self).spec_index((c, p)) && final(self).structure_cache((c, p)) == old(self).structure_cache((c, p)),
    {
        unsafe { veriflat_remote_flush_pcid(cpu_id, pcid); }
        self.cpu_tlbs = Ghost(self.cpu_tlbs.view().insert((cpu_id, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }));
        self.structure_caches = Ghost(self.structure_caches.view().insert((cpu_id, pcid), PagingStructureCache { pml4e: Map::empty(), pdpte: Map::empty(), pde: Map::empty() }));
    }

    /// INVPCID individual-address invalidations on this cpu of the `count` addresses, 4K or 2M apart by `stride_2m`, from
    /// `va` under `pcid`: they drop the translations of those addresses and every paging-structure-cache entry of `pcid`,
    /// and the walker may refill at once what this cpu may cache in `k`, the kernel state whose TLB this is.
    #[verifier::external_body]
    pub fn flush_local_va_range(&mut self, cpu_id: CpuId, pcid: Pcid, va: VAddr, count: usize, stride_2m: bool, Ghost(k): Ghost<KernelK>, Tracked(lctx): Tracked<&LocalContext>)
        requires
            old(self).inv(),
            k.cpu_tlb == *old(self),
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == lctx.cpu_id(),
            pcid_valid(pcid),
            pcid != KERNEL_DEFAULT_PCID,
            va_4k_valid(va),
            stride_2m ==> va_2m_valid(va),
            1 <= count < 0x4000,
            lctx.kernel_view_locking_state() is Release,
        ensures
            final(self).inv(),
            final(self).view() == old(self).view().insert((cpu_id, pcid), final(self).spec_index((cpu_id, pcid))),
            final(self).structure_caches.view() == old(self).structure_caches.view().insert((cpu_id, pcid), final(self).structure_cache((cpu_id, pcid))),
            cpu_tlb_va_range_flushed(k, cpu_id, pcid, va, count, stride_2m, old(self).spec_index((cpu_id, pcid)), final(self).spec_index((cpu_id, pcid)), final(self).structure_cache((cpu_id, pcid))),
            forall|c: CpuId, p: Pcid|
                #![trigger final(self).spec_index((c, p))] #![trigger old(self).spec_index((c, p))] #![trigger final(self).structure_cache((c, p))] #![trigger old(self).structure_cache((c, p))]
                index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid)
                    ==> final(self).spec_index((c, p)) == old(self).spec_index((c, p)) && final(self).structure_cache((c, p)) == old(self).structure_cache((c, p)),
    {
        unsafe { veriflat_local_flush_va_range(pcid, va, count, stride_2m); }
        let ghost old_tlb = self.cpu_tlbs.view().index((cpu_id, pcid));
        self.cpu_tlbs = Ghost(self.cpu_tlbs.view().insert((cpu_id, pcid), SingleTLB {
            tlb_4k: old_tlb.tlb_4k.restrict(old_tlb.tlb_4k.dom().filter(|x: VAddr| !va_range_flush_drops_4k(va, count, stride_2m, x))),
            tlb_2m: old_tlb.tlb_2m.restrict(old_tlb.tlb_2m.dom().filter(|x: VAddr| !va_range_flush_drops_2m(va, count, stride_2m, x))),
            tlb_1g: old_tlb.tlb_1g.restrict(old_tlb.tlb_1g.dom().filter(|x: VAddr| !va_range_flush_drops_1g(va, count, stride_2m, x))),
        }));
        self.structure_caches = Ghost(self.structure_caches.view().insert((cpu_id, pcid), PagingStructureCache { pml4e: Map::empty(), pdpte: Map::empty(), pde: Map::empty() }));
    }

    /// The remote form of `flush_local_va_range`: cpu `cpu_id` runs the invalidations in its NMI handler.
    #[verifier::external_body]
    pub fn flush_remote_va_range(&mut self, cpu_id: CpuId, pcid: Pcid, va: VAddr, count: usize, stride_2m: bool, Ghost(k): Ghost<KernelK>, Tracked(lctx): Tracked<&LocalContext>)
        requires
            old(self).inv(),
            k.cpu_tlb == *old(self),
            index_valid(NUM_CPUS, cpu_id),
            cpu_id != lctx.cpu_id(),
            pcid_valid(pcid),
            pcid != KERNEL_DEFAULT_PCID,
            va_4k_valid(va),
            stride_2m ==> va_2m_valid(va),
            1 <= count < 0x4000,
            lctx.kernel_view_locking_state() is Release,
        ensures
            final(self).inv(),
            final(self).view() == old(self).view().insert((cpu_id, pcid), final(self).spec_index((cpu_id, pcid))),
            final(self).structure_caches.view() == old(self).structure_caches.view().insert((cpu_id, pcid), final(self).structure_cache((cpu_id, pcid))),
            cpu_tlb_va_range_flushed(k, cpu_id, pcid, va, count, stride_2m, old(self).spec_index((cpu_id, pcid)), final(self).spec_index((cpu_id, pcid)), final(self).structure_cache((cpu_id, pcid))),
            forall|c: CpuId, p: Pcid|
                #![trigger final(self).spec_index((c, p))] #![trigger old(self).spec_index((c, p))] #![trigger final(self).structure_cache((c, p))] #![trigger old(self).structure_cache((c, p))]
                index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid)
                    ==> final(self).spec_index((c, p)) == old(self).spec_index((c, p)) && final(self).structure_cache((c, p)) == old(self).structure_cache((c, p)),
    {
        unsafe { veriflat_remote_flush_va_range(cpu_id, pcid, va, count, stride_2m); }
        let ghost old_tlb = self.cpu_tlbs.view().index((cpu_id, pcid));
        self.cpu_tlbs = Ghost(self.cpu_tlbs.view().insert((cpu_id, pcid), SingleTLB {
            tlb_4k: old_tlb.tlb_4k.restrict(old_tlb.tlb_4k.dom().filter(|x: VAddr| !va_range_flush_drops_4k(va, count, stride_2m, x))),
            tlb_2m: old_tlb.tlb_2m.restrict(old_tlb.tlb_2m.dom().filter(|x: VAddr| !va_range_flush_drops_2m(va, count, stride_2m, x))),
            tlb_1g: old_tlb.tlb_1g.restrict(old_tlb.tlb_1g.dom().filter(|x: VAddr| !va_range_flush_drops_1g(va, count, stride_2m, x))),
        }));
        self.structure_caches = Ghost(self.structure_caches.view().insert((cpu_id, pcid), PagingStructureCache { pml4e: Map::empty(), pdpte: Map::empty(), pde: Map::empty() }));
    }

    /// Invalidate every non-default PCID of the calling cpu before it goes Off; each may hold at once what the cpu may cache
    /// under it in `k`, the kernel state whose TLB this is.
    #[verifier::external_body]
    pub fn flush_all_local_pcids(&mut self, cpu_id: CpuId, Ghost(k): Ghost<KernelK>, Tracked(lctx): Tracked<&LocalContext>)
        requires
            old(self).inv(),
            k.cpu_tlb == *old(self),
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == lctx.cpu_id(),
            lctx.kernel_view_locking_state() is Release,
        ensures
            final(self).inv(),
            final(self).view().dom() == old(self).view().dom(),
            forall|p: Pcid| #![trigger final(self).spec_index((cpu_id, p))] #![trigger final(self).structure_cache((cpu_id, p))] pcid_valid(p) && p != KERNEL_DEFAULT_PCID
                ==> cpu_tlb_within_may_cache(k, cpu_id, p, final(self).spec_index((cpu_id, p)), final(self).structure_cache((cpu_id, p))),
            forall|key: (CpuId, Pcid)| #![trigger final(self).view()[key]] #![trigger final(self).structure_caches.view()[key]] old(self).view().dom().contains(key) && (key.0 != cpu_id || key.1 == KERNEL_DEFAULT_PCID)
                ==> final(self).view()[key] == old(self).view()[key] && final(self).structure_caches.view()[key] == old(self).structure_caches.view()[key],
            forall|c: CpuId, p: Pcid|
                #![trigger final(self).spec_index((c, p))] #![trigger old(self).spec_index((c, p))] #![trigger final(self).structure_cache((c, p))] #![trigger old(self).structure_cache((c, p))]
                index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p == KERNEL_DEFAULT_PCID)
                    ==> final(self).spec_index((c, p)) == old(self).spec_index((c, p)) && final(self).structure_cache((c, p)) == old(self).structure_cache((c, p)),
    {
        unsafe { veriflat_local_flush_all_pcids(); }
        let ghost old_tlbs = self.cpu_tlbs.view();
        let ghost old_caches = self.structure_caches.view();
        self.cpu_tlbs = Ghost(Map::new(old_tlbs.dom(), |k: (CpuId, Pcid)| if k.0 == cpu_id && k.1 != KERNEL_DEFAULT_PCID { SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() } } else { old_tlbs.index(k) }));
        self.structure_caches = Ghost(Map::new(old_caches.dom(), |k: (CpuId, Pcid)| if k.0 == cpu_id && k.1 != KERNEL_DEFAULT_PCID {
            PagingStructureCache { pml4e: Map::empty(), pdpte: Map::empty(), pde: Map::empty() }
        } else { old_caches.index(k) }));
    }
}
}
