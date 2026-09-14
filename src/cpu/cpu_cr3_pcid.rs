use vstd::prelude::*;
use crate::*;

verus! {
pub(super) struct CpuCr3Pcid {
    pub(super) hardware: Ghost<(PageTableRoot, Pcid)>,
}

impl CpuCr3Pcid {
    pub(super) closed spec fn cr3(&self) -> PageTableRoot { self.hardware.view().0 }
    pub(super) closed spec fn pcid(&self) -> Pcid { self.hardware.view().1 }

    pub(super) fn flush_current(&mut self, cpu_id: CpuId, cr3: PageTableRoot, pcid: Pcid, tlb: &mut CpuTLB, Tracked(lctx): Tracked<&LocalContext>)
        requires
            old(tlb).inv(),
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == lctx.cpu_id(),
            page_ptr_valid(cr3),
            pcid_valid(pcid),
            old(self).cr3() == cr3,
            old(self).pcid() == pcid,
            lctx.kernel_view_locking_state() is Release,
        ensures
            *final(self) == *old(self),
            final(tlb).inv(),
            forall|c: CpuId, p: Pcid| #![trigger final(tlb).spec_index((c, p))] #![trigger old(tlb).spec_index((c, p))] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid) ==> final(tlb).spec_index((c, p)) == old(tlb).spec_index((c, p)),
            final(tlb).spec_index((cpu_id, pcid)).is_empty(),
            final(tlb).view() == old(tlb).view().insert((cpu_id, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }),
    {
        tlb.write_cr3_pcid(cpu_id, cr3, pcid, true, self, Tracked(lctx));
    }

    pub(super) fn write(&mut self, cpu_id: CpuId, cr3: PageTableRoot, pcid: Pcid, flush: bool, tlb: &mut CpuTLB, Tracked(lctx): Tracked<&mut LocalContext>)
        requires
            old(lctx).kernel_view_locking_state() is Acquire,
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            page_ptr_valid(cr3),
            pcid_valid(pcid),
            old(tlb).inv(),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(self).cr3() == cr3,
            final(self).pcid() == pcid,
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).lock_id_set() == old(lctx).lock_id_set(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            lock_id_set_aligned(old(lctx)) ==> lock_id_set_aligned(final(lctx)),
            final(tlb).inv(),
            !flush ==> *final(tlb) == *old(tlb),
            forall|other_cpu: CpuId, other_pcid: Pcid|
                #![trigger final(tlb).spec_index((other_cpu, other_pcid))]
                #![trigger old(tlb).spec_index((other_cpu, other_pcid))]
                index_valid(NUM_CPUS, other_cpu) && pcid_valid(other_pcid) ==>
                    final(tlb).spec_index((other_cpu, other_pcid)) == if flush && other_cpu == cpu_id && other_pcid == pcid { SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() } } else { old(tlb).spec_index((other_cpu, other_pcid)) },
            final(tlb).view() == if flush { old(tlb).view().insert((cpu_id, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }) } else { old(tlb).view() },
    {
        proof { lctx.enter_kernel_view_release(); }
        tlb.write_cr3_pcid(cpu_id, cr3, pcid, flush, self, Tracked(&*lctx));
    }
}
}
