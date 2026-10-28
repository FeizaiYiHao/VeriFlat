use vstd::prelude::*;
use crate::*;

verus! {
pub(super) struct CpuCr3Pcid {
    /// What the last `mov cr3` loaded; only `CpuTLB::write_cr3_pcid` moves it.
    pub(super) hardware: Ghost<(PageTableRoot, Pcid)>,
    /// Exec copy of `hardware`, so a switch to the same root and pcid skips the `mov cr3`.
    pub(super) current_cr3: PageTableRoot,
    pub(super) current_pcid: Pcid,
}

impl CpuCr3Pcid {
    pub(super) closed spec fn cr3(&self) -> PageTableRoot { self.hardware.view().0 }
    pub(super) closed spec fn pcid(&self) -> Pcid { self.hardware.view().1 }
    /// The exec copy matches the physical register; part of the cpu lock invariant.
    pub(super) closed spec fn wf(&self) -> bool { self.hardware.view() == (self.current_cr3, self.current_pcid) }

    pub(super) fn new(cr3: PageTableRoot, pcid: Pcid) -> (ret: Self)
        ensures
            ret.wf(),
            ret.cr3() == cr3,
            ret.pcid() == pcid,
    {
        Self { hardware: Ghost((cr3, pcid)), current_cr3: cr3, current_pcid: pcid }
    }

    pub(super) fn flush_current(&mut self, cpu_id: CpuId, cr3: PageTableRoot, pcid: Pcid, tlb: &mut CpuTLB, Ghost(k): Ghost<KernelK>, Ghost(next_table): Ghost<Option<RwLockPageTableRoot>>,
        Tracked(lctx): Tracked<&LocalContext>)
        requires
            old(tlb).inv(),
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == lctx.cpu_id(),
            page_ptr_valid(cr3),
            pcid_valid(pcid),
            old(self).cr3() == cr3,
            old(self).pcid() == pcid,
            lctx.kernel_view_locking_state() is Release,
            next_table matches Some(ptr) ==> k.pt_mp.dom().contains(ptr) && k.pt_mp.spec_index(ptr).view().cr3 == cr3,
        ensures
            *final(self) == *old(self),
            final(tlb).inv(),
            forall|c: CpuId, p: Pcid| #![trigger final(tlb).spec_index((c, p))] #![trigger old(tlb).spec_index((c, p))] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid) ==> final(tlb).spec_index((c, p)) == old(tlb).spec_index((c, p)),
            final(tlb).view() == old(tlb).view().insert((cpu_id, pcid), final(tlb).spec_index((cpu_id, pcid))),
            match next_table {
                Some(ptr) => single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(tlb).spec_index((cpu_id, pcid)), pagetable_c(k.pt_mp, k.pt_lower.view(), ptr)),
                None => final(tlb).spec_index((cpu_id, pcid)).is_empty(),
            },
    {
        tlb.write_cr3_pcid(cpu_id, cr3, pcid, true, self, Ghost(k), Ghost(next_table), Tracked(lctx));
    }

    pub(super) fn write(&mut self, cpu_id: CpuId, cr3: PageTableRoot, pcid: Pcid, flush: bool, tlb: &mut CpuTLB, Ghost(k): Ghost<KernelK>,
        Ghost(next_table): Ghost<Option<RwLockPageTableRoot>>, Tracked(lctx): Tracked<&mut LocalContext>)
        requires
            old(self).wf(),
            old(lctx).kernel_view_locking_state() is Acquire,
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            page_ptr_valid(cr3),
            pcid_valid(pcid),
            old(tlb).inv(),
            next_table matches Some(ptr) ==> k.pt_mp.dom().contains(ptr) && k.pt_mp.spec_index(ptr).view().cr3 == cr3,
        ensures
            final(self).wf(),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(self).cr3() == cr3,
            final(self).pcid() == pcid,
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            final(tlb).inv(),
            !flush ==> *final(tlb) == *old(tlb),
            forall|other_cpu: CpuId, other_pcid: Pcid|
                #![trigger final(tlb).spec_index((other_cpu, other_pcid))]
                #![trigger old(tlb).spec_index((other_cpu, other_pcid))]
                index_valid(NUM_CPUS, other_cpu) && pcid_valid(other_pcid) && (other_cpu != cpu_id || other_pcid != pcid)
                    ==> final(tlb).spec_index((other_cpu, other_pcid)) == old(tlb).spec_index((other_cpu, other_pcid)),
            final(tlb).view() == if flush { old(tlb).view().insert((cpu_id, pcid), final(tlb).spec_index((cpu_id, pcid))) } else { old(tlb).view() },
            flush ==> match next_table {
                Some(ptr) => single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(tlb).spec_index((cpu_id, pcid)), pagetable_c(k.pt_mp, k.pt_lower.view(), ptr)),
                None => final(tlb).spec_index((cpu_id, pcid)).is_empty(),
            },
    {
        proof { lctx.enter_kernel_view_release(); }
        if flush || self.current_cr3 != cr3 || self.current_pcid != pcid {
            tlb.write_cr3_pcid(cpu_id, cr3, pcid, flush, self, Ghost(k), Ghost(next_table), Tracked(&*lctx));
            self.current_cr3 = cr3;
            self.current_pcid = pcid;
        }
    }
}
}
