use vstd::prelude::*;
use crate::*;

verus! {
pub struct AtomicPcidCr3 {
    atomic: TrustedAtomicUsize,
}

impl AtomicPcidCr3 {
    pub closed spec fn view(&self) -> (PageTableRoot, Pcid) { (self.atomic.view() & MEM_MASK as usize, self.atomic.view() & 0xfffusize) }
    pub closed spec fn owner_cpu(&self) -> CpuId { self.atomic.owner_cpu() }
    pub closed spec fn inv(&self) -> bool {
        &&& page_ptr_valid(self.view().0)
        &&& pcid_valid(self.view().1)
        &&& self.atomic.view() & !(MEM_MASK as usize | 0xfffusize) == 0
    }

    pub fn new(cr3: PageTableRoot, pcid: Pcid, Ghost(owner_cpu): Ghost<CpuId>) -> (ret: Self)
        requires page_ptr_valid(cr3), pcid_valid(pcid), index_valid(NUM_CPUS, owner_cpu),
        ensures ret.inv(), ret.view() == (cr3, pcid), ret.owner_cpu() == owner_cpu,
    {
        let packed = pack_pcid_cr3(cr3, pcid);
        Self { atomic: TrustedAtomicUsize::new(packed, Ghost(owner_cpu)) }
    }

    pub fn load(&self, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: (PageTableRoot, Pcid))
        requires old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            ret == self.view(),
            self.inv() ==> page_ptr_valid(ret.0) && pcid_valid(ret.1),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
    {
        let packed = self.atomic.load(Tracked(&mut *lctx));
        (packed & MEM_MASK as usize, packed & 0xfffusize)
    }

    pub fn store(&mut self, cr3: PageTableRoot, pcid: Pcid, Tracked(lctx): Tracked<&LocalContext>)
        requires
            page_ptr_valid(cr3),
            pcid_valid(pcid),
            old(self).owner_cpu() == lctx.cpu_id(),
            lctx.kernel_view_locking_state() is Release,
        ensures
            final(self).inv(),
            final(self).view() == (cr3, pcid),
            final(self).owner_cpu() == old(self).owner_cpu(),
    {
        let packed = pack_pcid_cr3(cr3, pcid);
        self.atomic.store(packed, Tracked(lctx));
    }
}

fn pack_pcid_cr3(cr3: PageTableRoot, pcid: Pcid) -> (ret: usize)
    requires page_ptr_valid(cr3), pcid_valid(pcid),
    ensures
        ret & MEM_MASK as usize == cr3,
        ret & 0xfffusize == pcid,
        ret & !(MEM_MASK as usize | 0xfffusize) == 0,
{
    assert({
        &&& (cr3 | pcid) & 0x0000_ffff_ffff_f000usize == cr3
        &&& (cr3 | pcid) & 0xfffusize == pcid
        &&& (cr3 | pcid) & !(MEM_MASK as usize | 0xfffusize) == 0
    }) by (bit_vector)
        requires cr3 % 4096 == 0, cr3 / 4096 < 2 * 1024 * 1024, pcid < 4096,
    ;
    cr3 | pcid
}
}
