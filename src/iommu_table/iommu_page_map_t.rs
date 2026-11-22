use vstd::prelude::*;

verus! {
use crate::*;
use vstd::simple_pptr::*;

/// The 512 words of an IOMMU table page. The words are private: `set` is the only exec writer, so every store
/// into an IOMMU table page reaches memory before a remapping unit that does not snoop CPU caches can need it.
#[repr(C)]
pub struct IommuArray {
    ar: [usize; 512],
}

impl IommuArray {
    pub closed spec fn view(&self) -> Seq<usize> { self.ar.view() }
    pub open spec fn wf(&self) -> bool { self.view().len() == 512 }

    pub fn get(&self, i: usize) -> (out: &usize)
        requires
            0 <= i < 512,
            self.wf(),
        ensures
            *out == self.view().spec_index(i as int),
    {
        &self.ar[i]
    }

    /// TCB: stores word `i`, then writes its cache line back to memory through the glue hook.
    #[verifier::external_body]
    pub fn set(&mut self, i: usize, raw: usize)
        requires
            0 <= i < 512,
            old(self).wf(),
        ensures
            final(self).view() =~= old(self).view().update(i as int, raw),
            final(self).wf(),
    {
        let word = &mut self.ar[i] as *mut usize;
        unsafe {
            core::ptr::write_volatile(word, raw);
            veriflat_iommu_flush_to_memory(word as usize, core::mem::size_of::<usize>());
        }
    }
}

/// TCB: an owned 4K page becomes an empty IOMMU table page; its bytes are zeroed and written back to memory through the
/// glue hook before the page can be linked.
#[verifier::external_body]
pub fn iommu_page_perm_to_page_map(pg_ptr: PagePtr, Tracked(page_perm): Tracked<PagePerm4k>) -> (ret: (PageMapPtr, Tracked<PointsTo<IommuPageMap>>))
    requires
        page_perm.is_init(),
        page_perm.addr() == pg_ptr,
    ensures
        ret.0 == pg_ptr,
        ret.1.view().addr() == ret.0,
        ret.1.view().is_init(),
        ret.1.view().value().wf(),
        forall|i: usize| #![trigger ret.1.view().value().spec_index(i).is_empty()] pei_valid(i) ==> ret.1.view().value().spec_index(i).is_empty(),
        forall|i: usize| #![trigger ret.1.view().value().ar.view().spec_index(i as int)]
            pei_valid(i) ==> ret.1.view().value().ar.view().spec_index(i as int) == 0usize,
{
    unsafe {
        core::ptr::write_bytes(pg_ptr as *mut u8, 0, PAGE_SZ_4K);
        veriflat_iommu_flush_to_memory(pg_ptr, PAGE_SZ_4K);
    }
    (pg_ptr, Tracked::assume_new())
}

/// TCB: an IOMMU table page that its table no longer links is an ordinary 4K page again; its bytes stay as they are.
/// Assumed: the remapping hardware reaches a table page only through the table's links or through its own caches, and its
/// caches are exactly what `IommuTLB` models. The paging-structure caches are emptied per domain by the domain-selective
/// IOTLB invalidation (VT-d 5.20, 6.5.1.2) and with `CAP.CM = 0` hold only entries of successful walks (6.2.5.5), so a
/// page that `iommu_page_unreferenced_by_iommu_caches` clears is reached by no cached walk and the unit no longer reads it.
#[verifier::external_body]
pub fn iommu_page_map_to_page_perm(page_map_ptr: PageMapPtr, Tracked(page_map_perm): Tracked<PointsTo<IommuPageMap>>, iommu_tlb: &IommuTLB) -> (ret: Tracked<PagePerm4k>)
    requires
        page_map_perm.is_init(),
        page_map_perm.addr() == page_map_ptr,
        iommu_page_unreferenced_by_iommu_caches(*iommu_tlb, page_map_ptr),
    ensures
        ret.view().is_init(),
        ret.view().addr() == page_map_ptr,
{
    let _ = (page_map_ptr, iommu_tlb);
    Tracked::assume_new()
}
} // verus!
