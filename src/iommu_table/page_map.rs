use vstd::prelude::*;
verus! {
use crate::*;
use super::entry::*;
use super::iommu_page_map_eof::*;
use vstd::simple_pptr::*;

impl PageMap {
    pub open spec fn iommu_wf(&self) -> bool {
        &&& self.wf()
        &&& forall|i: usize| #![trigger self.ar.view().spec_index(i as int)] pei_valid(i) ==> iommu_word_valid(self.ar.view().spec_index(i as int))
        &&& forall|i: usize| #![trigger self.spec_seq.view().spec_index(i as int)] pei_valid(i) ==> {
            &&& !self.spec_seq.view().spec_index(i as int).perm.ps
            &&& !self.spec_seq.view().spec_index(i as int).perm.user
            &&& self.spec_seq.view().spec_index(i as int).perm.write ==> self.spec_seq.view().spec_index(i as int).perm.present
        }
    }
}

pub(crate) fn iommu_page_map_set_published(page_map_ptr: PageMapPtr, Tracked(page_map_perm): Tracked<&mut PointsTo<PageMap>>, index: usize, value: PageEntry, Tracked(lctx): Tracked<&mut LocalContext>)
    requires
        old(page_map_perm).addr() == page_map_ptr,
        old(page_map_perm).is_init(),
        old(page_map_perm).value().iommu_wf(),
        pei_valid(index),
        mem_valid(value.addr),
        !value.perm.ps,
        !value.perm.user,
        value.perm.write ==> value.perm.present,
        old(lctx).kernel_view_locking_state() is Acquire,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(page_map_perm).addr() == page_map_ptr,
        final(page_map_perm).is_init(),
        final(page_map_perm).value().iommu_wf(),
        forall|i: usize|
            #![trigger old(page_map_perm).value().spec_index(i)]
            #![trigger final(page_map_perm).value().spec_index(i)]
            pei_valid(i) && i != index ==> final(page_map_perm).value().spec_index(i) =~= old(page_map_perm).value().spec_index(i),
        final(page_map_perm).value().spec_index(index) =~= value,
        forall|i: int| #![trigger final(page_map_perm).value().ar.view().spec_index(i)]
            0 <= i < 512 && i != index ==> final(page_map_perm).value().ar.view().spec_index(i) == old(page_map_perm).value().ar.view().spec_index(i),
        value.is_empty() ==> final(page_map_perm).value().ar.view().spec_index(index as int) == 0,
{
    proof { lctx.enter_kernel_view_release(); }
    let entry = IommuEntry::from_bit_view(&value);
    let raw = entry.encode();
    let pm = PPtr::<PageMap>::from_usize(page_map_ptr).borrow_mut(Tracked(page_map_perm));
    pm.ar.set(index, raw);
    proof { pm.spec_seq = Ghost(pm.spec_seq.view().update(index as int, value)); }
    proof { iommu_page_map_set_eof_implies_wf(old(page_map_perm).value(), *pm, index, value, raw); }
}

pub(crate) fn iommu_page_map_set_published_in_map(page_map_ptr: PageMapPtr, Tracked(page_map_perms): Tracked<&mut Map<PageMapPtr, PointsTo<PageMap>>>, index: usize, value: PageEntry, Tracked(lctx): Tracked<&mut LocalContext>)
    requires
        old(page_map_perms).dom().contains(page_map_ptr),
        old(page_map_perms).spec_index(page_map_ptr).addr() == page_map_ptr,
        old(page_map_perms).spec_index(page_map_ptr).is_init(),
        old(page_map_perms).spec_index(page_map_ptr).value().iommu_wf(),
        pei_valid(index),
        mem_valid(value.addr),
        !value.perm.ps,
        !value.perm.user,
        value.perm.write ==> value.perm.present,
        old(lctx).kernel_view_locking_state() is Acquire,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(page_map_perms).dom() == old(page_map_perms).dom(),
        forall|p: PageMapPtr| #![trigger final(page_map_perms).spec_index(p)] old(page_map_perms).dom().contains(p) && p != page_map_ptr ==> final(page_map_perms).spec_index(p) == old(page_map_perms).spec_index(p),
        final(page_map_perms).spec_index(page_map_ptr).addr() == page_map_ptr,
        final(page_map_perms).spec_index(page_map_ptr).is_init(),
        final(page_map_perms).spec_index(page_map_ptr).value().iommu_wf(),
        forall|i: usize|
            #![trigger final(page_map_perms).spec_index(page_map_ptr).value().spec_index(i)]
            pei_valid(i) && i != index ==> final(page_map_perms).spec_index(page_map_ptr).value().spec_index(i) =~= old(page_map_perms).spec_index(page_map_ptr).value().spec_index(i),
        final(page_map_perms).spec_index(page_map_ptr).value().spec_index(index) =~= value,
{
    let tracked mut page_map_perm = page_map_perms.tracked_remove(page_map_ptr);
    iommu_page_map_set_published(page_map_ptr, Tracked(&mut page_map_perm), index, value, Tracked(&mut *lctx));
    proof { page_map_perms.tracked_insert(page_map_ptr, page_map_perm); }
}

} // verus!
