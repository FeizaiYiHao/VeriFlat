use vstd::prelude::*;

verus! {
use crate::*;
use vstd::simple_pptr::*;
use super::entry::*;
use super::pagemap::*;
use core::mem::MaybeUninit;

/// Raw PageMap mutation for an unpublished page-table page.
///
/// This helper intentionally has no `LocalContext` phase contract: constructors
/// initialize many entries before the page-table page is reachable by any CPU or
/// IOMMU page walk. Published page tables must use `page_map_set_published`.
///
/// `mem_valid(value.addr)` is required because `PageMap::wf()` requires every
/// kernel-present entry to contain a valid physical address. The implementation
/// uses `PageMap::set_internal` so upper-level entries whose software-only
/// `kernel_present` bit is clear are still stored exactly.
fn page_map_set_raw(
    page_map_ptr: PageMapPtr,
    Tracked(page_map_perm): Tracked<&mut PointsTo<PageMap>>,
    index: usize,
    value: PageEntry,
)
    requires
        old(page_map_perm).addr() == page_map_ptr,
        old(page_map_perm).is_init(),
        old(page_map_perm).value().wf(),
        pei_valid(index),
        mem_valid(value.addr),
    ensures
        final(page_map_perm).addr() == page_map_ptr,
        final(page_map_perm).is_init(),
        final(page_map_perm).value().wf(),
        forall|i: usize|
            #![trigger final(page_map_perm).value().spec_index(i)]
            pei_valid(i) && i != index ==> final(page_map_perm).value().spec_index(i) =~= old(page_map_perm).value().spec_index(i),
        final(page_map_perm).value().spec_index(index) =~= value,
{
    let pptr: PPtr<PageMap> = PPtr::from_addr(page_map_ptr);
    let pm: &mut PageMap = pptr.borrow_mut(Tracked(page_map_perm));
    pm.set_internal(index, value);
}

pub fn page_map_copy_kernel_entry_range(
    source_ptr: PageMapPtr,
    Tracked(source_perm): Tracked<&PointsTo<PageMap>>,
    target_ptr: PageMapPtr,
    Tracked(target_perm): Tracked<&mut PointsTo<PageMap>>,
    end: usize,
)
    requires
        source_perm.addr() == source_ptr,
        source_perm.is_init(),
        source_perm.value().wf(),
        old(target_perm).addr() == target_ptr,
        old(target_perm).is_init(),
        old(target_perm).value().wf(),
        pei_valid(end),
        forall|i: usize| #![trigger old(target_perm).value().spec_index(i).is_empty()]
            pei_valid(i) ==> old(target_perm).value().spec_index(i).is_empty(),
    ensures
        final(target_perm).addr() == target_ptr,
        final(target_perm).is_init(),
        final(target_perm).value().wf(),
        forall|i: usize|
            #![trigger final(target_perm).value().spec_index(i).is_empty()]
            end <= i && pei_valid(i) ==> final(target_perm).value().spec_index(i).is_empty(),
        forall|i: usize|
            #![trigger final(target_perm).value().spec_index(i)]
            0 <= i < end ==> final(target_perm).value().spec_index(i) =~= source_perm.value().spec_index(i),
{
    let source: &PageMap = PPtr::<PageMap>::from_usize(source_ptr).borrow(Tracked(source_perm));
    for index in 0..end
        invariant
            0 <= index <= end,
            pei_valid(end),
            source_perm.addr() == source_ptr,
            source_perm.is_init(),
            source_perm.value().wf(),
            source.wf(),
            source == source_perm.value(),
            target_perm.addr() == target_ptr,
            target_perm.is_init(),
            target_perm.value().wf(),
            forall|i: usize|
                #![trigger target_perm.value().spec_index(i).is_empty()]
                end <= i && pei_valid(i) ==> target_perm.value().spec_index(i).is_empty(),
            forall|i: usize|
                #![trigger target_perm.value().spec_index(i)]
                0 <= i < index ==> target_perm.value().spec_index(i) =~= source_perm.value().spec_index(i),
    {
        let raw = *source.ar.get(index);
        let addr = usize2pa(raw);
        let value = usize2page_entry(raw);
        page_map_set_raw(target_ptr, Tracked(&mut *target_perm), index, value);
    }
}

impl PageTable<PT_TYPE> {
    pub fn copy_kernel_entries_to_unpublished_root(
        &self,
        target_ptr: PageMapPtr,
        Tracked(target_perm): Tracked<&mut PointsTo<PageMap>>,
    )
        requires
            self.wf(),
            old(target_perm).addr() == target_ptr,
            old(target_perm).is_init(),
            old(target_perm).value().wf(),
            forall|i: usize| #![trigger old(target_perm).value().spec_index(i).is_empty()]
                pei_valid(i) ==> old(target_perm).value().spec_index(i).is_empty(),
        ensures
            final(target_perm).addr() == target_ptr,
            final(target_perm).is_init(),
            final(target_perm).value().wf(),
        forall|i: usize|
                #![trigger final(target_perm).value().spec_index(i).is_empty()]
                self.kernel_l4_end <= i && pei_valid(i) ==> final(target_perm).value().spec_index(i).is_empty(),
            forall|i: usize|
                #![trigger final(target_perm).value().spec_index(i)]
                0 <= i < self.kernel_l4_end ==> final(target_perm).value().spec_index(i) =~= self.kernel_entries.view().spec_index(i as int),
    {
        assert({
            &&& self.l4_table.view().dom().contains(self.cr3)
            &&& self.l4_table.view().spec_index(self.cr3).addr() == self.cr3
            &&& self.l4_table.view().spec_index(self.cr3).is_init()
            &&& self.l4_table.view().spec_index(self.cr3).value().wf()
        }) by { reveal(PageTable::wf_l4); };
        assert(pei_valid(self.kernel_l4_end)) by { reveal(PageTable::kernel_entries_wf); };
        let tracked source_perm = self.l4_table.borrow().tracked_borrow(self.cr3);
        page_map_copy_kernel_entry_range(self.cr3, Tracked(source_perm), target_ptr, Tracked(&mut *target_perm), self.kernel_l4_end);
        proof { reveal(PageTable::kernel_entries_wf); }
    }
}

pub(super) fn page_map_set_published(page_map_ptr: PageMapPtr, Tracked(page_map_perm): Tracked<&mut PointsTo<PageMap>>, index: usize, value: PageEntry, Tracked(lctx): Tracked<&mut LocalContext>)
    requires
        old(page_map_perm).addr() == page_map_ptr,
        old(page_map_perm).is_init(),
        old(page_map_perm).value().wf(),
        pei_valid(index),
        mem_valid(value.addr),
        old(lctx).kernel_view_locking_state() is Acquire,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(page_map_perm).addr() == page_map_ptr,
        final(page_map_perm).is_init(),
        final(page_map_perm).value().wf(),
        forall|i: usize|
            #![trigger
                old(page_map_perm).value().spec_index(i),
            ]
            #![trigger
                final(page_map_perm).value().spec_index(i),
            ]
            pei_valid(i) && i != index ==> final(page_map_perm).value().spec_index(i) =~= old(page_map_perm).value().spec_index(i),
        final(page_map_perm).value().spec_index(index) =~= value,
{
    proof { lctx.enter_kernel_view_release(); }
    page_map_set_raw(page_map_ptr, Tracked(page_map_perm), index, value);
}

pub(super) fn page_map_set_published_in_map(page_map_ptr: PageMapPtr, Tracked(page_map_perms): Tracked<&mut Map<PageMapPtr, PointsTo<PageMap>>>, index: usize, value: PageEntry, Tracked(lctx): Tracked<&mut LocalContext>)
    requires
        old(page_map_perms).dom().contains(page_map_ptr),
        old(page_map_perms).spec_index(page_map_ptr).addr() == page_map_ptr,
        old(page_map_perms).spec_index(page_map_ptr).is_init(),
        old(page_map_perms).spec_index(page_map_ptr).value().wf(),
        pei_valid(index),
        mem_valid(value.addr),
        old(lctx).kernel_view_locking_state() is Acquire,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(page_map_perms).dom() == old(page_map_perms).dom(),
        forall|p: PageMapPtr|
            #![trigger final(page_map_perms).spec_index(p)]
            old(page_map_perms).dom().contains(p) && p != page_map_ptr ==> final(page_map_perms).spec_index(p) == old(page_map_perms).spec_index(p),
        final(page_map_perms).spec_index(page_map_ptr).addr() == page_map_ptr,
        final(page_map_perms).spec_index(page_map_ptr).is_init(),
        final(page_map_perms).spec_index(page_map_ptr).value().wf(),
        forall|i: usize|
            #![trigger final(page_map_perms).spec_index(page_map_ptr).value().spec_index(i)]
            pei_valid(i) && i != index ==> final(page_map_perms).spec_index(page_map_ptr).value().spec_index(i) =~= old(page_map_perms).spec_index(page_map_ptr).value().spec_index(i),
        final(page_map_perms).spec_index(page_map_ptr).value().spec_index(index) =~= value,
{
    let tracked mut page_map_perm = page_map_perms.tracked_remove(page_map_ptr);
    page_map_set_published(page_map_ptr, Tracked(&mut page_map_perm), index, value, Tracked(&mut *lctx));
    proof { page_map_perms.tracked_insert(page_map_ptr, page_map_perm); }
}

#[verifier(external_body)]
pub fn page_perm_to_page_map(page_ptr: PagePtr, Tracked(page_perm): Tracked<PagePerm4k>) -> (ret: (
    PageMapPtr,
    Tracked<PointsTo<PageMap>>,
))
    requires
        page_perm.is_init(),
        page_perm.addr() == page_ptr,
    ensures
        ret.0 == page_ptr,
        ret.1.view().addr() == ret.0,
        ret.1.view().is_init(),
        ret.1.view().value().wf(),
        forall|i: usize|
            #![trigger ret.1.view().value().spec_index(i).is_empty()]
            pei_valid(i) ==> ret.1.view().value().spec_index(i).is_empty(),
{
    unsafe {
        let uptr = page_ptr as *mut MaybeUninit<PageMap>;
        for i in 0..512 {
            (*uptr).assume_init_mut().set_unpublished(i, PageEntry::empty());
        }
    }
    (page_ptr, Tracked::assume_new())
}

// PERF: ~19 ms / ~144k rlimit. Loop over NUM_CPUS with submap_by_transitivity broadcast
// inside the body and a per-iteration assert-forall to re-establish the submap_of invariant
// across the updated seq element.
pub fn flush_tlb_4kentry(tlbmap_4k: Ghost<Seq<Map<VAddr, MapEntry>>>, va: Ghost<VAddr>) -> (ret:
    Ghost<Seq<Map<VAddr, MapEntry>>>)
    requires
        NUM_CPUS > 0,
        tlbmap_4k.view().len() == NUM_CPUS,
    ensures
        ret.view().len() == NUM_CPUS,
        forall|cpu_id: CpuId|
            #![trigger ret.view().spec_index(cpu_id as int)]
            index_valid(NUM_CPUS, cpu_id) ==> !(ret.view().spec_index(cpu_id as int).contains_key(va.view())),
        forall|cpu_id: CpuId|
            #![trigger ret.view().spec_index(cpu_id as int)]
            #![trigger tlbmap_4k.view().spec_index(cpu_id as int)]
            index_valid(NUM_CPUS, cpu_id) ==> ret.view().spec_index(cpu_id as int).submap_of(tlbmap_4k.view().spec_index(cpu_id as int)),
{
    let mut cpu_id = 0;
    let mut ret_map = tlbmap_4k;

    // #[verifier::loop_isolation(false)]
    for cpu_id in 0..NUM_CPUS
        invariant
            0 <= cpu_id <= NUM_CPUS,
            tlbmap_4k.view().len() == NUM_CPUS,
            ret_map.view().len() == NUM_CPUS,
            forall|cpu_i: CpuId|
                #![auto]
                0 <= cpu_i < cpu_id ==> ret_map.view().spec_index(cpu_i as int).contains_key(va.view()) == false,
            forall|cpu_i: CpuId|
                #![trigger ret_map.view().spec_index(cpu_i as int)]
                index_valid(NUM_CPUS, cpu_i) ==> ret_map.view().spec_index(cpu_i as int).submap_of(tlbmap_4k.view().spec_index(cpu_i as int)),
    {
        proof {
            let old_at_i = ret_map.view().spec_index(cpu_id as int);
            let tlbmap = old_at_i.remove(va.view());
            // tlbmap is a submap of old_at_i, which (by loop invariant) is a submap of tlbmap_4k[cpu_id]
            assert(tlbmap.submap_of(tlbmap_4k.view().spec_index(cpu_id as int))) by {
            }
            let tlbseq = ret_map.view().update(cpu_id as int, tlbmap);
            *ret_map.borrow_mut() = tlbseq;
        }
    }
    ret_map
}
} // verus!
