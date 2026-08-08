use vstd::prelude::*;

verus! {

use crate::define::*;
use vstd::simple_pptr::*;
use crate::util::page_ptr_util_u::*;
use super::entry::*;
use super::pagemap::*;
use core::mem::MaybeUninit;
use crate::primitive::*;
use crate::lemma::lemma_u::*;
use crate::locks::*;

fn page_map_set_kernel_entry_range(
    kernel_entries: &Array<usize, KERNEL_MEM_END_L4INDEX>,
    page_map_ptr: PageMapPtr,
    Tracked(page_map_perm): Tracked<&mut PointsTo<PageMap>>,
)
    requires
        old(page_map_perm).addr() == page_map_ptr,
        old(page_map_perm).is_init(),
        old(page_map_perm).value().wf(),
        kernel_entries.wf(),
        kernel_entries.view().len() == KERNEL_MEM_END_L4INDEX,
    ensures
        final(page_map_perm).addr() == page_map_ptr,
        final(page_map_perm).is_init(),
        final(page_map_perm).value().wf(),
        forall|i: usize|
            #![trigger final(page_map_perm).value().spec_index(i)]
            KERNEL_MEM_END_L4INDEX <= i < 512 ==> final(page_map_perm).value().spec_index(i) =~= old(page_map_perm).value().spec_index(i),
        forall|i: usize|
            #![trigger final(page_map_perm).value().spec_index(i)]
            0 <= i < KERNEL_MEM_END_L4INDEX ==> final(page_map_perm).value().spec_index(i) =~= usize2page_entry(
                kernel_entries.view().spec_index(i as int),
            ),
{
    for index in 0..KERNEL_MEM_END_L4INDEX
        invariant
            0 <= index <= KERNEL_MEM_END_L4INDEX,
            kernel_entries.wf(),
            kernel_entries.view().len() == KERNEL_MEM_END_L4INDEX,
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i: usize|
                #![trigger page_map_perm.value().spec_index(i)]
                KERNEL_MEM_END_L4INDEX <= i < 512 ==> page_map_perm.value().spec_index(i) =~= old(
                    page_map_perm,
                ).value().spec_index(i),
            forall|i: usize|
                #![trigger page_map_perm.value().spec_index(i)]
                0 <= i < index ==> page_map_perm.value().spec_index(i) =~= usize2page_entry(
                    kernel_entries.view().spec_index(i as int),
                ),
    {
        let v = *kernel_entries.get(index);
        let value = usize2page_entry(v);
        // mem_valid(value.addr) holds because usize2pa always masks to a valid address.
        assert(mem_valid(value.addr)) by {
            assert((v & 0x0000_ffff_ffff_f000u64 as usize) & (!0x0000_ffff_ffff_f000u64) as usize == 0)
                by (bit_vector);
        }
        page_map_set_raw(
            page_map_ptr,
            Tracked(page_map_perm),
            index,
            value,
        );
    }
}

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
        0 <= index < 512,
        mem_valid(value.addr),
    ensures
        final(page_map_perm).addr() == page_map_ptr,
        final(page_map_perm).is_init(),
        final(page_map_perm).value().wf(),
        forall|i: usize|
            #![trigger final(page_map_perm).value().spec_index(i)]
            0 <= i < 512 && i != index ==> final(page_map_perm).value().spec_index(i) =~= old(page_map_perm).value().spec_index(i),
        final(page_map_perm).value().spec_index(index) =~= value,
{
    let pptr: PPtr<PageMap> = PPtr::from_addr(page_map_ptr);
    let pm: &mut PageMap = pptr.borrow_mut(Tracked(page_map_perm));
    pm.set_internal(index, value);
}

/// The single PageMap write gate for a page-table page that is already published.
///
/// A kernel-level caller first opens a `KernelSteps` user-view step; that operation
/// changes both `LocalContext` phases from Acquire to Release. This helper checks
/// and preserves that Release phase. The phase is only the proof model for abstract
/// kernel/user interleaving and step-ledger discipline. It does *not* establish
/// machine-level PTE-store atomicity or CPU/MMU memory ordering. The concrete
/// write ultimately reaches the trusted `Array::set`; this layer only models the
/// abstract state transition.
///
/// Nor does this phase contract permit arbitrary PTE replacement. Each PageTable
/// operation must retain its transition-specific proof: publish only initialized
/// children or fresh leaves, clear user `present` before invalidation, and remove
/// the kernel-view entry only after every stale TLB translation is gone.
/// Release-to-Release also does not prove that a step performs only one PTE write
/// or that this store is its final executable mutation; that stronger property
/// would require a linear, one-shot write permit owned by `KernelSteps`.
pub(super) fn page_map_set_published(
    page_map_ptr: PageMapPtr,
    Tracked(page_map_perm): Tracked<&mut PointsTo<PageMap>>,
    index: usize,
    value: PageEntry,
    Tracked(lctx): Tracked<&LocalContext>,
)
    requires
        old(page_map_perm).addr() == page_map_ptr,
        old(page_map_perm).is_init(),
        old(page_map_perm).value().wf(),
        0 <= index < 512,
        mem_valid(value.addr),
        lctx.kernel_view_locking_state() is Release,
    ensures
        final(page_map_perm).addr() == page_map_ptr,
        final(page_map_perm).is_init(),
        final(page_map_perm).value().wf(),
        forall|i: usize|
            #![trigger final(page_map_perm).value().spec_index(i)]
            0 <= i < 512 && i != index ==> final(page_map_perm).value().spec_index(i) =~= old(page_map_perm).value().spec_index(i),
        final(page_map_perm).value().spec_index(index) =~= value,
{
    page_map_set_raw(page_map_ptr, Tracked(page_map_perm), index, value);
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
            0 <= i < 512 ==> ret.1.view().value().spec_index(i).is_empty(),
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
            0 <= cpu_id < NUM_CPUS ==> !(ret.view().spec_index(cpu_id as int).contains_key(va.view())),
        forall|cpu_id: CpuId|
            #![trigger ret.view().spec_index(cpu_id as int)]
            #![trigger tlbmap_4k.view().spec_index(cpu_id as int)]
            0 <= cpu_id < NUM_CPUS ==> ret.view().spec_index(cpu_id as int).submap_of(tlbmap_4k.view().spec_index(cpu_id as int)),
{
    let mut cpu_id = 0;
    let mut ret_map = tlbmap_4k;

    // broadcast use map_equal_implies_submap_each_other;

    assert(forall|cpu_id: CpuId|
        #![auto]
        0 <= cpu_id < NUM_CPUS ==> ret_map.view().spec_index(cpu_id as int) =~= tlbmap_4k.view().spec_index(cpu_id as int));
    assert(forall|cpu_id: CpuId|
        #![auto]
        0 <= cpu_id < NUM_CPUS ==> ret_map.view().spec_index(cpu_id as int).submap_of(tlbmap_4k.view().spec_index(cpu_id as int)));

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
                #![auto]
                0 <= cpu_i < NUM_CPUS ==> ret_map.view().spec_index(cpu_i as int).submap_of(tlbmap_4k.view().spec_index(cpu_i as int)),
    {
        proof {
            assert(cpu_id < ret_map.view().len());
            let old_at_i = ret_map.view().spec_index(cpu_id as int);
            let tlbmap = old_at_i.remove(va.view());
            assert(!tlbmap.contains_key(va.view()));
            // tlbmap is a submap of old_at_i, which (by loop invariant) is a submap of tlbmap_4k[cpu_id]
            assert(tlbmap.submap_of(old_at_i));
            assert(old_at_i.submap_of(tlbmap_4k.view().spec_index(cpu_id as int)));
            assert(tlbmap.submap_of(tlbmap_4k.view().spec_index(cpu_id as int))) by {
                broadcast use crate::lemma::lemma_u::submap_by_transitivity;
            }
            let tlbseq = ret_map.view().update(cpu_id as int, tlbmap);
            assert(tlbseq.index(cpu_id as int) =~= tlbmap);
            *ret_map.borrow_mut() = tlbseq;
            // After update, ret_map@[cpu_id] = tlbmap, all others unchanged.
            assert(!ret_map.view().spec_index(cpu_id as int).contains_key(va.view()));
            assert forall|cpu_i: CpuId| 0 <= cpu_i < NUM_CPUS implies
                #[trigger] ret_map.view().spec_index(cpu_i as int).submap_of(tlbmap_4k.view().spec_index(cpu_i as int)) by {
                if cpu_i as int == cpu_id as int {
                    assert(ret_map.view().spec_index(cpu_i as int) == tlbmap);
                } else {
                    // unchanged
                }
            }
        }
    }
    ret_map
}

} // verus!
