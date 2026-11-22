use vstd::prelude::*;
use crate::*;

verus! {
/// IPC hand-off detach of the B/D/F `(bus, device, function)` of the PCI function array `pci` of the owner of the write-held
/// IOMMU table `iommu_table_ptr`, under the held root-table lock; owners stay. An absent entry is never cached: nothing else
/// changes. A present non-anchor entry invalidates its DID. A present anchor entry (`pci_bdf_did(bus, device, function)` is its
/// DID) re-anchors the table at the first other function `ret` of `pci` attached in that DID, moving every such function of
/// `pci` to `pci_bdf_did(ret)`; with none left the table loses its DID. Every path that cleared a present entry ends with an
/// invalidation of the old DID.
pub fn iommu_root_table_detach_owned(
    irt: &mut IommuRootTableLock, iommu_tlb: &mut IommuTLB, iommu_table_map: &mut IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot,
    pci: &PciFunctionArray, bus: usize, device: usize, function: usize, Ghost(k): Ghost<KernelK>, Tracked(lctx): Tracked<&LocalContext>,
    Tracked(irt_lock_perm): Tracked<&LockPerm>, Tracked(iommu_table_lock_perm): Tracked<&LockPerm>,
) -> (ret: Option<PciBdf>)
    requires
        iommu_table_perms_wf(k.it_mp),
        old(irt).inv(),
        old(iommu_tlb).inv(),
        pci.wf(),
        pci_bdf_valid(bus, device, function),
        iommu_root_table_typed_lock_map_aligned(*old(irt), lctx.iommu_root_table_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.iommu_root_table_lock_map(), old(irt).view().table_base(), TypedLockMode::Write),
        irt_lock_perm.state() is WriteLock,
        irt_lock_perm.thread_id() == lctx.thread_id(),
        irt_lock_perm.lock_id() == old(irt).locking_thread()->Write_lock_id,
        iommu_table_perms_wf(*old(iommu_table_map)),
        old(iommu_table_map).dom().contains(iommu_table_ptr),
        old(iommu_table_map).typed_lock_map_aligned(lctx.iommu_table_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write),
        iommu_table_lock_perm.state() is WriteLock,
        iommu_table_lock_perm.thread_id() == lctx.thread_id(),
        iommu_table_lock_perm.lock_id() == old(iommu_table_map).spec_index(iommu_table_ptr).locking_thread()->Write_lock_id,
        page_ptr_valid(old(iommu_table_map).spec_index(iommu_table_ptr).view().cr3),
    ensures
        final(irt).inv(),
        iommu_root_table_typed_lock_map_aligned(*final(irt), lctx.iommu_root_table_lock_map(), lctx.thread_id()),
        final(irt).locking_thread() == old(irt).locking_thread(),
        final(irt).view().table_base() == old(irt).view().table_base(),
        final(irt).view().owners() == old(irt).view().owners(),
        forall|b: usize, d: usize, f: usize| #![trigger final(irt).view().spec_index_iommu_root(b, d, f)] #![trigger final(irt).view().spec_index_iommu_did(b, d, f)]
            pci_bdf_valid(b, d, f) ==> {
            let moved = ret is Some && (b, d, f) != (bus, device, function) && pci.view().dom().contains((b, d, f))
                && old(irt).view().spec_index_iommu_did(b, d, f) == old(irt).view().spec_index_iommu_did(bus, device, function);
            &&& final(irt).view().spec_index_iommu_root(b, d, f) == if (b, d, f) == (bus, device, function) { None }
                else if moved { Some(old(iommu_table_map).spec_index(iommu_table_ptr).view().cr3) } else { old(irt).view().spec_index_iommu_root(b, d, f) }
            &&& final(irt).view().spec_index_iommu_did(b, d, f) == if (b, d, f) == (bus, device, function) { None }
                else if moved { Some(pci_bdf_did(ret.unwrap().0, ret.unwrap().1, ret.unwrap().2)) } else { old(irt).view().spec_index_iommu_did(b, d, f) }
        },
        ret matches Some(anchor) ==> {
            &&& old(irt).view().spec_index_iommu_did(bus, device, function) == Some(pci_bdf_did(bus, device, function))
            &&& pci_bdf_valid(anchor.0, anchor.1, anchor.2)
            &&& anchor != (bus, device, function)
            &&& pci.view().dom().contains(anchor)
            &&& old(irt).view().spec_index_iommu_did(anchor.0, anchor.1, anchor.2) == Some(pci_bdf_did(bus, device, function))
            &&& forall|b: usize, d: usize, f: usize| #![trigger old(irt).view().spec_index_iommu_did(b, d, f)]
                pci_bdf_valid(b, d, f) && (b, d, f) != (bus, device, function) && pci.view().dom().contains((b, d, f))
                    && old(irt).view().spec_index_iommu_did(b, d, f) == Some(pci_bdf_did(bus, device, function)) ==> !pci_bdf_lt((b, d, f), anchor)
        },
        ret is None && old(irt).view().spec_index_iommu_did(bus, device, function) == Some(pci_bdf_did(bus, device, function)) ==> forall|b: usize, d: usize, f: usize|
            #![trigger old(irt).view().spec_index_iommu_did(b, d, f)]
            pci_bdf_valid(b, d, f) && (b, d, f) != (bus, device, function) && pci.view().dom().contains((b, d, f))
                ==> old(irt).view().spec_index_iommu_did(b, d, f) != Some(pci_bdf_did(bus, device, function)),
        iommu_table_perms_wf(*final(iommu_table_map)),
        final(iommu_table_map).unchanged_except(old(iommu_table_map), iommu_table_ptr),
        final(iommu_table_map).typed_lock_map_aligned(lctx.iommu_table_lock_map(), lctx.thread_id()),
        final(iommu_table_map).lock_id_by_key(iommu_table_ptr) == old(iommu_table_map).lock_id_by_key(iommu_table_ptr),
        final(iommu_table_map).spec_index(iommu_table_ptr).locking_thread() == old(iommu_table_map).spec_index(iommu_table_ptr).locking_thread(),
        final(iommu_table_map).spec_index(iommu_table_ptr).being_killed() == old(iommu_table_map).spec_index(iommu_table_ptr).being_killed(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view()
            == (IommuTable { did: final(iommu_table_map).spec_index(iommu_table_ptr).view().did, ..old(iommu_table_map).spec_index(iommu_table_ptr).view() }),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().did == if ret is Some { Some(pci_bdf_did(ret.unwrap().0, ret.unwrap().1, ret.unwrap().2)) }
            else if old(irt).view().spec_index_iommu_did(bus, device, function) == Some(pci_bdf_did(bus, device, function)) { None }
            else { old(iommu_table_map).spec_index(iommu_table_ptr).view().did },
        final(iommu_tlb).inv(),
        old(irt).view().spec_index_iommu_did(bus, device, function) matches Some(did) ==> {
            &&& final(iommu_tlb).view() == old(iommu_tlb).view().insert(did, final(iommu_tlb).spec_index(did))
            &&& iommu_tlb_within_may_cache(KernelK { irt: *final(irt), ..k }, did, final(iommu_tlb).spec_index(did))
            &&& final(iommu_tlb).structure_caches() == old(iommu_tlb).structure_caches().insert(did, final(iommu_tlb).structure_cache(did))
            &&& iommu_structure_cache_within_may_cache(KernelK { irt: *final(irt), ..k }, did, final(iommu_tlb).structure_cache(did))
            &&& Map::new(final(iommu_tlb).context_cache().dom().filter(|bdf: PciBdf| final(iommu_tlb).context_cache()[bdf].1 != did), |bdf: PciBdf| final(iommu_tlb).context_cache()[bdf])
                == Map::new(old(iommu_tlb).context_cache().dom().filter(|bdf: PciBdf| old(iommu_tlb).context_cache()[bdf].1 != did), |bdf: PciBdf| old(iommu_tlb).context_cache()[bdf])
            &&& forall|bdf: PciBdf| #![trigger final(iommu_tlb).context_cache().dom().contains(bdf)] final(iommu_tlb).context_cache().dom().contains(bdf) && final(iommu_tlb).context_cache()[bdf].1 == did
                ==> iommu_context_cache_entry_present(KernelK { irt: *final(irt), ..k }, bdf, final(iommu_tlb).context_cache()[bdf])
        },
        old(irt).view().spec_index_iommu_did(bus, device, function) is None ==> final(iommu_tlb).view() == old(iommu_tlb).view() && final(iommu_tlb).context_cache() == old(iommu_tlb).context_cache()
            && final(iommu_tlb).structure_caches() == old(iommu_tlb).structure_caches(),
{
    assert(irt.wlocked_by(lctx)) by { reveal(iommu_root_table_typed_lock_map_aligned); };
    assert(iommu_table_map.perms_wf() && iommu_table_map.spec_index(iommu_table_ptr).is_init()) by { iommu_table_perms_wf_map(*iommu_table_map); iommu_table_perms_wf_at(*iommu_table_map, iommu_table_ptr); };
    let iommu_table = iommu_table_map.borrow_typed(iommu_table_ptr, Ghost(lctx.iommu_table_lock_map()), Tracked(lctx), Tracked(iommu_table_lock_perm));
    let root = iommu_table.cr3;
    let old_did = irt.borrow(Tracked(irt_lock_perm)).iommu_did(bus, device, function);
    match old_did {
        None => {
            assert(irt.view().spec_index_iommu_root(bus, device, function) is None) by { irt.view().wf_context_entry_at(bus, device, function); };
            None
        },
        Some(did) => {
            let anchored = IommuRootTable::pci_bdf_slot(bus, device, function) == did;
            let new_anchor = if anchored { irt.borrow(Tracked(irt_lock_perm)).first_attached_in_did(pci, did, (bus, device, function)) } else { None };
            irt.borrow_mut(Tracked(lctx), Tracked(irt_lock_perm)).detach(bus, device, function);
            proof { assert(iommu_root_table_typed_lock_map_aligned(*irt, lctx.iommu_root_table_lock_map(), lctx.thread_id())) by { reveal(iommu_root_table_typed_lock_map_aligned); }; }
            match new_anchor {
                Some(anchor) => {
                    let new_did = IommuRootTable::pci_bdf_slot(anchor.0, anchor.1, anchor.2);
                    iommu_root_table_migrate_did(irt, iommu_tlb, pci, root, did, new_did, Ghost(k), Tracked(lctx), Tracked(irt_lock_perm));
                    iommu_table_map_set_did(iommu_table_map, iommu_table_ptr, Some(new_did), Tracked(lctx), Tracked(iommu_table_lock_perm));
                },
                None => {
                    iommu_tlb.invalidate_domain(did, Ghost(KernelK { irt: *irt, iommu_tlb: *iommu_tlb, ..k }), Tracked(lctx));
                    if anchored { iommu_table_map_set_did(iommu_table_map, iommu_table_ptr, None, Tracked(lctx), Tracked(iommu_table_lock_perm)); }
                },
            }
            new_anchor
        },
    }
}

/// Moves every present context entry of a function of `pci` in domain `old_did` to domain `new_did` at `root`, under the held
/// root-table lock. `old_did` is invalidated first; each entry is then cleared, `old_did` invalidated, and the entry
/// republished in `new_did`. A last invalidation drops whatever a not-yet-moved entry cached meanwhile, so no `old_did`
/// context or IOTLB entry of a moved function survives.
fn iommu_root_table_migrate_did(
    irt: &mut IommuRootTableLock, iommu_tlb: &mut IommuTLB, pci: &PciFunctionArray, root: PageTableRoot, old_did: VtdDomainId, new_did: VtdDomainId,
    Ghost(k): Ghost<KernelK>, Tracked(lctx): Tracked<&LocalContext>, Tracked(irt_lock_perm): Tracked<&LockPerm>,
)
    requires
        iommu_table_perms_wf(k.it_mp),
        old(irt).inv(),
        old(iommu_tlb).inv(),
        pci.wf(),
        page_ptr_valid(root),
        vtd_domain_id_valid(old_did),
        vtd_domain_id_valid(new_did),
        iommu_root_table_typed_lock_map_aligned(*old(irt), lctx.iommu_root_table_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.iommu_root_table_lock_map(), old(irt).view().table_base(), TypedLockMode::Write),
        irt_lock_perm.state() is WriteLock,
        irt_lock_perm.thread_id() == lctx.thread_id(),
        irt_lock_perm.lock_id() == old(irt).locking_thread()->Write_lock_id,
    ensures
        final(irt).inv(),
        iommu_root_table_typed_lock_map_aligned(*final(irt), lctx.iommu_root_table_lock_map(), lctx.thread_id()),
        final(irt).locking_thread() == old(irt).locking_thread(),
        final(irt).view().table_base() == old(irt).view().table_base(),
        final(irt).view().owners() == old(irt).view().owners(),
        forall|b: usize, d: usize, f: usize| #![trigger final(irt).view().spec_index_iommu_root(b, d, f)] #![trigger final(irt).view().spec_index_iommu_did(b, d, f)]
            pci_bdf_valid(b, d, f) ==> {
            let moved = pci.view().dom().contains((b, d, f)) && old(irt).view().spec_index_iommu_did(b, d, f) == Some(old_did);
            &&& final(irt).view().spec_index_iommu_root(b, d, f) == if moved { Some(root) } else { old(irt).view().spec_index_iommu_root(b, d, f) }
            &&& final(irt).view().spec_index_iommu_did(b, d, f) == if moved { Some(new_did) } else { old(irt).view().spec_index_iommu_did(b, d, f) }
        },
        final(iommu_tlb).inv(),
        final(iommu_tlb).view() == old(iommu_tlb).view().insert(old_did, final(iommu_tlb).spec_index(old_did)),
        iommu_tlb_within_may_cache(KernelK { irt: *final(irt), ..k }, old_did, final(iommu_tlb).spec_index(old_did)),
        final(iommu_tlb).structure_caches() == old(iommu_tlb).structure_caches().insert(old_did, final(iommu_tlb).structure_cache(old_did)),
        iommu_structure_cache_within_may_cache(KernelK { irt: *final(irt), ..k }, old_did, final(iommu_tlb).structure_cache(old_did)),
        Map::new(final(iommu_tlb).context_cache().dom().filter(|bdf: PciBdf| final(iommu_tlb).context_cache()[bdf].1 != old_did), |bdf: PciBdf| final(iommu_tlb).context_cache()[bdf])
            == Map::new(old(iommu_tlb).context_cache().dom().filter(|bdf: PciBdf| old(iommu_tlb).context_cache()[bdf].1 != old_did), |bdf: PciBdf| old(iommu_tlb).context_cache()[bdf]),
        forall|bdf: PciBdf| #![trigger final(iommu_tlb).context_cache().dom().contains(bdf)] final(iommu_tlb).context_cache().dom().contains(bdf) && final(iommu_tlb).context_cache()[bdf].1 == old_did
            ==> iommu_context_cache_entry_present(KernelK { irt: *final(irt), ..k }, bdf, final(iommu_tlb).context_cache()[bdf]),
{
    broadcast use PciFunctionArray::wf_function_at, PciFunctionArray::wf_entry_at;
    assert(irt.wlocked_by(lctx)) by { reveal(iommu_root_table_typed_lock_map_aligned); };
    iommu_tlb.invalidate_domain(old_did, Ghost(KernelK { irt: *irt, iommu_tlb: *iommu_tlb, ..k }), Tracked(lctx));
    let mut i: usize = 0;
    while i < PCI_FUNCTIONS_PER_PROCESS
        invariant
            iommu_table_perms_wf(k.it_mp),
            irt.inv(),
            irt.wlocked_by(lctx),
            irt.locking_thread() == old(irt).locking_thread(),
            irt.view().table_base() == old(irt).view().table_base(),
            irt.view().owners() == old(irt).view().owners(),
            iommu_tlb.inv(),
            iommu_tlb.view() =~= old(iommu_tlb).view().insert(old_did, iommu_tlb.spec_index(old_did)),
            iommu_tlb.structure_caches() =~= old(iommu_tlb).structure_caches().insert(old_did, iommu_tlb.structure_cache(old_did)),
            Map::new(iommu_tlb.context_cache().dom().filter(|bdf: PciBdf| iommu_tlb.context_cache()[bdf].1 != old_did), |bdf: PciBdf| iommu_tlb.context_cache()[bdf])
                == Map::new(old(iommu_tlb).context_cache().dom().filter(|bdf: PciBdf| old(iommu_tlb).context_cache()[bdf].1 != old_did), |bdf: PciBdf| old(iommu_tlb).context_cache()[bdf]),
            pci.wf(),
            page_ptr_valid(root),
            vtd_domain_id_valid(old_did),
            vtd_domain_id_valid(new_did),
            typed_lock_map_contains_mode(lctx.iommu_root_table_lock_map(), old(irt).view().table_base(), TypedLockMode::Write),
            irt_lock_perm.state() is WriteLock,
            irt_lock_perm.thread_id() == lctx.thread_id(),
            irt_lock_perm.lock_id() == old(irt).locking_thread()->Write_lock_id,
            i <= PCI_FUNCTIONS_PER_PROCESS,
            forall|b: usize, d: usize, f: usize| #![trigger irt.view().spec_index_iommu_root(b, d, f)] #![trigger irt.view().spec_index_iommu_did(b, d, f)] pci_bdf_valid(b, d, f) ==> {
                let moved = pci.view().dom().contains((b, d, f)) && pci.index_of((b, d, f)) < i && old(irt).view().spec_index_iommu_did(b, d, f) == Some(old_did);
                &&& irt.view().spec_index_iommu_root(b, d, f) == if moved { Some(root) } else { old(irt).view().spec_index_iommu_root(b, d, f) }
                &&& irt.view().spec_index_iommu_did(b, d, f) == if moved { Some(new_did) } else { old(irt).view().spec_index_iommu_did(b, d, f) }
            },
        decreases PCI_FUNCTIONS_PER_PROCESS - i,
    {
        broadcast use PciFunctionArray::wf_function_at, PciFunctionArray::wf_entry_at;
        let entry = pci.entry(i);
        if entry.used {
            let (bus, device, function) = entry.bdf;
            proof { pci.wf_entry_at(i as int); pci.wf_function_at(entry.bdf); }
            let current_did = irt.borrow(Tracked(irt_lock_perm)).iommu_did(bus, device, function);
            if current_did.is_some() && current_did.unwrap() == old_did {
                irt.borrow_mut(Tracked(lctx), Tracked(irt_lock_perm)).detach(bus, device, function);
                iommu_tlb.invalidate_domain(old_did, Ghost(KernelK { irt: *irt, iommu_tlb: *iommu_tlb, ..k }), Tracked(lctx));
                irt.borrow_mut(Tracked(lctx), Tracked(irt_lock_perm)).attach(bus, device, function, root, new_did);
            }
        }
        i = i + 1;
    }
    iommu_tlb.invalidate_domain(old_did, Ghost(KernelK { irt: *irt, iommu_tlb: *iommu_tlb, ..k }), Tracked(lctx));
    proof { assert(iommu_root_table_typed_lock_map_aligned(*irt, lctx.iommu_root_table_lock_map(), lctx.thread_id())) by { reveal(iommu_root_table_typed_lock_map_aligned); }; }
}

/// Detaches one B/D/F under the held root-table lock; its owner is untouched. If the entry was present, drops every cached
/// context entry tagged with its old DID and flushes that DID's IOTLB domain; an absent entry is never cached.
pub fn iommu_root_table_detach(
    irt: &mut IommuRootTableLock, iommu_tlb: &mut IommuTLB, bus: usize, device: usize, function: usize, Ghost(k): Ghost<KernelK>,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(irt_lock_perm): Tracked<&LockPerm>,
)
    requires
        iommu_table_perms_wf(k.it_mp),
        old(irt).inv(),
        old(iommu_tlb).inv(),
        pci_bdf_valid(bus, device, function),
        iommu_root_table_typed_lock_map_aligned(*old(irt), lctx.iommu_root_table_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.iommu_root_table_lock_map(), old(irt).view().table_base(), TypedLockMode::Write),
        irt_lock_perm.state() is WriteLock,
        irt_lock_perm.thread_id() == lctx.thread_id(),
        irt_lock_perm.lock_id() == old(irt).locking_thread()->Write_lock_id,
    ensures
        final(irt).inv(),
        iommu_root_table_typed_lock_map_aligned(*final(irt), lctx.iommu_root_table_lock_map(), lctx.thread_id()),
        final(irt).locking_thread() == old(irt).locking_thread(),
        final(irt).view().table_base() == old(irt).view().table_base(),
        final(irt).view().owners() == old(irt).view().owners(),
        final(irt).view().iommu_roots() == seq3_update(old(irt).view().iommu_roots(), bus as int, device as int, function as int, None),
        final(irt).view().iommu_dids() == seq3_update(old(irt).view().iommu_dids(), bus as int, device as int, function as int, None),
        final(iommu_tlb).inv(),
        old(irt).view().spec_index_iommu_did(bus, device, function) matches Some(did) ==> {
            &&& final(iommu_tlb).view() == old(iommu_tlb).view().insert(did, final(iommu_tlb).spec_index(did))
            &&& iommu_tlb_within_may_cache(KernelK { irt: *final(irt), ..k }, did, final(iommu_tlb).spec_index(did))
            &&& final(iommu_tlb).structure_caches() == old(iommu_tlb).structure_caches().insert(did, final(iommu_tlb).structure_cache(did))
            &&& iommu_structure_cache_within_may_cache(KernelK { irt: *final(irt), ..k }, did, final(iommu_tlb).structure_cache(did))
            &&& Map::new(final(iommu_tlb).context_cache().dom().filter(|bdf: PciBdf| final(iommu_tlb).context_cache()[bdf].1 != did), |bdf: PciBdf| final(iommu_tlb).context_cache()[bdf])
                == Map::new(old(iommu_tlb).context_cache().dom().filter(|bdf: PciBdf| old(iommu_tlb).context_cache()[bdf].1 != did), |bdf: PciBdf| old(iommu_tlb).context_cache()[bdf])
            &&& forall|bdf: PciBdf| #![trigger final(iommu_tlb).context_cache().dom().contains(bdf)] final(iommu_tlb).context_cache().dom().contains(bdf) && final(iommu_tlb).context_cache()[bdf].1 == did
                ==> iommu_context_cache_entry_present(KernelK { irt: *final(irt), ..k }, bdf, final(iommu_tlb).context_cache()[bdf])
        },
        old(irt).view().spec_index_iommu_did(bus, device, function) is None ==> final(iommu_tlb).view() == old(iommu_tlb).view() && final(iommu_tlb).context_cache() == old(iommu_tlb).context_cache()
            && final(iommu_tlb).structure_caches() == old(iommu_tlb).structure_caches(),
{
    assert(irt.wlocked_by(lctx)) by { reveal(iommu_root_table_typed_lock_map_aligned); };
    let table = irt.borrow_mut(Tracked(lctx), Tracked(irt_lock_perm));
    let old_did = table.iommu_did(bus, device, function);
    table.detach(bus, device, function);
    if let Some(did) = old_did { iommu_tlb.invalidate_domain(did, Ghost(KernelK { irt: *irt, iommu_tlb: *iommu_tlb, ..k }), Tracked(lctx)); }
    proof { assert(iommu_root_table_typed_lock_map_aligned(*irt, lctx.iommu_root_table_lock_map(), lctx.thread_id())) by { reveal(iommu_root_table_typed_lock_map_aligned); }; }
}

/// Points one absent B/D/F context entry at the root of the write-held IOMMU table `iommu_table_ptr` under the held root-table
/// lock and returns the DID it carries: the table's DID, or, for a table without one, the B/D/F's candidate DID, which the table
/// then takes and which the B/D/F anchors. Needs no invalidation: a not-present entry is never cached (`CAP.CM = 0`).
pub fn iommu_root_table_attach(
    irt: &mut IommuRootTableLock, iommu_table_map: &mut IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot, bus: usize, device: usize, function: usize,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(irt_lock_perm): Tracked<&LockPerm>, Tracked(iommu_table_lock_perm): Tracked<&LockPerm>,
) -> (did: VtdDomainId)
    requires
        old(irt).inv(),
        pci_bdf_valid(bus, device, function),
        old(irt).view().spec_index_iommu_root(bus, device, function) is None,
        old(irt).view().spec_index_owner(bus, device, function) == Some(old(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr),
        page_ptr_valid(old(iommu_table_map).spec_index(iommu_table_ptr).view().cr3),
        iommu_root_table_typed_lock_map_aligned(*old(irt), lctx.iommu_root_table_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.iommu_root_table_lock_map(), old(irt).view().table_base(), TypedLockMode::Write),
        irt_lock_perm.state() is WriteLock,
        irt_lock_perm.thread_id() == lctx.thread_id(),
        irt_lock_perm.lock_id() == old(irt).locking_thread()->Write_lock_id,
        iommu_table_perms_wf(*old(iommu_table_map)),
        old(iommu_table_map).dom().contains(iommu_table_ptr),
        old(iommu_table_map).typed_lock_map_aligned(lctx.iommu_table_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write),
        iommu_table_lock_perm.state() is WriteLock,
        iommu_table_lock_perm.thread_id() == lctx.thread_id(),
        iommu_table_lock_perm.lock_id() == old(iommu_table_map).spec_index(iommu_table_ptr).locking_thread()->Write_lock_id,
    ensures
        vtd_domain_id_valid(did),
        did == if old(iommu_table_map).spec_index(iommu_table_ptr).view().did is Some { old(iommu_table_map).spec_index(iommu_table_ptr).view().did.unwrap() }
            else { pci_bdf_did(bus, device, function) },
        final(irt).inv(),
        iommu_root_table_typed_lock_map_aligned(*final(irt), lctx.iommu_root_table_lock_map(), lctx.thread_id()),
        final(irt).locking_thread() == old(irt).locking_thread(),
        final(irt).view().table_base() == old(irt).view().table_base(),
        final(irt).view().owners() == old(irt).view().owners(),
        final(irt).view().iommu_roots() == seq3_update(old(irt).view().iommu_roots(), bus as int, device as int, function as int, Some(old(iommu_table_map).spec_index(iommu_table_ptr).view().cr3)),
        final(irt).view().iommu_dids() == seq3_update(old(irt).view().iommu_dids(), bus as int, device as int, function as int, Some(did)),
        iommu_table_perms_wf(*final(iommu_table_map)),
        final(iommu_table_map).unchanged_except(old(iommu_table_map), iommu_table_ptr),
        final(iommu_table_map).typed_lock_map_aligned(lctx.iommu_table_lock_map(), lctx.thread_id()),
        final(iommu_table_map).lock_id_by_key(iommu_table_ptr) == old(iommu_table_map).lock_id_by_key(iommu_table_ptr),
        final(iommu_table_map).spec_index(iommu_table_ptr).locking_thread() == old(iommu_table_map).spec_index(iommu_table_ptr).locking_thread(),
        final(iommu_table_map).spec_index(iommu_table_ptr).being_killed() == old(iommu_table_map).spec_index(iommu_table_ptr).being_killed(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view() == (IommuTable { did: Some(did), ..old(iommu_table_map).spec_index(iommu_table_ptr).view() }),
{
    assert(irt.wlocked_by(lctx)) by { reveal(iommu_root_table_typed_lock_map_aligned); };
    assert(iommu_table_map.perms_wf() && iommu_table_map.spec_index(iommu_table_ptr).is_init() && iommu_table_map.spec_index(iommu_table_ptr).view().inv()) by {
        iommu_table_perms_wf_map(*iommu_table_map); iommu_table_perms_wf_at(*iommu_table_map, iommu_table_ptr);
    };
    let iommu_table = iommu_table_map.borrow_typed(iommu_table_ptr, Ghost(lctx.iommu_table_lock_map()), Tracked(lctx), Tracked(iommu_table_lock_perm));
    let root = iommu_table.cr3;
    let did = match iommu_table.did {
        Some(did) => did,
        None => {
            let did = IommuRootTable::pci_bdf_slot(bus, device, function);
            iommu_table_map_set_did(iommu_table_map, iommu_table_ptr, Some(did), Tracked(lctx), Tracked(iommu_table_lock_perm));
            did
        },
    };
    irt.borrow_mut(Tracked(lctx), Tracked(irt_lock_perm)).attach(bus, device, function, root, did);
    proof { assert(iommu_root_table_typed_lock_map_aligned(*irt, lctx.iommu_root_table_lock_map(), lctx.thread_id())) by { reveal(iommu_root_table_typed_lock_map_aligned); }; }
    did
}

/// Kill and exit reclaim of the write-held IOMMU table `iommu_table_ptr` under the held root-table lock: clears the context entry
/// of every function of its owner's PCI function array `pci`, owners untouched, then invalidates the table's DID once and drops
/// it. A table without a DID invalidates nothing.
pub fn iommu_root_table_detach_array(
    irt: &mut IommuRootTableLock, iommu_tlb: &mut IommuTLB, iommu_table_map: &mut IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot,
    pci: &PciFunctionArray, Ghost(k): Ghost<KernelK>, Tracked(lctx): Tracked<&LocalContext>, Tracked(irt_lock_perm): Tracked<&LockPerm>, Tracked(iommu_table_lock_perm): Tracked<&LockPerm>,
)
    requires
        iommu_table_perms_wf(k.it_mp),
        old(irt).inv(),
        old(iommu_tlb).inv(),
        pci.wf(),
        iommu_root_table_typed_lock_map_aligned(*old(irt), lctx.iommu_root_table_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.iommu_root_table_lock_map(), old(irt).view().table_base(), TypedLockMode::Write),
        irt_lock_perm.state() is WriteLock,
        irt_lock_perm.thread_id() == lctx.thread_id(),
        irt_lock_perm.lock_id() == old(irt).locking_thread()->Write_lock_id,
        iommu_table_perms_wf(*old(iommu_table_map)),
        old(iommu_table_map).dom().contains(iommu_table_ptr),
        old(iommu_table_map).typed_lock_map_aligned(lctx.iommu_table_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write),
        iommu_table_lock_perm.state() is WriteLock,
        iommu_table_lock_perm.thread_id() == lctx.thread_id(),
        iommu_table_lock_perm.lock_id() == old(iommu_table_map).spec_index(iommu_table_ptr).locking_thread()->Write_lock_id,
    ensures
        final(irt).inv(),
        iommu_root_table_typed_lock_map_aligned(*final(irt), lctx.iommu_root_table_lock_map(), lctx.thread_id()),
        final(irt).locking_thread() == old(irt).locking_thread(),
        final(irt).view().table_base() == old(irt).view().table_base(),
        final(irt).view().owners() == old(irt).view().owners(),
        forall|b: usize, d: usize, f: usize| #![trigger final(irt).view().spec_index_iommu_root(b, d, f)] #![trigger final(irt).view().spec_index_iommu_did(b, d, f)]
            pci_bdf_valid(b, d, f) ==> {
            let owned = pci.view().dom().contains((b, d, f));
            &&& final(irt).view().spec_index_iommu_root(b, d, f) == if owned { None } else { old(irt).view().spec_index_iommu_root(b, d, f) }
            &&& final(irt).view().spec_index_iommu_did(b, d, f) == if owned { None } else { old(irt).view().spec_index_iommu_did(b, d, f) }
        },
        forall|b: usize, d: usize, f: usize| #![trigger final(irt).view().spec_index_iommu_root(b, d, f)]
            pci.view().dom().contains((b, d, f)) ==> final(irt).view().spec_index_iommu_root(b, d, f) is None,
        iommu_table_perms_wf(*final(iommu_table_map)),
        final(iommu_table_map).unchanged_except(old(iommu_table_map), iommu_table_ptr),
        final(iommu_table_map).typed_lock_map_aligned(lctx.iommu_table_lock_map(), lctx.thread_id()),
        final(iommu_table_map).lock_id_by_key(iommu_table_ptr) == old(iommu_table_map).lock_id_by_key(iommu_table_ptr),
        final(iommu_table_map).spec_index(iommu_table_ptr).locking_thread() == old(iommu_table_map).spec_index(iommu_table_ptr).locking_thread(),
        final(iommu_table_map).spec_index(iommu_table_ptr).being_killed() == old(iommu_table_map).spec_index(iommu_table_ptr).being_killed(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view() == (IommuTable { did: None, ..old(iommu_table_map).spec_index(iommu_table_ptr).view() }),
        final(iommu_tlb).inv(),
        old(iommu_table_map).spec_index(iommu_table_ptr).view().did matches Some(did) ==> {
            &&& final(iommu_tlb).view() == old(iommu_tlb).view().insert(did, final(iommu_tlb).spec_index(did))
            &&& iommu_tlb_within_may_cache(KernelK { irt: *final(irt), ..k }, did, final(iommu_tlb).spec_index(did))
            &&& final(iommu_tlb).structure_caches() == old(iommu_tlb).structure_caches().insert(did, final(iommu_tlb).structure_cache(did))
            &&& iommu_structure_cache_within_may_cache(KernelK { irt: *final(irt), ..k }, did, final(iommu_tlb).structure_cache(did))
            &&& Map::new(final(iommu_tlb).context_cache().dom().filter(|bdf: PciBdf| final(iommu_tlb).context_cache()[bdf].1 != did), |bdf: PciBdf| final(iommu_tlb).context_cache()[bdf])
                == Map::new(old(iommu_tlb).context_cache().dom().filter(|bdf: PciBdf| old(iommu_tlb).context_cache()[bdf].1 != did), |bdf: PciBdf| old(iommu_tlb).context_cache()[bdf])
            &&& forall|bdf: PciBdf| #![trigger final(iommu_tlb).context_cache().dom().contains(bdf)] final(iommu_tlb).context_cache().dom().contains(bdf) && final(iommu_tlb).context_cache()[bdf].1 == did
                ==> iommu_context_cache_entry_present(KernelK { irt: *final(irt), ..k }, bdf, final(iommu_tlb).context_cache()[bdf])
        },
        old(iommu_table_map).spec_index(iommu_table_ptr).view().did is None ==> *final(iommu_tlb) == *old(iommu_tlb),
{
    broadcast use PciFunctionArray::wf_function_at;
    assert(irt.wlocked_by(lctx)) by { reveal(iommu_root_table_typed_lock_map_aligned); };
    assert(iommu_table_map.perms_wf() && iommu_table_map.spec_index(iommu_table_ptr).is_init() && iommu_table_map.spec_index(iommu_table_ptr).view().inv()) by {
        iommu_table_perms_wf_map(*iommu_table_map); iommu_table_perms_wf_at(*iommu_table_map, iommu_table_ptr);
    };
    let iommu_table = iommu_table_map.borrow_typed(iommu_table_ptr, Ghost(lctx.iommu_table_lock_map()), Tracked(lctx), Tracked(iommu_table_lock_perm));
    let old_did = iommu_table.did;
    irt.borrow_mut(Tracked(lctx), Tracked(irt_lock_perm)).detach_array(pci);
    if let Some(did) = old_did {
        iommu_tlb.invalidate_domain(did, Ghost(KernelK { irt: *irt, iommu_tlb: *iommu_tlb, ..k }), Tracked(lctx));
        iommu_table_map_set_did(iommu_table_map, iommu_table_ptr, None, Tracked(lctx), Tracked(iommu_table_lock_perm));
    }
    proof { assert(iommu_root_table_typed_lock_map_aligned(*irt, lctx.iommu_root_table_lock_map(), lctx.thread_id())) by { reveal(iommu_root_table_typed_lock_map_aligned); }; }
}
}
