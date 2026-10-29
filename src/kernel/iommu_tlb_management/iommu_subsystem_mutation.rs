use vstd::prelude::*;
use crate::*;

verus! {
/// IPC transfer of one B/D/F from the owner of the write-held IOMMU table `iommu_table_ptr` to `owner`, under the held root-table
/// lock. The entry is cleared and its slot handed to `owner`. An absent entry is never cached: nothing else changes. A present
/// non-anchor entry invalidates its DID. A present anchor entry (`pci_bdf_did(bus, device, function)` is its DID) re-anchors the
/// table at the first remaining attached B/D/F `ret` of the same owner and DID, moving every such entry to `pci_bdf_did(ret)`;
/// with none left the table loses its DID. Every path that cleared a present entry ends with an invalidation of the old DID.
pub fn iommu_root_table_reassign_detached(
    irt: &mut IommuRootTableLock, iommu_tlb: &mut IommuTLB, iommu_table_map: &mut IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot,
    bus: usize, device: usize, function: usize, owner: RwLockProcessPtr, Ghost(k): Ghost<KernelK>, Tracked(lctx): Tracked<&LocalContext>,
    Tracked(irt_lock_perm): Tracked<&LockPerm>, Tracked(iommu_table_lock_perm): Tracked<&LockPerm>,
) -> (ret: Option<PciBdf>)
    requires
        old(irt).inv(),
        old(iommu_tlb).inv(),
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
        final(irt).view().owners() == seq3_update(old(irt).view().owners(), bus as int, device as int, function as int, owner),
        forall|b: usize, d: usize, f: usize| #![trigger final(irt).view().spec_index_owner(b, d, f)] #![trigger final(irt).view().spec_index_iommu_root(b, d, f)]
            #![trigger final(irt).view().spec_index_iommu_did(b, d, f)] pci_bdf_valid(b, d, f) ==> {
            let moved = ret is Some && (b, d, f) != (bus, device, function) && old(irt).view().spec_index_owner(b, d, f) == old(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr
                && old(irt).view().spec_index_iommu_did(b, d, f) == old(irt).view().spec_index_iommu_did(bus, device, function);
            &&& final(irt).view().spec_index_owner(b, d, f) == if (b, d, f) == (bus, device, function) { owner } else { old(irt).view().spec_index_owner(b, d, f) }
            &&& final(irt).view().spec_index_iommu_root(b, d, f) == if (b, d, f) == (bus, device, function) { None }
                else if moved { Some(old(iommu_table_map).spec_index(iommu_table_ptr).view().cr3) } else { old(irt).view().spec_index_iommu_root(b, d, f) }
            &&& final(irt).view().spec_index_iommu_did(b, d, f) == if (b, d, f) == (bus, device, function) { None }
                else if moved { Some(pci_bdf_did(ret.unwrap().0, ret.unwrap().1, ret.unwrap().2)) } else { old(irt).view().spec_index_iommu_did(b, d, f) }
        },
        ret matches Some(anchor) ==> {
            &&& old(irt).view().spec_index_iommu_did(bus, device, function) == Some(pci_bdf_did(bus, device, function))
            &&& pci_bdf_valid(anchor.0, anchor.1, anchor.2)
            &&& anchor != (bus, device, function)
            &&& old(irt).view().spec_index_owner(anchor.0, anchor.1, anchor.2) == old(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr
            &&& old(irt).view().spec_index_iommu_did(anchor.0, anchor.1, anchor.2) == Some(pci_bdf_did(bus, device, function))
        },
        old(irt).view().spec_index_iommu_did(bus, device, function) == Some(pci_bdf_did(bus, device, function)) ==> forall|b: usize, d: usize, f: usize|
            #![trigger old(irt).view().spec_index_owner(b, d, f)] #![trigger old(irt).view().spec_index_iommu_did(b, d, f)]
            pci_bdf_valid(b, d, f) && (ret is None || pci_bdf_lt((b, d, f), ret.unwrap())) && (b, d, f) != (bus, device, function)
                && old(irt).view().spec_index_owner(b, d, f) == old(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr
                ==> old(irt).view().spec_index_iommu_did(b, d, f) != Some(pci_bdf_did(bus, device, function)),
        ret is Some ==> forall|b: usize, d: usize, f: usize| #![trigger old(irt).view().spec_index_iommu_did(b, d, f)]
            pci_bdf_valid(b, d, f) ==> (old(irt).view().spec_index_iommu_did(b, d, f) is Some) == (old(irt).view().spec_index_iommu_root(b, d, f) is Some),
        iommu_table_perms_wf(*final(iommu_table_map)),
        final(iommu_table_map).unchanged_except(old(iommu_table_map), iommu_table_ptr),
        final(iommu_table_map).typed_lock_map_aligned(lctx.iommu_table_lock_map(), lctx.thread_id()),
        final(iommu_table_map).lock_id_by_key(iommu_table_ptr) == old(iommu_table_map).lock_id_by_key(iommu_table_ptr),
        final(iommu_table_map).spec_index(iommu_table_ptr).locking_thread() == old(iommu_table_map).spec_index(iommu_table_ptr).locking_thread(),
        final(iommu_table_map).spec_index(iommu_table_ptr).being_killed() == old(iommu_table_map).spec_index(iommu_table_ptr).being_killed(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view()
            == (PageTable { did: final(iommu_table_map).spec_index(iommu_table_ptr).view().did, ..old(iommu_table_map).spec_index(iommu_table_ptr).view() }),
        final(iommu_table_map).spec_index(iommu_table_ptr).view().did == if ret is Some { Some(pci_bdf_did(ret.unwrap().0, ret.unwrap().1, ret.unwrap().2)) }
            else if old(irt).view().spec_index_iommu_did(bus, device, function) == Some(pci_bdf_did(bus, device, function)) { None }
            else { old(iommu_table_map).spec_index(iommu_table_ptr).view().did },
        final(iommu_tlb).inv(),
        old(irt).view().spec_index_iommu_did(bus, device, function) matches Some(did) ==> {
            &&& final(iommu_tlb).view() == old(iommu_tlb).view().insert(did, final(iommu_tlb).spec_index(did))
            &&& iommu_tlb_within_may_cache(KernelK { irt: *final(irt), ..k }, did, final(iommu_tlb).spec_index(did))
            &&& Map::new(final(iommu_tlb).context_cache().dom().filter(|bdf: PciBdf| final(iommu_tlb).context_cache()[bdf].1 != did), |bdf: PciBdf| final(iommu_tlb).context_cache()[bdf])
                == Map::new(old(iommu_tlb).context_cache().dom().filter(|bdf: PciBdf| old(iommu_tlb).context_cache()[bdf].1 != did), |bdf: PciBdf| old(iommu_tlb).context_cache()[bdf])
            &&& forall|bdf: PciBdf| #![trigger final(iommu_tlb).context_cache().dom().contains(bdf)] final(iommu_tlb).context_cache().dom().contains(bdf) && final(iommu_tlb).context_cache()[bdf].1 == did
                ==> iommu_context_cache_entry_present(KernelK { irt: *final(irt), ..k }, bdf, final(iommu_tlb).context_cache()[bdf])
        },
        old(irt).view().spec_index_iommu_did(bus, device, function) is None ==> final(iommu_tlb).view() == old(iommu_tlb).view() && final(iommu_tlb).context_cache() == old(iommu_tlb).context_cache(),
{
    assert(irt.wlocked_by(lctx)) by { reveal(iommu_root_table_typed_lock_map_aligned); };
    assert(iommu_table_map.perms_wf() && iommu_table_map.spec_index(iommu_table_ptr).is_init()) by { iommu_table_perms_wf_map(*iommu_table_map); iommu_table_perms_wf_at(*iommu_table_map, iommu_table_ptr); };
    let iommu_table = iommu_table_map.borrow_typed(iommu_table_ptr, Ghost(lctx.iommu_table_lock_map()), Tracked(lctx), Tracked(iommu_table_lock_perm));
    let sender = iommu_table.proc_ptr;
    let root = iommu_table.cr3;
    let old_did = irt.borrow(Tracked(irt_lock_perm)).iommu_did(bus, device, function);
    match old_did {
        None => {
            assert(irt.view().spec_index_iommu_root(bus, device, function) is None) by { irt.view().context_wf_at(bus, device, function); };
            irt.borrow_mut(Tracked(lctx), Tracked(irt_lock_perm)).set_owner(bus, device, function, owner);
            proof { assert(iommu_root_table_typed_lock_map_aligned(*irt, lctx.iommu_root_table_lock_map(), lctx.thread_id())) by { reveal(iommu_root_table_typed_lock_map_aligned); }; }
            None
        },
        Some(did) => {
            let anchored = IommuRootTable::pci_bdf_slot(bus, device, function) == did;
            let new_anchor = if anchored { irt.borrow(Tracked(irt_lock_perm)).first_attached_owned(sender, did, Some((bus, device, function))) } else { None };
            let table = irt.borrow_mut(Tracked(lctx), Tracked(irt_lock_perm));
            table.detach(bus, device, function);
            table.set_owner(bus, device, function, owner);
            proof { assert(iommu_root_table_typed_lock_map_aligned(*irt, lctx.iommu_root_table_lock_map(), lctx.thread_id())) by { reveal(iommu_root_table_typed_lock_map_aligned); }; }
            match new_anchor {
                Some(anchor) => {
                    let new_did = IommuRootTable::pci_bdf_slot(anchor.0, anchor.1, anchor.2);
                    iommu_root_table_migrate_did(irt, iommu_tlb, sender, root, did, new_did, Ghost(k), Tracked(lctx), Tracked(irt_lock_perm));
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

/// Moves every present context entry that `owner` owns in domain `old_did` to domain `new_did` at `root`, under the held root-table
/// lock. `old_did` is invalidated first; each entry is then cleared, `old_did` invalidated, and the entry republished in `new_did`.
/// A last invalidation drops whatever a not-yet-moved entry cached meanwhile, so no `old_did` context or IOTLB entry survives.
fn iommu_root_table_migrate_did(
    irt: &mut IommuRootTableLock, iommu_tlb: &mut IommuTLB, owner: RwLockProcessPtr, root: PageTableRoot, old_did: VtdDomainId, new_did: VtdDomainId,
    Ghost(k): Ghost<KernelK>, Tracked(lctx): Tracked<&LocalContext>, Tracked(irt_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(irt).inv(),
        old(iommu_tlb).inv(),
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
            let moved = old(irt).view().spec_index_owner(b, d, f) == owner && old(irt).view().spec_index_iommu_did(b, d, f) == Some(old_did);
            &&& final(irt).view().spec_index_iommu_root(b, d, f) == if moved { Some(root) } else { old(irt).view().spec_index_iommu_root(b, d, f) }
            &&& final(irt).view().spec_index_iommu_did(b, d, f) == if moved { Some(new_did) } else { old(irt).view().spec_index_iommu_did(b, d, f) }
        },
        final(iommu_tlb).inv(),
        final(iommu_tlb).view() == old(iommu_tlb).view().insert(old_did, final(iommu_tlb).spec_index(old_did)),
        iommu_tlb_within_may_cache(KernelK { irt: *final(irt), ..k }, old_did, final(iommu_tlb).spec_index(old_did)),
        Map::new(final(iommu_tlb).context_cache().dom().filter(|bdf: PciBdf| final(iommu_tlb).context_cache()[bdf].1 != old_did), |bdf: PciBdf| final(iommu_tlb).context_cache()[bdf])
            == Map::new(old(iommu_tlb).context_cache().dom().filter(|bdf: PciBdf| old(iommu_tlb).context_cache()[bdf].1 != old_did), |bdf: PciBdf| old(iommu_tlb).context_cache()[bdf]),
        forall|bdf: PciBdf| #![trigger final(iommu_tlb).context_cache().dom().contains(bdf)] final(iommu_tlb).context_cache().dom().contains(bdf) && final(iommu_tlb).context_cache()[bdf].1 == old_did
            ==> iommu_context_cache_entry_present(KernelK { irt: *final(irt), ..k }, bdf, final(iommu_tlb).context_cache()[bdf]),
{
    assert(irt.wlocked_by(lctx)) by { reveal(iommu_root_table_typed_lock_map_aligned); };
    iommu_tlb.invalidate_domain(old_did, Ghost(KernelK { irt: *irt, iommu_tlb: *iommu_tlb, ..k }), Tracked(lctx));
    let mut bus: usize = 0;
    let mut device: usize = 0;
    let mut function: usize = 0;
    while bus < PCI_BUS_COUNT
        invariant
            irt.inv(),
            irt.wlocked_by(lctx),
            irt.locking_thread() == old(irt).locking_thread(),
            irt.view().table_base() == old(irt).view().table_base(),
            irt.view().owners() == old(irt).view().owners(),
            iommu_tlb.inv(),
            iommu_tlb.view() =~= old(iommu_tlb).view().insert(old_did, iommu_tlb.spec_index(old_did)),
            Map::new(iommu_tlb.context_cache().dom().filter(|bdf: PciBdf| iommu_tlb.context_cache()[bdf].1 != old_did), |bdf: PciBdf| iommu_tlb.context_cache()[bdf])
                == Map::new(old(iommu_tlb).context_cache().dom().filter(|bdf: PciBdf| old(iommu_tlb).context_cache()[bdf].1 != old_did), |bdf: PciBdf| old(iommu_tlb).context_cache()[bdf]),
            page_ptr_valid(root),
            vtd_domain_id_valid(old_did),
            vtd_domain_id_valid(new_did),
            typed_lock_map_contains_mode(lctx.iommu_root_table_lock_map(), old(irt).view().table_base(), TypedLockMode::Write),
            irt_lock_perm.state() is WriteLock,
            irt_lock_perm.thread_id() == lctx.thread_id(),
            irt_lock_perm.lock_id() == old(irt).locking_thread()->Write_lock_id,
            bus <= PCI_BUS_COUNT,
            device < PCI_DEVICE_COUNT,
            function < PCI_FUNCTION_COUNT,
            bus == PCI_BUS_COUNT ==> device == 0 && function == 0,
            forall|b: usize, d: usize, f: usize| #![trigger irt.view().spec_index_iommu_root(b, d, f)] #![trigger irt.view().spec_index_iommu_did(b, d, f)] pci_bdf_valid(b, d, f) ==> {
                let moved = pci_bdf_lt((b, d, f), (bus, device, function)) && old(irt).view().spec_index_owner(b, d, f) == owner
                    && old(irt).view().spec_index_iommu_did(b, d, f) == Some(old_did);
                &&& irt.view().spec_index_iommu_root(b, d, f) == if moved { Some(root) } else { old(irt).view().spec_index_iommu_root(b, d, f) }
                &&& irt.view().spec_index_iommu_did(b, d, f) == if moved { Some(new_did) } else { old(irt).view().spec_index_iommu_did(b, d, f) }
            },
        decreases PCI_BUS_COUNT - bus, PCI_DEVICE_COUNT - device, PCI_FUNCTION_COUNT - function,
    {
        let current_owner = irt.borrow(Tracked(irt_lock_perm)).owner(bus, device, function);
        let current_did = irt.borrow(Tracked(irt_lock_perm)).iommu_did(bus, device, function);
        if current_owner == owner && current_did.is_some() && current_did.unwrap() == old_did {
            irt.borrow_mut(Tracked(lctx), Tracked(irt_lock_perm)).detach(bus, device, function);
            iommu_tlb.invalidate_domain(old_did, Ghost(KernelK { irt: *irt, iommu_tlb: *iommu_tlb, ..k }), Tracked(lctx));
            irt.borrow_mut(Tracked(lctx), Tracked(irt_lock_perm)).attach(bus, device, function, root, new_did);
        }
        if function + 1 < PCI_FUNCTION_COUNT {
            function = function + 1;
        } else if device + 1 < PCI_DEVICE_COUNT {
            function = 0;
            device = device + 1;
        } else {
            function = 0;
            device = 0;
            bus = bus + 1;
        }
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
        forall|b: usize, d: usize, f: usize| #![trigger final(irt).view().spec_index_owner(b, d, f)] final(irt).view().spec_index_owner(b, d, f) == old(irt).view().spec_index_owner(b, d, f),
        final(irt).view().iommu_roots() == seq3_update(old(irt).view().iommu_roots(), bus as int, device as int, function as int, None),
        final(irt).view().iommu_dids() == seq3_update(old(irt).view().iommu_dids(), bus as int, device as int, function as int, None),
        forall|b: usize, d: usize, f: usize| #![trigger final(irt).view().spec_index_iommu_root(b, d, f)] #![trigger final(irt).view().spec_index_iommu_did(b, d, f)] pci_bdf_valid(b, d, f) ==> {
            &&& final(irt).view().spec_index_iommu_root(b, d, f) == if (b, d, f) == (bus, device, function) { None } else { old(irt).view().spec_index_iommu_root(b, d, f) }
            &&& final(irt).view().spec_index_iommu_did(b, d, f) == if (b, d, f) == (bus, device, function) { None } else { old(irt).view().spec_index_iommu_did(b, d, f) }
        },
        final(iommu_tlb).inv(),
        old(irt).view().spec_index_iommu_did(bus, device, function) matches Some(did) ==> {
            &&& final(iommu_tlb).view() == old(iommu_tlb).view().insert(did, final(iommu_tlb).spec_index(did))
            &&& iommu_tlb_within_may_cache(KernelK { irt: *final(irt), ..k }, did, final(iommu_tlb).spec_index(did))
            &&& Map::new(final(iommu_tlb).context_cache().dom().filter(|bdf: PciBdf| final(iommu_tlb).context_cache()[bdf].1 != did), |bdf: PciBdf| final(iommu_tlb).context_cache()[bdf])
                == Map::new(old(iommu_tlb).context_cache().dom().filter(|bdf: PciBdf| old(iommu_tlb).context_cache()[bdf].1 != did), |bdf: PciBdf| old(iommu_tlb).context_cache()[bdf])
            &&& forall|bdf: PciBdf| #![trigger final(iommu_tlb).context_cache().dom().contains(bdf)] final(iommu_tlb).context_cache().dom().contains(bdf) && final(iommu_tlb).context_cache()[bdf].1 == did
                ==> iommu_context_cache_entry_present(KernelK { irt: *final(irt), ..k }, bdf, final(iommu_tlb).context_cache()[bdf])
        },
        old(irt).view().spec_index_iommu_did(bus, device, function) is None ==> final(iommu_tlb).view() == old(iommu_tlb).view() && final(iommu_tlb).context_cache() == old(iommu_tlb).context_cache(),
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
        old(irt).view().spec_index_owner(bus, device, function) == old(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr,
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
        forall|b: usize, d: usize, f: usize| #![trigger final(irt).view().spec_index_owner(b, d, f)] #![trigger final(irt).view().spec_index_iommu_root(b, d, f)]
            #![trigger final(irt).view().spec_index_iommu_did(b, d, f)] pci_bdf_valid(b, d, f) ==> {
            &&& final(irt).view().spec_index_owner(b, d, f) == old(irt).view().spec_index_owner(b, d, f)
            &&& final(irt).view().spec_index_iommu_root(b, d, f) == if (b, d, f) == (bus, device, function) { Some(old(iommu_table_map).spec_index(iommu_table_ptr).view().cr3) }
                else { old(irt).view().spec_index_iommu_root(b, d, f) }
            &&& final(irt).view().spec_index_iommu_did(b, d, f) == if (b, d, f) == (bus, device, function) { Some(did) } else { old(irt).view().spec_index_iommu_did(b, d, f) }
        },
        iommu_table_perms_wf(*final(iommu_table_map)),
        final(iommu_table_map).unchanged_except(old(iommu_table_map), iommu_table_ptr),
        final(iommu_table_map).typed_lock_map_aligned(lctx.iommu_table_lock_map(), lctx.thread_id()),
        final(iommu_table_map).lock_id_by_key(iommu_table_ptr) == old(iommu_table_map).lock_id_by_key(iommu_table_ptr),
        final(iommu_table_map).spec_index(iommu_table_ptr).locking_thread() == old(iommu_table_map).spec_index(iommu_table_ptr).locking_thread(),
        final(iommu_table_map).spec_index(iommu_table_ptr).being_killed() == old(iommu_table_map).spec_index(iommu_table_ptr).being_killed(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view() == (PageTable { did: Some(did), ..old(iommu_table_map).spec_index(iommu_table_ptr).view() }),
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

/// Thread-exit reclaim of the write-held IOMMU table `iommu_table_ptr` under the held root-table lock: clears every context entry
/// its owner owns, owners untouched, then invalidates the table's DID once and drops it. A table without a DID invalidates nothing.
pub fn iommu_root_table_detach_all(
    irt: &mut IommuRootTableLock, iommu_tlb: &mut IommuTLB, iommu_table_map: &mut IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot,
    Ghost(k): Ghost<KernelK>, Tracked(lctx): Tracked<&LocalContext>, Tracked(irt_lock_perm): Tracked<&LockPerm>, Tracked(iommu_table_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(irt).inv(),
        old(iommu_tlb).inv(),
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
        forall|b: usize, d: usize, f: usize| #![trigger old(irt).view().spec_index_iommu_did(b, d, f)]
            pci_bdf_valid(b, d, f) ==> (old(irt).view().spec_index_iommu_did(b, d, f) is Some) == (old(irt).view().spec_index_iommu_root(b, d, f) is Some),
        forall|b: usize, d: usize, f: usize| #![trigger final(irt).view().spec_index_iommu_root(b, d, f)] #![trigger final(irt).view().spec_index_iommu_did(b, d, f)]
            pci_bdf_valid(b, d, f) ==> {
            let owned = old(irt).view().spec_index_owner(b, d, f) == old(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr;
            &&& final(irt).view().spec_index_iommu_root(b, d, f) == if owned { None } else { old(irt).view().spec_index_iommu_root(b, d, f) }
            &&& final(irt).view().spec_index_iommu_did(b, d, f) == if owned { None } else { old(irt).view().spec_index_iommu_did(b, d, f) }
        },
        iommu_table_perms_wf(*final(iommu_table_map)),
        final(iommu_table_map).unchanged_except(old(iommu_table_map), iommu_table_ptr),
        final(iommu_table_map).typed_lock_map_aligned(lctx.iommu_table_lock_map(), lctx.thread_id()),
        final(iommu_table_map).lock_id_by_key(iommu_table_ptr) == old(iommu_table_map).lock_id_by_key(iommu_table_ptr),
        final(iommu_table_map).spec_index(iommu_table_ptr).locking_thread() == old(iommu_table_map).spec_index(iommu_table_ptr).locking_thread(),
        final(iommu_table_map).spec_index(iommu_table_ptr).being_killed() == old(iommu_table_map).spec_index(iommu_table_ptr).being_killed(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view() == (PageTable { did: None, ..old(iommu_table_map).spec_index(iommu_table_ptr).view() }),
        final(iommu_tlb).inv(),
        old(iommu_table_map).spec_index(iommu_table_ptr).view().did matches Some(did) ==> {
            &&& final(iommu_tlb).view() == old(iommu_tlb).view().insert(did, final(iommu_tlb).spec_index(did))
            &&& iommu_tlb_within_may_cache(KernelK { irt: *final(irt), ..k }, did, final(iommu_tlb).spec_index(did))
            &&& Map::new(final(iommu_tlb).context_cache().dom().filter(|bdf: PciBdf| final(iommu_tlb).context_cache()[bdf].1 != did), |bdf: PciBdf| final(iommu_tlb).context_cache()[bdf])
                == Map::new(old(iommu_tlb).context_cache().dom().filter(|bdf: PciBdf| old(iommu_tlb).context_cache()[bdf].1 != did), |bdf: PciBdf| old(iommu_tlb).context_cache()[bdf])
            &&& forall|bdf: PciBdf| #![trigger final(iommu_tlb).context_cache().dom().contains(bdf)] final(iommu_tlb).context_cache().dom().contains(bdf) && final(iommu_tlb).context_cache()[bdf].1 == did
                ==> iommu_context_cache_entry_present(KernelK { irt: *final(irt), ..k }, bdf, final(iommu_tlb).context_cache()[bdf])
        },
        old(iommu_table_map).spec_index(iommu_table_ptr).view().did is None ==> *final(iommu_tlb) == *old(iommu_tlb),
{
    assert(irt.wlocked_by(lctx)) by { reveal(iommu_root_table_typed_lock_map_aligned); };
    assert(iommu_table_map.perms_wf() && iommu_table_map.spec_index(iommu_table_ptr).is_init() && iommu_table_map.spec_index(iommu_table_ptr).view().inv()) by {
        iommu_table_perms_wf_map(*iommu_table_map); iommu_table_perms_wf_at(*iommu_table_map, iommu_table_ptr);
    };
    let iommu_table = iommu_table_map.borrow_typed(iommu_table_ptr, Ghost(lctx.iommu_table_lock_map()), Tracked(lctx), Tracked(iommu_table_lock_perm));
    let process_ptr = iommu_table.proc_ptr;
    let old_did = iommu_table.did;
    irt.borrow_mut(Tracked(lctx), Tracked(irt_lock_perm)).detach_owned_contexts(process_ptr, process_ptr);
    if let Some(did) = old_did {
        iommu_tlb.invalidate_domain(did, Ghost(KernelK { irt: *irt, iommu_tlb: *iommu_tlb, ..k }), Tracked(lctx));
        iommu_table_map_set_did(iommu_table_map, iommu_table_ptr, None, Tracked(lctx), Tracked(iommu_table_lock_perm));
    }
    proof { assert(iommu_root_table_typed_lock_map_aligned(*irt, lctx.iommu_root_table_lock_map(), lctx.thread_id())) by { reveal(iommu_root_table_typed_lock_map_aligned); }; }
}

/// Kill reclaim of the write-held IOMMU table `iommu_table_ptr` under the held root-table lock: clears every context entry its
/// owner owns and hands each such slot to `recipient`, then invalidates the table's DID once and drops it. A table without a DID
/// invalidates nothing.
pub fn iommu_root_table_reassign_detach_all(
    irt: &mut IommuRootTableLock, iommu_tlb: &mut IommuTLB, iommu_table_map: &mut IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot,
    recipient: RwLockProcessPtr, Ghost(k): Ghost<KernelK>, Tracked(lctx): Tracked<&LocalContext>, Tracked(irt_lock_perm): Tracked<&LockPerm>,
    Tracked(iommu_table_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(irt).inv(),
        old(iommu_tlb).inv(),
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
        forall|b: usize, d: usize, f: usize| #![trigger old(irt).view().spec_index_iommu_did(b, d, f)]
            pci_bdf_valid(b, d, f) ==> (old(irt).view().spec_index_iommu_did(b, d, f) is Some) == (old(irt).view().spec_index_iommu_root(b, d, f) is Some),
        forall|b: usize, d: usize, f: usize| #![trigger final(irt).view().spec_index_owner(b, d, f)] #![trigger final(irt).view().spec_index_iommu_root(b, d, f)]
            #![trigger final(irt).view().spec_index_iommu_did(b, d, f)] pci_bdf_valid(b, d, f) ==> {
            let owned = old(irt).view().spec_index_owner(b, d, f) == old(iommu_table_map).spec_index(iommu_table_ptr).view().proc_ptr;
            &&& final(irt).view().spec_index_owner(b, d, f) == if owned { recipient } else { old(irt).view().spec_index_owner(b, d, f) }
            &&& final(irt).view().spec_index_iommu_root(b, d, f) == if owned { None } else { old(irt).view().spec_index_iommu_root(b, d, f) }
            &&& final(irt).view().spec_index_iommu_did(b, d, f) == if owned { None } else { old(irt).view().spec_index_iommu_did(b, d, f) }
        },
        iommu_table_perms_wf(*final(iommu_table_map)),
        final(iommu_table_map).unchanged_except(old(iommu_table_map), iommu_table_ptr),
        final(iommu_table_map).typed_lock_map_aligned(lctx.iommu_table_lock_map(), lctx.thread_id()),
        final(iommu_table_map).lock_id_by_key(iommu_table_ptr) == old(iommu_table_map).lock_id_by_key(iommu_table_ptr),
        final(iommu_table_map).spec_index(iommu_table_ptr).locking_thread() == old(iommu_table_map).spec_index(iommu_table_ptr).locking_thread(),
        final(iommu_table_map).spec_index(iommu_table_ptr).being_killed() == old(iommu_table_map).spec_index(iommu_table_ptr).being_killed(),
        final(iommu_table_map).spec_index(iommu_table_ptr).view() == (PageTable { did: None, ..old(iommu_table_map).spec_index(iommu_table_ptr).view() }),
        final(iommu_tlb).inv(),
        old(iommu_table_map).spec_index(iommu_table_ptr).view().did matches Some(did) ==> {
            &&& final(iommu_tlb).view() == old(iommu_tlb).view().insert(did, final(iommu_tlb).spec_index(did))
            &&& iommu_tlb_within_may_cache(KernelK { irt: *final(irt), ..k }, did, final(iommu_tlb).spec_index(did))
            &&& Map::new(final(iommu_tlb).context_cache().dom().filter(|bdf: PciBdf| final(iommu_tlb).context_cache()[bdf].1 != did), |bdf: PciBdf| final(iommu_tlb).context_cache()[bdf])
                == Map::new(old(iommu_tlb).context_cache().dom().filter(|bdf: PciBdf| old(iommu_tlb).context_cache()[bdf].1 != did), |bdf: PciBdf| old(iommu_tlb).context_cache()[bdf])
            &&& forall|bdf: PciBdf| #![trigger final(iommu_tlb).context_cache().dom().contains(bdf)] final(iommu_tlb).context_cache().dom().contains(bdf) && final(iommu_tlb).context_cache()[bdf].1 == did
                ==> iommu_context_cache_entry_present(KernelK { irt: *final(irt), ..k }, bdf, final(iommu_tlb).context_cache()[bdf])
        },
        old(iommu_table_map).spec_index(iommu_table_ptr).view().did is None ==> *final(iommu_tlb) == *old(iommu_tlb),
{
    assert(irt.wlocked_by(lctx)) by { reveal(iommu_root_table_typed_lock_map_aligned); };
    assert(iommu_table_map.perms_wf() && iommu_table_map.spec_index(iommu_table_ptr).is_init() && iommu_table_map.spec_index(iommu_table_ptr).view().inv()) by {
        iommu_table_perms_wf_map(*iommu_table_map); iommu_table_perms_wf_at(*iommu_table_map, iommu_table_ptr);
    };
    let iommu_table = iommu_table_map.borrow_typed(iommu_table_ptr, Ghost(lctx.iommu_table_lock_map()), Tracked(lctx), Tracked(iommu_table_lock_perm));
    let process_ptr = iommu_table.proc_ptr;
    let old_did = iommu_table.did;
    irt.borrow_mut(Tracked(lctx), Tracked(irt_lock_perm)).detach_owned_contexts(process_ptr, recipient);
    if let Some(did) = old_did {
        iommu_tlb.invalidate_domain(did, Ghost(KernelK { irt: *irt, iommu_tlb: *iommu_tlb, ..k }), Tracked(lctx));
        iommu_table_map_set_did(iommu_table_map, iommu_table_ptr, None, Tracked(lctx), Tracked(iommu_table_lock_perm));
    }
    proof { assert(iommu_root_table_typed_lock_map_aligned(*irt, lctx.iommu_root_table_lock_map(), lctx.thread_id())) by { reveal(iommu_root_table_typed_lock_map_aligned); }; }
}

/// Kill reclaim of a process `owner` without an IOMMU table under the held root-table lock: hands every slot `owner` owns to
/// `recipient` and clears its context entry. A table-less owner has no present entry, so nothing is cached or invalidated.
pub fn iommu_root_table_reassign_owned(
    irt: &mut IommuRootTableLock, owner: RwLockProcessPtr, recipient: RwLockProcessPtr, Tracked(lctx): Tracked<&LocalContext>, Tracked(irt_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(irt).inv(),
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
        forall|b: usize, d: usize, f: usize| #![trigger old(irt).view().spec_index_iommu_did(b, d, f)]
            pci_bdf_valid(b, d, f) ==> (old(irt).view().spec_index_iommu_did(b, d, f) is Some) == (old(irt).view().spec_index_iommu_root(b, d, f) is Some),
        forall|b: usize, d: usize, f: usize| #![trigger final(irt).view().spec_index_owner(b, d, f)] #![trigger final(irt).view().spec_index_iommu_root(b, d, f)]
            #![trigger final(irt).view().spec_index_iommu_did(b, d, f)] pci_bdf_valid(b, d, f) ==> {
            let owned = old(irt).view().spec_index_owner(b, d, f) == owner;
            &&& final(irt).view().spec_index_owner(b, d, f) == if owned { recipient } else { old(irt).view().spec_index_owner(b, d, f) }
            &&& final(irt).view().spec_index_iommu_root(b, d, f) == if owned { None } else { old(irt).view().spec_index_iommu_root(b, d, f) }
            &&& final(irt).view().spec_index_iommu_did(b, d, f) == if owned { None } else { old(irt).view().spec_index_iommu_did(b, d, f) }
        },
{
    assert(irt.wlocked_by(lctx)) by { reveal(iommu_root_table_typed_lock_map_aligned); };
    irt.borrow_mut(Tracked(lctx), Tracked(irt_lock_perm)).detach_owned_contexts(owner, recipient);
    proof { assert(iommu_root_table_typed_lock_map_aligned(*irt, lctx.iommu_root_table_lock_map(), lctx.thread_id())) by { reveal(iommu_root_table_typed_lock_map_aligned); }; }
}
}
