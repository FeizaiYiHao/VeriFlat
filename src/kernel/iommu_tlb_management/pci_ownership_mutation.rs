use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::pci_ownership_mutation_eof::*;

verus! {
/// One change of a page table's PCI function array together with the root-table owner of that function.
#[derive(Clone, Copy)]
pub enum PciEntryUpdate {
    /// The unowned function `(bus, device, function)` enters the free entry, owned by the table's process.
    Claim { bus: usize, device: usize, function: usize },
    /// The detached function of the used entry leaves the array and becomes unowned.
    Release,
}

/// The function an update of entry `index` of `pci` concerns.
pub open spec fn pci_entry_update_bdf(pci: PciFunctionArray, index: int, update: PciEntryUpdate) -> PciBdf {
    match update {
        PciEntryUpdate::Claim { bus, device, function } => (bus, device, function),
        PciEntryUpdate::Release => pci.spec_entry(index).bdf,
    }
}

/// The array view after an update of entry `index` of `pci`.
pub open spec fn pci_entry_update_view(pci: PciFunctionArray, index: int, update: PciEntryUpdate) -> Map<PciBdf, Set<PciBarMapping>> {
    match update {
        PciEntryUpdate::Claim { bus, device, function } => pci.view().insert((bus, device, function), Set::<PciBarMapping>::empty()),
        PciEntryUpdate::Release => pci.view().remove(pci.spec_entry(index).bdf),
    }
}

impl KernelK {
    /// Apply `update` to entry `index` of the PCI function array of page table `pagetable_ptr`, which this thread write-holds,
    /// under the held root-table lock: a `Claim` puts the unowned function into the free entry and makes the table's process
    /// its owner; a `Release` takes the detached function of the used entry out and leaves it unowned. Context entries, the
    /// rest of the table, and every other kernel object stay.
    pub fn update_pci_entry(
        &mut self, pagetable_ptr: RwLockPageTableRoot, index: usize, update: PciEntryUpdate, Tracked(lctx): Tracked<&LocalContext>,
        Tracked(pagetable_perm): Tracked<&LockPerm>, Tracked(irt_perm): Tracked<&LockPerm>,
    )
        requires
            old(self).inv(),
            typed_lock_maps_aligned(old(self), lctx),
            old(self).pt_mp.dom().contains(pagetable_ptr),
            typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            pagetable_perm.state() is WriteLock,
            pagetable_perm.thread_id() == lctx.thread_id(),
            pagetable_perm.lock_id() == old(self).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(lctx.iommu_root_table_lock_map(), old(self).irt.view().table_base(), TypedLockMode::Write),
            irt_perm.state() is WriteLock,
            irt_perm.thread_id() == lctx.thread_id(),
            irt_perm.lock_id() == old(self).irt.locking_thread()->Write_lock_id,
            index < PCI_FUNCTIONS_PER_PROCESS,
            update matches PciEntryUpdate::Claim { bus, device, function } ==> {
                let process = old(self).prc_mp.spec_index(old(self).pt_mp.spec_index(pagetable_ptr).view().higher.proc_ptr).view();
                &&& pci_bdf_valid(bus, device, function)
                &&& old(self).irt.view().spec_index_owner(bus, device, function) is None
                &&& !old(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci.spec_entry(index as int).used
                &&& old(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci.view().dom().len() < PCI_FUNCTIONS_PER_PROCESS
                &&& !(process.state.view() is TablesEmptied)
                &&& !(process.state.view() is Zombie)
            },
            update is Release ==> {
                let bdf = old(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci.spec_entry(index as int).bdf;
                &&& old(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci.spec_entry(index as int).used
                &&& old(self).prc_mp.spec_index(old(self).pt_mp.spec_index(pagetable_ptr).view().higher.proc_ptr).view().iommu_table is Some
                    ==> old(self).irt.view().spec_index_iommu_root(bdf.0, bdf.1, bdf.2) is None
            },
        ensures
            final(self).inv(),
            typed_lock_maps_aligned(final(self), lctx),
            *final(self) == (KernelK { irt: final(self).irt, pt_mp: final(self).pt_mp, ..*old(self) }),
            final(self).irt.locking_thread() == old(self).irt.locking_thread(),
            final(self).irt.view().table_base() == old(self).irt.view().table_base(),
            final(self).irt.view().iommu_roots() == old(self).irt.view().iommu_roots(),
            final(self).irt.view().iommu_dids() == old(self).irt.view().iommu_dids(),
            ({
                let pci = old(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci;
                let bdf = pci_entry_update_bdf(pci, index as int, update);
                let owner = if update is Claim { Some(old(self).pt_mp.spec_index(pagetable_ptr).view().higher.proc_ptr) } else { None };
                &&& pci_bdf_valid(bdf.0, bdf.1, bdf.2)
                &&& final(self).irt.view().owners() == seq3_update(old(self).irt.view().owners(), bdf.0 as int, bdf.1 as int, bdf.2 as int, owner)
                &&& forall|b: usize, d: usize, f: usize| #![trigger final(self).irt.view().spec_index_owner(b, d, f)] #![trigger final(self).irt.view().spec_index_iommu_root(b, d, f)]
                    #![trigger final(self).irt.view().spec_index_iommu_did(b, d, f)] pci_bdf_valid(b, d, f) ==> {
                    &&& final(self).irt.view().spec_index_owner(b, d, f) == if (b, d, f) == bdf { owner } else { old(self).irt.view().spec_index_owner(b, d, f) }
                    &&& final(self).irt.view().spec_index_iommu_root(b, d, f) == old(self).irt.view().spec_index_iommu_root(b, d, f)
                    &&& final(self).irt.view().spec_index_iommu_did(b, d, f) == old(self).irt.view().spec_index_iommu_did(b, d, f)
                }
                &&& final(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci.view() == pci_entry_update_view(pci, index as int, update)
            }),
            final(self).pt_mp.unchanged_except(&old(self).pt_mp, pagetable_ptr),
            forall|k: RwLockPageTableRoot| #![trigger final(self).pt_mp.lock_id_by_key(k)] old(self).pt_mp.dom().contains(k) ==> final(self).pt_mp.lock_id_by_key(k) == old(self).pt_mp.lock_id_by_key(k),
            final(self).pt_mp.spec_index(pagetable_ptr).locking_thread() == old(self).pt_mp.spec_index(pagetable_ptr).locking_thread(),
            final(self).pt_mp.spec_index(pagetable_ptr).being_killed() == old(self).pt_mp.spec_index(pagetable_ptr).being_killed(),
            final(self).pt_mp.spec_index(pagetable_ptr).view().higher
                == (PageTableHigher { pci: final(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci, ..old(self).pt_mp.spec_index(pagetable_ptr).view().higher }),
            final(self).pt_mp.spec_index(pagetable_ptr).view().lower_backup == old(self).pt_mp.spec_index(pagetable_ptr).view().lower_backup,
            forall|l4i: L4Index| #![trigger final(self).pt_mp.spec_index(pagetable_ptr).view().higher.spec_held_l4(l4i)]
                final(self).pt_mp.spec_index(pagetable_ptr).view().higher.spec_held_l4(l4i) == old(self).pt_mp.spec_index(pagetable_ptr).view().higher.spec_held_l4(l4i)
                && final(self).pt_mp.spec_index(pagetable_ptr).view().higher.spec_resolve_mapping_l4(l4i) == old(self).pt_mp.spec_index(pagetable_ptr).view().higher.spec_resolve_mapping_l4(l4i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger final(self).pt_mp.spec_index(pagetable_ptr).view().higher.spec_held_l3(l4i, l3i)]
                final(self).pt_mp.spec_index(pagetable_ptr).view().higher.spec_held_l3(l4i, l3i) == old(self).pt_mp.spec_index(pagetable_ptr).view().higher.spec_held_l3(l4i, l3i)
                && final(self).pt_mp.spec_index(pagetable_ptr).view().higher.spec_resolve_mapping_l3(l4i, l3i)
                    == old(self).pt_mp.spec_index(pagetable_ptr).view().higher.spec_resolve_mapping_l3(l4i, l3i),
            update is Claim ==> final(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci.spec_entry(index as int).used,
            update is Release ==> !final(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci.spec_entry(index as int).used,
            forall|j: int| #![trigger final(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci.spec_entry(j)]
                j != index ==> final(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci.spec_entry(j) == old(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci.spec_entry(j),
            forall|f: PciBdf| #![trigger final(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci.index_of(f)]
                old(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci.view().dom().contains(f) && final(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci.view().dom().contains(f)
                    ==> final(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci.index_of(f) == old(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci.index_of(f),
    {
        broadcast use PciFunctionArray::wf_function_at, PciFunctionArray::wf_entry_at;
        proof {
            pagetable_perms_wf_map(old(self).pt_mp);
            pagetable_perms_wf_at(old(self).pt_mp, pagetable_ptr);
            old(self).pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
        }
        assert(self.irt.wlocked_by(lctx)) by { reveal(iommu_root_table_typed_lock_map_aligned); };
        let ghost proc_ptr = self.pt_mp.spec_index(pagetable_ptr).view().higher.proc_ptr;
        let (bus, device, function) = match update {
            PciEntryUpdate::Claim { bus, device, function } => (bus, device, function),
            PciEntryUpdate::Release => self.pt_mp.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(lctx), Tracked(pagetable_perm)).higher.pci.entry(index).bdf,
        };
        proof {
            if self.pt_mp.spec_index(pagetable_ptr).view().higher.pci.view().dom().contains((bus, device, function)) {
                pci_function_ownership_wf_pagetable_at(self.irt.view(), self.prc_mp, self.pt_mp, pagetable_ptr, (bus, device, function));
            }
            if update is Release && self.prc_mp.spec_index(proc_ptr).view().iommu_table is None {
                update_pci_entry_eof_released_function_detached(*old(self), pagetable_ptr, (bus, device, function));
            }
        }
        let pagetable = self.pt_mp.borrow_mut_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(lctx), Tracked(pagetable_perm));
        match update {
            PciEntryUpdate::Claim { .. } => { pagetable.higher.pci.insert(index, bus, device, function); },
            PciEntryUpdate::Release => { pagetable.higher.pci.remove(index); },
        }
        match update {
            PciEntryUpdate::Claim { .. } => { self.irt.borrow_mut(Tracked(lctx), Tracked(irt_perm)).claim(bus, device, function, Ghost(proc_ptr)); },
            PciEntryUpdate::Release => { self.irt.borrow_mut(Tracked(lctx), Tracked(irt_perm)).release(bus, device, function); },
        }
        proof {
            match update {
                PciEntryUpdate::Claim { .. } => {
                    assert(update_pci_entry_eof_transition_framing(*old(self), *self, pagetable_ptr, index as int, update)) by { reveal(update_pci_entry_eof_transition_framing); };
                    assert(update_pci_entry_eof_owner_update(*old(self), *self, pagetable_ptr, index as int, update)) by { reveal(update_pci_entry_eof_owner_update); };
                },
                PciEntryUpdate::Release => {
                    assert(update_pci_entry_eof_transition_framing(*old(self), *self, pagetable_ptr, index as int, update)) by { reveal(update_pci_entry_eof_transition_framing); };
                    assert(update_pci_entry_eof_owner_update(*old(self), *self, pagetable_ptr, index as int, update)) by { reveal(update_pci_entry_eof_owner_update); };
                },
            }
            update_pci_entry_eof(*old(self), *self, pagetable_ptr, index as int, update);
            assert(iommu_root_table_typed_lock_map_aligned(self.irt, lctx.iommu_root_table_lock_map(), lctx.thread_id())) by { reveal(iommu_root_table_typed_lock_map_aligned); };
            assert(typed_lock_maps_aligned(self, lctx)) by {
                reveal(update_pci_entry_eof_transition_framing); reveal(pagetable_window_typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned);
            };
        }
    }

    /// Release every function of the PCI function array of page table `pagetable_ptr`, which this thread write-holds, under the
    /// held root-table lock: each function, detached, leaves the array and becomes unowned. Context entries, the rest of the
    /// table, and every other kernel object stay.
    pub fn release_pci_functions(
        &mut self, pagetable_ptr: RwLockPageTableRoot, Tracked(lctx): Tracked<&LocalContext>, Tracked(pagetable_perm): Tracked<&LockPerm>,
        Tracked(irt_perm): Tracked<&LockPerm>,
    )
        requires
            old(self).inv(),
            typed_lock_maps_aligned(old(self), lctx),
            old(self).pt_mp.dom().contains(pagetable_ptr),
            typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            pagetable_perm.state() is WriteLock,
            pagetable_perm.thread_id() == lctx.thread_id(),
            pagetable_perm.lock_id() == old(self).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(lctx.iommu_root_table_lock_map(), old(self).irt.view().table_base(), TypedLockMode::Write),
            irt_perm.state() is WriteLock,
            irt_perm.thread_id() == lctx.thread_id(),
            irt_perm.lock_id() == old(self).irt.locking_thread()->Write_lock_id,
            old(self).prc_mp.spec_index(old(self).pt_mp.spec_index(pagetable_ptr).view().higher.proc_ptr).view().iommu_table is Some
                ==> forall|b: usize, d: usize, f: usize| #![trigger old(self).irt.view().spec_index_iommu_root(b, d, f)]
                old(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci.view().dom().contains((b, d, f)) ==> old(self).irt.view().spec_index_iommu_root(b, d, f) is None,
        ensures
            final(self).inv(),
            typed_lock_maps_aligned(final(self), lctx),
            *final(self) == (KernelK { irt: final(self).irt, pt_mp: final(self).pt_mp, ..*old(self) }),
            final(self).irt.locking_thread() == old(self).irt.locking_thread(),
            final(self).irt.view().table_base() == old(self).irt.view().table_base(),
            final(self).irt.view().iommu_roots() == old(self).irt.view().iommu_roots(),
            final(self).irt.view().iommu_dids() == old(self).irt.view().iommu_dids(),
            forall|b: usize, d: usize, f: usize| #![trigger final(self).irt.view().spec_index_owner(b, d, f)] pci_bdf_valid(b, d, f) ==> final(self).irt.view().spec_index_owner(b, d, f)
                == if old(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci.view().dom().contains((b, d, f)) { None } else { old(self).irt.view().spec_index_owner(b, d, f) },
            final(self).pt_mp.unchanged_except(&old(self).pt_mp, pagetable_ptr),
            forall|k: RwLockPageTableRoot| #![trigger final(self).pt_mp.lock_id_by_key(k)] old(self).pt_mp.dom().contains(k) ==> final(self).pt_mp.lock_id_by_key(k) == old(self).pt_mp.lock_id_by_key(k),
            final(self).pt_mp.spec_index(pagetable_ptr).locking_thread() == old(self).pt_mp.spec_index(pagetable_ptr).locking_thread(),
            final(self).pt_mp.spec_index(pagetable_ptr).being_killed() == old(self).pt_mp.spec_index(pagetable_ptr).being_killed(),
            final(self).pt_mp.spec_index(pagetable_ptr).view().higher
                == (PageTableHigher { pci: final(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci, ..old(self).pt_mp.spec_index(pagetable_ptr).view().higher }),
            final(self).pt_mp.spec_index(pagetable_ptr).view().lower_backup == old(self).pt_mp.spec_index(pagetable_ptr).view().lower_backup,
            forall|l4i: L4Index| #![trigger final(self).pt_mp.spec_index(pagetable_ptr).view().higher.spec_held_l4(l4i)]
                final(self).pt_mp.spec_index(pagetable_ptr).view().higher.spec_held_l4(l4i) == old(self).pt_mp.spec_index(pagetable_ptr).view().higher.spec_held_l4(l4i)
                && final(self).pt_mp.spec_index(pagetable_ptr).view().higher.spec_resolve_mapping_l4(l4i) == old(self).pt_mp.spec_index(pagetable_ptr).view().higher.spec_resolve_mapping_l4(l4i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger final(self).pt_mp.spec_index(pagetable_ptr).view().higher.spec_held_l3(l4i, l3i)]
                final(self).pt_mp.spec_index(pagetable_ptr).view().higher.spec_held_l3(l4i, l3i) == old(self).pt_mp.spec_index(pagetable_ptr).view().higher.spec_held_l3(l4i, l3i)
                && final(self).pt_mp.spec_index(pagetable_ptr).view().higher.spec_resolve_mapping_l3(l4i, l3i)
                    == old(self).pt_mp.spec_index(pagetable_ptr).view().higher.spec_resolve_mapping_l3(l4i, l3i),
            final(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci.view() == Map::<PciBdf, Set<PciBarMapping>>::empty(),
            old(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci.view().dom() != Set::<PciBdf>::empty()
                ==> final(self).irt.view().owners() == pci_owners_released(old(self).irt.view().owners(), old(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci.view().dom()),
    {
        broadcast use PciFunctionArray::wf_function_at, PciFunctionArray::wf_entry_at;
        proof { pagetable_perms_wf_map(self.pt_mp); pagetable_perms_wf_at(self.pt_mp, pagetable_ptr); }
        let ghost pci = old(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci;
        let ghost mut released = false;
        let mut i: usize = 0;
        while i < PCI_FUNCTIONS_PER_PROCESS
            invariant
                self.inv(),
                old(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci.wf(),
                pci == old(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci,
                released ==> self.irt.view().owners() == pci_owners_released(old(self).irt.view().owners(), pci.view().dom().filter(|f: PciBdf| pci.index_of(f) < i)),
                !released ==> self.irt.view().owners() == old(self).irt.view().owners(),
                !released ==> forall|j: int| #![trigger pci.spec_entry(j)] 0 <= j < i ==> !pci.spec_entry(j).used,
                typed_lock_maps_aligned(self, lctx),
                old(self).inv(),
                old(self).pt_mp.dom().contains(pagetable_ptr),
                typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
                pagetable_perm.state() is WriteLock,
                pagetable_perm.thread_id() == lctx.thread_id(),
                pagetable_perm.lock_id() == self.pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
                typed_lock_map_contains_mode(lctx.iommu_root_table_lock_map(), self.irt.view().table_base(), TypedLockMode::Write),
                irt_perm.state() is WriteLock,
                irt_perm.thread_id() == lctx.thread_id(),
                irt_perm.lock_id() == self.irt.locking_thread()->Write_lock_id,
                i <= PCI_FUNCTIONS_PER_PROCESS,
                *self == (KernelK { irt: self.irt, pt_mp: self.pt_mp, ..*old(self) }),
                self.irt.locking_thread() == old(self).irt.locking_thread(),
                self.irt.view().table_base() == old(self).irt.view().table_base(),
                self.irt.view().iommu_roots() == old(self).irt.view().iommu_roots(),
                self.irt.view().iommu_dids() == old(self).irt.view().iommu_dids(),
                forall|b: usize, d: usize, f: usize| #![trigger self.irt.view().spec_index_owner(b, d, f)] pci_bdf_valid(b, d, f) ==> self.irt.view().spec_index_owner(b, d, f)
                    == if old(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci.view().dom().contains((b, d, f))
                        && old(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci.index_of((b, d, f)) < i { None } else { old(self).irt.view().spec_index_owner(b, d, f) },
                old(self).prc_mp.spec_index(old(self).pt_mp.spec_index(pagetable_ptr).view().higher.proc_ptr).view().iommu_table is Some
                    ==> forall|b: usize, d: usize, f: usize| #![trigger self.irt.view().spec_index_iommu_root(b, d, f)]
                    old(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci.view().dom().contains((b, d, f)) ==> self.irt.view().spec_index_iommu_root(b, d, f) is None,
                self.pt_mp.unchanged_except(&old(self).pt_mp, pagetable_ptr),
                forall|k: RwLockPageTableRoot| #![trigger self.pt_mp.lock_id_by_key(k)] old(self).pt_mp.dom().contains(k) ==> self.pt_mp.lock_id_by_key(k) == old(self).pt_mp.lock_id_by_key(k),
                self.pt_mp.spec_index(pagetable_ptr).locking_thread() == old(self).pt_mp.spec_index(pagetable_ptr).locking_thread(),
                self.pt_mp.spec_index(pagetable_ptr).being_killed() == old(self).pt_mp.spec_index(pagetable_ptr).being_killed(),
                self.pt_mp.spec_index(pagetable_ptr).view().higher
                    == (PageTableHigher { pci: self.pt_mp.spec_index(pagetable_ptr).view().higher.pci, ..old(self).pt_mp.spec_index(pagetable_ptr).view().higher }),
                self.pt_mp.spec_index(pagetable_ptr).view().lower_backup == old(self).pt_mp.spec_index(pagetable_ptr).view().lower_backup,
                forall|j: int| #![trigger self.pt_mp.spec_index(pagetable_ptr).view().higher.pci.spec_entry(j)]
                    0 <= j < i ==> !self.pt_mp.spec_index(pagetable_ptr).view().higher.pci.spec_entry(j).used,
                forall|j: int| #![trigger self.pt_mp.spec_index(pagetable_ptr).view().higher.pci.spec_entry(j)]
                    i <= j < PCI_FUNCTIONS_PER_PROCESS ==> self.pt_mp.spec_index(pagetable_ptr).view().higher.pci.spec_entry(j) == old(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci.spec_entry(j),
            decreases PCI_FUNCTIONS_PER_PROCESS - i,
        {
            broadcast use PciFunctionArray::wf_function_at, PciFunctionArray::wf_entry_at;
            proof { pagetable_perms_wf_map(self.pt_mp); pagetable_perms_wf_at(self.pt_mp, pagetable_ptr); }
            let used = self.pt_mp.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(lctx), Tracked(pagetable_perm)).higher.pci.entry(i).used;
            if used {
                proof { old(self).pt_mp.spec_index(pagetable_ptr).view().higher.pci.wf_entry_at(i as int); }
                let ghost cur = self.irt.view().owners();
                self.update_pci_entry(pagetable_ptr, i, PciEntryUpdate::Release, Tracked(lctx), Tracked(pagetable_perm), Tracked(irt_perm));
                proof {
                    let done = pci.view().dom().filter(|f: PciBdf| pci.index_of(f) < i);
                    if !released { assert(done =~= Set::<PciBdf>::empty()); }
                    release_pci_functions_eol_owners(old(self).irt.view().owners(), cur, self.irt.view().owners(), done, pci.spec_entry(i as int).bdf, released);
                    released = true;
                }
            }
            let ghost done = pci.view().dom().filter(|f: PciBdf| pci.index_of(f) < i);
            let ghost g = pci.spec_entry(i as int).bdf;
            i = i + 1;
            proof {
                if used { assert(pci.view().dom().filter(|f: PciBdf| pci.index_of(f) < i) =~= done.insert(g)); }
                else { assert(pci.view().dom().filter(|f: PciBdf| pci.index_of(f) < i) =~= done); }
            }
        }
        proof {
            pagetable_perms_wf_map(self.pt_mp);
            pagetable_perms_wf_at(self.pt_mp, pagetable_ptr);
            if !released { assert(pci.view().dom() =~= Set::<PciBdf>::empty()); }
            assert(pci.view().dom().filter(|f: PciBdf| pci.index_of(f) < PCI_FUNCTIONS_PER_PROCESS) =~= pci.view().dom());
        }
    }
}
} // verus!
