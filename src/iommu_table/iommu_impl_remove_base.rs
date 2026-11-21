use vstd::prelude::*;
verus! {
use crate::*;
use super::entry::*;
use super::page_map::*;
use vstd::simple_pptr::*;

impl IommuTable {
    /// First half of 4K unmap: make future page walks miss while retaining the kernel mapping record that backs any stale TLB entry. A caller must flush those entries before invoking `unmap_4k_page_kernel`.
    pub fn unmap_4k_page_user_view(&mut self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, Tracked(lctx): Tracked<&mut LocalContext>)
        requires
            old(self).wf(),
            pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            old(self).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            old(self).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            old(self).spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is Some || old(self).mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == true,
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            final(self).wf(),
            final(self).spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is Some,
            !final(self).spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i)->0.perm.present,
            !final(self).spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i)->0.perm.write,
            final(self).cr3 == old(self).cr3,
            final(self).proc_ptr == old(self).proc_ptr,
            final(self).did == old(self).did,
            final(self).page_closure() =~= old(self).page_closure(),
            final(self).mapping_4k() == old(self).mapping_4k().insert(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
                MapEntry { is_io: old(self).mapping_4k().spec_index(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))).is_io,
                    addr: old(self).mapping_4k().spec_index(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))).addr,
                    write: old(self).mapping_4k().spec_index(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))).write,
                    execute_disable: old(self).mapping_4k().spec_index(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))).execute_disable, present: false,
                    owning_container: old(self).mapping_4k().spec_index(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))).owning_container }),
    {
        let va = Ghost(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)));
        proof {
            self.wf_l4_at(target_l4i);
            self.wf_l3_at(self.spec_resolve_mapping_l4(target_l4i)->0.addr, target_l3i);
            self.wf_l2_at(self.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr, target_l2i);
            self.wf_l1_at(self.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr, target_l1i);
        }
        proof { self.wf_mapping_4k_at(target_l4i, target_l3i, target_l2i, target_l1i); }
        let tracked l1_perm = self.l1_tables.borrow().tracked_borrow(target_l1_p);
        let l1_tbl: &IommuPageMap = PPtr::<IommuPageMap>::from_usize(target_l1_p).borrow(Tracked(l1_perm));
        let mut l1_entry = l1_tbl.get(target_l1i);
        proof {
            let raw = l1_tbl.ar.view().spec_index(target_l1i as int);
            assert(!l1_entry.perm.is_io) by {
                l1_tbl.wf_at(target_l1i);
                assert(raw & PAGE_ENTRY_IO_MASK as usize == 0) by (bit_vector) requires raw & !IOMMU_WORD_MASK == 0;
            };
        }
        l1_entry.perm.present = false;
        l1_entry.perm.write = false;
        iommu_page_map_set_published_in_map(target_l1_p, Tracked(self.l1_tables.borrow_mut()), target_l1i, l1_entry, Tracked(&mut *lctx));
        proof {
            self.mapping_4k = Ghost(self.mapping_4k.view().insert(va.view(), MapEntry { is_io: old(self).mapping_4k.view().spec_index(va.view()).is_io,
                addr: old(self).mapping_4k.view().spec_index(va.view()).addr, write: old(self).mapping_4k.view().spec_index(va.view()).write,
                execute_disable: old(self).mapping_4k.view().spec_index(va.view()).execute_disable, present: false,
                owning_container: old(self).mapping_4k.view().spec_index(va.view()).owning_container }));
        }

        proof {
            assert(Self::unmap_4k_page_user_view_eof_transition_framing(*old(self), *self, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p)) by { reveal(IommuTable::unmap_4k_page_user_view_eof_transition_framing); };
            Self::unmap_4k_page_user_view_eof(*old(self), *self, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        }
    }

    /// Final half of 4K unmap: remove the kernel mapping only after its user present bit is clear, or from a table no device domain references (`did is None`), which no IOTLB can cache. Kernel-level callers must also show no stale IOTLB entry remains; restoring `iommu_tlb_wf` enforces it.
    pub fn unmap_4k_page_kernel(&mut self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, Tracked(lctx): Tracked<&mut LocalContext>)
        requires
            old(self).wf(),
            pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            old(self).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            old(self).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            old(self).mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            old(self).mapping_4k().spec_index(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))).present == false || old(self).did is None,
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            final(self).wf(),
            final(self).cr3 == old(self).cr3,
            final(self).proc_ptr == old(self).proc_ptr,
            final(self).did == old(self).did,
            final(self).page_closure() =~= old(self).page_closure(),
            final(self).mapping_4k.view() == old(self).mapping_4k.view().remove(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            final(self).spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None,
    {
        let va = Ghost(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)));
        proof {
            self.wf_l4_at(target_l4i);
            self.wf_l3_at(self.spec_resolve_mapping_l4(target_l4i)->0.addr, target_l3i);
            self.wf_l2_at(self.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr, target_l2i);
            self.wf_l1_at(self.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr, target_l1i);
        }
        let empty_entry = PageEntry::empty();
        assert(mem_valid(empty_entry.addr)) by { mem_valid_zero(); };
        iommu_page_map_set_published_in_map(target_l1_p, Tracked(self.l1_tables.borrow_mut()), target_l1i, empty_entry, Tracked(&mut *lctx));
        proof { self.mapping_4k = Ghost(self.mapping_4k.view().remove(va.view())); }

        proof {
            assert(Self::unmap_4k_page_kernel_eof_transition_framing(*old(self), *self, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p)) by { reveal(IommuTable::unmap_4k_page_kernel_eof_transition_framing); };
            Self::unmap_4k_page_kernel_eof(*old(self), *self, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        }
    }

    pub fn remove_l2_entry(&mut self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: (PageMapPtr, Tracked<PointsTo<IommuPageMap>>))
        requires
            old(self).wf(),
            pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            old(self).spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            old(self).spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            old(self).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            old(self).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i).unwrap().addr == target_l1_p,
            forall|i: L1Index| #![auto] pei_valid(i) ==> old(self).spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, i) is None,
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            final(self).wf(),
            final(self).page_closure() =~= old(self).page_closure().remove(target_l1_p),
            final(self).mapping_4k() =~= old(self).mapping_4k(),
            final(self).cr3 == old(self).cr3,
            final(self).did == old(self).did,
            final(self).proc_ptr == old(self).proc_ptr,
            ret.0 == target_l1_p,
            ret.1.view().is_init(),
            ret.1.view().addr() == target_l1_p,
    {
        proof {
            self.wf_l4_at(target_l4i);
            self.wf_l3_at(self.spec_resolve_mapping_l4(target_l4i)->0.addr, target_l3i);
            self.wf_l2_at(self.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr, target_l2i);
            self.wf_l1_at(self.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr, 0);
        }

        let tracked mut l2_perm = self.l2_tables.borrow_mut().tracked_remove(target_l2_p);
        assert(mem_valid(0)) by { mem_valid_zero(); };
        iommu_page_map_set_published(target_l2_p, Tracked(&mut l2_perm), target_l2i,
            PageEntry { addr: 0, perm: PageEntryPerm { is_io: false, present: false, ps: false, write: false, execute_disable: false, user: false, kernel_present: false } },
            Tracked(&mut *lctx));
        proof { self.l2_tables.borrow_mut().tracked_insert(target_l2_p, l2_perm); self.l1_rev_map = Ghost(self.l1_rev_map.view().remove(target_l1_p)); }
        let tracked mut l1_perm = self.l1_tables.borrow_mut().tracked_remove(target_l1_p);
        let ret = (target_l1_p, Tracked(l1_perm));
        proof {
            assert(Self::remove_l2_entry_eof_transition_framing(*old(self), *self, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p, ret.1.view())) by { reveal(IommuTable::remove_l2_entry_eof_transition_framing); };
            Self::remove_l2_entry_eof_implies_wf(*old(self), *self, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p, ret.1.view());
        }
        return ret;
    }

    pub fn remove_l3_entry(&mut self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_l2_p: PageMapPtr, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: (PageMapPtr, Tracked<PointsTo<IommuPageMap>>))
        requires
            old(self).wf(),
            pei_valid(target_l4i),
            pei_valid(target_l3i),
            old(self).spec_resolve_mapping_l4(target_l4i) is Some,
            old(self).spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            old(self).spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            old(self).spec_resolve_mapping_l3(target_l4i, target_l3i).unwrap().addr == target_l2_p,
            forall|i: L2Index| #![auto] pei_valid(i) ==> old(self).spec_resolve_mapping_l2(target_l4i, target_l3i, i) is None,
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            final(self).wf(),
            final(self).page_closure() =~= old(self).page_closure().remove(target_l2_p),
            final(self).mapping_4k() =~= old(self).mapping_4k(),
            final(self).cr3 == old(self).cr3,
            final(self).did == old(self).did,
            final(self).proc_ptr == old(self).proc_ptr,
            ret.0 == target_l2_p,
            ret.1.view().is_init(),
            ret.1.view().addr() == target_l2_p,
    {
        proof {
            self.wf_l4_at(target_l4i);
            self.wf_l3_at(self.spec_resolve_mapping_l4(target_l4i)->0.addr, target_l3i);
            self.wf_l2_at(self.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr, 0);
        }

        let tracked mut l3_perm = self.l3_tables.borrow_mut().tracked_remove(target_l3_p);
        assert(mem_valid(0)) by { mem_valid_zero(); };
        iommu_page_map_set_published(target_l3_p, Tracked(&mut l3_perm), target_l3i,
            PageEntry { addr: 0, perm: PageEntryPerm { is_io: false, present: false, ps: false, write: false, execute_disable: false, user: false, kernel_present: false } },
            Tracked(&mut *lctx));
        proof { self.l3_tables.borrow_mut().tracked_insert(target_l3_p, l3_perm); self.l2_rev_map = Ghost(self.l2_rev_map.view().remove(target_l2_p)); }
        let tracked mut l2_perm = self.l2_tables.borrow_mut().tracked_remove(target_l2_p);
        let ret = (target_l2_p, Tracked(l2_perm));
        proof {
            assert(Self::remove_l3_entry_eof_transition_framing(*old(self), *self, target_l4i, target_l3i, target_l3_p, target_l2_p, ret.1.view())) by { reveal(IommuTable::remove_l3_entry_eof_transition_framing); };
            Self::remove_l3_entry_eof_implies_wf(*old(self), *self, target_l4i, target_l3i, target_l3_p, target_l2_p, ret.1.view());
        }
        return ret;
    }

    pub fn remove_l4_entry(&mut self, target_l4i: L4Index, target_l3_p: PageMapPtr, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: (PageMapPtr, Tracked<PointsTo<IommuPageMap>>))
        requires
            old(self).wf(),
            pei_valid(target_l4i),
            old(self).spec_resolve_mapping_l4(target_l4i) is Some,
            old(self).spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            forall|i: L3Index| #![auto] pei_valid(i) ==> old(self).spec_resolve_mapping_l3(target_l4i, i) is None,
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            final(self).wf(),
            final(self).page_closure() =~= old(self).page_closure().remove(target_l3_p),
            final(self).mapping_4k() =~= old(self).mapping_4k(),
            final(self).cr3 == old(self).cr3,
            final(self).did == old(self).did,
            final(self).proc_ptr == old(self).proc_ptr,
            ret.0 == target_l3_p,
            ret.1.view().is_init(),
            ret.1.view().addr() == target_l3_p,
    {
        proof {
            self.wf_l4_at(target_l4i);
            self.wf_l3_at(self.spec_resolve_mapping_l4(target_l4i)->0.addr, 0);
        }

        let tracked mut l4_perm = self.l4_table.borrow_mut().tracked_remove(self.cr3);
        let zero_entry = PageEntry { addr: 0, perm: PageEntryPerm { is_io: false, present: false, ps: false, write: false, execute_disable: false, user: false, kernel_present: false } };
        assert(mem_valid(zero_entry.addr)) by { mem_valid_zero(); };
        iommu_page_map_set_published(self.cr3, Tracked(&mut l4_perm), target_l4i, zero_entry, Tracked(&mut *lctx));
        proof { self.l4_table.borrow_mut().tracked_insert(self.cr3, l4_perm); self.l3_rev_map = Ghost(self.l3_rev_map.view().remove(target_l3_p)); }
        let tracked mut l3_perm = self.l3_tables.borrow_mut().tracked_remove(target_l3_p);
        let ret = (target_l3_p, Tracked(l3_perm));
        proof {
            assert(Self::remove_l4_entry_eof_transition_framing(*old(self), *self, target_l4i, target_l3_p)) by { reveal(IommuTable::remove_l4_entry_eof_transition_framing); };
            Self::remove_l4_entry_eof(*old(self), *self, target_l4i, target_l3_p);
        }
        return ret;
    }
}
} // verus!
