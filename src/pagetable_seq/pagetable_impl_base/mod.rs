use vstd::prelude::*;
verus! {

use super::pagemap_util_t::*;
use crate::util::page_ptr_util_u::*;
use super::pagetable_spec::*;
use super::pagemap::*;
use super::entry::*;
use crate::define::*;
use crate::locks::*;
use crate::iommu::iova_4k_valid;
use vstd::simple_pptr::*;
use crate::lemma::lemma_u::*;

// exec
impl<const TABLE_TYPE:PTType> PageTable<TABLE_TYPE> {
    pub fn get_entry_l4(&self, target_l4i: L4Index) -> (ret: Option<PageEntry>)
        requires
            self.wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
        ensures
            self.spec_resolve_mapping_l4(target_l4i) == ret,
            forall|l3i: L3Index, l2i: L2Index, l1i: L1Index|
                #![trigger spec_index2va((target_l4i, l3i, l2i, l1i))]
                #![trigger self.spec_resolve_mapping_4k_l1(target_l4i, l3i, l2i, l1i)]
                pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && ret is None
                    ==> self.spec_resolve_mapping_4k_l1(target_l4i, l3i, l2i, l1i) is None
                    && self.mapping_4k().dom().contains(spec_index2va((target_l4i, l3i, l2i, l1i)))
                    == false,
    {
        assert({
            &&& self.l4_table.view().dom().contains(self.cr3)
            &&& self.l4_table.view().spec_index(self.cr3).addr() == self.cr3
            &&& self.l4_table.view().spec_index(self.cr3).is_init()
            &&& self.l4_table.view().spec_index(self.cr3).value().wf()
        }) by {
            reveal(PageTable::wf_l4);
        };
        let tracked l4_perm = self.l4_table.borrow().tracked_borrow(self.cr3);
        let l4_tbl: &PageMap = PPtr::<PageMap>::from_usize(self.cr3).borrow(Tracked(l4_perm));
        let l4_entry = l4_tbl.get(target_l4i);
        let ret = if l4_entry.perm.present {
            Some(l4_entry)
        } else {
            None
        };
        assert(forall|l3i: L3Index, l2i: L2Index, l1i: L1Index|
            #![trigger spec_index2va((target_l4i, l3i, l2i, l1i))]
            #![trigger self.spec_resolve_mapping_4k_l1(target_l4i, l3i, l2i, l1i)]
            pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && ret is None
                ==> self.spec_resolve_mapping_4k_l1(target_l4i, l3i, l2i, l1i) is None
                && self.mapping_4k().dom().contains(
                    spec_index2va((target_l4i, l3i, l2i, l1i)),
                ) == false
        ) by {
            reveal(PageTable::wf_mapping_4k);
        };
        ret
    }

    pub fn get_entry_l3(
        &self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        l4_entry: &PageEntry,
    ) -> (ret: Option<PageEntry>)
        requires
            self.wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            self.spec_resolve_mapping_l4(target_l4i) =~= Some(*l4_entry),
        ensures
            self.spec_resolve_mapping_l3(target_l4i, target_l3i) =~= ret,
            forall|l2i: L2Index, l1i: L1Index|
                #![trigger spec_index2va((target_l4i, target_l3i, l2i, l1i))]
                #![trigger self.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, l2i, l1i)]
                pei_valid(l2i) && pei_valid(l1i) && ret is None
                    ==> self.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, l2i, l1i) is None
                    && self.mapping_4k().dom().contains(
                    spec_index2va((target_l4i, target_l3i, l2i, l1i)),
                ) == false,
            ret is Some ==> self.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
    {
        assert({
            &&& self.l3_tables.view().dom().contains(l4_entry.addr)
            &&& self.l3_tables.view().spec_index(l4_entry.addr).addr() == l4_entry.addr
            &&& self.l3_tables.view().spec_index(l4_entry.addr).is_init()
            &&& self.l3_tables.view().spec_index(l4_entry.addr).value().wf()
        }) by {
            reveal(PageTable::wf_l4);
            reveal(PageTable::wf_l3);
        };
        let tracked l3_perm = self.l3_tables.borrow().tracked_borrow(l4_entry.addr);
        let l3_tbl: &PageMap = PPtr::<PageMap>::from_usize(l4_entry.addr).borrow(Tracked(l3_perm));
        let l3_entry = l3_tbl.get(target_l3i);
        let ret = if l3_entry.perm.present && !l3_entry.perm.ps {
            Some(l3_entry)
        } else {
            None
        };
        assert(forall|l2i: L2Index, l1i: L1Index|
            #![trigger spec_index2va((target_l4i, target_l3i, l2i, l1i))]
            #![trigger self.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, l2i, l1i)]
            pei_valid(l2i) && pei_valid(l1i) && ret is None
                ==> self.spec_resolve_mapping_4k_l1(
                    target_l4i, target_l3i, l2i, l1i,
                ) is None
                && self.mapping_4k().dom().contains(
                    spec_index2va((target_l4i, target_l3i, l2i, l1i)),
                ) == false
        ) by {
            reveal(PageTable::wf_mapping_4k);
        };
        ret
    }

    pub fn get_entry_1g_l3(
        &self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        l4_entry: &PageEntry,
    ) -> (ret: Option<PageEntry>)
        requires
            self.wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            self.spec_resolve_mapping_l4(target_l4i) =~= Some(*l4_entry),
        ensures
            self.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) =~= ret,
    {
        assert({
            &&& self.l3_tables.view().dom().contains(l4_entry.addr)
            &&& self.l3_tables.view().spec_index(l4_entry.addr).addr() == l4_entry.addr
            &&& self.l3_tables.view().spec_index(l4_entry.addr).is_init()
            &&& self.l3_tables.view().spec_index(l4_entry.addr).value().wf()
        }) by {
            reveal(PageTable::wf_l4);
            reveal(PageTable::wf_l3);
        };

        let tracked l3_perm = self.l3_tables.borrow().tracked_borrow(l4_entry.addr);
        let l3_tbl: &PageMap = PPtr::<PageMap>::from_usize(l4_entry.addr).borrow(Tracked(l3_perm));
        let l3_entry = l3_tbl.get(target_l3i);
        if l3_entry.perm.ps && l3_entry.perm.kernel_present {
            Some(l3_entry)
        } else {
            None
        }
    }

    pub fn get_entry_l2(
        &self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        l3_entry: &PageEntry,
    ) -> (ret: Option<PageEntry>)
        requires
            self.wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            self.spec_resolve_mapping_l3(target_l4i, target_l3i) =~= Some(*l3_entry),
        ensures
            self.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) =~= ret,
            forall|l1i: L1Index|
                #![trigger spec_index2va((target_l4i, target_l3i, target_l2i, l1i))]
                #![trigger self.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, l1i)]
                pei_valid(l1i) && ret is None ==> self.spec_resolve_mapping_4k_l1(
                    target_l4i,
                    target_l3i,
                    target_l2i,
                    l1i,
                ) is None && self.mapping_4k().dom().contains(
                    spec_index2va((target_l4i, target_l3i, target_l2i, l1i)),
                ) == false,
    {
        assert({
            &&& self.l2_tables.view().dom().contains(l3_entry.addr)
            &&& self.l2_tables.view().spec_index(l3_entry.addr).addr() == l3_entry.addr
            &&& self.l2_tables.view().spec_index(l3_entry.addr).is_init()
            &&& self.l2_tables.view().spec_index(l3_entry.addr).value().wf()
        }) by {
            reveal(PageTable::wf_l4);
            reveal(PageTable::wf_l3);
            reveal(PageTable::wf_l2);
        };
        let tracked l2_perm = self.l2_tables.borrow().tracked_borrow(l3_entry.addr);
        let l2_tbl: &PageMap = PPtr::<PageMap>::from_usize(l3_entry.addr).borrow(Tracked(l2_perm));
        let l2_entry = l2_tbl.get(target_l2i);
        let ret = if l2_entry.perm.present && !l2_entry.perm.ps {
            Some(l2_entry)
        } else {
            None
        };
        assert(forall|l1i: L1Index|
            #![trigger spec_index2va((target_l4i, target_l3i, target_l2i, l1i))]
            #![trigger self.spec_resolve_mapping_4k_l1(
                target_l4i, target_l3i, target_l2i, l1i,
            )]
            pei_valid(l1i) && ret is None ==> self.spec_resolve_mapping_4k_l1(
                target_l4i,
                target_l3i,
                target_l2i,
                l1i,
            ) is None && self.mapping_4k().dom().contains(
                spec_index2va((target_l4i, target_l3i, target_l2i, l1i)),
            ) == false
        ) by {
            reveal(PageTable::wf_mapping_4k);
        };
        ret
    }

    pub fn get_entry_2m_l2(
        &self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        l3_entry: &PageEntry,
    ) -> (ret: Option<PageEntry>)
        requires
            self.wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            self.spec_resolve_mapping_l3(target_l4i, target_l3i) =~= Some(*l3_entry),
        ensures
            self.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) =~= ret,
    {
        assert({
            &&& self.l2_tables.view().dom().contains(l3_entry.addr)
            &&& self.l2_tables.view().spec_index(l3_entry.addr).addr() == l3_entry.addr
            &&& self.l2_tables.view().spec_index(l3_entry.addr).is_init()
            &&& self.l2_tables.view().spec_index(l3_entry.addr).value().wf()
        }) by {
            reveal(PageTable::wf_l4);
            reveal(PageTable::wf_l3);
            reveal(PageTable::wf_l2);
        };

        let tracked l2_perm = self.l2_tables.borrow().tracked_borrow(l3_entry.addr);
        let l2_tbl: &PageMap = PPtr::<PageMap>::from_usize(l3_entry.addr).borrow(Tracked(l2_perm));
        let l2_entry = l2_tbl.get(target_l2i);
        if l2_entry.perm.kernel_present && l2_entry.perm.ps {
            Some(l2_entry)
        } else {
            None
        }
    }

    pub fn get_entry_l1(
        &self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l1i: L2Index,
        l2_entry: &PageEntry,
    ) -> (ret: Option<PageEntry>)
        requires
            self.wf(),
            self.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            self.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) =~= Some(*l2_entry),
        ensures
            self.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) =~= ret,
            self.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),) =~= ret is Some,
            ret is Some
                ==> self.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)))
                && self.mapping_4k().spec_index(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == page_entry_to_map_entry(&ret.unwrap()),
    {
        assert({
            &&& self.l1_tables.view().dom().contains(l2_entry.addr)
            &&& self.l1_tables.view().spec_index(l2_entry.addr).addr() == l2_entry.addr
            &&& self.l1_tables.view().spec_index(l2_entry.addr).is_init()
            &&& self.l1_tables.view().spec_index(l2_entry.addr).value().wf()
        }) by {
            reveal(PageTable::wf_l4);
            reveal(PageTable::wf_l3);
            reveal(PageTable::wf_l2);
            reveal(PageTable::wf_l1);
        };
        assert({
            &&& self.mapping_4k().dom().contains(spec_index2va((
                target_l4i,
                target_l3i,
                target_l2i,
                target_l1i,
            ))) == self.spec_resolve_mapping_4k_l1(
                target_l4i,
                target_l3i,
                target_l2i,
                target_l1i,
            ) is Some
            &&& self.spec_resolve_mapping_4k_l1(
                target_l4i,
                target_l3i,
                target_l2i,
                target_l1i,
            ) is Some ==> self.mapping_4k().spec_index(spec_index2va((
                target_l4i,
                target_l3i,
                target_l2i,
                target_l1i,
            ))) == page_entry_to_map_entry(&self.spec_resolve_mapping_4k_l1(
                target_l4i,
                target_l3i,
                target_l2i,
                target_l1i,
            )->0)
        }) by {
            reveal(PageTable::wf_mapping_4k);
        };

        let tracked l1_perm = self.l1_tables.borrow().tracked_borrow(l2_entry.addr);
        let l1_tbl: &PageMap = PPtr::<PageMap>::from_usize(l2_entry.addr).borrow(Tracked(l1_perm));
        let l1_entry = l1_tbl.get(target_l1i);
        if l1_entry.perm.kernel_present {
            Some(l1_entry)
        } else {
            None
        }
    }

    pub fn create_entry_l4(
        &mut self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        page_map_ptr: PageMapPtr,
        Tracked(page_map_perm): Tracked<PointsTo<PageMap>>,
        Tracked(lctx): Tracked<&mut LocalContext>,
    )
        requires
            old(self).wf(),
            old(self).kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            old(self).spec_resolve_mapping_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            old(self).page_closure().contains(page_map_ptr) == false,
            // old(self).page_not_mapped(page_map_ptr),
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i: usize|
                #![trigger page_map_perm.value().spec_index(i)]
                pei_valid(i) ==> page_map_perm.value().spec_index(i).is_empty(),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            page_map_write_lctx_ensures(old(lctx), final(lctx)),
            final(lctx).stable_lock_id_set() == old(lctx).stable_lock_id_set(),
            final(self).wf(),
            final(self).kernel_l4_end == old(self).kernel_l4_end,
            final(self).pcid == old(self).pcid,
            final(self).cr3 == old(self).cr3,
            final(self).proc_ptr == old(self).proc_ptr,
            final(self).page_closure() =~= old(self).page_closure().insert(page_map_ptr),
            final(self).mapping_4k() =~= old(self).mapping_4k(),
            final(self).mapping_2m() =~= old(self).mapping_2m(),
            final(self).mapping_1g() =~= old(self).mapping_1g(),
            final(self).spec_resolve_mapping_l4(target_l4i) is Some,
            final(self).spec_resolve_mapping_l4(target_l4i)->0.addr == page_map_ptr,
            final(self).spec_resolve_mapping_l3(target_l4i, target_l3i) is None,
            final(self).spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            final(self).kernel_entries =~= old(self).kernel_entries,
    {
        assert({
            &&& self.l4_table.view().dom().contains(self.cr3)
            &&& self.l4_table.view().spec_index(self.cr3).addr() == self.cr3
            &&& self.l4_table.view().spec_index(self.cr3).is_init()
            &&& self.l4_table.view().spec_index(self.cr3).value().wf()
        }) by {
            reveal(PageTable::wf_l4);
        };
        assert(mem_valid(page_map_ptr)) by {
            page_ptr_valid_imply_mem_valid(page_map_ptr);
        };
        page_map_set_published_in_map(
            self.cr3,
            Tracked(self.l4_table.borrow_mut()),
            target_l4i,
            PageEntry {
                addr: page_map_ptr,
                perm: PageEntryPerm {
                    present: true,
                    ps: false,
                    write: true,
                    execute_disable: false,
                    user: true,
                    kernel_present: false,
                },
            },
            Tracked(&mut *lctx),
        );
        proof {
            self.l3_tables.borrow_mut().tracked_insert(page_map_ptr, page_map_perm);
            self.l3_rev_map = Ghost(self.l3_rev_map.view().insert(page_map_ptr, target_l4i));
        }
        assert(self.wf_l4()) by {
            reveal(PageTable::wf_l4);
        };
        assert(self.wf_l3()) by {
            reveal(PageTable::wf_l3);
        };
        assert(self.wf_l2()) by {
            reveal(PageTable::wf_l2);
        };
        assert(self.wf_l1()) by {
            reveal(PageTable::wf_l1);
        };
        assert(self.disjoint_l4()) by {
            reveal(PageTable::disjoint_l4);
            reveal(PageTable::wf_l4);
        };
        assert(self.disjoint_l3()) by {
            reveal(PageTable::disjoint_l3);
        };
        assert(self.disjoint_l2()) by {
            reveal(PageTable::disjoint_l2);
        };
        assert(self.wf_mapping_4k()) by {
            assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L2Index|
                #![trigger self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                #![trigger old(self).spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i)
                    && pei_valid(l3i)
                    && pei_valid(l2i)
                    && pei_valid(l1i)
                    ==>
                    old(self).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)) by {
                reveal(PageTable::wf_l4);
                reveal(PageTable::wf_l3);
                reveal(PageTable::wf_l2);
            };
            reveal(PageTable::wf_mapping_4k);
        };
        assert(self.wf_mapping_2m()) by {
            assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                #![trigger old(self).spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i)
                    && pei_valid(l3i)
                    && pei_valid(l2i)
                    ==>
                    old(self).spec_resolve_mapping_2m_l2(l4i, l3i, l2i) == self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)) by {
                reveal(PageTable::wf_l4);
                reveal(PageTable::wf_l3);
                reveal(PageTable::wf_l2);
            };
            reveal(PageTable::wf_mapping_2m);
        };
        assert(self.wf_mapping_1g()) by {
            assert(forall|l4i: L4Index, l3i: L3Index|
                #![trigger self.spec_resolve_mapping_1g_l3(l4i,l3i)]
                #![trigger old(self).spec_resolve_mapping_1g_l3(l4i,l3i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i)
                    && pei_valid(l3i)
                    ==>
                    old(self).spec_resolve_mapping_1g_l3(l4i, l3i) == self.spec_resolve_mapping_1g_l3(l4i, l3i)
                ) by {
                reveal(PageTable::wf_l4);
                reveal(PageTable::wf_l3);
            };
            reveal(PageTable::wf_mapping_1g);
        };
        assert(self.user_only()) by {
            reveal(PageTable::user_only);
        };
        assert(self.rwx_upper_level_entries()) by {
            reveal(PageTable::rwx_upper_level_entries);
        };
        assert(self.table_pages_wf()) by {
            reveal(PageTable::table_pages_wf);
        };
        assert(self.kernel_entries_wf()) by {
            reveal(PageTable::kernel_entries_wf);
        };
    }

    pub fn create_entry_l3(
        &mut self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l3_p: PageMapPtr,
        page_map_ptr: PageMapPtr,
        Tracked(page_map_perm): Tracked<PointsTo<PageMap>>,
        Tracked(lctx): Tracked<&mut LocalContext>,
    )
        requires
            old(self).wf(),
            old(self).kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            old(self).spec_resolve_mapping_l4(target_l4i) is Some,
            old(self).spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            old(self).spec_resolve_mapping_l3(target_l4i, target_l3i) is None,
            old(self).spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_valid(page_map_ptr),
            old(self).page_closure().contains(page_map_ptr) == false,
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i: usize|
                #![trigger page_map_perm.value().spec_index(i).is_empty()]
                pei_valid(i)
                ==>
                page_map_perm.value().spec_index(i).is_empty(),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            page_map_write_lctx_ensures(old(lctx), final(lctx)),
            final(lctx).stable_lock_id_set() == old(lctx).stable_lock_id_set(),
            final(self).wf(),
            final(self).kernel_l4_end == old(self).kernel_l4_end,
            final(self).pcid == old(self).pcid,
            final(self).cr3 == old(self).cr3,
            final(self).proc_ptr == old(self).proc_ptr,
            final(self).page_closure() =~= old(self).page_closure().insert(page_map_ptr),
            final(self).mapping_4k() =~= old(self).mapping_4k(),
            final(self).mapping_2m() =~= old(self).mapping_2m(),
            final(self).mapping_1g() =~= old(self).mapping_1g(),
            final(self).spec_resolve_mapping_l4(target_l4i) == old(self).spec_resolve_mapping_l4(
                target_l4i,
            ),
            final(self).spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            final(self).spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == page_map_ptr,
            final(self).spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            final(self).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            final(self).spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None,
            final(self).kernel_entries =~= old(self).kernel_entries,
    {
        assert(forall|i: usize|
            #![trigger page_map_perm.value().spec_index(i).is_empty()]
            #![trigger page_map_perm.value().spec_index(i).perm.present]
            #![trigger page_map_perm.value().spec_index(i).perm.ps]
            pei_valid(i)
            ==>
                page_map_perm.value().spec_index(i).is_empty()
                && page_map_perm.value().spec_index(i).perm.present == false
                && page_map_perm.value().spec_index(i).perm.write == false
                && page_map_perm.value().spec_index(i).perm.execute_disable == false
                && page_map_perm.value().spec_index(i).perm.ps == false
            );
        assert(old(self).spec_resolve_mapping_l4(target_l4i)->0.perm.present
            && !old(self).spec_resolve_mapping_l4(target_l4i)->0.perm.ps
            && old(self).spec_resolve_mapping_l4(target_l4i)->0.perm.write
            && !old(self).spec_resolve_mapping_l4(target_l4i)->0.perm.execute_disable) by {
            reveal(PageTable::wf_l4);
            reveal(PageTable::rwx_upper_level_entries);
        };
        assert({
            &&& self.l3_tables.view().dom().contains(target_l3_p)
            &&& self.l3_tables.view().spec_index(target_l3_p).addr() == target_l3_p
            &&& self.l3_tables.view().spec_index(target_l3_p).is_init()
            &&& self.l3_tables.view().spec_index(target_l3_p).value().wf()
        }) by {
            reveal(PageTable::wf_l4);
            reveal(PageTable::wf_l3);
        };

        assert(mem_valid(page_map_ptr)) by {
            page_ptr_valid_imply_mem_valid(page_map_ptr);
        };
        page_map_set_published_in_map(
            target_l3_p,
            Tracked(self.l3_tables.borrow_mut()),
            target_l3i,
            PageEntry {
                addr: page_map_ptr,
                perm: PageEntryPerm {
                    present: true,
                    ps: false,
                    write: true,
                    execute_disable: false,
                    user: true,
                    kernel_present: true,
                },
            },
            Tracked(&mut *lctx),
        );
        proof {
            self.l2_tables.borrow_mut().tracked_insert(page_map_ptr, page_map_perm);
            self.l2_rev_map = Ghost(self.l2_rev_map.view().insert(page_map_ptr, (target_l4i, target_l3i)));
        }
        assert(self.wf_l4()) by {
            reveal(PageTable::wf_l4);
        };
        assert(self.wf_l3()) by {
            reveal(PageTable::wf_l3);
        };
        assert(self.wf_l2()) by {
            reveal(PageTable::wf_l2);
        };
        assert(self.wf_l1()) by {
            reveal(PageTable::wf_l1);
        };
        assert(self.disjoint_l4()) by {
            reveal(PageTable::disjoint_l4);
        };
        assert(self.disjoint_l3()) by {
            reveal(PageTable::disjoint_l3);
            reveal(PageTable::wf_l3);
        };
        assert(self.disjoint_l2()) by {
            reveal(PageTable::disjoint_l2);
        };
        assert(self.wf_mapping_4k()) by {
            assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L2Index|
                #![trigger self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                #![trigger old(self).spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i)
                    && pei_valid(l3i)
                    && pei_valid(l2i)
                    && pei_valid(l1i)
                    ==>
                    old(self).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)) by {
                reveal(PageTable::wf_l4);
                reveal(PageTable::wf_l3);
                reveal(PageTable::wf_l2);
            };
            reveal(PageTable::wf_mapping_4k);
        };
        assert(self.wf_mapping_2m()) by {
            assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                #![trigger old(self).spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i)
                    && pei_valid(l3i)
                    && pei_valid(l2i)
                    ==>
                    old(self).spec_resolve_mapping_2m_l2(l4i, l3i, l2i) == self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)) by {
                reveal(PageTable::wf_l4);
                reveal(PageTable::wf_l3);
            };
            reveal(PageTable::wf_mapping_2m);
        };
        assert(self.wf_mapping_1g()) by {
            assert(forall|l4i: L4Index, l3i: L3Index|
                #![trigger self.spec_resolve_mapping_1g_l3(l4i,l3i)]
                #![trigger old(self).spec_resolve_mapping_1g_l3(l4i,l3i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i)
                    && pei_valid(l3i)
                    && (l4i, l3i) != (target_l4i,target_l3i)
                    ==>
                    old(self).spec_resolve_mapping_1g_l3(l4i, l3i) =~= self.spec_resolve_mapping_1g_l3(l4i, l3i)) by {
                reveal(PageTable::wf_l4);
                reveal(PageTable::wf_l3);
            };
            reveal(PageTable::wf_mapping_1g);
        };
        assert(self.user_only()) by {
            reveal(PageTable::user_only);
        };
        assert(self.rwx_upper_level_entries()) by {
            reveal(PageTable::rwx_upper_level_entries);
        };
        assert(self.table_pages_wf()) by {
            reveal(PageTable::table_pages_wf);
        };
        assert(self.kernel_entries_wf()) by {
            reveal(PageTable::kernel_entries_wf);
        };
    }

    pub fn create_entry_l2(
        &mut self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l2_p: PageMapPtr,
        page_map_ptr: PageMapPtr,
        Tracked(page_map_perm): Tracked<PointsTo<PageMap>>,
        Tracked(lctx): Tracked<&mut LocalContext>,
    )
        requires
            old(self).wf(),
            old(self).kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            old(self).spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            old(self).spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr
                == target_l2_p,
            old(self).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            old(self).spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None,
            page_ptr_valid(page_map_ptr),
            old(self).page_closure().contains(page_map_ptr) == false,
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i: usize|
                #![trigger page_map_perm.value().spec_index(i).is_empty()]
                pei_valid(i) ==> page_map_perm.value().spec_index(i).is_empty(),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            page_map_write_lctx_ensures(old(lctx), final(lctx)),
            final(lctx).stable_lock_id_set() == old(lctx).stable_lock_id_set(),
            final(self).wf(),
            final(self).kernel_l4_end == old(self).kernel_l4_end,
            final(self).pcid == old(self).pcid,
            final(self).cr3 == old(self).cr3,
            final(self).proc_ptr == old(self).proc_ptr,
            final(self).page_closure() =~= old(self).page_closure().insert(page_map_ptr),
            final(self).mapping_4k() =~= old(self).mapping_4k(),
            final(self).mapping_2m() =~= old(self).mapping_2m(),
            final(self).mapping_1g() =~= old(self).mapping_1g(),
            final(self).spec_resolve_mapping_l4(target_l4i)
                == old(self).spec_resolve_mapping_l4(target_l4i),
            final(self).spec_resolve_mapping_l3(target_l4i, target_l3i)
                == old(self).spec_resolve_mapping_l3(target_l4i, target_l3i),
            final(self).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            final(self).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr
                == page_map_ptr,
            final(self).spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None,
            final(self).kernel_entries =~= old(self).kernel_entries,
    {
        assert(forall|i: usize|
            #![trigger page_map_perm.value().spec_index(i).is_empty()]
            #![trigger page_map_perm.value().spec_index(i).perm.present]
            #![trigger page_map_perm.value().spec_index(i).perm.ps]
            #![trigger page_map_perm.value().spec_index(i).perm.kernel_present]
            pei_valid(i) ==> page_map_perm.value().spec_index(i).is_empty()
                && page_map_perm.value().spec_index(i).perm.present == false
                && page_map_perm.value().spec_index(i).perm.write == false
                && page_map_perm.value().spec_index(i).perm.execute_disable == false
                && page_map_perm.value().spec_index(i).perm.ps == false
                && page_map_perm.value().spec_index(i).perm.kernel_present == false
            )
        by{
            assert(
                forall|i: usize|
                    #![trigger page_map_perm.value().spec_index(i)]
                    pei_valid(i) ==> page_map_perm.value().spec_index(i).is_empty()
            );
        };
        assert(old(self).spec_resolve_mapping_l4(target_l4i)->0.perm.present &&
                !old(self).spec_resolve_mapping_l4(target_l4i)->0.perm.ps &&
                 old(self).spec_resolve_mapping_l4(target_l4i)->0.perm.write &&
                 !old(self).spec_resolve_mapping_l4(target_l4i)->0.perm.execute_disable) by {
            reveal(PageTable::wf_l4);
            reveal(PageTable::rwx_upper_level_entries);
        };
        assert(old(self).spec_resolve_mapping_l3(target_l4i, target_l3i)->0.perm.present
            && !old(self).spec_resolve_mapping_l3(target_l4i, target_l3i)->0.perm.ps
            && old(self).spec_resolve_mapping_l3(target_l4i, target_l3i)->0.perm.write
            && !old(self).spec_resolve_mapping_l3(target_l4i,target_l3i,)->0.perm.execute_disable) by {
            reveal(PageTable::wf_l4);
            reveal(PageTable::rwx_upper_level_entries);
        };
        assert({
            &&& self.l2_tables.view().dom().contains(target_l2_p)
            &&& self.l2_tables.view().spec_index(target_l2_p).addr() == target_l2_p
            &&& self.l2_tables.view().spec_index(target_l2_p).is_init()
            &&& self.l2_tables.view().spec_index(target_l2_p).value().wf()
        }) by {
            reveal(PageTable::wf_l4);
            reveal(PageTable::wf_l3);
            reveal(PageTable::wf_l2);
        };

        assert(mem_valid(page_map_ptr)) by {
            page_ptr_valid_imply_mem_valid(page_map_ptr);
        };
        page_map_set_published_in_map(
            target_l2_p,
            Tracked(self.l2_tables.borrow_mut()),
            target_l2i,
            PageEntry {
                addr: page_map_ptr,
                perm: PageEntryPerm {
                    present: true,
                    ps: false,
                    write: true,
                    execute_disable: false,
                    user: true,
                    kernel_present: true,
                },
            },
            Tracked(&mut *lctx),
        );
        proof {
            self.l1_tables.borrow_mut().tracked_insert(page_map_ptr, page_map_perm);
            self.l1_rev_map = Ghost(self.l1_rev_map.view().insert(
                page_map_ptr,
                (target_l4i, target_l3i, target_l2i),
            ));
        }
        assert(self.wf_l4()) by {
            reveal(PageTable::wf_l4);
        };
        assert(self.wf_l3()) by {
            reveal(PageTable::wf_l3);
        };
        assert(self.wf_l2()) by {
            reveal(PageTable::wf_l2);
        };
        assert(self.wf_l1()) by {
            reveal(PageTable::wf_l1);
        };
        assert(self.disjoint_l4()) by {
            reveal(PageTable::disjoint_l4);
        };
        assert(self.disjoint_l3()) by {
            reveal(PageTable::disjoint_l3);
        };
        assert(self.disjoint_l2()) by {
            reveal(PageTable::disjoint_l2);
            reveal(PageTable::wf_l2);
        };
        assert(self.wf_mapping_4k()) by {
            assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L2Index|
                #![trigger self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                #![trigger old(self).spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i)
                    && pei_valid(l3i)
                    && pei_valid(l2i)
                    && pei_valid(l1i)
                    ==>
                    old(self).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)) by {
                reveal(PageTable::wf_l4);
                reveal(PageTable::wf_l3);
                reveal(PageTable::wf_l2);
            };
            reveal(PageTable::wf_mapping_4k);
        };
        assert(self.wf_mapping_2m()) by {
            assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                #![trigger old(self).spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i)
                    && pei_valid(l3i)
                    && pei_valid(l2i)
                    ==>
                    old(self).spec_resolve_mapping_2m_l2(l4i, l3i, l2i) == self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)) by {
                reveal(PageTable::wf_l4);
                reveal(PageTable::wf_l3);
                reveal(PageTable::wf_l2);
            };
            reveal(PageTable::wf_mapping_2m);
        };
        assert(self.wf_mapping_1g()) by {
            reveal(PageTable::wf_mapping_1g);
        };
        assert(self.user_only()) by {
            reveal(PageTable::user_only);
        };
        assert(self.rwx_upper_level_entries()) by {
            reveal(PageTable::rwx_upper_level_entries);
        };
        assert(self.table_pages_wf()) by {
            reveal(PageTable::table_pages_wf);
        };
        assert(self.kernel_entries_wf()) by {
            reveal(PageTable::kernel_entries_wf);
        };
    }

    pub fn map_4k_page(
        &mut self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l1i: L2Index,
        target_l1_p: PageMapPtr,
        target_entry: &MapEntry,
        Tracked(lctx): Tracked<&mut LocalContext>,
    )
        requires
            old(self).wf(),
            old(self).kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            page_table_key_4k_valid::<TABLE_TYPE>(spec_index2va((
                target_l4i,
                target_l3i,
                target_l2i,
                target_l1i,
            ))),
            old(self).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            old(self).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr
                == target_l1_p,
            old(self).spec_resolve_mapping_4k_l1(target_l4i,target_l3i,target_l2i,target_l1i,) is None
                || old(self).mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            target_entry.present,
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            page_map_write_lctx_ensures(old(lctx), final(lctx)),
            final(lctx).stable_lock_id_set() == old(lctx).stable_lock_id_set(),
            final(self).wf(),
            final(self).kernel_l4_end == old(self).kernel_l4_end,
            final(self).page_closure() =~= old(self).page_closure(),
            final(self).mapping_4k.view() == old(self).mapping_4k.view().insert(
                spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
                *target_entry,
            ),
            final(self).mapping_2m() =~= old(self).mapping_2m(),
            final(self).mapping_1g() =~= old(self).mapping_1g(),
            final(self).spec_resolve_mapping_l4(target_l4i)
                == old(self).spec_resolve_mapping_l4(target_l4i),
            final(self).spec_resolve_mapping_l3(target_l4i, target_l3i)
                == old(self).spec_resolve_mapping_l3(target_l4i, target_l3i),
            final(self).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)
                == old(self).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger final(self).spec_resolve_mapping_l2(l4i, l3i, l2i)]
                final(self).kernel_l4_end <= l4i && pei_valid(l4i)
                    && pei_valid(l3i)
                    && pei_valid(l2i)
                ==> final(self).spec_resolve_mapping_l2(l4i, l3i, l2i)
                    == old(self).spec_resolve_mapping_l2(l4i, l3i, l2i),
            final(self).kernel_entries =~= old(self).kernel_entries,
            final(self).pcid == old(self).pcid,
            final(self).cr3 =~= old(self).cr3,
            final(self).proc_ptr =~= old(self).proc_ptr,
    {
        assert({
            &&& self.l1_tables.view().dom().contains(target_l1_p)
            &&& self.l1_tables.view().spec_index(target_l1_p).addr() == target_l1_p
            &&& self.l1_tables.view().spec_index(target_l1_p).is_init()
            &&& self.l1_tables.view().spec_index(target_l1_p).value().wf()
        }) by {
            reveal(PageTable::wf_l4);
            reveal(PageTable::wf_l3);
            reveal(PageTable::wf_l2);
            reveal(PageTable::wf_l1);
        };
        assert(mem_valid(target_entry.addr)) by {
            page_ptr_valid_imply_mem_valid(target_entry.addr);
        };
        page_map_set_published_in_map(
            target_l1_p,
            Tracked(self.l1_tables.borrow_mut()),
            target_l1i,
            PageEntry {
                addr: target_entry.addr,
                perm: PageEntryPerm {
                    present: true,
                    ps: false,
                    write: target_entry.write,
                    execute_disable: target_entry.execute_disable,
                    user: true,
                    kernel_present: true,
                },
            },
            Tracked(&mut *lctx),
        );
        proof {
            self.mapping_4k = Ghost(self.mapping_4k.view().insert(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),*target_entry));
        }
        assert(self.wf_l1()) by {
            reveal(PageTable::wf_l1);
        };
        assert(self.wf_l4()) by {
            reveal(PageTable::wf_l4);
        };
        assert(self.wf_l3()) by {
            reveal(PageTable::wf_l3);
        };
        assert(self.wf_l2()) by {
            reveal(PageTable::wf_l2);
        };
        assert(self.disjoint_l4()) by {
            reveal(PageTable::disjoint_l4);
        };
        assert(self.disjoint_l3()) by {
            reveal(PageTable::disjoint_l3);
        };
        assert(self.disjoint_l2()) by {
            reveal(PageTable::disjoint_l2);
        };
        assert(self.wf_mapping_4k()) by {
            reveal(PageTable::wf_mapping_4k);
            reveal(PageTable::wf_l4);
            reveal(PageTable::wf_l3);
            reveal(PageTable::wf_l2);
            assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L2Index|
                #![trigger self.mapping_4k.view().dom().contains(
                    spec_index2va((l4i, l3i, l2i, l1i)))]
                #![trigger old(self).mapping_4k.view().dom().contains(
                    spec_index2va((l4i, l3i, l2i, l1i)))]
                self.kernel_l4_end <= l4i && pei_valid(l4i)
                    && pei_valid(l3i)
                    && pei_valid(l2i)
                    && pei_valid(l1i)
                    && (target_l4i, target_l3i, target_l2i, target_l1i)
                        != (l4i, l3i, l2i, l1i)
                ==> self.mapping_4k.view().dom().contains(
                        spec_index2va((l4i, l3i, l2i, l1i)))
                    == old(self).mapping_4k.view().dom().contains(
                        spec_index2va((l4i, l3i, l2i, l1i)))) by {
                spec_index2va_injective();
            };
            assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger self.spec_resolve_mapping_l2(l4i, l3i, l2i)]
                #![trigger old(self).spec_resolve_mapping_l2(l4i, l3i, l2i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i)
                    && pei_valid(l3i)
                    && pei_valid(l2i)
                    && (target_l4i, target_l3i, target_l2i)
                        != (l4i, l3i, l2i)
                ==> self.spec_resolve_mapping_l2(l4i, l3i, l2i)
                    == old(self).spec_resolve_mapping_l2(l4i, l3i, l2i)) by {
                self.resolve_l2_unchanged(old(self));
            };
            assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger self.spec_resolve_mapping_l2(l4i,l3i,l2i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i)
                    && pei_valid(l3i)
                    && pei_valid(l2i)
                    && self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                    && !((target_l4i,target_l3i,target_l2i,) =~= (l4i, l3i, l2i))
                    ==>
                    self.spec_resolve_mapping_l2(l4i,l3i,l2i,)->0.addr != target_l1_p) by {
                broadcast use PageTable::resolve_l2_addr_unique_at;
            };
            assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L2Index|
                #![trigger self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
                #![trigger old(self).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
                self.kernel_l4_end <= l4i && pei_valid(l4i)
                    && pei_valid(l3i)
                    && pei_valid(l2i)
                    && pei_valid(l1i)
                    && (target_l4i, target_l3i, target_l2i)
                        != (l4i, l3i, l2i)
                ==> (self.spec_resolve_mapping_4k_l1(
                        l4i, l3i, l2i, l1i) is Some)
                    == (old(self).spec_resolve_mapping_4k_l1(
                        l4i, l3i, l2i, l1i) is Some)) by {
                broadcast use PageTable::resolve_4k_l1_unchanged_at;
            };
        };
        assert(self.wf_mapping_2m()) by {
            reveal(PageTable::wf_mapping_2m);
        };
        assert(self.wf_mapping_1g()) by {
            reveal(PageTable::wf_mapping_1g);
        };
        assert(self.user_only()) by {
            reveal(PageTable::user_only);
        };
        assert(self.rwx_upper_level_entries()) by {
            reveal(PageTable::rwx_upper_level_entries);
        };
        assert(self.table_pages_wf()) by {
            reveal(PageTable::table_pages_wf);
        };
        assert(self.kernel_entries_wf()) by {
            reveal(PageTable::kernel_entries_wf);
        };
    }

}

} // verus!
