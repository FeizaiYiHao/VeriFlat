use vstd::prelude::*;
verus! {

use super::pagemap_util_t::*;
use crate::*;
use super::pagetable_spec::*;
use super::pagemap::*;
use super::entry::*;
use vstd::simple_pptr::*;
use vstd::assert_sets_equal;

impl<const TABLE_TYPE:PTType> PageTable<TABLE_TYPE> {
    /// First half of 4K unmap: make future page walks miss while retaining the
    /// kernel mapping record that backs any stale TLB entry. A caller must flush
    /// those entries before invoking `unmap_4k_page_kernel`.
    #[verifier::spinoff_prover]
    pub fn unmap_4k_page_user_view(
        &mut self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l1i: L2Index,
        target_l1_p: PageMapPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
    )
        requires
            old(self).wf(),
            old(self).kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            old(self).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            old(self).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr
                == target_l1_p,
            old(self).spec_resolve_mapping_4k_l1(
                target_l4i,
                target_l3i,
                target_l2i,
                target_l1i,
            ) is Some || old(self).mapping_4k().dom().contains(
                spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
            ) == true,
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            page_map_write_lctx_ensures(old(lctx), final(lctx)),
            final(self).wf(),
            final(self).kernel_l4_end == old(self).kernel_l4_end,
            final(self).page_closure() =~= old(self).page_closure(),
            final(self).mapping_4k() == old(self).mapping_4k().insert(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
                MapEntry{
                    addr: old(self).mapping_4k().spec_index(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))).addr,
                    write: old(self).mapping_4k().spec_index(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))).write,
                    execute_disable: old(self).mapping_4k().spec_index(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))).execute_disable,
                    present: false,
                    owning_container: old(self).mapping_4k().spec_index(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))).owning_container,
                }),
            final(self).mapping_2m() =~= old(self).mapping_2m(),
            final(self).mapping_1g() =~= old(self).mapping_1g(),
            final(self).kernel_entries =~= old(self).kernel_entries,
    {
        let va = Ghost(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)));
        assert(self.mapping_4k.view().dom().contains(va.view())) by {
            reveal(PageTable::wf_mapping_4k);
        };
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
        let tracked l1_perm = self.l1_tables.borrow().tracked_borrow(target_l1_p);
        let l1_tbl: &PageMap = PPtr::<PageMap>::from_usize(target_l1_p).borrow(Tracked(l1_perm));
        let mut l1_entry = l1_tbl.get(target_l1i);
        // l1_entry came from get(...) -> usize2page_entry(...).addr = usize2pa(v) = v & MEM_MASK,
        // which is always mem_valid. After mutation of perm.present, addr is unchanged.
        let ghost orig_addr = l1_entry.addr;
        assert(mem_valid(orig_addr)) by {
            let v = l1_perm.value().ar.view().spec_index(target_l1i as int);
            // wf says spec_seq@[i] =~= usize2page_entry(ar@[i])
            assert(usize2page_entry(v) =~= l1_perm.value().spec_seq.view().spec_index(target_l1i as int)) by {
                reveal(PageTable::wf_l1);
            };
            assert(spec_usize2pa(v) & (!0x0000_ffff_ffff_f000u64) as usize == 0) by (bit_vector);
        }
        l1_entry.perm.present = false;
        page_map_set_published_in_map(
            target_l1_p,
            Tracked(self.l1_tables.borrow_mut()),
            target_l1i,
            l1_entry,
            Tracked(&mut *lctx),
        );
        proof {
            self.mapping_4k = Ghost(self.mapping_4k.view().insert(va.view(), MapEntry{
                    addr: old(self).mapping_4k.view().spec_index(va.view()).addr,
                    write: old(self).mapping_4k.view().spec_index(va.view()).write,
                    execute_disable: old(self).mapping_4k.view().spec_index(va.view()).execute_disable,
                    present: false,
                    owning_container: old(self).mapping_4k.view().spec_index(va.view()).owning_container,
                }));
        }

        assert(self.wf_l4()) by { reveal(PageTable::wf_l4); };
        assert(self.wf_l3()) by { reveal(PageTable::wf_l3); };
        assert(self.wf_l2()) by { reveal(PageTable::wf_l2); };
        assert(self.wf_l1()) by {
            reveal(PageTable::wf_l1);
        };
        assert(self.disjoint_l4()) by { reveal(PageTable::disjoint_l4); };
        assert(self.disjoint_l3()) by { reveal(PageTable::disjoint_l3); };
        assert(self.disjoint_l2()) by { reveal(PageTable::disjoint_l2); };
        assert(self.wf_mapping_4k()) by {
                spec_index2va_injective();

                assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L2Index|
                    #![trigger self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                    #![trigger old(self).spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                    self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (target_l4i, target_l3i, target_l2i)
                            != (l4i, l3i, l2i)
                        ==> self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)
                            == old(self).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)) by {
                    self.resolve_l2_unchanged(old(self));
                    broadcast use PageTable::resolve_4k_l1_unchanged_at;
                    broadcast use PageTable::resolve_l2_addr_unique_at;
                    broadcast use PageTable::resolve_l2_target_exists;
                };

                reveal(PageTable::wf_mapping_4k);
        };
        assert(self.wf_mapping_2m()) by {
                reveal(PageTable::wf_mapping_2m);
        };
        assert(self.wf_mapping_1g()) by {
                reveal(PageTable::wf_mapping_1g);
        };
        assert(self.user_only()) by { reveal(PageTable::user_only); };
        assert(self.rwx_upper_level_entries()) by {
            reveal(PageTable::rwx_upper_level_entries);
        };
        assert(self.table_pages_wf()) by { reveal(PageTable::table_pages_wf); };
        assert(self.kernel_entries_wf()) by {
            reveal(PageTable::kernel_entries_wf);
        };
    }

    /// Final half of 4K unmap: remove the kernel mapping only after its user
    /// present bit is already clear. Kernel-level callers must additionally
    /// establish that no stale TLB entry remains; restoring `tlb_wf_spec` after
    /// this removal enforces that obligation.
    #[verifier::spinoff_prover]
    pub fn unmap_4k_page_kernel(
        &mut self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l1i: L2Index,
        target_l1_p: PageMapPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
    )
        requires
            old(self).wf(),
            old(self).kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            old(self).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            old(self).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr
                == target_l1_p,
            old(self).spec_resolve_mapping_4k_l1(
                target_l4i,
                target_l3i,
                target_l2i,
                target_l1i,
            ) is Some || old(self).mapping_4k().dom().contains(
                spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
            ) == true,
            old(self).mapping_4k().dom().contains(
                spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
            ),
            old(self).mapping_4k().spec_index(
                spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
            ).present == false,
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            page_map_write_lctx_ensures(old(lctx), final(lctx)),
            final(self).wf(),
            final(self).kernel_l4_end == old(self).kernel_l4_end,
            final(self).page_closure() =~= old(self).page_closure(),
            final(self).mapping_4k.view() == old(self).mapping_4k.view().remove(
                spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
            ),
            final(self).spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None,
            final(self).mapping_2m() =~= old(self).mapping_2m(),
            final(self).mapping_1g() =~= old(self).mapping_1g(),
            final(self).kernel_entries =~= old(self).kernel_entries,
    {
        let va = Ghost(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)));
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
        let empty_entry = PageEntry::empty();
        assert(mem_valid(empty_entry.addr)) by { mem_valid_zero(); };
        page_map_set_published_in_map(
            target_l1_p,
            Tracked(self.l1_tables.borrow_mut()),
            target_l1i,
            empty_entry,
            Tracked(&mut *lctx),
        );
        proof {
            self.mapping_4k = Ghost(self.mapping_4k.view().remove(va.view()));
        }

        assert(self.wf_l4()) by { reveal(PageTable::wf_l4); };
        assert(self.wf_l3()) by { reveal(PageTable::wf_l3); };
        assert(self.wf_l2()) by { reveal(PageTable::wf_l2); };
        assert(self.wf_l1()) by {
            reveal(PageTable::wf_l1);
        };
        assert(self.disjoint_l4()) by { reveal(PageTable::disjoint_l4); };
        assert(self.disjoint_l3()) by { reveal(PageTable::disjoint_l3); };
        assert(self.disjoint_l2()) by { reveal(PageTable::disjoint_l2); };
        assert(self.wf_mapping_4k()) by {
                spec_index2va_injective();

                assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L2Index|
                    #![trigger self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                    #![trigger old(self).spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                    self.kernel_l4_end <= l4i && pei_valid(l4i)
                        && pei_valid(l3i)
                        && pei_valid(l2i)
                        && pei_valid(l1i)
                        && (target_l4i, target_l3i, target_l2i) != (l4i, l3i, l2i)
                        ==> self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)
                            == old(self).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)) by {
                    self.resolve_l2_unchanged(old(self));
                    broadcast use PageTable::resolve_4k_l1_unchanged_at;
                    broadcast use PageTable::resolve_l2_addr_unique_at;
                    broadcast use PageTable::resolve_l2_target_exists;
                };

                reveal(PageTable::wf_mapping_4k);
        };
        assert(self.wf_mapping_2m()) by {
                reveal(PageTable::wf_mapping_2m);
        };
        assert(self.wf_mapping_1g()) by {
                reveal(PageTable::wf_mapping_1g);
        };
        assert(self.user_only()) by { reveal(PageTable::user_only); };
        assert(self.rwx_upper_level_entries()) by {
            reveal(PageTable::rwx_upper_level_entries);
        };
        assert(self.table_pages_wf()) by { reveal(PageTable::table_pages_wf); };
        assert(self.kernel_entries_wf()) by {
            reveal(PageTable::kernel_entries_wf);
        };
    }

    #[verifier::spinoff_prover]
    pub fn map_2m_page(
        &mut self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l2_p: PageMapPtr,
        target_entry: &MapEntry,
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
            old(self).spec_resolve_mapping_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ) is None,
            old(self).spec_resolve_mapping_2m_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ) is None || old(self).mapping_2m().dom().contains(
                spec_index2va((target_l4i, target_l3i, target_l2i, 0)),
            ) == false,
            old(self).page_closure().contains(target_entry.addr) == false,
            page_ptr_valid(target_entry.addr),
            page_ptr_2m_valid(target_entry.addr),
            page_table_key_2m_valid::<TABLE_TYPE>(spec_index2va((
                target_l4i,
                target_l3i,
                target_l2i,
                0,
            ))),
            target_entry.present,
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            page_map_write_lctx_ensures(old(lctx), final(lctx)),
            final(self).wf(),
            final(self).kernel_l4_end == old(self).kernel_l4_end,
            final(self).page_closure() =~= old(self).page_closure(),
            final(self).mapping_2m() == old(self).mapping_2m().insert(
                spec_index2va((target_l4i, target_l3i, target_l2i, 0)),
                *target_entry,
            ),
            final(self).mapping_4k() =~= old(self).mapping_4k(),
            final(self).mapping_1g() =~= old(self).mapping_1g(),
            final(self).kernel_entries =~= old(self).kernel_entries,
    {
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
        let tracked mut l2_perm = self.l2_tables.borrow_mut().tracked_remove(target_l2_p);
        assert(mem_valid(target_entry.addr)) by {
            page_ptr_valid_imply_mem_valid(target_entry.addr);
        };
        page_map_set_published(
            target_l2_p,
            Tracked(&mut l2_perm),
            target_l2i,
            PageEntry {
                addr: target_entry.addr,
                perm: PageEntryPerm {
                    present: true,
                    ps: true,
                    write: target_entry.write,
                    execute_disable: target_entry.execute_disable,
                    user: true,
                    kernel_present: true,
                },
            },
            Tracked(&mut *lctx),
        );
        proof {
            self.l2_tables.borrow_mut().tracked_insert(target_l2_p, l2_perm);
        }
        proof{
            *self.mapping_2m = self.mapping_2m.view().insert(
                spec_index2va((target_l4i, target_l3i, target_l2i, 0)),
                *target_entry,
            );
        }
        assert(self.wf_l4()) by { reveal(PageTable::wf_l4); };
        assert(self.wf_l3()) by { reveal(PageTable::wf_l3); };
        assert(self.wf_l2()) by { reveal(PageTable::wf_l2); };
        assert(self.wf_l1()) by { reveal(PageTable::wf_l1); };
        assert(self.disjoint_l4()) by { reveal(PageTable::disjoint_l4); };
        assert(self.disjoint_l3()) by { reveal(PageTable::disjoint_l3); };
        assert(self.disjoint_l2()) by { reveal(PageTable::disjoint_l2); };
        assert(self.wf_mapping_4k())
                by {
                    reveal(PageTable::wf_mapping_4k);
        };
        assert(self.wf_mapping_2m()) by {
                    reveal(PageTable::wf_mapping_2m);
                    spec_index2va_injective();
                    reveal(PageTable::wf_l4);
                    reveal(PageTable::wf_l3);
                    reveal(PageTable::disjoint_l4);
                    reveal(PageTable::disjoint_l3);
        };
        assert(self.wf_mapping_1g()) by {
                    reveal(PageTable::wf_mapping_1g);
        };
        assert(self.user_only()) by { reveal(PageTable::user_only); };
        assert(self.rwx_upper_level_entries()) by {
            reveal(PageTable::rwx_upper_level_entries);
        };
        assert(self.table_pages_wf()) by { reveal(PageTable::table_pages_wf); };
        assert(self.kernel_entries_wf()) by {
            reveal(PageTable::kernel_entries_wf);
        };
    }

    #[verifier::spinoff_prover]
    pub fn remove_l2_entry(
        &mut self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l2_p: PageMapPtr,
        target_l1_p: PageMapPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
    ) -> (ret:(PageMapPtr, Tracked<PointsTo<PageMap>>))
        requires
            old(self).wf(),
            old(self).kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            old(self).spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            old(self).spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr
                == target_l2_p,
            old(self).spec_resolve_mapping_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ) is Some,
            old(self).spec_resolve_mapping_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ).unwrap().addr == target_l1_p,
            forall|i: L1Index| #![auto] pei_valid(i) ==> old(self).spec_resolve_mapping_4k_l1(
                target_l4i,
                target_l3i,
                target_l2i,
                i
            ) is None,
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            page_map_write_lctx_ensures(old(lctx), final(lctx)),
            final(self).wf(),
            final(self).kernel_l4_end == old(self).kernel_l4_end,
            final(self).page_closure() =~= old(self).page_closure().remove(target_l1_p),
            final(self).mapping_2m() == old(self).mapping_2m(),
            final(self).mapping_4k() =~= old(self).mapping_4k(),
            final(self).mapping_1g() =~= old(self).mapping_1g(),
            final(self).kernel_entries =~= old(self).kernel_entries,
            ret.0 == target_l1_p,
            ret.1.view().is_init(),
            ret.1.view().addr() == target_l1_p,
    {
        assert({
            &&& self.l2_tables.view().dom().contains(target_l2_p)
            &&& self.l2_tables.view().spec_index(target_l2_p).addr() == target_l2_p
            &&& self.l2_tables.view().spec_index(target_l2_p).is_init()
            &&& self.l2_tables.view().spec_index(target_l2_p).value().wf()
            &&& self.l2_tables.view().spec_index(target_l2_p).value().spec_index(
                target_l2i,
            ).perm.present
            &&& !self.l2_tables.view().spec_index(target_l2_p).value().spec_index(
                target_l2i,
            ).perm.ps
            &&& self.l2_tables.view().spec_index(target_l2_p).value().spec_index(
                target_l2i,
            ).addr == target_l1_p
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

        let tracked mut l2_perm = self.l2_tables.borrow_mut().tracked_remove(target_l2_p);
        assert(mem_valid(0)) by { mem_valid_zero(); };
        page_map_set_published(
            target_l2_p,
            Tracked(&mut l2_perm),
            target_l2i,
            PageEntry {
                addr: 0,
                perm: PageEntryPerm {
                    present: false,
                    ps: false,
                    write: false,
                    execute_disable: false,
                    user: false,
                    kernel_present: false,
                },
            },
            Tracked(&mut *lctx),
        );
        proof {
            self.l2_tables.borrow_mut().tracked_insert(target_l2_p, l2_perm);
            self.l1_rev_map = Ghost(self.l1_rev_map.view().remove(
                target_l1_p,
            ));
        }
        let tracked mut l1_perm = self.l1_tables.borrow_mut().tracked_remove(target_l1_p);
        let ret = (target_l1_p, Tracked(l1_perm));
        assert(self.wf_l4()) by { reveal(PageTable::wf_l4); };
        assert(self.wf_l3()) by { reveal(PageTable::wf_l3); };
        assert(self.wf_l2()) by {
            broadcast use PageTable::l2_entry_addr_unique_at;
            reveal(PageTable::wf_l2);
        };
        assert(self.wf_l1()) by { reveal(PageTable::wf_l1); };
        assert(self.disjoint_l4()) by { reveal(PageTable::disjoint_l4); };
        assert(self.disjoint_l3()) by { reveal(PageTable::disjoint_l3); };
        assert(self.disjoint_l2()) by { reveal(PageTable::disjoint_l2); };
        assert(self.wf_mapping_4k())
                by {
                    reveal(PageTable::wf_mapping_4k);
                    assert(forall|l4i: L4Index, l3i: L3Index,|
                        #![trigger self.spec_resolve_mapping_l3(l4i,l3i)]
                        self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i)
                            && self.spec_resolve_mapping_l3(l4i, l3i) is Some && !((
                            target_l4i,
                            target_l3i,
                        ) =~= (l4i, l3i)) ==> self.spec_resolve_mapping_l3(
                        l4i,
                        l3i,
                        )->0.addr != target_l2_p) by {
                        broadcast use PageTable::resolve_l3_addr_unique_at;
                    };
                    assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                        #![trigger self.spec_resolve_mapping_l2(l4i,l3i,l2i)]
                        #![trigger old(self).spec_resolve_mapping_l2(l4i,l3i,l2i)]
                        self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && !((
                            target_l4i,
                            target_l3i,
                            target_l2i,
                        ) == (l4i, l3i, l2i)) ==> self.spec_resolve_mapping_l2(l4i, l3i, l2i) =~= old(
                            self,
                        ).spec_resolve_mapping_l2(l4i, l3i, l2i)) by {
                        reveal(PageTable::wf_l4);
                        reveal(PageTable::wf_l3);
                    };
                    assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index,|
                        #![trigger self.spec_resolve_mapping_l2(l4i,l3i,l2i)]
                        self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                            && self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some && !((
                            target_l4i,
                            target_l3i,
                            target_l2i,
                        ) =~= (l4i, l3i, l2i)) ==> self.spec_resolve_mapping_l2(
                        l4i,
                        l3i,
                        l2i,
                        )->0.addr != target_l1_p) by {
                        broadcast use PageTable::resolve_l2_addr_unique_at;
                    };
                    assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
                        #![trigger self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                        #![trigger old(self).spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                        self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> old(
                            self,
                        ).spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i) ==
                        self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)) by {
                        reveal(PageTable::wf_l4);
                        reveal(PageTable::wf_l3);
                        reveal(PageTable::wf_l2);
                    };
        };
        assert(self.wf_mapping_2m()) by {
                    reveal(PageTable::wf_mapping_2m);
                    assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index,|
                        #![trigger self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                        #![trigger old(self).spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                        self.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                            && !((target_l4i, target_l3i, target_l2i) =~= (l4i, l3i, l2i))
                            ==> self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is Some == old(
                            self,
                        ).spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is Some) by {
                        reveal(PageTable::wf_l4);
                        reveal(PageTable::wf_l3);
                    };
        };
        assert(self.wf_mapping_1g()) by {
                    reveal(PageTable::wf_mapping_1g);
        }

        assert(self.user_only()) by { reveal(PageTable::user_only); };
        assert(self.rwx_upper_level_entries()) by {
            reveal(PageTable::rwx_upper_level_entries);
        };
        assert(self.table_pages_wf()) by { reveal(PageTable::table_pages_wf); };
        assert(self.kernel_entries_wf()) by {
            reveal(PageTable::kernel_entries_wf);
        };
        assert(self.page_closure() =~= old(self).page_closure().remove(target_l1_p)) by {
            reveal(PageTable::table_pages_wf);
        }
        return ret;
    }

    #[verifier::spinoff_prover]
    pub fn remove_l3_entry(
        &mut self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l3_p: PageMapPtr,
        target_l2_p: PageMapPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
    ) -> (ret:(PageMapPtr, Tracked<PointsTo<PageMap>>))
        requires
            old(self).wf(),
            old(self).kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            old(self).spec_resolve_mapping_l4(target_l4i) is Some,
            old(self).spec_resolve_mapping_l4(target_l4i)->0.addr
                == target_l3_p,
            old(self).spec_resolve_mapping_l3(
                target_l4i,
                target_l3i,
            ) is Some,old(self).spec_resolve_mapping_1g_l3(
                target_l4i,
                target_l3i,
            ) is None,
            old(self).spec_resolve_mapping_l3(
                target_l4i,
                target_l3i,
            ).unwrap().addr == target_l2_p,
            forall|i: L2Index| #![auto] pei_valid(i) ==> old(self).spec_resolve_mapping_l2(
                target_l4i,
                target_l3i,
                i
            ) is None,
            forall|i: L2Index| #![auto] pei_valid(i) ==> old(self).spec_resolve_mapping_2m_l2(
                target_l4i,
                target_l3i,
                i
            ) is None,
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            page_map_write_lctx_ensures(old(lctx), final(lctx)),
            final(self).wf(),
            final(self).kernel_l4_end == old(self).kernel_l4_end,
            final(self).page_closure() =~= old(self).page_closure().remove(target_l2_p),
            final(self).mapping_2m() == old(self).mapping_2m(),
            final(self).mapping_4k() =~= old(self).mapping_4k(),
            final(self).mapping_1g() =~= old(self).mapping_1g(),
            final(self).kernel_entries =~= old(self).kernel_entries,
            ret.0 == target_l2_p,
            ret.1.view().is_init(),
            ret.1.view().addr() == target_l2_p,
    {
        assert({
            &&& self.l4_table.view().dom().contains(self.cr3)
            &&& self.l4_table.view().spec_index(self.cr3).addr() == self.cr3
            &&& self.l4_table.view().spec_index(self.cr3).is_init()
            &&& self.l4_table.view().spec_index(self.cr3).value().wf()
            &&& self.l3_tables.view().dom().contains(target_l3_p)
            &&& self.l3_tables.view().spec_index(target_l3_p).addr() == target_l3_p
            &&& self.l3_tables.view().spec_index(target_l3_p).is_init()
            &&& self.l3_tables.view().spec_index(target_l3_p).value().wf()
            &&& self.l2_tables.view().dom().contains(target_l2_p)
            &&& self.l2_tables.view().spec_index(target_l2_p).addr() == target_l2_p
            &&& self.l2_tables.view().spec_index(target_l2_p).is_init()
            &&& self.l2_tables.view().spec_index(target_l2_p).value().wf()
        }) by {
            reveal(PageTable::wf_l4);
            reveal(PageTable::wf_l3);
            reveal(PageTable::wf_l2);
        };

        let tracked mut l3_perm = self.l3_tables.borrow_mut().tracked_remove(target_l3_p);
        assert(mem_valid(0)) by { mem_valid_zero(); };
        page_map_set_published(
            target_l3_p,
            Tracked(&mut l3_perm),
            target_l3i,
            PageEntry {
                addr: 0,
                perm: PageEntryPerm {
                    present: false,
                    ps: false,
                    write: false,
                    execute_disable: false,
                    user: false,
                    kernel_present: false,
                },
            },
            Tracked(&mut *lctx),
        );
        proof {
            self.l3_tables.borrow_mut().tracked_insert(target_l3_p, l3_perm);
            self.l2_rev_map = Ghost(self.l2_rev_map.view().remove(
                target_l2_p,
            ));
        }
        let tracked mut l2_perm = self.l2_tables.borrow_mut().tracked_remove(target_l2_p);
        let ret = (target_l2_p, Tracked(l2_perm));
        assert(self.wf_l4()) by { reveal(PageTable::wf_l4); };
        assert(self.wf_l3()) by {
            reveal(PageTable::wf_l3);
            reveal(PageTable::disjoint_l3);
        };
        assert(self.wf_l2()) by {
            reveal(PageTable::wf_l2);
        };
        assert(self.wf_l1()) by {
            reveal(PageTable::wf_l1);
        };
        assert(self.disjoint_l4()) by { reveal(PageTable::disjoint_l4); };
        assert(self.disjoint_l3()) by { reveal(PageTable::disjoint_l3); };
        assert(self.disjoint_l2()) by { reveal(PageTable::disjoint_l2); };
        assert(self.wf_mapping_4k())
                by {
                    reveal(PageTable::wf_mapping_4k);
                    reveal(PageTable::wf_l4);
                    reveal(PageTable::disjoint_l3);
        };
        assert(self.wf_mapping_2m()) by {
                    reveal(PageTable::wf_mapping_2m);
                    reveal(PageTable::wf_l4);
                    reveal(PageTable::disjoint_l3);
        };
        assert(self.wf_mapping_1g()) by {
                    reveal(PageTable::wf_mapping_1g);
        }

        assert(self.user_only()) by { reveal(PageTable::user_only); };
        assert(self.rwx_upper_level_entries()) by {
            reveal(PageTable::rwx_upper_level_entries);
        };
        assert(self.table_pages_wf()) by { reveal(PageTable::table_pages_wf); };
        assert(self.kernel_entries_wf()) by { reveal(PageTable::kernel_entries_wf); };
        assert(self.page_closure() =~= old(self).page_closure().remove(target_l2_p)) by {
            reveal(PageTable::table_pages_wf);
        };
        return ret;
    }

    #[verifier::spinoff_prover]
    pub fn remove_l4_entry(
        &mut self,
        target_l4i: L4Index,
        target_l3_p: PageMapPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
    ) -> (ret:(PageMapPtr, Tracked<PointsTo<PageMap>>))
        requires
            old(self).wf(),
            old(self).kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            old(self).spec_resolve_mapping_l4(target_l4i) is Some,
            old(self).spec_resolve_mapping_l4(target_l4i)->0.addr
                == target_l3_p,
            forall|i: L3Index| #![auto] pei_valid(i) ==> old(self).spec_resolve_mapping_l3(
                target_l4i,
                i
            ) is None,
            forall|i: L3Index| #![auto] pei_valid(i) ==> old(self).spec_resolve_mapping_1g_l3(
                target_l4i,
                i
            ) is None,
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            page_map_write_lctx_ensures(old(lctx), final(lctx)),
            final(self).wf(),
            final(self).kernel_l4_end == old(self).kernel_l4_end,
            final(self).page_closure() =~= old(self).page_closure().remove(target_l3_p),
            final(self).mapping_2m() == old(self).mapping_2m(),
            final(self).mapping_4k() =~= old(self).mapping_4k(),
            final(self).mapping_1g() =~= old(self).mapping_1g(),
            final(self).kernel_entries =~= old(self).kernel_entries,
            ret.0 == target_l3_p,
            ret.1.view().is_init(),
            ret.1.view().addr() == target_l3_p,
    {
        assert({
            &&& self.l4_table.view().dom().contains(self.cr3)
            &&& self.l4_table.view().spec_index(self.cr3).addr() == self.cr3
            &&& self.l4_table.view().spec_index(self.cr3).is_init()
            &&& self.l4_table.view().spec_index(self.cr3).value().wf()
            &&& self.l3_tables.view().dom().contains(target_l3_p)
            &&& self.l3_tables.view().spec_index(target_l3_p).addr() == target_l3_p
            &&& self.l3_tables.view().spec_index(target_l3_p).is_init()
            &&& self.l3_tables.view().spec_index(target_l3_p).value().wf()
        }) by {
            reveal(PageTable::wf_l4);
            reveal(PageTable::wf_l3);
        };

        let tracked mut l4_perm = self.l4_table.borrow_mut().tracked_remove(self.cr3);
        let zero_entry = PageEntry {
            addr: 0,
            perm: PageEntryPerm {
                present: false,
                ps: false,
                write: false,
                execute_disable: false,
                user: false,
                kernel_present: false,
            },
        };
        assert(mem_valid(zero_entry.addr)) by { mem_valid_zero(); };
        page_map_set_published(
            self.cr3,
            Tracked(&mut l4_perm),
            target_l4i,
            zero_entry,
            Tracked(&mut *lctx),
        );
        proof {
            self.l4_table.borrow_mut().tracked_insert(self.cr3, l4_perm);
            self.l3_rev_map = Ghost(self.l3_rev_map.view().remove(
                target_l3_p,
            ));
        }
        let tracked mut l3_perm = self.l3_tables.borrow_mut().tracked_remove(target_l3_p);
        let ret = (target_l3_p, Tracked(l3_perm));
        assert(self.wf_l4()) by {
            reveal(PageTable::wf_l4);
            reveal(PageTable::disjoint_l4);
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
        assert(self.disjoint_l4()) by { reveal(PageTable::disjoint_l4); };
        assert(self.disjoint_l3()) by { reveal(PageTable::disjoint_l3); };
        assert(self.disjoint_l2()) by { reveal(PageTable::disjoint_l2); };
        assert(self.wf_mapping_4k())
                by {
                    reveal(PageTable::wf_mapping_4k);
                    reveal(PageTable::disjoint_l4);
        };
        assert(self.wf_mapping_2m()) by {
                reveal(PageTable::wf_mapping_2m);
                reveal(PageTable::disjoint_l4);
        };
        assert(self.wf_mapping_1g()) by {
                    reveal(PageTable::wf_mapping_1g);
                    reveal(PageTable::disjoint_l4);
        }

        assert(self.user_only()) by { reveal(PageTable::user_only); };
        assert(self.rwx_upper_level_entries()) by {
            reveal(PageTable::rwx_upper_level_entries);
        };
        assert(self.table_pages_wf()) by { reveal(PageTable::table_pages_wf); };
        assert(self.kernel_entries_wf()) by { reveal(PageTable::kernel_entries_wf); };
        proof {
            assert_sets_equal!(
                self.page_closure() == old(self).page_closure().remove(target_l3_p),
                page_ptr => {
                    reveal(PageTable::table_pages_wf);
                    broadcast use vstd::set::group_set_lemmas;
                }
            );
        }
        return ret;
    }

}

} // verus!
