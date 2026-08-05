use vstd::prelude::*;
verus! {

use super::super::pagemap_util_t::*;
use crate::util::page_ptr_util_u::*;
use super::super::pagetable_spec::*;
use super::super::pagemap::*;
use super::super::entry::*;
use crate::define::*;
use vstd::simple_pptr::*;
use crate::lemma::lemma_u::*;

impl<const TABLE_TYPE:PTType> PageTable<TABLE_TYPE> {
    pub fn unmap_4k_page_user_view(
        &mut self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l1i: L2Index,
        target_l1_p: PageMapPtr,
    )
        requires
            old(self).wf(),
            old(self).kernel_l4_end <= target_l4i < 512,
            0 <= target_l3i < 512,
            0 <= target_l2i < 512,
            0 <= target_l1i < 512,
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
        ensures
            final(self).wf(),
            final(self).kernel_l4_end == old(self).kernel_l4_end,
            final(self).page_closure() =~= old(self).page_closure(),
            final(self).mapping_4k() == old(self).mapping_4k().insert(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)), 
                MapEntry{
                    addr: old(self).mapping_4k().spec_index(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))).addr,
                    write: old(self).mapping_4k().spec_index(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))).write,
                    execute_disable: old(self).mapping_4k().spec_index(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))).execute_disable,
                    present: false,
                }),
            final(self).mapping_2m() =~= old(self).mapping_2m(),
            final(self).mapping_1g() =~= old(self).mapping_1g(),
            final(self).kernel_entries =~= old(self).kernel_entries,
    {
        broadcast use PageTable::reveal_page_table_wf;
        broadcast use PageTable::reveal_page_table_levels_wf;
        // broadcast use PageTable::reveal_page_table_disjoint_wf;
        // broadcast use PageTable::reveal_page_table_mappings_wf;
        // broadcast use PageTable::reveal_page_table_additional_wf;

        let va = Ghost(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)));
        assert(va_4k_valid(va.view())) by {
            va_lemma();
        };
        assert(self.mapping_4k.view().dom().contains(va.view())) by { broadcast use PageTable::reveal_page_table_mappings_wf; };
        let tracked mut l1_perm = self.l1_tables.borrow_mut().tracked_remove(target_l1_p);
        let l1_tbl: &PageMap = PPtr::<PageMap>::from_usize(target_l1_p).borrow(Tracked(&l1_perm));
        let mut l1_entry = l1_tbl.get(target_l1i);
        // l1_entry came from get(...) -> usize2page_entry(...).addr = usize2pa(v) = v & MEM_MASK,
        // which is always mem_valid. After mutation of perm.present, addr is unchanged.
        let ghost orig_addr = l1_entry.addr;
        assert(mem_valid(orig_addr)) by {
            let v = l1_perm.value().ar.view().spec_index(target_l1i as int);
            // wf says spec_seq@[i] =~= usize2page_entry(ar@[i])
            assert(l1_perm.value().wf());
            assert(usize2page_entry(v) =~= l1_perm.value().spec_seq.view().spec_index(target_l1i as int));
            assert(l1_entry =~= l1_perm.value().spec_index(target_l1i));
            assert(l1_perm.value().spec_index(target_l1i) == l1_perm.value().spec_seq.view().spec_index(target_l1i as int));
            assert(orig_addr == spec_usize2pa(v));
            assert(spec_usize2pa(v) & (!0x0000_ffff_ffff_f000u64) as usize == 0) by (bit_vector);
        }
        l1_entry.perm.present = false;
        assert(l1_entry.addr == orig_addr);
        page_map_set(target_l1_p, Tracked(&mut l1_perm), target_l1i, l1_entry);

        proof {
            self.l1_tables.borrow_mut().tracked_insert(target_l1_p, l1_perm);
            self.mapping_4k = Ghost(self.mapping_4k.view().insert(va.view(), MapEntry{
                    addr: old(self).mapping_4k.view().spec_index(va.view()).addr,
                    write: old(self).mapping_4k.view().spec_index(va.view()).write,
                    execute_disable: old(self).mapping_4k.view().spec_index(va.view()).execute_disable,
                    present: false,
                }));
        }
        
        assert(self.wf_l4());
        assert(self.wf_l3());
        assert(self.wf_l2());
        assert(self.wf_l1());
        assert(self.disjoint_wf()) by {
            broadcast use PageTable::reveal_page_table_disjoint_wf;
            assert(self.disjoint_l4()) by { broadcast use PageTable::reveal_page_table_disjoint_wf; };
            assert(self.disjoint_l3()) by { broadcast use PageTable::reveal_page_table_disjoint_wf; };
            assert(self.disjoint_l2()) by { broadcast use PageTable::reveal_page_table_disjoint_wf; };
        }
        assert(self.mappings_wf()) by {
            broadcast use PageTable::reveal_page_table_mappings_wf;
            assert(self.wf_mapping_4k()) by {
                broadcast use PageTable::reveal_page_table_mappings_wf;
                va_lemma();
                assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L2Index|
                    #![trigger self.mapping_4k.view().dom().contains(spec_index2va((l4i,l3i,l2i,l1i)))]
                    #![trigger old(self).mapping_4k.view().dom().contains(spec_index2va((l4i,l3i,l2i,l1i)))]
                    self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i
                        < 512 && !((target_l4i, target_l3i, target_l2i, target_l1i) =~= (
                        l4i,
                        l3i,
                        l2i,
                        l1i,
                    )) ==> self.mapping_4k.view().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))) == old(
                        self,
                    ).mapping_4k.view().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))));

                assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                    #![trigger self.spec_resolve_mapping_l2(l4i,l3i,l2i)]
                    #![trigger old(self).spec_resolve_mapping_l2(l4i,l3i,l2i)]
                    self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && !((
                        target_l4i,
                        target_l3i,
                        target_l2i,
                    ) =~= (l4i, l3i, l2i)) ==> self.spec_resolve_mapping_l2(l4i, l3i, l2i) =~= old(
                        self,
                    ).spec_resolve_mapping_l2(l4i, l3i, l2i));

                assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                    #![trigger self.spec_resolve_mapping_l2(l4i,l3i,l2i)]
                    self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512
                        && self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some && !((
                        target_l4i,
                        target_l3i,
                        target_l2i,
                    ) =~= (l4i, l3i, l2i)) ==> self.spec_resolve_mapping_l2(
                        l4i,
                        l3i,
                        l2i,
                    )->0.addr != target_l1_p) by {
                    old(self).internal_resolve_disjoint();
                };

                assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L2Index|
                    #![trigger self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                    #![trigger old(self).spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                    self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i
                        < 512 && !((target_l4i, target_l3i, target_l2i) =~= (l4i, l3i, l2i))
                        ==> self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is Some == old(
                        self,
                    ).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is Some);

                assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L2Index|
                    #![trigger self.mapping_4k.view().spec_index(spec_index2va((l4i,l3i,l2i,l1i)))]
                    #![trigger self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                    self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i
                        < 512 ==> self.mapping_4k.view().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                        == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is Some);
            };
            assert(self.wf_mapping_2m()) by {
                broadcast use PageTable::reveal_page_table_mappings_wf;
                assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                    #![trigger self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                    #![trigger old(self).spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                    self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 ==> old(
                        self,
                    ).spec_resolve_mapping_2m_l2(l4i, l3i, l2i) == self.spec_resolve_mapping_2m_l2(
                        l4i,
                        l3i,
                        l2i,
                    ));
            };
            assert(self.wf_mapping_1g()) by {
                broadcast use PageTable::reveal_page_table_mappings_wf;
                assert(forall|l4i: L4Index, l3i: L3Index|
                    #![trigger self.spec_resolve_mapping_1g_l3(l4i,l3i)]
                    #![trigger old(self).spec_resolve_mapping_1g_l3(l4i,l3i)]
                    self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && (l4i, l3i) != (
                        target_l4i,
                        target_l3i,
                    ) ==> old(self).spec_resolve_mapping_1g_l3(l4i, l3i)
                        =~= self.spec_resolve_mapping_1g_l3(l4i, l3i));
            };
        }
        assert(self.additional_wf()) by {broadcast use PageTable::reveal_page_table_additional_wf;}
        assert(self.mapping_2m() =~= old(self).mapping_2m());
        assert(self.mapping_1g() =~= old(self).mapping_1g());
        assert(self.va_addr_valid()) by {
            va_addr_valid_proof::<TABLE_TYPE>();
        };
    }

    pub fn unmap_4k_page_kernel(
        &mut self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l1i: L2Index,
        target_l1_p: PageMapPtr,
    )
        requires
            old(self).wf(),
            old(self).kernel_l4_end <= target_l4i < 512,
            0 <= target_l3i < 512,
            0 <= target_l2i < 512,
            0 <= target_l1i < 512,
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
        ensures
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
        broadcast use PageTable::reveal_page_table_wf;
        broadcast use PageTable::reveal_page_table_levels_wf;

        let va = Ghost(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)));
        assert(va_4k_valid(va.view())) by {
            va_lemma();
        };
        assert(self.mapping_4k.view().dom().contains(va.view())) by { broadcast use PageTable::reveal_page_table_mappings_wf; };
        let tracked mut l1_perm = self.l1_tables.borrow_mut().tracked_remove(target_l1_p);
        proof { mem_valid_zero(); }
        page_map_set(target_l1_p, Tracked(&mut l1_perm), target_l1i, PageEntry::empty());

        proof {
            self.l1_tables.borrow_mut().tracked_insert(target_l1_p, l1_perm);
            self.mapping_4k = Ghost(self.mapping_4k.view().remove(va.view()));
            assert(!self.mapping_4k.view().contains_key(va.view()));
        }
        
        assert(self.wf_l4());
        assert(self.wf_l3());
        assert(self.wf_l2());
        assert(self.wf_l1());
        assert(self.disjoint_wf()) by { broadcast use PageTable::reveal_page_table_disjoint_wf; };
        assert(self.mappings_wf()) by { broadcast use PageTable::reveal_page_table_mappings_wf; 
            assert(self.wf_mapping_4k()) by {
                broadcast use PageTable::reveal_page_table_mappings_wf;
                va_lemma();
                assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L2Index|
                    #![trigger self.mapping_4k.view().dom().contains(spec_index2va((l4i,l3i,l2i,l1i)))]
                    #![trigger old(self).mapping_4k.view().dom().contains(spec_index2va((l4i,l3i,l2i,l1i)))]
                    self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i
                        < 512 && !((target_l4i, target_l3i, target_l2i, target_l1i) =~= (
                        l4i,
                        l3i,
                        l2i,
                        l1i,
                    )) ==> self.mapping_4k.view().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))) == old(
                        self,
                    ).mapping_4k.view().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))));

                assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                    #![trigger self.spec_resolve_mapping_l2(l4i,l3i,l2i)]
                    #![trigger old(self).spec_resolve_mapping_l2(l4i,l3i,l2i)]
                    self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && !((
                        target_l4i,
                        target_l3i,
                        target_l2i,
                    ) =~= (l4i, l3i, l2i)) ==> self.spec_resolve_mapping_l2(l4i, l3i, l2i) =~= old(
                        self,
                    ).spec_resolve_mapping_l2(l4i, l3i, l2i));

                assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                    #![trigger self.spec_resolve_mapping_l2(l4i,l3i,l2i)]
                    self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512
                        && self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some && !((
                        target_l4i,
                        target_l3i,
                        target_l2i,
                    ) =~= (l4i, l3i, l2i)) ==> self.spec_resolve_mapping_l2(
                        l4i,
                        l3i,
                        l2i,
                    )->0.addr != target_l1_p) by {
                    old(self).internal_resolve_disjoint();
                };

                assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L2Index|
                    #![trigger self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                    #![trigger old(self).spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                    self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i
                        < 512 && !((target_l4i, target_l3i, target_l2i) =~= (l4i, l3i, l2i))
                        ==> self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is Some == old(
                        self,
                    ).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is Some);

                assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L2Index|
                    #![trigger self.mapping_4k.view().spec_index(spec_index2va((l4i,l3i,l2i,l1i)))]
                    #![trigger self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                    self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i
                        < 512 ==> self.mapping_4k.view().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                        == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is Some);
            };
            assert(self.wf_mapping_2m()) by {
                broadcast use PageTable::reveal_page_table_mappings_wf;
                assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                    #![trigger self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                    #![trigger old(self).spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                    self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 ==> old(
                        self,
                    ).spec_resolve_mapping_2m_l2(l4i, l3i, l2i) == self.spec_resolve_mapping_2m_l2(
                        l4i,
                        l3i,
                        l2i,
                    ));
            };
            assert(self.wf_mapping_1g()) by {
                broadcast use PageTable::reveal_page_table_mappings_wf;
                assert(forall|l4i: L4Index, l3i: L3Index|
                    #![trigger self.spec_resolve_mapping_1g_l3(l4i,l3i)]
                    #![trigger old(self).spec_resolve_mapping_1g_l3(l4i,l3i)]
                    self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && (l4i, l3i) != (
                        target_l4i,
                        target_l3i,
                    ) ==> old(self).spec_resolve_mapping_1g_l3(l4i, l3i)
                        =~= self.spec_resolve_mapping_1g_l3(l4i, l3i));
            };
        };
        assert(self.additional_wf()) by {broadcast use PageTable::reveal_page_table_additional_wf;}
        assert(self.mapping_2m() =~= old(self).mapping_2m());
        assert(self.mapping_1g() =~= old(self).mapping_1g());        
        assert(self.va_addr_valid()) by {
            va_addr_valid_proof::<TABLE_TYPE>();
        };
    }

    pub fn map_2m_page(
        &mut self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l2_p: PageMapPtr,
        target_entry: &MapEntry,
    )
        requires
            old(self).wf(),
            old(self).kernel_l4_end <= target_l4i < 512,
            0 <= target_l3i < 512,
            0 <= target_l2i < 512,
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
            target_entry.present,
        ensures
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
        broadcast use PageTable::reveal_page_table_wf;
        broadcast use PageTable::reveal_page_table_levels_wf;
        // broadcast use PageTable::reveal_page_table_disjoint_wf;
        // broadcast use PageTable::reveal_page_table_mappings_wf;
        // broadcast use PageTable::reveal_page_table_additional_wf;

        assert(va_2m_valid(spec_index2va((target_l4i, target_l3i, target_l2i, 0)))) by {
            va_lemma();
        };
        assert(self.mapping_2m.view().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, 0))) == false) by {
            broadcast use PageTable::reveal_page_table_mappings_wf;
        };
        let tracked mut l2_perm = self.l2_tables.borrow_mut().tracked_remove(target_l2_p);
        proof {
            page_ptr_valid_imply_mem_valid(target_entry.addr);
        }
        page_map_set(
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
        );
        proof {
            self.l2_tables.borrow_mut().tracked_insert(target_l2_p, l2_perm);
            assert(self.spec_resolve_mapping_2m_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ) is Some);
        }
        proof{
            *self.mapping_2m = self.mapping_2m.view().insert(
                spec_index2va((target_l4i, target_l3i, target_l2i, 0)),
                *target_entry,
            );
        }
        assert(self.wf_l4());
        assert(self.wf_l3());
        assert(self.wf_l2());
        assert(self.wf_l1());
        assert(self.disjoint_wf()) by { broadcast use PageTable::reveal_page_table_disjoint_wf; };
        assert(self.mappings_wf()) by { 
            broadcast use PageTable::reveal_page_table_mappings_wf; 
            assert(self.wf_mapping_4k())
                by {
                    broadcast use PageTable::reveal_page_table_mappings_wf;
                    assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
                        #![trigger self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                        #![trigger old(self).spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                        self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i < 512 ==> old(
                            self,
                        ).spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i) == 
                        self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i));
                };
                assert(self.wf_mapping_2m()) by {
                    broadcast use PageTable::reveal_page_table_mappings_wf;
                    va_lemma();
                    assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                        #![trigger self.mapping_2m.view().dom().contains(spec_index2va((l4i,l3i,l2i,0)))]
                        #![trigger old(self).mapping_2m.view().dom().contains(spec_index2va((l4i,l3i,l2i,0)))]
                        self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && !((target_l4i, target_l3i, target_l2i) =~= (
                            l4i,
                            l3i,
                            l2i,
                        )) ==> self.mapping_2m.view().dom().contains(spec_index2va((l4i, l3i, l2i, 0))) == old(
                            self,
                        ).mapping_2m.view().dom().contains(spec_index2va((l4i, l3i, l2i, 0))));

                    assert(forall|l4i: L4Index, l3i: L3Index|
                        #![trigger self.spec_resolve_mapping_l3(l4i,l3i)]
                        #![trigger old(self).spec_resolve_mapping_l3(l4i,l3i)]
                        self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && !((
                            target_l4i,
                            target_l3i,
                        ) =~= (l4i, l3i)) ==> self.spec_resolve_mapping_l3(l4i, l3i) =~= old(
                            self,
                        ).spec_resolve_mapping_l3(l4i, l3i));

                    assert(forall|l4i: L4Index, l3i: L3Index,|
                        #![trigger self.spec_resolve_mapping_l3(l4i,l3i)]
                        self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 
                            && self.spec_resolve_mapping_l3(l4i, l3i) is Some && !((
                            target_l4i,
                            target_l3i,
                        ) =~= (l4i, l3i)) ==> self.spec_resolve_mapping_l3(
                            l4i,
                            l3i,
                        )->0.addr != target_l2_p) by {
                        old(self).internal_resolve_disjoint();
                    };

                    assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index,|
                        #![trigger self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                        #![trigger old(self).spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                        self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512
                            && !((target_l4i, target_l3i, target_l2i) =~= (l4i, l3i, l2i))
                            ==> self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is Some == old(
                            self,
                        ).spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is Some);

                    assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                        #![trigger self.mapping_2m.view().spec_index(spec_index2va((l4i,l3i,l2i,0)))]
                        #![trigger self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                        self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512
                        ==> self.mapping_2m.view().dom().contains(spec_index2va((l4i, l3i, l2i, 0)))
                            == self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is Some);
                };
                assert(self.wf_mapping_1g()) by {
                    broadcast use PageTable::reveal_page_table_mappings_wf;
                    assert(forall|l4i: L4Index, l3i: L3Index|
                        #![trigger self.spec_resolve_mapping_1g_l3(l4i,l3i)]
                        #![trigger old(self).spec_resolve_mapping_1g_l3(l4i,l3i)]
                        self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && (l4i, l3i) != (
                            target_l4i,
                            target_l3i,
                        ) ==> old(self).spec_resolve_mapping_1g_l3(l4i, l3i)
                            =~= self.spec_resolve_mapping_1g_l3(l4i, l3i));
                };
        };
        assert(self.mapping_4k() =~= old(self).mapping_4k());
        assert(self.mapping_1g() =~= old(self).mapping_1g());
        assert(self.additional_wf()) by {broadcast use PageTable::reveal_page_table_additional_wf;}        
        assert(self.va_addr_valid()) by {
            va_addr_valid_proof::<TABLE_TYPE>();
        };
    }

    pub fn remove_l2_entry(
        &mut self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l2_p: PageMapPtr,
        target_l1_p: PageMapPtr,
    ) -> (ret:(PageMapPtr, Tracked<PointsTo<PageMap>>))
        requires
            old(self).wf(),
            old(self).kernel_l4_end <= target_l4i < 512,
            0 <= target_l3i < 512,
            0 <= target_l2i < 512,
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
            forall|i: L1Index| #![auto] 0 <= i < 512 ==> old(self).spec_resolve_mapping_4k_l1(
                target_l4i,
                target_l3i,
                target_l2i,
                i
            ) is None,
        ensures
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
        broadcast use PageTable::reveal_page_table_wf;
        broadcast use PageTable::reveal_page_table_levels_wf;
        // broadcast use PageTable::reveal_page_table_disjoint_wf;
        // broadcast use PageTable::reveal_page_table_mappings_wf;
        // broadcast use PageTable::reveal_page_table_additional_wf;

        assert forall |i: L4Index| #![auto]  0 <= i < 512 ==> (va_4k_valid(spec_index2va((target_l4i, target_l3i, target_l2i, i)))) by {
            va_lemma();
        };
        let tracked mut l2_perm = self.l2_tables.borrow_mut().tracked_remove(target_l2_p);
        proof { mem_valid_zero(); }
        page_map_set(
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
        );
        proof {
            self.l2_tables.borrow_mut().tracked_insert(target_l2_p, l2_perm);
            self.l1_rev_map = Ghost(self.l1_rev_map.view().remove(
                target_l1_p,
            ));
        }
        let tracked mut l1_perm = self.l1_tables.borrow_mut().tracked_remove(target_l1_p);
        let ret = (target_l1_p, Tracked(l1_perm));
        assert(self.wf_l4());
        assert(self.wf_l3());
        assert(self.wf_l2()) by {
            broadcast use PageTable::reveal_page_table_wf;
            broadcast use PageTable::reveal_page_table_levels_wf;
            broadcast use PageTable::reveal_page_table_disjoint_wf;
            broadcast use PageTable::reveal_page_table_mappings_wf;
            broadcast use PageTable::reveal_page_table_additional_wf;
            assert(forall|p: PageMapPtr, i: L2Index|
            #![auto]
            old(self).l2_tables.view().dom().contains(p) && 0 <= i < 512 && (p != target_l2_p || i != target_l2i)
                && old(self).l2_tables.view().spec_index(p).value().spec_index(i).perm.present
                && !old(self).l2_tables.view().spec_index(p).value().spec_index(i).perm.ps ==>
                    old(self).l2_tables.view().spec_index(p).value().spec_index(i).addr != target_l1_p);
        };
        assert(self.wf_l1());
        assert(self.disjoint_wf()) by { broadcast use PageTable::reveal_page_table_disjoint_wf; };
        assert(self.mappings_wf()) by {
            broadcast use PageTable::reveal_page_table_mappings_wf;
            assert(self.wf_mapping_4k())
                by {
                    broadcast use PageTable::reveal_page_table_mappings_wf;
                    assert(forall|l4i: L4Index, l3i: L3Index|
                        #![trigger self.spec_resolve_mapping_l3(l4i,l3i)]
                        #![trigger old(self).spec_resolve_mapping_l3(l4i,l3i)]
                        self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 
                        ==> self.spec_resolve_mapping_l3(l4i, l3i) =~= old(
                            self,
                        ).spec_resolve_mapping_l3(l4i, l3i));
                    assert(forall|l4i: L4Index, l3i: L3Index,|
                        #![trigger self.spec_resolve_mapping_l3(l4i,l3i)]
                        self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 
                            && self.spec_resolve_mapping_l3(l4i, l3i) is Some && !((
                            target_l4i,
                            target_l3i,
                        ) =~= (l4i, l3i)) ==> self.spec_resolve_mapping_l3(
                            l4i,
                            l3i,
                        )->0.addr != target_l2_p) by {
                        old(self).internal_resolve_disjoint();
                    };
                    assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                        #![trigger self.spec_resolve_mapping_l2(l4i,l3i,l2i)]
                        #![trigger old(self).spec_resolve_mapping_l2(l4i,l3i,l2i)]
                        self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && !((
                            target_l4i,
                            target_l3i,
                            target_l2i,
                        ) == (l4i, l3i, l2i)) ==> self.spec_resolve_mapping_l2(l4i, l3i, l2i) =~= old(
                            self,
                        ).spec_resolve_mapping_l2(l4i, l3i, l2i));
                    assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index,|
                        #![trigger self.spec_resolve_mapping_l2(l4i,l3i,l2i)]
                        self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 
                            && self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some && !((
                            target_l4i,
                            target_l3i,
                            target_l2i,
                        ) =~= (l4i, l3i, l2i)) ==> self.spec_resolve_mapping_l2(
                            l4i,
                            l3i,
                            l2i,
                        )->0.addr != target_l1_p) by {
                        old(self).internal_resolve_disjoint();
                    };
                    assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
                        #![trigger self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                        #![trigger old(self).spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                        self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i < 512 ==> old(
                            self,
                        ).spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i) == 
                        self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i));
                };
                assert(self.wf_mapping_2m()) by {
                    broadcast use PageTable::reveal_page_table_mappings_wf;
                    assert(forall|l4i: L4Index, l3i: L3Index|
                        #![trigger self.spec_resolve_mapping_l3(l4i,l3i)]
                        #![trigger old(self).spec_resolve_mapping_l3(l4i,l3i)]
                        self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && !((
                            target_l4i,
                            target_l3i,
                        ) =~= (l4i, l3i)) ==> self.spec_resolve_mapping_l3(l4i, l3i) =~= old(
                            self,
                        ).spec_resolve_mapping_l3(l4i, l3i));
                    assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index,|
                        #![trigger self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                        #![trigger old(self).spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                        self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512
                            && !((target_l4i, target_l3i, target_l2i) =~= (l4i, l3i, l2i))
                            ==> self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is Some == old(
                            self,
                        ).spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is Some);
                };
                assert(self.wf_mapping_1g()) by {
                    broadcast use PageTable::reveal_page_table_mappings_wf;
                    assert(forall|l4i: L4Index, l3i: L3Index|
                        #![trigger self.spec_resolve_mapping_1g_l3(l4i,l3i)]
                        #![trigger old(self).spec_resolve_mapping_1g_l3(l4i,l3i)]
                        self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && (l4i, l3i) != (
                            target_l4i,
                            target_l3i,
                        ) ==> old(self).spec_resolve_mapping_1g_l3(l4i, l3i)
                            =~= self.spec_resolve_mapping_1g_l3(l4i, l3i));
                };
        }
        
        assert(self.additional_wf()) by {broadcast use PageTable::reveal_page_table_additional_wf;}
        assert(self.page_closure() =~= old(self).page_closure().remove(target_l1_p)) by {
            broadcast use PageTable::reveal_page_table_wf;
            broadcast use PageTable::reveal_page_table_levels_wf;
            broadcast use PageTable::reveal_page_table_disjoint_wf;
            broadcast use PageTable::reveal_page_table_mappings_wf;
            broadcast use PageTable::reveal_page_table_additional_wf;
        }       
        assert(self.va_addr_valid()) by {
            va_addr_valid_proof::<TABLE_TYPE>();
        };
        return ret;
    }

    pub fn remove_l3_entry(
        &mut self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l3_p: PageMapPtr,
        target_l2_p: PageMapPtr,
    ) -> (ret:(PageMapPtr, Tracked<PointsTo<PageMap>>))
        requires
            old(self).wf(),
            old(self).kernel_l4_end <= target_l4i < 512,
            0 <= target_l3i < 512,
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
            forall|i: L2Index| #![auto] 0 <= i < 512 ==> old(self).spec_resolve_mapping_l2(
                target_l4i,
                target_l3i,
                i
            ) is None,
            forall|i: L2Index| #![auto] 0 <= i < 512 ==> old(self).spec_resolve_mapping_2m_l2(
                target_l4i,
                target_l3i,
                i
            ) is None,
        ensures
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
        broadcast use PageTable::reveal_page_table_wf;
        broadcast use PageTable::reveal_page_table_levels_wf;
        // broadcast use PageTable::reveal_page_table_disjoint_wf;
        // broadcast use PageTable::reveal_page_table_mappings_wf;
        // broadcast use PageTable::reveal_page_table_additional_wf;

        let tracked mut l3_perm = self.l3_tables.borrow_mut().tracked_remove(target_l3_p);
        proof { mem_valid_zero(); }
        page_map_set(
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
        );
        proof {
            self.l3_tables.borrow_mut().tracked_insert(target_l3_p, l3_perm);
            self.l2_rev_map = Ghost(self.l2_rev_map.view().remove(
                target_l2_p,
            ));
        }
        let tracked mut l2_perm = self.l2_tables.borrow_mut().tracked_remove(target_l2_p);
        let ret = (target_l2_p, Tracked(l2_perm));
        assert(self.wf_l4());
        assert(self.wf_l3()) by {
            broadcast use PageTable::reveal_page_table_disjoint_wf;
            broadcast use PageTable::reveal_page_table_mappings_wf;
            broadcast use PageTable::reveal_page_table_additional_wf;
            assert(forall|p: PageMapPtr, i: L3Index|
            #![auto]
            old(self).l3_tables.view().dom().contains(p) && 0 <= i < 512 && p != target_l3_p
                && old(self).l3_tables.view().spec_index(p).value().spec_index(i).perm.present
                && !old(self).l3_tables.view().spec_index(p).value().spec_index(i).perm.ps ==>
                    old(self).l3_tables.view().spec_index(p).value().spec_index(i).addr != target_l2_p);
        };
        assert(self.wf_l2()) by {
            broadcast use PageTable::reveal_page_table_disjoint_wf;
            broadcast use PageTable::reveal_page_table_mappings_wf;
            broadcast use PageTable::reveal_page_table_additional_wf;
            assert(forall|l4i: L4Index, l3i: L3Index|
                #![trigger self.spec_resolve_mapping_l3(l4i,l3i)]
                #![trigger old(self).spec_resolve_mapping_l3(l4i,l3i)]
                self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && !((
                    target_l4i,
                    target_l3i,
                ) == (l4i, l3i))
                 ==> self.spec_resolve_mapping_l3(l4i, l3i) =~= old(
                    self,
                ).spec_resolve_mapping_l3(l4i, l3i));
        };
        assert(self.wf_l1()) by {
            broadcast use PageTable::reveal_page_table_disjoint_wf;
            broadcast use PageTable::reveal_page_table_mappings_wf;
            broadcast use PageTable::reveal_page_table_additional_wf;
            assert(forall|l4i: L4Index, l3i: L3Index|
                #![trigger self.spec_resolve_mapping_l3(l4i,l3i)]
                #![trigger old(self).spec_resolve_mapping_l3(l4i,l3i)]
                self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && !((
                    target_l4i,
                    target_l3i,
                ) == (l4i, l3i))
                 ==> self.spec_resolve_mapping_l3(l4i, l3i) =~= old(
                    self,
                ).spec_resolve_mapping_l3(l4i, l3i));
            
            assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger self.spec_resolve_mapping_l2(l4i,l3i,l2i)]
                #![trigger old(self).spec_resolve_mapping_l2(l4i,l3i,l2i)]
                self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && !((
                    target_l4i,
                    target_l3i,
                ) == (l4i, l3i))
                 ==> self.spec_resolve_mapping_l2(l4i, l3i,l2i) =~= old(
                    self,
                ).spec_resolve_mapping_l2(l4i, l3i,l2i));
        };
        assert(self.disjoint_wf()) by { broadcast use PageTable::reveal_page_table_disjoint_wf; };
        assert(self.mappings_wf()) by {
            broadcast use PageTable::reveal_page_table_mappings_wf;
            assert(self.wf_mapping_4k())
                by {
                    broadcast use PageTable::reveal_page_table_mappings_wf;
                    broadcast use PageTable::reveal_page_table_disjoint_wf;
                    assert(forall|l4i: L4Index, l3i: L3Index|
                        #![trigger self.spec_resolve_mapping_l3(l4i,l3i)]
                        #![trigger old(self).spec_resolve_mapping_l3(l4i,l3i)]
                        self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && !((
                            target_l4i,
                            target_l3i,
                        ) == (l4i, l3i))
                        ==> self.spec_resolve_mapping_l3(l4i, l3i) =~= old(
                            self,
                        ).spec_resolve_mapping_l3(l4i, l3i));
                    assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                        #![trigger self.spec_resolve_mapping_l2(l4i,l3i,l2i)]
                        #![trigger old(self).spec_resolve_mapping_l2(l4i,l3i,l2i)]
                        self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && !((
                            target_l4i,
                            target_l3i,
                        ) == (l4i, l3i))
                        ==> self.spec_resolve_mapping_l2(l4i, l3i,l2i) =~= old(
                            self,
                        ).spec_resolve_mapping_l2(l4i, l3i,l2i));
                    assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
                        #![trigger self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                        #![trigger old(self).spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                        self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i < 512 ==> old(
                            self,
                        ).spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i) == 
                        self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i));
                };
                assert(self.wf_mapping_2m()) by {
                    broadcast use PageTable::reveal_page_table_mappings_wf;
                    broadcast use PageTable::reveal_page_table_disjoint_wf;
                    assert(forall|l4i: L4Index, l3i: L3Index|
                        #![trigger self.spec_resolve_mapping_l3(l4i,l3i)]
                        #![trigger old(self).spec_resolve_mapping_l3(l4i,l3i)]
                        self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && !((
                            target_l4i,
                            target_l3i,
                        ) == (l4i, l3i))
                        ==> self.spec_resolve_mapping_l3(l4i, l3i) =~= old(
                            self,
                        ).spec_resolve_mapping_l3(l4i, l3i));
                    assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                        #![trigger self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                        #![trigger old(self).spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                        self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && !((
                            target_l4i,
                            target_l3i,
                        ) == (l4i, l3i))
                        ==> self.spec_resolve_mapping_2m_l2(l4i, l3i,l2i) =~= old(
                            self,
                        ).spec_resolve_mapping_2m_l2(l4i, l3i,l2i));
                };
                assert(self.wf_mapping_1g()) by {
                    broadcast use PageTable::reveal_page_table_mappings_wf;
                    broadcast use PageTable::reveal_page_table_disjoint_wf;
                    assert(forall|l4i: L4Index, l3i: L3Index|
                        #![trigger self.spec_resolve_mapping_1g_l3(l4i,l3i)]
                        #![trigger old(self).spec_resolve_mapping_1g_l3(l4i,l3i)]
                        self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && (l4i, l3i) != (
                            target_l4i,
                            target_l3i,
                        ) ==> old(self).spec_resolve_mapping_1g_l3(l4i, l3i)
                            =~= self.spec_resolve_mapping_1g_l3(l4i, l3i));
                };
        }
        
        assert(self.additional_wf()) by {broadcast use PageTable::reveal_page_table_additional_wf;}
        assert(self.page_closure() =~= old(self).page_closure().remove(target_l2_p)) by {
            broadcast use PageTable::reveal_page_table_wf;
            broadcast use PageTable::reveal_page_table_levels_wf;
            broadcast use PageTable::reveal_page_table_disjoint_wf;
            broadcast use PageTable::reveal_page_table_mappings_wf;
            broadcast use PageTable::reveal_page_table_additional_wf;
        };        
        assert(self.va_addr_valid()) by {
            va_addr_valid_proof::<TABLE_TYPE>();
        };
        return ret;
    }

    pub fn remove_l4_entry(
        &mut self,
        target_l4i: L4Index,
        target_l3_p: PageMapPtr,
    ) -> (ret:(PageMapPtr, Tracked<PointsTo<PageMap>>))
        requires
            old(self).wf(),
            old(self).kernel_l4_end <= target_l4i < 512,
            old(self).spec_resolve_mapping_l4(target_l4i) is Some,
            old(self).spec_resolve_mapping_l4(target_l4i)->0.addr
                == target_l3_p,
            forall|i: L3Index| #![auto] 0 <= i < 512 ==> old(self).spec_resolve_mapping_l3(
                target_l4i,
                i
            ) is None,
            forall|i: L3Index| #![auto] 0 <= i < 512 ==> old(self).spec_resolve_mapping_1g_l3(
                target_l4i,
                i
            ) is None,
        ensures
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
        broadcast use PageTable::reveal_page_table_wf;
        broadcast use PageTable::reveal_page_table_levels_wf;
        // broadcast use PageTable::reveal_page_table_disjoint_wf;
        // broadcast use PageTable::reveal_page_table_mappings_wf;
        // broadcast use PageTable::reveal_page_table_additional_wf;

        let tracked mut l4_perm = self.l4_table.borrow_mut().tracked_remove(self.cr3);
        proof {
            mem_valid_zero();
        }
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
        page_map_set(
            self.cr3,
            Tracked(&mut l4_perm),
            target_l4i,
            zero_entry,
        );
        proof {
            self.l4_table.borrow_mut().tracked_insert(self.cr3, l4_perm);
            self.l3_rev_map = Ghost(self.l3_rev_map.view().remove(
                target_l3_p,
            ));
        }
        let tracked mut l3_perm = self.l3_tables.borrow_mut().tracked_remove(target_l3_p);
        let ret = (target_l3_p, Tracked(l3_perm));
        assert(self.levels_wf()) by {
        assert(self.wf_l4()) by {
            broadcast use PageTable::reveal_page_table_disjoint_wf;
            broadcast use PageTable::reveal_page_table_mappings_wf;
            broadcast use PageTable::reveal_page_table_additional_wf;
            assert(forall|i: L4Index|
            #![auto]
            old(self).l4_table.view().dom().contains(self.cr3) && self.kernel_l4_end <= i < 512 && i != target_l4i
                && old(self).l4_table.view().spec_index(self.cr3).value().spec_index(i).perm.present
                && !old(self).l4_table.view().spec_index(self.cr3).value().spec_index(i).perm.ps ==>
                    old(self).l4_table.view().spec_index(self.cr3).value().spec_index(i).addr != target_l3_p);
        };
        assert(self.wf_l3()) by {
            broadcast use PageTable::reveal_page_table_disjoint_wf;
            broadcast use PageTable::reveal_page_table_mappings_wf;
            broadcast use PageTable::reveal_page_table_additional_wf;
            assert(forall|l4i: L4Index|
                #![trigger self.spec_resolve_mapping_l4(l4i)]
                #![trigger old(self).spec_resolve_mapping_l4(l4i)]
                self.kernel_l4_end <= l4i < 512 && !(target_l4i == l4i)
                 ==> self.spec_resolve_mapping_l4(l4i) =~= old(
                    self,
                ).spec_resolve_mapping_l4(l4i));
            // assert(forall|p: PageMapPtr, i: L3Index|
            // #![auto]
            // old(self).l3_tables@.dom().contains(p) && 0 <= i < 512 && p != target_l3_p
            //     && old(self).l3_tables@[p].value()[i].perm.present
            //     && !old(self).l3_tables@[p].value()[i].perm.ps ==>
            //         old(self).l3_tables@[p].value()[i].addr != target_l2_p);
        };
        assert(self.wf_l2()) by {
            broadcast use PageTable::reveal_page_table_disjoint_wf;
            broadcast use PageTable::reveal_page_table_mappings_wf;
            broadcast use PageTable::reveal_page_table_additional_wf;
            assert(forall|l4i: L4Index, l3i: L3Index|
                #![trigger self.spec_resolve_mapping_l3(l4i,l3i)]
                #![trigger old(self).spec_resolve_mapping_l3(l4i,l3i)]
                self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && !(target_l4i == l4i)
                 ==> self.spec_resolve_mapping_l3(l4i, l3i) =~= old(
                    self,
                ).spec_resolve_mapping_l3(l4i, l3i));
        };
        assert(self.wf_l1()) by {
            broadcast use PageTable::reveal_page_table_disjoint_wf;
            broadcast use PageTable::reveal_page_table_mappings_wf;
            broadcast use PageTable::reveal_page_table_additional_wf;
            assert(forall|l4i: L4Index, l3i: L3Index|
                #![trigger self.spec_resolve_mapping_l3(l4i,l3i)]
                #![trigger old(self).spec_resolve_mapping_l3(l4i,l3i)]
                self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && !(target_l4i == l4i)
                 ==> self.spec_resolve_mapping_l3(l4i, l3i) =~= old(
                    self,
                ).spec_resolve_mapping_l3(l4i, l3i));
            
            assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger self.spec_resolve_mapping_l2(l4i,l3i,l2i)]
                #![trigger old(self).spec_resolve_mapping_l2(l4i,l3i,l2i)]
                self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && !(target_l4i == l4i)
                 ==> self.spec_resolve_mapping_l2(l4i, l3i,l2i) =~= old(
                    self,
                ).spec_resolve_mapping_l2(l4i, l3i,l2i));
        };
        };
        assert(self.disjoint_wf()) by { broadcast use PageTable::reveal_page_table_disjoint_wf; };
        assert(self.mappings_wf()) by {
            broadcast use PageTable::reveal_page_table_mappings_wf;
            assert(self.wf_mapping_4k())
                by {
                    broadcast use PageTable::reveal_page_table_mappings_wf;
                    broadcast use PageTable::reveal_page_table_disjoint_wf;
                    assert(forall|l4i: L4Index, l3i: L3Index|
                        #![trigger self.spec_resolve_mapping_l3(l4i,l3i)]
                        #![trigger old(self).spec_resolve_mapping_l3(l4i,l3i)]
                        self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && !(
                            target_l4i
                        == l4i)
                        ==> self.spec_resolve_mapping_l3(l4i, l3i) =~= old(
                            self,
                        ).spec_resolve_mapping_l3(l4i, l3i));
                    assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                        #![trigger self.spec_resolve_mapping_l2(l4i,l3i,l2i)]
                        #![trigger old(self).spec_resolve_mapping_l2(l4i,l3i,l2i)]
                        self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && !(
                            target_l4i == l4i)
                        ==> self.spec_resolve_mapping_l2(l4i, l3i,l2i) =~= old(
                            self,
                        ).spec_resolve_mapping_l2(l4i, l3i,l2i));
                    assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
                        #![trigger self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                        #![trigger old(self).spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                        self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i < 512 ==> old(
                            self,
                        ).spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i) == 
                        self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i));
                };
                assert(self.wf_mapping_2m()) by {
                    broadcast use PageTable::reveal_page_table_mappings_wf;
                    broadcast use PageTable::reveal_page_table_disjoint_wf;
                    assert(forall|l4i: L4Index, l3i: L3Index|
                        #![trigger self.spec_resolve_mapping_l3(l4i,l3i)]
                        #![trigger old(self).spec_resolve_mapping_l3(l4i,l3i)]
                        self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && !(
                            target_l4i == l4i)
                        ==> self.spec_resolve_mapping_l3(l4i, l3i) =~= old(
                            self,
                        ).spec_resolve_mapping_l3(l4i, l3i));
                    assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                        #![trigger self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                        #![trigger old(self).spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                        self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && !(
                            target_l4i == l4i)
                        ==> self.spec_resolve_mapping_2m_l2(l4i, l3i,l2i) =~= old(
                            self,
                        ).spec_resolve_mapping_2m_l2(l4i, l3i,l2i));
                };
                assert(self.wf_mapping_1g()) by {
                    broadcast use PageTable::reveal_page_table_mappings_wf;
                    broadcast use PageTable::reveal_page_table_disjoint_wf;
                    assert(forall|l4i: L4Index, l3i: L3Index|
                        #![trigger self.spec_resolve_mapping_1g_l3(l4i,l3i)]
                        #![trigger old(self).spec_resolve_mapping_1g_l3(l4i,l3i)]
                        self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && l4i != 
                            target_l4i ==> old(self).spec_resolve_mapping_1g_l3(l4i, l3i)
                            =~= self.spec_resolve_mapping_1g_l3(l4i, l3i));
                };
        }
        
        assert(self.additional_wf()) by {broadcast use PageTable::reveal_page_table_additional_wf;}
        assert(self.page_closure() =~= old(self).page_closure().remove(target_l3_p)) by {
            broadcast use PageTable::reveal_page_table_wf;
            broadcast use PageTable::reveal_page_table_levels_wf;
            broadcast use PageTable::reveal_page_table_disjoint_wf;
            broadcast use PageTable::reveal_page_table_mappings_wf;
            broadcast use PageTable::reveal_page_table_additional_wf;
        };        
        assert(self.va_addr_valid()) by {
            va_addr_valid_proof::<TABLE_TYPE>();
        };
        return ret;
    }

}

} // verus!
