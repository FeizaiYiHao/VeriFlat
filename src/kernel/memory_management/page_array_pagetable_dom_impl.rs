use vstd::prelude::*;
use crate::*;
verus! {

    impl Kernel{
        pub fn kernel_add_mapping_4k(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, pagetable_root: RwLockPageTableRoot, page_index: PageIndex,
            target_l4i: L4Index,
            target_l3i: L3Index,
            target_l2i: L2Index,
            target_l1i: L2Index,
            target_l1_p: PageMapPtr,
            target_entry: &MapEntry,
            pagetable_lock_perm: Tracked<&LockPerm>)
            requires
                old(self).inv(),
                page_index_wf(page_index),
                // forall|i:PageIndex|
                //     #![trigger old(self).page_array[i]]
                //     page_index_wf(i) ==> wlock_requires(old(self).page_array[i]@, old(lctx)),

                forall|i:PageIndex|
                    #![trigger old(self).page_array[i]]
                    page_index_wf(i) ==> 
                    old(self).page_array[i]@.locking_thread() is None
                    &&
                    old(self).page_array[i]@.serial_num() == old(lctx).locking_serial_num()
                    ,
                
                forall|cpu_id:CpuId|
                    #![trigger old(self).get_cpu(cpu_id)]
                    cpu_id_valid(cpu_id) ==> 
                    old(self).get_cpu(cpu_id).locking_thread() is None
                    &&
                    old(self).get_cpu(cpu_id).serial_num() == old(lctx).locking_serial_num()
                    ,

                old(self).page_array[page_index]@@.is_mapped(),
                old(lctx).lock_seq().len() != 0,
                old(lctx).lock_seq().last() == pagetable_root.to_lock_id(),

                old(self).pagetable_map.dom().contains(pagetable_root),
                old(self).pagetable_map[pagetable_root].wlocked_by(old(lctx)) == true,
                old(self).pagetable_map[pagetable_root].inv(),

                old(self).pagetable_map[pagetable_root]@.kernel_l4_end <= target_l4i < 512,
                0 <= target_l3i < 512,
                0 <= target_l2i < 512,
                0 <= target_l1i < 512,
                old(self).pagetable_map[pagetable_root]@.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
                old(self).pagetable_map[pagetable_root]@.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr
                    == target_l1_p,
                old(self).pagetable_map[pagetable_root]@.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
                page_ptr_valid(target_entry.addr),
                target_entry.present,
                target_entry.addr == page_index2page_ptr(page_index),

                pagetable_lock_perm.state() is WriteLock,
                pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
                pagetable_lock_perm.lock_id() == old(self).pagetable_map[pagetable_root].locking_thread() -> Write_lock_id,
        {
            proof{
                page_ptr_lemma();
            }
            let vaddr = index2va((target_l4i, target_l3i, target_l2i, target_l1i));
            let Tracked(page_lock_perm) = self.page_array.wlock_page(page_index, Tracked(lctx), Ghost(LockId{container: LockOwnerId::none(), process: LockOwnerId::none(), major: MAPPED_PAGE_LOCK_MAJOR, minor: page_index}));
            let mut page = self.page_array.take(page_index, Tracked(lctx), Tracked(&page_lock_perm));
            if page.ref_count == usize::MAX {
                self.page_array.put(page_index, Tracked(lctx), Tracked(&page_lock_perm), page);
                self.page_array.wunlock_page(page_index, Tracked(lctx), Tracked(page_lock_perm));
                // assert(self.page_array[page_index]@@ == old(self).page_array[page_index]@@);
                // assert(
                //     forall|p_i:PageIndex, pt_r: RwLockPageTableRoot, va: VAddr|
                //         #![trigger self.page_array[p_i]@@.mappings_4k@.contains((pt_r, va))]
                //         page_index_valid(p_i) ==>
                //         self.page_array[p_i]@@.mappings_4k@.contains((pt_r, va)) ==
                //             old(self).page_array[p_i]@@.mappings_4k@.contains((pt_r, va))
                // );
                // assert(self.page_array_pagetable_map_inv1());
                // assert(self.page_array_pagetable_map_inv2());
                // assert(self.pagetable_map_page_array_inv1());
                // assert(self.pagetable_map_page_array_inv2());
                
                assert(self.inv()) by {
                    assert(self.container_pages_wf()) by {
                        Self::container_pages_wf_proof();
                    };
                    assert(self.process_pages_wf()) by {
                        Self::process_pages_wf_proof();
                    };
                    assert(self.allocator_pages_wf()) by {
                        Self::allocator_pages_wf_proof();
                    };
                    assert(container_process_wf(self.container_map, self.process_map)) by {
                        container_process_wf_proof();
                    };
                    assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                        container_process_wf_proof();
                        per_container_process_tree_wf_proof();
                    };
                    assert(hugepage_2m_wf(self.page_array)) by {
                        page_ptr_lemma1();
                        page_ptr_2m_lemma();
                        page_ptr_1g_lemma();
                        page_index_lemma();
                        page_ptr_page_index_truncate_lemma();
                        hugepage_2m_wf_proof();
                    };
                    assert(hugepage_1g_wf(self.page_array)) by {
                        page_ptr_lemma1();
                        page_ptr_2m_lemma();
                        page_ptr_1g_lemma();
                        page_index_lemma();
                        page_ptr_page_index_truncate_lemma();
                        hugepage_1g_wf_proof();
                    };
                };
                return;
            }
            assert(page.mappings_4k@.contains((pagetable_root, vaddr)) == false);
            page.ref_count = page.ref_count + 1;
            page.mappings_4k = Ghost(page.mappings_4k@.insert((pagetable_root, vaddr)));
            self.page_array.put(page_index, Tracked(lctx), Tracked(&page_lock_perm), page);
            self.pagetable_map.map_4k_page(pagetable_root, Tracked(lctx), pagetable_lock_perm,  
                target_l4i,
                target_l3i,
                target_l2i,
                target_l1i,
                target_l1_p,
                target_entry,);
            self.page_array.wunlock_page(page_index, Tracked(lctx), Tracked(page_lock_perm));
            // assert(
            //     forall|cpu_id: CpuId|
            //         #![auto]
            //         cpu_id_valid(cpu_id) 
            //         // && usize_in_range::<PCID_MAX>(pcid) 
            //         ==> 
            //         old(self).get_cpu(cpu_id).view().tlb_dirty_bitmap.inv()
            // );
            // assert(
            //     forall|cpu_id: CpuId|
            //         #![auto]
            //         cpu_id_valid(cpu_id) 
            //         // && usize_in_range::<PCID_MAX>(pcid) 
            //         ==> 
            //         self.get_cpu(cpu_id).view().tlb_dirty_bitmap.inv()
            // );
            // assert(
            //     forall|cpu_id: CpuId, pcid:Pcid|
            //         #![trigger self.get_cpu(cpu_id).view().tlb_dirty_bitmap()[pcid]]
            //         #![trigger cpu_id_valid(cpu_id), usize_in_range::<PCID_MAX>(pcid)]
            //         cpu_id_valid(cpu_id) && usize_in_range::<PCID_MAX>(pcid) && self.get_cpu(cpu_id).view().tlb_dirty_bitmap()[pcid] is Some && pcid != self.get_pagetable(pagetable_root).view().pcid_or_ioid()
            //         ==> 
            //         old(self).cpu_array.get_tlb(cpu_id, pcid) == self.cpu_array.get_tlb(cpu_id, pcid)
            //         &&
            //         old(self).get_cpu(cpu_id).view().tlb_dirty_bitmap()[pcid].unwrap() == self.get_cpu(cpu_id).view().tlb_dirty_bitmap()[pcid].unwrap()
            //         &&
            //         self.get_cpu(cpu_id).view().tlb_dirty_bitmap()[pcid].unwrap() != pagetable_root
            //         &&
            //         old(self).get_pagetable(old(self).get_cpu(cpu_id).view().tlb_dirty_bitmap()[pcid].unwrap()) == self.get_pagetable(self.get_cpu(cpu_id).view().tlb_dirty_bitmap()[pcid].unwrap())
            // );
            // assert(
            //     forall|cpu_id: CpuId, pcid:Pcid|
            //         #![trigger self.get_cpu(cpu_id).view().tlb_dirty_bitmap()[pcid]]
            //         #![trigger cpu_id_valid(cpu_id), usize_in_range::<PCID_MAX>(pcid)]
            //         cpu_id_valid(cpu_id) && usize_in_range::<PCID_MAX>(pcid) && self.get_cpu(cpu_id).view().tlb_dirty_bitmap()[pcid] is Some && pcid != self.get_pagetable(pagetable_root).view().pcid_or_ioid()
            //         ==> 
            //         super::pagetable_tlb_spec::single_cpu_single_pcid_tlb_subset_of_pagetable(self.cpu_array.get_tlb(cpu_id, pcid), self.get_pagetable(self.get_cpu(cpu_id).view().tlb_dirty_bitmap()[pcid].unwrap()))
            // );

            // assert(self.cpu_tlb_submap_of_dirty_pagetable());
            // // assert(self.inv());
            // assert(self.inv()) by {
            //     assert(self.container_pages_wf()) by {
            //         Self::container_pages_wf_proof();
            //     };
            //     assert(self.process_pages_wf()) by {
            //         Self::process_pages_wf_proof();
            //     };
            //     assert(self.allocator_pages_wf()) by {
            //         Self::allocator_pages_wf_proof();
            //     };
            //     assert(self.container_process_wf()) by {
            //         Self::container_process_wf_proof();
            //     };
            //     assert(self.process_tree_wf()) by {
            //         Self::container_process_wf_proof();
            //         Self::process_tree_wf_proof();
            //     };
            //     assert(hugepage_2m_wf(self.page_array)) by {
            //         page_ptr_lemma1();
            //         page_ptr_2m_lemma();
            //         page_ptr_1g_lemma();
            //         page_index_lemma();
            //         page_ptr_page_index_truncate_lemma();
            //         hugepage_2m_wf_proof();
            //     };
            //     assert(hugepage_1g_wf(self.page_array)) by {
            //         page_ptr_lemma1();
            //         page_ptr_2m_lemma();
            //         page_ptr_1g_lemma();
            //         page_index_lemma();
            //         page_ptr_page_index_truncate_lemma();
            //         hugepage_1g_wf_proof();
            //     };
            // };
            return;
        }
    }
}