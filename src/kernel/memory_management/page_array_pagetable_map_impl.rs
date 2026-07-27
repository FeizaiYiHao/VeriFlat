use vstd::prelude::*;
use crate::*;
verus! {

    impl KernelK{
        pub fn kernel_add_mapping_4k(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, pagetable_root: RwLockPageTableRoot, page_index: PageIndex,
            target_l4i: L4Index,
            target_l3i: L3Index,
            target_l2i: L2Index,
            target_l1i: L2Index,
            target_l1_p: PageMapPtr,
            target_entry: &MapEntry,
            pagetable_lock_perm: Tracked<&LockPerm>)
            requires
                old(lctx).kernel_view_locking_state() is Acquire,

                cpu_id_valid(old(lctx).thread_id()),
                old(self).inv(),
                page_index_wf(page_index),
                // forall|i:PageIndex|
                //     #![trigger old(self).page_array[i]]
                //     page_index_wf(i) ==> wlock_requires(old(self).page_array[i]@, old(lctx)),

                forall|i:PageIndex|
                    #![trigger old(self).page_array[i]]
                    page_index_wf(i) ==> 
                    old(self).page_array[i]@.locked_by(old(lctx)) == false
                    ,
                
                forall|cpu_id:CpuId|
                    #![trigger old(self).cpu_array.spec_index(cpu_id)]
                    cpu_id_valid(cpu_id) && cpu_id != old(lctx).thread_id() ==> 
                    old(self).cpu_array.spec_index(cpu_id).view().locked_by(old(lctx)) == false
                    ,
                old(self).cpu_array.spec_index(old(lctx).thread_id()).view().rlocked_by(old(lctx)),
                old(self).page_array[page_index]@@.is_mapped(),
                old(self).page_array.spec_index(page_index).view().view().state is Mapped4k,
                old(lctx).lock_map_contains(KernelObjId::PageTable(pagetable_root)),
                old(lctx).lock_id_for_obj(KernelObjId::PageTable(pagetable_root)) == pagetable_root.to_lock_id(),

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
            let Tracked(page_lock_perm) = self.page_array.wlock(page_index, Tracked(lctx), Ghost(LockId{container: LockOwnerId::none(), process: LockOwnerId::none(), major: MAPPED_PAGE_LOCK_MAJOR, minor: page_index}));
            let mut page = self.page_array.take(page_index, Tracked(lctx), Tracked(&page_lock_perm));
            if page.ref_count == usize::MAX {
                self.page_array.put(page_index, Tracked(lctx), Tracked(&page_lock_perm), page);
                self.page_array.wunlock(page_index, Tracked(lctx), Tracked(page_lock_perm));
                
                // assert(self.inv()) by {
                    assert(page_pagetable_wf(self.pagetable_map, self.page_array)) by{
                        reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
                    };
                    assert(container_tree_wf(self.root_container, self.container_map));
                    assert(self.container_pages_wf()) by {
                        reveal(KernelK::container_pages_wf);
                    };
                    assert(self.process_pages_wf()) by {
                        reveal(KernelK::process_pages_wf);
                    };
                    assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                        reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf);
                    };
                    assert(container_process_wf(self.container_map, self.process_map)) by {
                        reveal(container_process_wf);
                    };
                    assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                        reveal(container_process_wf);
                        reveal(per_container_process_tree_wf);
                    };
                    assert(hugepage_2m_wf(self.page_array)) by {
                        page_ptr_lemma1();
                        page_ptr_2m_lemma();
                        page_ptr_1g_lemma();
                        page_index_lemma();
                        page_ptr_page_index_truncate_lemma();
                        reveal(hugepage_2m_wf);
                    };
                    assert(hugepage_1g_wf(self.page_array)) by {
                        page_ptr_lemma1();
                        page_ptr_2m_lemma();
                        page_ptr_1g_lemma();
                        page_index_lemma();
                        page_ptr_page_index_truncate_lemma();
                        reveal(hugepage_1g_wf);
                    };
                    assert(container_cpu_wf(self.container_map, self.cpu_array)) by {reveal(container_cpu_wf);};
                    assert(process_cpu_wf(self.process_map, self.cpu_array)) by {reveal(process_cpu_wf);};
                    assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
                        reveal(cpu_dirty_map_contains_container_processes);
                        reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                        reveal(cpu_dirty_map_proc_pcid_match);
                        reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                    };assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by {
                        reveal(tlb_wf_spec);
                    };
                    assert(process_pagetable_match(self.process_map, self.pagetable_map)) by {reveal(process_pagetable_match)};
                // };
                return;
            }
            assert(page.mappings@.contains((pagetable_root, vaddr)) == false) by {
                reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
            };
            page.ref_count = page.ref_count + 1;
            page.mappings = Ghost(page.mappings@.insert((pagetable_root, vaddr)));
            self.page_array.put(page_index, Tracked(lctx), Tracked(&page_lock_perm), page);

            let mut pagetable = self.pagetable_map.take(pagetable_root, Tracked(lctx), pagetable_lock_perm);
            pagetable.map_4k_page(target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
            self.pagetable_map.put(pagetable_root, Tracked(lctx), pagetable_lock_perm, pagetable);
            self.page_array.wunlock(page_index, Tracked(lctx), Tracked(page_lock_perm));

            // assert(self.inv()) by {
                assert(page_pagetable_wf(self.pagetable_map, self.page_array)) by{
                    reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
                };
                assert(container_tree_wf(self.root_container, self.container_map));
                assert(self.container_pages_wf()) by {
                    reveal(KernelK::container_pages_wf);
                };
                assert(self.process_pages_wf()) by {
                    reveal(KernelK::process_pages_wf);
                };
                assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf);
                };
                assert(container_process_wf(self.container_map, self.process_map)) by {
                    reveal(container_process_wf);
                };
                assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                    reveal(container_process_wf);
                    reveal(per_container_process_tree_wf);
                };
                assert(hugepage_2m_wf(self.page_array)) by {
                    page_ptr_lemma1();
                    page_ptr_2m_lemma();
                    page_ptr_1g_lemma();
                    page_index_lemma();
                    page_ptr_page_index_truncate_lemma();
                    reveal(hugepage_2m_wf);
                };
                assert(hugepage_1g_wf(self.page_array)) by {
                    page_ptr_lemma1();
                    page_ptr_2m_lemma();
                    page_ptr_1g_lemma();
                    page_index_lemma();
                    page_ptr_page_index_truncate_lemma();
                    reveal(hugepage_1g_wf);
                };
                assert(container_cpu_wf(self.container_map, self.cpu_array)) by {reveal(container_cpu_wf);};
                assert(process_cpu_wf(self.process_map, self.cpu_array)) by {reveal(process_cpu_wf);};
                assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb,self.pagetable_map)) by {
                    reveal(cpu_dirty_map_contains_container_processes);
                    reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                    reveal(cpu_dirty_map_proc_pcid_match);
                    reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                };
                
                assert(process_pagetable_match(self.process_map, self.pagetable_map)) by {
                    reveal(process_pagetable_match);
                    assert(forall|proc_ptr:RwLockProcessPtr|
                            #![trigger self.process_map.spec_index(proc_ptr).view().pagetable]
                            self.process_map.dom().contains(proc_ptr) 
                            ==>
                            self.pagetable_map.dom().contains(self.process_map.spec_index(proc_ptr).view().pagetable)
                            // &&
                            // {
                            //     |||
                            //     write_locked_by_same_thread(self.process_map.spec_index(proc_ptr), self.pagetable_map.spec_index(self.process_map.spec_index(proc_ptr).view().pagetable))
                            //     |||
                            //     {
                            //         self.pagetable_map.spec_index(self.process_map.spec_index(proc_ptr).view().pagetable).view().proc_ptr == proc_ptr
                            //         &&
                            //         self.pagetable_map.spec_index(self.process_map.spec_index(proc_ptr).view().pagetable).view().pcid_or_ioid() == self.process_map.spec_index(proc_ptr).view().pcid
                            //     }
                            // }
                        );
                    //     assert(forall|pt_ptr:RwLockPageTableRoot|
                    //         #![trigger self.pagetable_map.spec_index(pt_ptr).view().proc_ptr]
                    //         self.pagetable_map.dom().contains(pt_ptr)
                    //         ==>
                    //         self.process_map.dom().contains(self.pagetable_map.spec_index(pt_ptr).view().proc_ptr)
                    //         &&
                    //         {
                    //             |||
                    //             write_locked_by_same_thread(self.pagetable_map.spec_index(pt_ptr), self.process_map.spec_index(self.pagetable_map.spec_index(pt_ptr).view().proc_ptr))
                    //             |||
                    //             self.process_map.spec_index(self.pagetable_map.spec_index(pt_ptr).view().proc_ptr).view().pagetable == pt_ptr
                    //         }
                    //     );
                };
                assert(process_thread_wf(self.process_map, self.thread_map)) by {};
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by {
                    reveal(process_cpu_wf);
                    // reveal(cpu_dirty_map_proc_pcid_match);
                    reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                    reveal(tlb_wf_spec);
                    reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                    // reveal(process_pagetable_match);

                    assert(
                        forall|cpu_id:CpuId, pcid:Pcid|
                            #![trigger self.cpu_tlb.spec_index((cpu_id, pcid))]
                            cpu_id_valid(cpu_id)
                            &&
                            pcid_valid(pcid)
                            &&
                            pcid != KERNEL_DEFAULT_PCID
                            &&
                            self.cpu_tlb.spec_index((cpu_id, pcid)).is_empty() == false
                            ==>
                            self.pagetable_map.dom().contains(self.cpu_array.spec_index(cpu_id).view().view().tlb_dirty_bitmap()[pcid].unwrap().pagetable_ptr)
                            // single_cpu_single_pcid_tlb_subset_of_pagetable(self.cpu_tlb.spec_index((cpu_id, pcid)), self.pagetable_map.spec_index(self.cpu_array.spec_index(cpu_id).view().view().current_pagetable))
                    );
                    // assert(false);
                };
            // };
            return;
        }
    }
}
