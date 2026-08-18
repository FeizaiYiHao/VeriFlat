use vstd::prelude::*;
use vstd::set::lemma_set_remove_len;

mod mmap_4k_create_entry_install;
mod mmap_4k_context;
mod mmap_4k_syscall_def;
pub use mmap_4k_syscall_def::{
    mmap_4k_range_empty,
    mmap_4k_range_mapped,
    mmap_4k_raw_range_mapped,
};
mod mmap_4k_raw_range;
mod mmap_4k_range_induction;
mod mmap_4k_syscall;
mod mmap_4k_install_one;
mod mmap_4k_prepare_one;
mod mmap_4k_map_one;
mod mmap_4k_range;
mod mmap_4k_entry;

verus! {

use crate::*;
use mmap_4k_context::{staged_4k_page_op_ensures, staged_4k_page_op_requires};

impl KernelK {
    /// Publish one staged 4K page at a fresh virtual address whose L1 table
    /// already exists.
    ///
    /// The caller holds the page, owner-thread, and target-page-table write
    /// locks. The thread lock is needed because mapping consumes the page from
    /// its temporary allocation cache and charges its quota. Hidden page/thread
    /// metadata is updated while the kernel phase is Acquire; the published PTE
    /// store is the operation that closes the section into Release. The caller
    /// later ends the kernel step, which observes the changed `PageTableU` and
    /// records exactly one non-stuttering transition.
    pub fn map_owned_4k_page(
        &mut self,
        page_ptr: PagePtr,
        thread_ptr: RwLockThreadPtr,
        pagetable_ptr: RwLockPageTableRoot,
        va: VAddr,
        write: bool,
        execute_disable: bool,
        Tracked(lctx): Tracked<&mut LocalContext>,
        page_lock_perm: Tracked<&LockPerm>,
        thread_lock_perm: Tracked<&LockPerm>,
        pagetable_lock_perm: Tracked<&LockPerm>,
    )
        requires
            staged_4k_page_op_requires(
                old(self), old(lctx), page_ptr, thread_ptr, pagetable_ptr, va,
                page_lock_perm.view(), thread_lock_perm.view(),
                pagetable_lock_perm.view(),
            ),
            old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k().dom().contains(va)
                == false,
            old(self).pagetable_map.spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(
                spec_va2index(va).0,
                spec_va2index(va).1,
                spec_va2index(va).2,
            ) is Some,
        ensures
            staged_4k_page_op_ensures(
                final(self), final(lctx), old(self), old(lctx), page_ptr,
                thread_ptr, pagetable_ptr, page_lock_perm.view(),
                thread_lock_perm.view(), pagetable_lock_perm.view(),
            ),
            kernel_k_to_kernel_u(*final(self))
                != kernel_k_to_kernel_u(*old(self)),
            final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                == PageState::Mapped4k,
            final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().mappings()
                == Set::empty().insert((pagetable_ptr, va)),
            final(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count == 1,
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k()
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k().insert(
                    va,
                    MapEntry {
                        addr: page_ptr,
                        present: true,
                        write,
                        execute_disable,
                    },
                ),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view()
                .spec_resolve_mapping_l4(spec_va2index(va).0)
                == old(self).pagetable_map.spec_index(pagetable_ptr).view()
                    .spec_resolve_mapping_l4(spec_va2index(va).0),
            final(self).pagetable_map.spec_index(pagetable_ptr).view()
                .spec_resolve_mapping_l3(spec_va2index(va).0, spec_va2index(va).1)
                == old(self).pagetable_map.spec_index(pagetable_ptr).view()
                    .spec_resolve_mapping_l3(spec_va2index(va).0, spec_va2index(va).1),
            final(self).pagetable_map.spec_index(pagetable_ptr).view()
                .spec_resolve_mapping_l2(
                    spec_va2index(va).0,
                    spec_va2index(va).1,
                    spec_va2index(va).2,
                )
                == old(self).pagetable_map.spec_index(pagetable_ptr).view()
                    .spec_resolve_mapping_l2(
                        spec_va2index(va).0,
                        spec_va2index(va).1,
                        spec_va2index(va).2,
                    ),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger final(self).pagetable_map.spec_index(pagetable_ptr)
                    .view().spec_resolve_mapping_l2(l4i, l3i, l2i)]
                final(self).pagetable_map.spec_index(pagetable_ptr).view()
                    .kernel_l4_end <= l4i && pei_valid(l4i)
                    && pei_valid(l3i)
                    && pei_valid(l2i)
                ==> final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(l4i, l3i, l2i)
                    == old(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(l4i, l3i, l2i),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().page_closure()
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().page_closure(),
    {
        let page_index = page_ptr2page_index(page_ptr);
        let indices = va2index(va);
        assert(
            self.pagetable_map.perms_wf()
            && self.pagetable_map.spec_index(pagetable_ptr).inv()
            && self.page_array.inv()
            && self.page_array.spec_index(page_index).view().inv()
            && self.thread_map.perms_wf()
            && self.thread_map.spec_index(thread_ptr).inv()
        ) by {
            reveal(pagetable_perms_wf);
            reveal(page_array_wf);
            reveal(thread_perms_wf);
        };
        let target_l1_ptr;
        {
            let pagetable = self.pagetable_map.borrow(
                pagetable_ptr,
                pagetable_lock_perm,
            );
            let l4_entry = pagetable.get_entry_l4(indices.0).unwrap();
            let l3_entry = pagetable.get_entry_l3(indices.0, indices.1, &l4_entry).unwrap();
            let l2_entry = pagetable.get_entry_l2(
                indices.0,
                indices.1,
                indices.2,
                &l3_entry,
            ).unwrap();
            target_l1_ptr = l2_entry.addr;
        }

        let ghost old_page_lock_id = self.page_array.lock_id_by_index(page_index);
        {
            let page = self.page_array.borrow_mut(
                page_index,
                Tracked(&*lctx),
                page_lock_perm,
            );
            let Tracked(_published_contents_perm) = take_perm_4k(page);
            page.state = PageState::Mapped4k;
            page.mappings = Ghost(Set::empty().insert((pagetable_ptr, va)));
            page.ref_count = 1;
        }
        {
            let thread = self.thread_map.borrow_mut(
                thread_ptr,
                Tracked(&*lctx),
                thread_lock_perm,
            );
            thread.temp_alloc_cache_4k = Ghost(
                thread.temp_alloc_cache_4k.view().remove(page_ptr),
            );
            thread.quota_4k = thread.quota_4k - 1;
        }
        let target_entry = MapEntry {
            addr: page_ptr,
            present: true,
            write,
            execute_disable,
        };
        proof {
            assert(spec_index2va(indices) == va) by {
                spec_va_4k_index_roundtrip();
            };
        }
        let pagetable = self.pagetable_map.borrow_mut(
            pagetable_ptr,
            Tracked(&mut *lctx),
            pagetable_lock_perm,
        );
        pagetable.map_4k_page(
            indices.0,
            indices.1,
            indices.2,
            indices.3,
            target_l1_ptr,
            &target_entry,
            Tracked(&mut *lctx),
        );

        proof {
            assert(lctx.lock_entry_contains_for(
                old_page_lock_id,
                KernelObjId::Page(page_index),
                MUTABLE_LOCK_ID,
            )) by { reveal(lock_id_aligned); };
            lctx.update_lock_id(
                KernelObjId::Page(page_index),
                old_page_lock_id,
                self.page_array.lock_id_by_index(page_index),
            );
            assert(self.subsystems_inv()) by {
                assert(self.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
                assert(pagetable_perms_wf(self.pagetable_map)) by { reveal(pagetable_perms_wf); };
                assert(page_array_wf(self.page_array)) by { reveal(page_array_wf); };
                assert(thread_perms_wf(self.thread_map)) by {
                    reveal(thread_perms_wf);
                    reveal(thread_temp_alloc_empty_unless_wlocked);
                    reveal(thread_free_quota_pending_empty_unless_wlocked);
                    lemma_set_remove_len(old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view(), page_ptr);
                };
            };
            assert(self.memory_management_inv()) by {
                assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    allocator_4k_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_4k_map, self.allocator_4k_map);
                    allocator_2m_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_2m_map, self.allocator_2m_map);
                    allocator_1g_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_1g_map, self.allocator_1g_map);
                };
                assert(container_page_owner_wf(self.container_map, self.page_array)) by { container_page_owner_wf_preserved_for_owning_container_eq(old(self).container_map, self.container_map, old(self).page_array, self.page_array); };
                assert(hugepage_2m_wf(self.page_array)) by { hugepage_2m_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array); };
                assert(hugepage_1g_wf(self.page_array)) by { hugepage_1g_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array); };
                assert(page_pagetable_wf(self.pagetable_map, self.page_array)) by { page_pagetable_wf_preserved_for_4k_mapping_insert(old(self).pagetable_map, self.pagetable_map, old(self).page_array, self.page_array, pagetable_ptr, page_ptr, va); };
                assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by {
                    reveal(process_thread_wf);
                    reveal(process_pagetable_match);
                    container_process_page_pagetable_wf_preserved_for_4k_mapping_insert(self.container_map, self.process_map, old(self).pagetable_map, self.pagetable_map, old(self).page_array, self.page_array, pagetable_ptr, page_ptr, va);
                };
                assert(container_pages_wf(self.page_array, self.container_map)) by { container_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).container_map, self.container_map); };
                assert(process_pages_wf(self.page_array, self.process_map)) by { process_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).process_map, self.process_map); };
                assert(pagetable_pages_wf(self.pagetable_map, self.page_array)) by { reveal(pagetable_pages_wf); };
                assert(iommu_table_pages_wf(self.iommu_table_map, self.page_array)) by { reveal(iommu_table_pages_wf); };
                assert(thread_pages_wf(self.thread_map, self.page_array)) by { thread_pages_wf_preserved_for_page_state_eq(old(self).thread_map, self.thread_map, old(self).page_array, self.page_array); };
                assert(pcid_allocator_pages_wf(self.page_array, self.pcid_allocator_map)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).pcid_allocator_map, self.pcid_allocator_map); };
                assert(thread_staged_pages_wf(self.thread_map, self.page_array)) by {
                    reveal(thread_staged_pages_4k_wf);
                    thread_staged_pages_2m_wf_preserved_for_eq(old(self).thread_map, self.thread_map, old(self).page_array, self.page_array);
                    thread_staged_pages_1g_wf_preserved_for_eq(old(self).thread_map, self.thread_map, old(self).page_array, self.page_array);
                };
                assert(endpoint_pages_wf(self.endpoint_map, self.page_array)) by { endpoint_pages_wf_preserved_for_page_state_eq(old(self).endpoint_map, self.endpoint_map, old(self).page_array, self.page_array); };
                assert(process_pagetable_match(self.process_map, self.pagetable_map)) by { reveal(process_pagetable_match); };
                assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    reveal(thread_quota_4k_fields_unchanged);
                    reveal(thread_quota_2m_fields_unchanged);
                    reveal(thread_quota_1g_fields_unchanged);
                    container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields_forall();
                    container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields_forall();
                    container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields_forall();
                };
                assert(container_allocator_free_4k_page_wf(self.allocator_4k_map, self.page_array)) by { container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(self.allocator_4k_map, old(self).page_array, self.page_array, page_index); };
                assert(container_allocator_free_2m_page_wf(self.allocator_2m_map, self.page_array)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(self.allocator_2m_map, old(self).page_array, self.page_array, page_index); };
                assert(container_allocator_free_1g_page_wf(self.allocator_1g_map, self.page_array)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(self.allocator_1g_map, old(self).page_array, self.page_array, page_index); };
            };
            assert(self.process_management_inv()) by {
                assert(thread_endpoint_ref_counter_wf(self.thread_map, self.endpoint_map)) by { reveal(thread_endpoint_ref_counter_wf); };
                assert(thread_endpoint_queue_wf(self.thread_map, self.endpoint_map)) by { reveal(thread_endpoint_queue_wf); };
                assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by { reveal(container_thread_endpoint_wf); };
                assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by { reveal(container_thread_scheduler_wf); };
                assert(container_thread_wf(self.container_map, self.thread_map)) by { reveal(container_thread_wf); };
                assert(process_thread_wf(self.process_map, self.thread_map)) by { reveal(process_thread_wf); };
                assert(thread_cpu_wf(self.thread_map, self.cpu_array)) by { reveal(thread_cpu_wf); };
            };
            assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by { reveal(cpu_dirty_map_contains_pagetable_pcid_match); };
            assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { tlb_wf_spec_preserved_for_4k_mapping_insert(self.cpu_tlb, self.cpu_array, old(self).pagetable_map, self.pagetable_map, pagetable_ptr, va); };
            assert(lock_id_aligned(self, &*lctx)) by {
                reveal(lock_id_aligned);
            };
            assert({
                let process_ptr = self.thread_map.spec_index(thread_ptr)
                    .view().owning_proc;
                &&& kernel_k_to_kernel_u(*old(self)).process_map.dom()
                    .contains(process_ptr)
                &&& kernel_k_to_kernel_u(*self).process_map.dom()
                    .contains(process_ptr)
                &&& !kernel_k_to_kernel_u(*old(self)).process_map
                    .spec_index(process_ptr).pagetable.mapping_4k.dom()
                    .contains(va)
                &&& kernel_k_to_kernel_u(*self).process_map
                    .spec_index(process_ptr).pagetable.mapping_4k.dom()
                    .contains(va)
            }) by {

                reveal(process_thread_wf);
                reveal(process_pagetable_match);
            };
        }
    }
}

}
