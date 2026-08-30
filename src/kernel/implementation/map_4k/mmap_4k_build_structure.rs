use vstd::prelude::*;

use crate::*;
use super::mmap_4k_context::{
    mmap_4k_allocation_ready,
    mmap_4k_held_context,
};
use super::mmap_4k_create_entry_install::MissingPageTableLevel;
use super::mmap_4k_install_one::install_one_mmap_4k_directory_page;

verus! {

#[derive(Clone, Copy)]
pub enum Mmap4kStructureBuild {
    Ready,
    NoQuota,
    InUse,
}

#[derive(Clone, Copy)]
enum Mmap4kDirectorySlot {
    Present,
    Missing,
    InUse,
}

    fn mmap_4k_l4_directory_slot<const TABLE_TYPE: PTType>(
        pagetable: &PageTable<TABLE_TYPE>,
        l4i: L4Index,
    ) -> (ret: Mmap4kDirectorySlot)
        requires
            pagetable.wf(),
            pagetable.kernel_l4_end <= l4i && pei_valid(l4i),
        ensures
            !(ret is InUse),
            ret is Present ==> pagetable.spec_resolve_mapping_l4(l4i) is Some,
            ret is Missing ==> pagetable.spec_resolve_mapping_l4(l4i) is None,
    {
        if pagetable.get_entry_l4(l4i).is_some() {
            Mmap4kDirectorySlot::Present
        } else {
            Mmap4kDirectorySlot::Missing
        }
    }

    fn mmap_4k_l3_directory_slot<const TABLE_TYPE: PTType>(
        pagetable: &PageTable<TABLE_TYPE>,
        l4i: L4Index,
        l3i: L3Index,
    ) -> (ret: Mmap4kDirectorySlot)
        requires
            pagetable.wf(),
            pagetable.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
        ensures
            ret is Present ==>
                pagetable.spec_resolve_mapping_l3(l4i, l3i) is Some,
            ret is InUse ==> {
                ||| pagetable.spec_resolve_mapping_l4(l4i) is None
                ||| pagetable.spec_resolve_mapping_1g_l3(l4i, l3i) is Some
            },
            ret is Missing ==> {
                &&& pagetable.spec_resolve_mapping_l4(l4i) is Some
                &&& pagetable.spec_resolve_mapping_l3(l4i, l3i) is None
                &&& pagetable.spec_resolve_mapping_1g_l3(l4i, l3i) is None
            },
    {
        let l4_entry = match pagetable.get_entry_l4(l4i) {
            Some(entry) => entry,
            None => return Mmap4kDirectorySlot::InUse,
        };
        if pagetable.get_entry_l3(l4i, l3i, &l4_entry).is_some() {
            return Mmap4kDirectorySlot::Present;
        }
        if pagetable.get_entry_1g_l3(l4i, l3i, &l4_entry).is_some() {
            Mmap4kDirectorySlot::InUse
        } else {
            Mmap4kDirectorySlot::Missing
        }
    }

    fn mmap_4k_l2_directory_slot<const TABLE_TYPE: PTType>(
        pagetable: &PageTable<TABLE_TYPE>,
        l4i: L4Index,
        l3i: L3Index,
        l2i: L2Index,
    ) -> (ret: Mmap4kDirectorySlot)
        requires
            pagetable.wf(),
            pagetable.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
        ensures
            ret is Present ==>
                pagetable.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some,
            ret is InUse ==> {
                ||| pagetable.spec_resolve_mapping_l4(l4i) is None
                ||| pagetable.spec_resolve_mapping_l3(l4i, l3i) is None
                ||| pagetable.spec_resolve_mapping_2m_l2(
                    l4i, l3i, l2i,
                ) is Some
            },
            ret is Missing ==> {
                &&& pagetable.spec_resolve_mapping_l3(l4i, l3i) is Some
                &&& pagetable.spec_resolve_mapping_l2(l4i, l3i, l2i) is None
                &&& pagetable.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is None
            },
    {
        let l4_entry = match pagetable.get_entry_l4(l4i) {
            Some(entry) => entry,
            None => return Mmap4kDirectorySlot::InUse,
        };
        let l3_entry = match pagetable.get_entry_l3(l4i, l3i, &l4_entry) {
            Some(entry) => entry,
            None => return Mmap4kDirectorySlot::InUse,
        };
        if pagetable.get_entry_l2(l4i, l3i, l2i, &l3_entry).is_some() {
            return Mmap4kDirectorySlot::Present;
        }
        if pagetable.get_entry_2m_l2(l4i, l3i, l2i, &l3_entry).is_some() {
            Mmap4kDirectorySlot::InUse
        } else {
            Mmap4kDirectorySlot::Missing
    }
}



    pub fn mmap_4k_build_one_structure(
        kernel: &mut KernelK,
        va: VAddr,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        process_ptr: RwLockProcessPtr,
        container_ptr: RwLockContainerPtr,
        cpu_id: CpuId,
        pagetable_ptr: RwLockPageTableRoot,
        quota_reserve: usize,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
        Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
    )
        requires
            mmap_4k_held_context(
                old(kernel), old(lctx), alloc_ptr_4k, thread_ptr, process_ptr,
                container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                pagetable_lock_perm,
            ),
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
            mmap_4k_allocation_ready(old(kernel), old(lctx)),
            va_4k_valid(va),
            quota_reserve <= usize::MAX - 3,
            old(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(kernel).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            old(kernel).thread_map.spec_index(thread_ptr).view().quota_4k
                >= 3 + quota_reserve,
            old(kernel).pagetable_map.spec_index(pagetable_ptr).view().wf(),
            old(kernel).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                <= spec_v2l4index(va),
            old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                .spec_4k_entry_useable(
                    spec_v2l4index(va), spec_v2l3index(va),
                    spec_v2l2index(va), spec_v2l1index(va),
                ),
        ensures
            mmap_4k_held_context(
                final(kernel), final(lctx), alloc_ptr_4k, thread_ptr, process_ptr,
                container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                pagetable_lock_perm,
            ),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
            mmap_4k_allocation_ready(final(kernel), final(lctx)),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|t: RwLockThreadPtr|
                #![trigger old(kernel).thread_map.spec_index(t)]
                #![trigger final(kernel).thread_map.spec_index(t)]
                (old(kernel).thread_map.dom().contains(t)
                    && old(kernel).thread_map.spec_index(t).locked_by_thread(old(lctx).thread_id()))
                == (final(kernel).thread_map.dom().contains(t)
                    && final(kernel).thread_map.spec_index(t).locked_by_thread(final(lctx).thread_id())),
            forall|t: RwLockThreadPtr|
                #![trigger old(kernel).thread_map.spec_index(t)]
                #![trigger final(kernel).thread_map.spec_index(t)]
                t != thread_ptr && old(kernel).thread_map.dom().contains(t)
                    && old(kernel).thread_map.spec_index(t).locked_by_thread(old(lctx).thread_id())
                ==> final(kernel).thread_map.dom().contains(t)
                    && final(kernel).thread_map.spec_index(t) == old(kernel).thread_map.spec_index(t)
                    && final(kernel).thread_map.lock_id_by_key(t)
                        == old(kernel).thread_map.lock_id_by_key(t),
            forall|p: RwLockPageTableRoot|
                #![trigger old(kernel).pagetable_map.spec_index(p)]
                #![trigger final(kernel).pagetable_map.spec_index(p)]
                (old(kernel).pagetable_map.dom().contains(p)
                    && old(kernel).pagetable_map.spec_index(p).locked_by_thread(old(lctx).thread_id()))
                == (final(kernel).pagetable_map.dom().contains(p)
                    && final(kernel).pagetable_map.spec_index(p).locked_by_thread(final(lctx).thread_id())),
            forall|p: RwLockPageTableRoot|
                #![trigger old(kernel).pagetable_map.spec_index(p)]
                #![trigger final(kernel).pagetable_map.spec_index(p)]
                p != pagetable_ptr && old(kernel).pagetable_map.dom().contains(p)
                    && old(kernel).pagetable_map.spec_index(p).locked_by_thread(old(lctx).thread_id())
                ==> final(kernel).pagetable_map.dom().contains(p)
                    && final(kernel).pagetable_map.spec_index(p) == old(kernel).pagetable_map.spec_index(p)
                    && final(kernel).pagetable_map.lock_id_by_key(p)
                        == old(kernel).pagetable_map.lock_id_by_key(p),
            held_containers_unchanged(
                old(kernel).container_map, final(kernel).container_map, old(lctx),
            ),
            held_processes_unchanged(
                old(kernel).process_map, final(kernel).process_map, old(lctx),
            ),
            held_endpoints_unchanged(
                old(kernel).endpoint_map, final(kernel).endpoint_map, old(lctx),
            ),
            held_schedulers_unchanged(
                old(kernel).scheduler_map, final(kernel).scheduler_map, old(lctx),
            ),
            held_pcid_allocators_unchanged(
                old(kernel).pcid_allocator_map, final(kernel).pcid_allocator_map,
                old(lctx),
            ),
            held_iommu_tables_unchanged(
                old(kernel).iommu_table_map, final(kernel).iommu_table_map,
                old(lctx),
            ),
            held_cpus_unchanged(
                old(kernel).cpu_array, final(kernel).cpu_array, old(lctx),
            ),
            allocator_objects_unlocked(
                old(kernel).allocator_2m_map, old(lctx).thread_id(),
            ) ==> allocator_objects_unlocked(
                final(kernel).allocator_2m_map, final(lctx).thread_id(),
            ),
            allocator_objects_unlocked(
                old(kernel).allocator_1g_map, old(lctx).thread_id(),
            ) ==> allocator_objects_unlocked(
                final(kernel).allocator_1g_map, final(lctx).thread_id(),
            ),
            final(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            final(kernel).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            final(kernel).thread_map.spec_index(thread_ptr).view().quota_4k
                >= quota_reserve,
            final(kernel).thread_map.spec_index(thread_ptr).view().quota_4k
                <= old(kernel).thread_map.spec_index(thread_ptr).view().quota_4k,
            final(kernel).thread_map.spec_index(thread_ptr).view().quota_4k
                >= old(kernel).thread_map.spec_index(thread_ptr).view().quota_4k - 3,
            final(kernel).thread_map.spec_index(thread_ptr).view().state
                == old(kernel).thread_map.spec_index(thread_ptr).view().state,
            final(kernel).thread_map.spec_index(thread_ptr).view()
                .blocking_endpoint_ptr
                == old(kernel).thread_map.spec_index(thread_ptr).view()
                    .blocking_endpoint_ptr,
            final(kernel).thread_map.spec_index(thread_ptr).view()
                .upper_container_seq
                == old(kernel).thread_map.spec_index(thread_ptr).view()
                    .upper_container_seq,
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view().wf(),
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                == old(kernel).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end,
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view().user_view()
                == old(kernel).pagetable_map.spec_index(pagetable_ptr).view().user_view(),
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k()
                =~= old(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k(),
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
                =~= old(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
                =~= old(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                .spec_resolve_mapping_l2(
                    spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va),
                ) is Some,
    {
        let indices = va2index(va);
        assert({
            &&& pei_valid(spec_v2l4index(va))
            &&& pei_valid(spec_v2l3index(va))
            &&& pei_valid(spec_v2l2index(va))
            &&& pei_valid(spec_v2l1index(va))
        }) by {
            spec_va_4k_valid_imply_indices_valid();
        };
        proof {
            assert(
                kernel.pagetable_map.perms_wf()
                    && kernel.pagetable_map.spec_index(pagetable_ptr).inv()
            ) by {
                reveal(pagetable_perms_wf);
            };
        }
        let l4_slot;
        {
            let pagetable = kernel.pagetable_map.borrow(
                pagetable_ptr, Tracked(pagetable_lock_perm),
            );
            l4_slot = mmap_4k_l4_directory_slot(pagetable, indices.0);
        }
        match l4_slot {
            Mmap4kDirectorySlot::Present => {},
            Mmap4kDirectorySlot::InUse => {},
            Mmap4kDirectorySlot::Missing => {
                assert(thread_effective_quota_4k(
                    kernel.thread_map.spec_index(thread_ptr),
                ) >= 1) by {
                    reveal(thread_perms_wf);
                };
                install_one_mmap_4k_directory_page(kernel,
                    MissingPageTableLevel::L4,
                    alloc_ptr_4k,
                    thread_ptr,
                    process_ptr,
                    container_ptr,
                    cpu_id,
                    pagetable_ptr,
                    (indices.0, indices.1, indices.2),
                    Tracked(&mut *lctx),
                    Tracked(&mut *steps),
                    Tracked(thread_lock_perm),
                    Tracked(pagetable_lock_perm),
                );
            },
        }
        proof {
            assert(
                kernel.pagetable_map.perms_wf()
                    && kernel.pagetable_map.spec_index(pagetable_ptr).inv()
            ) by {
                reveal(pagetable_perms_wf);
            };
        }
        let l3_slot;
        {
            let pagetable = kernel.pagetable_map.borrow(
                pagetable_ptr, Tracked(pagetable_lock_perm),
            );
            l3_slot = mmap_4k_l3_directory_slot(
                pagetable, indices.0, indices.1,
            );
        }
        match l3_slot {
            Mmap4kDirectorySlot::Present => {},
            Mmap4kDirectorySlot::InUse => {},
            Mmap4kDirectorySlot::Missing => {
                assert(thread_effective_quota_4k(
                    kernel.thread_map.spec_index(thread_ptr),
                ) >= 1) by {
                    reveal(thread_perms_wf);
                };
                install_one_mmap_4k_directory_page(kernel,
                    MissingPageTableLevel::L3,
                    alloc_ptr_4k,
                    thread_ptr,
                    process_ptr,
                    container_ptr,
                    cpu_id,
                    pagetable_ptr,
                    (indices.0, indices.1, indices.2),
                    Tracked(&mut *lctx),
                    Tracked(&mut *steps),
                    Tracked(thread_lock_perm),
                    Tracked(pagetable_lock_perm),
                );
            },
        }
        proof {
            assert(
                kernel.pagetable_map.perms_wf()
                    && kernel.pagetable_map.spec_index(pagetable_ptr).inv()
            ) by {
                reveal(pagetable_perms_wf);
            };
        }
        let l2_slot;
        {
            let pagetable = kernel.pagetable_map.borrow(
                pagetable_ptr, Tracked(pagetable_lock_perm),
            );
            l2_slot = mmap_4k_l2_directory_slot(
                pagetable, indices.0, indices.1, indices.2,
            );
        }
        match l2_slot {
            Mmap4kDirectorySlot::Present => {},
            Mmap4kDirectorySlot::InUse => {},
            Mmap4kDirectorySlot::Missing => {
                assert(thread_effective_quota_4k(
                    kernel.thread_map.spec_index(thread_ptr),
                ) >= 1) by {
                    reveal(thread_perms_wf);
                };
                install_one_mmap_4k_directory_page(kernel,
                    MissingPageTableLevel::L2,
                    alloc_ptr_4k,
                    thread_ptr,
                    process_ptr,
                    container_ptr,
                    cpu_id,
                    pagetable_ptr,
                    (indices.0, indices.1, indices.2),
                    Tracked(&mut *lctx),
                    Tracked(&mut *steps),
                    Tracked(thread_lock_perm),
                    Tracked(pagetable_lock_perm),
                );
            },
        }
    }



} // verus!
