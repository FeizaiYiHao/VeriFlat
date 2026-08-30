use vstd::prelude::*;

use crate::*;
use super::mmap_4k_context::{
    mmap_4k_allocation_ready,
    mmap_4k_held_context,
};
use super::mmap_4k_create_entry_install::MissingPageTableLevel;
use super::mmap_4k_install_one::install_one_mmap_4k_directory_page;

verus! {
    fn mmap_4k_l4_directory_present<const TABLE_TYPE: PTType>(
        pagetable: &PageTable<TABLE_TYPE>,
        l4i: L4Index,
    ) -> (ret: bool)
        requires
            pagetable.wf(),
            pagetable.kernel_l4_end <= l4i && pei_valid(l4i),
        ensures
            ret == (pagetable.spec_resolve_mapping_l4(l4i) is Some),
    {
        pagetable.get_entry_l4(l4i).is_some()
    }

    fn mmap_4k_l3_directory_present<const TABLE_TYPE: PTType>(
        pagetable: &PageTable<TABLE_TYPE>,
        l4i: L4Index,
        l3i: L3Index,
    ) -> (ret: bool)
        requires
            pagetable.wf(),
            pagetable.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pagetable.spec_resolve_mapping_l4(l4i) is Some,
            pagetable.spec_resolve_mapping_1g_l3(l4i, l3i) is None,
        ensures
            ret == (pagetable.spec_resolve_mapping_l3(l4i, l3i) is Some),
    {
        let l4_entry = pagetable.get_entry_l4(l4i).unwrap();
        pagetable.get_entry_l3(l4i, l3i, &l4_entry).is_some()
    }

    fn mmap_4k_l2_directory_present<const TABLE_TYPE: PTType>(
        pagetable: &PageTable<TABLE_TYPE>,
        l4i: L4Index,
        l3i: L3Index,
        l2i: L2Index,
    ) -> (ret: bool)
        requires
            pagetable.wf(),
            pagetable.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
            pagetable.spec_resolve_mapping_l4(l4i) is Some,
            pagetable.spec_resolve_mapping_l3(l4i, l3i) is Some,
            pagetable.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is None,
        ensures
            ret == (pagetable.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some),
    {
        let l4_entry = pagetable.get_entry_l4(l4i).unwrap();
        let l3_entry = pagetable.get_entry_l3(l4i, l3i, &l4_entry).unwrap();
        pagetable.get_entry_l2(l4i, l3i, l2i, &l3_entry).is_some()
    }

    pub fn mmap_4k_build_one_structure(
        krnl: &mut KernelK,
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
            mmap_4k_held_context(old(krnl), old(lctx), alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, thread_lock_perm, pagetable_lock_perm),
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
            mmap_4k_allocation_ready(old(krnl), old(lctx)),
            va_4k_valid(va),
            quota_reserve <= usize::MAX - 3,
            old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k >= 3 + quota_reserve,
            old(krnl).pt_mp.spec_index(pagetable_ptr).view().wf(),
            old(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(va),
            old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_4k_entry_useable(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va)),
        ensures
            mmap_4k_held_context(final(krnl), final(lctx), alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, thread_lock_perm, pagetable_lock_perm),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
            mmap_4k_allocation_ready(final(krnl), final(lctx)),
            final(lctx).lock_id_set() == old(lctx).lock_id_set(),
            final(krnl).thr_mp.lock_id_by_key(thread_ptr) == old(krnl).thr_mp.lock_id_by_key(thread_ptr),
            forall|t: RwLockThreadPtr|
                #![trigger old(krnl).thr_mp.spec_index(t)]
                #![trigger final(krnl).thr_mp.spec_index(t)]
                (old(krnl).thr_mp.dom().contains(t)
                    && old(krnl).thr_mp.spec_index(t).locked_by_thread(old(lctx).thread_id()))
                == (final(krnl).thr_mp.dom().contains(t)
                    && final(krnl).thr_mp.spec_index(t).locked_by_thread(final(lctx).thread_id())),
            forall|t: RwLockThreadPtr|
                #![trigger old(krnl).thr_mp.spec_index(t)]
                #![trigger final(krnl).thr_mp.spec_index(t)]
                t != thread_ptr && old(krnl).thr_mp.dom().contains(t)
                    && old(krnl).thr_mp.spec_index(t).locked_by_thread(old(lctx).thread_id())
                ==> final(krnl).thr_mp.dom().contains(t)
                    && final(krnl).thr_mp.spec_index(t) == old(krnl).thr_mp.spec_index(t)
                    && final(krnl).thr_mp.lock_id_by_key(t)
                        == old(krnl).thr_mp.lock_id_by_key(t),
            forall|p: RwLockPageTableRoot|
                #![trigger old(krnl).pt_mp.spec_index(p)]
                #![trigger final(krnl).pt_mp.spec_index(p)]
                (old(krnl).pt_mp.dom().contains(p)
                    && old(krnl).pt_mp.spec_index(p).locked_by_thread(old(lctx).thread_id()))
                == (final(krnl).pt_mp.dom().contains(p)
                    && final(krnl).pt_mp.spec_index(p).locked_by_thread(final(lctx).thread_id())),
            forall|p: RwLockPageTableRoot|
                #![trigger old(krnl).pt_mp.spec_index(p)]
                #![trigger final(krnl).pt_mp.spec_index(p)]
                p != pagetable_ptr && old(krnl).pt_mp.dom().contains(p)
                    && old(krnl).pt_mp.spec_index(p).locked_by_thread(old(lctx).thread_id())
                ==> final(krnl).pt_mp.dom().contains(p)
                    && final(krnl).pt_mp.spec_index(p) == old(krnl).pt_mp.spec_index(p)
                    && final(krnl).pt_mp.lock_id_by_key(p)
                        == old(krnl).pt_mp.lock_id_by_key(p),
            held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
            held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
            held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
            held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
            held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
            allocator_objects_unlocked(old(krnl).allc_2m_mp, old(lctx).thread_id()) ==> allocator_objects_unlocked(final(krnl).allc_2m_mp, final(lctx).thread_id()),
            allocator_objects_unlocked(old(krnl).allc_1g_mp, old(lctx).thread_id()) ==> allocator_objects_unlocked(final(krnl).allc_1g_mp, final(lctx).thread_id()),
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k >= quota_reserve,
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k <= old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k,
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k >= old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k - 3,
            final(krnl).thr_mp.spec_index(thread_ptr).view().state == old(krnl).thr_mp.spec_index(thread_ptr).view().state,
            final(krnl).thr_mp.spec_index(thread_ptr).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(thread_ptr).view().blocking_endpoint_ptr,
            final(krnl).thr_mp.spec_index(thread_ptr).view().upper_container_seq == old(krnl).thr_mp.spec_index(thread_ptr).view().upper_container_seq,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().wf(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().user_view() == old(krnl).pt_mp.spec_index(pagetable_ptr).view().user_view(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k() =~= old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_2m() =~= old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_2m(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_1g() =~= old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_1g(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some,
    {
        let indices = va2index(va);
        assert({
            &&& pei_valid(spec_v2l4index(va))
            &&& pei_valid(spec_v2l3index(va))
            &&& pei_valid(spec_v2l2index(va))
            &&& pei_valid(spec_v2l1index(va))
        }) by { spec_va_4k_valid_imply_indices_valid(); };
        proof {
            assert(
                krnl.pt_mp.perms_wf()
                    && krnl.pt_mp.spec_index(pagetable_ptr).inv()
            ) by { reveal(pagetable_perms_wf); };
        }
        let l4_present;
        {
            let pagetable = krnl.pt_mp.borrow(pagetable_ptr, Tracked(pagetable_lock_perm));
            l4_present = mmap_4k_l4_directory_present(pagetable, indices.0);
        }
        if !l4_present {
            assert(thread_effective_quota_4k(krnl.thr_mp.spec_index(thread_ptr)) >= 1) by { reveal(thread_perms_wf); };
            install_one_mmap_4k_directory_page(krnl, MissingPageTableLevel::L4, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, (indices.0, indices.1, indices.2), Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm));
        }
        proof {
            assert(krnl.pt_mp.perms_wf()) by { reveal(pagetable_perms_wf); };
        }
        let l3_present;
        {
            let pagetable = krnl.pt_mp.borrow(pagetable_ptr, Tracked(pagetable_lock_perm));
            l3_present = mmap_4k_l3_directory_present(pagetable, indices.0, indices.1);
        }
        if !l3_present {
            assert(thread_effective_quota_4k(krnl.thr_mp.spec_index(thread_ptr)) >= 1) by { reveal(thread_perms_wf); };
            install_one_mmap_4k_directory_page(krnl, MissingPageTableLevel::L3, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, (indices.0, indices.1, indices.2), Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm));
        }
        proof {
            assert(krnl.pt_mp.perms_wf()) by { reveal(pagetable_perms_wf); };
        }
        let l2_present;
        {
            let pagetable = krnl.pt_mp.borrow(pagetable_ptr, Tracked(pagetable_lock_perm));
            l2_present = mmap_4k_l2_directory_present(pagetable, indices.0, indices.1, indices.2);
        }
        if !l2_present {
            assert(thread_effective_quota_4k(krnl.thr_mp.spec_index(thread_ptr)) >= 1) by { reveal(thread_perms_wf); };
            install_one_mmap_4k_directory_page(krnl, MissingPageTableLevel::L2, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, (indices.0, indices.1, indices.2), Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm));
        }
    }

} // verus!
