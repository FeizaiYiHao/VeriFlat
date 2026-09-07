use vstd::prelude::*;

use crate::*;
use super::mmap_4k_context::{mmap_4k_allocation_ready, mmap_4k_held_context};
use super::mmap_4k_create_entry_install::MissingPageTableLevel;
use super::mmap_4k_install_one::install_one_mmap_4k_directory_page;

verus! {
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
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            old(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR) ==> final(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
            held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
            held_threads_unchanged_except(
                old(krnl).thr_mp, final(krnl).thr_mp, old(lctx), set![thread_ptr],
            ),
            held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
            held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
            held_pagetables_unchanged_except(
                old(krnl).pt_mp, final(krnl).pt_mp, old(lctx), set![pagetable_ptr],
            ),
            held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
            held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k >= quota_reserve,
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k <= old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k,
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k >= old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k - 3,
            final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc,
            final(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr,
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
            broadcast use group_held_objects_unchanged_transitive;
        }
        let l4_present = {
            let pagetable = krnl.pt_mp.borrow(pagetable_ptr, Tracked(pagetable_lock_perm));
            pagetable.get_entry_l4(indices.0).is_some()
        };
        if !l4_present {
            assert(thread_effective_quota_4k(krnl.thr_mp.spec_index(thread_ptr)) >= 1) by { reveal(thread_perms_wf); };
            install_one_mmap_4k_directory_page(krnl, MissingPageTableLevel::L4, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, (indices.0, indices.1, indices.2), Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm));
        }
        assert(krnl.pt_mp.perms_wf()) by { reveal(pagetable_perms_wf); };
        let l3_present = {
            let pagetable = krnl.pt_mp.borrow(pagetable_ptr, Tracked(pagetable_lock_perm));
            let l4_entry = pagetable.get_entry_l4(indices.0).unwrap();
            pagetable.get_entry_l3(indices.0, indices.1, &l4_entry).is_some()
        };
        if !l3_present {
            assert(thread_effective_quota_4k(krnl.thr_mp.spec_index(thread_ptr)) >= 1) by { reveal(thread_perms_wf); };
            install_one_mmap_4k_directory_page(krnl, MissingPageTableLevel::L3, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, (indices.0, indices.1, indices.2), Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm));
        }
        assert(krnl.pt_mp.perms_wf()) by { reveal(pagetable_perms_wf); };
        let l2_present = {
            let pagetable = krnl.pt_mp.borrow(pagetable_ptr, Tracked(pagetable_lock_perm));
            let l4_entry = pagetable.get_entry_l4(indices.0).unwrap();
            let l3_entry = pagetable.get_entry_l3(indices.0, indices.1, &l4_entry).unwrap();
            pagetable.get_entry_l2(indices.0, indices.1, indices.2, &l3_entry).is_some()
        };
        if !l2_present {
            assert(thread_effective_quota_4k(krnl.thr_mp.spec_index(thread_ptr)) >= 1) by { reveal(thread_perms_wf); };
            install_one_mmap_4k_directory_page(krnl, MissingPageTableLevel::L2, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, (indices.0, indices.1, indices.2), Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm));
        }
    }

} // verus!
