use vstd::prelude::*;
use vstd::assert_sets_equal;
use crate::*;
#[cfg(feature = "split-crates")]
use veriflat_kernel_core::{attach_endpoint_reference_and_unlock, create_thread_from_staged_page_merged, kernel_u_new_thread_changed};
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::create_thread_from_staged_page::{create_thread_from_staged_page_merged, kernel_u_new_thread_changed};
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::attach_endpoint_reference_and_unlock::attach_endpoint_reference_and_unlock;
use super::syscall_new_process_helpers::share_pages_and_lock_scheduler;
use super::syscall_new_process_spec::kernel_u_new_process_shared;
use super::syscall_new_process_with_iommu_publish::publish_staged_process_with_iommu;

verus! {

#[verifier::spinoff_prover]
pub(super) fn allocate_new_process_with_iommu_pages(
    krnl: &mut KernelK,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>,
    current_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr,
    cpu_id: CpuId,
    Tracked(current_thread_lock_perm): Tracked<&LockPerm>,
) -> (ret: (PagePtr, PagePtr, PagePtr, PagePtr, PagePtr, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>))
    requires
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 5,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).wlocked_by(old(lctx)),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        page_objects_unlocked(old(krnl).pg_arr, old(lctx).thread_id()),
        allocator_objects_unlocked(old(krnl).allc_4k_mp, old(lctx).thread_id()),
        thread_objects_unlocked_except(old(krnl).thr_mp, old(lctx).thread_id(), set![current_thread_ptr]),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
    ensures
        final(krnl).inv(),
        final(steps).steps == old(steps).steps,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        final(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        final(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        ret.0 != ret.1 && ret.0 != ret.2 && ret.0 != ret.3 && ret.0 != ret.4
            && ret.1 != ret.2 && ret.1 != ret.3 && ret.1 != ret.4
            && ret.2 != ret.3 && ret.2 != ret.4 && ret.3 != ret.4,
        page_ptr_valid(ret.0) && page_ptr_valid(ret.1) && page_ptr_valid(ret.2) && page_ptr_valid(ret.3) && page_ptr_valid(ret.4),
        final(lctx).page_lock_map().dom() == set![page_ptr2page_index(ret.0), page_ptr2page_index(ret.1), page_ptr2page_index(ret.2), page_ptr2page_index(ret.3), page_ptr2page_index(ret.4)],
        page_objects_unlocked_except(final(krnl).pg_arr, final(lctx).thread_id(), set![page_ptr2page_index(ret.0), page_ptr2page_index(ret.1), page_ptr2page_index(ret.2), page_ptr2page_index(ret.3), page_ptr2page_index(ret.4)]),
        thread_objects_unlocked_except(final(krnl).thr_mp, final(lctx).thread_id(), set![current_thread_ptr]),
        forall|exceptions: Set<RwLockPageTableRoot>|
            #![trigger pagetable_objects_unlocked_except(old(krnl).pt_mp, old(lctx).thread_id(), exceptions)]
            #![trigger pagetable_objects_unlocked_except(final(krnl).pt_mp, final(lctx).thread_id(), exceptions)]
            pagetable_objects_unlocked_except(old(krnl).pt_mp, old(lctx).thread_id(), exceptions)
            ==> pagetable_objects_unlocked_except(final(krnl).pt_mp, final(lctx).thread_id(), exceptions),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view() == set![ret.0, ret.1, ret.2, ret.3, ret.4],
        final(krnl).thr_mp.dom().contains(current_thread_ptr),
        !final(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().state == old(krnl).thr_mp.spec_index(current_thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m == old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_1g == old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_1g,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).wlocked_by(final(lctx)),
        current_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.1)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.2)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.3)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.4)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().owning_container == container_ptr,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.1)).view().view().owning_container == container_ptr,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.2)).view().view().owning_container == container_ptr,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.3)).view().view().owning_container == container_ptr,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.4)).view().view().owning_container == container_ptr,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().wlocked_by(final(lctx)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.1)).view().wlocked_by(final(lctx)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.2)).view().wlocked_by(final(lctx)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.3)).view().wlocked_by(final(lctx)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.4)).view().wlocked_by(final(lctx)),
        ret.5.view().state() is WriteLock && ret.5.view().thread_id() == final(lctx).thread_id() && ret.5.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().locking_thread()->Write_lock_id,
        ret.6.view().state() is WriteLock && ret.6.view().thread_id() == final(lctx).thread_id() && ret.6.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.1)).view().locking_thread()->Write_lock_id,
        ret.7.view().state() is WriteLock && ret.7.view().thread_id() == final(lctx).thread_id() && ret.7.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.2)).view().locking_thread()->Write_lock_id,
        ret.8.view().state() is WriteLock && ret.8.view().thread_id() == final(lctx).thread_id() && ret.8.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.3)).view().locking_thread()->Write_lock_id,
        ret.9.view().state() is WriteLock && ret.9.view().thread_id() == final(lctx).thread_id() && ret.9.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.4)).view().locking_thread()->Write_lock_id,
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
        held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
        held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        allocator_objects_unlocked(final(krnl).allc_4k_mp, final(lctx).thread_id()),
        allocator_objects_unlocked(old(krnl).allc_2m_mp, old(lctx).thread_id()) ==> allocator_objects_unlocked(final(krnl).allc_2m_mp, final(lctx).thread_id()),
        allocator_objects_unlocked(old(krnl).allc_1g_mp, old(lctx).thread_id()) ==> allocator_objects_unlocked(final(krnl).allc_1g_mp, final(lctx).thread_id()),
{
    let (pages, Tracked(mut page_lock_perms)) = allocate_free_4k_pages::<5>(krnl, current_thread_ptr, container_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(current_thread_lock_perm));
    let process_page_ptr = *pages.get(0);
    let pagetable_page_ptr = *pages.get(1);
    let l4_page_ptr = *pages.get(2);
    let iommu_table_page_ptr = *pages.get(3);
    let iommu_l4_page_ptr = *pages.get(4);
    proof {
        assert(pages.view().to_set().contains(process_page_ptr) && pages.view().to_set().contains(pagetable_page_ptr) && pages.view().to_set().contains(l4_page_ptr) && pages.view().to_set().contains(iommu_table_page_ptr) && pages.view().to_set().contains(iommu_l4_page_ptr)) by { pages.view().to_set_ensures(); };
        assert(process_page_ptr != pagetable_page_ptr && process_page_ptr != l4_page_ptr && process_page_ptr != iommu_table_page_ptr && process_page_ptr != iommu_l4_page_ptr && pagetable_page_ptr != l4_page_ptr && pagetable_page_ptr != iommu_table_page_ptr && pagetable_page_ptr != iommu_l4_page_ptr && l4_page_ptr != iommu_table_page_ptr && l4_page_ptr != iommu_l4_page_ptr && iommu_table_page_ptr != iommu_l4_page_ptr) by { seq_index_lemma::<PagePtr>(); };
        assert(page_ptrs_to_indices(pages.view()) =~= set![page_ptr2page_index(process_page_ptr), page_ptr2page_index(pagetable_page_ptr), page_ptr2page_index(l4_page_ptr), page_ptr2page_index(iommu_table_page_ptr), page_ptr2page_index(iommu_l4_page_ptr)]) by {
            reveal(page_ptrs_to_indices);
            broadcast use Seq::lemma_push_map_commute;
            pages.view().map_values(|page_ptr: PagePtr| page_ptr2page_index(page_ptr)).to_set_ensures();
            assert_sets_equal!(page_ptrs_to_indices(pages.view()) == set![page_ptr2page_index(process_page_ptr), page_ptr2page_index(pagetable_page_ptr), page_ptr2page_index(l4_page_ptr), page_ptr2page_index(iommu_table_page_ptr), page_ptr2page_index(iommu_l4_page_ptr)]);
        };
        assert(krnl.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view() =~= set![process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr]) by { pages.view().to_set_ensures(); assert_sets_equal!(krnl.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view() == set![process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr]); };
        assert(page_ptr_valid(process_page_ptr) && page_ptr_valid(pagetable_page_ptr) && page_ptr_valid(l4_page_ptr) && page_ptr_valid(iommu_table_page_ptr) && page_ptr_valid(iommu_l4_page_ptr)) by { reveal(allocated_4k_page_lock_perms_wf); pages.view().to_set_ensures(); };
        assert(krnl.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }) && krnl.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }) && krnl.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }) && krnl.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }) && krnl.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })) by { reveal(allocated_4k_page_lock_perms_wf); pages.view().to_set_ensures(); };
        assert(krnl.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().owning_container == container_ptr && krnl.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().wlocked_by(lctx) && page_lock_perms.spec_index(process_page_ptr).state() is WriteLock && page_lock_perms.spec_index(process_page_ptr).thread_id() == lctx.thread_id() && page_lock_perms.spec_index(process_page_ptr).lock_id() == krnl.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().locking_thread()->Write_lock_id) by { reveal(allocated_4k_page_lock_perms_wf); };
        assert(krnl.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().owning_container == container_ptr && krnl.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().wlocked_by(lctx) && page_lock_perms.spec_index(pagetable_page_ptr).state() is WriteLock && page_lock_perms.spec_index(pagetable_page_ptr).thread_id() == lctx.thread_id() && page_lock_perms.spec_index(pagetable_page_ptr).lock_id() == krnl.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().locking_thread()->Write_lock_id) by { reveal(allocated_4k_page_lock_perms_wf); };
        assert(krnl.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().owning_container == container_ptr && krnl.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().wlocked_by(lctx) && page_lock_perms.spec_index(l4_page_ptr).state() is WriteLock && page_lock_perms.spec_index(l4_page_ptr).thread_id() == lctx.thread_id() && page_lock_perms.spec_index(l4_page_ptr).lock_id() == krnl.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().locking_thread()->Write_lock_id) by { reveal(allocated_4k_page_lock_perms_wf); };
        assert(krnl.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().owning_container == container_ptr && krnl.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().wlocked_by(lctx) && page_lock_perms.spec_index(iommu_table_page_ptr).state() is WriteLock && page_lock_perms.spec_index(iommu_table_page_ptr).thread_id() == lctx.thread_id() && page_lock_perms.spec_index(iommu_table_page_ptr).lock_id() == krnl.pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().locking_thread()->Write_lock_id) by { reveal(allocated_4k_page_lock_perms_wf); };
        assert(krnl.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().owning_container == container_ptr && krnl.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().wlocked_by(lctx) && page_lock_perms.spec_index(iommu_l4_page_ptr).state() is WriteLock && page_lock_perms.spec_index(iommu_l4_page_ptr).thread_id() == lctx.thread_id() && page_lock_perms.spec_index(iommu_l4_page_ptr).lock_id() == krnl.pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().locking_thread()->Write_lock_id) by { reveal(allocated_4k_page_lock_perms_wf); };
    }
    let tracked process_page_lock_perm = page_lock_perms.tracked_remove(process_page_ptr);
    let tracked pagetable_page_lock_perm = page_lock_perms.tracked_remove(pagetable_page_ptr);
    let tracked l4_page_lock_perm = page_lock_perms.tracked_remove(l4_page_ptr);
    let tracked iommu_table_page_lock_perm = page_lock_perms.tracked_remove(iommu_table_page_ptr);
    let tracked iommu_l4_page_lock_perm = page_lock_perms.tracked_remove(iommu_l4_page_ptr);
    proof {
        assert(lctx.holds_no_allocator_locks(PageSize::SZ2m) && lctx.holds_no_allocator_locks(PageSize::SZ1g)) by { reveal(LocalContext::holds_no_allocator_locks); };
        assert(krnl.thr_mp.spec_index(current_thread_ptr).view().state == old(krnl).thr_mp.spec_index(current_thread_ptr).view().state) by { reveal(Thread::stable_allocation_root_equal); };
        assert(thread_objects_unlocked_except(krnl.thr_mp, lctx.thread_id(), set![current_thread_ptr])) by { reveal(thread_objects_unlocked_except); };
    }
    (process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr, Tracked(process_page_lock_perm), Tracked(pagetable_page_lock_perm), Tracked(l4_page_lock_perm), Tracked(iommu_table_page_lock_perm), Tracked(iommu_l4_page_lock_perm))
}


#[verifier::spinoff_prover]
pub(super) fn create_initial_thread_with_iommu_endpoint_and_finish_new_process(
    krnl: &mut KernelK,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>,
    cpu_id: CpuId,
    container_ptr: RwLockContainerPtr,
    child_ptr: RwLockProcessPtr,
    current_thread_ptr: RwLockThreadPtr,
    scheduler_ptr: RwLockSchedulerPtr,
    endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx,
    source_pagetable_ptr: RwLockPageTableRoot,
    target_pagetable_ptr: RwLockPageTableRoot,
    iommu_table_ptr: RwLockPageTableRoot,
    cpu_lock_perm: Tracked<LockPerm>,
    container_lock_perm: Tracked<LockPerm>,
    child_lock_perm: Tracked<LockPerm>,
    current_thread_lock_perm: Tracked<LockPerm>,
    scheduler_lock_perm: Tracked<LockPerm>,
    endpoint_lock_perm: Tracked<LockPerm>,
    source_pagetable_lock_perm: Tracked<LockPerm>,
    target_pagetable_lock_perm: Tracked<LockPerm>,
    iommu_table_lock_perm: Tracked<LockPerm>,
) -> (new_thread_ptr: RwLockThreadPtr)
    requires
        index_valid(NUM_CPUS, cpu_id),
        edp_idx_valid(endpoint_index),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        mmap_4k_allocation_ready(old(krnl), old(lctx)),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).object_lock_scope(Set::empty(), set![cpu_id], set![container_ptr], set![child_ptr], set![current_thread_ptr], set![endpoint_ptr], set![scheduler_ptr], Set::empty(), set![source_pagetable_ptr, target_pagetable_ptr], set![iommu_table_ptr]),
        kernel_objects_unlocked_except(old(krnl), old(lctx).thread_id(), set![cpu_id], set![container_ptr], set![scheduler_ptr], set![child_ptr], set![current_thread_ptr], Set::empty(), set![endpoint_ptr], set![source_pagetable_ptr, target_pagetable_ptr], set![iommu_table_ptr], Set::empty(), Set::empty(), Set::empty(), Set::empty()),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        old(krnl).cpu_arr.spec_index(cpu_id).view().wlocked_by(old(lctx)),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        cpu_lock_perm.view().state() is WriteLock,
        cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).wlocked_by(old(lctx)),
        !old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
        container_lock_perm.view().state() is WriteLock,
        container_lock_perm.view().thread_id() == old(lctx).thread_id(),
        container_lock_perm.view().lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(child_ptr),
        old(krnl).prc_mp.spec_index(child_ptr).wlocked_by(old(lctx)),
        !old(krnl).prc_mp.spec_index(child_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(child_ptr).view_rodata().view().owning_container == container_ptr,
        old(krnl).prc_mp.spec_index(child_ptr).view().iommu_table == Some(iommu_table_ptr),
        child_lock_perm.view().state() is WriteLock,
        child_lock_perm.view().thread_id() == old(lctx).thread_id(),
        child_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(child_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).wlocked_by(old(lctx)),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state is RUNNING,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 1,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.wf(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).sched_mp.dom().contains(scheduler_ptr),
        old(krnl).sched_mp.spec_index(scheduler_ptr).wlocked_by(old(lctx)),
        !old(krnl).sched_mp.spec_index(scheduler_ptr).being_killed(),
        scheduler_lock_perm.view().state() is WriteLock,
        scheduler_lock_perm.view().thread_id() == old(lctx).thread_id(),
        scheduler_lock_perm.view().lock_id() == old(krnl).sched_mp.spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
        old(krnl).ep_mp.dom().contains(endpoint_ptr),
        old(krnl).ep_mp.spec_index(endpoint_ptr).is_init(),
        old(krnl).ep_mp.spec_index(endpoint_ptr).wlocked_by(old(lctx)),
        !old(krnl).ep_mp.spec_index(endpoint_ptr).being_killed(),
        old(krnl).ctn_mp.dom().contains(old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container),
        {
            ||| old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container == container_ptr
            ||| old(krnl).ctn_mp.spec_index(old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container).view().subtree_set.view().contains(container_ptr)
        },
        endpoint_lock_perm.view().state() is WriteLock,
        endpoint_lock_perm.view().thread_id() == old(lctx).thread_id(),
        endpoint_lock_perm.view().lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
        source_pagetable_ptr != target_pagetable_ptr,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).wlocked_by(old(lctx)),
        source_pagetable_lock_perm.view().state() is WriteLock,
        source_pagetable_lock_perm.view().thread_id() == old(lctx).thread_id(),
        source_pagetable_lock_perm.view().lock_id() == old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(target_pagetable_ptr),
        old(krnl).pt_mp.spec_index(target_pagetable_ptr).wlocked_by(old(lctx)),
        target_pagetable_lock_perm.view().state() is WriteLock,
        target_pagetable_lock_perm.view().thread_id() == old(lctx).thread_id(),
        target_pagetable_lock_perm.view().lock_id() == old(krnl).pt_mp.spec_index(target_pagetable_ptr).locking_thread()->Write_lock_id,
        old(krnl).it_mp.dom().contains(iommu_table_ptr),
        old(krnl).it_mp.spec_index(iommu_table_ptr).wlocked_by(old(lctx)),
        old(krnl).it_mp.spec_index(iommu_table_ptr).view().is_empty(),
        iommu_table_lock_perm.view().state() is WriteLock,
        iommu_table_lock_perm.view().thread_id() == old(lctx).thread_id(),
        iommu_table_lock_perm.view().lock_id() == old(krnl).it_mp.spec_index(iommu_table_ptr).locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        final(steps).steps.len() == old(steps).steps.len() + 1,
        final(steps).steps.subrange(0, old(steps).steps.len() as int) == old(steps).steps,
        final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(krnl)),
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        kernel_u_new_thread_changed(final(steps).steps.last().old_u, final(steps).steps.last().new_u, child_ptr),
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(krnl).prc_mp.dom().contains(child_ptr),
        final(krnl).prc_mp.spec_index(child_ptr).view().iommu_table == Some(iommu_table_ptr),
        final(krnl).it_mp.dom().contains(iommu_table_ptr),
        final(krnl).it_mp.spec_index(iommu_table_ptr).view().is_empty(),
        final(krnl).thr_mp.dom().contains(new_thread_ptr),
        final(krnl).thr_mp.spec_index(new_thread_ptr).view().state is SCHEDULED,
        final(krnl).thr_mp.spec_index(new_thread_ptr).view().owning_proc == child_ptr,
        final(krnl).thr_mp.spec_index(new_thread_ptr).view().owning_container == container_ptr,
        final(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.wf(),
        final(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.spec_index(0) == Some(endpoint_ptr),
{
    hide(kernel_u_new_thread_changed);
    hide(kernel_objects_unlocked_except);
    hide(held_containers_unchanged);
    hide(held_processes_unchanged);
    hide(held_endpoints_unchanged);
    hide(held_schedulers_unchanged);
    hide(held_pcid_allocators_unchanged);
    hide(held_pagetables_unchanged);
    hide(held_iommu_tables_unchanged);
    hide(held_cpus_unchanged);
    let tracked cpu_lock_perm = cpu_lock_perm.get();
    let tracked container_lock_perm = container_lock_perm.get();
    let tracked child_lock_perm = child_lock_perm.get();
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked scheduler_lock_perm = scheduler_lock_perm.get();
    let tracked endpoint_lock_perm = endpoint_lock_perm.get();
    let tracked source_pagetable_lock_perm = source_pagetable_lock_perm.get();
    let tracked target_pagetable_lock_perm = target_pagetable_lock_perm.get();
    let tracked iommu_table_lock_perm = iommu_table_lock_perm.get();
    proof {
        assert(thread_effective_quota_4k(krnl.thr_mp.spec_index(current_thread_ptr)) >= 1) by { reveal(thread_effective_quota_4k); reveal(Thread::temp_alloc_clean); };
        assert(endpoint_objects_unlocked_except(krnl.ep_mp, lctx.thread_id(), set![endpoint_ptr])) by { reveal(kernel_objects_unlocked_except); };
        assert(thread_objects_unlocked_except(krnl.thr_mp, lctx.thread_id(), set![current_thread_ptr])) by { reveal(kernel_objects_unlocked_except); };
    }
    let (thread_page_ptr, Tracked(thread_page_lock_perm)) = allocate_free_4k_page(krnl, current_thread_ptr, container_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&current_thread_lock_perm));
    proof {
        assert(held_endpoints_unchanged(old(krnl).ep_mp, krnl.ep_mp, lctx)) by { reveal(held_endpoints_unchanged); };
        assert(endpoint_objects_unlocked_except(krnl.ep_mp, lctx.thread_id(), set![endpoint_ptr])) by { endpoint_objects_unlocked_except_preserved_for_held_unchanged(old(krnl).ep_mp, krnl.ep_mp, &*lctx, set![endpoint_ptr]); };
        assert(krnl.ctn_mp.dom().contains(container_ptr) && krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr) by { reveal(held_containers_unchanged); };
        assert(krnl.prc_mp.dom().contains(child_ptr) && krnl.prc_mp.spec_index(child_ptr).view_rodata().view().owning_container == container_ptr && !krnl.prc_mp.spec_index(child_ptr).being_killed() && krnl.prc_mp.spec_index(child_ptr).wlocked_by(lctx) && child_lock_perm.lock_id() == krnl.prc_mp.spec_index(child_ptr).locking_thread()->Write_lock_id) by { reveal(held_processes_unchanged); };
        assert(krnl.sched_mp.dom().contains(scheduler_ptr) && krnl.sched_mp.spec_index(scheduler_ptr).wlocked_by(lctx) && scheduler_lock_perm.lock_id() == krnl.sched_mp.spec_index(scheduler_ptr).locking_thread()->Write_lock_id) by { reveal(held_schedulers_unchanged); };
        assert(krnl.ep_mp.dom().contains(endpoint_ptr) && krnl.ep_mp.spec_index(endpoint_ptr).wlocked_by(lctx) && endpoint_lock_perm.lock_id() == krnl.ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id) by { reveal(held_endpoints_unchanged); };
        assert(krnl.prc_mp.spec_index(child_ptr).view().iommu_table == Some(iommu_table_ptr)) by { reveal(held_processes_unchanged); };
        assert(krnl.it_mp.dom().contains(iommu_table_ptr) && krnl.it_mp.spec_index(iommu_table_ptr).wlocked_by(lctx) && krnl.it_mp.spec_index(iommu_table_ptr).view().is_empty() && iommu_table_lock_perm.lock_id() == krnl.it_mp.spec_index(iommu_table_ptr).locking_thread()->Write_lock_id) by { reveal(held_iommu_tables_unchanged); reveal(typed_lock_maps_aligned); reveal(LockedMap::typed_lock_map_aligned); };
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
    }
    let (new_thread_ptr, Tracked(new_thread_lock_perm)) = create_thread_from_staged_page_merged(krnl, thread_page_ptr, child_ptr, current_thread_ptr, container_ptr, scheduler_ptr, Tracked(&mut *lctx), Tracked(&thread_page_lock_perm), Tracked(&child_lock_perm), Tracked(&current_thread_lock_perm), Tracked(&scheduler_lock_perm));
    proof {
        assert(kernel_k_to_kernel_u(*krnl) != steps.snap_shot) by { reveal(kernel_u_new_thread_changed); reveal(kernel_k_to_kernel_u); };
        assert(krnl.prc_mp.spec_index(child_ptr).view().iommu_table == Some(iommu_table_ptr)) by { reveal(kernel_u_new_thread_changed); reveal(kernel_k_to_kernel_u); reveal(process_iommu_table_match); };
        assert(krnl.ep_mp.dom().contains(endpoint_ptr) && krnl.ep_mp.spec_index(endpoint_ptr).is_init() && krnl.ep_mp.spec_index(endpoint_ptr).wlocked_by(lctx) && endpoint_lock_perm.lock_id() == krnl.ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id) by { reveal(endpoint_perms_wf); reveal(endpoints_inv); reveal(held_endpoints_unchanged); };
        assert(krnl.ctn_mp.dom().contains(krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container)) by { reveal(container_endpoint_wf); };
        assert({
            ||| krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container == container_ptr
            ||| krnl.ctn_mp.spec_index(krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container).view().subtree_set.view().contains(container_ptr)
        }) by { reveal(container_thread_endpoint_wf); };
        assert(thread_objects_unlocked_except(krnl.thr_mp, lctx.thread_id(), set![current_thread_ptr, new_thread_ptr])) by { reveal(thread_objects_unlocked_except); };
        assert(krnl.pt_mp.dom().contains(target_pagetable_ptr) && krnl.pt_mp.spec_index(target_pagetable_ptr).wlocked_by(lctx) && target_pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(target_pagetable_ptr).locking_thread()->Write_lock_id) by { reveal(held_pagetables_unchanged); };
        assert(krnl.pt_mp.dom().contains(source_pagetable_ptr) && krnl.pt_mp.spec_index(source_pagetable_ptr).wlocked_by(lctx) && source_pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Write_lock_id) by { reveal(held_pagetables_unchanged); };
    }
    attach_endpoint_reference_and_unlock(krnl, new_thread_ptr, endpoint_ptr, cpu_id, scheduler_ptr, child_ptr, current_thread_ptr, page_ptr2page_index(thread_page_ptr), Tracked(&mut *lctx), Tracked(new_thread_lock_perm), Tracked(endpoint_lock_perm));
    krnl.wunlock_process(child_ptr, Tracked(&mut *lctx), Tracked(child_lock_perm));
    krnl.wunlock_pagetable(target_pagetable_ptr, Tracked(&mut *lctx), Tracked(target_pagetable_lock_perm));
    proof { assert(krnl.pt_mp.dom().contains(source_pagetable_ptr) && krnl.pt_mp.spec_index(source_pagetable_ptr).wlocked_by(lctx) && source_pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Write_lock_id) by { reveal(LockedMap::unchanged_except); }; }
    krnl.wunlock_pagetable(source_pagetable_ptr, Tracked(&mut *lctx), Tracked(source_pagetable_lock_perm));
    krnl.wunlock_page(page_ptr2page_index(thread_page_ptr), Tracked(&mut *lctx), Tracked(thread_page_lock_perm));
    krnl.wunlock_scheduler(scheduler_ptr, Tracked(&mut *lctx), Tracked(scheduler_lock_perm));
    proof { assert(krnl.thr_mp.dom().contains(current_thread_ptr) && krnl.thr_mp.spec_index(current_thread_ptr).wlocked_by(lctx) && current_thread_lock_perm.lock_id() == krnl.thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id) by { reveal(LockedMap::unchanged_except); }; }
    krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
    proof { assert(krnl.ctn_mp.dom().contains(container_ptr) && !krnl.ctn_mp.spec_index(container_ptr).being_killed() && !krnl.ctn_mp.spec_index(container_ptr).view().owned_processes.view().is_empty() && krnl.ctn_mp.spec_index(container_ptr).wlocked_by(lctx) && container_lock_perm.lock_id() == krnl.ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id) by { reveal(held_containers_unchanged); reveal(container_process_wf); }; }
    krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
    proof { assert(krnl.cpu_arr.spec_index(cpu_id).view().wlocked_by(lctx) && cpu_lock_perm.lock_id() == krnl.cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id) by { reveal(held_cpus_unchanged); }; }
    krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        assert(krnl.prc_mp.spec_index(child_ptr).view().iommu_table == Some(iommu_table_ptr)) by { reveal(held_processes_unchanged); reveal(LockedMap::unchanged_except); };
        assert(krnl.it_mp.dom().contains(iommu_table_ptr) && krnl.it_mp.spec_index(iommu_table_ptr).wlocked_by(lctx) && krnl.it_mp.spec_index(iommu_table_ptr).view().is_empty() && iommu_table_lock_perm.lock_id() == krnl.it_mp.spec_index(iommu_table_ptr).locking_thread()->Write_lock_id) by { reveal(held_iommu_tables_unchanged); reveal(LockedMap::unchanged_except); };
    }
    krnl.wunlock_iommu_table(iommu_table_ptr, Tracked(&mut *lctx), Tracked(iommu_table_lock_perm));
    proof {
        assert({
            &&& krnl.thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.wf()
            &&& krnl.thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.spec_index(0) == Some(endpoint_ptr)
            &&& krnl.thr_mp.spec_index(new_thread_ptr).view().owning_proc == child_ptr
            &&& krnl.thr_mp.spec_index(new_thread_ptr).view().owning_container == container_ptr
        }) by { reveal(thread_perms_wf); reveal(process_thread_wf); reveal(LockedMap::unchanged_except); };
        assert(krnl.it_mp.dom().contains(iommu_table_ptr) && krnl.it_mp.spec_index(iommu_table_ptr).view().is_empty()) by { reveal(LockedMap::unchanged_except); };
        assert(krnl.all_objects_unlocked(lctx)) by { reveal(KernelK::all_objects_unlocked); reveal(kernel_objects_unlocked_except); reveal(cpu_objects_unlocked_except); reveal(container_objects_unlocked_except); reveal(scheduler_objects_unlocked_except); reveal(process_objects_unlocked_except); reveal(thread_objects_unlocked_except); reveal(endpoint_objects_unlocked_except); reveal(page_objects_unlocked_except); reveal(pagetable_objects_unlocked_except); reveal(iommu_table_objects_unlocked_except); reveal(pcid_allocator_objects_unlocked_except); reveal(allocator_objects_unlocked_except); reveal(held_cpus_unchanged); reveal(held_containers_unchanged); reveal(held_schedulers_unchanged); reveal(held_processes_unchanged); reveal(held_endpoints_unchanged); reveal(held_pcid_allocators_unchanged); reveal(held_pagetables_unchanged); reveal(held_iommu_tables_unchanged); };
        steps.end_kernel_step(&*krnl, &*lctx);
        assert(steps.steps.subrange(0, old(steps).steps.len() as int) == old(steps).steps) by { reveal(record_user_view_change); };
        assert(kernel_u_new_thread_changed(steps.steps.last().old_u, steps.steps.last().new_u, child_ptr)) by { reveal(record_user_view_change); };
    }
    new_thread_ptr
}

#[verifier::spinoff_prover]
pub(super) fn commit_new_process_with_iommu_and_endpoint(
    krnl: &mut KernelK,
    source_range: &VaRange4K,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>,
    cpu_id: CpuId,
    container_ptr: RwLockContainerPtr,
    parent_ptr: RwLockProcessPtr,
    current_thread_ptr: RwLockThreadPtr,
    scheduler_ptr: RwLockSchedulerPtr,
    allocator_ptr: RwLockPageAllocatorPtr,
    pcid_allocator_ptr: RwLockPcidAllocatorPtr,
    source_pagetable_ptr: RwLockPageTableRoot,
    endpoint_ptr: RwLockEndpointPtr,
    endpoint_index: EndpointIdx,
    pcid: Pcid,
    cpu_lock_perm: Tracked<LockPerm>,
    container_lock_perm: Tracked<LockPerm>,
    pcid_allocator_lock_perm: Tracked<LockPerm>,
    parent_lock_perm: Tracked<LockPerm>,
    current_thread_lock_perm: Tracked<LockPerm>,
    source_pagetable_lock_perm: Tracked<LockPerm>,
    endpoint_lock_perm: Tracked<LockPerm>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        edp_idx_valid(endpoint_index),
        source_range.wf(),
        source_range.len > 0,
        source_range.len <= (usize::MAX - 6) / 3,
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        old(krnl).cpu_arr.spec_index(cpu_id).view().wlocked_by(old(lctx)),
        cpu_lock_perm.view().state() is WriteLock,
        cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).wlocked_by(old(lctx)),
        !old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator == pcid_allocator_ptr,
        container_lock_perm.view().state() is WriteLock,
        container_lock_perm.view().thread_id() == old(lctx).thread_id(),
        container_lock_perm.view().lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        old(krnl).pcid_allc_mp.dom().contains(pcid_allocator_ptr),
        old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).wlocked_by(old(lctx)),
        old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).view().pcid_is_free(pcid),
        pcid_allocator_lock_perm.view().state() is WriteLock,
        pcid_allocator_lock_perm.view().thread_id() == old(lctx).thread_id(),
        pcid_allocator_lock_perm.view().lock_id() == old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(parent_ptr),
        old(krnl).prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == container_ptr,
        old(krnl).prc_mp.spec_index(parent_ptr).wlocked_by(old(lctx)),
        !old(krnl).prc_mp.spec_index(parent_ptr).being_killed(),
        parent_lock_perm.view().state() is WriteLock,
        parent_lock_perm.view().thread_id() == old(lctx).thread_id(),
        parent_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(parent_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == source_pagetable_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state is RUNNING,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 6 + 3 * source_range.len,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.wf(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).wlocked_by(old(lctx)),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).ep_mp.dom().contains(endpoint_ptr),
        old(krnl).ep_mp.spec_index(endpoint_ptr).is_init(),
        old(krnl).ep_mp.spec_index(endpoint_ptr).wlocked_by(old(lctx)),
        !old(krnl).ep_mp.spec_index(endpoint_ptr).being_killed(),
        old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((current_thread_ptr, endpoint_index)),
        old(krnl).ctn_mp.dom().contains(old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container),
        {
            ||| old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container == container_ptr
            ||| old(krnl).ctn_mp.spec_index(old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container).view().subtree_set.view().contains(container_ptr)
        },
        endpoint_lock_perm.view().state() is WriteLock,
        endpoint_lock_perm.view().thread_id() == old(lctx).thread_id(),
        endpoint_lock_perm.view().lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().wf(),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).wlocked_by(old(lctx)),
        source_pagetable_lock_perm.view().state() is WriteLock,
        source_pagetable_lock_perm.view().thread_id() == old(lctx).thread_id(),
        source_pagetable_lock_perm.view().lock_id() == old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(source_range.start),
        share_mapping_4k_source_range_present(old(krnl), source_pagetable_ptr, source_range),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        old(lctx).object_lock_scope(Set::empty(), set![cpu_id], set![container_ptr], set![parent_ptr], set![current_thread_ptr], set![endpoint_ptr], Set::empty(), set![pcid_allocator_ptr], set![source_pagetable_ptr], Set::empty()),
        kernel_objects_unlocked_except(old(krnl), old(lctx).thread_id(), set![cpu_id], set![container_ptr], Set::empty(), set![parent_ptr], set![current_thread_ptr], Set::empty(), set![endpoint_ptr], set![source_pagetable_ptr], Set::empty(), set![pcid_allocator_ptr], Set::empty(), Set::empty(), Set::empty()),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
    ensures
        final(krnl).inv(),
        final(steps).steps.len() == old(steps).steps.len() + source_range.len + 2,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(krnl)),
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        exists|child_ptr: RwLockProcessPtr, iommu_table_ptr: RwLockPageTableRoot, thread_ptr: RwLockThreadPtr|
            #![trigger kernel_u_new_process_shared(final(steps).steps.spec_index(old(steps).steps.len() as int).new_u, final(steps).steps.spec_index((old(steps).steps.len() + source_range.len) as int).new_u, parent_ptr, child_ptr, source_range), final(krnl).it_mp.spec_index(iommu_table_ptr), final(krnl).thr_mp.spec_index(thread_ptr)]
        {
            let first_step = final(steps).steps.spec_index(old(steps).steps.len() as int);
            &&& kernel_u_create_process_with_iommu_changed(first_step.old_u, first_step.new_u, parent_ptr, child_ptr)
            &&& kernel_u_new_process_shared(first_step.new_u, final(steps).steps.spec_index((old(steps).steps.len() + source_range.len) as int).new_u, parent_ptr, child_ptr, source_range)
            &&& kernel_u_new_thread_changed(final(steps).steps.last().old_u, final(steps).steps.last().new_u, child_ptr)
            &&& final(krnl).prc_mp.dom().contains(child_ptr)
            &&& final(krnl).prc_mp.spec_index(child_ptr).view().iommu_table == Some(iommu_table_ptr)
            &&& final(krnl).it_mp.dom().contains(iommu_table_ptr)
            &&& final(krnl).it_mp.spec_index(iommu_table_ptr).view().is_empty()
            &&& final(krnl).thr_mp.dom().contains(thread_ptr)
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().state is SCHEDULED
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == child_ptr
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.wf()
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.spec_index(0) == Some(endpoint_ptr)
        },
{
    hide(kernel_objects_unlocked_except);
    hide(held_containers_unchanged);
    hide(held_processes_unchanged);
    hide(held_endpoints_unchanged);
    hide(held_schedulers_unchanged);
    hide(held_pcid_allocators_unchanged);
    hide(held_pagetables_unchanged);
    hide(held_iommu_tables_unchanged);
    hide(held_cpus_unchanged);
    let tracked cpu_lock_perm = cpu_lock_perm.get();
    let tracked container_lock_perm = container_lock_perm.get();
    let tracked pcid_allocator_lock_perm = pcid_allocator_lock_perm.get();
    let tracked parent_lock_perm = parent_lock_perm.get();
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked source_pagetable_lock_perm = source_pagetable_lock_perm.get();
    let tracked endpoint_lock_perm = endpoint_lock_perm.get();
    proof {
        assert(page_objects_unlocked(krnl.pg_arr, lctx.thread_id())) by { reveal(kernel_objects_unlocked_except); reveal(page_objects_unlocked_except); reveal(page_objects_unlocked); };
        assert(allocator_objects_unlocked(krnl.allc_4k_mp, lctx.thread_id())) by { reveal(kernel_objects_unlocked_except); reveal(allocator_objects_unlocked_except); };
        assert(thread_objects_unlocked_except(krnl.thr_mp, lctx.thread_id(), set![current_thread_ptr])) by { reveal(kernel_objects_unlocked_except); };
        assert(endpoint_objects_unlocked_except(krnl.ep_mp, lctx.thread_id(), set![endpoint_ptr])) by { reveal(kernel_objects_unlocked_except); };
    }
    let (process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr, Tracked(process_page_lock_perm), Tracked(pagetable_page_lock_perm), Tracked(l4_page_lock_perm), Tracked(iommu_table_page_lock_perm), Tracked(iommu_l4_page_lock_perm)) = allocate_new_process_with_iommu_pages(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), current_thread_ptr, container_ptr, cpu_id, Tracked(&current_thread_lock_perm));
    proof {
        assert(held_endpoints_unchanged(old(krnl).ep_mp, krnl.ep_mp, lctx)) by { reveal(held_endpoints_unchanged); };
        assert(endpoint_objects_unlocked_except(krnl.ep_mp, lctx.thread_id(), set![endpoint_ptr])) by { endpoint_objects_unlocked_except_preserved_for_held_unchanged(old(krnl).ep_mp, krnl.ep_mp, &*lctx, set![endpoint_ptr]); };
        assert(krnl.cpu_arr.spec_index(cpu_id).view().wlocked_by(lctx) && cpu_lock_perm.lock_id() == krnl.cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id) by { reveal(held_cpus_unchanged); };
        assert(krnl.ctn_mp.dom().contains(container_ptr) && krnl.ctn_mp.spec_index(container_ptr) == old(krnl).ctn_mp.spec_index(container_ptr)) by { reveal(held_containers_unchanged); };
        assert(krnl.prc_mp.dom().contains(parent_ptr) && krnl.prc_mp.spec_index(parent_ptr) == old(krnl).prc_mp.spec_index(parent_ptr)) by { reveal(held_processes_unchanged); };
        assert(krnl.pcid_allc_mp.dom().contains(pcid_allocator_ptr) && krnl.pcid_allc_mp.spec_index(pcid_allocator_ptr) == old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr)) by { reveal(held_pcid_allocators_unchanged); };
        assert(krnl.pt_mp.dom().contains(source_pagetable_ptr) && krnl.pt_mp.spec_index(source_pagetable_ptr) == old(krnl).pt_mp.spec_index(source_pagetable_ptr)) by { reveal(held_pagetables_unchanged); };
        assert(share_mapping_4k_source_range_present(krnl, source_pagetable_ptr, source_range)) by { reveal(share_mapping_4k_source_range_present); reveal(PageTable::wf_mapping_4k); reveal(mapped_4k_page_pagetable_wf); source_range.va_range_lemma(); };
        assert(!krnl.prc_mp.dom().contains(process_page_ptr)) by { page_ptr_roundtrip(); reveal(process_pages_wf); };
        assert(!krnl.pt_mp.dom().contains(pagetable_page_ptr)) by { page_ptr_roundtrip(); reveal(pagetable_pages_wf); };
        assert(!krnl.it_mp.dom().contains(iommu_table_page_ptr)) by { page_ptr_roundtrip(); reveal(iommu_table_pages_wf); };
        assert(thread_objects_unlocked_except(krnl.thr_mp, lctx.thread_id(), set![current_thread_ptr])) by { reveal(kernel_objects_unlocked_except); reveal(thread_objects_unlocked_except); };
        assert(pagetable_objects_unlocked_except(krnl.pt_mp, lctx.thread_id(), set![source_pagetable_ptr])) by { reveal(kernel_objects_unlocked_except); reveal(pagetable_objects_unlocked_except); reveal(held_pagetables_unchanged); };
        assert({
            &&& cpu_objects_unlocked_except(krnl.cpu_arr, lctx.thread_id(), set![cpu_id])
            &&& container_objects_unlocked_except(krnl.ctn_mp, lctx.thread_id(), set![container_ptr])
            &&& scheduler_objects_unlocked(krnl.sched_mp, lctx.thread_id())
            &&& process_objects_unlocked_except(krnl.prc_mp, lctx.thread_id(), set![parent_ptr])
            &&& endpoint_objects_unlocked_except(krnl.ep_mp, lctx.thread_id(), set![endpoint_ptr])
            &&& iommu_table_objects_unlocked(krnl.it_mp, lctx.thread_id())
            &&& pcid_allocator_objects_unlocked_except(krnl.pcid_allc_mp, lctx.thread_id(), set![pcid_allocator_ptr])
            &&& allocator_objects_unlocked(krnl.allc_2m_mp, lctx.thread_id())
            &&& allocator_objects_unlocked(krnl.allc_1g_mp, lctx.thread_id())
        }) by { reveal(kernel_objects_unlocked_except); reveal(cpu_objects_unlocked_except); reveal(container_objects_unlocked_except); reveal(scheduler_objects_unlocked); reveal(process_objects_unlocked_except); reveal(endpoint_objects_unlocked_except); reveal(iommu_table_objects_unlocked); reveal(pcid_allocator_objects_unlocked_except); reveal(allocator_objects_unlocked_except); reveal(held_cpus_unchanged); reveal(held_containers_unchanged); reveal(held_schedulers_unchanged); reveal(held_processes_unchanged); reveal(held_endpoints_unchanged); reveal(held_pcid_allocators_unchanged); reveal(held_iommu_tables_unchanged); };
    }
    let (child_ptr, target_pagetable_ptr, iommu_table_ptr, Tracked(child_lock_perm), Tracked(target_pagetable_lock_perm), Tracked(iommu_table_lock_perm)) = publish_staged_process_with_iommu(krnl, source_range, Ghost(Set::empty().insert(endpoint_ptr)), Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, parent_ptr, current_thread_ptr, scheduler_ptr, allocator_ptr, pcid_allocator_ptr, source_pagetable_ptr, pcid, process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr, Tracked(process_page_lock_perm), Tracked(pagetable_page_lock_perm), Tracked(l4_page_lock_perm), Tracked(iommu_table_page_lock_perm), Tracked(iommu_l4_page_lock_perm), Tracked(&cpu_lock_perm), Tracked(&container_lock_perm), Tracked(pcid_allocator_lock_perm), Tracked(parent_lock_perm), Tracked(&current_thread_lock_perm), Tracked(&source_pagetable_lock_perm));
    let Tracked(scheduler_lock_perm) = share_pages_and_lock_scheduler(krnl, source_range, Ghost(Set::empty().insert(endpoint_ptr)), Ghost(Set::empty().insert(iommu_table_ptr)), Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, parent_ptr, child_ptr, current_thread_ptr, scheduler_ptr, allocator_ptr, source_pagetable_ptr, target_pagetable_ptr, Tracked(&cpu_lock_perm), Tracked(&container_lock_perm), Tracked(&child_lock_perm), Tracked(&current_thread_lock_perm), Tracked(&source_pagetable_lock_perm), Tracked(&target_pagetable_lock_perm));
    proof {
        assert(krnl.ep_mp.dom().contains(endpoint_ptr) && krnl.ep_mp.spec_index(endpoint_ptr).is_init() && krnl.ep_mp.spec_index(endpoint_ptr).wlocked_by(lctx) && !krnl.ep_mp.spec_index(endpoint_ptr).being_killed() && krnl.ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((current_thread_ptr, endpoint_index)) && endpoint_lock_perm.lock_id() == krnl.ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id) by { reveal(held_endpoints_unchanged); reveal(endpoint_perms_wf); reveal(endpoints_inv); };
        assert(krnl.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.wf() && krnl.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr)) by { reveal(thread_perms_wf); reveal(thread_endpoint_ref_counter_wf); };
        assert(krnl.ctn_mp.dom().contains(krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container)) by { reveal(container_endpoint_wf); };
        assert({
            ||| krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container == container_ptr
            ||| krnl.ctn_mp.spec_index(krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container).view().subtree_set.view().contains(container_ptr)
        }) by { reveal(container_thread_endpoint_wf); };
        assert(krnl.prc_mp.spec_index(child_ptr).view().iommu_table == Some(iommu_table_ptr) && krnl.it_mp.dom().contains(iommu_table_ptr) && krnl.it_mp.spec_index(iommu_table_ptr).wlocked_by(lctx) && krnl.it_mp.spec_index(iommu_table_ptr).view().is_empty() && iommu_table_lock_perm.lock_id() == krnl.it_mp.spec_index(iommu_table_ptr).locking_thread()->Write_lock_id) by { reveal(process_iommu_table_match); reveal(held_iommu_tables_unchanged); };
    }
    let new_thread_ptr = create_initial_thread_with_iommu_endpoint_and_finish_new_process(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, child_ptr, current_thread_ptr, scheduler_ptr, endpoint_ptr, endpoint_index, source_pagetable_ptr, target_pagetable_ptr, iommu_table_ptr, Tracked(cpu_lock_perm), Tracked(container_lock_perm), Tracked(child_lock_perm), Tracked(current_thread_lock_perm), Tracked(scheduler_lock_perm), Tracked(endpoint_lock_perm), Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm), Tracked(iommu_table_lock_perm));
    proof {
        assert(kernel_u_create_process_with_iommu_changed(steps.steps.spec_index(old(steps).steps.len() as int).old_u, steps.steps.spec_index(old(steps).steps.len() as int).new_u, parent_ptr, child_ptr)) by { vstd::seq::lemma_seq_subrange_index(steps.steps, 0, (old(steps).steps.len() + 1) as int, old(steps).steps.len() as int); };
        assert(kernel_u_new_process_shared(steps.steps.spec_index(old(steps).steps.len() as int).new_u, steps.steps.spec_index((old(steps).steps.len() + source_range.len) as int).new_u, parent_ptr, child_ptr, source_range)) by {
            vstd::seq::lemma_seq_subrange_index(steps.steps, 0, (old(steps).steps.len() + 1) as int, old(steps).steps.len() as int);
            assert(1 + source_range.len - 1 == source_range.len) by (nonlinear_arith);
        };
    }
}

} // verus!
