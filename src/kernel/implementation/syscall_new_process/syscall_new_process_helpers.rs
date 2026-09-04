use vstd::prelude::*;
use vstd::assert_sets_equal;
use crate::*;
#[cfg(feature = "split-crates")]
use veriflat_kernel_core::{attach_endpoint_reference_and_unlock, create_thread_from_staged_page_merged, kernel_u_new_thread_changed};
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::create_thread_from_staged_page::{create_thread_from_staged_page_merged, kernel_u_new_thread_changed};
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::attach_endpoint_reference_and_unlock::attach_endpoint_reference_and_unlock;
use super::syscall_new_process_publish::publish_staged_process;
use super::syscall_new_process_spec::kernel_u_new_process_shared;

verus! {

#[verifier::spinoff_prover]
pub(super) fn allocate_new_process_pages(
    krnl: &mut KernelK,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>,
    current_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr,
    cpu_id: CpuId,
    Tracked(current_thread_lock_perm): Tracked<&LockPerm>,
) -> (ret: (PagePtr, PagePtr, PagePtr, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>))
    requires
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 3,
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
        ret.0 != ret.1 && ret.0 != ret.2 && ret.1 != ret.2,
        page_ptr_valid(ret.0) && page_ptr_valid(ret.1) && page_ptr_valid(ret.2),
        final(lctx).page_lock_map().dom() == set![page_ptr2page_index(ret.0), page_ptr2page_index(ret.1), page_ptr2page_index(ret.2)],
        page_objects_unlocked_except(final(krnl).pg_arr, final(lctx).thread_id(), set![page_ptr2page_index(ret.0), page_ptr2page_index(ret.1), page_ptr2page_index(ret.2)]),
        thread_objects_unlocked_except(final(krnl).thr_mp, final(lctx).thread_id(), set![current_thread_ptr]),
        forall|exceptions: Set<RwLockPageTableRoot>|
            #![trigger pagetable_objects_unlocked_except(old(krnl).pt_mp, old(lctx).thread_id(), exceptions)]
            #![trigger pagetable_objects_unlocked_except(final(krnl).pt_mp, final(lctx).thread_id(), exceptions)]
            pagetable_objects_unlocked_except(old(krnl).pt_mp, old(lctx).thread_id(), exceptions)
            ==> pagetable_objects_unlocked_except(final(krnl).pt_mp, final(lctx).thread_id(), exceptions),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view() == set![ret.0, ret.1, ret.2],
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
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().owning_container == container_ptr,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.1)).view().view().owning_container == container_ptr,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.2)).view().view().owning_container == container_ptr,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().wlocked_by(final(lctx)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.1)).view().wlocked_by(final(lctx)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.2)).view().wlocked_by(final(lctx)),
        ret.3.view().state() is WriteLock && ret.3.view().thread_id() == final(lctx).thread_id() && ret.3.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().locking_thread()->Write_lock_id,
        ret.4.view().state() is WriteLock && ret.4.view().thread_id() == final(lctx).thread_id() && ret.4.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.1)).view().locking_thread()->Write_lock_id,
        ret.5.view().state() is WriteLock && ret.5.view().thread_id() == final(lctx).thread_id() && ret.5.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.2)).view().locking_thread()->Write_lock_id,
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
    let (pages, Tracked(mut page_lock_perms)) = allocate_free_4k_pages::<3>(krnl, current_thread_ptr, container_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(current_thread_lock_perm));
    let process_page_ptr = *pages.get(0);
    let pagetable_page_ptr = *pages.get(1);
    let l4_page_ptr = *pages.get(2);
    proof {
        assert(pages.view().to_set().contains(process_page_ptr) && pages.view().to_set().contains(pagetable_page_ptr) && pages.view().to_set().contains(l4_page_ptr)) by { pages.view().to_set_ensures(); };
        assert(process_page_ptr != pagetable_page_ptr && process_page_ptr != l4_page_ptr && pagetable_page_ptr != l4_page_ptr) by { seq_index_lemma::<PagePtr>(); };
        assert(page_ptrs_to_indices(pages.view()) =~= set![page_ptr2page_index(process_page_ptr), page_ptr2page_index(pagetable_page_ptr), page_ptr2page_index(l4_page_ptr)]) by {
            broadcast use Seq::lemma_push_map_commute;
            pages.view().map_values(|page_ptr: PagePtr| page_ptr2page_index(page_ptr)).to_set_ensures();
            assert_sets_equal!(page_ptrs_to_indices(pages.view()) == set![page_ptr2page_index(process_page_ptr), page_ptr2page_index(pagetable_page_ptr), page_ptr2page_index(l4_page_ptr)]);
        };
        assert(krnl.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view() =~= set![process_page_ptr, pagetable_page_ptr, l4_page_ptr]) by { pages.view().to_set_ensures(); assert_sets_equal!(krnl.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view() == set![process_page_ptr, pagetable_page_ptr, l4_page_ptr]); };
        assert(page_ptr_valid(process_page_ptr) && page_ptr_valid(pagetable_page_ptr) && page_ptr_valid(l4_page_ptr)) by {  pages.view().to_set_ensures(); };
        assert(krnl.pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }) && krnl.pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }) && krnl.pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr })) by {  pages.view().to_set_ensures(); };
    }
    let tracked process_page_lock_perm = page_lock_perms.tracked_remove(process_page_ptr);
    let tracked pagetable_page_lock_perm = page_lock_perms.tracked_remove(pagetable_page_ptr);
    let tracked l4_page_lock_perm = page_lock_perms.tracked_remove(l4_page_ptr);
    proof {
        assert(lctx.holds_no_allocator_locks(PageSize::SZ2m) && lctx.holds_no_allocator_locks(PageSize::SZ1g)) by { reveal(LocalContext::holds_no_allocator_locks); };
        assert(krnl.thr_mp.spec_index(current_thread_ptr).view().state == old(krnl).thr_mp.spec_index(current_thread_ptr).view().state) by { reveal(Thread::stable_allocation_root_equal); };
    }
    (process_page_ptr, pagetable_page_ptr, l4_page_ptr, Tracked(process_page_lock_perm), Tracked(pagetable_page_lock_perm), Tracked(l4_page_lock_perm))
}

/// Allocate and publish the initial thread, then release the creation locks.
#[verifier::spinoff_prover]
fn create_initial_thread_and_finish_new_process(
    krnl: &mut KernelK,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>,
    cpu_id: CpuId,
    container_ptr: RwLockContainerPtr,
    child_ptr: RwLockProcessPtr,
    current_thread_ptr: RwLockThreadPtr,
    scheduler_ptr: RwLockSchedulerPtr,
    source_pagetable_ptr: RwLockPageTableRoot,
    target_pagetable_ptr: RwLockPageTableRoot,
    cpu_lock_perm: Tracked<LockPerm>,
    container_lock_perm: Tracked<LockPerm>,
    child_lock_perm: Tracked<LockPerm>,
    current_thread_lock_perm: Tracked<LockPerm>,
    scheduler_lock_perm: Tracked<LockPerm>,
    source_pagetable_lock_perm: Tracked<LockPerm>,
    target_pagetable_lock_perm: Tracked<LockPerm>,
) -> (new_thread_ptr: RwLockThreadPtr)
    requires
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        mmap_4k_allocation_ready(old(krnl), old(lctx)),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).object_lock_scope(Set::empty(), set![cpu_id], set![container_ptr], set![child_ptr], set![current_thread_ptr], Set::empty(), set![scheduler_ptr], Set::empty(), set![source_pagetable_ptr, target_pagetable_ptr], Set::empty()),
        kernel_objects_unlocked_except(old(krnl), old(lctx).thread_id(), set![cpu_id], set![container_ptr], set![scheduler_ptr], set![child_ptr], set![current_thread_ptr], Set::empty(), Set::empty(), set![source_pagetable_ptr, target_pagetable_ptr], Set::empty(), Set::empty(), Set::empty(), Set::empty(), Set::empty()),
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
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).sched_mp.dom().contains(scheduler_ptr),
        old(krnl).sched_mp.spec_index(scheduler_ptr).wlocked_by(old(lctx)),
        !old(krnl).sched_mp.spec_index(scheduler_ptr).being_killed(),
        scheduler_lock_perm.view().state() is WriteLock,
        scheduler_lock_perm.view().thread_id() == old(lctx).thread_id(),
        scheduler_lock_perm.view().lock_id() == old(krnl).sched_mp.spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
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
        final(krnl).thr_mp.dom().contains(new_thread_ptr),
        final(krnl).thr_mp.spec_index(new_thread_ptr).view().state is SCHEDULED,
        final(krnl).thr_mp.spec_index(new_thread_ptr).view().owning_proc == child_ptr,
        final(krnl).thr_mp.spec_index(new_thread_ptr).view().owning_container == container_ptr,
{
    let tracked cpu_lock_perm = cpu_lock_perm.get();
    let tracked container_lock_perm = container_lock_perm.get();
    let tracked child_lock_perm = child_lock_perm.get();
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked scheduler_lock_perm = scheduler_lock_perm.get();
    let tracked source_pagetable_lock_perm = source_pagetable_lock_perm.get();
    let tracked target_pagetable_lock_perm = target_pagetable_lock_perm.get();
    let (thread_page_ptr, Tracked(thread_page_lock_perm)) = allocate_free_4k_page(krnl, current_thread_ptr, container_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&current_thread_lock_perm));
    proof {
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
    }
    let (new_thread_ptr, Tracked(new_thread_lock_perm)) = create_thread_from_staged_page_merged(krnl, thread_page_ptr, child_ptr, current_thread_ptr, container_ptr, scheduler_ptr, Tracked(&mut *lctx), Tracked(&thread_page_lock_perm), Tracked(&child_lock_perm), Tracked(&current_thread_lock_perm), Tracked(&scheduler_lock_perm));
krnl.wunlock_thread(new_thread_ptr, Tracked(&mut *lctx), Tracked(new_thread_lock_perm));
    krnl.wunlock_process(child_ptr, Tracked(&mut *lctx), Tracked(child_lock_perm));
    krnl.wunlock_pagetable(target_pagetable_ptr, Tracked(&mut *lctx), Tracked(target_pagetable_lock_perm));
    krnl.wunlock_pagetable(source_pagetable_ptr, Tracked(&mut *lctx), Tracked(source_pagetable_lock_perm));
    krnl.wunlock_page(page_ptr2page_index(thread_page_ptr), Tracked(&mut *lctx), Tracked(thread_page_lock_perm));
    krnl.wunlock_scheduler(scheduler_ptr, Tracked(&mut *lctx), Tracked(scheduler_lock_perm));
    krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
    proof { assert(krnl.ctn_mp.dom().contains(container_ptr) && !krnl.ctn_mp.spec_index(container_ptr).being_killed() && !krnl.ctn_mp.spec_index(container_ptr).view().owned_processes.view().is_empty() && krnl.ctn_mp.spec_index(container_ptr).wlocked_by(lctx) && container_lock_perm.lock_id() == krnl.ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id) by {  reveal(container_process_wf); }; }
    krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
    krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        steps.end_kernel_step(&*krnl, &*lctx);
    }
    new_thread_ptr
}

#[verifier::spinoff_prover]
pub(super) fn create_initial_thread_with_endpoint_and_finish_new_process(
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
    cpu_lock_perm: Tracked<LockPerm>,
    container_lock_perm: Tracked<LockPerm>,
    child_lock_perm: Tracked<LockPerm>,
    current_thread_lock_perm: Tracked<LockPerm>,
    scheduler_lock_perm: Tracked<LockPerm>,
    endpoint_lock_perm: Tracked<LockPerm>,
    source_pagetable_lock_perm: Tracked<LockPerm>,
    target_pagetable_lock_perm: Tracked<LockPerm>,
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
        old(lctx).object_lock_scope(Set::empty(), set![cpu_id], set![container_ptr], set![child_ptr], set![current_thread_ptr], set![endpoint_ptr], set![scheduler_ptr], Set::empty(), set![source_pagetable_ptr, target_pagetable_ptr], Set::empty()),
        kernel_objects_unlocked_except(old(krnl), old(lctx).thread_id(), set![cpu_id], set![container_ptr], set![scheduler_ptr], set![child_ptr], set![current_thread_ptr], Set::empty(), set![endpoint_ptr], set![source_pagetable_ptr, target_pagetable_ptr], Set::empty(), Set::empty(), Set::empty(), Set::empty(), Set::empty()),
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
        final(krnl).thr_mp.dom().contains(new_thread_ptr),
        final(krnl).thr_mp.spec_index(new_thread_ptr).view().state is SCHEDULED,
        final(krnl).thr_mp.spec_index(new_thread_ptr).view().owning_proc == child_ptr,
        final(krnl).thr_mp.spec_index(new_thread_ptr).view().owning_container == container_ptr,
        final(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.wf(),
        final(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.spec_index(0) == Some(endpoint_ptr),
{
    let tracked cpu_lock_perm = cpu_lock_perm.get();
    let tracked container_lock_perm = container_lock_perm.get();
    let tracked child_lock_perm = child_lock_perm.get();
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked scheduler_lock_perm = scheduler_lock_perm.get();
    let tracked endpoint_lock_perm = endpoint_lock_perm.get();
    let tracked source_pagetable_lock_perm = source_pagetable_lock_perm.get();
    let tracked target_pagetable_lock_perm = target_pagetable_lock_perm.get();
let (thread_page_ptr, Tracked(thread_page_lock_perm)) = allocate_free_4k_page(krnl, current_thread_ptr, container_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&current_thread_lock_perm));
    proof {
        assert(endpoint_objects_unlocked_except(krnl.ep_mp, lctx.thread_id(), set![endpoint_ptr])) by { endpoint_objects_unlocked_except_preserved_for_held_unchanged(old(krnl).ep_mp, krnl.ep_mp, &*lctx, set![endpoint_ptr]); };
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
    }
    let (new_thread_ptr, Tracked(new_thread_lock_perm)) = create_thread_from_staged_page_merged(krnl, thread_page_ptr, child_ptr, current_thread_ptr, container_ptr, scheduler_ptr, Tracked(&mut *lctx), Tracked(&thread_page_lock_perm), Tracked(&child_lock_perm), Tracked(&current_thread_lock_perm), Tracked(&scheduler_lock_perm));
    proof {
        assert(krnl.ep_mp.dom().contains(endpoint_ptr) && krnl.ep_mp.spec_index(endpoint_ptr).is_init() && krnl.ep_mp.spec_index(endpoint_ptr).wlocked_by(lctx) && endpoint_lock_perm.lock_id() == krnl.ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id) by { reveal(endpoint_perms_wf);   };
        assert(krnl.ctn_mp.dom().contains(krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container)) by { reveal(container_endpoint_wf); };
        assert({
            ||| krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container == container_ptr
            ||| krnl.ctn_mp.spec_index(krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container).view().subtree_set.view().contains(container_ptr)
        }) by { reveal(container_thread_endpoint_wf); };
    }
    attach_endpoint_reference_and_unlock(krnl, new_thread_ptr, endpoint_ptr, cpu_id, scheduler_ptr, child_ptr, current_thread_ptr, page_ptr2page_index(thread_page_ptr), Tracked(&mut *lctx), Tracked(new_thread_lock_perm), Tracked(endpoint_lock_perm));
    krnl.wunlock_process(child_ptr, Tracked(&mut *lctx), Tracked(child_lock_perm));
    krnl.wunlock_pagetable(target_pagetable_ptr, Tracked(&mut *lctx), Tracked(target_pagetable_lock_perm));
    krnl.wunlock_pagetable(source_pagetable_ptr, Tracked(&mut *lctx), Tracked(source_pagetable_lock_perm));
    krnl.wunlock_page(page_ptr2page_index(thread_page_ptr), Tracked(&mut *lctx), Tracked(thread_page_lock_perm));
    krnl.wunlock_scheduler(scheduler_ptr, Tracked(&mut *lctx), Tracked(scheduler_lock_perm));
    krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
    proof { assert(krnl.ctn_mp.dom().contains(container_ptr) && !krnl.ctn_mp.spec_index(container_ptr).being_killed() && !krnl.ctn_mp.spec_index(container_ptr).view().owned_processes.view().is_empty() && krnl.ctn_mp.spec_index(container_ptr).wlocked_by(lctx) && container_lock_perm.lock_id() == krnl.ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id) by {  reveal(container_process_wf); }; }
    krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
    krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        assert({
            &&& krnl.thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.wf()
            &&& krnl.thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.spec_index(0) == Some(endpoint_ptr)
            &&& krnl.thr_mp.spec_index(new_thread_ptr).view().owning_proc == child_ptr
            &&& krnl.thr_mp.spec_index(new_thread_ptr).view().owning_container == container_ptr
        }) by { reveal(thread_perms_wf); reveal(process_thread_wf);  };
        steps.end_kernel_step(&*krnl, &*lctx);
    }
    new_thread_ptr
}

#[verifier::spinoff_prover]
pub(super) fn share_pages_and_lock_scheduler(
    krnl: &mut KernelK,
    source_range: &VaRange4K,
    Ghost(endpoint_exceptions): Ghost<Set<RwLockEndpointPtr>>,
    Ghost(iommu_table_exceptions): Ghost<Set<RwLockPageTableRoot>>,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>,
    cpu_id: CpuId,
    container_ptr: RwLockContainerPtr,
    parent_ptr: RwLockProcessPtr,
    child_ptr: RwLockProcessPtr,
    current_thread_ptr: RwLockThreadPtr,
    scheduler_ptr: RwLockSchedulerPtr,
    allocator_ptr: RwLockPageAllocatorPtr,
    source_pagetable_ptr: RwLockPageTableRoot,
    target_pagetable_ptr: RwLockPageTableRoot,
    Tracked(cpu_lock_perm): Tracked<&LockPerm>,
    Tracked(container_lock_perm): Tracked<&LockPerm>,
    Tracked(child_lock_perm): Tracked<&LockPerm>,
    Tracked(current_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>,
    Tracked(target_pagetable_lock_perm): Tracked<&LockPerm>,
) -> (scheduler_lock_perm: Tracked<LockPerm>)
    requires
        source_range.wf(),
        source_range.len > 0,
        source_range.len <= usize::MAX / 3usize,
        old(steps).steps.len() > 0,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        old(steps).steps.last().new_u.process_map.dom().contains(parent_ptr),
        old(steps).steps.last().new_u.process_map.dom().contains(child_ptr),
        kernel_k_to_kernel_u(*old(krnl)).process_map.dom().contains(child_ptr),
        old(steps).steps.last().new_u.process_map.spec_index(child_ptr) == kernel_k_to_kernel_u(*old(krnl)).process_map.spec_index(child_ptr),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        mmap_4k_allocation_ready(old(krnl), old(lctx)),
        old(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).object_lock_scope(Set::empty(), set![cpu_id], set![container_ptr], set![child_ptr], set![current_thread_ptr], endpoint_exceptions, Set::empty(), Set::empty(), set![source_pagetable_ptr, target_pagetable_ptr], iommu_table_exceptions),
        kernel_objects_unlocked_except(old(krnl), old(lctx).thread_id(), set![cpu_id], set![container_ptr], Set::empty(), set![child_ptr], set![current_thread_ptr], Set::empty(), endpoint_exceptions, set![source_pagetable_ptr, target_pagetable_ptr], iommu_table_exceptions, Set::empty(), Set::empty(), Set::empty(), Set::empty()),
        old(krnl).cpu_arr.spec_index(cpu_id).view().wlocked_by(old(lctx)),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).wlocked_by(old(lctx)),
        !old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        old(krnl).allc_4k_mp.dom().contains(allocator_ptr),
        container_lock_perm.state() is WriteLock,
        container_lock_perm.thread_id() == old(lctx).thread_id(),
        container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(child_ptr),
        old(krnl).prc_mp.spec_index(child_ptr).wlocked_by(old(lctx)),
        !old(krnl).prc_mp.spec_index(child_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(child_ptr).view_rodata().view().owning_container == container_ptr,
        old(krnl).prc_mp.spec_index(child_ptr).view_rodata().view().pagetable == target_pagetable_ptr,
        old(krnl).prc_mp.spec_index(child_ptr).view().iommu_table is Some ==> iommu_table_exceptions.contains(old(krnl).prc_mp.spec_index(child_ptr).view().iommu_table.unwrap()),
        child_lock_perm.state() is WriteLock,
        child_lock_perm.thread_id() == old(lctx).thread_id(),
        child_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(child_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).wlocked_by(old(lctx)),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc != child_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == source_pagetable_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state is RUNNING,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 1 + 3 * source_range.len,
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        source_pagetable_ptr != target_pagetable_ptr,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).wlocked_by(old(lctx)),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().proc_ptr == parent_ptr,
        source_pagetable_lock_perm.state() is WriteLock,
        source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        source_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().wf(),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(source_range.start),
        share_mapping_4k_source_range_present(old(krnl), source_pagetable_ptr, source_range),
        old(krnl).pt_mp.dom().contains(target_pagetable_ptr),
        old(krnl).pt_mp.spec_index(target_pagetable_ptr).wlocked_by(old(lctx)),
        old(krnl).pt_mp.spec_index(target_pagetable_ptr).view().proc_ptr == child_ptr,
        target_pagetable_lock_perm.state() is WriteLock,
        target_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        target_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(target_pagetable_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.spec_index(target_pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(source_range.start),
        old(krnl).pt_mp.spec_index(target_pagetable_ptr).view().is_empty(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
    ensures
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(steps).steps.len() == old(steps).steps.len() + source_range.len,
        final(steps).steps.subrange(0, old(steps).steps.len() as int) == old(steps).steps,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        kernel_u_new_process_shared(old(steps).steps.last().new_u, final(steps).steps.spec_index((old(steps).steps.len() + source_range.len - 1) as int).new_u, parent_ptr, child_ptr, source_range),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        mmap_4k_allocation_ready(final(krnl), final(lctx)),
        final(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        final(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        final(lctx).object_lock_scope(Set::empty(), set![cpu_id], set![container_ptr], set![child_ptr], set![current_thread_ptr], endpoint_exceptions, set![scheduler_ptr], Set::empty(), set![source_pagetable_ptr, target_pagetable_ptr], iommu_table_exceptions),
        kernel_objects_unlocked_except(final(krnl), final(lctx).thread_id(), set![cpu_id], set![container_ptr], set![scheduler_ptr], set![child_ptr], set![current_thread_ptr], Set::empty(), endpoint_exceptions, set![source_pagetable_ptr, target_pagetable_ptr], iommu_table_exceptions, Set::empty(), Set::empty(), Set::empty(), Set::empty()),
        held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().wlocked_by(final(lctx)),
        !final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == final(lctx).thread_id(),
        cpu_lock_perm.lock_id() == final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        final(krnl).ctn_mp.dom().contains(container_ptr),
        final(krnl).ctn_mp.spec_index(container_ptr).wlocked_by(final(lctx)),
        !final(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
        container_lock_perm.state() is WriteLock,
        container_lock_perm.thread_id() == final(lctx).thread_id(),
        container_lock_perm.lock_id() == final(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        final(krnl).prc_mp.dom().contains(child_ptr),
        final(krnl).prc_mp.spec_index(child_ptr).wlocked_by(final(lctx)),
        !final(krnl).prc_mp.spec_index(child_ptr).being_killed(),
        final(krnl).prc_mp.spec_index(child_ptr).view_rodata().view().owning_container == container_ptr,
        final(krnl).prc_mp.spec_index(child_ptr).view().iommu_table == old(krnl).prc_mp.spec_index(child_ptr).view().iommu_table,
        child_lock_perm.state() is WriteLock,
        child_lock_perm.thread_id() == final(lctx).thread_id(),
        child_lock_perm.lock_id() == final(krnl).prc_mp.spec_index(child_ptr).locking_thread()->Write_lock_id,
        final(krnl).thr_mp.dom().contains(current_thread_ptr),
        final(krnl).thr_mp.spec_index(current_thread_ptr).wlocked_by(final(lctx)),
        !final(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().state is RUNNING,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 1,
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == final(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).sched_mp.dom().contains(scheduler_ptr),
        final(krnl).sched_mp.spec_index(scheduler_ptr).wlocked_by(final(lctx)),
        !final(krnl).sched_mp.spec_index(scheduler_ptr).being_killed(),
        scheduler_lock_perm.view().state() is WriteLock,
        scheduler_lock_perm.view().thread_id() == final(lctx).thread_id(),
        scheduler_lock_perm.view().lock_id() == final(krnl).sched_mp.spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
        source_pagetable_ptr != target_pagetable_ptr,
        final(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        final(krnl).pt_mp.spec_index(source_pagetable_ptr).wlocked_by(final(lctx)),
        source_pagetable_lock_perm.state() is WriteLock,
        source_pagetable_lock_perm.thread_id() == final(lctx).thread_id(),
        source_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Write_lock_id,
        final(krnl).pt_mp.dom().contains(target_pagetable_ptr),
        final(krnl).pt_mp.spec_index(target_pagetable_ptr).wlocked_by(final(lctx)),
        target_pagetable_lock_perm.state() is WriteLock,
        target_pagetable_lock_perm.thread_id() == final(lctx).thread_id(),
        target_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(target_pagetable_ptr).locking_thread()->Write_lock_id,
{
    proof {
        assert(share_mapping_4k_range_owner_compatible(krnl, source_pagetable_ptr, current_thread_ptr, source_range)) by { source_range.va_range_lemma(); reveal(mapped_4k_page_pagetable_wf); reveal(container_process_page_pagetable_wf); reveal(container_page_owner_wf); reveal(container_thread_wf); reveal(process_thread_wf); reveal(process_pagetable_match); reveal(container_perms_wf); reveal(container_subtree_set_wf); reveal(container_uppertree_seq_wf); reveal(container_subtree_set_exclusive); };
        assert(krnl.pt_mp.spec_index(target_pagetable_ptr).view().spec_mapping_4k_va_range_empty(source_range.start, source_range.view().spec_index((source_range.len - 1) as int))) by {  reveal(PageTable::spec_mapping_4k_va_range_empty); };
    }
    share_mapping_4k_build_and_share(krnl, source_range, source_range, allocator_ptr, current_thread_ptr, current_thread_ptr, child_ptr, container_ptr, cpu_id, source_pagetable_ptr, target_pagetable_ptr, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(current_thread_lock_perm), Tracked(current_thread_lock_perm), Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm));
    proof {
        assert(kernel_u_new_process_shared(old(steps).steps.last().new_u, steps.steps.last().new_u, parent_ptr, child_ptr, source_range)) by {  reveal(process_pagetable_match); reveal(LockedMap::typed_lock_map_aligned); };
        assert(krnl.sched_mp.dom().contains(scheduler_ptr) && krnl.sched_mp.lock_id_by_key(scheduler_ptr).major == SCHEDULER_LOCK_MAJOR) by { reveal(container_scheduler_wf); reveal(scheduler_perms_wf); };
        assert(!krnl.sched_mp.spec_index(scheduler_ptr).locked_by_thread(lctx.thread_id())) by {  reveal(LockedMap::typed_lock_map_aligned); };
    }
    let Tracked(scheduler_lock_perm) = krnl.wlock_scheduler(scheduler_ptr, Tracked(&mut *lctx));
    proof {
        assert(lctx.holds_no_allocator_locks(PageSize::SZ4k)) by {  reveal(LocalContext::holds_no_allocator_locks);  };
        assert(lctx.holds_no_allocator_locks(PageSize::SZ2m) && lctx.holds_no_allocator_locks(PageSize::SZ1g)) by { reveal(LocalContext::holds_no_allocator_locks);   };
        assert({
            &&& !krnl.cpu_arr.spec_index(cpu_id).view().being_killed()
            &&& !krnl.ctn_mp.spec_index(container_ptr).being_killed()
            &&& krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr
            &&& !krnl.prc_mp.spec_index(child_ptr).being_killed()
            &&& krnl.prc_mp.spec_index(child_ptr).view_rodata().view().owning_container == container_ptr
            &&& !krnl.thr_mp.spec_index(current_thread_ptr).being_killed()
            &&& krnl.thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr
            &&& krnl.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean()
            &&& krnl.thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean()
            &&& krnl.thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 1
            &&& krnl.sched_mp.dom().contains(scheduler_ptr)
            &&& !krnl.sched_mp.spec_index(scheduler_ptr).being_killed()
        }) by {     reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf); };
    }
    Tracked(scheduler_lock_perm)
}


#[verifier::spinoff_prover]
pub(super) fn commit_new_process(
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
    pcid: Pcid,
    cpu_lock_perm: Tracked<LockPerm>,
    container_lock_perm: Tracked<LockPerm>,
    pcid_allocator_lock_perm: Tracked<LockPerm>,
    parent_lock_perm: Tracked<LockPerm>,
    current_thread_lock_perm: Tracked<LockPerm>,
    source_pagetable_lock_perm: Tracked<LockPerm>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        source_range.wf(),
        source_range.len > 0,
        source_range.len <= (usize::MAX - 4) / 3,
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
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 4 + 3 * source_range.len,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).wlocked_by(old(lctx)),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
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
        old(lctx).object_lock_scope(Set::empty(), set![cpu_id], set![container_ptr], set![parent_ptr], set![current_thread_ptr], Set::empty(), Set::empty(), set![pcid_allocator_ptr], set![source_pagetable_ptr], Set::empty()),
        kernel_objects_unlocked_except(old(krnl), old(lctx).thread_id(), set![cpu_id], set![container_ptr], Set::empty(), set![parent_ptr], set![current_thread_ptr], Set::empty(), Set::empty(), set![source_pagetable_ptr], Set::empty(), set![pcid_allocator_ptr], Set::empty(), Set::empty(), Set::empty()),
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
        exists|child_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr|
            #![trigger kernel_u_new_process_shared(final(steps).steps.spec_index(old(steps).steps.len() as int).new_u, final(steps).steps.spec_index((old(steps).steps.len() + source_range.len) as int).new_u, parent_ptr, child_ptr, source_range), final(krnl).thr_mp.spec_index(thread_ptr)]
        {
            let first_step = final(steps).steps.spec_index(old(steps).steps.len() as int);
            &&& kernel_u_create_process_changed(first_step.old_u, first_step.new_u, parent_ptr, child_ptr)
            &&& kernel_u_new_process_shared(first_step.new_u, final(steps).steps.spec_index((old(steps).steps.len() + source_range.len) as int).new_u, parent_ptr, child_ptr, source_range)
            &&& kernel_u_new_thread_changed(final(steps).steps.last().old_u, final(steps).steps.last().new_u, child_ptr)
            &&& final(krnl).thr_mp.dom().contains(thread_ptr)
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().state is SCHEDULED
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == child_ptr
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr
        },
{
    let tracked cpu_lock_perm = cpu_lock_perm.get();
    let tracked container_lock_perm = container_lock_perm.get();
    let tracked pcid_allocator_lock_perm = pcid_allocator_lock_perm.get();
    let tracked parent_lock_perm = parent_lock_perm.get();
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked source_pagetable_lock_perm = source_pagetable_lock_perm.get();
let (process_page_ptr, pagetable_page_ptr, l4_page_ptr, Tracked(process_page_lock_perm), Tracked(pagetable_page_lock_perm), Tracked(l4_page_lock_perm)) = allocate_new_process_pages(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), current_thread_ptr, container_ptr, cpu_id, Tracked(&current_thread_lock_perm));
    proof {
        assert(share_mapping_4k_source_range_present(krnl, source_pagetable_ptr, source_range)) by {  reveal(PageTable::wf_mapping_4k); reveal(mapped_4k_page_pagetable_wf); source_range.va_range_lemma(); };
        assert(!krnl.prc_mp.dom().contains(process_page_ptr)) by { page_ptr_roundtrip(); reveal(process_pages_wf); };
        assert(!krnl.pt_mp.dom().contains(pagetable_page_ptr)) by { page_ptr_roundtrip(); reveal(pagetable_pages_wf); };
    }
    let (child_ptr, target_pagetable_ptr, Tracked(child_lock_perm), Tracked(target_pagetable_lock_perm)) = publish_staged_process(krnl, source_range, Ghost(Set::empty()), Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, parent_ptr, current_thread_ptr, scheduler_ptr, allocator_ptr, pcid_allocator_ptr, source_pagetable_ptr, pcid, process_page_ptr, pagetable_page_ptr, l4_page_ptr, Tracked(process_page_lock_perm), Tracked(pagetable_page_lock_perm), Tracked(l4_page_lock_perm), Tracked(&cpu_lock_perm), Tracked(&container_lock_perm), Tracked(pcid_allocator_lock_perm), Tracked(parent_lock_perm), Tracked(&current_thread_lock_perm), Tracked(&source_pagetable_lock_perm));
    let Tracked(scheduler_lock_perm) = share_pages_and_lock_scheduler(krnl, source_range, Ghost(Set::empty()), Ghost(Set::empty()), Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, parent_ptr, child_ptr, current_thread_ptr, scheduler_ptr, allocator_ptr, source_pagetable_ptr, target_pagetable_ptr, Tracked(&cpu_lock_perm), Tracked(&container_lock_perm), Tracked(&child_lock_perm), Tracked(&current_thread_lock_perm), Tracked(&source_pagetable_lock_perm), Tracked(&target_pagetable_lock_perm));
    let new_thread_ptr = create_initial_thread_and_finish_new_process(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, child_ptr, current_thread_ptr, scheduler_ptr, source_pagetable_ptr, target_pagetable_ptr, Tracked(cpu_lock_perm), Tracked(container_lock_perm), Tracked(child_lock_perm), Tracked(current_thread_lock_perm), Tracked(scheduler_lock_perm), Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm));
    proof {
        assert(kernel_u_create_process_changed(steps.steps.spec_index(old(steps).steps.len() as int).old_u, steps.steps.spec_index(old(steps).steps.len() as int).new_u, parent_ptr, child_ptr)) by { vstd::seq::lemma_seq_subrange_index(steps.steps, 0, (old(steps).steps.len() + 1) as int, old(steps).steps.len() as int); };
        assert(kernel_u_new_process_shared(steps.steps.spec_index(old(steps).steps.len() as int).new_u, steps.steps.spec_index((old(steps).steps.len() + source_range.len) as int).new_u, parent_ptr, child_ptr, source_range)) by {
            vstd::seq::lemma_seq_subrange_index(steps.steps, 0, (old(steps).steps.len() + 1) as int, old(steps).steps.len() as int);
            assert(1 + source_range.len - 1 == source_range.len) by (nonlinear_arith);
        };
    }
}

#[verifier::spinoff_prover]
pub(super) fn commit_new_process_with_endpoint(
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
        source_range.len <= (usize::MAX - 4) / 3,
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
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 4 + 3 * source_range.len,
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
        exists|child_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr|
            #![trigger kernel_u_new_process_shared(final(steps).steps.spec_index(old(steps).steps.len() as int).new_u, final(steps).steps.spec_index((old(steps).steps.len() + source_range.len) as int).new_u, parent_ptr, child_ptr, source_range), final(krnl).thr_mp.spec_index(thread_ptr)]
        {
            let first_step = final(steps).steps.spec_index(old(steps).steps.len() as int);
            &&& kernel_u_create_process_changed(first_step.old_u, first_step.new_u, parent_ptr, child_ptr)
            &&& kernel_u_new_process_shared(first_step.new_u, final(steps).steps.spec_index((old(steps).steps.len() + source_range.len) as int).new_u, parent_ptr, child_ptr, source_range)
            &&& kernel_u_new_thread_changed(final(steps).steps.last().old_u, final(steps).steps.last().new_u, child_ptr)
            &&& final(krnl).thr_mp.dom().contains(thread_ptr)
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().state is SCHEDULED
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == child_ptr
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.wf()
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.spec_index(0) == Some(endpoint_ptr)
        },
{
    let tracked cpu_lock_perm = cpu_lock_perm.get();
    let tracked container_lock_perm = container_lock_perm.get();
    let tracked pcid_allocator_lock_perm = pcid_allocator_lock_perm.get();
    let tracked parent_lock_perm = parent_lock_perm.get();
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked source_pagetable_lock_perm = source_pagetable_lock_perm.get();
    let tracked endpoint_lock_perm = endpoint_lock_perm.get();
let (process_page_ptr, pagetable_page_ptr, l4_page_ptr, Tracked(process_page_lock_perm), Tracked(pagetable_page_lock_perm), Tracked(l4_page_lock_perm)) = allocate_new_process_pages(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), current_thread_ptr, container_ptr, cpu_id, Tracked(&current_thread_lock_perm));
    proof {
        assert(endpoint_objects_unlocked_except(krnl.ep_mp, lctx.thread_id(), set![endpoint_ptr])) by { endpoint_objects_unlocked_except_preserved_for_held_unchanged(old(krnl).ep_mp, krnl.ep_mp, &*lctx, set![endpoint_ptr]); };
        assert(share_mapping_4k_source_range_present(krnl, source_pagetable_ptr, source_range)) by {  reveal(PageTable::wf_mapping_4k); reveal(mapped_4k_page_pagetable_wf); source_range.va_range_lemma(); };
        assert(!krnl.prc_mp.dom().contains(process_page_ptr)) by { page_ptr_roundtrip(); reveal(process_pages_wf); };
        assert(!krnl.pt_mp.dom().contains(pagetable_page_ptr)) by { page_ptr_roundtrip(); reveal(pagetable_pages_wf); };
    }
    let (child_ptr, target_pagetable_ptr, Tracked(child_lock_perm), Tracked(target_pagetable_lock_perm)) = publish_staged_process(krnl, source_range, Ghost(Set::empty().insert(endpoint_ptr)), Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, parent_ptr, current_thread_ptr, scheduler_ptr, allocator_ptr, pcid_allocator_ptr, source_pagetable_ptr, pcid, process_page_ptr, pagetable_page_ptr, l4_page_ptr, Tracked(process_page_lock_perm), Tracked(pagetable_page_lock_perm), Tracked(l4_page_lock_perm), Tracked(&cpu_lock_perm), Tracked(&container_lock_perm), Tracked(pcid_allocator_lock_perm), Tracked(parent_lock_perm), Tracked(&current_thread_lock_perm), Tracked(&source_pagetable_lock_perm));
    let Tracked(scheduler_lock_perm) = share_pages_and_lock_scheduler(krnl, source_range, Ghost(Set::empty().insert(endpoint_ptr)), Ghost(Set::empty()), Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, parent_ptr, child_ptr, current_thread_ptr, scheduler_ptr, allocator_ptr, source_pagetable_ptr, target_pagetable_ptr, Tracked(&cpu_lock_perm), Tracked(&container_lock_perm), Tracked(&child_lock_perm), Tracked(&current_thread_lock_perm), Tracked(&source_pagetable_lock_perm), Tracked(&target_pagetable_lock_perm));
    proof {
        assert(krnl.ep_mp.dom().contains(endpoint_ptr) && krnl.ep_mp.spec_index(endpoint_ptr).is_init() && krnl.ep_mp.spec_index(endpoint_ptr).wlocked_by(lctx) && !krnl.ep_mp.spec_index(endpoint_ptr).being_killed() && krnl.ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((current_thread_ptr, endpoint_index)) && endpoint_lock_perm.lock_id() == krnl.ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id) by {  reveal(endpoint_perms_wf);  };
        assert(krnl.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.wf() && krnl.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr)) by { reveal(thread_perms_wf); reveal(thread_endpoint_ref_counter_wf); };
        assert(krnl.ctn_mp.dom().contains(krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container)) by { reveal(container_endpoint_wf); };
        assert({
            ||| krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container == container_ptr
            ||| krnl.ctn_mp.spec_index(krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container).view().subtree_set.view().contains(container_ptr)
        }) by { reveal(container_thread_endpoint_wf); };
    }
    let new_thread_ptr = create_initial_thread_with_endpoint_and_finish_new_process(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, child_ptr, current_thread_ptr, scheduler_ptr, endpoint_ptr, endpoint_index, source_pagetable_ptr, target_pagetable_ptr, Tracked(cpu_lock_perm), Tracked(container_lock_perm), Tracked(child_lock_perm), Tracked(current_thread_lock_perm), Tracked(scheduler_lock_perm), Tracked(endpoint_lock_perm), Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm));
    proof {
        assert(kernel_u_create_process_changed(steps.steps.spec_index(old(steps).steps.len() as int).old_u, steps.steps.spec_index(old(steps).steps.len() as int).new_u, parent_ptr, child_ptr)) by { vstd::seq::lemma_seq_subrange_index(steps.steps, 0, (old(steps).steps.len() + 1) as int, old(steps).steps.len() as int); };
        assert(kernel_u_new_process_shared(steps.steps.spec_index(old(steps).steps.len() as int).new_u, steps.steps.spec_index((old(steps).steps.len() + source_range.len) as int).new_u, parent_ptr, child_ptr, source_range)) by {
            vstd::seq::lemma_seq_subrange_index(steps.steps, 0, (old(steps).steps.len() + 1) as int, old(steps).steps.len() as int);
            assert(1 + source_range.len - 1 == source_range.len) by (nonlinear_arith);
        };
    }
}

}
