use vstd::prelude::*;
use crate::*;
use super::syscall_thread_exit_spec::*;
use super::syscall_thread_exit_trace::*;
use super::syscall_thread_exit_destroy::thread_exit_destroy;

verus! {
/// Lock phase of the finish step of the exit of the running thread: for its process's last thread (`last`), take the
/// container's PCID allocator; then take the thread's page and the 4K allocator cache on `cpu_id` of the page's owner.
/// Returns the owner, its 4K allocator, the container's PCID allocator, the page, cache, and PCID allocator perms, and
/// whether that cache is full.
pub(super) fn thread_exit_finish_lock_page_and_cache(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, last: bool,
) -> (ret: (RwLockContainerPtr, RwLockPageAllocatorPtr, RwLockPcidAllocatorPtr, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<Option<LockPerm>>, bool))
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom() =~= set![container_ptr],
        old(lctx).process_lock_map().dom() =~= set![process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).prc_mp.dom().contains(process_ptr),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
        !old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        !old(krnl).prc_mp.spec_index(process_ptr).being_killed(),
        !old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, allc_4k_mp: final(krnl).allc_4k_mp, pcid_allc_mp: final(krnl).pcid_allc_mp, ..*old(krnl) }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).page_lock_map().dom() =~= set![page_ptr2page_index(thread_ptr)],
        final(lctx).allocator_cache_4k_lock_map().dom() =~= set![(ret.1, cpu_id)],
        final(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        final(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        final(lctx).pcid_allocator_lock_map().dom() =~= if last { set![ret.2] } else { Set::empty() },
        final(lctx).endpoint_lock_map().dom().is_empty(),
        final(lctx).scheduler_lock_map().dom().is_empty(),
        final(lctx).cpu_set_lock_map().dom().is_empty(),
        final(lctx).pagetable_lock_map().dom().is_empty(),
        final(lctx).pagetable_window_lock_map().dom().is_empty(),
        final(lctx).iommu_table_lock_map().dom().is_empty(),
        final(lctx).iommu_root_table_lock_map().dom().is_empty(),
        final(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        final(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        final(lctx).pcid_needflush_lock_map().dom().is_empty(),
        final(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        page_ptr_valid(thread_ptr),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(thread_ptr), TypedLockMode::Write),
        ret.3.view().state() is WriteLock,
        ret.3.view().thread_id() == old(lctx).thread_id(),
        ret.3.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(thread_ptr)).view().locking_thread()->Write_lock_id,
        typed_lock_map_majors_lt(final(lctx).page_lock_map(), ALLOCATOR_CACHE_4K_MAJOR),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(thread_ptr)).view().view().owning_container == ret.0,
        final(krnl).ctn_mp.dom().contains(ret.0),
        final(krnl).ctn_mp.spec_index(ret.0).view_rodata().view().allocator_ptr_4k == ret.1,
        final(krnl).allc_4k_mp.dom().contains(ret.1),
        typed_lock_map_contains_mode(final(lctx).allocator_cache_4k_lock_map(), (ret.1, cpu_id), TypedLockMode::Write),
        ret.4.view().state() is WriteLock,
        ret.4.view().thread_id() == old(lctx).thread_id(),
        ret.4.view().lock_id() == final(krnl).allc_4k_mp.spec_index(ret.1).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        final(krnl).allc_4k_mp.spec_index(ret.1).cpu_caches.spec_index(cpu_id).view().view().view().len() <= ALLOCATOR_MAX_WATERMARK,
        ret.6 == (final(krnl).allc_4k_mp.spec_index(ret.1).cpu_caches.spec_index(cpu_id).view().view().view().len() == ALLOCATOR_MAX_WATERMARK),
        ret.2 == final(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator,
        last ==> {
            &&& typed_lock_map_contains_mode(final(lctx).pcid_allocator_lock_map(), ret.2, TypedLockMode::Write)
            &&& ret.5.view() is Some
            &&& ret.5.view()->Some_0.state() is WriteLock
            &&& ret.5.view()->Some_0.thread_id() == old(lctx).thread_id()
            &&& ret.5.view()->Some_0.lock_id() == final(krnl).pcid_allc_mp.spec_index(ret.2).locking_thread()->Write_lock_id
        },
{
    proof {
        container_perms_wf_at(krnl.ctn_mp, container_ptr);
        assert(typed_lock_map_majors_lt(lctx.cpu_lock_map(), CPU_LOCK_MAJOR_OFF) && typed_lock_map_majors_lt(lctx.thread_lock_map(), THREAD_SCHEDULED_LOCK_MAJOR)) by {
            krnl.cpu_arr.typed_lock_map_aligned_lock_id_at(lctx.cpu_lock_map(), lctx.thread_id(), cpu_id); krnl.thr_mp.typed_lock_map_aligned_lock_id_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr);
        };
    }
    let pcid_allocator_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().pcid_allocator;
    let tracked mut pcid_allocator_lock_perm: Option<LockPerm> = None;
    if last {
        proof {
            assert({
                &&& krnl.pcid_allc_mp.dom().contains(pcid_allocator_ptr)
                &&& krnl.pcid_allc_mp.spec_index(pcid_allocator_ptr).view().owning_container.view() == container_ptr
                &&& krnl.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr
                &&& krnl.pcid_allc_mp.spec_index(pcid_allocator_ptr).view().container_depth.view() == krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().depth
                &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().container_depth == krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().depth
                &&& krnl.prc_mp.spec_index(process_ptr).view_rodata().view().container_depth == krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().depth
                &&& krnl.thr_mp.spec_index(thread_ptr).view().container_depth == krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().depth
            }) by {
                container_pcid_allocator_wf_container_at(krnl.ctn_mp, krnl.pcid_allc_mp, container_ptr); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, thread_ptr);
                container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id); container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, process_ptr);
            };
        }
        let Tracked(lock_perm) = krnl.wlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx));
        proof { pcid_allocator_lock_perm = Some(lock_perm); }
    }
    proof {
        thread_perms_wf_at(krnl.thr_mp, thread_ptr); page_ptr_valid_imply_page_index_valid();
        assert(page_ptr_valid(thread_ptr) && krnl.pg_arr.spec_index(page_ptr2page_index(thread_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsThread })) by { thread_pages_wf_at(krnl.thr_mp, krnl.pg_arr, thread_ptr); };
    }
    let page_index = page_ptr2page_index(thread_ptr);
    let Tracked(page_lock_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));
    proof { page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, page_index); }
    let owner = krnl.pg_arr.borrow_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(&page_lock_perm)).owning_container;
    proof { assert(krnl.ctn_mp.dom().contains(owner)) by { container_page_owner_backward_at(krnl.ctn_mp, krnl.pg_arr, page_index); }; container_perms_wf_at(krnl.ctn_mp, owner); }
    let allocator_ptr = krnl.ctn_mp.borrow_rodata(owner).borrow().allocator_ptr_4k;
    proof { assert(krnl.allc_4k_mp.dom().contains(allocator_ptr)) by { container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, owner); }; }
    let Tracked(cache_lock_perm) = krnl.wlock_allocator_cache_4k(allocator_ptr, cpu_id, Tracked(&mut *lctx));
    let cache = krnl.allc_4k_mp.borrow_cache_typed(allocator_ptr, cpu_id, Ghost(lctx.allocator_cache_4k_lock_map()), Tracked(&*lctx), Tracked(&cache_lock_perm));
    let full = cache.linked_list.len() == ALLOCATOR_MAX_WATERMARK;
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    (owner, allocator_ptr, pcid_allocator_ptr, Tracked(page_lock_perm), Tracked(cache_lock_perm), Tracked(pcid_allocator_lock_perm), full)
}

/// Finish step of the exit of the running thread whose page, the 4K allocator cache on `cpu_id` of the page's owner
/// `owner`, and (for the last thread) the container's PCID allocator are write-held: take that allocator's quota and the
/// default-pcid needflush cell of `cpu_id`, remove the thread, release every lock, and record the finish step. The step
/// starts at the snapshot of `steps`, where `finish_lctx` holds the cpu, container, process, and thread.
pub(super) fn thread_exit_finish_destroy_and_record(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, Ghost(finish_lctx): Ghost<LocalContext>, cpu_id: CpuId,
    container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr,
    pcid_allocator_ptr: RwLockPcidAllocatorPtr, Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(container_lock_perm): Tracked<LockPerm>,
    Tracked(process_lock_perm): Tracked<LockPerm>, Tracked(thread_lock_perm): Tracked<LockPerm>, Tracked(page_lock_perm): Tracked<LockPerm>,
    Tracked(cache_lock_perm): Tracked<LockPerm>, Tracked(pcid_allocator_lock_perm): Tracked<Option<LockPerm>>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        page_ptr_valid(thread_ptr),
        0 <= start <= old(steps).view().len(),
        thread_exit_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id),
        typed_lock_maps_aligned(&old(steps).snapshot_k(), &finish_lctx),
        typed_lock_map_contains_mode(finish_lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(finish_lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(finish_lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(finish_lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        *old(krnl) == (KernelK { pg_arr: old(krnl).pg_arr, allc_4k_mp: old(krnl).allc_4k_mp, pcid_allc_mp: old(krnl).pcid_allc_mp, ..old(steps).snapshot_k() }),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).prc_mp.dom().contains(process_ptr),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom() =~= set![container_ptr],
        old(lctx).process_lock_map().dom() =~= set![process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(lctx).page_lock_map().dom() =~= set![page_ptr2page_index(thread_ptr)],
        old(lctx).allocator_cache_4k_lock_map().dom() =~= set![(allocator_ptr, cpu_id)],
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        container_lock_perm.state() is WriteLock,
        container_lock_perm.thread_id() == old(lctx).thread_id(),
        container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        process_lock_perm.state() is WriteLock,
        process_lock_perm.thread_id() == old(lctx).thread_id(),
        process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(thread_ptr), TypedLockMode::Write),
        page_lock_perm.state() is WriteLock,
        page_lock_perm.thread_id() == old(lctx).thread_id(),
        page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_ptr)).view().locking_thread()->Write_lock_id,
        typed_lock_map_majors_lt(old(lctx).page_lock_map(), QUOTA_4K_MAJOR),
        typed_lock_map_contains_mode(old(lctx).allocator_cache_4k_lock_map(), (allocator_ptr, cpu_id), TypedLockMode::Write),
        cache_lock_perm.state() is WriteLock,
        cache_lock_perm.thread_id() == old(lctx).thread_id(),
        cache_lock_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        pcid_allocator_ptr == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator,
        old(lctx).pcid_allocator_lock_map().dom() =~= if old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().len() == 1 { set![pcid_allocator_ptr] } else { Set::empty() },
        old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().len() == 1 ==> {
            &&& typed_lock_map_contains_mode(old(lctx).pcid_allocator_lock_map(), pcid_allocator_ptr, TypedLockMode::Write)
            &&& pcid_allocator_lock_perm is Some
            &&& pcid_allocator_lock_perm->Some_0.state() is WriteLock
            &&& pcid_allocator_lock_perm->Some_0.thread_id() == old(lctx).thread_id()
            &&& pcid_allocator_lock_perm->Some_0.lock_id() == old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).locking_thread()->Write_lock_id
        },
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
        !old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        !old(krnl).prc_mp.spec_index(process_ptr).being_killed(),
        !old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().caller is None,
        old(krnl).thr_mp.spec_index(thread_ptr).view().callee is None,
        forall|j: int| #![trigger old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[j]]
            0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==> old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[j] is None,
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        if old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().len() == 1 {
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitZombie)
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k == 0
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().quota_2m == 0
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().quota_1g == 0
            &&& old(krnl).prc_mp.spec_index(process_ptr).view().quota_4k == 0
            &&& old(krnl).prc_mp.spec_index(process_ptr).view().quota_2m == 0
            &&& old(krnl).prc_mp.spec_index(process_ptr).view().quota_1g == 0
            &&& old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is TablesEmptied
        } else {
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() matches Some(SyscallProgress::ThreadExit { .. })
            &&& old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Running
        },
        old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_ptr)).view().view().owning_container == owner,
        old(krnl).ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        old(krnl).allc_4k_mp.dom().contains(allocator_ptr),
        old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().len() < ALLOCATOR_MAX_WATERMARK,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        thread_exit_syscall_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, kernel_k_to_kernel_u(*final(krnl)), cpu_id, true),
{
    proof { assert(typed_lock_map_majors_lt(lctx.cpu_lock_map(), CPU_LOCK_MAJOR_OFF)) by { krnl.cpu_arr.typed_lock_map_aligned_lock_id_at(lctx.cpu_lock_map(), lctx.thread_id(), cpu_id); }; }
    let Tracked(quota_lock_perm) = krnl.wlock_allocator_quota_4k(allocator_ptr, Tracked(&mut *lctx));
    let Tracked(needflush_lock_perm) = krnl.wlock_pcid_needflush(cpu_id, KERNEL_DEFAULT_PCID, Tracked(&mut *lctx));
    let ghost finish_k = steps.snapshot_k();
    let ghost finish_before = steps.view();
    let ghost flushed = krnl.pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).view().needflush;
    proof { assert(kernel_container_nonlock_fields_and_quotas_unchanged(&finish_k, &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; }; }
    thread_exit_destroy(krnl, Tracked(&mut *lctx), Ghost(finish_k), cpu_id, container_ptr, process_ptr, thread_ptr, owner, allocator_ptr, pcid_allocator_ptr,
        Tracked(cpu_lock_perm), Tracked(container_lock_perm), Tracked(process_lock_perm), Tracked(thread_lock_perm), Tracked(page_lock_perm), Tracked(cache_lock_perm),
        Tracked(quota_lock_perm), Tracked(needflush_lock_perm), Tracked(pcid_allocator_lock_perm));
    proof {
        steps.end_kernel_step_thread_exit(&*krnl, &*lctx, cpu_id, thread_ptr, flushed);
        assert(thread_exit_syscall_trace(steps.view().subrange(start, steps.view().len() as int), pre, kernel_k_to_kernel_u(*krnl), cpu_id, true)) by {
            thread_exit_finish_step_pre_from_k(&finish_k, &finish_lctx, cpu_id, container_ptr, process_ptr, thread_ptr);
            kernel_thread_exit_fields_and_unlocks_implies_u_step(&finish_k, &*krnl, cpu_id, container_ptr, process_ptr, thread_ptr, flushed);
            thread_exit_finish_step_from_u(kernel_k_to_kernel_u(finish_k), kernel_k_to_kernel_u(*krnl), cpu_id, container_ptr, process_ptr, thread_ptr, flushed);
            thread_exit_trace_finish_step(&*steps, finish_before, start, pre, kernel_k_to_kernel_u(finish_k), kernel_k_to_kernel_u(*krnl), cpu_id);
        };
    }
}
} // verus!
