use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_thread_exit_destroy_eof::thread_exit_destroy_eof_fields;
use super::syscall_thread_exit_destroy_helpers::thread_exit_destroy_remove_thread;

verus! {
/// Remove the running exiting thread and release every lock of the finish step: `cpu_id` goes idle on the default page
/// table, the process drops the thread and absorbs its quotas, a zombie root process makes the container a zombie, the
/// containers drop the thread, and the thread's page returns to shard `cpu_id` of the 4K allocator of its owner
/// `owner`, whose quota grows by one; a zombie releases its PCID to the write-held PCID allocator `pcid_allocator_ptr`
/// of the container. `start` is the state at the start of the step, before the PCID allocator, page, allocator, and
/// needflush locks were taken.
pub(super) fn thread_exit_destroy(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Ghost(start): Ghost<KernelK>, cpu_id: CpuId, container_ptr: RwLockContainerPtr,
    process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr,
    Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(container_lock_perm): Tracked<LockPerm>, Tracked(process_lock_perm): Tracked<LockPerm>,
    Tracked(thread_lock_perm): Tracked<LockPerm>, Tracked(page_lock_perm): Tracked<LockPerm>, Tracked(cache_lock_perm): Tracked<LockPerm>,
    Tracked(quota_lock_perm): Tracked<LockPerm>, Tracked(needflush_lock_perm): Tracked<LockPerm>, Tracked(pcid_allocator_lock_perm): Tracked<Option<LockPerm>>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        page_ptr_valid(thread_ptr),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).prc_mp.dom().contains(process_ptr),
        *old(krnl) == (KernelK { pg_arr: old(krnl).pg_arr, allc_4k_mp: old(krnl).allc_4k_mp, pcid_needflush: old(krnl).pcid_needflush, pcid_allc_mp: old(krnl).pcid_allc_mp, ..start }),
        kernel_container_nonlock_fields_and_quotas_unchanged(&start, old(krnl)),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom() =~= set![container_ptr],
        old(lctx).process_lock_map().dom() =~= set![process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(lctx).page_lock_map().dom() =~= set![page_ptr2page_index(thread_ptr)],
        old(lctx).allocator_cache_4k_lock_map().dom() =~= set![(allocator_ptr, cpu_id)],
        old(lctx).allocator_quota_4k_lock_map().dom() =~= set![allocator_ptr],
        old(lctx).pcid_needflush_lock_map().dom() =~= set![(cpu_id, KERNEL_DEFAULT_PCID)],
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom() =~= if old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().len() == 1 { set![pcid_allocator_ptr] } else { Set::empty() },
        old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().len() == 1 ==> old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is TablesEmptied,
        old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().len() != 1 ==> old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Running,
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
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
        progress_peer_of(old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()) is None,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(thread_ptr), TypedLockMode::Write),
        page_lock_perm.state() is WriteLock,
        page_lock_perm.thread_id() == old(lctx).thread_id(),
        page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_ptr)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).allocator_cache_4k_lock_map(), (allocator_ptr, cpu_id), TypedLockMode::Write),
        cache_lock_perm.state() is WriteLock,
        cache_lock_perm.thread_id() == old(lctx).thread_id(),
        cache_lock_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).allocator_quota_4k_lock_map(), allocator_ptr, TypedLockMode::Write),
        quota_lock_perm.state() is WriteLock,
        quota_lock_perm.thread_id() == old(lctx).thread_id(),
        quota_lock_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).pcid_needflush_lock_map(), (cpu_id, KERNEL_DEFAULT_PCID), TypedLockMode::Write),
        needflush_lock_perm.state() is WriteLock,
        needflush_lock_perm.thread_id() == old(lctx).thread_id(),
        needflush_lock_perm.lock_id() == old(krnl).pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).locking_thread()->Write_lock_id,
        pcid_allocator_ptr == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator,
        old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().len() == 1 ==> {
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k == 0
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().quota_2m == 0
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().quota_1g == 0
            &&& old(krnl).prc_mp.spec_index(process_ptr).view().quota_4k == 0
            &&& old(krnl).prc_mp.spec_index(process_ptr).view().quota_2m == 0
            &&& old(krnl).prc_mp.spec_index(process_ptr).view().quota_1g == 0
        },
        old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().len() == 1 ==> {
            &&& typed_lock_map_contains_mode(old(lctx).pcid_allocator_lock_map(), pcid_allocator_ptr, TypedLockMode::Write)
            &&& pcid_allocator_lock_perm is Some
            &&& pcid_allocator_lock_perm->Some_0.state() is WriteLock
            &&& pcid_allocator_lock_perm->Some_0.thread_id() == old(lctx).thread_id()
            &&& pcid_allocator_lock_perm->Some_0.lock_id() == old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).locking_thread()->Write_lock_id
        },
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        !old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        !old(krnl).prc_mp.spec_index(process_ptr).being_killed(),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        !old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().caller is None,
        old(krnl).thr_mp.spec_index(thread_ptr).view().callee is None,
        forall|j: int| #![trigger old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view().spec_index(j)]
            0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==> old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view().spec_index(j) is None,
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_ptr)).view().view().owning_container == owner,
        old(krnl).ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().len() < ALLOCATOR_MAX_WATERMARK,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        kernel_thread_exit_fields(&start, final(krnl), cpu_id, thread_ptr, old(krnl).pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).view().needflush),
        final(krnl).cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        forall|c: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(c)]
            start.ctn_mp.dom().contains(c) ==> if c == container_ptr { final(krnl).ctn_mp.spec_index(c).locking_thread() is None }
                else { final(krnl).ctn_mp.spec_index(c).locking_thread() == start.ctn_mp.spec_index(c).locking_thread() },
        final(krnl).prc_mp.spec_index(process_ptr).locking_thread() is None,
{
    let page_index = page_ptr2page_index(thread_ptr);
    let ghost proc_node_addr = krnl.thr_mp.spec_index(thread_ptr).view().proc_linkedlist_node.addr();
    let ghost cache_node_addr = krnl.pg_arr.spec_index(page_index).view().view().free_list_node_storage.addr();
    let zombie = thread_exit_destroy_remove_thread(krnl, Tracked(&mut *lctx), cpu_id, container_ptr, process_ptr, thread_ptr, owner, allocator_ptr, pcid_allocator_ptr,
        Tracked(&cpu_lock_perm), Tracked(&container_lock_perm), Tracked(&process_lock_perm), Tracked(thread_lock_perm), Tracked(&page_lock_perm), Tracked(&cache_lock_perm),
        Tracked(&quota_lock_perm), Tracked(&needflush_lock_perm), Tracked(&pcid_allocator_lock_perm));
    let ghost mid = *krnl;
    if zombie {
        let tracked pcid_allocator_lock_perm = pcid_allocator_lock_perm.tracked_unwrap();
        krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
    }
    krnl.wunlock_pcid_needflush(cpu_id, KERNEL_DEFAULT_PCID, Tracked(&mut *lctx), Tracked(needflush_lock_perm));
    krnl.wunlock_allocator_quota_4k(allocator_ptr, Tracked(&mut *lctx), Tracked(quota_lock_perm));
    krnl.wunlock_allocator_cache_4k(allocator_ptr, cpu_id, Tracked(&mut *lctx), Tracked(cache_lock_perm));
    krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_lock_perm));
    krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
    krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
    krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive;
        thread_exit_destroy_eof_fields(start, *old(krnl), mid, *krnl, cpu_id, container_ptr, process_ptr, thread_ptr, owner, allocator_ptr, proc_node_addr, cache_node_addr);
    }
}
} // verus!
