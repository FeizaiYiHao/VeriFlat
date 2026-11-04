use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_thread_exit_destroy_spec::thread_exit_destroy_eof_transition_framing;
#[cfg(verus_keep_ghost)]
use super::syscall_thread_exit_destroy_eof::thread_exit_destroy_eof;

verus! {
/// Destroy the running exiting thread while every lock of the finish step is held: `cpu_id` goes idle on the default
/// page table, the process drops the thread and absorbs its quotas, a zombie releases its PCID to the container's PCID
/// allocator `pcid_allc_ptr`, a zombie root process makes the container a zombie, the containers drop the thread,
/// and the thread's page returns to shard `cpu_id` of the 4K allocator `allc_ptr` of its owner `owner`, whose quota
/// grows by one. Returns whether the process became a zombie.
pub(super) fn thread_exit_destroy_remove_thread(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, ctn_ptr: RwLockContainerPtr, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, allc_ptr: RwLockPageAllocatorPtr, pcid_allc_ptr: RwLockPcidAllocatorPtr,
    Tracked(cpu_lock_perm): Tracked<&LockPerm>, Tracked(container_lock_perm): Tracked<&LockPerm>, Tracked(process_lock_perm): Tracked<&LockPerm>,
    Tracked(thread_lock_perm): Tracked<LockPerm>, Tracked(page_lock_perm): Tracked<&LockPerm>, Tracked(cache_lock_perm): Tracked<&LockPerm>,
    Tracked(quota_lock_perm): Tracked<&LockPerm>, Tracked(needflush_lock_perm): Tracked<&LockPerm>, Tracked(pcid_allocator_lock_perm): Tracked<&Option<LockPerm>>,
) -> (zombie: bool)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        page_ptr_valid(thrd_ptr),
        old(krnl).ctn_mp.dom().contains(ctn_ptr),
        old(krnl).prc_mp.dom().contains(prc_ptr),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom() =~= set![ctn_ptr],
        old(lctx).process_lock_map().dom() =~= set![prc_ptr],
        old(lctx).thread_lock_map().dom() =~= set![thrd_ptr],
        old(lctx).page_lock_map().dom() =~= set![page_ptr2page_index(thrd_ptr)],
        old(lctx).allocator_cache_4k_lock_map().dom() =~= set![(allc_ptr, cpu_id)],
        old(lctx).allocator_quota_4k_lock_map().dom() =~= set![allc_ptr],
        old(lctx).pcid_needflush_lock_map().dom() =~= set![(cpu_id, KERNEL_DEFAULT_PCID)],
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom() =~= if old(krnl).prc_mp.spec_index(prc_ptr).view().owned_threads.view().len() == 1 { set![pcid_allc_ptr] } else { Set::empty() },
        old(krnl).prc_mp.spec_index(prc_ptr).view().owned_threads.view().len() == 1 ==> old(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is TablesEmptied,
        old(krnl).prc_mp.spec_index(prc_ptr).view().owned_threads.view().len() != 1 ==> old(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is Running,
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
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), ctn_ptr, TypedLockMode::Write),
        container_lock_perm.state() is WriteLock,
        container_lock_perm.thread_id() == old(lctx).thread_id(),
        container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(ctn_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), prc_ptr, TypedLockMode::Write),
        process_lock_perm.state() is WriteLock,
        process_lock_perm.thread_id() == old(lctx).thread_id(),
        process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(prc_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        progress_peer_of(old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()) is None,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(thrd_ptr), TypedLockMode::Write),
        page_lock_perm.state() is WriteLock,
        page_lock_perm.thread_id() == old(lctx).thread_id(),
        page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(thrd_ptr)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).allocator_cache_4k_lock_map(), (allc_ptr, cpu_id), TypedLockMode::Write),
        cache_lock_perm.state() is WriteLock,
        cache_lock_perm.thread_id() == old(lctx).thread_id(),
        cache_lock_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).allocator_quota_4k_lock_map(), allc_ptr, TypedLockMode::Write),
        quota_lock_perm.state() is WriteLock,
        quota_lock_perm.thread_id() == old(lctx).thread_id(),
        quota_lock_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allc_ptr).quota.locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).pcid_needflush_lock_map(), (cpu_id, KERNEL_DEFAULT_PCID), TypedLockMode::Write),
        needflush_lock_perm.state() is WriteLock,
        needflush_lock_perm.thread_id() == old(lctx).thread_id(),
        needflush_lock_perm.lock_id() == old(krnl).pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).locking_thread()->Write_lock_id,
        pcid_allc_ptr == old(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata().view().pcid_allocator,
        old(krnl).prc_mp.spec_index(prc_ptr).view().owned_threads.view().len() == 1 ==> {
            &&& old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_4k == 0
            &&& old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_2m == 0
            &&& old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_1g == 0
            &&& old(krnl).prc_mp.spec_index(prc_ptr).view().quota_4k == 0
            &&& old(krnl).prc_mp.spec_index(prc_ptr).view().quota_2m == 0
            &&& old(krnl).prc_mp.spec_index(prc_ptr).view().quota_1g == 0
        },
        old(krnl).prc_mp.spec_index(prc_ptr).view().owned_threads.view().len() == 1 ==> {
            &&& typed_lock_map_contains_mode(old(lctx).pcid_allocator_lock_map(), pcid_allc_ptr, TypedLockMode::Write)
            &&& pcid_allocator_lock_perm is Some
            &&& pcid_allocator_lock_perm->Some_0.state() is WriteLock
            &&& pcid_allocator_lock_perm->Some_0.thread_id() == old(lctx).thread_id()
            &&& pcid_allocator_lock_perm->Some_0.lock_id() == old(krnl).pcid_allc_mp.spec_index(pcid_allc_ptr).locking_thread()->Write_lock_id
        },
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        !old(krnl).ctn_mp.spec_index(ctn_ptr).being_killed(),
        !old(krnl).prc_mp.spec_index(prc_ptr).being_killed(),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().caller is None,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().callee is None,
        forall|j: int| #![trigger old(krnl).thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors.view().spec_index(j)]
            0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==> old(krnl).thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors.view().spec_index(j) is None,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(thrd_ptr)).view().view().owning_container == owner,
        old(krnl).ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allc_ptr,
        old(krnl).allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().len() < ALLOCATOR_MAX_WATERMARK,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(krnl).cpu_op == old(krnl).cpu_op,
        thread_exit_destroy_eof_transition_framing(*old(krnl), *final(krnl), cpu_id, ctn_ptr, prc_ptr, thrd_ptr, owner, allc_ptr,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_linkedlist_node.addr(), old(krnl).pg_arr.spec_index(page_ptr2page_index(thrd_ptr)).view().view().free_list_node_storage.addr()),
        zombie == (old(krnl).prc_mp.spec_index(prc_ptr).view().owned_threads.view().len() == 1),
        final(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        final(lctx).container_lock_map().dom() =~= set![ctn_ptr],
        final(lctx).process_lock_map().dom() =~= set![prc_ptr],
        final(lctx).thread_lock_map().dom().is_empty(),
        final(lctx).page_lock_map().dom() =~= set![page_ptr2page_index(thrd_ptr)],
        final(lctx).allocator_cache_4k_lock_map().dom() =~= set![(allc_ptr, cpu_id)],
        final(lctx).allocator_quota_4k_lock_map().dom() =~= set![allc_ptr],
        final(lctx).pcid_needflush_lock_map().dom() =~= set![(cpu_id, KERNEL_DEFAULT_PCID)],
        final(lctx).pcid_allocator_lock_map().dom() =~= if zombie { set![pcid_allc_ptr] } else { Set::empty() },
        final(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        final(lctx).endpoint_lock_map().dom().is_empty(),
        final(lctx).scheduler_lock_map().dom().is_empty(),
        final(lctx).cpu_set_lock_map().dom().is_empty(),
        final(lctx).pagetable_lock_map().dom().is_empty(),
        final(lctx).pagetable_window_lock_map().dom().is_empty(),
        final(lctx).iommu_table_lock_map().dom().is_empty(),
        final(lctx).iommu_root_table_lock_map().dom().is_empty(),
        final(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        final(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        final(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), ctn_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), prc_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(thrd_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).allocator_cache_4k_lock_map(), (allc_ptr, cpu_id), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).allocator_quota_4k_lock_map(), allc_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).pcid_needflush_lock_map(), (cpu_id, KERNEL_DEFAULT_PCID), TypedLockMode::Write),
        zombie ==> typed_lock_map_contains_mode(final(lctx).pcid_allocator_lock_map(), pcid_allc_ptr, TypedLockMode::Write),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
        !final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == KERNEL_DEFAULT_PCID,
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, KERNEL_DEFAULT_PCID),
        final(krnl).pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).locking_thread() == old(krnl).pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).locking_thread(),
        final(krnl).ctn_mp.dom() == old(krnl).ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(c)] old(krnl).ctn_mp.dom().contains(c)
            ==> final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread() && final(krnl).ctn_mp.spec_index(c).lock_process_owner_u() == old(krnl).ctn_mp.spec_index(c).lock_process_owner_u(),
        !final(krnl).ctn_mp.spec_index(ctn_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view().contains(prc_ptr),
        final(krnl).prc_mp.dom() == old(krnl).prc_mp.dom(),
        final(krnl).prc_mp.spec_index(prc_ptr).locking_thread() == old(krnl).prc_mp.spec_index(prc_ptr).locking_thread(),
        !final(krnl).prc_mp.spec_index(prc_ptr).being_killed(),
        final(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is Running || final(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is Zombie,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(thrd_ptr)).view().locking_thread() == old(krnl).pg_arr.spec_index(page_ptr2page_index(thrd_ptr)).view().locking_thread(),
        final(krnl).allc_4k_mp.dom().contains(allc_ptr),
        final(krnl).allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread() == old(krnl).allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread(),
        final(krnl).allc_4k_mp.spec_index(allc_ptr).quota.locking_thread() == old(krnl).allc_4k_mp.spec_index(allc_ptr).quota.locking_thread(),
        zombie ==> final(krnl).pcid_allc_mp.dom().contains(pcid_allc_ptr),
        zombie ==> final(krnl).pcid_allc_mp.spec_index(pcid_allc_ptr).locking_thread() == old(krnl).pcid_allc_mp.spec_index(pcid_allc_ptr).locking_thread(),
        old(krnl).prc_mp.spec_index(prc_ptr).view().quota_4k + old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_4k <= usize::MAX,
        old(krnl).prc_mp.spec_index(prc_ptr).view().quota_2m + old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_2m <= usize::MAX,
        old(krnl).prc_mp.spec_index(prc_ptr).view().quota_1g + old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_1g <= usize::MAX,
        old(krnl).ctn_mp.dom().contains(owner),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(thrd_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsThread }),
        old(krnl).allc_4k_mp.dom().contains(allc_ptr),
        old(krnl).prc_mp.spec_index(prc_ptr).view().owned_threads.view().contains(thrd_ptr),
        old(krnl).prc_mp.spec_index(prc_ptr).view().owned_threads.map().dom().contains(old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_linkedlist_node.addr()),
        old(krnl).prc_mp.spec_index(prc_ptr).view().owned_threads.map().spec_index(old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_linkedlist_node.addr()) == thrd_ptr,
        !old(krnl).allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(old(krnl).pg_arr.spec_index(page_ptr2page_index(thrd_ptr)).view().view().free_list_node_storage.addr()),
        old(krnl).pcid_allc_mp.dom().contains(pcid_allc_ptr),
{
    hide(Set::is_empty);
    let pg_idx = page_ptr2page_index(thrd_ptr);
    let ghost uppers = krnl.ctn_mp.spec_index(ctn_ptr).view_ghost().uppertree_seq.view();
    let ghost proc_node_addr = krnl.thrd_mp.spec_index(thrd_ptr).view().proc_linkedlist_node.addr();
    proof {
        thread_perms_wf_map(krnl.thrd_mp);
        thread_perms_wf_at(krnl.thrd_mp, thrd_ptr);
        process_thread_wf_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr);
        process_perms_wf_map(krnl.prc_mp);
        process_perms_wf_at(krnl.prc_mp, prc_ptr);
        container_thread_wf_at(krnl.ctn_mp, krnl.thrd_mp, thrd_ptr);
        container_perms_wf_map(krnl.ctn_mp);
        container_perms_wf_at(krnl.ctn_mp, ctn_ptr);
        assert(krnl.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view().contains(prc_ptr)) by { container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, prc_ptr); };
        container_process_thread_quota_sums_bounded(&*krnl, ctn_ptr, prc_ptr, thrd_ptr);
        assert(page_ptr_valid(thrd_ptr) && krnl.pg_arr.spec_index(pg_idx).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsThread })) by { thread_pages_wf_at(krnl.thrd_mp, krnl.pg_arr, thrd_ptr); };
        page_array_wf_at(krnl.pg_arr, pg_idx);
        assert(krnl.ctn_mp.dom().contains(owner)) by { container_page_owner_backward_at(krnl.ctn_mp, krnl.pg_arr, pg_idx); };
        lemma_container_allocator_4k_quota_bounded(&*krnl, owner);
        allocator_perms_wf_map(krnl.allc_4k_mp); allocator_perms_wf_at(krnl.allc_4k_mp, allc_ptr);
        assert(!krnl.allc_4k_mp.spec_index(allc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().contains(thrd_ptr)) by { container_allocator_free_4k_page_wf_cache_at(krnl.allc_4k_mp, krnl.pg_arr, allc_ptr, cpu_id, thrd_ptr); };
        assert(uppers.to_set().subset_of(krnl.ctn_mp.dom()) && !uppers.to_set().contains(ctn_ptr)) by {
            uppers.to_set_ensures(); container_uppertree_seq_in_dom(krnl.rt_ctn, krnl.ctn_mp, ctn_ptr); container_uppertree_seq_not_self(krnl.rt_ctn, krnl.ctn_mp, ctn_ptr);
        };
        assert(krnl.prc_mp.spec_index(prc_ptr).view().owned_threads.dom().contains(proc_node_addr)) by { krnl.prc_mp.spec_index(prc_ptr).view().owned_threads.wf_map_at(proc_node_addr); };
        assert(krnl.cpu_arr.inv() && krnl.cpu_arr.spec_index(cpu_id).view().is_init() && krnl.cpu_arr.spec_index(cpu_id).view().view().wf()) by { cpu_array_wf_map(krnl.cpu_arr, krnl.dflt_pt.view()); cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), cpu_id); };
        assert(krnl.cpu_hw_cr3_pcid[cpu_id as int].owner_cpu() == cpu_id) by { cpu_hw_cr3_pcid_wf_at(krnl.cpu_hw_cr3_pcid, krnl.cpu_arr, krnl.pcid_needflush, cpu_id); };
        assert(krnl.pcid_needflush.inv() && krnl.pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).inv()) by { pcid_needflush_wf_implies_array_inv(krnl.pcid_needflush); pcid_needflush_wf_at(krnl.pcid_needflush, cpu_id, KERNEL_DEFAULT_PCID); };
        assert(krnl.pcid_allc_mp.dom().contains(pcid_allc_ptr)) by { container_pcid_allocator_wf_container_at(krnl.ctn_mp, krnl.pcid_allc_mp, ctn_ptr); };
        assert({
            &&& krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().pcid == krnl.prc_mp.spec_index(prc_ptr).view().pcid
            &&& pcid_valid(krnl.prc_mp.spec_index(prc_ptr).view().pcid)
            &&& !krnl.prc_mp.spec_index(prc_ptr).view().zombie
            &&& krnl.pcid_allc_mp.spec_index(pcid_allc_ptr).view().id_to_proc.view().spec_index(krnl.prc_mp.spec_index(prc_ptr).view().pcid as int).contains(prc_ptr)
        }) by { process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr); process_pcid_allocator_wf_process_at(krnl.ctn_mp, krnl.prc_mp, krnl.pcid_allc_mp, prc_ptr); };
    }
    let pcid = krnl.prc_mp.borrow_rodata(prc_ptr).borrow().pcid;
    let root_process = krnl.ctn_mp.borrow_typed(ctn_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(container_lock_perm)).root_process;
    let default_cr3 = krnl.dflt_pt.borrow().cr3;
    assert(page_ptr_valid(default_cr3)) by { krnl.default_pagetable_view_inv(); };
    let ghost old_cpu_lock_id = krnl.cpu_arr.lock_id_by_index(cpu_id);
    krnl.cpu_arr.block_current(cpu_id, default_cr3, &mut krnl.cpu_tlb, &mut krnl.pcid_needflush, &mut krnl.cpu_hw_cr3_pcid, Tracked(needflush_lock_perm), Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof { lctx.update_lock_id(KernelObjId::Cpu(cpu_id), old_cpu_lock_id, krnl.cpu_arr.lock_id_by_index(cpu_id)); }
    let (proc_node, quota_4k, quota_2m, quota_1g) = {
        let thread = krnl.thrd_mp.borrow_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&thread_lock_perm));
        (thread.proc_linkedlist_node.addr(), thread.quota_4k, thread.quota_2m, thread.quota_1g)
    };
    let (proc_node_perm, zombie) = {
        let process = krnl.prc_mp.borrow_mut_typed(prc_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(process_lock_perm));
        let node_perm = process.remove_exiting_thread(proc_node, quota_4k, quota_2m, quota_1g);
        (node_perm, process.zombie)
    };
    proof {
        remove_thread_from_container_sets(&mut krnl.ctn_mp, ctn_ptr, thrd_ptr, uppers, lctx.container_lock_map(), lctx.thread_id());
        container_perms_wf_at(krnl.ctn_mp, ctn_ptr);
        old(krnl).prc_mp.spec_index(prc_ptr).view().owned_threads.view().index_of_first_ensures(thrd_ptr);
    }
    if zombie {
        let tracked pcid_allocator_lock_perm = pcid_allocator_lock_perm.tracked_borrow();
        pcid_allocator_map_release(&mut krnl.pcid_allc_mp, pcid_allc_ptr, prc_ptr, pcid, Tracked(&*lctx), Tracked(pcid_allocator_lock_perm));
    }
    if zombie && root_process == prc_ptr {
        let container = krnl.ctn_mp.borrow_mut_typed(ctn_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(container_lock_perm));
        container.zombie = true;
    }
    let Tracked(page_perm) = krnl.remove_thread_and_reclaim_4k_page_perm(thrd_ptr, proc_node_perm, Tracked(thread_lock_perm), Tracked(&mut *lctx));
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(pg_idx);
    let (cache_node_addr, cache_node_perm) = page_array_retire_kernel_object_4k_to_cache(&mut krnl.pg_arr, pg_idx, Tracked(page_perm), allc_ptr, cpu_id, Tracked(&*lctx), Tracked(page_lock_perm));
    proof { lctx.update_lock_id(KernelObjId::Page(pg_idx), old_page_lock_id, krnl.pg_arr.lock_id_by_index(pg_idx)); }
    krnl.allc_4k_mp.push_cache_page_typed(allc_ptr, cpu_id, cache_node_addr, cache_node_perm, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
        Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(cache_lock_perm));
    {
        let quota = krnl.allc_4k_mp.borrow_mut_quota_typed(allc_ptr, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
            Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(quota_lock_perm));
        quota.value = quota.value + 1;
    }
    proof {
        assert(thread_exit_destroy_eof_transition_framing(*old(krnl), *krnl, cpu_id, ctn_ptr, prc_ptr, thrd_ptr, owner, allc_ptr, proc_node_addr, cache_node_addr)) by { reveal(thread_exit_destroy_eof_transition_framing); };
        assert(krnl.inv()) by {
            reveal(LockedMap::typed_lock_map_aligned);
            thread_exit_destroy_eof(*old(krnl), *krnl, cpu_id, ctn_ptr, prc_ptr, thrd_ptr, owner, allc_ptr, proc_node_addr, cache_node_addr);
        };
    }
    zombie
}
} // verus!
