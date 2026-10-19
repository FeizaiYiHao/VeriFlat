use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_thread_exit_destroy_spec::thread_exit_destroy_eof_transition_framing;
#[cfg(verus_keep_ghost)]
use super::syscall_thread_exit_destroy_eof::thread_exit_destroy_eof;

verus! {
/// Destroy the running exiting thread while every lock of the finish step is held: `cpu_id` goes idle on the default
/// page table, the process drops the thread and absorbs its quotas, a zombie releases its PCID to the container's PCID
/// allocator `pcid_allocator_ptr`, a zombie root process makes the container a zombie, the containers drop the thread,
/// and the thread's page returns to shard `cpu_id` of the 4K allocator `allocator_ptr` of its owner `owner`, whose quota
/// grows by one. Returns whether the process became a zombie.
pub(super) fn thread_exit_destroy_remove_thread(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr,
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
        page_ptr_valid(thread_ptr),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).prc_mp.dom().contains(process_ptr),
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
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        thread_exit_destroy_eof_transition_framing(*old(krnl), *final(krnl), cpu_id, container_ptr, process_ptr, thread_ptr, owner, allocator_ptr,
            old(krnl).thr_mp.spec_index(thread_ptr).view().proc_linkedlist_node.addr(), old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_ptr)).view().view().free_list_node_storage.addr()),
        zombie == (old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().len() == 1),
        final(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        final(lctx).container_lock_map().dom() =~= set![container_ptr],
        final(lctx).process_lock_map().dom() =~= set![process_ptr],
        final(lctx).thread_lock_map().dom().is_empty(),
        final(lctx).page_lock_map().dom() =~= set![page_ptr2page_index(thread_ptr)],
        final(lctx).allocator_cache_4k_lock_map().dom() =~= set![(allocator_ptr, cpu_id)],
        final(lctx).allocator_quota_4k_lock_map().dom() =~= set![allocator_ptr],
        final(lctx).pcid_needflush_lock_map().dom() =~= set![(cpu_id, KERNEL_DEFAULT_PCID)],
        final(lctx).pcid_allocator_lock_map().dom() =~= if zombie { set![pcid_allocator_ptr] } else { Set::empty() },
        final(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        final(lctx).endpoint_lock_map().dom().is_empty(),
        final(lctx).scheduler_lock_map().dom().is_empty(),
        final(lctx).cpu_set_lock_map().dom().is_empty(),
        final(lctx).pagetable_lock_map().dom().is_empty(),
        final(lctx).iommu_table_lock_map().dom().is_empty(),
        final(lctx).iommu_root_table_lock_map().dom().is_empty(),
        final(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        final(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        final(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(thread_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).allocator_cache_4k_lock_map(), (allocator_ptr, cpu_id), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).allocator_quota_4k_lock_map(), allocator_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).pcid_needflush_lock_map(), (cpu_id, KERNEL_DEFAULT_PCID), TypedLockMode::Write),
        zombie ==> typed_lock_map_contains_mode(final(lctx).pcid_allocator_lock_map(), pcid_allocator_ptr, TypedLockMode::Write),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
        !final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == KERNEL_DEFAULT_PCID,
        final(krnl).cpu_published[cpu_id as int].view() == (final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, KERNEL_DEFAULT_PCID),
        final(krnl).pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).locking_thread() == old(krnl).pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).locking_thread(),
        final(krnl).ctn_mp.dom() == old(krnl).ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(c)] old(krnl).ctn_mp.dom().contains(c) ==> final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread(),
        !final(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(process_ptr),
        final(krnl).prc_mp.dom() == old(krnl).prc_mp.dom(),
        final(krnl).prc_mp.spec_index(process_ptr).locking_thread() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread(),
        !final(krnl).prc_mp.spec_index(process_ptr).being_killed(),
        final(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Running || final(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Zombie,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(thread_ptr)).view().locking_thread() == old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_ptr)).view().locking_thread(),
        final(krnl).allc_4k_mp.dom().contains(allocator_ptr),
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread(),
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.locking_thread() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.locking_thread(),
        zombie ==> final(krnl).pcid_allc_mp.dom().contains(pcid_allocator_ptr),
        zombie ==> final(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).locking_thread() == old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).locking_thread(),
        old(krnl).prc_mp.spec_index(process_ptr).view().quota_4k + old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k <= usize::MAX,
        old(krnl).prc_mp.spec_index(process_ptr).view().quota_2m + old(krnl).thr_mp.spec_index(thread_ptr).view().quota_2m <= usize::MAX,
        old(krnl).prc_mp.spec_index(process_ptr).view().quota_1g + old(krnl).thr_mp.spec_index(thread_ptr).view().quota_1g <= usize::MAX,
        old(krnl).ctn_mp.dom().contains(owner),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsThread }),
        old(krnl).allc_4k_mp.dom().contains(allocator_ptr),
        old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().contains(thread_ptr),
        old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.map().dom().contains(old(krnl).thr_mp.spec_index(thread_ptr).view().proc_linkedlist_node.addr()),
        old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.map().spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().proc_linkedlist_node.addr()) == thread_ptr,
        !old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_ptr)).view().view().free_list_node_storage.addr()),
        old(krnl).pcid_allc_mp.dom().contains(pcid_allocator_ptr),
{
    let page_index = page_ptr2page_index(thread_ptr);
    let ghost uppers = krnl.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view();
    let ghost proc_node_addr = krnl.thr_mp.spec_index(thread_ptr).view().proc_linkedlist_node.addr();
    proof {
        thread_perms_wf_map(krnl.thr_mp);
        thread_perms_wf_at(krnl.thr_mp, thread_ptr);
        process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, thread_ptr);
        process_perms_wf_map(krnl.prc_mp);
        process_perms_wf_at(krnl.prc_mp, process_ptr);
        container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, thread_ptr);
        container_perms_wf_map(krnl.ctn_mp);
        container_perms_wf_at(krnl.ctn_mp, container_ptr);
        assert(krnl.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(process_ptr)) by { container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, process_ptr); };
        container_process_thread_quota_sums_bounded(&*krnl, container_ptr, process_ptr, thread_ptr);
        assert(page_ptr_valid(thread_ptr) && krnl.pg_arr.spec_index(page_index).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsThread })) by { thread_pages_wf_at(krnl.thr_mp, krnl.pg_arr, thread_ptr); };
        page_array_wf_at(krnl.pg_arr, page_index);
        assert(krnl.ctn_mp.dom().contains(owner)) by { container_page_owner_backward_at(krnl.ctn_mp, krnl.pg_arr, page_index); };
        lemma_container_allocator_4k_quota_bounded(&*krnl, owner);
        allocator_perms_wf_map(krnl.allc_4k_mp); allocator_perms_wf_at(krnl.allc_4k_mp, allocator_ptr);
        assert(!krnl.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().contains(thread_ptr)) by { container_allocator_free_4k_page_wf_cache_at(krnl.allc_4k_mp, krnl.pg_arr, allocator_ptr, cpu_id, thread_ptr); };
        assert(uppers.to_set().subset_of(krnl.ctn_mp.dom()) && !uppers.to_set().contains(container_ptr)) by {
            uppers.to_set_ensures(); container_uppertree_seq_in_dom(krnl.rt_ctn, krnl.ctn_mp, container_ptr); container_uppertree_seq_not_self(krnl.rt_ctn, krnl.ctn_mp, container_ptr);
        };
        assert(krnl.prc_mp.spec_index(process_ptr).view().owned_threads.dom().contains(proc_node_addr)) by { reveal(LinkedList::wf_map); };
        assert(krnl.cpu_arr.inv() && krnl.cpu_arr.spec_index(cpu_id).view().is_init() && krnl.cpu_arr.spec_index(cpu_id).view().view().wf()) by { cpu_array_wf_map(krnl.cpu_arr, krnl.dflt_pt.view()); cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), cpu_id); };
        assert(krnl.cpu_published[cpu_id as int].owner_cpu() == cpu_id) by { cpu_published_wf_at(krnl.cpu_published, krnl.cpu_arr, krnl.pcid_needflush, cpu_id); };
        assert(krnl.pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).inv()) by { pcid_needflush_wf_at(krnl.pcid_needflush, cpu_id, KERNEL_DEFAULT_PCID); };
        assert(krnl.pcid_allc_mp.dom().contains(pcid_allocator_ptr)) by { container_pcid_allocator_wf_container_at(krnl.ctn_mp, krnl.pcid_allc_mp, container_ptr); };
        assert({
            &&& krnl.prc_mp.spec_index(process_ptr).view_rodata().view().pcid == krnl.prc_mp.spec_index(process_ptr).view().pcid
            &&& pcid_valid(krnl.prc_mp.spec_index(process_ptr).view().pcid)
            &&& !krnl.prc_mp.spec_index(process_ptr).view().zombie
            &&& krnl.pcid_allc_mp.spec_index(pcid_allocator_ptr).view().id_to_proc.view().spec_index(krnl.prc_mp.spec_index(process_ptr).view().pcid as int).contains(process_ptr)
        }) by { process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, process_ptr); process_pcid_allocator_wf_process_at(krnl.ctn_mp, krnl.prc_mp, krnl.pcid_allc_mp, process_ptr); };
    }
    let pcid = krnl.prc_mp.borrow_rodata(process_ptr).borrow().pcid;
    let root_process = krnl.ctn_mp.borrow_typed(container_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(container_lock_perm)).root_process;
    let default_cr3 = krnl.dflt_pt.borrow().cr3;
    assert(page_ptr_valid(default_cr3)) by { krnl.default_pagetable_view_inv(); };
    let ghost old_cpu_lock_id = krnl.cpu_arr.lock_id_by_index(cpu_id);
    krnl.cpu_arr.block_current(cpu_id, default_cr3, &mut krnl.cpu_tlb, &mut krnl.pcid_needflush, &mut krnl.cpu_published, Tracked(needflush_lock_perm), Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof { lctx.update_lock_id(KernelObjId::Cpu(cpu_id), old_cpu_lock_id, krnl.cpu_arr.lock_id_by_index(cpu_id)); }
    let (proc_node, quota_4k, quota_2m, quota_1g) = {
        let thread = krnl.thr_mp.borrow_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&thread_lock_perm));
        (thread.proc_linkedlist_node.addr(), thread.quota_4k, thread.quota_2m, thread.quota_1g)
    };
    let (proc_node_perm, zombie) = {
        let process = krnl.prc_mp.borrow_mut_typed(process_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(process_lock_perm));
        let node_perm = process.remove_exiting_thread(proc_node, quota_4k, quota_2m, quota_1g);
        (node_perm, process.zombie)
    };
    proof {
        remove_thread_from_container_sets(&mut krnl.ctn_mp, container_ptr, thread_ptr, uppers, lctx.container_lock_map(), lctx.thread_id());
        container_perms_wf_at(krnl.ctn_mp, container_ptr);
        old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().index_of_first_ensures(thread_ptr);
    }
    if zombie {
        let tracked pcid_allocator_lock_perm = pcid_allocator_lock_perm.tracked_borrow();
        pcid_allocator_map_release(&mut krnl.pcid_allc_mp, pcid_allocator_ptr, process_ptr, pcid, Tracked(&*lctx), Tracked(pcid_allocator_lock_perm));
    }
    if zombie && root_process == process_ptr {
        let container = krnl.ctn_mp.borrow_mut_typed(container_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(container_lock_perm));
        container.zombie = true;
    }
    let Tracked(page_perm) = krnl.remove_thread_and_reclaim_4k_page_perm(thread_ptr, proc_node_perm, Tracked(thread_lock_perm), Tracked(&mut *lctx));
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
    let (cache_node_addr, cache_node_perm) = page_array_retire_kernel_object_4k_to_cache(&mut krnl.pg_arr, page_index, Tracked(page_perm), allocator_ptr, cpu_id, Tracked(&*lctx), Tracked(page_lock_perm));
    proof { lctx.update_lock_id(KernelObjId::Page(page_index), old_page_lock_id, krnl.pg_arr.lock_id_by_index(page_index)); }
    krnl.allc_4k_mp.push_cache_page_typed(allocator_ptr, cpu_id, cache_node_addr, cache_node_perm, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
        Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(cache_lock_perm));
    {
        let quota = krnl.allc_4k_mp.borrow_mut_quota_typed(allocator_ptr, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
            Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(quota_lock_perm));
        quota.value = quota.value + 1;
    }
    proof {
        assert(thread_exit_destroy_eof_transition_framing(*old(krnl), *krnl, cpu_id, container_ptr, process_ptr, thread_ptr, owner, allocator_ptr, proc_node_addr, cache_node_addr)) by { reveal(thread_exit_destroy_eof_transition_framing); };
        old(krnl).thr_mp.typed_lock_map_aligned_write_at(old(lctx).thread_lock_map(), old(lctx).thread_id(), thread_ptr);
        reveal(LockedMap::typed_lock_map_aligned);
        thread_exit_destroy_eof(*old(krnl), *krnl, cpu_id, container_ptr, process_ptr, thread_ptr, owner, allocator_ptr, proc_node_addr, cache_node_addr);
    }
    zombie
}
} // verus!
