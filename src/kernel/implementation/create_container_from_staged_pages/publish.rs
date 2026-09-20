use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
pub fn publish_staged_container_root(
    krnl: &mut KernelK,
    parent_container_ptr: RwLockContainerPtr,
    current_thread_ptr: RwLockThreadPtr,
    container_page: PagePtr,
    pcid_allocator_page: PagePtr,
    allocator_4k_page: PagePtr,
    allocator_2m_page: PagePtr,
    allocator_1g_page: PagePtr,
    scheduler_page: PagePtr,
    cpu_set_page: PagePtr,
    process_page: PagePtr,
    pagetable_page: PagePtr,
    l4_page: PagePtr,
    thread_page: PagePtr,
    funding_page_count: usize,
    funding_page_head: PagePtr,
    Ghost(funding_pages): Ghost<Seq<PagePtr>>,
    allocator_quota_4k: usize,
    process_quota_4k: usize,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(parent_container_lock_perm): Tracked<&LockPerm>,
    Tracked(current_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(container_page_lock_perm): Tracked<&LockPerm>,
    Tracked(pcid_allocator_page_lock_perm): Tracked<&LockPerm>,
    Tracked(allocator_4k_page_lock_perm): Tracked<&LockPerm>,
    Tracked(allocator_2m_page_lock_perm): Tracked<&LockPerm>,
    Tracked(allocator_1g_page_lock_perm): Tracked<&LockPerm>,
    Tracked(scheduler_page_lock_perm): Tracked<&LockPerm>,
    Tracked(cpu_set_page_lock_perm): Tracked<&LockPerm>,
    Tracked(process_page_lock_perm): Tracked<&LockPerm>,
    Tracked(pagetable_page_lock_perm): Tracked<&LockPerm>,
    Tracked(l4_page_lock_perm): Tracked<&LockPerm>,
    Tracked(funding_page_lock_perms): Tracked<&Map<PagePtr, LockPerm>>,
    Tracked(container_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
    Tracked(pcid_allocator_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
) -> (ret: (
    Tracked<LockPerm>,
    Tracked<LockPerm>,
    Tracked<LockPerm>,
    Tracked<LockPerm>,
    Tracked<LockPerm>,
))
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        old(krnl).ctn_mp.dom().contains(parent_container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), parent_container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        parent_container_lock_perm.state() is WriteLock,
        parent_container_lock_perm.thread_id() == old(lctx).thread_id(),
        parent_container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.spec_index(parent_container_ptr).view_rodata().view().depth < MAX_CONTAINER_TREE_DEPTH,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == parent_container_ptr,
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 8,
        funding_page_count <= old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k - 8,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_2m >= 2,
        forall|page_ptr: PagePtr|
            #![trigger old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr)]
            #![trigger funding_pages.to_set().contains(page_ptr)]
            #![trigger new_container_bootstrap_4k_pages(
                allocator_4k_page,
                allocator_2m_page,
                allocator_1g_page,
                scheduler_page,
                cpu_set_page,
                process_page,
                pagetable_page,
                l4_page,
            ).contains(page_ptr)]
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) <==> new_container_bootstrap_4k_pages(
                    allocator_4k_page,
                    allocator_2m_page,
                    allocator_1g_page,
                    scheduler_page, cpu_set_page,
                    process_page,
                    pagetable_page,
                    l4_page,
                ).contains(page_ptr) || funding_pages.to_set().contains(page_ptr) || page_ptr == thread_page,
        forall|page_ptr: PagePtr|
            #![trigger old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr)]
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr) <==> page_ptr == container_page || page_ptr == pcid_allocator_page,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_1g.view().is_empty(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        container_page != pcid_allocator_page,
        page_ptr_valid(allocator_4k_page),
        page_ptr_valid(allocator_2m_page),
        page_ptr_valid(allocator_1g_page),
        page_ptr_valid(scheduler_page),
        page_ptr_valid(cpu_set_page),
        page_ptr_valid(process_page),
        page_ptr_valid(pagetable_page),
        page_ptr_valid(l4_page),
        page_ptr_valid(thread_page),
        new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).len() == 8,
        !new_container_bootstrap_4k_pages(allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,).contains(thread_page),
        funding_pages.len() == funding_page_count,
        funding_pages.no_duplicates(),
        funding_page_head == staged_4k_page_chain_head(funding_pages),
        staged_4k_page_chain(old(krnl).pg_arr, funding_pages),
        funding_page_lock_perms.dom() == funding_pages.to_set(),
        process_quota_4k <= funding_page_count,
        allocator_quota_4k == funding_page_count - process_quota_4k,
        !funding_pages.to_set().contains(thread_page),
        funding_pages.to_set().disjoint(new_container_moved_pages(
            container_page,
            pcid_allocator_page,
            allocator_4k_page,
            allocator_2m_page,
            allocator_1g_page,
            scheduler_page, cpu_set_page,
            process_page,
            pagetable_page,
            l4_page,
        )),
        new_container_bootstrap_4k_pages(
            allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,
        ).disjoint(page_2m_all_ptrs(page_ptr2page_index(container_page))),
        new_container_bootstrap_4k_pages(
            allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page,
        ).disjoint(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))),
        page_2m_all_ptrs(page_ptr2page_index(container_page)).disjoint(page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page))),
        new_container_moved_pages(
            container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
            process_page, pagetable_page, l4_page,
        ).union(funding_pages.to_set()).subset_of(old(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view(),),
        !old(krnl).ctn_mp.dom().contains(container_page),
        !old(krnl).pcid_allc_mp.dom().contains(pcid_allocator_page),
        !old(krnl).allc_4k_mp.dom().contains(allocator_4k_page),
        !old(krnl).allc_2m_mp.dom().contains(allocator_2m_page),
        !old(krnl).allc_1g_mp.dom().contains(allocator_1g_page),
        !old(krnl).sched_mp.dom().contains(scheduler_page),
        !old(krnl).cpu_set_mp.dom().contains(cpu_set_page),
        !old(krnl).prc_mp.dom().contains(process_page),
        !old(krnl).pt_mp.dom().contains(pagetable_page),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(container_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().state == (PageState::Owned2m { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page),).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page)).view().view().owning_container == parent_container_ptr,
        forall|page_ptr: PagePtr|
            #![trigger funding_page_lock_perms.dom().contains(page_ptr)]
            funding_page_lock_perms.dom().contains(page_ptr) ==> {
                &&& page_ptr_valid(page_ptr)
                &&& funding_page_lock_perms.spec_index(page_ptr).state()
                    is WriteLock
                &&& funding_page_lock_perms.spec_index(page_ptr).thread_id() == old(lctx).thread_id()
                &&& old(krnl).pg_arr.spec_index(
                    page_ptr2page_index(page_ptr),
                ).view().view().state == (PageState::Owned4k {
                        thread_ptr: current_thread_ptr,
                    })
                &&& old(krnl).pg_arr.spec_index(
                    page_ptr2page_index(page_ptr),
                ).view().view().owning_container == parent_container_ptr
                &&& typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write)
                &&& funding_page_lock_perms.spec_index(page_ptr).lock_id() == old(krnl).pg_arr.spec_index(
                        page_ptr2page_index(page_ptr),
                    ).view().locking_thread()->Write_lock_id
            },
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, old(krnl).pg_arr, old(lctx), page_ptr2page_index(container_page),),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, old(krnl).pg_arr, old(lctx), page_ptr2page_index(pcid_allocator_page),),
        container_page_lock_perm.state() is WriteLock,
        container_page_lock_perm.thread_id() == old(lctx).thread_id(),
        container_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(container_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(container_page), TypedLockMode::Write),
        pcid_allocator_page_lock_perm.state() is WriteLock,
        pcid_allocator_page_lock_perm.thread_id() == old(lctx).thread_id(),
        pcid_allocator_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pcid_allocator_page), TypedLockMode::Write),
        allocator_4k_page_lock_perm.state() is WriteLock,
        allocator_4k_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_4k_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(allocator_4k_page), TypedLockMode::Write),
        allocator_2m_page_lock_perm.state() is WriteLock,
        allocator_2m_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_2m_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(allocator_2m_page), TypedLockMode::Write),
        allocator_1g_page_lock_perm.state() is WriteLock,
        allocator_1g_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_1g_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(allocator_1g_page), TypedLockMode::Write),
        scheduler_page_lock_perm.state() is WriteLock,
        cpu_set_page_lock_perm.state() is WriteLock,
        scheduler_page_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_set_page_lock_perm.thread_id() == old(lctx).thread_id(),
        scheduler_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page)).view().locking_thread()->Write_lock_id,
        cpu_set_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(scheduler_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(cpu_set_page), TypedLockMode::Write),
        process_page_lock_perm.state() is WriteLock,
        process_page_lock_perm.thread_id() == old(lctx).thread_id(),
        process_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(process_page), TypedLockMode::Write),
        pagetable_page_lock_perm.state() is WriteLock,
        pagetable_page_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pagetable_page), TypedLockMode::Write),
        l4_page_lock_perm.state() is WriteLock,
        l4_page_lock_perm.thread_id() == old(lctx).thread_id(),
        l4_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(l4_page), TypedLockMode::Write),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(krnl).inv(),
        final(krnl).cpu_tlb == old(krnl).cpu_tlb,
        final(krnl).cpu_arr == old(krnl).cpu_arr,
        final(krnl).pcid_needflush == old(krnl).pcid_needflush,
        final(krnl).cpu_published == old(krnl).cpu_published,
        final(krnl).allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom().insert(allocator_4k_page),
        final(krnl).allc_2m_mp.dom() == old(krnl).allc_2m_mp.dom().insert(allocator_2m_page),
        final(krnl).allc_1g_mp.dom() == old(krnl).allc_1g_mp.dom().insert(allocator_1g_page),
        final(krnl).pg_arr.spec_index(
            page_ptr2page_index(allocator_4k_page),
        ).view().view().state == (PageState::Allocated4k {
            state: Allocated4KPageState::As4KAllocator,
        }),
        final(krnl).pg_arr.spec_index(
            page_ptr2page_index(allocator_2m_page),
        ).view().view().state == (PageState::Allocated4k {
            state: Allocated4KPageState::As2MAllocator,
        }),
        final(krnl).pg_arr.spec_index(
            page_ptr2page_index(allocator_1g_page),
        ).view().view().state == (PageState::Allocated4k {
            state: Allocated4KPageState::As1GAllocator,
        }),
        !final(krnl).ctn_mp.spec_index(container_page).being_killed(),
        final(krnl).ctn_mp.spec_index(container_page).view_rodata().view().parent == Some(parent_container_ptr),
        final(krnl).ctn_mp.spec_index(container_page).view_rodata().view().scheduler == scheduler_page,
        final(krnl).ctn_mp.spec_index(container_page).view_rodata().view().allocator_ptr_4k == allocator_4k_page,
        final(krnl).ctn_mp.spec_index(container_page).view().owned_processes.view() == set![process_page],
        !final(krnl).prc_mp.spec_index(process_page).being_killed(),
        !final(krnl).prc_mp.spec_index(process_page).view().zombie,
        final(krnl).prc_mp.spec_index(process_page).view_rodata().view().owning_container == container_page,
        final(krnl).prc_mp.spec_index(process_page).view_rodata().view().pagetable == pagetable_page,
        final(krnl).prc_mp.spec_index(process_page).view().quota_4k == process_quota_4k,
        final(krnl).allc_4k_mp.spec_index(allocator_4k_page).owning_container == container_page,
        final(krnl).allc_4k_mp.spec_index(allocator_4k_page).global_pool.view().view() == funding_pages,
        final(krnl).allc_4k_mp.spec_index(allocator_4k_page).total_free_pages.view() == funding_page_count,
        final(krnl).allc_4k_mp.spec_index(allocator_4k_page).quota.view().view() == allocator_quota_4k,
        final(krnl).pt_mp.spec_index(pagetable_page).view().is_empty(),
        final(krnl).pt_mp.spec_index(pagetable_page).view().proc_ptr == process_page,
        !final(krnl).sched_mp.spec_index(scheduler_page).being_killed(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view() == set![thread_page],
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().is_empty(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_1g == old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_1g,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_fields_equal(
                &old(krnl).thr_mp.spec_index(current_thread_ptr).view(),
            ),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().state == old(krnl).thr_mp.spec_index(current_thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k - 8 - funding_page_count,
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx),),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx),),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx),),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page)) == old(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page)),
        final(lctx).page_lock_map().get(page_ptr2page_index(thread_page)) == old(lctx).page_lock_map().get(page_ptr2page_index(thread_page)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(thread_page)).view().view().owning_container == parent_container_ptr,
        final(krnl).ctn_mp.dom().contains(parent_container_ptr),
        !final(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view().contains(thread_page),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_processes == old(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_processes,
        !final(krnl).ctn_mp.spec_index(container_page).view().owned_pages.view().contains(thread_page),
        parent_container_lock_perm.lock_id() == final(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        current_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom(),
        page_2m_tail_indices(page_ptr2page_index(container_page)).disjoint(set![
            page_ptr2page_index(container_page), page_ptr2page_index(pcid_allocator_page), page_ptr2page_index(allocator_4k_page),
            page_ptr2page_index(allocator_2m_page), page_ptr2page_index(allocator_1g_page), page_ptr2page_index(scheduler_page),
            page_ptr2page_index(cpu_set_page), page_ptr2page_index(process_page), page_ptr2page_index(pagetable_page),
            page_ptr2page_index(l4_page), page_ptr2page_index(thread_page),
        ],),
        page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)).disjoint(set![
            page_ptr2page_index(container_page), page_ptr2page_index(pcid_allocator_page), page_ptr2page_index(allocator_4k_page),
            page_ptr2page_index(allocator_2m_page), page_ptr2page_index(allocator_1g_page), page_ptr2page_index(scheduler_page),
            page_ptr2page_index(cpu_set_page), page_ptr2page_index(process_page), page_ptr2page_index(pagetable_page),
            page_ptr2page_index(l4_page), page_ptr2page_index(thread_page),
        ],),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).container_lock_map().dom() == old(lctx).container_lock_map().dom().insert(container_page),
        forall|ptr: RwLockContainerPtr|
            #![trigger final(lctx).container_lock_map().get(ptr)]
            #![trigger old(lctx).container_lock_map().get(ptr)]
            old(lctx).container_lock_map().dom().contains(ptr) && ptr != container_page ==> final(lctx).container_lock_map().get(ptr) == old(lctx).container_lock_map().get(ptr),
        final(lctx).process_lock_map().dom() == old(lctx).process_lock_map().dom().insert(process_page),
        forall|ptr: RwLockProcessPtr|
            #![trigger final(lctx).process_lock_map().get(ptr)]
            #![trigger old(lctx).process_lock_map().get(ptr)]
            old(lctx).process_lock_map().dom().contains(ptr) && ptr != process_page ==> final(lctx).process_lock_map().get(ptr) == old(lctx).process_lock_map().get(ptr),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map().dom() == old(lctx).scheduler_lock_map().dom().insert(scheduler_page),
        final(lctx).pcid_allocator_lock_map().dom() == old(lctx).pcid_allocator_lock_map().dom().insert(pcid_allocator_page),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map().dom() == old(lctx).pagetable_lock_map().dom().insert(pagetable_page),
        forall|ptr: RwLockPageTableRoot|
            #![trigger final(lctx).pagetable_lock_map().get(ptr)]
            #![trigger old(lctx).pagetable_lock_map().get(ptr)]
            old(lctx).pagetable_lock_map().dom().contains(ptr) && ptr != pagetable_page ==> final(lctx).pagetable_lock_map().get(ptr) == old(lctx).pagetable_lock_map().get(ptr),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(krnl).ctn_mp.dom().contains(container_page),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), container_page, TypedLockMode::Write),
        final(krnl).prc_mp.dom().contains(process_page),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), process_page, TypedLockMode::Write),
        final(krnl).pt_mp.dom().contains(pagetable_page),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), pagetable_page, TypedLockMode::Write),
        staged_4k_page_chain(final(krnl).pg_arr, funding_pages),
        final(krnl).sched_mp.dom().contains(scheduler_page),
        typed_lock_map_contains_mode(final(lctx).scheduler_lock_map(), scheduler_page, TypedLockMode::Write),
        final(krnl).pcid_allc_mp.dom().contains(pcid_allocator_page),
        typed_lock_map_contains_mode(final(lctx).pcid_allocator_lock_map(), pcid_allocator_page, TypedLockMode::Write),
        final(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(container_page), TypedLockMode::Write),
        container_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(container_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pcid_allocator_page), TypedLockMode::Write),
        pcid_allocator_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(allocator_4k_page), TypedLockMode::Write),
        allocator_4k_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(allocator_2m_page), TypedLockMode::Write),
        allocator_2m_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(allocator_1g_page), TypedLockMode::Write),
        allocator_1g_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(scheduler_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(cpu_set_page), TypedLockMode::Write),
        scheduler_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page)).view().locking_thread()->Write_lock_id,
        cpu_set_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(process_page), TypedLockMode::Write),
        process_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(process_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pagetable_page), TypedLockMode::Write),
        pagetable_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(l4_page), TypedLockMode::Write),
        l4_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page)).view().locking_thread()->Write_lock_id,
        forall|page_ptr: PagePtr|
            #![trigger funding_page_lock_perms.dom().contains(page_ptr)]
            funding_page_lock_perms.dom().contains(page_ptr) ==> {
                &&& final(krnl).pg_arr.spec_index(
                    page_ptr2page_index(page_ptr),
                ).view().view().state == (PageState::Free4k {
                    allocator_ptr: Ghost(allocator_4k_page),
                    state: FreePageAllocatorState::GlobalList,
                })
                &&& final(krnl).pg_arr.spec_index(
                    page_ptr2page_index(page_ptr),
                ).view().view().owning_container == container_page
                &&& typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write)
                &&& funding_page_lock_perms.spec_index(page_ptr).lock_id() == final(krnl).pg_arr.spec_index(
                        page_ptr2page_index(page_ptr),
                    ).view().locking_thread()->Write_lock_id
            },
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, final(krnl).pg_arr, final(lctx), page_ptr2page_index(container_page),),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, final(krnl).pg_arr, final(lctx), page_ptr2page_index(pcid_allocator_page),),
        ret.0.view().state() is WriteLock,
        ret.0.view().thread_id() == final(lctx).thread_id(),
        ret.0.view().lock_id() == final(krnl).ctn_mp.spec_index(container_page).locking_thread()->Write_lock_id,
        ret.1.view().state() is WriteLock,
        ret.1.view().thread_id() == final(lctx).thread_id(),
        ret.1.view().lock_id() == final(krnl).prc_mp.spec_index(process_page).locking_thread()->Write_lock_id,
        ret.2.view().state() is WriteLock,
        ret.2.view().thread_id() == final(lctx).thread_id(),
        ret.2.view().lock_id() == final(krnl).pt_mp.spec_index(pagetable_page).locking_thread()->Write_lock_id,
        ret.3.view().state() is WriteLock,
        ret.3.view().thread_id() == final(lctx).thread_id(),
        ret.3.view().lock_id() == final(krnl).sched_mp.spec_index(scheduler_page).locking_thread()->Write_lock_id,
        ret.4.view().state() is WriteLock,
        ret.4.view().thread_id() == final(lctx).thread_id(),
        ret.4.view().lock_id() == final(krnl).pcid_allc_mp.spec_index(pcid_allocator_page).locking_thread()->Write_lock_id,
{
    let ghost pre_krnl = *krnl;
    let ret = publish_staged_container_root_mutation(
        krnl,
        parent_container_ptr,
        current_thread_ptr,
        container_page,
        pcid_allocator_page,
        allocator_4k_page,
        allocator_2m_page,
        allocator_1g_page,
        scheduler_page,
        cpu_set_page,
        process_page,
        pagetable_page,
        l4_page,
        thread_page,
        funding_page_count,
        funding_page_head,
        Ghost(funding_pages),
        allocator_quota_4k,
        process_quota_4k,
        Tracked(&mut *lctx),
        Tracked(parent_container_lock_perm),
        Tracked(current_thread_lock_perm),
        Tracked(container_page_lock_perm),
        Tracked(pcid_allocator_page_lock_perm),
        Tracked(allocator_4k_page_lock_perm),
        Tracked(allocator_2m_page_lock_perm),
        Tracked(allocator_1g_page_lock_perm),
        Tracked(scheduler_page_lock_perm),
        Tracked(cpu_set_page_lock_perm),
        Tracked(process_page_lock_perm),
        Tracked(pagetable_page_lock_perm),
        Tracked(l4_page_lock_perm),
        Tracked(funding_page_lock_perms),
        Tracked(container_tail_lock_perms),
        Tracked(pcid_allocator_tail_lock_perms),
    );
    proof {
        page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
        page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
        owned_4k_page_not_in_2m_region(&pre_krnl, thread_page, page_ptr2page_index(container_page),);
        owned_4k_page_not_in_2m_region(&pre_krnl, thread_page, page_ptr2page_index(pcid_allocator_page),);
        assert(!new_container_moved_pages(
            container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
            process_page, pagetable_page, l4_page,
        ).union(funding_pages.to_set()).contains(thread_page)) by {
            reveal(new_container_moved_pages); reveal(new_container_bootstrap_4k_pages); reveal(Set::disjoint);
        };
        assert(krnl.ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view().contains(thread_page)) by {
            assert(pre_krnl.ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view().contains(thread_page)) by {
                assert(container_page_owner_wf(pre_krnl.ctn_mp, pre_krnl.pg_arr)) by { reveal(KernelK::inv); };
                reveal(container_page_owner_wf);
            };
            broadcast use vstd::set::lemma_set_difference;
        };
        publish_staged_container_root_eof(
            pre_krnl, *krnl, parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
            allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
            funding_pages, allocator_quota_4k, process_quota_4k,
        );
    }
    ret
}
}
