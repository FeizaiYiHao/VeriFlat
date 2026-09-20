use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub(super) proof fn publish_staged_container_root_mutation_object_invs(
    post: KernelK, parent_container_ptr: RwLockContainerPtr, container_page: PagePtr, pcid_allocator_page: PagePtr, scheduler_page: PagePtr,
    cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr,
)
    requires
        pagetable_perms_wf(post.pt_mp),
        post.pt_mp.dom().contains(pagetable_page),
        container_perms_wf(post.ctn_mp),
        post.ctn_mp.dom().contains(parent_container_ptr),
        post.ctn_mp.dom().contains(container_page),
        process_perms_wf(post.prc_mp),
        post.prc_mp.dom().contains(process_page),
        scheduler_perms_wf(post.sched_mp),
        post.sched_mp.dom().contains(scheduler_page),
        cpu_set_perms_wf(post.cpu_set_mp),
        post.cpu_set_mp.dom().contains(cpu_set_page),
        pcid_allocator_perms_wf(post.pcid_allc_mp),
        post.pcid_allc_mp.dom().contains(pcid_allocator_page),
    ensures
        post.pt_mp.spec_index(pagetable_page).inv(),
        post.ctn_mp.spec_index(parent_container_ptr).inv(),
        post.ctn_mp.spec_index(container_page).inv(),
        post.prc_mp.spec_index(process_page).inv(),
        post.sched_mp.spec_index(scheduler_page).inv(),
        post.cpu_set_mp.spec_index(cpu_set_page).inv(),
        post.pcid_allc_mp.spec_index(pcid_allocator_page).inv(),
{
    pagetable_perms_wf_at(post.pt_mp, pagetable_page);
    container_perms_wf_at(post.ctn_mp, parent_container_ptr);
    container_perms_wf_at(post.ctn_mp, container_page);
    process_perms_wf_at(post.prc_mp, process_page);
    scheduler_perms_wf_at(post.sched_mp, scheduler_page);
    assert(post.cpu_set_mp.spec_index(cpu_set_page).inv()) by { reveal(cpu_set_perms_wf); };
    pcid_allocator_perms_wf_at(post.pcid_allc_mp, pcid_allocator_page);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
pub(super) fn publish_staged_container_root_mutation(
    krnl: &mut KernelK, parent_container_ptr: RwLockContainerPtr, current_thread_ptr: RwLockThreadPtr, container_page: PagePtr,
    pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr, allocator_2m_page: PagePtr, allocator_1g_page: PagePtr,
    scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr, pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr,
    funding_page_count: usize, funding_page_head: PagePtr, Ghost(funding_pages): Ghost<Seq<PagePtr>>, allocator_quota_4k: usize,
    process_quota_4k: usize, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(parent_container_lock_perm): Tracked<&LockPerm>,
    Tracked(current_thread_lock_perm): Tracked<&LockPerm>, Tracked(container_page_lock_perm): Tracked<&LockPerm>,
    Tracked(pcid_allocator_page_lock_perm): Tracked<&LockPerm>, Tracked(allocator_4k_page_lock_perm): Tracked<&LockPerm>,
    Tracked(allocator_2m_page_lock_perm): Tracked<&LockPerm>, Tracked(allocator_1g_page_lock_perm): Tracked<&LockPerm>,
    Tracked(scheduler_page_lock_perm): Tracked<&LockPerm>, Tracked(cpu_set_page_lock_perm): Tracked<&LockPerm>,
    Tracked(process_page_lock_perm): Tracked<&LockPerm>, Tracked(pagetable_page_lock_perm): Tracked<&LockPerm>,
    Tracked(l4_page_lock_perm): Tracked<&LockPerm>, Tracked(funding_page_lock_perms): Tracked<&Map<PagePtr, LockPerm>>,
    Tracked(container_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
    Tracked(pcid_allocator_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
) -> (ret: (Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>,))
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
        page_array_wf(final(krnl).pg_arr),
        final(krnl).pt_mp.perms_wf(),
        final(krnl).pt_mp.dom().contains(pagetable_page),
        final(krnl).pt_mp.spec_index(pagetable_page).inv(),
        final(krnl).ctn_mp.perms_wf(),
        final(krnl).ctn_mp.dom().contains(parent_container_ptr),
        final(krnl).ctn_mp.dom().contains(container_page),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).inv(),
        final(krnl).ctn_mp.spec_index(container_page).inv(),
        final(krnl).prc_mp.perms_wf(),
        final(krnl).prc_mp.dom().contains(process_page),
        final(krnl).prc_mp.spec_index(process_page).inv(),
        final(krnl).thr_mp.perms_wf(),
        final(krnl).thr_mp.dom().contains(current_thread_ptr),
        final(krnl).thr_mp.spec_index(current_thread_ptr).inv(),
        final(krnl).sched_mp.perms_wf(),
        final(krnl).sched_mp.dom().contains(scheduler_page),
        final(krnl).sched_mp.spec_index(scheduler_page).inv(),
        final(krnl).cpu_set_mp.perms_wf(),
        final(krnl).cpu_set_mp.dom().contains(cpu_set_page),
        final(krnl).cpu_set_mp.spec_index(cpu_set_page).inv(),
        final(krnl).pcid_allc_mp.perms_wf(),
        final(krnl).pcid_allc_mp.dom().contains(pcid_allocator_page),
        final(krnl).pcid_allc_mp.spec_index(pcid_allocator_page).inv(),
        final(krnl).allc_4k_mp.perms_wf(),
        final(krnl).allc_4k_mp.dom().contains(allocator_4k_page),
        final(krnl).allc_4k_mp.spec_index(allocator_4k_page).inv(),
        final(krnl).allc_2m_mp.perms_wf(),
        final(krnl).allc_2m_mp.dom().contains(allocator_2m_page),
        final(krnl).allc_2m_mp.spec_index(allocator_2m_page).inv(),
        final(krnl).allc_1g_mp.perms_wf(),
        final(krnl).allc_1g_mp.dom().contains(allocator_1g_page),
        final(krnl).allc_1g_mp.spec_index(allocator_1g_page).inv(),
        publish_staged_container_root_kernel_state_framing( *old(krnl), *final(krnl), parent_container_ptr, current_thread_ptr, container_page, pcid_allocator_page, allocator_4k_page,
            allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page, process_page, pagetable_page, l4_page, thread_page,
            funding_pages, allocator_quota_4k, process_quota_4k,
        ),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        final(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view() == old(krnl).ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view().difference(
                new_container_moved_pages(
                    container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page,
                    cpu_set_page, process_page, pagetable_page, l4_page,
                ).union(funding_pages.to_set()),
            ),
        final(lctx).page_lock_map().get(page_ptr2page_index(thread_page)) == old(lctx).page_lock_map().get(page_ptr2page_index(thread_page)),
        parent_container_lock_perm.lock_id() == final(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        current_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom(),
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
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), container_page, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), process_page, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), pagetable_page, TypedLockMode::Write),
        staged_4k_page_chain(final(krnl).pg_arr, funding_pages),
        typed_lock_map_contains_mode(final(lctx).scheduler_lock_map(), scheduler_page, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).pcid_allocator_lock_map(), pcid_allocator_page, TypedLockMode::Write),
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
    hide(Seq::contains);
    hide(Seq::no_duplicates);
    let ghost pre_krnl = *krnl;
    let child_container_ptr = container_page;
    let child_pcid_allocator_ptr = pcid_allocator_page;
    let child_allocator_4k_ptr = allocator_4k_page;
    let child_allocator_2m_ptr = allocator_2m_page;
    let child_allocator_1g_ptr = allocator_1g_page;
    let child_scheduler_ptr = scheduler_page;
    let child_cpu_set_ptr = cpu_set_page;
    let child_process_ptr = process_page;
    let child_pagetable_ptr = pagetable_page;
    let root_pcid: Pcid = KERNEL_DEFAULT_PCID + 1usize;
    let container_head = page_ptr2page_index(container_page);
    let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
    let allocator_4k_index = page_ptr2page_index(allocator_4k_page);
    let allocator_2m_index = page_ptr2page_index(allocator_2m_page);
    let allocator_1g_index = page_ptr2page_index(allocator_1g_page);
    let scheduler_index = page_ptr2page_index(scheduler_page);
    let cpu_set_index = page_ptr2page_index(cpu_set_page);
    let process_index = page_ptr2page_index(process_page);
    let pagetable_index = page_ptr2page_index(pagetable_page);
    let l4_index = page_ptr2page_index(l4_page);
    let ghost bootstrap_pages = new_container_bootstrap_4k_pages(
        allocator_4k_page,
        allocator_2m_page,
        allocator_1g_page,
        scheduler_page, cpu_set_page,
        process_page,
        pagetable_page,
        l4_page,
    );
    let ghost bootstrap_seq = seq![
        allocator_4k_page,
        allocator_2m_page,
        allocator_1g_page,
        scheduler_page,
        cpu_set_page,
        process_page,
        pagetable_page,
        l4_page,
    ];
    let ghost funding_indices = funding_pages.map_values(
        |page_ptr: PagePtr| page_ptr2page_index(page_ptr),
    ).to_set();
    proof {
        assert(typed_lock_maps_aligned(krnl, lctx));
        assert(bootstrap_seq.to_set() == bootstrap_pages) by { reveal(new_container_bootstrap_4k_pages); };
        assert(bootstrap_seq.to_set().len() == bootstrap_seq.len());
        bootstrap_seq.lemma_no_dup_set_cardinality();
        page_ptr_seq_indices_no_duplicates(bootstrap_seq);
        assert({
            &&& allocator_2m_index != allocator_4k_index
            &&& allocator_1g_index != allocator_4k_index
            &&& allocator_1g_index != allocator_2m_index
            &&& scheduler_index != allocator_4k_index
            &&& scheduler_index != allocator_2m_index
            &&& scheduler_index != allocator_1g_index
            &&& cpu_set_index != allocator_4k_index
            &&& cpu_set_index != allocator_2m_index
            &&& cpu_set_index != allocator_1g_index
            &&& cpu_set_index != scheduler_index
            &&& process_index != allocator_4k_index
            &&& process_index != allocator_2m_index
            &&& process_index != allocator_1g_index
            &&& process_index != scheduler_index
            &&& process_index != cpu_set_index
            &&& pagetable_index != allocator_4k_index
            &&& pagetable_index != allocator_2m_index
            &&& pagetable_index != allocator_1g_index
            &&& pagetable_index != scheduler_index
            &&& pagetable_index != cpu_set_index
            &&& pagetable_index != process_index
            &&& l4_index != allocator_4k_index
            &&& l4_index != allocator_2m_index
            &&& l4_index != allocator_1g_index
            &&& l4_index != scheduler_index
            &&& l4_index != cpu_set_index
            &&& l4_index != process_index
            &&& l4_index != pagetable_index
        }) by { reveal(Seq::no_duplicates); reveal(Seq::map_values); };
        page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
        page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
        assert(page_ptr_valid(container_page)) by { reveal(page_ptr_valid); reveal(page_ptr_2m_valid); };
        assert(page_ptr_valid(pcid_allocator_page)) by { reveal(page_ptr_valid); reveal(page_ptr_2m_valid); };
        assert(container_head != pcid_allocator_head) by { page_ptr2page_index_neq(container_page, pcid_allocator_page); };
        distinct_2m_heads_have_disjoint_tails(container_head, pcid_allocator_head,);
        distinct_2m_heads_have_disjoint_all_ptrs(container_head, pcid_allocator_head,);
        page_2m_all_ptrs_contains_head(container_head);
        page_2m_all_ptrs_contains_head(pcid_allocator_head);
        assert(!page_2m_tail_indices(container_head).contains(container_head) && !page_2m_tail_indices(pcid_allocator_head).contains(pcid_allocator_head)) by { reveal(page_2m_tail_indices); };
        assert(!page_2m_tail_indices(container_head).contains(pcid_allocator_head) && !page_2m_tail_indices(pcid_allocator_head).contains(container_head)) by {
            if page_2m_tail_indices(container_head).contains(pcid_allocator_head)
            {
                reveal(page_2m_tail_indices);
                page_2m_all_ptrs_contains_index(container_head, pcid_allocator_head,);
            }
            if page_2m_tail_indices(pcid_allocator_head).contains(container_head)
            {
                reveal(page_2m_tail_indices);
                page_2m_all_ptrs_contains_index(pcid_allocator_head, container_head,);
            }
            reveal(Set::disjoint);
        };
        assert(page_array_wf(krnl.pg_arr)) by { reveal(KernelK::inv); };
        assert(krnl.pg_arr.inv()) by { page_array_wf_at(krnl.pg_arr, container_head); };
        assert(krnl.ctn_mp.perms_wf()) by { reveal(KernelK::inv); reveal(typed_lock_maps_aligned); reveal(container_perms_wf); };
        assert(container_perms_wf(krnl.ctn_mp)) by { reveal(KernelK::inv); };
        assert(krnl.ctn_mp.spec_index(parent_container_ptr).is_init()) by { assert(krnl.ctn_mp.dom().contains(parent_container_ptr)); container_perms_wf_at(krnl.ctn_mp, parent_container_ptr); };
        assert(krnl.pg_arr.spec_index(container_head).view().is_init() && krnl.pg_arr.spec_index(container_head).view().view().inv() && krnl.pg_arr.spec_index(container_head).view().view().addr == container_page && krnl.pg_arr.spec_index(container_head).view().view().perm_2m.view().is_some()) by { page_array_wf_at(krnl.pg_arr, container_head); };
        assert(krnl.pg_arr.spec_index(pcid_allocator_head).view().is_init() && krnl.pg_arr.spec_index(pcid_allocator_head).view().view().inv() && krnl.pg_arr.spec_index(pcid_allocator_head).view().view().addr == pcid_allocator_page && krnl.pg_arr.spec_index(pcid_allocator_head).view().view().perm_2m.view().is_some()) by { page_array_wf_at(krnl.pg_arr, pcid_allocator_head); };
        assert(bootstrap_pages.contains(allocator_4k_page) && bootstrap_pages.contains(allocator_2m_page) && bootstrap_pages.contains(allocator_1g_page) && bootstrap_pages.contains(scheduler_page) && bootstrap_pages.contains(cpu_set_page) && bootstrap_pages.contains(process_page) && bootstrap_pages.contains(pagetable_page) && bootstrap_pages.contains(l4_page)) by {
            bootstrap_seq.to_set_ensures(); reveal(new_container_bootstrap_4k_pages); reveal(Seq::contains);
        };
        assert(
            krnl.pg_arr.spec_index(allocator_4k_index).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }) && krnl.pg_arr.spec_index(allocator_2m_index).view().view().state == (PageState::Owned4k {
                        thread_ptr: current_thread_ptr,
                    }) && krnl.pg_arr.spec_index(allocator_1g_index).view().view().state == (PageState::Owned4k {
                        thread_ptr: current_thread_ptr,
                    }) && krnl.pg_arr.spec_index(scheduler_index).view().view().state == (PageState::Owned4k {
                        thread_ptr: current_thread_ptr,
                    }) && krnl.pg_arr.spec_index(cpu_set_index).view().view().state == (PageState::Owned4k {
                        thread_ptr: current_thread_ptr,
                    }) && krnl.pg_arr.spec_index(process_index).view().view().state == (PageState::Owned4k {
                        thread_ptr: current_thread_ptr,
                    }) && krnl.pg_arr.spec_index(pagetable_index).view().view().state == (PageState::Owned4k {
                        thread_ptr: current_thread_ptr,
                    }) && krnl.pg_arr.spec_index(l4_index).view().view().state == (PageState::Owned4k {
                        thread_ptr: current_thread_ptr,
                    })
        ) by { reveal(new_container_bootstrap_4k_pages); };
        assert({
            &&& index_valid(NUM_PAGES, l4_index)
            &&& index_valid(NUM_PAGES, pagetable_index)
            &&& index_valid(NUM_PAGES, process_index)
            &&& index_valid(NUM_PAGES, allocator_4k_index)
            &&& index_valid(NUM_PAGES, allocator_2m_index)
            &&& index_valid(NUM_PAGES, allocator_1g_index)
            &&& index_valid(NUM_PAGES, scheduler_index)
            &&& index_valid(NUM_PAGES, cpu_set_index)
        }) by { page_ptr_valid_imply_page_index_valid(); };
        assert(krnl.pg_arr.spec_index(l4_index).view().is_init() && krnl.pg_arr.spec_index(l4_index).view().view().inv() && krnl.pg_arr.spec_index(l4_index).view().view().addr == l4_page && krnl.pg_arr.spec_index(l4_index).view().view().perm_4k.view().is_some()) by { page_array_wf_at(krnl.pg_arr, l4_index); };
        assert(krnl.pg_arr.spec_index(pagetable_index).view().is_init() && krnl.pg_arr.spec_index(pagetable_index).view().view().inv() && krnl.pg_arr.spec_index(pagetable_index).view().view().addr == pagetable_page && krnl.pg_arr.spec_index(pagetable_index).view().view().perm_4k.view().is_some()) by { page_array_wf_at(krnl.pg_arr, pagetable_index); };
        assert(krnl.pg_arr.spec_index(process_index).view().is_init() && krnl.pg_arr.spec_index(process_index).view().view().inv() && krnl.pg_arr.spec_index(process_index).view().view().addr == process_page && krnl.pg_arr.spec_index(process_index).view().view().perm_4k.view().is_some()) by { page_array_wf_at(krnl.pg_arr, process_index); };
        assert(krnl.pg_arr.spec_index(allocator_4k_index).view().is_init() && krnl.pg_arr.spec_index(allocator_4k_index).view().view().inv() && krnl.pg_arr.spec_index(allocator_4k_index).view().view().addr == allocator_4k_page && krnl.pg_arr.spec_index(allocator_4k_index).view().view().perm_4k.view().is_some()) by { page_array_wf_at(krnl.pg_arr, allocator_4k_index); };
        assert(krnl.pg_arr.spec_index(allocator_2m_index).view().is_init() && krnl.pg_arr.spec_index(allocator_2m_index).view().view().inv() && krnl.pg_arr.spec_index(allocator_2m_index).view().view().addr == allocator_2m_page && krnl.pg_arr.spec_index(allocator_2m_index).view().view().perm_4k.view().is_some()) by { page_array_wf_at(krnl.pg_arr, allocator_2m_index); };
        assert(krnl.pg_arr.spec_index(allocator_1g_index).view().is_init() && krnl.pg_arr.spec_index(allocator_1g_index).view().view().inv() && krnl.pg_arr.spec_index(allocator_1g_index).view().view().addr == allocator_1g_page && krnl.pg_arr.spec_index(allocator_1g_index).view().view().perm_4k.view().is_some()) by { page_array_wf_at(krnl.pg_arr, allocator_1g_index); };
        assert(krnl.pg_arr.spec_index(scheduler_index).view().is_init() && krnl.pg_arr.spec_index(scheduler_index).view().view().inv() && krnl.pg_arr.spec_index(scheduler_index).view().view().addr == scheduler_page && krnl.pg_arr.spec_index(scheduler_index).view().view().perm_4k.view().is_some()) by { page_array_wf_at(krnl.pg_arr, scheduler_index); };
        assert(krnl.pg_arr.spec_index(cpu_set_index).view().is_init() && krnl.pg_arr.spec_index(cpu_set_index).view().view().inv() && krnl.pg_arr.spec_index(cpu_set_index).view().view().addr == cpu_set_page && krnl.pg_arr.spec_index(cpu_set_index).view().view().perm_4k.view().is_some()) by { page_array_wf_at(krnl.pg_arr, cpu_set_index); };
        assert(krnl.dflt_pt.view().wf()) by {
            assert(krnl.default_pagetable_wf()) by { reveal(KernelK::inv); };
            reveal(KernelK::default_pagetable_wf);
        };
        assert(pei_valid(krnl.dflt_pt.view().kernel_l4_end)) by { reveal(PageTable::kernel_entries_wf); };
    }
    let child_depth = krnl.ctn_mp.borrow_rodata(parent_container_ptr).borrow().depth + 1;
    let ghost parent_uppers = krnl.ctn_mp.spec_index(parent_container_ptr).view_ghost().uppertree_seq.view();
    let ghost child_uppers = krnl.ctn_mp.spec_index(parent_container_ptr).view_ghost().uppertree_seq.view().push(parent_container_ptr);
    let ghost moved_pages = new_container_moved_pages(
        container_page,
        pcid_allocator_page,
        allocator_4k_page,
        allocator_2m_page,
        allocator_1g_page,
        scheduler_page, cpu_set_page,
        process_page,
        pagetable_page,
        l4_page,
    ).union(funding_pages.to_set());
    proof {
        assert(krnl.prc_mp.perms_wf()) by { reveal(KernelK::inv); reveal(typed_lock_maps_aligned); reveal(process_perms_wf); };
        assert(krnl.pt_mp.perms_wf()) by { reveal(KernelK::inv); reveal(typed_lock_maps_aligned); reveal(pagetable_perms_wf); };
        assert(krnl.sched_mp.perms_wf()) by { reveal(KernelK::inv); reveal(typed_lock_maps_aligned); reveal(scheduler_perms_wf); };
        assert(krnl.pcid_allc_mp.perms_wf()) by { reveal(KernelK::inv); reveal(typed_lock_maps_aligned); reveal(pcid_allocator_perms_wf); };
        assert(krnl.allc_4k_mp.perms_wf()) by { reveal(KernelK::inv); reveal(typed_lock_maps_aligned); reveal(allocator_perms_wf); };
        assert(krnl.allc_2m_mp.perms_wf()) by { reveal(KernelK::inv); reveal(typed_lock_maps_aligned); reveal(allocator_perms_wf); };
        assert(krnl.allc_1g_mp.perms_wf()) by { reveal(KernelK::inv); reveal(typed_lock_maps_aligned); reveal(allocator_perms_wf); };
        assert(parent_uppers.no_duplicates() && parent_uppers.len() == krnl.ctn_mp.spec_index(parent_container_ptr).view_rodata().view().depth) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
        assert(container_tree_wf(krnl.rt_ctn, krnl.ctn_mp)) by { reveal(KernelK::inv); };
        assert(container_uppertree_seq_wf(krnl.rt_ctn, krnl.ctn_mp)) by { reveal(KernelK::inv); };
        assert(!parent_uppers.contains(parent_container_ptr)) by { reveal(container_uppertree_seq_wf); reveal(Seq::contains); reveal(Seq::index_of); };
        assert(child_uppers.no_duplicates()) by { seq_push_unique_lemma::<RwLockContainerPtr>(); };
        assert(child_uppers.to_set().subset_of(krnl.ctn_mp.dom())) by { reveal(KernelK::inv); parent_uppers.to_set_ensures(); child_uppers.to_set_ensures(); seq_push_lemma::<RwLockContainerPtr>(); reveal(container_uppertree_seq_wf); };
        owned_4k_page_not_in_2m_region(krnl, thread_page, container_head,);
        owned_4k_page_not_in_2m_region(krnl, thread_page, pcid_allocator_head,);
        owned_4k_page_not_in_2m_tail(krnl, allocator_4k_page, container_head,);
        owned_4k_page_not_in_2m_tail(krnl, allocator_2m_page, container_head,);
        owned_4k_page_not_in_2m_tail(krnl, allocator_1g_page, container_head,);
        owned_4k_page_not_in_2m_tail(krnl, allocator_4k_page, pcid_allocator_head,);
        owned_4k_page_not_in_2m_tail(krnl, allocator_2m_page, pcid_allocator_head,);
        owned_4k_page_not_in_2m_tail(krnl, allocator_1g_page, pcid_allocator_head,);
        owned_4k_page_not_in_2m_tail(krnl, scheduler_page, container_head,);
        owned_4k_page_not_in_2m_tail(krnl, scheduler_page, pcid_allocator_head,);
        owned_4k_page_not_in_2m_tail(krnl, cpu_set_page, container_head,);
        owned_4k_page_not_in_2m_tail(krnl, cpu_set_page, pcid_allocator_head,);
        owned_4k_page_not_in_2m_tail(krnl, process_page, container_head,);
        owned_4k_page_not_in_2m_tail(krnl, process_page, pcid_allocator_head,);
        owned_4k_page_not_in_2m_tail(krnl, pagetable_page, container_head,);
        owned_4k_page_not_in_2m_tail(krnl, pagetable_page, pcid_allocator_head,);
        owned_4k_page_not_in_2m_tail(krnl, l4_page, container_head,);
        owned_4k_page_not_in_2m_tail(krnl, l4_page, pcid_allocator_head,);
        assert(!moved_pages.contains(thread_page)) by { reveal(new_container_moved_pages); reveal(Set::disjoint); };
        assert(krnl.ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view().contains(thread_page)) by {
            assert(container_page_owner_wf(krnl.ctn_mp, krnl.pg_arr)) by { reveal(KernelK::inv); };
            reveal(container_page_owner_wf);
        };
    }

    proof {
        assert(krnl.pg_arr.typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id(),)) by { reveal(typed_lock_maps_aligned); };
        assert(staged_4k_page_chain(pre_krnl.pg_arr, funding_pages,));
        assert({
            &&& !funding_pages.to_set().contains(container_page)
            &&& !funding_pages.to_set().contains(pcid_allocator_page)
            &&& !funding_pages.to_set().contains(allocator_4k_page)
            &&& !funding_pages.to_set().contains(allocator_2m_page)
            &&& !funding_pages.to_set().contains(allocator_1g_page)
            &&& !funding_pages.to_set().contains(scheduler_page)
            &&& !funding_pages.to_set().contains(cpu_set_page)
            &&& !funding_pages.to_set().contains(process_page)
            &&& !funding_pages.to_set().contains(pagetable_page)
            &&& !funding_pages.to_set().contains(l4_page)
            &&& !funding_pages.to_set().contains(thread_page)
        }) by { reveal(new_container_moved_pages); reveal(new_container_bootstrap_4k_pages); reveal(Set::disjoint); };
    }
    let (funded_global_pool, Tracked(container_perm), Tracked(pcid_allocator_perm),) = prepare_new_container_backing_pages(
        &mut krnl.pg_arr, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page,
        cpu_set_page, process_page, pagetable_page, l4_page, thread_page, funding_page_count, funding_page_head, Ghost(funding_pages),
        Ghost(funding_indices), child_allocator_4k_ptr, child_container_ptr, child_depth, Ghost(pre_krnl), Tracked(&mut *lctx),
        Tracked(funding_page_lock_perms), Tracked(container_page_lock_perm), Tracked(pcid_allocator_page_lock_perm),
        Tracked(container_tail_lock_perms), Tracked(pcid_allocator_tail_lock_perms),
    );
    let ghost pages_after_backing_prepare = krnl.pg_arr;
    let ghost page_lock_map_after_backing_prepare = lctx.page_lock_map();
    proof {
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), l4_index, TypedLockMode::Write,)) by { assert(lctx.page_lock_map().get(l4_index) == old(lctx).page_lock_map().get(l4_index)); reveal(typed_lock_map_contains_mode); };
    }

    let allocator_4k_value = PageAllocator::new_with_global_pool(
        child_container_ptr,
        child_depth,
        funded_global_pool,
        allocator_quota_4k,
    );
    let allocator_2m_value = PageAllocator::new_empty(child_container_ptr, child_depth);
    let allocator_1g_value = PageAllocator::new_empty(child_container_ptr, child_depth);
    let scheduler_value = Scheduler::new_empty(
        child_scheduler_ptr,
        child_container_ptr,
        child_depth,
    );
    let mut pcid_allocator_value = PcidAllocator::new_empty(child_container_ptr, child_depth);
    proof {
        assert(pcid_valid(root_pcid)) by { reveal(pcid_valid); };
        assert(pcid_allocator_value.process_is_unallocated(child_process_ptr)) by { reveal(PcidAllocator::process_is_unallocated); };
    }
    pcid_allocator_value.alloc(root_pcid, child_process_ptr);

    let ghost lctx_before_process_publish = *lctx;
    proof {
        assert(root_pcid != KERNEL_DEFAULT_PCID);
        assert(krnl.pg_arr.inv()) by { page_array_wf_at(krnl.pg_arr, process_index); };
        assert(krnl.prc_mp.perms_wf()) by { reveal(process_perms_wf); };
        assert(process_perms_wf(pre_krnl.prc_mp)) by { reveal(KernelK::inv); };
        assert(pagetable_perms_wf(pre_krnl.pt_mp)) by { reveal(KernelK::inv); };
        assert(pre_krnl.memory_management_inv()) by { reveal(KernelK::inv); };
        assert(krnl.prc_mp == pre_krnl.prc_mp);
        assert(process_perms_wf(krnl.prc_mp));
        assert(krnl.pt_mp == pre_krnl.pt_mp);
        assert(pagetable_perms_wf(krnl.pt_mp));
        assert(krnl.it_mp == pre_krnl.it_mp);
        assert(process_pages_wf(krnl.pg_arr, krnl.prc_mp)) by { reveal(process_pages_wf); };
        assert(process_pagetable_match(krnl.prc_mp, krnl.pt_mp));
        assert(process_iommu_table_match(krnl.prc_mp, krnl.it_mp));
        assert(krnl.dflt_pt.view().wf());
        assert(pei_valid(krnl.dflt_pt.view().kernel_l4_end));
        assert(typed_lock_maps_aligned(krnl, lctx)) by { reveal(typed_lock_maps_aligned); };
        assert(lock_id_set_aligned(lctx));
        assert({
            &&& krnl.pg_arr.spec_index(l4_index) == pre_krnl.pg_arr.spec_index(l4_index)
            &&& krnl.pg_arr.spec_index(pagetable_index) == pre_krnl.pg_arr.spec_index(pagetable_index)
            &&& krnl.pg_arr.spec_index(process_index) == pre_krnl.pg_arr.spec_index(process_index)
        }) by { reveal(new_container_bootstrap_4k_pages); reveal(new_container_moved_pages); };
        assert({
            &&& process_index != container_head
            &&& process_index != pcid_allocator_head
            &&& pagetable_index != container_head
            &&& pagetable_index != pcid_allocator_head
            &&& l4_index != container_head
            &&& l4_index != pcid_allocator_head
            &&& allocator_4k_index != container_head
            &&& allocator_4k_index != pcid_allocator_head
            &&& allocator_2m_index != container_head
            &&& allocator_2m_index != pcid_allocator_head
            &&& allocator_1g_index != container_head
            &&& allocator_1g_index != pcid_allocator_head
            &&& scheduler_index != container_head
            &&& scheduler_index != pcid_allocator_head
            &&& cpu_set_index != container_head
            &&& cpu_set_index != pcid_allocator_head
        }) by {
            assert(pre_krnl.pg_arr.spec_index(container_head).view().view().state is Owned2m);
            assert(pre_krnl.pg_arr.spec_index(pcid_allocator_head).view().view().state is Owned2m);
            assert(pre_krnl.pg_arr.spec_index(process_index).view().view().state is Owned4k);
            assert(pre_krnl.pg_arr.spec_index(pagetable_index).view().view().state is Owned4k);
            assert(pre_krnl.pg_arr.spec_index(l4_index).view().view().state is Owned4k);
            assert(pre_krnl.pg_arr.spec_index(allocator_4k_index).view().view().state is Owned4k);
            assert(pre_krnl.pg_arr.spec_index(allocator_2m_index).view().view().state is Owned4k);
            assert(pre_krnl.pg_arr.spec_index(allocator_1g_index).view().view().state is Owned4k);
            assert(pre_krnl.pg_arr.spec_index(scheduler_index).view().view().state is Owned4k);
            assert(pre_krnl.pg_arr.spec_index(cpu_set_index).view().view().state is Owned4k);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), process_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(process_index) == page_lock_map_after_backing_prepare.get(process_index));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), pagetable_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(pagetable_index) == page_lock_map_after_backing_prepare.get(pagetable_index));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), l4_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(l4_index) == page_lock_map_after_backing_prepare.get(l4_index));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), allocator_4k_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(allocator_4k_index) == page_lock_map_after_backing_prepare.get(allocator_4k_index));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), allocator_2m_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(allocator_2m_index) == page_lock_map_after_backing_prepare.get(allocator_2m_index));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), allocator_1g_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(allocator_1g_index) == page_lock_map_after_backing_prepare.get(allocator_1g_index));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), scheduler_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(scheduler_index) == page_lock_map_after_backing_prepare.get(scheduler_index));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), cpu_set_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(cpu_set_index) == page_lock_map_after_backing_prepare.get(cpu_set_index));
            reveal(typed_lock_map_contains_mode);
        };
        assert({
            &&& !funding_pages.to_set().contains(process_page)
            &&& !funding_pages.to_set().contains(pagetable_page)
            &&& !funding_pages.to_set().contains(l4_page)
        }) by { assert(funding_pages.to_set().disjoint(new_container_moved_pages(
            container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
            process_page, pagetable_page, l4_page,
        ),)); reveal(Set::disjoint); reveal(new_container_moved_pages); };
        assert(staged_4k_page_chain(krnl.pg_arr, funding_pages)) by {
            staged_4k_page_chain_page_ptrs_valid(pages_after_backing_prepare, funding_pages,);
            broadcast use page_ptr_sequence_index_in_equal_set; broadcast use page_ptr_sequence_index_in_mapped_set;
            reveal(staged_4k_page_chain);
        };
        assert(owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, krnl.pg_arr, lctx, container_head,)) by {
            assert(!page_2m_tail_indices(container_head).contains(container_head,));
            assert(!page_2m_tail_indices(container_head).contains(pcid_allocator_head,)); reveal(owned_2m_tail_lock_perms_wf);
            reveal(page_2m_tail_indices); reveal(Set::disjoint);
        };
        assert(owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, krnl.pg_arr, lctx, pcid_allocator_head,)) by {
            assert(!page_2m_tail_indices(pcid_allocator_head).contains(container_head,));
            assert(!page_2m_tail_indices(pcid_allocator_head).contains(pcid_allocator_head,)); reveal(owned_2m_tail_lock_perms_wf);
            reveal(page_2m_tail_indices); reveal(Set::disjoint);
        };
    }
    let (Tracked(child_process_lock_perm), Tracked(child_pagetable_lock_perm),) = publish_new_container_process_and_pagetable(
        krnl, child_container_ptr, child_process_ptr, child_pagetable_ptr, l4_page, root_pcid, child_depth, process_quota_4k,
        Ghost(funding_pages), container_head, pcid_allocator_head, Tracked(&mut *lctx), Tracked(process_page_lock_perm),
        Tracked(pagetable_page_lock_perm), Tracked(l4_page_lock_perm), Tracked(container_tail_lock_perms),
        Tracked(pcid_allocator_tail_lock_perms),
    );
    proof {
        assert(process_perms_wf(krnl.prc_mp));
        assert(pagetable_perms_wf(krnl.pt_mp));
        assert({
            &&& typed_lock_map_contains_mode(
                lctx.page_lock_map(),
                container_head,
                TypedLockMode::Write,
            )
            &&& typed_lock_map_contains_mode(
                lctx.page_lock_map(),
                pcid_allocator_head,
                TypedLockMode::Write,
            )
            &&& typed_lock_map_contains_mode(
                lctx.page_lock_map(),
                allocator_4k_index,
                TypedLockMode::Write,
            )
            &&& typed_lock_map_contains_mode(
                lctx.page_lock_map(),
                allocator_2m_index,
                TypedLockMode::Write,
            )
            &&& typed_lock_map_contains_mode(
                lctx.page_lock_map(),
                allocator_1g_index,
                TypedLockMode::Write,
            )
            &&& typed_lock_map_contains_mode(
                lctx.page_lock_map(),
                scheduler_index,
                TypedLockMode::Write,
            )
            &&& typed_lock_map_contains_mode(
                lctx.page_lock_map(),
                cpu_set_index,
                TypedLockMode::Write,
            )
            &&& typed_lock_map_contains_mode(
                lctx.page_lock_map(),
                process_index,
                TypedLockMode::Write,
            )
            &&& typed_lock_map_contains_mode(
                lctx.page_lock_map(),
                pagetable_index,
                TypedLockMode::Write,
            )
            &&& typed_lock_map_contains_mode(
                lctx.page_lock_map(),
                l4_index,
                TypedLockMode::Write,
            )
        }) by {
            assert(lctx.page_lock_map().get(container_head) == lctx_before_process_publish.page_lock_map().get(container_head,));
            assert(lctx.page_lock_map().get(pcid_allocator_head) == lctx_before_process_publish.page_lock_map().get(pcid_allocator_head,));
            assert(lctx.page_lock_map().get(allocator_4k_index) == lctx_before_process_publish.page_lock_map().get(allocator_4k_index,));
            assert(lctx.page_lock_map().get(allocator_2m_index) == lctx_before_process_publish.page_lock_map().get(allocator_2m_index,));
            assert(lctx.page_lock_map().get(allocator_1g_index) == lctx_before_process_publish.page_lock_map().get(allocator_1g_index,));
            assert(lctx.page_lock_map().get(scheduler_index) == lctx_before_process_publish.page_lock_map().get(scheduler_index,));
            assert(lctx.page_lock_map().get(cpu_set_index) == lctx_before_process_publish.page_lock_map().get(cpu_set_index,));
            reveal(typed_lock_map_contains_mode);
        };
    }

    let ghost pages_before_allocators = krnl.pg_arr;
    let ghost lctx_before_allocators = *lctx;
    proof {
        assert(seq![ allocator_4k_page, allocator_2m_page, allocator_1g_page, ].no_duplicates()) by { reveal(Seq::no_duplicates); };
        assert({
            &&& krnl.pg_arr.spec_index(allocator_4k_index).view().is_init()
            &&& krnl.pg_arr.spec_index(allocator_4k_index).view().view().perm_inv()
            &&& krnl.pg_arr.spec_index(allocator_4k_index).view().view().perm_4k.view().is_some()
            &&& krnl.pg_arr.spec_index(allocator_4k_index).view().view().state is Owned4k
            &&& krnl.pg_arr.spec_index(allocator_4k_index).view().view().addr == allocator_4k_page
            &&& allocator_4k_page_lock_perm.lock_id() == krnl.pg_arr.spec_index(allocator_4k_index).view().locking_thread()->Write_lock_id
            &&& krnl.pg_arr.spec_index(allocator_2m_index).view().is_init()
            &&& krnl.pg_arr.spec_index(allocator_2m_index).view().view().perm_inv()
            &&& krnl.pg_arr.spec_index(allocator_2m_index).view().view().perm_4k.view().is_some()
            &&& krnl.pg_arr.spec_index(allocator_2m_index).view().view().state is Owned4k
            &&& krnl.pg_arr.spec_index(allocator_2m_index).view().view().addr == allocator_2m_page
            &&& allocator_2m_page_lock_perm.lock_id() == krnl.pg_arr.spec_index(allocator_2m_index).view().locking_thread()->Write_lock_id
            &&& krnl.pg_arr.spec_index(allocator_1g_index).view().is_init()
            &&& krnl.pg_arr.spec_index(allocator_1g_index).view().view().perm_inv()
            &&& krnl.pg_arr.spec_index(allocator_1g_index).view().view().perm_4k.view().is_some()
            &&& krnl.pg_arr.spec_index(allocator_1g_index).view().view().state is Owned4k
            &&& krnl.pg_arr.spec_index(allocator_1g_index).view().view().addr == allocator_1g_page
            &&& allocator_1g_page_lock_perm.lock_id() == krnl.pg_arr.spec_index(allocator_1g_index).view().locking_thread()->Write_lock_id
        }) by { reveal(new_container_bootstrap_4k_pages); reveal(new_container_moved_pages); };
        assert({
            &&& typed_lock_map_contains_mode(
                lctx.page_lock_map(),
                allocator_4k_index,
                TypedLockMode::Write,
            )
            &&& typed_lock_map_contains_mode(
                lctx.page_lock_map(),
                allocator_2m_index,
                TypedLockMode::Write,
            )
            &&& typed_lock_map_contains_mode(
                lctx.page_lock_map(),
                allocator_1g_index,
                TypedLockMode::Write,
            )
            &&& typed_lock_map_contains_mode(
                lctx.page_lock_map(),
                scheduler_index,
                TypedLockMode::Write,
            )
            &&& typed_lock_map_contains_mode(
                lctx.page_lock_map(),
                cpu_set_index,
                TypedLockMode::Write,
            )
        }) by {
            assert(lctx_before_allocators.page_lock_map().get(allocator_4k_index,) == lctx_before_process_publish.page_lock_map().get(allocator_4k_index,));
            assert(lctx_before_allocators.page_lock_map().get(allocator_2m_index,) == lctx_before_process_publish.page_lock_map().get(allocator_2m_index,));
            assert(lctx_before_allocators.page_lock_map().get(allocator_1g_index,) == lctx_before_process_publish.page_lock_map().get(allocator_1g_index,));
            assert(lctx_before_allocators.page_lock_map().get(scheduler_index,) == lctx_before_process_publish.page_lock_map().get(scheduler_index,));
            assert(lctx_before_allocators.page_lock_map().get(cpu_set_index,) == lctx_before_process_publish.page_lock_map().get(cpu_set_index,));
            reveal(typed_lock_map_contains_mode);
        };
    }
    proof {
        assert(allocator_perms_wf(pre_krnl.allc_4k_mp)) by { reveal(KernelK::inv); };
        assert(allocator_perms_wf(pre_krnl.allc_2m_mp)) by { reveal(KernelK::inv); };
        assert(allocator_perms_wf(pre_krnl.allc_1g_mp)) by { reveal(KernelK::inv); };
        assert(krnl.allc_4k_mp == pre_krnl.allc_4k_mp);
        assert(krnl.allc_2m_mp == pre_krnl.allc_2m_mp);
        assert(krnl.allc_1g_mp == pre_krnl.allc_1g_mp);
        assert(allocator_perms_wf(krnl.allc_4k_mp));
        assert(allocator_perms_wf(krnl.allc_2m_mp));
        assert(allocator_perms_wf(krnl.allc_1g_mp));
        assert(krnl.allc_4k_mp.perms_wf()) by { reveal(allocator_perms_wf); };
        assert(krnl.allc_2m_mp.perms_wf()) by { reveal(allocator_perms_wf); };
        assert(krnl.allc_1g_mp.perms_wf()) by { reveal(allocator_perms_wf); };
        assert(krnl.pg_arr.typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id(),)) by { reveal(typed_lock_maps_aligned); };
        assert(krnl.allc_4k_mp.typed_quota_lock_map_aligned(lctx.allocator_quota_4k_lock_map(), lctx.thread_id(),)) by { reveal(typed_lock_maps_aligned); };
        assert(krnl.allc_4k_mp.typed_cache_lock_map_aligned(lctx.allocator_cache_4k_lock_map(), lctx.thread_id(),)) by { reveal(typed_lock_maps_aligned); };
        assert(krnl.allc_4k_mp.typed_global_pool_lock_map_aligned(lctx.allocator_global_pool_4k_lock_map(), lctx.thread_id(),)) by { reveal(typed_lock_maps_aligned); };
        assert(krnl.allc_2m_mp.typed_quota_lock_map_aligned(lctx.allocator_quota_2m_lock_map(), lctx.thread_id(),)) by { reveal(typed_lock_maps_aligned); };
        assert(krnl.allc_2m_mp.typed_cache_lock_map_aligned(lctx.allocator_cache_2m_lock_map(), lctx.thread_id(),)) by { reveal(typed_lock_maps_aligned); };
        assert(krnl.allc_2m_mp.typed_global_pool_lock_map_aligned(lctx.allocator_global_pool_2m_lock_map(), lctx.thread_id(),)) by { reveal(typed_lock_maps_aligned); };
        assert(krnl.allc_1g_mp.typed_quota_lock_map_aligned(lctx.allocator_quota_1g_lock_map(), lctx.thread_id(),)) by { reveal(typed_lock_maps_aligned); };
        assert(krnl.allc_1g_mp.typed_cache_lock_map_aligned(lctx.allocator_cache_1g_lock_map(), lctx.thread_id(),)) by { reveal(typed_lock_maps_aligned); };
        assert(krnl.allc_1g_mp.typed_global_pool_lock_map_aligned(lctx.allocator_global_pool_1g_lock_map(), lctx.thread_id(),)) by { reveal(typed_lock_maps_aligned); };
        assert(allocator_4k_page != allocator_2m_page);
        assert(allocator_4k_page != allocator_1g_page);
        assert(allocator_2m_page != allocator_1g_page);
        page_ptr2page_index_neq(allocator_4k_page, allocator_2m_page);
        page_ptr2page_index_neq(allocator_4k_page, allocator_1g_page);
        page_ptr2page_index_neq(allocator_2m_page, allocator_1g_page);
        assert(allocator_4k_index != allocator_2m_index);
        assert(allocator_4k_index != allocator_1g_index);
        assert(allocator_2m_index != allocator_1g_index);
    }
    publish_new_container_allocators(
        &mut krnl.pg_arr, &mut krnl.allc_4k_mp, &mut krnl.allc_2m_mp, &mut krnl.allc_1g_mp, child_container_ptr, allocator_4k_page,
        allocator_2m_page, allocator_1g_page, allocator_4k_value, allocator_2m_value, allocator_1g_value, Tracked(&mut *lctx),
        Tracked(allocator_4k_page_lock_perm), Tracked(allocator_2m_page_lock_perm), Tracked(allocator_1g_page_lock_perm),
    );
    proof {
        assert(typed_lock_maps_aligned(krnl, lctx)) by { reveal(typed_lock_maps_aligned); };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), container_head, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(container_head) == lctx_before_allocators.page_lock_map().get(container_head));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), pcid_allocator_head, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(pcid_allocator_head) == lctx_before_allocators.page_lock_map().get(pcid_allocator_head));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), process_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(process_index) == lctx_before_allocators.page_lock_map().get(process_index));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), pagetable_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(pagetable_index) == lctx_before_allocators.page_lock_map().get(pagetable_index));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), l4_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(l4_index) == lctx_before_allocators.page_lock_map().get(l4_index));
            reveal(typed_lock_map_contains_mode);
        };
        assert(lctx.page_lock_map().get(scheduler_index) == lctx_before_allocators.page_lock_map().get(scheduler_index));
        assert(lctx.page_lock_map().get(cpu_set_index) == lctx_before_allocators.page_lock_map().get(cpu_set_index));
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), scheduler_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(scheduler_index) == lctx_before_allocators.page_lock_map().get(scheduler_index));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), cpu_set_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(cpu_set_index) == lctx_before_allocators.page_lock_map().get(cpu_set_index));
            reveal(typed_lock_map_contains_mode);
        };
        assert(staged_4k_page_chain(krnl.pg_arr, funding_pages)) by {
            staged_4k_page_chain_page_ptrs_valid(pages_before_allocators, funding_pages,);
            broadcast use page_ptr_sequence_index_in_equal_set; broadcast use page_ptr_sequence_index_in_mapped_set;
            reveal(staged_4k_page_chain);
        };
        assert(owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, krnl.pg_arr, lctx, container_head,)) by { reveal(owned_2m_tail_lock_perms_wf); reveal(page_2m_tail_indices); reveal(typed_lock_map_contains_mode); };
        assert(owned_2m_tail_lock_perms_wf( *pcid_allocator_tail_lock_perms, krnl.pg_arr, lctx, pcid_allocator_head,
        )) by { reveal(owned_2m_tail_lock_perms_wf); reveal(page_2m_tail_indices); reveal(typed_lock_map_contains_mode); };
    }

    let ghost pages_before_scheduler = krnl.pg_arr;
    let ghost lctx_before_scheduler = *lctx;
    proof {
        assert(scheduler_index != allocator_4k_index);
        assert(scheduler_index != allocator_2m_index);
        assert(scheduler_index != allocator_1g_index);
        assert(krnl.pg_arr.spec_index(scheduler_index) == pages_before_allocators.spec_index(scheduler_index));
        assert(krnl.pg_arr.spec_index(scheduler_index).view().is_init()) by { reveal(new_container_bootstrap_4k_pages); reveal(new_container_moved_pages); };
        assert(krnl.pg_arr.spec_index(scheduler_index).view().view().perm_inv()) by { reveal(new_container_bootstrap_4k_pages); reveal(new_container_moved_pages); };
        assert(krnl.pg_arr.spec_index(scheduler_index).view().view().perm_4k.view().is_some()) by { reveal(new_container_bootstrap_4k_pages); reveal(new_container_moved_pages); };
        assert(krnl.pg_arr.spec_index(scheduler_index).view().view().state is Owned4k) by { reveal(new_container_bootstrap_4k_pages); reveal(new_container_moved_pages); };
        assert(krnl.pg_arr.spec_index(scheduler_index).view().view().addr == scheduler_page) by { reveal(new_container_bootstrap_4k_pages); reveal(new_container_moved_pages); };
        assert(scheduler_page_lock_perm.lock_id() == krnl.pg_arr.spec_index(scheduler_index).view().locking_thread()->Write_lock_id) by { reveal(new_container_bootstrap_4k_pages); reveal(new_container_moved_pages); };
        assert(krnl.sched_mp == pre_krnl.sched_mp);
        assert(scheduler_perms_wf(pre_krnl.sched_mp)) by { reveal(KernelK::inv); };
        assert(scheduler_perms_wf(krnl.sched_mp));
    }
    let Tracked(child_scheduler_lock_perm) =
        publish_new_container_scheduler(
            krnl, child_container_ptr, child_scheduler_ptr, scheduler_page, cpu_set_index, scheduler_value, Ghost(funding_pages),
            container_head, pcid_allocator_head, Tracked(&mut *lctx), Tracked(scheduler_page_lock_perm), Tracked(container_tail_lock_perms),
            Tracked(pcid_allocator_tail_lock_perms),
        );
    proof {
        assert(scheduler_perms_wf(krnl.sched_mp));
        assert(krnl.pg_arr.typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id(),)) by { reveal(typed_lock_maps_aligned); };
        assert(krnl.pg_arr.spec_index(cpu_set_index) == pages_before_scheduler.spec_index(cpu_set_index));
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), container_head, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(container_head) == lctx_before_scheduler.page_lock_map().get(container_head,));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), pcid_allocator_head, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(pcid_allocator_head) == lctx_before_scheduler.page_lock_map().get(pcid_allocator_head,));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), allocator_4k_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(allocator_4k_index) == lctx_before_scheduler.page_lock_map().get(allocator_4k_index,));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), allocator_2m_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(allocator_2m_index) == lctx_before_scheduler.page_lock_map().get(allocator_2m_index,));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), allocator_1g_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(allocator_1g_index) == lctx_before_scheduler.page_lock_map().get(allocator_1g_index,));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), process_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(process_index) == lctx_before_scheduler.page_lock_map().get(process_index,));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), pagetable_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(pagetable_index) == lctx_before_scheduler.page_lock_map().get(pagetable_index,));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), l4_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(l4_index) == lctx_before_scheduler.page_lock_map().get(l4_index));
            reveal(typed_lock_map_contains_mode);
        };
    }

    let cpu_set_value = CpuSet::new_empty(child_container_ptr, child_depth);
    proof {
        assert(pages_before_scheduler.spec_index(cpu_set_index) == pages_before_allocators.spec_index(cpu_set_index));
        assert(krnl.pg_arr.spec_index(cpu_set_index).view().is_init()) by { reveal(new_container_bootstrap_4k_pages); reveal(new_container_moved_pages); };
        assert(krnl.pg_arr.spec_index(cpu_set_index).view().view().perm_inv()) by { reveal(new_container_bootstrap_4k_pages); reveal(new_container_moved_pages); };
        assert(krnl.pg_arr.spec_index(cpu_set_index).view().view().perm_4k.view().is_some()) by { reveal(new_container_bootstrap_4k_pages); reveal(new_container_moved_pages); };
        assert(krnl.pg_arr.spec_index(cpu_set_index).view().view().state is Owned4k) by { reveal(new_container_bootstrap_4k_pages); reveal(new_container_moved_pages); };
        assert(krnl.pg_arr.spec_index(cpu_set_index).view().view().addr == cpu_set_page) by { reveal(new_container_bootstrap_4k_pages); reveal(new_container_moved_pages); };
        assert(cpu_set_page_lock_perm.lock_id() == krnl.pg_arr.spec_index(cpu_set_index).view().locking_thread()->Write_lock_id) by { reveal(new_container_bootstrap_4k_pages); reveal(new_container_moved_pages); };
        assert(cpu_set_perms_wf(pre_krnl.cpu_set_mp)) by { reveal(KernelK::inv); };
        assert(krnl.cpu_set_mp == pre_krnl.cpu_set_mp);
        assert(cpu_set_perms_wf(krnl.cpu_set_mp));
        assert(krnl.cpu_set_mp.perms_wf()) by { reveal(cpu_set_perms_wf); };
    }
    let ghost lctx_before_cpu_set = *lctx;
    proof { assert(typed_lock_map_contains_mode(lctx_before_cpu_set.scheduler_lock_map(), scheduler_page, TypedLockMode::Write,)); }
    publish_new_container_cpu_set(
        krnl, child_container_ptr, child_cpu_set_ptr, cpu_set_page, cpu_set_value, Ghost(funding_pages), container_head,
        pcid_allocator_head, Tracked(&mut *lctx), Tracked(cpu_set_page_lock_perm), Tracked(container_tail_lock_perms),
        Tracked(pcid_allocator_tail_lock_perms),
    );
    let ghost page_lock_map_after_cpu_set = lctx.page_lock_map();
    proof {
        assert(cpu_set_perms_wf(krnl.cpu_set_mp));
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), container_head, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(container_head) == lctx_before_cpu_set.page_lock_map().get(container_head,));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), pcid_allocator_head, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(pcid_allocator_head) == lctx_before_cpu_set.page_lock_map().get(pcid_allocator_head,));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), allocator_4k_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(allocator_4k_index) == lctx_before_cpu_set.page_lock_map().get(allocator_4k_index,));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), allocator_2m_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(allocator_2m_index) == lctx_before_cpu_set.page_lock_map().get(allocator_2m_index,));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), allocator_1g_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(allocator_1g_index) == lctx_before_cpu_set.page_lock_map().get(allocator_1g_index,));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), scheduler_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(scheduler_index) == lctx_before_cpu_set.page_lock_map().get(scheduler_index,));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), cpu_set_index, TypedLockMode::Write,));
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), process_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(process_index) == lctx_before_cpu_set.page_lock_map().get(process_index,));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), pagetable_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(pagetable_index) == lctx_before_cpu_set.page_lock_map().get(pagetable_index,));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), l4_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(l4_index) == lctx_before_cpu_set.page_lock_map().get(l4_index));
            reveal(typed_lock_map_contains_mode);
        };
    }

    let mut container_value = Container::new_staged(
        child_container_ptr,
        child_process_ptr,
        child_depth,
    );
    container_value.owned_processes = Ghost(Set::empty().insert(child_process_ptr));
    container_value.owned_pages = Ghost(moved_pages);
    let container_rodata = ReadOnlyNode::new(
        ContainerRO {
            parent: Some(parent_container_ptr),
            depth: child_depth,
            scheduler: child_scheduler_ptr,
            pcid_allocator: child_pcid_allocator_ptr,
            cpu_set: child_cpu_set_ptr,
            allocator_ptr_4k: child_allocator_4k_ptr,
            allocator_ptr_2m: child_allocator_2m_ptr,
            allocator_ptr_1g: child_allocator_1g_ptr,
        },
        Ghost(child_container_ptr),
    );
    let container_ghost = ContainerGhost {
        uppertree_seq: Ghost(child_uppers),
        subtree_set: Ghost(Set::empty()),
        owned_threads: Ghost(Set::empty()),
        owned_indirect_threads: Ghost(Set::empty()),
    };
    let ghost container_lock_map_before_child_insert =
        lctx.container_lock_map();
    let ghost lctx_before_pcid_and_container = *lctx;
    proof {
        assert(pcid_allocator_perms_wf(pre_krnl.pcid_allc_mp)) by { reveal(KernelK::inv); };
        assert(krnl.pcid_allc_mp == pre_krnl.pcid_allc_mp);
        assert(pcid_allocator_perms_wf(krnl.pcid_allc_mp));
        assert(krnl.pcid_allc_mp.perms_wf()) by { reveal(pcid_allocator_perms_wf); };
    }
    let (Tracked(child_pcid_allocator_lock_perm), Tracked(child_container_lock_perm),) = publish_new_container_pcid_allocator_and_container(
        krnl, child_pcid_allocator_ptr, pcid_allocator_value, child_container_ptr, container_value, container_rodata, container_ghost,
        Tracked(&mut *lctx), Tracked(pcid_allocator_perm), Tracked(container_perm),
    );
    proof { assert(pcid_allocator_perms_wf(krnl.pcid_allc_mp)); }

    proof {
        assert(container_perms_wf(pre_krnl.ctn_mp)) by { reveal(KernelK::inv); };
        assert(container_tree_wf(pre_krnl.rt_ctn, pre_krnl.ctn_mp)) by { reveal(KernelK::inv); };
        assert(container_pages_wf(pre_krnl.pg_arr, pre_krnl.ctn_mp)) by { reveal(KernelK::inv); };
        assert(child_uppers.to_set().subset_of(pre_krnl.ctn_mp.dom()));
        assert(!child_uppers.to_set().contains(child_container_ptr)) by {
            if child_uppers.to_set().contains(child_container_ptr) {
                assert(pre_krnl.ctn_mp.dom().contains(child_container_ptr));
            }
        };
        assert(moved_pages.subset_of(pre_krnl.ctn_mp.spec_index(parent_container_ptr).view().owned_pages.view(),)) by { reveal(new_container_moved_pages); };
        assert(krnl.ctn_mp.typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id(),)) by { reveal(typed_lock_maps_aligned); };
        assert(typed_lock_map_contains_mode(lctx.container_lock_map(), parent_container_ptr, TypedLockMode::Write,)) by {
            assert(parent_container_ptr != child_container_ptr);
            assert(lctx.container_lock_map().get(parent_container_ptr) == container_lock_map_before_child_insert.get(parent_container_ptr,));
            reveal(typed_lock_map_contains_mode);
        };
    }
    link_new_container_into_tree(
        &mut krnl.ctn_mp, krnl.rt_ctn, parent_container_ptr, child_container_ptr, child_process_ptr, child_scheduler_ptr,
        child_pcid_allocator_ptr, child_cpu_set_ptr, child_allocator_4k_ptr, child_allocator_2m_ptr, child_allocator_1g_ptr, child_depth,
        thread_page, Ghost(child_uppers), Ghost(moved_pages), Ghost(pre_krnl.ctn_mp), Ghost(pre_krnl.pg_arr), Tracked(&*lctx),
        Tracked(parent_container_lock_perm), Tracked(&child_container_lock_perm),
    );
    proof {
        assert(typed_lock_maps_aligned(krnl, lctx)) by { reveal(typed_lock_maps_aligned); };
    }
    proof {
        let ghost consumed_4k_pages =
            bootstrap_pages.union(funding_pages.to_set());
        let ghost initial_cache = krnl.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view();
        assert(initial_cache == consumed_4k_pages.insert(thread_page)) by { vstd::set::axiom_set_ext_equal(initial_cache, consumed_4k_pages.insert(thread_page),); };
        assert(thread_perms_wf(krnl.thr_mp)) by { reveal(KernelK::inv); reveal(thread_perms_wf); };
        thread_perms_wf_at(krnl.thr_mp, current_thread_ptr);
        funding_pages.unique_seq_to_set();
        assert(bootstrap_pages.disjoint(funding_pages.to_set())) by { reveal(Set::disjoint); reveal(new_container_moved_pages); };
        vstd::set_lib::lemma_set_disjoint_lens(bootstrap_pages, funding_pages.to_set(),);
        assert(consumed_4k_pages.len() == 8 + funding_page_count);
        assert(!consumed_4k_pages.contains(thread_page)) by { broadcast use vstd::set::lemma_set_union; };
        vstd::set::lemma_set_insert_len(consumed_4k_pages, thread_page,);
        assert(initial_cache.len() == 9 + funding_page_count);
        let ghost initial_2m_cache = krnl.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view();
        assert(initial_2m_cache =~= set![container_page, pcid_allocator_page]) by { vstd::set::axiom_set_ext_equal(initial_2m_cache, set![container_page, pcid_allocator_page],); };
        assert(initial_2m_cache.len() == 2) by { broadcast use vstd::set::lemma_set_empty_len; broadcast use vstd::set::lemma_set_insert_len; broadcast use vstd::set::lemma_set_contains_len; };
        assert(krnl.thr_mp.spec_index(current_thread_ptr).view().quota_4k >= initial_cache.len()) by { reveal(Thread::quota_within_bound); };
        assert(funding_page_count < krnl.thr_mp.spec_index(current_thread_ptr).view().quota_4k - 8);
        assert(krnl.thr_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id(),)) by { reveal(typed_lock_maps_aligned); };
    }
    consume_new_container_thread_staging(&mut krnl.thr_mp, current_thread_ptr, thread_page, funding_page_count, Ghost(bootstrap_pages.union(funding_pages.to_set())), Tracked(&*lctx), Tracked(current_thread_lock_perm),);
    proof {
        assert(thread_perms_wf(krnl.thr_mp));
        thread_perms_wf_at(krnl.thr_mp, current_thread_ptr);
        assert(lctx.page_lock_map() == page_lock_map_after_cpu_set);
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), container_head, TypedLockMode::Write,)) by { reveal(typed_lock_map_contains_mode); };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), pcid_allocator_head, TypedLockMode::Write,)) by { reveal(typed_lock_map_contains_mode); };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), allocator_4k_index, TypedLockMode::Write,)) by { reveal(typed_lock_map_contains_mode); };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), allocator_2m_index, TypedLockMode::Write,)) by { reveal(typed_lock_map_contains_mode); };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), allocator_1g_index, TypedLockMode::Write,)) by { reveal(typed_lock_map_contains_mode); };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), scheduler_index, TypedLockMode::Write,)) by { reveal(typed_lock_map_contains_mode); };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), cpu_set_index, TypedLockMode::Write,)) by { reveal(typed_lock_map_contains_mode); };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), process_index, TypedLockMode::Write,)) by { reveal(typed_lock_map_contains_mode); };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), pagetable_index, TypedLockMode::Write,)) by { reveal(typed_lock_map_contains_mode); };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), l4_index, TypedLockMode::Write,)) by { reveal(typed_lock_map_contains_mode); };
        assert(container_page_lock_perm.lock_id() == krnl.pg_arr.spec_index(container_head).view().locking_thread()->Write_lock_id);
        assert(pcid_allocator_page_lock_perm.lock_id() == krnl.pg_arr.spec_index(pcid_allocator_head).view().locking_thread()->Write_lock_id);
        assert(allocator_4k_page_lock_perm.lock_id() == krnl.pg_arr.spec_index(allocator_4k_index).view().locking_thread()->Write_lock_id);
        assert(allocator_2m_page_lock_perm.lock_id() == krnl.pg_arr.spec_index(allocator_2m_index).view().locking_thread()->Write_lock_id);
        assert(allocator_1g_page_lock_perm.lock_id() == krnl.pg_arr.spec_index(allocator_1g_index).view().locking_thread()->Write_lock_id);
        assert(scheduler_page_lock_perm.lock_id() == krnl.pg_arr.spec_index(scheduler_index).view().locking_thread()->Write_lock_id);
        assert(cpu_set_page_lock_perm.lock_id() == krnl.pg_arr.spec_index(cpu_set_index).view().locking_thread()->Write_lock_id);
        assert(process_page_lock_perm.lock_id() == krnl.pg_arr.spec_index(process_index).view().locking_thread()->Write_lock_id);
        assert(pagetable_page_lock_perm.lock_id() == krnl.pg_arr.spec_index(pagetable_index).view().locking_thread()->Write_lock_id);
        assert(l4_page_lock_perm.lock_id() == krnl.pg_arr.spec_index(l4_index).view().locking_thread()->Write_lock_id);
        assert forall|page_ptr: PagePtr|
            #![trigger funding_page_lock_perms.dom().contains(page_ptr)]
            funding_page_lock_perms.dom().contains(page_ptr) implies {
                &&& krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Free4k {
                    allocator_ptr: Ghost(allocator_4k_page),
                    state: FreePageAllocatorState::GlobalList,
                })
                &&& krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == container_page
                &&& typed_lock_map_contains_mode(
                    lctx.page_lock_map(),
                    page_ptr2page_index(page_ptr),
                    TypedLockMode::Write,
                )
                &&& funding_page_lock_perms.spec_index(page_ptr).lock_id() == krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id
            } by {
            let page_index = page_ptr2page_index(page_ptr);
            reveal(new_container_moved_pages);
            page_ptr2page_index_neq(page_ptr, container_page);
            page_ptr2page_index_neq(page_ptr, pcid_allocator_page);
            page_ptr2page_index_neq(page_ptr, allocator_4k_page);
            page_ptr2page_index_neq(page_ptr, allocator_2m_page);
            page_ptr2page_index_neq(page_ptr, allocator_1g_page);
            page_ptr2page_index_neq(page_ptr, scheduler_page);
            page_ptr2page_index_neq(page_ptr, cpu_set_page);
            page_ptr2page_index_neq(page_ptr, process_page);
            page_ptr2page_index_neq(page_ptr, pagetable_page);
            page_ptr2page_index_neq(page_ptr, l4_page);
            assert(lctx_before_process_publish.page_lock_map().get(page_index) == page_lock_map_after_backing_prepare.get(page_index));
            assert(lctx_before_allocators.page_lock_map().get(page_index) == lctx_before_process_publish.page_lock_map().get(page_index,));
            assert(page_lock_map_after_cpu_set.get(page_index) == lctx_before_cpu_set.page_lock_map().get(page_index));
            assert(lctx_before_cpu_set.page_lock_map().get(page_index) == lctx_before_scheduler.page_lock_map().get(page_index));
            assert(lctx_before_scheduler.page_lock_map().get(page_index) == lctx_before_allocators.page_lock_map().get(page_index));
            assert(lctx.page_lock_map().get(page_index) == page_lock_map_after_cpu_set.get(page_index));
            reveal(typed_lock_map_contains_mode);
        };
    }

    proof {
        assert(!funding_indices.contains(page_ptr2page_index(thread_page),)) by { staged_4k_page_chain_page_ptrs_valid(krnl.pg_arr, funding_pages,); page_ptr_seq_indices_excludes_page(funding_pages, thread_page); };
        assert(lctx.page_lock_map().get(page_ptr2page_index(thread_page)) == old(lctx).page_lock_map().get(page_ptr2page_index(thread_page))) by {
            let thread_page_index = page_ptr2page_index(thread_page);
            assert({
                &&& thread_page_index != process_index
                &&& thread_page_index != pagetable_index
                &&& thread_page_index != l4_index
            }) by { reveal(new_container_moved_pages); page_ptr2page_index_neq(thread_page, process_page); page_ptr2page_index_neq(thread_page, pagetable_page); page_ptr2page_index_neq(thread_page, l4_page); };
            assert(lctx_before_process_publish.page_lock_map().get(thread_page_index) == page_lock_map_after_backing_prepare.get(thread_page_index));
            assert(lctx_before_allocators.page_lock_map().get(thread_page_index,) == lctx_before_process_publish.page_lock_map().get(thread_page_index,));
            assert(page_lock_map_after_cpu_set.get(thread_page_index) == lctx_before_cpu_set.page_lock_map().get(thread_page_index,));
            assert(lctx_before_cpu_set.page_lock_map().get(thread_page_index) == lctx_before_scheduler.page_lock_map().get(thread_page_index,));
            assert(lctx_before_scheduler.page_lock_map().get(thread_page_index) == lctx_before_allocators.page_lock_map().get(thread_page_index,));
            assert(lctx.page_lock_map().get(thread_page_index) == page_lock_map_after_cpu_set.get(thread_page_index));
            reveal(new_container_moved_pages);
            page_ptr2page_index_neq(thread_page, container_page);
            page_ptr2page_index_neq(thread_page, pcid_allocator_page);
            page_ptr2page_index_neq(thread_page, allocator_4k_page);
            page_ptr2page_index_neq(thread_page, allocator_2m_page);
            page_ptr2page_index_neq(thread_page, allocator_1g_page);
            page_ptr2page_index_neq(thread_page, scheduler_page);
            page_ptr2page_index_neq(thread_page, cpu_set_page);
        };
        assert(typed_lock_maps_aligned(krnl, lctx)) by { reveal(typed_lock_maps_aligned); };
        reveal(Seq::contains);
        assert(lctx_before_pcid_and_container.page_lock_map().dom() == old(lctx).page_lock_map().dom()) by {
            assert(page_lock_map_after_backing_prepare.dom() == old(lctx).page_lock_map().dom());
            assert(lctx_before_process_publish.page_lock_map().dom() == page_lock_map_after_backing_prepare.dom());
            assert(lctx_before_allocators.page_lock_map().dom() == lctx_before_process_publish.page_lock_map().dom());
            assert(lctx_before_scheduler.page_lock_map().dom() == lctx_before_allocators.page_lock_map().dom());
            assert(lctx_before_cpu_set.page_lock_map().dom() == lctx_before_scheduler.page_lock_map().dom());
            assert(lctx_before_pcid_and_container.page_lock_map().dom() == lctx_before_cpu_set.page_lock_map().dom());
        };
        assert(lctx_before_pcid_and_container.container_lock_map() == old(lctx).container_lock_map()) by {
            assert(lctx_before_process_publish.container_lock_map() == old(lctx).container_lock_map());
            assert(lctx_before_allocators.container_lock_map() == lctx_before_process_publish.container_lock_map());
            assert(lctx_before_scheduler.container_lock_map() == lctx_before_allocators.container_lock_map());
            assert(lctx_before_cpu_set.container_lock_map() == lctx_before_scheduler.container_lock_map());
            assert(lctx_before_pcid_and_container.container_lock_map() == lctx_before_cpu_set.container_lock_map());
        };
        assert(lctx_before_pcid_and_container.process_lock_map().dom() == old(lctx).process_lock_map().dom().insert(process_page)) by {
            assert(lctx_before_process_publish.process_lock_map() == old(lctx).process_lock_map());
            assert(lctx_before_allocators.process_lock_map().dom() == lctx_before_process_publish.process_lock_map().dom().insert(process_page));
            assert(lctx_before_scheduler.process_lock_map() == lctx_before_allocators.process_lock_map());
            assert(lctx_before_cpu_set.process_lock_map() == lctx_before_scheduler.process_lock_map());
            assert(lctx_before_pcid_and_container.process_lock_map() == lctx_before_cpu_set.process_lock_map());
        };
        assert(lctx_before_pcid_and_container.scheduler_lock_map().dom() == old(lctx).scheduler_lock_map().dom().insert(scheduler_page)) by {
            assert(lctx_before_scheduler.scheduler_lock_map() == lctx_before_allocators.scheduler_lock_map());
            assert(lctx_before_allocators.scheduler_lock_map() == lctx_before_process_publish.scheduler_lock_map());
            assert(lctx_before_process_publish.scheduler_lock_map() == old(lctx).scheduler_lock_map());
            assert(lctx_before_cpu_set.scheduler_lock_map().dom() == lctx_before_scheduler.scheduler_lock_map().dom().insert(scheduler_page));
            assert(lctx_before_pcid_and_container.scheduler_lock_map() == lctx_before_cpu_set.scheduler_lock_map());
        };
        assert(lctx_before_pcid_and_container.pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map()) by {
            assert(lctx_before_process_publish.pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map());
            assert(lctx_before_allocators.pcid_allocator_lock_map() == lctx_before_process_publish.pcid_allocator_lock_map());
            assert(lctx_before_scheduler.pcid_allocator_lock_map() == lctx_before_allocators.pcid_allocator_lock_map());
            assert(lctx_before_cpu_set.pcid_allocator_lock_map() == lctx_before_scheduler.pcid_allocator_lock_map());
            assert(lctx_before_pcid_and_container.pcid_allocator_lock_map() == lctx_before_cpu_set.pcid_allocator_lock_map());
        };
        assert(lctx_before_pcid_and_container.pagetable_lock_map().dom() == old(lctx).pagetable_lock_map().dom().insert(pagetable_page)) by {
            assert(lctx_before_process_publish.pagetable_lock_map() == old(lctx).pagetable_lock_map());
            assert(lctx_before_allocators.pagetable_lock_map().dom() == lctx_before_process_publish.pagetable_lock_map().dom().insert(pagetable_page));
            assert(lctx_before_scheduler.pagetable_lock_map() == lctx_before_allocators.pagetable_lock_map());
            assert(lctx_before_cpu_set.pagetable_lock_map() == lctx_before_scheduler.pagetable_lock_map());
            assert(lctx_before_pcid_and_container.pagetable_lock_map() == lctx_before_cpu_set.pagetable_lock_map());
        };
        assert(lctx.page_lock_map() == lctx_before_pcid_and_container.page_lock_map());
        assert(lctx.process_lock_map() == lctx_before_pcid_and_container.process_lock_map());
        assert(lctx.scheduler_lock_map() == lctx_before_pcid_and_container.scheduler_lock_map());
        assert(lctx.pagetable_lock_map() == lctx_before_pcid_and_container.pagetable_lock_map());
        assert(lctx.container_lock_map().dom() == lctx_before_pcid_and_container.container_lock_map().dom().insert(container_page));
        assert(lctx.pcid_allocator_lock_map().dom() == lctx_before_pcid_and_container.pcid_allocator_lock_map().dom().insert(pcid_allocator_page));
        assert(*krnl == (KernelK {
            pt_mp: krnl.pt_mp,
            pg_arr: krnl.pg_arr,
            ctn_mp: krnl.ctn_mp,
            sched_mp: krnl.sched_mp,
            pcid_allc_mp: krnl.pcid_allc_mp,
            cpu_set_mp: krnl.cpu_set_mp,
            prc_mp: krnl.prc_mp,
            thr_mp: krnl.thr_mp,
            allc_4k_mp: krnl.allc_4k_mp,
            allc_2m_mp: krnl.allc_2m_mp,
            allc_1g_mp: krnl.allc_1g_mp,
            ..*old(krnl)
        }));
        assert(lctx.cpu_id() == old(lctx).cpu_id());
        assert(lctx.thread_id() == old(lctx).thread_id());
        assert(lctx.kernel_view_locking_state() is Release);
        assert(lock_id_set_aligned(lctx));
        assert(lctx.allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps());
        assert(lctx.allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps());
        assert(lctx.allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps());
        assert(lctx.page_lock_map().dom() == old(lctx).page_lock_map().dom());
        assert(lctx.cpu_lock_map() == old(lctx).cpu_lock_map());
        assert(lctx.pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map());
        assert(lctx.container_lock_map().dom() == old(lctx).container_lock_map().dom().insert(container_page));
        assert(lctx.process_lock_map().dom() == old(lctx).process_lock_map().dom().insert(process_page));
        assert(lctx.thread_lock_map() == old(lctx).thread_lock_map());
        assert(lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map());
        assert(lctx.scheduler_lock_map().dom() == old(lctx).scheduler_lock_map().dom().insert(scheduler_page));
        assert(lctx.pcid_allocator_lock_map().dom() == old(lctx).pcid_allocator_lock_map().dom().insert(pcid_allocator_page));
        assert(lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map());
        assert(lctx.pagetable_lock_map().dom() == old(lctx).pagetable_lock_map().dom().insert(pagetable_page));
        assert(lctx.iommu_table_lock_map() == old(lctx).iommu_table_lock_map());
        assert(typed_lock_map_contains_mode(lctx.thread_lock_map(), current_thread_ptr, TypedLockMode::Write));
        assert(krnl.thr_mp.spec_index(current_thread_ptr).locking_thread() is Write) by {
            reveal(typed_lock_maps_aligned); reveal(LockedMap::typed_lock_map_aligned);
        };
        assert({
            &&& owned_2m_tail_lock_perms_wf( *container_tail_lock_perms,
                krnl.pg_arr,
                lctx,
                container_head,
            )
            &&& owned_2m_tail_lock_perms_wf( *pcid_allocator_tail_lock_perms,
                krnl.pg_arr,
                lctx,
                pcid_allocator_head,
            )
            &&& child_container_lock_perm.state() is WriteLock
            &&& child_container_lock_perm.thread_id() == lctx.thread_id()
            &&& child_container_lock_perm.lock_id() == krnl.ctn_mp.spec_index(container_page).locking_thread()->Write_lock_id
            &&& child_process_lock_perm.state() is WriteLock
            &&& child_process_lock_perm.thread_id() == lctx.thread_id()
            &&& child_process_lock_perm.lock_id() == krnl.prc_mp.spec_index(process_page).locking_thread()->Write_lock_id
            &&& child_pagetable_lock_perm.state() is WriteLock
            &&& child_pagetable_lock_perm.thread_id() == lctx.thread_id()
            &&& child_pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(pagetable_page).locking_thread()->Write_lock_id
            &&& child_scheduler_lock_perm.state() is WriteLock
            &&& child_scheduler_lock_perm.thread_id() == lctx.thread_id()
            &&& child_scheduler_lock_perm.lock_id() == krnl.sched_mp.spec_index(scheduler_page).locking_thread()->Write_lock_id
            &&& child_pcid_allocator_lock_perm.state() is WriteLock
            &&& child_pcid_allocator_lock_perm.thread_id() == lctx.thread_id()
            &&& child_pcid_allocator_lock_perm.lock_id() == krnl.pcid_allc_mp.spec_index(pcid_allocator_page).locking_thread()->Write_lock_id
        }) by { reveal(owned_2m_tail_lock_perms_wf); };
        assert(krnl.prc_mp.spec_index(process_page).write_lock_perm_match(&child_process_lock_perm));
        assert(krnl.prc_mp.spec_index(process_page).wlocked());
        assert(held_cpus_unchanged(old(krnl).cpu_arr, krnl.cpu_arr, old(lctx))) by { held_kernel_objects_unchanged_reflexive(old(krnl), old(lctx)); };
        assert(held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx))) by { reveal(typed_lock_maps_aligned); reveal(held_processes_unchanged); reveal(LockedMap::typed_lock_map_aligned); };
        assert(held_pagetables_unchanged(old(krnl).pt_mp, krnl.pt_mp, old(lctx))) by { reveal(typed_lock_maps_aligned); reveal(held_pagetables_unchanged); reveal(LockedMap::typed_lock_map_aligned); };
    }

    proof { publish_staged_container_root_mutation_object_invs(*krnl, parent_container_ptr, container_page, pcid_allocator_page, scheduler_page, cpu_set_page, process_page, pagetable_page,); }
    (
        Tracked(child_container_lock_perm),
        Tracked(child_process_lock_perm),
        Tracked(child_pagetable_lock_perm),
        Tracked(child_scheduler_lock_perm),
        Tracked(child_pcid_allocator_lock_perm),
    )
}
}
