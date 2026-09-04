use vstd::prelude::*;
use vstd::assert_sets_equal;
use crate::*;
use super::allocate_free_4k_impl_basd::allocate_free_4k_page;

verus! {

pub open spec fn page_ptrs_to_indices(pages: Seq<PagePtr>) -> Set<PageIndex> {
    pages.map_values(|page_ptr: PagePtr| page_ptr2page_index(page_ptr)).to_set()
}

proof fn map_insert_seq_push_domain<K, V>(map: Map<K, V>, seq: Seq<K>, key: K, value: V)
    requires
        map.dom() == seq.to_set(),
    ensures
        map.insert(key, value).dom() == seq.push(key).to_set(),
{
    broadcast use vstd::map::lemma_map_insert_domain;
    assert_sets_equal!(map.insert(key, value).dom() == seq.push(key).to_set(), x => { seq_push_lemma::<K>(); seq.to_set_ensures(); seq.push(key).to_set_ensures(); broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different; });
}

proof fn set_union_seq_push_insert<A>(base: Set<A>, seq: Seq<A>, key: A)
    ensures
        base.union(seq.to_set()).insert(key) == base.union(seq.push(key).to_set()),
{
    assert_sets_equal!(base.union(seq.to_set()).insert(key) == base.union(seq.push(key).to_set()), x => { seq_push_lemma::<A>(); seq.to_set_ensures(); seq.push(key).to_set_ensures(); broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different; broadcast use vstd::set::lemma_set_union; });
}

pub open spec fn allocated_4k_page_lock_perms_wf(
    perms: Map<PagePtr, LockPerm>,
    krnl: &KernelK,
    lctx: &LocalContext,
    thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr,
) -> bool {
    forall|page_ptr: PagePtr|
        #![trigger perms.dom().contains(page_ptr)]
        perms.dom().contains(page_ptr) ==> {
            &&& page_ptr_valid(page_ptr)
            &&& perms.spec_index(page_ptr).state() is WriteLock
            &&& perms.spec_index(page_ptr).thread_id() == lctx.thread_id()
            &&& lctx.page_lock_map().dom().contains(page_ptr2page_index(page_ptr))
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == PageState::Owned4k { thread_ptr }
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == container_ptr
            &&& krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().wlocked_by(lctx)
            &&& perms.spec_index(page_ptr).lock_id() == krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id
        }
}

pub fn allocate_free_4k_pages<const N: usize>(
    krnl: &mut KernelK,
    thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr,
    cpu_id: CpuId,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>,
    Tracked(thread_lock_perm): Tracked<&LockPerm>,
) -> (ret: (ArrayVec<PagePtr, N>, Tracked<Map<PagePtr, LockPerm>>))
    requires
        old(krnl).inv(),
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        thread_effective_quota_4k(old(krnl).thr_mp.spec_index(thread_ptr)) >= N,
        old(krnl).thr_mp.spec_index(thread_ptr).wlocked_by(old(lctx)),
        page_objects_unlocked_except(old(krnl).pg_arr, old(lctx).thread_id(), old(lctx).page_lock_map().dom()),
        allocator_objects_unlocked(old(krnl).allc_4k_mp, old(lctx).thread_id()),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
    ensures
        final(krnl).inv(),
        ret.0.wf(),
        ret.0.len() == N,
        ret.0.view().no_duplicates(),
        ret.1.view().dom() == ret.0.view().to_set(),
        allocated_4k_page_lock_perms_wf(ret.1.view(), final(krnl), final(lctx), thread_ptr, container_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
        final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc,
        final(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container,
        final(krnl).thr_mp.spec_index(thread_ptr).view().stable_allocation_root_equal(&old(krnl).thr_mp.spec_index(thread_ptr).view()),
        final(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr,
        final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().union(ret.0.view().to_set()),
        final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k,
        final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m,
        final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g,
        final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_fields_equal(&old(krnl).thr_mp.spec_index(thread_ptr).view()),
        final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors == old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors,
        thread_effective_quota_4k(final(krnl).thr_mp.spec_index(thread_ptr)) == thread_effective_quota_4k(old(krnl).thr_mp.spec_index(thread_ptr)) - N,
        thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).thr_mp.lock_id_by_key(thread_ptr) == old(krnl).thr_mp.lock_id_by_key(thread_ptr),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).wlocked_by(final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom().union(page_ptrs_to_indices(ret.0.view())),
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
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        page_objects_unlocked_except(final(krnl).pg_arr, final(lctx).thread_id(), final(lctx).page_lock_map().dom()),
        allocator_objects_unlocked(final(krnl).allc_4k_mp, final(lctx).thread_id()),
        allocator_objects_unlocked(old(krnl).allc_2m_mp, old(lctx).thread_id()) ==> allocator_objects_unlocked(final(krnl).allc_2m_mp, final(lctx).thread_id()),
        allocator_objects_unlocked(old(krnl).allc_1g_mp, old(lctx).thread_id()) ==> allocator_objects_unlocked(final(krnl).allc_1g_mp, final(lctx).thread_id()),
        forall|t: RwLockThreadPtr|
            #![trigger old(krnl).thr_mp.spec_index(t).locked_by_thread(old(lctx).thread_id())]
            #![trigger final(krnl).thr_mp.spec_index(t).locked_by_thread(final(lctx).thread_id())]
            (old(krnl).thr_mp.dom().contains(t) && old(krnl).thr_mp.spec_index(t).locked_by_thread(old(lctx).thread_id()))
                == (final(krnl).thr_mp.dom().contains(t) && final(krnl).thr_mp.spec_index(t).locked_by_thread(final(lctx).thread_id())),
        final(steps).steps == old(steps).steps,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
        held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
        held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        forall|exceptions: Set<RwLockPageTableRoot>|
            #![trigger pagetable_objects_unlocked_except(old(krnl).pt_mp, old(lctx).thread_id(), exceptions)]
            pagetable_objects_unlocked_except(old(krnl).pt_mp, old(lctx).thread_id(), exceptions)
            ==> pagetable_objects_unlocked_except(final(krnl).pt_mp, final(lctx).thread_id(), exceptions),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
{
    let mut pages = ArrayVec::<PagePtr, N>::new();
    let tracked mut page_lock_perms: Map<PagePtr, LockPerm> = Map::tracked_empty();
    let mut i: usize = 0;
    proof {
        assert(krnl.thr_mp.spec_index(thread_ptr).view().stable_allocation_root_equal(&old(krnl).thr_mp.spec_index(thread_ptr).view())) by { reveal(Thread::stable_allocation_root_equal); };
        assert(krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().union(pages.view().to_set())) by { vstd::set::axiom_set_ext_equal(krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view(), old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().union(pages.view().to_set())); };
    }
    while i < N
        invariant
            krnl.inv(),
            index_valid(NUM_CPUS, cpu_id),
            old(krnl).thr_mp.dom().contains(thread_ptr),
            pages.wf(),
            pages.len() == i,
            pages.view().no_duplicates(),
            page_lock_perms.dom() == pages.view().to_set(),
            allocated_4k_page_lock_perms_wf(page_lock_perms, &*krnl, &*lctx, thread_ptr, container_ptr),
            krnl.thr_mp.dom().contains(thread_ptr),
            krnl.thr_mp.spec_index(thread_ptr).being_killed() == false,
            krnl.thr_mp.spec_index(thread_ptr).view().owning_proc == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc,
            krnl.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
            krnl.thr_mp.spec_index(thread_ptr).view().stable_allocation_root_equal(&old(krnl).thr_mp.spec_index(thread_ptr).view()),
            krnl.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr,
            krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().union(pages.view().to_set()),
            krnl.thr_mp.spec_index(thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k,
            krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m,
            krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g,
            krnl.thr_mp.spec_index(thread_ptr).view().free_quota_pending_fields_equal(&old(krnl).thr_mp.spec_index(thread_ptr).view()),
            krnl.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors == old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors,
            thread_effective_quota_4k(krnl.thr_mp.spec_index(thread_ptr)) == thread_effective_quota_4k(old(krnl).thr_mp.spec_index(thread_ptr)) - i,
            thread_effective_quota_4k(krnl.thr_mp.spec_index(thread_ptr)) >= N - i,
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == lctx.thread_id(),
            thread_lock_perm.lock_id() == krnl.thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            krnl.thr_mp.spec_index(thread_ptr).wlocked_by(&*lctx),
            krnl.thr_mp.lock_id_by_key(thread_ptr) == old(krnl).thr_mp.lock_id_by_key(thread_ptr),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.page_lock_map().dom() == old(lctx).page_lock_map().dom().union(page_ptrs_to_indices(pages.view())),
            lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            lctx.process_lock_map() == old(lctx).process_lock_map(),
            lctx.thread_lock_map() == old(lctx).thread_lock_map(),
            lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            lctx.scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            lctx.pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            lctx.pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            lctx.iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            lctx.allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
            lctx.allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            lctx.allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            lctx.kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(krnl, &*lctx),
            lock_id_set_aligned(&*lctx),
            lctx.held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
            lctx.holds_no_allocator_locks(PageSize::SZ4k),
            page_objects_unlocked_except(krnl.pg_arr, lctx.thread_id(), lctx.page_lock_map().dom()),
            allocator_objects_unlocked(krnl.allc_4k_mp, lctx.thread_id()),
            allocator_objects_unlocked(old(krnl).allc_2m_mp, old(lctx).thread_id()) ==> allocator_objects_unlocked(krnl.allc_2m_mp, lctx.thread_id()),
            allocator_objects_unlocked(old(krnl).allc_1g_mp, old(lctx).thread_id()) ==> allocator_objects_unlocked(krnl.allc_1g_mp, lctx.thread_id()),
            forall|t: RwLockThreadPtr|
                #![trigger old(krnl).thr_mp.spec_index(t).locked_by_thread(old(lctx).thread_id())]
                #![trigger krnl.thr_mp.spec_index(t).locked_by_thread(lctx.thread_id())]
                (old(krnl).thr_mp.dom().contains(t) && old(krnl).thr_mp.spec_index(t).locked_by_thread(old(lctx).thread_id()))
                    == (krnl.thr_mp.dom().contains(t) && krnl.thr_mp.spec_index(t).locked_by_thread(lctx.thread_id())),
            steps.steps == old(steps).steps,
            steps.snap_shot == kernel_k_to_kernel_u(*krnl),
            held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx)),
            held_endpoints_unchanged(old(krnl).ep_mp, krnl.ep_mp, old(lctx)),
            held_schedulers_unchanged(old(krnl).sched_mp, krnl.sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, krnl.pcid_allc_mp, old(lctx)),
            held_pagetables_unchanged(old(krnl).pt_mp, krnl.pt_mp, old(lctx)),
            forall|exceptions: Set<RwLockPageTableRoot>|
                #![trigger pagetable_objects_unlocked_except(old(krnl).pt_mp, old(lctx).thread_id(), exceptions)]
                pagetable_objects_unlocked_except(old(krnl).pt_mp, old(lctx).thread_id(), exceptions)
                ==> pagetable_objects_unlocked_except(krnl.pt_mp, lctx.thread_id(), exceptions),
            held_iommu_tables_unchanged(old(krnl).it_mp, krnl.it_mp, old(lctx)),
            held_cpus_unchanged(old(krnl).cpu_arr, krnl.cpu_arr, old(lctx)),
            i <= N,
        decreases N - i,
    {
        let (page_ptr, Tracked(page_lock_perm)) = allocate_free_4k_page(krnl, thread_ptr, container_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm));
        proof {
            assert(lctx.page_lock_map().dom() == old(lctx).page_lock_map().dom().union(page_ptrs_to_indices(pages.view().push(page_ptr)))) by {
                reveal(typed_lock_maps_inserted);
                seq_push_lemma::<PagePtr>();
                assert_sets_equal!(lctx.page_lock_map().dom() == old(lctx).page_lock_map().dom().union(page_ptrs_to_indices(pages.view().push(page_ptr))), page_index => { reveal(page_ptrs_to_indices); broadcast use Seq::lemma_push_map_commute; pages.view().map_values(|page_ptr: PagePtr| page_ptr2page_index(page_ptr)).to_set_ensures(); pages.view().map_values(|page_ptr: PagePtr| page_ptr2page_index(page_ptr)).push(page_ptr2page_index(page_ptr)).to_set_ensures(); broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different; broadcast use vstd::set::lemma_set_union; });
            };
            assert(!pages.view().contains(page_ptr)) by { pages.view().to_set_ensures(); };
            assert(page_lock_perms.insert(page_ptr, page_lock_perm).dom() == pages.view().push(page_ptr).to_set()) by { map_insert_seq_push_domain(page_lock_perms, pages.view(), page_ptr, page_lock_perm); };
            assert(krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().union(pages.view().push(page_ptr).to_set())) by { set_union_seq_push_insert(old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view(), pages.view(), page_ptr); };
            assert(allocated_4k_page_lock_perms_wf(page_lock_perms.insert(page_ptr, page_lock_perm), &*krnl, &*lctx, thread_ptr, container_ptr)) by { reveal(allocated_4k_page_lock_perms_wf); reveal(held_pages_unchanged_except); page_ptr2page_index_injective(); broadcast use vstd::map::lemma_map_insert_same; broadcast use vstd::map::axiom_map_insert_different; broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different; };
            page_lock_perms.tracked_insert(page_ptr, page_lock_perm);
        }
        pages.push_unique(page_ptr);
        proof {
            assert(krnl.thr_mp.spec_index(thread_ptr).view().stable_allocation_root_equal(&old(krnl).thr_mp.spec_index(thread_ptr).view())) by { reveal(Thread::stable_allocation_root_equal); };
            assert(krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().union(pages.view().to_set())) by { seq_push_lemma::<PagePtr>(); pages.view().to_set_ensures(); vstd::set::axiom_set_ext_equal(krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view(), old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().union(pages.view().to_set())); };
            assert(thread_effective_quota_4k(krnl.thr_mp.spec_index(thread_ptr)) == thread_effective_quota_4k(old(krnl).thr_mp.spec_index(thread_ptr)) - (i + 1)) by { reveal(thread_effective_quota_4k); };
        }
        i = i + 1;
    }
    (pages, Tracked(page_lock_perms))
}

}
