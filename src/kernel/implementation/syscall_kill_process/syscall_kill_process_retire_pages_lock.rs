use vstd::prelude::*;
use crate::*;

verus! {
/// Sorts the distinct retired pages into strictly increasing index order, the order in which pages of one lock major are acquired.
pub(super) fn kill_retire_sort_pages(pages: &ArrayVec<PageIndex, 5>) -> (ret: ArrayVec<PageIndex, 5>)
    requires
        pages.wf(),
        pages.view().no_duplicates(),
    ensures
        ret.wf(),
        ret.view().len() == pages.view().len(),
        ret.view().to_set() == pages.view().to_set(),
        forall|k: int| #![trigger ret.view()[k]] 0 <= k < ret.view().len() ==> pages.view().contains(ret.view()[k]),
        forall|i: int, j: int| #![trigger ret.view()[i], ret.view()[j]] 0 <= i < j < ret.view().len() ==> ret.view()[i] < ret.view()[j],
{
    let mut ret = ArrayVec::<PageIndex, 5>::new();
    let mut i: usize = 0;
    while i < pages.len()
        invariant
            pages.wf(),
            pages.view().no_duplicates(),
            ret.wf(),
            0 <= i <= pages.view().len(),
            ret.view().len() == i,
            forall|p: PageIndex| #![trigger ret.view().contains(p)] #![trigger pages.view().subrange(0, i as int).contains(p)] ret.view().contains(p) == pages.view().subrange(0, i as int).contains(p),
            forall|a: int, b: int| #![trigger ret.view()[a], pages.view()[b]] 0 <= a < ret.view().len() && i <= b < pages.view().len() ==> ret.view()[a] != pages.view()[b],
            forall|a: int, b: int| #![trigger ret.view()[a], ret.view()[b]] 0 <= a < b < ret.view().len() ==> ret.view()[a] < ret.view()[b],
        decreases pages.view().len() - i,
    {
        broadcast use vstd::seq_lib::lemma_seq_concat_contains_all_elements, vstd::seq_lib::lemma_seq_contains_after_push;
        let page = *pages.get(i);
        let ghost cur = ret.view();
        ret.push(page);
        let mut j: usize = i;
        while j > 0 && *ret.get(j - 1) > page
            invariant
                ret.wf(),
                0 <= j <= cur.len(),
                ret.view() == cur.insert(j as int, page),
                forall|a: int| #![trigger cur[a]] j <= a < cur.len() ==> page < cur[a],
            decreases j,
        {
            let prev = *ret.get(j - 1);
            ret.set(j, prev);
            ret.set(j - 1, page);
            j = j - 1;
        }
        proof {
            assert(cur =~= cur.subrange(0, j as int) + cur.subrange(j as int, cur.len() as int));
            assert(pages.view().subrange(0, i + 1) =~= pages.view().subrange(0, i as int).push(page));
        }
        i = i + 1;
    }
    proof { assert(pages.view().subrange(0, pages.view().len() as int) =~= pages.view()); }
    ret
}

/// Write-locks the `Allocated4k` pages `sorted`, all of lock major `major`, in increasing index order from a context whose
/// held pages all have a lower major and are write-held with `perms`; returns `perms` with the new pages' permissions.
pub(super) fn wlock_kill_retire_pages(
    krnl: &mut KernelK, sorted: &ArrayVec<PageIndex, 5>, Ghost(major): Ghost<LockMajorId>, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(perms): Tracked<Map<PageIndex, LockPerm>>,
) -> (ret: Tracked<Map<PageIndex, LockPerm>>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        major < PAGETABLE_PAGE_MAJOR ==> old(lctx).pagetable_lock_map().dom().is_empty() && old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        forall|held_thread: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(held_thread)] old(lctx).thread_lock_map().dom().contains(held_thread) ==> {
            let state = old(krnl).thr_mp.spec_index(held_thread).view().state;
            !(state.is_endpoint_waiting() || state.is_reply_waiting() || state is IPC_ENDPOINT_TRANSIT)
        },
        forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page)
            ==> index_valid(NUM_PAGES, held_page) && old(krnl).pg_arr.lock_id_by_index(held_page).major < major,
        perms.dom() == old(lctx).page_lock_map().dom(),
        forall|p: PageIndex| #![trigger perms.dom().contains(p)] perms.dom().contains(p) ==> {
            &&& typed_lock_map_contains_mode(old(lctx).page_lock_map(), p, TypedLockMode::Write)
            &&& perms.spec_index(p).state() is WriteLock
            &&& perms.spec_index(p).thread_id() == old(lctx).thread_id()
            &&& perms.spec_index(p).lock_id() == old(krnl).pg_arr.spec_index(p).view().locking_thread()->Write_lock_id
        },
        sorted.wf(),
        forall|i: int, j: int| #![trigger sorted.view()[i], sorted.view()[j]] 0 <= i < j < sorted.view().len() ==> sorted.view()[i] < sorted.view()[j],
        forall|k: int| #![trigger sorted.view()[k]] 0 <= k < sorted.view().len() ==> {
            &&& index_valid(NUM_PAGES, sorted.view()[k])
            &&& old(krnl).pg_arr.spec_index(sorted.view()[k]).view().view().state is Allocated4k
            &&& old(krnl).pg_arr.lock_id_by_index(sorted.view()[k]).major == major
        },
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, ..*old(krnl) }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        kernel_k_to_nonlock_kernel_u(*final(krnl)) == kernel_k_to_nonlock_kernel_u(*old(krnl)),
        forall|i: PageIndex| #![trigger final(krnl).pg_arr.spec_index(i)] index_valid(NUM_PAGES, i) && !sorted.view().to_set().contains(i) ==> final(krnl).pg_arr.spec_index(i) == old(krnl).pg_arr.spec_index(i),
        forall|i: PageIndex| #![trigger final(krnl).pg_arr.spec_index(i).view()] index_valid(NUM_PAGES, i) ==> {
            &&& final(krnl).pg_arr.spec_index(i).view().view() == old(krnl).pg_arr.spec_index(i).view().view()
            &&& final(krnl).pg_arr.spec_index(i).view().view_rodata() == old(krnl).pg_arr.spec_index(i).view().view_rodata()
            &&& final(krnl).pg_arr.spec_index(i).view().view_ghost() == old(krnl).pg_arr.spec_index(i).view().view_ghost()
            &&& final(krnl).pg_arr.spec_index(i).view().being_killed() == old(krnl).pg_arr.spec_index(i).view().being_killed()
        },
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom() + sorted.view().to_set(),
        forall|p: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(p)] old(lctx).page_lock_map().dom().contains(p)
            ==> final(lctx).page_lock_map()[p] == old(lctx).page_lock_map()[p] && final(krnl).pg_arr.spec_index(p) == old(krnl).pg_arr.spec_index(p),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        ret.view().dom() == final(lctx).page_lock_map().dom(),
        forall|p: PageIndex| #![trigger ret.view().dom().contains(p)] ret.view().dom().contains(p) ==> {
            &&& typed_lock_map_contains_mode(final(lctx).page_lock_map(), p, TypedLockMode::Write)
            &&& ret.view().spec_index(p).state() is WriteLock
            &&& ret.view().spec_index(p).thread_id() == final(lctx).thread_id()
            &&& ret.view().spec_index(p).lock_id() == final(krnl).pg_arr.spec_index(p).view().locking_thread()->Write_lock_id
            &&& final(krnl).pg_arr.lock_id_by_index(p).major <= major
        },
{
    let tracked mut perms = perms;
    let mut k: usize = 0;
    proof { assert(sorted.view().subrange(0, 0).to_set() =~= Set::<PageIndex>::empty()) by { sorted.view().subrange(0, 0).to_set_ensures(); }; }
    while k < sorted.len()
        invariant
            krnl.inv(),
            typed_lock_maps_aligned(krnl, &*lctx),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.kernel_view_locking_state() is Acquire,
            sorted.wf(),
            0 <= k <= sorted.view().len(),
            forall|i: int, j: int| #![trigger sorted.view()[i], sorted.view()[j]] 0 <= i < j < sorted.view().len() ==> sorted.view()[i] < sorted.view()[j],
            forall|j: int| #![trigger sorted.view()[j]] 0 <= j < sorted.view().len() ==> {
                &&& index_valid(NUM_PAGES, sorted.view()[j])
                &&& old(krnl).pg_arr.spec_index(sorted.view()[j]).view().view().state is Allocated4k
                &&& old(krnl).pg_arr.lock_id_by_index(sorted.view()[j]).major == major
            },
            forall|p: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(p)] old(lctx).page_lock_map().dom().contains(p) ==> {
                &&& index_valid(NUM_PAGES, p)
                &&& old(krnl).pg_arr.lock_id_by_index(p).major < major
                &&& lctx.page_lock_map().dom().contains(p)
                &&& lctx.page_lock_map()[p] == old(lctx).page_lock_map()[p]
                &&& krnl.pg_arr.spec_index(p) == old(krnl).pg_arr.spec_index(p)
            },
            lctx.page_lock_map().dom() =~= old(lctx).page_lock_map().dom() + sorted.view().subrange(0, k as int).to_set(),
            perms.dom() == lctx.page_lock_map().dom(),
            lctx.pcid_needflush_lock_map().dom().is_empty(),
            lctx.cpu_offline_flag_lock_map().dom().is_empty(),
            lctx.endpoint_lock_map().dom().is_empty(),
            lctx.scheduler_lock_map().dom().is_empty(),
            lctx.cpu_set_lock_map().dom().is_empty(),
            major < PAGETABLE_PAGE_MAJOR ==> lctx.pagetable_lock_map().dom().is_empty() && lctx.iommu_table_lock_map().dom().is_empty(),
            lctx.iommu_root_table_lock_map().dom().is_empty(),
            lctx.holds_no_allocator_locks(PageSize::SZ4k),
            lctx.holds_no_allocator_locks(PageSize::SZ2m),
            lctx.holds_no_allocator_locks(PageSize::SZ1g),
            forall|held_cpu_id: CpuId| #![trigger lctx.cpu_lock_map().dom().contains(held_cpu_id)] lctx.cpu_lock_map().dom().contains(held_cpu_id) ==> !(krnl.cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            forall|held_thread: RwLockThreadPtr| #![trigger lctx.thread_lock_map().dom().contains(held_thread)] lctx.thread_lock_map().dom().contains(held_thread) ==> {
                let state = krnl.thr_mp.spec_index(held_thread).view().state;
                !(state.is_endpoint_waiting() || state.is_reply_waiting() || state is IPC_ENDPOINT_TRANSIT)
            },
            lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
            lctx.pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            lctx.cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            lctx.process_lock_map() == old(lctx).process_lock_map(),
            lctx.thread_lock_map() == old(lctx).thread_lock_map(),
            lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            lctx.scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            lctx.pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            lctx.pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            lctx.iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            lctx.iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
            lctx.allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
            lctx.allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            lctx.allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            *krnl == (KernelK { pg_arr: krnl.pg_arr, ..*old(krnl) }),
            forall|i: PageIndex| #![trigger krnl.pg_arr.spec_index(i).view()] index_valid(NUM_PAGES, i) ==> {
                &&& krnl.pg_arr.spec_index(i).view().view() == old(krnl).pg_arr.spec_index(i).view().view()
                &&& krnl.pg_arr.spec_index(i).view().view_rodata() == old(krnl).pg_arr.spec_index(i).view().view_rodata()
                &&& krnl.pg_arr.spec_index(i).view().view_ghost() == old(krnl).pg_arr.spec_index(i).view().view_ghost()
                &&& krnl.pg_arr.spec_index(i).view().being_killed() == old(krnl).pg_arr.spec_index(i).view().being_killed()
            },
            forall|i: PageIndex| #![trigger krnl.pg_arr.spec_index(i)] #![trigger old(krnl).pg_arr.spec_index(i)]
                index_valid(NUM_PAGES, i) && !sorted.view().subrange(0, k as int).to_set().contains(i) ==> krnl.pg_arr.spec_index(i) == old(krnl).pg_arr.spec_index(i),
            forall|held_page: PageIndex| #![trigger lctx.page_lock_map().dom().contains(held_page)] lctx.page_lock_map().dom().contains(held_page) ==> {
                let held_major = krnl.pg_arr.lock_id_by_index(held_page).major;
                held_major < major || held_major == major && (k < sorted.view().len() ==> held_page < sorted.view()[k as int])
            },
            forall|p: PageIndex| #![trigger perms.dom().contains(p)] perms.dom().contains(p) ==> {
                &&& typed_lock_map_contains_mode(lctx.page_lock_map(), p, TypedLockMode::Write)
                &&& perms.spec_index(p).state() is WriteLock
                &&& perms.spec_index(p).thread_id() == lctx.thread_id()
                &&& perms.spec_index(p).lock_id() == krnl.pg_arr.spec_index(p).view().locking_thread()->Write_lock_id
            },
        decreases sorted.view().len() - k,
    {
        let page_index = *sorted.get(k);
        let Tracked(perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));
        proof {
            perms.tracked_insert(page_index, perm);
            assert(sorted.view().subrange(0, k + 1).to_set() == sorted.view().subrange(0, k as int).to_set().insert(page_index)) by {
                assert(sorted.view().subrange(0, k + 1) =~= sorted.view().subrange(0, k as int).push(page_index));
                sorted.view().subrange(0, k as int).lemma_push_to_set_commute(page_index);
            };
        }
        k = k + 1;
    }
    proof {
        assert(sorted.view().subrange(0, sorted.view().len() as int) =~= sorted.view());
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), krnl)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
        assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use kernel_endpoint_nonlock_fields_unchanged_for_equal; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
        assert(kernel_k_to_nonlock_kernel_u(*krnl) == kernel_k_to_nonlock_kernel_u(*old(krnl))) by { kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(old(krnl), krnl); };
    }
    Tracked(perms)
}

/// Releases the distinct write-held pages `pages`, in either locking phase.
pub(super) fn wunlock_kill_retire_pages(krnl: &mut KernelK, pages: &ArrayVec<PageIndex, 5>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(perms): Tracked<Map<PageIndex, LockPerm>>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        pages.wf(),
        0 < pages.view().len(),
        pages.view().no_duplicates(),
        forall|k: int| #![trigger pages.view()[k]] 0 <= k < pages.view().len() ==> index_valid(NUM_PAGES, pages.view()[k]),
        perms.dom() == pages.view().to_set(),
        forall|p: PageIndex| #![trigger perms.dom().contains(p)] perms.dom().contains(p) ==> {
            &&& typed_lock_map_contains_mode(old(lctx).page_lock_map(), p, TypedLockMode::Write)
            &&& perms.spec_index(p).state() is WriteLock
            &&& perms.spec_index(p).thread_id() == old(lctx).thread_id()
            &&& perms.spec_index(p).lock_id() == old(krnl).pg_arr.spec_index(p).view().locking_thread()->Write_lock_id
        },
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, ..*old(krnl) }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        kernel_k_to_nonlock_kernel_u(*final(krnl)) == kernel_k_to_nonlock_kernel_u(*old(krnl)),
        forall|i: PageIndex| #![trigger final(krnl).pg_arr.spec_index(i)] #![trigger old(krnl).pg_arr.spec_index(i)] index_valid(NUM_PAGES, i) && !pages.view().to_set().contains(i) ==> final(krnl).pg_arr.spec_index(i) == old(krnl).pg_arr.spec_index(i),
        forall|i: PageIndex| #![trigger final(krnl).pg_arr.spec_index(i).view()] index_valid(NUM_PAGES, i) ==> {
            &&& final(krnl).pg_arr.spec_index(i).view().view() == old(krnl).pg_arr.spec_index(i).view().view()
            &&& final(krnl).pg_arr.spec_index(i).view().view_rodata() == old(krnl).pg_arr.spec_index(i).view().view_rodata()
            &&& final(krnl).pg_arr.spec_index(i).view().view_ghost() == old(krnl).pg_arr.spec_index(i).view().view_ghost()
            &&& final(krnl).pg_arr.spec_index(i).view().being_killed() == old(krnl).pg_arr.spec_index(i).view().being_killed()
        },
        final(lctx).page_lock_map() == old(lctx).page_lock_map().remove_keys(pages.view().to_set()),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
{
    let tracked mut perms = perms;
    let mut k: usize = 0;
    proof { assert(pages.view().subrange(0, 0).to_set() =~= Set::<PageIndex>::empty()) by { pages.view().subrange(0, 0).to_set_ensures(); }; }
    while k < pages.len()
        invariant
            krnl.inv(),
            typed_lock_maps_aligned(krnl, &*lctx),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            k > 0 ==> lctx.kernel_view_locking_state() is Release,
            pages.wf(),
            0 <= k <= pages.view().len(),
            pages.view().no_duplicates(),
            forall|j: int| #![trigger pages.view()[j]] 0 <= j < pages.view().len() ==> index_valid(NUM_PAGES, pages.view()[j]),
            lctx.page_lock_map() =~= old(lctx).page_lock_map().remove_keys(pages.view().subrange(0, k as int).to_set()),
            lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
            lctx.pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            lctx.cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            lctx.process_lock_map() == old(lctx).process_lock_map(),
            lctx.thread_lock_map() == old(lctx).thread_lock_map(),
            lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            lctx.scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            lctx.pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            lctx.pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            lctx.iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            lctx.iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
            lctx.allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
            lctx.allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            lctx.allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            *krnl == (KernelK { pg_arr: krnl.pg_arr, ..*old(krnl) }),
            forall|i: PageIndex| #![trigger krnl.pg_arr.spec_index(i).view()] index_valid(NUM_PAGES, i) ==> {
                &&& krnl.pg_arr.spec_index(i).view().view() == old(krnl).pg_arr.spec_index(i).view().view()
                &&& krnl.pg_arr.spec_index(i).view().view_rodata() == old(krnl).pg_arr.spec_index(i).view().view_rodata()
                &&& krnl.pg_arr.spec_index(i).view().view_ghost() == old(krnl).pg_arr.spec_index(i).view().view_ghost()
                &&& krnl.pg_arr.spec_index(i).view().being_killed() == old(krnl).pg_arr.spec_index(i).view().being_killed()
            },
            forall|i: PageIndex| #![trigger krnl.pg_arr.spec_index(i)] #![trigger old(krnl).pg_arr.spec_index(i)] index_valid(NUM_PAGES, i) && !pages.view().subrange(0, k as int).to_set().contains(i) ==> krnl.pg_arr.spec_index(i) == old(krnl).pg_arr.spec_index(i),
            forall|j: int| #![trigger pages.view()[j]] k <= j < pages.view().len() ==> {
                let p = pages.view()[j];
                &&& perms.dom().contains(p)
                &&& typed_lock_map_contains_mode(lctx.page_lock_map(), p, TypedLockMode::Write)
                &&& perms.spec_index(p).state() is WriteLock
                &&& perms.spec_index(p).thread_id() == lctx.thread_id()
                &&& perms.spec_index(p).lock_id() == krnl.pg_arr.spec_index(p).view().locking_thread()->Write_lock_id
            },
        decreases pages.view().len() - k,
    {
        let page_index = *pages.get(k);
        let tracked perm = perms.tracked_remove(page_index);
        krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(perm));
        proof {
            assert(pages.view().subrange(0, k + 1).to_set() == pages.view().subrange(0, k as int).to_set().insert(page_index)) by {
                assert(pages.view().subrange(0, k + 1) =~= pages.view().subrange(0, k as int).push(page_index));
                pages.view().subrange(0, k as int).lemma_push_to_set_commute(page_index);
            };
        }
        k = k + 1;
    }
    proof {
        assert(pages.view().subrange(0, pages.view().len() as int) =~= pages.view());
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), krnl)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
        assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use kernel_endpoint_nonlock_fields_unchanged_for_equal; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
        assert(kernel_k_to_nonlock_kernel_u(*krnl) == kernel_k_to_nonlock_kernel_u(*old(krnl))) by { kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(old(krnl), krnl); };
    }
}

/// Retires the write-held `Allocated4k` pages `pages`, whose kernel objects were removed with their permissions in
/// `page_perms`, through their free-list nodes into shard `cpu_id` of the 4K allocator `allocator_ptr`, during Release.
/// The quota is left to the caller.
pub(super) fn kill_retire_pages_to_cache(
    krnl: &mut KernelK, pages: &ArrayVec<PageIndex, 5>, Tracked(page_perms): Tracked<Map<PageIndex, PagePerm4k>>, allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(page_lock_perms): Tracked<&Map<PageIndex, LockPerm>>, Tracked(cache_lock_perm): Tracked<&LockPerm>,
)
    requires
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        page_array_wf(old(krnl).pg_arr),
        old(krnl).allc_4k_mp.perms_wf(),
        old(krnl).allc_4k_mp.dom().contains(allocator_ptr),
        old(krnl).allc_4k_mp.spec_index(allocator_ptr).wf(),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(old(lctx).allocator_cache_4k_lock_map(), (allocator_ptr, cpu_id), TypedLockMode::Write),
        cache_lock_perm.state() is WriteLock,
        cache_lock_perm.thread_id() == old(lctx).thread_id(),
        cache_lock_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().len() + pages.view().len() <= ALLOCATOR_MAX_WATERMARK,
        old(krnl).allc_4k_mp.spec_index(allocator_ptr).total_free_pages.view() + pages.view().len() < usize::MAX,
        pages.wf(),
        pages.view().no_duplicates(),
        forall|k: int| #![trigger pages.view()[k]] 0 <= k < pages.view().len() ==> {
            let page_index = pages.view()[k];
            &&& index_valid(NUM_PAGES, page_index)
            &&& old(krnl).pg_arr.spec_index(page_index).view().view().state is Allocated4k
            &&& typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_index, TypedLockMode::Write)
            &&& page_lock_perms.dom().contains(page_index)
            &&& page_lock_perms.spec_index(page_index).state() is WriteLock
            &&& page_lock_perms.spec_index(page_index).thread_id() == old(lctx).thread_id()
            &&& page_lock_perms.spec_index(page_index).lock_id() == old(krnl).pg_arr.spec_index(page_index).view().locking_thread()->Write_lock_id
            &&& page_perms.dom().contains(page_index)
            &&& page_perms.spec_index(page_index).is_init()
            &&& page_perms.spec_index(page_index).addr() == page_index2page_ptr(page_index)
            &&& !old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().contains(page_index2page_ptr(page_index))
        },
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        page_array_wf(final(krnl).pg_arr),
        final(krnl).allc_4k_mp.perms_wf(),
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).wf(),
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, allc_4k_mp: final(krnl).allc_4k_mp, ..*old(krnl) }),
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom(),
        forall|i: PageIndex| #![trigger final(lctx).page_lock_map().index(i)] old(lctx).page_lock_map().dom().contains(i) ==> final(lctx).page_lock_map().index(i)
            == if pages.view().contains(i) { TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(i), mode: TypedLockMode::Write } } else { old(lctx).page_lock_map().index(i) },
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        forall|i: PageIndex| #![trigger final(krnl).pg_arr.spec_index(i)] index_valid(NUM_PAGES, i) && !pages.view().contains(i) ==> final(krnl).pg_arr.spec_index(i) == old(krnl).pg_arr.spec_index(i),
        forall|k: int| #![trigger pages.view()[k]] 0 <= k < pages.view().len() ==> {
            let pre_page = old(krnl).pg_arr.spec_index(pages.view()[k]).view();
            let post_page = final(krnl).pg_arr.spec_index(pages.view()[k]).view();
            &&& post_page.is_init() == pre_page.is_init()
            &&& post_page.view_rodata() == pre_page.view_rodata()
            &&& post_page.view_ghost() == pre_page.view_ghost()
            &&& post_page.locking_thread() == pre_page.locking_thread()
            &&& post_page.being_killed() == pre_page.being_killed()
            &&& post_page.view().free_list_node_storage.addr() == pre_page.view().free_list_node_storage.addr()
            &&& post_page.view() == (Page { state: PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } },
                free_list_node_storage: post_page.view().free_list_node_storage, perm_4k: post_page.view().perm_4k, ..pre_page.view() })
        },
        final(krnl).allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
        final(krnl).allc_4k_mp.unchanged_except(&old(krnl).allc_4k_mp, allocator_ptr),
        ({
            let pre_allocator = old(krnl).allc_4k_mp.spec_index(allocator_ptr);
            let post_allocator = final(krnl).allc_4k_mp.spec_index(allocator_ptr);
            let pre_cache = pre_allocator.cpu_caches.spec_index(cpu_id).view();
            let post_cache = post_allocator.cpu_caches.spec_index(cpu_id).view();
            &&& post_allocator.total_free_pages.view() == pre_allocator.total_free_pages.view() + pages.view().len()
            &&& post_cache.view().view().len() == pre_cache.view().view().len() + pages.view().len()
            &&& forall|p: PagePtr| #![trigger post_cache.view().view().contains(p)] post_cache.view().view().contains(p) == (pre_cache.view().view().contains(p) || pages.view().contains(page_ptr2page_index(p)) && page_ptr_valid(p))
            &&& forall|a: usize| #![trigger pre_cache.view().map().dom().contains(a)] pre_cache.view().map().dom().contains(a) ==> post_cache.view().map().dom().contains(a) && post_cache.view().map().spec_index(a) == pre_cache.view().map().spec_index(a)
            &&& forall|k: int| #![trigger pages.view()[k]] 0 <= k < pages.view().len() ==> {
                let node = old(krnl).pg_arr.spec_index(pages.view()[k]).view().view().free_list_node_storage.addr();
                &&& !pre_cache.view().map().dom().contains(node)
                &&& post_cache.view().map().dom().contains(node)
                &&& post_cache.view().map().spec_index(node) == page_index2page_ptr(pages.view()[k])
            }
            &&& post_allocator.cpu_caches.entries_unchanged_except(&pre_allocator.cpu_caches, cpu_id)
            &&& post_cache.locking_thread() == pre_cache.locking_thread()
            &&& post_allocator.global_pool == pre_allocator.global_pool
            &&& post_allocator.owning_container == pre_allocator.owning_container
            &&& post_allocator.quota == pre_allocator.quota
        }),
{
    let tracked mut page_perms = page_perms;
    let mut k: usize = 0;
    while k < pages.len()
        invariant
            pages.wf(),
            pages.view().no_duplicates(),
            0 <= k <= pages.view().len(),
            index_valid(NUM_CPUS, cpu_id),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(krnl, &*lctx),
            page_array_wf(krnl.pg_arr),
            krnl.allc_4k_mp.perms_wf(),
            typed_lock_map_contains_mode(lctx.allocator_cache_4k_lock_map(), (allocator_ptr, cpu_id), TypedLockMode::Write),
            cache_lock_perm.state() is WriteLock,
            cache_lock_perm.thread_id() == lctx.thread_id(),
            cache_lock_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().len() + pages.view().len() <= ALLOCATOR_MAX_WATERMARK,
            old(krnl).allc_4k_mp.spec_index(allocator_ptr).total_free_pages.view() + pages.view().len() < usize::MAX,
            forall|j: int| #![trigger pages.view()[j]] 0 <= j < pages.view().len() ==> {
                let page_index = pages.view()[j];
                &&& index_valid(NUM_PAGES, page_index)
                &&& old(krnl).pg_arr.spec_index(page_index).view().view().state is Allocated4k
                &&& typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_index, TypedLockMode::Write)
                &&& page_lock_perms.dom().contains(page_index)
                &&& page_lock_perms.spec_index(page_index).state() is WriteLock
                &&& page_lock_perms.spec_index(page_index).thread_id() == old(lctx).thread_id()
                &&& page_lock_perms.spec_index(page_index).lock_id() == old(krnl).pg_arr.spec_index(page_index).view().locking_thread()->Write_lock_id
                &&& !old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().contains(page_index2page_ptr(page_index))
            },
            forall|j: int| #![trigger pages.view()[j]] k <= j < pages.view().len() ==> {
                let page_index = pages.view()[j];
                &&& page_perms.dom().contains(page_index)
                &&& page_perms.spec_index(page_index).is_init()
                &&& page_perms.spec_index(page_index).addr() == page_index2page_ptr(page_index)
            },
            lctx.page_lock_map().dom() == old(lctx).page_lock_map().dom(),
            forall|i: PageIndex| #![trigger lctx.page_lock_map().index(i)] old(lctx).page_lock_map().dom().contains(i) ==> lctx.page_lock_map().index(i)
                == if pages.view().subrange(0, k as int).contains(i) { TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(i), mode: TypedLockMode::Write } } else { old(lctx).page_lock_map().index(i) },
            lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
            lctx.pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            lctx.cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            lctx.process_lock_map() == old(lctx).process_lock_map(),
            lctx.thread_lock_map() == old(lctx).thread_lock_map(),
            lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            lctx.scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            lctx.pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            lctx.pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            lctx.iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            lctx.iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
            lctx.allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
            lctx.allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            lctx.allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            *krnl == (KernelK { pg_arr: krnl.pg_arr, allc_4k_mp: krnl.allc_4k_mp, ..*old(krnl) }),
            forall|i: PageIndex| #![trigger krnl.pg_arr.spec_index(i)] index_valid(NUM_PAGES, i) && !pages.view().subrange(0, k as int).contains(i) ==> krnl.pg_arr.spec_index(i) == old(krnl).pg_arr.spec_index(i),
            forall|j: int| #![trigger pages.view()[j]] 0 <= j < k ==> {
                let pre_page = old(krnl).pg_arr.spec_index(pages.view()[j]).view();
                let cur_page = krnl.pg_arr.spec_index(pages.view()[j]).view();
                &&& cur_page.is_init() == pre_page.is_init()
                &&& cur_page.view_rodata() == pre_page.view_rodata()
                &&& cur_page.view_ghost() == pre_page.view_ghost()
                &&& cur_page.locking_thread() == pre_page.locking_thread()
                &&& cur_page.being_killed() == pre_page.being_killed()
                &&& cur_page.view().free_list_node_storage.addr() == pre_page.view().free_list_node_storage.addr()
                &&& cur_page.view() == (Page { state: PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } },
                    free_list_node_storage: cur_page.view().free_list_node_storage, perm_4k: cur_page.view().perm_4k, ..pre_page.view() })
            },
            krnl.allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
            krnl.allc_4k_mp.unchanged_except(&old(krnl).allc_4k_mp, allocator_ptr),
            ({
                let pre_allocator = old(krnl).allc_4k_mp.spec_index(allocator_ptr);
                let cur_allocator = krnl.allc_4k_mp.spec_index(allocator_ptr);
                let pre_cache = pre_allocator.cpu_caches.spec_index(cpu_id).view();
                let cur_cache = cur_allocator.cpu_caches.spec_index(cpu_id).view();
                &&& cur_allocator.wf()
                &&& cur_allocator.total_free_pages.view() == pre_allocator.total_free_pages.view() + k
                &&& cur_cache.view().view().len() == pre_cache.view().view().len() + k
                &&& forall|p: PagePtr| #![trigger cur_cache.view().view().contains(p)] cur_cache.view().view().contains(p) == (pre_cache.view().view().contains(p) || pages.view().subrange(0, k as int).contains(page_ptr2page_index(p)) && page_ptr_valid(p))
                &&& forall|a: usize| #![trigger pre_cache.view().map().dom().contains(a)] pre_cache.view().map().dom().contains(a) ==> cur_cache.view().map().dom().contains(a) && cur_cache.view().map().spec_index(a) == pre_cache.view().map().spec_index(a)
                &&& forall|j: int| #![trigger pages.view()[j]] 0 <= j < k ==> {
                    let node = old(krnl).pg_arr.spec_index(pages.view()[j]).view().view().free_list_node_storage.addr();
                    &&& !pre_cache.view().map().dom().contains(node)
                    &&& cur_cache.view().map().dom().contains(node)
                    &&& cur_cache.view().map().spec_index(node) == page_index2page_ptr(pages.view()[j])
                }
                &&& cur_allocator.cpu_caches.entries_unchanged_except(&pre_allocator.cpu_caches, cpu_id)
                &&& cur_cache.locking_thread() == pre_cache.locking_thread()
                &&& cur_allocator.global_pool == pre_allocator.global_pool
                &&& cur_allocator.owning_container == pre_allocator.owning_container
                &&& cur_allocator.quota == pre_allocator.quota
            }),
        decreases pages.view().len() - k,
    {
        broadcast use vstd::seq_lib::lemma_seq_concat_contains_all_elements, vstd::seq_lib::lemma_seq_contains_after_push;
        let page_index = *pages.get(k);
        let ghost cur_cache = krnl.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view();
        let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
        proof { page_array_wf_at(krnl.pg_arr, page_index); }
        let tracked page_perm = page_perms.tracked_remove(page_index);
        let tracked page_lock_perm = page_lock_perms.tracked_borrow(page_index);
        let (node_addr, node_perm) = page_array_retire_kernel_object_4k_to_cache(&mut krnl.pg_arr, page_index, Tracked(page_perm), allocator_ptr, cpu_id, Tracked(&*lctx), Tracked(page_lock_perm));
        proof { lctx.update_lock_id(KernelObjId::Page(page_index), old_page_lock_id, krnl.pg_arr.lock_id_by_index(page_index)); }
        krnl.allc_4k_mp.push_cache_page_typed(allocator_ptr, cpu_id, node_addr, node_perm, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
            Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(cache_lock_perm));
        proof {
            assert(pages.view().subrange(0, k + 1) =~= pages.view().subrange(0, k as int).push(page_index));
            assert(cur_cache.subrange(0, cur_cache.len() as int) =~= cur_cache);
        }
        k = k + 1;
    }
}
} // verus!
