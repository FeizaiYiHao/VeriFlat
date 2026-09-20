use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
pub(super) fn publish_new_container_allocator(
    pages: &mut PageLockedArray, allocator_map: &mut PageAllocatorUnLockedMap, child_container_ptr: RwLockContainerPtr,
    allocator_page: PagePtr, allocator_state: Allocated4KPageState, allocator_value: PageAllocator,
    Ghost(quota_lock_map): Ghost< Map<RwLockPageAllocatorPtr, TypedHeldLock>, >,
    Ghost(cache_lock_map): Ghost< Map<(RwLockPageAllocatorPtr, CpuId), TypedHeldLock>, >,
    Ghost(global_pool_lock_map): Ghost< Map<RwLockPageAllocatorPtr, TypedHeldLock>, >, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(allocator_page_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(pages).inv(),
        page_array_wf(*old(pages)),
        old(allocator_map).perms_wf(),
        old(pages).typed_lock_map_aligned(old(lctx).page_lock_map(), old(lctx).thread_id(),),
        old(allocator_map).typed_quota_lock_map_aligned(quota_lock_map, old(lctx).thread_id(),),
        old(allocator_map).typed_cache_lock_map_aligned(cache_lock_map, old(lctx).thread_id(),),
        old(allocator_map).typed_global_pool_lock_map_aligned(global_pool_lock_map, old(lctx).thread_id(),),
        lock_id_set_aligned(old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        allocator_value.inv(),
        allocator_state is As4KAllocator || allocator_state is As2MAllocator || allocator_state is As1GAllocator,
        !allocator_value.quota.locked(),
        !allocator_value.global_pool.locked(),
        forall|cpu_id: CpuId|
            #![trigger allocator_value.cpu_caches.spec_index(cpu_id).view().locked()]
            #![trigger allocator_value.cpu_caches.spec_index(cpu_id).view().locked_by_thread(old(lctx).thread_id())]
            #![trigger allocator_value.cpu_caches.spec_index(cpu_id).view().rlocked_by_thread(old(lctx).thread_id())]
            #![trigger allocator_value.cpu_caches.spec_index(cpu_id).view().wlocked_by_thread(old(lctx).thread_id())]
            index_valid(NUM_CPUS, cpu_id) ==> !allocator_value.cpu_caches.spec_index(cpu_id).view().locked(),
        !old(allocator_map).dom().contains(allocator_page),
        page_ptr_valid(allocator_page),
        old(pages).spec_index(page_ptr2page_index(allocator_page),).view().is_init(),
        old(pages).spec_index(page_ptr2page_index(allocator_page),).view().view().perm_inv(),
        old(pages).spec_index(page_ptr2page_index(allocator_page),).view().view().perm_4k.view().is_some(),
        old(pages).spec_index(page_ptr2page_index(allocator_page),).view().view().state is Owned4k,
        old(pages).spec_index(page_ptr2page_index(allocator_page),).view().view().addr == allocator_page,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(allocator_page), TypedLockMode::Write,),
        allocator_page_lock_perm.state() is WriteLock,
        allocator_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_page_lock_perm.lock_id() == old(pages).spec_index(
                page_ptr2page_index(allocator_page),
            ).view().locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        lock_id_set_aligned(final(lctx)),
        final(pages).inv(),
        page_array_wf(*final(pages)),
        final(allocator_map).perms_wf(),
        allocator_perms_wf(*old(allocator_map)) ==> allocator_perms_wf(*final(allocator_map)),
        final(pages).typed_lock_map_aligned(final(lctx).page_lock_map(), final(lctx).thread_id(),),
        final(allocator_map).typed_quota_lock_map_aligned(quota_lock_map, final(lctx).thread_id(),),
        final(allocator_map).typed_cache_lock_map_aligned(cache_lock_map, final(lctx).thread_id(),),
        final(allocator_map).typed_global_pool_lock_map_aligned(global_pool_lock_map, final(lctx).thread_id(),),
        typed_lock_maps_inserted(
            old(lctx),
            final(lctx),
            KernelObjId::Page(page_ptr2page_index(allocator_page)),
            TypedHeldLock {
                lock_id: final(pages).lock_id_by_index(
                    page_ptr2page_index(allocator_page),
                ),
                mode: TypedLockMode::Write,
            },
        ),
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom(),
        final(pages).entries_unchanged_except(old(pages), page_ptr2page_index(allocator_page),),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().mappings()]
            #![trigger old(pages).spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().mappings() == old(pages).spec_index(index).view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(lctx).page_lock_map().get(index)]
            index != page_ptr2page_index(allocator_page) ==> final(lctx).page_lock_map().get(index) == old(lctx).page_lock_map().get(index),
        final(pages).spec_index(
            page_ptr2page_index(allocator_page),
        ).view().view().state == (PageState::Allocated4k {
            state: allocator_state,
        }),
        final(pages).spec_index(page_ptr2page_index(allocator_page),).view().view().owning_container == child_container_ptr,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(allocator_page), TypedLockMode::Write,),
        allocator_page_lock_perm.lock_id() == final(pages).spec_index(
                page_ptr2page_index(allocator_page),
            ).view().locking_thread()->Write_lock_id,
        final(allocator_map).dom()
            =~= old(allocator_map).dom().insert(allocator_page),
        final(allocator_map).spec_index(allocator_page) == allocator_value,
        forall|ptr: RwLockPageAllocatorPtr|
            #![trigger final(allocator_map).spec_index(ptr)]
            old(allocator_map).dom().contains(ptr) ==> final(allocator_map).spec_index(ptr) == old(allocator_map).spec_index(ptr),
{
    let allocator_index = page_ptr2page_index(allocator_page);
    let ghost pages_before = *pages;
    let ghost lctx_before = *lctx;
    let ghost allocator_map_before = *allocator_map;

    let Tracked(allocator_perm) =
        retype_owned_4k_page_for_new_container(pages, child_container_ptr, allocator_page, allocator_state, Tracked(&mut *lctx), Tracked(allocator_page_lock_perm),);
    allocator_map.retype_page_to_allocator_and_insert(
        allocator_page,
        allocator_value,
        Tracked(allocator_perm),
    );

    proof {
        assert(lctx.page_lock_map().dom() == lctx_before.page_lock_map().dom()) by { reveal(typed_lock_maps_inserted); reveal(typed_lock_map_contains_mode); broadcast use vstd::map::lemma_map_insert_domain; };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), allocator_index, TypedLockMode::Write,)) by { reveal(typed_lock_maps_inserted); reveal(typed_lock_map_contains_mode); };
        assert(pages.typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id(),)) by { reveal(typed_lock_maps_inserted); reveal(LockedArray::typed_lock_map_aligned); };
        assert(allocator_map.typed_quota_lock_map_aligned(quota_lock_map, lctx.thread_id(),)) by {
            assert(!quota_lock_map.dom().contains(allocator_page)) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); };
            reveal(UnLockedMap::typed_quota_lock_map_aligned);
            broadcast use vstd::map::lemma_map_insert_domain;
            broadcast use vstd::map::lemma_map_new_index;
        };
        assert(allocator_map.typed_cache_lock_map_aligned(cache_lock_map, lctx.thread_id(),)) by {
            reveal(UnLockedMap::typed_cache_lock_map_aligned); broadcast use vstd::map::lemma_map_insert_domain;
            broadcast use vstd::map::lemma_map_new_index;
        };
        assert(allocator_map.typed_global_pool_lock_map_aligned(global_pool_lock_map, lctx.thread_id(),)) by {
            assert(!global_pool_lock_map.dom().contains(allocator_page)) by { reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
            reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
            broadcast use vstd::map::lemma_map_insert_domain;
            broadcast use vstd::map::lemma_map_new_index;
        };
        assert(allocator_page_lock_perm.lock_id() == pages.spec_index(allocator_index).view().locking_thread()->Write_lock_id);
        assert(allocator_map_before.dom() == old(allocator_map).dom());
        if allocator_perms_wf(*old(allocator_map)) {
            assert(allocator_perms_wf(*allocator_map)) by { reveal(allocator_perms_wf); };
        }
    }
}

pub(super) fn publish_new_container_allocators(
    pages: &mut PageLockedArray, allocator_4k_map: &mut PageAllocatorUnLockedMap, allocator_2m_map: &mut PageAllocatorUnLockedMap,
    allocator_1g_map: &mut PageAllocatorUnLockedMap, child_container_ptr: RwLockContainerPtr, allocator_4k_page: PagePtr,
    allocator_2m_page: PagePtr, allocator_1g_page: PagePtr, allocator_4k_value: PageAllocator, allocator_2m_value: PageAllocator,
    allocator_1g_value: PageAllocator, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(allocator_4k_page_lock_perm): Tracked<&LockPerm>,
    Tracked(allocator_2m_page_lock_perm): Tracked<&LockPerm>, Tracked(allocator_1g_page_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(pages).inv(),
        page_array_wf(*old(pages)),
        old(allocator_4k_map).perms_wf(),
        old(allocator_2m_map).perms_wf(),
        old(allocator_1g_map).perms_wf(),
        allocator_perms_wf(*old(allocator_4k_map)),
        allocator_perms_wf(*old(allocator_2m_map)),
        allocator_perms_wf(*old(allocator_1g_map)),
        old(pages).typed_lock_map_aligned(old(lctx).page_lock_map(), old(lctx).thread_id(),),
        old(allocator_4k_map).typed_quota_lock_map_aligned(old(lctx).allocator_quota_4k_lock_map(), old(lctx).thread_id(),),
        old(allocator_4k_map).typed_cache_lock_map_aligned(old(lctx).allocator_cache_4k_lock_map(), old(lctx).thread_id(),),
        old(allocator_4k_map).typed_global_pool_lock_map_aligned(old(lctx).allocator_global_pool_4k_lock_map(), old(lctx).thread_id(),),
        old(allocator_2m_map).typed_quota_lock_map_aligned(old(lctx).allocator_quota_2m_lock_map(), old(lctx).thread_id(),),
        old(allocator_2m_map).typed_cache_lock_map_aligned(old(lctx).allocator_cache_2m_lock_map(), old(lctx).thread_id(),),
        old(allocator_2m_map).typed_global_pool_lock_map_aligned(old(lctx).allocator_global_pool_2m_lock_map(), old(lctx).thread_id(),),
        old(allocator_1g_map).typed_quota_lock_map_aligned(old(lctx).allocator_quota_1g_lock_map(), old(lctx).thread_id(),),
        old(allocator_1g_map).typed_cache_lock_map_aligned(old(lctx).allocator_cache_1g_lock_map(), old(lctx).thread_id(),),
        old(allocator_1g_map).typed_global_pool_lock_map_aligned(old(lctx).allocator_global_pool_1g_lock_map(), old(lctx).thread_id(),),
        lock_id_set_aligned(old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        allocator_4k_value.inv(),
        allocator_2m_value.inv(),
        allocator_1g_value.inv(),
        !allocator_4k_value.quota.locked(),
        !allocator_2m_value.quota.locked(),
        !allocator_1g_value.quota.locked(),
        !allocator_4k_value.global_pool.locked(),
        !allocator_2m_value.global_pool.locked(),
        !allocator_1g_value.global_pool.locked(),
        forall|cpu_id: CpuId|
            #![trigger allocator_4k_value.cpu_caches.spec_index(cpu_id).view().locked()]
            index_valid(NUM_CPUS, cpu_id) ==> !allocator_4k_value.cpu_caches.spec_index(cpu_id).view().locked(),
        forall|cpu_id: CpuId|
            #![trigger allocator_2m_value.cpu_caches.spec_index(cpu_id).view().locked()]
            index_valid(NUM_CPUS, cpu_id) ==> !allocator_2m_value.cpu_caches.spec_index(cpu_id).view().locked(),
        forall|cpu_id: CpuId|
            #![trigger allocator_1g_value.cpu_caches.spec_index(cpu_id).view().locked()]
            index_valid(NUM_CPUS, cpu_id) ==> !allocator_1g_value.cpu_caches.spec_index(cpu_id).view().locked(),
        !old(allocator_4k_map).dom().contains(allocator_4k_page),
        !old(allocator_2m_map).dom().contains(allocator_2m_page),
        !old(allocator_1g_map).dom().contains(allocator_1g_page),
        page_ptr_valid(allocator_4k_page),
        page_ptr_valid(allocator_2m_page),
        page_ptr_valid(allocator_1g_page),
        page_ptr2page_index(allocator_4k_page) != page_ptr2page_index(allocator_2m_page),
        page_ptr2page_index(allocator_4k_page) != page_ptr2page_index(allocator_1g_page),
        page_ptr2page_index(allocator_2m_page) != page_ptr2page_index(allocator_1g_page),
        old(pages).spec_index(page_ptr2page_index(allocator_4k_page)).view().is_init(),
        old(pages).spec_index(page_ptr2page_index(allocator_2m_page)).view().is_init(),
        old(pages).spec_index(page_ptr2page_index(allocator_1g_page)).view().is_init(),
        old(pages).spec_index(page_ptr2page_index(allocator_4k_page)).view().view().perm_inv(),
        old(pages).spec_index(page_ptr2page_index(allocator_2m_page)).view().view().perm_inv(),
        old(pages).spec_index(page_ptr2page_index(allocator_1g_page)).view().view().perm_inv(),
        old(pages).spec_index(page_ptr2page_index(allocator_4k_page)).view().view().perm_4k.view().is_some(),
        old(pages).spec_index(page_ptr2page_index(allocator_2m_page)).view().view().perm_4k.view().is_some(),
        old(pages).spec_index(page_ptr2page_index(allocator_1g_page)).view().view().perm_4k.view().is_some(),
        old(pages).spec_index(page_ptr2page_index(allocator_4k_page)).view().view().state is Owned4k,
        old(pages).spec_index(page_ptr2page_index(allocator_2m_page)).view().view().state is Owned4k,
        old(pages).spec_index(page_ptr2page_index(allocator_1g_page)).view().view().state is Owned4k,
        old(pages).spec_index(page_ptr2page_index(allocator_4k_page)).view().view().addr == allocator_4k_page,
        old(pages).spec_index(page_ptr2page_index(allocator_2m_page)).view().view().addr == allocator_2m_page,
        old(pages).spec_index(page_ptr2page_index(allocator_1g_page)).view().view().addr == allocator_1g_page,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(allocator_4k_page), TypedLockMode::Write,),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(allocator_2m_page), TypedLockMode::Write,),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(allocator_1g_page), TypedLockMode::Write,),
        allocator_4k_page_lock_perm.state() is WriteLock,
        allocator_2m_page_lock_perm.state() is WriteLock,
        allocator_1g_page_lock_perm.state() is WriteLock,
        allocator_4k_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_2m_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_1g_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_4k_page_lock_perm.lock_id() == old(pages).spec_index(
                page_ptr2page_index(allocator_4k_page),
            ).view().locking_thread()->Write_lock_id,
        allocator_2m_page_lock_perm.lock_id() == old(pages).spec_index(
                page_ptr2page_index(allocator_2m_page),
            ).view().locking_thread()->Write_lock_id,
        allocator_1g_page_lock_perm.lock_id() == old(pages).spec_index(
                page_ptr2page_index(allocator_1g_page),
            ).view().locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        lock_id_set_aligned(final(lctx)),
        final(pages).inv(),
        page_array_wf(*final(pages)),
        final(allocator_4k_map).perms_wf(),
        final(allocator_2m_map).perms_wf(),
        final(allocator_1g_map).perms_wf(),
        allocator_perms_wf(*final(allocator_4k_map)),
        allocator_perms_wf(*final(allocator_2m_map)),
        allocator_perms_wf(*final(allocator_1g_map)),
        final(pages).typed_lock_map_aligned(final(lctx).page_lock_map(), final(lctx).thread_id(),),
        final(allocator_4k_map).typed_quota_lock_map_aligned(final(lctx).allocator_quota_4k_lock_map(), final(lctx).thread_id(),),
        final(allocator_4k_map).typed_cache_lock_map_aligned(final(lctx).allocator_cache_4k_lock_map(), final(lctx).thread_id(),),
        final(allocator_4k_map).typed_global_pool_lock_map_aligned(final(lctx).allocator_global_pool_4k_lock_map(), final(lctx).thread_id(),),
        final(allocator_2m_map).typed_quota_lock_map_aligned(final(lctx).allocator_quota_2m_lock_map(), final(lctx).thread_id(),),
        final(allocator_2m_map).typed_cache_lock_map_aligned(final(lctx).allocator_cache_2m_lock_map(), final(lctx).thread_id(),),
        final(allocator_2m_map).typed_global_pool_lock_map_aligned(final(lctx).allocator_global_pool_2m_lock_map(), final(lctx).thread_id(),),
        final(allocator_1g_map).typed_quota_lock_map_aligned(final(lctx).allocator_quota_1g_lock_map(), final(lctx).thread_id(),),
        final(allocator_1g_map).typed_cache_lock_map_aligned(final(lctx).allocator_cache_1g_lock_map(), final(lctx).thread_id(),),
        final(allocator_1g_map).typed_global_pool_lock_map_aligned(final(lctx).allocator_global_pool_1g_lock_map(), final(lctx).thread_id(),),
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index)]
            index_valid(NUM_PAGES, index) && index != page_ptr2page_index(allocator_4k_page) && index != page_ptr2page_index(allocator_2m_page) && index != page_ptr2page_index(allocator_1g_page) ==> final(pages).spec_index(index) == old(pages).spec_index(index),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().mappings()]
            #![trigger old(pages).spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().mappings() == old(pages).spec_index(index).view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(lctx).page_lock_map().get(index)]
            index != page_ptr2page_index(allocator_4k_page) && index != page_ptr2page_index(allocator_2m_page) && index != page_ptr2page_index(allocator_1g_page) ==> final(lctx).page_lock_map().get(index) == old(lctx).page_lock_map().get(index),
        forall|index: PageIndex|
            #![trigger old(pages).spec_index(index).view().view().state]
            index_valid(NUM_PAGES, index) && old(pages).spec_index(index).view().view().state is Merged2m ==> {
                &&& final(pages).spec_index(index) == old(pages).spec_index(index)
                &&& final(lctx).page_lock_map().get(index) == old(lctx).page_lock_map().get(index)
            },
        final(pages).spec_index(page_ptr2page_index(allocator_4k_page)).view().view().state == (PageState::Allocated4k {
                state: Allocated4KPageState::As4KAllocator,
            }),
        final(pages).spec_index(page_ptr2page_index(allocator_2m_page)).view().view().state == (PageState::Allocated4k {
                state: Allocated4KPageState::As2MAllocator,
            }),
        final(pages).spec_index(page_ptr2page_index(allocator_1g_page)).view().view().state == (PageState::Allocated4k {
                state: Allocated4KPageState::As1GAllocator,
            }),
        final(pages).spec_index(page_ptr2page_index(allocator_4k_page)).view().view().owning_container == child_container_ptr,
        final(pages).spec_index(page_ptr2page_index(allocator_2m_page)).view().view().owning_container == child_container_ptr,
        final(pages).spec_index(page_ptr2page_index(allocator_1g_page)).view().view().owning_container == child_container_ptr,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(allocator_4k_page), TypedLockMode::Write,),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(allocator_2m_page), TypedLockMode::Write,),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(allocator_1g_page), TypedLockMode::Write,),
        allocator_4k_page_lock_perm.lock_id() == final(pages).spec_index(
                page_ptr2page_index(allocator_4k_page),
            ).view().locking_thread()->Write_lock_id,
        allocator_2m_page_lock_perm.lock_id() == final(pages).spec_index(
                page_ptr2page_index(allocator_2m_page),
            ).view().locking_thread()->Write_lock_id,
        allocator_1g_page_lock_perm.lock_id() == final(pages).spec_index(
                page_ptr2page_index(allocator_1g_page),
            ).view().locking_thread()->Write_lock_id,
        final(allocator_4k_map).dom()
            =~= old(allocator_4k_map).dom().insert(allocator_4k_page),
        final(allocator_2m_map).dom()
            =~= old(allocator_2m_map).dom().insert(allocator_2m_page),
        final(allocator_1g_map).dom()
            =~= old(allocator_1g_map).dom().insert(allocator_1g_page),
        final(allocator_4k_map).spec_index(allocator_4k_page) == allocator_4k_value,
        final(allocator_2m_map).spec_index(allocator_2m_page) == allocator_2m_value,
        final(allocator_1g_map).spec_index(allocator_1g_page) == allocator_1g_value,
        forall|ptr: RwLockPageAllocatorPtr|
            #![trigger final(allocator_4k_map).spec_index(ptr)]
            old(allocator_4k_map).dom().contains(ptr) ==> final(allocator_4k_map).spec_index(ptr) == old(allocator_4k_map).spec_index(ptr),
        forall|ptr: RwLockPageAllocatorPtr|
            #![trigger final(allocator_2m_map).spec_index(ptr)]
            old(allocator_2m_map).dom().contains(ptr) ==> final(allocator_2m_map).spec_index(ptr) == old(allocator_2m_map).spec_index(ptr),
        forall|ptr: RwLockPageAllocatorPtr|
            #![trigger final(allocator_1g_map).spec_index(ptr)]
            old(allocator_1g_map).dom().contains(ptr) ==> final(allocator_1g_map).spec_index(ptr) == old(allocator_1g_map).spec_index(ptr),
{
    let allocator_4k_index = page_ptr2page_index(allocator_4k_page);
    let allocator_2m_index = page_ptr2page_index(allocator_2m_page);
    let allocator_1g_index = page_ptr2page_index(allocator_1g_page);
    let ghost pages_before = *pages;
    let ghost lctx_before = *lctx;
    let ghost allocator_4k_quota_lock_map =
        lctx.allocator_quota_4k_lock_map();
    let ghost allocator_4k_cache_lock_map =
        lctx.allocator_cache_4k_lock_map();
    let ghost allocator_4k_global_pool_lock_map =
        lctx.allocator_global_pool_4k_lock_map();
    let ghost allocator_2m_quota_lock_map =
        lctx.allocator_quota_2m_lock_map();
    let ghost allocator_2m_cache_lock_map =
        lctx.allocator_cache_2m_lock_map();
    let ghost allocator_2m_global_pool_lock_map =
        lctx.allocator_global_pool_2m_lock_map();
    let ghost allocator_1g_quota_lock_map =
        lctx.allocator_quota_1g_lock_map();
    let ghost allocator_1g_cache_lock_map =
        lctx.allocator_cache_1g_lock_map();
    let ghost allocator_1g_global_pool_lock_map =
        lctx.allocator_global_pool_1g_lock_map();

    publish_new_container_allocator(
        pages, allocator_4k_map, child_container_ptr, allocator_4k_page, Allocated4KPageState::As4KAllocator, allocator_4k_value,
        Ghost(allocator_4k_quota_lock_map), Ghost(allocator_4k_cache_lock_map), Ghost(allocator_4k_global_pool_lock_map),
        Tracked(&mut *lctx), Tracked(allocator_4k_page_lock_perm),
    );
    let ghost pages_after_4k = *pages;
    let ghost lctx_after_4k = *lctx;
    proof {
        assert(pages.spec_index(allocator_2m_index) == pages_before.spec_index(allocator_2m_index));
        assert(pages.spec_index(allocator_1g_index) == pages_before.spec_index(allocator_1g_index));
        assert(lctx.allocator_2m_lock_maps() == lctx_before.allocator_2m_lock_maps()) by { reveal(typed_lock_maps_inserted); };
        assert(lctx.allocator_1g_lock_maps() == lctx_before.allocator_1g_lock_maps()) by { reveal(typed_lock_maps_inserted); };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), allocator_2m_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(allocator_2m_index) == lctx_before.page_lock_map().get(allocator_2m_index));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), allocator_1g_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(allocator_1g_index) == lctx_before.page_lock_map().get(allocator_1g_index));
            reveal(typed_lock_map_contains_mode);
        };
    }

    publish_new_container_allocator(
        pages, allocator_2m_map, child_container_ptr, allocator_2m_page, Allocated4KPageState::As2MAllocator, allocator_2m_value,
        Ghost(allocator_2m_quota_lock_map), Ghost(allocator_2m_cache_lock_map), Ghost(allocator_2m_global_pool_lock_map),
        Tracked(&mut *lctx), Tracked(allocator_2m_page_lock_perm),
    );
    let ghost pages_after_2m = *pages;
    let ghost lctx_after_2m = *lctx;
    proof {
        assert(pages.spec_index(allocator_4k_index) == pages_after_4k.spec_index(allocator_4k_index));
        assert(pages.spec_index(allocator_1g_index) == pages_after_4k.spec_index(allocator_1g_index));
        assert(lctx.allocator_1g_lock_maps() == lctx_after_4k.allocator_1g_lock_maps()) by { reveal(typed_lock_maps_inserted); };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), allocator_1g_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(allocator_1g_index) == lctx_after_4k.page_lock_map().get(allocator_1g_index));
            reveal(typed_lock_map_contains_mode);
        };
    }

    publish_new_container_allocator(
        pages, allocator_1g_map, child_container_ptr, allocator_1g_page, Allocated4KPageState::As1GAllocator, allocator_1g_value,
        Ghost(allocator_1g_quota_lock_map), Ghost(allocator_1g_cache_lock_map), Ghost(allocator_1g_global_pool_lock_map),
        Tracked(&mut *lctx), Tracked(allocator_1g_page_lock_perm),
    );

    proof {
        assert(lctx.page_lock_map().dom() == lctx_before.page_lock_map().dom());
        assert(lctx.cpu_lock_map() == lctx_before.cpu_lock_map()) by { reveal(typed_lock_maps_inserted); };
        assert(lctx.pcid_needflush_lock_map() == lctx_before.pcid_needflush_lock_map()) by { reveal(typed_lock_maps_inserted); };
        assert(lctx.container_lock_map() == lctx_before.container_lock_map()) by { reveal(typed_lock_maps_inserted); };
        assert(lctx.process_lock_map() == lctx_before.process_lock_map()) by { reveal(typed_lock_maps_inserted); };
        assert(lctx.thread_lock_map() == lctx_before.thread_lock_map()) by { reveal(typed_lock_maps_inserted); };
        assert(lctx.endpoint_lock_map() == lctx_before.endpoint_lock_map()) by { reveal(typed_lock_maps_inserted); };
        assert(lctx.scheduler_lock_map() == lctx_before.scheduler_lock_map()) by { reveal(typed_lock_maps_inserted); };
        assert(lctx.pcid_allocator_lock_map() == lctx_before.pcid_allocator_lock_map()) by { reveal(typed_lock_maps_inserted); };
        assert(lctx.cpu_set_lock_map() == lctx_before.cpu_set_lock_map()) by { reveal(typed_lock_maps_inserted); };
        assert(lctx.pagetable_lock_map() == lctx_before.pagetable_lock_map()) by { reveal(typed_lock_maps_inserted); };
        assert(lctx.iommu_table_lock_map() == lctx_before.iommu_table_lock_map()) by { reveal(typed_lock_maps_inserted); };
        assert(lctx.allocator_4k_lock_maps() == lctx_before.allocator_4k_lock_maps()) by { reveal(typed_lock_maps_inserted); };
        assert(lctx.allocator_2m_lock_maps() == lctx_before.allocator_2m_lock_maps()) by { reveal(typed_lock_maps_inserted); };
        assert(lctx.allocator_1g_lock_maps() == lctx_before.allocator_1g_lock_maps()) by { reveal(typed_lock_maps_inserted); };
        assert(pages.spec_index(allocator_4k_index) == pages_after_2m.spec_index(allocator_4k_index));
        assert(pages.spec_index(allocator_2m_index) == pages_after_2m.spec_index(allocator_2m_index));
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), allocator_4k_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(allocator_4k_index) == lctx_after_2m.page_lock_map().get(allocator_4k_index));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), allocator_2m_index, TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(allocator_2m_index) == lctx_after_2m.page_lock_map().get(allocator_2m_index));
            reveal(typed_lock_map_contains_mode);
        };
        assert(allocator_4k_map.typed_quota_lock_map_aligned(lctx.allocator_quota_4k_lock_map(), lctx.thread_id(),));
        assert(allocator_4k_map.typed_cache_lock_map_aligned(lctx.allocator_cache_4k_lock_map(), lctx.thread_id(),));
        assert(allocator_4k_map.typed_global_pool_lock_map_aligned(lctx.allocator_global_pool_4k_lock_map(), lctx.thread_id(),));
        assert(allocator_2m_map.typed_quota_lock_map_aligned(lctx.allocator_quota_2m_lock_map(), lctx.thread_id(),));
        assert(allocator_2m_map.typed_cache_lock_map_aligned(lctx.allocator_cache_2m_lock_map(), lctx.thread_id(),));
        assert(allocator_2m_map.typed_global_pool_lock_map_aligned(lctx.allocator_global_pool_2m_lock_map(), lctx.thread_id(),));
        assert(allocator_perms_wf(*allocator_4k_map));
        assert(allocator_perms_wf(*allocator_2m_map));
    }
}


}
