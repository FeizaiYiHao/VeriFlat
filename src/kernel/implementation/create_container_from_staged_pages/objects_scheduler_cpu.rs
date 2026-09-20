use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
pub(super) fn publish_new_container_scheduler(
    krnl: &mut KernelK, child_container_ptr: RwLockContainerPtr, child_scheduler_ptr: RwLockSchedulerPtr, scheduler_page: PagePtr,
    cpu_set_index: PageIndex, scheduler_value: Scheduler, Ghost(funding_pages): Ghost<Seq<PagePtr>>, container_head: PageIndex,
    pcid_allocator_head: PageIndex, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(scheduler_page_lock_perm): Tracked<&LockPerm>,
    Tracked(container_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
    Tracked(pcid_allocator_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
) -> (ret: Tracked<LockPerm>)
    requires
        old(krnl).pg_arr.inv(),
        page_array_wf(old(krnl).pg_arr),
        old(krnl).sched_mp.perms_wf(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        scheduler_value.inv(),
        child_scheduler_ptr == scheduler_page,
        !old(krnl).sched_mp.dom().contains(child_scheduler_ptr),
        page_ptr_valid(scheduler_page),
        index_valid(NUM_PAGES, cpu_set_index),
        page_ptr2page_index(scheduler_page) != cpu_set_index,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page),).view().is_init(),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page),).view().view().perm_inv(),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page),).view().view().perm_4k.view().is_some(),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page),).view().view().state is Owned4k,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page),).view().view().addr == scheduler_page,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(scheduler_page), TypedLockMode::Write,),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), cpu_set_index, TypedLockMode::Write,),
        scheduler_page_lock_perm.state() is WriteLock,
        scheduler_page_lock_perm.thread_id() == old(lctx).thread_id(),
        scheduler_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(
                page_ptr2page_index(scheduler_page),
            ).view().locking_thread()->Write_lock_id,
        !funding_pages.to_set().contains(scheduler_page),
        staged_4k_page_chain(old(krnl).pg_arr, funding_pages),
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, old(krnl).pg_arr, old(lctx), container_head,),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, old(krnl).pg_arr, old(lctx), pcid_allocator_head,),
        !page_2m_tail_indices(container_head).contains(page_ptr2page_index(scheduler_page),),
        !page_2m_tail_indices(pcid_allocator_head).contains(page_ptr2page_index(scheduler_page),),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        lock_id_set_aligned(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)), *final(krnl) == (KernelK {
            pg_arr: final(krnl).pg_arr,
            sched_mp: final(krnl).sched_mp,
            ..*old(krnl)
        }),
        final(krnl).pg_arr.inv(),
        page_array_wf(final(krnl).pg_arr),
        final(krnl).sched_mp.perms_wf(),
        scheduler_perms_wf(old(krnl).sched_mp) ==> scheduler_perms_wf(final(krnl).sched_mp),
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom(),
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(scheduler_page),),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index).view().view().mappings()]
            #![trigger old(krnl).pg_arr.spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(krnl).pg_arr.spec_index(index).view().view().mappings() == old(krnl).pg_arr.spec_index(index).view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(lctx).page_lock_map().get(index)]
            index != page_ptr2page_index(scheduler_page) ==> final(lctx).page_lock_map().get(index) == old(lctx).page_lock_map().get(index),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).scheduler_lock_map().dom() == old(lctx).scheduler_lock_map().dom().insert(child_scheduler_ptr),
        typed_lock_map_contains_mode(final(lctx).scheduler_lock_map(), child_scheduler_ptr, TypedLockMode::Write,),
        forall|ptr: RwLockSchedulerPtr|
            #![trigger final(lctx).scheduler_lock_map().get(ptr)]
            ptr != child_scheduler_ptr ==> final(lctx).scheduler_lock_map().get(ptr) == old(lctx).scheduler_lock_map().get(ptr),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), cpu_set_index, TypedLockMode::Write,),
        final(krnl).pg_arr.spec_index(
            page_ptr2page_index(scheduler_page),
        ).view().view().state == (PageState::Allocated4k {
            state: Allocated4KPageState::AsScheduler,
        }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(scheduler_page),).view().view().owning_container == child_container_ptr,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(scheduler_page), TypedLockMode::Write,),
        scheduler_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(
                page_ptr2page_index(scheduler_page),
            ).view().locking_thread()->Write_lock_id,
        final(krnl).sched_mp.dom()
            =~= old(krnl).sched_mp.dom().insert(child_scheduler_ptr),
        final(krnl).sched_mp.spec_index(child_scheduler_ptr).view() == scheduler_value,
        forall|ptr: RwLockSchedulerPtr|
            #![trigger final(krnl).sched_mp.spec_index(ptr)]
            old(krnl).sched_mp.dom().contains(ptr) ==> final(krnl).sched_mp.spec_index(ptr) == old(krnl).sched_mp.spec_index(ptr),
        ret.view().state() is WriteLock,
        ret.view().thread_id() == final(lctx).thread_id(),
        ret.view().lock_id() == final(krnl).sched_mp.spec_index(child_scheduler_ptr).locking_thread()->Write_lock_id,
        staged_4k_page_chain(final(krnl).pg_arr, funding_pages),
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, final(krnl).pg_arr, final(lctx), container_head,),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, final(krnl).pg_arr, final(lctx), pcid_allocator_head,),
{
    let scheduler_index = page_ptr2page_index(scheduler_page);
    let ghost pages_before_scheduler = krnl.pg_arr;
    let ghost lctx_before_scheduler = *lctx;
    let Tracked(scheduler_perm) =
        retype_owned_4k_page_for_new_container(&mut krnl.pg_arr, child_container_ptr, scheduler_page, Allocated4KPageState::AsScheduler, Tracked(&mut *lctx), Tracked(scheduler_page_lock_perm),);
    proof {
        vstd::set::lemma_set_insert_different(lctx_before_scheduler.page_lock_map().dom(), cpu_set_index, scheduler_index,);
        assert(krnl.pg_arr.typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id(),)) by { reveal(typed_lock_maps_inserted); };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), cpu_set_index, TypedLockMode::Write,)) by { reveal(typed_lock_maps_inserted); reveal(typed_lock_map_contains_mode); };
        assert(lctx.typed_lock_entry(KernelObjId::Scheduler(child_scheduler_ptr),) is None) by { reveal(LocalContext::typed_lock_entry); reveal(typed_lock_maps_aligned); reveal(LockedMap::typed_lock_map_aligned); };
        assert(scheduler_perm.addr() == child_scheduler_ptr);
    }
    let Tracked(child_scheduler_lock_perm) =
        krnl.sched_mp.retype_4k_and_insert(
            child_scheduler_ptr,
            scheduler_value,
            (),
            Ghost(()),
            Tracked(scheduler_perm),
            Tracked(&mut *lctx),
            Ghost(KernelObjId::Scheduler(child_scheduler_ptr)),
        );
    proof {
        assert(krnl.sched_mp.typed_lock_map_aligned(lctx.scheduler_lock_map(), lctx.thread_id(),)) by {
            broadcast use vstd::set::lemma_set_insert_different; reveal(typed_lock_maps_inserted);
            reveal(LockedMap::typed_lock_map_aligned); broadcast use vstd::map::lemma_map_insert_domain;
            broadcast use vstd::map::lemma_map_new_index;
        };
        assert(typed_lock_map_contains_mode(lctx.scheduler_lock_map(), child_scheduler_ptr, TypedLockMode::Write,)) by { reveal(typed_lock_maps_inserted); reveal(typed_lock_map_contains_mode); };
        assert(typed_lock_maps_aligned(krnl, lctx)) by {
            broadcast use vstd::set::lemma_set_insert_different;
            reveal(typed_lock_maps_aligned);
            reveal(LockedArray::typed_lock_map_aligned);
            reveal(LockedMap::typed_lock_map_aligned);
            reveal(UnLockedMap::typed_quota_lock_map_aligned);
            reveal(UnLockedMap::typed_cache_lock_map_aligned);
            reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
            broadcast use vstd::map::lemma_map_insert_domain;
            broadcast use vstd::map::lemma_map_new_index;
        };
        assert(staged_4k_page_chain(krnl.pg_arr, funding_pages)) by {
            staged_4k_page_chain_page_ptrs_valid(pages_before_scheduler, funding_pages,);
            page_ptr_seq_indices_excludes_page(funding_pages, scheduler_page,); reveal(staged_4k_page_chain);
        };
        assert(owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, krnl.pg_arr, lctx, container_head,)) by { reveal(owned_2m_tail_lock_perms_wf); reveal(page_2m_tail_indices); };
        assert(owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, krnl.pg_arr, lctx, pcid_allocator_head,)) by { reveal(owned_2m_tail_lock_perms_wf); reveal(page_2m_tail_indices); };
        assert({
            &&& lctx.cpu_lock_map() == lctx_before_scheduler.cpu_lock_map()
            &&& lctx.pcid_needflush_lock_map() == lctx_before_scheduler.pcid_needflush_lock_map()
            &&& lctx.container_lock_map() == lctx_before_scheduler.container_lock_map()
            &&& lctx.process_lock_map() == lctx_before_scheduler.process_lock_map()
            &&& lctx.thread_lock_map() == lctx_before_scheduler.thread_lock_map()
            &&& lctx.endpoint_lock_map() == lctx_before_scheduler.endpoint_lock_map()
            &&& lctx.cpu_set_lock_map() == lctx_before_scheduler.cpu_set_lock_map()
            &&& lctx.pcid_allocator_lock_map() == lctx_before_scheduler.pcid_allocator_lock_map()
            &&& lctx.pagetable_lock_map() == lctx_before_scheduler.pagetable_lock_map()
            &&& lctx.iommu_table_lock_map() == lctx_before_scheduler.iommu_table_lock_map()
            &&& lctx.allocator_4k_lock_maps() == lctx_before_scheduler.allocator_4k_lock_maps()
            &&& lctx.allocator_2m_lock_maps() == lctx_before_scheduler.allocator_2m_lock_maps()
            &&& lctx.allocator_1g_lock_maps() == lctx_before_scheduler.allocator_1g_lock_maps()
        }) by { reveal(typed_lock_maps_inserted); };
        assert(lctx.scheduler_lock_map().dom() == lctx_before_scheduler.scheduler_lock_map().dom().insert(child_scheduler_ptr)) by { reveal(typed_lock_maps_inserted); };
        if scheduler_perms_wf(old(krnl).sched_mp) {
            assert(scheduler_perms_wf(krnl.sched_mp)) by { reveal(scheduler_perms_wf); };
        }
    }
    Tracked(child_scheduler_lock_perm)
}

pub(super) fn publish_new_container_cpu_set(
    krnl: &mut KernelK, child_container_ptr: RwLockContainerPtr, child_cpu_set_ptr: RwLockCpuSetPtr, cpu_set_page: PagePtr,
    cpu_set_value: CpuSet, Ghost(funding_pages): Ghost<Seq<PagePtr>>, container_head: PageIndex, pcid_allocator_head: PageIndex,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(cpu_set_page_lock_perm): Tracked<&LockPerm>,
    Tracked(container_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
    Tracked(pcid_allocator_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
)
    requires
        old(krnl).pg_arr.inv(),
        page_array_wf(old(krnl).pg_arr),
        old(krnl).cpu_set_mp.perms_wf(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        cpu_set_value.inv(),
        child_cpu_set_ptr == cpu_set_page,
        !old(krnl).cpu_set_mp.dom().contains(child_cpu_set_ptr),
        page_ptr_valid(cpu_set_page),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page),).view().is_init(),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page),).view().view().perm_inv(),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page),).view().view().perm_4k.view().is_some(),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page),).view().view().state is Owned4k,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page),).view().view().addr == cpu_set_page,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(cpu_set_page), TypedLockMode::Write,),
        cpu_set_page_lock_perm.state() is WriteLock,
        cpu_set_page_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_set_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(
                page_ptr2page_index(cpu_set_page),
            ).view().locking_thread()->Write_lock_id,
        !funding_pages.to_set().contains(cpu_set_page),
        staged_4k_page_chain(old(krnl).pg_arr, funding_pages),
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, old(krnl).pg_arr, old(lctx), container_head,),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, old(krnl).pg_arr, old(lctx), pcid_allocator_head,),
        !page_2m_tail_indices(container_head).contains(page_ptr2page_index(cpu_set_page),),
        !page_2m_tail_indices(pcid_allocator_head).contains(page_ptr2page_index(cpu_set_page),),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        lock_id_set_aligned(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)), *final(krnl) == (KernelK {
            pg_arr: final(krnl).pg_arr,
            cpu_set_mp: final(krnl).cpu_set_mp,
            ..*old(krnl)
        }),
        final(krnl).pg_arr.inv(),
        page_array_wf(final(krnl).pg_arr),
        final(krnl).cpu_set_mp.perms_wf(),
        cpu_set_perms_wf(old(krnl).cpu_set_mp) ==> cpu_set_perms_wf(final(krnl).cpu_set_mp),
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom(),
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(cpu_set_page),),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index).view().view().mappings()]
            #![trigger old(krnl).pg_arr.spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(krnl).pg_arr.spec_index(index).view().view().mappings() == old(krnl).pg_arr.spec_index(index).view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(lctx).page_lock_map().get(index)]
            index != page_ptr2page_index(cpu_set_page) ==> final(lctx).page_lock_map().get(index) == old(lctx).page_lock_map().get(index),
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
        final(krnl).pg_arr.spec_index(
            page_ptr2page_index(cpu_set_page),
        ).view().view().state == (PageState::Allocated4k {
            state: Allocated4KPageState::AsCpuSet,
        }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(cpu_set_page),).view().view().owning_container == child_container_ptr,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(cpu_set_page), TypedLockMode::Write,),
        cpu_set_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(
                page_ptr2page_index(cpu_set_page),
            ).view().locking_thread()->Write_lock_id,
        final(krnl).cpu_set_mp.dom()
            =~= old(krnl).cpu_set_mp.dom().insert(child_cpu_set_ptr),
        final(krnl).cpu_set_mp.spec_index(child_cpu_set_ptr).view() == cpu_set_value,
        !final(krnl).cpu_set_mp.spec_index(child_cpu_set_ptr).locked(),
        forall|ptr: RwLockCpuSetPtr|
            #![trigger final(krnl).cpu_set_mp.spec_index(ptr)]
            old(krnl).cpu_set_mp.dom().contains(ptr) ==> final(krnl).cpu_set_mp.spec_index(ptr) == old(krnl).cpu_set_mp.spec_index(ptr),
        staged_4k_page_chain(final(krnl).pg_arr, funding_pages),
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, final(krnl).pg_arr, final(lctx), container_head,),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, final(krnl).pg_arr, final(lctx), pcid_allocator_head,),
{
    let cpu_set_index = page_ptr2page_index(cpu_set_page);
    let ghost pages_before_cpu_set = krnl.pg_arr;
    let ghost lctx_before_cpu_set = *lctx;
    let Tracked(cpu_set_perm) =
        retype_owned_4k_page_for_new_container(&mut krnl.pg_arr, child_container_ptr, cpu_set_page, Allocated4KPageState::AsCpuSet, Tracked(&mut *lctx), Tracked(cpu_set_page_lock_perm),);
    proof {
        assert(krnl.pg_arr.typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id(),)) by { reveal(typed_lock_maps_inserted); };
        assert(lctx.typed_lock_entry(KernelObjId::CpuSet(child_cpu_set_ptr),) is None) by { reveal(LocalContext::typed_lock_entry); reveal(typed_lock_maps_aligned); reveal(LockedMap::typed_lock_map_aligned); };
        assert(cpu_set_perm.addr() == child_cpu_set_ptr);
    }
    let Tracked(child_cpu_set_lock_perm) =
        krnl.cpu_set_mp.retype_4k_and_insert(
            child_cpu_set_ptr,
            cpu_set_value,
            (),
            Ghost(()),
            Tracked(cpu_set_perm),
            Tracked(&mut *lctx),
            Ghost(KernelObjId::CpuSet(child_cpu_set_ptr)),
        );
    proof {
        assert(krnl.cpu_set_mp.typed_lock_map_aligned(lctx.cpu_set_lock_map(), lctx.thread_id(),)) by {
            broadcast use vstd::set::lemma_set_insert_different; reveal(typed_lock_maps_inserted);
            reveal(LockedMap::typed_lock_map_aligned); broadcast use vstd::map::lemma_map_insert_domain;
            broadcast use vstd::map::lemma_map_new_index;
        };
    }
    krnl.cpu_set_mp.wunlock(
        child_cpu_set_ptr,
        Tracked(&mut *lctx),
        Tracked(child_cpu_set_lock_perm),
        Ghost(KernelObjId::CpuSet(child_cpu_set_ptr)),
    );
    proof {
        assert(krnl.cpu_set_mp.typed_lock_map_aligned(lctx.cpu_set_lock_map(), lctx.thread_id(),)) by {
            reveal(unlock_ensures); reveal(typed_lock_maps_removed); reveal(LockedMap::typed_lock_map_aligned);
            broadcast use vstd::map::lemma_map_remove_domain;
        };
        assert(staged_4k_page_chain(krnl.pg_arr, funding_pages)) by {
            staged_4k_page_chain_page_ptrs_valid(pages_before_cpu_set, funding_pages,);
            page_ptr_seq_indices_excludes_page(funding_pages, cpu_set_page,); reveal(staged_4k_page_chain);
        };
        assert(owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, krnl.pg_arr, lctx, container_head,)) by { reveal(owned_2m_tail_lock_perms_wf); reveal(page_2m_tail_indices); };
        assert(owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, krnl.pg_arr, lctx, pcid_allocator_head,)) by { reveal(owned_2m_tail_lock_perms_wf); reveal(page_2m_tail_indices); };
        assert(typed_lock_maps_aligned(krnl, lctx)) by {
            broadcast use vstd::set::lemma_set_insert_different;
            reveal(typed_lock_maps_aligned);
            reveal(LockedArray::typed_lock_map_aligned);
            reveal(LockedMap::typed_lock_map_aligned);
            reveal(UnLockedMap::typed_quota_lock_map_aligned);
            reveal(UnLockedMap::typed_cache_lock_map_aligned);
            reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
            broadcast use vstd::map::lemma_map_insert_domain;
            broadcast use vstd::map::lemma_map_remove_domain;
            broadcast use vstd::map::lemma_map_new_index;
        };
        assert({
            &&& lctx.cpu_lock_map() == lctx_before_cpu_set.cpu_lock_map()
            &&& lctx.pcid_needflush_lock_map() == lctx_before_cpu_set.pcid_needflush_lock_map()
            &&& lctx.container_lock_map() == lctx_before_cpu_set.container_lock_map()
            &&& lctx.process_lock_map() == lctx_before_cpu_set.process_lock_map()
            &&& lctx.thread_lock_map() == lctx_before_cpu_set.thread_lock_map()
            &&& lctx.endpoint_lock_map() == lctx_before_cpu_set.endpoint_lock_map()
            &&& lctx.scheduler_lock_map() == lctx_before_cpu_set.scheduler_lock_map()
            &&& lctx.pcid_allocator_lock_map() == lctx_before_cpu_set.pcid_allocator_lock_map()
            &&& lctx.cpu_set_lock_map() == lctx_before_cpu_set.cpu_set_lock_map()
            &&& lctx.pagetable_lock_map() == lctx_before_cpu_set.pagetable_lock_map()
            &&& lctx.iommu_table_lock_map() == lctx_before_cpu_set.iommu_table_lock_map()
            &&& lctx.allocator_4k_lock_maps() == lctx_before_cpu_set.allocator_4k_lock_maps()
            &&& lctx.allocator_2m_lock_maps() == lctx_before_cpu_set.allocator_2m_lock_maps()
            &&& lctx.allocator_1g_lock_maps() == lctx_before_cpu_set.allocator_1g_lock_maps()
        }) by { reveal(typed_lock_maps_inserted); reveal(typed_lock_maps_removed); };
        if cpu_set_perms_wf(old(krnl).cpu_set_mp) {
            assert(cpu_set_perms_wf(krnl.cpu_set_mp)) by { reveal(cpu_set_perms_wf); };
        }
    }
}


}
