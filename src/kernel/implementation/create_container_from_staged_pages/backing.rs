use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
pub(super) fn retype_owned_4k_page_for_new_container(
    pages: &mut PageLockedArray, child_container_ptr: RwLockContainerPtr, page_ptr: PagePtr, page_state: Allocated4KPageState,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(page_lock_perm): Tracked<&LockPerm>,
) -> (ret: Tracked<PagePerm4k>)
    requires
        old(pages).inv(),
        page_array_wf(*old(pages)),
        old(pages).typed_lock_map_aligned(old(lctx).page_lock_map(), old(lctx).thread_id(),),
        lock_id_set_aligned(old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        page_ptr_valid(page_ptr),
        old(pages).spec_index(page_ptr2page_index(page_ptr),).view().is_init(),
        old(pages).spec_index(page_ptr2page_index(page_ptr),).view().view().perm_inv(),
        old(pages).spec_index(page_ptr2page_index(page_ptr),).view().view().perm_4k.view().is_some(),
        old(pages).spec_index(page_ptr2page_index(page_ptr),).view().view().state is Owned4k,
        old(pages).spec_index(page_ptr2page_index(page_ptr),).view().view().addr == page_ptr,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write,),
        page_lock_perm.state() is WriteLock,
        page_lock_perm.thread_id() == old(lctx).thread_id(),
        page_lock_perm.lock_id() == old(pages).spec_index(
                page_ptr2page_index(page_ptr),
            ).view().locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        lock_id_set_aligned(final(lctx)),
        final(pages).inv(),
        page_array_wf(*final(pages)),
        final(pages).typed_lock_map_aligned(final(lctx).page_lock_map(), final(lctx).thread_id(),),
        typed_lock_maps_inserted(
            old(lctx),
            final(lctx),
            KernelObjId::Page(page_ptr2page_index(page_ptr)),
            TypedHeldLock {
                lock_id: final(pages).lock_id_by_index(
                    page_ptr2page_index(page_ptr),
                ),
                mode: TypedLockMode::Write,
            },
        ),
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom(),
        final(pages).entries_unchanged_except(old(pages), page_ptr2page_index(page_ptr),),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().mappings()]
            #![trigger old(pages).spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().mappings() == old(pages).spec_index(index).view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(lctx).page_lock_map().get(index)]
            #![trigger old(lctx).page_lock_map().get(index)]
            index != page_ptr2page_index(page_ptr) ==> final(lctx).page_lock_map().get(index) == old(lctx).page_lock_map().get(index),
        final(pages).spec_index(
            page_ptr2page_index(page_ptr),
        ).view().view().state == (PageState::Allocated4k {
            state: page_state,
        }),
        final(pages).spec_index(page_ptr2page_index(page_ptr),).view().view().owning_container == child_container_ptr,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write,),
        page_lock_perm.lock_id() == final(pages).spec_index(
                page_ptr2page_index(page_ptr),
            ).view().locking_thread()->Write_lock_id,
        ret.view().is_init(),
        ret.view().addr() == page_ptr,
{
    let page_index = page_ptr2page_index(page_ptr);
    let ghost old_page_lock_id = pages.lock_id_by_index(page_index);
    proof {
        page_ptr_valid_imply_page_index_valid();
        page_array_wf_at(*pages, page_index);
    }
    let Tracked(page_perm) = {
        let page = pages.borrow_mut_typed(
            page_index,
            Ghost(lctx.page_lock_map()),
            Tracked(&*lctx),
            Tracked(page_lock_perm),
        );
        proof {
            assert(page.inv());
            assert({
                &&& page.ref_count == 0
                &&& page.free_list_node_storage.is_init()
                &&& page.perm_2m.view().is_none()
                &&& page.perm_1g.view().is_none()
                &&& !page.is_io_page
            }) by { reveal(Page::mapped_state_inv); reveal(Page::node_storage_inv); reveal(Page::perm_inv); };
        }
        let Tracked(page_perm) = take_perm_4k(page);
        page.state = PageState::Allocated4k {
            state: page_state,
        };
        page.owning_container = child_container_ptr;
        proof {
            assert(page.inv()) by {
                reveal(Page::mappings_va_valid); reveal(Page::mappings_finite); reveal(Page::ref_count_inv); reveal(Page::mapped_state_inv);
                reveal(Page::node_storage_inv); reveal(Page::free_state_inv); reveal(Page::perm_inv);
            };
        }
        Tracked(page_perm)
    };
    proof {
        lctx.update_lock_id(
            KernelObjId::Page(page_index),
            old_page_lock_id,
            pages.lock_id_by_index(page_index),
        );
        assert(pages.spec_index(page_index).view().inv()) by { reveal(RwLock::inv); };
        assert(pages.spec_index(page_index).view().view().addr == page_index2page_ptr(page_index)) by { page_ptr_roundtrip(); reveal(page_array_wf); };
        assert(page_array_wf(*pages)) by { reveal(page_array_wf); };
        assert(pages.inv()) by { reveal(page_array_wf); };
        assert(lctx.page_lock_map().dom() == old(lctx).page_lock_map().dom()) by { reveal(typed_lock_maps_inserted); reveal(typed_lock_map_contains_mode); broadcast use vstd::map::lemma_map_insert_domain; };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), page_index, TypedLockMode::Write,)) by { reveal(typed_lock_maps_inserted); reveal(typed_lock_map_contains_mode); };
        assert(pages.typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id(),)) by { reveal(typed_lock_maps_inserted); reveal(LockedArray::typed_lock_map_aligned); };
    }
    Tracked(page_perm)
}

#[verifier::rlimit(15)]
pub(super) fn retype_owned_2m_page_for_new_container(
    pages: &mut PageLockedArray, child_container_ptr: RwLockContainerPtr, page_ptr: PagePtr, page_state: Allocated2MPageState,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(page_lock_perm): Tracked<&LockPerm>,
) -> (ret: Tracked<PagePerm2m>)
    requires
        old(pages).inv(),
        page_array_wf(*old(pages)),
        old(pages).typed_lock_map_aligned(old(lctx).page_lock_map(), old(lctx).thread_id(),),
        lock_id_set_aligned(old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        page_ptr_2m_valid(page_ptr),
        old(pages).spec_index(page_ptr2page_index(page_ptr),).view().is_init(),
        old(pages).spec_index(page_ptr2page_index(page_ptr),).view().view().perm_inv(),
        old(pages).spec_index(page_ptr2page_index(page_ptr),).view().view().perm_2m.view().is_some(),
        old(pages).spec_index(page_ptr2page_index(page_ptr),).view().view().state is Owned2m,
        old(pages).spec_index(page_ptr2page_index(page_ptr),).view().view().addr == page_ptr,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write,),
        page_lock_perm.state() is WriteLock,
        page_lock_perm.thread_id() == old(lctx).thread_id(),
        page_lock_perm.lock_id() == old(pages).spec_index(
                page_ptr2page_index(page_ptr),
            ).view().locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        lock_id_set_aligned(final(lctx)),
        final(pages).inv(),
        page_array_wf(*final(pages)),
        final(pages).typed_lock_map_aligned(final(lctx).page_lock_map(), final(lctx).thread_id(),),
        typed_lock_maps_inserted(
            old(lctx),
            final(lctx),
            KernelObjId::Page(page_ptr2page_index(page_ptr)),
            TypedHeldLock {
                lock_id: final(pages).lock_id_by_index(
                    page_ptr2page_index(page_ptr),
                ),
                mode: TypedLockMode::Write,
            },
        ),
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom(),
        final(pages).entries_unchanged_except(old(pages), page_ptr2page_index(page_ptr),),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().state]
            index_valid(NUM_PAGES, index) && {
                    ||| old(pages).spec_index(index).view().view().state is Allocated4k
                    ||| final(pages).spec_index(index).view().view().state is Allocated4k
                } ==> final(pages).spec_index(index).view().view().state == old(pages).spec_index(index).view().view().state,
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().mappings()]
            #![trigger old(pages).spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().mappings() == old(pages).spec_index(index).view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(lctx).page_lock_map().get(index)]
            #![trigger old(lctx).page_lock_map().get(index)]
            index != page_ptr2page_index(page_ptr) ==> final(lctx).page_lock_map().get(index) == old(lctx).page_lock_map().get(index),
        final(pages).spec_index(
            page_ptr2page_index(page_ptr),
        ).view().view().state == (PageState::Allocated2m {
            state: page_state,
        }),
        final(pages).spec_index(page_ptr2page_index(page_ptr),).view().view().owning_container == child_container_ptr,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write,),
        page_lock_perm.lock_id() == final(pages).spec_index(
                page_ptr2page_index(page_ptr),
            ).view().locking_thread()->Write_lock_id,
        ret.view().is_init(),
        ret.view().addr() == page_ptr,
{
    let page_index = page_ptr2page_index(page_ptr);
    let ghost old_page_lock_id = pages.lock_id_by_index(page_index);
    proof {
        assert(page_ptr_valid(page_ptr)) by { reveal(page_ptr_2m_valid); reveal(page_ptr_valid); };
        page_ptr_valid_imply_page_index_valid();
        page_array_wf_at(*pages, page_index);
    }
    let Tracked(page_perm) = {
        let page = pages.borrow_mut_typed(
            page_index,
            Ghost(lctx.page_lock_map()),
            Tracked(&*lctx),
            Tracked(page_lock_perm),
        );
        proof {
            assert(page.inv());
            assert({
                &&& page.ref_count == 0
                &&& page.free_list_node_storage.is_init()
                &&& page.perm_4k.view().is_none()
                &&& page.perm_1g.view().is_none()
                &&& !page.is_io_page
            }) by { reveal(Page::mapped_state_inv); reveal(Page::node_storage_inv); reveal(Page::perm_inv); };
        }
        let Tracked(page_perm) = take_perm_2m(page);
        page.state = PageState::Allocated2m {
            state: page_state,
        };
        page.owning_container = child_container_ptr;
        proof {
            assert(page.inv()) by {
                reveal(Page::mappings_va_valid); reveal(Page::mappings_finite); reveal(Page::ref_count_inv); reveal(Page::mapped_state_inv);
                reveal(Page::node_storage_inv); reveal(Page::free_state_inv); reveal(Page::perm_inv);
            };
        }
        Tracked(page_perm)
    };
    proof {
        lctx.update_lock_id(
            KernelObjId::Page(page_index),
            old_page_lock_id,
            pages.lock_id_by_index(page_index),
        );
        assert(pages.spec_index(page_index).view().inv()) by { reveal(RwLock::inv); };
        assert(pages.spec_index(page_index).view().view().addr == page_index2page_ptr(page_index)) by { page_ptr_roundtrip(); reveal(page_array_wf); };
        assert(page_array_wf(*pages)) by { reveal(page_array_wf); };
        assert(lctx.page_lock_map().dom() == old(lctx).page_lock_map().dom()) by { reveal(typed_lock_maps_inserted); reveal(typed_lock_map_contains_mode); broadcast use vstd::map::lemma_map_insert_domain; };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), page_index, TypedLockMode::Write,)) by { reveal(typed_lock_maps_inserted); reveal(typed_lock_map_contains_mode); };
        assert(pages.typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id(),)) by { reveal(typed_lock_maps_inserted); reveal(LockedArray::typed_lock_map_aligned); };
    }
    Tracked(page_perm)
}

pub(super) fn retype_new_container_owned_2m_pages(
    pages: &mut PageLockedArray, child_container_ptr: RwLockContainerPtr, container_page: PagePtr, pcid_allocator_page: PagePtr,
    Ghost(process_map): Ghost<ProcessLockedMap>, Ghost(scheduler_map): Ghost<SchedulerLockedMap>,
    Ghost(cpu_set_map): Ghost<CpuSetLockedMap>, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(container_page_lock_perm): Tracked<&LockPerm>, Tracked(pcid_allocator_page_lock_perm): Tracked<&LockPerm>,
) -> (ret: (Tracked<PagePerm2m>, Tracked<PagePerm2m>))
    requires
        old(pages).inv(),
        page_array_wf(*old(pages)),
        process_pages_wf(*old(pages), process_map),
        scheduler_pages_wf(scheduler_map, *old(pages)),
        cpu_set_pages_wf(cpu_set_map, *old(pages)),
        old(pages).typed_lock_map_aligned(old(lctx).page_lock_map(), old(lctx).thread_id()),
        lock_id_set_aligned(old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        container_page != pcid_allocator_page,
        old(pages).spec_index(page_ptr2page_index(container_page)).view().is_init(),
        old(pages).spec_index(page_ptr2page_index(container_page)).view().view().perm_inv(),
        old(pages).spec_index(page_ptr2page_index(container_page)).view().view().perm_2m.view().is_some(),
        old(pages).spec_index(page_ptr2page_index(container_page)).view().view().state is Owned2m,
        old(pages).spec_index(page_ptr2page_index(container_page)).view().view().addr == container_page,
        old(pages).spec_index(page_ptr2page_index(pcid_allocator_page)).view().is_init(),
        old(pages).spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().perm_inv(),
        old(pages).spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().perm_2m.view().is_some(),
        old(pages).spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().state is Owned2m,
        old(pages).spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().addr == pcid_allocator_page,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(container_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pcid_allocator_page), TypedLockMode::Write),
        container_page_lock_perm.state() is WriteLock,
        container_page_lock_perm.thread_id() == old(lctx).thread_id(),
        container_page_lock_perm.lock_id() == old(pages).spec_index(page_ptr2page_index(container_page)).view().locking_thread()->Write_lock_id,
        pcid_allocator_page_lock_perm.state() is WriteLock,
        pcid_allocator_page_lock_perm.thread_id() == old(lctx).thread_id(),
        pcid_allocator_page_lock_perm.lock_id() == old(pages).spec_index(page_ptr2page_index(pcid_allocator_page)).view().locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        lock_id_set_aligned(final(lctx)),
        final(pages).inv(),
        page_array_wf(*final(pages)),
        process_pages_wf(*final(pages), process_map),
        scheduler_pages_wf(scheduler_map, *final(pages)),
        cpu_set_pages_wf(cpu_set_map, *final(pages)),
        final(pages).typed_lock_map_aligned(final(lctx).page_lock_map(), final(lctx).thread_id()),
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom(),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index)]
            index_valid(NUM_PAGES, index) && index != page_ptr2page_index(container_page) && index != page_ptr2page_index(pcid_allocator_page) ==> final(pages).spec_index(index) == old(pages).spec_index(index),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().mappings()]
            #![trigger old(pages).spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().mappings() == old(pages).spec_index(index).view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(lctx).page_lock_map().get(index)]
            #![trigger old(lctx).page_lock_map().get(index)]
            index != page_ptr2page_index(container_page) && index != page_ptr2page_index(pcid_allocator_page) ==> final(lctx).page_lock_map().get(index) == old(lctx).page_lock_map().get(index),
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
        final(pages).spec_index(page_ptr2page_index(container_page)).view().view().state == (PageState::Allocated2m { state: Allocated2MPageState::AsContainer }),
        final(pages).spec_index(page_ptr2page_index(container_page)).view().view().owning_container == child_container_ptr,
        final(pages).spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().state == (PageState::Allocated2m { state: Allocated2MPageState::AsPcidAllocator }),
        final(pages).spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().owning_container == child_container_ptr,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(container_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pcid_allocator_page), TypedLockMode::Write),
        container_page_lock_perm.lock_id() == final(pages).spec_index(page_ptr2page_index(container_page)).view().locking_thread()->Write_lock_id,
        pcid_allocator_page_lock_perm.lock_id() == final(pages).spec_index(page_ptr2page_index(pcid_allocator_page)).view().locking_thread()->Write_lock_id,
        ret.0.view().is_init(),
        ret.0.view().addr() == container_page,
        ret.1.view().is_init(),
        ret.1.view().addr() == pcid_allocator_page,
{
    let container_head = page_ptr2page_index(container_page);
    let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
    proof {
        assert(page_ptr_valid(container_page) && page_ptr_valid(pcid_allocator_page)) by { reveal(page_ptr_2m_valid); reveal(page_ptr_valid); };
        assert(container_head != pcid_allocator_head) by { page_ptr2page_index_injective(); };
    }
    let ghost pages_before = *pages;
    let ghost lctx_before = *lctx;
    let Tracked(container_perm) = retype_owned_2m_page_for_new_container(
        pages,
        child_container_ptr,
        container_page,
        Allocated2MPageState::AsContainer,
        Tracked(&mut *lctx),
        Tracked(container_page_lock_perm),
    );
    proof {
        assert(pages.spec_index(pcid_allocator_head) == pages_before.spec_index(pcid_allocator_head));
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), pcid_allocator_head, TypedLockMode::Write)) by {
            assert(lctx.page_lock_map().get(pcid_allocator_head) == lctx_before.page_lock_map().get(pcid_allocator_head));
            reveal(typed_lock_map_contains_mode);
        };
        assert(pcid_allocator_page_lock_perm.lock_id() == pages.spec_index(pcid_allocator_head).view().locking_thread()->Write_lock_id);
        process_pages_wf_preserved_for_page_state_eq(pages_before, *pages, process_map, process_map,);
        scheduler_pages_wf_preserved_for_page_state_eq(scheduler_map, scheduler_map, pages_before, *pages,);
        assert(cpu_set_pages_wf(cpu_set_map, *pages)) by { reveal(cpu_set_pages_wf); };
    }
    let ghost pages_after_container = *pages;
    let ghost lctx_after_container = *lctx;
    let Tracked(pcid_allocator_perm) = retype_owned_2m_page_for_new_container(
        pages,
        child_container_ptr,
        pcid_allocator_page,
        Allocated2MPageState::AsPcidAllocator,
        Tracked(&mut *lctx),
        Tracked(pcid_allocator_page_lock_perm),
    );
    proof {
        assert(pages.spec_index(container_head) == pages_after_container.spec_index(container_head));
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), container_head, TypedLockMode::Write)) by {
            assert(lctx.page_lock_map().get(container_head) == lctx_after_container.page_lock_map().get(container_head));
            reveal(typed_lock_map_contains_mode);
        };
        assert(container_page_lock_perm.lock_id() == pages.spec_index(container_head).view().locking_thread()->Write_lock_id);
        process_pages_wf_preserved_for_page_state_eq(pages_after_container, *pages, process_map, process_map,);
        scheduler_pages_wf_preserved_for_page_state_eq(scheduler_map, scheduler_map, pages_after_container, *pages,);
        assert(cpu_set_pages_wf(cpu_set_map, *pages)) by { reveal(cpu_set_pages_wf); };
    }
    (Tracked(container_perm), Tracked(pcid_allocator_perm))
}

#[verifier::spinoff_prover]
pub(super) fn prepare_new_container_backing_pages(
    pages: &mut PageLockedArray, container_page: PagePtr, pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr,
    allocator_2m_page: PagePtr, allocator_1g_page: PagePtr, scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr,
    pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr, funding_page_count: usize, funding_page_head: PagePtr,
    Ghost(funding_pages): Ghost<Seq<PagePtr>>, Ghost(funding_indices): Ghost<Set<PageIndex>>,
    child_allocator_4k_ptr: RwLockPageAllocatorPtr, child_container_ptr: RwLockContainerPtr, child_depth: usize,
    Ghost(reference_krnl): Ghost<KernelK>, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(funding_page_lock_perms): Tracked<&Map<PagePtr, LockPerm>>, Tracked(container_page_lock_perm): Tracked<&LockPerm>,
    Tracked(pcid_allocator_page_lock_perm): Tracked<&LockPerm>, Tracked(container_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
    Tracked(pcid_allocator_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
) -> (ret: (LinkedList<PagePtr, ALLOCATOR_GLOBAL_POLL_MAJOR>, Tracked<PagePerm2m>, Tracked<PagePerm2m>,))
    requires
        reference_krnl.inv(),
        reference_krnl.pg_arr == *old(pages),
        old(pages).inv(),
        page_array_wf(*old(pages)),
        old(pages).typed_lock_map_aligned(old(lctx).page_lock_map(), old(lctx).thread_id()),
        lock_id_set_aligned(old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
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
        reference_krnl.pg_arr.spec_index(page_ptr2page_index(container_page)).view().view().state is Owned2m,
        reference_krnl.pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().state is Owned2m,
        reference_krnl.pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)).view().view().state is Owned4k,
        reference_krnl.pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)).view().view().state is Owned4k,
        reference_krnl.pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)).view().view().state is Owned4k,
        reference_krnl.pg_arr.spec_index(page_ptr2page_index(scheduler_page)).view().view().state is Owned4k,
        reference_krnl.pg_arr.spec_index(page_ptr2page_index(cpu_set_page)).view().view().state is Owned4k,
        reference_krnl.pg_arr.spec_index(page_ptr2page_index(process_page)).view().view().state is Owned4k,
        reference_krnl.pg_arr.spec_index(page_ptr2page_index(pagetable_page)).view().view().state is Owned4k,
        reference_krnl.pg_arr.spec_index(page_ptr2page_index(l4_page)).view().view().state is Owned4k,
        reference_krnl.pg_arr.spec_index(page_ptr2page_index(thread_page)).view().view().state is Owned4k,
        funding_pages.len() == funding_page_count,
        funding_pages.no_duplicates(),
        funding_indices == funding_pages.map_values(|page_ptr: PagePtr| page_ptr2page_index(page_ptr)).to_set(),
        funding_page_head == staged_4k_page_chain_head(funding_pages),
        staged_4k_page_chain(reference_krnl.pg_arr, funding_pages),
        funding_page_lock_perms.dom() == funding_pages.to_set(),
        forall|page_ptr: PagePtr|
            #![trigger funding_page_lock_perms.dom().contains(page_ptr)]
            funding_page_lock_perms.dom().contains(page_ptr) ==> {
                &&& page_ptr_valid(page_ptr)
                &&& reference_krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state is Owned4k
                &&& typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write)
                &&& funding_page_lock_perms.spec_index(page_ptr).state() is WriteLock
                &&& funding_page_lock_perms.spec_index(page_ptr).thread_id() == old(lctx).thread_id()
                &&& funding_page_lock_perms.spec_index(page_ptr).lock_id() == reference_krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id
            },
        funding_pages.to_set().disjoint(new_container_moved_pages(
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
        )),
        !funding_pages.to_set().contains(thread_page),
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, *old(pages), old(lctx), page_ptr2page_index(container_page),),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, *old(pages), old(lctx), page_ptr2page_index(pcid_allocator_page),),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(container_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pcid_allocator_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(allocator_4k_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(allocator_2m_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(allocator_1g_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(scheduler_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(cpu_set_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(process_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pagetable_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(l4_page), TypedLockMode::Write),
        container_page_lock_perm.state() is WriteLock,
        container_page_lock_perm.thread_id() == old(lctx).thread_id(),
        container_page_lock_perm.lock_id() == old(pages).spec_index(page_ptr2page_index(container_page)).view().locking_thread()->Write_lock_id,
        pcid_allocator_page_lock_perm.state() is WriteLock,
        pcid_allocator_page_lock_perm.thread_id() == old(lctx).thread_id(),
        pcid_allocator_page_lock_perm.lock_id() == old(pages).spec_index(page_ptr2page_index(pcid_allocator_page)).view().locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        lock_id_set_aligned(final(lctx)),
        final(pages).inv(),
        page_array_wf(*final(pages)),
        process_pages_wf(*final(pages), reference_krnl.prc_mp),
        scheduler_pages_wf(reference_krnl.sched_mp, *final(pages)),
        cpu_set_pages_wf(reference_krnl.cpu_set_mp, *final(pages)),
        final(pages).typed_lock_map_aligned(final(lctx).page_lock_map(), final(lctx).thread_id()),
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom(),
        forall|index: PageIndex|
            #![trigger final(lctx).page_lock_map().get(index)]
            #![trigger old(lctx).page_lock_map().get(index)]
            !funding_indices.contains(index) && index != page_ptr2page_index(container_page) && index != page_ptr2page_index(pcid_allocator_page) ==> final(lctx).page_lock_map().get(index) == old(lctx).page_lock_map().get(index),
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
        ret.0.wf(),
        ret.0.view() == funding_pages,
        forall|page_ptr: PagePtr|
            #![trigger ret.0.view().contains(page_ptr)]
            ret.0.view().contains(page_ptr) ==> {
                &&& page_ptr_valid(page_ptr)
                &&& page_ptr_valid(page_ptr) ==> {
                    let node_addr = final(pages).spec_index(
                        page_ptr2page_index(page_ptr),
                    ).view().view().free_list_node_storage.addr();
                    &&& ret.0.map().dom().contains(node_addr)
                    &&& ret.0.map().spec_index(node_addr) == page_ptr
                }
            },
        ret.0.container_depth == Some(child_depth),
        ret.0.minor == Some(child_container_ptr),
        ret.1.view().is_init(),
        ret.1.view().addr() == container_page,
        ret.2.view().is_init(),
        ret.2.view().addr() == pcid_allocator_page,
        staged_4k_page_chain(*final(pages), funding_pages),
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, *final(pages), final(lctx), page_ptr2page_index(container_page),),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, *final(pages), final(lctx), page_ptr2page_index(pcid_allocator_page),),
        funding_indices.disjoint(page_2m_tail_indices(page_ptr2page_index(container_page))),
        funding_indices.disjoint(page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page))),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().mappings()]
            #![trigger reference_krnl.pg_arr.spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().mappings() == reference_krnl.pg_arr.spec_index(index).view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index)]
            #![trigger reference_krnl.pg_arr.spec_index(index)]
            index_valid(NUM_PAGES, index) && !funding_indices.contains(index) && !page_2m_tail_indices(page_ptr2page_index(container_page)).contains(index) && !page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)).contains(index) && index != page_ptr2page_index(container_page) && index != page_ptr2page_index(pcid_allocator_page) ==> final(pages).spec_index(index) == reference_krnl.pg_arr.spec_index(index),
        forall|index: PageIndex|
            #![trigger container_tail_lock_perms.dom().contains(index)]
            container_tail_lock_perms.dom().contains(index) ==> final(pages).spec_index(index).view().view().owning_container == child_container_ptr,
        forall|index: PageIndex|
            #![trigger pcid_allocator_tail_lock_perms.dom().contains(index)]
            pcid_allocator_tail_lock_perms.dom().contains(index) ==> final(pages).spec_index(index).view().view().owning_container == child_container_ptr,
        forall|page_ptr: PagePtr|
            #![trigger funding_page_lock_perms.dom().contains(page_ptr)]
            funding_page_lock_perms.dom().contains(page_ptr) ==> {
                &&& final(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Free4k {
                    allocator_ptr: Ghost(child_allocator_4k_ptr),
                    state: FreePageAllocatorState::GlobalList,
                })
                &&& final(pages).spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == child_container_ptr
                &&& typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write)
                &&& funding_page_lock_perms.spec_index(page_ptr).lock_id() == final(pages).spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id
            },
        final(pages).spec_index(page_ptr2page_index(container_page)).view().view().state == (PageState::Allocated2m { state: Allocated2MPageState::AsContainer }),
        final(pages).spec_index(page_ptr2page_index(container_page)).view().view().owning_container == child_container_ptr,
        final(pages).spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().state == (PageState::Allocated2m { state: Allocated2MPageState::AsPcidAllocator }),
        final(pages).spec_index(page_ptr2page_index(pcid_allocator_page)).view().view().owning_container == child_container_ptr,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(container_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pcid_allocator_page), TypedLockMode::Write),
        container_page_lock_perm.lock_id() == final(pages).spec_index(page_ptr2page_index(container_page)).view().locking_thread()->Write_lock_id,
        pcid_allocator_page_lock_perm.lock_id() == final(pages).spec_index(page_ptr2page_index(pcid_allocator_page)).view().locking_thread()->Write_lock_id,
        final(pages).spec_index(page_ptr2page_index(allocator_4k_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(allocator_4k_page)),
        final(pages).spec_index(page_ptr2page_index(allocator_2m_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(allocator_2m_page)),
        final(pages).spec_index(page_ptr2page_index(allocator_1g_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(allocator_1g_page)),
        final(pages).spec_index(page_ptr2page_index(scheduler_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(scheduler_page)),
        final(pages).spec_index(page_ptr2page_index(cpu_set_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(cpu_set_page)),
        final(pages).spec_index(page_ptr2page_index(process_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(process_page)),
        final(pages).spec_index(page_ptr2page_index(pagetable_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(pagetable_page)),
        final(pages).spec_index(page_ptr2page_index(l4_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(l4_page)),
        final(pages).spec_index(page_ptr2page_index(thread_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(thread_page)),
        final(lctx).page_lock_map().get(page_ptr2page_index(allocator_4k_page)) == old(lctx).page_lock_map().get(page_ptr2page_index(allocator_4k_page)),
        final(lctx).page_lock_map().get(page_ptr2page_index(allocator_2m_page)) == old(lctx).page_lock_map().get(page_ptr2page_index(allocator_2m_page)),
        final(lctx).page_lock_map().get(page_ptr2page_index(allocator_1g_page)) == old(lctx).page_lock_map().get(page_ptr2page_index(allocator_1g_page)),
        final(lctx).page_lock_map().get(page_ptr2page_index(scheduler_page)) == old(lctx).page_lock_map().get(page_ptr2page_index(scheduler_page)),
        final(lctx).page_lock_map().get(page_ptr2page_index(cpu_set_page)) == old(lctx).page_lock_map().get(page_ptr2page_index(cpu_set_page)),
        final(lctx).page_lock_map().get(page_ptr2page_index(process_page)) == old(lctx).page_lock_map().get(page_ptr2page_index(process_page)),
        final(lctx).page_lock_map().get(page_ptr2page_index(pagetable_page)) == old(lctx).page_lock_map().get(page_ptr2page_index(pagetable_page)),
        final(lctx).page_lock_map().get(page_ptr2page_index(l4_page)) == old(lctx).page_lock_map().get(page_ptr2page_index(l4_page)),
        final(lctx).page_lock_map().get(page_ptr2page_index(thread_page)) == old(lctx).page_lock_map().get(page_ptr2page_index(thread_page)),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(allocator_4k_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(allocator_2m_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(allocator_1g_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(scheduler_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(cpu_set_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(process_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pagetable_page), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(l4_page), TypedLockMode::Write),
{
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
    let thread_page_index = page_ptr2page_index(thread_page);
    set_new_container_owned_2m_page_tail_pair(
        pages, container_page, pcid_allocator_page, allocator_4k_page, allocator_2m_page, allocator_1g_page, scheduler_page, cpu_set_page,
        process_page, pagetable_page, l4_page, thread_page, child_container_ptr, Ghost(reference_krnl), Ghost(funding_pages),
        Ghost(funding_indices), Tracked(&*lctx), Tracked(funding_page_lock_perms), Tracked(container_tail_lock_perms),
        Tracked(pcid_allocator_tail_lock_perms),
    );
    proof {
        assert forall|page_ptr: PagePtr|
            #![trigger funding_page_lock_perms.dom().contains(page_ptr)]
            funding_page_lock_perms.dom().contains(page_ptr) implies {
                &&& page_ptr_valid(page_ptr)
                &&& pages.spec_index(page_ptr2page_index(page_ptr)).view().view().state is Owned4k
                &&& typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write)
                &&& funding_page_lock_perms.spec_index(page_ptr).state() is WriteLock
                &&& funding_page_lock_perms.spec_index(page_ptr).thread_id() == lctx.thread_id()
                &&& funding_page_lock_perms.spec_index(page_ptr).lock_id() == pages.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id
            } by { assert(pages.spec_index(page_ptr2page_index(page_ptr)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr))); };
    }
    let ghost pages_after_tail_setup = *pages;
    let global_pool = build_staged_4k_global_pool(
        pages,
        funding_page_count,
        funding_page_head,
        Ghost(funding_pages),
        Ghost(funding_indices),
        Ghost(reference_krnl.prc_mp),
        Ghost(reference_krnl.sched_mp),
        Ghost(reference_krnl.cpu_set_mp),
        child_allocator_4k_ptr,
        child_container_ptr,
        child_depth,
        Tracked(&mut *lctx),
        Tracked(funding_page_lock_perms),
    );
    proof {
        assert(owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, *pages, lctx, page_ptr2page_index(container_page),)) by {
            reveal(owned_2m_tail_lock_perms_wf); reveal(page_2m_tail_indices); reveal(Set::disjoint); reveal(typed_lock_map_contains_mode);
        };
        assert(owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, *pages, lctx, page_ptr2page_index(pcid_allocator_page),)) by {
            reveal(owned_2m_tail_lock_perms_wf); reveal(page_2m_tail_indices); reveal(Set::disjoint); reveal(typed_lock_map_contains_mode);
        };
        assert(!funding_pages.to_set().contains(container_page) && !funding_pages.to_set().contains(pcid_allocator_page)) by { reveal(new_container_moved_pages); reveal(Set::disjoint); };
        staged_4k_page_chain_page_ptrs_valid(*pages, funding_pages);
        page_ptr_seq_indices_excludes_page(funding_pages, container_page);
        page_ptr_seq_indices_excludes_page(funding_pages, pcid_allocator_page);
        assert(pages.spec_index(page_ptr2page_index(container_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(container_page)));
        assert(pages.spec_index(page_ptr2page_index(pcid_allocator_page)) == reference_krnl.pg_arr.spec_index(page_ptr2page_index(pcid_allocator_page)));
        page_array_wf_at(*pages, page_ptr2page_index(container_page));
        page_array_wf_at(*pages, page_ptr2page_index(pcid_allocator_page));
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(container_page), TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(page_ptr2page_index(container_page)) == old(lctx).page_lock_map().get(page_ptr2page_index(container_page)));
            reveal(typed_lock_map_contains_mode);
        };
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(pcid_allocator_page), TypedLockMode::Write,)) by {
            assert(lctx.page_lock_map().get(page_ptr2page_index(pcid_allocator_page)) == old(lctx).page_lock_map().get(page_ptr2page_index(pcid_allocator_page)));
            reveal(typed_lock_map_contains_mode);
        };
    }
    let ghost pages_before_2m_retype = *pages;
    let ghost lctx_before_2m_retype = *lctx;
    let (Tracked(container_perm), Tracked(pcid_allocator_perm)) =
        retype_new_container_owned_2m_pages(
            pages, child_container_ptr, container_page, pcid_allocator_page, Ghost(reference_krnl.prc_mp), Ghost(reference_krnl.sched_mp),
            Ghost(reference_krnl.cpu_set_mp), Tracked(&mut *lctx), Tracked(container_page_lock_perm),
            Tracked(pcid_allocator_page_lock_perm),
        );
    proof {
        assert(staged_4k_page_chain(*pages, funding_pages)) by {
            staged_4k_page_chain_page_ptrs_valid(pages_before_2m_retype, funding_pages,);
            broadcast use page_ptr_sequence_index_in_equal_set; broadcast use page_ptr_sequence_index_in_mapped_set;
            reveal(staged_4k_page_chain);
        };
        assert forall|page_ptr: PagePtr|
            #![trigger funding_page_lock_perms.dom().contains(page_ptr)]
            funding_page_lock_perms.dom().contains(page_ptr) implies {
                &&& pages.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Free4k {
                    allocator_ptr: Ghost(child_allocator_4k_ptr),
                    state: FreePageAllocatorState::GlobalList,
                })
                &&& pages.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == child_container_ptr
                &&& typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write)
                &&& funding_page_lock_perms.spec_index(page_ptr).lock_id() == pages.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id
            } by {
            assert(page_ptr != container_page && page_ptr != pcid_allocator_page) by { reveal(new_container_moved_pages); reveal(Set::disjoint); };
            page_ptr2page_index_neq(page_ptr, container_page);
            page_ptr2page_index_neq(page_ptr, pcid_allocator_page);
            assert(pages.spec_index(page_ptr2page_index(page_ptr)) == pages_before_2m_retype.spec_index(page_ptr2page_index(page_ptr)));
            assert(lctx.page_lock_map().get(page_ptr2page_index(page_ptr)) == lctx_before_2m_retype.page_lock_map().get(page_ptr2page_index(page_ptr)));
            reveal(typed_lock_map_contains_mode);
        };
        assert({
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
            &&& process_index != container_head
            &&& process_index != pcid_allocator_head
            &&& pagetable_index != container_head
            &&& pagetable_index != pcid_allocator_head
            &&& l4_index != container_head
            &&& l4_index != pcid_allocator_head
            &&& thread_page_index != container_head
            &&& thread_page_index != pcid_allocator_head
        }) by {
            assert(reference_krnl.pg_arr.spec_index(container_head).view().view().state is Owned2m);
            assert(reference_krnl.pg_arr.spec_index(pcid_allocator_head).view().view().state is Owned2m);
            assert(reference_krnl.pg_arr.spec_index(allocator_4k_index).view().view().state is Owned4k);
            assert(reference_krnl.pg_arr.spec_index(allocator_2m_index).view().view().state is Owned4k);
            assert(reference_krnl.pg_arr.spec_index(allocator_1g_index).view().view().state is Owned4k);
            assert(reference_krnl.pg_arr.spec_index(scheduler_index).view().view().state is Owned4k);
            assert(reference_krnl.pg_arr.spec_index(cpu_set_index).view().view().state is Owned4k);
            assert(reference_krnl.pg_arr.spec_index(process_index).view().view().state is Owned4k);
            assert(reference_krnl.pg_arr.spec_index(pagetable_index).view().view().state is Owned4k);
            assert(reference_krnl.pg_arr.spec_index(l4_index).view().view().state is Owned4k);
            assert(reference_krnl.pg_arr.spec_index(thread_page_index).view().view().state is Owned4k);
        };
        assert({
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
        staged_4k_page_chain_page_ptrs_valid(reference_krnl.pg_arr, funding_pages);
        page_ptr_seq_indices_excludes_page(funding_pages, allocator_4k_page);
        page_ptr_seq_indices_excludes_page(funding_pages, allocator_2m_page);
        page_ptr_seq_indices_excludes_page(funding_pages, allocator_1g_page);
        page_ptr_seq_indices_excludes_page(funding_pages, scheduler_page);
        page_ptr_seq_indices_excludes_page(funding_pages, cpu_set_page);
        page_ptr_seq_indices_excludes_page(funding_pages, process_page);
        page_ptr_seq_indices_excludes_page(funding_pages, pagetable_page);
        page_ptr_seq_indices_excludes_page(funding_pages, l4_page);
        page_ptr_seq_indices_excludes_page(funding_pages, thread_page);
        assert({
            &&& pages.spec_index(allocator_4k_index) == reference_krnl.pg_arr.spec_index(allocator_4k_index)
            &&& pages.spec_index(allocator_2m_index) == reference_krnl.pg_arr.spec_index(allocator_2m_index)
            &&& pages.spec_index(allocator_1g_index) == reference_krnl.pg_arr.spec_index(allocator_1g_index)
            &&& pages.spec_index(scheduler_index) == reference_krnl.pg_arr.spec_index(scheduler_index)
            &&& pages.spec_index(cpu_set_index) == reference_krnl.pg_arr.spec_index(cpu_set_index)
            &&& pages.spec_index(process_index) == reference_krnl.pg_arr.spec_index(process_index)
            &&& pages.spec_index(pagetable_index) == reference_krnl.pg_arr.spec_index(pagetable_index)
            &&& pages.spec_index(l4_index) == reference_krnl.pg_arr.spec_index(l4_index)
            &&& pages.spec_index(thread_page_index) == reference_krnl.pg_arr.spec_index(thread_page_index)
        }) by {
            assert(pages_before_2m_retype.spec_index(allocator_4k_index) == pages_after_tail_setup.spec_index(allocator_4k_index));
            assert(pages_before_2m_retype.spec_index(allocator_2m_index) == pages_after_tail_setup.spec_index(allocator_2m_index));
            assert(pages_before_2m_retype.spec_index(allocator_1g_index) == pages_after_tail_setup.spec_index(allocator_1g_index));
            assert(pages_before_2m_retype.spec_index(scheduler_index) == pages_after_tail_setup.spec_index(scheduler_index));
            assert(pages_before_2m_retype.spec_index(cpu_set_index) == pages_after_tail_setup.spec_index(cpu_set_index));
            assert(pages_before_2m_retype.spec_index(process_index) == pages_after_tail_setup.spec_index(process_index));
            assert(pages_before_2m_retype.spec_index(pagetable_index) == pages_after_tail_setup.spec_index(pagetable_index));
            assert(pages_before_2m_retype.spec_index(l4_index) == pages_after_tail_setup.spec_index(l4_index));
            assert(pages_before_2m_retype.spec_index(thread_page_index) == pages_after_tail_setup.spec_index(thread_page_index));
        };
        assert({
            &&& lctx.page_lock_map().get(allocator_4k_index) == old(lctx).page_lock_map().get(allocator_4k_index)
            &&& lctx.page_lock_map().get(allocator_2m_index) == old(lctx).page_lock_map().get(allocator_2m_index)
            &&& lctx.page_lock_map().get(allocator_1g_index) == old(lctx).page_lock_map().get(allocator_1g_index)
            &&& lctx.page_lock_map().get(scheduler_index) == old(lctx).page_lock_map().get(scheduler_index)
            &&& lctx.page_lock_map().get(cpu_set_index) == old(lctx).page_lock_map().get(cpu_set_index)
            &&& lctx.page_lock_map().get(process_index) == old(lctx).page_lock_map().get(process_index)
            &&& lctx.page_lock_map().get(pagetable_index) == old(lctx).page_lock_map().get(pagetable_index)
            &&& lctx.page_lock_map().get(l4_index) == old(lctx).page_lock_map().get(l4_index)
            &&& lctx.page_lock_map().get(thread_page_index) == old(lctx).page_lock_map().get(thread_page_index)
        });
        assert({
            &&& typed_lock_map_contains_mode(lctx.page_lock_map(), allocator_4k_index, TypedLockMode::Write)
            &&& typed_lock_map_contains_mode(lctx.page_lock_map(), allocator_2m_index, TypedLockMode::Write)
            &&& typed_lock_map_contains_mode(lctx.page_lock_map(), allocator_1g_index, TypedLockMode::Write)
            &&& typed_lock_map_contains_mode(lctx.page_lock_map(), scheduler_index, TypedLockMode::Write)
            &&& typed_lock_map_contains_mode(lctx.page_lock_map(), cpu_set_index, TypedLockMode::Write)
            &&& typed_lock_map_contains_mode(lctx.page_lock_map(), process_index, TypedLockMode::Write)
            &&& typed_lock_map_contains_mode(lctx.page_lock_map(), pagetable_index, TypedLockMode::Write)
            &&& typed_lock_map_contains_mode(lctx.page_lock_map(), l4_index, TypedLockMode::Write)
        }) by { reveal(typed_lock_map_contains_mode); };
    }
    (global_pool, Tracked(container_perm), Tracked(pcid_allocator_perm))
}
}
