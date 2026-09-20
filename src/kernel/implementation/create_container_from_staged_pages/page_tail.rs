use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
pub(super) fn set_new_container_owned_2m_page_tail_pair(
    pages: &mut PageLockedArray, container_page: PagePtr, pcid_allocator_page: PagePtr, allocator_4k_page: PagePtr,
    allocator_2m_page: PagePtr, allocator_1g_page: PagePtr, scheduler_page: PagePtr, cpu_set_page: PagePtr, process_page: PagePtr,
    pagetable_page: PagePtr, l4_page: PagePtr, thread_page: PagePtr, owning_container: RwLockContainerPtr,
    Ghost(reference_krnl): Ghost<KernelK>, Ghost(funding_pages): Ghost<Seq<PagePtr>>, Ghost(funding_indices): Ghost<Set<PageIndex>>,
    Tracked(lctx): Tracked<&LocalContext>, Tracked(funding_page_lock_perms): Tracked<&Map<PagePtr, LockPerm>>,
    Tracked(container_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
    Tracked(pcid_allocator_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
)
    requires
        reference_krnl.inv(),
        reference_krnl.pg_arr == *old(pages),
        old(pages).inv(),
        page_array_wf(*old(pages)),
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
        reference_krnl.pg_arr.spec_index(
            page_ptr2page_index(container_page),
        ).view().view().state is Owned2m,
        reference_krnl.pg_arr.spec_index(
            page_ptr2page_index(pcid_allocator_page),
        ).view().view().state is Owned2m,
        reference_krnl.pg_arr.spec_index(
            page_ptr2page_index(allocator_4k_page),
        ).view().view().state is Owned4k,
        reference_krnl.pg_arr.spec_index(
            page_ptr2page_index(allocator_2m_page),
        ).view().view().state is Owned4k,
        reference_krnl.pg_arr.spec_index(
            page_ptr2page_index(allocator_1g_page),
        ).view().view().state is Owned4k,
        reference_krnl.pg_arr.spec_index(
            page_ptr2page_index(scheduler_page),
        ).view().view().state is Owned4k,
        reference_krnl.pg_arr.spec_index(
            page_ptr2page_index(cpu_set_page),
        ).view().view().state is Owned4k,
        reference_krnl.pg_arr.spec_index(
            page_ptr2page_index(process_page),
        ).view().view().state is Owned4k,
        reference_krnl.pg_arr.spec_index(
            page_ptr2page_index(pagetable_page),
        ).view().view().state is Owned4k,
        reference_krnl.pg_arr.spec_index(
            page_ptr2page_index(l4_page),
        ).view().view().state is Owned4k,
        reference_krnl.pg_arr.spec_index(
            page_ptr2page_index(thread_page),
        ).view().view().state is Owned4k,
        funding_indices == funding_pages.map_values(
            |page_ptr: PagePtr| page_ptr2page_index(page_ptr),
        ).to_set(),
        staged_4k_page_chain(reference_krnl.pg_arr, funding_pages),
        funding_page_lock_perms.dom() == funding_pages.to_set(),
        forall|page_ptr: PagePtr|
            #![trigger funding_page_lock_perms.dom().contains(page_ptr)]
            funding_page_lock_perms.dom().contains(page_ptr) ==> page_ptr_valid(page_ptr),
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
        old(pages).typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id(),),
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, *old(pages), lctx, page_ptr2page_index(container_page),),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, *old(pages), lctx, page_ptr2page_index(pcid_allocator_page),),
    ensures
        final(pages).inv(),
        page_array_wf(*final(pages)),
        process_pages_wf(*final(pages), reference_krnl.prc_mp),
        scheduler_pages_wf(reference_krnl.sched_mp, *final(pages)),
        cpu_set_pages_wf(reference_krnl.cpu_set_mp, *final(pages)),
        final(pages).typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id(),),
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, *final(pages), lctx, page_ptr2page_index(container_page),),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, *final(pages), lctx, page_ptr2page_index(pcid_allocator_page),),
        funding_indices.disjoint(page_2m_tail_indices(
            page_ptr2page_index(container_page),
        )),
        funding_indices.disjoint(page_2m_tail_indices(
            page_ptr2page_index(pcid_allocator_page),
        )),
        page_2m_tail_indices(page_ptr2page_index(container_page),).disjoint(set![
            page_ptr2page_index(container_page), page_ptr2page_index(pcid_allocator_page), page_ptr2page_index(allocator_4k_page),
            page_ptr2page_index(allocator_2m_page), page_ptr2page_index(allocator_1g_page), page_ptr2page_index(scheduler_page),
            page_ptr2page_index(cpu_set_page), page_ptr2page_index(process_page), page_ptr2page_index(pagetable_page),
            page_ptr2page_index(l4_page), page_ptr2page_index(thread_page),
        ]),
        page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page),).disjoint(set![
            page_ptr2page_index(container_page), page_ptr2page_index(pcid_allocator_page), page_ptr2page_index(allocator_4k_page),
            page_ptr2page_index(allocator_2m_page), page_ptr2page_index(allocator_1g_page), page_ptr2page_index(scheduler_page),
            page_ptr2page_index(cpu_set_page), page_ptr2page_index(process_page), page_ptr2page_index(pagetable_page),
            page_ptr2page_index(l4_page), page_ptr2page_index(thread_page),
        ]),
        staged_4k_page_chain(*final(pages), funding_pages),
        forall|index: PageIndex|
            #![trigger container_tail_lock_perms.dom().contains(index)]
            container_tail_lock_perms.dom().contains(index) ==> final(pages).spec_index(index).view().view().owning_container == owning_container,
        forall|index: PageIndex|
            #![trigger pcid_allocator_tail_lock_perms.dom().contains(index)]
            pcid_allocator_tail_lock_perms.dom().contains(index) ==> final(pages).spec_index(index).view().view().owning_container == owning_container,
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().mappings()]
            #![trigger reference_krnl.pg_arr.spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().mappings() == reference_krnl.pg_arr.spec_index(index).view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().state]
            #![trigger reference_krnl.pg_arr.spec_index(index).view().view().state]
            index_valid(NUM_PAGES, index) ==> final(pages).spec_index(index).view().view().state == reference_krnl.pg_arr.spec_index(index).view().view().state,
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().owning_container]
            #![trigger reference_krnl.pg_arr.spec_index(index).view().view().owning_container]
            index_valid(NUM_PAGES, index) && !page_2m_tail_indices(
                    page_ptr2page_index(container_page),
                ).contains(index) && !page_2m_tail_indices(
                    page_ptr2page_index(pcid_allocator_page),
                ).contains(index) ==> final(pages).spec_index(index).view().view().owning_container == reference_krnl.pg_arr.spec_index(index).view().view().owning_container,
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index)]
            #![trigger reference_krnl.pg_arr.spec_index(index)]
            index_valid(NUM_PAGES, index) && !page_2m_tail_indices(
                    page_ptr2page_index(container_page),
                ).contains(index) && !page_2m_tail_indices(
                    page_ptr2page_index(pcid_allocator_page),
                ).contains(index) ==> final(pages).spec_index(index) == reference_krnl.pg_arr.spec_index(index),
        forall|page_ptr: PagePtr|
            #![trigger funding_page_lock_perms.dom().contains(page_ptr)]
            funding_page_lock_perms.dom().contains(page_ptr) ==> final(pages).spec_index(page_ptr2page_index(page_ptr)) == reference_krnl.pg_arr.spec_index(
                    page_ptr2page_index(page_ptr),
                ),
        final(pages).spec_index(page_ptr2page_index(container_page)) == reference_krnl.pg_arr.spec_index(
                page_ptr2page_index(container_page),
            ),
        final(pages).spec_index(page_ptr2page_index(pcid_allocator_page)) == reference_krnl.pg_arr.spec_index(
                page_ptr2page_index(pcid_allocator_page),
            ),
        final(pages).spec_index(page_ptr2page_index(allocator_4k_page)) == reference_krnl.pg_arr.spec_index(
                page_ptr2page_index(allocator_4k_page),
            ),
        final(pages).spec_index(page_ptr2page_index(allocator_2m_page)) == reference_krnl.pg_arr.spec_index(
                page_ptr2page_index(allocator_2m_page),
            ),
        final(pages).spec_index(page_ptr2page_index(allocator_1g_page)) == reference_krnl.pg_arr.spec_index(
                page_ptr2page_index(allocator_1g_page),
            ),
        final(pages).spec_index(page_ptr2page_index(scheduler_page)) == reference_krnl.pg_arr.spec_index(
                page_ptr2page_index(scheduler_page),
            ),
        final(pages).spec_index(page_ptr2page_index(cpu_set_page)) == reference_krnl.pg_arr.spec_index(
                page_ptr2page_index(cpu_set_page),
            ),
        final(pages).spec_index(page_ptr2page_index(process_page)) == reference_krnl.pg_arr.spec_index(
                page_ptr2page_index(process_page),
            ),
        final(pages).spec_index(page_ptr2page_index(pagetable_page)) == reference_krnl.pg_arr.spec_index(
                page_ptr2page_index(pagetable_page),
            ),
        final(pages).spec_index(page_ptr2page_index(l4_page)) == reference_krnl.pg_arr.spec_index(
                page_ptr2page_index(l4_page),
            ),
        final(pages).spec_index(page_ptr2page_index(thread_page)) == reference_krnl.pg_arr.spec_index(
                page_ptr2page_index(thread_page),
            ),
{
    let container_head = page_ptr2page_index(container_page);
    let pcid_allocator_head =
        page_ptr2page_index(pcid_allocator_page);
    let ghost protected_page_index_seq = seq![
        container_head,
        pcid_allocator_head,
        page_ptr2page_index(allocator_4k_page),
        page_ptr2page_index(allocator_2m_page),
        page_ptr2page_index(allocator_1g_page),
        page_ptr2page_index(scheduler_page),
        page_ptr2page_index(cpu_set_page),
        page_ptr2page_index(process_page),
        page_ptr2page_index(pagetable_page),
        page_ptr2page_index(l4_page),
        page_ptr2page_index(thread_page),
    ];
    let ghost protected_page_indices =
        protected_page_index_seq.to_set();
    proof {
        page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
        page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page,);
        assert(page_ptr_valid(container_page)) by { reveal(page_ptr_valid); reveal(page_ptr_2m_valid); };
        assert(page_ptr_valid(pcid_allocator_page)) by { reveal(page_ptr_valid); reveal(page_ptr_2m_valid); };
        assert(container_head != pcid_allocator_head) by { page_ptr2page_index_injective(); };
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
        assert(page_2m_tail_indices(container_head).disjoint(protected_page_indices) && page_2m_tail_indices(pcid_allocator_head).disjoint(protected_page_indices)) by {
            owned_4k_page_not_in_2m_tail(&reference_krnl, allocator_4k_page, container_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, allocator_2m_page, container_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, allocator_1g_page, container_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, scheduler_page, container_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, cpu_set_page, container_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, process_page, container_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, pagetable_page, container_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, l4_page, container_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, thread_page, container_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, allocator_4k_page, pcid_allocator_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, allocator_2m_page, pcid_allocator_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, allocator_1g_page, pcid_allocator_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, scheduler_page, pcid_allocator_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, cpu_set_page, pcid_allocator_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, process_page, pcid_allocator_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, pagetable_page, pcid_allocator_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, l4_page, pcid_allocator_head,);
            owned_4k_page_not_in_2m_tail(&reference_krnl, thread_page, pcid_allocator_head,);
            protected_page_index_seq.to_set_ensures();
            reveal(Seq::contains);
            reveal(Set::disjoint);
        };
        assert(funding_pages.to_set().disjoint(page_2m_all_ptrs(container_head),)) by { reveal(new_container_moved_pages); reveal(Set::disjoint); };
        assert(funding_pages.to_set().disjoint(page_2m_all_ptrs(pcid_allocator_head),)) by { reveal(new_container_moved_pages); reveal(Set::disjoint); };
        page_ptr_indices_disjoint_from_2m_tail(funding_pages, funding_indices, container_head,);
        page_ptr_indices_disjoint_from_2m_tail(funding_pages, funding_indices, pcid_allocator_head,);
        assert(funding_pages.to_set().map(|page_ptr: PagePtr| page_ptr2page_index(page_ptr),) =~= funding_indices) by { broadcast use Seq::lemma_to_set_map_commutes; };
    }
    set_owned_2m_page_tail_pair_container(
        pages, container_head, pcid_allocator_head, owning_container, Ghost(reference_krnl.pg_arr), Ghost(funding_pages),
        Ghost(funding_page_lock_perms.dom()), Ghost(funding_indices), Ghost(protected_page_indices), Tracked(lctx),
        Tracked(container_tail_lock_perms), Tracked(pcid_allocator_tail_lock_perms),
    );
    proof {
        assert(page_array_wf(*pages));
        page_ptr_valid_imply_page_index_valid();
        protected_page_index_seq.to_set_ensures();
        reveal(Seq::contains);
        assert({
            &&& protected_page_indices.contains(container_head)
            &&& protected_page_indices.contains(pcid_allocator_head)
            &&& protected_page_indices.contains(
                page_ptr2page_index(allocator_4k_page),
            )
            &&& protected_page_indices.contains(
                page_ptr2page_index(allocator_2m_page),
            )
            &&& protected_page_indices.contains(
                page_ptr2page_index(allocator_1g_page),
            )
            &&& protected_page_indices.contains(
                page_ptr2page_index(scheduler_page),
            )
            &&& protected_page_indices.contains(
                page_ptr2page_index(cpu_set_page),
            )
            &&& protected_page_indices.contains(
                page_ptr2page_index(process_page),
            )
            &&& protected_page_indices.contains(
                page_ptr2page_index(pagetable_page),
            )
            &&& protected_page_indices.contains(
                page_ptr2page_index(l4_page),
            )
            &&& protected_page_indices.contains(
                page_ptr2page_index(thread_page),
            )
        });
        assert({
            &&& pages.spec_index(container_head) == reference_krnl.pg_arr.spec_index(container_head)
            &&& pages.spec_index(pcid_allocator_head) == reference_krnl.pg_arr.spec_index(pcid_allocator_head)
            &&& pages.spec_index(page_ptr2page_index(allocator_4k_page)) == reference_krnl.pg_arr.spec_index(
                    page_ptr2page_index(allocator_4k_page),
                )
            &&& pages.spec_index(page_ptr2page_index(allocator_2m_page)) == reference_krnl.pg_arr.spec_index(
                    page_ptr2page_index(allocator_2m_page),
                )
            &&& pages.spec_index(page_ptr2page_index(allocator_1g_page)) == reference_krnl.pg_arr.spec_index(
                    page_ptr2page_index(allocator_1g_page),
                )
            &&& pages.spec_index(page_ptr2page_index(scheduler_page)) == reference_krnl.pg_arr.spec_index(
                    page_ptr2page_index(scheduler_page),
                )
            &&& pages.spec_index(page_ptr2page_index(cpu_set_page)) == reference_krnl.pg_arr.spec_index(
                    page_ptr2page_index(cpu_set_page),
                )
            &&& pages.spec_index(page_ptr2page_index(process_page)) == reference_krnl.pg_arr.spec_index(
                    page_ptr2page_index(process_page),
                )
            &&& pages.spec_index(page_ptr2page_index(pagetable_page)) == reference_krnl.pg_arr.spec_index(
                    page_ptr2page_index(pagetable_page),
                )
            &&& pages.spec_index(page_ptr2page_index(l4_page)) == reference_krnl.pg_arr.spec_index(
                    page_ptr2page_index(l4_page),
                )
            &&& pages.spec_index(page_ptr2page_index(thread_page)) == reference_krnl.pg_arr.spec_index(
                    page_ptr2page_index(thread_page),
                )
        });
        assert(process_pages_wf(*pages, reference_krnl.prc_mp)) by { reveal(process_pages_wf); };
        assert(scheduler_pages_wf(reference_krnl.sched_mp, *pages)) by { reveal(scheduler_pages_wf); };
        assert(cpu_set_pages_wf(reference_krnl.cpu_set_mp, *pages)) by { reveal(cpu_set_pages_wf); };
    }
}
}
