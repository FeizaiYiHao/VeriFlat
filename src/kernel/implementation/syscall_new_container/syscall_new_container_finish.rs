use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub(super) fn finish_staged_container_publish(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, pages_4k: &ArrayVec<PagePtr, 9>,
    container_page: PagePtr, pcid_allocator_page: PagePtr,
    Tracked(container_tail_lock_perms): Tracked<Map<PageIndex, LockPerm>>,
    Tracked(pcid_allocator_tail_lock_perms): Tracked<Map<PageIndex, LockPerm>>,
    Tracked(container_page_lock_perm): Tracked<LockPerm>,
    Tracked(pcid_allocator_page_lock_perm): Tracked<LockPerm>,
    Tracked(allocator_4k_page_lock_perm): Tracked<LockPerm>, Tracked(allocator_2m_page_lock_perm): Tracked<LockPerm>,
    Tracked(allocator_1g_page_lock_perm): Tracked<LockPerm>, Tracked(scheduler_page_lock_perm): Tracked<LockPerm>,
    Tracked(cpu_set_page_lock_perm): Tracked<LockPerm>, Tracked(process_page_lock_perm): Tracked<LockPerm>,
    Tracked(pagetable_page_lock_perm): Tracked<LockPerm>, Tracked(l4_page_lock_perm): Tracked<LockPerm>,
    Tracked(thread_page_lock_perm): Tracked<LockPerm>, Tracked(child_container_lock_perm): Tracked<LockPerm>,
    Tracked(child_process_lock_perm): Tracked<LockPerm>, Tracked(child_pagetable_lock_perm): Tracked<LockPerm>,
    Tracked(child_scheduler_lock_perm): Tracked<LockPerm>,
    Tracked(child_pcid_allocator_lock_perm): Tracked<LockPerm>,
) -> (ret: (Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>))
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        pages_4k.wf(),
        pages_4k.len() == 9,
        pages_4k.view().no_duplicates(),
        page_ptr_valid(pages_4k.view().spec_index(0)),
        page_ptr_valid(pages_4k.view().spec_index(1)),
        page_ptr_valid(pages_4k.view().spec_index(2)),
        page_ptr_valid(pages_4k.view().spec_index(3)),
        page_ptr_valid(pages_4k.view().spec_index(4)),
        page_ptr_valid(pages_4k.view().spec_index(5)),
        page_ptr_valid(pages_4k.view().spec_index(6)),
        page_ptr_valid(pages_4k.view().spec_index(7)),
        page_ptr_valid(pages_4k.view().spec_index(8)),
        old(krnl).allc_4k_mp.dom().contains(
            pages_4k.view().spec_index(0),
        ),
        page_ptr_2m_valid(container_page),
        page_ptr_2m_valid(pcid_allocator_page),
        container_page != pcid_allocator_page,
        pages_4k.view().to_set().disjoint(
            page_2m_all_ptrs(page_ptr2page_index(container_page)),
        ),
        pages_4k.view().to_set().disjoint(
            page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)),
        ),
        page_2m_all_ptrs(page_ptr2page_index(container_page)).disjoint(
            page_2m_all_ptrs(page_ptr2page_index(pcid_allocator_page)),
        ),
        page_2m_tail_indices(page_ptr2page_index(container_page)).disjoint(
            set![
                page_ptr2page_index(container_page),
                page_ptr2page_index(pcid_allocator_page),
                page_ptr2page_index(pages_4k.view().spec_index(0)),
                page_ptr2page_index(pages_4k.view().spec_index(1)),
                page_ptr2page_index(pages_4k.view().spec_index(2)),
                page_ptr2page_index(pages_4k.view().spec_index(3)),
                page_ptr2page_index(pages_4k.view().spec_index(4)),
                page_ptr2page_index(pages_4k.view().spec_index(5)),
                page_ptr2page_index(pages_4k.view().spec_index(6)),
                page_ptr2page_index(pages_4k.view().spec_index(7)), page_ptr2page_index(pages_4k.view().spec_index(8)),
            ],
        ),
        page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page))
            .disjoint(
                set![
                    page_ptr2page_index(container_page),
                    page_ptr2page_index(pcid_allocator_page),
                    page_ptr2page_index(pages_4k.view().spec_index(0)),
                    page_ptr2page_index(pages_4k.view().spec_index(1)),
                    page_ptr2page_index(pages_4k.view().spec_index(2)),
                    page_ptr2page_index(pages_4k.view().spec_index(3)),
                    page_ptr2page_index(pages_4k.view().spec_index(4)),
                    page_ptr2page_index(pages_4k.view().spec_index(5)),
                    page_ptr2page_index(pages_4k.view().spec_index(6)),
                    page_ptr2page_index(pages_4k.view().spec_index(7)), page_ptr2page_index(pages_4k.view().spec_index(8)),
                ],
            ),
        old(lctx).page_lock_map().dom()
            .difference(
                page_2m_tail_indices(page_ptr2page_index(container_page))
                    .union(page_2m_tail_indices(page_ptr2page_index(pcid_allocator_page)))
                    .union(seq![
                        page_ptr2page_index(pages_4k.view().spec_index(0)),
                        page_ptr2page_index(pages_4k.view().spec_index(1)),
                        page_ptr2page_index(pages_4k.view().spec_index(2)),
                        page_ptr2page_index(pages_4k.view().spec_index(3)),
                        page_ptr2page_index(pages_4k.view().spec_index(8)),
                        page_ptr2page_index(pages_4k.view().spec_index(4)),
                        page_ptr2page_index(pages_4k.view().spec_index(5)),
                        page_ptr2page_index(pages_4k.view().spec_index(6)),
                        page_ptr2page_index(container_page),
                        page_ptr2page_index(pcid_allocator_page),
                    ].to_set()),
            )
            =~= set![page_ptr2page_index(pages_4k.view().spec_index(7))],
        owned_2m_tail_lock_perms_wf(container_tail_lock_perms, old(krnl).pg_arr, old(lctx), page_ptr2page_index(container_page)),
        owned_2m_tail_lock_perms_wf(pcid_allocator_tail_lock_perms, old(krnl).pg_arr, old(lctx), page_ptr2page_index(pcid_allocator_page)),
        old(krnl).ctn_mp.dom().contains(container_page),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_page, TypedLockMode::Write),
        child_container_lock_perm.state() is WriteLock,
        child_container_lock_perm.thread_id() == old(lctx).thread_id(),
        child_container_lock_perm.lock_id()
            == old(krnl).ctn_mp.spec_index(container_page)
                .locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(pages_4k.view().spec_index(4)),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), pages_4k.view().spec_index(4), TypedLockMode::Write),
        child_process_lock_perm.state() is WriteLock,
        child_process_lock_perm.thread_id() == old(lctx).thread_id(),
        child_process_lock_perm.lock_id()
            == old(krnl).prc_mp.spec_index(pages_4k.view().spec_index(4))
                .locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(pages_4k.view().spec_index(5)),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pages_4k.view().spec_index(5), TypedLockMode::Write),
        child_pagetable_lock_perm.state() is WriteLock,
        child_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        child_pagetable_lock_perm.lock_id()
            == old(krnl).pt_mp.spec_index(pages_4k.view().spec_index(5))
                .locking_thread()->Write_lock_id,
        old(krnl).sched_mp.dom().contains(pages_4k.view().spec_index(3)),
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), pages_4k.view().spec_index(3), TypedLockMode::Write),
        child_scheduler_lock_perm.state() is WriteLock,
        child_scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
        child_scheduler_lock_perm.lock_id()
            == old(krnl).sched_mp.spec_index(pages_4k.view().spec_index(3))
                .locking_thread()->Write_lock_id,
        old(krnl).pcid_allc_mp.dom().contains(pcid_allocator_page),
        typed_lock_map_contains_mode(old(lctx).pcid_allocator_lock_map(), pcid_allocator_page, TypedLockMode::Write),
        child_pcid_allocator_lock_perm.state() is WriteLock,
        child_pcid_allocator_lock_perm.thread_id()
            == old(lctx).thread_id(),
        child_pcid_allocator_lock_perm.lock_id()
            == old(krnl).pcid_allc_mp.spec_index(pcid_allocator_page)
                .locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(container_page), TypedLockMode::Write),
        container_page_lock_perm.state() is WriteLock,
        container_page_lock_perm.thread_id() == old(lctx).thread_id(),
        container_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(
                container_page,
            )).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pcid_allocator_page), TypedLockMode::Write),
        pcid_allocator_page_lock_perm.state() is WriteLock,
        pcid_allocator_page_lock_perm.thread_id()
            == old(lctx).thread_id(),
        pcid_allocator_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(
                pcid_allocator_page,
            )).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pages_4k.view().spec_index(0)), TypedLockMode::Write),
        allocator_4k_page_lock_perm.state() is WriteLock,
        allocator_4k_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_4k_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(
                pages_4k.view().spec_index(0),
            )).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pages_4k.view().spec_index(1)), TypedLockMode::Write),
        allocator_2m_page_lock_perm.state() is WriteLock,
        allocator_2m_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_2m_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(
                pages_4k.view().spec_index(1),
            )).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pages_4k.view().spec_index(2)), TypedLockMode::Write),
        allocator_1g_page_lock_perm.state() is WriteLock,
        allocator_1g_page_lock_perm.thread_id() == old(lctx).thread_id(),
        allocator_1g_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(
                pages_4k.view().spec_index(2),
            )).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pages_4k.view().spec_index(3)), TypedLockMode::Write),
        scheduler_page_lock_perm.state() is WriteLock,
        scheduler_page_lock_perm.thread_id() == old(lctx).thread_id(),
        scheduler_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(
                pages_4k.view().spec_index(3),
            )).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pages_4k.view().spec_index(8)), TypedLockMode::Write),
        cpu_set_page_lock_perm.state() is WriteLock,
        cpu_set_page_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_set_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(
                pages_4k.view().spec_index(8),
            )).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pages_4k.view().spec_index(4)), TypedLockMode::Write),
        process_page_lock_perm.state() is WriteLock,
        process_page_lock_perm.thread_id() == old(lctx).thread_id(),
        process_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(
                pages_4k.view().spec_index(4),
            )).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pages_4k.view().spec_index(5)), TypedLockMode::Write),
        pagetable_page_lock_perm.state() is WriteLock,
        pagetable_page_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(
                pages_4k.view().spec_index(5),
            )).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pages_4k.view().spec_index(6)), TypedLockMode::Write),
        l4_page_lock_perm.state() is WriteLock,
        l4_page_lock_perm.thread_id() == old(lctx).thread_id(),
        l4_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(
                pages_4k.view().spec_index(6),
            )).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pages_4k.view().spec_index(7)), TypedLockMode::Write),
        thread_page_lock_perm.state() is WriteLock,
        thread_page_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(
                pages_4k.view().spec_index(7),
            )).view().locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        kernel_k_to_kernel_u(*final(krnl))
            == kernel_k_to_kernel_u(*old(krnl)),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(lctx).page_lock_map().dom()
            =~= set![page_ptr2page_index(pages_4k.view().spec_index(7))],
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map().dom() == old(lctx).endpoint_lock_map().dom(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map().dom() == old(lctx).pcid_allocator_lock_map().dom().remove(pcid_allocator_page),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).iommu_table_lock_map().dom() == old(lctx).iommu_table_lock_map().dom(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(krnl).allc_4k_mp.dom().contains(
            pages_4k.view().spec_index(0),
        ),
        final(krnl).allc_4k_mp.spec_index(
            pages_4k.view().spec_index(0),
        ) == old(krnl).allc_4k_mp.spec_index(
            pages_4k.view().spec_index(0),
        ),
        *final(krnl) == (KernelK {
            pg_arr: final(krnl).pg_arr,
            pcid_allc_mp: final(krnl).pcid_allc_mp,
            ..*old(krnl)
        }),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), container_page, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), pages_4k.view().spec_index(4), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), pages_4k.view().spec_index(5), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).scheduler_lock_map(), pages_4k.view().spec_index(3), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pages_4k.view().spec_index(7)), TypedLockMode::Write),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(
            pages_4k.view().spec_index(7),
        )) == old(krnl).pg_arr.spec_index(page_ptr2page_index(
            pages_4k.view().spec_index(7),
        )),
        ret.0.view().state() is WriteLock,
        ret.0.view().thread_id() == final(lctx).thread_id(),
        ret.0.view().lock_id()
            == final(krnl).ctn_mp.spec_index(container_page)
                .locking_thread()->Write_lock_id,
        ret.1.view().state() is WriteLock,
        ret.1.view().thread_id() == final(lctx).thread_id(),
        ret.1.view().lock_id()
            == final(krnl).prc_mp.spec_index(
                pages_4k.view().spec_index(4),
            ).locking_thread()->Write_lock_id,
        ret.2.view().state() is WriteLock,
        ret.2.view().thread_id() == final(lctx).thread_id(),
        ret.2.view().lock_id()
            == final(krnl).pt_mp.spec_index(
                pages_4k.view().spec_index(5),
            ).locking_thread()->Write_lock_id,
        ret.3.view().state() is WriteLock,
        ret.3.view().thread_id() == final(lctx).thread_id(),
        ret.3.view().lock_id()
            == final(krnl).sched_mp.spec_index(
                pages_4k.view().spec_index(3),
            ).locking_thread()->Write_lock_id,
        ret.4.view().state() is WriteLock,
        ret.4.view().thread_id() == final(lctx).thread_id(),
        ret.4.view().lock_id()
            == final(krnl).pg_arr.spec_index(page_ptr2page_index(
                pages_4k.view().spec_index(7),
            )).view().locking_thread()->Write_lock_id,
{
    let allocator_4k_page = *pages_4k.get(0);
    let allocator_2m_page = *pages_4k.get(1);
    let allocator_1g_page = *pages_4k.get(2);
    let scheduler_page = *pages_4k.get(3);
    let cpu_set_page = *pages_4k.get(8);
    let process_page = *pages_4k.get(4);
    let pagetable_page = *pages_4k.get(5);
    let l4_page = *pages_4k.get(6);
    let thread_page = *pages_4k.get(7);
    let container_head = page_ptr2page_index(container_page);
    let pcid_allocator_head = page_ptr2page_index(pcid_allocator_page);
    proof {
        page_ptr_2m_valid_imply_page_index_2m_valid(container_page);
        page_ptr_2m_valid_imply_page_index_2m_valid(pcid_allocator_page);
        assert({
            &&& page_ptr_valid(container_page)
            &&& page_ptr_valid(pcid_allocator_page)
        });
        assert({
            &&& index_valid(NUM_PAGES, page_ptr2page_index(allocator_4k_page))
            &&& index_valid(NUM_PAGES, page_ptr2page_index(allocator_2m_page))
            &&& index_valid(NUM_PAGES, page_ptr2page_index(allocator_1g_page))
            &&& index_valid(NUM_PAGES, page_ptr2page_index(scheduler_page))
            &&& index_valid(NUM_PAGES, page_ptr2page_index(cpu_set_page))
            &&& index_valid(NUM_PAGES, page_ptr2page_index(process_page))
            &&& index_valid(NUM_PAGES, page_ptr2page_index(pagetable_page))
            &&& index_valid(NUM_PAGES, page_ptr2page_index(l4_page))
            &&& index_valid(NUM_PAGES, page_ptr2page_index(thread_page))
        }) by {
            page_ptr_valid_imply_page_index_valid();
        };
    }
    wunlock_owned_2m_page_tails(krnl, container_head, Tracked(&mut *lctx), Tracked(container_tail_lock_perms));
    proof {
        assert(owned_2m_tail_lock_perms_wf(
            pcid_allocator_tail_lock_perms,
            krnl.pg_arr,
            lctx,
            pcid_allocator_head,
        ));
    }
    wunlock_owned_2m_page_tails(krnl, pcid_allocator_head, Tracked(&mut *lctx), Tracked(pcid_allocator_tail_lock_perms));
    proof {
        new_container_page_positions(pages_4k.view());
        assert({
            &&& container_head
                != page_ptr2page_index(allocator_4k_page)
            &&& container_head
                != page_ptr2page_index(allocator_2m_page)
            &&& container_head
                != page_ptr2page_index(allocator_1g_page)
            &&& container_head != page_ptr2page_index(scheduler_page)
            &&& container_head != page_ptr2page_index(cpu_set_page)
            &&& container_head != page_ptr2page_index(process_page)
            &&& container_head != page_ptr2page_index(pagetable_page)
            &&& container_head != page_ptr2page_index(l4_page)
            &&& container_head != page_ptr2page_index(thread_page)
            &&& pcid_allocator_head
                != page_ptr2page_index(allocator_4k_page)
            &&& pcid_allocator_head
                != page_ptr2page_index(allocator_2m_page)
            &&& pcid_allocator_head
                != page_ptr2page_index(allocator_1g_page)
            &&& pcid_allocator_head
                != page_ptr2page_index(scheduler_page)
            &&& pcid_allocator_head != page_ptr2page_index(cpu_set_page)
            &&& pcid_allocator_head != page_ptr2page_index(process_page)
            &&& pcid_allocator_head
                != page_ptr2page_index(pagetable_page)
            &&& pcid_allocator_head != page_ptr2page_index(l4_page)
            &&& pcid_allocator_head != page_ptr2page_index(thread_page)
        }) by {
            page_ptr_roundtrip();
            page_ptr2page_index_injective();
            page_2m_all_ptrs_contains_head(container_head);
            page_2m_all_ptrs_contains_head(pcid_allocator_head);
        };
        assert({
            &&& typed_lock_map_contains_mode(lctx.page_lock_map(), container_head, TypedLockMode::Write)
            &&& container_page_lock_perm.lock_id()
                == krnl.pg_arr.spec_index(container_head)
                    .view().locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(lctx.page_lock_map(), pcid_allocator_head, TypedLockMode::Write)
            &&& pcid_allocator_page_lock_perm.lock_id()
                == krnl.pg_arr.spec_index(pcid_allocator_head)
                    .view().locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(allocator_4k_page), TypedLockMode::Write)
            &&& allocator_4k_page_lock_perm.lock_id()
                == krnl.pg_arr.spec_index(page_ptr2page_index(
                    allocator_4k_page,
                )).view().locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(allocator_2m_page), TypedLockMode::Write)
            &&& allocator_2m_page_lock_perm.lock_id()
                == krnl.pg_arr.spec_index(page_ptr2page_index(
                    allocator_2m_page,
                )).view().locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(allocator_1g_page), TypedLockMode::Write)
            &&& allocator_1g_page_lock_perm.lock_id()
                == krnl.pg_arr.spec_index(page_ptr2page_index(
                    allocator_1g_page,
                )).view().locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(scheduler_page), TypedLockMode::Write)
            &&& scheduler_page_lock_perm.lock_id()
                == krnl.pg_arr.spec_index(page_ptr2page_index(
                    scheduler_page,
                )).view().locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(process_page), TypedLockMode::Write)
            &&& process_page_lock_perm.lock_id()
                == krnl.pg_arr.spec_index(page_ptr2page_index(
                    process_page,
                )).view().locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(pagetable_page), TypedLockMode::Write)
            &&& pagetable_page_lock_perm.lock_id()
                == krnl.pg_arr.spec_index(page_ptr2page_index(
                    pagetable_page,
                )).view().locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(l4_page), TypedLockMode::Write)
            &&& l4_page_lock_perm.lock_id()
                == krnl.pg_arr.spec_index(page_ptr2page_index(l4_page))
                    .view().locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(thread_page), TypedLockMode::Write)
            &&& thread_page_lock_perm.lock_id()
                == krnl.pg_arr.spec_index(page_ptr2page_index(thread_page))
                    .view().locking_thread()->Write_lock_id
        });
    }
    krnl.wunlock_page(page_ptr2page_index(allocator_4k_page), Tracked(&mut *lctx), Tracked(allocator_4k_page_lock_perm));
    krnl.wunlock_page(page_ptr2page_index(allocator_2m_page), Tracked(&mut *lctx), Tracked(allocator_2m_page_lock_perm));
    krnl.wunlock_page(page_ptr2page_index(allocator_1g_page), Tracked(&mut *lctx), Tracked(allocator_1g_page_lock_perm));
    krnl.wunlock_page(page_ptr2page_index(scheduler_page), Tracked(&mut *lctx), Tracked(scheduler_page_lock_perm));
    krnl.wunlock_page(page_ptr2page_index(cpu_set_page), Tracked(&mut *lctx), Tracked(cpu_set_page_lock_perm));
    krnl.wunlock_page(page_ptr2page_index(process_page), Tracked(&mut *lctx), Tracked(process_page_lock_perm));
    krnl.wunlock_page(page_ptr2page_index(pagetable_page), Tracked(&mut *lctx), Tracked(pagetable_page_lock_perm));
    krnl.wunlock_page(page_ptr2page_index(l4_page), Tracked(&mut *lctx), Tracked(l4_page_lock_perm));
    proof {
        assert(
            typed_lock_map_contains_mode(lctx.page_lock_map(), container_head, TypedLockMode::Write)
                && container_page_lock_perm.lock_id()
                    == krnl.pg_arr.spec_index(container_head)
                        .view().locking_thread()->Write_lock_id
        );
    }
    krnl.wunlock_page(container_head, Tracked(&mut *lctx), Tracked(container_page_lock_perm));
    proof {
        assert(
            typed_lock_map_contains_mode(lctx.page_lock_map(), pcid_allocator_head, TypedLockMode::Write)
                && pcid_allocator_page_lock_perm.lock_id()
                    == krnl.pg_arr.spec_index(pcid_allocator_head)
                        .view().locking_thread()->Write_lock_id
        );
    }
    krnl.wunlock_page(pcid_allocator_head, Tracked(&mut *lctx), Tracked(pcid_allocator_page_lock_perm));
    krnl.wunlock_pcid_allocator(pcid_allocator_page, Tracked(&mut *lctx), Tracked(child_pcid_allocator_lock_perm));

    (
        Tracked(child_container_lock_perm),
        Tracked(child_process_lock_perm),
        Tracked(child_pagetable_lock_perm),
        Tracked(child_scheduler_lock_perm),
        Tracked(thread_page_lock_perm),
    )
}
}
