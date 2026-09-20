use vstd::prelude::*;
use crate::*;

verus! {
#[verifier::spinoff_prover]
pub(super) fn release_staged_process_with_iommu_input_locks(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId,
    container_ptr: RwLockContainerPtr, parent_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr,
    current_thread_ptr: RwLockThreadPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr,
    source_pagetable_ptr: RwLockPageTableRoot, target_pagetable_ptr: RwLockPageTableRoot,
    iommu_table_ptr: RwLockPageTableRoot, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr,
    l4_page_ptr: PagePtr, iommu_table_page_ptr: PagePtr, iommu_l4_page_ptr: PagePtr,
    Tracked(process_page_lock_perm): Tracked<LockPerm>, Tracked(pagetable_page_lock_perm): Tracked<LockPerm>,
    Tracked(l4_page_lock_perm): Tracked<LockPerm>, Tracked(iommu_table_page_lock_perm): Tracked<LockPerm>,
    Tracked(iommu_l4_page_lock_perm): Tracked<LockPerm>, Tracked(parent_lock_perm): Tracked<LockPerm>,
    Tracked(pcid_allocator_lock_perm): Tracked<LockPerm>,
)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Release,
        old(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        page_ptr_valid(process_page_ptr),
        page_ptr_valid(pagetable_page_ptr),
        page_ptr_valid(l4_page_ptr),
        page_ptr_valid(iommu_table_page_ptr),
        page_ptr_valid(iommu_l4_page_ptr),
        process_page_ptr != pagetable_page_ptr,
        process_page_ptr != l4_page_ptr,
        process_page_ptr != iommu_table_page_ptr,
        process_page_ptr != iommu_l4_page_ptr,
        pagetable_page_ptr != l4_page_ptr,
        pagetable_page_ptr != iommu_table_page_ptr,
        pagetable_page_ptr != iommu_l4_page_ptr,
        l4_page_ptr != iommu_table_page_ptr,
        l4_page_ptr != iommu_l4_page_ptr,
        iommu_table_page_ptr != iommu_l4_page_ptr,
        old(lctx).page_lock_map().dom() =~= set![
            page_ptr2page_index(process_page_ptr),
            page_ptr2page_index(pagetable_page_ptr),
            page_ptr2page_index(l4_page_ptr),
            page_ptr2page_index(iommu_table_page_ptr),
            page_ptr2page_index(iommu_l4_page_ptr),
        ],
        typed_lock_map_contains_mode(
            old(lctx).page_lock_map(),
            page_ptr2page_index(process_page_ptr),
            TypedLockMode::Write,
        ),
        typed_lock_map_contains_mode(
            old(lctx).page_lock_map(),
            page_ptr2page_index(pagetable_page_ptr),
            TypedLockMode::Write,
        ),
        typed_lock_map_contains_mode(
            old(lctx).page_lock_map(),
            page_ptr2page_index(l4_page_ptr),
            TypedLockMode::Write,
        ),
        typed_lock_map_contains_mode(
            old(lctx).page_lock_map(),
            page_ptr2page_index(iommu_table_page_ptr),
            TypedLockMode::Write,
        ),
        typed_lock_map_contains_mode(
            old(lctx).page_lock_map(),
            page_ptr2page_index(iommu_l4_page_ptr),
            TypedLockMode::Write,
        ),
        process_page_lock_perm.state() is WriteLock,
        process_page_lock_perm.thread_id() == old(lctx).thread_id(),
        process_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(
                process_page_ptr,
            )).view().locking_thread()->Write_lock_id,
        pagetable_page_lock_perm.state() is WriteLock,
        pagetable_page_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(
                pagetable_page_ptr,
            )).view().locking_thread()->Write_lock_id,
        l4_page_lock_perm.state() is WriteLock,
        l4_page_lock_perm.thread_id() == old(lctx).thread_id(),
        l4_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(
                l4_page_ptr,
            )).view().locking_thread()->Write_lock_id,
        iommu_table_page_lock_perm.state() is WriteLock,
        iommu_table_page_lock_perm.thread_id() == old(lctx).thread_id(),
        iommu_table_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(
                iommu_table_page_ptr,
            )).view().locking_thread()->Write_lock_id,
        iommu_l4_page_lock_perm.state() is WriteLock,
        iommu_l4_page_lock_perm.thread_id() == old(lctx).thread_id(),
        iommu_l4_page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(
                iommu_l4_page_ptr,
            )).view().locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(parent_ptr),
        old(krnl).prc_mp.dom().contains(child_ptr),
        parent_ptr != child_ptr,
        old(krnl).prc_mp.spec_index(parent_ptr)
            .view().owned_threads.view().len() != 0,
        !old(krnl).prc_mp.spec_index(parent_ptr).being_killed(),
        typed_lock_map_contains_mode(
            old(lctx).process_lock_map(),
            parent_ptr,
            TypedLockMode::Write,
        ),
        parent_lock_perm.state() is WriteLock,
        parent_lock_perm.thread_id() == old(lctx).thread_id(),
        parent_lock_perm.lock_id()
            == old(krnl).prc_mp.spec_index(parent_ptr)
                .locking_thread()->Write_lock_id,
        old(krnl).pcid_allc_mp.dom().contains(pcid_allocator_ptr),
        typed_lock_map_contains_mode(
            old(lctx).pcid_allocator_lock_map(),
            pcid_allocator_ptr,
            TypedLockMode::Write,
        ),
        pcid_allocator_lock_perm.state() is WriteLock,
        pcid_allocator_lock_perm.thread_id() == old(lctx).thread_id(),
        pcid_allocator_lock_perm.lock_id()
            == old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr)
                .locking_thread()->Write_lock_id,
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom() =~= set![container_ptr],
        old(lctx).process_lock_map().dom() =~= set![parent_ptr, child_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom() =~= set![pcid_allocator_ptr],
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom()
            =~= set![source_pagetable_ptr, target_pagetable_ptr],
        old(lctx).iommu_table_lock_map().dom() =~= set![iommu_table_ptr],
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
    ensures
        final(krnl).inv(),
        kernel_k_to_kernel_u(*final(krnl))
            == kernel_k_to_kernel_u(*old(krnl)),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(lctx).page_lock_map()
            == old(lctx).page_lock_map()
                .remove(page_ptr2page_index(iommu_l4_page_ptr))
                .remove(page_ptr2page_index(iommu_table_page_ptr))
                .remove(page_ptr2page_index(l4_page_ptr))
                .remove(page_ptr2page_index(pagetable_page_ptr))
                .remove(page_ptr2page_index(process_page_ptr)),
        final(lctx).page_lock_map().dom().is_empty(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map()
            == old(lctx).process_lock_map().remove(parent_ptr),
        final(lctx).process_lock_map().dom() =~= set![child_ptr],
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map()
            == old(lctx).pcid_allocator_lock_map()
                .remove(pcid_allocator_ptr),
        final(lctx).pcid_allocator_lock_map().dom().is_empty(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).allocator_4k_lock_maps()
            == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps()
            == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps()
            == old(lctx).allocator_1g_lock_maps(),
        final(lctx).pcid_needflush_lock_map()
            == old(lctx).pcid_needflush_lock_map(),
        *final(krnl) == (KernelK {
            pg_arr: final(krnl).pg_arr,
            prc_mp: final(krnl).prc_mp,
            pcid_allc_mp: final(krnl).pcid_allc_mp,
            ..*old(krnl)
        }),
        final(krnl).prc_mp.dom() == old(krnl).prc_mp.dom(),
        final(krnl).prc_mp.spec_index(parent_ptr).view()
            == old(krnl).prc_mp.spec_index(parent_ptr).view(),
        final(krnl).prc_mp.spec_index(child_ptr)
            == old(krnl).prc_mp.spec_index(child_ptr),
        final(krnl).pcid_allc_mp.dom()
            == old(krnl).pcid_allc_mp.dom(),
        final(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).view()
            == old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).view(),
        final(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
{
    krnl.wunlock_page(
        page_ptr2page_index(iommu_l4_page_ptr),
        Tracked(&mut *lctx),
        Tracked(iommu_l4_page_lock_perm),
    );
    krnl.wunlock_page(
        page_ptr2page_index(iommu_table_page_ptr),
        Tracked(&mut *lctx),
        Tracked(iommu_table_page_lock_perm),
    );
    krnl.wunlock_page(
        page_ptr2page_index(l4_page_ptr),
        Tracked(&mut *lctx),
        Tracked(l4_page_lock_perm),
    );
    krnl.wunlock_page(
        page_ptr2page_index(pagetable_page_ptr),
        Tracked(&mut *lctx),
        Tracked(pagetable_page_lock_perm),
    );
    krnl.wunlock_page(
        page_ptr2page_index(process_page_ptr),
        Tracked(&mut *lctx),
        Tracked(process_page_lock_perm),
    );
    krnl.wunlock_pcid_allocator(
        pcid_allocator_ptr,
        Tracked(&mut *lctx),
        Tracked(pcid_allocator_lock_perm),
    );
    krnl.wunlock_process(
        parent_ptr,
        Tracked(&mut *lctx),
        Tracked(parent_lock_perm),
    );
    proof {
        reveal(typed_lock_maps_removed);
    }
}

}
