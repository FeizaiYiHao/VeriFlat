use vstd::prelude::*;
use vstd::assert_sets_equal;
use crate::*;

verus! {

/// Locks and stable owner relations retained throughout a 4K sharing pass.
pub open spec fn share_mapping_4k_held_context(
    kernel: &KernelK,
    lctx: &LocalContext,
    source_thread: RwLockThreadPtr,
    target_thread: RwLockThreadPtr,
    source_pagetable: RwLockPageTableRoot,
    target_pagetable: RwLockPageTableRoot,
    source_thread_lock_perm: &LockPerm,
    target_thread_lock_perm: &LockPerm,
    source_pagetable_lock_perm: &LockPerm,
    target_pagetable_lock_perm: &LockPerm,
) -> bool {
    &&& kernel.inv()
    &&& lctx.kernel_view_locking_state() is Acquire
    &&& typed_lock_maps_aligned(kernel, lctx)
    &&& page_objects_unlocked(kernel.page_array, lctx.thread_id())
    &&& lctx.held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR)
    &&& source_thread != target_thread
    &&& source_pagetable != target_pagetable
    &&& kernel.thread_map.dom().contains(source_thread)
    &&& kernel.thread_map.dom().contains(target_thread)
    &&& kernel.thread_map.spec_index(source_thread).wlocked_by(lctx)
    &&& !kernel.thread_map.spec_index(source_thread).being_killed()
    &&& kernel.thread_map.spec_index(target_thread).wlocked_by(lctx)
    &&& !kernel.thread_map.spec_index(target_thread).being_killed()
    &&& kernel.thread_map.spec_index(source_thread).view().owning_proc
        != kernel.thread_map.spec_index(target_thread).view().owning_proc
    &&& kernel.thread_map.spec_index(source_thread).view().proc_pagetable_ptr
        == source_pagetable
    &&& kernel.thread_map.spec_index(target_thread).view().proc_pagetable_ptr
        == target_pagetable
    &&& source_thread_lock_perm.state() is WriteLock
    &&& source_thread_lock_perm.thread_id() == lctx.thread_id()
    &&& source_thread_lock_perm.lock_id()
        == kernel.thread_map.spec_index(source_thread)
            .locking_thread()->Write_lock_id
    &&& target_thread_lock_perm.state() is WriteLock
    &&& target_thread_lock_perm.thread_id() == lctx.thread_id()
    &&& target_thread_lock_perm.lock_id()
        == kernel.thread_map.spec_index(target_thread)
            .locking_thread()->Write_lock_id
    &&& kernel.pagetable_map.dom().contains(source_pagetable)
    &&& kernel.pagetable_map.dom().contains(target_pagetable)
    &&& kernel.pagetable_map.spec_index(source_pagetable).wlocked_by(lctx)
    &&& kernel.pagetable_map.spec_index(target_pagetable).wlocked_by(lctx)
    &&& kernel.pagetable_map.spec_index(source_pagetable).view().proc_ptr
        == kernel.thread_map.spec_index(source_thread).view().owning_proc
    &&& kernel.pagetable_map.spec_index(target_pagetable).view().proc_ptr
        == kernel.thread_map.spec_index(target_thread).view().owning_proc
    &&& source_pagetable_lock_perm.state() is WriteLock
    &&& source_pagetable_lock_perm.thread_id() == lctx.thread_id()
    &&& source_pagetable_lock_perm.lock_id()
        == kernel.pagetable_map.spec_index(source_pagetable)
            .locking_thread()->Write_lock_id
    &&& target_pagetable_lock_perm.state() is WriteLock
    &&& target_pagetable_lock_perm.thread_id() == lctx.thread_id()
    &&& target_pagetable_lock_perm.lock_id()
        == kernel.pagetable_map.spec_index(target_pagetable)
            .locking_thread()->Write_lock_id
    &&& lctx.lock_entry_contains(
        kernel.thread_map.lock_id_by_key(source_thread),
        KernelObjId::Thread(source_thread),
    )
    &&& lctx.lock_entry_contains(
        kernel.thread_map.lock_id_by_key(target_thread),
        KernelObjId::Thread(target_thread),
    )
    &&& lctx.lock_entry_contains(
        kernel.pagetable_map.lock_id_by_key(source_pagetable),
        KernelObjId::PageTable(source_pagetable),
    )
    &&& lctx.lock_entry_contains(
        kernel.pagetable_map.lock_id_by_key(target_pagetable),
        KernelObjId::PageTable(target_pagetable),
    )
}

pub open spec fn share_mapping_4k_source_range_present(
    kernel: &KernelK,
    source_pagetable: RwLockPageTableRoot,
    source_range: &VaRange4K,
) -> bool
    recommends
        kernel.pagetable_map.dom().contains(source_pagetable),
        kernel.pagetable_map.spec_index(source_pagetable).view().wf(),
        source_range.wf(),
        kernel.pagetable_map.spec_index(source_pagetable).view().kernel_l4_end
            <= spec_va2index(source_range.start).0,
{
    &&& kernel.pagetable_map.spec_index(source_pagetable).view()
        .spec_mapping_4k_va_range_present(source_range)
    &&& forall|i: int|
        #![trigger kernel.pagetable_map.spec_index(source_pagetable)
            .view().mapping_4k().spec_index(
                source_range.view().spec_index(i),
            )]
        0 <= i < source_range.len
        ==> {
            let source_va = source_range.view().spec_index(i);
            let source_entry = kernel.pagetable_map
                .spec_index(source_pagetable).view().mapping_4k()
                .spec_index(source_va);
            let page_index = page_ptr2page_index(source_entry.addr);
            &&& kernel.pagetable_map.spec_index(source_pagetable).view()
                .mapping_4k().dom().contains(source_va)
            &&& source_entry.present
            &&& page_ptr_valid(source_entry.addr)
            &&& index_valid(NUM_PAGES, page_index)
            &&& kernel.page_array.spec_index(page_index).view().view().state
                is Mapped4k
            &&& kernel.page_array.spec_index(page_index).view().view()
                .mappings().contains((source_pagetable, source_va))
        }
}

pub open spec fn share_mapping_4k_leaf_structure_ready(
    kernel: &KernelK,
    source_pagetable: RwLockPageTableRoot,
    target_pagetable: RwLockPageTableRoot,
    source_va: VAddr,
    target_va: VAddr,
) -> bool {
    let source_indices = spec_va2index(source_va);
    let target_indices = spec_va2index(target_va);
    &&& va_4k_valid(source_va)
    &&& va_4k_valid(target_va)
    &&& kernel.pagetable_map.spec_index(source_pagetable).view().kernel_l4_end
        <= source_indices.0
    &&& pei_valid(source_indices.0)
    &&& pei_valid(source_indices.1)
    &&& pei_valid(source_indices.2)
    &&& pei_valid(source_indices.3)
    &&& kernel.pagetable_map.spec_index(source_pagetable).view()
        .mapping_4k().dom().contains(source_va)
    &&& kernel.pagetable_map.spec_index(source_pagetable).view()
        .mapping_4k().spec_index(source_va).present
    &&& kernel.pagetable_map.spec_index(target_pagetable).view().kernel_l4_end
        <= target_indices.0
    &&& pei_valid(target_indices.0)
    &&& pei_valid(target_indices.1)
    &&& pei_valid(target_indices.2)
    &&& pei_valid(target_indices.3)
    &&& !kernel.pagetable_map.spec_index(target_pagetable).view()
        .mapping_4k().dom().contains(target_va)
    &&& kernel.pagetable_map.spec_index(target_pagetable).view()
        .spec_resolve_mapping_l2(
            target_indices.0, target_indices.1, target_indices.2,
        ) is Some
}

pub open spec fn share_mapping_4k_leaf_owner_compatible(
    kernel: &KernelK,
    source_pagetable: RwLockPageTableRoot,
    target_thread: RwLockThreadPtr,
    source_va: VAddr,
) -> bool {
    let owner = kernel.pagetable_map.spec_index(source_pagetable).view()
        .mapping_4k().spec_index(source_va).owning_container@;
    &&& kernel.thread_map.dom().contains(target_thread)
    &&& kernel.container_map.dom().contains(owner)
    &&& (kernel.thread_map.spec_index(target_thread).view().owning_container
            == owner
        || kernel.thread_map.spec_index(target_thread).view()
            .upper_container_seq@.contains(owner))
}

pub open spec fn share_mapping_4k_leaf_ready(
    kernel: &KernelK,
    source_pagetable: RwLockPageTableRoot,
    target_pagetable: RwLockPageTableRoot,
    target_thread: RwLockThreadPtr,
    source_va: VAddr,
    target_va: VAddr,
) -> bool {
    &&& share_mapping_4k_leaf_structure_ready(
        kernel, source_pagetable, target_pagetable, source_va, target_va,
    )
    &&& share_mapping_4k_leaf_owner_compatible(
        kernel, source_pagetable, target_thread, source_va,
    )
}

pub open spec fn share_mapping_4k_range_structure_ready_from(
    kernel: &KernelK,
    source_pagetable: RwLockPageTableRoot,
    target_pagetable: RwLockPageTableRoot,
    source_range: &VaRange4K,
    target_range: &VaRange4K,
    first: int,
) -> bool {
    forall|i: int|
        #![trigger source_range.view().spec_index(i),
            target_range.view().spec_index(i)]
        first <= i < source_range.len
        ==> share_mapping_4k_leaf_structure_ready(
            kernel,
            source_pagetable,
            target_pagetable,
            source_range.view().spec_index(i),
            target_range.view().spec_index(i),
        )
}

pub open spec fn share_mapping_4k_range_owner_compatible(
    kernel: &KernelK,
    source_pagetable: RwLockPageTableRoot,
    target_thread: RwLockThreadPtr,
    source_range: &VaRange4K,
) -> bool {
    forall|i: int|
        #![trigger source_range.view().spec_index(i)]
        0 <= i < source_range.len
        ==> share_mapping_4k_leaf_owner_compatible(
            kernel,
            source_pagetable,
            target_thread,
            source_range.view().spec_index(i),
        )
}

pub open spec fn share_mapping_4k_range_owner_compatible_prefix(
    kernel: &KernelK,
    source_pagetable: RwLockPageTableRoot,
    target_thread: RwLockThreadPtr,
    source_range: &VaRange4K,
    upper: int,
) -> bool {
    forall|i: int|
        #![trigger source_range.view().spec_index(i)]
        0 <= i < upper
        ==> share_mapping_4k_leaf_owner_compatible(
            kernel,
            source_pagetable,
            target_thread,
            source_range.view().spec_index(i),
        )
}

pub open spec fn share_mapping_4k_target_map_after(
    source: Map<VAddr, MapEntry>,
    target: Map<VAddr, MapEntry>,
    source_range: &VaRange4K,
    target_range: &VaRange4K,
    upper: nat,
) -> Map<VAddr, MapEntry>
    decreases upper,
{
    if upper == 0 {
        target
    } else {
        share_mapping_4k_target_map_after(
            source,
            target,
            source_range,
            target_range,
            (upper - 1) as nat,
        ).insert(
            target_range.view().spec_index((upper - 1) as int),
            source.spec_index(
                source_range.view().spec_index((upper - 1) as int),
            ),
        )
    }
}

pub open spec fn share_mapping_4k_range_mapped_prefix(
    target: PageTable<PT_TYPE>,
    target_range: &VaRange4K,
    upper: int,
) -> bool {
    forall|i: int|
        #![trigger target.mapping_4k().dom().contains(
            target_range.view().spec_index(i))]
        0 <= i < upper
        ==> target.mapping_4k().dom().contains(
            target_range.view().spec_index(i),
        )
}

/// Every not-yet-shared target VA is still absent from the 4K mapping.
pub open spec fn share_mapping_4k_target_range_empty_from(
    pagetable: PageTable<PT_TYPE>,
    target_range: &VaRange4K,
    first: int,
) -> bool {
    forall|i: int|
        #![trigger pagetable.mapping_4k().dom().contains(
            target_range.view().spec_index(i),
        )]
        first <= i < target_range.len
        ==> !pagetable.mapping_4k().dom().contains(
            target_range.view().spec_index(i),
        )
}

pub open spec fn share_mapping_4k_reverse_mappings(
    kernel: &KernelK,
    target_pagetable: RwLockPageTableRoot,
    target_range: &VaRange4K,
) -> bool {
    forall|i: int|
        #![trigger kernel.pagetable_map.spec_index(target_pagetable)
            .view().mapping_4k().spec_index(
                target_range.view().spec_index(i),
            )]
        0 <= i < target_range.len
        ==> {
            let target_va = target_range.view().spec_index(i);
            let target_entry = kernel.pagetable_map
                .spec_index(target_pagetable).view().mapping_4k()
                .spec_index(target_va);
            let page_index = page_ptr2page_index(target_entry.addr);
            &&& kernel.pagetable_map.spec_index(target_pagetable).view()
                .mapping_4k().dom().contains(target_va)
            &&& page_ptr_valid(target_entry.addr)
            &&& index_valid(NUM_PAGES, page_index)
            &&& kernel.page_array.spec_index(page_index).view().view().state
                is Mapped4k
            &&& kernel.page_array.spec_index(page_index).view().view()
                .mappings().contains((target_pagetable, target_va))
        }
}

/// Checks a source 4K range without mutating kernel or page-table state.
pub fn share_mapping_4k_source_precheck(
    kernel: &KernelK,
    source_range: &VaRange4K,
    source_pagetable: RwLockPageTableRoot,
    Tracked(lctx): Tracked<&LocalContext>,
    Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>,
) -> (ret: bool)
    requires
        kernel.inv(),
        source_range.wf(),
        kernel.pagetable_map.dom().contains(source_pagetable),
        kernel.pagetable_map.spec_index(source_pagetable).view().wf(),
        kernel.pagetable_map.spec_index(source_pagetable).view().kernel_l4_end
            <= spec_va2index(source_range.start).0,
        kernel.pagetable_map.spec_index(source_pagetable).locked_by(lctx),
        source_pagetable_lock_perm.thread_id() == lctx.thread_id(),
        (source_pagetable_lock_perm.state() is ReadLock
            || source_pagetable_lock_perm.state() is WriteLock),
        source_pagetable_lock_perm.state() is ReadLock
            ==> kernel.pagetable_map.spec_index(source_pagetable)
                .read_lock_perm_match(source_pagetable_lock_perm),
        source_pagetable_lock_perm.state() is WriteLock
            ==> kernel.pagetable_map.spec_index(source_pagetable)
                .write_lock_perm_match(source_pagetable_lock_perm),
    ensures
        ret == share_mapping_4k_source_range_present(
            kernel, source_pagetable, source_range,
        ),
{
    proof {
        assert({
            &&& kernel.pagetable_map.perms_wf()
            &&& kernel.pagetable_map.spec_index(source_pagetable).is_init()
        }) by {
            reveal(pagetable_perms_wf);
        };
    }
    let pagetable = kernel.pagetable_map.borrow(
        source_pagetable,
        Tracked(source_pagetable_lock_perm),
    );
    let ret = pagetable.mapping_4k_va_range_present(source_range);
    proof {
        assert(ret == share_mapping_4k_source_range_present(
            kernel, source_pagetable, source_range,
        )) by {
            if ret {
                reveal(mapped_4k_page_pagetable_wf);
            }
        };
    }
    ret
}

#[verifier::spinoff_prover]
fn share_one_mapping_4k(
    kernel: &mut KernelK,
    source_thread: RwLockThreadPtr,
    target_thread: RwLockThreadPtr,
    target_process: RwLockProcessPtr,
    target_container: RwLockContainerPtr,
    source_pagetable: RwLockPageTableRoot,
    target_pagetable: RwLockPageTableRoot,
    cpu_id: CpuId,
    source_va: VAddr,
    target_va: VAddr,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>,
    Tracked(source_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(target_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>,
    Tracked(target_pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        share_mapping_4k_held_context(
            old(kernel), old(lctx), source_thread, target_thread,
            source_pagetable, target_pagetable, source_thread_lock_perm,
            target_thread_lock_perm, source_pagetable_lock_perm,
            target_pagetable_lock_perm,
        ),
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
        index_valid(NUM_CPUS, cpu_id),
        old(kernel).cpu_array.spec_index(cpu_id).view().wlocked_by(old(lctx)),
        old(lctx).lock_entry_contains(
            old(kernel).cpu_array.lock_id_by_index(cpu_id),
            KernelObjId::Cpu(cpu_id),
        ),
        old(kernel).thread_map.spec_index(target_thread).view().owning_proc
            == target_process,
        old(kernel).thread_map.spec_index(target_thread).view().owning_container
            == target_container,
        old(kernel).process_map.dom().contains(target_process),
        old(kernel).container_map.dom().contains(target_container),
        mmap_4k_allocation_ready(old(kernel), old(lctx)),
        thread_objects_unlocked_except(
            old(kernel).thread_map, old(lctx).thread_id(),
            set![source_thread, target_thread],
        ),
        pagetable_objects_unlocked_except(
            old(kernel).pagetable_map, old(lctx).thread_id(),
            set![source_pagetable, target_pagetable],
        ),
        share_mapping_4k_leaf_ready(
            old(kernel), source_pagetable, target_pagetable,
            target_thread,
            source_va, target_va,
        ),
    ensures
        share_mapping_4k_held_context(
            final(kernel), final(lctx), source_thread, target_thread,
            source_pagetable, target_pagetable, source_thread_lock_perm,
            target_thread_lock_perm, source_pagetable_lock_perm,
            target_pagetable_lock_perm,
        ),
        final(steps).steps.len() == old(steps).steps.len() + 1,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(kernel).cpu_array.spec_index(cpu_id).view()
            == old(kernel).cpu_array.spec_index(cpu_id).view(),
        final(lctx).lock_entry_contains(
            final(kernel).cpu_array.lock_id_by_index(cpu_id),
            KernelObjId::Cpu(cpu_id),
        ),
        mmap_4k_allocation_ready(final(kernel), final(lctx)),
        held_containers_unchanged(
            old(kernel).container_map, final(kernel).container_map, old(lctx),
        ),
        held_processes_unchanged(
            old(kernel).process_map, final(kernel).process_map, old(lctx),
        ),
        held_endpoints_unchanged(
            old(kernel).endpoint_map, final(kernel).endpoint_map, old(lctx),
        ),
        held_schedulers_unchanged(
            old(kernel).scheduler_map, final(kernel).scheduler_map, old(lctx),
        ),
        held_pcid_allocators_unchanged(
            old(kernel).pcid_allocator_map, final(kernel).pcid_allocator_map,
            old(lctx),
        ),
        held_iommu_tables_unchanged(
            old(kernel).iommu_table_map, final(kernel).iommu_table_map,
            old(lctx),
        ),
        held_cpus_unchanged(
            old(kernel).cpu_array, final(kernel).cpu_array, old(lctx),
        ),
        thread_objects_unlocked_except(
            final(kernel).thread_map, final(lctx).thread_id(),
            set![source_thread, target_thread],
        ),
        pagetable_objects_unlocked_except(
            final(kernel).pagetable_map, final(lctx).thread_id(),
            set![source_pagetable, target_pagetable],
        ),
        allocator_objects_unlocked(
            old(kernel).allocator_2m_map, old(lctx).thread_id(),
        ) ==> allocator_objects_unlocked(
            final(kernel).allocator_2m_map, final(lctx).thread_id(),
        ),
        allocator_objects_unlocked(
            old(kernel).allocator_1g_map, old(lctx).thread_id(),
        ) ==> allocator_objects_unlocked(
            final(kernel).allocator_1g_map, final(lctx).thread_id(),
        ),
        final(kernel).thread_map.spec_index(target_thread).view()
            == old(kernel).thread_map.spec_index(target_thread).view(),
        final(kernel).thread_map.spec_index(source_thread).view()
            == old(kernel).thread_map.spec_index(source_thread).view(),
        final(kernel).container_map.dom().contains(target_container),
        final(kernel).container_map.spec_index(target_container).view_rodata()
            == old(kernel).container_map.spec_index(target_container).view_rodata(),
        final(kernel).process_map.dom().contains(target_process),
        final(kernel).process_map.spec_index(target_process).view_rodata()
            == old(kernel).process_map.spec_index(target_process).view_rodata(),
        final(kernel).pagetable_map.spec_index(source_pagetable).view()
            == old(kernel).pagetable_map.spec_index(source_pagetable).view(),
        final(kernel).pagetable_map.spec_index(target_pagetable).view().mapping_4k()
            == old(kernel).pagetable_map.spec_index(target_pagetable).view()
                .mapping_4k().insert(
                    target_va,
                    old(kernel).pagetable_map.spec_index(source_pagetable).view()
                        .mapping_4k().spec_index(source_va),
                ),
        final(kernel).pagetable_map.spec_index(target_pagetable).view().mapping_2m()
            == old(kernel).pagetable_map.spec_index(target_pagetable).view().mapping_2m(),
        final(kernel).pagetable_map.spec_index(target_pagetable).view().mapping_1g()
            == old(kernel).pagetable_map.spec_index(target_pagetable).view().mapping_1g(),
        final(kernel).pagetable_map.spec_index(target_pagetable).view().kernel_l4_end
            == old(kernel).pagetable_map.spec_index(target_pagetable).view().kernel_l4_end,
        final(kernel).pagetable_map.spec_index(target_pagetable).view().page_closure()
            == old(kernel).pagetable_map.spec_index(target_pagetable).view().page_closure(),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger final(kernel).pagetable_map.spec_index(target_pagetable)
                .view().spec_resolve_mapping_l2(l4i, l3i, l2i)]
            final(kernel).pagetable_map.spec_index(target_pagetable).view()
                .kernel_l4_end <= l4i && pei_valid(l4i)
                && pei_valid(l3i) && pei_valid(l2i)
            ==> final(kernel).pagetable_map.spec_index(target_pagetable).view()
                    .spec_resolve_mapping_l2(l4i, l3i, l2i)
                == old(kernel).pagetable_map.spec_index(target_pagetable).view()
                    .spec_resolve_mapping_l2(l4i, l3i, l2i),
        {
            let page_ptr = old(kernel).pagetable_map
                .spec_index(source_pagetable).view().mapping_4k()
                .spec_index(source_va).addr;
            final(kernel).page_array.spec_index(page_ptr2page_index(page_ptr))
                .view().view().mappings().contains((target_pagetable, target_va))
        },
{
    let source_indices = va2index(source_va);
    proof {
        assert({
            &&& kernel.pagetable_map.perms_wf()
            &&& kernel.pagetable_map.spec_index(source_pagetable).inv()
            &&& kernel.pagetable_map.spec_index(target_pagetable).inv()
        }) by { reveal(pagetable_perms_wf); };
    }
    let target_indices = va2index(target_va);
    proof {
        assert({
            &&& spec_index2va(source_indices) == source_va
            &&& kernel.pagetable_map.spec_index(source_pagetable).view()
                .spec_resolve_mapping_4k_l1(
                    source_indices.0, source_indices.1,
                    source_indices.2, source_indices.3,
                ) is Some
        }) by {
            spec_va_4k_index_roundtrip();
            reveal(PageTable::wf_mapping_4k);
        };
    }
    let source_entry;
    {
        let source = kernel.pagetable_map.borrow(
            source_pagetable, Tracked(source_pagetable_lock_perm),
        );
        source_entry = source.resolve_mapping_4k_l1(
            source_indices.0,
            source_indices.1,
            source_indices.2,
            source_indices.3,
        ).2.unwrap();
    }
    let page_ptr = source_entry.addr;
    proof {
        assert({
            &&& source_entry =~= kernel.pagetable_map
                .spec_index(source_pagetable).view().mapping_4k()
                .spec_index(source_va)
            &&& page_ptr_valid(page_ptr)
        }) by {
            reveal(PageTable::wf_mapping_4k);
        };
    }
    let page_index = page_ptr2page_index(page_ptr);
    let target_l1_ptr;
    {
        let target = kernel.pagetable_map.borrow(
            target_pagetable, Tracked(target_pagetable_lock_perm),
        );
        let l4_entry = target.get_entry_l4(target_indices.0).unwrap();
        let l3_entry = target.get_entry_l3(
            target_indices.0, target_indices.1, &l4_entry,
        ).unwrap();
        let l2_entry = target.get_entry_l2(
            target_indices.0,
            target_indices.1,
            target_indices.2,
            &l3_entry,
        ).unwrap();
        target_l1_ptr = l2_entry.addr;
    }

    proof {
        assert(index_valid(NUM_PAGES, page_index)) by {
            page_ptr_valid_imply_page_index_valid();
        };
        assert(kernel.page_array.spec_index(page_index).view().view().state
            is Mapped4k) by {
            reveal(mapped_4k_page_pagetable_wf);
        };
        assert(!kernel.page_array.spec_index(page_index).view()
            .locked_by_thread(lctx.thread_id())) by {
            reveal(page_objects_unlocked);
        };
        assert(kernel.page_array.lock_id_by_index(page_index).major
            == MAPPED_PAGE_LOCK_MAJOR) by {
            reveal(page_array_wf);
        };
        assert(lctx.lock_id_acyclic(
            kernel.page_array.lock_id_by_index(page_index))) by {
            reveal(page_array_wf);
        };
    }
    let Tracked(page_lock_perm) = kernel.wlock_page(
        page_index, Tracked(&mut *lctx),
    );

    proof {
        assert({
            &&& kernel.page_array.inv()
            &&& kernel.page_array.spec_index(page_index).view().inv()
        }) by {
            reveal(page_array_wf);
        };
        assert(!kernel.page_array.spec_index(page_index).view().view()
            .mappings().contains((target_pagetable, target_va))) by {
            reveal(mapped_4k_page_pagetable_wf);
        };
        assert(kernel.page_array.spec_index(page_index).view().view().ref_count
            < usize::MAX) by {
            mapped_4k_page_ref_count_lt_usize_max(
                kernel.pagetable_map, kernel.page_array, page_index,
            );
        };
    }
    {
        let page = kernel.page_array.borrow_mut(
            page_index,
            Tracked(&*lctx),
            Tracked(&page_lock_perm),
        );
        add_4k_mapping(page, target_pagetable, target_va);
    }
    proof {
        assert(spec_index2va(target_indices) == target_va) by {
            spec_va_4k_index_roundtrip();
        };
    }
    let target = kernel.pagetable_map.borrow_mut(
        target_pagetable,
        Tracked(&mut *lctx),
        Tracked(target_pagetable_lock_perm),
    );
    target.map_4k_page(
        target_indices.0,
        target_indices.1,
        target_indices.2,
        target_indices.3,
        target_l1_ptr,
        &source_entry,
        Tracked(&mut *lctx),
    );

    proof {
        assert(kernel.subsystems_inv()) by {
            assert(kernel.default_pagetable_wf()) by {
                reveal(KernelK::default_pagetable_wf);
            };
            assert(pagetable_perms_wf(kernel.pagetable_map)) by {
                reveal(pagetable_perms_wf);
            };
            assert(page_array_wf(kernel.page_array)) by {
                reveal(page_array_wf);
            };
        };
        assert(kernel.memory_management_inv()) by {
            assert(allocator_pages_wf(
                kernel.page_array, kernel.allocator_4k_map,
                kernel.allocator_2m_map, kernel.allocator_1g_map,
            )) by {
                allocator_4k_pages_wf_preserved_for_page_state_eq(
                    old(kernel).page_array, kernel.page_array,
                    old(kernel).allocator_4k_map, kernel.allocator_4k_map,
                );
                allocator_2m_pages_wf_preserved_for_page_state_eq(
                    old(kernel).page_array, kernel.page_array,
                    old(kernel).allocator_2m_map, kernel.allocator_2m_map,
                );
                allocator_1g_pages_wf_preserved_for_page_state_eq(
                    old(kernel).page_array, kernel.page_array,
                    old(kernel).allocator_1g_map, kernel.allocator_1g_map,
                );
            };
            assert(container_page_owner_wf(
                kernel.container_map, kernel.page_array,
            )) by {
                container_page_owner_wf_preserved_for_owning_container_eq(
                    old(kernel).container_map, kernel.container_map,
                    old(kernel).page_array, kernel.page_array,
                );
            };
            assert(hugepage_2m_wf(kernel.page_array)) by {
                hugepage_2m_wf_preserved_for_page_state_eq(
                    old(kernel).page_array, kernel.page_array,
                );
            };
            assert(hugepage_1g_wf(kernel.page_array)) by {
                hugepage_1g_wf_preserved_for_page_state_eq(
                    old(kernel).page_array, kernel.page_array,
                );
            };
            assert(page_pagetable_wf(
                kernel.pagetable_map, kernel.page_array,
            )) by {
                assert({
                    let target_entry = kernel.pagetable_map
                        .spec_index(target_pagetable).view().mapping_4k()
                        .spec_index(target_va);
                    target_entry.owning_container@
                        == kernel.page_array.spec_index(page_index)
                            .view().view().owning_container
                }) by {
                    reveal(mapped_4k_page_pagetable_wf);
                };
                page_pagetable_wf_preserved_for_4k_mapping_insert(
                    old(kernel).pagetable_map, kernel.pagetable_map,
                    old(kernel).page_array, kernel.page_array,
                    target_pagetable, page_ptr, target_va,
                );
            };
            assert(container_process_page_pagetable_wf(
                kernel.container_map, kernel.process_map,
                kernel.pagetable_map, kernel.page_array,
            )) by {
                assert({
                    let owner = kernel.page_array.spec_index(page_index)
                        .view().view().owning_container;
                    let mapping_process = kernel.pagetable_map
                        .spec_index(target_pagetable).view().proc_ptr;
                    let mapping_container = kernel.process_map
                        .spec_index(mapping_process).view_rodata().view()
                        .owning_container;
                    &&& kernel.process_map.dom().contains(mapping_process)
                    &&& kernel.container_map.dom().contains(owner)
                    &&& (mapping_container == owner
                        || kernel.container_map.spec_index(owner).view()
                            .subtree_set.view().contains(mapping_container))
                }) by {
                    reveal(mapped_4k_page_pagetable_wf);
                    reveal(container_page_owner_wf);
                    reveal(container_thread_wf);
                    reveal(container_uppertree_seq_wf);
                    reveal(process_thread_wf);
                    reveal(process_pagetable_match);
                };
                container_process_page_pagetable_wf_preserved_for_4k_mapping_insert(
                    kernel.container_map, kernel.process_map,
                    old(kernel).pagetable_map, kernel.pagetable_map,
                    old(kernel).page_array, kernel.page_array,
                    target_pagetable, page_ptr, target_va,
                );
            };
            assert(container_pages_wf(
                kernel.page_array, kernel.container_map,
            )) by {
                container_pages_wf_preserved_for_page_state_eq(
                    old(kernel).page_array, kernel.page_array,
                    old(kernel).container_map, kernel.container_map,
                );
            };
            assert(process_pages_wf(
                kernel.page_array, kernel.process_map,
            )) by {
                process_pages_wf_preserved_for_page_state_eq(
                    old(kernel).page_array, kernel.page_array,
                    old(kernel).process_map, kernel.process_map,
                );
            };
            assert(pagetable_pages_wf(
                kernel.pagetable_map, kernel.page_array,
            )) by {
                assert({
                    &&& kernel.pagetable_map.unchanged_except(
                        &old(kernel).pagetable_map, target_pagetable,
                    )
                    &&& kernel.pagetable_map.spec_index(target_pagetable)
                        .view().page_closure()
                        == old(kernel).pagetable_map
                            .spec_index(target_pagetable).view().page_closure()
                }) by {
                    reveal(pagetable_pages_wf);
                };
                reveal(pagetable_pages_wf);
            };
            assert(iommu_table_pages_wf(
                kernel.iommu_table_map, kernel.page_array,
            )) by {
                reveal(iommu_table_pages_wf);
            };
            assert(thread_pages_wf(
                kernel.thread_map, kernel.page_array,
            )) by {
                thread_pages_wf_preserved_for_page_state_eq(
                    old(kernel).thread_map, kernel.thread_map,
                    old(kernel).page_array, kernel.page_array,
                );
            };
            assert(pcid_allocator_pages_wf(
                kernel.page_array, kernel.pcid_allocator_map,
            )) by {
                pcid_allocator_pages_wf_preserved_for_page_state_eq(
                    old(kernel).page_array, kernel.page_array,
                    old(kernel).pcid_allocator_map, kernel.pcid_allocator_map,
                );
            };
            assert(thread_staged_pages_wf(
                kernel.thread_map, kernel.page_array,
            )) by {
                reveal(thread_staged_pages_4k_wf);
                thread_staged_pages_2m_wf_preserved_for_eq(
                    old(kernel).thread_map, kernel.thread_map,
                    old(kernel).page_array, kernel.page_array,
                );
                thread_staged_pages_1g_wf_preserved_for_eq(
                    old(kernel).thread_map, kernel.thread_map,
                    old(kernel).page_array, kernel.page_array,
                );
            };
            assert(endpoint_pages_wf(
                kernel.endpoint_map, kernel.page_array,
            )) by {
                endpoint_pages_wf_preserved_for_page_state_eq(
                    old(kernel).endpoint_map, kernel.endpoint_map,
                    old(kernel).page_array, kernel.page_array,
                );
            };
            assert(process_pagetable_match(
                kernel.process_map, kernel.pagetable_map,
            )) by {
                assert({
                    &&& kernel.process_map == old(kernel).process_map
                    &&& kernel.pagetable_map.unchanged_except(
                        &old(kernel).pagetable_map, target_pagetable,
                    )
                    &&& kernel.pagetable_map.spec_index(target_pagetable)
                        .view().proc_ptr
                        == old(kernel).pagetable_map
                            .spec_index(target_pagetable).view().proc_ptr
                    &&& kernel.pagetable_map.spec_index(target_pagetable)
                        .view().pcid
                        == old(kernel).pagetable_map
                            .spec_index(target_pagetable).view().pcid
                }) by {
                    reveal(process_pagetable_match);
                };
                reveal(process_pagetable_match);
            };
            assert(container_allocator_free_4k_page_wf(
                kernel.allocator_4k_map, kernel.page_array,
            )) by {
                container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(
                    kernel.allocator_4k_map, old(kernel).page_array,
                    kernel.page_array, page_index,
                );
            };
            assert(container_allocator_free_2m_page_wf(
                kernel.allocator_2m_map, kernel.page_array,
            )) by {
                container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(
                    kernel.allocator_2m_map, old(kernel).page_array,
                    kernel.page_array, page_index,
                );
            };
            assert(container_allocator_free_1g_page_wf(
                kernel.allocator_1g_map, kernel.page_array,
            )) by {
                container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(
                    kernel.allocator_1g_map, old(kernel).page_array,
                    kernel.page_array, page_index,
                );
            };
        };
        assert(kernel.process_management_inv()) by {
            reveal(thread_caller_callee_wf);
            reveal(thread_endpoint_ref_counter_wf);
            reveal(thread_endpoint_queue_wf);
            reveal(container_thread_endpoint_wf);
            reveal(container_thread_scheduler_wf);
            reveal(container_thread_wf);
            reveal(process_thread_wf);
            reveal(thread_cpu_wf);
        };
        assert(cpu_dirty_map_wf(
            kernel.container_map, kernel.process_map, kernel.cpu_array,
            kernel.cpu_tlb, kernel.pagetable_map,
        )) by {
            reveal(cpu_dirty_map_contains_pagetable_pcid_match);
        };
        assert(tlb_wf_spec(
            kernel.cpu_tlb, kernel.pagetable_map, kernel.cpu_array,
        )) by {
            tlb_wf_spec_preserved_for_4k_mapping_insert(
                kernel.cpu_tlb, kernel.cpu_array,
                old(kernel).pagetable_map, kernel.pagetable_map,
                target_pagetable, target_va,
            );
        };
        assert(typed_lock_maps_aligned(kernel, &*lctx)) by {
            reveal(typed_lock_maps_aligned);
        };
        assert(kernel_k_to_kernel_u(*kernel)
            != kernel_k_to_kernel_u(*old(kernel))) by {
            assert({
                let process_ptr = kernel.thread_map.spec_index(target_thread)
                    .view().owning_proc;
                &&& kernel_k_to_kernel_u(*old(kernel)).process_map.dom()
                    .contains(process_ptr)
                &&& kernel_k_to_kernel_u(*kernel).process_map.dom()
                    .contains(process_ptr)
                &&& !kernel_k_to_kernel_u(*old(kernel)).process_map
                    .spec_index(process_ptr).pagetable.mapping_4k.dom()
                    .contains(target_va)
                &&& kernel_k_to_kernel_u(*kernel).process_map
                    .spec_index(process_ptr).pagetable.mapping_4k.dom()
                    .contains(target_va)
            }) by {
                reveal(process_thread_wf);
                reveal(process_pagetable_match);
            };
        };
        assert(page_objects_unlocked_except(
            kernel.page_array, lctx.thread_id(), set![page_index],
        )) by {
            reveal(page_objects_unlocked_except);
        };
    }
    kernel.wunlock_page(
        page_index,
        Tracked(&mut *lctx),
        Tracked(page_lock_perm),
    );
    proof {
        assert(lctx.lock_entry_contains(
            kernel.thread_map.lock_id_by_key(source_thread),
            KernelObjId::Thread(source_thread),
        )) by {
            lock_id_fields_eq_imply_eq();
        };
        assert(lctx.lock_entry_contains(
            kernel.thread_map.lock_id_by_key(target_thread),
            KernelObjId::Thread(target_thread),
        )) by {
            lock_id_fields_eq_imply_eq();
        };
        assert(lctx.lock_entry_contains(
            kernel.pagetable_map.lock_id_by_key(source_pagetable),
            KernelObjId::PageTable(source_pagetable),
        )) by {
            lock_id_fields_eq_imply_eq();
        };
        assert(lctx.lock_entry_contains(
            kernel.pagetable_map.lock_id_by_key(target_pagetable),
            KernelObjId::PageTable(target_pagetable),
        )) by {
            lock_id_fields_eq_imply_eq();
        };
        assert(thread_objects_unlocked_except(
            kernel.thread_map, lctx.thread_id(),
            set![source_thread, target_thread],
        )) by {
            reveal(thread_objects_unlocked_except);
        };
        assert(kernel.pagetable_map.unchanged_except(
            &old(kernel).pagetable_map, target_pagetable,
        )) by {
            reveal(pagetable_perms_wf);
        };
        assert(pagetable_objects_unlocked_except(
            kernel.pagetable_map, lctx.thread_id(),
            set![source_pagetable, target_pagetable],
        )) by {
            reveal(pagetable_objects_unlocked_except);
        };
        kernel.kernel_step_boundary(&mut *lctx, &mut *steps);
        assert(share_mapping_4k_held_context(
            kernel, &*lctx, source_thread, target_thread,
            source_pagetable, target_pagetable, source_thread_lock_perm,
            target_thread_lock_perm, source_pagetable_lock_perm,
            target_pagetable_lock_perm,
        )) by {
            lock_id_fields_eq_imply_eq();
        };
        assert({
            &&& kernel.container_map.dom().contains(target_container)
            &&& kernel.container_map.spec_index(target_container).view_rodata()
                == old(kernel).container_map.spec_index(target_container)
                    .view_rodata()
            &&& kernel.process_map.dom().contains(target_process)
            &&& kernel.process_map.spec_index(target_process).view_rodata()
                == old(kernel).process_map.spec_index(target_process)
                    .view_rodata()
        }) by {
            reveal(container_thread_wf);
            reveal(process_thread_wf);
        };
        assert({
            let mapped_page = kernel.pagetable_map
                .spec_index(target_pagetable).view().mapping_4k()
                .spec_index(target_va).addr;
            kernel.page_array.spec_index(page_ptr2page_index(mapped_page))
                .view().view().mappings().contains(
                    (target_pagetable, target_va),
                )
        }) by {
            reveal(mapped_4k_page_pagetable_wf);
        };
        assert(mmap_4k_allocation_ready(kernel, &*lctx)) by {
            reveal(mmap_4k_allocation_ready);
            reveal(mmap_4k_no_page_locks);
            reveal(allocator_objects_unlocked);
        };
        assert(thread_objects_unlocked_except(
            kernel.thread_map, lctx.thread_id(),
            set![source_thread, target_thread],
        )) by {
            reveal(thread_objects_unlocked_except);
            reveal(held_threads_unchanged);
        };
        assert(pagetable_objects_unlocked_except(
            kernel.pagetable_map, lctx.thread_id(),
            set![source_pagetable, target_pagetable],
        )) by {
            reveal(pagetable_objects_unlocked_except);
            reveal(held_pagetables_unchanged);
        };
    }
}


/// Read-only owner precheck for every present source 4K mapping.
///
/// The source page table and target thread are stable roots. Each physical
/// page is write-locked only long enough to read its runtime owner. Locking is
/// an internal stuttering step: mappings, page payloads, and user-visible state
/// are unchanged.
#[verifier::spinoff_prover]
pub fn share_mapping_4k_source_owner_precheck(
    kernel: &mut KernelK,
    source_range: &VaRange4K,
    source_thread: RwLockThreadPtr,
    target_thread: RwLockThreadPtr,
    source_pagetable: RwLockPageTableRoot,
    target_pagetable: RwLockPageTableRoot,
    cpu_id: CpuId,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>,
    Tracked(source_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(target_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>,
    Tracked(target_pagetable_lock_perm): Tracked<&LockPerm>,
) -> (ret: bool)
    requires
        share_mapping_4k_held_context(
            old(kernel), old(lctx), source_thread, target_thread,
            source_pagetable, target_pagetable, source_thread_lock_perm,
            target_thread_lock_perm, source_pagetable_lock_perm,
            target_pagetable_lock_perm,
        ),
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
        index_valid(NUM_CPUS, cpu_id),
        old(kernel).cpu_array.spec_index(cpu_id).view().wlocked_by(old(lctx)),
        old(lctx).lock_entry_contains(
            old(kernel).cpu_array.lock_id_by_index(cpu_id),
            KernelObjId::Cpu(cpu_id),
        ),
        source_range.wf(),
        old(kernel).pagetable_map.spec_index(source_pagetable).view().wf(),
        old(kernel).pagetable_map.spec_index(source_pagetable).view()
            .kernel_l4_end
            <= spec_va2index(source_range.start).0,
        share_mapping_4k_source_range_present(
            old(kernel), source_pagetable, source_range,
        ),
        thread_objects_unlocked_except(
            old(kernel).thread_map, old(lctx).thread_id(),
            set![source_thread, target_thread],
        ),
        pagetable_objects_unlocked_except(
            old(kernel).pagetable_map, old(lctx).thread_id(),
            set![source_pagetable, target_pagetable],
        ),
    ensures
        share_mapping_4k_held_context(
            final(kernel), final(lctx), source_thread, target_thread,
            source_pagetable, target_pagetable, source_thread_lock_perm,
            target_thread_lock_perm, source_pagetable_lock_perm,
            target_pagetable_lock_perm,
        ),
        final(steps).steps.len() == old(steps).steps.len(),
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        held_containers_unchanged(
            old(kernel).container_map, final(kernel).container_map, old(lctx),
        ),
        held_processes_unchanged(
            old(kernel).process_map, final(kernel).process_map, old(lctx),
        ),
        held_endpoints_unchanged(
            old(kernel).endpoint_map, final(kernel).endpoint_map, old(lctx),
        ),
        held_schedulers_unchanged(
            old(kernel).scheduler_map, final(kernel).scheduler_map, old(lctx),
        ),
        held_pcid_allocators_unchanged(
            old(kernel).pcid_allocator_map, final(kernel).pcid_allocator_map,
            old(lctx),
        ),
        held_iommu_tables_unchanged(
            old(kernel).iommu_table_map, final(kernel).iommu_table_map, old(lctx),
        ),
        held_cpus_unchanged(
            old(kernel).cpu_array, final(kernel).cpu_array, old(lctx),
        ),
        allocator_objects_unlocked(
            old(kernel).allocator_2m_map, old(lctx).thread_id(),
        ) ==> allocator_objects_unlocked(
            final(kernel).allocator_2m_map, final(lctx).thread_id(),
        ),
        allocator_objects_unlocked(
            old(kernel).allocator_1g_map, old(lctx).thread_id(),
        ) ==> allocator_objects_unlocked(
            final(kernel).allocator_1g_map, final(lctx).thread_id(),
        ),
        thread_objects_unlocked_except(
            final(kernel).thread_map, final(lctx).thread_id(),
            set![source_thread, target_thread],
        ),
        pagetable_objects_unlocked_except(
            final(kernel).pagetable_map, final(lctx).thread_id(),
            set![source_pagetable, target_pagetable],
        ),
        final(kernel).cpu_array.spec_index(cpu_id).view()
            == old(kernel).cpu_array.spec_index(cpu_id).view(),
        final(kernel).cpu_array.spec_index(cpu_id).view().wlocked_by(final(lctx)),
        final(kernel).cpu_array.lock_id_by_index(cpu_id)
            == old(kernel).cpu_array.lock_id_by_index(cpu_id),
        final(lctx).lock_entry_contains(
            final(kernel).cpu_array.lock_id_by_index(cpu_id),
            KernelObjId::Cpu(cpu_id),
        ),
        final(kernel).pagetable_map.spec_index(source_pagetable).view()
            == old(kernel).pagetable_map.spec_index(source_pagetable).view(),
        final(kernel).pagetable_map.spec_index(target_pagetable).view()
            == old(kernel).pagetable_map.spec_index(target_pagetable).view(),
        final(kernel).thread_map.spec_index(source_thread).view()
            == old(kernel).thread_map.spec_index(source_thread).view(),
        final(kernel).thread_map.spec_index(target_thread).view()
            == old(kernel).thread_map.spec_index(target_thread).view(),
        mmap_4k_allocation_ready(old(kernel), old(lctx)) ==>
            mmap_4k_allocation_ready(final(kernel), final(lctx)),
        share_mapping_4k_source_range_present(
            final(kernel), source_pagetable, source_range,
        ),
        ret == share_mapping_4k_range_owner_compatible(
            final(kernel), source_pagetable, target_thread, source_range,
        ),
{
    proof {
        assert({
            &&& kernel.thread_map.perms_wf()
            &&& kernel.thread_map.spec_index(target_thread).inv()
        }) by {
            reveal(thread_perms_wf);
        };
    }
    let target_container;
    {
        let thread = kernel.thread_map.borrow(
            target_thread, Tracked(target_thread_lock_perm),
        );
        target_container = thread.owning_container;
    }

    let mut i: usize = 0;
    let mut all_compatible = true;
    while i < source_range.len
        invariant
            share_mapping_4k_held_context(
                kernel, &*lctx, source_thread, target_thread,
                source_pagetable, target_pagetable,
                source_thread_lock_perm, target_thread_lock_perm,
                source_pagetable_lock_perm, target_pagetable_lock_perm,
            ),
            steps.snap_shot == kernel_k_to_kernel_u(*kernel),
            thread_objects_unlocked_except(
                kernel.thread_map, lctx.thread_id(),
                set![source_thread, target_thread],
            ),
            pagetable_objects_unlocked_except(
                kernel.pagetable_map, lctx.thread_id(),
                set![source_pagetable, target_pagetable],
            ),
            index_valid(NUM_CPUS, cpu_id),
            kernel.cpu_array.spec_index(cpu_id).view()
                == old(kernel).cpu_array.spec_index(cpu_id).view(),
            kernel.cpu_array.spec_index(cpu_id).view().wlocked_by(&*lctx),
            kernel.cpu_array.spec_index(cpu_id).view()
                .locked_by_thread(lctx.thread_id()),
            kernel.cpu_array.lock_id_by_index(cpu_id)
                == old(kernel).cpu_array.lock_id_by_index(cpu_id),
            lctx.lock_entry_contains(
                kernel.cpu_array.lock_id_by_index(cpu_id),
                KernelObjId::Cpu(cpu_id),
            ),
            source_range.wf(),
            kernel.pagetable_map.spec_index(source_pagetable).view().wf(),
            kernel.pagetable_map.spec_index(source_pagetable).view()
                .kernel_l4_end
                <= spec_va2index(source_range.start).0,
            share_mapping_4k_source_range_present(
                kernel, source_pagetable, source_range,
            ),
            0 <= i <= source_range.len,
            all_compatible
                == share_mapping_4k_range_owner_compatible_prefix(
                    kernel, source_pagetable, target_thread,
                    source_range, i as int,
                ),
            steps.steps.len() == old(steps).steps.len(),
            lctx.thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), lctx),
            held_containers_unchanged(
                old(kernel).container_map, kernel.container_map, old(lctx),
            ),
            held_processes_unchanged(
                old(kernel).process_map, kernel.process_map, old(lctx),
            ),
            held_endpoints_unchanged(
                old(kernel).endpoint_map, kernel.endpoint_map, old(lctx),
            ),
            held_schedulers_unchanged(
                old(kernel).scheduler_map, kernel.scheduler_map, old(lctx),
            ),
            held_pcid_allocators_unchanged(
                old(kernel).pcid_allocator_map, kernel.pcid_allocator_map,
                old(lctx),
            ),
            held_iommu_tables_unchanged(
                old(kernel).iommu_table_map, kernel.iommu_table_map, old(lctx),
            ),
            held_cpus_unchanged(
                old(kernel).cpu_array, kernel.cpu_array, old(lctx),
            ),
            allocator_objects_unlocked(
                old(kernel).allocator_2m_map, old(lctx).thread_id(),
            ) ==> allocator_objects_unlocked(
                kernel.allocator_2m_map, lctx.thread_id(),
            ),
            allocator_objects_unlocked(
                old(kernel).allocator_1g_map, old(lctx).thread_id(),
            ) ==> allocator_objects_unlocked(
                kernel.allocator_1g_map, lctx.thread_id(),
            ),
            old(kernel).pagetable_map.dom().contains(source_pagetable),
            old(kernel).thread_map.dom().contains(target_thread),
            kernel.pagetable_map.spec_index(source_pagetable).view()
                == old(kernel).pagetable_map
                    .spec_index(source_pagetable).view(),
            kernel.pagetable_map.spec_index(target_pagetable).view()
                == old(kernel).pagetable_map
                    .spec_index(target_pagetable).view(),
            kernel.thread_map.spec_index(target_thread).view()
                == old(kernel).thread_map.spec_index(target_thread).view(),
            kernel.thread_map.spec_index(source_thread).view()
                == old(kernel).thread_map.spec_index(source_thread).view(),
            mmap_4k_allocation_ready(old(kernel), old(lctx)) ==>
                mmap_4k_allocation_ready(kernel, &*lctx),
            target_container
                == kernel.thread_map.spec_index(target_thread).view()
                    .owning_container,
        decreases source_range.len - i,
    {
        let source_va = source_range.index(i);
        let source_indices = va2index(source_va);
        proof {
            assert({
                &&& kernel.pagetable_map.perms_wf()
                &&& kernel.pagetable_map.spec_index(source_pagetable).inv()
            }) by {
                reveal(pagetable_perms_wf);
            };
            assert({
                &&& spec_index2va(source_indices) == source_va
                &&& kernel.pagetable_map.spec_index(source_pagetable).view()
                    .spec_resolve_mapping_4k_l1(
                        source_indices.0, source_indices.1,
                        source_indices.2, source_indices.3,
                    ) is Some
            }) by {
                spec_va_4k_index_roundtrip();
                reveal(PageTable::wf_mapping_4k);
                seq_index_lemma::<VAddr>();
                source_range.va_range_lemma();
            };
        }
        let source_entry;
        {
            let source = kernel.pagetable_map.borrow(
                source_pagetable, Tracked(source_pagetable_lock_perm),
            );
            source_entry = source.resolve_mapping_4k_l1(
                source_indices.0,
                source_indices.1,
                source_indices.2,
                source_indices.3,
            ).2.unwrap();
        }
        let page_ptr = source_entry.addr;
        let page_index = page_ptr2page_index(page_ptr);
        proof {
            assert({
                &&& source_entry =~= kernel.pagetable_map
                    .spec_index(source_pagetable).view().mapping_4k()
                    .spec_index(source_va)
                &&& page_ptr_valid(page_ptr)
            }) by {
                reveal(PageTable::wf_mapping_4k);
                seq_index_lemma::<VAddr>();
                source_range.va_range_lemma();
            };
            assert(index_valid(NUM_PAGES, page_index)) by {
                page_ptr_valid_imply_page_index_valid();
            };
            assert(!kernel.page_array.spec_index(page_index).view()
                .locked_by_thread(lctx.thread_id())) by {
                reveal(page_objects_unlocked);
            };
            assert(kernel.page_array.lock_id_by_index(page_index).major
                == MAPPED_PAGE_LOCK_MAJOR) by {
                reveal(page_array_wf);
            };
            assert(lctx.lock_id_acyclic(
                kernel.page_array.lock_id_by_index(page_index))) by {
                reveal(page_array_wf);
            };
        }
        let Tracked(page_lock_perm) = kernel.wlock_page(
            page_index, Tracked(&mut *lctx),
        );

        let page_owner;
        {
            proof {
                assert(kernel.page_array.inv()) by {
                    reveal(page_array_wf);
                };
            }
            let page = kernel.page_array.borrow(
                page_index, Tracked(&page_lock_perm),
            );
            page_owner = page.owning_container;
        }

        let page_compatible;
        if page_owner == target_container {
            page_compatible = true;
        } else {
            proof {
                assert({
                    &&& container_perms_wf(kernel.container_map)
                    &&& container_tree_wf(
                        kernel.root_container, kernel.container_map,
                    )
                    &&& kernel.container_map.dom().contains(page_owner)
                    &&& kernel.container_map.dom().contains(target_container)
                }) by {
                    reveal(container_page_owner_wf);
                    reveal(container_thread_wf);
                };
            }
            page_compatible = container_tree_check_is_ancestor(
                kernel.root_container,
                &kernel.container_map,
                page_owner,
                target_container,
            );
        }
        proof {
            assert(page_compatible
                == share_mapping_4k_leaf_owner_compatible(
                    kernel, source_pagetable, target_thread, source_va,
                )) by {
                reveal(mapped_4k_page_pagetable_wf);
                reveal(container_thread_wf);
            };
        }

        kernel.wunlock_page(
            page_index,
            Tracked(&mut *lctx),
            Tracked(page_lock_perm),
        );
        proof {
            assert(lctx.lock_entry_contains(
                kernel.thread_map.lock_id_by_key(source_thread),
                KernelObjId::Thread(source_thread),
            )) by {
                lock_id_fields_eq_imply_eq();
            };
            assert(lctx.lock_entry_contains(
                kernel.thread_map.lock_id_by_key(target_thread),
                KernelObjId::Thread(target_thread),
            )) by {
                lock_id_fields_eq_imply_eq();
            };
            assert(lctx.lock_entry_contains(
                kernel.pagetable_map.lock_id_by_key(source_pagetable),
                KernelObjId::PageTable(source_pagetable),
            )) by {
                lock_id_fields_eq_imply_eq();
            };
            assert(lctx.lock_entry_contains(
                kernel.pagetable_map.lock_id_by_key(target_pagetable),
                KernelObjId::PageTable(target_pagetable),
            )) by {
                lock_id_fields_eq_imply_eq();
            };
            assert(thread_objects_unlocked_except(
                kernel.thread_map, lctx.thread_id(),
                set![source_thread, target_thread],
            )) by {
                reveal(thread_objects_unlocked_except);
            };
            assert(pagetable_objects_unlocked_except(
                kernel.pagetable_map, lctx.thread_id(),
                set![source_pagetable, target_pagetable],
            )) by {
                reveal(pagetable_objects_unlocked_except);
            };
            kernel.kernel_step_boundary(&mut *lctx, &mut *steps);
            assert({
                &&& held_containers_unchanged(
                    old(kernel).container_map, kernel.container_map, old(lctx),
                )
                &&& held_processes_unchanged(
                    old(kernel).process_map, kernel.process_map, old(lctx),
                )
                &&& held_endpoints_unchanged(
                    old(kernel).endpoint_map, kernel.endpoint_map, old(lctx),
                )
                &&& held_schedulers_unchanged(
                    old(kernel).scheduler_map, kernel.scheduler_map, old(lctx),
                )
                &&& held_pcid_allocators_unchanged(
                    old(kernel).pcid_allocator_map,
                    kernel.pcid_allocator_map,
                    old(lctx),
                )
                &&& held_iommu_tables_unchanged(
                    old(kernel).iommu_table_map,
                    kernel.iommu_table_map,
                    old(lctx),
                )
                &&& held_cpus_unchanged(
                    old(kernel).cpu_array, kernel.cpu_array, old(lctx),
                )
                &&& (allocator_objects_unlocked(
                    old(kernel).allocator_2m_map, old(lctx).thread_id(),
                ) ==> allocator_objects_unlocked(
                    kernel.allocator_2m_map, lctx.thread_id(),
                ))
                &&& (allocator_objects_unlocked(
                    old(kernel).allocator_1g_map, old(lctx).thread_id(),
                ) ==> allocator_objects_unlocked(
                    kernel.allocator_1g_map, lctx.thread_id(),
                ))
            }) by {
                lock_id_fields_eq_imply_eq();
            };
            assert({
                &&& kernel.cpu_array.spec_index(cpu_id).view()
                    == old(kernel).cpu_array.spec_index(cpu_id).view()
                &&& kernel.cpu_array.spec_index(cpu_id).view()
                    .wlocked_by(&*lctx)
                &&& kernel.cpu_array.lock_id_by_index(cpu_id)
                    == old(kernel).cpu_array.lock_id_by_index(cpu_id)
                &&& lctx.lock_entry_contains(
                    kernel.cpu_array.lock_id_by_index(cpu_id),
                    KernelObjId::Cpu(cpu_id),
                )
            }) by {
                reveal(held_cpus_unchanged);
                lock_id_fields_eq_imply_eq();
            };
            assert(share_mapping_4k_held_context(
                kernel, &*lctx, source_thread, target_thread,
                source_pagetable, target_pagetable,
                source_thread_lock_perm, target_thread_lock_perm,
                source_pagetable_lock_perm, target_pagetable_lock_perm,
            )) by {
                lock_id_fields_eq_imply_eq();
            };
            assert(thread_objects_unlocked_except(
                kernel.thread_map, lctx.thread_id(),
                set![source_thread, target_thread],
            )) by {
                reveal(thread_objects_unlocked_except);
                reveal(held_threads_unchanged);
            };
            assert(pagetable_objects_unlocked_except(
                kernel.pagetable_map, lctx.thread_id(),
                set![source_pagetable, target_pagetable],
            )) by {
                reveal(pagetable_objects_unlocked_except);
                reveal(held_pagetables_unchanged);
            };
            assert(mmap_4k_allocation_ready(old(kernel), old(lctx)) ==>
                mmap_4k_allocation_ready(kernel, &*lctx)) by {
                reveal(mmap_4k_allocation_ready);
                reveal(mmap_4k_no_page_locks);
                reveal(page_objects_unlocked);
                reveal(allocator_objects_unlocked);
            };
            assert(share_mapping_4k_source_range_present(
                kernel, source_pagetable, source_range,
            )) by {
                reveal(pagetable_perms_wf);
                reveal(mapped_4k_page_pagetable_wf);
                page_ptr_valid_imply_page_index_valid();
            };
            assert(page_compatible
                == share_mapping_4k_leaf_owner_compatible(
                    kernel, source_pagetable, target_thread, source_va,
                )) by {
                reveal(pagetable_perms_wf);
                reveal(mapped_4k_page_pagetable_wf);
                reveal(container_page_owner_wf);
                page_ptr_valid_imply_page_index_valid();
            };
            assert(all_compatible
                == share_mapping_4k_range_owner_compatible_prefix(
                    kernel, source_pagetable, target_thread,
                    source_range, i as int,
                )) by {
                reveal(pagetable_perms_wf);
                reveal(mapped_4k_page_pagetable_wf);
                reveal(container_page_owner_wf);
                page_ptr_valid_imply_page_index_valid();
            };
        }
        all_compatible = all_compatible && page_compatible;
        proof {
            assert(all_compatible
                == share_mapping_4k_range_owner_compatible_prefix(
                    kernel, source_pagetable, target_thread,
                    source_range, (i + 1) as int,
                )) by {
                assert(share_mapping_4k_range_owner_compatible_prefix(
                    kernel, source_pagetable, target_thread,
                    source_range, (i + 1) as int,
                ) == (share_mapping_4k_range_owner_compatible_prefix(
                    kernel, source_pagetable, target_thread,
                    source_range, i as int,
                ) && share_mapping_4k_leaf_owner_compatible(
                    kernel, source_pagetable, target_thread, source_va,
                ))) by {
                    seq_index_lemma::<VAddr>();
                    source_range.va_range_lemma();
                };
                seq_index_lemma::<VAddr>();
                source_range.va_range_lemma();
            };
        }
        i = i + 1;
    }
    all_compatible
}


/// Copy a present 4K mapping range into a prepared, empty range.
///
/// Both endpoint threads and both page tables remain write-locked throughout
/// the operation. Each physical page is locked only while its reverse mapping
/// and reference count are updated. A zero-length pair of ranges is a no-op.
#[verifier::spinoff_prover]
pub fn share_mapping_4k(
    kernel: &mut KernelK,
    source_range: &VaRange4K,
    target_range: &VaRange4K,
    source_thread: RwLockThreadPtr,
    target_thread: RwLockThreadPtr,
    target_process: RwLockProcessPtr,
    target_container: RwLockContainerPtr,
    cpu_id: CpuId,
    source_pagetable: RwLockPageTableRoot,
    target_pagetable: RwLockPageTableRoot,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>,
    Tracked(source_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(target_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>,
    Tracked(target_pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        share_mapping_4k_held_context(
            old(kernel), old(lctx), source_thread, target_thread,
            source_pagetable, target_pagetable, source_thread_lock_perm,
            target_thread_lock_perm, source_pagetable_lock_perm,
            target_pagetable_lock_perm,
        ),
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
        index_valid(NUM_CPUS, cpu_id),
        old(kernel).cpu_array.spec_index(cpu_id).view().wlocked_by(old(lctx)),
        old(lctx).lock_entry_contains(
            old(kernel).cpu_array.lock_id_by_index(cpu_id),
            KernelObjId::Cpu(cpu_id),
        ),
        old(kernel).thread_map.spec_index(target_thread).view().owning_proc
            == target_process,
        old(kernel).thread_map.spec_index(target_thread).view().owning_container
            == target_container,
        old(kernel).process_map.dom().contains(target_process),
        old(kernel).container_map.dom().contains(target_container),
        mmap_4k_allocation_ready(old(kernel), old(lctx)),
        thread_objects_unlocked_except(
            old(kernel).thread_map, old(lctx).thread_id(),
            set![source_thread, target_thread],
        ),
        pagetable_objects_unlocked_except(
            old(kernel).pagetable_map, old(lctx).thread_id(),
            set![source_pagetable, target_pagetable],
        ),
        source_range.wf(),
        old(kernel).pagetable_map.spec_index(source_pagetable).view().wf(),
        old(kernel).pagetable_map.spec_index(source_pagetable).view()
            .kernel_l4_end
            <= spec_va2index(source_range.start).0,
        target_range.wf(),
        source_range.len == target_range.len,
        share_mapping_4k_source_range_present(
            old(kernel), source_pagetable, source_range,
        ),
        share_mapping_4k_range_structure_ready_from(
            old(kernel), source_pagetable, target_pagetable,
            source_range, target_range, 0,
        ),
        share_mapping_4k_range_owner_compatible(
            old(kernel), source_pagetable, target_thread, source_range,
        ),
    ensures
        share_mapping_4k_held_context(
            final(kernel), final(lctx), source_thread, target_thread,
            source_pagetable, target_pagetable, source_thread_lock_perm,
            target_thread_lock_perm, source_pagetable_lock_perm,
            target_pagetable_lock_perm,
        ),
        final(steps).steps.len()
            == old(steps).steps.len() + source_range.len,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(kernel).pagetable_map.spec_index(source_pagetable).view()
            == old(kernel).pagetable_map.spec_index(source_pagetable).view(),
        final(kernel).thread_map.spec_index(source_thread).view()
            == old(kernel).thread_map.spec_index(source_thread).view(),
        final(kernel).pagetable_map.spec_index(target_pagetable).view()
            .mapping_4k()
            == share_mapping_4k_target_map_after(
                old(kernel).pagetable_map.spec_index(source_pagetable).view()
                    .mapping_4k(),
                old(kernel).pagetable_map.spec_index(target_pagetable).view()
                    .mapping_4k(),
                source_range,
                target_range,
                source_range.len as nat,
            ),
        share_mapping_4k_range_mapped_prefix(
            final(kernel).pagetable_map.spec_index(target_pagetable).view(),
            target_range,
            source_range.len as int,
        ),
        final(kernel).pagetable_map.spec_index(target_pagetable).view().mapping_2m()
            == old(kernel).pagetable_map.spec_index(target_pagetable).view()
                .mapping_2m(),
        final(kernel).pagetable_map.spec_index(target_pagetable).view().mapping_1g()
            == old(kernel).pagetable_map.spec_index(target_pagetable).view()
                .mapping_1g(),
        final(kernel).pagetable_map.spec_index(target_pagetable).view().kernel_l4_end
            == old(kernel).pagetable_map.spec_index(target_pagetable).view()
                .kernel_l4_end,
        final(kernel).pagetable_map.spec_index(target_pagetable).view().page_closure()
            == old(kernel).pagetable_map.spec_index(target_pagetable).view()
                .page_closure(),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger final(kernel).pagetable_map.spec_index(target_pagetable)
                .view().spec_resolve_mapping_l2(l4i, l3i, l2i)]
            final(kernel).pagetable_map.spec_index(target_pagetable).view()
                .kernel_l4_end <= l4i && pei_valid(l4i)
                && pei_valid(l3i) && pei_valid(l2i)
            ==> final(kernel).pagetable_map.spec_index(target_pagetable).view()
                    .spec_resolve_mapping_l2(l4i, l3i, l2i)
                == old(kernel).pagetable_map.spec_index(target_pagetable).view()
                    .spec_resolve_mapping_l2(l4i, l3i, l2i),
        share_mapping_4k_reverse_mappings(
            final(kernel), target_pagetable, target_range,
        ),
{
    let mut i: usize = 0;
    while i < source_range.len
        invariant
            share_mapping_4k_held_context(
                kernel, &*lctx, source_thread, target_thread,
                source_pagetable, target_pagetable,
                source_thread_lock_perm, target_thread_lock_perm,
                source_pagetable_lock_perm, target_pagetable_lock_perm,
            ),
            steps.snap_shot == kernel_k_to_kernel_u(*kernel),
            index_valid(NUM_CPUS, cpu_id),
            kernel.cpu_array.spec_index(cpu_id).view().wlocked_by(&*lctx),
            kernel.cpu_array.spec_index(cpu_id).view()
                .locked_by_thread(lctx.thread_id()),
            lctx.lock_entry_contains(
                kernel.cpu_array.lock_id_by_index(cpu_id),
                KernelObjId::Cpu(cpu_id),
            ),
            mmap_4k_allocation_ready(kernel, &*lctx),
            thread_objects_unlocked_except(
                kernel.thread_map, lctx.thread_id(),
                set![source_thread, target_thread],
            ),
            pagetable_objects_unlocked_except(
                kernel.pagetable_map, lctx.thread_id(),
                set![source_pagetable, target_pagetable],
            ),
            source_range.wf(),
            kernel.pagetable_map.spec_index(source_pagetable).view().wf(),
            kernel.pagetable_map.spec_index(source_pagetable).view()
                .kernel_l4_end
                <= spec_va2index(source_range.start).0,
            target_range.wf(),
            source_range.len == target_range.len,
            0 <= i <= source_range.len,
            steps.steps.len() == old(steps).steps.len() + i,
            lctx.thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), lctx),
            old(kernel).pagetable_map.dom().contains(source_pagetable),
            old(kernel).pagetable_map.dom().contains(target_pagetable),
            kernel.process_map.dom().contains(target_process),
            kernel.container_map.dom().contains(target_container),
            kernel.thread_map.spec_index(target_thread).view().owning_proc
                == target_process,
            kernel.thread_map.spec_index(target_thread).view().owning_container
                == target_container,
            kernel.pagetable_map.spec_index(source_pagetable).view()
                == old(kernel).pagetable_map
                    .spec_index(source_pagetable).view(),
            kernel.thread_map.spec_index(source_thread).view()
                == old(kernel).thread_map.spec_index(source_thread).view(),
            share_mapping_4k_source_range_present(
                kernel, source_pagetable, source_range,
            ),
            share_mapping_4k_range_owner_compatible(
                kernel, source_pagetable, target_thread, source_range,
            ),
            share_mapping_4k_range_structure_ready_from(
                kernel, source_pagetable, target_pagetable,
                source_range, target_range, i as int,
            ),
            kernel.pagetable_map.spec_index(target_pagetable).view()
                .mapping_4k()
                == share_mapping_4k_target_map_after(
                    old(kernel).pagetable_map.spec_index(source_pagetable).view()
                        .mapping_4k(),
                    old(kernel).pagetable_map.spec_index(target_pagetable).view()
                        .mapping_4k(),
                    source_range,
                    target_range,
                    i as nat,
                ),
            share_mapping_4k_range_mapped_prefix(
                kernel.pagetable_map.spec_index(target_pagetable).view(),
                target_range,
                i as int,
            ),
            kernel.pagetable_map.spec_index(target_pagetable).view().mapping_2m()
                == old(kernel).pagetable_map.spec_index(target_pagetable).view()
                    .mapping_2m(),
            kernel.pagetable_map.spec_index(target_pagetable).view().mapping_1g()
                == old(kernel).pagetable_map.spec_index(target_pagetable).view()
                    .mapping_1g(),
            kernel.pagetable_map.spec_index(target_pagetable).view().kernel_l4_end
                == old(kernel).pagetable_map.spec_index(target_pagetable).view()
                    .kernel_l4_end,
            kernel.pagetable_map.spec_index(target_pagetable).view().page_closure()
                == old(kernel).pagetable_map.spec_index(target_pagetable).view()
                    .page_closure(),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger kernel.pagetable_map.spec_index(target_pagetable)
                    .view().spec_resolve_mapping_l2(l4i, l3i, l2i)]
                kernel.pagetable_map.spec_index(target_pagetable).view()
                    .kernel_l4_end <= l4i && pei_valid(l4i)
                    && pei_valid(l3i) && pei_valid(l2i)
                ==> kernel.pagetable_map.spec_index(target_pagetable).view()
                        .spec_resolve_mapping_l2(l4i, l3i, l2i)
                    == old(kernel).pagetable_map.spec_index(target_pagetable)
                        .view().spec_resolve_mapping_l2(l4i, l3i, l2i),
        decreases source_range.len - i,
    {
        let source_va = source_range.index(i);
        let target_va = target_range.index(i);
        proof {
            assert(share_mapping_4k_leaf_ready(
                kernel, source_pagetable, target_pagetable,
                target_thread, source_va, target_va,
            )) by {
                assert(share_mapping_4k_leaf_structure_ready(
                    kernel, source_pagetable, target_pagetable,
                    source_va, target_va,
                )) by {
                    seq_index_lemma::<VAddr>();
                    source_range.va_range_lemma();
                    target_range.va_range_lemma();
                    reveal(PageTable::wf_mapping_4k);
                };
                assert(share_mapping_4k_leaf_owner_compatible(
                    kernel, source_pagetable, target_thread, source_va,
                )) by {
                    seq_index_lemma::<VAddr>();
                    source_range.va_range_lemma();
                };
            };
        }
        share_one_mapping_4k(
            kernel,
            source_thread,
            target_thread,
            target_process,
            target_container,
            source_pagetable,
            target_pagetable,
            cpu_id,
            source_va,
            target_va,
            Tracked(&mut *lctx),
            Tracked(&mut *steps),
            Tracked(source_thread_lock_perm),
            Tracked(target_thread_lock_perm),
            Tracked(source_pagetable_lock_perm),
            Tracked(target_pagetable_lock_perm),
        );
        proof {
            assert(share_mapping_4k_source_range_present(
                kernel, source_pagetable, source_range,
            )) by {
                reveal(pagetable_perms_wf);
                reveal(mapped_4k_page_pagetable_wf);
                page_ptr_valid_imply_page_index_valid();
            };
            assert(share_mapping_4k_range_owner_compatible(
                kernel, source_pagetable, target_thread, source_range,
            )) by {
                reveal(pagetable_perms_wf);
                reveal(mapped_4k_page_pagetable_wf);
                reveal(container_page_owner_wf);
                page_ptr_valid_imply_page_index_valid();
            };
            assert(kernel.pagetable_map.spec_index(target_pagetable).view()
                .wf()) by {
                reveal(pagetable_perms_wf);
            };
            assert(share_mapping_4k_range_structure_ready_from(
                kernel, source_pagetable, target_pagetable,
                source_range, target_range, (i + 1) as int,
            )) by {
                seq_index_lemma::<VAddr>();
                source_range.va_range_lemma();
                target_range.va_range_lemma();
            };
            assert(kernel.pagetable_map.spec_index(target_pagetable).view()
                .mapping_4k()
                == share_mapping_4k_target_map_after(
                    old(kernel).pagetable_map.spec_index(source_pagetable).view()
                        .mapping_4k(),
                    old(kernel).pagetable_map.spec_index(target_pagetable).view()
                        .mapping_4k(),
                    source_range,
                    target_range,
                    (i + 1) as nat,
                )) by {
                    source_range.va_range_lemma();
                    target_range.va_range_lemma();
                };
            assert(share_mapping_4k_range_mapped_prefix(
                kernel.pagetable_map.spec_index(target_pagetable).view(),
                target_range,
                (i + 1) as int,
            )) by {
                broadcast use vstd::map::group_map_lemmas;
                seq_index_lemma::<VAddr>();
                target_range.va_range_lemma();
            };
        }
        i = i + 1;
    }
    proof {
        assert(share_mapping_4k_reverse_mappings(
            kernel, target_pagetable, target_range,
        )) by {
            seq_index_lemma::<VAddr>();
            source_range.va_range_lemma();
            target_range.va_range_lemma();
            page_ptr_valid_imply_page_index_valid();
            reveal(pagetable_perms_wf);
            reveal(mapped_4k_page_pagetable_wf);
        };
    }
}

/// Build each missing target directory path and immediately share its 4K leaf.
/// All fallible checks are completed by the caller before this function starts.
#[verifier::spinoff_prover]
pub fn share_mapping_4k_build_and_share(
    kernel: &mut KernelK,
    source_range: &VaRange4K,
    target_range: &VaRange4K,
    target_allocator: RwLockPageAllocatorPtr,
    source_thread: RwLockThreadPtr,
    target_thread: RwLockThreadPtr,
    target_process: RwLockProcessPtr,
    target_container: RwLockContainerPtr,
    cpu_id: CpuId,
    source_pagetable: RwLockPageTableRoot,
    target_pagetable: RwLockPageTableRoot,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>,
    Tracked(source_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(target_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>,
    Tracked(target_pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        share_mapping_4k_held_context(
            old(kernel), old(lctx), source_thread, target_thread,
            source_pagetable, target_pagetable, source_thread_lock_perm,
            target_thread_lock_perm, source_pagetable_lock_perm,
            target_pagetable_lock_perm,
        ),
        mmap_4k_held_context(
            old(kernel), old(lctx), target_allocator, target_thread,
            target_process, target_container, cpu_id, target_pagetable,
            target_thread_lock_perm, target_pagetable_lock_perm,
        ),
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
        mmap_4k_allocation_ready(old(kernel), old(lctx)),
        thread_objects_unlocked_except(
            old(kernel).thread_map, old(lctx).thread_id(),
            set![source_thread, target_thread],
        ),
        pagetable_objects_unlocked_except(
            old(kernel).pagetable_map, old(lctx).thread_id(),
            set![source_pagetable, target_pagetable],
        ),
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        source_range.len <= usize::MAX / 3usize,
        old(kernel).pagetable_map.spec_index(source_pagetable).view().wf(),
        old(kernel).pagetable_map.spec_index(source_pagetable).view()
            .kernel_l4_end <= spec_v2l4index(source_range.start),
        share_mapping_4k_source_range_present(
            old(kernel), source_pagetable, source_range,
        ),
        share_mapping_4k_range_owner_compatible(
            old(kernel), source_pagetable, target_thread, source_range,
        ),
        old(kernel).thread_map.spec_index(target_thread).view().temp_alloc_clean(),
        old(kernel).thread_map.spec_index(target_thread).view()
            .free_quota_pending_clean(),
        old(kernel).thread_map.spec_index(target_thread).view().quota_4k
            >= 3 * target_range.len,
        old(kernel).pagetable_map.spec_index(target_pagetable).view().wf(),
        old(kernel).pagetable_map.spec_index(target_pagetable).view().kernel_l4_end
            <= spec_v2l4index(target_range.start),
        old(kernel).pagetable_map.spec_index(target_pagetable).view()
            .spec_mapping_4k_va_range_empty(
                target_range.start,
                target_range.view().spec_index((target_range.len - 1) as int),
            ),
        old(kernel).pagetable_map.spec_index(target_pagetable).view()
            .spec_mapping_4k_va_range_buildable(target_range),
    ensures
        share_mapping_4k_held_context(
            final(kernel), final(lctx), source_thread, target_thread,
            source_pagetable, target_pagetable, source_thread_lock_perm,
            target_thread_lock_perm, source_pagetable_lock_perm,
            target_pagetable_lock_perm,
        ),
        mmap_4k_held_context(
            final(kernel), final(lctx), target_allocator, target_thread,
            target_process, target_container, cpu_id, target_pagetable,
            target_thread_lock_perm, target_pagetable_lock_perm,
        ),
        mmap_4k_allocation_ready(final(kernel), final(lctx)),
        held_containers_unchanged(
            old(kernel).container_map, final(kernel).container_map, old(lctx),
        ),
        held_processes_unchanged(
            old(kernel).process_map, final(kernel).process_map, old(lctx),
        ),
        held_endpoints_unchanged(
            old(kernel).endpoint_map, final(kernel).endpoint_map, old(lctx),
        ),
        held_schedulers_unchanged(
            old(kernel).scheduler_map, final(kernel).scheduler_map, old(lctx),
        ),
        held_pcid_allocators_unchanged(
            old(kernel).pcid_allocator_map, final(kernel).pcid_allocator_map,
            old(lctx),
        ),
        held_iommu_tables_unchanged(
            old(kernel).iommu_table_map, final(kernel).iommu_table_map, old(lctx),
        ),
        held_cpus_unchanged(
            old(kernel).cpu_array, final(kernel).cpu_array, old(lctx),
        ),
        allocator_objects_unlocked(
            old(kernel).allocator_2m_map, old(lctx).thread_id(),
        ) ==> allocator_objects_unlocked(
            final(kernel).allocator_2m_map, final(lctx).thread_id(),
        ),
        allocator_objects_unlocked(
            old(kernel).allocator_1g_map, old(lctx).thread_id(),
        ) ==> allocator_objects_unlocked(
            final(kernel).allocator_1g_map, final(lctx).thread_id(),
        ),
        thread_objects_unlocked_except(
            final(kernel).thread_map, final(lctx).thread_id(),
            set![source_thread, target_thread],
        ),
        pagetable_objects_unlocked_except(
            final(kernel).pagetable_map, final(lctx).thread_id(),
            set![source_pagetable, target_pagetable],
        ),
        final(steps).steps.len()
            == old(steps).steps.len() + source_range.len,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(kernel).pagetable_map.spec_index(source_pagetable).view()
            == old(kernel).pagetable_map.spec_index(source_pagetable).view(),
        final(kernel).thread_map.spec_index(source_thread).view()
            == old(kernel).thread_map.spec_index(source_thread).view(),
        final(kernel).thread_map.spec_index(target_thread).view().temp_alloc_clean(),
        final(kernel).thread_map.spec_index(target_thread).view()
            .free_quota_pending_clean(),
        final(kernel).thread_map.spec_index(target_thread).view().state
            == old(kernel).thread_map.spec_index(target_thread).view().state,
        final(kernel).thread_map.spec_index(target_thread).view()
            .blocking_endpoint_ptr
            == old(kernel).thread_map.spec_index(target_thread).view()
                .blocking_endpoint_ptr,
        final(kernel).thread_map.spec_index(target_thread).view().quota_4k
            <= old(kernel).thread_map.spec_index(target_thread).view().quota_4k,
        final(kernel).thread_map.spec_index(target_thread).view().quota_4k
            >= old(kernel).thread_map.spec_index(target_thread).view().quota_4k
                - 3 * target_range.len,
        final(kernel).pagetable_map.spec_index(target_pagetable).view()
            .mapping_4k()
            == share_mapping_4k_target_map_after(
                old(kernel).pagetable_map.spec_index(source_pagetable).view()
                    .mapping_4k(),
                old(kernel).pagetable_map.spec_index(target_pagetable).view()
                    .mapping_4k(),
                source_range,
                target_range,
                source_range.len as nat,
            ),
        share_mapping_4k_range_mapped_prefix(
            final(kernel).pagetable_map.spec_index(target_pagetable).view(),
            target_range,
            source_range.len as int,
        ),
        final(kernel).pagetable_map.spec_index(target_pagetable).view().mapping_2m()
            == old(kernel).pagetable_map.spec_index(target_pagetable).view()
                .mapping_2m(),
        final(kernel).pagetable_map.spec_index(target_pagetable).view().mapping_1g()
            == old(kernel).pagetable_map.spec_index(target_pagetable).view()
                .mapping_1g(),
        final(kernel).pagetable_map.spec_index(target_pagetable).view().kernel_l4_end
            == old(kernel).pagetable_map.spec_index(target_pagetable).view()
                .kernel_l4_end,
        share_mapping_4k_reverse_mappings(
            final(kernel), target_pagetable, target_range,
        ),
{
    let target_range_start = target_range.start;
    proof {
        assert({
            &&& kernel.pagetable_map.spec_index(target_pagetable).view()
                .wf_mapping_1g()
            &&& kernel.pagetable_map.spec_index(target_pagetable).view()
                .wf_mapping_2m()
            &&& kernel.pagetable_map.spec_index(target_pagetable).view()
                .wf_mapping_4k()
        }) by {
            reveal(pagetable_perms_wf);
        };
        assert(share_mapping_4k_target_range_empty_from(
            kernel.pagetable_map.spec_index(target_pagetable).view(),
            target_range,
            0,
        )) by {
            reveal(PageTable::spec_mapping_4k_va_range_empty);
            target_range.va_range_lemma();
        };
    }
    let mut i: usize = 0;
    while i < source_range.len
        invariant
            share_mapping_4k_held_context(
                kernel, &*lctx, source_thread, target_thread,
                source_pagetable, target_pagetable,
                source_thread_lock_perm, target_thread_lock_perm,
                source_pagetable_lock_perm, target_pagetable_lock_perm,
            ),
            mmap_4k_held_context(
                kernel, &*lctx, target_allocator, target_thread,
                target_process, target_container, cpu_id, target_pagetable,
                target_thread_lock_perm, target_pagetable_lock_perm,
            ),
            steps.snap_shot == kernel_k_to_kernel_u(*kernel),
            mmap_4k_allocation_ready(kernel, &*lctx),
            held_containers_unchanged(
                old(kernel).container_map, kernel.container_map, old(lctx),
            ),
            held_processes_unchanged(
                old(kernel).process_map, kernel.process_map, old(lctx),
            ),
            held_endpoints_unchanged(
                old(kernel).endpoint_map, kernel.endpoint_map, old(lctx),
            ),
            held_schedulers_unchanged(
                old(kernel).scheduler_map, kernel.scheduler_map, old(lctx),
            ),
            held_pcid_allocators_unchanged(
                old(kernel).pcid_allocator_map, kernel.pcid_allocator_map,
                old(lctx),
            ),
            held_iommu_tables_unchanged(
                old(kernel).iommu_table_map, kernel.iommu_table_map, old(lctx),
            ),
            held_cpus_unchanged(
                old(kernel).cpu_array, kernel.cpu_array, old(lctx),
            ),
            allocator_objects_unlocked(
                old(kernel).allocator_2m_map, old(lctx).thread_id(),
            ) ==> allocator_objects_unlocked(
                kernel.allocator_2m_map, lctx.thread_id(),
            ),
            allocator_objects_unlocked(
                old(kernel).allocator_1g_map, old(lctx).thread_id(),
            ) ==> allocator_objects_unlocked(
                kernel.allocator_1g_map, lctx.thread_id(),
            ),
            kernel.cpu_array.spec_index(cpu_id).view()
                .locked_by_thread(lctx.thread_id()),
            thread_objects_unlocked_except(
                kernel.thread_map, lctx.thread_id(),
                set![source_thread, target_thread],
            ),
            pagetable_objects_unlocked_except(
                kernel.pagetable_map, lctx.thread_id(),
                set![source_pagetable, target_pagetable],
            ),
            source_range.wf(),
            target_range.wf(),
            source_range.len == target_range.len,
            source_range.len > 0,
            source_range.len <= usize::MAX / 3usize,
            target_range_start == target_range.start,
            0 <= i <= source_range.len,
            steps.steps.len() == old(steps).steps.len() + i,
            lctx.thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), lctx),
            old(kernel).thread_map.dom().contains(source_thread),
            old(kernel).thread_map.dom().contains(target_thread),
            old(kernel).pagetable_map.dom().contains(source_pagetable),
            old(kernel).pagetable_map.dom().contains(target_pagetable),
            kernel.pagetable_map.spec_index(source_pagetable).view()
                == old(kernel).pagetable_map.spec_index(source_pagetable).view(),
            kernel.thread_map.spec_index(source_thread).view()
                == old(kernel).thread_map.spec_index(source_thread).view(),
            kernel.pagetable_map.spec_index(source_pagetable).view().wf(),
            kernel.pagetable_map.spec_index(source_pagetable).view()
                .kernel_l4_end <= spec_v2l4index(source_range.start),
            kernel.thread_map.spec_index(target_thread).view()
                .upper_container_seq
                == old(kernel).thread_map.spec_index(target_thread).view()
                    .upper_container_seq,
            kernel.thread_map.spec_index(target_thread).view().state
                == old(kernel).thread_map.spec_index(target_thread).view().state,
            kernel.thread_map.spec_index(target_thread).view()
                .blocking_endpoint_ptr
                == old(kernel).thread_map.spec_index(target_thread).view()
                    .blocking_endpoint_ptr,
            share_mapping_4k_source_range_present(
                kernel, source_pagetable, source_range,
            ),
            share_mapping_4k_range_owner_compatible(
                kernel, source_pagetable, target_thread, source_range,
            ),
            kernel.thread_map.spec_index(target_thread).view().temp_alloc_clean(),
            kernel.thread_map.spec_index(target_thread).view()
                .free_quota_pending_clean(),
            old(kernel).thread_map.spec_index(target_thread).view().quota_4k
                >= 3 * target_range.len,
            kernel.thread_map.spec_index(target_thread).view().quota_4k
                >= 3 * (target_range.len - i),
            kernel.thread_map.spec_index(target_thread).view().quota_4k
                >= old(kernel).thread_map.spec_index(target_thread).view().quota_4k
                    - 3 * i,
            kernel.thread_map.spec_index(target_thread).view().quota_4k
                <= old(kernel).thread_map.spec_index(target_thread).view().quota_4k,
            kernel.pagetable_map.spec_index(target_pagetable).view().wf(),
            old(kernel).pagetable_map.spec_index(target_pagetable).view().wf(),
            kernel.pagetable_map.spec_index(target_pagetable).view().kernel_l4_end
                == old(kernel).pagetable_map.spec_index(target_pagetable).view()
                    .kernel_l4_end,
            kernel.pagetable_map.spec_index(target_pagetable).view().kernel_l4_end
                <= spec_v2l4index(target_range.start),
            kernel.pagetable_map.spec_index(target_pagetable).view().mapping_2m()
                == old(kernel).pagetable_map.spec_index(target_pagetable).view()
                    .mapping_2m(),
            kernel.pagetable_map.spec_index(target_pagetable).view().mapping_1g()
                == old(kernel).pagetable_map.spec_index(target_pagetable).view()
                    .mapping_1g(),
            old(kernel).pagetable_map.spec_index(target_pagetable).view()
                .wf_mapping_1g(),
            old(kernel).pagetable_map.spec_index(target_pagetable).view()
                .wf_mapping_2m(),
            old(kernel).pagetable_map.spec_index(target_pagetable).view()
                .wf_mapping_4k(),
            old(kernel).pagetable_map.spec_index(target_pagetable).view()
                .spec_mapping_4k_va_range_buildable(target_range),
            kernel.pagetable_map.spec_index(target_pagetable).view().mapping_4k()
                == share_mapping_4k_target_map_after(
                    old(kernel).pagetable_map.spec_index(source_pagetable).view()
                        .mapping_4k(),
                    old(kernel).pagetable_map.spec_index(target_pagetable).view()
                        .mapping_4k(),
                    source_range,
                    target_range,
                    i as nat,
                ),
            share_mapping_4k_range_mapped_prefix(
                kernel.pagetable_map.spec_index(target_pagetable).view(),
                target_range,
                i as int,
            ),
            share_mapping_4k_target_range_empty_from(
                kernel.pagetable_map.spec_index(target_pagetable).view(),
                target_range,
                i as int,
            ),
        decreases source_range.len - i,
    {
        let source_va = source_range.index(i);
        let target_va = target_range.index(i);
        proof {
            assert({
                &&& spec_va_4k_valid(target_range_start)
                &&& spec_va_4k_valid(target_va)
                &&& target_range_start <= target_va
            }) by {
                target_range.va_range_lemma();
            };
            assert(spec_v2l4index(target_range_start)
                <= spec_v2l4index(target_va)) by (bit_vector)
                requires
                    spec_va_4k_valid(target_range_start),
                    spec_va_4k_valid(target_va),
                    target_range_start <= target_va,
            ;
            assert(va_4k_valid(target_va)) by {
                target_range.va_range_lemma();
            };
            assert(kernel.pagetable_map.spec_index(target_pagetable).view()
                .kernel_l4_end <= spec_v2l4index(target_va)) by {
                target_range.va_range_lemma();
            };
            assert({
                &&& pei_valid(spec_v2l4index(target_va))
                &&& pei_valid(spec_v2l3index(target_va))
                &&& pei_valid(spec_v2l2index(target_va))
                &&& pei_valid(spec_v2l1index(target_va))
            }) by {
                spec_va_4k_valid_imply_indices_valid();
            };
            assert(old(kernel).pagetable_map.spec_index(target_pagetable).view()
                .spec_4k_entry_useable(
                    spec_v2l4index(target_va), spec_v2l3index(target_va),
                    spec_v2l2index(target_va), spec_v2l1index(target_va),
                )) by {
                target_range.va_range_lemma();
                seq_index_lemma::<VAddr>();
                assert(old(kernel).pagetable_map.spec_index(target_pagetable)
                    .view().spec_resolve_mapping_4k_l1(
                        spec_va2index(target_range.view().spec_index(i as int)).0,
                        spec_va2index(target_range.view().spec_index(i as int)).1,
                        spec_va2index(target_range.view().spec_index(i as int)).2,
                        spec_va2index(target_range.view().spec_index(i as int)).3,
                    ) is None) by {
                        seq_index_lemma::<VAddr>();
                    };
            };
            assert({
                &&& kernel.pagetable_map.spec_index(target_pagetable).view()
                    .wf_mapping_1g()
                &&& kernel.pagetable_map.spec_index(target_pagetable).view()
                    .wf_mapping_2m()
                &&& kernel.pagetable_map.spec_index(target_pagetable).view()
                    .wf_mapping_4k()
            }) by {
                reveal(pagetable_perms_wf);
            };
            assert(kernel.pagetable_map.spec_index(target_pagetable).view()
                .spec_resolve_mapping_1g_l3(
                    spec_v2l4index(target_va), spec_v2l3index(target_va),
                ) is None) by {
                reveal(PageTable::wf_mapping_1g);
            };
            assert(kernel.pagetable_map.spec_index(target_pagetable).view()
                .spec_resolve_mapping_2m_l2(
                    spec_v2l4index(target_va), spec_v2l3index(target_va),
                    spec_v2l2index(target_va),
                ) is None) by {
                reveal(PageTable::wf_mapping_2m);
            };
            assert(!kernel.pagetable_map.spec_index(target_pagetable).view()
                .mapping_4k().dom().contains(target_va)) by {
                target_range.va_range_lemma();
                seq_index_lemma::<VAddr>();
            };
            assert(kernel.pagetable_map.spec_index(target_pagetable).view()
                .spec_resolve_mapping_4k_l1(
                    spec_v2l4index(target_va), spec_v2l3index(target_va),
                    spec_v2l2index(target_va), spec_v2l1index(target_va),
                ) is None) by {
                reveal(PageTable::wf_mapping_4k);
                spec_va_4k_index_roundtrip();
            };
        }
        mmap_4k_build_one_structure(
            kernel,
            target_va,
            target_allocator,
            target_thread,
            target_process,
            target_container,
            cpu_id,
            target_pagetable,
            3 * (target_range.len - i - 1),
            Tracked(&mut *lctx),
            Tracked(&mut *steps),
            Tracked(target_thread_lock_perm),
            Tracked(target_pagetable_lock_perm),
        );
        proof {
            assert(thread_objects_unlocked_except(
                kernel.thread_map, lctx.thread_id(),
                set![source_thread, target_thread],
            )) by {
                reveal(thread_objects_unlocked_except);
            };
            assert(pagetable_objects_unlocked_except(
                kernel.pagetable_map, lctx.thread_id(),
                set![source_pagetable, target_pagetable],
            )) by {
                reveal(pagetable_objects_unlocked_except);
            };
            assert(share_mapping_4k_held_context(
                kernel, &*lctx, source_thread, target_thread,
                source_pagetable, target_pagetable,
                source_thread_lock_perm, target_thread_lock_perm,
                source_pagetable_lock_perm, target_pagetable_lock_perm,
            )) by {
                reveal(process_thread_wf);
                reveal(process_pagetable_match);
                lock_id_fields_eq_imply_eq();
            };
            assert(share_mapping_4k_source_range_present(
                kernel, source_pagetable, source_range,
            )) by {
                reveal(pagetable_perms_wf);
                reveal(mapped_4k_page_pagetable_wf);
                page_ptr_valid_imply_page_index_valid();
            };
            assert(share_mapping_4k_range_owner_compatible(
                kernel, source_pagetable, target_thread, source_range,
            )) by {
                reveal(pagetable_perms_wf);
                reveal(mapped_4k_page_pagetable_wf);
                reveal(container_page_owner_wf);
                reveal(PageTable::wf_mapping_4k);
                page_ptr_valid_imply_page_index_valid();
            };
            assert(share_mapping_4k_leaf_ready(
                kernel, source_pagetable, target_pagetable,
                target_thread, source_va, target_va,
            )) by {
                assert(share_mapping_4k_leaf_structure_ready(
                    kernel, source_pagetable, target_pagetable,
                    source_va, target_va,
                )) by {
                    seq_index_lemma::<VAddr>();
                    source_range.va_range_lemma();
                    target_range.va_range_lemma();
                    reveal(PageTable::wf_mapping_4k);
                };
                assert(share_mapping_4k_leaf_owner_compatible(
                    kernel, source_pagetable, target_thread, source_va,
                )) by {
                    seq_index_lemma::<VAddr>();
                    source_range.va_range_lemma();
                };
            };
        }
        share_one_mapping_4k(
            kernel,
            source_thread,
            target_thread,
            target_process,
            target_container,
            source_pagetable,
            target_pagetable,
            cpu_id,
            source_va,
            target_va,
            Tracked(&mut *lctx),
            Tracked(&mut *steps),
            Tracked(source_thread_lock_perm),
            Tracked(target_thread_lock_perm),
            Tracked(source_pagetable_lock_perm),
            Tracked(target_pagetable_lock_perm),
        );
        proof {
            assert({
                &&& kernel.cpu_array.spec_index(cpu_id).view()
                    .wlocked_by(&*lctx)
                &&& kernel.cpu_array.spec_index(cpu_id).view()
                    .being_killed() == false
            }) by {
                reveal(held_cpus_unchanged);
            };
            assert(lctx.lock_entry_contains(
                kernel.cpu_array.lock_id_by_index(cpu_id),
                KernelObjId::Cpu(cpu_id),
            )) by {
                reveal(held_cpus_unchanged);
                lock_id_fields_eq_imply_eq();
            };
            assert({
                &&& kernel.container_map.dom().contains(target_container)
                &&& kernel.container_map.spec_index(target_container)
                    .view_rodata().view().allocator_ptr_4k == target_allocator
                &&& kernel.allocator_4k_map.dom().contains(target_allocator)
            }) by {
                reveal(container_allocator_wf);
                reveal(container_thread_wf);
            };
            assert({
                &&& kernel.process_map.dom().contains(target_process)
                &&& kernel.process_map.spec_index(target_process)
                    .view_rodata().view().owning_container == target_container
            }) by {
                reveal(container_thread_wf);
                reveal(process_thread_wf);
            };
            assert(mmap_4k_held_context(
                kernel, &*lctx, target_allocator, target_thread,
                target_process, target_container, cpu_id, target_pagetable,
                target_thread_lock_perm, target_pagetable_lock_perm,
            )) by {
                reveal(container_allocator_wf);
                reveal(container_thread_wf);
                reveal(process_thread_wf);
                reveal(process_pagetable_match);
                reveal(held_cpus_unchanged);
                lock_id_fields_eq_imply_eq();
            };
            assert(share_mapping_4k_source_range_present(
                kernel, source_pagetable, source_range,
            )) by {
                reveal(pagetable_perms_wf);
                reveal(mapped_4k_page_pagetable_wf);
                page_ptr_valid_imply_page_index_valid();
            };
            assert(share_mapping_4k_range_owner_compatible(
                kernel, source_pagetable, target_thread, source_range,
            )) by {
                reveal(pagetable_perms_wf);
                reveal(mapped_4k_page_pagetable_wf);
                reveal(container_page_owner_wf);
                page_ptr_valid_imply_page_index_valid();
            };
            assert(kernel.pagetable_map.spec_index(target_pagetable).view()
                .wf()) by {
                reveal(pagetable_perms_wf);
            };
            assert(held_containers_unchanged(
                old(kernel).container_map, kernel.container_map, old(lctx),
            )) by {
                lock_id_fields_eq_imply_eq();
            };
            assert(held_processes_unchanged(
                old(kernel).process_map, kernel.process_map, old(lctx),
            )) by {
                lock_id_fields_eq_imply_eq();
            };
            assert(held_endpoints_unchanged(
                old(kernel).endpoint_map, kernel.endpoint_map, old(lctx),
            )) by {
                lock_id_fields_eq_imply_eq();
            };
            assert(held_schedulers_unchanged(
                old(kernel).scheduler_map, kernel.scheduler_map, old(lctx),
            )) by {
                lock_id_fields_eq_imply_eq();
            };
            assert(held_pcid_allocators_unchanged(
                old(kernel).pcid_allocator_map,
                kernel.pcid_allocator_map,
                old(lctx),
            )) by {
                lock_id_fields_eq_imply_eq();
            };
            assert(held_iommu_tables_unchanged(
                old(kernel).iommu_table_map,
                kernel.iommu_table_map,
                old(lctx),
            )) by {
                lock_id_fields_eq_imply_eq();
            };
            assert(held_cpus_unchanged(
                old(kernel).cpu_array, kernel.cpu_array, old(lctx),
            )) by {
                lock_id_fields_eq_imply_eq();
            };
            assert(allocator_objects_unlocked(
                old(kernel).allocator_2m_map, old(lctx).thread_id(),
            ) ==> allocator_objects_unlocked(
                kernel.allocator_2m_map, lctx.thread_id(),
            )) by {
                lock_id_fields_eq_imply_eq();
            };
            assert(allocator_objects_unlocked(
                old(kernel).allocator_1g_map, old(lctx).thread_id(),
            ) ==> allocator_objects_unlocked(
                kernel.allocator_1g_map, lctx.thread_id(),
            )) by {
                lock_id_fields_eq_imply_eq();
            };
            assert(kernel.pagetable_map.spec_index(target_pagetable).view()
                .mapping_4k()
                == share_mapping_4k_target_map_after(
                    old(kernel).pagetable_map.spec_index(source_pagetable).view()
                        .mapping_4k(),
                    old(kernel).pagetable_map.spec_index(target_pagetable).view()
                        .mapping_4k(),
                    source_range,
                    target_range,
                    (i + 1) as nat,
                )) by {
                source_range.va_range_lemma();
                target_range.va_range_lemma();
            };
            assert(share_mapping_4k_range_mapped_prefix(
                kernel.pagetable_map.spec_index(target_pagetable).view(),
                target_range,
                (i + 1) as int,
            )) by {
                broadcast use vstd::map::group_map_lemmas;
                seq_index_lemma::<VAddr>();
                target_range.va_range_lemma();
            };
            assert(share_mapping_4k_target_range_empty_from(
                kernel.pagetable_map.spec_index(target_pagetable).view(),
                target_range,
                (i + 1) as int,
            )) by {
                seq_index_lemma::<VAddr>();
                target_range.va_range_lemma();
            };
        }
        i = i + 1;
    }
    proof {
        assert(share_mapping_4k_reverse_mappings(
            kernel, target_pagetable, target_range,
        )) by {
            seq_index_lemma::<VAddr>();
            source_range.va_range_lemma();
            target_range.va_range_lemma();
            page_ptr_valid_imply_page_index_valid();
            reveal(pagetable_perms_wf);
            reveal(mapped_4k_page_pagetable_wf);
        };
    }
}
} // verus!
