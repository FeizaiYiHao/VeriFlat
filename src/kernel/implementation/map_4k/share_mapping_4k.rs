use vstd::prelude::*;
use crate::*;

verus! {

/// Locks and stable owner relations retained throughout a 4K sharing pass.
pub open spec fn share_mapping_4k_held_context(
    krnl: &KernelK,
    lctx: &LocalContext,
    source_thread: RwLockThreadPtr,
    target_thread: RwLockThreadPtr,
    target_process: RwLockProcessPtr,
    target_container: RwLockContainerPtr,
    source_pagetable: RwLockPageTableRoot,
    target_pagetable: RwLockPageTableRoot,
    source_thread_lock_perm: &LockPerm,
    target_thread_lock_perm: &LockPerm,
    source_pagetable_lock_perm: &LockPerm,
    target_pagetable_lock_perm: &LockPerm,
) -> bool {
    &&& krnl.inv()
    &&& lctx.kernel_view_locking_state() is Acquire
    &&& typed_lock_maps_aligned(krnl, lctx)
    &&& lock_id_set_aligned(lctx)
    &&& lctx.page_lock_map().dom().is_empty()
    &&& page_objects_unlocked(krnl.pg_arr, lctx.thread_id())
    &&& lctx.held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR)
    &&& source_pagetable != target_pagetable
    &&& krnl.thr_mp.dom().contains(source_thread)
    &&& krnl.thr_mp.dom().contains(target_thread)
    &&& krnl.thr_mp.spec_index(source_thread).wlocked_by(lctx)
    &&& !krnl.thr_mp.spec_index(source_thread).being_killed()
    &&& krnl.thr_mp.spec_index(target_thread).wlocked_by(lctx)
    &&& !krnl.thr_mp.spec_index(target_thread).being_killed()
    &&& krnl.thr_mp.spec_index(source_thread).view().owning_proc
        != target_process
    &&& krnl.thr_mp.spec_index(source_thread).view().proc_pagetable_ptr
        == source_pagetable
    &&& krnl.thr_mp.spec_index(target_thread).view().owning_container
        == target_container
    &&& krnl.prc_mp.dom().contains(target_process)
    &&& krnl.prc_mp.spec_index(target_process).view_rodata().view()
        .owning_container == target_container
    &&& krnl.prc_mp.spec_index(target_process).view_rodata().view()
        .pagetable == target_pagetable
    &&& {
        ||| {
            &&& krnl.thr_mp.spec_index(target_thread).view().owning_proc
                == target_process
            &&& krnl.thr_mp.spec_index(target_thread).view().proc_pagetable_ptr
                == target_pagetable
        }
        ||| krnl.prc_mp.spec_index(target_process).wlocked_by(lctx)
    }
    &&& source_thread_lock_perm.state() is WriteLock
    &&& source_thread_lock_perm.thread_id() == lctx.thread_id()
    &&& source_thread_lock_perm.lock_id()
        == krnl.thr_mp.spec_index(source_thread)
            .locking_thread()->Write_lock_id
    &&& target_thread_lock_perm.state() is WriteLock
    &&& target_thread_lock_perm.thread_id() == lctx.thread_id()
    &&& target_thread_lock_perm.lock_id()
        == krnl.thr_mp.spec_index(target_thread)
            .locking_thread()->Write_lock_id
    &&& krnl.pt_mp.dom().contains(source_pagetable)
    &&& krnl.pt_mp.dom().contains(target_pagetable)
    &&& krnl.pt_mp.spec_index(source_pagetable).wlocked_by(lctx)
    &&& krnl.pt_mp.spec_index(target_pagetable).wlocked_by(lctx)
    &&& krnl.pt_mp.spec_index(source_pagetable).view().proc_ptr
        == krnl.thr_mp.spec_index(source_thread).view().owning_proc
    &&& krnl.pt_mp.spec_index(target_pagetable).view().proc_ptr
        == target_process
    &&& source_pagetable_lock_perm.state() is WriteLock
    &&& source_pagetable_lock_perm.thread_id() == lctx.thread_id()
    &&& source_pagetable_lock_perm.lock_id()
        == krnl.pt_mp.spec_index(source_pagetable)
            .locking_thread()->Write_lock_id
    &&& target_pagetable_lock_perm.state() is WriteLock
    &&& target_pagetable_lock_perm.thread_id() == lctx.thread_id()
    &&& target_pagetable_lock_perm.lock_id()
        == krnl.pt_mp.spec_index(target_pagetable)
            .locking_thread()->Write_lock_id
}

pub open spec fn share_mapping_4k_source_range_present(
    krnl: &KernelK,
    source_pagetable: RwLockPageTableRoot,
    source_range: &VaRange4K,
) -> bool
    recommends
        krnl.pt_mp.dom().contains(source_pagetable),
        krnl.pt_mp.spec_index(source_pagetable).view().wf(),
        source_range.wf(),
        krnl.pt_mp.spec_index(source_pagetable).view().kernel_l4_end <= spec_va2index(source_range.start).0,
{
    &&& krnl.pt_mp.spec_index(source_pagetable).view()
        .spec_mapping_4k_va_range_present(source_range)
    &&& forall|i: int|
        #![trigger krnl.pt_mp.spec_index(source_pagetable)
            .view().mapping_4k().spec_index(source_range.view().spec_index(i))]
        0 <= i < source_range.len
        ==> {
            let source_va = source_range.view().spec_index(i);
            let source_entry = krnl.pt_mp
                .spec_index(source_pagetable).view().mapping_4k()
                .spec_index(source_va);
            let page_index = page_ptr2page_index(source_entry.addr);
            &&& krnl.pt_mp.spec_index(source_pagetable).view()
                .mapping_4k().dom().contains(source_va)
            &&& source_entry.present
            &&& page_ptr_valid(source_entry.addr)
            &&& index_valid(NUM_PAGES, page_index)
            &&& krnl.pg_arr.spec_index(page_index).view().view().state
                is Mapped4k
            &&& krnl.pg_arr.spec_index(page_index).view().view()
                .mappings().contains((source_pagetable, source_va))
        }
}

pub open spec fn share_mapping_4k_leaf_structure_ready(
    krnl: &KernelK,
    source_pagetable: RwLockPageTableRoot,
    target_pagetable: RwLockPageTableRoot,
    source_va: VAddr,
    target_va: VAddr,
) -> bool {
    let source_indices = spec_va2index(source_va);
    let target_indices = spec_va2index(target_va);
    &&& va_4k_valid(source_va)
    &&& va_4k_valid(target_va)
    &&& krnl.pt_mp.spec_index(source_pagetable).view().kernel_l4_end
        <= source_indices.0
    &&& pei_valid(source_indices.0)
    &&& pei_valid(source_indices.1)
    &&& pei_valid(source_indices.2)
    &&& pei_valid(source_indices.3)
    &&& krnl.pt_mp.spec_index(source_pagetable).view()
        .mapping_4k().dom().contains(source_va)
    &&& krnl.pt_mp.spec_index(source_pagetable).view()
        .mapping_4k().spec_index(source_va).present
    &&& krnl.pt_mp.spec_index(target_pagetable).view().kernel_l4_end
        <= target_indices.0
    &&& pei_valid(target_indices.0)
    &&& pei_valid(target_indices.1)
    &&& pei_valid(target_indices.2)
    &&& pei_valid(target_indices.3)
    &&& !krnl.pt_mp.spec_index(target_pagetable).view()
        .mapping_4k().dom().contains(target_va)
    &&& krnl.pt_mp.spec_index(target_pagetable).view()
        .spec_resolve_mapping_l2(target_indices.0, target_indices.1, target_indices.2) is Some
}

pub open spec fn share_mapping_4k_leaf_owner_compatible(
    krnl: &KernelK,
    source_pagetable: RwLockPageTableRoot,
    target_thread: RwLockThreadPtr,
    source_va: VAddr,
) -> bool {
    let owner = krnl.pt_mp.spec_index(source_pagetable).view()
        .mapping_4k().spec_index(source_va).owning_container@;
    &&& krnl.thr_mp.dom().contains(target_thread)
    &&& krnl.ctn_mp.dom().contains(owner)
    &&& (krnl.thr_mp.spec_index(target_thread).view().owning_container
            == owner
        || krnl.thr_mp.spec_index(target_thread).view()
            .upper_container_seq@.contains(owner))
}

pub open spec fn share_mapping_4k_leaf_ready(
    krnl: &KernelK,
    source_pagetable: RwLockPageTableRoot,
    target_pagetable: RwLockPageTableRoot,
    target_thread: RwLockThreadPtr,
    source_va: VAddr,
    target_va: VAddr,
) -> bool {
    &&& share_mapping_4k_leaf_structure_ready(krnl, source_pagetable, target_pagetable, source_va, target_va)
    &&& share_mapping_4k_leaf_owner_compatible(krnl, source_pagetable, target_thread, source_va)
}

pub open spec fn share_mapping_4k_range_structure_ready_from(
    krnl: &KernelK,
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
        ==> share_mapping_4k_leaf_structure_ready(krnl, source_pagetable, target_pagetable, source_range.view().spec_index(i), target_range.view().spec_index(i))
}

pub open spec fn share_mapping_4k_range_owner_compatible(
    krnl: &KernelK,
    source_pagetable: RwLockPageTableRoot,
    target_thread: RwLockThreadPtr,
    source_range: &VaRange4K,
) -> bool {
    forall|i: int|
        #![trigger source_range.view().spec_index(i)]
        0 <= i < source_range.len
        ==> share_mapping_4k_leaf_owner_compatible(krnl, source_pagetable, target_thread, source_range.view().spec_index(i))
}

pub open spec fn share_mapping_4k_range_owner_compatible_prefix(
    krnl: &KernelK,
    source_pagetable: RwLockPageTableRoot,
    target_thread: RwLockThreadPtr,
    source_range: &VaRange4K,
    upper: int,
) -> bool {
    forall|i: int|
        #![trigger source_range.view().spec_index(i)]
        0 <= i < upper
        ==> share_mapping_4k_leaf_owner_compatible(krnl, source_pagetable, target_thread, source_range.view().spec_index(i))
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
        share_mapping_4k_target_map_after(source, target, source_range, target_range, (upper - 1) as nat).insert(target_range.view().spec_index((upper - 1) as int), source.spec_index(source_range.view().spec_index((upper - 1) as int)))
    }
}

pub open spec fn share_mapping_4k_range_mapped_prefix(
    target: PageTable<PT_TYPE>,
    target_range: &VaRange4K,
    upper: int,
) -> bool {
    forall|i: int|
        #![trigger target.mapping_4k().dom().contains(target_range.view().spec_index(i))]
        0 <= i < upper
        ==> target.mapping_4k().dom().contains(target_range.view().spec_index(i))
}

/// Every not-yet-shared target VA is still absent from the 4K mapping.
pub open spec fn share_mapping_4k_target_range_empty_from(
    pagetable: PageTable<PT_TYPE>,
    target_range: &VaRange4K,
    first: int,
) -> bool {
    forall|i: int|
        #![trigger pagetable.mapping_4k().dom().contains(target_range.view().spec_index(i))]
        first <= i < target_range.len
        ==> !pagetable.mapping_4k().dom().contains(target_range.view().spec_index(i))
}

pub open spec fn share_mapping_4k_reverse_mappings(
    krnl: &KernelK,
    target_pagetable: RwLockPageTableRoot,
    target_range: &VaRange4K,
) -> bool {
    forall|i: int|
        #![trigger krnl.pt_mp.spec_index(target_pagetable)
            .view().mapping_4k().spec_index(target_range.view().spec_index(i))]
        0 <= i < target_range.len
        ==> {
            let target_va = target_range.view().spec_index(i);
            let target_entry = krnl.pt_mp
                .spec_index(target_pagetable).view().mapping_4k()
                .spec_index(target_va);
            let page_index = page_ptr2page_index(target_entry.addr);
            &&& krnl.pt_mp.spec_index(target_pagetable).view()
                .mapping_4k().dom().contains(target_va)
            &&& page_ptr_valid(target_entry.addr)
            &&& index_valid(NUM_PAGES, page_index)
            &&& krnl.pg_arr.spec_index(page_index).view().view().state
                is Mapped4k
            &&& krnl.pg_arr.spec_index(page_index).view().view()
                .mappings().contains((target_pagetable, target_va))
        }
}

/// Checks a source 4K range without mutating krnl or page-table state.
pub fn share_mapping_4k_source_precheck(
    krnl: &KernelK,
    source_range: &VaRange4K,
    source_pagetable: RwLockPageTableRoot,
    Tracked(lctx): Tracked<&LocalContext>,
    Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>,
) -> (ret: bool)
    requires
        krnl.inv(),
        source_range.wf(),
        krnl.pt_mp.dom().contains(source_pagetable),
        krnl.pt_mp.spec_index(source_pagetable).view().kernel_l4_end <= spec_va2index(source_range.start).0,
        krnl.pt_mp.spec_index(source_pagetable).locked_by(lctx),
        source_pagetable_lock_perm.thread_id() == lctx.thread_id(),
        (source_pagetable_lock_perm.state() is ReadLock || source_pagetable_lock_perm.state() is WriteLock),
        source_pagetable_lock_perm.state() is ReadLock ==> krnl.pt_mp.spec_index(source_pagetable).read_lock_perm_match(source_pagetable_lock_perm),
        source_pagetable_lock_perm.state() is WriteLock ==> krnl.pt_mp.spec_index(source_pagetable).write_lock_perm_match(source_pagetable_lock_perm),
    ensures
        ret == share_mapping_4k_source_range_present(krnl, source_pagetable, source_range),
{
    proof {
        assert({
            &&& krnl.pt_mp.perms_wf()
            &&& krnl.pt_mp.spec_index(source_pagetable).is_init()
            &&& krnl.pt_mp.spec_index(source_pagetable).view().wf()
        }) by { reveal(pagetable_perms_wf); };
    }
    let pagetable = krnl.pt_mp.borrow(source_pagetable, Tracked(source_pagetable_lock_perm));
    let ret = pagetable.mapping_4k_va_range_present(source_range);
    proof {
        assert(ret == share_mapping_4k_source_range_present(krnl, source_pagetable, source_range)) by {
            if ret {
                reveal(mapped_4k_page_pagetable_wf);
                page_ptr_valid_imply_page_index_valid();
            }
        };
    }
    ret
}

#[verifier::spinoff_prover]
fn share_one_mapping_4k(
    krnl: &mut KernelK,
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
        share_mapping_4k_held_context(old(krnl), old(lctx), source_thread, target_thread, target_process, target_container, source_pagetable, target_pagetable, source_thread_lock_perm, target_thread_lock_perm, source_pagetable_lock_perm, target_pagetable_lock_perm),
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).cpu_arr.spec_index(cpu_id).view().wlocked_by(old(lctx)),
        old(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        old(krnl).prc_mp.dom().contains(target_process),
        old(krnl).ctn_mp.dom().contains(target_container),
        mmap_4k_allocation_ready(old(krnl), old(lctx)),
        thread_objects_unlocked_except(old(krnl).thr_mp, old(lctx).thread_id(), set![source_thread, target_thread]),
        pagetable_objects_unlocked_except(old(krnl).pt_mp, old(lctx).thread_id(), set![source_pagetable, target_pagetable]),
        share_mapping_4k_leaf_ready(old(krnl), source_pagetable, target_pagetable, target_thread, source_va, target_va),
    ensures
        share_mapping_4k_held_context(final(krnl), final(lctx), source_thread, target_thread, target_process, target_container, source_pagetable, target_pagetable, source_thread_lock_perm, target_thread_lock_perm, source_pagetable_lock_perm, target_pagetable_lock_perm),
        final(steps).steps.len() == old(steps).steps.len() + 1,
        final(steps).steps.subrange(0, old(steps).steps.len() as int) == old(steps).steps,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        {
            let source_process = old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr;
            &&& final(steps).steps.last().new_u.process_map.dom().contains(source_process)
            &&& kernel_k_to_kernel_u(*final(krnl)).process_map.dom().contains(source_process)
            &&& final(steps).steps.last().new_u.process_map.spec_index(source_process).pagetable == kernel_k_to_kernel_u(*final(krnl)).process_map.spec_index(source_process).pagetable
            &&& final(steps).steps.last().new_u.process_map.dom().contains(target_process)
            &&& old(krnl).prc_mp.spec_index(target_process).wlocked_by(old(lctx)) && {
                let iommu_table = old(krnl).prc_mp.spec_index(target_process).view().iommu_table;
                ||| iommu_table is None
                ||| iommu_table is Some && old(lctx).iommu_table_lock_map().dom().contains(iommu_table.unwrap())
            } ==> {
                &&& kernel_k_to_kernel_u(*final(krnl)).process_map.dom().contains(target_process)
                &&& final(steps).steps.last().new_u.process_map.spec_index(target_process) == kernel_k_to_kernel_u(*final(krnl)).process_map.spec_index(target_process)
            }
        },
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(krnl).thr_mp.lock_id_by_key(target_thread) == old(krnl).thr_mp.lock_id_by_key(target_thread),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        mmap_4k_allocation_ready(final(krnl), final(lctx)),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
        held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
        held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        thread_objects_unlocked_except(final(krnl).thr_mp, final(lctx).thread_id(), set![source_thread, target_thread]),
        pagetable_objects_unlocked_except(final(krnl).pt_mp, final(lctx).thread_id(), set![source_pagetable, target_pagetable]),
        allocator_objects_unlocked(old(krnl).allc_2m_mp, old(lctx).thread_id()) ==> allocator_objects_unlocked(final(krnl).allc_2m_mp, final(lctx).thread_id()),
        allocator_objects_unlocked(old(krnl).allc_1g_mp, old(lctx).thread_id()) ==> allocator_objects_unlocked(final(krnl).allc_1g_mp, final(lctx).thread_id()),
        final(krnl).thr_mp.spec_index(target_thread).view() == old(krnl).thr_mp.spec_index(target_thread).view(),
        final(krnl).thr_mp.spec_index(source_thread).view() == old(krnl).thr_mp.spec_index(source_thread).view(),
        final(krnl).ctn_mp.dom().contains(target_container),
        final(krnl).ctn_mp.spec_index(target_container).view_rodata() == old(krnl).ctn_mp.spec_index(target_container).view_rodata(),
        final(krnl).prc_mp.dom().contains(target_process),
        final(krnl).prc_mp.spec_index(target_process).view_rodata() == old(krnl).prc_mp.spec_index(target_process).view_rodata(),
        final(krnl).pt_mp.spec_index(source_pagetable).view() == old(krnl).pt_mp.spec_index(source_pagetable).view(),
        final(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k() == old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k().insert(target_va, old(krnl).pt_mp.spec_index(source_pagetable).view().mapping_4k().spec_index(source_va)),
        final(krnl).pt_mp.spec_index(target_pagetable).view().mapping_2m() == old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_2m(),
        final(krnl).pt_mp.spec_index(target_pagetable).view().mapping_1g() == old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_1g(),
        final(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end,
        final(krnl).pt_mp.spec_index(target_pagetable).view().page_closure() == old(krnl).pt_mp.spec_index(target_pagetable).view().page_closure(),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger final(krnl).pt_mp.spec_index(target_pagetable)
                .view().spec_resolve_mapping_l2(l4i, l3i, l2i)]
            final(krnl).pt_mp.spec_index(target_pagetable).view()
                .kernel_l4_end <= l4i && pei_valid(l4i)
                && pei_valid(l3i) && pei_valid(l2i)
            ==> final(krnl).pt_mp.spec_index(target_pagetable).view()
                    .spec_resolve_mapping_l2(l4i, l3i, l2i)
                == old(krnl).pt_mp.spec_index(target_pagetable).view()
                    .spec_resolve_mapping_l2(l4i, l3i, l2i),
        {
            let page_ptr = old(krnl).pt_mp
                .spec_index(source_pagetable).view().mapping_4k()
                .spec_index(source_va).addr;
            final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr))
                .view().view().mappings().contains((target_pagetable, target_va))
        },
{
    let source_indices = va2index(source_va);
    proof {
        assert({
            &&& krnl.pt_mp.perms_wf()
            &&& krnl.pt_mp.spec_index(source_pagetable).inv()
            &&& krnl.pt_mp.spec_index(target_pagetable).inv()
        }) by { reveal(pagetable_perms_wf); };
    }
    let target_indices = va2index(target_va);
    proof {
        assert({
            &&& spec_index2va(source_indices) == source_va
            &&& krnl.pt_mp.spec_index(source_pagetable).view()
                .spec_resolve_mapping_4k_l1(source_indices.0, source_indices.1, source_indices.2, source_indices.3) is Some
        }) by {
            spec_va_4k_index_roundtrip();
            reveal(PageTable::wf_mapping_4k);
        };
    }
    let source_entry;
    {
        let source = krnl.pt_mp.borrow(source_pagetable, Tracked(source_pagetable_lock_perm));
        source_entry = source.resolve_mapping_4k_l1(source_indices.0, source_indices.1, source_indices.2, source_indices.3).2.unwrap();
    }
    let page_ptr = source_entry.addr;
    proof {
        assert({
            &&& source_entry =~= krnl.pt_mp
                .spec_index(source_pagetable).view().mapping_4k()
                .spec_index(source_va)
            &&& page_ptr_valid(page_ptr)
        }) by { reveal(PageTable::wf_mapping_4k); };
    }
    let page_index = page_ptr2page_index(page_ptr);
    let target_l1_ptr;
    {
        let target = krnl.pt_mp.borrow(target_pagetable, Tracked(target_pagetable_lock_perm));
        let l4_entry = target.get_entry_l4(target_indices.0).unwrap();
        let l3_entry = target.get_entry_l3(target_indices.0, target_indices.1, &l4_entry).unwrap();
        let l2_entry = target.get_entry_l2(target_indices.0, target_indices.1, target_indices.2, &l3_entry).unwrap();
        target_l1_ptr = l2_entry.addr;
    }

    proof {
        assert({
            &&& index_valid(NUM_PAGES, page_index)
            &&& krnl.pg_arr.spec_index(page_index).view().view().state
                is Mapped4k
            &&& !krnl.pg_arr.spec_index(page_index).view()
                .locked_by_thread(lctx.thread_id())
            &&& krnl.pg_arr.lock_id_by_index(page_index).major
                == MAPPED_PAGE_LOCK_MAJOR
            &&& lctx.lock_id_acyclic(krnl.pg_arr.lock_id_by_index(page_index))
        }) by {
            page_ptr_valid_imply_page_index_valid();
            reveal(mapped_4k_page_pagetable_wf); reveal(page_array_wf);
        };
    }
    let Tracked(page_lock_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));

    proof {
        assert({
            &&& krnl.pg_arr.inv()
            &&& krnl.pg_arr.spec_index(page_index).view().inv()
        }) by { reveal(page_array_wf); };
        assert({
            &&& !krnl.pg_arr.spec_index(page_index).view().view()
                .mappings().contains((target_pagetable, target_va))
            &&& krnl.pg_arr.spec_index(page_index).view().view().ref_count
                < usize::MAX
        }) by {
            reveal(mapped_4k_page_pagetable_wf);
            mapped_4k_page_ref_count_lt_usize_max(krnl.pt_mp, krnl.pg_arr, page_index);
        };
    }
    {
        let page = krnl.pg_arr.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(&page_lock_perm));
        add_4k_mapping(page, target_pagetable, target_va);
    }
    proof {
        assert(spec_index2va(target_indices) == target_va) by { spec_va_4k_index_roundtrip(); };
    }
    {
        let target = krnl.pt_mp.borrow_mut_typed(target_pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&mut *lctx), Tracked(target_pagetable_lock_perm));
        target.map_4k_page(target_indices.0,target_indices.1,target_indices.2,target_indices.3,target_l1_ptr,&source_entry,Tracked(&mut *lctx));
    }

    proof {
        assert(krnl.subsystems_inv()) by {
            assert(krnl.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
            assert(pagetable_perms_wf(krnl.pt_mp)) by { reveal(pagetable_perms_wf); };
            assert(page_array_wf(krnl.pg_arr)) by { reveal(page_array_wf); };
        };
        assert(krnl.memory_management_inv()) by {
            assert(allocator_pages_wf(krnl.pg_arr, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by {
                allocator_4k_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_4k_mp, krnl.allc_4k_mp);
                allocator_2m_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_2m_mp, krnl.allc_2m_mp);
                allocator_1g_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_1g_mp, krnl.allc_1g_mp);
            };
            assert(container_page_owner_wf(krnl.ctn_mp, krnl.pg_arr)) by { container_page_owner_wf_preserved_for_owning_container_eq(old(krnl).ctn_mp, krnl.ctn_mp, old(krnl).pg_arr, krnl.pg_arr); };
            assert(hugepage_2m_wf(krnl.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr); };
            assert(hugepage_1g_wf(krnl.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr); };
            assert(page_pagetable_wf(krnl.pt_mp, krnl.pg_arr)) by {
                assert({
                    let target_entry = krnl.pt_mp
                        .spec_index(target_pagetable).view().mapping_4k()
                        .spec_index(target_va);
                    target_entry.owning_container@
                        == krnl.pg_arr.spec_index(page_index)
                            .view().view().owning_container
                }) by { reveal(mapped_4k_page_pagetable_wf); };
                page_pagetable_wf_preserved_for_4k_mapping_insert(old(krnl).pt_mp, krnl.pt_mp, old(krnl).pg_arr, krnl.pg_arr, target_pagetable, page_ptr, target_va);
            };
            assert(container_process_page_pagetable_wf(krnl.ctn_mp, krnl.prc_mp, krnl.pt_mp, krnl.pg_arr)) by {
                assert({
                    let owner = krnl.pg_arr.spec_index(page_index)
                        .view().view().owning_container;
                    let mapping_process = krnl.pt_mp
                        .spec_index(target_pagetable).view().proc_ptr;
                    let mapping_container = krnl.prc_mp
                        .spec_index(mapping_process).view_rodata().view()
                        .owning_container;
                    &&& krnl.prc_mp.dom().contains(mapping_process)
                    &&& krnl.ctn_mp.dom().contains(owner)
                    &&& (mapping_container == owner
                        || krnl.ctn_mp.spec_index(owner).view()
                            .subtree_set.view().contains(mapping_container))
                }) by { reveal(mapped_4k_page_pagetable_wf); reveal(container_thread_wf); reveal(container_uppertree_seq_wf); };
                container_process_page_pagetable_wf_preserved_for_4k_mapping_insert(krnl.ctn_mp, krnl.prc_mp, old(krnl).pt_mp, krnl.pt_mp, old(krnl).pg_arr, krnl.pg_arr, target_pagetable, page_ptr, target_va);
            };
            assert(container_pages_wf(krnl.pg_arr, krnl.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).ctn_mp, krnl.ctn_mp); };
            assert(process_pages_wf(krnl.pg_arr, krnl.prc_mp)) by { process_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).prc_mp, krnl.prc_mp); };
            assert(pagetable_pages_wf(krnl.pt_mp, krnl.pg_arr)) by { reveal(pagetable_pages_wf); };
            assert(iommu_table_pages_wf(krnl.it_mp, krnl.pg_arr)) by { reveal(iommu_table_pages_wf); };
            assert(thread_pages_wf(krnl.thr_mp, krnl.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr); };
            assert(pcid_allocator_pages_wf(krnl.pg_arr, krnl.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).pcid_allc_mp, krnl.pcid_allc_mp); };
            assert(thread_staged_pages_wf(krnl.thr_mp, krnl.pg_arr)) by {
                reveal(thread_staged_pages_4k_wf);
                thread_staged_pages_2m_wf_preserved_for_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr);
                thread_staged_pages_1g_wf_preserved_for_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr);
            };
            assert(endpoint_pages_wf(krnl.ep_mp, krnl.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(old(krnl).ep_mp, krnl.ep_mp, old(krnl).pg_arr, krnl.pg_arr); };
            assert(process_pagetable_match(krnl.prc_mp, krnl.pt_mp)) by { reveal(process_pagetable_match); };
            assert(container_allocator_free_4k_page_wf(krnl.allc_4k_mp, krnl.pg_arr)) by { container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(krnl.allc_4k_mp, old(krnl).pg_arr, krnl.pg_arr, page_index); };
            assert(container_allocator_free_2m_page_wf(krnl.allc_2m_mp, krnl.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(krnl.allc_2m_mp, old(krnl).pg_arr, krnl.pg_arr, page_index); };
            assert(container_allocator_free_1g_page_wf(krnl.allc_1g_mp, krnl.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(krnl.allc_1g_mp, old(krnl).pg_arr, krnl.pg_arr, page_index); };
        };
        assert(cpu_dirty_map_wf(krnl.ctn_mp, krnl.prc_mp, krnl.cpu_arr, krnl.cpu_tlb, krnl.pt_mp)) by { reveal(cpu_dirty_map_contains_pagetable_pcid_match); };
        assert(tlb_wf_spec(krnl.cpu_tlb, krnl.pt_mp, krnl.cpu_arr)) by { tlb_wf_spec_preserved_for_4k_mapping_insert(krnl.cpu_tlb, krnl.cpu_arr, old(krnl).pt_mp, krnl.pt_mp, target_pagetable, target_va); };
        assert(kernel_k_to_kernel_u(*krnl) != kernel_k_to_kernel_u(*old(krnl))) by {
            assert({
                let process_ptr = target_process;
                &&& kernel_k_to_kernel_u(*old(krnl)).process_map.dom()
                    .contains(process_ptr)
                &&& kernel_k_to_kernel_u(*krnl).process_map.dom()
                    .contains(process_ptr)
                &&& !kernel_k_to_kernel_u(*old(krnl)).process_map
                    .spec_index(process_ptr).pagetable.mapping_4k.dom()
                    .contains(target_va)
                &&& kernel_k_to_kernel_u(*krnl).process_map
                    .spec_index(process_ptr).pagetable.mapping_4k.dom()
                    .contains(target_va)
            }) by { reveal(process_thread_wf); reveal(process_pagetable_match); };
        };
    }
    krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_lock_perm));
    proof {
        assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
            map_insert_remove_absent_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock {
                lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write,
            });
        };
        krnl.kernel_step_boundary(&mut *lctx, &mut *steps);
        assert(steps.steps.subrange(0, old(steps).steps.len() as int) == old(steps).steps) by { reveal(record_user_view_change); };
        assert({
            let source_process = old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr;
            &&& steps.steps.last().new_u.process_map.dom().contains(source_process)
            &&& kernel_k_to_kernel_u(*krnl).process_map.dom().contains(source_process)
            &&& steps.steps.last().new_u.process_map.spec_index(source_process).pagetable == kernel_k_to_kernel_u(*krnl).process_map.spec_index(source_process).pagetable
            &&& steps.steps.last().new_u.process_map.dom().contains(target_process)
            &&& old(krnl).prc_mp.spec_index(target_process).wlocked_by(old(lctx)) && {
                let iommu_table = old(krnl).prc_mp.spec_index(target_process).view().iommu_table;
                ||| iommu_table is None
                ||| iommu_table is Some && old(lctx).iommu_table_lock_map().dom().contains(iommu_table.unwrap())
            } ==> {
                &&& kernel_k_to_kernel_u(*krnl).process_map.dom().contains(target_process)
                &&& steps.steps.last().new_u.process_map.spec_index(target_process) == kernel_k_to_kernel_u(*krnl).process_map.spec_index(target_process)
            }
        }) by { reveal(record_user_view_change); reveal(kernel_k_to_kernel_u); reveal(process_pagetable_match); reveal(process_iommu_table_match); reveal(processes_rodata_unchanged); reveal(held_processes_unchanged); reveal(held_pagetables_unchanged); reveal(held_iommu_tables_unchanged); reveal(typed_lock_maps_aligned); reveal(LockedMap::typed_lock_map_aligned); };
        assert({
            &&& krnl.ctn_mp.dom().contains(target_container)
            &&& krnl.ctn_mp.spec_index(target_container).view_rodata()
                == old(krnl).ctn_mp.spec_index(target_container)
                    .view_rodata()
            &&& krnl.prc_mp.dom().contains(target_process)
            &&& krnl.prc_mp.spec_index(target_process).view_rodata()
                == old(krnl).prc_mp.spec_index(target_process)
                    .view_rodata()
        }) by { reveal(container_thread_wf); reveal(process_thread_wf); };
        assert({
            let mapped_page = krnl.pt_mp
                .spec_index(target_pagetable).view().mapping_4k()
                .spec_index(target_va).addr;
            krnl.pg_arr.spec_index(page_ptr2page_index(mapped_page))
                .view().view().mappings().contains((target_pagetable, target_va))
        }) by { reveal(mapped_4k_page_pagetable_wf); };
        assert(mmap_4k_allocation_ready(krnl, &*lctx)) by { reveal(LocalContext::holds_no_allocator_locks); };
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
    krnl: &mut KernelK,
    source_range: &VaRange4K,
    source_thread: RwLockThreadPtr,
    target_thread: RwLockThreadPtr,
    target_process: RwLockProcessPtr,
    target_container: RwLockContainerPtr,
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
        share_mapping_4k_held_context(old(krnl), old(lctx), source_thread, target_thread, target_process, target_container, source_pagetable, target_pagetable, source_thread_lock_perm, target_thread_lock_perm, source_pagetable_lock_perm, target_pagetable_lock_perm),
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).cpu_arr.spec_index(cpu_id).view().wlocked_by(old(lctx)),
        source_range.wf(),
        old(krnl).pt_mp.spec_index(source_pagetable).view().kernel_l4_end <= spec_va2index(source_range.start).0,
        share_mapping_4k_source_range_present(old(krnl), source_pagetable, source_range),
        old(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process,
        old(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        thread_objects_unlocked_except(old(krnl).thr_mp, old(lctx).thread_id(), set![source_thread, target_thread]),
        pagetable_objects_unlocked_except(old(krnl).pt_mp, old(lctx).thread_id(), set![source_pagetable, target_pagetable]),
    ensures
        share_mapping_4k_held_context(final(krnl), final(lctx), source_thread, target_thread, target_process, target_container, source_pagetable, target_pagetable, source_thread_lock_perm, target_thread_lock_perm, source_pagetable_lock_perm, target_pagetable_lock_perm),
        final(steps).steps.len() == old(steps).steps.len(),
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
        held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
        held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        allocator_objects_unlocked(old(krnl).allc_2m_mp, old(lctx).thread_id()) ==> allocator_objects_unlocked(final(krnl).allc_2m_mp, final(lctx).thread_id()),
        allocator_objects_unlocked(old(krnl).allc_1g_mp, old(lctx).thread_id()) ==> allocator_objects_unlocked(final(krnl).allc_1g_mp, final(lctx).thread_id()),
        thread_objects_unlocked_except(final(krnl).thr_mp, final(lctx).thread_id(), set![source_thread, target_thread]),
        pagetable_objects_unlocked_except(final(krnl).pt_mp, final(lctx).thread_id(), set![source_pagetable, target_pagetable]),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().wlocked_by(final(lctx)),
        final(krnl).cpu_arr.lock_id_by_index(cpu_id) == old(krnl).cpu_arr.lock_id_by_index(cpu_id),
        final(krnl).pt_mp.spec_index(source_pagetable).view() == old(krnl).pt_mp.spec_index(source_pagetable).view(),
        final(krnl).pt_mp.spec_index(target_pagetable).view() == old(krnl).pt_mp.spec_index(target_pagetable).view(),
        final(krnl).thr_mp.spec_index(source_thread).view() == old(krnl).thr_mp.spec_index(source_thread).view(),
        final(krnl).thr_mp.spec_index(target_thread).view() == old(krnl).thr_mp.spec_index(target_thread).view(),
        mmap_4k_allocation_ready(old(krnl), old(lctx)) ==> mmap_4k_allocation_ready(final(krnl), final(lctx)),
        share_mapping_4k_source_range_present(final(krnl), source_pagetable, source_range),
        ret == share_mapping_4k_range_owner_compatible(final(krnl), source_pagetable, target_thread, source_range),
{
    proof {
        assert({
            &&& krnl.thr_mp.perms_wf()
            &&& krnl.thr_mp.spec_index(target_thread).inv()
            &&& krnl.pt_mp.perms_wf()
            &&& krnl.pt_mp.spec_index(source_pagetable).view().wf()
        }) by { reveal(thread_perms_wf); reveal(pagetable_perms_wf); };
        assert(krnl.ctn_mp.dom().contains(target_container)) by { reveal(container_thread_wf); };
    }
    let mut i: usize = 0;
    let mut all_compatible = true;
    while i < source_range.len
        invariant
            share_mapping_4k_held_context(krnl, &*lctx, source_thread, target_thread, target_process, target_container, source_pagetable, target_pagetable, source_thread_lock_perm, target_thread_lock_perm, source_pagetable_lock_perm, target_pagetable_lock_perm),
            steps.snap_shot == kernel_k_to_kernel_u(*krnl),
            thread_objects_unlocked_except(krnl.thr_mp, lctx.thread_id(), set![source_thread, target_thread]),
            pagetable_objects_unlocked_except(krnl.pt_mp, lctx.thread_id(), set![source_pagetable, target_pagetable]),
            index_valid(NUM_CPUS, cpu_id),
            krnl.cpu_arr.spec_index(cpu_id).view()
                == old(krnl).cpu_arr.spec_index(cpu_id).view(),
            krnl.cpu_arr.spec_index(cpu_id).view().wlocked_by(&*lctx),
            krnl.cpu_arr.spec_index(cpu_id).view()
                .locked_by_thread(lctx.thread_id()),
            krnl.cpu_arr.lock_id_by_index(cpu_id)
                == old(krnl).cpu_arr.lock_id_by_index(cpu_id),
            source_range.wf(),
            krnl.pt_mp.spec_index(source_pagetable).view().wf(),
            krnl.pt_mp.spec_index(source_pagetable).view()
                .kernel_l4_end
                <= spec_va2index(source_range.start).0,
            share_mapping_4k_source_range_present(krnl, source_pagetable, source_range),
            0 <= i <= source_range.len,
            all_compatible
                == share_mapping_4k_range_owner_compatible_prefix(krnl, source_pagetable, target_thread, source_range, i as int),
            steps.steps.len() == old(steps).steps.len(),
            lctx.thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), lctx),
            held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx)),
            held_endpoints_unchanged(old(krnl).ep_mp, krnl.ep_mp, old(lctx)),
            held_schedulers_unchanged(old(krnl).sched_mp, krnl.sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, krnl.pcid_allc_mp, old(lctx)),
            held_iommu_tables_unchanged(old(krnl).it_mp, krnl.it_mp, old(lctx)),
            held_cpus_unchanged(old(krnl).cpu_arr, krnl.cpu_arr, old(lctx)),
            allocator_objects_unlocked(old(krnl).allc_2m_mp, old(lctx).thread_id()) ==> allocator_objects_unlocked(krnl.allc_2m_mp, lctx.thread_id()),
            allocator_objects_unlocked(old(krnl).allc_1g_mp, old(lctx).thread_id()) ==> allocator_objects_unlocked(krnl.allc_1g_mp, lctx.thread_id()),
            old(krnl).pt_mp.dom().contains(source_pagetable),
            old(krnl).thr_mp.dom().contains(target_thread),
            krnl.pt_mp.spec_index(source_pagetable).view()
                == old(krnl).pt_mp
                    .spec_index(source_pagetable).view(),
            krnl.pt_mp.spec_index(target_pagetable).view()
                == old(krnl).pt_mp
                    .spec_index(target_pagetable).view(),
            krnl.thr_mp.spec_index(target_thread).view()
                == old(krnl).thr_mp.spec_index(target_thread).view(),
            krnl.thr_mp.spec_index(source_thread).view()
                == old(krnl).thr_mp.spec_index(source_thread).view(),
            mmap_4k_allocation_ready(old(krnl), old(lctx)) ==>
                mmap_4k_allocation_ready(krnl, &*lctx),
            krnl.thr_mp.spec_index(target_thread).view().owning_proc == target_process,
            krnl.thr_mp.spec_index(target_thread).view().owning_container == target_container,
        decreases source_range.len - i,
    {
        let source_va = source_range.index(i);
        let source_indices = va2index(source_va);
        proof {
            assert({
                &&& krnl.pt_mp.perms_wf()
                &&& krnl.pt_mp.spec_index(source_pagetable).inv()
            }) by { reveal(pagetable_perms_wf); };
            assert({
                &&& spec_index2va(source_indices) == source_va
                &&& krnl.pt_mp.spec_index(source_pagetable).view()
                    .spec_resolve_mapping_4k_l1(source_indices.0, source_indices.1, source_indices.2, source_indices.3) is Some
            }) by {
                spec_va_4k_index_roundtrip();
                reveal(PageTable::wf_mapping_4k);
                seq_index_lemma::<VAddr>();
                source_range.va_range_lemma();
            };
        }
        let source_entry;
        {
            let source = krnl.pt_mp.borrow(source_pagetable, Tracked(source_pagetable_lock_perm));
            source_entry = source.resolve_mapping_4k_l1(source_indices.0, source_indices.1, source_indices.2, source_indices.3).2.unwrap();
        }
        let page_ptr = source_entry.addr;
        let page_index = page_ptr2page_index(page_ptr);
        proof {
            assert({
                &&& source_entry =~= krnl.pt_mp
                    .spec_index(source_pagetable).view().mapping_4k()
                    .spec_index(source_va)
                &&& page_ptr_valid(page_ptr)
                &&& index_valid(NUM_PAGES, page_index)
                &&& !krnl.pg_arr.spec_index(page_index).view()
                    .locked_by_thread(lctx.thread_id())
                &&& krnl.pg_arr.lock_id_by_index(page_index).major
                    == MAPPED_PAGE_LOCK_MAJOR
                &&& lctx.lock_id_acyclic(krnl.pg_arr.lock_id_by_index(page_index))
            }) by {
                reveal(PageTable::wf_mapping_4k);
                seq_index_lemma::<VAddr>();
                source_range.va_range_lemma();
                page_ptr_valid_imply_page_index_valid();
                reveal(page_array_wf);
            };
        }
        let Tracked(page_lock_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));

        let page_owner;
        {
            proof {
                assert(krnl.pg_arr.inv()) by { reveal(page_array_wf); };
            }
            let page = krnl.pg_arr.borrow(page_index, Tracked(&page_lock_perm));
            page_owner = page.owning_container;
        }

        let page_compatible;
        if page_owner == target_container {
            page_compatible = true;
        } else {
            proof {
                assert({
                    &&& container_perms_wf(krnl.ctn_mp)
                    &&& container_tree_wf(krnl.rt_ctn, krnl.ctn_mp)
                    &&& krnl.ctn_mp.dom().contains(page_owner)
                    &&& krnl.ctn_mp.dom().contains(target_container)
                }) by { reveal(container_page_owner_wf); reveal(container_thread_wf); };
            }
            page_compatible = container_tree_check_is_ancestor(krnl.rt_ctn, &krnl.ctn_mp, page_owner, target_container);
        }
        proof {
            assert(page_compatible == share_mapping_4k_leaf_owner_compatible(krnl, source_pagetable, target_thread, source_va)) by { reveal(mapped_4k_page_pagetable_wf); reveal(container_thread_wf); };
        }
        krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_lock_perm));
        proof {
            assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
                map_insert_remove_absent_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock {
                    lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write,
                });
            };
            krnl.kernel_step_boundary(&mut *lctx, &mut *steps);
            assert(share_mapping_4k_held_context(krnl, &*lctx, source_thread, target_thread, target_process, target_container, source_pagetable, target_pagetable, source_thread_lock_perm, target_thread_lock_perm, source_pagetable_lock_perm, target_pagetable_lock_perm)) by { reveal(container_thread_wf); reveal(process_thread_wf); reveal(process_pagetable_match); };
            assert(mmap_4k_allocation_ready(old(krnl), old(lctx)) ==> mmap_4k_allocation_ready(krnl, &*lctx)) by { reveal(LocalContext::holds_no_allocator_locks); };
            assert(share_mapping_4k_source_range_present(krnl, source_pagetable, source_range)) by {
                reveal(pagetable_perms_wf); reveal(mapped_4k_page_pagetable_wf);
                page_ptr_valid_imply_page_index_valid();
            };
            assert(page_compatible == share_mapping_4k_leaf_owner_compatible(krnl, source_pagetable, target_thread, source_va)) by {
                reveal(pagetable_perms_wf); reveal(mapped_4k_page_pagetable_wf); reveal(container_page_owner_wf);
            };
            assert(all_compatible == share_mapping_4k_range_owner_compatible_prefix(krnl, source_pagetable, target_thread, source_range, i as int)) by {
                reveal(pagetable_perms_wf); reveal(mapped_4k_page_pagetable_wf); reveal(container_page_owner_wf);
            };
        }
        all_compatible = all_compatible && page_compatible;
        proof {
            assert(all_compatible == share_mapping_4k_range_owner_compatible_prefix(krnl, source_pagetable, target_thread, source_range, (i + 1) as int)) by {
                assert(share_mapping_4k_range_owner_compatible_prefix(krnl, source_pagetable, target_thread, source_range, (i + 1) as int) == (share_mapping_4k_range_owner_compatible_prefix(krnl, source_pagetable, target_thread, source_range, i as int) && share_mapping_4k_leaf_owner_compatible(krnl, source_pagetable, target_thread, source_va))) by {
                    seq_index_lemma::<VAddr>();
                    source_range.va_range_lemma();
                };
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
    krnl: &mut KernelK,
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
        share_mapping_4k_held_context(old(krnl), old(lctx), source_thread, target_thread, target_process, target_container, source_pagetable, target_pagetable, source_thread_lock_perm, target_thread_lock_perm, source_pagetable_lock_perm, target_pagetable_lock_perm),
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).cpu_arr.spec_index(cpu_id).view().wlocked_by(old(lctx)),
        old(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        old(krnl).prc_mp.dom().contains(target_process),
        old(krnl).ctn_mp.dom().contains(target_container),
        mmap_4k_allocation_ready(old(krnl), old(lctx)),
        thread_objects_unlocked_except(old(krnl).thr_mp, old(lctx).thread_id(), set![source_thread, target_thread]),
        pagetable_objects_unlocked_except(old(krnl).pt_mp, old(lctx).thread_id(), set![source_pagetable, target_pagetable]),
        source_range.wf(),
        old(krnl).pt_mp.spec_index(source_pagetable).view().wf(),
        old(krnl).pt_mp.spec_index(source_pagetable).view().kernel_l4_end <= spec_va2index(source_range.start).0,
        target_range.wf(),
        source_range.len == target_range.len,
        share_mapping_4k_source_range_present(old(krnl), source_pagetable, source_range),
        share_mapping_4k_range_structure_ready_from(old(krnl), source_pagetable, target_pagetable, source_range, target_range, 0),
        share_mapping_4k_range_owner_compatible(old(krnl), source_pagetable, target_thread, source_range),
    ensures
        share_mapping_4k_held_context(final(krnl), final(lctx), source_thread, target_thread, target_process, target_container, source_pagetable, target_pagetable, source_thread_lock_perm, target_thread_lock_perm, source_pagetable_lock_perm, target_pagetable_lock_perm),
        final(steps).steps.len() == old(steps).steps.len() + source_range.len,
        final(steps).steps.subrange(0, old(steps).steps.len() as int) == old(steps).steps,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(krnl).pt_mp.spec_index(source_pagetable).view() == old(krnl).pt_mp.spec_index(source_pagetable).view(),
        final(krnl).thr_mp.spec_index(source_thread).view() == old(krnl).thr_mp.spec_index(source_thread).view(),
        final(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k() == share_mapping_4k_target_map_after(old(krnl).pt_mp.spec_index(source_pagetable).view().mapping_4k(), old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k(), source_range, target_range, source_range.len as nat),
        share_mapping_4k_range_mapped_prefix(final(krnl).pt_mp.spec_index(target_pagetable).view(), target_range, source_range.len as int),
        final(krnl).pt_mp.spec_index(target_pagetable).view().mapping_2m() == old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_2m(),
        final(krnl).pt_mp.spec_index(target_pagetable).view().mapping_1g() == old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_1g(),
        final(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end,
        final(krnl).pt_mp.spec_index(target_pagetable).view().page_closure() == old(krnl).pt_mp.spec_index(target_pagetable).view().page_closure(),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger final(krnl).pt_mp.spec_index(target_pagetable)
                .view().spec_resolve_mapping_l2(l4i, l3i, l2i)]
            final(krnl).pt_mp.spec_index(target_pagetable).view()
                .kernel_l4_end <= l4i && pei_valid(l4i)
                && pei_valid(l3i) && pei_valid(l2i)
            ==> final(krnl).pt_mp.spec_index(target_pagetable).view()
                    .spec_resolve_mapping_l2(l4i, l3i, l2i)
                == old(krnl).pt_mp.spec_index(target_pagetable).view()
                    .spec_resolve_mapping_l2(l4i, l3i, l2i),
        share_mapping_4k_reverse_mappings(final(krnl), target_pagetable, target_range),
{
    let mut i: usize = 0;
    while i < source_range.len
        invariant
            share_mapping_4k_held_context(krnl, &*lctx, source_thread, target_thread, target_process, target_container, source_pagetable, target_pagetable, source_thread_lock_perm, target_thread_lock_perm, source_pagetable_lock_perm, target_pagetable_lock_perm),
            steps.snap_shot == kernel_k_to_kernel_u(*krnl),
            index_valid(NUM_CPUS, cpu_id),
            krnl.cpu_arr.spec_index(cpu_id).view().wlocked_by(&*lctx),
            krnl.cpu_arr.spec_index(cpu_id).view()
                .locked_by_thread(lctx.thread_id()),
            mmap_4k_allocation_ready(krnl, &*lctx),
            thread_objects_unlocked_except(krnl.thr_mp, lctx.thread_id(), set![source_thread, target_thread]),
            pagetable_objects_unlocked_except(krnl.pt_mp, lctx.thread_id(), set![source_pagetable, target_pagetable]),
            source_range.wf(),
            krnl.pt_mp.spec_index(source_pagetable).view().wf(),
            krnl.pt_mp.spec_index(source_pagetable).view()
                .kernel_l4_end
                <= spec_va2index(source_range.start).0,
            target_range.wf(),
            source_range.len == target_range.len,
            0 <= i <= source_range.len,
            steps.steps.len() == old(steps).steps.len() + i,
            steps.steps.subrange(0, old(steps).steps.len() as int) == old(steps).steps,
            lctx.thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), lctx),
            old(krnl).pt_mp.dom().contains(source_pagetable),
            old(krnl).pt_mp.dom().contains(target_pagetable),
            krnl.prc_mp.dom().contains(target_process),
            krnl.ctn_mp.dom().contains(target_container),
            krnl.thr_mp.spec_index(target_thread).view().owning_container
                == target_container,
            krnl.pt_mp.spec_index(source_pagetable).view()
                == old(krnl).pt_mp
                    .spec_index(source_pagetable).view(),
            krnl.thr_mp.spec_index(source_thread).view()
                == old(krnl).thr_mp.spec_index(source_thread).view(),
            share_mapping_4k_source_range_present(krnl, source_pagetable, source_range),
            share_mapping_4k_range_owner_compatible(krnl, source_pagetable, target_thread, source_range),
            share_mapping_4k_range_structure_ready_from(krnl, source_pagetable, target_pagetable, source_range, target_range, i as int),
            krnl.pt_mp.spec_index(target_pagetable).view()
                .mapping_4k()
                == share_mapping_4k_target_map_after(old(krnl).pt_mp.spec_index(source_pagetable).view().mapping_4k(), old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k(), source_range, target_range, i as nat),
            share_mapping_4k_range_mapped_prefix(krnl.pt_mp.spec_index(target_pagetable).view(), target_range, i as int),
            krnl.pt_mp.spec_index(target_pagetable).view().mapping_2m()
                == old(krnl).pt_mp.spec_index(target_pagetable).view()
                    .mapping_2m(),
            krnl.pt_mp.spec_index(target_pagetable).view().mapping_1g()
                == old(krnl).pt_mp.spec_index(target_pagetable).view()
                    .mapping_1g(),
            krnl.pt_mp.spec_index(target_pagetable).view().kernel_l4_end
                == old(krnl).pt_mp.spec_index(target_pagetable).view()
                    .kernel_l4_end,
            krnl.pt_mp.spec_index(target_pagetable).view().page_closure()
                == old(krnl).pt_mp.spec_index(target_pagetable).view()
                    .page_closure(),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger krnl.pt_mp.spec_index(target_pagetable)
                    .view().spec_resolve_mapping_l2(l4i, l3i, l2i)]
                krnl.pt_mp.spec_index(target_pagetable).view()
                    .kernel_l4_end <= l4i && pei_valid(l4i)
                    && pei_valid(l3i) && pei_valid(l2i)
                ==> krnl.pt_mp.spec_index(target_pagetable).view()
                        .spec_resolve_mapping_l2(l4i, l3i, l2i)
                    == old(krnl).pt_mp.spec_index(target_pagetable)
                        .view().spec_resolve_mapping_l2(l4i, l3i, l2i),
        decreases source_range.len - i,
    {
        let source_va = source_range.index(i);
        let target_va = target_range.index(i);
        proof {
            assert(share_mapping_4k_leaf_ready(krnl, source_pagetable, target_pagetable, target_thread, source_va, target_va)) by {
                assert(share_mapping_4k_leaf_structure_ready(krnl, source_pagetable, target_pagetable, source_va, target_va)) by {
                    seq_index_lemma::<VAddr>();
                    source_range.va_range_lemma();
                    target_range.va_range_lemma();
                    reveal(PageTable::wf_mapping_4k);
                };
                assert(share_mapping_4k_leaf_owner_compatible(krnl, source_pagetable, target_thread, source_va)) by {
                    seq_index_lemma::<VAddr>();
                    source_range.va_range_lemma();
                };
            };
        }
        share_one_mapping_4k(krnl, source_thread, target_thread, target_process, target_container, source_pagetable, target_pagetable, cpu_id, source_va, target_va, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(source_thread_lock_perm), Tracked(target_thread_lock_perm), Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm));
        proof {
            assert(steps.steps.subrange(0, old(steps).steps.len() as int) == old(steps).steps) by {
                vstd::seq::lemma_seq_subrange_composition(steps.steps, 0, (steps.steps.len() - 1) as int, 0, old(steps).steps.len() as int);
            };
            assert(share_mapping_4k_source_range_present(krnl, source_pagetable, source_range)) by {
                reveal(pagetable_perms_wf); reveal(mapped_4k_page_pagetable_wf);
                page_ptr_valid_imply_page_index_valid();
            };
            assert(share_mapping_4k_range_owner_compatible(krnl, source_pagetable, target_thread, source_range)) by {
                reveal(pagetable_perms_wf); reveal(mapped_4k_page_pagetable_wf); reveal(container_page_owner_wf);
            };
            assert(krnl.pt_mp.spec_index(target_pagetable).view().wf()) by { reveal(pagetable_perms_wf); };
            assert(share_mapping_4k_range_structure_ready_from(krnl, source_pagetable, target_pagetable, source_range, target_range, (i + 1) as int)) by {
                seq_index_lemma::<VAddr>();
                source_range.va_range_lemma();
                target_range.va_range_lemma();
            };
            assert(krnl.pt_mp.spec_index(target_pagetable).view().mapping_4k() == share_mapping_4k_target_map_after(old(krnl).pt_mp.spec_index(source_pagetable).view().mapping_4k(), old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k(), source_range, target_range, (i + 1) as nat)) by {
                    source_range.va_range_lemma();
                    target_range.va_range_lemma();
                };
            assert(share_mapping_4k_range_mapped_prefix(krnl.pt_mp.spec_index(target_pagetable).view(), target_range, (i + 1) as int)) by {
                seq_index_lemma::<VAddr>();
                target_range.va_range_lemma();
            };
        }
        i = i + 1;
    }
    proof {
        assert(share_mapping_4k_reverse_mappings(krnl, target_pagetable, target_range)) by {
            seq_index_lemma::<VAddr>();
            source_range.va_range_lemma();
            target_range.va_range_lemma();
            page_ptr_valid_imply_page_index_valid();
            reveal(pagetable_perms_wf); reveal(mapped_4k_page_pagetable_wf);
        };
    }
}

/// Build each missing target directory path and immediately share its 4K leaf.
/// All fallible checks are completed by the caller before this function starts.
#[verifier::spinoff_prover]
pub fn share_mapping_4k_build_and_share(
    krnl: &mut KernelK,
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
        share_mapping_4k_held_context(old(krnl), old(lctx), source_thread, target_thread, target_process, target_container, source_pagetable, target_pagetable, source_thread_lock_perm, target_thread_lock_perm, source_pagetable_lock_perm, target_pagetable_lock_perm),
        mmap_4k_held_context(old(krnl), old(lctx), target_allocator, target_thread, target_process, target_container, cpu_id, target_pagetable, target_thread_lock_perm, target_pagetable_lock_perm),
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        mmap_4k_allocation_ready(old(krnl), old(lctx)),
        thread_objects_unlocked_except(old(krnl).thr_mp, old(lctx).thread_id(), set![source_thread, target_thread]),
        pagetable_objects_unlocked_except(old(krnl).pt_mp, old(lctx).thread_id(), set![source_pagetable, target_pagetable]),
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        source_range.len <= usize::MAX / 3usize,
        old(krnl).pt_mp.spec_index(source_pagetable).view().wf(),
        old(krnl).pt_mp.spec_index(source_pagetable).view().kernel_l4_end <= spec_v2l4index(source_range.start),
        share_mapping_4k_source_range_present(old(krnl), source_pagetable, source_range),
        share_mapping_4k_range_owner_compatible(old(krnl), source_pagetable, target_thread, source_range),
        old(krnl).thr_mp.spec_index(target_thread).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(target_thread).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(target_thread).view().quota_4k >= 3 * target_range.len,
        old(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end <= spec_v2l4index(target_range.start),
        old(krnl).pt_mp.spec_index(target_pagetable).view().spec_mapping_4k_va_range_empty(target_range.start, target_range.view().spec_index((target_range.len - 1) as int)),
        old(krnl).pt_mp.spec_index(target_pagetable).view().is_empty() || old(krnl).pt_mp.spec_index(target_pagetable).view().spec_mapping_4k_va_range_buildable(target_range),
    ensures
        share_mapping_4k_held_context(final(krnl), final(lctx), source_thread, target_thread, target_process, target_container, source_pagetable, target_pagetable, source_thread_lock_perm, target_thread_lock_perm, source_pagetable_lock_perm, target_pagetable_lock_perm),
        mmap_4k_held_context(final(krnl), final(lctx), target_allocator, target_thread, target_process, target_container, cpu_id, target_pagetable, target_thread_lock_perm, target_pagetable_lock_perm),
        mmap_4k_allocation_ready(final(krnl), final(lctx)),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
        held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
        held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        allocator_objects_unlocked(old(krnl).allc_2m_mp, old(lctx).thread_id()) ==> allocator_objects_unlocked(final(krnl).allc_2m_mp, final(lctx).thread_id()),
        allocator_objects_unlocked(old(krnl).allc_1g_mp, old(lctx).thread_id()) ==> allocator_objects_unlocked(final(krnl).allc_1g_mp, final(lctx).thread_id()),
        thread_objects_unlocked_except(final(krnl).thr_mp, final(lctx).thread_id(), set![source_thread, target_thread]),
        pagetable_objects_unlocked_except(final(krnl).pt_mp, final(lctx).thread_id(), set![source_pagetable, target_pagetable]),
        final(steps).steps.len() == old(steps).steps.len() + source_range.len,
        final(steps).steps.subrange(0, old(steps).steps.len() as int) == old(steps).steps,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        {
            let source_process = old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr;
            &&& final(steps).steps.last().new_u.process_map.dom().contains(source_process)
            &&& kernel_k_to_kernel_u(*final(krnl)).process_map.dom().contains(source_process)
            &&& final(steps).steps.last().new_u.process_map.spec_index(source_process).pagetable == kernel_k_to_kernel_u(*final(krnl)).process_map.spec_index(source_process).pagetable
            &&& final(steps).steps.last().new_u.process_map.dom().contains(target_process)
            &&& old(krnl).prc_mp.spec_index(target_process).wlocked_by(old(lctx)) && {
                let iommu_table = old(krnl).prc_mp.spec_index(target_process).view().iommu_table;
                ||| iommu_table is None
                ||| iommu_table is Some && old(lctx).iommu_table_lock_map().dom().contains(iommu_table.unwrap())
            } ==> {
                &&& kernel_k_to_kernel_u(*final(krnl)).process_map.dom().contains(target_process)
                &&& final(steps).steps.last().new_u.process_map.spec_index(target_process) == kernel_k_to_kernel_u(*final(krnl)).process_map.spec_index(target_process)
            }
        },
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(krnl).thr_mp.lock_id_by_key(target_thread) == old(krnl).thr_mp.lock_id_by_key(target_thread),
        final(krnl).pt_mp.spec_index(source_pagetable).view() == old(krnl).pt_mp.spec_index(source_pagetable).view(),
        source_thread != target_thread ==> final(krnl).thr_mp.spec_index(source_thread).view() == old(krnl).thr_mp.spec_index(source_thread).view(),
        final(krnl).thr_mp.spec_index(target_thread).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(target_thread).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(target_thread).view().owning_proc == old(krnl).thr_mp.spec_index(target_thread).view().owning_proc,
        final(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr,
        final(krnl).thr_mp.spec_index(target_thread).view().state == old(krnl).thr_mp.spec_index(target_thread).view().state,
        final(krnl).thr_mp.spec_index(target_thread).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(target_thread).view().blocking_endpoint_ptr,
        final(krnl).thr_mp.spec_index(target_thread).view().quota_4k <= old(krnl).thr_mp.spec_index(target_thread).view().quota_4k,
        final(krnl).thr_mp.spec_index(target_thread).view().quota_4k >= old(krnl).thr_mp.spec_index(target_thread).view().quota_4k - 3 * target_range.len,
        final(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k() == share_mapping_4k_target_map_after(old(krnl).pt_mp.spec_index(source_pagetable).view().mapping_4k(), old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k(), source_range, target_range, source_range.len as nat),
        share_mapping_4k_range_mapped_prefix(final(krnl).pt_mp.spec_index(target_pagetable).view(), target_range, source_range.len as int),
        final(krnl).pt_mp.spec_index(target_pagetable).view().mapping_2m() == old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_2m(),
        final(krnl).pt_mp.spec_index(target_pagetable).view().mapping_1g() == old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_1g(),
        final(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end,
        share_mapping_4k_reverse_mappings(final(krnl), target_pagetable, target_range),
{
    let target_range_start = target_range.start;
    proof {
        assert({
            &&& krnl.pt_mp.spec_index(source_pagetable).view().wf()
            &&& krnl.pt_mp.spec_index(target_pagetable).view().wf()
            &&& krnl.pt_mp.spec_index(target_pagetable).view()
                .wf_mapping_1g()
            &&& krnl.pt_mp.spec_index(target_pagetable).view()
                .wf_mapping_2m()
            &&& krnl.pt_mp.spec_index(target_pagetable).view()
                .wf_mapping_4k()
        }) by { reveal(pagetable_perms_wf); };
        assert(share_mapping_4k_target_range_empty_from(krnl.pt_mp.spec_index(target_pagetable).view(), target_range, 0)) by {
            reveal(PageTable::spec_mapping_4k_va_range_empty);
            target_range.va_range_lemma();
        };
    }
    let mut i: usize = 0;
    while i < source_range.len
        invariant
            share_mapping_4k_held_context(krnl, &*lctx, source_thread, target_thread, target_process, target_container, source_pagetable, target_pagetable, source_thread_lock_perm, target_thread_lock_perm, source_pagetable_lock_perm, target_pagetable_lock_perm),
            mmap_4k_held_context(krnl, &*lctx, target_allocator, target_thread, target_process, target_container, cpu_id, target_pagetable, target_thread_lock_perm, target_pagetable_lock_perm),
            steps.snap_shot == kernel_k_to_kernel_u(*krnl),
            mmap_4k_allocation_ready(krnl, &*lctx),
            held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx)),
            held_endpoints_unchanged(old(krnl).ep_mp, krnl.ep_mp, old(lctx)),
            held_schedulers_unchanged(old(krnl).sched_mp, krnl.sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, krnl.pcid_allc_mp, old(lctx)),
            held_iommu_tables_unchanged(old(krnl).it_mp, krnl.it_mp, old(lctx)),
            held_cpus_unchanged(old(krnl).cpu_arr, krnl.cpu_arr, old(lctx)),
            allocator_objects_unlocked(old(krnl).allc_2m_mp, old(lctx).thread_id()) ==> allocator_objects_unlocked(krnl.allc_2m_mp, lctx.thread_id()),
            allocator_objects_unlocked(old(krnl).allc_1g_mp, old(lctx).thread_id()) ==> allocator_objects_unlocked(krnl.allc_1g_mp, lctx.thread_id()),
            krnl.cpu_arr.spec_index(cpu_id).view()
                .locked_by_thread(lctx.thread_id()),
            thread_objects_unlocked_except(krnl.thr_mp, lctx.thread_id(), set![source_thread, target_thread]),
            pagetable_objects_unlocked_except(krnl.pt_mp, lctx.thread_id(), set![source_pagetable, target_pagetable]),
            source_range.wf(),
            target_range.wf(),
            source_range.len == target_range.len,
            source_range.len > 0,
            source_range.len <= usize::MAX / 3usize,
            target_range_start == target_range.start,
            0 <= i <= source_range.len,
            steps.steps.len() == old(steps).steps.len() + i,
            steps.steps.subrange(0, old(steps).steps.len() as int) == old(steps).steps,
            i > 0 ==> {
                let source_process = old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr;
                &&& steps.steps.last().new_u.process_map.dom().contains(source_process)
                &&& kernel_k_to_kernel_u(*krnl).process_map.dom().contains(source_process)
                &&& steps.steps.last().new_u.process_map.spec_index(source_process).pagetable == kernel_k_to_kernel_u(*krnl).process_map.spec_index(source_process).pagetable
                &&& old(krnl).prc_mp.dom().contains(target_process)
                &&& steps.steps.last().new_u.process_map.dom().contains(target_process)
                &&& old(krnl).prc_mp.spec_index(target_process).wlocked_by(old(lctx)) && {
                    let iommu_table = old(krnl).prc_mp.spec_index(target_process).view().iommu_table;
                    ||| iommu_table is None
                    ||| iommu_table is Some && old(lctx).iommu_table_lock_map().dom().contains(iommu_table.unwrap())
                } ==> {
                    &&& kernel_k_to_kernel_u(*krnl).process_map.dom().contains(target_process)
                    &&& steps.steps.last().new_u.process_map.spec_index(target_process) == kernel_k_to_kernel_u(*krnl).process_map.spec_index(target_process)
                }
            },
            lctx.thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), lctx),
            krnl.thr_mp.lock_id_by_key(target_thread)
                == old(krnl).thr_mp.lock_id_by_key(target_thread),
            old(krnl).thr_mp.dom().contains(source_thread),
            old(krnl).thr_mp.dom().contains(target_thread),
            old(krnl).prc_mp.dom().contains(target_process),
            old(krnl).pt_mp.dom().contains(source_pagetable),
            old(krnl).pt_mp.dom().contains(target_pagetable),
            krnl.pt_mp.spec_index(source_pagetable).view()
                == old(krnl).pt_mp.spec_index(source_pagetable).view(),
            source_thread != target_thread ==> krnl.thr_mp.spec_index(source_thread).view()
                == old(krnl).thr_mp.spec_index(source_thread).view(),
            krnl.pt_mp.spec_index(source_pagetable).view().wf(),
            krnl.pt_mp.spec_index(source_pagetable).view()
                .kernel_l4_end <= spec_v2l4index(source_range.start),
            krnl.thr_mp.spec_index(target_thread).view()
                .upper_container_seq
                == old(krnl).thr_mp.spec_index(target_thread).view()
                    .upper_container_seq,
            krnl.thr_mp.spec_index(target_thread).view().owning_proc
                == old(krnl).thr_mp.spec_index(target_thread).view().owning_proc,
            krnl.thr_mp.spec_index(target_thread).view().proc_pagetable_ptr
                == old(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr,
            krnl.thr_mp.spec_index(target_thread).view().state
                == old(krnl).thr_mp.spec_index(target_thread).view().state,
            krnl.thr_mp.spec_index(target_thread).view()
                .blocking_endpoint_ptr
                == old(krnl).thr_mp.spec_index(target_thread).view()
                    .blocking_endpoint_ptr,
            share_mapping_4k_source_range_present(krnl, source_pagetable, source_range),
            share_mapping_4k_range_owner_compatible(krnl, source_pagetable, target_thread, source_range),
            krnl.thr_mp.spec_index(target_thread).view().temp_alloc_clean(),
            krnl.thr_mp.spec_index(target_thread).view()
                .free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(target_thread).view().quota_4k
                >= 3 * target_range.len,
            krnl.thr_mp.spec_index(target_thread).view().quota_4k
                >= 3 * (target_range.len - i),
            krnl.thr_mp.spec_index(target_thread).view().quota_4k
                >= old(krnl).thr_mp.spec_index(target_thread).view().quota_4k
                    - 3 * i,
            krnl.thr_mp.spec_index(target_thread).view().quota_4k
                <= old(krnl).thr_mp.spec_index(target_thread).view().quota_4k,
            krnl.pt_mp.spec_index(target_pagetable).view().wf(),
            old(krnl).pt_mp.spec_index(target_pagetable).view().wf(),
            krnl.pt_mp.spec_index(target_pagetable).view().kernel_l4_end
                == old(krnl).pt_mp.spec_index(target_pagetable).view()
                    .kernel_l4_end,
            krnl.pt_mp.spec_index(target_pagetable).view().kernel_l4_end
                <= spec_v2l4index(target_range.start),
            krnl.pt_mp.spec_index(target_pagetable).view().mapping_2m()
                == old(krnl).pt_mp.spec_index(target_pagetable).view()
                    .mapping_2m(),
            krnl.pt_mp.spec_index(target_pagetable).view().mapping_1g()
                == old(krnl).pt_mp.spec_index(target_pagetable).view()
                    .mapping_1g(),
            old(krnl).pt_mp.spec_index(target_pagetable).view()
                .wf_mapping_1g(),
            old(krnl).pt_mp.spec_index(target_pagetable).view()
                .wf_mapping_2m(),
            old(krnl).pt_mp.spec_index(target_pagetable).view()
                .wf_mapping_4k(),
            old(krnl).pt_mp.spec_index(target_pagetable).view().is_empty()
                || old(krnl).pt_mp.spec_index(target_pagetable).view()
                    .spec_mapping_4k_va_range_buildable(target_range),
            krnl.pt_mp.spec_index(target_pagetable).view().mapping_4k()
                == share_mapping_4k_target_map_after(old(krnl).pt_mp.spec_index(source_pagetable).view().mapping_4k(), old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k(), source_range, target_range, i as nat),
            share_mapping_4k_range_mapped_prefix(krnl.pt_mp.spec_index(target_pagetable).view(), target_range, i as int),
            share_mapping_4k_target_range_empty_from(krnl.pt_mp.spec_index(target_pagetable).view(), target_range, i as int),
        decreases source_range.len - i,
    {
        let source_va = source_range.index(i);
        let target_va = target_range.index(i);
        proof {
            assert({
                &&& spec_va_4k_valid(target_range_start)
                &&& spec_va_4k_valid(target_va)
                &&& target_range_start <= target_va
                &&& va_4k_valid(target_va)
            }) by { target_range.va_range_lemma(); };
            assert(spec_v2l4index(target_range_start) <= spec_v2l4index(target_va)) by (bit_vector)
                requires
                    spec_va_4k_valid(target_range_start),
                    spec_va_4k_valid(target_va),
                    target_range_start <= target_va,
            ;
            assert(krnl.pt_mp.spec_index(target_pagetable).view().kernel_l4_end <= spec_v2l4index(target_va)) by { target_range.va_range_lemma(); };
            assert({
                &&& pei_valid(spec_v2l4index(target_va))
                &&& pei_valid(spec_v2l3index(target_va))
                &&& pei_valid(spec_v2l2index(target_va))
                &&& pei_valid(spec_v2l1index(target_va))
            }) by { spec_va_4k_valid_imply_indices_valid(); };
            assert(old(krnl).pt_mp.spec_index(target_pagetable).view().spec_4k_entry_useable(spec_v2l4index(target_va), spec_v2l3index(target_va), spec_v2l2index(target_va), spec_v2l1index(target_va))) by {
                target_range.va_range_lemma();
                seq_index_lemma::<VAddr>();
                if old(krnl).pt_mp.spec_index(target_pagetable).view().is_empty() {
                    spec_va_4k_index_roundtrip();
                    reveal(PageTable::is_empty); reveal(PageTable::wf_mapping_1g); reveal(PageTable::wf_mapping_2m); reveal(PageTable::wf_mapping_4k); reveal(PageTable::spec_4k_entry_useable);
                } else {
                    assert(old(krnl).pt_mp.spec_index(target_pagetable).view().spec_resolve_mapping_4k_l1(spec_va2index(target_range.view().spec_index(i as int)).0, spec_va2index(target_range.view().spec_index(i as int)).1, spec_va2index(target_range.view().spec_index(i as int)).2, spec_va2index(target_range.view().spec_index(i as int)).3) is None) by { seq_index_lemma::<VAddr>(); };
                }
            };
            assert({
                &&& krnl.pt_mp.spec_index(target_pagetable).view()
                    .wf_mapping_1g()
                &&& krnl.pt_mp.spec_index(target_pagetable).view()
                    .wf_mapping_2m()
                &&& krnl.pt_mp.spec_index(target_pagetable).view()
                    .wf_mapping_4k()
            }) by { reveal(pagetable_perms_wf); };
            assert({
                &&& krnl.pt_mp.spec_index(target_pagetable).view()
                    .spec_resolve_mapping_1g_l3(spec_v2l4index(target_va), spec_v2l3index(target_va)) is None
                &&& krnl.pt_mp.spec_index(target_pagetable).view()
                    .spec_resolve_mapping_2m_l2(spec_v2l4index(target_va), spec_v2l3index(target_va), spec_v2l2index(target_va)) is None
            }) by { reveal(PageTable::wf_mapping_1g); reveal(PageTable::wf_mapping_2m); };
            assert({
                &&& !krnl.pt_mp.spec_index(target_pagetable).view()
                    .mapping_4k().dom().contains(target_va)
                &&& krnl.pt_mp.spec_index(target_pagetable).view()
                    .spec_resolve_mapping_4k_l1(spec_v2l4index(target_va), spec_v2l3index(target_va), spec_v2l2index(target_va), spec_v2l1index(target_va)) is None
            }) by {
                target_range.va_range_lemma();
                seq_index_lemma::<VAddr>();
                reveal(PageTable::wf_mapping_4k);
                spec_va_4k_index_roundtrip();
            };
        }
        mmap_4k_build_one_structure(krnl, target_va, target_allocator, target_thread, target_process, target_container, cpu_id, target_pagetable, 3 * (target_range.len - i - 1), Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(target_thread_lock_perm), Tracked(target_pagetable_lock_perm));
        proof {
            assert(share_mapping_4k_held_context(krnl, &*lctx, source_thread, target_thread, target_process, target_container, source_pagetable, target_pagetable, source_thread_lock_perm, target_thread_lock_perm, source_pagetable_lock_perm, target_pagetable_lock_perm)) by { reveal(process_thread_wf); reveal(process_pagetable_match); };
            assert(share_mapping_4k_source_range_present(krnl, source_pagetable, source_range)) by {
                reveal(pagetable_perms_wf); reveal(mapped_4k_page_pagetable_wf);
                page_ptr_valid_imply_page_index_valid();
            };
            assert(share_mapping_4k_range_owner_compatible(krnl, source_pagetable, target_thread, source_range)) by {
                reveal(pagetable_perms_wf); reveal(mapped_4k_page_pagetable_wf); reveal(container_page_owner_wf);
            };
            assert(share_mapping_4k_leaf_ready(krnl, source_pagetable, target_pagetable, target_thread, source_va, target_va)) by {
                assert(share_mapping_4k_leaf_structure_ready(krnl, source_pagetable, target_pagetable, source_va, target_va)) by {
                    seq_index_lemma::<VAddr>();
                    source_range.va_range_lemma();
                    target_range.va_range_lemma();
                    reveal(PageTable::wf_mapping_4k);
                };
                assert(share_mapping_4k_leaf_owner_compatible(krnl, source_pagetable, target_thread, source_va)) by {
                    seq_index_lemma::<VAddr>();
                    source_range.va_range_lemma();
                };
            };
        }
        share_one_mapping_4k(krnl, source_thread, target_thread, target_process, target_container, source_pagetable, target_pagetable, cpu_id, source_va, target_va, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(source_thread_lock_perm), Tracked(target_thread_lock_perm), Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm));
        proof {
            assert(steps.steps.subrange(0, old(steps).steps.len() as int) == old(steps).steps) by {
                vstd::seq::lemma_seq_subrange_composition(steps.steps, 0, (steps.steps.len() - 1) as int, 0, old(steps).steps.len() as int);
            };
            assert(old(krnl).prc_mp.spec_index(target_process).wlocked_by(old(lctx)) && {
                let iommu_table = old(krnl).prc_mp.spec_index(target_process).view().iommu_table;
                ||| iommu_table is None
                ||| iommu_table is Some && old(lctx).iommu_table_lock_map().dom().contains(iommu_table.unwrap())
            } ==> kernel_k_to_kernel_u(*krnl).process_map.dom().contains(target_process)) by { reveal(kernel_k_to_kernel_u); reveal(held_processes_unchanged); };
            assert(mmap_4k_held_context(krnl, &*lctx, target_allocator, target_thread, target_process, target_container, cpu_id, target_pagetable, target_thread_lock_perm, target_pagetable_lock_perm)) by { reveal(container_allocator_wf); reveal(container_thread_wf); reveal(process_thread_wf); reveal(process_pagetable_match); };
            assert(share_mapping_4k_source_range_present(krnl, source_pagetable, source_range)) by {
                reveal(pagetable_perms_wf); reveal(mapped_4k_page_pagetable_wf);
                page_ptr_valid_imply_page_index_valid();
            };
            assert(share_mapping_4k_range_owner_compatible(krnl, source_pagetable, target_thread, source_range)) by {
                reveal(pagetable_perms_wf); reveal(mapped_4k_page_pagetable_wf); reveal(container_page_owner_wf);
            };
            assert(krnl.pt_mp.spec_index(target_pagetable).view().wf()) by { reveal(pagetable_perms_wf); };
            assert(krnl.pt_mp.spec_index(target_pagetable).view().mapping_4k() == share_mapping_4k_target_map_after(old(krnl).pt_mp.spec_index(source_pagetable).view().mapping_4k(), old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k(), source_range, target_range, (i + 1) as nat)) by {
                source_range.va_range_lemma();
                target_range.va_range_lemma();
            };
            assert(share_mapping_4k_range_mapped_prefix(krnl.pt_mp.spec_index(target_pagetable).view(), target_range, (i + 1) as int)) by {
                seq_index_lemma::<VAddr>();
                target_range.va_range_lemma();
            };
            assert(share_mapping_4k_target_range_empty_from(krnl.pt_mp.spec_index(target_pagetable).view(), target_range, (i + 1) as int)) by {
                seq_index_lemma::<VAddr>();
                target_range.va_range_lemma();
            };
        }
        i = i + 1;
    }
    proof {
        assert(share_mapping_4k_reverse_mappings(krnl, target_pagetable, target_range)) by {
            seq_index_lemma::<VAddr>();
            source_range.va_range_lemma();
            target_range.va_range_lemma();
            page_ptr_valid_imply_page_index_valid();
            reveal(pagetable_perms_wf); reveal(mapped_4k_page_pagetable_wf);
        };
    }
}
} // verus!
