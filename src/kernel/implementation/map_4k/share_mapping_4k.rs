use vstd::prelude::*;
use crate::*;

verus! {
/// Number of L1/L2/L3 directory pages required to map `target_range` into an
/// otherwise empty target page table. The existing L4 root is not counted.
pub open spec fn spec_required_4k_directory_pages_for_empty_target(
    target_range: &VaRange4K,
) -> int
    recommends
        target_range.wf(),
        target_range.len > 0,
{
    let end = target_range.view().spec_index((target_range.len - 1) as int);
    (end >> 21) - (target_range.start >> 21) + 1usize
        + ((end >> 30) - (target_range.start >> 30) + 1usize)
        + ((end >> 39) - (target_range.start >> 39) + 1usize)
}

pub fn required_4k_directory_pages_for_empty_target(
    target_range: &VaRange4K,
) -> (ret: usize)
    requires
        target_range.wf(),
        target_range.len > 0,
    ensures
        ret as int == spec_required_4k_directory_pages_for_empty_target(target_range),
        ret >= 3,
{
    let start = target_range.start;
    let end = target_range.index(target_range.len - 1);
    proof {
        target_range.va_range_lemma();
        assert({
            &&& (start >> 21) <= (end >> 21)
            &&& (start >> 30) <= (end >> 30)
            &&& (start >> 39) <= (end >> 39)
            &&& (end >> 21) < 8_796_093_022_208usize
            &&& (end >> 30) < 17_179_869_184usize
            &&& (end >> 39) < 33_554_432usize
        }) by (bit_vector)
            requires
                start <= end,
        ;
    }
    let l1_pages = (end >> 21) - (start >> 21) + 1;
    let l2_pages = (end >> 30) - (start >> 30) + 1;
    let l3_pages = (end >> 39) - (start >> 39) + 1;
    l1_pages + l2_pages + l3_pages
}

pub open spec fn share_mapping_4k_source_range_present(
    krnl: &KernelK, source_pagetable: RwLockPageTableRoot, source_range: &VaRange4K,
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
    krnl: &KernelK, source_pagetable: RwLockPageTableRoot, target_pagetable: RwLockPageTableRoot, source_va: VAddr, target_va: VAddr,
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
    krnl: &KernelK, source_pagetable: RwLockPageTableRoot, target_container: RwLockContainerPtr, source_va: VAddr,
) -> bool {
    let owner = krnl.pt_mp.spec_index(source_pagetable).view()
        .mapping_4k().spec_index(source_va).owning_container@;
    &&& krnl.ctn_mp.dom().contains(target_container)
    &&& krnl.ctn_mp.dom().contains(owner)
    &&& (target_container == owner || krnl.ctn_mp.spec_index(target_container).view_ghost().uppertree_seq.view().contains(owner))
}

pub open spec fn share_mapping_4k_leaf_ready(
    krnl: &KernelK, source_pagetable: RwLockPageTableRoot, target_pagetable: RwLockPageTableRoot, target_container: RwLockContainerPtr,
    source_va: VAddr, target_va: VAddr,
) -> bool {
    &&& share_mapping_4k_leaf_structure_ready(krnl, source_pagetable, target_pagetable, source_va, target_va)
    &&& share_mapping_4k_leaf_owner_compatible(krnl, source_pagetable, target_container, source_va)
}

pub open spec fn share_mapping_4k_range_structure_ready_from(
    krnl: &KernelK, source_pagetable: RwLockPageTableRoot, target_pagetable: RwLockPageTableRoot, source_range: &VaRange4K,
    target_range: &VaRange4K, first: int,
) -> bool {
    forall|i: int|
        #![trigger source_range.view().spec_index(i),
            target_range.view().spec_index(i)]
        first <= i < source_range.len
        ==> share_mapping_4k_leaf_structure_ready(krnl, source_pagetable, target_pagetable, source_range.view().spec_index(i), target_range.view().spec_index(i))
}

pub open spec fn share_mapping_4k_range_owner_compatible(
    krnl: &KernelK, source_pagetable: RwLockPageTableRoot, target_container: RwLockContainerPtr, source_range: &VaRange4K,
) -> bool {
    forall|i: int|
        #![trigger source_range.view().spec_index(i)]
        0 <= i < source_range.len
        ==> share_mapping_4k_leaf_owner_compatible(krnl, source_pagetable, target_container, source_range.view().spec_index(i))
}

pub open spec fn share_mapping_4k_range_owner_compatible_prefix(
    krnl: &KernelK, source_pagetable: RwLockPageTableRoot, target_container: RwLockContainerPtr, source_range: &VaRange4K, upper: int,
) -> bool {
    forall|i: int|
        #![trigger source_range.view().spec_index(i)]
        0 <= i < upper
        ==> share_mapping_4k_leaf_owner_compatible(krnl, source_pagetable, target_container, source_range.view().spec_index(i))
}

/// Target map after copying the first `upper` source-range mappings to the
/// corresponding target-range addresses.
pub open spec fn share_mapping_4k_target_map_with_shared_prefix(
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
        share_mapping_4k_target_map_with_shared_prefix(source, target, source_range, target_range, (upper - 1) as nat).insert(target_range.view().spec_index((upper - 1) as int), source.spec_index(source_range.view().spec_index((upper - 1) as int)))
    }
}

pub open spec fn share_mapping_4k_range_mapped_prefix(
    target: PageTable<PT_TYPE>, target_range: &VaRange4K, upper: int,
) -> bool {
    forall|i: int|
        #![trigger target.mapping_4k().dom().contains(target_range.view().spec_index(i))]
        0 <= i < upper
        ==> target.mapping_4k().dom().contains(target_range.view().spec_index(i))
}

/// Every not-yet-shared target VA is still absent from the 4K mapping.
pub open spec fn share_mapping_4k_target_range_empty_from(
    pagetable: PageTable<PT_TYPE>, target_range: &VaRange4K, first: int,
) -> bool {
    forall|i: int|
        #![trigger pagetable.mapping_4k().dom().contains(target_range.view().spec_index(i))]
        first <= i < target_range.len
        ==> !pagetable.mapping_4k().dom().contains(target_range.view().spec_index(i))
}

pub open spec fn share_mapping_4k_reverse_mappings(
    krnl: &KernelK, target_pagetable: RwLockPageTableRoot, target_range: &VaRange4K,
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
    krnl: &KernelK, source_range: &VaRange4K, source_pagetable: RwLockPageTableRoot, Tracked(lctx): Tracked<&LocalContext>,
    Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>,
) -> (ret: bool)
    requires
        krnl.inv(),
        source_range.wf(),
        krnl.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        krnl.pt_mp.dom().contains(source_pagetable),
        krnl.pt_mp.spec_index(source_pagetable).view().kernel_l4_end <= spec_va2index(source_range.start).0,
        lctx.pagetable_lock_map().dom().contains(source_pagetable),
        source_pagetable_lock_perm.thread_id() == lctx.thread_id(),
        (source_pagetable_lock_perm.state() is ReadLock || source_pagetable_lock_perm.state() is WriteLock),
        source_pagetable_lock_perm.state() is ReadLock ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), source_pagetable, TypedLockMode::Read),
        source_pagetable_lock_perm.state() is ReadLock ==> krnl.pt_mp.spec_index(source_pagetable).locking_thread()->Read_reader_map.contains_pair(lctx.thread_id(), source_pagetable_lock_perm.lock_id()),
        source_pagetable_lock_perm.state() is WriteLock ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), source_pagetable, TypedLockMode::Write),
        source_pagetable_lock_perm.state() is WriteLock ==> source_pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
    ensures
        ret == share_mapping_4k_source_range_present(krnl, source_pagetable, source_range),
{
    assert({
        &&& krnl.pt_mp.perms_wf()
        &&& krnl.pt_mp.spec_index(source_pagetable).is_init()
        &&& krnl.pt_mp.spec_index(source_pagetable).view().wf()
    }) by { reveal(pagetable_perms_wf); };
    let pagetable = krnl.pt_mp.borrow_typed(source_pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(source_pagetable_lock_perm));
    let ret = pagetable.mapping_4k_va_range_present(source_range);
    assert(ret == share_mapping_4k_source_range_present(krnl, source_pagetable, source_range)) by {
        if ret {
            reveal(mapped_4k_page_pagetable_wf);
            page_ptr_valid_imply_page_index_valid();
        }
    };
    ret
}

#[verifier::spinoff_prover]
fn share_one_mapping_4k(krnl: &mut KernelK, source_thread: RwLockThreadPtr, target_thread: RwLockThreadPtr, target_process: RwLockProcessPtr, target_container: RwLockContainerPtr, source_pagetable: RwLockPageTableRoot, target_pagetable: RwLockPageTableRoot, cpu_id: CpuId, source_va: VAddr, target_va: VAddr, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, Tracked(source_thread_lock_perm): Tracked<&LockPerm>, Tracked(target_thread_lock_perm): Tracked<&LockPerm>, Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>, Tracked(target_pagetable_lock_perm): Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() == set![source_thread, target_thread],
        old(lctx).pagetable_lock_map().dom() == set![source_pagetable, target_pagetable],
        old(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
        source_pagetable != target_pagetable,
        old(krnl).thr_mp.dom().contains(source_thread),
        old(krnl).thr_mp.dom().contains(target_thread),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), source_thread, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(source_thread).being_killed(),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), target_thread, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(target_thread).being_killed(),
        old(krnl).thr_mp.spec_index(source_thread).view().owning_proc != target_process,
        old(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        old(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        old(krnl).prc_mp.dom().contains(target_process),
        old(krnl).prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container,
        old(krnl).prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable,
        ((old(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process && old(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable) || typed_lock_map_contains_mode(old(lctx).process_lock_map(), target_process, TypedLockMode::Write)),
        source_thread_lock_perm.state() is WriteLock,
        source_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        source_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(source_thread).locking_thread()->Write_lock_id,
        target_thread_lock_perm.state() is WriteLock,
        target_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        target_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(target_thread).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable),
        old(krnl).pt_mp.dom().contains(target_pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
        old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == old(krnl).thr_mp.spec_index(source_thread).view().owning_proc,
        old(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_pagetable_lock_perm.state() is WriteLock,
        source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        source_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
        target_pagetable_lock_perm.state() is WriteLock,
        target_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        target_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).ctn_mp.dom().contains(target_container),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        share_mapping_4k_leaf_ready(old(krnl), source_pagetable, target_pagetable, target_container, source_va, target_va),
    ensures
        forall|pt: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(pt)]
            old(lctx).pagetable_lock_map().dom().contains(pt)
            && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
            ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(lctx).page_lock_map().dom().is_empty(),
        final(lctx).thread_lock_map().dom() == set![source_thread, target_thread],
        final(lctx).pagetable_lock_map().dom() == set![source_pagetable, target_pagetable],
        final(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
        final(krnl).thr_mp.dom().contains(source_thread),
        final(krnl).thr_mp.dom().contains(target_thread),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), source_thread, TypedLockMode::Write),
        !final(krnl).thr_mp.spec_index(source_thread).being_killed(),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), target_thread, TypedLockMode::Write),
        !final(krnl).thr_mp.spec_index(target_thread).being_killed(),
        final(krnl).thr_mp.spec_index(source_thread).view().owning_proc != target_process,
        final(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        final(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        final(krnl).prc_mp.dom().contains(target_process),
        final(krnl).prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container,
        final(krnl).prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable,
        ((final(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process && final(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable) || typed_lock_map_contains_mode(final(lctx).process_lock_map(), target_process, TypedLockMode::Write)),
        source_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(source_thread).locking_thread()->Write_lock_id,
        target_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(target_thread).locking_thread()->Write_lock_id,
        final(krnl).pt_mp.dom().contains(source_pagetable),
        final(krnl).pt_mp.dom().contains(target_pagetable),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
        final(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == final(krnl).thr_mp.spec_index(source_thread).view().owning_proc,
        final(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
        target_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        final(steps).steps.len() == old(steps).steps.len() + 1,
        final(steps).steps.subrange(0, old(steps).steps.len() as int) == old(steps).steps,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        {
            let source_process = old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr;
            &&& final(steps).steps.last().new_u.process_map.dom().contains(source_process)
            &&& kernel_k_to_kernel_u(*final(krnl)).process_map.dom().contains(source_process)
            &&& final(steps).steps.last().new_u.process_map.spec_index(source_process).pagetable == kernel_k_to_kernel_u(*final(krnl)).process_map.spec_index(source_process).pagetable
            &&& final(steps).steps.last().new_u.process_map.dom().contains(target_process)
            &&& typed_lock_map_contains_mode(old(lctx).process_lock_map(), target_process, TypedLockMode::Write) && ({
                let iommu_table = old(krnl).prc_mp.spec_index(target_process).view().iommu_table;
                ||| iommu_table is None
                ||| iommu_table is Some && old(lctx).iommu_table_lock_map().dom().contains(iommu_table.unwrap())
            }) ==> {
                &&& kernel_k_to_kernel_u(*final(krnl)).process_map.dom().contains(target_process)
                &&& final(steps).steps.last().new_u.process_map.spec_index(target_process) == kernel_k_to_kernel_u(*final(krnl)).process_map.spec_index(target_process)
            }
        },
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(krnl).thr_mp.lock_id_by_key(target_thread) == old(krnl).thr_mp.lock_id_by_key(target_thread),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        final(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
        held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
        held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
        held_cpu_sets_unchanged(old(krnl).cpu_set_mp, final(krnl).cpu_set_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        final(krnl).thr_mp.spec_index(target_thread).view() == old(krnl).thr_mp.spec_index(target_thread).view(),
        final(krnl).thr_mp.spec_index(source_thread).view() == old(krnl).thr_mp.spec_index(source_thread).view(),
        final(krnl).ctn_mp.dom().contains(target_container),
        final(krnl).ctn_mp.spec_index(target_container).view_rodata() == old(krnl).ctn_mp.spec_index(target_container).view_rodata(),
        final(krnl).prc_mp.spec_index(target_process).view_rodata() == old(krnl).prc_mp.spec_index(target_process).view_rodata(),
        final(krnl).pt_mp.spec_index(source_pagetable).view() == old(krnl).pt_mp.spec_index(source_pagetable).view(),
        final(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k() == old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k().insert(target_va, old(krnl).pt_mp.spec_index(source_pagetable).view().mapping_4k().spec_index(source_va)),
        final(krnl).pt_mp.spec_index(target_pagetable).view().user_view().mapping_4k == old(krnl).pt_mp.spec_index(target_pagetable).view().user_view().mapping_4k.insert(target_va, old(krnl).pt_mp.spec_index(source_pagetable).view().user_view().mapping_4k.spec_index(source_va)),
        final(krnl).pt_mp.spec_index(target_pagetable).view().mapping_2m() == old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_2m(),
        final(krnl).pt_mp.spec_index(target_pagetable).view().mapping_1g() == old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_1g(),
        final(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end,
        final(krnl).pt_mp.spec_index(target_pagetable).view().page_closure() == old(krnl).pt_mp.spec_index(target_pagetable).view().page_closure(),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger final(krnl).pt_mp.spec_index(target_pagetable).view().spec_resolve_mapping_l2(l4i, l3i, l2i)]
            final(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end <= l4i && pei_valid(l4i)
                && pei_valid(l3i) && pei_valid(l2i) ==> final(krnl).pt_mp.spec_index(target_pagetable).view().spec_resolve_mapping_l2(l4i, l3i, l2i) == old(krnl).pt_mp.spec_index(target_pagetable).view().spec_resolve_mapping_l2(l4i, l3i, l2i),
        {
            let page_ptr = old(krnl).pt_mp .spec_index(source_pagetable).view().mapping_4k().spec_index(source_va).addr;
            final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().mappings().contains((target_pagetable, target_va))
        },
{
    let source_indices = va2index(source_va);
    proof {
        pagetable_perms_wf_at(krnl.pt_mp, source_pagetable);
        pagetable_perms_wf_at(krnl.pt_mp, target_pagetable);
    }
    let target_indices = va2index(target_va);
    assert({
        &&& spec_index2va(source_indices) == source_va
        &&& krnl.pt_mp.spec_index(source_pagetable).view().spec_resolve_mapping_4k_l1(source_indices.0, source_indices.1, source_indices.2, source_indices.3) is Some
    }) by {
        spec_va_4k_index_roundtrip_at(source_va, source_indices.0, source_indices.1, source_indices.2, source_indices.3);
        reveal(PageTable::wf_mapping_4k);
    };
    let source_entry;
    {
        let source = krnl.pt_mp.borrow_typed(source_pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(source_pagetable_lock_perm));
        source_entry = source.resolve_mapping_4k_l1(source_indices.0, source_indices.1, source_indices.2, source_indices.3).2.unwrap();
    }
    let page_ptr = source_entry.addr;
    proof {
        assert({
            &&& source_entry =~= krnl.pt_mp .spec_index(source_pagetable).view().mapping_4k().spec_index(source_va)
            &&& page_ptr_valid(page_ptr)
        }) by { reveal(PageTable::wf_mapping_4k); };
    }
    let page_index = page_ptr2page_index(page_ptr);
    let target_l1_ptr;
    {
        let target = krnl.pt_mp.borrow_typed(target_pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(target_pagetable_lock_perm));
        target_l1_ptr = target.resolve_mapping_4k_l2(target_indices.0, target_indices.1, target_indices.2).0.unwrap().addr;
    }
    proof {
        assert({
            &&& index_valid(NUM_PAGES, page_index)
            &&& krnl.pg_arr.spec_index(page_index).view().view().state
                is Mapped4k
            &&& !lctx.page_lock_map().dom().contains(page_index)
            &&& krnl.pg_arr.lock_id_by_index(page_index).major == MAPPED_PAGE_LOCK_MAJOR
            &&& lctx.lock_id_acyclic(krnl.pg_arr.lock_id_by_index(page_index))
        }) by {
            page_ptr_valid_imply_page_index_valid();
            reveal(mapped_4k_page_pagetable_wf);
        };
    }
    let Tracked(page_lock_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));
    proof {
        assert({
            &&& krnl.pg_arr.inv()
            &&& krnl.pg_arr.spec_index(page_index).view().inv()
        }) by { reveal(page_array_wf); };
        assert({
            &&& !krnl.pg_arr.spec_index(page_index).view().view().mappings().contains((target_pagetable, target_va))
            &&& krnl.pg_arr.spec_index(page_index).view().view().ref_count
                < usize::MAX
        }) by {
            reveal(mapped_4k_page_pagetable_wf);
            mapped_4k_page_ref_count_lt_usize_max(krnl.pt_mp, krnl.pg_arr, page_index);
        };
    }
    page_array_add_4k_mapping(
        &mut krnl.pg_arr, page_index, target_pagetable, target_va, Tracked(&*lctx), Tracked(&page_lock_perm),
    );
    proof {
        assert(spec_index2va(target_indices) == target_va) by {
            spec_va_4k_index_roundtrip_at(target_va, target_indices.0, target_indices.1, target_indices.2, target_indices.3);
        };
    }
    pagetable_map_insert_4k(
        &mut krnl.pt_mp, target_pagetable, target_indices, target_l1_ptr, &source_entry,
        Tracked(&mut *lctx), Tracked(target_pagetable_lock_perm),
    );

    proof {
        assert(krnl.subsystems_inv()) by {
            assert(krnl.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
            assert(pagetable_perms_wf(krnl.pt_mp)) by { reveal(pagetable_perms_wf); };
            assert(page_array_wf(krnl.pg_arr)) by { reveal(page_array_wf); };
        };
        assert(krnl.memory_management_inv()) by {
                assert(cpu_set_pages_wf(krnl.cpu_set_mp, krnl.pg_arr)) by { reveal(cpu_set_pages_wf); };
            assert(allocator_pages_wf(krnl.pg_arr, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by {
                allocator_4k_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_4k_mp, krnl.allc_4k_mp);
                allocator_2m_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_2m_mp, krnl.allc_2m_mp);
                allocator_1g_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_1g_mp, krnl.allc_1g_mp);
            };
            assert(container_page_owner_wf(krnl.ctn_mp, krnl.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(old(krnl).ctn_mp, krnl.ctn_mp, old(krnl).pg_arr, krnl.pg_arr); };
            assert(page_pagetable_wf(krnl.pt_mp, krnl.pg_arr)) by {
                assert({
                    let target_entry = krnl.pt_mp .spec_index(target_pagetable).view().mapping_4k().spec_index(target_va);
                    target_entry.owning_container@ == krnl.pg_arr.spec_index(page_index).view().view().owning_container
                }) by { reveal(mapped_4k_page_pagetable_wf); };
                page_pagetable_wf_preserved_for_4k_mapping_insert(old(krnl).pt_mp, krnl.pt_mp, old(krnl).pg_arr, krnl.pg_arr, target_pagetable, page_ptr, target_va);
            };
            assert(container_process_page_pagetable_wf(krnl.ctn_mp, krnl.prc_mp, krnl.pt_mp, krnl.pg_arr)) by {
                assert({
                    let owner = krnl.pg_arr.spec_index(page_index).view().view().owning_container;
                    let mapping_process = krnl.pt_mp .spec_index(target_pagetable).view().proc_ptr;
                    let mapping_container = krnl.prc_mp .spec_index(mapping_process).view_rodata().view().owning_container;
                    &&& krnl.prc_mp.dom().contains(mapping_process)
                    &&& krnl.ctn_mp.dom().contains(owner)
                    &&& (mapping_container == owner || krnl.ctn_mp.spec_index(owner).view_ghost().subtree_set.view().contains(mapping_container))
                }) by { reveal(mapped_4k_page_pagetable_wf); reveal(container_thread_wf); reveal(container_uppertree_seq_wf); };
                container_process_page_pagetable_wf_preserved_for_4k_mapping_insert(krnl.ctn_mp, krnl.prc_mp, old(krnl).pt_mp, krnl.pt_mp, old(krnl).pg_arr, krnl.pg_arr, target_pagetable, page_ptr, target_va);
            };
            assert(container_pages_wf(krnl.pg_arr, krnl.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).ctn_mp, krnl.ctn_mp); };
            assert(process_pages_wf(krnl.pg_arr, krnl.prc_mp)) by { process_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).prc_mp, krnl.prc_mp); };
            assert(pagetable_pages_wf(krnl.pt_mp, krnl.pg_arr)) by { reveal(pagetable_pages_wf); };
            assert(iommu_table_pages_wf(krnl.it_mp, krnl.pg_arr)) by { reveal(iommu_table_pages_wf); };
            assert(thread_pages_wf(krnl.thr_mp, krnl.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr); };
            assert(scheduler_pages_wf(krnl.sched_mp, krnl.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(old(krnl).sched_mp, krnl.sched_mp, old(krnl).pg_arr, krnl.pg_arr); };
            assert(pcid_allocator_pages_wf(krnl.pg_arr, krnl.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).pcid_allc_mp, krnl.pcid_allc_mp); };
            assert(thread_staged_pages_wf(krnl.thr_mp, krnl.pg_arr)) by {
                reveal(thread_staged_pages_4k_wf);
                thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr);
                thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr);
            };
            assert(endpoint_pages_wf(krnl.ep_mp, krnl.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(old(krnl).ep_mp, krnl.ep_mp, old(krnl).pg_arr, krnl.pg_arr); };
            assert(process_pagetable_match(krnl.prc_mp, krnl.pt_mp)) by { reveal(process_pagetable_match); };
            assert(container_allocator_free_4k_page_wf(krnl.allc_4k_mp, krnl.pg_arr)) by { container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(krnl.allc_4k_mp, old(krnl).pg_arr, krnl.pg_arr, page_index); };
            assert(container_allocator_free_2m_page_wf(krnl.allc_2m_mp, krnl.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(krnl.allc_2m_mp, old(krnl).pg_arr, krnl.pg_arr, page_index); };
            assert(container_allocator_free_1g_page_wf(krnl.allc_1g_mp, krnl.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(krnl.allc_1g_mp, old(krnl).pg_arr, krnl.pg_arr, page_index); };
        };
        assert(cpu_dirty_map_wf(krnl.ctn_mp, krnl.cpu_set_mp, krnl.prc_mp, krnl.cpu_arr, krnl.cpu_tlb, krnl.pt_mp, krnl.pcid_needflush)) by { reveal(cpu_dirty_map_contains_pagetable_pcid_match); };
        assert(tlb_wf_spec(krnl.cpu_tlb, krnl.pt_mp, krnl.cpu_arr, krnl.pcid_needflush)) by { tlb_wf_spec_preserved_for_4k_mapping_insert(krnl.cpu_tlb, krnl.cpu_arr, old(krnl).pt_mp, krnl.pt_mp, target_pagetable, target_va, krnl.pcid_needflush); };
        assert(kernel_k_to_kernel_u(*krnl) != kernel_k_to_kernel_u(*old(krnl))) by {
            assert({
                let process_ptr = target_process;
                &&& kernel_k_to_kernel_u(*old(krnl)).process_map.dom().contains(process_ptr)
                &&& kernel_k_to_kernel_u(*krnl).process_map.dom().contains(process_ptr)
                &&& !kernel_k_to_kernel_u(*old(krnl)).process_map .spec_index(process_ptr).pagetable.unwrap().mapping_4k.dom().contains(target_va)
                &&& kernel_k_to_kernel_u(*krnl).process_map .spec_index(process_ptr).pagetable.unwrap().mapping_4k.dom().contains(target_va)
            }) by {
                reveal(kernel_k_to_kernel_u);
                reveal(process_pagetable_match);
            };
        };
    }
    krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_lock_perm));
    proof {
        assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
            map_insert_remove_absent_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock {
                lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write,
            });
        };
        assert(krnl.pt_mp.spec_index(target_pagetable).view().user_view().mapping_4k =~= old(krnl).pt_mp.spec_index(target_pagetable).view().user_view().mapping_4k.insert(target_va, old(krnl).pt_mp.spec_index(source_pagetable).view().user_view().mapping_4k.spec_index(source_va))) by { vstd::map::axiom_map_ext_equal(krnl.pt_mp.spec_index(target_pagetable).view().user_view().mapping_4k, old(krnl).pt_mp.spec_index(target_pagetable).view().user_view().mapping_4k.insert(target_va, old(krnl).pt_mp.spec_index(source_pagetable).view().user_view().mapping_4k.spec_index(source_va))); };
        krnl.kernel_step_boundary(&mut *lctx, &mut *steps);
        assert({
            let source_process = old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr;
            &&& steps.steps.last().new_u.process_map.dom().contains(source_process)
            &&& kernel_k_to_kernel_u(*krnl).process_map.dom().contains(source_process)
            &&& steps.steps.last().new_u.process_map.spec_index(source_process).pagetable == kernel_k_to_kernel_u(*krnl).process_map.spec_index(source_process).pagetable
            &&& steps.steps.last().new_u.process_map.dom().contains(target_process)
            &&& typed_lock_map_contains_mode(old(lctx).process_lock_map(), target_process, TypedLockMode::Write) && ({
                let iommu_table = old(krnl).prc_mp.spec_index(target_process).view().iommu_table;
                ||| iommu_table is None
                ||| iommu_table is Some && old(lctx).iommu_table_lock_map().dom().contains(iommu_table.unwrap())
            }) ==> {
                &&& kernel_k_to_kernel_u(*krnl).process_map.dom().contains(target_process)
                &&& steps.steps.last().new_u.process_map.spec_index(target_process) == kernel_k_to_kernel_u(*krnl).process_map.spec_index(target_process)
            }
        }) by {
            reveal(kernel_k_to_kernel_u);
            reveal(process_pagetable_match);
            reveal(process_iommu_table_match);
        };
        assert({
            let mapped_page = krnl.pt_mp .spec_index(target_pagetable).view().mapping_4k().spec_index(target_va).addr;
            krnl.pg_arr.spec_index(page_ptr2page_index(mapped_page)).view().view().mappings().contains((target_pagetable, target_va))
        }) by { reveal(mapped_4k_page_pagetable_wf); };
        assert({
            &&& lctx.holds_no_allocator_locks(PageSize::SZ4k)
            &&& krnl.ctn_mp.dom().contains(target_container)
            &&& krnl.prc_mp.dom().contains(target_process)
            &&& krnl.prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container
            &&& krnl.prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable
            &&& ((krnl.thr_mp.spec_index(target_thread).view().owning_proc == target_process && krnl.thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable) || typed_lock_map_contains_mode(lctx.process_lock_map(), target_process, TypedLockMode::Write))
        }) by { reveal(process_pagetable_match); reveal(container_process_wf); reveal(LocalContext::holds_no_allocator_locks); };
    }
}

/// Read-only owner precheck for every present source 4K mapping.
///
/// The source page table and target thread are stable roots. Each physical
/// page is write-locked only long enough to read its runtime owner. Locking is
/// an internal stuttering step: mappings, page payloads, and user-visible state
/// are unchanged.
#[verifier::spinoff_prover]
pub fn share_mapping_4k_source_owner_precheck(krnl: &mut KernelK, source_range: &VaRange4K, source_thread: RwLockThreadPtr, target_thread: RwLockThreadPtr, target_process: RwLockProcessPtr, target_container: RwLockContainerPtr, source_pagetable: RwLockPageTableRoot, target_pagetable: RwLockPageTableRoot, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, Tracked(source_thread_lock_perm): Tracked<&LockPerm>, Tracked(target_thread_lock_perm): Tracked<&LockPerm>, Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>, Tracked(target_pagetable_lock_perm): Tracked<&LockPerm>) -> (ret: bool)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() == set![source_thread, target_thread],
        old(lctx).pagetable_lock_map().dom() == set![source_pagetable, target_pagetable],
        old(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
        source_pagetable != target_pagetable,
        old(krnl).thr_mp.dom().contains(source_thread),
        old(krnl).thr_mp.dom().contains(target_thread),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), source_thread, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(source_thread).being_killed(),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), target_thread, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(target_thread).being_killed(),
        old(krnl).thr_mp.spec_index(source_thread).view().owning_proc != target_process,
        old(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        old(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        old(krnl).prc_mp.dom().contains(target_process),
        old(krnl).prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container,
        old(krnl).prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable,
        ((old(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process && old(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable) || typed_lock_map_contains_mode(old(lctx).process_lock_map(), target_process, TypedLockMode::Write)),
        source_thread_lock_perm.state() is WriteLock,
        source_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        source_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(source_thread).locking_thread()->Write_lock_id,
        target_thread_lock_perm.state() is WriteLock,
        target_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        target_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(target_thread).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable),
        old(krnl).pt_mp.dom().contains(target_pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
        old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == old(krnl).thr_mp.spec_index(source_thread).view().owning_proc,
        old(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_pagetable_lock_perm.state() is WriteLock,
        source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        source_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
        target_pagetable_lock_perm.state() is WriteLock,
        target_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        target_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        source_range.wf(),
        old(krnl).pt_mp.spec_index(source_pagetable).view().kernel_l4_end <= spec_va2index(source_range.start).0,
        share_mapping_4k_source_range_present(old(krnl), source_pagetable, source_range),
        old(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process,
    ensures
        forall|pt: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(pt)]
            old(lctx).pagetable_lock_map().dom().contains(pt)
            && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
            ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(lctx).page_lock_map().dom().is_empty(),
        final(lctx).thread_lock_map().dom() == set![source_thread, target_thread],
        final(lctx).pagetable_lock_map().dom() == set![source_pagetable, target_pagetable],
        final(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
        final(krnl).thr_mp.dom().contains(source_thread),
        final(krnl).thr_mp.dom().contains(target_thread),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), source_thread, TypedLockMode::Write),
        !final(krnl).thr_mp.spec_index(source_thread).being_killed(),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), target_thread, TypedLockMode::Write),
        !final(krnl).thr_mp.spec_index(target_thread).being_killed(),
        final(krnl).thr_mp.spec_index(source_thread).view().owning_proc != target_process,
        final(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        final(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        final(krnl).prc_mp.dom().contains(target_process),
        final(krnl).prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container,
        final(krnl).prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable,
        ((final(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process && final(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable) || typed_lock_map_contains_mode(final(lctx).process_lock_map(), target_process, TypedLockMode::Write)),
        source_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(source_thread).locking_thread()->Write_lock_id,
        target_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(target_thread).locking_thread()->Write_lock_id,
        final(krnl).pt_mp.dom().contains(source_pagetable),
        final(krnl).pt_mp.dom().contains(target_pagetable),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
        final(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == final(krnl).thr_mp.spec_index(source_thread).view().owning_proc,
        final(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
        target_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        final(steps).steps.len() == old(steps).steps.len(),
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
        held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
        held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
        held_cpu_sets_unchanged(old(krnl).cpu_set_mp, final(krnl).cpu_set_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        final(krnl).cpu_arr.lock_id_by_index(cpu_id) == old(krnl).cpu_arr.lock_id_by_index(cpu_id),
        final(krnl).pt_mp.spec_index(source_pagetable).view() == old(krnl).pt_mp.spec_index(source_pagetable).view(),
        final(krnl).pt_mp.spec_index(target_pagetable).view() == old(krnl).pt_mp.spec_index(target_pagetable).view(),
        final(krnl).thr_mp.spec_index(source_thread).view() == old(krnl).thr_mp.spec_index(source_thread).view(),
        final(krnl).thr_mp.spec_index(target_thread).view() == old(krnl).thr_mp.spec_index(target_thread).view(),
        ({
            &&& old(lctx).page_lock_map().dom().is_empty()
            &&& old(lctx).holds_no_allocator_locks(PageSize::SZ4k)
            &&& old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR)
        }) ==> {
            &&& final(lctx).page_lock_map().dom().is_empty()
            &&& final(lctx).holds_no_allocator_locks(PageSize::SZ4k)
            &&& final(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR)
        },
        share_mapping_4k_source_range_present(final(krnl), source_pagetable, source_range),
        ret == share_mapping_4k_range_owner_compatible(final(krnl), source_pagetable, target_container, source_range),
{
    proof {
        thread_perms_wf_at(krnl.thr_mp, target_thread);
        pagetable_perms_wf_at(krnl.pt_mp, source_pagetable);
        assert(krnl.ctn_mp.dom().contains(target_container)) by { reveal(container_thread_wf); };
        assert({
            &&& held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx))
            &&& held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx))
            &&& held_threads_unchanged(old(krnl).thr_mp, krnl.thr_mp, old(lctx))
            &&& held_endpoints_unchanged(old(krnl).ep_mp, krnl.ep_mp, old(lctx))
            &&& held_schedulers_unchanged(old(krnl).sched_mp, krnl.sched_mp, old(lctx))
            &&& held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, krnl.pcid_allc_mp, old(lctx))
            &&& held_cpu_sets_unchanged(old(krnl).cpu_set_mp, krnl.cpu_set_mp, old(lctx))
            &&& held_pagetables_unchanged(old(krnl).pt_mp, krnl.pt_mp, old(lctx))
            &&& held_iommu_tables_unchanged(old(krnl).it_mp, krnl.it_mp, old(lctx))
            &&& held_cpus_unchanged(old(krnl).cpu_arr, krnl.cpu_arr, old(lctx))
        }) by { held_kernel_objects_unchanged_reflexive(krnl, lctx); };
    }
    let mut i: usize = 0;
    let mut all_compatible = true;
    while i < source_range.len
        invariant
            forall|pt: RwLockPageTableRoot| #![trigger krnl.pt_mp.spec_index(pt)]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pt, krnl.pt_mp.spec_index(pt).view()),
            krnl.inv(),
            lctx.kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(krnl, &*lctx),
            lock_id_set_aligned(&*lctx),
            lctx.page_lock_map().dom().is_empty(),
            lctx.thread_lock_map().dom() == set![source_thread, target_thread],
            lctx.pagetable_lock_map().dom() == set![source_pagetable, target_pagetable],
            lctx.held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
            source_pagetable != target_pagetable,
            krnl.thr_mp.dom().contains(source_thread),
            krnl.thr_mp.dom().contains(target_thread),
            typed_lock_map_contains_mode(lctx.thread_lock_map(), source_thread, TypedLockMode::Write),
            !krnl.thr_mp.spec_index(source_thread).being_killed(),
            typed_lock_map_contains_mode(lctx.thread_lock_map(), target_thread, TypedLockMode::Write),
            !krnl.thr_mp.spec_index(target_thread).being_killed(),
            krnl.thr_mp.spec_index(source_thread).view().owning_proc != target_process,
            krnl.thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
            krnl.thr_mp.spec_index(target_thread).view().owning_container == target_container,
            krnl.prc_mp.dom().contains(target_process),
            krnl.prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container,
            krnl.prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable,
            ((krnl.thr_mp.spec_index(target_thread).view().owning_proc == target_process && krnl.thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable) || typed_lock_map_contains_mode(lctx.process_lock_map(), target_process, TypedLockMode::Write)),
            source_thread_lock_perm.state() is WriteLock,
            source_thread_lock_perm.thread_id() == lctx.thread_id(),
            source_thread_lock_perm.lock_id() == krnl.thr_mp.spec_index(source_thread).locking_thread()->Write_lock_id,
            target_thread_lock_perm.state() is WriteLock,
            target_thread_lock_perm.thread_id() == lctx.thread_id(),
            target_thread_lock_perm.lock_id() == krnl.thr_mp.spec_index(target_thread).locking_thread()->Write_lock_id,
            krnl.pt_mp.dom().contains(source_pagetable),
            krnl.pt_mp.dom().contains(target_pagetable),
            typed_lock_map_contains_mode(lctx.pagetable_lock_map(), source_pagetable, TypedLockMode::Write),
            typed_lock_map_contains_mode(lctx.pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
            krnl.pt_mp.spec_index(source_pagetable).view().proc_ptr == krnl.thr_mp.spec_index(source_thread).view().owning_proc,
            krnl.pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
            source_pagetable_lock_perm.state() is WriteLock,
            source_pagetable_lock_perm.thread_id() == lctx.thread_id(),
            source_pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
            target_pagetable_lock_perm.state() is WriteLock,
            target_pagetable_lock_perm.thread_id() == lctx.thread_id(),
            target_pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
            steps.snap_shot == kernel_k_to_kernel_u(*krnl),
            index_valid(NUM_CPUS, cpu_id),
            krnl.cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
            typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
            lctx.cpu_lock_map().dom().contains(cpu_id),
            krnl.cpu_arr.lock_id_by_index(cpu_id) == old(krnl).cpu_arr.lock_id_by_index(cpu_id),
            source_range.wf(),
            krnl.pt_mp.spec_index(source_pagetable).view().wf(),
            krnl.pt_mp.spec_index(source_pagetable).view().kernel_l4_end
                <= spec_va2index(source_range.start).0,
            share_mapping_4k_source_range_present(krnl, source_pagetable, source_range),
            0 <= i <= source_range.len,
            all_compatible == share_mapping_4k_range_owner_compatible_prefix(krnl, source_pagetable, target_container, source_range, i as int),
            steps.steps.len() == old(steps).steps.len(),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
            typed_lock_maps_unchanged(old(lctx), lctx),
            old(lctx).thread_lock_map().dom().contains(source_thread),
            old(lctx).thread_lock_map().dom().contains(target_thread),
            old(lctx).pagetable_lock_map().dom().contains(source_pagetable),
            old(lctx).pagetable_lock_map().dom().contains(target_pagetable),
            held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx)),
            held_threads_unchanged(old(krnl).thr_mp, krnl.thr_mp, old(lctx)),
            held_endpoints_unchanged(old(krnl).ep_mp, krnl.ep_mp, old(lctx)),
            held_schedulers_unchanged(old(krnl).sched_mp, krnl.sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, krnl.pcid_allc_mp, old(lctx)),
            held_cpu_sets_unchanged(old(krnl).cpu_set_mp, krnl.cpu_set_mp, old(lctx)),
            held_pagetables_unchanged(old(krnl).pt_mp, krnl.pt_mp, old(lctx)),
            held_iommu_tables_unchanged(old(krnl).it_mp, krnl.it_mp, old(lctx)),
            held_cpus_unchanged(old(krnl).cpu_arr, krnl.cpu_arr, old(lctx)),
            old(krnl).pt_mp.dom().contains(source_pagetable),
            old(krnl).thr_mp.dom().contains(target_thread),
            krnl.pt_mp.spec_index(source_pagetable).view() == old(krnl).pt_mp .spec_index(source_pagetable).view(),
            krnl.pt_mp.spec_index(target_pagetable).view() == old(krnl).pt_mp .spec_index(target_pagetable).view(),
            krnl.thr_mp.spec_index(target_thread).view() == old(krnl).thr_mp.spec_index(target_thread).view(),
            krnl.thr_mp.spec_index(source_thread).view() == old(krnl).thr_mp.spec_index(source_thread).view(),
            ({
                &&& old(lctx).page_lock_map().dom().is_empty()
                &&& old(lctx).holds_no_allocator_locks(PageSize::SZ4k)
                &&& old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR)
            }) ==> {
                &&& lctx.page_lock_map().dom().is_empty()
                &&& lctx.holds_no_allocator_locks(PageSize::SZ4k)
                &&& lctx.held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR)
            },
            krnl.thr_mp.spec_index(target_thread).view().owning_proc == target_process,
        decreases source_range.len - i,
    {
        let source_va = source_range.index(i);
        let source_indices = va2index(source_va);
        proof {
            pagetable_perms_wf_at(krnl.pt_mp, source_pagetable);
            assert({
                &&& spec_index2va(source_indices) == source_va
                &&& krnl.pt_mp.spec_index(source_pagetable).view().spec_resolve_mapping_4k_l1(source_indices.0, source_indices.1, source_indices.2, source_indices.3) is Some
            }) by {
                spec_va_4k_index_roundtrip_at(source_va, source_indices.0, source_indices.1, source_indices.2, source_indices.3);
            };
        }
        let source_entry;
        {
            let source = krnl.pt_mp.borrow_typed(source_pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(source_pagetable_lock_perm));
            source_entry = source.resolve_mapping_4k_l1(source_indices.0, source_indices.1, source_indices.2, source_indices.3).2.unwrap();
        }
        let page_ptr = source_entry.addr;
        let page_index = page_ptr2page_index(page_ptr);
        proof {
            assert({
                &&& source_entry =~= krnl.pt_mp .spec_index(source_pagetable).view().mapping_4k().spec_index(source_va)
                &&& page_ptr_valid(page_ptr)
                &&& index_valid(NUM_PAGES, page_index)
                &&& !lctx.page_lock_map().dom().contains(page_index)
                &&& krnl.pg_arr.lock_id_by_index(page_index).major == MAPPED_PAGE_LOCK_MAJOR
                &&& lctx.lock_id_acyclic(krnl.pg_arr.lock_id_by_index(page_index))
            }) by {
                page_ptr_valid_imply_page_index_valid();
            };
        }
        let Tracked(page_lock_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));
        let page_owner;
        {
            proof {
                assert(krnl.pg_arr.inv()) by { reveal(page_array_wf); };
            }
            let page = krnl.pg_arr.borrow_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(&page_lock_perm));
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
            assert(page_compatible == share_mapping_4k_leaf_owner_compatible(krnl, source_pagetable, target_container, source_va)) by { reveal(mapped_4k_page_pagetable_wf); reveal(container_thread_wf); };
        }
        krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_lock_perm));
        proof {
            assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
                map_insert_remove_absent_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock {
                    lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write,
                });
            };
            krnl.kernel_step_boundary(&mut *lctx, &mut *steps);
            assert({
                &&& held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx))
                &&& held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx))
                &&& held_threads_unchanged(old(krnl).thr_mp, krnl.thr_mp, old(lctx))
                &&& held_endpoints_unchanged(old(krnl).ep_mp, krnl.ep_mp, old(lctx))
                &&& held_schedulers_unchanged(old(krnl).sched_mp, krnl.sched_mp, old(lctx))
                &&& held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, krnl.pcid_allc_mp, old(lctx))
                &&& held_cpu_sets_unchanged(old(krnl).cpu_set_mp, krnl.cpu_set_mp, old(lctx))
                &&& held_pagetables_unchanged(old(krnl).pt_mp, krnl.pt_mp, old(lctx))
                &&& held_iommu_tables_unchanged(old(krnl).it_mp, krnl.it_mp, old(lctx))
                &&& held_cpus_unchanged(old(krnl).cpu_arr, krnl.cpu_arr, old(lctx))
            }) by { broadcast use group_held_objects_unchanged_transitive; };
            assert({
                &&& krnl.prc_mp.dom().contains(target_process)
                &&& krnl.prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container
                &&& krnl.prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable
                &&& ((krnl.thr_mp.spec_index(target_thread).view().owning_proc == target_process && krnl.thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable) || typed_lock_map_contains_mode(lctx.process_lock_map(), target_process, TypedLockMode::Write))
            }) by { reveal(container_thread_wf); reveal(process_thread_wf); reveal(process_pagetable_match); };
            assert(old(lctx).holds_no_allocator_locks(PageSize::SZ4k) ==> lctx.holds_no_allocator_locks(PageSize::SZ4k)) by { reveal(LocalContext::holds_no_allocator_locks); };
            assert(share_mapping_4k_source_range_present(krnl, source_pagetable, source_range)) by {
                reveal(mapped_4k_page_pagetable_wf);
                page_ptr_valid_imply_page_index_valid();
            };
            assert(page_compatible == share_mapping_4k_leaf_owner_compatible(krnl, source_pagetable, target_container, source_va)) by { reveal(mapped_4k_page_pagetable_wf); reveal(container_page_owner_wf); reveal(container_thread_wf); };
            assert(all_compatible == share_mapping_4k_range_owner_compatible_prefix(krnl, source_pagetable, target_container, source_range, i as int)) by { reveal(mapped_4k_page_pagetable_wf); reveal(container_page_owner_wf); reveal(container_thread_wf); };
        }
        all_compatible = all_compatible && page_compatible;
        proof {
            assert(all_compatible == share_mapping_4k_range_owner_compatible_prefix(krnl, source_pagetable, target_container, source_range, (i + 1) as int)) by {
                assert(share_mapping_4k_range_owner_compatible_prefix(krnl, source_pagetable, target_container, source_range, (i + 1) as int) == (share_mapping_4k_range_owner_compatible_prefix(krnl, source_pagetable, target_container, source_range, i as int) && share_mapping_4k_leaf_owner_compatible(krnl, source_pagetable, target_container, source_va))) by { source_range.va_range_lemma(); };
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
pub fn share_mapping_4k(krnl: &mut KernelK, source_range: &VaRange4K, target_range: &VaRange4K, source_thread: RwLockThreadPtr, target_thread: RwLockThreadPtr, target_process: RwLockProcessPtr, target_container: RwLockContainerPtr, cpu_id: CpuId, source_pagetable: RwLockPageTableRoot, target_pagetable: RwLockPageTableRoot, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, Tracked(source_thread_lock_perm): Tracked<&LockPerm>, Tracked(target_thread_lock_perm): Tracked<&LockPerm>, Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>, Tracked(target_pagetable_lock_perm): Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() == set![source_thread, target_thread],
        old(lctx).pagetable_lock_map().dom() == set![source_pagetable, target_pagetable],
        old(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
        source_pagetable != target_pagetable,
        old(krnl).thr_mp.dom().contains(source_thread),
        old(krnl).thr_mp.dom().contains(target_thread),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), source_thread, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(source_thread).being_killed(),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), target_thread, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(target_thread).being_killed(),
        old(krnl).thr_mp.spec_index(source_thread).view().owning_proc != target_process,
        old(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        old(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        old(krnl).prc_mp.dom().contains(target_process),
        old(krnl).prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container,
        old(krnl).prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable,
        ((old(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process && old(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable) || typed_lock_map_contains_mode(old(lctx).process_lock_map(), target_process, TypedLockMode::Write)),
        source_thread_lock_perm.state() is WriteLock,
        source_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        source_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(source_thread).locking_thread()->Write_lock_id,
        target_thread_lock_perm.state() is WriteLock,
        target_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        target_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(target_thread).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable),
        old(krnl).pt_mp.dom().contains(target_pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
        old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == old(krnl).thr_mp.spec_index(source_thread).view().owning_proc,
        old(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_pagetable_lock_perm.state() is WriteLock,
        source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        source_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
        target_pagetable_lock_perm.state() is WriteLock,
        target_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        target_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).ctn_mp.dom().contains(target_container),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        source_range.wf(),
        old(krnl).pt_mp.spec_index(source_pagetable).view().wf(),
        old(krnl).pt_mp.spec_index(source_pagetable).view().kernel_l4_end <= spec_va2index(source_range.start).0,
        target_range.wf(),
        source_range.len == target_range.len,
        share_mapping_4k_source_range_present(old(krnl), source_pagetable, source_range),
        share_mapping_4k_range_structure_ready_from(old(krnl), source_pagetable, target_pagetable, source_range, target_range, 0),
        share_mapping_4k_range_owner_compatible(old(krnl), source_pagetable, target_container, source_range),
    ensures
        forall|pt: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(pt)]
            old(lctx).pagetable_lock_map().dom().contains(pt)
            && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
            ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(lctx).page_lock_map().dom().is_empty(),
        final(lctx).thread_lock_map().dom() == set![source_thread, target_thread],
        final(lctx).pagetable_lock_map().dom() == set![source_pagetable, target_pagetable],
        final(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
        final(krnl).thr_mp.dom().contains(source_thread),
        final(krnl).thr_mp.dom().contains(target_thread),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), source_thread, TypedLockMode::Write),
        !final(krnl).thr_mp.spec_index(source_thread).being_killed(),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), target_thread, TypedLockMode::Write),
        !final(krnl).thr_mp.spec_index(target_thread).being_killed(),
        final(krnl).thr_mp.spec_index(source_thread).view().owning_proc != target_process,
        final(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        final(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        final(krnl).prc_mp.dom().contains(target_process),
        final(krnl).prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container,
        final(krnl).prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable,
        ((final(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process && final(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable) || typed_lock_map_contains_mode(final(lctx).process_lock_map(), target_process, TypedLockMode::Write)),
        source_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(source_thread).locking_thread()->Write_lock_id,
        target_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(target_thread).locking_thread()->Write_lock_id,
        final(krnl).pt_mp.dom().contains(source_pagetable),
        final(krnl).pt_mp.dom().contains(target_pagetable),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
        final(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == final(krnl).thr_mp.spec_index(source_thread).view().owning_proc,
        final(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
        target_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        final(steps).steps.len() == old(steps).steps.len() + source_range.len,
        final(steps).steps.subrange(0, old(steps).steps.len() as int) == old(steps).steps,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(krnl).pt_mp.spec_index(source_pagetable).view() == old(krnl).pt_mp.spec_index(source_pagetable).view(),
        final(krnl).thr_mp.spec_index(source_thread).view() == old(krnl).thr_mp.spec_index(source_thread).view(),
        final(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k() == share_mapping_4k_target_map_with_shared_prefix(old(krnl).pt_mp.spec_index(source_pagetable).view().mapping_4k(), old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k(), source_range, target_range, source_range.len as nat),
        share_mapping_4k_range_mapped_prefix(final(krnl).pt_mp.spec_index(target_pagetable).view(), target_range, source_range.len as int),
        final(krnl).pt_mp.spec_index(target_pagetable).view().mapping_2m() == old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_2m(),
        final(krnl).pt_mp.spec_index(target_pagetable).view().mapping_1g() == old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_1g(),
        final(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end,
        final(krnl).pt_mp.spec_index(target_pagetable).view().page_closure() == old(krnl).pt_mp.spec_index(target_pagetable).view().page_closure(),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger final(krnl).pt_mp.spec_index(target_pagetable).view().spec_resolve_mapping_l2(l4i, l3i, l2i)]
            final(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end <= l4i && pei_valid(l4i)
                && pei_valid(l3i) && pei_valid(l2i) ==> final(krnl).pt_mp.spec_index(target_pagetable).view().spec_resolve_mapping_l2(l4i, l3i, l2i) == old(krnl).pt_mp.spec_index(target_pagetable).view().spec_resolve_mapping_l2(l4i, l3i, l2i),
        share_mapping_4k_reverse_mappings(final(krnl), target_pagetable, target_range),
{
    let mut i: usize = 0;
    while i < source_range.len
        invariant
            forall|pt: RwLockPageTableRoot| #![trigger krnl.pt_mp.spec_index(pt)]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pt, krnl.pt_mp.spec_index(pt).view()),
            krnl.inv(),
            lctx.kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(krnl, &*lctx),
            lock_id_set_aligned(&*lctx),
            lctx.page_lock_map().dom().is_empty(),
            lctx.thread_lock_map().dom() == set![source_thread, target_thread],
            lctx.pagetable_lock_map().dom() == set![source_pagetable, target_pagetable],
            lctx.held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
            source_pagetable != target_pagetable,
            krnl.thr_mp.dom().contains(source_thread),
            krnl.thr_mp.dom().contains(target_thread),
            typed_lock_map_contains_mode(lctx.thread_lock_map(), source_thread, TypedLockMode::Write),
            !krnl.thr_mp.spec_index(source_thread).being_killed(),
            typed_lock_map_contains_mode(lctx.thread_lock_map(), target_thread, TypedLockMode::Write),
            !krnl.thr_mp.spec_index(target_thread).being_killed(),
            krnl.thr_mp.spec_index(source_thread).view().owning_proc != target_process,
            krnl.thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
            krnl.thr_mp.spec_index(target_thread).view().owning_container == target_container,
            krnl.prc_mp.dom().contains(target_process),
            krnl.prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container,
            krnl.prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable,
            ((krnl.thr_mp.spec_index(target_thread).view().owning_proc == target_process && krnl.thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable) || typed_lock_map_contains_mode(lctx.process_lock_map(), target_process, TypedLockMode::Write)),
            source_thread_lock_perm.state() is WriteLock,
            source_thread_lock_perm.thread_id() == lctx.thread_id(),
            source_thread_lock_perm.lock_id() == krnl.thr_mp.spec_index(source_thread).locking_thread()->Write_lock_id,
            target_thread_lock_perm.state() is WriteLock,
            target_thread_lock_perm.thread_id() == lctx.thread_id(),
            target_thread_lock_perm.lock_id() == krnl.thr_mp.spec_index(target_thread).locking_thread()->Write_lock_id,
            krnl.pt_mp.dom().contains(source_pagetable),
            krnl.pt_mp.dom().contains(target_pagetable),
            typed_lock_map_contains_mode(lctx.pagetable_lock_map(), source_pagetable, TypedLockMode::Write),
            typed_lock_map_contains_mode(lctx.pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
            krnl.pt_mp.spec_index(source_pagetable).view().proc_ptr == krnl.thr_mp.spec_index(source_thread).view().owning_proc,
            krnl.pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
            source_pagetable_lock_perm.state() is WriteLock,
            source_pagetable_lock_perm.thread_id() == lctx.thread_id(),
            source_pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
            target_pagetable_lock_perm.state() is WriteLock,
            target_pagetable_lock_perm.thread_id() == lctx.thread_id(),
            target_pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
            steps.snap_shot == kernel_k_to_kernel_u(*krnl),
            index_valid(NUM_CPUS, cpu_id),
            typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
            lctx.cpu_lock_map().dom().contains(cpu_id),
            lctx.holds_no_allocator_locks(PageSize::SZ4k),
            lctx.held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
            source_range.wf(),
            krnl.pt_mp.spec_index(source_pagetable).view().wf(),
            krnl.pt_mp.spec_index(source_pagetable).view().kernel_l4_end
                <= spec_va2index(source_range.start).0,
            target_range.wf(),
            source_range.len == target_range.len,
            0 <= i <= source_range.len,
            steps.steps.len() == old(steps).steps.len() + i,
            steps.steps.subrange(0, old(steps).steps.len() as int) == old(steps).steps,
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
            typed_lock_maps_unchanged(old(lctx), lctx),
            old(krnl).pt_mp.dom().contains(source_pagetable),
            old(krnl).pt_mp.dom().contains(target_pagetable),
            krnl.ctn_mp.dom().contains(target_container),
            krnl.pt_mp.spec_index(source_pagetable).view() == old(krnl).pt_mp .spec_index(source_pagetable).view(),
            krnl.thr_mp.spec_index(source_thread).view() == old(krnl).thr_mp.spec_index(source_thread).view(),
            share_mapping_4k_source_range_present(krnl, source_pagetable, source_range),
            share_mapping_4k_range_owner_compatible(krnl, source_pagetable, target_container, source_range),
            share_mapping_4k_range_structure_ready_from(krnl, source_pagetable, target_pagetable, source_range, target_range, i as int),
            krnl.pt_mp.spec_index(target_pagetable).view().mapping_4k() == share_mapping_4k_target_map_with_shared_prefix(old(krnl).pt_mp.spec_index(source_pagetable).view().mapping_4k(), old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k(), source_range, target_range, i as nat),
            share_mapping_4k_range_mapped_prefix(krnl.pt_mp.spec_index(target_pagetable).view(), target_range, i as int),
            krnl.pt_mp.spec_index(target_pagetable).view().mapping_2m() == old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_2m(),
            krnl.pt_mp.spec_index(target_pagetable).view().mapping_1g() == old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_1g(),
            krnl.pt_mp.spec_index(target_pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end,
            krnl.pt_mp.spec_index(target_pagetable).view().page_closure() == old(krnl).pt_mp.spec_index(target_pagetable).view().page_closure(),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger krnl.pt_mp.spec_index(target_pagetable).view().spec_resolve_mapping_l2(l4i, l3i, l2i)]
                krnl.pt_mp.spec_index(target_pagetable).view().kernel_l4_end <= l4i && pei_valid(l4i)
                    && pei_valid(l3i) && pei_valid(l2i) ==> krnl.pt_mp.spec_index(target_pagetable).view().spec_resolve_mapping_l2(l4i, l3i, l2i) == old(krnl).pt_mp.spec_index(target_pagetable).view().spec_resolve_mapping_l2(l4i, l3i, l2i),
        decreases source_range.len - i,
    {
        let source_va = source_range.index(i);
        let target_va = target_range.index(i);
        share_one_mapping_4k(krnl, source_thread, target_thread, target_process, target_container, source_pagetable, target_pagetable, cpu_id, source_va, target_va, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(source_thread_lock_perm), Tracked(target_thread_lock_perm), Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm));
        proof {
            assert(steps.steps.subrange(0, old(steps).steps.len() as int) == old(steps).steps) by { vstd::seq::lemma_seq_subrange_composition(steps.steps, 0, (steps.steps.len() - 1) as int, 0, old(steps).steps.len() as int); };
            assert(share_mapping_4k_source_range_present(krnl, source_pagetable, source_range)) by {
                reveal(mapped_4k_page_pagetable_wf);
                page_ptr_valid_imply_page_index_valid();
            };
            assert(share_mapping_4k_range_owner_compatible(krnl, source_pagetable, target_container, source_range)) by { reveal(mapped_4k_page_pagetable_wf); reveal(container_page_owner_wf); reveal(container_thread_wf); };
            assert(krnl.pt_mp.spec_index(target_pagetable).view().wf()) by { pagetable_perms_wf_at(krnl.pt_mp, target_pagetable); };
            assert(share_mapping_4k_range_structure_ready_from(krnl, source_pagetable, target_pagetable, source_range, target_range, (i + 1) as int)) by {
                source_range.va_range_lemma();
                target_range.va_range_lemma();
            };
            assert(krnl.pt_mp.spec_index(target_pagetable).view().mapping_4k() == share_mapping_4k_target_map_with_shared_prefix(old(krnl).pt_mp.spec_index(source_pagetable).view().mapping_4k(), old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k(), source_range, target_range, (i + 1) as nat)) by {
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
            page_ptr_valid_imply_page_index_valid();
            reveal(pagetable_perms_wf); reveal(mapped_4k_page_pagetable_wf);
        };
    }
}

#[verifier::spinoff_prover]
proof fn prove_share_mapping_4k_build_target_slot_usable(
    current_target: PageTable<PT_TYPE>, initial_target: PageTable<PT_TYPE>, target_range: &VaRange4K, i: usize, target_va: VAddr,
)
    requires
        target_range.wf(),
        0 <= i < target_range.len,
        target_va == target_range.view().spec_index(i as int),
        current_target.wf(),
        initial_target.wf(),
        initial_target.kernel_l4_end == current_target.kernel_l4_end,
        current_target.kernel_l4_end <= spec_v2l4index(target_range.start),
        initial_target.is_empty()
            || initial_target.spec_mapping_4k_va_range_buildable(target_range),
        current_target.mapping_1g() == initial_target.mapping_1g(),
        current_target.mapping_2m() == initial_target.mapping_2m(),
        share_mapping_4k_target_range_empty_from(current_target, target_range, i as int),
    ensures
        va_4k_valid(target_va),
        current_target.kernel_l4_end <= spec_v2l4index(target_va),
        pei_valid(spec_v2l4index(target_va)),
        pei_valid(spec_v2l3index(target_va)),
        pei_valid(spec_v2l2index(target_va)),
        pei_valid(spec_v2l1index(target_va)),
        initial_target.spec_4k_entry_usable(
            spec_v2l4index(target_va), spec_v2l3index(target_va), spec_v2l2index(target_va), spec_v2l1index(target_va),
        ),
        current_target.spec_resolve_mapping_1g_l3(spec_v2l4index(target_va), spec_v2l3index(target_va)) is None,
        current_target.spec_resolve_mapping_2m_l2(spec_v2l4index(target_va), spec_v2l3index(target_va), spec_v2l2index(target_va)) is None,
        !current_target.mapping_4k().dom().contains(target_va),
        current_target.spec_resolve_mapping_4k_l1(
            spec_v2l4index(target_va), spec_v2l3index(target_va), spec_v2l2index(target_va), spec_v2l1index(target_va),
        ) is None,
        current_target.spec_4k_entry_usable(
            spec_v2l4index(target_va), spec_v2l3index(target_va), spec_v2l2index(target_va), spec_v2l1index(target_va),
        ),
{
    assert({
        &&& spec_va_4k_valid(target_range.start)
        &&& spec_va_4k_valid(target_va)
        &&& target_range.start <= target_va
        &&& va_4k_valid(target_va)
    }) by {
        target_range.va_range_lemma();
    };
    spec_v2l4index_monotonic(target_range.start, target_va);
    assert({
        &&& pei_valid(spec_v2l4index(target_va))
        &&& pei_valid(spec_v2l3index(target_va))
        &&& pei_valid(spec_v2l2index(target_va))
        &&& pei_valid(spec_v2l1index(target_va))
    }) by {
        spec_va_4k_valid_imply_indices_valid();
    };
    assert(initial_target.spec_4k_entry_usable(
        spec_v2l4index(target_va),
        spec_v2l3index(target_va),
        spec_v2l2index(target_va),
        spec_v2l1index(target_va),
    )) by {
        if initial_target.is_empty() {
            spec_va_4k_index_roundtrip_at(
                target_va, spec_v2l4index(target_va), spec_v2l3index(target_va), spec_v2l2index(target_va), spec_v2l1index(target_va),
            );
        } else {
            assert(initial_target.spec_resolve_mapping_4k_l1(
                spec_va2index(target_range.view().spec_index(i as int)).0,
                spec_va2index(target_range.view().spec_index(i as int)).1,
                spec_va2index(target_range.view().spec_index(i as int)).2,
                spec_va2index(target_range.view().spec_index(i as int)).3,
            ) is None) by {
                seq_index_lemma::<VAddr>();
            };
        }
    };
    assert({
        &&& current_target.spec_resolve_mapping_1g_l3(spec_v2l4index(target_va), spec_v2l3index(target_va)) is None
        &&& current_target.spec_resolve_mapping_2m_l2(
            spec_v2l4index(target_va), spec_v2l3index(target_va), spec_v2l2index(target_va),
        ) is None
    }) by {
        reveal(PageTable::wf_mapping_1g);
        reveal(PageTable::wf_mapping_2m);
    };
    assert({
        &&& !current_target.mapping_4k().dom().contains(target_va)
        &&& current_target.spec_resolve_mapping_4k_l1(
            spec_v2l4index(target_va), spec_v2l3index(target_va), spec_v2l2index(target_va), spec_v2l1index(target_va),
        ) is None
    }) by {
        reveal(PageTable::wf_mapping_4k);
        spec_va_4k_index_roundtrip_at(
            target_va, spec_v2l4index(target_va), spec_v2l3index(target_va), spec_v2l2index(target_va), spec_v2l1index(target_va),
        );
    };
}

#[verifier::spinoff_prover]
proof fn prove_share_mapping_4k_iteration_target_partition(
    source: Map<VAddr, MapEntry>,
    initial_target: Map<VAddr, MapEntry>,
    previous_target: PageTable<PT_TYPE>,
    current_target: PageTable<PT_TYPE>,
    source_range: &VaRange4K,
    target_range: &VaRange4K,
    i: usize,
    source_va: VAddr,
    target_va: VAddr,
)
    requires
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        0 <= i < source_range.len,
        source_va == source_range.view().spec_index(i as int),
        target_va == target_range.view().spec_index(i as int),
        previous_target.mapping_4k()
            == share_mapping_4k_target_map_with_shared_prefix(source, initial_target, source_range, target_range, i as nat),
        current_target.mapping_4k()
            == previous_target.mapping_4k().insert(target_va, source.spec_index(source_va)),
        share_mapping_4k_range_mapped_prefix(previous_target, target_range, i as int),
        share_mapping_4k_target_range_empty_from(previous_target, target_range, i as int),
    ensures
        current_target.mapping_4k()
            == share_mapping_4k_target_map_with_shared_prefix(source, initial_target, source_range, target_range, (i + 1) as nat),
        share_mapping_4k_range_mapped_prefix(current_target, target_range, (i + 1) as int),
        share_mapping_4k_target_range_empty_from(current_target, target_range, (i + 1) as int),
{
    assert(current_target.mapping_4k()
        == share_mapping_4k_target_map_with_shared_prefix(source, initial_target, source_range, target_range, (i + 1) as nat)) by {
        source_range.va_range_lemma();
        target_range.va_range_lemma();
    };
    assert(share_mapping_4k_range_mapped_prefix(
        current_target,
        target_range,
        (i + 1) as int,
    )) by {
        seq_index_lemma::<VAddr>();
        target_range.va_range_lemma();
    };
    assert(share_mapping_4k_target_range_empty_from(
        current_target,
        target_range,
        (i + 1) as int,
    )) by {
        seq_index_lemma::<VAddr>();
        target_range.va_range_lemma();
    };
}

/// Build each missing target directory path and immediately share its 4K leaf.
/// All fallible checks are completed by the caller before this function starts.
#[verifier::spinoff_prover]
pub fn share_mapping_4k_build_and_share(krnl: &mut KernelK, source_range: &VaRange4K, target_range: &VaRange4K, target_allocator: RwLockPageAllocatorPtr, source_thread: RwLockThreadPtr, quota_thread: RwLockThreadPtr, target_process: RwLockProcessPtr, target_container: RwLockContainerPtr, cpu_id: CpuId, source_pagetable: RwLockPageTableRoot, target_pagetable: RwLockPageTableRoot, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, Tracked(source_thread_lock_perm): Tracked<&LockPerm>, Tracked(quota_thread_lock_perm): Tracked<&LockPerm>, Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>, Tracked(target_pagetable_lock_perm): Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() == set![source_thread, quota_thread],
        old(lctx).pagetable_lock_map().dom() == set![source_pagetable, target_pagetable],
        old(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
        source_pagetable != target_pagetable,
        old(krnl).thr_mp.dom().contains(source_thread),
        old(krnl).thr_mp.dom().contains(quota_thread),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), source_thread, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(source_thread).being_killed(),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), quota_thread, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(quota_thread).being_killed(),
        old(krnl).thr_mp.spec_index(source_thread).view().owning_proc != target_process,
        old(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        old(krnl).thr_mp.spec_index(quota_thread).view().owning_container == target_container,
        old(krnl).prc_mp.dom().contains(target_process),
        old(krnl).prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container,
        old(krnl).prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable,
        ((old(krnl).thr_mp.spec_index(quota_thread).view().owning_proc == target_process && old(krnl).thr_mp.spec_index(quota_thread).view().proc_pagetable_ptr == target_pagetable) || typed_lock_map_contains_mode(old(lctx).process_lock_map(), target_process, TypedLockMode::Write)),
        source_thread_lock_perm.state() is WriteLock,
        source_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        source_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(source_thread).locking_thread()->Write_lock_id,
        quota_thread_lock_perm.state() is WriteLock,
        quota_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        quota_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(quota_thread).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable),
        old(krnl).pt_mp.dom().contains(target_pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
        old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == old(krnl).thr_mp.spec_index(source_thread).view().owning_proc,
        old(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_pagetable_lock_perm.state() is WriteLock,
        source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        source_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
        target_pagetable_lock_perm.state() is WriteLock,
        target_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        target_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        old(krnl).ctn_mp.dom().contains(target_container),
        old(krnl).ctn_mp.spec_index(target_container).view_rodata().view().allocator_ptr_4k == target_allocator,
        old(krnl).allc_4k_mp.dom().contains(target_allocator),
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        source_range.len <= usize::MAX / 3usize,
        old(krnl).pt_mp.spec_index(source_pagetable).view().wf(),
        old(krnl).pt_mp.spec_index(source_pagetable).view().kernel_l4_end <= spec_v2l4index(source_range.start),
        share_mapping_4k_source_range_present(old(krnl), source_pagetable, source_range),
        share_mapping_4k_range_owner_compatible(old(krnl), source_pagetable, target_container, source_range),
        old(krnl).thr_mp.spec_index(quota_thread).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(quota_thread).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(quota_thread).view().quota_4k >= 3 * target_range.len,
        old(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end <= spec_v2l4index(target_range.start),
        old(krnl).pt_mp.spec_index(target_pagetable).view().spec_mapping_4k_va_range_empty(target_range.start, target_range.view().spec_index((target_range.len - 1) as int)),
        old(krnl).pt_mp.spec_index(target_pagetable).view().is_empty() || old(krnl).pt_mp.spec_index(target_pagetable).view().spec_mapping_4k_va_range_buildable(target_range),
    ensures
        forall|pt: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(pt)]
            old(lctx).pagetable_lock_map().dom().contains(pt)
            && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
            ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(lctx).page_lock_map().dom().is_empty(),
        final(lctx).thread_lock_map().dom() == set![source_thread, quota_thread],
        final(lctx).pagetable_lock_map().dom() == set![source_pagetable, target_pagetable],
        final(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
        final(krnl).thr_mp.dom().contains(source_thread),
        final(krnl).thr_mp.dom().contains(quota_thread),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), source_thread, TypedLockMode::Write),
        !final(krnl).thr_mp.spec_index(source_thread).being_killed(),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), quota_thread, TypedLockMode::Write),
        !final(krnl).thr_mp.spec_index(quota_thread).being_killed(),
        final(krnl).thr_mp.spec_index(source_thread).view().owning_proc != target_process,
        final(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        final(krnl).thr_mp.spec_index(quota_thread).view().owning_container == target_container,
        final(krnl).prc_mp.dom().contains(target_process),
        final(krnl).prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container,
        final(krnl).prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable,
        ((final(krnl).thr_mp.spec_index(quota_thread).view().owning_proc == target_process && final(krnl).thr_mp.spec_index(quota_thread).view().proc_pagetable_ptr == target_pagetable) || typed_lock_map_contains_mode(final(lctx).process_lock_map(), target_process, TypedLockMode::Write)),
        source_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(source_thread).locking_thread()->Write_lock_id,
        quota_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(quota_thread).locking_thread()->Write_lock_id,
        final(krnl).pt_mp.dom().contains(source_pagetable),
        final(krnl).pt_mp.dom().contains(target_pagetable),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
        final(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == final(krnl).thr_mp.spec_index(source_thread).view().owning_proc,
        final(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
        target_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        final(krnl).ctn_mp.dom().contains(target_container),
        final(krnl).ctn_mp.spec_index(target_container).view_rodata().view().allocator_ptr_4k == target_allocator,
        final(krnl).allc_4k_mp.dom().contains(target_allocator),
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        final(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
        held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
        held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
        held_cpu_sets_unchanged(old(krnl).cpu_set_mp, final(krnl).cpu_set_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        final(steps).steps.len() == old(steps).steps.len() + source_range.len,
        final(steps).steps.subrange(0, old(steps).steps.len() as int) == old(steps).steps,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        {
            let source_process = old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr;
            &&& final(steps).steps.last().new_u.process_map.dom().contains(source_process)
            &&& kernel_k_to_kernel_u(*final(krnl)).process_map.dom().contains(source_process)
            &&& final(steps).steps.last().new_u.process_map.spec_index(source_process).pagetable == kernel_k_to_kernel_u(*final(krnl)).process_map.spec_index(source_process).pagetable
            &&& final(steps).steps.last().new_u.process_map.dom().contains(target_process)
            &&& typed_lock_map_contains_mode(old(lctx).process_lock_map(), target_process, TypedLockMode::Write) && ({
                let iommu_table = old(krnl).prc_mp.spec_index(target_process).view().iommu_table;
                ||| iommu_table is None
                ||| iommu_table is Some && old(lctx).iommu_table_lock_map().dom().contains(iommu_table.unwrap())
            }) ==> {
                &&& kernel_k_to_kernel_u(*final(krnl)).process_map.dom().contains(target_process)
                &&& final(steps).steps.last().new_u.process_map.spec_index(target_process) == kernel_k_to_kernel_u(*final(krnl)).process_map.spec_index(target_process)
            }
        },
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(krnl).thr_mp.lock_id_by_key(quota_thread) == old(krnl).thr_mp.lock_id_by_key(quota_thread),
        final(krnl).pt_mp.spec_index(source_pagetable).view() == old(krnl).pt_mp.spec_index(source_pagetable).view(),
        source_thread != quota_thread ==> final(krnl).thr_mp.spec_index(source_thread).view() == old(krnl).thr_mp.spec_index(source_thread).view(),
        final(krnl).thr_mp.spec_index(quota_thread).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(quota_thread).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(quota_thread).view().owning_proc == old(krnl).thr_mp.spec_index(quota_thread).view().owning_proc,
        final(krnl).thr_mp.spec_index(quota_thread).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(quota_thread).view().proc_pagetable_ptr,
        final(krnl).thr_mp.spec_index(quota_thread).view().state == old(krnl).thr_mp.spec_index(quota_thread).view().state,
        final(krnl).thr_mp.spec_index(quota_thread).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(quota_thread).view().blocking_endpoint_ptr,
        final(krnl).thr_mp.spec_index(quota_thread).view().quota_4k <= old(krnl).thr_mp.spec_index(quota_thread).view().quota_4k,
        final(krnl).thr_mp.spec_index(quota_thread).view().quota_4k >= old(krnl).thr_mp.spec_index(quota_thread).view().quota_4k - 3 * target_range.len,
        final(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k() == share_mapping_4k_target_map_with_shared_prefix(old(krnl).pt_mp.spec_index(source_pagetable).view().mapping_4k(), old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k(), source_range, target_range, source_range.len as nat),
        final(krnl).pt_mp.spec_index(target_pagetable).view().user_view().mapping_4k == share_mapping_4k_target_map_with_shared_prefix(old(krnl).pt_mp.spec_index(source_pagetable).view().user_view().mapping_4k, old(krnl).pt_mp.spec_index(target_pagetable).view().user_view().mapping_4k, source_range, target_range, source_range.len as nat),
        share_mapping_4k_range_mapped_prefix(final(krnl).pt_mp.spec_index(target_pagetable).view(), target_range, source_range.len as int),
        final(krnl).pt_mp.spec_index(target_pagetable).view().mapping_2m() == old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_2m(),
        final(krnl).pt_mp.spec_index(target_pagetable).view().mapping_1g() == old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_1g(),
        final(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end,
        share_mapping_4k_reverse_mappings(final(krnl), target_pagetable, target_range),
{
    let target_range_start = target_range.start;
    proof {
        assert({
            &&& held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx))
            &&& held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx))
            &&& held_endpoints_unchanged(old(krnl).ep_mp, krnl.ep_mp, old(lctx))
            &&& held_schedulers_unchanged(old(krnl).sched_mp, krnl.sched_mp, old(lctx))
            &&& held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, krnl.pcid_allc_mp, old(lctx))
            &&& held_cpu_sets_unchanged(old(krnl).cpu_set_mp, krnl.cpu_set_mp, old(lctx))
            &&& held_iommu_tables_unchanged(old(krnl).it_mp, krnl.it_mp, old(lctx))
            &&& held_cpus_unchanged(old(krnl).cpu_arr, krnl.cpu_arr, old(lctx))
        }) by { held_kernel_objects_unchanged_reflexive(krnl, lctx); };
        assert({
            &&& krnl.pt_mp.spec_index(source_pagetable).view().wf()
            &&& krnl.pt_mp.spec_index(target_pagetable).view().wf()
            &&& krnl.pt_mp.spec_index(target_pagetable).view().wf_mapping_1g()
            &&& krnl.pt_mp.spec_index(target_pagetable).view().wf_mapping_2m()
            &&& krnl.pt_mp.spec_index(target_pagetable).view().wf_mapping_4k()
        }) by {
            pagetable_perms_wf_at(krnl.pt_mp, source_pagetable);
            pagetable_perms_wf_at(krnl.pt_mp, target_pagetable);
        };
        assert(share_mapping_4k_target_range_empty_from(krnl.pt_mp.spec_index(target_pagetable).view(), target_range, 0)) by {
            reveal(PageTable::spec_mapping_4k_va_range_empty);
            target_range.va_range_lemma();
        };
    }
    let mut i: usize = 0;
    while i < source_range.len
        invariant
            forall|pt: RwLockPageTableRoot| #![trigger krnl.pt_mp.spec_index(pt)]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pt, krnl.pt_mp.spec_index(pt).view()),
            krnl.inv(),
            lctx.kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(krnl, &*lctx),
            lock_id_set_aligned(&*lctx),
            lctx.page_lock_map().dom().is_empty(),
            lctx.thread_lock_map().dom() == set![source_thread, quota_thread],
            lctx.pagetable_lock_map().dom() == set![source_pagetable, target_pagetable],
            lctx.held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
            krnl.thr_mp.dom().contains(source_thread),
            krnl.thr_mp.dom().contains(quota_thread),
            typed_lock_map_contains_mode(lctx.thread_lock_map(), source_thread, TypedLockMode::Write),
            !krnl.thr_mp.spec_index(source_thread).being_killed(),
            typed_lock_map_contains_mode(lctx.thread_lock_map(), quota_thread, TypedLockMode::Write),
            !krnl.thr_mp.spec_index(quota_thread).being_killed(),
            krnl.thr_mp.spec_index(source_thread).view().owning_proc != target_process,
            krnl.thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
            krnl.thr_mp.spec_index(quota_thread).view().owning_container == target_container,
            krnl.prc_mp.dom().contains(target_process),
            krnl.prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container,
            krnl.prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable,
            ((krnl.thr_mp.spec_index(quota_thread).view().owning_proc == target_process && krnl.thr_mp.spec_index(quota_thread).view().proc_pagetable_ptr == target_pagetable) || typed_lock_map_contains_mode(lctx.process_lock_map(), target_process, TypedLockMode::Write)),
            source_thread_lock_perm.state() is WriteLock,
            source_thread_lock_perm.thread_id() == lctx.thread_id(),
            source_thread_lock_perm.lock_id() == krnl.thr_mp.spec_index(source_thread).locking_thread()->Write_lock_id,
            quota_thread_lock_perm.state() is WriteLock,
            quota_thread_lock_perm.thread_id() == lctx.thread_id(),
            quota_thread_lock_perm.lock_id() == krnl.thr_mp.spec_index(quota_thread).locking_thread()->Write_lock_id,
            krnl.pt_mp.dom().contains(source_pagetable),
            krnl.pt_mp.dom().contains(target_pagetable),
            typed_lock_map_contains_mode(lctx.pagetable_lock_map(), source_pagetable, TypedLockMode::Write),
            typed_lock_map_contains_mode(lctx.pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
            krnl.pt_mp.spec_index(source_pagetable).view().proc_ptr == krnl.thr_mp.spec_index(source_thread).view().owning_proc,
            krnl.pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
            source_pagetable_lock_perm.state() is WriteLock,
            source_pagetable_lock_perm.thread_id() == lctx.thread_id(),
            source_pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
            target_pagetable_lock_perm.state() is WriteLock,
            target_pagetable_lock_perm.thread_id() == lctx.thread_id(),
            target_pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
            krnl.cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            krnl.ctn_mp.dom().contains(target_container),
            krnl.ctn_mp.spec_index(target_container).view_rodata().view().allocator_ptr_4k == target_allocator,
            krnl.allc_4k_mp.dom().contains(target_allocator),
            steps.snap_shot == kernel_k_to_kernel_u(*krnl),
            lctx.holds_no_allocator_locks(PageSize::SZ4k),
            lctx.held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
            held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx)),
            held_endpoints_unchanged(old(krnl).ep_mp, krnl.ep_mp, old(lctx)),
            held_schedulers_unchanged(old(krnl).sched_mp, krnl.sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, krnl.pcid_allc_mp, old(lctx)),
            held_cpu_sets_unchanged(old(krnl).cpu_set_mp, krnl.cpu_set_mp, old(lctx)),
            held_iommu_tables_unchanged(old(krnl).it_mp, krnl.it_mp, old(lctx)),
            held_cpus_unchanged(old(krnl).cpu_arr, krnl.cpu_arr, old(lctx)),
            source_range.wf(),
            target_range.wf(),
            source_range.len == target_range.len,
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
                &&& typed_lock_map_contains_mode(old(lctx).process_lock_map(), target_process, TypedLockMode::Write) && ({
                    let iommu_table = old(krnl).prc_mp.spec_index(target_process).view().iommu_table;
                    ||| iommu_table is None
                    ||| iommu_table is Some && old(lctx).iommu_table_lock_map().dom().contains(iommu_table.unwrap())
                }) ==> {
                    &&& kernel_k_to_kernel_u(*krnl).process_map.dom().contains(target_process)
                    &&& steps.steps.last().new_u.process_map.spec_index(target_process) == kernel_k_to_kernel_u(*krnl).process_map.spec_index(target_process)
                }
            },
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
            old(krnl).inv(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            typed_lock_maps_unchanged(old(lctx), lctx),
            old(lctx).thread_lock_map().dom().contains(quota_thread),
            old(krnl).prc_mp.dom().contains(target_process),
            old(krnl).pt_mp.dom().contains(source_pagetable),
            krnl.thr_mp.lock_id_by_key(quota_thread) == old(krnl).thr_mp.lock_id_by_key(quota_thread),
            krnl.pt_mp.spec_index(source_pagetable).view() == old(krnl).pt_mp.spec_index(source_pagetable).view(),
            source_thread != quota_thread ==> krnl.thr_mp.spec_index(source_thread).view() == old(krnl).thr_mp.spec_index(source_thread).view(),
            krnl.pt_mp.spec_index(source_pagetable).view().wf(),
            krnl.pt_mp.spec_index(source_pagetable).view().kernel_l4_end <= spec_v2l4index(source_range.start),
            krnl.thr_mp.spec_index(quota_thread).view().upper_container_seq == old(krnl).thr_mp.spec_index(quota_thread).view().upper_container_seq,
            krnl.thr_mp.spec_index(quota_thread).view().owning_proc == old(krnl).thr_mp.spec_index(quota_thread).view().owning_proc,
            krnl.thr_mp.spec_index(quota_thread).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(quota_thread).view().proc_pagetable_ptr,
            krnl.thr_mp.spec_index(quota_thread).view().state == old(krnl).thr_mp.spec_index(quota_thread).view().state,
            krnl.thr_mp.spec_index(quota_thread).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(quota_thread).view().blocking_endpoint_ptr,
            share_mapping_4k_source_range_present(krnl, source_pagetable, source_range),
            share_mapping_4k_range_owner_compatible(krnl, source_pagetable, target_container, source_range),
            krnl.thr_mp.spec_index(quota_thread).view().temp_alloc_clean(),
            krnl.thr_mp.spec_index(quota_thread).view().free_quota_pending_clean(),
            krnl.thr_mp.spec_index(quota_thread).view().quota_4k
                >= 3 * (target_range.len - i),
            krnl.thr_mp.spec_index(quota_thread).view().quota_4k
                >= old(krnl).thr_mp.spec_index(quota_thread).view().quota_4k
                    - 3 * i,
            krnl.thr_mp.spec_index(quota_thread).view().quota_4k
                <= old(krnl).thr_mp.spec_index(quota_thread).view().quota_4k,
            krnl.pt_mp.spec_index(target_pagetable).view().wf(),
            old(krnl).pt_mp.spec_index(target_pagetable).view().wf(),
            krnl.pt_mp.spec_index(target_pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end,
            krnl.pt_mp.spec_index(target_pagetable).view().kernel_l4_end
                <= spec_v2l4index(target_range.start),
            krnl.pt_mp.spec_index(target_pagetable).view().mapping_2m() == old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_2m(),
            krnl.pt_mp.spec_index(target_pagetable).view().mapping_1g() == old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_1g(),
            old(krnl).pt_mp.spec_index(target_pagetable).view().wf_mapping_1g(),
            old(krnl).pt_mp.spec_index(target_pagetable).view().wf_mapping_2m(),
            old(krnl).pt_mp.spec_index(target_pagetable).view().wf_mapping_4k(),
            old(krnl).pt_mp.spec_index(target_pagetable).view().is_empty()
                || old(krnl).pt_mp.spec_index(target_pagetable).view().spec_mapping_4k_va_range_buildable(target_range),
            krnl.pt_mp.spec_index(target_pagetable).view().mapping_4k() == share_mapping_4k_target_map_with_shared_prefix(old(krnl).pt_mp.spec_index(source_pagetable).view().mapping_4k(), old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k(), source_range, target_range, i as nat),
            krnl.pt_mp.spec_index(target_pagetable).view().user_view().mapping_4k == share_mapping_4k_target_map_with_shared_prefix(old(krnl).pt_mp.spec_index(source_pagetable).view().user_view().mapping_4k, old(krnl).pt_mp.spec_index(target_pagetable).view().user_view().mapping_4k, source_range, target_range, i as nat),
            share_mapping_4k_range_mapped_prefix(krnl.pt_mp.spec_index(target_pagetable).view(), target_range, i as int),
            share_mapping_4k_target_range_empty_from(krnl.pt_mp.spec_index(target_pagetable).view(), target_range, i as int),
        decreases source_range.len - i,
    {
        let source_va = source_range.index(i);
        let target_va = target_range.index(i);
        proof {
            assert(krnl.pt_mp.spec_index(target_pagetable).view().wf()) by { pagetable_perms_wf_at(krnl.pt_mp, target_pagetable); };
            prove_share_mapping_4k_build_target_slot_usable(
                krnl.pt_mp.spec_index(target_pagetable).view(), old(krnl).pt_mp.spec_index(target_pagetable).view(), target_range, i,
                target_va,
            );
        }
        mmap_4k_build_one_structure(krnl, target_va, target_allocator, quota_thread, target_process, target_container, cpu_id, target_pagetable, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(quota_thread_lock_perm), Tracked(target_pagetable_lock_perm));
        proof {
            assert(krnl.thr_mp.lock_id_by_key(quota_thread) == old(krnl).thr_mp.lock_id_by_key(quota_thread)) by { thread_lock_id_preserved_for_typed_maps_unchanged(old(krnl), krnl, old(lctx), lctx, quota_thread); };
            assert(krnl.pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process) by { reveal(process_thread_wf); reveal(process_pagetable_match); };
            assert(share_mapping_4k_leaf_ready(krnl, source_pagetable, target_pagetable, target_container, source_va, target_va)) by {
                assert(share_mapping_4k_leaf_structure_ready(krnl, source_pagetable, target_pagetable, source_va, target_va)) by { reveal(PageTable::wf_mapping_4k); };
                assert(share_mapping_4k_leaf_owner_compatible(krnl, source_pagetable, target_container, source_va)) by { reveal(mapped_4k_page_pagetable_wf); reveal(container_page_owner_wf); reveal(container_thread_wf); };
            };
        }
        let ghost target_before_share = krnl.pt_mp.spec_index(target_pagetable).view();
        share_one_mapping_4k(krnl, source_thread, quota_thread, target_process, target_container, source_pagetable, target_pagetable, cpu_id, source_va, target_va, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(source_thread_lock_perm), Tracked(quota_thread_lock_perm), Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm));
        proof {
            assert(steps.steps.subrange(0, old(steps).steps.len() as int) == old(steps).steps) by { vstd::seq::lemma_seq_subrange_composition(steps.steps, 0, (steps.steps.len() - 1) as int, 0, old(steps).steps.len() as int); };
            assert({
                &&& held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx))
                &&& held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx))
                &&& held_endpoints_unchanged(old(krnl).ep_mp, krnl.ep_mp, old(lctx))
                &&& held_schedulers_unchanged(old(krnl).sched_mp, krnl.sched_mp, old(lctx))
                &&& held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, krnl.pcid_allc_mp, old(lctx))
                &&& held_cpu_sets_unchanged(old(krnl).cpu_set_mp, krnl.cpu_set_mp, old(lctx))
                &&& held_iommu_tables_unchanged(old(krnl).it_mp, krnl.it_mp, old(lctx))
                &&& held_cpus_unchanged(old(krnl).cpu_arr, krnl.cpu_arr, old(lctx))
            }) by { broadcast use group_held_objects_unchanged_transitive; };
            assert(share_mapping_4k_source_range_present(krnl, source_pagetable, source_range)) by {
                reveal(mapped_4k_page_pagetable_wf);
                page_ptr_valid_imply_page_index_valid();
            };
            assert(share_mapping_4k_range_owner_compatible(krnl, source_pagetable, target_container, source_range)) by { reveal(mapped_4k_page_pagetable_wf); reveal(container_page_owner_wf); reveal(container_thread_wf); };
            assert(krnl.pt_mp.spec_index(target_pagetable).view().wf()) by { pagetable_perms_wf_at(krnl.pt_mp, target_pagetable); };
            prove_share_mapping_4k_iteration_target_partition(
                old(krnl).pt_mp.spec_index(source_pagetable).view().mapping_4k(),
                old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k(), target_before_share,
                krnl.pt_mp.spec_index(target_pagetable).view(), source_range, target_range, i, source_va, target_va,
            );
        }
        assert(krnl.allc_4k_mp.dom().contains(target_allocator)) by { reveal(container_allocator_wf); };
        i = i + 1;
    }
    proof {
        assert(share_mapping_4k_reverse_mappings(krnl, target_pagetable, target_range)) by {
            page_ptr_valid_imply_page_index_valid();
            reveal(mapped_4k_page_pagetable_wf);
        };
    }
}
} // verus!
