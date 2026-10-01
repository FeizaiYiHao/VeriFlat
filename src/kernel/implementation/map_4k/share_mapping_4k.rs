use vstd::prelude::*;
use crate::*;
use super::share_mapping_4k_trace::*;

verus! {
/// Number of L1/L2/L3 directory pages required to map `target_range` into an
/// otherwise empty target page table. The existing L4 root is not counted.
pub open spec fn spec_required_4k_directory_pages_for_empty_target(target_range: &VaRange4K) -> int
    recommends
        target_range.wf(),
        target_range.len > 0,
{
    let end = target_range.view().spec_index((target_range.len - 1) as int);
    (end >> 21) - (target_range.start >> 21) + 1usize + ((end >> 30) - (target_range.start >> 30) + 1usize) + ((end >> 39) - (target_range.start >> 39) + 1usize)
}

pub fn required_4k_directory_pages_for_empty_target(target_range: &VaRange4K) -> (ret: usize)
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

pub open spec fn share_mapping_4k_source_range_present(krnl: &KernelK, source_pagetable: RwLockPageTableRoot, source_range: &VaRange4K) -> bool
    recommends
        krnl.pt_mp.dom().contains(source_pagetable),
        krnl.pt_mp.spec_index(source_pagetable).view().wf(),
        source_range.wf(),
        krnl.pt_mp.spec_index(source_pagetable).view().kernel_l4_end <= spec_va2index(source_range.start).0,
{
    &&& krnl.pt_mp.spec_index(source_pagetable).view().spec_mapping_4k_va_range_present(source_range)
    &&& forall|i: int|
        #![trigger krnl.pt_mp.spec_index(source_pagetable)
            .view().mapping_4k().spec_index(source_range.view().spec_index(i))]
        0 <= i < source_range.len ==> {
            let source_va = source_range.view().spec_index(i);
            let source_entry = krnl.pt_mp.spec_index(source_pagetable).view().mapping_4k().spec_index(source_va);
            let page_index = page_ptr2page_index(source_entry.addr);
            &&& krnl.pt_mp.spec_index(source_pagetable).view().mapping_4k().dom().contains(source_va)
            &&& source_entry.present
            &&& page_ptr_valid(source_entry.addr)
            &&& index_valid(NUM_PAGES, page_index)
            &&& krnl.pg_arr.spec_index(page_index).view().view().state is Mapped4k
            &&& krnl.pg_arr.spec_index(page_index).view().view().mappings().contains((source_pagetable, source_va))
        }
}

pub open spec fn share_mapping_4k_leaf_structure_ready(
    krnl: &KernelK, source_pagetable: RwLockPageTableRoot, target_pagetable: RwLockPageTableRoot, source_va: VAddr, target_va: VAddr,
) -> bool {
    let source_indices = spec_va2index(source_va);
    let target_indices = spec_va2index(target_va);
    &&& va_4k_valid(source_va)
    &&& va_4k_valid(target_va)
    &&& krnl.pt_mp.spec_index(source_pagetable).view().kernel_l4_end <= source_indices.0
    &&& pei_valid(source_indices.0)
    &&& pei_valid(source_indices.1)
    &&& pei_valid(source_indices.2)
    &&& pei_valid(source_indices.3)
    &&& krnl.pt_mp.spec_index(source_pagetable).view().mapping_4k().dom().contains(source_va)
    &&& krnl.pt_mp.spec_index(source_pagetable).view().mapping_4k().spec_index(source_va).present
    &&& krnl.pt_mp.spec_index(target_pagetable).view().kernel_l4_end <= target_indices.0
    &&& pei_valid(target_indices.0)
    &&& pei_valid(target_indices.1)
    &&& pei_valid(target_indices.2)
    &&& pei_valid(target_indices.3)
    &&& !krnl.pt_mp.spec_index(target_pagetable).view().mapping_4k().dom().contains(target_va)
    &&& krnl.pt_mp.spec_index(target_pagetable).view().spec_resolve_mapping_l2(target_indices.0, target_indices.1, target_indices.2) is Some
}

pub open spec fn share_mapping_4k_leaf_owner_compatible(krnl: &KernelK, source_pagetable: RwLockPageTableRoot, target_container: RwLockContainerPtr, source_va: VAddr) -> bool {
    let owner = krnl.pt_mp.spec_index(source_pagetable).view().mapping_4k().spec_index(source_va).owning_container@;
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
        0 <= i < source_range.len ==> share_mapping_4k_leaf_owner_compatible(krnl, source_pagetable, target_container, source_range.view().spec_index(i))
}

pub open spec fn share_mapping_4k_range_owner_compatible_prefix(
    krnl: &KernelK, source_pagetable: RwLockPageTableRoot, target_container: RwLockContainerPtr, source_range: &VaRange4K, upper: int,
) -> bool {
    forall|i: int|
        #![trigger source_range.view().spec_index(i)]
        0 <= i < upper ==> share_mapping_4k_leaf_owner_compatible(krnl, source_pagetable, target_container, source_range.view().spec_index(i))
}

/// Target map after copying the first `upper` source-range mappings to the
/// corresponding target-range addresses.
#[verifier::opaque]
pub open spec fn share_mapping_4k_target_map_with_shared_prefix(
    source: Map<VAddr, MapEntry>, target: Map<VAddr, MapEntry>, source_range: &VaRange4K, target_range: &VaRange4K, upper: nat,
) -> Map<VAddr, MapEntry>
    decreases upper,
{
    if upper == 0 {
        target
    } else {
        share_mapping_4k_target_map_with_shared_prefix(source, target, source_range, target_range, (upper - 1) as nat).insert(target_range.view().spec_index((upper - 1) as int),
            source.spec_index(source_range.view().spec_index((upper - 1) as int)))
    }
}

#[verifier::opaque]
pub open spec fn share_mapping_4k_range_mapped_prefix(target: Map<VAddr, MapEntry>, target_range: &VaRange4K, upper: int) -> bool {
    forall|i: int|
        #![trigger target.dom().contains(target_range.view().spec_index(i))]
        0 <= i < upper ==> target.dom().contains(target_range.view().spec_index(i))
}

/// Every not-yet-shared target VA is still absent from the 4K mapping.
#[verifier::opaque]
pub open spec fn share_mapping_4k_target_range_empty_from(pagetable: Map<VAddr, MapEntry>, target_range: &VaRange4K, first: int) -> bool {
    forall|i: int|
        #![trigger pagetable.dom().contains(target_range.view().spec_index(i))]
        first <= i < target_range.len ==> !pagetable.dom().contains(target_range.view().spec_index(i))
}

pub open spec fn share_mapping_4k_reverse_mappings(krnl: &KernelK, target_pagetable: RwLockPageTableRoot, target_range: &VaRange4K) -> bool {
    forall|i: int|
        #![trigger krnl.pt_mp.spec_index(target_pagetable)
            .view().mapping_4k().spec_index(target_range.view().spec_index(i))]
        0 <= i < target_range.len ==> {
            let target_va = target_range.view().spec_index(i);
            let target_entry = krnl.pt_mp.spec_index(target_pagetable).view().mapping_4k().spec_index(target_va);
            let page_index = page_ptr2page_index(target_entry.addr);
            &&& krnl.pt_mp.spec_index(target_pagetable).view().mapping_4k().dom().contains(target_va)
            &&& page_ptr_valid(target_entry.addr)
            &&& index_valid(NUM_PAGES, page_index)
            &&& krnl.pg_arr.spec_index(page_index).view().view().state is Mapped4k
            &&& krnl.pg_arr.spec_index(page_index).view().view().mappings().contains((target_pagetable, target_va))
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
        ret == forall|j: int| #![trigger source_range.view().spec_index(j)] 0 <= j < source_range.len ==> {
            &&& krnl.pt_mp.spec_index(source_pagetable).view().mapping_4k().dom().contains(source_range.view().spec_index(j))
            &&& krnl.pt_mp.spec_index(source_pagetable).view().mapping_4k().spec_index(source_range.view().spec_index(j)).present
        },
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
fn share_one_mapping_4k(
    krnl: &mut KernelK, source_thread: RwLockThreadPtr, target_thread: RwLockThreadPtr, progress_thread: RwLockThreadPtr,
    target_process: RwLockProcessPtr, target_container: RwLockContainerPtr, source_pagetable: RwLockPageTableRoot, target_pagetable: RwLockPageTableRoot,
    cpu_id: CpuId, source_va: VAddr, target_va: VAddr, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    Tracked(source_thread_lock_perm): Tracked<&LockPerm>, Tracked(target_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>, Tracked(target_pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).thread_lock_map().dom() == set![source_thread, target_thread],
        old(lctx).pagetable_lock_map().dom() == set![source_pagetable, target_pagetable],
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(krnl).pg_arr.lock_id_by_index(held_page).major < MAPPED_PAGE_LOCK_MAJOR,
        source_pagetable != target_pagetable,
        old(krnl).thr_mp.dom().contains(source_thread),
        old(krnl).thr_mp.dom().contains(target_thread),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), source_thread, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(source_thread).being_killed(),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), target_thread, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(target_thread).being_killed(),
        old(krnl).thr_mp.spec_index(source_thread).view().owning_proc != target_process,
        old(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        mmap_4k_quota_thread_container_compatible(old(krnl), old(lctx), target_thread, target_container),
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
        old(steps).snapshot_k() == *old(krnl),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).ctn_mp.dom().contains(target_container),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        share_mapping_4k_leaf_ready(old(krnl), source_pagetable, target_pagetable, target_container, source_va, target_va),
        progress_thread == source_thread || progress_thread == target_thread,
        old(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress.view() is Some,
        ({
            let progress = old(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress.view()->Some_0;
            &&& progress is Share4k
            &&& progress->Share4k_shared < progress->Share4k_source_range.len
            &&& progress->Share4k_shared < progress->Share4k_target_range.len
            &&& progress->Share4k_source_range.view()[progress->Share4k_shared as int] == source_va
            &&& progress->Share4k_target_range.view()[progress->Share4k_shared as int] == target_va
        }),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(progress_thread),
        share_4k_objects_k(*old(krnl), cpu_id).source_thread == source_thread && share_4k_objects_k(*old(krnl), cpu_id).quota_thread == target_thread,
        share_4k_objects_k(*old(krnl), cpu_id).target == target_process && share_4k_objects_k(*old(krnl), cpu_id).target_container == target_container,
        share_4k_objects_k(*old(krnl), cpu_id).transfer_source is Some ==> old(lctx).container_lock_map().dom().contains(target_container),
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(steps).view() == old(steps).view().push(final(steps).view().last()),
        final(steps).view().last().old_u == old(steps).snapshot_u(),
        share_4k_leaf_step_pre(old(steps).snapshot_u(), cpu_id),
        share_4k_leaf_step(old(steps).snapshot_u(), final(steps).view().last().new_u, cpu_id),
        share_4k_objects_k(*final(krnl), cpu_id) == share_4k_objects_k(*old(krnl), cpu_id),
        forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view())]
            old(lctx).pagetable_lock_map().dom().contains(pt)
            && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
            ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_lock_map().dom() == set![source_thread, target_thread],
        final(lctx).pagetable_lock_map().dom() == set![source_pagetable, target_pagetable],
        final(krnl).thr_mp.dom().contains(source_thread),
        final(krnl).thr_mp.dom().contains(target_thread),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), source_thread, TypedLockMode::Write),
        !final(krnl).thr_mp.spec_index(source_thread).being_killed(),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), target_thread, TypedLockMode::Write),
        !final(krnl).thr_mp.spec_index(target_thread).being_killed(),
        final(krnl).thr_mp.spec_index(source_thread).view().owning_proc != target_process,
        final(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        mmap_4k_quota_thread_container_compatible(final(krnl), final(lctx), target_thread, target_container),
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
        final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
        final(steps).nonlock_view().subrange(0, old(steps).nonlock_view().len() as int) == old(steps).nonlock_view(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        {
            let source_process = old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr;
            &&& final(steps).nonlock_view().last().new_u.process_map.dom().contains(source_process)
            &&& kernel_k_to_nonlock_kernel_u(*final(krnl)).process_map.dom().contains(source_process)
            &&& final(steps).nonlock_view().last().new_u.process_map.spec_index(source_process).pagetable == kernel_k_to_nonlock_kernel_u(*final(krnl)).process_map.spec_index(source_process).pagetable
            &&& final(steps).nonlock_view().last().new_u.process_map.dom().contains(target_process)
            &&& final(steps).nonlock_view().last().new_u.thread_map.dom().contains(target_thread)
            &&& kernel_k_to_nonlock_kernel_u(*final(krnl)).thread_map.dom().contains(target_thread)
            &&& final(steps).nonlock_view().last().new_u.thread_map.spec_index(target_thread) == kernel_k_to_nonlock_kernel_u(*final(krnl)).thread_map.spec_index(target_thread)
            &&& typed_lock_map_contains_mode(old(lctx).process_lock_map(), target_process, TypedLockMode::Write) && ({
                let iommu_table = old(krnl).prc_mp.spec_index(target_process).view().iommu_table;
                ||| iommu_table is None
                ||| iommu_table is Some && old(lctx).iommu_table_lock_map().dom().contains(iommu_table.unwrap())
            }) ==> {
                &&& kernel_k_to_nonlock_kernel_u(*final(krnl)).process_map.dom().contains(target_process)
                &&& final(steps).nonlock_view().last().new_u.process_map.spec_index(target_process) == kernel_k_to_nonlock_kernel_u(*final(krnl)).process_map.spec_index(target_process)
            }
        },
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
        final(krnl).thr_mp.lock_id_by_key(target_thread) == old(krnl).thr_mp.lock_id_by_key(target_thread),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
        held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
        held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
        held_cpu_sets_unchanged(old(krnl).cpu_set_mp, final(krnl).cpu_set_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        final(krnl).thr_mp.spec_index(progress_thread).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress, ..old(krnl).thr_mp.spec_index(progress_thread).view() }),
        final(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress.view() == share_4k_progress_after_leaf(old(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress.view()),
        progress_thread != target_thread ==> final(krnl).thr_mp.spec_index(target_thread).view() == old(krnl).thr_mp.spec_index(target_thread).view(),
        progress_thread != source_thread ==> final(krnl).thr_mp.spec_index(source_thread).view() == old(krnl).thr_mp.spec_index(source_thread).view(),
        final(krnl).ctn_mp.dom().contains(target_container),
        final(krnl).ctn_mp.spec_index(target_container).view_rodata() == old(krnl).ctn_mp.spec_index(target_container).view_rodata(),
        final(krnl).prc_mp.spec_index(target_process).view_rodata() == old(krnl).prc_mp.spec_index(target_process).view_rodata(),
        final(krnl).pt_mp.spec_index(source_pagetable).view() == old(krnl).pt_mp.spec_index(source_pagetable).view(),
        final(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k() == old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k().insert(target_va, old(krnl).pt_mp.spec_index(source_pagetable).view().mapping_4k().spec_index(source_va)),
        final(krnl).pt_mp.spec_index(target_pagetable).view().user_view(LockStateU::Unlocked).mapping_4k == old(krnl).pt_mp.spec_index(target_pagetable).view().user_view(LockStateU::Unlocked).mapping_4k.insert(target_va, old(krnl).pt_mp.spec_index(source_pagetable).view().user_view(LockStateU::Unlocked).mapping_4k.spec_index(source_va)),
        final(krnl).pt_mp.spec_index(target_pagetable).view().mapping_2m() == old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_2m(),
        final(krnl).pt_mp.spec_index(target_pagetable).view().mapping_1g() == old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_1g(),
        final(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end,
        final(krnl).pt_mp.spec_index(target_pagetable).view().page_closure() == old(krnl).pt_mp.spec_index(target_pagetable).view().page_closure(),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
            #![trigger final(krnl).pt_mp.spec_index(target_pagetable).view().spec_resolve_mapping_l2(l4i, l3i, l2i)]
            final(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end <= l4i && pei_valid(l4i)
                && pei_valid(l3i) && pei_valid(l2i) ==> final(krnl).pt_mp.spec_index(target_pagetable).view().spec_resolve_mapping_l2(l4i, l3i, l2i) == old(krnl).pt_mp.spec_index(target_pagetable).view().spec_resolve_mapping_l2(l4i, l3i, l2i),
        {
            let page_ptr = old(krnl).pt_mp.spec_index(source_pagetable).view().mapping_4k().spec_index(source_va).addr;
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
    }) by { spec_va_4k_index_roundtrip_at(source_va, source_indices.0, source_indices.1, source_indices.2, source_indices.3); reveal(PageTable::wf_mapping_4k); };
    let source_entry;
    {
        let source = krnl.pt_mp.borrow_typed(source_pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(source_pagetable_lock_perm));
        source_entry = source.resolve_mapping_4k_l1(source_indices.0, source_indices.1, source_indices.2, source_indices.3).2.unwrap();
    }
    let page_ptr = source_entry.addr;
    proof {
        assert({
            &&& source_entry =~= krnl.pt_mp.spec_index(source_pagetable).view().mapping_4k().spec_index(source_va)
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
            &&& krnl.pg_arr.spec_index(page_index).view().view().state is Mapped4k
            &&& !lctx.page_lock_map().dom().contains(page_index)
            &&& krnl.pg_arr.lock_id_by_index(page_index).major == MAPPED_PAGE_LOCK_MAJOR
        }) by { page_ptr_valid_imply_page_index_valid(); reveal(mapped_4k_page_pagetable_wf); };
    }
    let Tracked(page_lock_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));
    proof {
        assert({
            &&& krnl.pg_arr.inv()
            &&& krnl.pg_arr.spec_index(page_index).view().inv()
        }) by { reveal(page_array_wf); };
        assert({
            &&& !krnl.pg_arr.spec_index(page_index).view().view().mappings().contains((target_pagetable, target_va))
            &&& krnl.pg_arr.spec_index(page_index).view().view().ref_count < usize::MAX
        }) by { reveal(mapped_4k_page_pagetable_wf); mapped_4k_page_ref_count_lt_usize_max(krnl.pt_mp, krnl.pg_arr, page_index); };
    }
    page_array_add_4k_mapping(&mut krnl.pg_arr, page_index, target_pagetable, target_va, Tracked(&*lctx), Tracked(&page_lock_perm));
    proof {
        assert(spec_index2va(target_indices) == target_va) by { spec_va_4k_index_roundtrip_at(target_va, target_indices.0, target_indices.1, target_indices.2, target_indices.3); };
    }
    pagetable_map_insert_4k(&mut krnl.pt_mp, target_pagetable, target_indices, target_l1_ptr, &source_entry, Tracked(&mut *lctx), Tracked(target_pagetable_lock_perm));

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
                    let target_entry = krnl.pt_mp.spec_index(target_pagetable).view().mapping_4k().spec_index(target_va);
                    target_entry.owning_container@ == krnl.pg_arr.spec_index(page_index).view().view().owning_container
                }) by { reveal(mapped_4k_page_pagetable_wf); };
                page_pagetable_wf_preserved_for_4k_mapping_insert(old(krnl).pt_mp, krnl.pt_mp, old(krnl).pg_arr, krnl.pg_arr, target_pagetable, page_ptr, target_va);
            };
            assert(container_process_page_pagetable_wf(krnl.ctn_mp, krnl.prc_mp, krnl.pt_mp, krnl.pg_arr)) by {
                assert({
                    let owner = krnl.pg_arr.spec_index(page_index).view().view().owning_container;
                    let mapping_process = krnl.pt_mp.spec_index(target_pagetable).view().proc_ptr;
                    let mapping_container = krnl.prc_mp.spec_index(mapping_process).view_rodata().view().owning_container;
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
    }
    krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_lock_perm));
    proof {
        assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
            map_insert_remove_absent_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock {
                lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write,
            });
        };
        assert(krnl.pt_mp.spec_index(target_pagetable).view().user_view(LockStateU::Unlocked).mapping_4k =~= old(krnl).pt_mp.spec_index(target_pagetable).view().user_view(LockStateU::Unlocked).mapping_4k.insert(target_va, old(krnl).pt_mp.spec_index(source_pagetable).view().user_view(LockStateU::Unlocked).mapping_4k.spec_index(source_va))) by { vstd::map::axiom_map_ext_equal(krnl.pt_mp.spec_index(target_pagetable).view().user_view(LockStateU::Unlocked).mapping_4k, old(krnl).pt_mp.spec_index(target_pagetable).view().user_view(LockStateU::Unlocked).mapping_4k.insert(target_va, old(krnl).pt_mp.spec_index(source_pagetable).view().user_view(LockStateU::Unlocked).mapping_4k.spec_index(source_va))); };
    }
    krnl.set_thread_syscall_progress(progress_thread, Ghost(share_4k_progress_after_leaf(krnl.thr_mp.spec_index(progress_thread).view().syscall_progress.view())), Tracked(&*lctx),
        Tracked(if progress_thread == source_thread { source_thread_lock_perm } else { target_thread_lock_perm }));
    proof {
        assert(kernel_process_4k_mapping_changed(&steps.snapshot_k(), &*krnl, target_process, target_pagetable, target_va)) by { reveal(kernel_process_4k_mapping_changed); reveal(process_pagetable_match); };
        let ghost source_process = old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr;
        assert({
            &&& krnl.prc_mp.dom().contains(source_process)
            &&& !krnl.prc_mp.spec_index(source_process).view().zombie
            &&& krnl.prc_mp.spec_index(source_process).view().pagetable == source_pagetable
        }) by { reveal(process_pagetable_match); };
        assert(!krnl.prc_mp.spec_index(target_process).view().zombie
            && krnl.prc_mp.spec_index(target_process).view().pagetable == target_pagetable) by { reveal(process_pagetable_match); };
        assert(share_4k_leaf_step_pre(kernel_k_to_kernel_u(*old(krnl)), cpu_id) && share_4k_leaf_step(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), cpu_id)) by {
            kernel_4k_mapping_copied_implies_u_step(old(krnl), &*krnl, old(lctx), source_process, target_process, source_pagetable, target_pagetable, source_va, target_va, progress_thread);
            kernel_share_4k_objects_projection(old(krnl), old(lctx), cpu_id);
            share_4k_leaf_step_from_u(
                kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), cpu_id, progress_thread, source_thread, source_process, target_process, source_va, target_va,
            );
        };
        krnl.kernel_step_boundary_process_4k_mapping_changed(&mut *lctx, &mut *steps, target_process, target_pagetable, target_va, source_process, source_pagetable, target_thread);
        assert({
            let mapped_page = krnl.pt_mp.spec_index(target_pagetable).view().mapping_4k().spec_index(target_va).addr;
            krnl.pg_arr.spec_index(page_ptr2page_index(mapped_page)).view().view().mappings().contains((target_pagetable, target_va))
        }) by { reveal(mapped_4k_page_pagetable_wf); };
        assert({
            &&& krnl.ctn_mp.dom().contains(target_container)
            &&& krnl.prc_mp.dom().contains(target_process)
            &&& krnl.prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container
            &&& krnl.prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable
            &&& ((krnl.thr_mp.spec_index(target_thread).view().owning_proc == target_process && krnl.thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable) || typed_lock_map_contains_mode(lctx.process_lock_map(), target_process, TypedLockMode::Write))
        }) by { reveal(process_pagetable_match); reveal(container_process_wf); };
        assert(krnl.thr_mp.lock_id_by_key(target_thread) == old(krnl).thr_mp.lock_id_by_key(target_thread)) by {
            thread_lock_id_preserved_for_typed_maps_unchanged(old(krnl), &*krnl, old(lctx), &*lctx, target_thread);
        };
        assert(share_4k_objects_k(*krnl, cpu_id) == share_4k_objects_k(*old(krnl), cpu_id)) by { reveal(share_4k_objects_k); };
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
        old(lctx).thread_lock_map().dom() == set![source_thread, target_thread],
        old(lctx).pagetable_lock_map().dom() == set![source_pagetable, target_pagetable],
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(krnl).pg_arr.lock_id_by_index(held_page).major < MAPPED_PAGE_LOCK_MAJOR,
        source_pagetable != target_pagetable,
        old(krnl).thr_mp.dom().contains(source_thread),
        old(krnl).thr_mp.dom().contains(target_thread),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), source_thread, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(source_thread).being_killed(),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), target_thread, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(target_thread).being_killed(),
        old(krnl).thr_mp.spec_index(source_thread).view().owning_proc != target_process,
        old(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        mmap_4k_quota_thread_container_compatible(old(krnl), old(lctx), target_thread, target_container),
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
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        old(krnl).irt.owners() == old(steps).snapshot_k().irt.owners(),
        old(krnl).irt.iommu_roots() == old(steps).snapshot_k().irt.iommu_roots(),
        old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
        old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        source_range.wf(),
        old(krnl).pt_mp.spec_index(source_pagetable).view().kernel_l4_end <= spec_va2index(source_range.start).0,
        share_mapping_4k_source_range_present(old(krnl), source_pagetable, source_range),
        old(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process,
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        source_range.len > 0 ==> final(steps).snapshot_k() == *final(krnl),
        final(steps).view() == if source_range.len == 0 { old(steps).view() }
            else { record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(krnl))) },
        forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view())]
            old(lctx).pagetable_lock_map().dom().contains(pt)
            && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
            ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_lock_map().dom() == set![source_thread, target_thread],
        final(lctx).pagetable_lock_map().dom() == set![source_pagetable, target_pagetable],
        final(krnl).thr_mp.dom().contains(source_thread),
        final(krnl).thr_mp.dom().contains(target_thread),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), source_thread, TypedLockMode::Write),
        !final(krnl).thr_mp.spec_index(source_thread).being_killed(),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), target_thread, TypedLockMode::Write),
        !final(krnl).thr_mp.spec_index(target_thread).being_killed(),
        final(krnl).thr_mp.spec_index(source_thread).view().owning_proc != target_process,
        final(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        mmap_4k_quota_thread_container_compatible(final(krnl), final(lctx), target_thread, target_container),
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
        final(steps).nonlock_view().len() == old(steps).nonlock_view().len(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
        final(krnl).irt.owners() == final(steps).snapshot_k().irt.owners(),
        final(krnl).irt.iommu_roots() == final(steps).snapshot_k().irt.iommu_roots(),
        final(krnl).cpu_tlb.view() == final(steps).snapshot_k().cpu_tlb.view(),
        final(krnl).iommu_tlb.view() == final(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(krnl)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
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
        share_mapping_4k_source_range_present(final(krnl), source_pagetable, source_range),
        ret == share_mapping_4k_range_owner_compatible(final(krnl), source_pagetable, target_container, source_range),
{
    proof { steps.rebase_snapshot_k_if_unchanged(&*krnl); }

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
            &&& held_pages_unchanged(old(krnl).pg_arr, krnl.pg_arr, old(lctx))
        }) by { held_kernel_objects_unchanged_reflexive(krnl, lctx); };
    }
    let mut i: usize = 0;
    let mut all_compatible = true;
    while i < source_range.len
        invariant
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            i == 0 ==> *krnl == *old(krnl) && steps.view() == old(steps).view() && steps.snapshot_u() == old(steps).snapshot_u(),
            i > 0 ==> steps.snapshot_k() == *krnl && steps.view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(krnl))),
            forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pt, krnl.pt_mp.spec_index(pt).view())]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pt, krnl.pt_mp.spec_index(pt).view()),
            krnl.inv(),
            lctx.kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(krnl, &*lctx),
            lctx.thread_lock_map().dom() == set![source_thread, target_thread],
            lctx.pagetable_lock_map().dom() == set![source_pagetable, target_pagetable],
            lctx.pcid_needflush_lock_map().dom().is_empty(),
            lctx.scheduler_lock_map().dom().is_empty(),
            lctx.cpu_set_lock_map().dom().is_empty(),
            forall|held_cpu_id: CpuId| #![trigger lctx.cpu_lock_map().dom().contains(held_cpu_id)] lctx.cpu_lock_map().dom().contains(held_cpu_id) ==> !(krnl.cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            forall|held_page: PageIndex| #![trigger lctx.page_lock_map().dom().contains(held_page)] lctx.page_lock_map().dom().contains(held_page) ==> krnl.pg_arr.lock_id_by_index(held_page).major < MAPPED_PAGE_LOCK_MAJOR,
            source_pagetable != target_pagetable,
            krnl.thr_mp.dom().contains(source_thread),
            krnl.thr_mp.dom().contains(target_thread),
            typed_lock_map_contains_mode(lctx.thread_lock_map(), source_thread, TypedLockMode::Write),
            !krnl.thr_mp.spec_index(source_thread).being_killed(),
            typed_lock_map_contains_mode(lctx.thread_lock_map(), target_thread, TypedLockMode::Write),
            !krnl.thr_mp.spec_index(target_thread).being_killed(),
            krnl.thr_mp.spec_index(source_thread).view().owning_proc != target_process,
            krnl.thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
            mmap_4k_quota_thread_container_compatible(krnl, lctx, target_thread, target_container),
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
            steps.nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), krnl),
            kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp),
            krnl.irt.owners() == steps.snapshot_k().irt.owners(),
            krnl.irt.iommu_roots() == steps.snapshot_k().irt.iommu_roots(),
            krnl.cpu_tlb.view() == steps.snapshot_k().cpu_tlb.view(),
            krnl.iommu_tlb.view() == steps.snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), krnl),
            index_valid(NUM_CPUS, cpu_id),
            krnl.cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
            typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
            lctx.cpu_lock_map().dom().contains(cpu_id),
            krnl.cpu_arr.lock_id_by_index(cpu_id) == old(krnl).cpu_arr.lock_id_by_index(cpu_id),
            source_range.wf(),
            krnl.pt_mp.spec_index(source_pagetable).view().wf(),
            krnl.pt_mp.spec_index(source_pagetable).view().kernel_l4_end <= spec_va2index(source_range.start).0,
            share_mapping_4k_source_range_present(krnl, source_pagetable, source_range),
            0 <= i <= source_range.len,
            all_compatible == share_mapping_4k_range_owner_compatible_prefix(krnl, source_pagetable, target_container, source_range, i as int),
            steps.nonlock_view().len() == old(steps).nonlock_view().len(),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
            typed_lock_maps_unchanged(old(lctx), lctx),
            held_pages_unchanged(old(krnl).pg_arr, krnl.pg_arr, old(lctx)),
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
            krnl.pt_mp.spec_index(source_pagetable).view() == old(krnl).pt_mp.spec_index(source_pagetable).view(),
            krnl.pt_mp.spec_index(target_pagetable).view() == old(krnl).pt_mp.spec_index(target_pagetable).view(),
            krnl.thr_mp.spec_index(target_thread).view() == old(krnl).thr_mp.spec_index(target_thread).view(),
            krnl.thr_mp.spec_index(source_thread).view() == old(krnl).thr_mp.spec_index(source_thread).view(),
            krnl.thr_mp.spec_index(target_thread).view().owning_proc == target_process,
            lctx.holds_no_allocator_locks(PageSize::SZ4k),
            lctx.holds_no_allocator_locks(PageSize::SZ2m),
            lctx.holds_no_allocator_locks(PageSize::SZ1g),
        decreases source_range.len - i,
    {
        let source_va = source_range.index(i);
        let source_indices = va2index(source_va);
        proof {
            pagetable_perms_wf_at(krnl.pt_mp, source_pagetable);
            assert({
                &&& spec_index2va(source_indices) == source_va
                &&& krnl.pt_mp.spec_index(source_pagetable).view().spec_resolve_mapping_4k_l1(source_indices.0, source_indices.1, source_indices.2, source_indices.3) is Some
            }) by { spec_va_4k_index_roundtrip_at(source_va, source_indices.0, source_indices.1, source_indices.2, source_indices.3); };
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
                &&& source_entry =~= krnl.pt_mp.spec_index(source_pagetable).view().mapping_4k().spec_index(source_va)
                &&& page_ptr_valid(page_ptr)
                &&& index_valid(NUM_PAGES, page_index)
                &&& !lctx.page_lock_map().dom().contains(page_index)
                &&& krnl.pg_arr.lock_id_by_index(page_index).major == MAPPED_PAGE_LOCK_MAJOR
            }) by { page_ptr_valid_imply_page_index_valid(); };
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
                }) by { container_page_owner_backward_at(krnl.ctn_mp, krnl.pg_arr, page_index); reveal(container_thread_wf); };
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
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
            use_type_invariant(&*steps);
            assert(if i == 0 { kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl)) }
                else { kernel_k_to_kernel_u(*krnl) == steps.snapshot_u() }) by {
                if i == 0 {
                    reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
                    kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(old(krnl), &*krnl);
                }
                else { kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl); }
            };
            krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
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
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl) && kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)
                && kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by {
                broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, kernel_endpoint_nonlock_fields_unchanged_for_equal;
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
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
    krnl: &mut KernelK, source_range: &VaRange4K, target_range: &VaRange4K, source_thread: RwLockThreadPtr, target_thread: RwLockThreadPtr,
    progress_thread: RwLockThreadPtr, target_process: RwLockProcessPtr, target_container: RwLockContainerPtr, cpu_id: CpuId,
    source_pagetable: RwLockPageTableRoot, target_pagetable: RwLockPageTableRoot, Ghost(origin): Ghost<Share4kOrigin>, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>, Tracked(source_thread_lock_perm): Tracked<&LockPerm>, Tracked(target_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>, Tracked(target_pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() == set![source_thread, target_thread],
        old(lctx).pagetable_lock_map().dom() == set![source_pagetable, target_pagetable],
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
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
        old(steps).snapshot_k() == *old(krnl),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).ctn_mp.dom().contains(target_container),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        source_range.wf(),
        old(krnl).pt_mp.spec_index(source_pagetable).view().wf(),
        old(krnl).pt_mp.spec_index(source_pagetable).view().kernel_l4_end <= spec_va2index(source_range.start).0,
        target_range.wf(),
        source_range.len == target_range.len,
        share_mapping_4k_source_range_present(old(krnl), source_pagetable, source_range),
        share_mapping_4k_range_structure_ready_from(old(krnl), source_pagetable, target_pagetable, source_range, target_range, 0),
        share_mapping_4k_range_owner_compatible(old(krnl), source_pagetable, target_container, source_range),
        progress_thread == source_thread || progress_thread == target_thread,
        old(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress.view() == Some(SyscallProgress::Share4k { source_range: *source_range, target_range: *target_range, shared: 0, origin }),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(progress_thread),
        share_4k_objects_k(*old(krnl), cpu_id).source_thread == source_thread && share_4k_objects_k(*old(krnl), cpu_id).quota_thread == target_thread,
        share_4k_objects_k(*old(krnl), cpu_id).target == target_process && share_4k_objects_k(*old(krnl), cpu_id).target_container == target_container,
        share_4k_objects_k(*old(krnl), cpu_id).transfer_source is Some ==> old(lctx).container_lock_map().dom().contains(target_container),
    ensures
        forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view())]
            old(lctx).pagetable_lock_map().dom().contains(pt)
            && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
            ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).page_lock_map().dom().is_empty(),
        final(lctx).thread_lock_map().dom() == set![source_thread, target_thread],
        final(lctx).pagetable_lock_map().dom() == set![source_pagetable, target_pagetable],
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
        old(steps).nonlock_view().len() as int + source_range.len as int <= final(steps).nonlock_view().len() as int,
        final(steps).nonlock_view().len() as int <= old(steps).nonlock_view().len() as int + 4 * source_range.len as int,
        final(steps).nonlock_view().subrange(0, old(steps).nonlock_view().len() as int) == old(steps).nonlock_view(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(krnl).pt_mp.spec_index(source_pagetable).view() == old(krnl).pt_mp.spec_index(source_pagetable).view(),
        final(krnl).thr_mp.spec_index(progress_thread).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress, ..old(krnl).thr_mp.spec_index(progress_thread).view() }),
        final(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress.view() == Some(SyscallProgress::Share4k { source_range: *source_range, target_range: *target_range, shared: source_range.len, origin }),
        progress_thread != source_thread ==> final(krnl).thr_mp.spec_index(source_thread).view() == old(krnl).thr_mp.spec_index(source_thread).view(),
        final(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k() == share_mapping_4k_target_map_with_shared_prefix(old(krnl).pt_mp.spec_index(source_pagetable).view().mapping_4k(), old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k(), source_range, target_range, source_range.len as nat),
        share_mapping_4k_range_mapped_prefix(final(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k(), target_range, source_range.len as int),
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
    assert(krnl.pt_mp.spec_index(target_pagetable).view().mapping_4k() == share_mapping_4k_target_map_with_shared_prefix(
        krnl.pt_mp.spec_index(source_pagetable).view().mapping_4k(), krnl.pt_mp.spec_index(target_pagetable).view().mapping_4k(),
        source_range, target_range, 0,
    )) by { reveal(share_mapping_4k_target_map_with_shared_prefix); };
    assert(share_mapping_4k_range_mapped_prefix(krnl.pt_mp.spec_index(target_pagetable).view().mapping_4k(), target_range, 0)) by { reveal(share_mapping_4k_range_mapped_prefix); };
    let mut i: usize = 0;
    while i < source_range.len
        invariant
            forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pt, krnl.pt_mp.spec_index(pt).view())]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pt, krnl.pt_mp.spec_index(pt).view()),
            krnl.inv(),
            lctx.kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(krnl, &*lctx),
            lctx.page_lock_map().dom().is_empty(),
            lctx.thread_lock_map().dom() == set![source_thread, target_thread],
            lctx.pagetable_lock_map().dom() == set![source_pagetable, target_pagetable],
            lctx.pcid_needflush_lock_map().dom().is_empty(),
            lctx.scheduler_lock_map().dom().is_empty(),
            lctx.cpu_set_lock_map().dom().is_empty(),
            forall|held_cpu_id: CpuId| #![trigger lctx.cpu_lock_map().dom().contains(held_cpu_id)] lctx.cpu_lock_map().dom().contains(held_cpu_id) ==> !(krnl.cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
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
            steps.nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
            steps.snapshot_k() == *krnl,
            index_valid(NUM_CPUS, cpu_id),
            typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
            lctx.cpu_lock_map().dom().contains(cpu_id),
            lctx.holds_no_allocator_locks(PageSize::SZ4k),
            lctx.holds_no_allocator_locks(PageSize::SZ2m),
            lctx.holds_no_allocator_locks(PageSize::SZ1g),
            source_range.wf(),
            krnl.pt_mp.spec_index(source_pagetable).view().wf(),
            krnl.pt_mp.spec_index(source_pagetable).view().kernel_l4_end <= spec_va2index(source_range.start).0,
            target_range.wf(),
            source_range.len == target_range.len,
            0 <= i <= source_range.len,
            steps.nonlock_view().len() == old(steps).nonlock_view().len() + i,
            steps.nonlock_view().subrange(0, old(steps).nonlock_view().len() as int) == old(steps).nonlock_view(),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
            typed_lock_maps_unchanged(old(lctx), lctx),
            old(krnl).pt_mp.dom().contains(source_pagetable),
            old(krnl).pt_mp.dom().contains(target_pagetable),
            krnl.ctn_mp.dom().contains(target_container),
            krnl.pt_mp.spec_index(source_pagetable).view() == old(krnl).pt_mp.spec_index(source_pagetable).view(),
            progress_thread == source_thread || progress_thread == target_thread,
            krnl.thr_mp.spec_index(progress_thread).view() == (Thread { syscall_progress: krnl.thr_mp.spec_index(progress_thread).view().syscall_progress, ..old(krnl).thr_mp.spec_index(progress_thread).view() }),
            krnl.thr_mp.spec_index(progress_thread).view().syscall_progress.view() == Some(SyscallProgress::Share4k { source_range: *source_range, target_range: *target_range, shared: i, origin }),
            krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(progress_thread),
            share_4k_objects_k(*krnl, cpu_id).source_thread == source_thread && share_4k_objects_k(*krnl, cpu_id).quota_thread == target_thread,
            share_4k_objects_k(*krnl, cpu_id).target == target_process && share_4k_objects_k(*krnl, cpu_id).target_container == target_container,
            share_4k_objects_k(*krnl, cpu_id).transfer_source is Some ==> lctx.container_lock_map().dom().contains(target_container),
            progress_thread != source_thread ==> krnl.thr_mp.spec_index(source_thread).view() == old(krnl).thr_mp.spec_index(source_thread).view(),
            share_mapping_4k_source_range_present(krnl, source_pagetable, source_range),
            share_mapping_4k_range_owner_compatible(krnl, source_pagetable, target_container, source_range),
            share_mapping_4k_range_structure_ready_from(krnl, source_pagetable, target_pagetable, source_range, target_range, i as int),
            krnl.pt_mp.spec_index(target_pagetable).view().mapping_4k() == share_mapping_4k_target_map_with_shared_prefix(old(krnl).pt_mp.spec_index(source_pagetable).view().mapping_4k(), old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k(), source_range, target_range, i as nat),
            share_mapping_4k_range_mapped_prefix(krnl.pt_mp.spec_index(target_pagetable).view().mapping_4k(), target_range, i as int),
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
        share_one_mapping_4k(
            krnl, source_thread, target_thread, progress_thread, target_process, target_container, source_pagetable, target_pagetable,
            cpu_id, source_va, target_va, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(source_thread_lock_perm), Tracked(target_thread_lock_perm),
            Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm),
        );
        proof {
            assert(steps.nonlock_view().subrange(0, old(steps).nonlock_view().len() as int) == old(steps).nonlock_view()) by { vstd::seq::lemma_seq_subrange_composition(steps.nonlock_view(), 0, (steps.nonlock_view().len() - 1) as int, 0, old(steps).nonlock_view().len() as int); };
            assert(share_mapping_4k_source_range_present(krnl, source_pagetable, source_range)) by {
                reveal(mapped_4k_page_pagetable_wf);
                page_ptr_valid_imply_page_index_valid();
            };
            assert(share_mapping_4k_range_owner_compatible(krnl, source_pagetable, target_container, source_range)) by { reveal(mapped_4k_page_pagetable_wf); reveal(container_thread_wf); };
            assert(krnl.pt_mp.spec_index(target_pagetable).view().wf()) by { pagetable_perms_wf_at(krnl.pt_mp, target_pagetable); };
            assert(share_mapping_4k_range_structure_ready_from(krnl, source_pagetable, target_pagetable, source_range, target_range, (i + 1) as int)) by {
                source_range.va_range_lemma(); target_range.va_range_lemma();
            };
            assert(krnl.pt_mp.spec_index(target_pagetable).view().mapping_4k() == share_mapping_4k_target_map_with_shared_prefix(
                old(krnl).pt_mp.spec_index(source_pagetable).view().mapping_4k(), old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k(),
                source_range, target_range, (i + 1) as nat,
            )) by { reveal(share_mapping_4k_target_map_with_shared_prefix); source_range.va_range_lemma(); target_range.va_range_lemma(); };
            assert(share_mapping_4k_range_mapped_prefix(krnl.pt_mp.spec_index(target_pagetable).view().mapping_4k(), target_range, (i + 1) as int)) by {
                reveal(share_mapping_4k_range_mapped_prefix); seq_index_lemma::<VAddr>(); target_range.va_range_lemma();
            };
        }
        i = i + 1;
    }
    proof {
        assert(share_mapping_4k_reverse_mappings(krnl, target_pagetable, target_range)) by {
            reveal(share_mapping_4k_range_mapped_prefix);
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
        initial_target.is_empty() || initial_target.spec_mapping_4k_va_range_buildable(target_range),
        current_target.mapping_1g() == initial_target.mapping_1g(),
        current_target.mapping_2m() == initial_target.mapping_2m(),
        share_mapping_4k_target_range_empty_from(current_target.mapping_4k(), target_range, i as int),
    ensures
        va_4k_valid(target_va),
        current_target.kernel_l4_end <= spec_v2l4index(target_va),
        pei_valid(spec_v2l4index(target_va)),
        pei_valid(spec_v2l3index(target_va)),
        pei_valid(spec_v2l2index(target_va)),
        pei_valid(spec_v2l1index(target_va)),
        initial_target.spec_4k_entry_usable(spec_v2l4index(target_va), spec_v2l3index(target_va), spec_v2l2index(target_va), spec_v2l1index(target_va)),
        current_target.spec_resolve_mapping_1g_l3(spec_v2l4index(target_va), spec_v2l3index(target_va)) is None,
        current_target.spec_resolve_mapping_2m_l2(spec_v2l4index(target_va), spec_v2l3index(target_va), spec_v2l2index(target_va)) is None,
        !current_target.mapping_4k().dom().contains(target_va),
        current_target.spec_resolve_mapping_4k_l1(spec_v2l4index(target_va), spec_v2l3index(target_va), spec_v2l2index(target_va), spec_v2l1index(target_va)) is None,
        current_target.spec_4k_entry_usable(spec_v2l4index(target_va), spec_v2l3index(target_va), spec_v2l2index(target_va), spec_v2l1index(target_va)),
{
    assert({
        &&& spec_va_4k_valid(target_range.start)
        &&& spec_va_4k_valid(target_va)
        &&& target_range.start <= target_va
        &&& va_4k_valid(target_va)
    }) by { target_range.va_range_lemma(); };
    spec_v2l4index_monotonic(target_range.start, target_va);
    assert({
        &&& pei_valid(spec_v2l4index(target_va))
        &&& pei_valid(spec_v2l3index(target_va))
        &&& pei_valid(spec_v2l2index(target_va))
        &&& pei_valid(spec_v2l1index(target_va))
    }) by { spec_va_4k_valid_imply_indices_valid(); };
    assert(initial_target.spec_4k_entry_usable(spec_v2l4index(target_va), spec_v2l3index(target_va), spec_v2l2index(target_va), spec_v2l1index(target_va))) by {
        if initial_target.is_empty() {
            spec_va_4k_index_roundtrip_at(target_va, spec_v2l4index(target_va), spec_v2l3index(target_va), spec_v2l2index(target_va), spec_v2l1index(target_va));
        } else {
            assert(initial_target.spec_resolve_mapping_4k_l1(
                spec_va2index(target_range.view().spec_index(i as int)).0, spec_va2index(target_range.view().spec_index(i as int)).1,
                spec_va2index(target_range.view().spec_index(i as int)).2, spec_va2index(target_range.view().spec_index(i as int)).3,
            ) is None) by { seq_index_lemma::<VAddr>(); };
        }
    };
    assert({
        &&& current_target.spec_resolve_mapping_1g_l3(spec_v2l4index(target_va), spec_v2l3index(target_va)) is None
        &&& current_target.spec_resolve_mapping_2m_l2(spec_v2l4index(target_va), spec_v2l3index(target_va), spec_v2l2index(target_va)) is None
    }) by { reveal(PageTable::wf_mapping_1g); reveal(PageTable::wf_mapping_2m); };
    assert({
        &&& !current_target.mapping_4k().dom().contains(target_va)
        &&& current_target.spec_resolve_mapping_4k_l1(spec_v2l4index(target_va), spec_v2l3index(target_va), spec_v2l2index(target_va), spec_v2l1index(target_va)) is None
    }) by {
        reveal(share_mapping_4k_target_range_empty_from); reveal(PageTable::wf_mapping_4k);
        spec_va_4k_index_roundtrip_at(target_va, spec_v2l4index(target_va), spec_v2l3index(target_va), spec_v2l2index(target_va), spec_v2l1index(target_va));
    };
}

#[verifier::spinoff_prover]
proof fn prove_share_mapping_4k_iteration_target_partition(
    source: Map<VAddr, MapEntry>, initial_target: Map<VAddr, MapEntry>, previous_target: PageTable<PT_TYPE>, current_target: PageTable<PT_TYPE>,
    source_range: &VaRange4K, target_range: &VaRange4K, i: usize, source_va: VAddr, target_va: VAddr,
)
    requires
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        0 <= i < source_range.len,
        source_va == source_range.view().spec_index(i as int),
        target_va == target_range.view().spec_index(i as int),
        previous_target.mapping_4k() == share_mapping_4k_target_map_with_shared_prefix(source, initial_target, source_range, target_range, i as nat),
        current_target.mapping_4k() == previous_target.mapping_4k().insert(target_va, source.spec_index(source_va)),
        share_mapping_4k_range_mapped_prefix(previous_target.mapping_4k(), target_range, i as int),
        share_mapping_4k_target_range_empty_from(previous_target.mapping_4k(), target_range, i as int),
    ensures
        current_target.mapping_4k() == share_mapping_4k_target_map_with_shared_prefix(source, initial_target, source_range, target_range, (i + 1) as nat),
        share_mapping_4k_range_mapped_prefix(current_target.mapping_4k(), target_range, (i + 1) as int),
        share_mapping_4k_target_range_empty_from(current_target.mapping_4k(), target_range, (i + 1) as int),
{
    assert(current_target.mapping_4k() == share_mapping_4k_target_map_with_shared_prefix(source, initial_target, source_range, target_range, (i + 1) as nat)) by {
        reveal(share_mapping_4k_target_map_with_shared_prefix); source_range.va_range_lemma(); target_range.va_range_lemma();
    };
    assert(share_mapping_4k_range_mapped_prefix(current_target.mapping_4k(), target_range, (i + 1) as int)) by {
        reveal(share_mapping_4k_range_mapped_prefix); seq_index_lemma::<VAddr>(); target_range.va_range_lemma();
    };
    assert(share_mapping_4k_target_range_empty_from(current_target.mapping_4k(), target_range, (i + 1) as int)) by {
        reveal(share_mapping_4k_target_range_empty_from); seq_index_lemma::<VAddr>(); target_range.va_range_lemma();
    };
}

/// Build each missing target directory path and immediately share its 4K leaf.
/// All fallible checks are completed by the caller before this function starts.
#[verifier::spinoff_prover]
pub fn share_mapping_4k_build_and_share(
    krnl: &mut KernelK, source_range: &VaRange4K, target_range: &VaRange4K, target_allocator: RwLockPageAllocatorPtr,
    source_thread: RwLockThreadPtr, quota_thread: RwLockThreadPtr, progress_thread: RwLockThreadPtr, target_process: RwLockProcessPtr,
    target_container: RwLockContainerPtr, cpu_id: CpuId, source_pagetable: RwLockPageTableRoot, target_pagetable: RwLockPageTableRoot,
    transfer_source: Option<RwLockContainerPtr>, Ghost(origin): Ghost<Share4kOrigin>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    Tracked(source_thread_lock_perm): Tracked<&LockPerm>, Tracked(quota_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>, Tracked(target_pagetable_lock_perm): Tracked<&LockPerm>,
    Tracked(transfer_source_lock_perm): Tracked<Option<&LockPerm>>, Tracked(transfer_target_lock_perm): Tracked<Option<&LockPerm>>,
)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).thread_lock_map().dom() == set![source_thread, quota_thread],
        old(lctx).pagetable_lock_map().dom() == set![source_pagetable, target_pagetable],
        held_locks_order_below(old(krnl), old(lctx), MAPPED_PAGE_LOCK_MAJOR),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(krnl).thr_mp.dom().contains(source_thread),
        old(krnl).thr_mp.dom().contains(quota_thread),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), source_thread, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(source_thread).being_killed(),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), quota_thread, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(quota_thread).being_killed(),
        old(krnl).thr_mp.spec_index(source_thread).view().owning_proc != target_process,
        old(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        transfer_source is None ==> old(krnl).thr_mp.spec_index(quota_thread).view().owning_container == target_container,
        transfer_source is Some ==> {
            let source = transfer_source->Some_0;
            &&& source == old(krnl).thr_mp.spec_index(quota_thread).view().owning_container
            &&& source != target_container
            &&& old(krnl).ctn_mp.dom().contains(source)
            &&& old(krnl).ctn_mp.spec_index(target_container).view_rodata().view().parent == Some(source)
            &&& typed_lock_map_contains_mode(old(lctx).container_lock_map(), source, TypedLockMode::Write)
            &&& typed_lock_map_contains_mode(old(lctx).container_lock_map(), target_container, TypedLockMode::Write)
            &&& !old(krnl).ctn_mp.spec_index(source).being_killed()
            &&& !old(krnl).ctn_mp.spec_index(target_container).being_killed()
            &&& transfer_source_lock_perm is Some
            &&& transfer_source_lock_perm->Some_0.state() is WriteLock
            &&& transfer_source_lock_perm->Some_0.thread_id() == old(lctx).thread_id()
            &&& transfer_source_lock_perm->Some_0.lock_id() == old(krnl).ctn_mp.spec_index(source).locking_thread()->Write_lock_id
            &&& transfer_target_lock_perm is Some
            &&& transfer_target_lock_perm->Some_0.state() is WriteLock
            &&& transfer_target_lock_perm->Some_0.thread_id() == old(lctx).thread_id()
            &&& transfer_target_lock_perm->Some_0.lock_id() == old(krnl).ctn_mp.spec_index(target_container).locking_thread()->Write_lock_id
        },
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
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).ctn_mp.dom().contains(target_container),
        old(krnl).ctn_mp.spec_index(target_container).view_rodata().view().allocator_ptr_4k == target_allocator,
        old(krnl).allc_4k_mp.dom().contains(target_allocator),
        old(steps).snapshot_k() == *old(krnl),
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        share_mapping_4k_source_range_present(old(krnl), source_pagetable, source_range),
        share_mapping_4k_range_owner_compatible(old(krnl), source_pagetable, target_container, source_range),
        old(krnl).thr_mp.spec_index(quota_thread).view().temp_alloc_cache_2m.view().len() == 0,
        old(krnl).thr_mp.spec_index(quota_thread).view().temp_alloc_cache_1g.view().len() == 0,
        progress_thread == source_thread || progress_thread == quota_thread,
        old(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress.view() == Some(SyscallProgress::Share4k { source_range: *source_range, target_range: *target_range, shared: 0, origin }),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(progress_thread),
        share_4k_objects_k(*old(krnl), cpu_id).source_thread == source_thread && share_4k_objects_k(*old(krnl), cpu_id).quota_thread == quota_thread,
        share_4k_objects_k(*old(krnl), cpu_id).target == target_process && share_4k_objects_k(*old(krnl), cpu_id).target_container == target_container,
        share_4k_objects_k(*old(krnl), cpu_id).transfer_source == transfer_source,
        quota_thread != progress_thread ==> old(krnl).thr_mp.spec_index(quota_thread).view().syscall_progress.view() is None,
        old(krnl).thr_mp.spec_index(quota_thread).view().free_quota_pending_clean(),
        thread_effective_quota_4k(old(krnl).thr_mp.spec_index(quota_thread)) >= 3 * target_range.len,
        old(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end <= spec_v2l4index(target_range.start),
        old(krnl).pt_mp.spec_index(target_pagetable).view().spec_mapping_4k_va_range_empty(target_range.start, target_range.view().spec_index((target_range.len - 1) as int)),
        old(krnl).pt_mp.spec_index(target_pagetable).view().is_empty() || old(krnl).pt_mp.spec_index(target_pagetable).view().spec_mapping_4k_va_range_buildable(target_range),
        old(krnl).pt_mp.spec_index(target_pagetable).view().leaves_present(),
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() + source_range.len <= final(steps).view().len() <= old(steps).view().len() + 4 * source_range.len,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len()
            ==> share_4k_range_step(final(steps).view()[j], cpu_id),
        forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view())]
            old(lctx).pagetable_lock_map().dom().contains(pt)
            && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
            ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(krnl).thr_mp.dom().contains(source_thread),
        final(krnl).thr_mp.dom().contains(quota_thread),
        !final(krnl).thr_mp.spec_index(source_thread).being_killed(),
        final(krnl).ctn_mp.dom().contains(target_container),
        final(krnl).ctn_mp.spec_index(target_container).view_rodata() == old(krnl).ctn_mp.spec_index(target_container).view_rodata(),
        final(krnl).prc_mp.dom().contains(target_process),
        final(krnl).prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container,
        final(krnl).prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable,
        source_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(source_thread).locking_thread()->Write_lock_id,
        quota_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(quota_thread).locking_thread()->Write_lock_id,
        final(krnl).pt_mp.dom().contains(source_pagetable),
        final(krnl).pt_mp.dom().contains(target_pagetable),
        final(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
        target_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        transfer_source is None ==> held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        transfer_source is Some ==> {
            let source = transfer_source->Some_0;
            let old_source_pages = old(krnl).ctn_mp.spec_index(source).view().owned_pages.view();
            let new_source_pages = final(krnl).ctn_mp.spec_index(source).view().owned_pages.view();
            &&& final(krnl).ctn_mp.dom().contains(source)
            &&& final(krnl).ctn_mp.spec_index(source).is_init() == old(krnl).ctn_mp.spec_index(source).is_init()
            &&& final(krnl).ctn_mp.spec_index(source).view_rodata() == old(krnl).ctn_mp.spec_index(source).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(source).view_ghost() == old(krnl).ctn_mp.spec_index(source).view_ghost()
            &&& final(krnl).ctn_mp.spec_index(source).locking_thread() == old(krnl).ctn_mp.spec_index(source).locking_thread()
            &&& final(krnl).ctn_mp.spec_index(source).being_killed() == old(krnl).ctn_mp.spec_index(source).being_killed()
            &&& final(krnl).ctn_mp.spec_index(source).view() == (Container { owned_pages: final(krnl).ctn_mp.spec_index(source).view().owned_pages, ..old(krnl).ctn_mp.spec_index(source).view() })
            &&& final(krnl).ctn_mp.dom().contains(target_container)
            &&& final(krnl).ctn_mp.spec_index(target_container).is_init() == old(krnl).ctn_mp.spec_index(target_container).is_init()
            &&& final(krnl).ctn_mp.spec_index(target_container).view_rodata() == old(krnl).ctn_mp.spec_index(target_container).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(target_container).view_ghost() == old(krnl).ctn_mp.spec_index(target_container).view_ghost()
            &&& final(krnl).ctn_mp.spec_index(target_container).locking_thread() == old(krnl).ctn_mp.spec_index(target_container).locking_thread()
            &&& final(krnl).ctn_mp.spec_index(target_container).being_killed() == old(krnl).ctn_mp.spec_index(target_container).being_killed()
            &&& final(krnl).ctn_mp.spec_index(target_container).view() == (Container { owned_pages: final(krnl).ctn_mp.spec_index(target_container).view().owned_pages, ..old(krnl).ctn_mp.spec_index(target_container).view() })
            &&& new_source_pages.subset_of(old_source_pages)
            &&& final(krnl).ctn_mp.spec_index(target_container).view().owned_pages.view() =~= old(krnl).ctn_mp.spec_index(target_container).view().owned_pages.view().union(old_source_pages.difference(new_source_pages))
        },
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        old(steps).nonlock_view().len() as int + source_range.len as int <= final(steps).nonlock_view().len() as int,
        final(steps).nonlock_view().len() as int <= old(steps).nonlock_view().len() as int + 4 * source_range.len as int,
        final(steps).nonlock_view().subrange(0, old(steps).nonlock_view().len() as int) == old(steps).nonlock_view(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
        final(krnl).irt.owners() == final(steps).snapshot_k().irt.owners(),
        final(krnl).irt.iommu_roots() == final(steps).snapshot_k().irt.iommu_roots(),
        final(krnl).cpu_tlb.view() == final(steps).snapshot_k().cpu_tlb.view(),
        final(krnl).iommu_tlb.view() == final(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(krnl)),
        {
            let source_process = old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr;
            &&& final(steps).nonlock_view().last().new_u.process_map.dom().contains(source_process)
            &&& kernel_k_to_nonlock_kernel_u(*final(krnl)).process_map.dom().contains(source_process)
            &&& final(steps).nonlock_view().last().new_u.process_map.spec_index(source_process).pagetable == kernel_k_to_nonlock_kernel_u(*final(krnl)).process_map.spec_index(source_process).pagetable
            &&& final(steps).nonlock_view().last().new_u.process_map.dom().contains(target_process)
            &&& final(steps).nonlock_view().last().new_u.thread_map.dom().contains(quota_thread)
            &&& kernel_k_to_nonlock_kernel_u(*final(krnl)).thread_map.dom().contains(quota_thread)
            &&& final(steps).nonlock_view().last().new_u.thread_map.spec_index(quota_thread) == kernel_k_to_nonlock_kernel_u(*final(krnl)).thread_map.spec_index(quota_thread)
            &&& typed_lock_map_contains_mode(old(lctx).process_lock_map(), target_process, TypedLockMode::Write) && ({
                let iommu_table = old(krnl).prc_mp.spec_index(target_process).view().iommu_table;
                ||| iommu_table is None
                ||| iommu_table is Some && old(lctx).iommu_table_lock_map().dom().contains(iommu_table.unwrap())
            }) ==> {
                &&& kernel_k_to_nonlock_kernel_u(*final(krnl)).process_map.dom().contains(target_process)
                &&& final(steps).nonlock_view().last().new_u.process_map.spec_index(target_process) == kernel_k_to_nonlock_kernel_u(*final(krnl)).process_map.spec_index(target_process)
            }
        },
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
        final(krnl).thr_mp.spec_index(quota_thread).view().caller == old(krnl).thr_mp.spec_index(quota_thread).view().caller,
        final(krnl).thr_mp.spec_index(quota_thread).view().callee == old(krnl).thr_mp.spec_index(quota_thread).view().callee,
        final(krnl).thr_mp.spec_index(quota_thread).view().owning_container == old(krnl).thr_mp.spec_index(quota_thread).view().owning_container,
        final(krnl).thr_mp.spec_index(quota_thread).view().quota_2m == old(krnl).thr_mp.spec_index(quota_thread).view().quota_2m,
        final(krnl).thr_mp.spec_index(quota_thread).view().quota_1g == old(krnl).thr_mp.spec_index(quota_thread).view().quota_1g,
        final(krnl).thr_mp.spec_index(quota_thread).view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(quota_thread).view().endpoint_descriptors.view(),
        final(krnl).thr_mp.spec_index(quota_thread).view().ipc_payload == old(krnl).thr_mp.spec_index(quota_thread).view().ipc_payload,
        final(krnl).thr_mp.spec_index(quota_thread).view().error_code == old(krnl).thr_mp.spec_index(quota_thread).view().error_code,
        final(krnl).thr_mp.spec_index(quota_thread).view().trap_frame == old(krnl).thr_mp.spec_index(quota_thread).view().trap_frame,
        final(krnl).thr_mp.spec_index(quota_thread).being_killed() == old(krnl).thr_mp.spec_index(quota_thread).being_killed(),
        final(krnl).thr_mp.lock_id_by_key(quota_thread) == old(krnl).thr_mp.lock_id_by_key(quota_thread),
        final(krnl).pt_mp.spec_index(source_pagetable).view() == old(krnl).pt_mp.spec_index(source_pagetable).view(),
        progress_thread != source_thread ==> final(krnl).thr_mp.spec_index(source_thread).view() == old(krnl).thr_mp.spec_index(source_thread).view(),
        source_thread != quota_thread ==> final(krnl).thr_mp.spec_index(source_thread).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(source_thread).view().syscall_progress, ..old(krnl).thr_mp.spec_index(source_thread).view() }),
        final(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress.view() == Some(SyscallProgress::Share4k { source_range: *source_range, target_range: *target_range, shared: source_range.len, origin }),
        final(krnl).thr_mp.spec_index(quota_thread).view().temp_alloc_cache_4k.view() == old(krnl).thr_mp.spec_index(quota_thread).view().temp_alloc_cache_4k.view(),
        final(krnl).thr_mp.spec_index(quota_thread).view().temp_alloc_cache_2m.view().len() == 0,
        final(krnl).thr_mp.spec_index(quota_thread).view().temp_alloc_cache_1g.view().len() == 0,
        final(krnl).thr_mp.spec_index(quota_thread).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(quota_thread).view().owning_proc == old(krnl).thr_mp.spec_index(quota_thread).view().owning_proc,
        final(krnl).thr_mp.spec_index(quota_thread).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(quota_thread).view().proc_pagetable_ptr,
        final(krnl).thr_mp.spec_index(quota_thread).view().state == old(krnl).thr_mp.spec_index(quota_thread).view().state,
        quota_thread != progress_thread ==> final(krnl).thr_mp.spec_index(quota_thread).view().syscall_progress.view() is None,
        final(krnl).thr_mp.spec_index(quota_thread).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(quota_thread).view().blocking_endpoint_ptr,
        final(krnl).thr_mp.spec_index(quota_thread).view().quota_4k <= old(krnl).thr_mp.spec_index(quota_thread).view().quota_4k,
        final(krnl).thr_mp.spec_index(quota_thread).view().quota_4k >= old(krnl).thr_mp.spec_index(quota_thread).view().quota_4k - 3 * target_range.len,
        final(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k() == share_mapping_4k_target_map_with_shared_prefix(old(krnl).pt_mp.spec_index(source_pagetable).view().mapping_4k(), old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k(), source_range, target_range, source_range.len as nat),
        final(krnl).pt_mp.spec_index(target_pagetable).view().user_view(LockStateU::Unlocked).mapping_4k == share_mapping_4k_target_map_with_shared_prefix(old(krnl).pt_mp.spec_index(source_pagetable).view().user_view(LockStateU::Unlocked).mapping_4k, old(krnl).pt_mp.spec_index(target_pagetable).view().user_view(LockStateU::Unlocked).mapping_4k, source_range, target_range, source_range.len as nat),
        final(krnl).pt_mp.spec_index(target_pagetable).view().mapping_2m() == old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_2m(),
        final(krnl).pt_mp.spec_index(target_pagetable).view().mapping_1g() == old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_1g(),
        final(krnl).pt_mp.spec_index(target_pagetable).view().leaves_present(),
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
            &&& held_pages_unchanged(old(krnl).pg_arr, krnl.pg_arr, old(lctx))
        }) by { held_kernel_objects_unchanged_reflexive(krnl, lctx); };
        assert(krnl.pt_mp.spec_index(target_pagetable).view().wf()) by { pagetable_perms_wf_at(krnl.pt_mp, target_pagetable); };
        assert(share_mapping_4k_target_range_empty_from(krnl.pt_mp.spec_index(target_pagetable).view().mapping_4k(), target_range, 0)) by { reveal(share_mapping_4k_target_range_empty_from);
            reveal(PageTable::spec_mapping_4k_va_range_empty);
            target_range.va_range_lemma();
        };
    }
    assert(krnl.pt_mp.spec_index(target_pagetable).view().mapping_4k() == share_mapping_4k_target_map_with_shared_prefix(
        krnl.pt_mp.spec_index(source_pagetable).view().mapping_4k(), krnl.pt_mp.spec_index(target_pagetable).view().mapping_4k(),
        source_range, target_range, 0,
    )) by { reveal(share_mapping_4k_target_map_with_shared_prefix); };
    assert(krnl.pt_mp.spec_index(target_pagetable).view().user_view(LockStateU::Unlocked).mapping_4k == share_mapping_4k_target_map_with_shared_prefix(
        old(krnl).pt_mp.spec_index(source_pagetable).view().user_view(LockStateU::Unlocked).mapping_4k,
        old(krnl).pt_mp.spec_index(target_pagetable).view().user_view(LockStateU::Unlocked).mapping_4k, source_range, target_range, 0,
    )) by { reveal(share_mapping_4k_target_map_with_shared_prefix); };
    assert(share_mapping_4k_range_mapped_prefix(krnl.pt_mp.spec_index(target_pagetable).view().mapping_4k(), target_range, 0)) by { reveal(share_mapping_4k_range_mapped_prefix); };
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl) && kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)
            && kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by {
            broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, group_kernel_endpoint_nonlock_fields_unchanged_transitive;
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
        };
    }
    let mut i: usize = 0;
    while i < source_range.len
        invariant
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            steps.snapshot_k() == *krnl,
            old(steps).view().len() + i <= steps.view().len() <= old(steps).view().len() + 4 * i,
            forall|j: int| #![trigger steps.view()[j]] 0 <= j < old(steps).view().len() ==> steps.view()[j] == old(steps).view()[j],
            forall|j: int| #![trigger steps.view()[j]] old(steps).view().len() <= j < steps.view().len()
                ==> share_4k_range_step(steps.view()[j], cpu_id),
            forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pt, krnl.pt_mp.spec_index(pt).view())]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pt, krnl.pt_mp.spec_index(pt).view()),
            krnl.inv(),
            lctx.kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(krnl, &*lctx),
            lctx.thread_lock_map().dom() == set![source_thread, quota_thread],
            lctx.pagetable_lock_map().dom() == set![source_pagetable, target_pagetable],
            held_locks_order_below(krnl, lctx, MAPPED_PAGE_LOCK_MAJOR),
            lctx.scheduler_lock_map().dom().is_empty(),
            lctx.cpu_set_lock_map().dom().is_empty(),
            krnl.thr_mp.dom().contains(source_thread),
            krnl.thr_mp.dom().contains(quota_thread),
            typed_lock_map_contains_mode(lctx.thread_lock_map(), source_thread, TypedLockMode::Write),
            !krnl.thr_mp.spec_index(source_thread).being_killed(),
            typed_lock_map_contains_mode(lctx.thread_lock_map(), quota_thread, TypedLockMode::Write),
            !krnl.thr_mp.spec_index(quota_thread).being_killed(),
            krnl.thr_mp.spec_index(source_thread).view().owning_proc != target_process,
            krnl.thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
            transfer_source is None ==> krnl.thr_mp.spec_index(quota_thread).view().owning_container == target_container,
            transfer_source is Some ==> {
                let source = transfer_source->Some_0;
                &&& source == krnl.thr_mp.spec_index(quota_thread).view().owning_container
                &&& source != target_container
                &&& krnl.ctn_mp.dom().contains(source)
                &&& krnl.ctn_mp.spec_index(target_container).view_rodata().view().parent == Some(source)
                &&& typed_lock_map_contains_mode(lctx.container_lock_map(), source, TypedLockMode::Write)
                &&& typed_lock_map_contains_mode(lctx.container_lock_map(), target_container, TypedLockMode::Write)
                &&& !krnl.ctn_mp.spec_index(source).being_killed()
                &&& !krnl.ctn_mp.spec_index(target_container).being_killed()
                &&& transfer_source_lock_perm is Some
                &&& transfer_source_lock_perm->Some_0.state() is WriteLock
                &&& transfer_source_lock_perm->Some_0.thread_id() == lctx.thread_id()
                &&& transfer_source_lock_perm->Some_0.lock_id() == krnl.ctn_mp.spec_index(source).locking_thread()->Write_lock_id
                &&& transfer_target_lock_perm is Some
                &&& transfer_target_lock_perm->Some_0.state() is WriteLock
                &&& transfer_target_lock_perm->Some_0.thread_id() == lctx.thread_id()
                &&& transfer_target_lock_perm->Some_0.lock_id() == krnl.ctn_mp.spec_index(target_container).locking_thread()->Write_lock_id
            },
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
            krnl.ctn_mp.spec_index(target_container).view_rodata() == old(krnl).ctn_mp.spec_index(target_container).view_rodata(),
            krnl.allc_4k_mp.dom().contains(target_allocator),
            steps.nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), krnl),
            kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp),
            krnl.irt.owners() == steps.snapshot_k().irt.owners(),
            krnl.irt.iommu_roots() == steps.snapshot_k().irt.iommu_roots(),
            krnl.cpu_tlb.view() == steps.snapshot_k().cpu_tlb.view(),
            krnl.iommu_tlb.view() == steps.snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), krnl),
            transfer_source is None ==> held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx)),
            transfer_source is Some ==> {
                let source = transfer_source->Some_0;
                let old_source_pages = old(krnl).ctn_mp.spec_index(source).view().owned_pages.view();
                let new_source_pages = krnl.ctn_mp.spec_index(source).view().owned_pages.view();
                &&& krnl.ctn_mp.dom().contains(source)
                &&& krnl.ctn_mp.spec_index(source).is_init() == old(krnl).ctn_mp.spec_index(source).is_init()
                &&& krnl.ctn_mp.spec_index(source).view_rodata() == old(krnl).ctn_mp.spec_index(source).view_rodata()
                &&& krnl.ctn_mp.spec_index(source).view_ghost() == old(krnl).ctn_mp.spec_index(source).view_ghost()
                &&& krnl.ctn_mp.spec_index(source).locking_thread() == old(krnl).ctn_mp.spec_index(source).locking_thread()
                &&& krnl.ctn_mp.spec_index(source).being_killed() == old(krnl).ctn_mp.spec_index(source).being_killed()
                &&& krnl.ctn_mp.spec_index(source).view() == (Container { owned_pages: krnl.ctn_mp.spec_index(source).view().owned_pages, ..old(krnl).ctn_mp.spec_index(source).view() })
                &&& krnl.ctn_mp.dom().contains(target_container)
                &&& krnl.ctn_mp.spec_index(target_container).is_init() == old(krnl).ctn_mp.spec_index(target_container).is_init()
                &&& krnl.ctn_mp.spec_index(target_container).view_rodata() == old(krnl).ctn_mp.spec_index(target_container).view_rodata()
                &&& krnl.ctn_mp.spec_index(target_container).view_ghost() == old(krnl).ctn_mp.spec_index(target_container).view_ghost()
                &&& krnl.ctn_mp.spec_index(target_container).locking_thread() == old(krnl).ctn_mp.spec_index(target_container).locking_thread()
                &&& krnl.ctn_mp.spec_index(target_container).being_killed() == old(krnl).ctn_mp.spec_index(target_container).being_killed()
                &&& krnl.ctn_mp.spec_index(target_container).view() == (Container { owned_pages: krnl.ctn_mp.spec_index(target_container).view().owned_pages, ..old(krnl).ctn_mp.spec_index(target_container).view() })
                &&& new_source_pages.subset_of(old_source_pages)
                &&& krnl.ctn_mp.spec_index(target_container).view().owned_pages.view() =~= old(krnl).ctn_mp.spec_index(target_container).view().owned_pages.view().union(old_source_pages.difference(new_source_pages))
            },
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
            old(steps).nonlock_view().len() as int + i as int <= steps.nonlock_view().len() as int,
            steps.nonlock_view().len() as int <= old(steps).nonlock_view().len() as int + 4 * i as int,
            steps.nonlock_view().subrange(0, old(steps).nonlock_view().len() as int) == old(steps).nonlock_view(),
            i > 0 ==> {
                let source_process = old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr;
                &&& steps.nonlock_view().last().new_u.process_map.dom().contains(source_process)
                &&& kernel_k_to_nonlock_kernel_u(*krnl).process_map.dom().contains(source_process)
                &&& steps.nonlock_view().last().new_u.process_map.spec_index(source_process).pagetable == kernel_k_to_nonlock_kernel_u(*krnl).process_map.spec_index(source_process).pagetable
                &&& old(krnl).prc_mp.dom().contains(target_process)
                &&& steps.nonlock_view().last().new_u.process_map.dom().contains(target_process)
                &&& steps.nonlock_view().last().new_u.thread_map.dom().contains(quota_thread)
                &&& kernel_k_to_nonlock_kernel_u(*krnl).thread_map.dom().contains(quota_thread)
                &&& steps.nonlock_view().last().new_u.thread_map.spec_index(quota_thread) == kernel_k_to_nonlock_kernel_u(*krnl).thread_map.spec_index(quota_thread)
                &&& typed_lock_map_contains_mode(old(lctx).process_lock_map(), target_process, TypedLockMode::Write) && ({
                    let iommu_table = old(krnl).prc_mp.spec_index(target_process).view().iommu_table;
                    ||| iommu_table is None
                    ||| iommu_table is Some && old(lctx).iommu_table_lock_map().dom().contains(iommu_table.unwrap())
                }) ==> {
                    &&& kernel_k_to_nonlock_kernel_u(*krnl).process_map.dom().contains(target_process)
                    &&& steps.nonlock_view().last().new_u.process_map.spec_index(target_process) == kernel_k_to_nonlock_kernel_u(*krnl).process_map.spec_index(target_process)
                }
            },
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
            old(krnl).inv(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            typed_lock_maps_unchanged(old(lctx), lctx),
            held_pages_unchanged(old(krnl).pg_arr, krnl.pg_arr, old(lctx)),
            old(lctx).thread_lock_map().dom().contains(quota_thread),
            old(krnl).prc_mp.dom().contains(target_process),
            old(krnl).pt_mp.dom().contains(source_pagetable),
            krnl.thr_mp.spec_index(quota_thread).view().caller == old(krnl).thr_mp.spec_index(quota_thread).view().caller,
            krnl.thr_mp.spec_index(quota_thread).view().callee == old(krnl).thr_mp.spec_index(quota_thread).view().callee,
            krnl.thr_mp.spec_index(quota_thread).view().owning_container == old(krnl).thr_mp.spec_index(quota_thread).view().owning_container,
            krnl.thr_mp.spec_index(quota_thread).view().quota_2m == old(krnl).thr_mp.spec_index(quota_thread).view().quota_2m,
            krnl.thr_mp.spec_index(quota_thread).view().quota_1g == old(krnl).thr_mp.spec_index(quota_thread).view().quota_1g,
            krnl.thr_mp.spec_index(quota_thread).view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(quota_thread).view().endpoint_descriptors.view(),
            krnl.thr_mp.spec_index(quota_thread).view().ipc_payload == old(krnl).thr_mp.spec_index(quota_thread).view().ipc_payload,
            krnl.thr_mp.spec_index(quota_thread).view().error_code == old(krnl).thr_mp.spec_index(quota_thread).view().error_code,
            krnl.thr_mp.spec_index(quota_thread).view().trap_frame == old(krnl).thr_mp.spec_index(quota_thread).view().trap_frame,
            krnl.thr_mp.spec_index(quota_thread).being_killed() == old(krnl).thr_mp.spec_index(quota_thread).being_killed(),
            krnl.thr_mp.lock_id_by_key(quota_thread) == old(krnl).thr_mp.lock_id_by_key(quota_thread),
            krnl.pt_mp.spec_index(source_pagetable).view() == old(krnl).pt_mp.spec_index(source_pagetable).view(),
            progress_thread == source_thread || progress_thread == quota_thread,
            progress_thread != source_thread ==> krnl.thr_mp.spec_index(source_thread).view() == old(krnl).thr_mp.spec_index(source_thread).view(),
            source_thread != quota_thread ==> krnl.thr_mp.spec_index(source_thread).view() == (Thread { syscall_progress: krnl.thr_mp.spec_index(source_thread).view().syscall_progress, ..old(krnl).thr_mp.spec_index(source_thread).view() }),
            krnl.thr_mp.spec_index(progress_thread).view().syscall_progress.view() == Some(SyscallProgress::Share4k { source_range: *source_range, target_range: *target_range, shared: i, origin }),
            krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(progress_thread),
            share_4k_objects_k(*krnl, cpu_id).source_thread == source_thread && share_4k_objects_k(*krnl, cpu_id).quota_thread == quota_thread,
            share_4k_objects_k(*krnl, cpu_id).target == target_process && share_4k_objects_k(*krnl, cpu_id).target_container == target_container,
            share_4k_objects_k(*krnl, cpu_id).transfer_source == transfer_source,
            krnl.thr_mp.spec_index(quota_thread).view().upper_container_seq == old(krnl).thr_mp.spec_index(quota_thread).view().upper_container_seq,
            krnl.thr_mp.spec_index(quota_thread).view().owning_proc == old(krnl).thr_mp.spec_index(quota_thread).view().owning_proc,
            krnl.thr_mp.spec_index(quota_thread).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(quota_thread).view().proc_pagetable_ptr,
            krnl.thr_mp.spec_index(quota_thread).view().state == old(krnl).thr_mp.spec_index(quota_thread).view().state,
            quota_thread != progress_thread ==> krnl.thr_mp.spec_index(quota_thread).view().syscall_progress.view() is None,
            krnl.thr_mp.spec_index(quota_thread).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(quota_thread).view().blocking_endpoint_ptr,
            share_mapping_4k_source_range_present(krnl, source_pagetable, source_range),
            share_mapping_4k_range_owner_compatible(krnl, source_pagetable, target_container, source_range),
            krnl.thr_mp.spec_index(quota_thread).view().temp_alloc_cache_4k.view() == old(krnl).thr_mp.spec_index(quota_thread).view().temp_alloc_cache_4k.view(),
            krnl.thr_mp.spec_index(quota_thread).view().temp_alloc_cache_2m.view().len() == 0,
            krnl.thr_mp.spec_index(quota_thread).view().temp_alloc_cache_1g.view().len() == 0,
            krnl.thr_mp.spec_index(quota_thread).view().free_quota_pending_clean(),
            thread_effective_quota_4k(krnl.thr_mp.spec_index(quota_thread)) >= 3 * (target_range.len - i),
            krnl.thr_mp.spec_index(quota_thread).view().quota_4k >= old(krnl).thr_mp.spec_index(quota_thread).view().quota_4k - 3 * i,
            krnl.thr_mp.spec_index(quota_thread).view().quota_4k <= old(krnl).thr_mp.spec_index(quota_thread).view().quota_4k,
            old(krnl).pt_mp.spec_index(target_pagetable).view().wf(),
            krnl.pt_mp.spec_index(target_pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end,
            krnl.pt_mp.spec_index(target_pagetable).view().kernel_l4_end <= spec_v2l4index(target_range.start),
            krnl.pt_mp.spec_index(target_pagetable).view().mapping_2m() == old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_2m(),
            krnl.pt_mp.spec_index(target_pagetable).view().mapping_1g() == old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_1g(),
            krnl.pt_mp.spec_index(target_pagetable).view().leaves_present(),
            old(krnl).pt_mp.spec_index(target_pagetable).view().wf_mapping_1g(),
            old(krnl).pt_mp.spec_index(target_pagetable).view().wf_mapping_2m(),
            old(krnl).pt_mp.spec_index(target_pagetable).view().wf_mapping_4k(),
            old(krnl).pt_mp.spec_index(target_pagetable).view().is_empty() || old(krnl).pt_mp.spec_index(target_pagetable).view().spec_mapping_4k_va_range_buildable(target_range),
            krnl.pt_mp.spec_index(target_pagetable).view().mapping_4k() == share_mapping_4k_target_map_with_shared_prefix(old(krnl).pt_mp.spec_index(source_pagetable).view().mapping_4k(), old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k(), source_range, target_range, i as nat),
            krnl.pt_mp.spec_index(target_pagetable).view().user_view(LockStateU::Unlocked).mapping_4k == share_mapping_4k_target_map_with_shared_prefix(old(krnl).pt_mp.spec_index(source_pagetable).view().user_view(LockStateU::Unlocked).mapping_4k, old(krnl).pt_mp.spec_index(target_pagetable).view().user_view(LockStateU::Unlocked).mapping_4k, source_range, target_range, i as nat),
            share_mapping_4k_range_mapped_prefix(krnl.pt_mp.spec_index(target_pagetable).view().mapping_4k(), target_range, i as int),
            share_mapping_4k_target_range_empty_from(krnl.pt_mp.spec_index(target_pagetable).view().mapping_4k(), target_range, i as int),
        decreases source_range.len - i,
    {
        let source_va = source_range.index(i);
        let target_va = target_range.index(i);
        proof {
            assert(krnl.pt_mp.spec_index(target_pagetable).view().wf()) by { pagetable_perms_wf_at(krnl.pt_mp, target_pagetable); };
            assert(krnl.pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process) by { reveal(process_thread_wf); reveal(process_pagetable_match); };
            prove_share_mapping_4k_build_target_slot_usable(
                krnl.pt_mp.spec_index(target_pagetable).view(), old(krnl).pt_mp.spec_index(target_pagetable).view(), target_range, i, target_va,
            );
        }
        let ghost build_before = steps.view();
        mmap_4k_build_one_structure(
            krnl, target_va, target_allocator, quota_thread, target_process, target_container, cpu_id, target_pagetable, transfer_source, Ghost(progress_thread),
            Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(quota_thread_lock_perm), Tracked(target_pagetable_lock_perm),
            Tracked(transfer_source_lock_perm), Tracked(transfer_target_lock_perm),
        );
        proof {
            assert(forall|j: int| #![trigger steps.view()[j]] old(steps).view().len() <= j < steps.view().len() ==> share_4k_range_step(steps.view()[j], cpu_id)) by {
                share_4k_range_steps_from_directory(&*steps, build_before, old(steps).view().len() as int, cpu_id);
            };
            assert(krnl.pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process) by { reveal(process_thread_wf); reveal(process_pagetable_match); };
            assert(share_mapping_4k_leaf_ready(krnl, source_pagetable, target_pagetable, target_container, source_va, target_va)) by {
                assert(share_mapping_4k_leaf_structure_ready(krnl, source_pagetable, target_pagetable, source_va, target_va)) by { reveal(PageTable::wf_mapping_4k); };
                assert(share_mapping_4k_leaf_owner_compatible(krnl, source_pagetable, target_container, source_va)) by { reveal(mapped_4k_page_pagetable_wf); reveal(container_page_owner_wf); reveal(container_thread_wf); };
            };
        }
        proof { use_type_invariant(&*steps); }
        let ghost target_before_share = krnl.pt_mp.spec_index(target_pagetable).view();
        let ghost leaf_before = steps.view();
        share_one_mapping_4k(
            krnl, source_thread, quota_thread, progress_thread, target_process, target_container, source_pagetable, target_pagetable,
            cpu_id, source_va, target_va, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(source_thread_lock_perm), Tracked(quota_thread_lock_perm),
            Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm),
        );
        proof {
            assert(steps.nonlock_view().subrange(0, old(steps).nonlock_view().len() as int) == old(steps).nonlock_view()) by { vstd::seq::lemma_seq_subrange_composition(steps.nonlock_view(), 0, (steps.nonlock_view().len() - 1) as int, 0, old(steps).nonlock_view().len() as int); };
            assert({
                &&& transfer_source is None ==> held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx))
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
            if krnl.thr_mp.spec_index(quota_thread).view().owning_container == target_container {
                assert(share_mapping_4k_range_owner_compatible(krnl, source_pagetable, target_container, source_range)) by { reveal(mapped_4k_page_pagetable_wf); reveal(container_thread_wf); };
            } else {
                assert(share_mapping_4k_range_owner_compatible(krnl, source_pagetable, target_container, source_range)) by { reveal(mapped_4k_page_pagetable_wf); reveal(container_page_owner_wf); reveal(container_thread_wf); };
            }
            assert(krnl.pt_mp.spec_index(target_pagetable).view().wf()) by { pagetable_perms_wf_at(krnl.pt_mp, target_pagetable); };
            prove_share_mapping_4k_iteration_target_partition(
                old(krnl).pt_mp.spec_index(source_pagetable).view().mapping_4k(), old(krnl).pt_mp.spec_index(target_pagetable).view().mapping_4k(),
                target_before_share, krnl.pt_mp.spec_index(target_pagetable).view(), source_range, target_range, i, source_va, target_va,
            );
        }
        assert(krnl.pt_mp.spec_index(target_pagetable).view().user_view(LockStateU::Unlocked).mapping_4k == share_mapping_4k_target_map_with_shared_prefix(
            old(krnl).pt_mp.spec_index(source_pagetable).view().user_view(LockStateU::Unlocked).mapping_4k,
            old(krnl).pt_mp.spec_index(target_pagetable).view().user_view(LockStateU::Unlocked).mapping_4k,
            source_range, target_range, (i + 1) as nat,
        )) by { reveal(share_mapping_4k_target_map_with_shared_prefix); };
        assert(krnl.allc_4k_mp.dom().contains(target_allocator)) by { reveal(container_allocator_wf); };
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl) && kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)
                && kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by {
                broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, kernel_endpoint_nonlock_fields_unchanged_for_equal;
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
            };
        }
        assert(forall|j: int| #![trigger steps.view()[j]] old(steps).view().len() <= j < steps.view().len() ==> share_4k_range_step(steps.view()[j], cpu_id)) by {
            share_4k_range_steps_from_leaf(&*steps, leaf_before, old(steps).view().len() as int, cpu_id);
        };
        i = i + 1;
    }
    proof {
        assert(share_mapping_4k_reverse_mappings(krnl, target_pagetable, target_range)) by {
            pagetable_perms_wf_at(krnl.pt_mp, target_pagetable);
            reveal(share_mapping_4k_range_mapped_prefix);
            page_ptr_valid_imply_page_index_valid();
            reveal(mapped_4k_page_pagetable_wf);
        };
    }
}
} // verus!
