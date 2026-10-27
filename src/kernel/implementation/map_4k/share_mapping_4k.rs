use vstd::prelude::*;
use crate::*;
use super::share_mapping_4k_trace::*;
use super::share_mapping_4k_precheck_helpers::*;
use super::share_mapping_4k_leaf_copy::share_one_mapping_4k_copy_leaf;
#[cfg(verus_keep_ghost)]
use super::share_mapping_4k_eof::*;

verus! {
pub open spec fn share_mapping_4k_source_range_present(krnl: &KernelK, source_pagetable: RwLockPageTableRoot, source_range: &VaRange4K) -> bool
    recommends
        krnl.pt_mp.dom().contains(source_pagetable),
        pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable).wf(),
        source_range.wf(),
        krnl.pt_mp.spec_index(source_pagetable).view().kernel_l4_end <= spec_va2index(source_range.start).0,
{
    &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable).spec_mapping_4k_va_range_present(source_range)
    &&& forall|i: int|
        #![trigger pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_range.view().spec_index(i))]
        0 <= i < source_range.len ==> {
            let source_va = source_range.view().spec_index(i);
            let source_entry = pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_va);
            let page_index = page_ptr2page_index(source_entry.addr);
            &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable).mapping_4k().dom().contains(source_va)
            &&& source_entry.present
            &&& page_ptr_valid(source_entry.addr)
            &&& index_valid(NUM_PAGES, page_index)
            &&& krnl.pg_arr.spec_index(page_index).view().view().state is Mapped4k
            &&& krnl.pg_arr.spec_index(page_index).view().view().mappings().contains((source_pagetable, source_va))
        }
}

pub open spec fn share_mapping_4k_leaf_structure_ready(krnl: &KernelK, source_pagetable: RwLockPageTableRoot, target_pagetable: RwLockPageTableRoot, source_va: VAddr, target_va: VAddr) -> bool {
    let source_indices = spec_va2index(source_va);
    let target_indices = spec_va2index(target_va);
    &&& va_4k_valid(source_va)
    &&& va_4k_valid(target_va)
    &&& krnl.pt_mp.spec_index(source_pagetable).view().kernel_l4_end <= source_indices.0
    &&& pei_valid(source_indices.0)
    &&& pei_valid(source_indices.1)
    &&& pei_valid(source_indices.2)
    &&& pei_valid(source_indices.3)
    &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable).mapping_4k().dom().contains(source_va)
    &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_va).present
    &&& krnl.pt_mp.spec_index(target_pagetable).view().kernel_l4_end <= target_indices.0
    &&& pei_valid(target_indices.0)
    &&& pei_valid(target_indices.1)
    &&& pei_valid(target_indices.2)
    &&& pei_valid(target_indices.3)
    &&& !pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).mapping_4k().dom().contains(target_va)
    &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).spec_resolve_mapping_l2(target_indices.0, target_indices.1, target_indices.2) is Some
}

pub open spec fn share_mapping_4k_leaf_owner_compatible(krnl: &KernelK, source_pagetable: RwLockPageTableRoot, target_container: RwLockContainerPtr, source_va: VAddr) -> bool {
    let owner = pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_va).owning_container.view();
    &&& krnl.ctn_mp.dom().contains(target_container)
    &&& krnl.ctn_mp.dom().contains(owner)
    &&& (target_container == owner || krnl.ctn_mp.spec_index(target_container).view_ghost().uppertree_seq.view().contains(owner))
}

pub open spec fn share_mapping_4k_leaf_ready(krnl: &KernelK, source_pagetable: RwLockPageTableRoot, target_pagetable: RwLockPageTableRoot, target_container: RwLockContainerPtr, source_va: VAddr, target_va: VAddr) -> bool {
    &&& share_mapping_4k_leaf_structure_ready(krnl, source_pagetable, target_pagetable, source_va, target_va)
    &&& share_mapping_4k_leaf_owner_compatible(krnl, source_pagetable, target_container, source_va)
}

pub open spec fn share_mapping_4k_range_owner_compatible(krnl: &KernelK, source_pagetable: RwLockPageTableRoot, target_container: RwLockContainerPtr, source_range: &VaRange4K) -> bool {
    forall|i: int|
        #![trigger source_range.view().spec_index(i)]
        0 <= i < source_range.len ==> share_mapping_4k_leaf_owner_compatible(krnl, source_pagetable, target_container, source_range.view().spec_index(i))
}

pub open spec fn share_mapping_4k_range_owner_compatible_prefix(krnl: &KernelK, source_pagetable: RwLockPageTableRoot, target_container: RwLockContainerPtr, source_range: &VaRange4K, upper: int) -> bool {
    forall|i: int|
        #![trigger source_range.view().spec_index(i)]
        0 <= i < upper ==> share_mapping_4k_leaf_owner_compatible(krnl, source_pagetable, target_container, source_range.view().spec_index(i))
}

/// A present source range of a well-formed 4K mapping resolves to `Mapped4k` pages that record each source leaf.
pub proof fn share_mapping_4k_source_range_present_from_wf(krnl: &KernelK, source_pagetable: RwLockPageTableRoot, source_range: &VaRange4K)
    requires
        mapped_4k_page_pagetable_wf(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr),
        krnl.pt_mp.dom().contains(source_pagetable),
        pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable).spec_mapping_4k_va_range_present(source_range),
    ensures
        share_mapping_4k_source_range_present(krnl, source_pagetable, source_range),
{ reveal(mapped_4k_page_pagetable_wf); page_ptr_valid_imply_page_index_valid(); }

/// Every leaf of a mapped source range is owned by the source process's own container or one of its ancestors.
pub proof fn share_mapping_4k_range_owner_compatible_own_container(krnl: &KernelK, source_pagetable: RwLockPageTableRoot, container_ptr: RwLockContainerPtr, source_range: &VaRange4K)
    requires
        pagetable_lower_wf(krnl.pt_mp, krnl.pt_lower.view()),
        mapped_4k_page_pagetable_wf(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr),
        container_process_page_pagetable_wf(krnl.ctn_mp, krnl.prc_mp, krnl.pt_mp, krnl.pg_arr),
        container_subtree_set_exclusive(krnl.rt_ctn, krnl.ctn_mp),
        krnl.pt_mp.dom().contains(source_pagetable),
        krnl.ctn_mp.dom().contains(container_ptr),
        krnl.prc_mp.spec_index(krnl.pt_mp.spec_index(source_pagetable).view().proc_ptr).view_rodata().view().owning_container == container_ptr,
        forall|j: int| #![trigger source_range.view().spec_index(j)] 0 <= j < source_range.len ==> pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable).mapping_4k().dom().contains(source_range.view().spec_index(j)),
    ensures
        share_mapping_4k_range_owner_compatible(krnl, source_pagetable, container_ptr, source_range),
{ pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable); reveal(mapped_4k_page_pagetable_wf); reveal(container_process_page_pagetable_wf); reveal(container_subtree_set_exclusive); page_ptr_valid_imply_page_index_valid(); }

/// Target map after copying the first `upper` source-range mappings to the
/// corresponding target-range addresses.
#[verifier::opaque]
pub open spec fn share_mapping_4k_target_map_with_shared_prefix(source: Map<VAddr, MapEntry>, target: Map<VAddr, MapEntry>, source_range: &VaRange4K, target_range: &VaRange4K, upper: nat) -> Map<VAddr, MapEntry>
    decreases upper,
{
    if upper == 0 {
        target
    } else {
        share_mapping_4k_target_map_with_shared_prefix(source, target, source_range, target_range, (upper - 1) as nat).insert(target_range.view().spec_index((upper - 1) as int),
            source.spec_index(source_range.view().spec_index((upper - 1) as int)))
    }
}

/// Every not-yet-shared target VA is still absent from the 4K mapping.
#[verifier::opaque]
pub open spec fn share_mapping_4k_target_range_empty_from(pagetable: Map<VAddr, MapEntry>, target_range: &VaRange4K, first: int) -> bool {
    forall|i: int|
        #![trigger pagetable.dom().contains(target_range.view().spec_index(i))]
        first <= i < target_range.len ==> !pagetable.dom().contains(target_range.view().spec_index(i))
}

/// Checks a source 4K range without mutating krnl or page-table state.
pub fn share_mapping_4k_source_precheck(krnl: &KernelK, source_range: &VaRange4K, source_pagetable: RwLockPageTableRoot, Tracked(lctx): Tracked<&LocalContext>, Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>) -> (ret: bool)
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
            &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable).mapping_4k().dom().contains(source_range.view().spec_index(j))
            &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_range.view().spec_index(j)).present
        },
{
    assert({
        &&& krnl.pt_mp.perms_wf()
        &&& krnl.pt_mp.spec_index(source_pagetable).is_init()
        &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable).wf()
        &&& krnl.pt_lower.view().dom().contains(source_pagetable)
    }) by { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, source_pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable); };
    let pagetable = krnl.pt_mp.borrow_typed(source_pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(source_pagetable_lock_perm));
    let tracked lower = krnl.pt_lower.borrow().tracked_borrow(source_pagetable);
    let ret = pagetable.mapping_4k_va_range_present(Tracked(lower), source_range);
    assert(ret == share_mapping_4k_source_range_present(krnl, source_pagetable, source_range)) by { if ret { share_mapping_4k_source_range_present_from_wf(krnl, source_pagetable, source_range); } };
    ret
}

#[verifier::spinoff_prover]
fn share_one_mapping_4k(
    krnl: &mut KernelK, source_thread: RwLockThreadPtr, target_thread: RwLockThreadPtr, progress_thread: RwLockThreadPtr,
    target_process: RwLockProcessPtr, target_container: RwLockContainerPtr, source_pagetable: RwLockPageTableRoot, target_pagetable: RwLockPageTableRoot, target_write_held: bool,
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
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        forall|held_thread: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(held_thread)] old(lctx).thread_lock_map().dom().contains(held_thread)
            ==> old(krnl).thr_mp.spec_index(held_thread).being_killed() || !(old(krnl).thr_mp.spec_index(held_thread).view().state is SCHEDULED),
        forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(krnl).pg_arr.spec_index(held_page).view().view().orders_below_table_locks(),
        source_pagetable != target_pagetable,
        old(krnl).thr_mp.dom().contains(source_thread),
        old(krnl).thr_mp.dom().contains(target_thread),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), source_thread, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(source_thread).being_killed(),
        !thread_is_dangling(old(krnl).thr_mp.spec_index(source_thread)),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), target_thread, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(target_thread).being_killed(),
        !thread_is_dangling(old(krnl).thr_mp.spec_index(target_thread)),
        old(krnl).thr_mp.spec_index(source_thread).view().owning_proc != target_process,
        old(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        old(krnl).prc_mp.dom().contains(target_process),
        old(krnl).prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container,
        old(krnl).prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable,
        ((old(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process && old(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable
            && !old(krnl).thr_mp.spec_index(target_thread).view_ghost().exited)
            || (typed_lock_map_contains_mode(old(lctx).process_lock_map(), target_process, TypedLockMode::Write) && !old(krnl).prc_mp.spec_index(target_process).view().zombie && !(old(krnl).prc_mp.spec_index(target_process).view().state.view() is TablesEmptied))),
        source_thread_lock_perm.state() is WriteLock,
        source_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        source_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(source_thread).locking_thread()->Write_lock_id,
        target_thread_lock_perm.state() is WriteLock,
        target_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        target_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(target_thread).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable),
        old(krnl).pt_mp.dom().contains(target_pagetable),
        old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == old(krnl).thr_mp.spec_index(source_thread).view().owning_proc,
        old(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        source_pagetable_lock_perm.state() is ReadLock || source_pagetable_lock_perm.state() is WriteLock,
        source_pagetable_lock_perm.state() is ReadLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Read),
        source_pagetable_lock_perm.state() is ReadLock ==> old(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), source_pagetable_lock_perm.lock_id()),
        source_pagetable_lock_perm.state() is WriteLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Write),
        source_pagetable_lock_perm.state() is WriteLock ==> source_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
        target_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        target_pagetable_lock_perm.state() is ReadLock || target_pagetable_lock_perm.state() is WriteLock,
        target_write_held == (target_pagetable_lock_perm.state() is WriteLock),
        target_pagetable_lock_perm.state() is ReadLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Read),
        target_pagetable_lock_perm.state() is ReadLock ==> old(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), target_pagetable_lock_perm.lock_id()),
        target_pagetable_lock_perm.state() is WriteLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
        target_pagetable_lock_perm.state() is WriteLock ==> target_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        old(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, window_of(target_va))),
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
        old(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress.view()->Some_0->Share4k_origin matches Share4kOrigin::IpcPages { peer }
            ==> old(krnl).thr_mp.spec_index(peer).view().state is IPC_TRANSIT && old(krnl).thr_mp.spec_index(peer).view().state->IPC_TRANSIT_partner == progress_thread,
        share_4k_objects_k(*old(krnl), cpu_id).source_thread == source_thread && share_4k_objects_k(*old(krnl), cpu_id).quota_thread == target_thread,
        share_4k_objects_k(*old(krnl), cpu_id).target == target_process && share_4k_objects_k(*old(krnl), cpu_id).target_container == target_container,
        share_4k_objects_k(*old(krnl), cpu_id).transfer_source is Some ==> old(lctx).container_lock_map().dom().contains(target_container),
        share_4k_objects_k(*old(krnl), cpu_id).transfer_source matches Some(source) ==> old(krnl).ctn_mp.spec_index(target_container).view_rodata().view().parent == Some(source),
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(steps).view() == old(steps).view().push(final(steps).view().last()),
        share_4k_leaf_step_pre(final(steps).view().last().old_u, cpu_id),
        share_4k_leaf_step(final(steps).view().last().old_u, final(steps).view().last().new_u, cpu_id),
        share_4k_objects_k(*final(krnl), cpu_id) == share_4k_objects_k(*old(krnl), cpu_id),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(krnl).thr_mp.dom().contains(source_thread),
        final(krnl).thr_mp.dom().contains(target_thread),
        !final(krnl).thr_mp.spec_index(source_thread).being_killed(),
        !thread_is_dangling(final(krnl).thr_mp.spec_index(source_thread)),
        !final(krnl).thr_mp.spec_index(target_thread).being_killed(),
        !thread_is_dangling(final(krnl).thr_mp.spec_index(target_thread)),
        final(krnl).prc_mp.dom().contains(target_process),
        final(krnl).prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container,
        final(krnl).prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable,
        ((final(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process && final(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable
            && !final(krnl).thr_mp.spec_index(target_thread).view_ghost().exited)
            || (typed_lock_map_contains_mode(final(lctx).process_lock_map(), target_process, TypedLockMode::Write) && !final(krnl).prc_mp.spec_index(target_process).view().zombie && !(final(krnl).prc_mp.spec_index(target_process).view().state.view() is TablesEmptied))),
        source_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(source_thread).locking_thread()->Write_lock_id,
        target_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(target_thread).locking_thread()->Write_lock_id,
        final(krnl).pt_mp.dom().contains(source_pagetable),
        final(krnl).pt_mp.dom().contains(target_pagetable),
        final(krnl).pt_mp.spec_index(source_pagetable).view() == old(krnl).pt_mp.spec_index(source_pagetable).view(),
        final(krnl).pt_mp.spec_index(target_pagetable).view() == old(krnl).pt_mp.spec_index(target_pagetable).view(),
        source_pagetable_lock_perm.state() is ReadLock ==> final(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), source_pagetable_lock_perm.lock_id()),
        source_pagetable_lock_perm.state() is WriteLock ==> source_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
        target_pagetable_lock_perm.state() is ReadLock ==> final(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), target_pagetable_lock_perm.lock_id()),
        target_pagetable_lock_perm.state() is WriteLock ==> target_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
        final(steps).nonlock_view().subrange(0, old(steps).nonlock_view().len() as int) == old(steps).nonlock_view(),
        final(steps).snapshot_k() == *final(krnl),
        {
            let source_process = old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr;
            &&& final(steps).nonlock_view().last().new_u.process_map.dom().contains(source_process)
            &&& kernel_k_to_nonlock_kernel_u(*final(krnl)).process_map.dom().contains(source_process)
            &&& final(steps).view().last().new_u.process_map.dom().contains(source_process) && final(steps).view().last().new_u.process_map.spec_index(source_process).pagetable is Some
            &&& kernel_k_to_kernel_u(*final(krnl)).process_map.dom().contains(source_process) && kernel_k_to_kernel_u(*final(krnl)).process_map.spec_index(source_process).pagetable is Some
            &&& final(steps).view().last().new_u.process_map.spec_index(source_process).pagetable->Some_0.lock_state
                == kernel_k_to_kernel_u(*final(krnl)).process_map.spec_index(source_process).pagetable->Some_0.lock_state
            &&& forall|wva: WindowVa, v: VAddr|
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((source_pagetable, wva)), kernel_k_to_nonlock_kernel_u(*final(krnl)).process_map.spec_index(source_process).pagetable->Some_0.mapping_4k.dom().contains(v)]
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((source_pagetable, wva)), final(steps).nonlock_view().last().new_u.process_map.spec_index(source_process).pagetable->Some_0.mapping_4k.dom().contains(v)]
                old(lctx).pagetable_window_lock_map().dom().contains((source_pagetable, wva)) && spec_v2l4index(v) == spec_v2l4index(wva.va) && spec_v2l3index(v) == spec_v2l3index(wva.va)
                    && spec_v2l2index(v) == spec_v2l2index(wva.va) ==> {
                    let pre_t = final(steps).nonlock_view().last().new_u.process_map.spec_index(source_process).pagetable->Some_0;
                    let post_t = kernel_k_to_nonlock_kernel_u(*final(krnl)).process_map.spec_index(source_process).pagetable->Some_0;
                    &&& post_t.mapping_4k.dom().contains(v) == pre_t.mapping_4k.dom().contains(v)
                    &&& pre_t.mapping_4k.dom().contains(v) ==> post_t.mapping_4k.spec_index(v) == pre_t.mapping_4k.spec_index(v)
                }
            &&& final(steps).nonlock_view().last().new_u.process_map.dom().contains(target_process)
            &&& final(steps).nonlock_view().last().new_u.thread_map.dom().contains(target_thread)
            &&& kernel_k_to_nonlock_kernel_u(*final(krnl)).thread_map.dom().contains(target_thread)
            &&& final(steps).nonlock_view().last().new_u.thread_map.spec_index(target_thread) == kernel_k_to_nonlock_kernel_u(*final(krnl)).thread_map.spec_index(target_thread)
            &&& target_write_held && typed_lock_map_contains_mode(old(lctx).process_lock_map(), target_process, TypedLockMode::Write) && ({
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
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        final(krnl).thr_mp.spec_index(progress_thread).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress, ..old(krnl).thr_mp.spec_index(progress_thread).view() }),
        final(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress.view() == share_4k_progress_after_leaf(old(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress.view()),
        final(krnl).thr_mp.spec_index(progress_thread).view_ghost() == old(krnl).thr_mp.spec_index(progress_thread).view_ghost(),
        final(krnl).thr_mp.spec_index(target_thread).view_ghost() == old(krnl).thr_mp.spec_index(target_thread).view_ghost(),
        final(krnl).thr_mp.spec_index(source_thread).view_ghost() == old(krnl).thr_mp.spec_index(source_thread).view_ghost(),
        progress_thread != target_thread ==> final(krnl).thr_mp.spec_index(target_thread).view() == old(krnl).thr_mp.spec_index(target_thread).view(),
        progress_thread != source_thread ==> final(krnl).thr_mp.spec_index(source_thread).view() == old(krnl).thr_mp.spec_index(source_thread).view(),
        final(krnl).ctn_mp.dom().contains(target_container),
        final(krnl).ctn_mp.spec_index(target_container).view_rodata() == old(krnl).ctn_mp.spec_index(target_container).view_rodata(),
        source_pagetable_lock_perm.state() is WriteLock ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable),
        source_pagetable_lock_perm.state() is ReadLock ==> {
            &&& final(krnl).pt_mp.spec_index(source_pagetable).rlocked_by_thread(old(lctx).thread_id())
            &&& final(krnl).pt_mp.spec_index(source_pagetable).being_killed() == old(krnl).pt_mp.spec_index(source_pagetable).being_killed()
            &&& final(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Read_reader_map.spec_index(old(lctx).thread_id())
                == old(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Read_reader_map.spec_index(old(lctx).thread_id())
        },
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((source_pagetable, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((source_pagetable, w)) ==> {
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).window_view(w) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).window_view(w)
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_2m().dom().contains(w.va) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_2m().dom().contains(w.va)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_2m().dom().contains(w.va)
                    ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_2m().spec_index(w.va) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_2m().spec_index(w.va)
            },
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), p).window_view(w)]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w)) && (p == source_pagetable || p == target_pagetable) ==> {
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), p).window_view(w).lock_state == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), p).window_view(w).lock_state
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), p).window_view(w).stale_cpus == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), p).window_view(w).stale_cpus
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), p).window_leaves_present(w) ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), p).window_leaves_present(w)
            },
        forall|w: WindowVa, v: VAddr|
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((source_pagetable, w)), pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_4k().dom().contains(v)]
            old(lctx).pagetable_window_lock_map().dom().contains((source_pagetable, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_4k().dom().contains(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().dom().contains(v)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().dom().contains(v)
                    ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_4k().spec_index(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().spec_index(v)
            },
        forall|w: WindowVa, v: VAddr|
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, w)), pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_4k().dom().contains(v)]
            old(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
                let shared = pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_4k()
                    .insert(target_va, pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_va));
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_4k().dom().contains(v) == shared.dom().contains(v)
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_4k().dom().contains(v) ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_4k().spec_index(v) == shared.spec_index(v)
            },
        forall|w: WindowVa|
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, w)) && old(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end <= spec_v2l4index(w.va)
                && pei_valid(spec_v2l4index(w.va)) && pei_valid(spec_v2l3index(w.va)) && pei_valid(spec_v2l2index(w.va))
                ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).spec_resolve_mapping_l2(spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va))
                    == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).spec_resolve_mapping_l2(spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va)),
        target_write_held ==> {
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_4k()
                == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_4k().insert(target_va, pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_va))
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).user_view(LockStateU::Unlocked).mapping_4k
                == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).user_view(LockStateU::Unlocked).mapping_4k.insert(target_va,
                    pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).user_view(LockStateU::Unlocked).mapping_4k.spec_index(source_va))
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_2m()
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_1g()
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.l2_lock == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).lower.l2_lock
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus
        },
{
    share_one_mapping_4k_copy_leaf(krnl, target_thread, target_process, target_container, source_pagetable, target_pagetable, target_write_held, source_va, target_va, Tracked(&mut *lctx),
        Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm));
    krnl.set_thread_syscall_progress(progress_thread, Ghost(share_4k_progress_after_leaf(krnl.thr_mp.spec_index(progress_thread).view().syscall_progress.view())), Tracked(&*lctx),
        Tracked(if progress_thread == source_thread { source_thread_lock_perm } else { target_thread_lock_perm }));
    proof {
        assert(!old(krnl).prc_mp.spec_index(target_process).view().zombie) by { process_thread_wf_at(old(krnl).prc_mp, old(krnl).thr_mp, target_thread); };
        assert(!krnl.prc_mp.spec_index(target_process).view().zombie
            && krnl.prc_mp.spec_index(target_process).view().pagetable == target_pagetable) by { process_pagetable_match_pagetable_at(krnl.prc_mp, krnl.pt_mp, target_pagetable); };
        assert(kernel_process_4k_mapping_changed(&steps.snapshot_k(), &*krnl, target_process, target_pagetable, target_va)) by {
            reveal(kernel_process_4k_mapping_changed); process_pagetable_match_pagetable_at(old(krnl).prc_mp, old(krnl).pt_mp, target_pagetable);
        };
        let ghost source_process = old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr;
        assert({
            &&& krnl.prc_mp.dom().contains(source_process)
            &&& !krnl.prc_mp.spec_index(source_process).view().zombie
            &&& krnl.prc_mp.spec_index(source_process).view().pagetable == source_pagetable
        }) by { process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, source_thread); };
        let ghost leaf_k = *krnl;
        krnl.kernel_step_boundary_process_4k_mapping_changed_windowed(&mut *lctx, &mut *steps, target_process, target_pagetable, target_va, source_process, source_pagetable, target_thread,
            source_thread);
        assert(share_4k_leaf_step_pre(steps.view().last().old_u, cpu_id) && share_4k_leaf_step(steps.view().last().old_u, steps.view().last().new_u, cpu_id)) by {
            share_4k_leaf_step_from_k(old(krnl), &leaf_k, old(lctx), cpu_id, progress_thread, source_thread, source_process, target_process, source_pagetable, target_pagetable, source_va, target_va);
        };
        assert({
            &&& krnl.ctn_mp.dom().contains(target_container)
            &&& krnl.prc_mp.dom().contains(target_process)
            &&& krnl.prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container
            &&& krnl.prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable
            &&& ((krnl.thr_mp.spec_index(target_thread).view().owning_proc == target_process && krnl.thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable
                && !krnl.thr_mp.spec_index(target_thread).view_ghost().exited)
                || (typed_lock_map_contains_mode(lctx.process_lock_map(), target_process, TypedLockMode::Write) && !krnl.prc_mp.spec_index(target_process).view().zombie && !(krnl.prc_mp.spec_index(target_process).view().state.view() is TablesEmptied)))
        }) by { process_pagetable_match_pagetable_at(krnl.prc_mp, krnl.pt_mp, target_pagetable); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, target_process); container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, target_process); };
        assert(krnl.thr_mp.lock_id_by_key(target_thread) == old(krnl).thr_mp.lock_id_by_key(target_thread)) by { thread_lock_id_preserved_for_typed_maps_unchanged(old(krnl), &*krnl, old(lctx), &*lctx, target_thread); };
        assert(share_4k_objects_k(*krnl, cpu_id) == share_4k_objects_k(*old(krnl), cpu_id)) by { reveal(share_4k_objects_k); };
    }
}

/// Read-only owner precheck for every present source 4K mapping.
///
/// The source page table is read- or write-held with every source 2M window held by the caller; the target thread is a stable root. Each physical
/// page is write-locked only long enough to read its runtime owner. Locking is
/// an internal stuttering step: mappings, page payloads, and user-visible state
/// are unchanged.
#[verifier::spinoff_prover]
pub fn share_mapping_4k_source_owner_precheck(
    krnl: &mut KernelK, source_range: &VaRange4K, source_thread: RwLockThreadPtr, target_thread: RwLockThreadPtr, target_process: RwLockProcessPtr, target_container: RwLockContainerPtr,
    source_pagetable: RwLockPageTableRoot, target_pagetable: RwLockPageTableRoot, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    Tracked(source_thread_lock_perm): Tracked<&LockPerm>, Tracked(target_thread_lock_perm): Tracked<&LockPerm>, Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>,
    Tracked(target_pagetable_lock_perm): Tracked<&LockPerm>,
) -> (ret: bool)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).thread_lock_map().dom() == set![source_thread, target_thread],
        old(lctx).pagetable_lock_map().dom() == set![source_pagetable, target_pagetable],
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        forall|held_thread: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(held_thread)] old(lctx).thread_lock_map().dom().contains(held_thread)
            ==> old(krnl).thr_mp.spec_index(held_thread).being_killed() || !(old(krnl).thr_mp.spec_index(held_thread).view().state is SCHEDULED),
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
        ((old(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process && old(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable)
            || (typed_lock_map_contains_mode(old(lctx).process_lock_map(), target_process, TypedLockMode::Write) && !old(krnl).prc_mp.spec_index(target_process).view().zombie)),
        source_thread_lock_perm.state() is WriteLock,
        source_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        source_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(source_thread).locking_thread()->Write_lock_id,
        target_thread_lock_perm.state() is WriteLock,
        target_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        target_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(target_thread).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable),
        old(krnl).pt_mp.dom().contains(target_pagetable),
        old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == old(krnl).thr_mp.spec_index(source_thread).view().owning_proc,
        old(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        source_pagetable_lock_perm.state() is ReadLock || source_pagetable_lock_perm.state() is WriteLock,
        source_pagetable_lock_perm.state() is ReadLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Read),
        source_pagetable_lock_perm.state() is ReadLock ==> old(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), source_pagetable_lock_perm.lock_id()),
        source_pagetable_lock_perm.state() is WriteLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Write),
        source_pagetable_lock_perm.state() is WriteLock ==> source_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
        target_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        target_pagetable_lock_perm.state() is ReadLock || target_pagetable_lock_perm.state() is WriteLock,
        target_pagetable_lock_perm.state() is ReadLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Read),
        target_pagetable_lock_perm.state() is ReadLock ==> old(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), target_pagetable_lock_perm.lock_id()),
        target_pagetable_lock_perm.state() is WriteLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
        target_pagetable_lock_perm.state() is WriteLock ==> target_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        old(krnl).irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
        old(krnl).irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
        old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
        old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        source_range.wf(),
        old(krnl).pt_mp.spec_index(source_pagetable).view().kernel_l4_end <= spec_va2index(source_range.start).0,
        share_mapping_4k_source_range_present(old(krnl), source_pagetable, source_range),
        forall|j: int| #![trigger source_range.view().spec_index(j)] 0 <= j < source_range.len ==> {
            let va = source_range.view().spec_index(j);
            ||| old(lctx).pagetable_window_lock_map().dom().contains((source_pagetable, window_of(va)))
            ||| pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is None
        },
        old(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process,
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        source_range.len > 0 ==> final(steps).snapshot_k() == *final(krnl),
        final(steps).view() == if source_range.len == 0 { old(steps).view() }
            else { record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(krnl))) },
        old(steps).snapshot_k() == *old(krnl) ==> final(steps).view() == old(steps).view(),
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
        ((final(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process && final(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable)
            || (typed_lock_map_contains_mode(final(lctx).process_lock_map(), target_process, TypedLockMode::Write) && !final(krnl).prc_mp.spec_index(target_process).view().zombie)),
        source_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(source_thread).locking_thread()->Write_lock_id,
        target_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(target_thread).locking_thread()->Write_lock_id,
        final(krnl).pt_mp.dom().contains(source_pagetable),
        final(krnl).pt_mp.dom().contains(target_pagetable),
        final(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == final(krnl).thr_mp.spec_index(source_thread).view().owning_proc,
        final(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_pagetable_lock_perm.state() is WriteLock ==> source_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
        source_pagetable_lock_perm.state() is ReadLock ==> final(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), source_pagetable_lock_perm.lock_id()),
        target_pagetable_lock_perm.state() is WriteLock ==> target_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        target_pagetable_lock_perm.state() is ReadLock ==> final(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), target_pagetable_lock_perm.lock_id()),
        final(steps).nonlock_view().len() == old(steps).nonlock_view().len(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
        final(krnl).irt.view().owners() == final(steps).snapshot_k().irt.view().owners(),
        final(krnl).irt.view().iommu_roots() == final(steps).snapshot_k().irt.view().iommu_roots(),
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
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        held_pagetable_windows_unchanged(old(krnl).pt_mp, old(krnl).pt_lower.view(), final(krnl).pt_mp, final(krnl).pt_lower.view(), old(lctx)),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Write)
            ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Write)
            ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable),
        final(krnl).thr_mp.spec_index(source_thread).view() == old(krnl).thr_mp.spec_index(source_thread).view(),
        final(krnl).thr_mp.spec_index(target_thread).view() == old(krnl).thr_mp.spec_index(target_thread).view(),
        final(krnl).thr_mp.spec_index(source_thread).view_ghost() == old(krnl).thr_mp.spec_index(source_thread).view_ghost(),
        final(krnl).thr_mp.spec_index(target_thread).view_ghost() == old(krnl).thr_mp.spec_index(target_thread).view_ghost(),
        ret == share_mapping_4k_range_owner_compatible(old(krnl), source_pagetable, target_container, source_range),
{
    proof { steps.rebase_snapshot_k_if_unchanged(&*krnl); }
    proof {
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
    proof {
        assert({
            &&& mapped_4k_page_pagetable_wf(old(krnl).pt_mp, old(krnl).pt_lower.view(), old(krnl).pg_arr)
            &&& container_page_owner_wf(old(krnl).ctn_mp, old(krnl).pg_arr)
            &&& old(krnl).ctn_mp.dom().contains(target_container)
        }) by { container_thread_wf_at(old(krnl).ctn_mp, old(krnl).thr_mp, target_thread); };
    }
    let mut i: usize = 0;
    let mut all_compatible = true;
    while i < source_range.len
        invariant
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            i == 0 ==> *krnl == *old(krnl) && steps.view() == old(steps).view() && steps.snapshot_u() == old(steps).snapshot_u(),
            i > 0 ==> steps.snapshot_k() == *krnl && steps.view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(krnl))),
            krnl.inv(),
            lctx.kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(krnl, &*lctx),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(krnl.cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            forall|held_thread: RwLockThreadPtr| #![trigger lctx.thread_lock_map().dom().contains(held_thread)] lctx.thread_lock_map().dom().contains(held_thread)
                ==> krnl.thr_mp.spec_index(held_thread).being_killed() || !(krnl.thr_mp.spec_index(held_thread).view().state is SCHEDULED),
            forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> krnl.pg_arr.lock_id_by_index(held_page).major < MAPPED_PAGE_LOCK_MAJOR,
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
            ((krnl.thr_mp.spec_index(target_thread).view().owning_proc == target_process && krnl.thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable)
                || (typed_lock_map_contains_mode(lctx.process_lock_map(), target_process, TypedLockMode::Write) && !krnl.prc_mp.spec_index(target_process).view().zombie)),
            source_thread_lock_perm.lock_id() == krnl.thr_mp.spec_index(source_thread).locking_thread()->Write_lock_id,
            target_thread_lock_perm.lock_id() == krnl.thr_mp.spec_index(target_thread).locking_thread()->Write_lock_id,
            krnl.pt_mp.dom().contains(source_pagetable),
            krnl.pt_mp.dom().contains(target_pagetable),
            krnl.pt_mp.spec_index(source_pagetable).view().proc_ptr == krnl.thr_mp.spec_index(source_thread).view().owning_proc,
            krnl.pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
            source_pagetable_lock_perm.thread_id() == lctx.thread_id(),
            source_pagetable_lock_perm.state() is ReadLock || source_pagetable_lock_perm.state() is WriteLock,
            source_pagetable_lock_perm.state() is ReadLock ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), source_pagetable, TypedLockMode::Read),
            source_pagetable_lock_perm.state() is ReadLock ==> krnl.pt_mp.spec_index(source_pagetable).locking_thread()->Read_reader_map.contains_pair(lctx.thread_id(), source_pagetable_lock_perm.lock_id()),
            source_pagetable_lock_perm.state() is WriteLock ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), source_pagetable, TypedLockMode::Write),
            source_pagetable_lock_perm.state() is WriteLock ==> source_pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
            target_pagetable_lock_perm.thread_id() == lctx.thread_id(),
            target_pagetable_lock_perm.state() is ReadLock || target_pagetable_lock_perm.state() is WriteLock,
            target_pagetable_lock_perm.state() is ReadLock ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), target_pagetable, TypedLockMode::Read),
            target_pagetable_lock_perm.state() is ReadLock ==> krnl.pt_mp.spec_index(target_pagetable).locking_thread()->Read_reader_map.contains_pair(lctx.thread_id(), target_pagetable_lock_perm.lock_id()),
            target_pagetable_lock_perm.state() is WriteLock ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
            target_pagetable_lock_perm.state() is WriteLock ==> target_pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
            steps.nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), krnl),
            kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp),
            krnl.irt.view().owners() == steps.snapshot_k().irt.view().owners(),
            krnl.irt.view().iommu_roots() == steps.snapshot_k().irt.view().iommu_roots(),
            krnl.cpu_tlb.view() == steps.snapshot_k().cpu_tlb.view(),
            krnl.iommu_tlb.view() == steps.snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), krnl),
            index_valid(NUM_CPUS, cpu_id),
            krnl.cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
            lctx.cpu_lock_map().dom().contains(cpu_id),
            krnl.cpu_arr.lock_id_by_index(cpu_id) == old(krnl).cpu_arr.lock_id_by_index(cpu_id),
            source_range.wf(),
            krnl.pt_mp.spec_index(source_pagetable).view().kernel_l4_end <= spec_va2index(source_range.start).0,
            old(krnl).pt_mp.dom().contains(source_pagetable),
            share_mapping_4k_source_range_present(old(krnl), source_pagetable, source_range),
            forall|j: int| #![trigger source_range.view().spec_index(j)] 0 <= j < source_range.len ==> {
                let va = source_range.view().spec_index(j);
                ||| old(lctx).pagetable_window_lock_map().dom().contains((source_pagetable, window_of(va)))
                ||| pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is None
            },
            mapped_4k_page_pagetable_wf(old(krnl).pt_mp, old(krnl).pt_lower.view(), old(krnl).pg_arr),
            container_page_owner_wf(old(krnl).ctn_mp, old(krnl).pg_arr),
            old(krnl).ctn_mp.dom().contains(target_container),
            krnl.ctn_mp.dom().contains(target_container),
            krnl.ctn_mp.spec_index(target_container).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(target_container).view_ghost().uppertree_seq,
            0 <= i <= source_range.len,
            all_compatible == share_mapping_4k_range_owner_compatible_prefix(old(krnl), source_pagetable, target_container, source_range, i as int),
            steps.nonlock_view().len() == old(steps).nonlock_view().len(),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
            typed_lock_maps_unchanged(old(lctx), lctx),
            held_pages_unchanged(old(krnl).pg_arr, krnl.pg_arr, old(lctx)),
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
            held_pagetable_windows_unchanged(old(krnl).pt_mp, old(krnl).pt_lower.view(), krnl.pt_mp, krnl.pt_lower.view(), old(lctx)),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Write)
                ==> pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Write)
                ==> pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable),
            krnl.thr_mp.spec_index(target_thread).view() == old(krnl).thr_mp.spec_index(target_thread).view(),
            krnl.thr_mp.spec_index(source_thread).view() == old(krnl).thr_mp.spec_index(source_thread).view(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        decreases source_range.len - i,
    {
        let ghost krnl_i = *krnl;
        proof {
            let va = source_range.view().spec_index(i as int);
            assert(pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable).mapping_4k().dom().contains(va)
                && pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable).mapping_4k().spec_index(va) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().spec_index(va)) by {
                spec_va_4k_index_roundtrip_at(va, spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va));
                spec_va_4k_index_roundtrip_at(window_of(va).va, spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), 0);
                assert(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().dom().contains(va));
                held_pagetable_window_mapping_4k_unchanged_at(old(krnl).pt_mp, old(krnl).pt_lower.view(), krnl.pt_mp, krnl.pt_lower.view(), old(lctx), source_pagetable, window_of(va), va);
            };
        }
        let page_compatible = share_mapping_4k_source_owner_check_at(krnl, source_range, i, target_thread, target_process, target_container, source_pagetable, target_pagetable, Tracked(&mut *lctx), Tracked(&mut *steps),
            Tracked(source_pagetable_lock_perm));
        proof {
            let va = source_range.view().spec_index(i as int);
            assert(page_compatible == share_mapping_4k_leaf_owner_compatible(old(krnl), source_pagetable, target_container, va)) by {
                let page_index = page_ptr2page_index(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().spec_index(va).addr);
                page_ptr_valid_imply_page_index_valid();
                mapped_4k_page_pagetable_wf_pagetable_at(old(krnl).pt_mp, old(krnl).pt_lower.view(), old(krnl).pg_arr, source_pagetable, va);
                mapped_4k_page_pagetable_wf_pagetable_at(krnl_i.pt_mp, krnl_i.pt_lower.view(), krnl_i.pg_arr, source_pagetable, va);
                container_page_owner_backward_at(old(krnl).ctn_mp, old(krnl).pg_arr, page_index); container_page_owner_backward_at(krnl_i.ctn_mp, krnl_i.pg_arr, page_index);
            };
        }
        all_compatible = all_compatible && page_compatible;
        i = i + 1;
    }
    all_compatible
}

/// Sharing target slot `i` adds exactly that slot to the shared-prefix target map; a target map `cur` that gained only that slot over a map `prev`
/// matching the slot-`i` prefix in every held window of `root` matches the slot-`i + 1` prefix in those windows.
proof fn prove_share_mapping_4k_iteration_target_partition(source: Map<VAddr, MapEntry>, initial_target: Map<VAddr, MapEntry>, source_range: &VaRange4K, target_range: &VaRange4K, i: usize,
    windows: Set<(RwLockPageTableRoot, WindowVa)>, root: RwLockPageTableRoot, prev: Map<VAddr, MapEntry>, cur: Map<VAddr, MapEntry>, entry: MapEntry)
    requires
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        0 <= i < source_range.len,
        share_mapping_4k_target_range_empty_from(share_mapping_4k_target_map_with_shared_prefix(source, initial_target, source_range, target_range, i as nat), target_range, i as int),
        entry == source.spec_index(source_range.view().spec_index(i as int)),
        forall|w: WindowVa, v: VAddr|
            #![trigger windows.contains((root, w)), prev.dom().contains(v)]
            windows.contains((root, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
                let expected = share_mapping_4k_target_map_with_shared_prefix(source, initial_target, source_range, target_range, i as nat);
                &&& prev.dom().contains(v) == expected.dom().contains(v)
                &&& prev.dom().contains(v) ==> prev.spec_index(v) == expected.spec_index(v)
            },
        forall|w: WindowVa, v: VAddr|
            #![trigger windows.contains((root, w)), cur.dom().contains(v)]
            windows.contains((root, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
                let shared = prev.insert(target_range.view().spec_index(i as int), entry);
                &&& cur.dom().contains(v) == shared.dom().contains(v)
                &&& cur.dom().contains(v) ==> cur.spec_index(v) == shared.spec_index(v)
            },
    ensures
        share_mapping_4k_target_map_with_shared_prefix(source, initial_target, source_range, target_range, (i + 1) as nat)
            == share_mapping_4k_target_map_with_shared_prefix(source, initial_target, source_range, target_range, i as nat).insert(target_range.view().spec_index(i as int), entry),
        share_mapping_4k_target_range_empty_from(share_mapping_4k_target_map_with_shared_prefix(source, initial_target, source_range, target_range, (i + 1) as nat), target_range, (i + 1) as int),
        i + 1 < target_range.len ==> !share_mapping_4k_target_map_with_shared_prefix(source, initial_target, source_range, target_range, (i + 1) as nat).dom().contains(target_range.view().spec_index(i + 1)),
        forall|w: WindowVa, v: VAddr|
            #![trigger windows.contains((root, w)), cur.dom().contains(v)]
            windows.contains((root, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
                let expected = share_mapping_4k_target_map_with_shared_prefix(source, initial_target, source_range, target_range, (i + 1) as nat);
                &&& cur.dom().contains(v) == expected.dom().contains(v)
                &&& cur.dom().contains(v) ==> cur.spec_index(v) == expected.spec_index(v)
            },
{
    let previous = share_mapping_4k_target_map_with_shared_prefix(source, initial_target, source_range, target_range, i as nat);
    let next = share_mapping_4k_target_map_with_shared_prefix(source, initial_target, source_range, target_range, (i + 1) as nat);
    assert(next == previous.insert(target_range.view().spec_index(i as int), entry) && share_mapping_4k_target_range_empty_from(next, target_range, (i + 1) as int)
        && (i + 1 < target_range.len ==> !next.dom().contains(target_range.view().spec_index(i + 1)))) by {
        reveal(share_mapping_4k_target_map_with_shared_prefix); reveal(share_mapping_4k_target_range_empty_from); seq_index_lemma::<VAddr>(); source_range.va_range_lemma(); target_range.va_range_lemma();
    };
}

/// Shares each source 4K leaf into the already-built target directory path of the matching target address.
/// All fallible checks are completed by the caller before this function starts. The caller holds every source and target 2M window of the two
/// ranges; the source table is read- or write-held and `target_write_held` names the target table's mode.
#[verifier::spinoff_prover]
pub fn share_mapping_4k_build_and_share(
    krnl: &mut KernelK, source_range: &VaRange4K, target_range: &VaRange4K, target_allocator: RwLockPageAllocatorPtr,
    source_thread: RwLockThreadPtr, quota_thread: RwLockThreadPtr, progress_thread: RwLockThreadPtr, target_process: RwLockProcessPtr,
    target_container: RwLockContainerPtr, cpu_id: CpuId, source_pagetable: RwLockPageTableRoot, target_pagetable: RwLockPageTableRoot,
    target_write_held: bool, transfer_source: Option<RwLockContainerPtr>, Ghost(origin): Ghost<Share4kOrigin>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    Tracked(source_thread_lock_perm): Tracked<&LockPerm>, Tracked(quota_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>, Tracked(target_pagetable_lock_perm): Tracked<&LockPerm>,
    Tracked(transfer_source_lock_perm): Tracked<Option<&LockPerm>>, Tracked(transfer_target_lock_perm): Tracked<Option<&LockPerm>>,
)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).thread_lock_map().dom() =~= set![source_thread, quota_thread],
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable, target_pagetable],
        held_locks_order_below(old(krnl), old(lctx), PAGE_TABLE_WINDOW_LOCK_MAJOR),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(krnl).thr_mp.dom().contains(source_thread),
        old(krnl).thr_mp.dom().contains(quota_thread),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), source_thread, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(source_thread).being_killed(),
        !thread_is_dangling(old(krnl).thr_mp.spec_index(source_thread)),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), quota_thread, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(quota_thread).being_killed(),
        !thread_is_dangling(old(krnl).thr_mp.spec_index(quota_thread)),
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
        ((old(krnl).thr_mp.spec_index(quota_thread).view().owning_proc == target_process && old(krnl).thr_mp.spec_index(quota_thread).view().proc_pagetable_ptr == target_pagetable
            && !old(krnl).thr_mp.spec_index(quota_thread).view_ghost().exited)
            || (typed_lock_map_contains_mode(old(lctx).process_lock_map(), target_process, TypedLockMode::Write) && !old(krnl).prc_mp.spec_index(target_process).view().zombie && !(old(krnl).prc_mp.spec_index(target_process).view().state.view() is TablesEmptied))),
        source_thread_lock_perm.state() is WriteLock,
        source_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        source_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(source_thread).locking_thread()->Write_lock_id,
        quota_thread_lock_perm.state() is WriteLock,
        quota_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        quota_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(quota_thread).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable),
        old(krnl).pt_mp.dom().contains(target_pagetable),
        old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == old(krnl).thr_mp.spec_index(source_thread).view().owning_proc,
        old(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        source_pagetable_lock_perm.state() is ReadLock || source_pagetable_lock_perm.state() is WriteLock,
        source_pagetable_lock_perm.state() is ReadLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Read),
        source_pagetable_lock_perm.state() is ReadLock ==> old(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), source_pagetable_lock_perm.lock_id()),
        source_pagetable_lock_perm.state() is WriteLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Write),
        source_pagetable_lock_perm.state() is WriteLock ==> source_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
        target_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        target_pagetable_lock_perm.state() is ReadLock || target_pagetable_lock_perm.state() is WriteLock,
        target_pagetable_lock_perm.state() is ReadLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Read),
        target_pagetable_lock_perm.state() is ReadLock ==> old(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), target_pagetable_lock_perm.lock_id()),
        target_pagetable_lock_perm.state() is WriteLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
        target_pagetable_lock_perm.state() is WriteLock ==> target_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        target_write_held == (target_pagetable_lock_perm.state() is WriteLock),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).ctn_mp.dom().contains(target_container),
        old(krnl).ctn_mp.spec_index(target_container).view_rodata().view().allocator_ptr_4k == target_allocator,
        old(krnl).allc_4k_mp.dom().contains(target_allocator),
        old(steps).snapshot_k() == *old(krnl),
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        old(krnl).pt_mp.spec_index(source_pagetable).view().kernel_l4_end <= spec_va2index(source_range.start).0,
        forall|j: int| #![trigger source_range.view().spec_index(j)] 0 <= j < source_range.len ==> {
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().dom().contains(source_range.view().spec_index(j))
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_range.view().spec_index(j)).present
        },
        share_mapping_4k_range_owner_compatible(old(krnl), source_pagetable, target_container, source_range),
        forall|j: int| #![trigger source_range.view().spec_index(j)] 0 <= j < source_range.len ==> old(lctx).pagetable_window_lock_map().dom().contains((source_pagetable, window_of(source_range.view().spec_index(j)))),
        forall|j: int| #![trigger target_range.view().spec_index(j)] 0 <= j < target_range.len ==> {
            let va = target_range.view().spec_index(j);
            &&& old(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, window_of(va)))
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some
        },
        old(krnl).thr_mp.spec_index(quota_thread).view().temp_alloc_cache_2m.view().len() == 0,
        old(krnl).thr_mp.spec_index(quota_thread).view().temp_alloc_cache_1g.view().len() == 0,
        progress_thread == source_thread || progress_thread == quota_thread,
        old(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress.view() == Some(SyscallProgress::Share4k { source_range: *source_range, target_range: *target_range, shared: 0, origin }),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(progress_thread),
        share_4k_objects_k(*old(krnl), cpu_id).source_thread == source_thread && share_4k_objects_k(*old(krnl), cpu_id).quota_thread == quota_thread,
        share_4k_objects_k(*old(krnl), cpu_id).target == target_process && share_4k_objects_k(*old(krnl), cpu_id).target_container == target_container,
        share_4k_objects_k(*old(krnl), cpu_id).transfer_source == transfer_source,
        quota_thread != progress_thread ==> old(krnl).thr_mp.spec_index(quota_thread).view().syscall_progress.view() is None,
        origin matches Share4kOrigin::IpcPages { peer }
            ==> old(krnl).thr_mp.spec_index(peer).view().state is IPC_TRANSIT && old(krnl).thr_mp.spec_index(peer).view().state->IPC_TRANSIT_partner == progress_thread,
        old(krnl).thr_mp.spec_index(quota_thread).view().free_quota_pending_clean(),
        old(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end <= spec_v2l4index(target_range.start),
        forall|j: int| #![trigger target_range.view().spec_index(j)] 0 <= j < target_range.len ==> !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_4k().dom().contains(target_range.view().spec_index(j)),
        target_write_held ==> pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).leaves_present(),
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view().len() == old(steps).view().len() + source_range.len,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len()
            ==> share_4k_range_step(final(steps).view()[j], cpu_id),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(krnl).thr_mp.dom().contains(source_thread),
        final(krnl).thr_mp.dom().contains(quota_thread),
        !final(krnl).thr_mp.spec_index(source_thread).being_killed(),
        !thread_is_dangling(final(krnl).thr_mp.spec_index(source_thread)),
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
        source_pagetable_lock_perm.state() is WriteLock ==> source_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
        source_pagetable_lock_perm.state() is ReadLock ==> final(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), source_pagetable_lock_perm.lock_id()),
        target_pagetable_lock_perm.state() is WriteLock ==> target_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        target_pagetable_lock_perm.state() is ReadLock ==> final(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), target_pagetable_lock_perm.lock_id()),
        final(krnl).pt_mp.spec_index(source_pagetable).view() == old(krnl).pt_mp.spec_index(source_pagetable).view(),
        final(krnl).pt_mp.spec_index(target_pagetable).view() == old(krnl).pt_mp.spec_index(target_pagetable).view(),
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
        final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + source_range.len,
        final(steps).nonlock_view().subrange(0, old(steps).nonlock_view().len() as int) == old(steps).nonlock_view(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
        final(krnl).irt.view().owners() == final(steps).snapshot_k().irt.view().owners(),
        final(krnl).irt.view().iommu_roots() == final(steps).snapshot_k().irt.view().iommu_roots(),
        final(krnl).cpu_tlb.view() == final(steps).snapshot_k().cpu_tlb.view(),
        final(krnl).iommu_tlb.view() == final(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(krnl)),
        {
            let source_process = old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr;
            &&& final(steps).nonlock_view().last().new_u.process_map.dom().contains(source_process)
            &&& kernel_k_to_nonlock_kernel_u(*final(krnl)).process_map.dom().contains(source_process)
            &&& final(steps).view().last().new_u.process_map.dom().contains(source_process) && final(steps).view().last().new_u.process_map.spec_index(source_process).pagetable is Some
            &&& kernel_k_to_kernel_u(*final(krnl)).process_map.dom().contains(source_process) && kernel_k_to_kernel_u(*final(krnl)).process_map.spec_index(source_process).pagetable is Some
            &&& final(steps).view().last().new_u.process_map.spec_index(source_process).pagetable->Some_0.lock_state == kernel_k_to_kernel_u(*final(krnl)).process_map.spec_index(source_process).pagetable->Some_0.lock_state
            &&& forall|wva: WindowVa, v: VAddr|
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((source_pagetable, wva)), kernel_k_to_nonlock_kernel_u(*final(krnl)).process_map.spec_index(source_process).pagetable->Some_0.mapping_4k.dom().contains(v)]
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((source_pagetable, wva)), final(steps).nonlock_view().last().new_u.process_map.spec_index(source_process).pagetable->Some_0.mapping_4k.dom().contains(v)]
                old(lctx).pagetable_window_lock_map().dom().contains((source_pagetable, wva)) && spec_v2l4index(v) == spec_v2l4index(wva.va) && spec_v2l3index(v) == spec_v2l3index(wva.va)
                    && spec_v2l2index(v) == spec_v2l2index(wva.va) ==> {
                    let pre_t = final(steps).nonlock_view().last().new_u.process_map.spec_index(source_process).pagetable->Some_0;
                    let post_t = kernel_k_to_nonlock_kernel_u(*final(krnl)).process_map.spec_index(source_process).pagetable->Some_0;
                    &&& post_t.mapping_4k.dom().contains(v) == pre_t.mapping_4k.dom().contains(v)
                    &&& pre_t.mapping_4k.dom().contains(v) ==> post_t.mapping_4k.spec_index(v) == pre_t.mapping_4k.spec_index(v)
                }
            &&& final(steps).nonlock_view().last().new_u.process_map.dom().contains(target_process)
            &&& final(steps).nonlock_view().last().new_u.thread_map.dom().contains(quota_thread)
            &&& kernel_k_to_nonlock_kernel_u(*final(krnl)).thread_map.dom().contains(quota_thread)
            &&& final(steps).nonlock_view().last().new_u.thread_map.spec_index(quota_thread) == kernel_k_to_nonlock_kernel_u(*final(krnl)).thread_map.spec_index(quota_thread)
            &&& target_write_held && typed_lock_map_contains_mode(old(lctx).process_lock_map(), target_process, TypedLockMode::Write) && ({
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
        !thread_is_dangling(final(krnl).thr_mp.spec_index(quota_thread)),
        final(krnl).thr_mp.lock_id_by_key(quota_thread) == old(krnl).thr_mp.lock_id_by_key(quota_thread),
        source_pagetable_lock_perm.state() is WriteLock ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable),
        source_pagetable_lock_perm.state() is ReadLock ==> {
            &&& final(krnl).pt_mp.spec_index(source_pagetable).rlocked_by_thread(old(lctx).thread_id())
            &&& final(krnl).pt_mp.spec_index(source_pagetable).being_killed() == old(krnl).pt_mp.spec_index(source_pagetable).being_killed()
            &&& final(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Read_reader_map.spec_index(old(lctx).thread_id())
                == old(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Read_reader_map.spec_index(old(lctx).thread_id())
        },
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((source_pagetable, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((source_pagetable, w)) ==> {
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).window_view(w) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).window_view(w)
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_2m().dom().contains(w.va) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_2m().dom().contains(w.va)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_2m().dom().contains(w.va)
                    ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_2m().spec_index(w.va) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_2m().spec_index(w.va)
            },
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w)) && (p == source_pagetable || p == target_pagetable) ==> {
                let pre = pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), p);
                let post = pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), p);
                &&& post.window_view(w).lock_state == pre.window_view(w).lock_state
                &&& post.window_view(w).stale_cpus == pre.window_view(w).stale_cpus
                &&& pre.window_leaves_present(w) ==> post.window_leaves_present(w)
            },
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).higher == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).higher,
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).higher == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).higher,
        forall|w: WindowVa, v: VAddr|
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((source_pagetable, w)), pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_4k().dom().contains(v)]
            old(lctx).pagetable_window_lock_map().dom().contains((source_pagetable, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_4k().dom().contains(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().dom().contains(v)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().dom().contains(v)
                    ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_4k().spec_index(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().spec_index(v)
            },
        progress_thread != source_thread ==> final(krnl).thr_mp.spec_index(source_thread).view() == old(krnl).thr_mp.spec_index(source_thread).view(),
        source_thread != quota_thread ==> final(krnl).thr_mp.spec_index(source_thread).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(source_thread).view().syscall_progress, ..old(krnl).thr_mp.spec_index(source_thread).view() }),
        final(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress.view() == Some(SyscallProgress::Share4k { source_range: *source_range, target_range: *target_range, shared: source_range.len, origin }),
        final(krnl).thr_mp.spec_index(progress_thread).view_ghost() == old(krnl).thr_mp.spec_index(progress_thread).view_ghost(),
        final(krnl).thr_mp.spec_index(quota_thread).view_ghost() == old(krnl).thr_mp.spec_index(quota_thread).view_ghost(),
        final(krnl).thr_mp.spec_index(source_thread).view_ghost() == old(krnl).thr_mp.spec_index(source_thread).view_ghost(),
        final(krnl).thr_mp.spec_index(quota_thread).view().temp_alloc_cache_4k.view() == old(krnl).thr_mp.spec_index(quota_thread).view().temp_alloc_cache_4k.view(),
        final(krnl).thr_mp.spec_index(quota_thread).view().temp_alloc_cache_2m.view().len() == 0,
        final(krnl).thr_mp.spec_index(quota_thread).view().temp_alloc_cache_1g.view().len() == 0,
        final(krnl).thr_mp.spec_index(quota_thread).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(quota_thread).view().owning_proc == old(krnl).thr_mp.spec_index(quota_thread).view().owning_proc,
        final(krnl).thr_mp.spec_index(quota_thread).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(quota_thread).view().proc_pagetable_ptr,
        final(krnl).thr_mp.spec_index(quota_thread).view().state == old(krnl).thr_mp.spec_index(quota_thread).view().state,
        quota_thread != progress_thread ==> final(krnl).thr_mp.spec_index(quota_thread).view().syscall_progress.view() is None,
        final(krnl).thr_mp.spec_index(quota_thread).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(quota_thread).view().blocking_endpoint_ptr,
        final(krnl).thr_mp.spec_index(quota_thread).view().quota_4k == old(krnl).thr_mp.spec_index(quota_thread).view().quota_4k,
        forall|w: WindowVa, v: VAddr|
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, w)), pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_4k().dom().contains(v)]
            old(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
                let expected = share_mapping_4k_target_map_with_shared_prefix(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k(), pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_4k(),
                    source_range, target_range, source_range.len as nat);
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_4k().dom().contains(v) == expected.dom().contains(v)
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_4k().dom().contains(v) ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_4k().spec_index(v) == expected.spec_index(v)
            },
        forall|w: WindowVa|
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, w)) && old(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end <= spec_v2l4index(w.va)
                && pei_valid(spec_v2l4index(w.va)) && pei_valid(spec_v2l3index(w.va)) && pei_valid(spec_v2l2index(w.va))
                ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).spec_resolve_mapping_l2(spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va))
                    == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).spec_resolve_mapping_l2(spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va)),
        target_write_held ==> {
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_4k()
                == share_mapping_4k_target_map_with_shared_prefix(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k(), pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_4k(),
                    source_range, target_range, source_range.len as nat)
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).user_view(LockStateU::Unlocked).mapping_4k
                == share_mapping_4k_target_map_with_shared_prefix(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).user_view(LockStateU::Unlocked).mapping_4k,
                    pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).user_view(LockStateU::Unlocked).mapping_4k, source_range, target_range, source_range.len as nat)
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_2m()
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_1g()
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).leaves_present()
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.l2_lock == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).lower.l2_lock
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus
        },
{
    hide(Set::is_empty);
    proof {
        assert({
            &&& held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx))
            &&& held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx))
            &&& held_endpoints_unchanged(old(krnl).ep_mp, krnl.ep_mp, old(lctx))
            &&& held_iommu_tables_unchanged(old(krnl).it_mp, krnl.it_mp, old(lctx))
            &&& held_cpus_unchanged(old(krnl).cpu_arr, krnl.cpu_arr, old(lctx))
            &&& held_pages_unchanged(old(krnl).pg_arr, krnl.pg_arr, old(lctx))
        }) by { held_kernel_objects_unchanged_reflexive(krnl, lctx); };
        assert(pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).wf()) by { pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable); };
        if source_pagetable_lock_perm.state() is ReadLock { krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), source_pagetable); }
        assert(share_mapping_4k_target_range_empty_from(pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).mapping_4k(), target_range, 0)
            && !pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).mapping_4k().dom().contains(target_range.view().spec_index(0))) by { reveal(share_mapping_4k_target_range_empty_from); };
    }
    assert(pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).mapping_4k() == share_mapping_4k_target_map_with_shared_prefix(
        pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable).mapping_4k(), pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).mapping_4k(),
        source_range, target_range, 0)) by { reveal(share_mapping_4k_target_map_with_shared_prefix); };
    proof {
        assert(origin matches Share4kOrigin::IpcPages { peer } ==> peer == source_thread || peer == quota_thread) by { reveal(share_4k_objects_k); };
        assert(share_mapping_4k_build_and_share_eol_loop_framing(*old(krnl), *krnl, old(lctx), old(steps), steps, 0, source_range, target_range, source_thread, quota_thread,
            progress_thread, target_process, target_container, cpu_id, source_pagetable, target_pagetable, source_pagetable_lock_perm.state() is WriteLock, target_write_held)) by {
            reveal(share_mapping_4k_build_and_share_eol_loop_framing); reveal(share_mapping_4k_target_map_with_shared_prefix);
        };
    }
    let mut i: usize = 0;
    while i < source_range.len
        invariant
            krnl.inv(),
            typed_lock_maps_aligned(krnl, &*lctx),
            0 <= i <= source_range.len,
            share_mapping_4k_build_and_share_eol_loop_framing(*old(krnl), *krnl, old(lctx), old(steps), steps, i as nat, source_range, target_range, source_thread, quota_thread,
                progress_thread, target_process, target_container, cpu_id, source_pagetable, target_pagetable, source_pagetable_lock_perm.state() is WriteLock, target_write_held),
            steps.snapshot_k() == *krnl,
            lctx.kernel_view_locking_state() is Acquire,
            lctx.thread_lock_map().dom() == set![source_thread, quota_thread],
            lctx.pagetable_lock_map().dom() == set![source_pagetable, target_pagetable],
            held_locks_order_below(krnl, lctx, PAGE_TABLE_WINDOW_LOCK_MAJOR),
            lctx.scheduler_lock_map().dom().is_empty(),
            lctx.cpu_set_lock_map().dom().is_empty(),
            krnl.thr_mp.dom().contains(source_thread),
            krnl.thr_mp.dom().contains(quota_thread),
            typed_lock_map_contains_mode(lctx.thread_lock_map(), source_thread, TypedLockMode::Write),
            !krnl.thr_mp.spec_index(source_thread).being_killed(),
            !thread_is_dangling(krnl.thr_mp.spec_index(source_thread)),
            typed_lock_map_contains_mode(lctx.thread_lock_map(), quota_thread, TypedLockMode::Write),
            !krnl.thr_mp.spec_index(quota_thread).being_killed(),
            !thread_is_dangling(krnl.thr_mp.spec_index(quota_thread)),
            krnl.thr_mp.spec_index(source_thread).view().owning_proc != target_process,
            krnl.thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
            transfer_source is None ==> krnl.thr_mp.spec_index(quota_thread).view().owning_container == target_container,
            transfer_source is Some ==> {
                &&& krnl.ctn_mp.spec_index(target_container).view_rodata().view().parent == transfer_source
                &&& typed_lock_map_contains_mode(lctx.container_lock_map(), target_container, TypedLockMode::Write)
                &&& krnl.ctn_mp.spec_index(target_container).view_ghost() == old(krnl).ctn_mp.spec_index(target_container).view_ghost()
            },
            krnl.prc_mp.dom().contains(target_process),
            krnl.prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container,
            krnl.prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable,
            ((krnl.thr_mp.spec_index(quota_thread).view().owning_proc == target_process && krnl.thr_mp.spec_index(quota_thread).view().proc_pagetable_ptr == target_pagetable && !krnl.thr_mp.spec_index(quota_thread).view_ghost().exited)
                || (typed_lock_map_contains_mode(lctx.process_lock_map(), target_process, TypedLockMode::Write) && !krnl.prc_mp.spec_index(target_process).view().zombie && !(krnl.prc_mp.spec_index(target_process).view().state.view() is TablesEmptied))),
            source_thread_lock_perm.state() is WriteLock,
            source_thread_lock_perm.thread_id() == lctx.thread_id(),
            source_thread_lock_perm.lock_id() == krnl.thr_mp.spec_index(source_thread).locking_thread()->Write_lock_id,
            quota_thread_lock_perm.state() is WriteLock,
            quota_thread_lock_perm.thread_id() == lctx.thread_id(),
            quota_thread_lock_perm.lock_id() == krnl.thr_mp.spec_index(quota_thread).locking_thread()->Write_lock_id,
            krnl.pt_mp.dom().contains(source_pagetable),
            krnl.pt_mp.dom().contains(target_pagetable),
            krnl.pt_mp.spec_index(source_pagetable).view().proc_ptr == krnl.thr_mp.spec_index(source_thread).view().owning_proc,
            krnl.pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
            source_pagetable_lock_perm.thread_id() == lctx.thread_id(),
            source_pagetable_lock_perm.state() is ReadLock || source_pagetable_lock_perm.state() is WriteLock,
            source_pagetable_lock_perm.state() is ReadLock ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), source_pagetable, TypedLockMode::Read),
            source_pagetable_lock_perm.state() is ReadLock ==> krnl.pt_mp.spec_index(source_pagetable).locking_thread()->Read_reader_map.contains_pair(lctx.thread_id(), source_pagetable_lock_perm.lock_id()),
            source_pagetable_lock_perm.state() is WriteLock ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), source_pagetable, TypedLockMode::Write),
            source_pagetable_lock_perm.state() is WriteLock ==> source_pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
            target_pagetable_lock_perm.thread_id() == lctx.thread_id(),
            target_pagetable_lock_perm.state() is ReadLock || target_pagetable_lock_perm.state() is WriteLock,
            target_pagetable_lock_perm.state() is ReadLock ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), target_pagetable, TypedLockMode::Read),
            target_pagetable_lock_perm.state() is ReadLock ==> krnl.pt_mp.spec_index(target_pagetable).locking_thread()->Read_reader_map.contains_pair(lctx.thread_id(), target_pagetable_lock_perm.lock_id()),
            target_pagetable_lock_perm.state() is WriteLock ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
            target_pagetable_lock_perm.state() is WriteLock ==> target_pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
            target_write_held == (target_pagetable_lock_perm.state() is WriteLock),
            typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
            index_valid(NUM_CPUS, cpu_id),
            krnl.ctn_mp.dom().contains(target_container),
            source_range.wf(),
            old(krnl).pt_mp.spec_index(source_pagetable).view().kernel_l4_end <= spec_va2index(source_range.start).0,
            target_range.wf(),
            source_range.len == target_range.len,
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            old(krnl).inv(),
            typed_lock_maps_unchanged(old(lctx), lctx),
            krnl.pt_mp.spec_index(source_pagetable).view() == old(krnl).pt_mp.spec_index(source_pagetable).view(),
            krnl.pt_mp.spec_index(target_pagetable).view() == old(krnl).pt_mp.spec_index(target_pagetable).view(),
            progress_thread == source_thread || progress_thread == quota_thread,
            krnl.thr_mp.spec_index(progress_thread).view().syscall_progress.view() == Some(SyscallProgress::Share4k { source_range: *source_range, target_range: *target_range, shared: i, origin }),
            origin matches Share4kOrigin::IpcPages { peer }
                ==> (peer == source_thread || peer == quota_thread) && krnl.thr_mp.spec_index(peer).view().state is IPC_TRANSIT && krnl.thr_mp.spec_index(peer).view().state->IPC_TRANSIT_partner == progress_thread,
            krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(progress_thread),
            share_4k_objects_k(*krnl, cpu_id).source_thread == source_thread && share_4k_objects_k(*krnl, cpu_id).quota_thread == quota_thread,
            share_4k_objects_k(*krnl, cpu_id).target == target_process && share_4k_objects_k(*krnl, cpu_id).target_container == target_container,
            share_4k_objects_k(*krnl, cpu_id).transfer_source == transfer_source,
            krnl.thr_mp.spec_index(quota_thread).view().upper_container_seq == old(krnl).thr_mp.spec_index(quota_thread).view().upper_container_seq,
            krnl.thr_mp.spec_index(quota_thread).view().owning_container == old(krnl).thr_mp.spec_index(quota_thread).view().owning_container,
            forall|j: int| #![trigger source_range.view().spec_index(j)] 0 <= j < source_range.len ==> {
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().dom().contains(source_range.view().spec_index(j))
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_range.view().spec_index(j)).present
            },
            share_mapping_4k_range_owner_compatible(old(krnl), source_pagetable, target_container, source_range),
            forall|j: int| #![trigger source_range.view().spec_index(j)] 0 <= j < source_range.len ==> old(lctx).pagetable_window_lock_map().dom().contains((source_pagetable, window_of(source_range.view().spec_index(j)))),
            forall|j: int| #![trigger target_range.view().spec_index(j)] 0 <= j < target_range.len ==> {
                let va = target_range.view().spec_index(j);
                &&& old(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, window_of(va)))
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some
            },
            old(krnl).thr_mp.dom().contains(quota_thread),
            krnl.pt_mp.spec_index(target_pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end,
            krnl.pt_mp.spec_index(target_pagetable).view().kernel_l4_end <= spec_v2l4index(target_range.start),
        decreases source_range.len - i,
    {
        let source_va = source_range.index(i);
        let target_va = target_range.index(i);
        proof {
            let source_page = page_ptr2page_index(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_va).addr);
            source_range.va_range_lemma(); target_range.va_range_lemma(); spec_va_4k_valid_imply_indices_valid(); spec_v2l4index_monotonic(target_range.start, target_va); spec_v2l4index_monotonic(source_range.start, source_va);
            spec_va_4k_index_roundtrip_at(source_va, spec_v2l4index(source_va), spec_v2l3index(source_va), spec_v2l2index(source_va), spec_v2l1index(source_va));
            spec_va_4k_index_roundtrip_at(window_of(source_va).va, spec_v2l4index(source_va), spec_v2l3index(source_va), spec_v2l2index(source_va), 0);
            spec_va_4k_index_roundtrip_at(target_va, spec_v2l4index(target_va), spec_v2l3index(target_va), spec_v2l2index(target_va), spec_v2l1index(target_va));
            spec_va_4k_index_roundtrip_at(window_of(target_va).va, spec_v2l4index(target_va), spec_v2l3index(target_va), spec_v2l2index(target_va), 0);
            assert(pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable).mapping_4k().dom().contains(source_va)
                && pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_va) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_va))
                by { reveal(share_mapping_4k_build_and_share_eol_loop_framing); };
            assert(!pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).mapping_4k().dom().contains(target_va)) by { reveal(share_mapping_4k_build_and_share_eol_loop_framing); };
            assert(pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).spec_resolve_mapping_l2(spec_v2l4index(target_va), spec_v2l3index(target_va), spec_v2l2index(target_va)) is Some)
                by { reveal(share_mapping_4k_build_and_share_eol_loop_framing); };
            assert(share_mapping_4k_leaf_ready(krnl, source_pagetable, target_pagetable, target_container, source_va, target_va)) by {
                page_ptr_valid_imply_page_index_valid(); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable); mapped_4k_page_pagetable_wf_pagetable_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, source_pagetable, source_va);
                container_page_owner_backward_at(krnl.ctn_mp, krnl.pg_arr, source_page);
                container_thread_wf_uppertree_at(old(krnl).ctn_mp, old(krnl).thr_mp, quota_thread); container_thread_wf_uppertree_at(krnl.ctn_mp, krnl.thr_mp, quota_thread);
            };
        }
        let ghost leaf_before = steps.view();
        let ghost krnl_i = *krnl;
        share_one_mapping_4k(
            krnl, source_thread, quota_thread, progress_thread, target_process, target_container, source_pagetable, target_pagetable, target_write_held,
            cpu_id, source_va, target_va, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(source_thread_lock_perm), Tracked(quota_thread_lock_perm),
            Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm),
        );
        proof {
            assert(share_mapping_4k_build_and_share_eol_loop_framing(*old(krnl), *krnl, old(lctx), old(steps), steps, (i + 1) as nat, source_range, target_range, source_thread, quota_thread,
                progress_thread, target_process, target_container, cpu_id, source_pagetable, target_pagetable, source_pagetable_lock_perm.state() is WriteLock, target_write_held)) by {
                reveal(share_mapping_4k_build_and_share_eol_loop_framing); share_4k_range_steps_from_leaf(&*steps, leaf_before, old(steps).view().len() as int, cpu_id);
                prove_share_mapping_4k_iteration_target_partition(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k(),
                    pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_4k(), source_range, target_range, i, old(lctx).pagetable_window_lock_map().dom(), target_pagetable,
                    pagetable_c(krnl_i.pt_mp, krnl_i.pt_lower.view(), target_pagetable).mapping_4k(), pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).mapping_4k(),
                    pagetable_c(krnl_i.pt_mp, krnl_i.pt_lower.view(), source_pagetable).mapping_4k().spec_index(source_va));
                if target_write_held {
                    assert(pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).user_view(LockStateU::Unlocked).mapping_4k == share_mapping_4k_target_map_with_shared_prefix(
                        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).user_view(LockStateU::Unlocked).mapping_4k,
                        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).user_view(LockStateU::Unlocked).mapping_4k, source_range, target_range, (i + 1) as nat)) by {
                        assert(pagetable_c(krnl_i.pt_mp, krnl_i.pt_lower.view(), source_pagetable).user_view(LockStateU::Unlocked).mapping_4k.spec_index(source_va)
                            == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).user_view(LockStateU::Unlocked).mapping_4k.spec_index(source_va));
                        reveal(share_mapping_4k_target_map_with_shared_prefix);
                    };
                }
            };
        }
        i = i + 1;
    }
    proof { reveal(share_mapping_4k_build_and_share_eol_loop_framing); kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
}
} // verus!
