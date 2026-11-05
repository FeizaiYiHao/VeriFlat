use vstd::prelude::*;
use crate::*;
use super::syscall_mmap_2m_hide_reclaim::{mmap_2m_flush_and_reclaim_hidden_l1_range, mmap_2m_hide_linked_l1_range};
use super::syscall_mmap_2m_finish::mmap_2m_unlock_range_and_finish;
use super::syscall_mmap_2m_map_one_leaf::mmap_2m_page;
use super::syscall_mmap_2m_spec::*;
use super::syscall_mmap_2m_trace::*;

verus! {
/// Under the pagetable's big read lock, holding the 2M windows of `va_range` through `window_perms`, none of which owns an
/// L1 page or lists a stale CPU, publish a present, writable, executable 2M leaf for every page of the range in order, one
/// leaf step each. Every window keeps its lock state, its stale CPUs and its 4K leaves, and owns no L1 page.
fn mmap_2m_map_leaf_range(
    krnl: &mut KernelK, va_range: &VaRange2M, thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr, cpu_id: CpuId, pagetable_ptr: RwLockPageTableRoot,
    Ghost(phase): Ghost<Mmap2mPhase>, Ghost(flushed): Ghost<bool>, Ghost(t4k): Ghost<WholePageTable<PT_TYPE>>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    Tracked(thread_lock_perm): Tracked<&LockPerm>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>, Tracked(window_perms): Tracked<&Map<WindowVa, LockPerm>>,
)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k() == *old(krnl),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).prc_mp.dom().contains(prc_ptr),
        old(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr,
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_2m >= va_range.len,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap2m { range: *va_range, mapped: 0, directory: Mmap2mDirectory::None, phase, flushed }),
        !(phase is Fill),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        pagetable_lock_perm.state() is ReadLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        va_range.wf(),
        forall|w: WindowVa, u: VAddr|
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u)]
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), t4k.mapping_4k().dom().contains(u)]
            old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) && spec_v2l4index(u) == spec_v2l4index(w.va) && spec_v2l3index(u) == spec_v2l3index(w.va)
                && spec_v2l2index(u) == spec_v2l2index(w.va) ==> {
                &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u) == t4k.mapping_4k().dom().contains(u)
                &&& t4k.mapping_4k().dom().contains(u) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(u) == t4k.mapping_4k().spec_index(u)
            },
        forall|j: int| #![trigger va_range.view()[j]] 0 <= j < va_range.len ==> {
            let v = va_range.view()[j];
            let table = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr);
            &&& window_of(v).va == v
            &&& old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, window_of(v)))
            &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable_ptr, window_of(v)), TypedLockMode::Write)
            &&& window_perms.dom().contains(window_of(v))
            &&& window_perms.index(window_of(v)).thread_id() == old(lctx).thread_id()
            &&& table.window_view(window_of(v)).lock_state == (RwLockState::Write { thread_id: window_perms.index(window_of(v)).thread_id(), lock_id: window_perms.index(window_of(v)).lock_id() })
            &&& table.kernel_l4_end() <= spec_v2l4index(v)
            &&& table.spec_resolve_mapping_l3(spec_v2l4index(v), spec_v2l3index(v)) is Some
            &&& table.window_view(window_of(v)).l1_table is None
            &&& table.window_view(window_of(v)).stale_cpus is None
            &&& !table.mapping_2m().dom().contains(v)
        },
    ensures
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view().len() == old(steps).view().len() + va_range.len,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==> mmap_2m_range_step(final(steps).view()[j], cpu_id),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        final(krnl).cpu_op.view().view()[cpu_id as int] == old(krnl).cpu_op.view().view()[cpu_id as int],
        final(krnl).prc_mp.dom().contains(prc_ptr),
        final(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr,
        final(krnl).thrd_mp.dom().contains(thrd_ptr),
        !final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().state == old(krnl).thrd_mp.spec_index(thrd_ptr).view().state,
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap2m { range: *va_range, mapped: va_range.len, directory: Mmap2mDirectory::None, phase, flushed }),
        thread_lock_perm.lock_id() == final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        final(krnl).pt_mp.dom().contains(pagetable_ptr),
        final(krnl).pt_mp.spec_index(pagetable_ptr).view() == old(krnl).pt_mp.spec_index(pagetable_ptr).view(),
        final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        forall|w: WindowVa, u: VAddr|
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u)]
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), t4k.mapping_4k().dom().contains(u)]
            old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) && spec_v2l4index(u) == spec_v2l4index(w.va) && spec_v2l3index(u) == spec_v2l3index(w.va)
                && spec_v2l2index(u) == spec_v2l2index(w.va) ==> {
                &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u) == t4k.mapping_4k().dom().contains(u)
                &&& t4k.mapping_4k().dom().contains(u) ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(u) == t4k.mapping_4k().spec_index(u)
            },
        forall|j: int| #![trigger va_range.view()[j]] 0 <= j < va_range.len ==> {
            let v = va_range.view()[j];
            let pre = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr);
            let post = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr);
            &&& post.window_view(window_of(v)).lock_state == pre.window_view(window_of(v)).lock_state
            &&& post.window_view(window_of(v)).stale_cpus is None
            &&& post.window_view(window_of(v)).l1_table is None
            &&& post.mapping_2m().dom().contains(v)
            &&& post.mapping_2m().spec_index(v).present
            &&& post.mapping_2m().spec_index(v).write
            &&& !post.mapping_2m().spec_index(v).execute_disable
        },
{
    let ghost t0 = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
    let ghost quota = krnl.thrd_mp.spec_index(thrd_ptr).view().quota_2m;
    let mut i: usize = 0;
    while i < va_range.len
        invariant
            krnl.inv(),
            lctx.kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(krnl, lctx),
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.thread_id() == old(lctx).thread_id(),
            held_locks_order_below(krnl, lctx, ALLOCATOR_CACHE_4K_MAJOR),
            steps.snapshot_k() == *krnl,
            steps.view().len() == old(steps).view().len() + i,
            forall|j: int| #![trigger steps.view()[j]] 0 <= j < old(steps).view().len() ==> steps.view()[j] == old(steps).view()[j],
            forall|j: int| #![trigger steps.view()[j]] old(steps).view().len() <= j < steps.view().len() ==> mmap_2m_range_step(steps.view()[j], cpu_id),
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
            krnl.cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            krnl.cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
            krnl.cpu_op.view().view()[cpu_id as int] == old(krnl).cpu_op.view().view()[cpu_id as int],
            old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
            krnl.prc_mp.dom().contains(prc_ptr),
            krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr,
            krnl.thrd_mp.dom().contains(thrd_ptr),
            !krnl.thrd_mp.spec_index(thrd_ptr).being_killed(),
            !thread_is_dangling(krnl.thrd_mp.spec_index(thrd_ptr)),
            krnl.thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
            !old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
            krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
            krnl.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
            krnl.thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr,
            krnl.thrd_mp.spec_index(thrd_ptr).view().state == old(krnl).thrd_mp.spec_index(thrd_ptr).view().state,
            krnl.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
            krnl.thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
            krnl.thrd_mp.spec_index(thrd_ptr).view().quota_2m + i == quota,
            quota >= va_range.len,
            krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap2m { range: *va_range, mapped: i, directory: Mmap2mDirectory::None, phase, flushed }),
            !(phase is Fill),
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == krnl.thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
            pagetable_lock_perm.state() is ReadLock,
            pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
            krnl.pt_mp.dom().contains(pagetable_ptr),
            krnl.pt_mp.spec_index(pagetable_ptr).view() == old(krnl).pt_mp.spec_index(pagetable_ptr).view(),
            krnl.pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
            t0 == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr),
            va_range.wf(),
            i <= va_range.len,
            forall|w: WindowVa, u: VAddr|
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u)]
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), t4k.mapping_4k().dom().contains(u)]
                old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) && spec_v2l4index(u) == spec_v2l4index(w.va) && spec_v2l3index(u) == spec_v2l3index(w.va)
                    && spec_v2l2index(u) == spec_v2l2index(w.va) ==> {
                    &&& whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u) == t4k.mapping_4k().dom().contains(u)
                    &&& t4k.mapping_4k().dom().contains(u) ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(u) == t4k.mapping_4k().spec_index(u)
                },
            forall|j: int| #![trigger va_range.view()[j]] 0 <= j < va_range.len ==> {
                let v = va_range.view()[j];
                let cur = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
                &&& window_of(v).va == v
                &&& old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, window_of(v)))
                &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable_ptr, window_of(v)), TypedLockMode::Write)
                &&& window_perms.dom().contains(window_of(v))
                &&& window_perms.index(window_of(v)).thread_id() == old(lctx).thread_id()
                &&& t0.window_view(window_of(v)).lock_state == (RwLockState::Write { thread_id: window_perms.index(window_of(v)).thread_id(), lock_id: window_perms.index(window_of(v)).lock_id() })
                &&& cur.window_view(window_of(v)).lock_state == t0.window_view(window_of(v)).lock_state
                &&& t0.kernel_l4_end() <= spec_v2l4index(v)
                &&& t0.spec_resolve_mapping_l3(spec_v2l4index(v), spec_v2l3index(v)) is Some
                &&& cur.window_view(window_of(v)).l1_table is None
                &&& cur.window_view(window_of(v)).stale_cpus is None
            },
            forall|j: int| #![trigger va_range.view()[j]] 0 <= j < i ==> {
                let post = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
                &&& post.mapping_2m().dom().contains(va_range.view()[j])
                &&& post.mapping_2m().spec_index(va_range.view()[j]).present
                &&& post.mapping_2m().spec_index(va_range.view()[j]).write
                &&& !post.mapping_2m().spec_index(va_range.view()[j]).execute_disable
            },
            forall|j: int| #![trigger va_range.view()[j]] i <= j < va_range.len ==> !whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_2m().dom().contains(va_range.view()[j]),
        decreases va_range.len - i,
    {
        let va = va_range.index(i);
        let ghost before = steps.view();
        proof {
            assert(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).higher == t0.higher);
            spec_va_2m_valid_index_roundtrip(va);
        }
        mmap_2m_page(krnl, thrd_ptr, prc_ptr, ctn_ptr, cpu_id, pagetable_ptr, va, Ghost(*va_range), Ghost(i), Ghost(phase), Ghost(flushed), Tracked(&mut *lctx), Tracked(&mut *steps),
            Tracked(thread_lock_perm), Tracked(pagetable_lock_perm), Tracked(window_perms.tracked_borrow(window_of(va))));
        proof {
            assert forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() implies steps.view()[j] == before[j] by { assert(steps.view().drop_last()[j] == steps.view()[j]); };
            assert(steps.view() =~= before.push(steps.view().last()));
            mmap_2m_range_steps_from_leaf(&*steps, before, old(steps).view().len() as int, cpu_id);
            assert forall|j: int| #![trigger va_range.view()[j]] 0 <= j < va_range.len && j != i implies va_range.view()[j] != va by {
                assert(va_range.view().no_duplicates());
            };
        }
        i = i + 1;
    }
}

/// Under the pagetable's big read lock, holding exactly the 2M windows of `va_range` through `window_perms`, none of which
/// maps a leaf: hide and flush every L1 page those windows link and return the pages to the caller's container. Afterwards
/// no window of the range owns an L1 page or lists a stale CPU; the caller's cpu and thread are unchanged.
fn mmap_2m_clear_range_windows(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, range: usize, va_range: &VaRange2M,
    thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr, pagetable_ptr: RwLockPageTableRoot, Ghost(phase): Ghost<Mmap2mPhase>, Ghost(t4k): Ghost<WholePageTable<PT_TYPE>>,
    Tracked(cpu_lock_perm): Tracked<&LockPerm>, Tracked(thread_lock_perm): Tracked<&LockPerm>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
    Tracked(window_perms): Tracked<&Map<WindowVa, LockPerm>>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k() == *old(krnl),
        range > 0,
        *va_range == mmap_2m_syscall_va_range(va, range),
        va_range.wf(),
        !(phase is Fill),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap2m { range: *va_range, mapped: 0, directory: Mmap2mDirectory::None, phase, flushed: false }),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(pagetable_ptr),
        pagetable_lock_perm.state() is ReadLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va_range.start),
        va_range.covering_4k_range().wf(),
        old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_mapping_4k_va_range_windows_exist(&va_range.covering_4k_range()),
        forall|w: WindowVa| #![trigger va_range_2m_windows(va_range.covering_4k_range()).contains(w)] va_range_2m_windows(va_range.covering_4k_range()).contains(w) ==> {
            let table = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr);
            let l2_page = table.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va));
            &&& window_perms.dom().contains(w)
            &&& window_perms.index(w).state() is WriteLock
            &&& window_perms.index(w).thread_id() == old(lctx).thread_id()
            &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable_ptr, w), TypedLockMode::Write)
            &&& table.lower.l2_owner(l2_page, spec_v2l2index(w.va)) == (RwLockState::Write { thread_id: window_perms.index(w).thread_id(), lock_id: window_perms.index(w).lock_id() })
            &&& !table.lower.window_stale_cpus.dom().contains((l2_page, spec_v2l2index(w.va)))
            &&& !table.lower.l2_entry_hides_l1(l2_page, spec_v2l2index(w.va))
            &&& !table.mapping_2m().dom().contains(w.va)
            &&& forall|l1i: L1Index| #![trigger t4k.mapping_4k().dom().contains(spec_index2va((spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va), l1i)))]
                pei_valid(l1i) ==> !t4k.mapping_4k().dom().contains(spec_index2va((spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va), l1i)))
        },
        forall|w: WindowVa, u: VAddr|
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u)]
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), t4k.mapping_4k().dom().contains(u)]
            old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) && spec_v2l4index(u) == spec_v2l4index(w.va) && spec_v2l3index(u) == spec_v2l3index(w.va)
                && spec_v2l2index(u) == spec_v2l2index(w.va) ==> {
                &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u) == t4k.mapping_4k().dom().contains(u)
                &&& t4k.mapping_4k().dom().contains(u) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(u) == t4k.mapping_4k().spec_index(u)
            },
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == pagetable_ptr && va_range_2m_windows(va_range.covering_4k_range()).contains(w)),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
    ensures
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len() <= old(steps).view().len() + NUM_CPUS + 1 + range,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==> mmap_2m_range_step(final(steps).view()[j], cpu_id),
        final(krnl).cpu_op.view().view()[cpu_id as int] == old(krnl).cpu_op.view().view()[cpu_id as int],
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).thrd_mp.dom().contains(thrd_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap2m {
            range: *va_range, mapped: 0, directory: Mmap2mDirectory::None, phase, flushed: final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()->Some_0->Mmap2m_flushed
        }),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        final(krnl).pt_mp.dom().contains(pagetable_ptr),
        final(krnl).pt_mp.spec_index(pagetable_ptr).view() == old(krnl).pt_mp.spec_index(pagetable_ptr).view(),
        final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        forall|w: WindowVa, u: VAddr|
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u)]
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), t4k.mapping_4k().dom().contains(u)]
            old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) && spec_v2l4index(u) == spec_v2l4index(w.va) && spec_v2l3index(u) == spec_v2l3index(w.va)
                && spec_v2l2index(u) == spec_v2l2index(w.va) ==> {
                &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u) == t4k.mapping_4k().dom().contains(u)
                &&& t4k.mapping_4k().dom().contains(u) ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(u) == t4k.mapping_4k().spec_index(u)
            },
        forall|j: int| #![trigger va_range.view()[j]] 0 <= j < va_range.len ==> {
            let v = va_range.view()[j];
            let pre = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr);
            let post = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr);
            &&& window_of(v).va == v
            &&& va_range_2m_windows(va_range.covering_4k_range()).contains(window_of(v))
            &&& pre.kernel_l4_end() <= spec_v2l4index(v)
            &&& pre.spec_resolve_mapping_l3(spec_v2l4index(v), spec_v2l3index(v)) is Some
            &&& post.window_view(window_of(v)).lock_state == pre.window_view(window_of(v)).lock_state
            &&& post.window_view(window_of(v)).l1_table is None
            &&& post.window_view(window_of(v)).stale_cpus is None
            &&& !post.mapping_2m().dom().contains(v)
        },
{
    let ghost cover = va_range.covering_4k_range();
    let ghost t0 = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
    proof {
        let s = va_range.start;
        broadcast use spec_va_2m_valid_index_roundtrip;
        va_range.wf_implies_view_index_is_start_plus_offset(); cover.wf_implies_view_index_is_start_plus_offset();
        va_range_2m_windows_contains_window_of_first_n_pages(cover, cover.len as int);
        assert forall|j: int| #![trigger va_range.view()[j]] 0 <= j < range implies {
            let v = va_range.view()[j];
            &&& va_range_2m_windows(cover).contains(window_of(v))
            &&& window_of(v).va == v
            &&& t0.kernel_l4_end() <= spec_v2l4index(v)
        } by {
            let v = va_range.view()[j];
            assert(cover.view()[512 * j] == v) by {
                assert(spec_va_add_range(s, (512 * j) as usize) == spec_va_add_range_2m(s, j as usize)) by (nonlinear_arith)
                    requires 0 <= j < range, range <= usize::MAX / 0x200000, s < usize::MAX - range * 0x200000;
            };
            assert(spec_va_2m_valid(s) ==> spec_va_4k_valid(s)) by (bit_vector);
            assert(spec_va_2m_valid(v) ==> spec_va_4k_valid(v)) by (bit_vector);
            assert(s <= v) by (nonlinear_arith) requires v == spec_va_add_range_2m(s, j as usize), 0 <= j < range, s < usize::MAX - range * 0x200000;
            spec_v2l4index_monotonic(s, v);
        };
    }
    let hidden = mmap_2m_hide_linked_l1_range(krnl, va_range, pagetable_ptr, Ghost(t4k), Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(pagetable_lock_perm), Tracked(window_perms));
    if hidden {
        mmap_2m_flush_and_reclaim_hidden_l1_range(krnl, va_range, cpu_id, thrd_ptr, prc_ptr, ctn_ptr, pagetable_ptr, Ghost(phase), Ghost(t4k), Tracked(&mut *lctx), Tracked(&mut *steps),
            Tracked(cpu_lock_perm), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm), Tracked(window_perms));
    }
}

/// Under the pagetable's big read lock, holding exactly the 2M windows of `va_range` through `window_perms`, none of which
/// maps a leaf: hide and flush every L1 page those windows link, return the pages to the caller's container, map every page
/// of the range, then release the windows and every lock and record the exiting step.
pub(super) fn mmap_2m_map_leaves_and_finish(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, range: usize, va_range: &VaRange2M,
    alloc_ptr_4k: RwLockPageAllocatorPtr, thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr, pagetable_ptr: RwLockPageTableRoot,
    Ghost(enter_phase): Ghost<Mmap2mPhase>, Ghost(entered): Ghost<Seq<KernelStep>>, Ghost(t4k): Ghost<WholePageTable<PT_TYPE>>, Tracked(thread_lock_perm): Tracked<LockPerm>,
    Tracked(pagetable_lock_perm): Tracked<LockPerm>, Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(window_perms): Tracked<Map<WindowVa, LockPerm>>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k() == *old(krnl),
        range > 0,
        va_4k_valid(va),
        *va_range == mmap_2m_syscall_va_range(va, range),
        va_range.wf(),
        enter_phase is Read || enter_phase is Fill,
        mmap_2m_trace_after_enter(entered, cpu_id, *va_range, enter_phase),
        entered.len() == if enter_phase is Fill { 2int } else { 1int },
        entered.len() <= old(steps).view().len() <= entered.len() + 2 * range + 1,
        forall|j: int| #![trigger old(steps).view()[j]] 0 <= j < entered.len() ==> old(steps).view()[j] == entered[j],
        forall|j: int| #![trigger old(steps).view()[j]] entered.len() <= j < old(steps).view().len() ==> mmap_2m_range_step(old(steps).view()[j], cpu_id),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).ctn_mp.dom().contains(ctn_ptr),
        old(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
        old(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
        old(krnl).prc_mp.dom().contains(prc_ptr),
        old(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container == ctn_ptr,
        old(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr,
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_2m >= range,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap2m {
            range: *va_range, mapped: 0, directory: Mmap2mDirectory::None, phase: if enter_phase is Read { Mmap2mPhase::Read } else { Mmap2mPhase::Filled }, flushed: false
        }),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(pagetable_ptr),
        pagetable_lock_perm.state() is ReadLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va_range.start),
        va_range.covering_4k_range().wf(),
        old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_mapping_4k_va_range_windows_exist(&va_range.covering_4k_range()),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == pagetable_ptr && va_range_2m_windows(va_range.covering_4k_range()).contains(w)),
        forall|w: WindowVa| #![trigger va_range_2m_windows(va_range.covering_4k_range()).contains(w)] va_range_2m_windows(va_range.covering_4k_range()).contains(w) ==> {
            let table = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr);
            let l2_page = table.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va));
            &&& window_perms.dom().contains(w)
            &&& window_perms.index(w).state() is WriteLock
            &&& window_perms.index(w).thread_id() == old(lctx).thread_id()
            &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable_ptr, w), TypedLockMode::Write)
            &&& table.lower.l2_owner(l2_page, spec_v2l2index(w.va)) == (RwLockState::Write { thread_id: window_perms.index(w).thread_id(), lock_id: window_perms.index(w).lock_id() })
            &&& !table.lower.window_stale_cpus.dom().contains((l2_page, spec_v2l2index(w.va)))
            &&& !table.lower.l2_entry_hides_l1(l2_page, spec_v2l2index(w.va))
            &&& !table.mapping_2m().dom().contains(w.va)
            &&& table.window_leaves_present(w)
            &&& forall|l1i: L1Index| #![trigger t4k.mapping_4k().dom().contains(spec_index2va((spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va), l1i)))]
                pei_valid(l1i) ==> !t4k.mapping_4k().dom().contains(spec_index2va((spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va), l1i)))
        },
        forall|w: WindowVa, u: VAddr|
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u)]
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), t4k.mapping_4k().dom().contains(u)]
            old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) && spec_v2l4index(u) == spec_v2l4index(w.va) && spec_v2l3index(u) == spec_v2l3index(w.va)
                && spec_v2l2index(u) == spec_v2l2index(w.va) ==> {
                &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u) == t4k.mapping_4k().dom().contains(u)
                &&& t4k.mapping_4k().dom().contains(u) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(u) == t4k.mapping_4k().spec_index(u)
            },
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).thread_lock_map().dom() =~= set![thrd_ptr],
        old(lctx).pagetable_lock_map().dom() =~= set![pagetable_ptr],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        entered.len() + range + 1 <= final(steps).view().len() <= entered.len() + 4 * range + NUM_CPUS + 3,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < entered.len() ==> final(steps).view()[j] == entered[j],
        mmap_2m_syscall_trace(final(steps).view(), cpu_id, va, range, enter_phase),
        mmap_2m_syscall_success_mapped(final(krnl), cpu_id, va, range),
{
    let ghost cover = va_range.covering_4k_range();
    let ghost phase = if enter_phase is Read { Mmap2mPhase::Read } else { Mmap2mPhase::Filled };
    proof {
        let s = va_range.start;
        broadcast use spec_va_2m_valid_index_roundtrip;
        va_range.wf_implies_view_index_is_start_plus_offset(); cover.wf_implies_view_index_is_start_plus_offset();
        assert forall|w: WindowVa| #![trigger va_range_2m_windows(cover).contains(w)] va_range_2m_windows(cover).contains(w) implies {
            let j = ((w.va - va_range.start) / 0x200000) as int;
            &&& 0 <= j < range
            &&& va_range.view()[j] == w.va
            &&& window_of(va_range.view()[j]) == w
        } by {
            let a = w.va;
            let last = va_range.view()[range - 1];
            let l4k = cover.view()[cover.len - 1];
            assert(spec_va_2m_valid(a) && spec_va_2m_valid(last));
            assert(last == s + (range - 1) * 0x200000 && l4k == last + 511 * 4096) by (nonlinear_arith)
                requires last == spec_va_add_range_2m(s, (range - 1) as usize), l4k == spec_va_add_range(s, (range * 512 - 1) as usize), cover.len == range * 512, range > 0,
                    range <= usize::MAX / 0x200000, s < usize::MAX - range * 0x200000;
            assert(spec_v2l4index(l4k) == spec_v2l4index(last) && spec_v2l3index(l4k) == spec_v2l3index(last) && spec_v2l2index(l4k) == spec_v2l2index(last)) by (bit_vector)
                requires spec_va_2m_valid(last), l4k == last + 511 * 4096;
            assert(s <= a) by (bit_vector)
                requires spec_va_2m_valid(s), spec_va_2m_valid(a),
                    spec_v2l4index(s) < spec_v2l4index(a) || (spec_v2l4index(s) == spec_v2l4index(a) && (spec_v2l3index(s) < spec_v2l3index(a)
                        || (spec_v2l3index(s) == spec_v2l3index(a) && spec_v2l2index(s) <= spec_v2l2index(a))));
            assert(a <= last) by (bit_vector)
                requires spec_va_2m_valid(a), spec_va_2m_valid(last),
                    spec_v2l4index(a) < spec_v2l4index(last) || (spec_v2l4index(a) == spec_v2l4index(last) && (spec_v2l3index(a) < spec_v2l3index(last)
                        || (spec_v2l3index(a) == spec_v2l3index(last) && spec_v2l2index(a) <= spec_v2l2index(last))));
            assert((a - s) as usize % 0x200000 == 0) by (bit_vector) requires spec_va_2m_valid(s), spec_va_2m_valid(a), s <= a;
            let j = (a - s) / 0x200000;
            assert(a == s + j * 0x200000 && 0 <= j < range) by (nonlinear_arith)
                requires (a - s) % 0x200000 == 0, j == (a - s) / 0x200000, s <= a, a <= last, last == s + (range - 1) * 0x200000, range > 0;
            assert(va_range.view()[j] == spec_va_add_range_2m(s, j as usize));
            assert(w == WindowVa { va: a });
        };
    }
    mmap_2m_clear_range_windows(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, range, va_range, thrd_ptr, prc_ptr, ctn_ptr, pagetable_ptr, Ghost(phase), Ghost(t4k),
        Tracked(&cpu_lock_perm), Tracked(&thread_lock_perm), Tracked(&pagetable_lock_perm), Tracked(&window_perms));
    let ghost flushed = krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()->Some_0->Mmap2m_flushed;
    proof {
        thread_perms_wf_at(krnl.thrd_mp, thrd_ptr); thread_cpu_wf_cpu_at(krnl.thrd_mp, krnl.cpu_arr, cpu_id);
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr);
    }
    mmap_2m_map_leaf_range(krnl, va_range, thrd_ptr, prc_ptr, ctn_ptr, cpu_id, pagetable_ptr, Ghost(phase), Ghost(flushed), Ghost(t4k), Tracked(&mut *lctx), Tracked(&mut *steps),
        Tracked(&thread_lock_perm), Tracked(&pagetable_lock_perm), Tracked(&window_perms));
    proof {
        mmap_2m_trace_range_steps(&*steps, entered, cpu_id, *va_range, enter_phase);
    }
    mmap_2m_unlock_range_and_finish(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, range, va_range, thrd_ptr, prc_ptr, pagetable_ptr, Ghost(enter_phase), Ghost(flushed),
        Tracked(thread_lock_perm), Tracked(pagetable_lock_perm), Tracked(cpu_lock_perm), Tracked(window_perms));
}
} // verus!
