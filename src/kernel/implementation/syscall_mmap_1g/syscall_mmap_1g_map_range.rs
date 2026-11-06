use vstd::prelude::*;
use crate::*;
#[cfg(feature = "split-crates")]
use veriflat_map_4k::map_4k::mmap_1g_install_directory::install_one_mmap_1g_directory_page;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::map_4k::mmap_1g_install_directory::install_one_mmap_1g_directory_page;
use super::syscall_mmap_1g_map_one_leaf::mmap_1g_map_one_leaf;
#[cfg(verus_keep_ghost)]
use super::syscall_mmap_1g_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_mmap_1g_map_trace::{mmap_1g_range_steps_from_directory, mmap_1g_range_steps_from_leaf};

verus! {
/// Map every page of `range`, whose 1G slots no 1G leaf maps and whose L3 entries link no L2 page, under the big write lock of `pagetable`, in order: install the L3 directory page under a missing root entry as one directory step, then publish the page's present, writable, executable 1G
/// leaf as one leaf step. Only the range's 1G leaves and the installed root entries change in the table.
pub(super) fn mmap_1g_map_range(
    krnl: &mut KernelK, range: &VaRange1G, pagetable: RwLockPageTableRoot, thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr, cpu_id: CpuId,
    Ghost(cr3): Ghost<PageTableRoot>, Ghost(pcid): Ghost<Pcid>, Ghost(hidden): Ghost<bool>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    thread_perm: Tracked<&LockPerm>, pagetable_perm: Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).page_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(steps).snapshot_k() == *old(krnl),
        index_valid(NUM_CPUS, cpu_id),
        old(lctx).cpu_id() == cpu_id,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (cr3, pcid),
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        page_ptr_valid(cr3),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable,
        !old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_1g >= range.len,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_4k >= range.len,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap1g { range: *range, mapped: 0, directory: false, hidden, flushed: hidden }),
        old(krnl).prc_mp.dom().contains(prc_ptr),
        !old(krnl).prc_mp.spec_index(prc_ptr).view().zombie,
        !(old(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is TablesEmptied),
        old(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().pcid == pcid,
        old(krnl).ctn_mp.dom().contains(ctn_ptr),
        old(krnl).pt_mp.dom().contains(pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr == prc_ptr,
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == KERNEL_MEM_END_L4INDEX,
        old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).leaves_present(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.hidden_l1_tables_in_locked_windows(),
        forall|l4i: L4Index| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().spec_held_l4(l4i)]
            old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= l4i && pei_valid(l4i) && old(krnl).pt_mp.spec_index(pagetable).view().spec_held_l4(l4i) is Some
            ==> old(krnl).pt_mp.spec_index(pagetable).view().spec_resolve_mapping_l4(l4i) is Some,
        forall|l4i: L4Index, l3i: L3Index| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().spec_held_l3(l4i, l3i)]
            old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && old(krnl).pt_mp.spec_index(pagetable).view().spec_held_l3(l4i, l3i) is Some
            ==> old(krnl).pt_mp.spec_index(pagetable).view().spec_resolve_mapping_l3(l4i, l3i) is Some,
        range.wf(),
        range.len > 0,
        forall|j: int| #![trigger range.view()[j]] 0 <= j < range.len ==> {
            &&& !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g().dom().contains(range.view()[j])
            &&& old(krnl).pt_mp.spec_index(pagetable).view().spec_held_l3(spec_v2l4index(range.view()[j]), spec_v2l3index(range.view()[j])) is None
        },
    ensures
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() + range.len <= final(steps).view().len() <= old(steps).view().len() + 2 * range.len,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==> mmap_1g_range_step(final(steps).view()[j], cpu_id),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        held_locks_order_below(final(krnl), final(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        final(krnl).cpu_op.view().view()[cpu_id as int] == old(krnl).cpu_op.view().view()[cpu_id as int],
        final(krnl).thrd_mp.dom().contains(thrd_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread {
            quota_1g: final(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_1g, quota_4k: final(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_4k,
            temp_alloc_cache_4k: final(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_4k, syscall_progress: final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress,
            ..old(krnl).thrd_mp.spec_index(thrd_ptr).view()
        }),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_1g == old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_1g - range.len,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_4k - range.len <= final(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_4k <= old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_4k,
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap1g { range: *range, mapped: range.len, directory: false, hidden, flushed: hidden }),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        final(krnl).prc_mp.dom().contains(prc_ptr),
        !final(krnl).prc_mp.spec_index(prc_ptr).view().zombie,
        !(final(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is TablesEmptied),
        final(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().pcid == pcid,
        final(krnl).ctn_mp.dom().contains(ctn_ptr),
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        final(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        final(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        final(krnl).pt_mp.spec_index(pagetable).view().proc_ptr == prc_ptr,
        final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == KERNEL_MEM_END_L4INDEX,
        final(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower,
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).leaves_present(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.hidden_l1_tables_in_locked_windows(),
        forall|l4i: L4Index| #![trigger final(krnl).pt_mp.spec_index(pagetable).view().spec_held_l4(l4i)]
            final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= l4i && pei_valid(l4i) && final(krnl).pt_mp.spec_index(pagetable).view().spec_held_l4(l4i) is Some
            ==> final(krnl).pt_mp.spec_index(pagetable).view().spec_resolve_mapping_l4(l4i) is Some,
        forall|l4i: L4Index, l3i: L3Index| #![trigger final(krnl).pt_mp.spec_index(pagetable).view().spec_held_l3(l4i, l3i)]
            final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && final(krnl).pt_mp.spec_index(pagetable).view().spec_held_l3(l4i, l3i) is Some
            ==> final(krnl).pt_mp.spec_index(pagetable).view().spec_resolve_mapping_l3(l4i, l3i) is Some,
        forall|j: int| #![trigger range.view()[j]] 0 <= j < range.len ==> {
            let post = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable);
            &&& post.mapping_1g().dom().contains(range.view()[j])
            &&& post.mapping_1g().spec_index(range.view()[j]).present
            &&& post.mapping_1g().spec_index(range.view()[j]).write
            &&& !post.mapping_1g().spec_index(range.view()[j]).execute_disable
        },
{
    let ghost entry = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
    let ghost q1g = krnl.thrd_mp.spec_index(thrd_ptr).view().quota_1g;
    let ghost q4k = krnl.thrd_mp.spec_index(thrd_ptr).view().quota_4k;
    let ghost mut dirs: int = 0;
    let mut i: usize = 0;
    while i < range.len
        invariant
            entry == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable),
            q1g == old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_1g,
            q4k == old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_4k,
            q1g >= range.len,
            q4k >= range.len,
            old(krnl).thrd_mp.dom().contains(thrd_ptr),
            index_valid(NUM_CPUS, cpu_id),
            old(lctx).cpu_id() == cpu_id,
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
            thread_perm.view().state() is WriteLock,
            thread_perm.view().thread_id() == old(lctx).thread_id(),
            thread_perm.view().lock_id() == krnl.thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
            pagetable_perm.view().state() is WriteLock,
            pagetable_perm.view().thread_id() == old(lctx).thread_id(),
            pagetable_perm.view().lock_id() == krnl.pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
            old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
            !old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
            !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
            !old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
            range.wf(),
            i <= range.len,
            0 <= dirs <= i,
            steps.snapshot_k() == *krnl,
            steps.view().len() == old(steps).view().len() + i + dirs,
            forall|j: int| #![trigger steps.view()[j]] 0 <= j < old(steps).view().len() ==> steps.view()[j] == old(steps).view()[j],
            forall|j: int| #![trigger steps.view()[j]] old(steps).view().len() <= j < steps.view().len() ==> mmap_1g_range_step(steps.view()[j], cpu_id),
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.kernel_view_locking_state() is Acquire,
            held_locks_order_below(krnl, lctx, ALLOCATOR_CACHE_4K_MAJOR),
            krnl.cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
            krnl.cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
            krnl.cpu_op.view().view()[cpu_id as int] == old(krnl).cpu_op.view().view()[cpu_id as int],
            krnl.thrd_mp.dom().contains(thrd_ptr),
            krnl.thrd_mp.spec_index(thrd_ptr).view() == (Thread {
                quota_1g: krnl.thrd_mp.spec_index(thrd_ptr).view().quota_1g, quota_4k: krnl.thrd_mp.spec_index(thrd_ptr).view().quota_4k,
                temp_alloc_cache_4k: krnl.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_4k, syscall_progress: krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress,
                ..old(krnl).thrd_mp.spec_index(thrd_ptr).view()
            }),
            krnl.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
            krnl.thrd_mp.spec_index(thrd_ptr).view().quota_1g + i == q1g,
            krnl.thrd_mp.spec_index(thrd_ptr).view().quota_4k + dirs == q4k,
            krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap1g { range: *range, mapped: i, directory: false, hidden, flushed: hidden }),
            krnl.thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
            krnl.thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
            !krnl.thrd_mp.spec_index(thrd_ptr).being_killed(),
            krnl.ctn_mp.dom().contains(ctn_ptr),
            krnl.pt_mp.dom().contains(pagetable),
            krnl.pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
            krnl.pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
            krnl.pt_mp.spec_index(pagetable).view().cr3 == cr3,
            krnl.pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
            krnl.pt_mp.spec_index(pagetable).view().proc_ptr == prc_ptr,
            krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end == KERNEL_MEM_END_L4INDEX,
            krnl.pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
            whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower == entry.lower,
            entry.lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
            entry.lower.hidden_l1_tables_in_locked_windows(),
            entry.leaves_present(),
            whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).leaves_present(),
            forall|l4i: L4Index| #![trigger krnl.pt_mp.spec_index(pagetable).view().spec_held_l4(l4i)]
                krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end <= l4i && pei_valid(l4i) && krnl.pt_mp.spec_index(pagetable).view().spec_held_l4(l4i) is Some
                ==> krnl.pt_mp.spec_index(pagetable).view().spec_resolve_mapping_l4(l4i) is Some,
            forall|l4i: L4Index, l3i: L3Index| #![trigger krnl.pt_mp.spec_index(pagetable).view().spec_held_l3(l4i, l3i)]
                krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && krnl.pt_mp.spec_index(pagetable).view().spec_held_l3(l4i, l3i) is Some
                ==> krnl.pt_mp.spec_index(pagetable).view().spec_resolve_mapping_l3(l4i, l3i) is Some,
            forall|l4i: L4Index, l3i: L3Index| #![trigger krnl.pt_mp.spec_index(pagetable).view().spec_held_l3(l4i, l3i)]
                KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i)
                ==> krnl.pt_mp.spec_index(pagetable).view().spec_held_l3(l4i, l3i) == old(krnl).pt_mp.spec_index(pagetable).view().spec_held_l3(l4i, l3i),
            forall|j: int| #![trigger range.view()[j]] 0 <= j < range.len
                ==> old(krnl).pt_mp.spec_index(pagetable).view().spec_held_l3(spec_v2l4index(range.view()[j]), spec_v2l3index(range.view()[j])) is None,
            forall|j: int| #![trigger range.view()[j]] i <= j < range.len ==> !whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_1g().dom().contains(range.view()[j]),
            forall|j: int| #![trigger range.view()[j]] 0 <= j < i ==> {
                let cur = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
                &&& cur.mapping_1g().dom().contains(range.view()[j])
                &&& cur.mapping_1g().spec_index(range.view()[j]).present
                &&& cur.mapping_1g().spec_index(range.view()[j]).write
                &&& !cur.mapping_1g().spec_index(range.view()[j]).execute_disable
            },
        decreases range.len - i,
    {
        let va = range.index(i);
        let l4i = v2l4index(va);
        proof {
            spec_va_1g_valid_index_roundtrip(va); pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable);
            container_thread_wf_thread_at(krnl.ctn_mp, krnl.thrd_mp, thrd_ptr);
        }
        let l4_entry = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), pagetable_perm).get_entry_l4(l4i);
        if l4_entry.is_none() {
            proof { container_perms_wf_at(krnl.ctn_mp, ctn_ptr); }
            let alloc_ptr_4k = krnl.ctn_mp.borrow_rodata(ctn_ptr).borrow().allocator_ptr_4k;
            proof {
                container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, ctn_ptr);
                krnl.thrd_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thrd_ptr);
                krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
                process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr);
                process_perms_wf_at(krnl.prc_mp, prc_ptr); process_emptied_threads_wf_at(krnl.prc_mp, krnl.thrd_mp, prc_ptr, thrd_ptr);
            }
            let ghost before = steps.view();
            install_one_mmap_1g_directory_page(krnl, alloc_ptr_4k, thrd_ptr, prc_ptr, ctn_ptr, cpu_id, pagetable, l4i, Tracked(&mut *lctx), Tracked(&mut *steps), thread_perm,
                pagetable_perm);
            proof {
                mmap_1g_range_steps_from_directory(&*steps, before, old(steps).view().len() as int, cpu_id);
                dirs = dirs + 1;
                krnl.thrd_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thrd_ptr);
                krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
            }
        }
        let ghost directory = l4_entry is None;
        let ghost before = steps.view();
        mmap_1g_map_one_leaf(krnl, thrd_ptr, prc_ptr, ctn_ptr, cpu_id, pagetable, va, Ghost(*range), Ghost(i), Ghost(directory), Ghost(hidden), Ghost(hidden), Tracked(&mut *lctx),
            Tracked(&mut *steps), thread_perm, pagetable_perm);
        proof {
            mmap_1g_range_steps_from_leaf(&*steps, before, old(steps).view().len() as int, cpu_id);
            container_thread_wf_thread_at(krnl.ctn_mp, krnl.thrd_mp, thrd_ptr);
        }
        i = i + 1;
    }
    proof {
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr);
        process_perms_wf_at(krnl.prc_mp, prc_ptr); process_emptied_threads_wf_at(krnl.prc_mp, krnl.thrd_mp, prc_ptr, thrd_ptr);
    }
}
} // verus!
