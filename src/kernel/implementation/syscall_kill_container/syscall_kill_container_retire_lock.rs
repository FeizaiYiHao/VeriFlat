use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_retire_spec::*;
use super::super::syscall_kill_process::syscall_kill_process_retire_pages_lock::{kill_retire_sort_pages, wlock_kill_retire_pages};
use super::syscall_kill_container_lock_pairs::{kill_container_wlock_pool_pairs, kill_container_wlock_quota_pairs};
#[cfg(feature = "split-crates")]
use veriflat_kernel_core::kernel::implementation::lock_allocated_2m_page_tails::wlock_allocated_2m_page_tails;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::lock_allocated_2m_page_tails::wlock_allocated_2m_page_tails;

verus! {
/// Write-hold the offline request cell of the marked container `container_ptr` on every cpu in cpu order, then its PCID
/// allocator, for the killer on this cpu running `thread_ptr`; return the PCID allocator's permission.
pub(crate) fn kill_container_retire_lock_flags_pcid(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    Tracked(flag_perms): Tracked<&mut Map<CpuId, LockPerm>>,
) -> (ret: Tracked<LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        ({
            let cpu = old(krnl).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view();
            &&& index_valid(NUM_CPUS, old(lctx).cpu_id())
            &&& old(lctx).cpu_lock_map().dom() =~= set![old(lctx).cpu_id()]
            &&& cpu.state is Running
        }),
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state is RUNNING,
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        forall|s: RwLockCpuSetPtr| #![trigger old(lctx).cpu_set_lock_map().dom().contains(s)] old(lctx).cpu_set_lock_map().dom().contains(s) ==> old(krnl).cpu_set_mp.spec_index(s).being_killed(),
        forall|x: (RwLockCpuOfflineFlagsPtr, CpuId)| #![trigger old(lctx).cpu_offline_flag_lock_map().dom().contains(x)]
            old(lctx).cpu_offline_flag_lock_map().dom().contains(x) ==> x.0 == cpu_offline_flags_ptr(container_ptr),
        old(flag_perms).dom().is_empty(),
        ({
            let cpu = old(krnl).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view();
            &&& cpu.container_depth < old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().depth
            &&& forall|p: RwLockProcessPtr| #![trigger old(lctx).process_lock_map().dom().contains(p)] old(lctx).process_lock_map().dom().contains(p) && cpu.current_process != Some(p) ==> old(krnl).prc_mp.spec_index(p).being_killed()
            &&& forall|t: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(t)] old(lctx).thread_lock_map().dom().contains(t) && cpu.current_thread != Some(t) ==> old(krnl).thr_mp.spec_index(t).being_killed()
            &&& forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) && c != cpu.owning_container ==> old(krnl).ctn_mp.spec_index(c).being_killed()
        }),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        *final(krnl) == (KernelK { cpu_offline_mp: final(krnl).cpu_offline_mp, pcid_allc_mp: final(krnl).pcid_allc_mp, ..*old(krnl) }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        ({
            let flags_ptr = cpu_offline_flags_ptr(container_ptr);
            let pcid_ptr = old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator;
            &&& final(krnl).cpu_offline_mp.dom() == old(krnl).cpu_offline_mp.dom()
            &&& final(krnl).pcid_allc_mp.dom() == old(krnl).pcid_allc_mp.dom()
            &&& forall|x: (RwLockCpuOfflineFlagsPtr, CpuId)| #![trigger final(lctx).cpu_offline_flag_lock_map().dom().contains(x)]
                final(lctx).cpu_offline_flag_lock_map().dom().contains(x) ==> x.0 == flags_ptr && index_valid(NUM_CPUS, x.1)
            &&& forall|i: CpuId| #![trigger final(flag_perms).dom().contains(i)] #![trigger final(flag_perms)[i]] index_valid(NUM_CPUS, i) ==> {
                &&& final(flag_perms).dom().contains(i)
                &&& final(flag_perms)[i].state() is WriteLock
                &&& final(flag_perms)[i].thread_id() == final(lctx).thread_id()
                &&& final(flag_perms)[i].lock_id() == final(krnl).cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(i).view().locking_thread()->Write_lock_id
                &&& typed_lock_map_contains_mode(final(lctx).cpu_offline_flag_lock_map(), (flags_ptr, i), TypedLockMode::Write)
            }
            &&& final(lctx).pcid_allocator_lock_map().dom() == set![pcid_ptr]
            &&& typed_lock_map_contains_mode(final(lctx).pcid_allocator_lock_map(), pcid_ptr, TypedLockMode::Write)
            &&& ret.view().state() is WriteLock && ret.view().thread_id() == final(lctx).thread_id()
            &&& ret.view().lock_id() == final(krnl).pcid_allc_mp.spec_index(pcid_ptr).locking_thread()->Write_lock_id
        }),
{
    proof {
        container_perms_wf_map(krnl.ctn_mp); container_perms_wf_at(krnl.ctn_mp, container_ptr); container_pages_backward_at(krnl.pg_arr, krnl.ctn_mp, container_ptr);
        container_cpu_offline_flags_wf_container_at(krnl.ctn_mp, krnl.cpu_offline_mp, container_ptr); container_pcid_allocator_wf_container_at(krnl.ctn_mp, krnl.pcid_allc_mp, container_ptr);
        cpu_offline_flags_wf_map(krnl.cpu_offline_mp, krnl.cpu_arr); cpu_offline_flags_wf_at(krnl.cpu_offline_mp, krnl.cpu_arr, cpu_offline_flags_ptr(container_ptr));
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
        assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
    }
    let flags_ptr = container_ptr + 4096;
    let pcid_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().pcid_allocator;
    let mut c: usize = 0;
    while c < NUM_CPUS
        invariant
            old(krnl).inv(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(lctx).kernel_view_locking_state() is Acquire,
            ({
                let cpu = old(krnl).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view();
                &&& index_valid(NUM_CPUS, old(lctx).cpu_id())
                &&& old(lctx).cpu_lock_map().dom() =~= set![old(lctx).cpu_id()]
                &&& cpu.state is Running
            }),
            old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
            old(krnl).thr_mp.dom().contains(thread_ptr),
            old(krnl).thr_mp.spec_index(thread_ptr).view().state is RUNNING,
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(lctx).endpoint_lock_map().dom().is_empty(),
            old(lctx).pagetable_lock_map().dom().is_empty(),
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).iommu_root_table_lock_map().dom().is_empty(),
            old(krnl).ctn_mp.dom().contains(container_ptr),
            typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
            old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
            forall|s: RwLockCpuSetPtr| #![trigger old(lctx).cpu_set_lock_map().dom().contains(s)] old(lctx).cpu_set_lock_map().dom().contains(s) ==> old(krnl).cpu_set_mp.spec_index(s).being_killed(),
            forall|x: (RwLockCpuOfflineFlagsPtr, CpuId)| #![trigger old(lctx).cpu_offline_flag_lock_map().dom().contains(x)]
                old(lctx).cpu_offline_flag_lock_map().dom().contains(x) ==> x.0 == cpu_offline_flags_ptr(container_ptr),
                    ({
                let cpu = old(krnl).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view();
                &&& cpu.container_depth < old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().depth
                &&& forall|p: RwLockProcessPtr| #![trigger old(lctx).process_lock_map().dom().contains(p)] old(lctx).process_lock_map().dom().contains(p) && cpu.current_process != Some(p) ==> old(krnl).prc_mp.spec_index(p).being_killed()
                &&& forall|t: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(t)] old(lctx).thread_lock_map().dom().contains(t) && cpu.current_thread != Some(t) ==> old(krnl).thr_mp.spec_index(t).being_killed()
                &&& forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) && c != cpu.owning_container ==> old(krnl).ctn_mp.spec_index(c).being_killed()
            }),
            old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).pcid_allocator_lock_map().dom().is_empty(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            0 <= c <= NUM_CPUS,
            flags_ptr == cpu_offline_flags_ptr(container_ptr),
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.kernel_view_locking_state() is Acquire,
            *krnl == (KernelK { cpu_offline_mp: krnl.cpu_offline_mp, ..*old(krnl) }),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), krnl),
            kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), krnl),
            krnl.cpu_offline_mp.dom() == old(krnl).cpu_offline_mp.dom(),
            krnl.cpu_offline_mp.dom().contains(flags_ptr),
            krnl.cpu_offline_mp.spec_index(flags_ptr).inv(),
            krnl.cpu_offline_mp.spec_index(flags_ptr).owning_container == old(krnl).cpu_offline_mp.spec_index(flags_ptr).owning_container,
            krnl.cpu_offline_mp.spec_index(flags_ptr).container_depth == old(krnl).cpu_offline_mp.spec_index(flags_ptr).container_depth,
            old(krnl).cpu_offline_mp.spec_index(flags_ptr).container_depth.view() == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().depth,
            lctx.page_lock_map() == old(lctx).page_lock_map(),
            lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
            lctx.pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            lctx.process_lock_map() == old(lctx).process_lock_map(),
            lctx.thread_lock_map() == old(lctx).thread_lock_map(),
            lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            lctx.scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            lctx.pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            lctx.pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            lctx.pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
            lctx.iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            lctx.iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
            lctx.allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
            lctx.allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            lctx.allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            forall|x: (RwLockCpuOfflineFlagsPtr, CpuId)| #![trigger lctx.cpu_offline_flag_lock_map().dom().contains(x)] lctx.cpu_offline_flag_lock_map().dom().contains(x) ==> x.0 == flags_ptr && x.1 < c,
            forall|i: CpuId| #![trigger flag_perms.dom().contains(i)] #![trigger flag_perms[i]] #![trigger lctx.cpu_offline_flag_lock_map().dom().contains((flags_ptr, i))] i < c ==> {
                &&& flag_perms.dom().contains(i)
                &&& flag_perms[i].state() is WriteLock
                &&& flag_perms[i].thread_id() == lctx.thread_id()
                &&& flag_perms[i].lock_id() == krnl.cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(i).view().locking_thread()->Write_lock_id
                &&& typed_lock_map_contains_mode(lctx.cpu_offline_flag_lock_map(), (flags_ptr, i), TypedLockMode::Write)
            },
        decreases NUM_CPUS - c,
    {
        proof {
            assert(typed_lock_map_2d_ids_lt(lctx.cpu_offline_flag_lock_map(), krnl.cpu_offline_mp.spec_index(flags_ptr).flags.lock_id_by_index(c))) by { reveal(UnLockedMap::typed_flag_lock_map_aligned); };
        }
        let Tracked(perm) = krnl.wlock_cpu_offline_flag(flags_ptr, c, Tracked(&mut *lctx));
        proof {
            flag_perms.tracked_insert(c, perm);
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        }
        c = c + 1;
    }
    let ret = krnl.wlock_pcid_allocator(pcid_ptr, Tracked(&mut *lctx));
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        assert(lctx.pcid_allocator_lock_map().dom() =~= set![pcid_ptr]);
    }
    ret
}

/// Write-hold, in index order, the five 4K object pages of the marked container `container_ptr` (its scheduler, cpu set,
/// and allocators) and its two 2M heads (the container and its PCID allocator); return their permissions.
pub(crate) fn kill_container_retire_lock_object_pages(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
) -> (ret: Tracked<Map<PageIndex, LockPerm>>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        ({
            let cpu = old(krnl).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view();
            &&& index_valid(NUM_CPUS, old(lctx).cpu_id())
            &&& old(lctx).cpu_lock_map().dom() =~= set![old(lctx).cpu_id()]
            &&& cpu.state is Running
        }),
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state is RUNNING,
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        forall|s: RwLockCpuSetPtr| #![trigger old(lctx).cpu_set_lock_map().dom().contains(s)] old(lctx).cpu_set_lock_map().dom().contains(s) ==> old(krnl).cpu_set_mp.spec_index(s).being_killed(),
        forall|x: (RwLockCpuOfflineFlagsPtr, CpuId)| #![trigger old(lctx).cpu_offline_flag_lock_map().dom().contains(x)]
            old(lctx).cpu_offline_flag_lock_map().dom().contains(x) ==> x.0 == cpu_offline_flags_ptr(container_ptr),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, ..*old(krnl) }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        forall|i: PageIndex| #![trigger final(krnl).pg_arr.spec_index(i).view()] index_valid(NUM_PAGES, i) ==> {
            &&& final(krnl).pg_arr.spec_index(i).view().view() == old(krnl).pg_arr.spec_index(i).view().view()
            &&& final(krnl).pg_arr.spec_index(i).view().being_killed() == old(krnl).pg_arr.spec_index(i).view().being_killed()
        },
        ({
            let ro = old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view();
            let heads = kill_container_retire_heads(container_ptr, ro);
            &&& ret.view().dom() == kill_container_retire_pages_4k(ro).to_set().insert(heads[0]).insert(heads[1])
            &&& final(lctx).page_lock_map().dom() == ret.view().dom()
        }),
        forall|p: PageIndex| #![trigger ret.view().dom().contains(p)] ret.view().dom().contains(p) ==> {
            &&& index_valid(NUM_PAGES, p)
            &&& typed_lock_map_contains_mode(final(lctx).page_lock_map(), p, TypedLockMode::Write)
            &&& ret.view()[p].state() is WriteLock && ret.view()[p].thread_id() == final(lctx).thread_id()
            &&& ret.view()[p].lock_id() == final(krnl).pg_arr.spec_index(p).view().locking_thread()->Write_lock_id
            &&& final(lctx).page_lock_map().index(p).lock_id.major <= ALLOCATED_PAGE_MAJOR
            &&& final(krnl).pg_arr.lock_id_by_index(p).major <= ALLOCATED_PAGE_MAJOR
        },
{
    let ghost ro = krnl.ctn_mp.spec_index(container_ptr).view_rodata().view();
    proof {
        container_perms_wf_map(krnl.ctn_mp); container_perms_wf_at(krnl.ctn_mp, container_ptr); container_pages_backward_at(krnl.pg_arr, krnl.ctn_mp, container_ptr);
        container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr);
        container_scheduler_wf_at(krnl.ctn_mp, krnl.sched_mp, container_ptr); container_cpu_set_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, container_ptr);
        container_pcid_allocator_wf_container_at(krnl.ctn_mp, krnl.pcid_allc_mp, container_ptr); container_cpu_offline_flags_wf_container_at(krnl.ctn_mp, krnl.cpu_offline_mp, container_ptr);
        page_array_wf_map(krnl.pg_arr); page_ptr_roundtrip();
        scheduler_pages_wf_at(krnl.sched_mp, krnl.pg_arr, ro.scheduler); cpu_set_pages_wf_at(krnl.cpu_set_mp, krnl.pg_arr, ro.cpu_set);
        allocator_4k_pages_wf_at(krnl.pg_arr, krnl.allc_4k_mp, ro.allocator_ptr_4k); allocator_2m_pages_wf_at(krnl.pg_arr, krnl.allc_2m_mp, ro.allocator_ptr_2m);
        allocator_1g_pages_wf_at(krnl.pg_arr, krnl.allc_1g_mp, ro.allocator_ptr_1g); pcid_allocator_pages_wf_at(krnl.pg_arr, krnl.pcid_allc_mp, ro.pcid_allocator);
        hugepage_2m_wf_head_at(krnl.pg_arr, page_ptr2page_index(ro.pcid_allocator)); hugepage_2m_wf_head_at(krnl.pg_arr, page_ptr2page_index(container_ptr));
    }
    let scheduler_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().scheduler;
    let cpu_set_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().cpu_set;
    let a4 = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().allocator_ptr_4k;
    let a2 = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().allocator_ptr_2m;
    let a1 = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().allocator_ptr_1g;
    let pcid_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().pcid_allocator;
    let mut pages = ArrayVec::<PageIndex, 7>::new();
    pages.push(page_ptr2page_index(scheduler_ptr));
    pages.push(page_ptr2page_index(cpu_set_ptr));
    pages.push(page_ptr2page_index(a4));
    pages.push(page_ptr2page_index(a2));
    pages.push(page_ptr2page_index(a1));
    pages.push(page_ptr2page_index(container_ptr));
    pages.push(page_ptr2page_index(pcid_ptr));
    proof {
        let heads = kill_container_retire_heads(container_ptr, ro);
        assert(pages.view() =~= kill_container_retire_pages_4k(ro).push(heads[0]).push(heads[1]));
        kill_container_retire_pages_4k(ro).lemma_push_to_set_commute(heads[0]); kill_container_retire_pages_4k(ro).push(heads[0]).lemma_push_to_set_commute(heads[1]);
        assert(pages.view().no_duplicates());
        assert(lctx.page_lock_map().dom() =~= Map::<PageIndex, LockPerm>::empty().dom());
        krnl.cpu_arr.typed_lock_map_aligned_lock_id_at(lctx.cpu_lock_map(), lctx.thread_id(), lctx.cpu_id());
    }
    let sorted = kill_retire_sort_pages(&pages);
    let ret = wlock_kill_retire_pages(krnl, &sorted, Ghost(ALLOCATED_PAGE_MAJOR), Tracked(&mut *lctx), Tracked(Map::<PageIndex, LockPerm>::tracked_empty()));
    proof { assert(lctx.page_lock_map().dom() =~= sorted.view().to_set()); }
    ret
}

/// Write-hold the scheduler shard of the marked container `container_ptr` on every cpu in cpu order.
pub(crate) fn kill_container_retire_lock_shards(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    Tracked(shard_perms): Tracked<&mut Map<CpuId, LockPerm>>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        ({
            let cpu = old(krnl).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view();
            &&& index_valid(NUM_CPUS, old(lctx).cpu_id())
            &&& old(lctx).cpu_lock_map().dom() =~= set![old(lctx).cpu_id()]
            &&& cpu.state is Running
        }),
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state is RUNNING,
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        forall|p: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(p)] old(lctx).page_lock_map().dom().contains(p) ==> old(krnl).pg_arr.lock_id_by_index(p).major <= ALLOCATED_PAGE_MAJOR,
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(shard_perms).dom().is_empty(),
        old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view() == Set::<RwLockThreadPtr>::empty(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        *final(krnl) == (KernelK { sched_mp: final(krnl).sched_mp, ..*old(krnl) }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(krnl).sched_mp.dom() == old(krnl).sched_mp.dom(),
        ({
            let sched = old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler;
            &&& forall|i: CpuId| #![trigger final(krnl).sched_mp.spec_index(sched).shards.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> final(krnl).sched_mp.spec_index(sched).shards.spec_index(i).view().view() == old(krnl).sched_mp.spec_index(sched).shards.spec_index(i).view().view()
            &&& forall|i: CpuId| #![trigger final(krnl).sched_mp.spec_index(sched).shards.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> final(krnl).sched_mp.spec_index(sched).shards.spec_index(i).view().view().queue.view().len() == 0
            &&& forall|x: (RwLockSchedulerPtr, CpuId)| #![trigger final(lctx).scheduler_lock_map().dom().contains(x)]
                final(lctx).scheduler_lock_map().dom().contains(x) ==> x.0 == sched && index_valid(NUM_CPUS, x.1)
            &&& forall|i: CpuId| #![trigger final(shard_perms).dom().contains(i)] #![trigger final(shard_perms)[i]] index_valid(NUM_CPUS, i) ==> {
                &&& final(shard_perms).dom().contains(i)
                &&& final(shard_perms)[i].state() is WriteLock
                &&& final(shard_perms)[i].thread_id() == final(lctx).thread_id()
                &&& final(krnl).sched_mp.spec_index(sched).shards.spec_index(i).view().locking_thread() == (RwLockState::Write { thread_id: final(lctx).thread_id(), lock_id: final(shard_perms)[i].lock_id() })
                &&& typed_lock_map_contains_mode(final(lctx).scheduler_lock_map(), (sched, i), TypedLockMode::Write)
            }
        }),
{
    proof {
        container_perms_wf_map(krnl.ctn_mp); container_perms_wf_at(krnl.ctn_mp, container_ptr); container_scheduler_wf_at(krnl.ctn_mp, krnl.sched_mp, container_ptr);
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
        assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
    }
    let sched = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().scheduler;
    let mut c: usize = 0;
    while c < NUM_CPUS
        invariant
            old(krnl).inv(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(lctx).kernel_view_locking_state() is Acquire,
            ({
                let cpu = old(krnl).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view();
                &&& index_valid(NUM_CPUS, old(lctx).cpu_id())
                &&& old(lctx).cpu_lock_map().dom() =~= set![old(lctx).cpu_id()]
                &&& cpu.state is Running
            }),
            old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
            old(krnl).thr_mp.dom().contains(thread_ptr),
            old(krnl).thr_mp.spec_index(thread_ptr).view().state is RUNNING,
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(lctx).endpoint_lock_map().dom().is_empty(),
            old(lctx).pagetable_lock_map().dom().is_empty(),
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).iommu_root_table_lock_map().dom().is_empty(),
            old(krnl).ctn_mp.dom().contains(container_ptr),
            forall|p: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(p)] old(lctx).page_lock_map().dom().contains(p) ==> old(krnl).pg_arr.lock_id_by_index(p).major <= ALLOCATED_PAGE_MAJOR,
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            0 <= c <= NUM_CPUS,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.kernel_view_locking_state() is Acquire,
            *krnl == (KernelK { sched_mp: krnl.sched_mp, ..*old(krnl) }),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), krnl),
            kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), krnl),
            krnl.sched_mp.dom() == old(krnl).sched_mp.dom(),
            krnl.sched_mp.dom().contains(sched),
            old(krnl).ctn_mp.dom().contains(container_ptr),
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == sched,
            forall|i: CpuId| #![trigger krnl.sched_mp.spec_index(sched).shards.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> krnl.sched_mp.spec_index(sched).shards.spec_index(i).view().view() == old(krnl).sched_mp.spec_index(sched).shards.spec_index(i).view().view(),
            old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view() == Set::<RwLockThreadPtr>::empty(),
            forall|i: CpuId| #![trigger old(krnl).sched_mp.spec_index(sched).shards.spec_index(i)]
                index_valid(NUM_CPUS, i) && i < c ==> old(krnl).sched_mp.spec_index(sched).shards.spec_index(i).view().view().queue.view().len() == 0,
            lctx.page_lock_map() == old(lctx).page_lock_map(),
            lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
            lctx.pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            lctx.cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            lctx.process_lock_map() == old(lctx).process_lock_map(),
            lctx.thread_lock_map() == old(lctx).thread_lock_map(),
            lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            lctx.pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            lctx.pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            lctx.pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
            lctx.iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            lctx.iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
            lctx.allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
            lctx.allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            lctx.allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            lctx.holds_no_allocator_locks(PageSize::SZ4k),
            lctx.holds_no_allocator_locks(PageSize::SZ2m),
            lctx.holds_no_allocator_locks(PageSize::SZ1g),
            forall|p: PageIndex| #![trigger lctx.page_lock_map().dom().contains(p)] lctx.page_lock_map().dom().contains(p) ==> krnl.pg_arr.lock_id_by_index(p).major <= ALLOCATED_PAGE_MAJOR,
            forall|x: (RwLockSchedulerPtr, CpuId)| #![trigger lctx.scheduler_lock_map().dom().contains(x)] lctx.scheduler_lock_map().dom().contains(x) ==> x.0 == sched && x.1 < c,
            forall|i: CpuId| #![trigger shard_perms.dom().contains(i)] #![trigger shard_perms[i]] #![trigger lctx.scheduler_lock_map().dom().contains((sched, i))] i < c ==> {
                &&& shard_perms.dom().contains(i)
                &&& shard_perms[i].state() is WriteLock
                &&& shard_perms[i].thread_id() == lctx.thread_id()
                &&& krnl.sched_mp.spec_index(sched).shards.spec_index(i).view().locking_thread() == (RwLockState::Write { thread_id: lctx.thread_id(), lock_id: shard_perms[i].lock_id() })
                &&& typed_lock_map_contains_mode(lctx.scheduler_lock_map(), (sched, i), TypedLockMode::Write)
            },
        decreases NUM_CPUS - c,
    {
        let Tracked(perm) = krnl.wlock_scheduler_shard(sched, c, Tracked(&mut *lctx));
        proof {
            shard_perms.tracked_insert(c, perm);
            container_without_threads_shard_empty_at(*old(krnl), container_ptr, c);
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        }
        c = c + 1;
    }
}

/// Write-hold the 4K, then the 2M, then the 1G allocator caches of the marked container `container_ptr` on every cpu in
/// cpu order.
pub(crate) fn kill_container_retire_lock_caches(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    Tracked(caches_4k): Tracked<&mut Map<CpuId, LockPerm>>, Tracked(caches_2m): Tracked<&mut Map<CpuId, LockPerm>>, Tracked(caches_1g): Tracked<&mut Map<CpuId, LockPerm>>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        ({
            let cpu = old(krnl).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view();
            &&& index_valid(NUM_CPUS, old(lctx).cpu_id())
            &&& old(lctx).cpu_lock_map().dom() =~= set![old(lctx).cpu_id()]
            &&& cpu.state is Running
        }),
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state is RUNNING,
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        forall|p: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(p)] old(lctx).page_lock_map().dom().contains(p) ==> old(krnl).pg_arr.lock_id_by_index(p).major <= ALLOCATED_PAGE_MAJOR,
        typed_lock_map_majors_lt(old(lctx).page_lock_map(), ALLOCATOR_CACHE_4K_MAJOR),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(caches_4k).dom().is_empty(),
        old(caches_2m).dom().is_empty(),
        old(caches_1g).dom().is_empty(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        *final(krnl) == (KernelK { allc_4k_mp: final(krnl).allc_4k_mp, allc_2m_mp: final(krnl).allc_2m_mp, allc_1g_mp: final(krnl).allc_1g_mp, ..*old(krnl) }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(krnl).allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
        final(krnl).allc_2m_mp.dom() == old(krnl).allc_2m_mp.dom(),
        final(krnl).allc_1g_mp.dom() == old(krnl).allc_1g_mp.dom(),
        forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_4k_mp.spec_index(a)] final(krnl).allc_4k_mp.dom().contains(a) ==> {
            &&& final(krnl).allc_4k_mp.spec_index(a).quota == old(krnl).allc_4k_mp.spec_index(a).quota
            &&& final(krnl).allc_4k_mp.spec_index(a).global_pool == old(krnl).allc_4k_mp.spec_index(a).global_pool
            &&& final(krnl).allc_4k_mp.spec_index(a).owning_container == old(krnl).allc_4k_mp.spec_index(a).owning_container
        },
        forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_2m_mp.spec_index(a)] final(krnl).allc_2m_mp.dom().contains(a) ==> {
            &&& final(krnl).allc_2m_mp.spec_index(a).quota == old(krnl).allc_2m_mp.spec_index(a).quota
            &&& final(krnl).allc_2m_mp.spec_index(a).global_pool == old(krnl).allc_2m_mp.spec_index(a).global_pool
            &&& final(krnl).allc_2m_mp.spec_index(a).owning_container == old(krnl).allc_2m_mp.spec_index(a).owning_container
        },
        forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_1g_mp.spec_index(a)] final(krnl).allc_1g_mp.dom().contains(a) ==> {
            &&& final(krnl).allc_1g_mp.spec_index(a).quota == old(krnl).allc_1g_mp.spec_index(a).quota
            &&& final(krnl).allc_1g_mp.spec_index(a).global_pool == old(krnl).allc_1g_mp.spec_index(a).global_pool
            &&& final(krnl).allc_1g_mp.spec_index(a).owning_container == old(krnl).allc_1g_mp.spec_index(a).owning_container
        },
        ({
            let ro = old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view();
            let (a4, a2, a1) = (ro.allocator_ptr_4k, ro.allocator_ptr_2m, ro.allocator_ptr_1g);
            &&& forall|i: CpuId| #![trigger final(krnl).allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i)
                ==> final(krnl).allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().view() == old(krnl).allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().view()
            &&& forall|x: (RwLockPageAllocatorPtr, CpuId)| #![trigger final(lctx).allocator_cache_4k_lock_map().dom().contains(x)]
                final(lctx).allocator_cache_4k_lock_map().dom().contains(x) ==> x.0 == a4 && index_valid(NUM_CPUS, x.1)
            &&& forall|i: CpuId| #![trigger final(caches_4k).dom().contains(i)] #![trigger final(caches_4k)[i]] index_valid(NUM_CPUS, i) ==> {
                &&& final(caches_4k).dom().contains(i)
                &&& final(caches_4k)[i].state() is WriteLock
                &&& final(caches_4k)[i].thread_id() == final(lctx).thread_id()
                &&& final(krnl).allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().locking_thread() == (RwLockState::Write { thread_id: final(lctx).thread_id(), lock_id: final(caches_4k)[i].lock_id() })
                &&& typed_lock_map_contains_mode(final(lctx).allocator_cache_4k_lock_map(), (a4, i), TypedLockMode::Write)
            }
            &&& forall|i: CpuId| #![trigger final(krnl).allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i)
                ==> final(krnl).allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().view() == old(krnl).allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().view()
            &&& forall|x: (RwLockPageAllocatorPtr, CpuId)| #![trigger final(lctx).allocator_cache_2m_lock_map().dom().contains(x)]
                final(lctx).allocator_cache_2m_lock_map().dom().contains(x) ==> x.0 == a2 && index_valid(NUM_CPUS, x.1)
            &&& forall|i: CpuId| #![trigger final(caches_2m).dom().contains(i)] #![trigger final(caches_2m)[i]] index_valid(NUM_CPUS, i) ==> {
                &&& final(caches_2m).dom().contains(i)
                &&& final(caches_2m)[i].state() is WriteLock
                &&& final(caches_2m)[i].thread_id() == final(lctx).thread_id()
                &&& final(krnl).allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().locking_thread() == (RwLockState::Write { thread_id: final(lctx).thread_id(), lock_id: final(caches_2m)[i].lock_id() })
                &&& typed_lock_map_contains_mode(final(lctx).allocator_cache_2m_lock_map(), (a2, i), TypedLockMode::Write)
            }
            &&& forall|i: CpuId| #![trigger final(krnl).allc_1g_mp.spec_index(a1).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i)
                ==> final(krnl).allc_1g_mp.spec_index(a1).cpu_caches.spec_index(i).view().view() == old(krnl).allc_1g_mp.spec_index(a1).cpu_caches.spec_index(i).view().view()
            &&& forall|x: (RwLockPageAllocatorPtr, CpuId)| #![trigger final(lctx).allocator_cache_1g_lock_map().dom().contains(x)]
                final(lctx).allocator_cache_1g_lock_map().dom().contains(x) ==> x.0 == a1 && index_valid(NUM_CPUS, x.1)
            &&& forall|i: CpuId| #![trigger final(caches_1g).dom().contains(i)] #![trigger final(caches_1g)[i]] index_valid(NUM_CPUS, i) ==> {
                &&& final(caches_1g).dom().contains(i)
                &&& final(caches_1g)[i].state() is WriteLock
                &&& final(caches_1g)[i].thread_id() == final(lctx).thread_id()
                &&& final(krnl).allc_1g_mp.spec_index(a1).cpu_caches.spec_index(i).view().locking_thread() == (RwLockState::Write { thread_id: final(lctx).thread_id(), lock_id: final(caches_1g)[i].lock_id() })
                &&& typed_lock_map_contains_mode(final(lctx).allocator_cache_1g_lock_map(), (a1, i), TypedLockMode::Write)
            }
            &&& final(lctx).allocator_quota_4k_lock_map().dom().is_empty() && final(lctx).allocator_global_pool_4k_lock_map().dom().is_empty()
            &&& final(lctx).allocator_quota_2m_lock_map().dom().is_empty() && final(lctx).allocator_global_pool_2m_lock_map().dom().is_empty()
            &&& final(lctx).allocator_quota_1g_lock_map().dom().is_empty() && final(lctx).allocator_global_pool_1g_lock_map().dom().is_empty()
        }),
{
    proof {
        container_perms_wf_map(krnl.ctn_mp); container_perms_wf_at(krnl.ctn_mp, container_ptr);
        container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr);
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
        assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
    }
    let a4 = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().allocator_ptr_4k;
    let a2 = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().allocator_ptr_2m;
    let a1 = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().allocator_ptr_1g;
    let mut c: usize = 0;
    while c < NUM_CPUS
        invariant
            old(krnl).inv(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(lctx).kernel_view_locking_state() is Acquire,
            ({
                let cpu = old(krnl).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view();
                &&& index_valid(NUM_CPUS, old(lctx).cpu_id())
                &&& old(lctx).cpu_lock_map().dom() =~= set![old(lctx).cpu_id()]
                &&& cpu.state is Running
            }),
            old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
            old(krnl).thr_mp.dom().contains(thread_ptr),
            old(krnl).thr_mp.spec_index(thread_ptr).view().state is RUNNING,
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(lctx).endpoint_lock_map().dom().is_empty(),
            old(lctx).pagetable_lock_map().dom().is_empty(),
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).iommu_root_table_lock_map().dom().is_empty(),
            old(krnl).ctn_mp.dom().contains(container_ptr),
            forall|p: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(p)] old(lctx).page_lock_map().dom().contains(p) ==> old(krnl).pg_arr.lock_id_by_index(p).major <= ALLOCATED_PAGE_MAJOR,
            typed_lock_map_majors_lt(old(lctx).page_lock_map(), ALLOCATOR_CACHE_4K_MAJOR),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            0 <= c <= NUM_CPUS,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.kernel_view_locking_state() is Acquire,
            *krnl == (KernelK { allc_4k_mp: krnl.allc_4k_mp, ..*old(krnl) }),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), krnl),
            kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), krnl),
            old(krnl).ctn_mp.dom().contains(container_ptr),
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == a4,
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_2m == a2,
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_1g == a1,
            old(krnl).allc_4k_mp.dom().contains(a4) && old(krnl).allc_2m_mp.dom().contains(a2) && old(krnl).allc_1g_mp.dom().contains(a1),
            forall|p: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(p)] old(lctx).page_lock_map().dom().contains(p) ==> old(krnl).pg_arr.lock_id_by_index(p).major <= ALLOCATED_PAGE_MAJOR,
            krnl.allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
            forall|i: CpuId| #![trigger krnl.allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i)
                ==> krnl.allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().view() == old(krnl).allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().view(),
            forall|a: RwLockPageAllocatorPtr| #![trigger krnl.allc_4k_mp.spec_index(a)] krnl.allc_4k_mp.dom().contains(a) ==> {
                &&& krnl.allc_4k_mp.spec_index(a).quota == old(krnl).allc_4k_mp.spec_index(a).quota
                &&& krnl.allc_4k_mp.spec_index(a).global_pool == old(krnl).allc_4k_mp.spec_index(a).global_pool
                &&& krnl.allc_4k_mp.spec_index(a).owning_container == old(krnl).allc_4k_mp.spec_index(a).owning_container
            },
            lctx.page_lock_map() == old(lctx).page_lock_map(),
            lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
            lctx.pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            lctx.cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            lctx.process_lock_map() == old(lctx).process_lock_map(),
            lctx.thread_lock_map() == old(lctx).thread_lock_map(),
            lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            lctx.scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            lctx.pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            lctx.pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            lctx.pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
            lctx.iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            lctx.iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
            lctx.allocator_quota_4k_lock_map().dom().is_empty() && lctx.allocator_global_pool_4k_lock_map().dom().is_empty(),
            lctx.allocator_quota_2m_lock_map().dom().is_empty() && lctx.allocator_global_pool_2m_lock_map().dom().is_empty(),
            lctx.allocator_quota_1g_lock_map().dom().is_empty() && lctx.allocator_global_pool_1g_lock_map().dom().is_empty(),
            lctx.allocator_cache_2m_lock_map().dom().is_empty(),
            lctx.allocator_cache_1g_lock_map().dom().is_empty(),
            forall|x: (RwLockPageAllocatorPtr, CpuId)| #![trigger lctx.allocator_cache_4k_lock_map().dom().contains(x)] lctx.allocator_cache_4k_lock_map().dom().contains(x) ==> x.0 == a4 && x.1 < c,
            forall|i: CpuId| #![trigger caches_4k.dom().contains(i)] #![trigger caches_4k[i]] #![trigger lctx.allocator_cache_4k_lock_map().dom().contains((a4, i))] i < c ==> {
                &&& caches_4k.dom().contains(i)
                &&& caches_4k[i].state() is WriteLock
                &&& caches_4k[i].thread_id() == lctx.thread_id()
                &&& krnl.allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().locking_thread() == (RwLockState::Write { thread_id: lctx.thread_id(), lock_id: caches_4k[i].lock_id() })
                &&& typed_lock_map_contains_mode(lctx.allocator_cache_4k_lock_map(), (a4, i), TypedLockMode::Write)
            },
        decreases NUM_CPUS - c,
    {
        proof { krnl.cpu_arr.typed_lock_map_aligned_lock_id_at(lctx.cpu_lock_map(), lctx.thread_id(), lctx.cpu_id()); krnl.thr_mp.typed_lock_map_aligned_lock_id_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr); }
        let Tracked(perm) = krnl.wlock_allocator_cache_4k(a4, c, Tracked(&mut *lctx));
        proof {
            caches_4k.tracked_insert(c, perm);
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        }
        c = c + 1;
    }
    let mut c: usize = 0;
    while c < NUM_CPUS
        invariant
            old(krnl).inv(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(lctx).kernel_view_locking_state() is Acquire,
            ({
                let cpu = old(krnl).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view();
                &&& index_valid(NUM_CPUS, old(lctx).cpu_id())
                &&& old(lctx).cpu_lock_map().dom() =~= set![old(lctx).cpu_id()]
                &&& cpu.state is Running
            }),
            old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
            old(krnl).thr_mp.dom().contains(thread_ptr),
            old(krnl).thr_mp.spec_index(thread_ptr).view().state is RUNNING,
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(lctx).endpoint_lock_map().dom().is_empty(),
            old(lctx).pagetable_lock_map().dom().is_empty(),
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).iommu_root_table_lock_map().dom().is_empty(),
            old(krnl).ctn_mp.dom().contains(container_ptr),
            forall|p: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(p)] old(lctx).page_lock_map().dom().contains(p) ==> old(krnl).pg_arr.lock_id_by_index(p).major <= ALLOCATED_PAGE_MAJOR,
            typed_lock_map_majors_lt(old(lctx).page_lock_map(), ALLOCATOR_CACHE_4K_MAJOR),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            0 <= c <= NUM_CPUS,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.kernel_view_locking_state() is Acquire,
            *krnl == (KernelK { allc_4k_mp: krnl.allc_4k_mp, allc_2m_mp: krnl.allc_2m_mp, ..*old(krnl) }),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), krnl),
            kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), krnl),
            old(krnl).ctn_mp.dom().contains(container_ptr),
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == a4,
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_2m == a2,
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_1g == a1,
            old(krnl).allc_4k_mp.dom().contains(a4) && old(krnl).allc_2m_mp.dom().contains(a2) && old(krnl).allc_1g_mp.dom().contains(a1),
            forall|p: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(p)] old(lctx).page_lock_map().dom().contains(p) ==> old(krnl).pg_arr.lock_id_by_index(p).major <= ALLOCATED_PAGE_MAJOR,
            krnl.allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
            forall|i: CpuId| #![trigger krnl.allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i)
                ==> krnl.allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().view() == old(krnl).allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().view(),
            forall|a: RwLockPageAllocatorPtr| #![trigger krnl.allc_4k_mp.spec_index(a)] krnl.allc_4k_mp.dom().contains(a) ==> {
                &&& krnl.allc_4k_mp.spec_index(a).quota == old(krnl).allc_4k_mp.spec_index(a).quota
                &&& krnl.allc_4k_mp.spec_index(a).global_pool == old(krnl).allc_4k_mp.spec_index(a).global_pool
                &&& krnl.allc_4k_mp.spec_index(a).owning_container == old(krnl).allc_4k_mp.spec_index(a).owning_container
            },
            krnl.allc_2m_mp.dom() == old(krnl).allc_2m_mp.dom(),
            forall|i: CpuId| #![trigger krnl.allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i)
                ==> krnl.allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().view() == old(krnl).allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().view(),
            forall|a: RwLockPageAllocatorPtr| #![trigger krnl.allc_2m_mp.spec_index(a)] krnl.allc_2m_mp.dom().contains(a) ==> {
                &&& krnl.allc_2m_mp.spec_index(a).quota == old(krnl).allc_2m_mp.spec_index(a).quota
                &&& krnl.allc_2m_mp.spec_index(a).global_pool == old(krnl).allc_2m_mp.spec_index(a).global_pool
                &&& krnl.allc_2m_mp.spec_index(a).owning_container == old(krnl).allc_2m_mp.spec_index(a).owning_container
            },
            lctx.page_lock_map() == old(lctx).page_lock_map(),
            lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
            lctx.pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            lctx.cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            lctx.process_lock_map() == old(lctx).process_lock_map(),
            lctx.thread_lock_map() == old(lctx).thread_lock_map(),
            lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            lctx.scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            lctx.pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            lctx.pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            lctx.pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
            lctx.iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            lctx.iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
            lctx.allocator_quota_4k_lock_map().dom().is_empty() && lctx.allocator_global_pool_4k_lock_map().dom().is_empty(),
            lctx.allocator_quota_2m_lock_map().dom().is_empty() && lctx.allocator_global_pool_2m_lock_map().dom().is_empty(),
            lctx.allocator_quota_1g_lock_map().dom().is_empty() && lctx.allocator_global_pool_1g_lock_map().dom().is_empty(),
            lctx.allocator_cache_1g_lock_map().dom().is_empty(),
            forall|x: (RwLockPageAllocatorPtr, CpuId)| #![trigger lctx.allocator_cache_4k_lock_map().dom().contains(x)] lctx.allocator_cache_4k_lock_map().dom().contains(x) ==> x.0 == a4 && index_valid(NUM_CPUS, x.1),
            forall|i: CpuId| #![trigger caches_4k.dom().contains(i)] #![trigger caches_4k[i]] index_valid(NUM_CPUS, i) ==> {
                &&& caches_4k.dom().contains(i)
                &&& caches_4k[i].state() is WriteLock
                &&& caches_4k[i].thread_id() == lctx.thread_id()
                &&& krnl.allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().locking_thread() == (RwLockState::Write { thread_id: lctx.thread_id(), lock_id: caches_4k[i].lock_id() })
                &&& typed_lock_map_contains_mode(lctx.allocator_cache_4k_lock_map(), (a4, i), TypedLockMode::Write)
            },
            forall|x: (RwLockPageAllocatorPtr, CpuId)| #![trigger lctx.allocator_cache_2m_lock_map().dom().contains(x)] lctx.allocator_cache_2m_lock_map().dom().contains(x) ==> x.0 == a2 && x.1 < c,
            forall|i: CpuId| #![trigger caches_2m.dom().contains(i)] #![trigger caches_2m[i]] #![trigger lctx.allocator_cache_2m_lock_map().dom().contains((a2, i))] i < c ==> {
                &&& caches_2m.dom().contains(i)
                &&& caches_2m[i].state() is WriteLock
                &&& caches_2m[i].thread_id() == lctx.thread_id()
                &&& krnl.allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().locking_thread() == (RwLockState::Write { thread_id: lctx.thread_id(), lock_id: caches_2m[i].lock_id() })
                &&& typed_lock_map_contains_mode(lctx.allocator_cache_2m_lock_map(), (a2, i), TypedLockMode::Write)
            },
        decreases NUM_CPUS - c,
    {
        proof { krnl.cpu_arr.typed_lock_map_aligned_lock_id_at(lctx.cpu_lock_map(), lctx.thread_id(), lctx.cpu_id()); krnl.thr_mp.typed_lock_map_aligned_lock_id_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr); }
        let Tracked(perm) = krnl.wlock_allocator_cache_2m(a2, c, Tracked(&mut *lctx));
        proof {
            caches_2m.tracked_insert(c, perm);
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        }
        c = c + 1;
    }
    let mut c: usize = 0;
    while c < NUM_CPUS
        invariant
            old(krnl).inv(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(lctx).kernel_view_locking_state() is Acquire,
            ({
                let cpu = old(krnl).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view();
                &&& index_valid(NUM_CPUS, old(lctx).cpu_id())
                &&& old(lctx).cpu_lock_map().dom() =~= set![old(lctx).cpu_id()]
                &&& cpu.state is Running
            }),
            old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
            old(krnl).thr_mp.dom().contains(thread_ptr),
            old(krnl).thr_mp.spec_index(thread_ptr).view().state is RUNNING,
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(lctx).endpoint_lock_map().dom().is_empty(),
            old(lctx).pagetable_lock_map().dom().is_empty(),
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).iommu_root_table_lock_map().dom().is_empty(),
            old(krnl).ctn_mp.dom().contains(container_ptr),
            forall|p: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(p)] old(lctx).page_lock_map().dom().contains(p) ==> old(krnl).pg_arr.lock_id_by_index(p).major <= ALLOCATED_PAGE_MAJOR,
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            0 <= c <= NUM_CPUS,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.kernel_view_locking_state() is Acquire,
            *krnl == (KernelK { allc_4k_mp: krnl.allc_4k_mp, allc_2m_mp: krnl.allc_2m_mp, allc_1g_mp: krnl.allc_1g_mp, ..*old(krnl) }),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), krnl),
            kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), krnl),
            old(krnl).ctn_mp.dom().contains(container_ptr),
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == a4,
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_2m == a2,
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_1g == a1,
            old(krnl).allc_4k_mp.dom().contains(a4) && old(krnl).allc_2m_mp.dom().contains(a2) && old(krnl).allc_1g_mp.dom().contains(a1),
            forall|p: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(p)] old(lctx).page_lock_map().dom().contains(p) ==> old(krnl).pg_arr.lock_id_by_index(p).major <= ALLOCATED_PAGE_MAJOR,
            krnl.allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
            forall|i: CpuId| #![trigger krnl.allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i)
                ==> krnl.allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().view() == old(krnl).allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().view(),
            forall|a: RwLockPageAllocatorPtr| #![trigger krnl.allc_4k_mp.spec_index(a)] krnl.allc_4k_mp.dom().contains(a) ==> {
                &&& krnl.allc_4k_mp.spec_index(a).quota == old(krnl).allc_4k_mp.spec_index(a).quota
                &&& krnl.allc_4k_mp.spec_index(a).global_pool == old(krnl).allc_4k_mp.spec_index(a).global_pool
                &&& krnl.allc_4k_mp.spec_index(a).owning_container == old(krnl).allc_4k_mp.spec_index(a).owning_container
            },
            krnl.allc_2m_mp.dom() == old(krnl).allc_2m_mp.dom(),
            forall|i: CpuId| #![trigger krnl.allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i)
                ==> krnl.allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().view() == old(krnl).allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().view(),
            forall|a: RwLockPageAllocatorPtr| #![trigger krnl.allc_2m_mp.spec_index(a)] krnl.allc_2m_mp.dom().contains(a) ==> {
                &&& krnl.allc_2m_mp.spec_index(a).quota == old(krnl).allc_2m_mp.spec_index(a).quota
                &&& krnl.allc_2m_mp.spec_index(a).global_pool == old(krnl).allc_2m_mp.spec_index(a).global_pool
                &&& krnl.allc_2m_mp.spec_index(a).owning_container == old(krnl).allc_2m_mp.spec_index(a).owning_container
            },
            krnl.allc_1g_mp.dom() == old(krnl).allc_1g_mp.dom(),
            forall|i: CpuId| #![trigger krnl.allc_1g_mp.spec_index(a1).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i)
                ==> krnl.allc_1g_mp.spec_index(a1).cpu_caches.spec_index(i).view().view() == old(krnl).allc_1g_mp.spec_index(a1).cpu_caches.spec_index(i).view().view(),
            forall|a: RwLockPageAllocatorPtr| #![trigger krnl.allc_1g_mp.spec_index(a)] krnl.allc_1g_mp.dom().contains(a) ==> {
                &&& krnl.allc_1g_mp.spec_index(a).quota == old(krnl).allc_1g_mp.spec_index(a).quota
                &&& krnl.allc_1g_mp.spec_index(a).global_pool == old(krnl).allc_1g_mp.spec_index(a).global_pool
                &&& krnl.allc_1g_mp.spec_index(a).owning_container == old(krnl).allc_1g_mp.spec_index(a).owning_container
            },
            lctx.page_lock_map() == old(lctx).page_lock_map(),
            lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
            lctx.pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            lctx.cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            lctx.process_lock_map() == old(lctx).process_lock_map(),
            lctx.thread_lock_map() == old(lctx).thread_lock_map(),
            lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            lctx.scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            lctx.pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            lctx.pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            lctx.pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
            lctx.iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            lctx.iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
            lctx.allocator_quota_4k_lock_map().dom().is_empty() && lctx.allocator_global_pool_4k_lock_map().dom().is_empty(),
            lctx.allocator_quota_2m_lock_map().dom().is_empty() && lctx.allocator_global_pool_2m_lock_map().dom().is_empty(),
            lctx.allocator_quota_1g_lock_map().dom().is_empty() && lctx.allocator_global_pool_1g_lock_map().dom().is_empty(),
            forall|x: (RwLockPageAllocatorPtr, CpuId)| #![trigger lctx.allocator_cache_4k_lock_map().dom().contains(x)] lctx.allocator_cache_4k_lock_map().dom().contains(x) ==> x.0 == a4 && index_valid(NUM_CPUS, x.1),
            forall|i: CpuId| #![trigger caches_4k.dom().contains(i)] #![trigger caches_4k[i]] index_valid(NUM_CPUS, i) ==> {
                &&& caches_4k.dom().contains(i)
                &&& caches_4k[i].state() is WriteLock
                &&& caches_4k[i].thread_id() == lctx.thread_id()
                &&& krnl.allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().locking_thread() == (RwLockState::Write { thread_id: lctx.thread_id(), lock_id: caches_4k[i].lock_id() })
                &&& typed_lock_map_contains_mode(lctx.allocator_cache_4k_lock_map(), (a4, i), TypedLockMode::Write)
            },
            forall|x: (RwLockPageAllocatorPtr, CpuId)| #![trigger lctx.allocator_cache_2m_lock_map().dom().contains(x)] lctx.allocator_cache_2m_lock_map().dom().contains(x) ==> x.0 == a2 && index_valid(NUM_CPUS, x.1),
            forall|i: CpuId| #![trigger caches_2m.dom().contains(i)] #![trigger caches_2m[i]] index_valid(NUM_CPUS, i) ==> {
                &&& caches_2m.dom().contains(i)
                &&& caches_2m[i].state() is WriteLock
                &&& caches_2m[i].thread_id() == lctx.thread_id()
                &&& krnl.allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().locking_thread() == (RwLockState::Write { thread_id: lctx.thread_id(), lock_id: caches_2m[i].lock_id() })
                &&& typed_lock_map_contains_mode(lctx.allocator_cache_2m_lock_map(), (a2, i), TypedLockMode::Write)
            },
            forall|x: (RwLockPageAllocatorPtr, CpuId)| #![trigger lctx.allocator_cache_1g_lock_map().dom().contains(x)] lctx.allocator_cache_1g_lock_map().dom().contains(x) ==> x.0 == a1 && x.1 < c,
            forall|i: CpuId| #![trigger caches_1g.dom().contains(i)] #![trigger caches_1g[i]] #![trigger lctx.allocator_cache_1g_lock_map().dom().contains((a1, i))] i < c ==> {
                &&& caches_1g.dom().contains(i)
                &&& caches_1g[i].state() is WriteLock
                &&& caches_1g[i].thread_id() == lctx.thread_id()
                &&& krnl.allc_1g_mp.spec_index(a1).cpu_caches.spec_index(i).view().locking_thread() == (RwLockState::Write { thread_id: lctx.thread_id(), lock_id: caches_1g[i].lock_id() })
                &&& typed_lock_map_contains_mode(lctx.allocator_cache_1g_lock_map(), (a1, i), TypedLockMode::Write)
            },
        decreases NUM_CPUS - c,
    {
        let Tracked(perm) = krnl.wlock_allocator_cache_1g(a1, c, Tracked(&mut *lctx));
        proof {
            caches_1g.tracked_insert(c, perm);
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        }
        c = c + 1;
    }
}

/// Write-hold the 4K, 2M, and 1G global pools and then quotas of the marked container `container_ptr`'s allocators and
/// the 4K and 2M ones of the killer's container `owner_ptr`'s allocators, each pair in container order; return the 1G
/// pool's and quota's permissions.
pub(crate) fn kill_container_retire_lock_pools_quotas(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr,
    Tracked(pools_4k): Tracked<&mut Map<RwLockPageAllocatorPtr, LockPerm>>, Tracked(pools_2m): Tracked<&mut Map<RwLockPageAllocatorPtr, LockPerm>>,
    Tracked(quotas_4k): Tracked<&mut Map<RwLockPageAllocatorPtr, LockPerm>>, Tracked(quotas_2m): Tracked<&mut Map<RwLockPageAllocatorPtr, LockPerm>>,
) -> (ret: (Tracked<LockPerm>, Tracked<LockPerm>))
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        ({
            let cpu = old(krnl).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view();
            &&& index_valid(NUM_CPUS, old(lctx).cpu_id())
            &&& old(lctx).cpu_lock_map().dom() =~= set![old(lctx).cpu_id()]
            &&& cpu.state is Running
        }),
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state is RUNNING,
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.dom().contains(owner_ptr),
        container_ptr != owner_ptr,
        forall|p: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(p)] old(lctx).page_lock_map().dom().contains(p) ==> old(krnl).pg_arr.lock_id_by_index(p).major <= ALLOCATED_PAGE_MAJOR,
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty() && old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty() && old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty() && old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
        old(pools_4k).dom().is_empty() && old(pools_2m).dom().is_empty() && old(quotas_4k).dom().is_empty() && old(quotas_2m).dom().is_empty(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        *final(krnl) == (KernelK { allc_4k_mp: final(krnl).allc_4k_mp, allc_2m_mp: final(krnl).allc_2m_mp, allc_1g_mp: final(krnl).allc_1g_mp, ..*old(krnl) }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_cache_4k_lock_map() == old(lctx).allocator_cache_4k_lock_map(),
        final(lctx).allocator_cache_2m_lock_map() == old(lctx).allocator_cache_2m_lock_map(),
        final(lctx).allocator_cache_1g_lock_map() == old(lctx).allocator_cache_1g_lock_map(),
        final(krnl).allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
        final(krnl).allc_2m_mp.dom() == old(krnl).allc_2m_mp.dom(),
        final(krnl).allc_1g_mp.dom() == old(krnl).allc_1g_mp.dom(),
        forall|a: RwLockPageAllocatorPtr, i: CpuId| #![trigger final(krnl).allc_4k_mp.spec_index(a).cpu_caches.spec_index(i)]
            final(krnl).allc_4k_mp.dom().contains(a) ==> final(krnl).allc_4k_mp.spec_index(a).cpu_caches.spec_index(i) == old(krnl).allc_4k_mp.spec_index(a).cpu_caches.spec_index(i),
        forall|a: RwLockPageAllocatorPtr, i: CpuId| #![trigger final(krnl).allc_2m_mp.spec_index(a).cpu_caches.spec_index(i)]
            final(krnl).allc_2m_mp.dom().contains(a) ==> final(krnl).allc_2m_mp.spec_index(a).cpu_caches.spec_index(i) == old(krnl).allc_2m_mp.spec_index(a).cpu_caches.spec_index(i),
        forall|a: RwLockPageAllocatorPtr, i: CpuId| #![trigger final(krnl).allc_1g_mp.spec_index(a).cpu_caches.spec_index(i)]
            final(krnl).allc_1g_mp.dom().contains(a) ==> final(krnl).allc_1g_mp.spec_index(a).cpu_caches.spec_index(i) == old(krnl).allc_1g_mp.spec_index(a).cpu_caches.spec_index(i),
        ({
            let ro = old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view();
            let owner_ro = old(krnl).ctn_mp.spec_index(owner_ptr).view_rodata().view();
            let (a4, a2, a1, o4, o2) = (ro.allocator_ptr_4k, ro.allocator_ptr_2m, ro.allocator_ptr_1g, owner_ro.allocator_ptr_4k, owner_ro.allocator_ptr_2m);
            &&& final(krnl).allc_4k_mp.spec_index(a4).quota.view() == old(krnl).allc_4k_mp.spec_index(a4).quota.view()
            &&& final(krnl).allc_2m_mp.spec_index(a2).quota.view() == old(krnl).allc_2m_mp.spec_index(a2).quota.view()
            &&& final(krnl).allc_1g_mp.spec_index(a1).quota.view() == old(krnl).allc_1g_mp.spec_index(a1).quota.view()
            &&& final(lctx).allocator_global_pool_4k_lock_map().dom() == set![a4, o4]
            &&& final(pools_4k).dom() == set![a4, o4]
            &&& typed_lock_map_contains_mode(final(lctx).allocator_global_pool_4k_lock_map(), a4, TypedLockMode::Write)
            &&& final(pools_4k)[a4].state() is WriteLock && final(pools_4k)[a4].thread_id() == final(lctx).thread_id()
            &&& final(pools_4k)[a4].lock_id() == final(krnl).allc_4k_mp.spec_index(a4).global_pool.locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(final(lctx).allocator_global_pool_4k_lock_map(), o4, TypedLockMode::Write)
            &&& final(pools_4k)[o4].state() is WriteLock && final(pools_4k)[o4].thread_id() == final(lctx).thread_id()
            &&& final(pools_4k)[o4].lock_id() == final(krnl).allc_4k_mp.spec_index(o4).global_pool.locking_thread()->Write_lock_id
            &&& final(lctx).allocator_global_pool_2m_lock_map().dom() == set![a2, o2]
            &&& final(pools_2m).dom() == set![a2, o2]
            &&& typed_lock_map_contains_mode(final(lctx).allocator_global_pool_2m_lock_map(), a2, TypedLockMode::Write)
            &&& final(pools_2m)[a2].state() is WriteLock && final(pools_2m)[a2].thread_id() == final(lctx).thread_id()
            &&& final(pools_2m)[a2].lock_id() == final(krnl).allc_2m_mp.spec_index(a2).global_pool.locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(final(lctx).allocator_global_pool_2m_lock_map(), o2, TypedLockMode::Write)
            &&& final(pools_2m)[o2].state() is WriteLock && final(pools_2m)[o2].thread_id() == final(lctx).thread_id()
            &&& final(pools_2m)[o2].lock_id() == final(krnl).allc_2m_mp.spec_index(o2).global_pool.locking_thread()->Write_lock_id
            &&& final(lctx).allocator_global_pool_1g_lock_map().dom() == set![a1]
            &&& typed_lock_map_contains_mode(final(lctx).allocator_global_pool_1g_lock_map(), a1, TypedLockMode::Write)
            &&& ret.0.view().state() is WriteLock && ret.0.view().thread_id() == final(lctx).thread_id()
            &&& ret.0.view().lock_id() == final(krnl).allc_1g_mp.spec_index(a1).global_pool.locking_thread()->Write_lock_id
            &&& final(lctx).allocator_quota_4k_lock_map().dom() == set![a4, o4]
            &&& final(quotas_4k).dom() == set![a4, o4]
            &&& typed_lock_map_contains_mode(final(lctx).allocator_quota_4k_lock_map(), a4, TypedLockMode::Write)
            &&& final(quotas_4k)[a4].state() is WriteLock && final(quotas_4k)[a4].thread_id() == final(lctx).thread_id()
            &&& final(quotas_4k)[a4].lock_id() == final(krnl).allc_4k_mp.spec_index(a4).quota.locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(final(lctx).allocator_quota_4k_lock_map(), o4, TypedLockMode::Write)
            &&& final(quotas_4k)[o4].state() is WriteLock && final(quotas_4k)[o4].thread_id() == final(lctx).thread_id()
            &&& final(quotas_4k)[o4].lock_id() == final(krnl).allc_4k_mp.spec_index(o4).quota.locking_thread()->Write_lock_id
            &&& final(lctx).allocator_quota_2m_lock_map().dom() == set![a2, o2]
            &&& final(quotas_2m).dom() == set![a2, o2]
            &&& typed_lock_map_contains_mode(final(lctx).allocator_quota_2m_lock_map(), a2, TypedLockMode::Write)
            &&& final(quotas_2m)[a2].state() is WriteLock && final(quotas_2m)[a2].thread_id() == final(lctx).thread_id()
            &&& final(quotas_2m)[a2].lock_id() == final(krnl).allc_2m_mp.spec_index(a2).quota.locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(final(lctx).allocator_quota_2m_lock_map(), o2, TypedLockMode::Write)
            &&& final(quotas_2m)[o2].state() is WriteLock && final(quotas_2m)[o2].thread_id() == final(lctx).thread_id()
            &&& final(quotas_2m)[o2].lock_id() == final(krnl).allc_2m_mp.spec_index(o2).quota.locking_thread()->Write_lock_id
            &&& final(lctx).allocator_quota_1g_lock_map().dom() == set![a1]
            &&& typed_lock_map_contains_mode(final(lctx).allocator_quota_1g_lock_map(), a1, TypedLockMode::Write)
            &&& ret.1.view().state() is WriteLock && ret.1.view().thread_id() == final(lctx).thread_id()
            &&& ret.1.view().lock_id() == final(krnl).allc_1g_mp.spec_index(a1).quota.locking_thread()->Write_lock_id
        }),
{
    proof {
        container_perms_wf_map(krnl.ctn_mp); container_perms_wf_at(krnl.ctn_mp, container_ptr); container_perms_wf_at(krnl.ctn_mp, owner_ptr);
        container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr);
        container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, owner_ptr);
    }
    let a4 = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().allocator_ptr_4k;
    let a2 = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().allocator_ptr_2m;
    let a1 = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().allocator_ptr_1g;
    let o4 = krnl.ctn_mp.borrow_rodata(owner_ptr).borrow().allocator_ptr_4k;
    let o2 = krnl.ctn_mp.borrow_rodata(owner_ptr).borrow().allocator_ptr_2m;
    kill_container_wlock_pool_pairs(krnl, Tracked(&mut *lctx), container_ptr, owner_ptr, a4, o4, a2, o2, Tracked(&mut *pools_4k), Tracked(&mut *pools_2m));
    let pool_1g = krnl.wlock_allocator_global_pool_1g_ordered(a1, Tracked(&mut *lctx));
    kill_container_wlock_quota_pairs(krnl, Tracked(&mut *lctx), container_ptr, owner_ptr, a4, o4, a2, o2, Tracked(&mut *quotas_4k), Tracked(&mut *quotas_2m));
    let quota_1g = krnl.wlock_allocator_quota_1g_ordered(a1, Tracked(&mut *lctx));
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        assert(lctx.allocator_global_pool_1g_lock_map().dom() =~= set![a1] && lctx.allocator_quota_1g_lock_map().dom() =~= set![a1]);
    }
    (pool_1g, quota_1g)
}

/// Write-hold the merged tails of the marked container `container_ptr`'s two 2M object pages, whose heads and 4K object
/// pages are exactly the held pages, lower head first; return the tails' permissions of the container head and of the
/// PCID allocator head.
pub(crate) fn kill_container_retire_lock_tails(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, container_ptr: RwLockContainerPtr)
    -> (ret: (Tracked<Map<PageIndex, LockPerm>>, Tracked<Map<PageIndex, LockPerm>>))
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        typed_lock_map_majors_lt(old(lctx).cpu_lock_map(), CPU_LOCK_MAJOR_OFF),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        forall|x: (RwLockCpuOfflineFlagsPtr, CpuId)| #![trigger old(lctx).cpu_offline_flag_lock_map().dom().contains(x)]
            old(lctx).cpu_offline_flag_lock_map().dom().contains(x) ==> x.0 == cpu_offline_flags_ptr(container_ptr),
        typed_lock_map_majors_lt(old(lctx).page_lock_map(), MERGED_PAGE_LOCK_MAJOR),
        ({
            let ro = old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view();
            let pages_4k = kill_container_retire_pages_4k(ro);
            let heads = kill_container_retire_heads(container_ptr, ro);
            &&& old(lctx).page_lock_map().dom() == pages_4k.to_set().insert(heads[0]).insert(heads[1])
            &&& index_valid(NUM_PAGES, pages_4k[0]) && old(krnl).pg_arr.spec_index(pages_4k[0]).view().view().state is Allocated4k
            &&& index_valid(NUM_PAGES, pages_4k[1]) && old(krnl).pg_arr.spec_index(pages_4k[1]).view().view().state is Allocated4k
            &&& index_valid(NUM_PAGES, pages_4k[2]) && old(krnl).pg_arr.spec_index(pages_4k[2]).view().view().state is Allocated4k
            &&& index_valid(NUM_PAGES, pages_4k[3]) && old(krnl).pg_arr.spec_index(pages_4k[3]).view().view().state is Allocated4k
            &&& index_valid(NUM_PAGES, pages_4k[4]) && old(krnl).pg_arr.spec_index(pages_4k[4]).view().view().state is Allocated4k
            &&& page_index_2m_valid(heads[0]) && old(krnl).pg_arr.spec_index(heads[0]).view().view().state is Allocated2m
            &&& page_index_2m_valid(heads[1]) && old(krnl).pg_arr.spec_index(heads[1]).view().view().state is Allocated2m
            &&& heads[0] != heads[1]
            &&& page_ptr_valid(container_ptr) && page_ptr_valid(ro.pcid_allocator)
        }),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, ..*old(krnl) }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        forall|i: PageIndex| #![trigger final(krnl).pg_arr.spec_index(i).view().view()]
            index_valid(NUM_PAGES, i) ==> final(krnl).pg_arr.spec_index(i).view().view() == old(krnl).pg_arr.spec_index(i).view().view(),
        ({
            let heads = kill_container_retire_heads(container_ptr, old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view());
            &&& final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom() + page_2m_tail_indices(heads[0]) + page_2m_tail_indices(heads[1])
            &&& forall|p: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(p)] old(lctx).page_lock_map().dom().contains(p)
                ==> final(lctx).page_lock_map()[p] == old(lctx).page_lock_map()[p] && final(krnl).pg_arr.spec_index(p) == old(krnl).pg_arr.spec_index(p)
            &&& owned_2m_tail_lock_perms_wf(ret.0.view(), final(krnl).pg_arr, final(lctx), heads[0])
            &&& owned_2m_tail_lock_perms_wf(ret.1.view(), final(krnl).pg_arr, final(lctx), heads[1])
        }),
{
    let ghost ro = krnl.ctn_mp.spec_index(container_ptr).view_rodata().view();
    let ghost pages_4k = kill_container_retire_pages_4k(ro);
    let ghost held = lctx.page_lock_map().dom();
    proof {
        container_perms_wf_map(krnl.ctn_mp); container_perms_wf_at(krnl.ctn_mp, container_ptr);
        container_cpu_offline_flags_wf_container_at(krnl.ctn_mp, krnl.cpu_offline_mp, container_ptr);
    }
    let pcid_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().pcid_allocator;
    let h0 = page_ptr2page_index(container_ptr);
    let h1 = page_ptr2page_index(pcid_ptr);
    proof {
        let (lo, hi) = if h0 < h1 { (h0, h1) } else { (h1, h0) };
        assert(lo + 512 <= hi) by (nonlinear_arith) requires lo % 512 == 0, hi % 512 == 0, lo < hi {};
        hugepage_2m_wf_tail_at(krnl.pg_arr, h0, pages_4k[0]); hugepage_2m_wf_tail_at(krnl.pg_arr, h0, pages_4k[1]); hugepage_2m_wf_tail_at(krnl.pg_arr, h0, pages_4k[2]);
        hugepage_2m_wf_tail_at(krnl.pg_arr, h0, pages_4k[3]); hugepage_2m_wf_tail_at(krnl.pg_arr, h0, pages_4k[4]); hugepage_2m_wf_tail_at(krnl.pg_arr, h0, h1);
        hugepage_2m_wf_tail_at(krnl.pg_arr, h1, pages_4k[0]); hugepage_2m_wf_tail_at(krnl.pg_arr, h1, pages_4k[1]); hugepage_2m_wf_tail_at(krnl.pg_arr, h1, pages_4k[2]);
        hugepage_2m_wf_tail_at(krnl.pg_arr, h1, pages_4k[3]); hugepage_2m_wf_tail_at(krnl.pg_arr, h1, pages_4k[4]); hugepage_2m_wf_tail_at(krnl.pg_arr, h1, h0);
        assert(held.disjoint(page_2m_tail_indices(h0)) && held.disjoint(page_2m_tail_indices(h1)));
        assert(page_2m_tail_indices(h0).disjoint(page_2m_tail_indices(h1)));
    }
    let tracked mut t0: Map<PageIndex, LockPerm> = Map::tracked_empty();
    let tracked mut t1: Map<PageIndex, LockPerm> = Map::tracked_empty();
    if h0 < h1 {
        let Tracked(x) = wlock_allocated_2m_page_tails(krnl, h0, Tracked(&mut *lctx));
        proof { t0 = x; }
        let Tracked(y) = wlock_allocated_2m_page_tails(krnl, h1, Tracked(&mut *lctx));
        proof { t1 = y; }
    } else {
        let Tracked(y) = wlock_allocated_2m_page_tails(krnl, h1, Tracked(&mut *lctx));
        proof { t1 = y; }
        let Tracked(x) = wlock_allocated_2m_page_tails(krnl, h0, Tracked(&mut *lctx));
        proof { t0 = x; }
    }
    proof {
        assert(lctx.page_lock_map().dom() =~= held + page_2m_tail_indices(h0) + page_2m_tail_indices(h1));
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
        assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
    }
    (Tracked(t0), Tracked(t1))
}
} // verus!
