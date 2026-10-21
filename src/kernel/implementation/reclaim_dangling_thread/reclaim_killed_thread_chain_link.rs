use vstd::prelude::*;
use crate::*;
use super::reclaim_dangling_thread::reclaim_dangling_thread;
use super::reclaim_killed_thread_chain::{release_killed_thread_descriptors, release_killed_thread_caller};
#[cfg(verus_keep_ghost)]
use super::reclaim_killed_thread_chain_trace::{killed_thread_reclaim_partial_trace, killed_thread_reclaim_chain_trace, killed_thread_reclaim_step_pre_from_k};

verus! {
/// Reclaim one link of a killed thread chain: release every descriptor of the write-held killed thread `thread_ptr`,
/// release its caller, and reclaim the thread; returns the killed caller it took over, if any, write-held.
pub(super) fn reclaim_killed_thread_link(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, thread_ptr: RwLockThreadPtr,
    Tracked(thread_lock_perm): Tracked<LockPerm>,
) -> (ret: (Option<RwLockThreadPtr>, Tracked<Option<LockPerm>>))
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        cpu_id == old(lctx).cpu_id(),
        old(steps).snapshot_k() == *old(krnl),
        killed_thread_reclaim_lock_context(*old(krnl), *old(lctx)),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state is KILLED,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(thread_ptr).view().callee is None,
        old(krnl).thr_mp.spec_index(thread_ptr).view().proc_linkedlist_node.is_init(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k == 0,
        old(krnl).thr_mp.spec_index(thread_ptr).view().quota_2m == 0,
        old(krnl).thr_mp.spec_index(thread_ptr).view().quota_1g == 0,
        forall|held_thread: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(held_thread)]
            old(lctx).thread_lock_map().dom().contains(held_thread) ==> !(old(krnl).thr_mp.spec_index(held_thread).view().state is KILLED) || old(krnl).thr_mp.spec_index(held_thread).being_killed() || held_thread == thread_ptr,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() < final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] #![trigger final(krnl).ctn_mp.spec_index(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
            &&& final(krnl).ctn_mp.dom().contains(c)
            &&& final(krnl).ctn_mp.spec_index(c).view() == old(krnl).ctn_mp.spec_index(c).view()
            &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
            &&& final(krnl).ctn_mp.spec_index(c).being_killed() == old(krnl).ctn_mp.spec_index(c).being_killed()
            &&& final(krnl).ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes
        },
        killed_thread_reclaim_lock_context(*final(krnl), *final(lctx)),
        held_threads_unchanged_except(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx), set![thread_ptr]),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_quota_4k_lock_map() == old(lctx).allocator_quota_4k_lock_map(),
        final(lctx).allocator_cache_4k_lock_map() == old(lctx).allocator_cache_4k_lock_map(),
        final(lctx).allocator_global_pool_4k_lock_map() == old(lctx).allocator_global_pool_4k_lock_map(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        ret.0 is None ==> final(lctx).thread_lock_map() == old(lctx).thread_lock_map().remove(thread_ptr),
        ret.0 matches Some(caller_ptr) ==> {
            &&& ret.1.view() is Some
            &&& !old(lctx).thread_lock_map().dom().contains(caller_ptr)
            &&& final(lctx).thread_lock_map() == old(lctx).thread_lock_map().remove(thread_ptr).insert(caller_ptr, final(lctx).thread_lock_map()[caller_ptr])
            &&& typed_lock_map_contains_mode(final(lctx).thread_lock_map(), caller_ptr, TypedLockMode::Write)
            &&& final(krnl).thr_mp.dom().contains(caller_ptr)
            &&& final(krnl).thr_mp.spec_index(caller_ptr).view().state is KILLED
            &&& final(krnl).thr_mp.spec_index(caller_ptr).view().callee is None
            &&& final(krnl).thr_mp.spec_index(caller_ptr).view().call_depth.view() + 1 == old(krnl).thr_mp.spec_index(thread_ptr).view().call_depth.view()
            &&& final(krnl).thr_mp.spec_index(caller_ptr).view().proc_linkedlist_node.is_init()
            &&& final(krnl).thr_mp.spec_index(caller_ptr).view().temp_alloc_clean()
            &&& final(krnl).thr_mp.spec_index(caller_ptr).view().free_quota_pending_clean()
            &&& final(krnl).thr_mp.spec_index(caller_ptr).view().quota_4k == 0
            &&& final(krnl).thr_mp.spec_index(caller_ptr).view().quota_2m == 0
            &&& final(krnl).thr_mp.spec_index(caller_ptr).view().quota_1g == 0
            &&& ret.1.view()->Some_0.state() is WriteLock
            &&& ret.1.view()->Some_0.thread_id() == old(lctx).thread_id()
            &&& ret.1.view()->Some_0.lock_id() == final(krnl).thr_mp.spec_index(caller_ptr).locking_thread()->Write_lock_id
            &&& forall|held_thread: RwLockThreadPtr| #![trigger final(lctx).thread_lock_map().dom().contains(held_thread)] final(lctx).thread_lock_map().dom().contains(held_thread)
                ==> !(final(krnl).thr_mp.spec_index(held_thread).view().state is KILLED) || final(krnl).thr_mp.spec_index(held_thread).being_killed() || held_thread == caller_ptr
        },
        killed_thread_reclaim_partial_trace(final(steps).view(), old(steps).view().len() as int, kernel_k_to_kernel_u(*old(krnl)), cpu_id, old(lctx).process_lock_map().dom(), old(lctx).container_lock_map().dom()),
{
    let ghost iter_steps = steps.view();
    proof {
        thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id);
        assert(kernel_steps_prefix_unchanged(iter_steps, iter_steps)) by { reveal(kernel_steps_prefix_unchanged); };
    }
    release_killed_thread_descriptors(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, thread_ptr, Tracked(&thread_lock_perm));
    let ghost caller_k = *krnl;
    let ghost desc_steps = steps.view();
    proof { assert(kernel_steps_prefix_unchanged(desc_steps, desc_steps)) by { reveal(kernel_steps_prefix_unchanged); }; }
    let (next, Tracked(next_perm)) = release_killed_thread_caller(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, thread_ptr, Tracked(&thread_lock_perm));
    let ghost caller_steps = steps.view();
    proof { assert(kernel_steps_prefix_unchanged(caller_steps, caller_steps)) by { reveal(kernel_steps_prefix_unchanged); }; }
    reclaim_dangling_thread(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, thread_ptr, Tracked(thread_lock_perm));
    let ghost reclaim_snap = steps.snapshot_k();
    proof {
        kernel_dangling_thread_reclaimed_implies_u_step(&reclaim_snap, &*krnl, thread_ptr);
        krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
        assert(killed_thread_reclaim_partial_trace(steps.view(), old(steps).view().len() as int, kernel_k_to_kernel_u(*old(krnl)), cpu_id, old(lctx).process_lock_map().dom(), old(lctx).container_lock_map().dom())) by {
            let processes = old(lctx).process_lock_map().dom();
            let containers = old(lctx).container_lock_map().dom();
            held_kernel_objects_unchanged_reflexive(old(krnl), old(lctx));
            killed_thread_reclaim_step_pre_from_k(&caller_k, old(krnl), cpu_id, processes, containers);
            killed_thread_reclaim_step_pre_from_k(&reclaim_snap, old(krnl), cpu_id, processes, containers);
            killed_thread_reclaim_chain_trace(steps.view(), old(steps).view().len() as int, iter_steps, desc_steps, caller_steps, kernel_k_to_kernel_u(*old(krnl)),
                kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(caller_k), cpu_id, processes, containers);
        };
        if let Some(caller_ptr) = next {
            assert(lctx.thread_lock_map() =~= old(lctx).thread_lock_map().remove(thread_ptr).insert(caller_ptr, lctx.thread_lock_map()[caller_ptr]));
        }
    }
    (next, Tracked(next_perm))
}
} // verus!
