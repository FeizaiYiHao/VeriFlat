use vstd::prelude::*;
use crate::*;
use super::reclaim_dangling_thread::reclaim_dangling_thread;
use super::take_over_dangling_caller::take_over_dangling_caller;
use super::wake_waiting_reply_caller::wake_waiting_reply_caller;
use super::drop_endpoint_descriptor::drop_endpoint_descriptor;
use super::reclaim_killed_thread_chain_link::reclaim_killed_thread_link;
#[cfg(verus_keep_ghost)]
use super::reclaim_killed_thread_chain_trace::{killed_thread_reclaim_partial_trace, killed_thread_reclaim_link_trace, killed_thread_reclaim_step_pre_from_k};

verus! {
/// Release every descriptor of the write-held killed thread `thread_ptr`, one step per descriptor holding an endpoint.
pub(super) fn release_killed_thread_descriptors(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, thread_ptr: RwLockThreadPtr,
    Tracked(thread_lock_perm): Tracked<&LockPerm>,
)
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
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
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
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        killed_thread_reclaim_lock_context(*final(krnl), *final(lctx)),
        held_threads_unchanged_except(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx), set![thread_ptr]),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { endpoint_descriptors: final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        forall|j: int| #![trigger final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[j]]
            0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==> final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[j] is None,
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        killed_thread_reclaim_partial_trace(final(steps).view(), old(steps).view().len() as int, kernel_k_to_kernel_u(*old(krnl)), cpu_id, old(lctx).process_lock_map().dom(), old(lctx).container_lock_map().dom()),
{
    let mut index: EndpointIdx = 0;
    proof { held_kernel_objects_unchanged_reflexive(&*krnl, &*lctx); thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); }
    while index < MAX_NUM_ENDPOINT_DESCRIPTORS
        invariant
            0 <= index <= MAX_NUM_ENDPOINT_DESCRIPTORS,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.kernel_view_locking_state() is Acquire,
            steps.snapshot_k() == *krnl,
            old(steps).view().len() <= steps.view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            krnl.cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
            held_cpus_unchanged(old(krnl).cpu_arr, krnl.cpu_arr, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx)),
            forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] #![trigger krnl.ctn_mp.spec_index(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
                &&& krnl.ctn_mp.dom().contains(c)
                &&& krnl.ctn_mp.spec_index(c).view() == old(krnl).ctn_mp.spec_index(c).view()
                &&& krnl.ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
                &&& krnl.ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
                &&& krnl.ctn_mp.spec_index(c).being_killed() == old(krnl).ctn_mp.spec_index(c).being_killed()
                &&& krnl.ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
                &&& krnl.ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
                &&& krnl.ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
                &&& krnl.ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes
            },
            typed_lock_maps_unchanged(old(lctx), lctx),
            killed_thread_reclaim_lock_context(*krnl, *lctx),
            held_threads_unchanged_except(old(krnl).thr_mp, krnl.thr_mp, old(lctx), set![thread_ptr]),
            krnl.thr_mp.dom().contains(thread_ptr),
            krnl.thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
            krnl.thr_mp.spec_index(thread_ptr).view() == (Thread { endpoint_descriptors: krnl.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
            forall|j: int| #![trigger krnl.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[j]]
                0 <= j < index ==> krnl.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[j] is None,
            krnl.thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
            krnl.thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
            killed_thread_reclaim_partial_trace(steps.view(), old(steps).view().len() as int, kernel_k_to_kernel_u(*old(krnl)), cpu_id, old(lctx).process_lock_map().dom(), old(lctx).container_lock_map().dom()),
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
        decreases MAX_NUM_ENDPOINT_DESCRIPTORS - index,
    {
        proof { thread_perms_wf_map(krnl.thr_mp); thread_perms_wf_at(krnl.thr_mp, thread_ptr); thread_cpu_wf_cpu_at(old(krnl).thr_mp, old(krnl).cpu_arr, cpu_id); }
        let descriptor = *krnl.thr_mp.borrow_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(thread_lock_perm)).endpoint_descriptors.get(index);
        if let Some(endpoint_ptr) = descriptor {
            proof { assert(krnl.ep_mp.dom().contains(endpoint_ptr)) by { thread_endpoint_ref_counter_wf_thread_at(krnl.thr_mp, krnl.ep_mp, thread_ptr, index); }; }
            let ghost drop_pre = *krnl;
            let ghost drop_lctx = *lctx;
            let released = drop_endpoint_descriptor(krnl, Tracked(&mut *lctx), cpu_id, thread_ptr, endpoint_ptr, index, Tracked(thread_lock_perm));
            proof {
                drop_pre.thr_mp.typed_lock_map_aligned_write_at(drop_lctx.thread_lock_map(), drop_lctx.thread_id(), thread_ptr);
                thread_perms_wf_at(drop_pre.thr_mp, thread_ptr);
                if released {
                    kernel_killed_endpoint_released_implies_u_step(&drop_pre, &*krnl, thread_ptr, endpoint_ptr, index);
                } else {
                    kernel_killed_descriptor_dropped_implies_u_step(&drop_pre, &*krnl, thread_ptr, endpoint_ptr, index);
                }
                krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
                assert(killed_thread_reclaim_partial_trace(steps.view(), old(steps).view().len() as int, kernel_k_to_kernel_u(*old(krnl)), cpu_id, old(lctx).process_lock_map().dom(), old(lctx).container_lock_map().dom())) by {
                    held_kernel_objects_unchanged_reflexive(old(krnl), old(lctx));
                    killed_thread_reclaim_step_pre_from_k(&drop_pre, old(krnl), cpu_id, old(lctx).process_lock_map().dom(), old(lctx).container_lock_map().dom());
                };
            }
        }
        index = index + 1;
    }
}

/// Release the caller of the write-held killed thread `thread_ptr`, if any, in one step: wake a caller waiting for the
/// reply on shard `cpu_id` of its container, or take over the dangling thread of a killed caller and return it write-held.
pub fn release_killed_thread_caller(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, thread_ptr: RwLockThreadPtr,
    Tracked(thread_lock_perm): Tracked<&LockPerm>,
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
        forall|held_thread: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(held_thread)]
            old(lctx).thread_lock_map().dom().contains(held_thread) ==> !(old(krnl).thr_mp.spec_index(held_thread).view().state is KILLED) || old(krnl).thr_mp.spec_index(held_thread).being_killed() || held_thread == thread_ptr,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        killed_thread_reclaim_lock_context(*final(krnl), *final(lctx)),
        held_threads_unchanged_except(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx), set![thread_ptr]),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { caller: None, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        ret.0 is None ==> typed_lock_maps_unchanged(old(lctx), final(lctx)),
        ret.0 matches Some(caller_ptr) ==> {
            &&& ret.1.view() is Some
            &&& caller_ptr != thread_ptr
            &&& !old(lctx).thread_lock_map().dom().contains(caller_ptr)
            &&& typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Thread(caller_ptr), TypedHeldLock { lock_id: final(krnl).thr_mp.lock_id_by_key(caller_ptr), mode: TypedLockMode::Write })
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
        },
        killed_thread_reclaim_partial_trace(final(steps).view(), old(steps).view().len() as int, kernel_k_to_kernel_u(*old(krnl)), cpu_id, old(lctx).process_lock_map().dom(), old(lctx).container_lock_map().dom()),
{
    proof {
        held_kernel_objects_unchanged_reflexive(&*krnl, &*lctx);
        thread_perms_wf_map(krnl.thr_mp);
        thread_perms_wf_at(krnl.thr_mp, thread_ptr);
        thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id);
        krnl.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr);
    }
    let caller = krnl.thr_mp.borrow_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(thread_lock_perm)).caller;
    if caller.is_none() {
        return (None, Tracked(None));
    }
    let caller_ptr = caller.unwrap();
    proof {
        assert({
            &&& krnl.thr_mp.dom().contains(caller_ptr)
            &&& caller_ptr != thread_ptr
            &&& krnl.thr_mp.spec_index(caller_ptr).view().state.is_reply_waiting()
            &&& krnl.thr_mp.spec_index(caller_ptr).view().callee == Some(thread_ptr)
            &&& krnl.thr_mp.spec_index(thread_ptr).view().call_depth.view() == krnl.thr_mp.spec_index(caller_ptr).view().call_depth.view() + 1
            &&& !lctx.thread_lock_map().dom().contains(caller_ptr)
        }) by { thread_caller_callee_wf_at(krnl.thr_mp, thread_ptr); };
        assert(!krnl.thr_mp.spec_index(caller_ptr).being_killed()) by { process_thread_wf_killed_thread_at(krnl.prc_mp, krnl.thr_mp, caller_ptr); };
        container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, caller_ptr);
    }
    let ghost section_pre = *krnl;
    let Tracked(caller_lock_perm) = krnl.wlock_thread_unless_killed(caller_ptr, Tracked(&mut *lctx)).unwrap();
    proof { thread_perms_wf_at(krnl.thr_mp, caller_ptr); }
    let caller_dangling = match krnl.thr_mp.borrow_typed(caller_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&caller_lock_perm)).state {
        ThreadState::DANGLING => true,
        _ => false,
    };
    if caller_dangling {
        take_over_dangling_caller(krnl, Tracked(&mut *lctx), thread_ptr, caller_ptr, Tracked(thread_lock_perm), Tracked(&caller_lock_perm));
        proof {
            kernel_killed_caller_taken_over_implies_u_step(&section_pre, &*krnl, thread_ptr, caller_ptr);
            assert(lctx.thread_lock_map() =~= old(lctx).thread_lock_map().insert(caller_ptr, TypedHeldLock { lock_id: krnl.thr_mp.lock_id_by_key(caller_ptr), mode: TypedLockMode::Write }));
            krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
            assert(killed_thread_reclaim_partial_trace(steps.view(), old(steps).view().len() as int, kernel_k_to_kernel_u(*old(krnl)), cpu_id, old(lctx).process_lock_map().dom(), old(lctx).container_lock_map().dom())) by {
                killed_thread_reclaim_step_pre_from_k(old(krnl), old(krnl), cpu_id, old(lctx).process_lock_map().dom(), old(lctx).container_lock_map().dom());
            };
        }
        (Some(caller_ptr), Tracked(Some(caller_lock_perm)))
    } else {
        let container_ptr = krnl.thr_mp.borrow_typed(caller_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&caller_lock_perm)).owning_container;
        wake_waiting_reply_caller(krnl, Tracked(&mut *lctx), cpu_id, container_ptr, thread_ptr, caller_ptr, Tracked(thread_lock_perm), Tracked(caller_lock_perm));
        proof {
            kernel_killed_caller_woken_implies_u_step(&section_pre, &*krnl, cpu_id, thread_ptr, caller_ptr);
            assert(lctx.thread_lock_map() =~= old(lctx).thread_lock_map());
            krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
            assert(killed_thread_reclaim_partial_trace(steps.view(), old(steps).view().len() as int, kernel_k_to_kernel_u(*old(krnl)), cpu_id, old(lctx).process_lock_map().dom(), old(lctx).container_lock_map().dom())) by {
                killed_thread_reclaim_step_pre_from_k(old(krnl), old(krnl), cpu_id, old(lctx).process_lock_map().dom(), old(lctx).container_lock_map().dom());
            };
        }
        (None, Tracked(None))
    }
}

/// Reclaim the write-held killed thread `thread_ptr` and every killed caller it takes over, one step per change:
/// release each descriptor, wake a caller waiting for the reply or take over the dangling thread of a killed caller, reclaim the
/// thread, and continue with a taken-over caller.
pub fn reclaim_killed_thread_chain(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, thread_ptr: RwLockThreadPtr,
    Tracked(thread_lock_perm): Tracked<LockPerm>,
)
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
        typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Thread(thread_ptr)),
        held_threads_unchanged_except(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx), set![thread_ptr]),
        killed_thread_reclaim_partial_trace(final(steps).view(), old(steps).view().len() as int, kernel_k_to_kernel_u(*old(krnl)), cpu_id, old(lctx).process_lock_map().dom(), old(lctx).container_lock_map().dom()),
{
    let mut cur = thread_ptr;
    let tracked mut cur_perm = thread_lock_perm;
    proof {
        held_kernel_objects_unchanged_reflexive(&*krnl, &*lctx);
        assert(lctx.thread_lock_map() =~= old(lctx).thread_lock_map().remove(thread_ptr).insert(thread_ptr, lctx.thread_lock_map()[thread_ptr]));
    }
    loop
        invariant_except_break
            krnl.thr_mp.dom().contains(cur),
            krnl.thr_mp.spec_index(cur).view().state is KILLED,
            typed_lock_map_contains_mode(lctx.thread_lock_map(), cur, TypedLockMode::Write),
            lctx.thread_lock_map().remove(cur) =~= old(lctx).thread_lock_map().remove(thread_ptr),
            lctx.thread_lock_map() == old(lctx).thread_lock_map().remove(thread_ptr).insert(cur, lctx.thread_lock_map()[cur]),
            cur == thread_ptr || !old(lctx).thread_lock_map().dom().contains(cur),
            cur_perm.state() is WriteLock,
            cur_perm.thread_id() == lctx.thread_id(),
            cur_perm.lock_id() == krnl.thr_mp.spec_index(cur).locking_thread()->Write_lock_id,
            krnl.thr_mp.spec_index(cur).view().callee is None,
            krnl.thr_mp.spec_index(cur).view().proc_linkedlist_node.is_init(),
            krnl.thr_mp.spec_index(cur).view().temp_alloc_clean(),
            krnl.thr_mp.spec_index(cur).view().free_quota_pending_clean(),
            krnl.thr_mp.spec_index(cur).view().quota_4k == 0,
            krnl.thr_mp.spec_index(cur).view().quota_2m == 0,
            krnl.thr_mp.spec_index(cur).view().quota_1g == 0,
            forall|held_thread: RwLockThreadPtr| #![trigger lctx.thread_lock_map().dom().contains(held_thread)]
                lctx.thread_lock_map().dom().contains(held_thread) ==> !(krnl.thr_mp.spec_index(held_thread).view().state is KILLED) || krnl.thr_mp.spec_index(held_thread).being_killed() || held_thread == cur,
        invariant
            old(krnl).inv(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            cpu_id == old(lctx).cpu_id(),
            killed_thread_reclaim_lock_context(*old(krnl), *old(lctx)),
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.kernel_view_locking_state() is Acquire,
            steps.snapshot_k() == *krnl,
            old(steps).view().len() <= steps.view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            krnl.cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
            held_cpus_unchanged(old(krnl).cpu_arr, krnl.cpu_arr, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx)),
            forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] #![trigger krnl.ctn_mp.spec_index(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
                &&& krnl.ctn_mp.dom().contains(c)
                &&& krnl.ctn_mp.spec_index(c).view() == old(krnl).ctn_mp.spec_index(c).view()
                &&& krnl.ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
                &&& krnl.ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
                &&& krnl.ctn_mp.spec_index(c).being_killed() == old(krnl).ctn_mp.spec_index(c).being_killed()
                &&& krnl.ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
                &&& krnl.ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
                &&& krnl.ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
                &&& krnl.ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes
            },
            killed_thread_reclaim_lock_context(*krnl, *lctx),
            held_threads_unchanged_except(old(krnl).thr_mp, krnl.thr_mp, old(lctx), set![thread_ptr]),
            lctx.page_lock_map() == old(lctx).page_lock_map(),
            lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
            lctx.pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            lctx.cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            lctx.process_lock_map() == old(lctx).process_lock_map(),
            lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            lctx.scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            lctx.pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            lctx.pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            lctx.iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            lctx.iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
            lctx.allocator_quota_4k_lock_map() == old(lctx).allocator_quota_4k_lock_map(),
            lctx.allocator_cache_4k_lock_map() == old(lctx).allocator_cache_4k_lock_map(),
            lctx.allocator_global_pool_4k_lock_map() == old(lctx).allocator_global_pool_4k_lock_map(),
            lctx.allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            lctx.allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            killed_thread_reclaim_partial_trace(steps.view(), old(steps).view().len() as int, kernel_k_to_kernel_u(*old(krnl)), cpu_id, old(lctx).process_lock_map().dom(), old(lctx).container_lock_map().dom()),
        ensures
            typed_lock_maps_removed(old(lctx), lctx, KernelObjId::Thread(thread_ptr)),
            old(steps).view().len() < steps.view().len(),
        decreases krnl.thr_mp.spec_index(cur).view().call_depth.view(),
    {
        let ghost iter_k = *krnl;
        let ghost iter_steps = steps.view();
        let (next, Tracked(next_perm)) = reclaim_killed_thread_link(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, cur, Tracked(cur_perm));
        proof {
            assert(killed_thread_reclaim_partial_trace(steps.view(), old(steps).view().len() as int, kernel_k_to_kernel_u(*old(krnl)), cpu_id, old(lctx).process_lock_map().dom(), old(lctx).container_lock_map().dom())) by {
                let processes = old(lctx).process_lock_map().dom();
                let containers = old(lctx).container_lock_map().dom();
                held_kernel_objects_unchanged_reflexive(old(krnl), old(lctx));
                assert(kernel_steps_prefix_unchanged(iter_steps, iter_steps)) by { reveal(kernel_steps_prefix_unchanged); };
                killed_thread_reclaim_step_pre_from_k(&iter_k, old(krnl), cpu_id, processes, containers);
                killed_thread_reclaim_link_trace(steps.view(), old(steps).view().len() as int, iter_steps, kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(iter_k), cpu_id, processes, containers);
            };
        }
        if let Some(caller_ptr) = next {
            cur = caller_ptr;
            proof {
                cur_perm = next_perm.tracked_unwrap();
                assert(lctx.thread_lock_map() =~= old(lctx).thread_lock_map().remove(thread_ptr).insert(cur, lctx.thread_lock_map()[cur]));
            }
        } else {
            break;
        }
    }
}
} // verus!
