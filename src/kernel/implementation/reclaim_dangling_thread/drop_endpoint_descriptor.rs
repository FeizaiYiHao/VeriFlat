use vstd::prelude::*;
use crate::*;
use super::release_endpoint::release_endpoint_last_reference;
#[cfg(verus_keep_ghost)]
use super::drop_endpoint_descriptor_eof::{drop_endpoint_descriptor_eof, drop_endpoint_descriptor_eof_transition_framing};

verus! {
/// Drop descriptor `index` of an exiting or killed thread: lock its endpoint and clear the descriptor. An endpoint with
/// other references loses this one; an endpoint whose last reference this is gets released, and the result says so.
pub fn drop_endpoint_descriptor(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, index: EndpointIdx,
    Tracked(thread_lock_perm): Tracked<&LockPerm>,
) -> (released: bool)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        cpu_id == old(lctx).cpu_id(),
        killed_thread_reclaim_lock_context(*old(krnl), *old(lctx)),
        index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state is RUNNING || old(krnl).thr_mp.spec_index(thread_ptr).view().state is KILLED,
        old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[index as int] == Some(endpoint_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        *final(krnl) == (KernelK { ctn_mp: final(krnl).ctn_mp, thr_mp: final(krnl).thr_mp, ep_mp: final(krnl).ep_mp, pg_arr: final(krnl).pg_arr, allc_4k_mp: final(krnl).allc_4k_mp, ..*old(krnl) }),
        final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { endpoint_descriptors: final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view().update(index as int, None),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).thr_mp.lock_id_by_key(thread_ptr) == old(krnl).thr_mp.lock_id_by_key(thread_ptr),
        old(krnl).ep_mp.dom().contains(endpoint_ptr),
        old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread() is None,
        !released ==> {
            &&& final(krnl).ctn_mp == old(krnl).ctn_mp
            &&& final(krnl).pg_arr == old(krnl).pg_arr
            &&& final(krnl).allc_4k_mp == old(krnl).allc_4k_mp
            &&& old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().len() > 1
            &&& final(krnl).ep_mp.unchanged_except(&old(krnl).ep_mp, endpoint_ptr)
            &&& final(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.view() == old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.view()
            &&& final(krnl).ep_mp.spec_index(endpoint_ptr).view().queue_state == old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue_state
            &&& final(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container == old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container
            &&& final(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_threads.view() == old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().remove((thread_ptr, index))
            &&& final(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread() is None
            &&& final(krnl).ep_mp.spec_index(endpoint_ptr).being_killed() == old(krnl).ep_mp.spec_index(endpoint_ptr).being_killed()
        },
        released ==> {
            &&& old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_threads.view() == set![(thread_ptr, index)]
            &&& old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.view() == Seq::<RwLockThreadPtr>::empty()
            &&& final(krnl).ep_mp.dom() == old(krnl).ep_mp.dom().remove(endpoint_ptr)
            &&& forall|e: RwLockEndpointPtr| #![trigger final(krnl).ep_mp.spec_index(e)] final(krnl).ep_mp.dom().contains(e) ==> final(krnl).ep_mp.spec_index(e) == old(krnl).ep_mp.spec_index(e)
            &&& final(krnl).ctn_mp.dom() == old(krnl).ctn_mp.dom()
            &&& forall|c: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(c)]
                old(krnl).ctn_mp.dom().contains(c) ==> {
                    let a = old(krnl).ctn_mp.spec_index(c);
                    let b = final(krnl).ctn_mp.spec_index(c);
                    &&& b.view() == a.view()
                    &&& b.view_rodata() == a.view_rodata()
                    &&& b.locking_thread() == a.locking_thread()
                    &&& b.being_killed() == a.being_killed()
                    &&& b.view_ghost() == if c == old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container {
                            ContainerGhost { owned_endpoints: Ghost(a.view_ghost().owned_endpoints.view().remove(endpoint_ptr)), ..a.view_ghost() }
                        } else { a.view_ghost() }
                    &&& final(krnl).allc_4k_mp.spec_index(a.view_rodata().view().allocator_ptr_4k).quota.view().view() as int
                        == old(krnl).allc_4k_mp.spec_index(a.view_rodata().view().allocator_ptr_4k).quota.view().view() as int + if a.view().owned_pages.view().contains(endpoint_ptr) { 1int } else { 0int }
                }
        },
{
    proof {
        thread_perms_wf_map(krnl.thr_mp);
        thread_perms_wf_at(krnl.thr_mp, thread_ptr);
        assert(krnl.ep_mp.dom().contains(endpoint_ptr) && krnl.ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((thread_ptr, index))) by {
            thread_endpoint_ref_counter_wf_thread_at(krnl.thr_mp, krnl.ep_mp, thread_ptr, index);
        };
    }
    let Tracked(endpoint_lock_perm) = krnl.wlock_endpoint(endpoint_ptr, Tracked(&mut *lctx));
    proof { endpoint_perms_wf_map(krnl.ep_mp); endpoint_perms_wf_at(krnl.ep_mp, endpoint_ptr); }
    let rf_counter = krnl.ep_mp.borrow_typed(endpoint_ptr, Ghost(lctx.endpoint_lock_map()), Tracked(&*lctx), Tracked(&endpoint_lock_perm)).rf_counter;
    let ghost locked = *krnl;
    let ghost owning_threads = krnl.ep_mp.spec_index(endpoint_ptr).view().owning_threads.view();
    proof { vstd::set::lemma_set_remove_len(owning_threads, (thread_ptr, index)); }
    if rf_counter == 1 {
        proof {
            assert(owning_threads =~= set![(thread_ptr, index)]) by { vstd::set_lib::lemma_set_empty_equivalency_len(owning_threads.remove((thread_ptr, index))); };
        }
        release_endpoint_last_reference(krnl, Tracked(&mut *lctx), cpu_id, thread_ptr, endpoint_ptr, index, Tracked(thread_lock_perm), Tracked(endpoint_lock_perm));
        proof { assert(lctx.endpoint_lock_map() =~= old(lctx).endpoint_lock_map()); }
        return true;
    }
    {
        let thread_mut = krnl.thr_mp.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(thread_lock_perm));
        thread_mut.endpoint_descriptors.set(index, None);
    } {
        let endpoint_mut = krnl.ep_mp.borrow_mut_typed(endpoint_ptr, Ghost(lctx.endpoint_lock_map()), Tracked(&*lctx), Tracked(&endpoint_lock_perm));
        endpoint_mut.rf_counter = endpoint_mut.rf_counter - 1;
        endpoint_mut.owning_threads = Ghost(endpoint_mut.owning_threads.view().remove((thread_ptr, index)));
    }
    proof {
        assert(typed_lock_maps_aligned(krnl, lctx) && krnl.thr_mp.lock_id_by_key(thread_ptr) == old(krnl).thr_mp.lock_id_by_key(thread_ptr)) by {
            lock_id_fields_eq_imply_eq(); reveal(LockedMap::typed_lock_map_aligned);
        };
        assert(drop_endpoint_descriptor_eof_transition_framing(locked, *krnl, thread_ptr, endpoint_ptr, index)) by { reveal(drop_endpoint_descriptor_eof_transition_framing); };
        drop_endpoint_descriptor_eof(locked, *krnl, thread_ptr, endpoint_ptr, index);
    }
    krnl.wunlock_endpoint(endpoint_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm));
    proof { assert(lctx.endpoint_lock_map() =~= old(lctx).endpoint_lock_map()); }
    false
}
} // verus!
