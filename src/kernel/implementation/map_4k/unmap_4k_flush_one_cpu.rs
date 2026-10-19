use vstd::prelude::*;
use crate::*;
use super::unmap_4k_tlb::*;
use super::unmap_4k_trace::unmap_4k_tlb_flush_step_pre_from_k;

verus! {
/// Flushes `pcid` on cpu `cpu_id` under its needflush lock and records the TLB step. The recorded step keeps the entry
/// projection of the thread, process, and container that `held` write-locks in `entry`, and the `pagetable` TLB subset
/// fact extends from the cpus below `cpu_id` to `cpu_id`.
pub(super) fn flush_pagetable_tlb_on_cpu(krnl: &mut KernelK, pagetable: RwLockPageTableRoot, cr3: PageTableRoot, pcid: Pcid, cpu_id: usize, local_cpu: CpuId, thread_ptr: RwLockThreadPtr,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_perm: Tracked<&LockPerm>, Ghost(entry): Ghost<KernelK>, Ghost(held): Ghost<LocalContext>)
    requires
        old(steps).snapshot_k() == *old(krnl),
        old(krnl).inv(),
        entry.inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        typed_lock_maps_unchanged(&held, old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        index_valid(NUM_CPUS, local_cpu),
        old(lctx).cpu_id() == local_cpu,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), local_cpu, TypedLockMode::Write),
        cpu_perm.view().state() is WriteLock,
        cpu_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(local_cpu).view().locking_thread()->Write_lock_id,
        old(krnl).cpu_arr.spec_index(local_cpu).view().view().view().current_cr3 == cr3,
        old(krnl).cpu_arr.spec_index(local_cpu).view().view().view().current_pcid == pcid,
        old(krnl).cpu_published[local_cpu as int].view() == (cr3, pcid),
        old(krnl).cpu_arr.spec_index(local_cpu).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).pt_mp.dom().contains(pagetable),
        old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        old(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        page_ptr_valid(cr3),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        entry.thr_mp.dom().contains(thread_ptr),
        entry.prc_mp.dom().contains(entry.thr_mp.spec_index(thread_ptr).view().owning_proc),
        entry.prc_mp.spec_index(entry.thr_mp.spec_index(thread_ptr).view().owning_proc).view().pagetable == pagetable,
        entry.pt_mp.dom().contains(pagetable),
        typed_lock_map_contains_mode(held.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(held.process_lock_map(), entry.thr_mp.spec_index(thread_ptr).view().owning_proc, TypedLockMode::Write),
        typed_lock_map_contains_mode(held.container_lock_map(), entry.thr_mp.spec_index(thread_ptr).view().owning_container, TypedLockMode::Write),
        typed_lock_map_contains_mode(held.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        held_threads_unchanged(entry.thr_mp, old(krnl).thr_mp, &held),
        held_processes_unchanged(entry.prc_mp, old(krnl).prc_mp, &held),
        held_pagetables_unchanged(entry.pt_mp, old(krnl).pt_mp, &held),
        forall|c: CpuId| #![trigger old(krnl).cpu_tlb.spec_index((c, pcid))] index_valid(cpu_id, c)
            && (!old(krnl).pcid_needflush.spec_index(c, pcid).view().needflush || old(krnl).cpu_arr.spec_index(c).view().view().view().current_pcid == pcid)
            && old(krnl).cpu_arr.spec_index(c).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some && old(krnl).cpu_arr.spec_index(c).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr == pagetable
                ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(old(krnl).cpu_tlb.spec_index((c, pcid)), old(krnl).pt_mp.spec_index(pagetable).view()),
    ensures
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len() <= old(steps).view().len() + 1,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==> {
            let old_u = final(steps).view()[j].old_u;
            let entry_u = kernel_k_to_kernel_u(entry);
            let process_ptr = entry.thr_mp.spec_index(thread_ptr).view().owning_proc;
            let container_ptr = entry.thr_mp.spec_index(thread_ptr).view().owning_container;
            &&& kernel_u_cpu_tlb_cleared(old_u, final(steps).view()[j].new_u, pcid)
            &&& old_u.cpu_array[local_cpu as int].lock_state is WriteLocked
            &&& old_u.cpu_array[local_cpu as int].current_thread == Some(thread_ptr)
            &&& old_u.thread_map.dom().contains(thread_ptr)
            &&& old_u.thread_map[thread_ptr] == entry_u.thread_map[thread_ptr]
            &&& old_u.process_map.dom().contains(process_ptr)
            &&& old_u.process_map[process_ptr].lock_state == entry_u.process_map[process_ptr].lock_state
            &&& old_u.process_map[process_ptr].pagetable == entry_u.process_map[process_ptr].pagetable
            &&& old_u.process_map[process_ptr].pcid == entry_u.process_map[process_ptr].pcid
            &&& old_u.container_map.dom().contains(container_ptr)
            &&& old_u.container_map[container_ptr].lock_state is WriteLocked
            &&& old_u.kernel_l4_end == entry_u.kernel_l4_end
        },
        old(steps).nonlock_view().len() <= final(steps).nonlock_view().len() <= old(steps).nonlock_view().len() + 1,
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(krnl).cpu_published[local_cpu as int].view() == old(krnl).cpu_published[local_cpu as int].view(),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> final(krnl).cpu_arr.spec_index(held_cpu_id).view().view() == old(krnl).cpu_arr.spec_index(held_cpu_id).view().view(),
        final(krnl).cpu_arr.spec_index(local_cpu).view().view() == old(krnl).cpu_arr.spec_index(local_cpu).view().view(),
        final(krnl).cpu_arr.spec_index(local_cpu).view().locking_thread() == old(krnl).cpu_arr.spec_index(local_cpu).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(local_cpu).view().being_killed() == old(krnl).cpu_arr.spec_index(local_cpu).view().being_killed(),
        final(krnl).cpu_arr.spec_index(local_cpu).view().killer_info() == old(krnl).cpu_arr.spec_index(local_cpu).view().killer_info(),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_threads_unchanged(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx)),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
        forall|c: CpuId| #![trigger final(krnl).cpu_tlb.spec_index((c, pcid))] index_valid((cpu_id + 1) as usize, c)
            && (!final(krnl).pcid_needflush.spec_index(c, pcid).view().needflush || final(krnl).cpu_arr.spec_index(c).view().view().view().current_pcid == pcid)
            && final(krnl).cpu_arr.spec_index(c).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some && final(krnl).cpu_arr.spec_index(c).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr == pagetable
                ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(final(krnl).cpu_tlb.spec_index((c, pcid)), final(krnl).pt_mp.spec_index(pagetable).view()),
{
    proof { unmap_4k_tlb_flush_step_pre_from_k(&*krnl, &entry, &*lctx, &held, local_cpu, thread_ptr, pagetable); }
    let Tracked(needflush_perm) = krnl.wlock_pcid_needflush(cpu_id, pcid, Tracked(&mut *lctx));
    let published = mark_pcid_needflush_and_load(krnl, cpu_id, pcid, Tracked(&mut *lctx), Tracked(&needflush_perm));
    if cpu_id == local_cpu {
        flush_local_pcid_and_clear(krnl, cpu_id, pcid, cr3, Tracked(&*lctx), Tracked(&needflush_perm), cpu_perm);
    } else if published.0 == cr3 && published.1 == pcid {
        flush_remote_pcid_and_clear(krnl, cpu_id, pcid, Tracked(&*lctx), Tracked(&needflush_perm));
    }
    assert((!krnl.pcid_needflush.spec_index(cpu_id, pcid).view().needflush || krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid)
        && krnl.cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some
        && krnl.cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr == pagetable
        ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(krnl.cpu_tlb.spec_index((cpu_id, pcid)), krnl.pt_mp.spec_index(pagetable).view())) by {
        cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), cpu_id); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id);
        process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap());
    };
    krnl.wunlock_pcid_needflush(cpu_id, pcid, Tracked(&mut *lctx), Tracked(needflush_perm));
    proof {
        assert(typed_lock_maps_unchanged(old(lctx), lctx)) by { map_insert_remove_absent_lemma(old(lctx).pcid_needflush_lock_map(), (cpu_id, pcid), TypedHeldLock { lock_id: krnl.pcid_needflush.lock_id_by_index(cpu_id, pcid), mode: TypedLockMode::Write }); };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by {
            broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
        };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        krnl.kernel_step_boundary_cpu_tlb_updated(&mut *lctx, &mut *steps, cpu_id, pcid, cpu_id == local_cpu || (published.0 == cr3 && published.1 == pcid));
    }
}
}
