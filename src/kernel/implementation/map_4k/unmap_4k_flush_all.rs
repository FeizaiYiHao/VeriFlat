use vstd::prelude::*;
use crate::*;
use super::unmap_4k_tlb::*;
use super::unmap_4k_trace::unmap_4k_tlb_flush_step_pre_from_k;

verus! {
pub fn flush_pagetable_tlbs(krnl: &mut KernelK, pagetable: RwLockPageTableRoot, cr3: PageTableRoot, pcid: Pcid, local_cpu: CpuId, thread_ptr: RwLockThreadPtr, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_perm: Tracked<&LockPerm>)
    requires
        old(steps).snapshot_k() == *old(krnl),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
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
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        old(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        page_ptr_valid(cr3),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc).view().zombie,
        old(krnl).prc_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc).view().pagetable == pagetable,
        old(krnl).prc_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc).view_rodata().view().pcid == pcid,
        old(krnl).prc_mp.dom().contains(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc),
    ensures
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len() <= old(steps).view().len() + NUM_CPUS,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        // Every flush step clears one cpu's TLB for `pcid` while the caller's held objects keep their entry projection.
        forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==> {
            let old_u = final(steps).view()[j].old_u;
            let entry_u = kernel_k_to_kernel_u(*old(krnl));
            let process_ptr = old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc;
            let container_ptr = old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container;
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
        final(krnl).cpu_published[local_cpu as int].view() == (cr3, pcid),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> final(krnl).cpu_arr.spec_index(held_cpu_id).view().view() == old(krnl).cpu_arr.spec_index(held_cpu_id).view().view(),
        old(steps).nonlock_view().len() <= final(steps).nonlock_view().len() <= old(steps).nonlock_view().len() + NUM_CPUS,
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_threads_unchanged(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx)),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
        final(krnl).cpu_arr.spec_index(local_cpu).view().view() == old(krnl).cpu_arr.spec_index(local_cpu).view().view(),
        final(krnl).cpu_arr.spec_index(local_cpu).view().locking_thread() == old(krnl).cpu_arr.spec_index(local_cpu).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(local_cpu).view().being_killed() == old(krnl).cpu_arr.spec_index(local_cpu).view().being_killed(),
        final(krnl).cpu_arr.spec_index(local_cpu).view().killer_info() == old(krnl).cpu_arr.spec_index(local_cpu).view().killer_info(),
        pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pagetable, final(krnl).pt_mp.spec_index(pagetable).view()),
{
    assert(held_containers_unchanged(krnl.ctn_mp, krnl.ctn_mp, lctx) && held_processes_unchanged(krnl.prc_mp, krnl.prc_mp, lctx) && held_threads_unchanged(krnl.thr_mp, krnl.thr_mp, lctx)
        && held_pages_unchanged(krnl.pg_arr, krnl.pg_arr, lctx) && held_pagetables_unchanged(krnl.pt_mp, krnl.pt_mp, lctx) && held_iommu_tables_unchanged(krnl.it_mp, krnl.it_mp, lctx)) by {
        held_kernel_objects_unchanged_reflexive(krnl, lctx);
    };
    let mut cpu_id = 0usize;
    while cpu_id < NUM_CPUS
        invariant
            steps.snapshot_k() == *krnl,
            old(steps).view().len() <= steps.view().len() <= old(steps).view().len() + cpu_id,
            forall|j: int| #![trigger steps.view()[j]] 0 <= j < old(steps).view().len() ==> steps.view()[j] == old(steps).view()[j],
            forall|j: int| #![trigger steps.view()[j]] old(steps).view().len() <= j < steps.view().len() ==> {
                let old_u = steps.view()[j].old_u;
                let entry_u = kernel_k_to_kernel_u(*old(krnl));
                let process_ptr = old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc;
                let container_ptr = old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container;
                &&& kernel_u_cpu_tlb_cleared(old_u, steps.view()[j].new_u, pcid)
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
            cpu_id <= NUM_CPUS,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.kernel_view_locking_state() is Acquire,
            index_valid(NUM_CPUS, local_cpu),
            lctx.cpu_id() == local_cpu,
            typed_lock_map_contains_mode(lctx.cpu_lock_map(), local_cpu, TypedLockMode::Write),
            cpu_perm.view().state() is WriteLock,
            cpu_perm.view().thread_id() == lctx.thread_id(),
            cpu_perm.view().lock_id() == krnl.cpu_arr.spec_index(local_cpu).view().locking_thread()->Write_lock_id,
            krnl.cpu_arr.spec_index(local_cpu).view().view().view().current_cr3 == cr3,
            krnl.cpu_arr.spec_index(local_cpu).view().view().view().current_pcid == pcid,
            krnl.cpu_published[local_cpu as int].view() == (cr3, pcid),
            krnl.pt_mp.dom().contains(pagetable),
            typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
            krnl.pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
            krnl.pt_mp.spec_index(pagetable).view().cr3 == cr3,
            page_ptr_valid(cr3),
            pcid_valid(pcid),
            pcid != KERNEL_DEFAULT_PCID,
            lctx.pcid_needflush_lock_map().dom().is_empty(),
            lctx.cpu_offline_flag_lock_map().dom().is_empty(),
            forall|held_cpu_id: CpuId| #![trigger lctx.cpu_lock_map().dom().contains(held_cpu_id)] lctx.cpu_lock_map().dom().contains(held_cpu_id) ==> !(krnl.cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.thread_id() == old(lctx).thread_id(),
            old(steps).nonlock_view().len() <= steps.nonlock_view().len() <= old(steps).nonlock_view().len() + cpu_id,
            held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx)),
            held_threads_unchanged(old(krnl).thr_mp, krnl.thr_mp, old(lctx)),
            held_pagetables_unchanged(old(krnl).pt_mp, krnl.pt_mp, old(lctx)),
            held_iommu_tables_unchanged(old(krnl).it_mp, krnl.it_mp, old(lctx)),
            held_pages_unchanged(old(krnl).pg_arr, krnl.pg_arr, old(lctx)),
            forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> krnl.cpu_arr.spec_index(held_cpu_id).view().view() == old(krnl).cpu_arr.spec_index(held_cpu_id).view().view(),
            old(krnl).thr_mp.dom().contains(thread_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).process_lock_map(), old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).container_lock_map(), old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container, TypedLockMode::Write),
            !old(krnl).prc_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc).view().zombie,
            old(krnl).prc_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc).view().pagetable == pagetable,
            old(krnl).prc_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc).view_rodata().view().pcid == pcid,
            old(krnl).cpu_arr.spec_index(local_cpu).view().view().view().current_thread == Some(thread_ptr),
            old(krnl).prc_mp.dom().contains(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc),
            old(krnl).pt_mp.dom().contains(pagetable),
            old(krnl).inv(),
            krnl.cpu_arr.spec_index(local_cpu).view().view() == old(krnl).cpu_arr.spec_index(local_cpu).view().view(),
            krnl.cpu_arr.spec_index(local_cpu).view().locking_thread() == old(krnl).cpu_arr.spec_index(local_cpu).view().locking_thread(),
            krnl.cpu_arr.spec_index(local_cpu).view().being_killed() == old(krnl).cpu_arr.spec_index(local_cpu).view().being_killed(),
            krnl.cpu_arr.spec_index(local_cpu).view().killer_info() == old(krnl).cpu_arr.spec_index(local_cpu).view().killer_info(),
            forall|c: CpuId| #![trigger krnl.cpu_tlb.spec_index((c, pcid))] index_valid(cpu_id, c)
                && (!krnl.pcid_needflush.spec_index(c, pcid).view().needflush || krnl.cpu_arr.spec_index(c).view().view().view().current_pcid == pcid)
                && krnl.cpu_arr.spec_index(c).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some && krnl.cpu_arr.spec_index(c).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr == pagetable
                    ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(krnl.cpu_tlb.spec_index((c, pcid)), krnl.pt_mp.spec_index(pagetable).view()),
        decreases NUM_CPUS - cpu_id,
    {
        proof { unmap_4k_tlb_flush_step_pre_from_k(&*krnl, &*old(krnl), &*lctx, &*old(lctx), local_cpu, thread_ptr, pagetable); }
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
        cpu_id = cpu_id + 1;
    }
    assert(pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pagetable, krnl.pt_mp.spec_index(pagetable).view())) by { reveal(cpu_dirty_map_contains_pagetable_pcid_match); };
}
}
