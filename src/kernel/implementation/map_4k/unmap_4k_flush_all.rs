use vstd::prelude::*;
use crate::*;
use super::unmap_4k_tlb::*;

verus! {
pub fn flush_pagetable_tlbs(krnl: &mut KernelK, pagetable: RwLockPageTableRoot, cr3: PageTableRoot, pcid: Pcid, local_cpu: CpuId, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_perm: Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
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
        old(krnl).pt_mp.dom().contains(pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        old(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        page_ptr_valid(cr3),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).held_lock_majors_lt(PCID_NEEDFLUSH_LOCK_MAJOR),
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
    ensures
        final(krnl).cpu_published[local_cpu as int].view() == (cr3, pcid),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).lock_id_set() == old(lctx).lock_id_set(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).held_lock_majors_lt(PCID_NEEDFLUSH_LOCK_MAJOR),
        final(steps).steps == old(steps).steps,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_threads_unchanged(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx)),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
        final(krnl).cpu_arr.spec_index(local_cpu).view().view() == old(krnl).cpu_arr.spec_index(local_cpu).view().view(),
        final(krnl).cpu_arr.spec_index(local_cpu).view().locking_thread() == old(krnl).cpu_arr.spec_index(local_cpu).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(local_cpu).view().being_killed() == old(krnl).cpu_arr.spec_index(local_cpu).view().being_killed(),
        pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pagetable, final(krnl).pt_mp.spec_index(pagetable).view()),
{
    assert(held_containers_unchanged(krnl.ctn_mp, krnl.ctn_mp, lctx) && held_processes_unchanged(krnl.prc_mp, krnl.prc_mp, lctx) && held_threads_unchanged(krnl.thr_mp, krnl.thr_mp, lctx) && held_pages_unchanged(krnl.pg_arr, krnl.pg_arr, lctx) && held_pagetables_unchanged(krnl.pt_mp, krnl.pt_mp, lctx) && held_iommu_tables_unchanged(krnl.it_mp, krnl.it_mp, lctx)) by { held_kernel_objects_unchanged_reflexive(krnl, lctx); };
    let mut cpu_id = 0usize;
    while cpu_id < NUM_CPUS
        invariant
            cpu_id <= NUM_CPUS,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lock_id_set_aligned(lctx),
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
            lctx.held_lock_majors_lt(PCID_NEEDFLUSH_LOCK_MAJOR),
            steps.snap_shot == kernel_k_to_kernel_u(*krnl),
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.lock_id_set() == old(lctx).lock_id_set(),
            lctx.thread_id() == old(lctx).thread_id(),
            steps.steps == old(steps).steps,
            held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx)),
            held_threads_unchanged(old(krnl).thr_mp, krnl.thr_mp, old(lctx)),
            held_pagetables_unchanged(old(krnl).pt_mp, krnl.pt_mp, old(lctx)),
            held_iommu_tables_unchanged(old(krnl).it_mp, krnl.it_mp, old(lctx)),
            held_pages_unchanged(old(krnl).pg_arr, krnl.pg_arr, old(lctx)),
            krnl.cpu_arr.spec_index(local_cpu).view().view() == old(krnl).cpu_arr.spec_index(local_cpu).view().view(),
            krnl.cpu_arr.spec_index(local_cpu).view().locking_thread() == old(krnl).cpu_arr.spec_index(local_cpu).view().locking_thread(),
            krnl.cpu_arr.spec_index(local_cpu).view().being_killed() == old(krnl).cpu_arr.spec_index(local_cpu).view().being_killed(),
            forall|c: CpuId| #![trigger krnl.cpu_tlb.spec_index((c, pcid))] index_valid(cpu_id, c)
                && (!krnl.pcid_needflush.spec_index(c, pcid).view().needflush || krnl.cpu_arr.spec_index(c).view().view().view().current_pcid == pcid)
                && krnl.cpu_arr.spec_index(c).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some
                && krnl.cpu_arr.spec_index(c).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr == pagetable
                ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(krnl.cpu_tlb.spec_index((c, pcid)), krnl.pt_mp.spec_index(pagetable).view()),
        decreases NUM_CPUS - cpu_id,
    {
        let ghost iteration_start = *krnl;
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
            ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(krnl.cpu_tlb.spec_index((cpu_id, pcid)), krnl.pt_mp.spec_index(pagetable).view())) by { reveal(cpu_array_wf); reveal(process_cpu_wf); reveal(process_pagetable_match); };
        krnl.wunlock_pcid_needflush(cpu_id, pcid, Tracked(&mut *lctx), Tracked(needflush_perm));
        proof {
            assert(typed_lock_maps_unchanged(old(lctx), lctx)) by { map_insert_remove_absent_lemma(old(lctx).pcid_needflush_lock_map(), (cpu_id, pcid), TypedHeldLock { lock_id: krnl.pcid_needflush.lock_id_by_index(cpu_id, pcid), mode: TypedLockMode::Write }); };
            assert(lctx.held_lock_majors_lt(PCID_NEEDFLUSH_LOCK_MAJOR)) by { broadcast use held_lock_major_lt_preserved_for_typed_maps_unchanged; };
            assert(kernel_k_to_kernel_u(iteration_start) == kernel_k_to_kernel_u(*krnl)) by {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(&iteration_start, krnl);
            };
            krnl.kernel_step_boundary(&mut *lctx, &mut *steps);
        }
        cpu_id = cpu_id + 1;
    }
    assert(pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pagetable, krnl.pt_mp.spec_index(pagetable).view())) by { reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(cpu_array_wf); };
}
}
