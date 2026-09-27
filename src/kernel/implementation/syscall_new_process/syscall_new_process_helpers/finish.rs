use vstd::prelude::*;
use vstd::assert_seqs_equal;
use crate::*;
#[cfg(feature = "split-crates")]
use veriflat_kernel_core::{attach_endpoint_reference_and_unlock, create_thread_from_staged_page_merged, kernel_u_new_thread_changed};
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::create_thread_from_staged_page::{create_thread_from_staged_page_merged, kernel_u_new_thread_changed};
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::attach_endpoint_reference_and_unlock::attach_endpoint_reference_and_unlock;

verus! {
#[verifier::spinoff_prover]
pub(in super::super) fn create_initial_thread_and_finish_new_process(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    cpu_id: CpuId, container_ptr: RwLockContainerPtr, child_ptr: RwLockProcessPtr,
    current_thread_ptr: RwLockThreadPtr, scheduler_ptr: RwLockSchedulerPtr,
    endpoint: Option<RwLockEndpointPtr>, endpoint_index: EndpointIdx,
    source_pagetable_ptr: RwLockPageTableRoot, target_pagetable_ptr: RwLockPageTableRoot, iommu_table: Option<RwLockPageTableRoot>,
    cpu_lock_perm: Tracked<LockPerm>, container_lock_perm: Tracked<LockPerm>, child_lock_perm: Tracked<LockPerm>,
    current_thread_lock_perm: Tracked<LockPerm>, scheduler_lock_perm: Tracked<LockPerm>, endpoint_lock_perm: Tracked<Option<LockPerm>>,
    source_pagetable_lock_perm: Tracked<LockPerm>, target_pagetable_lock_perm: Tracked<LockPerm>,
    iommu_table_lock_perm: Tracked<Option<LockPerm>>, initial_regs: &Registers,
) -> (new_thread_ptr: RwLockThreadPtr)
    requires
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, source_pagetable_ptr, old(krnl).pt_mp.spec_index(source_pagetable_ptr).view()),
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, target_pagetable_ptr, old(krnl).pt_mp.spec_index(target_pagetable_ptr).view()),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        old(krnl).irt.owners() == old(steps).snapshot_k().irt.owners(),
        old(krnl).irt.iommu_roots() == old(steps).snapshot_k().irt.iommu_roots(),
        old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
        old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        old(lctx).page_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_MAJOR),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom() =~= set![container_ptr],
        old(lctx).process_lock_map().dom() =~= set![child_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        endpoint is None ==> old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom() =~= set![scheduler_ptr],
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr, target_pagetable_ptr],
        iommu_table is None ==> old(lctx).iommu_table_lock_map().dom().is_empty(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        cpu_lock_perm.view().state() is WriteLock,
        cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
        container_lock_perm.view().state() is WriteLock,
        container_lock_perm.view().thread_id() == old(lctx).thread_id(),
        container_lock_perm.view().lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(child_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), child_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(child_ptr).being_killed(),
        !old(krnl).prc_mp.spec_index(child_ptr).view().zombie,
        old(krnl).prc_mp.spec_index(child_ptr).view_rodata().view().owning_container == container_ptr,
        child_lock_perm.view().state() is WriteLock,
        child_lock_perm.view().thread_id() == old(lctx).thread_id(),
        child_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(child_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state is RUNNING,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 1,
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).sched_mp.dom().contains(scheduler_ptr),
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), scheduler_ptr, TypedLockMode::Write),
        !old(krnl).sched_mp.spec_index(scheduler_ptr).being_killed(),
        scheduler_lock_perm.view().state() is WriteLock,
        scheduler_lock_perm.view().thread_id() == old(lctx).thread_id(),
        scheduler_lock_perm.view().lock_id() == old(krnl).sched_mp.spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
        endpoint is Some ==> {
            let endpoint_ptr = endpoint->Some_0;
            let endpoint_owner = old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container;
            &&& edp_idx_valid(endpoint_index)
            &&& old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr]
            &&& old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.wf()
            &&& old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == endpoint
            &&& old(krnl).ep_mp.dom().contains(endpoint_ptr)
            &&& old(krnl).ep_mp.spec_index(endpoint_ptr).is_init()
            &&& typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write)
            &&& !old(krnl).ep_mp.spec_index(endpoint_ptr).being_killed()
            &&& old(krnl).ctn_mp.dom().contains(endpoint_owner)
            &&& endpoint_owner == container_ptr || old(krnl).ctn_mp.spec_index(endpoint_owner).view_ghost().subtree_set.view().contains(container_ptr)
            &&& endpoint_lock_perm.view() is Some
            &&& endpoint_lock_perm.view()->Some_0.state() is WriteLock
            &&& endpoint_lock_perm.view()->Some_0.thread_id() == old(lctx).thread_id()
            &&& endpoint_lock_perm.view()->Some_0.lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id
        },
        source_pagetable_ptr != target_pagetable_ptr,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Write),
        source_pagetable_lock_perm.view().state() is WriteLock,
        source_pagetable_lock_perm.view().thread_id() == old(lctx).thread_id(),
        source_pagetable_lock_perm.view().lock_id() == old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(target_pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable_ptr, TypedLockMode::Write),
        target_pagetable_lock_perm.view().state() is WriteLock,
        target_pagetable_lock_perm.view().thread_id() == old(lctx).thread_id(),
        target_pagetable_lock_perm.view().lock_id() == old(krnl).pt_mp.spec_index(target_pagetable_ptr).locking_thread()->Write_lock_id,
        iommu_table is Some ==> {
            let iommu_table_ptr = iommu_table->Some_0;
            &&& old(lctx).iommu_table_lock_map().dom() =~= set![iommu_table_ptr]
            &&& old(krnl).prc_mp.spec_index(child_ptr).view().iommu_table == iommu_table
            &&& old(krnl).it_mp.dom().contains(iommu_table_ptr)
            &&& typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write)
            &&& old(krnl).it_mp.spec_index(iommu_table_ptr).view().is_empty()
            &&& iommu_table_lock_perm.view() is Some
            &&& iommu_table_lock_perm.view()->Some_0.state() is WriteLock
            &&& iommu_table_lock_perm.view()->Some_0.thread_id() == old(lctx).thread_id()
            &&& iommu_table_lock_perm.view()->Some_0.lock_id() == old(krnl).it_mp.spec_index(iommu_table_ptr).locking_thread()->Write_lock_id
        },
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
        final(steps).nonlock_view().subrange(0, old(steps).nonlock_view().len() as int) == old(steps).nonlock_view(),
        final(steps).nonlock_view().last().new_u == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        kernel_u_new_thread_changed(
            final(steps).nonlock_view().last().old_u, final(steps).nonlock_view().last().new_u, child_ptr, current_thread_ptr, container_ptr,
            new_thread_ptr, *initial_regs, endpoint,
        ),
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(krnl).thr_mp.dom().contains(new_thread_ptr),
        final(krnl).thr_mp.spec_index(new_thread_ptr).view().state is SCHEDULED,
        final(krnl).thr_mp.spec_index(new_thread_ptr).view().owning_proc == child_ptr,
        final(krnl).thr_mp.spec_index(new_thread_ptr).view().owning_container == container_ptr,
        endpoint is Some ==> final(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.wf(),
        endpoint is Some ==> final(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.spec_index(0) == endpoint,
        iommu_table is Some ==> final(krnl).prc_mp.dom().contains(child_ptr) && final(krnl).prc_mp.spec_index(child_ptr).view().iommu_table == iommu_table,
        iommu_table is Some ==> final(krnl).it_mp.dom().contains(iommu_table->Some_0) && final(krnl).it_mp.spec_index(iommu_table->Some_0).view().is_empty(),
{
    let tracked cpu_lock_perm = cpu_lock_perm.get();
    let tracked container_lock_perm = container_lock_perm.get();
    let tracked child_lock_perm = child_lock_perm.get();
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked scheduler_lock_perm = scheduler_lock_perm.get();
    let tracked endpoint_lock_perm = endpoint_lock_perm.get();
    let tracked source_pagetable_lock_perm = source_pagetable_lock_perm.get();
    let tracked target_pagetable_lock_perm = target_pagetable_lock_perm.get();
    let tracked iommu_table_lock_perm = iommu_table_lock_perm.get();
    let (thread_page_ptr, Tracked(thread_page_lock_perm)) = allocate_free_4k_page(krnl, current_thread_ptr, container_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&current_thread_lock_perm));
    proof { enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); }
    let (new_thread_ptr, Tracked(new_thread_lock_perm)) = create_thread_from_staged_page_merged(
        krnl, thread_page_ptr, child_ptr, current_thread_ptr, container_ptr, scheduler_ptr, Tracked(&mut *lctx),
        Tracked(&thread_page_lock_perm), Tracked(&child_lock_perm), Tracked(&current_thread_lock_perm),
        Tracked(&scheduler_lock_perm), initial_regs,
    );
    proof { if iommu_table is Some { assert(krnl.prc_mp.spec_index(child_ptr).view().iommu_table == iommu_table) by { reveal(process_iommu_table_match); }; } }
    match endpoint {
        Some(endpoint_ptr) => {
            let tracked endpoint_lock_perm = endpoint_lock_perm.tracked_unwrap();
            let ghost created_k = *krnl;
            proof {
                assert(created_k.thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.view()
                    == Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat, |i: int| None)) by { reveal(kernel_new_thread_fields); };
                assert(krnl.ctn_mp.dom().contains(krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container)) by { reveal(container_endpoint_wf); };
                assert({
                    ||| krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container == container_ptr
                    ||| krnl.ctn_mp.spec_index(krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container).view_ghost().subtree_set.view().contains(container_ptr)
                }) by { reveal(container_thread_endpoint_wf); };
            }
            attach_endpoint_reference_and_unlock(krnl, new_thread_ptr, endpoint_ptr, current_thread_ptr, Tracked(&mut *lctx), Tracked(new_thread_lock_perm), Tracked(endpoint_lock_perm));
        },
        None => krnl.wunlock_thread(new_thread_ptr, Tracked(&mut *lctx), Tracked(new_thread_lock_perm)),
    }
    krnl.wunlock_process(child_ptr, Tracked(&mut *lctx), Tracked(child_lock_perm));
    krnl.wunlock_pagetable(target_pagetable_ptr, Tracked(&mut *lctx), Tracked(target_pagetable_lock_perm));
    krnl.wunlock_pagetable(source_pagetable_ptr, Tracked(&mut *lctx), Tracked(source_pagetable_lock_perm));
    krnl.wunlock_page(page_ptr2page_index(thread_page_ptr), Tracked(&mut *lctx), Tracked(thread_page_lock_perm));
    krnl.wunlock_scheduler(scheduler_ptr, Tracked(&mut *lctx), Tracked(scheduler_lock_perm));
    krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
    proof {
        assert(!krnl.ctn_mp.spec_index(container_ptr).view().owned_processes.view().is_empty()) by { reveal(container_process_wf); };
    }
    krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
    krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    if let Some(iommu_table_ptr) = iommu_table {
        let tracked iommu_table_lock_perm = iommu_table_lock_perm.tracked_unwrap();
        krnl.wunlock_iommu_table(iommu_table_ptr, Tracked(&mut *lctx), Tracked(iommu_table_lock_perm));
        proof { no_locks_held_imply_all_objects_unlocked(&*krnl, &*lctx); }
    }
    proof {
        if let Some(endpoint_ptr) = endpoint {
            assert(krnl.thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.wf()) by { thread_perms_wf_at(krnl.thr_mp, new_thread_ptr); };
            assert(krnl.thr_mp.spec_index(new_thread_ptr).view().owning_proc == child_ptr && krnl.thr_mp.spec_index(new_thread_ptr).view().owning_container == container_ptr) by { reveal(process_thread_wf); };
            assert(kernel_new_thread_fields(&steps.snapshot_k(), krnl, child_ptr, current_thread_ptr, container_ptr, new_thread_ptr, *initial_regs, endpoint)) by {
                reveal(kernel_new_thread_fields);
                reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
                assert_seqs_equal!(
                    krnl.thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.view()
                        == Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat, |i: int| if i == 0 { Some(endpoint_ptr) } else { None }),
                    i => {}
                );
            };
        } else {
            assert(kernel_new_thread_fields(&steps.snapshot_k(), krnl, child_ptr, current_thread_ptr, container_ptr, new_thread_ptr, *initial_regs, endpoint)) by {
                reveal(kernel_new_thread_fields); reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
            };
        }
        steps.end_kernel_step_new_thread(&*krnl, &*lctx, child_ptr, current_thread_ptr, container_ptr, new_thread_ptr, *initial_regs, endpoint);
    }
    new_thread_ptr
}
}
