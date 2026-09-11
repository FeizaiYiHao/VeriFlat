use vstd::prelude::*;
use crate::*;
#[cfg(feature = "split-crates")]
use veriflat_kernel_core::kernel_u_new_thread_changed;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::create_thread_from_staged_page::kernel_u_new_thread_changed;
use super::syscall_new_process_spec::kernel_u_new_process_shared;
use super::syscall_new_process_with_iommu_helpers::commit_new_process_with_iommu_and_endpoint;

verus! {

pub fn syscall_new_process_with_iommu_and_endpoint(
    krnl: &mut KernelK,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>,
    cpu_id: CpuId,
    va: VAddr,
    range: usize,
    endpoint_index: EndpointIdx,
    initial_regs: &Registers,
) -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        edp_idx_valid(endpoint_index),
        old(krnl).inv(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state == CpuState::Running,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        old(steps).steps.len() == 0,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(steps).steps.len() <= range + 2,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(lctx).no_locks_held(),
        !(ret is SuccessThreeUsize) ==> final(steps).steps.len() == 0,
        ret is SuccessThreeUsize ==> {
            let parent_ptr = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process->Some_0;
            let current_thread_ptr = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0;
            let child_ptr = ret->SuccessThreeUsize_value1;
            let iommu_table_ptr = ret->SuccessThreeUsize_value2;
            let thread_ptr = ret->SuccessThreeUsize_value3;
            let source_range = VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) };
            &&& range > 0
            &&& final(steps).steps.len() == range + 2
            &&& final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(krnl))
            &&& source_range.wf()
            &&& old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.wf()
            &&& old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) is Some
            &&& kernel_u_create_process_with_iommu_changed(final(steps).steps.spec_index(0).old_u, final(steps).steps.spec_index(0).new_u, parent_ptr, child_ptr)
            &&& kernel_u_new_process_shared(final(steps).steps.spec_index(0).new_u, final(steps).steps.spec_index(source_range.len as int).new_u, parent_ptr, child_ptr, &source_range)
            &&& kernel_u_new_thread_changed(final(steps).steps.last().old_u, final(steps).steps.last().new_u, child_ptr)
            &&& final(krnl).prc_mp.dom().contains(child_ptr)
            &&& final(krnl).prc_mp.spec_index(child_ptr).view().iommu_table == Some(iommu_table_ptr)
            &&& final(krnl).it_mp.dom().contains(iommu_table_ptr)
            &&& final(krnl).it_mp.spec_index(iommu_table_ptr).view().is_empty()
            &&& final(krnl).thr_mp.dom().contains(thread_ptr)
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().state is SCHEDULED
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == child_ptr
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.wf()
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.spec_index(0) == old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index)
        },
        ret is SuccessThreeUsize || ret is Error || ret is ErrorContainerKilled || ret is ErrorNoPcid || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorNoQuota,
{
    proof { reveal(KernelK::all_objects_unlocked); }
    if range == 0
        || range > usize::MAX / 4096usize
        || range > (usize::MAX - 6usize) / 3usize
        || !va_4k_valid(va)
    {
        proof { enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); steps.end_kernel_step(&*krnl, &*lctx); }
        return RetValueType::Error;
    }
    let span = range * 4096usize;
    if va >= usize::MAX - span || !va_4k_range_valid(va, range) {
        proof { enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); steps.end_kernel_step(&*krnl, &*lctx); }
        return RetValueType::Error;
    }
    let source_range = VaRange4K::new(va, range);
    proof {
        assert(krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process is Some && krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread is Some) by { reveal(cpu_array_wf); };
    }
    let Tracked(cpu_lock_perm) = krnl.wlock_cpu(cpu_id, Tracked(&mut *lctx));
    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    let parent_ptr = cpu.current_process().unwrap();
    let current_thread_ptr = cpu.current_thread().unwrap();
    let container_ptr = cpu.owning_container();
    proof {
        assert(krnl.prc_mp.dom().contains(parent_ptr) && krnl.prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == container_ptr) by { reveal(process_cpu_wf); };
        assert(krnl.ctn_mp.dom().contains(container_ptr) && krnl.ctn_mp.spec_index(container_ptr).view().owned_processes.view().contains(parent_ptr)) by { reveal(container_process_wf); };
        assert(krnl.thr_mp.dom().contains(current_thread_ptr) && krnl.thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }) && krnl.thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_ptr && krnl.thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr) by { reveal(thread_cpu_wf); reveal(process_thread_wf); };
    }
    let container_res = krnl.wlock_container_unless_killed(container_ptr, Tracked(&mut *lctx));
    if let (false, _) = container_res {
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof { steps.end_kernel_step(&*krnl, &*lctx); }
        return RetValueType::ErrorContainerKilled;
    }
    let Tracked(container_lock_perm) = container_res.1.unwrap();
    let container_rodata = krnl.ctn_mp.borrow_rodata(container_ptr);
    let pcid_allocator_ptr = container_rodata.borrow().pcid_allocator;
    let scheduler_ptr = container_rodata.borrow().scheduler;
    let allocator_ptr = container_rodata.borrow().allocator_ptr_4k;
    proof {
        assert(krnl.pcid_allc_mp.dom().contains(pcid_allocator_ptr) && krnl.pcid_allc_mp.spec_index(pcid_allocator_ptr).view().wf() && krnl.pcid_allc_mp.spec_index(pcid_allocator_ptr).view().owning_container.view() == container_ptr) by { reveal(container_pcid_allocator_wf); reveal(pcid_allocator_perms_wf); };
    }
    let Tracked(pcid_allocator_lock_perm) = krnl.wlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx));
    let pcid_allocator = krnl.pcid_allc_mp.borrow_typed(pcid_allocator_ptr, Ghost(lctx.pcid_allocator_lock_map()), Tracked(&*lctx), Tracked(&pcid_allocator_lock_perm));
    let pcid_option = pcid_allocator.find_lowest_free_nonzero();
    if let None = pcid_option {
        krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof { steps.end_kernel_step(&*krnl, &*lctx); }
        return RetValueType::ErrorNoPcid;
    }
    let pcid = pcid_option.unwrap();
    let process_res = krnl.wlock_process_unless_killed(parent_ptr, Ghost(cpu_id), Tracked(&mut *lctx));
    if let (false, _) = process_res {
        krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof { steps.end_kernel_step(&*krnl, &*lctx); }
        return RetValueType::ErrorProcessKilled;
    }
    let Tracked(parent_lock_perm) = process_res.1.unwrap();
    proof {
        assert(krnl.thr_mp.dom().contains(current_thread_ptr) && krnl.thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_ptr && krnl.thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr && krnl.prc_mp.spec_index(parent_ptr).view().owned_threads.view().len() != 0) by { reveal(thread_cpu_wf); reveal(process_thread_wf); };
    }
    let thread_res = krnl.wlock_thread_unless_killed(current_thread_ptr, Tracked(&mut *lctx));
    if let (false, _) = thread_res {
        krnl.wunlock_process(parent_ptr, Tracked(&mut *lctx), Tracked(parent_lock_perm));
        krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof { steps.end_kernel_step(&*krnl, &*lctx); }
        return RetValueType::ErrorThreadKilled;
    }
    let Tracked(current_thread_lock_perm) = thread_res.1.unwrap();
    let thread_ref = krnl.thr_mp.borrow_typed(current_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&current_thread_lock_perm));
    let endpoint_option = *thread_ref.endpoint_descriptors.get(endpoint_index);
    let source_pagetable_ptr = thread_ref.proc_pagetable_ptr;
    let quota_insufficient = thread_ref.quota_4k < 6 + 3 * range;
    if endpoint_option.is_none() || quota_insufficient {
        let error = if endpoint_option.is_none() { RetValueType::Error } else { RetValueType::ErrorNoQuota };
        krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
        krnl.wunlock_process(parent_ptr, Tracked(&mut *lctx), Tracked(parent_lock_perm));
        krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof { steps.end_kernel_step(&*krnl, &*lctx); }
        return error;
    }
    let endpoint_ptr = endpoint_option.unwrap();
    proof {
        assert(krnl.ep_mp.dom().contains(endpoint_ptr) && krnl.ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((current_thread_ptr, endpoint_index))) by { reveal(thread_endpoint_ref_counter_wf); };
        assert(krnl.ctn_mp.dom().contains(krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container)) by { reveal(container_endpoint_wf); };
        assert({ ||| krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container == container_ptr ||| krnl.ctn_mp.spec_index(krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container).view_ghost().subtree_set.view().contains(container_ptr) }) by { reveal(container_thread_endpoint_wf); };
    }
    let Tracked(endpoint_lock_perm) = krnl.wlock_endpoint(endpoint_ptr, Tracked(&mut *lctx));
    proof {
        assert(krnl.pt_mp.dom().contains(source_pagetable_ptr) && !lctx.pagetable_lock_map().dom().contains(source_pagetable_ptr)) by { reveal(process_thread_wf); reveal(process_pagetable_match); };
    }
    let Tracked(source_pagetable_lock_perm) = krnl.wlock_pagetable(source_pagetable_ptr, Tracked(&mut *lctx));
    let source_start_indices = va2index(va);
    proof { assert(krnl.pt_mp.perms_wf()) by { reveal(pagetable_perms_wf); }; }
    let source_pt = krnl.pt_mp.borrow_typed(source_pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(&source_pagetable_lock_perm));
    let source_ready = if source_start_indices.0 < source_pt.kernel_l4_end {
        false
    } else {
        share_mapping_4k_source_precheck(krnl, &source_range, source_pagetable_ptr, Tracked(&*lctx), Tracked(&source_pagetable_lock_perm))
    };
    if !source_ready {
        krnl.wunlock_pagetable(source_pagetable_ptr, Tracked(&mut *lctx), Tracked(source_pagetable_lock_perm));
        krnl.wunlock_endpoint(endpoint_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm));
        krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
        krnl.wunlock_process(parent_ptr, Tracked(&mut *lctx), Tracked(parent_lock_perm));
        krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof { steps.end_kernel_step(&*krnl, &*lctx); }
        return RetValueType::Error;
    }
    proof {
        assert(lctx.holds_no_allocator_locks(PageSize::SZ4k) && lctx.holds_no_allocator_locks(PageSize::SZ2m) && lctx.holds_no_allocator_locks(PageSize::SZ1g)) by { reveal(LocalContext::holds_no_allocator_locks); };
    }
    let (child_ptr, iommu_table_ptr, thread_ptr) = commit_new_process_with_iommu_and_endpoint(krnl, &source_range, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, parent_ptr, current_thread_ptr, scheduler_ptr, allocator_ptr, pcid_allocator_ptr, source_pagetable_ptr, endpoint_ptr, endpoint_index, pcid, Tracked(cpu_lock_perm), Tracked(container_lock_perm), Tracked(pcid_allocator_lock_perm), Tracked(parent_lock_perm), Tracked(current_thread_lock_perm), Tracked(source_pagetable_lock_perm), Tracked(endpoint_lock_perm), initial_regs);
    RetValueType::SuccessThreeUsize { value1: child_ptr, value2: iommu_table_ptr, value3: thread_ptr }
}

}
