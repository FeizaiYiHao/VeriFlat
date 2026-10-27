use vstd::prelude::*;
use crate::*;
use super::syscall_iommu_unmap_4k_spec::*;

verus! {
/// The entry state's K facts on the running thread's cpu, container, process, and IOMMU table decide the result `ret`.
pub(super) proof fn iommu_unmap_4k_result_from_k(krnl: &KernelK, cpu_id: CpuId, iova: VAddr, range: usize, ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        !(range == 0 || range > usize::MAX / 4096 || !spec_va_4k_valid(iova) || iova >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(iova, range)),
        {
            let cpu = krnl.cpu_arr.spec_index(cpu_id).value;
            let thread_ptr = cpu.view().view().current_thread->Some_0;
            let thread = krnl.thr_mp.spec_index(thread_ptr);
            let container = krnl.ctn_mp.spec_index(thread.view().owning_container);
            let process = krnl.prc_mp.spec_index(thread.view().owning_proc);
            let table = krnl.it_mp.spec_index(process.view().iommu_table->Some_0).view();
            let iova_range = iommu_unmap_4k_iova_range(iova, range);
            let unowned = container.lock_process_owner_u() is None;
            let conflict = container.lock_process_owner_u() is Some && container.lock_process_owner_u()->Some_0 < LockOwnerId::Some(process.view_rodata().view().depth);
            let live = !container.being_killed() && unowned && !container.view().zombie && !process.being_killed() && !thread.being_killed() && !process.view().zombie;
            let mapped = spec_v2l4index(iova) >= krnl.dflt_pt.view().kernel_l4_end && forall|j: int| #![trigger iova_range.view()[j]] 0 <= j < range
                ==> table.mapping_4k().dom().contains(iova_range.view()[j]) && table.mapping_4k()[iova_range.view()[j]].present;
            &&& ret is CpuIdle ==> !(cpu.view().view().state is Running) || cpu.being_killed()
            &&& !(ret is CpuIdle) ==> cpu.view().view().state is Running && !cpu.being_killed() && cpu.view().view().current_thread is Some
            &&& !(ret is CpuIdle) ==> krnl.thr_mp.dom().contains(thread_ptr) && krnl.prc_mp.dom().contains(thread.view().owning_proc) && krnl.ctn_mp.dom().contains(thread.view().owning_container)
            &&& ret is ErrorContainerKilled ==> container.being_killed()
            &&& ret is ErrorContainerLockOrderConflict ==> !container.being_killed() && conflict
            &&& ret is ErrorContainerZombie ==> !container.being_killed() && unowned && container.view().zombie
            &&& ret is ErrorProcessKilled ==> !container.being_killed() && unowned && !container.view().zombie && process.being_killed()
            &&& ret is ErrorThreadKilled ==> !container.being_killed() && unowned && !container.view().zombie && !process.being_killed() && thread.being_killed()
            &&& ret is ErrorPciNoIommuTable ==> live && process.view().iommu_table is None
            &&& (ret is Success || ret is ErrorIommuIovaNotMapped) ==> live && process.view().iommu_table is Some && krnl.it_mp.dom().contains(process.view().iommu_table->Some_0) && table.leaves_present()
            &&& ret is Success ==> mapped
            &&& ret is ErrorIommuIovaNotMapped ==> !mapped
            &&& ret is CpuIdle || ret is ErrorContainerKilled || ret is ErrorContainerLockOrderConflict || ret is ErrorContainerZombie || ret is ErrorProcessKilled || ret is ErrorThreadKilled
                || ret is ErrorPciNoIommuTable || ret is Success || ret is ErrorIommuIovaNotMapped
        },
    ensures
        iommu_unmap_4k_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, iova, range) == ret,
{
    let c = krnl.cpu_arr.spec_index(cpu_id).value.view().view();
    let thread = krnl.thr_mp.spec_index(c.current_thread->Some_0).view();
    kernel_cpu_projection_at(krnl, cpu_id); kernel_u_domains_projection(krnl);
    if !(ret is CpuIdle) {
        kernel_cpu_thread_projection_at(krnl, cpu_id, thread.owning_proc, c.current_thread->Some_0, None); kernel_container_projection_at(krnl, thread.owning_container);
        kernel_process_projection_at(krnl, thread.owning_proc);
        if ret is Success || ret is ErrorIommuIovaNotMapped { kernel_iommu_table_mappings_projection_at(krnl, thread.owning_proc); }
    }
}

/// Hiding the next iova of the recorded range and advancing the progress is a leaf step on `pre`/`post`.
pub(super) proof fn iommu_unmap_4k_leaf_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, iova: VAddr)
    requires
        {
            let thread = pre.thread_map.spec_index(thread_ptr);
            let process = pre.process_map.spec_index(process_ptr);
            let progress = thread.syscall_progress->Some_0;
            &&& iommu_unmap_4k_table_locked(pre, cpu_id)
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& thread.owning_proc == process_ptr
            &&& thread.syscall_progress is Some
            &&& progress is IommuUnmap4k
            &&& progress->IommuUnmap4k_unmapped < progress->IommuUnmap4k_iova_range.len
            &&& !progress->IommuUnmap4k_flushed
            &&& progress->IommuUnmap4k_iova_range.view()[progress->IommuUnmap4k_unmapped as int] == iova
            &&& process.iommu_table->Some_0.mapping_4k.dom().contains(iova)
            &&& post == (KernelU {
                thread_map: pre.thread_map.insert(thread_ptr, ThreadU {
                    syscall_progress: Some(SyscallProgress::IommuUnmap4k {
                        iova_range: progress->IommuUnmap4k_iova_range, unmapped: (progress->IommuUnmap4k_unmapped + 1) as usize, flushed: false,
                    }),
                    ..thread
                }),
                process_map: pre.process_map.insert(process_ptr, ProcessU {
                    iommu_table: Some(PageTableU { mapping_4k: process.iommu_table->Some_0.mapping_4k.remove(iova), ..process.iommu_table->Some_0 }), ..process
                }),
                ..pre
            })
        },
    ensures
        iommu_unmap_4k_range_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(iommu_unmap_4k_leaf_step_pre); reveal(iommu_unmap_4k_leaf_step); reveal(iommu_unmap_4k_range_step); }

/// Emptying every IOTLB domain and recording the flush after the last hidden iova is the flush step on `pre`/`post`.
pub(super) proof fn iommu_unmap_4k_flush_step_from_u(pre: KernelU, post: KernelU, cpu_id: CpuId, thread_ptr: RwLockThreadPtr)
    requires
        {
            let thread = pre.thread_map.spec_index(thread_ptr);
            let progress = thread.syscall_progress->Some_0;
            &&& iommu_unmap_4k_table_locked(pre, cpu_id)
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            &&& thread.syscall_progress is Some
            &&& progress is IommuUnmap4k
            &&& progress->IommuUnmap4k_unmapped == progress->IommuUnmap4k_iova_range.len
            &&& !progress->IommuUnmap4k_flushed
            &&& post.iommu_tlb.dom() == pre.iommu_tlb.dom()
            &&& forall|did: VtdDomainId| #![trigger post.iommu_tlb[did]] vtd_domain_id_valid(did) ==> post.iommu_tlb[did].is_empty()
            &&& post == (KernelU {
                iommu_tlb: post.iommu_tlb,
                thread_map: pre.thread_map.insert(thread_ptr, ThreadU {
                    syscall_progress: Some(SyscallProgress::IommuUnmap4k { iova_range: progress->IommuUnmap4k_iova_range, unmapped: progress->IommuUnmap4k_unmapped, flushed: true }),
                    ..thread
                }),
                ..pre
            })
        },
    ensures
        iommu_unmap_4k_range_step(KernelStep { old_u: pre, new_u: post }, cpu_id),
{ reveal(iommu_unmap_4k_flush_step_pre); reveal(iommu_unmap_4k_flush_step); reveal(iommu_unmap_4k_range_step); }

/// The enter step pushed onto an empty trace is the partial trace after entering.
pub(super) proof fn iommu_unmap_4k_trace_enter_step(before: Seq<KernelStep>, trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, iova_range: VaRange4K)
    requires
        before.len() == 0,
        trace == before.push(KernelStep { old_u: pre, new_u: post }),
        iommu_unmap_4k_enter_step_pre(pre, cpu_id, iova_range),
        iommu_unmap_4k_enter_step(pre, post, cpu_id, iova_range),
    ensures
        iommu_unmap_4k_partial_trace(trace, cpu_id, iova_range),
{ reveal(iommu_unmap_4k_partial_trace); }

/// Range steps appended after the partial trace `before` extend it.
pub(super) proof fn iommu_unmap_4k_trace_range_steps(before: Seq<KernelStep>, after: Seq<KernelStep>, cpu_id: CpuId, iova_range: VaRange4K)
    requires
        iommu_unmap_4k_partial_trace(before, cpu_id, iova_range),
        before.len() <= after.len(),
        forall|j: int| #![trigger after[j]] 0 <= j < before.len() ==> after[j] == before[j],
        forall|j: int| #![trigger after[j]] before.len() <= j < after.len() ==> iommu_unmap_4k_range_step(after[j], cpu_id),
    ensures
        iommu_unmap_4k_partial_trace(after, cpu_id, iova_range),
{ reveal(iommu_unmap_4k_partial_trace); }

/// The exit step pushed after the partial trace completes the syscall trace.
pub(super) proof fn iommu_unmap_4k_trace_exit_step(before: Seq<KernelStep>, trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, iova: VAddr, range: usize)
    requires
        iommu_unmap_4k_partial_trace(before, cpu_id, iommu_unmap_4k_iova_range(iova, range)),
        range + 2 <= before.len() <= range + MAX_CONTAINER_TREE_DEPTH + 3,
        trace == before.push(KernelStep { old_u: pre, new_u: post }),
        iommu_unmap_4k_exit_step_pre(pre, cpu_id),
        iommu_unmap_4k_exit_step(pre, post, cpu_id),
    ensures
        iommu_unmap_4k_syscall_trace(trace, cpu_id, iova, range),
{ reveal(iommu_unmap_4k_partial_trace); reveal(iommu_unmap_4k_syscall_trace); }
/// Write-locking the cpu, its running thread, the thread's process and container, and the process's IOMMU table, and
/// recording the first iova from a `Success` entry state is the enter step.
pub(super) proof fn iommu_unmap_4k_enter_step_from_k(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, iommu_table_ptr: RwLockPageTableRoot,
    iova: VAddr, range: usize,
)
    requires
        process_iommu_table_match(pre.prc_mp, pre.it_mp),
        index_valid(NUM_CPUS, cpu_id),
        pre.prc_mp.dom().contains(process_ptr),
        !pre.prc_mp.spec_index(process_ptr).view().zombie,
        pre.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        pre.it_mp.dom().contains(iommu_table_ptr),
        iommu_unmap_4k_syscall_result(kernel_k_to_kernel_u(*pre), cpu_id, iova, range) is Success,
        iommu_unmap_4k_iova_range(iova, range).wf(),
        *post == (KernelK { cpu_arr: post.cpu_arr, ctn_mp: post.ctn_mp, prc_mp: post.prc_mp, thr_mp: post.thr_mp, it_mp: post.it_mp, ..*pre }),
        !pre.cpu_arr.spec_index(cpu_id).value.locked(),
        post.cpu_arr.unchanged_except(&pre.cpu_arr, cpu_id),
        post.cpu_arr.spec_index(cpu_id).view().view() == pre.cpu_arr.spec_index(cpu_id).view().view(),
        post.cpu_arr.spec_index(cpu_id).value.killer_info() == pre.cpu_arr.spec_index(cpu_id).value.killer_info(),
        post.cpu_arr.spec_index(cpu_id).value.being_killed() == pre.cpu_arr.spec_index(cpu_id).value.being_killed(),
        post.cpu_arr.spec_index(cpu_id).value.locking_thread() is Write,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        pre.ctn_mp.dom().contains(container_ptr),
        !pre.ctn_mp.spec_index(container_ptr).locked(),
        post.ctn_mp.unchanged_except(&pre.ctn_mp, container_ptr),
        post.ctn_mp.spec_index(container_ptr).view() == pre.ctn_mp.spec_index(container_ptr).view(),
        post.ctn_mp.spec_index(container_ptr).view_rodata() == pre.ctn_mp.spec_index(container_ptr).view_rodata(),
        post.ctn_mp.spec_index(container_ptr).view_ghost() == pre.ctn_mp.spec_index(container_ptr).view_ghost(),
        post.ctn_mp.spec_index(container_ptr).being_killed() == pre.ctn_mp.spec_index(container_ptr).being_killed(),
        post.ctn_mp.spec_index(container_ptr).locking_thread() is Write,
        post.ctn_mp.spec_index(container_ptr).lock_process_owner_u() == Some(LockOwnerId::Some(pre.prc_mp.spec_index(process_ptr).view_rodata().view().depth)),
        !pre.prc_mp.spec_index(process_ptr).locked(),
        post.prc_mp.unchanged_except(&pre.prc_mp, process_ptr),
        post.prc_mp.spec_index(process_ptr).view() == pre.prc_mp.spec_index(process_ptr).view(),
        post.prc_mp.spec_index(process_ptr).view_rodata() == pre.prc_mp.spec_index(process_ptr).view_rodata(),
        post.prc_mp.spec_index(process_ptr).view_ghost() == pre.prc_mp.spec_index(process_ptr).view_ghost(),
        post.prc_mp.spec_index(process_ptr).being_killed() == pre.prc_mp.spec_index(process_ptr).being_killed(),
        post.prc_mp.spec_index(process_ptr).locking_thread() is Write,
        pre.prc_mp.spec_index(process_ptr).view().iommu_table == Some(iommu_table_ptr),
        pre.thr_mp.dom().contains(thread_ptr),
        !pre.thr_mp.spec_index(thread_ptr).locked(),
        pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None,
        pre.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..pre.thr_mp.spec_index(thread_ptr).view() }),
        post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::IommuUnmap4k { iova_range: iommu_unmap_4k_iova_range(iova, range), unmapped: 0, flushed: false }),
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
        post.thr_mp.spec_index(thread_ptr).locking_thread() is Write,
        !pre.it_mp.spec_index(iommu_table_ptr).locked(),
        post.it_mp.unchanged_except(&pre.it_mp, iommu_table_ptr),
        post.it_mp.spec_index(iommu_table_ptr).view() == pre.it_mp.spec_index(iommu_table_ptr).view(),
        post.it_mp.spec_index(iommu_table_ptr).locking_thread() is Write,
    ensures
        iommu_unmap_4k_enter_step_pre(kernel_k_to_kernel_u(*pre), cpu_id, iommu_unmap_4k_iova_range(iova, range)),
        iommu_unmap_4k_enter_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id, iommu_unmap_4k_iova_range(iova, range)),
{
    reveal(iommu_unmap_4k_enter_step_pre); reveal(iommu_unmap_4k_enter_step);
    kernel_cpu_container_process_thread_iommu_table_lock_states_and_progress_changed_implies_u_step(pre, post, cpu_id, container_ptr, process_ptr, thread_ptr, iommu_table_ptr);
    kernel_cpu_projection_at(pre, cpu_id); kernel_cpu_thread_projection_at(pre, cpu_id, process_ptr, thread_ptr, None);
    kernel_thread_projection_at(pre, thread_ptr); kernel_process_projection_at(pre, process_ptr); kernel_container_projection_at(pre, container_ptr);
}

/// Advancing the progress past iova `iova` and then clearing its present leaf in the write-held IOMMU table under the
/// IOMMU-unmap locks is one leaf step from `pre` to `post`.
pub(super) proof fn iommu_unmap_4k_leaf_step_from_k(
    pre: &KernelK, mid: &KernelK, post: &KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    iommu_table_ptr: RwLockPageTableRoot, iova_range: VaRange4K, unmapped: usize,
)
    requires
        process_iommu_table_match(pre.prc_mp, pre.it_mp),
        index_valid(NUM_CPUS, cpu_id),
        pre.cpu_arr.spec_index(cpu_id).value.locking_thread() is Write,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).locking_thread() is Write,
        pre.prc_mp.dom().contains(process_ptr),
        !pre.prc_mp.spec_index(process_ptr).view().zombie,
        pre.prc_mp.spec_index(process_ptr).locking_thread() is Write,
        pre.prc_mp.spec_index(process_ptr).view().iommu_table == Some(iommu_table_ptr),
        pre.it_mp.spec_index(iommu_table_ptr).locking_thread() is Write,
        pre.thr_mp.dom().contains(thread_ptr),
        pre.thr_mp.spec_index(thread_ptr).locking_thread() is Write,
        pre.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        pre.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        unmapped < iova_range.len,
        pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::IommuUnmap4k { iova_range, unmapped, flushed: false }),
        *mid == (KernelK { thr_mp: mid.thr_mp, ..*pre }),
        mid.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        mid.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: mid.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..pre.thr_mp.spec_index(thread_ptr).view() }),
        mid.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::IommuUnmap4k { iova_range, unmapped: (unmapped + 1) as usize, flushed: false }),
        mid.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
        mid.thr_mp.spec_index(thread_ptr).locking_thread() == pre.thr_mp.spec_index(thread_ptr).locking_thread(),
        *post == (KernelK { it_mp: post.it_mp, ..*mid }),
        post.it_mp.unchanged_except(&mid.it_mp, iommu_table_ptr),
        post.it_mp.spec_index(iommu_table_ptr).locking_thread() == mid.it_mp.spec_index(iommu_table_ptr).locking_thread(),
        post.it_mp.spec_index(iommu_table_ptr).view().proc_ptr == mid.it_mp.spec_index(iommu_table_ptr).view().proc_ptr,
        mid.it_mp.spec_index(iommu_table_ptr).view().mapping_4k().dom().contains(iova_range.view()[unmapped as int]),
        mid.it_mp.spec_index(iommu_table_ptr).view().mapping_4k()[iova_range.view()[unmapped as int]].present,
        post.it_mp.spec_index(iommu_table_ptr).view().mapping_4k() == mid.it_mp.spec_index(iommu_table_ptr).view().mapping_4k().insert(iova_range.view()[unmapped as int],
            MapEntry { present: false, ..mid.it_mp.spec_index(iommu_table_ptr).view().mapping_4k()[iova_range.view()[unmapped as int]] }),
        post.it_mp.spec_index(iommu_table_ptr).view().mapping_2m() == mid.it_mp.spec_index(iommu_table_ptr).view().mapping_2m(),
        post.it_mp.spec_index(iommu_table_ptr).view().mapping_1g() == mid.it_mp.spec_index(iommu_table_ptr).view().mapping_1g(),
    ensures
        iommu_unmap_4k_range_step(KernelStep { old_u: kernel_k_to_kernel_u(*pre), new_u: kernel_k_to_kernel_u(*post) }, cpu_id),
{
    let iova = iova_range.view()[unmapped as int];
    assert(pre.it_mp.dom().contains(iommu_table_ptr) && pre.it_mp.spec_index(iommu_table_ptr).view().proc_ptr == process_ptr) by { reveal(process_iommu_table_match); };
    kernel_thread_syscall_progress_changed_implies_u_step(pre, mid, thread_ptr);
    kernel_iommu_table_4k_present_cleared_implies_u_step(mid, post, iommu_table_ptr, iova);
    kernel_u_domains_projection(pre);
    kernel_cpu_projection_at(pre, cpu_id); kernel_container_projection_at(pre, container_ptr);
    kernel_thread_projection_at(pre, thread_ptr); kernel_thread_projection_at(mid, thread_ptr);
    kernel_process_projection_at(pre, process_ptr); kernel_iommu_table_mappings_projection_at(pre, process_ptr);
    iommu_unmap_4k_leaf_step_from_u(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id, process_ptr, thread_ptr, iova);
}

/// Flushing every IOTLB domain and then recording the flush after the last hidden iova under the IOMMU-unmap locks is the
/// flush step from `pre` to `post`.
pub(super) proof fn iommu_unmap_4k_flush_step_from_k(
    pre: &KernelK, mid: &KernelK, post: &KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    iommu_table_ptr: RwLockPageTableRoot, iova_range: VaRange4K,
)
    requires
        process_iommu_table_match(pre.prc_mp, pre.it_mp),
        index_valid(NUM_CPUS, cpu_id),
        pre.cpu_arr.spec_index(cpu_id).value.locking_thread() is Write,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).locking_thread() is Write,
        pre.prc_mp.dom().contains(process_ptr),
        !pre.prc_mp.spec_index(process_ptr).view().zombie,
        pre.prc_mp.spec_index(process_ptr).locking_thread() is Write,
        pre.prc_mp.spec_index(process_ptr).view().iommu_table == Some(iommu_table_ptr),
        pre.it_mp.spec_index(iommu_table_ptr).locking_thread() is Write,
        pre.thr_mp.dom().contains(thread_ptr),
        pre.thr_mp.spec_index(thread_ptr).locking_thread() is Write,
        pre.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        pre.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::IommuUnmap4k { iova_range, unmapped: iova_range.len, flushed: false }),
        *mid == (KernelK { iommu_tlb: mid.iommu_tlb, ..*pre }),
        mid.iommu_tlb.view().dom() == pre.iommu_tlb.view().dom(),
        forall|did: VtdDomainId| #![trigger mid.iommu_tlb.view()[did]] vtd_domain_id_valid(did) ==> mid.iommu_tlb.spec_index(did).is_empty(),
        *post == (KernelK { thr_mp: post.thr_mp, ..*mid }),
        post.thr_mp.unchanged_except(&mid.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..mid.thr_mp.spec_index(thread_ptr).view() }),
        post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::IommuUnmap4k { iova_range, unmapped: iova_range.len, flushed: true }),
        post.thr_mp.spec_index(thread_ptr).being_killed() == mid.thr_mp.spec_index(thread_ptr).being_killed(),
        post.thr_mp.spec_index(thread_ptr).locking_thread() == mid.thr_mp.spec_index(thread_ptr).locking_thread(),
    ensures
        iommu_unmap_4k_range_step(KernelStep { old_u: kernel_k_to_kernel_u(*pre), new_u: kernel_k_to_kernel_u(*post) }, cpu_id),
{
    assert(pre.it_mp.dom().contains(iommu_table_ptr)) by { reveal(process_iommu_table_match); };
    kernel_iommu_tlb_flushed_implies_u_step(pre, mid); kernel_thread_syscall_progress_changed_implies_u_step(mid, post, thread_ptr);
    kernel_cpu_projection_at(pre, cpu_id); kernel_container_projection_at(pre, container_ptr); kernel_thread_projection_at(pre, thread_ptr);
    kernel_process_projection_at(pre, process_ptr); kernel_iommu_table_mappings_projection_at(pre, process_ptr);
    iommu_unmap_4k_flush_step_from_u(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id, thread_ptr);
}

/// Clearing progress and unlocking the IOMMU table, the running thread, its process and container, and the cpu after the
/// recorded flush is the exit step.
pub(super) proof fn iommu_unmap_4k_exit_step_from_k(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, iommu_table_ptr: RwLockPageTableRoot,
)
    requires
        process_iommu_table_match(pre.prc_mp, pre.it_mp),
        index_valid(NUM_CPUS, cpu_id),
        pre.prc_mp.dom().contains(process_ptr),
        !pre.prc_mp.spec_index(process_ptr).view().zombie,
        pre.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        pre.it_mp.dom().contains(iommu_table_ptr),
        *post == (KernelK { cpu_arr: post.cpu_arr, ctn_mp: post.ctn_mp, prc_mp: post.prc_mp, thr_mp: post.thr_mp, it_mp: post.it_mp, ..*pre }),
        pre.cpu_arr.spec_index(cpu_id).value.locking_thread() is Write,
        post.cpu_arr.unchanged_except(&pre.cpu_arr, cpu_id),
        post.cpu_arr.spec_index(cpu_id).view().view() == pre.cpu_arr.spec_index(cpu_id).view().view(),
        post.cpu_arr.spec_index(cpu_id).value.killer_info() == pre.cpu_arr.spec_index(cpu_id).value.killer_info(),
        post.cpu_arr.spec_index(cpu_id).value.being_killed() == pre.cpu_arr.spec_index(cpu_id).value.being_killed(),
        post.cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).locking_thread() is Write,
        post.ctn_mp.unchanged_except(&pre.ctn_mp, container_ptr),
        post.ctn_mp.spec_index(container_ptr).view() == pre.ctn_mp.spec_index(container_ptr).view(),
        post.ctn_mp.spec_index(container_ptr).view_rodata() == pre.ctn_mp.spec_index(container_ptr).view_rodata(),
        post.ctn_mp.spec_index(container_ptr).view_ghost() == pre.ctn_mp.spec_index(container_ptr).view_ghost(),
        post.ctn_mp.spec_index(container_ptr).being_killed() == pre.ctn_mp.spec_index(container_ptr).being_killed(),
        post.ctn_mp.spec_index(container_ptr).locking_thread() is None,
        pre.prc_mp.spec_index(process_ptr).locking_thread() is Write,
        post.prc_mp.unchanged_except(&pre.prc_mp, process_ptr),
        post.prc_mp.spec_index(process_ptr).view() == pre.prc_mp.spec_index(process_ptr).view(),
        post.prc_mp.spec_index(process_ptr).view_rodata() == pre.prc_mp.spec_index(process_ptr).view_rodata(),
        post.prc_mp.spec_index(process_ptr).view_ghost() == pre.prc_mp.spec_index(process_ptr).view_ghost(),
        post.prc_mp.spec_index(process_ptr).being_killed() == pre.prc_mp.spec_index(process_ptr).being_killed(),
        post.prc_mp.spec_index(process_ptr).locking_thread() is None,
        pre.prc_mp.spec_index(process_ptr).view().iommu_table == Some(iommu_table_ptr),
        pre.thr_mp.dom().contains(thread_ptr),
        pre.thr_mp.spec_index(thread_ptr).locking_thread() is Write,
        pre.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is Some,
        pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0 is IommuUnmap4k,
        pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->IommuUnmap4k_unmapped == pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->IommuUnmap4k_iova_range.len,
        pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->IommuUnmap4k_flushed,
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..pre.thr_mp.spec_index(thread_ptr).view() }),
        post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None,
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
        post.thr_mp.spec_index(thread_ptr).locking_thread() is None,
        pre.it_mp.spec_index(iommu_table_ptr).locking_thread() is Write,
        post.it_mp.unchanged_except(&pre.it_mp, iommu_table_ptr),
        post.it_mp.spec_index(iommu_table_ptr).view() == pre.it_mp.spec_index(iommu_table_ptr).view(),
        post.it_mp.spec_index(iommu_table_ptr).locking_thread() is None,
    ensures
        iommu_unmap_4k_exit_step_pre(kernel_k_to_kernel_u(*pre), cpu_id),
        iommu_unmap_4k_exit_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id),
{
    reveal(iommu_unmap_4k_exit_step_pre); reveal(iommu_unmap_4k_exit_step);
    kernel_cpu_container_process_thread_iommu_table_lock_states_and_progress_changed_implies_u_step(pre, post, cpu_id, container_ptr, process_ptr, thread_ptr, iommu_table_ptr);
    kernel_cpu_projection_at(pre, cpu_id); kernel_cpu_thread_projection_at(pre, cpu_id, process_ptr, thread_ptr, None);
    kernel_thread_projection_at(pre, thread_ptr); kernel_process_projection_at(pre, process_ptr); kernel_container_projection_at(pre, container_ptr);
}
/// The 4K quota refund steps that `refund_unmap_4k_quota` appended under the IOMMU-unmap context locks after the recorded
/// flush extend the partial trace `before`.
pub(super) proof fn iommu_unmap_4k_trace_refund_steps(
    before: Seq<KernelStep>, after: Seq<KernelStep>, krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, iova_range: VaRange4K,
)
    requires
        iommu_unmap_4k_partial_trace(before, cpu_id, iova_range),
        before.len() <= after.len(),
        forall|j: int| #![trigger after[j]] #![trigger before[j]] 0 <= j < before.len() ==> after[j] == before[j],
        index_valid(NUM_CPUS, cpu_id),
        lctx.cpu_id() == cpu_id,
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::IommuUnmap4k { iova_range, unmapped: iova_range.len, flushed: true }),
        typed_lock_map_contains_mode(lctx.container_lock_map(), krnl.thr_mp.spec_index(thread_ptr).view().owning_container, TypedLockMode::Write),
        forall|j: int| #![trigger after[j]] before.len() <= j < after.len() ==> {
            let old_u = after[j].old_u;
            let thread = krnl.thr_mp.spec_index(thread_ptr).view();
            &&& kernel_u_container_quota_4k_increased(old_u, after[j].new_u, thread.owning_container)
            &&& old_u.cpu_array[lctx.cpu_id() as int].lock_state is WriteLocked
            &&& old_u.cpu_array[lctx.cpu_id() as int].current_thread == krnl.cpu_arr.spec_index(lctx.cpu_id()).view().view().view().current_thread
            &&& old_u.thread_map.dom().contains(thread_ptr)
            &&& old_u.thread_map[thread_ptr].lock_state is WriteLocked
            &&& old_u.thread_map[thread_ptr].owning_container == thread.owning_container
            &&& old_u.thread_map[thread_ptr].owning_proc == thread.owning_proc
            &&& old_u.thread_map[thread_ptr].syscall_progress == thread.syscall_progress.view()
            &&& old_u.process_map.dom().contains(thread.owning_proc)
            &&& old_u.process_map[thread.owning_proc].lock_state is WriteLocked
            &&& typed_lock_map_contains_mode(lctx.container_lock_map(), thread.owning_container, TypedLockMode::Write) ==> {
                &&& old_u.container_map.dom().contains(thread.owning_container)
                &&& old_u.container_map[thread.owning_container].lock_state is WriteLocked
            }
        },
    ensures
        iommu_unmap_4k_partial_trace(after, cpu_id, iova_range),
{
    reveal(iommu_unmap_4k_partial_trace); reveal(iommu_unmap_4k_refund_step_pre); reveal(iommu_unmap_4k_range_step);
}
} // verus!
