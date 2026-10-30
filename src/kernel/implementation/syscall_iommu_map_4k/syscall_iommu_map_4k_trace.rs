use vstd::prelude::*;
use crate::*;
use super::syscall_iommu_map_4k_spec::*;

verus! {
/// The entry state's K facts on the running thread's cpu, process, page table, and IOMMU table decide the IOMMU-map result
/// `ret`.
pub(super) proof fn iommu_map_4k_result_from_k(krnl: &KernelK, cpu_id: CpuId, va: VAddr, iova: VAddr, range: usize, ret: RetValueType)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        ({
            let cpu = krnl.cpu_arr.spec_index(cpu_id).value;
            let thread_ptr = cpu.view().view().current_thread->Some_0;
            let thread = krnl.thr_mp.spec_index(thread_ptr);
            let process = krnl.prc_mp.spec_index(thread.view().owning_proc);
            let table = pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), process.view().pagetable);
            let it = krnl.it_mp.spec_index(process.view().iommu_table->Some_0).view();
            let va_range = iommu_map_4k_syscall_range(va, range);
            let iova_range = iommu_map_4k_syscall_range(iova, range);
            let malformed = range == 0 || range > usize::MAX / 4096 || !spec_va_4k_valid(va) || va >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(va, range) || !spec_va_4k_valid(iova)
                || iova >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(iova, range);
            let checked = !malformed && !(ret is CpuIdle) && !(ret is ErrorProcessKilled) && !(ret is ErrorThreadKilled);
            let tabled = checked && !(ret is ErrorPciNoIommuTable);
            let mapped = forall|j: int| #![trigger va_range.view()[j]] 0 <= j < range ==> table.mapping_4k().dom().contains(va_range.view()[j]) && table.mapping_4k()[va_range.view()[j]].present;
            let free = forall|j: int| #![trigger iova_range.view()[j]] 0 <= j < range ==> !it.mapping_4k().dom().contains(iova_range.view()[j]);
            &&& malformed ==> ret is Error
            &&& !malformed && ret is CpuIdle ==> !(cpu.view().view().state is Running) || cpu.being_killed()
            &&& !malformed && !(ret is CpuIdle) ==> cpu.view().view().state is Running && !cpu.being_killed() && cpu.view().view().current_thread is Some
            &&& !malformed && !(ret is CpuIdle) ==> krnl.thr_mp.dom().contains(thread_ptr) && krnl.prc_mp.dom().contains(thread.view().owning_proc)
            &&& !malformed && ret is ErrorProcessKilled ==> process.being_killed()
            &&& !malformed && ret is ErrorThreadKilled ==> !process.being_killed() && thread.being_killed()
            &&& checked ==> !process.being_killed() && !thread.being_killed() && !process.view().zombie && krnl.pt_mp.dom().contains(process.view().pagetable)
            &&& checked && ret is ErrorPciNoIommuTable ==> process.view().iommu_table is None
            &&& tabled ==> process.view().iommu_table is Some && krnl.it_mp.dom().contains(process.view().iommu_table->Some_0)
            &&& tabled && !(ret is ErrorNoQuota) ==> it.leaves_present()
            &&& tabled && ret is ErrorNoQuota ==> thread.view().quota_4k < 3 * range
            &&& tabled && !(ret is ErrorNoQuota) ==> thread.view().quota_4k >= 3 * range
            &&& tabled && ret is Error ==> spec_v2l4index(va) < table.kernel_l4_end()
            &&& tabled && (ret is ErrorIommuVaNotMapped || ret is ErrorIommuIovaAlreadyMapped || ret is Success) ==> spec_v2l4index(va) >= table.kernel_l4_end()
            &&& tabled && ret is ErrorIommuVaNotMapped ==> !mapped
            &&& tabled && (ret is ErrorIommuIovaAlreadyMapped || ret is Success) ==> mapped
            &&& tabled && ret is ErrorIommuIovaAlreadyMapped ==> !free
            &&& tabled && ret is Success ==> free
            &&& ret is Error || ret is CpuIdle || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorPciNoIommuTable || ret is ErrorNoQuota || ret is ErrorIommuVaNotMapped
                || ret is ErrorIommuIovaAlreadyMapped || ret is Success
        }),
    ensures
        iommu_map_4k_syscall_result(kernel_k_to_kernel_u(*krnl), cpu_id, va, iova, range) == ret,
{
    let c = krnl.cpu_arr.spec_index(cpu_id).value.view().view();
    let thread = krnl.thr_mp.spec_index(c.current_thread->Some_0).view();
    let process = krnl.prc_mp.spec_index(thread.owning_proc).view();
    let u = kernel_k_to_kernel_u(*krnl);
    kernel_cpu_projection_at(krnl, cpu_id);
    if !(ret is Error && (range == 0 || range > usize::MAX / 4096 || !spec_va_4k_valid(va) || va >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(va, range) || !spec_va_4k_valid(iova)
        || iova >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(iova, range))) && !(ret is CpuIdle) {
        kernel_cpu_thread_projection_at(krnl, cpu_id, thread.owning_proc, c.current_thread->Some_0, None);
        if !(ret is ErrorProcessKilled) && !(ret is ErrorThreadKilled) {
            kernel_l4_end_projection_at(krnl, process.pagetable); kernel_process_projection_at(krnl, thread.owning_proc);
            let table = pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), process.pagetable);
            assert(forall|v: VAddr| #![trigger u.process_map[thread.owning_proc].pagetable->Some_0.mapping_4k.dom().contains(v)] #![trigger table.mapping_4k().dom().contains(v)]
                u.process_map[thread.owning_proc].pagetable->Some_0.mapping_4k.dom().contains(v) == (table.mapping_4k().dom().contains(v) && table.mapping_4k()[v].present));
            assert(user_va_range(u, iommu_map_4k_syscall_range(va, range)) == (spec_v2l4index(va) >= table.kernel_l4_end()));
            if !(ret is ErrorPciNoIommuTable) && !(ret is ErrorNoQuota) {
                kernel_iommu_table_mappings_projection_at(krnl, thread.owning_proc);
            }
        }
    }
}

/// Write-locking the cpu, its running thread and process, read-locking the page table, write-locking the IOMMU table, and
/// recording the first page from a `Success` entry state is the enter step.
pub(super) proof fn iommu_map_4k_enter_step_from_k(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, iommu_table_ptr: RwLockPageTableRoot,
    va: VAddr, iova: VAddr, range: usize,
)
    requires
        process_cpu_wf(pre.prc_mp, pre.cpu_arr),
        process_pagetable_match(pre.prc_mp, pre.pt_mp),
        process_iommu_table_match(pre.prc_mp, pre.it_mp),
        index_valid(NUM_CPUS, cpu_id),
        iommu_map_4k_syscall_result(kernel_k_to_kernel_u(*pre), cpu_id, va, iova, range) is Success,
        iommu_map_4k_syscall_range(va, range).wf(),
        iommu_map_4k_syscall_range(iova, range).wf(),
        *post == (KernelK { cpu_arr: post.cpu_arr, cpu_op: post.cpu_op, prc_mp: post.prc_mp, thr_mp: post.thr_mp, pt_mp: post.pt_mp, pt_lower: post.pt_lower, it_mp: post.it_mp, ..*pre }),
        !pre.cpu_arr.spec_index(cpu_id).value.locked(),
        post.cpu_arr.entries_unchanged_except(&pre.cpu_arr, cpu_id),
        post.cpu_arr.spec_index(cpu_id).view().view().view() == pre.cpu_arr.spec_index(cpu_id).view().view().view(),
        pre.cpu_op.view().view().len() == NUM_CPUS,
        post.cpu_op.view().view() == pre.cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
        post.cpu_arr.spec_index(cpu_id).value.killer_info() == pre.cpu_arr.spec_index(cpu_id).value.killer_info(),
        post.cpu_arr.spec_index(cpu_id).value.being_killed() == pre.cpu_arr.spec_index(cpu_id).value.being_killed(),
        post.cpu_arr.spec_index(cpu_id).value.locking_thread() is Write,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        !pre.prc_mp.spec_index(process_ptr).locked(),
        post.prc_mp.unchanged_except(&pre.prc_mp, process_ptr),
        post.prc_mp.spec_index(process_ptr).view() == pre.prc_mp.spec_index(process_ptr).view(),
        post.prc_mp.spec_index(process_ptr).view_rodata() == pre.prc_mp.spec_index(process_ptr).view_rodata(),
        post.prc_mp.spec_index(process_ptr).view_ghost() == pre.prc_mp.spec_index(process_ptr).view_ghost(),
        post.prc_mp.spec_index(process_ptr).being_killed() == pre.prc_mp.spec_index(process_ptr).being_killed(),
        post.prc_mp.spec_index(process_ptr).locking_thread() is Write,
        pre.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr,
        pre.prc_mp.spec_index(process_ptr).view().iommu_table == Some(iommu_table_ptr),
        pre.thr_mp.dom().contains(thread_ptr),
        pre.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        !pre.thr_mp.spec_index(thread_ptr).locked(),
        pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None,
        pre.ctn_mp.dom().contains(pre.thr_mp.spec_index(thread_ptr).view().owning_container),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..pre.thr_mp.spec_index(thread_ptr).view() }),
        post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::IommuMap4k {
            va_range: iommu_map_4k_syscall_range(va, range), iova_range: iommu_map_4k_syscall_range(iova, range), mapped: 0, directory: Mmap4kDirectory::None }),
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
        post.thr_mp.spec_index(thread_ptr).locking_thread() is Write,
        !pre.pt_mp.spec_index(pagetable_ptr).wlocked(),
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        post.pt_mp.spec_index(pagetable_ptr).view() == pre.pt_mp.spec_index(pagetable_ptr).view(),
        post.pt_mp.spec_index(pagetable_ptr).locking_thread() is Read,
        post.pt_lower.view() == pre.pt_lower.view().insert(pagetable_ptr, post.pt_lower.view().spec_index(pagetable_ptr)),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k(),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_2m() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m(),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_1g(),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks == pagetable_window_locks_after_locking_range(pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks, iommu_map_4k_syscall_range(va, range)),
        !pre.it_mp.spec_index(iommu_table_ptr).locked(),
        post.it_mp.unchanged_except(&pre.it_mp, iommu_table_ptr),
        post.it_mp.spec_index(iommu_table_ptr).view() == pre.it_mp.spec_index(iommu_table_ptr).view(),
        post.it_mp.spec_index(iommu_table_ptr).locking_thread() is Write,
    ensures
        iommu_map_4k_enter_step_pre(kernel_k_to_kernel_u(*pre), cpu_id, iommu_map_4k_syscall_range(va, range), iommu_map_4k_syscall_range(iova, range)),
        iommu_map_4k_enter_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id, iommu_map_4k_syscall_range(va, range), iommu_map_4k_syscall_range(iova, range)),
{
    reveal(iommu_map_4k_enter_step_pre); reveal(iommu_map_4k_enter_step);
    assert(pre.prc_mp.dom().contains(process_ptr) && !pre.prc_mp.spec_index(process_ptr).view().zombie && pre.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr
        && pre.pt_mp.dom().contains(pagetable_ptr) && pre.it_mp.dom().contains(iommu_table_ptr)) by { reveal(process_cpu_wf); reveal(process_pagetable_match); reveal(process_iommu_table_match); };
    kernel_cpu_process_thread_pagetable_iommu_table_lock_states_and_progress_changed_implies_u_step(pre, post, cpu_id, process_ptr, thread_ptr, pagetable_ptr, iommu_table_ptr);
    kernel_cpu_projection_at(pre, cpu_id); kernel_cpu_thread_projection_at(pre, cpu_id, process_ptr, thread_ptr, None);
    kernel_thread_projection_at(pre, thread_ptr); kernel_process_projection_at(pre, process_ptr);
}

/// Clearing progress, unlocking the cpu, its running thread and process and the IOMMU table, and dropping the read hold on
/// the page table after the whole range is mapped is the exit step.
pub(super) proof fn iommu_map_4k_exit_step_from_k(
    pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot, iommu_table_ptr: RwLockPageTableRoot,
)
    requires
        process_cpu_wf(pre.prc_mp, pre.cpu_arr),
        process_pagetable_match(pre.prc_mp, pre.pt_mp),
        process_iommu_table_match(pre.prc_mp, pre.it_mp),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(pre, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write),
        *post == (KernelK { cpu_arr: post.cpu_arr, cpu_op: post.cpu_op, prc_mp: post.prc_mp, thr_mp: post.thr_mp, pt_mp: post.pt_mp, pt_lower: post.pt_lower, it_mp: post.it_mp, ..*pre }),
        post.cpu_arr.entries_unchanged_except(&pre.cpu_arr, cpu_id),
        post.cpu_arr.spec_index(cpu_id).view().view().view() == pre.cpu_arr.spec_index(cpu_id).view().view().view(),
        pre.cpu_op.view().view().len() == NUM_CPUS,
        post.cpu_op.view().view() == pre.cpu_op.view().view().update(cpu_id as int, cpu_op_after_step(pre.cpu_arr.spec_index(cpu_id).view().view().view().state)),
        post.cpu_arr.spec_index(cpu_id).value.killer_info() == pre.cpu_arr.spec_index(cpu_id).value.killer_info(),
        post.cpu_arr.spec_index(cpu_id).value.being_killed() == pre.cpu_arr.spec_index(cpu_id).value.being_killed(),
        post.cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        post.prc_mp.unchanged_except(&pre.prc_mp, process_ptr),
        post.prc_mp.spec_index(process_ptr).view() == pre.prc_mp.spec_index(process_ptr).view(),
        post.prc_mp.spec_index(process_ptr).view_rodata() == pre.prc_mp.spec_index(process_ptr).view_rodata(),
        post.prc_mp.spec_index(process_ptr).view_ghost() == pre.prc_mp.spec_index(process_ptr).view_ghost(),
        post.prc_mp.spec_index(process_ptr).being_killed() == pre.prc_mp.spec_index(process_ptr).being_killed(),
        post.prc_mp.spec_index(process_ptr).locking_thread() is None,
        pre.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr,
        pre.prc_mp.spec_index(process_ptr).view().iommu_table == Some(iommu_table_ptr),
        pre.thr_mp.dom().contains(thread_ptr),
        pre.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is Some,
        pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0 is IommuMap4k,
        pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->IommuMap4k_mapped == pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->IommuMap4k_iova_range.len,
        pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->IommuMap4k_directory is None,
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..pre.thr_mp.spec_index(thread_ptr).view() }),
        post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None,
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
        post.thr_mp.spec_index(thread_ptr).locking_thread() is None,
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        post.pt_mp.spec_index(pagetable_ptr).view() == pre.pt_mp.spec_index(pagetable_ptr).view(),
        !(post.pt_mp.spec_index(pagetable_ptr).locking_thread() is Write),
        post.pt_lower.view() == pre.pt_lower.view().insert(pagetable_ptr, post.pt_lower.view().spec_index(pagetable_ptr)),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k(),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_2m() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m(),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_1g(),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks == pagetable_window_locks_after_unlocking_range(
            pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks, pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->IommuMap4k_va_range),
        post.it_mp.unchanged_except(&pre.it_mp, iommu_table_ptr),
        post.it_mp.spec_index(iommu_table_ptr).view() == pre.it_mp.spec_index(iommu_table_ptr).view(),
        post.it_mp.spec_index(iommu_table_ptr).locking_thread() is None,
    ensures
        iommu_map_4k_exit_step_pre(kernel_k_to_kernel_u(*pre), cpu_id),
        iommu_map_4k_exit_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id),
{
    reveal(iommu_map_4k_exit_step_pre); reveal(iommu_map_4k_exit_step);
    assert(pre.prc_mp.dom().contains(process_ptr) && !pre.prc_mp.spec_index(process_ptr).view().zombie) by { reveal(process_cpu_wf); };
    process_pagetable_match_process_at(pre.prc_mp, pre.pt_mp, process_ptr);
    kernel_cpu_process_thread_pagetable_iommu_table_lock_states_and_progress_changed_implies_u_step(pre, post, cpu_id, process_ptr, thread_ptr, pagetable_ptr, iommu_table_ptr);
    iommu_map_4k_locked_from_k(pre, lctx, cpu_id, process_ptr, thread_ptr, pagetable_ptr, iommu_table_ptr);
    kernel_cpu_projection_at(pre, cpu_id); kernel_thread_projection_at(pre, thread_ptr); kernel_process_projection_at(pre, process_ptr);
}

/// The running thread holding its cpu, process, and thread write locks, its page table's read lock, and its IOMMU table's
/// write lock gives the IOMMU-map lock state.
pub(super) proof fn iommu_map_4k_locked_from_k(
    krnl: &KernelK, lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot,
    iommu_table_ptr: RwLockPageTableRoot,
)
    requires
        process_cpu_wf(krnl.prc_mp, krnl.cpu_arr),
        process_pagetable_match(krnl.prc_mp, krnl.pt_mp),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        krnl.thr_mp.dom().contains(thread_ptr),
        krnl.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        krnl.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr,
        krnl.prc_mp.spec_index(process_ptr).view().iommu_table == Some(iommu_table_ptr),
    ensures
        iommu_map_4k_locked(kernel_k_to_kernel_u(*krnl), cpu_id),
{
    assert(krnl.prc_mp.dom().contains(process_ptr) && !krnl.prc_mp.spec_index(process_ptr).view().zombie && krnl.pt_mp.dom().contains(pagetable_ptr)) by {
        reveal(process_cpu_wf); reveal(process_pagetable_match);
    };
    kernel_write_held_context_projection(krnl, lctx, cpu_id, process_ptr, thread_ptr, None);
    krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
    kernel_process_projection_at(krnl, process_ptr);
}

/// Publishing the page table's entry for the next va at the next iova of the write-held IOMMU table and recording its page's
/// IOMMU mapping (`pre` to `mid`), then advancing progress (`mid` to `post`) under the IOMMU-map locks is one leaf step.
pub(super) proof fn iommu_map_4k_leaf_step_from_k(
    pre: &KernelK, mid: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot,
    iommu_table_ptr: RwLockPageTableRoot,
)
    requires
        process_cpu_wf(pre.prc_mp, pre.cpu_arr),
        process_pagetable_match(pre.prc_mp, pre.pt_mp),
        process_iommu_table_match(pre.prc_mp, pre.it_mp),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(pre, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        pre.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr,
        pre.thr_mp.dom().contains(thread_ptr),
        pre.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        pre.prc_mp.spec_index(process_ptr).view().iommu_table == Some(iommu_table_ptr),
        pre.it_mp.spec_index(iommu_table_ptr).view().leaves_present(),
        ({
            let progress = pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view();
            let table = pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr);
            let va = progress->Some_0->IommuMap4k_va_range.view()[progress->Some_0->IommuMap4k_mapped as int];
            let iova = progress->Some_0->IommuMap4k_iova_range.view()[progress->Some_0->IommuMap4k_mapped as int];
            &&& progress is Some && progress->Some_0 is IommuMap4k
            &&& progress->Some_0->IommuMap4k_mapped < progress->Some_0->IommuMap4k_iova_range.len
            &&& progress->Some_0->IommuMap4k_iova_range.len == progress->Some_0->IommuMap4k_va_range.len
            &&& table.mapping_4k().dom().contains(va) && table.mapping_4k()[va].present
            &&& !pre.it_mp.spec_index(iommu_table_ptr).view().mapping_4k().dom().contains(iova)
            &&& mid.it_mp.spec_index(iommu_table_ptr).view().mapping_4k() == pre.it_mp.spec_index(iommu_table_ptr).view().mapping_4k().insert(iova, table.mapping_4k()[va])
        }),
        *mid == (KernelK { it_mp: mid.it_mp, pg_arr: mid.pg_arr, ..*pre }),
        mid.it_mp.unchanged_except(&pre.it_mp, iommu_table_ptr),
        mid.it_mp.spec_index(iommu_table_ptr).locking_thread() == pre.it_mp.spec_index(iommu_table_ptr).locking_thread(),
        mid.it_mp.spec_index(iommu_table_ptr).view().proc_ptr == pre.it_mp.spec_index(iommu_table_ptr).view().proc_ptr,
        mid.it_mp.spec_index(iommu_table_ptr).view().mapping_2m() == pre.it_mp.spec_index(iommu_table_ptr).view().mapping_2m(),
        mid.it_mp.spec_index(iommu_table_ptr).view().mapping_1g() == pre.it_mp.spec_index(iommu_table_ptr).view().mapping_1g(),
        mid.it_mp.spec_index(iommu_table_ptr).view().did == pre.it_mp.spec_index(iommu_table_ptr).view().did,
        *post == (KernelK { thr_mp: post.thr_mp, ..*mid }),
        post.thr_mp.unchanged_except(&mid.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..mid.thr_mp.spec_index(thread_ptr).view() }),
        post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == iommu_map_4k_progress_after_leaf(pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()),
        post.thr_mp.spec_index(thread_ptr).being_killed() == mid.thr_mp.spec_index(thread_ptr).being_killed(),
        post.thr_mp.spec_index(thread_ptr).locking_thread() == mid.thr_mp.spec_index(thread_ptr).locking_thread(),
    ensures
        iommu_map_4k_leaf_step_pre(kernel_k_to_kernel_u(*pre), cpu_id),
        iommu_map_4k_leaf_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id),
{
    reveal(iommu_map_4k_leaf_step_pre); reveal(iommu_map_4k_leaf_step);
    iommu_map_4k_locked_from_k(pre, lctx, cpu_id, process_ptr, thread_ptr, pagetable_ptr, iommu_table_ptr);
    let progress = pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view();
    let table = pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr);
    let va = progress->Some_0->IommuMap4k_va_range.view()[progress->Some_0->IommuMap4k_mapped as int];
    let iova = progress->Some_0->IommuMap4k_iova_range.view()[progress->Some_0->IommuMap4k_mapped as int];
    assert(pre.prc_mp.dom().contains(process_ptr) && !pre.prc_mp.spec_index(process_ptr).view().zombie && pre.pt_mp.dom().contains(pagetable_ptr) && pre.it_mp.dom().contains(iommu_table_ptr)
        && pre.it_mp.spec_index(iommu_table_ptr).view().proc_ptr == process_ptr) by { reveal(process_cpu_wf); reveal(process_pagetable_match); reveal(process_iommu_table_match); };
    kernel_iommu_table_4k_mapping_added_implies_u_step(pre, mid, iommu_table_ptr, iova, table.mapping_4k()[va]);
    kernel_thread_syscall_progress_changed_implies_u_step(mid, post, thread_ptr);
    kernel_cpu_projection_at(pre, cpu_id); kernel_thread_projection_at(pre, thread_ptr); kernel_process_projection_at(pre, process_ptr);
}

/// Installing one IOMMU directory page of the write-held IOMMU table from the running thread's quota and recording a deeper
/// level under the IOMMU-map locks is one directory step.
pub(super) proof fn iommu_map_4k_directory_step_from_k(
    pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot,
    iommu_table_ptr: RwLockPageTableRoot, level: MissingPageTableLevel,
)
    requires
        process_cpu_wf(pre.prc_mp, pre.cpu_arr),
        process_pagetable_match(pre.prc_mp, pre.pt_mp),
        process_iommu_table_match(pre.prc_mp, pre.it_mp),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(pre, lctx),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write),
        pre.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr,
        *post == (KernelK { it_mp: post.it_mp, pg_arr: post.pg_arr, thr_mp: post.thr_mp, ..*pre }),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        pre.thr_mp.dom().contains(thread_ptr),
        pre.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        pre.prc_mp.spec_index(process_ptr).view().iommu_table == Some(iommu_table_ptr),
        post.it_mp.unchanged_except(&pre.it_mp, iommu_table_ptr),
        post.it_mp.spec_index(iommu_table_ptr).locking_thread() == pre.it_mp.spec_index(iommu_table_ptr).locking_thread(),
        post.it_mp.spec_index(iommu_table_ptr).view().mapping_4k() == pre.it_mp.spec_index(iommu_table_ptr).view().mapping_4k(),
        post.it_mp.spec_index(iommu_table_ptr).view().mapping_2m() == pre.it_mp.spec_index(iommu_table_ptr).view().mapping_2m(),
        post.it_mp.spec_index(iommu_table_ptr).view().mapping_1g() == pre.it_mp.spec_index(iommu_table_ptr).view().mapping_1g(),
        post.it_mp.spec_index(iommu_table_ptr).view().did == pre.it_mp.spec_index(iommu_table_ptr).view().did,
        ({
            let progress = pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view();
            &&& progress is Some && progress->Some_0 is IommuMap4k
            &&& progress->Some_0->IommuMap4k_mapped < progress->Some_0->IommuMap4k_iova_range.len
            &&& mmap_4k_directory_rank(progress->Some_0->IommuMap4k_directory) < mmap_4k_directory_rank(mmap_4k_installed_directory(level))
        }),
        pre.thr_mp.spec_index(thread_ptr).view().quota_4k >= 1,
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread {
            quota_4k: post.thr_mp.spec_index(thread_ptr).view().quota_4k, temp_alloc_cache_4k: post.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k,
            syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..pre.thr_mp.spec_index(thread_ptr).view()
        }),
        post.thr_mp.spec_index(thread_ptr).view().quota_4k == pre.thr_mp.spec_index(thread_ptr).view().quota_4k - 1,
        post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == iommu_map_4k_progress_after_directory(pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(), level),
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
        post.thr_mp.spec_index(thread_ptr).locking_thread() == pre.thr_mp.spec_index(thread_ptr).locking_thread(),
    ensures
        iommu_map_4k_directory_step_pre(kernel_k_to_kernel_u(*pre), cpu_id),
        iommu_map_4k_directory_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id),
{
    reveal(iommu_map_4k_directory_step_pre); reveal(iommu_map_4k_directory_step);
    iommu_map_4k_locked_from_k(pre, lctx, cpu_id, process_ptr, thread_ptr, pagetable_ptr, iommu_table_ptr);
    kernel_thread_quota_4k_progress_and_iommu_table_structure_changed_implies_u_step(pre, post, thread_ptr, iommu_table_ptr);
    kernel_cpu_projection_at(pre, cpu_id); kernel_thread_projection_at(pre, thread_ptr);
}

/// The enter step recorded on an empty trace starts the IOMMU-map trace.
pub(super) proof fn iommu_map_4k_trace_enter(steps: Seq<KernelStep>, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, va_range: VaRange4K, iova_range: VaRange4K)
    requires
        before.len() == 0,
        steps == before.push(KernelStep { old_u: pre, new_u: post }),
        iommu_map_4k_enter_step_pre(pre, cpu_id, va_range, iova_range),
        iommu_map_4k_enter_step(pre, post, cpu_id, va_range, iova_range),
    ensures
        steps.len() == 1,
        iommu_map_4k_enter_step_pre(steps[0].old_u, cpu_id, va_range, iova_range),
        iommu_map_4k_enter_step(steps[0].old_u, steps[0].new_u, cpu_id, va_range, iova_range),
{}

/// A directory or leaf step pushed after the enter step and earlier range steps keeps every later step a range step.
pub(super) proof fn iommu_map_4k_trace_push_range_step(steps: Seq<KernelStep>, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, va_range: VaRange4K, iova_range: VaRange4K)
    requires
        before.len() >= 1,
        iommu_map_4k_enter_step_pre(before[0].old_u, cpu_id, va_range, iova_range),
        iommu_map_4k_enter_step(before[0].old_u, before[0].new_u, cpu_id, va_range, iova_range),
        forall|j: int| #![trigger before[j]] 0 < j < before.len() ==> iommu_map_4k_range_step(before[j], cpu_id),
        steps == before.push(KernelStep { old_u: pre, new_u: post }),
        (iommu_map_4k_directory_step_pre(pre, cpu_id) && iommu_map_4k_directory_step(pre, post, cpu_id)) || (iommu_map_4k_leaf_step_pre(pre, cpu_id) && iommu_map_4k_leaf_step(pre, post, cpu_id)),
    ensures
        steps.len() == before.len() + 1,
        iommu_map_4k_enter_step_pre(steps[0].old_u, cpu_id, va_range, iova_range),
        iommu_map_4k_enter_step(steps[0].old_u, steps[0].new_u, cpu_id, va_range, iova_range),
        forall|j: int| #![trigger steps[j]] 0 < j < steps.len() ==> iommu_map_4k_range_step(steps[j], cpu_id),
{
    reveal(iommu_map_4k_range_step);
}

/// The exit step pushed after the enter step and the range steps completes the IOMMU-map trace.
pub(super) proof fn iommu_map_4k_trace_exit(steps: Seq<KernelStep>, before: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, va_range: VaRange4K, iova_range: VaRange4K)
    requires
        va_range.len + 1 <= before.len() <= 4 * va_range.len + 1,
        iommu_map_4k_enter_step_pre(before[0].old_u, cpu_id, va_range, iova_range),
        iommu_map_4k_enter_step(before[0].old_u, before[0].new_u, cpu_id, va_range, iova_range),
        forall|j: int| #![trigger before[j]] 0 < j < before.len() ==> iommu_map_4k_range_step(before[j], cpu_id),
        steps == before.push(KernelStep { old_u: pre, new_u: post }),
        iommu_map_4k_exit_step_pre(pre, cpu_id),
        iommu_map_4k_exit_step(pre, post, cpu_id),
    ensures
        iommu_map_4k_syscall_trace(steps, cpu_id, va_range, iova_range),
{
    reveal(iommu_map_4k_syscall_trace);
}
} // verus!
