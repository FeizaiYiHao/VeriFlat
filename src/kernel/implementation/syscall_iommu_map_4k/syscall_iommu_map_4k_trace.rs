use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal};
use crate::*;
use super::syscall_iommu_map_4k_spec::*;

verus! {
/// The entry state's K facts on the running thread's cpu, process, page table, and IOMMU table decide the IOMMU-map result
/// `ret`.
pub(super) proof fn iommu_map_4k_result_from_k(krnl: &KernelK, cpu_id: CpuId, va: VAddr, iova: VAddr, range: usize, ret: RetValueType)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        ret is ErrorIommuIovaAlreadyMapped ==> iommu_map_4k_syscall_range(iova, range).wf(),
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
            &&& tabled && ret is ErrorIommuIovaAlreadyMapped ==> !it.spec_mapping_4k_range_empty(spec_va2index(iova), spec_va2index(iova_range.view()[range - 1]))
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
            if ret is ErrorIommuIovaAlreadyMapped {
                let it = krnl.it_mp.spec_index(process.iommu_table->Some_0).view();
                let iova_range = iommu_map_4k_syscall_range(iova, range);
                let end_iova = iova_range.view()[range - 1];
                let (a4, a3, a2, a1) = spec_va2index(iova);
                let (e4, e3, e2, e1) = spec_va2index(end_iova);
                iova_range.va_range_lemma();
                assert(end_iova == spec_va_add_range(iova, (range - 1) as usize) && spec_va_4k_valid(end_iova));
                spec_va_4k_valid_index_roundtrip(iova); spec_va_4k_valid_index_roundtrip(end_iova);
                assert(iova % 4096 == 0) by (bit_vector) requires spec_va_4k_valid(iova);
                if forall|j: int| #![trigger iova_range.view()[j]] 0 <= j < range ==> !it.mapping_4k().dom().contains(iova_range.view()[j]) {
                    assert forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger it.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                        pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_l4_index_path_le((a4, a3, a2, a1), (l4i, l3i, l2i, l1i))
                            && spec_l4_index_path_le((l4i, l3i, l2i, l1i), (e4, e3, e2, e1)) implies !it.mapping_4k().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))) by {
                        let v = spec_index2va((l4i, l3i, l2i, l1i));
                        assert(a4 < l4i || (a4 == l4i && (a3 < l3i || (a3 == l3i && (a2 < l2i || (a2 == l2i && a1 <= l1i))))));
                        assert(l4i < e4 || (l4i == e4 && (l3i < e3 || (l3i == e3 && (l2i < e2 || (l2i == e2 && l1i <= e1))))));
                        assert(spec_index2va((a4, a3, a2, a1)) <= spec_index2va((l4i, l3i, l2i, l1i))) by (bit_vector)
                            requires a4 < 512 && a3 < 512 && a2 < 512 && a1 < 512 && l4i < 512 && l3i < 512 && l2i < 512 && l1i < 512,
                                a4 < l4i || (a4 == l4i && (a3 < l3i || (a3 == l3i && (a2 < l2i || (a2 == l2i && a1 <= l1i)))));
                        assert(spec_index2va((l4i, l3i, l2i, l1i)) <= spec_index2va((e4, e3, e2, e1))) by (bit_vector)
                            requires e4 < 512 && e3 < 512 && e2 < 512 && e1 < 512 && l4i < 512 && l3i < 512 && l2i < 512 && l1i < 512,
                                l4i < e4 || (l4i == e4 && (l3i < e3 || (l3i == e3 && (l2i < e2 || (l2i == e2 && l1i <= e1)))));
                        assert(spec_index2va((l4i, l3i, l2i, l1i)) % 4096 == 0) by (bit_vector) requires l4i < 512 && l3i < 512 && l2i < 512 && l1i < 512;
                        assert(iova <= v <= end_iova && v % 4096 == 0);
                        let k = (v / 4096 - iova / 4096) as usize;
                        assert(v == (v / 4096) * 4096 && iova == (iova / 4096) * 4096) by (nonlinear_arith) requires v % 4096 == 0, iova % 4096 == 0;
                        assert(0 <= k < range && v == iova + k * 4096);
                        assert(iova_range.view()[k as int] == spec_va_add_range(iova, k));
                    };
                    assert(it.spec_mapping_4k_range_empty((a4, a3, a2, a1), (e4, e3, e2, e1)));
                }
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
        *post == (KernelK { cpu_arr: post.cpu_arr, prc_mp: post.prc_mp, thr_mp: post.thr_mp, pt_mp: post.pt_mp, pt_lower: post.pt_lower, it_mp: post.it_mp, ..*pre }),
        !pre.cpu_arr.spec_index(cpu_id).value.locked(),
        post.cpu_arr.unchanged_except(&pre.cpu_arr, cpu_id),
        post.cpu_arr.spec_index(cpu_id).view().view() == pre.cpu_arr.spec_index(cpu_id).view().view(),
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
        !pre.it_mp.spec_index(iommu_table_ptr).locked(),
        post.it_mp.unchanged_except(&pre.it_mp, iommu_table_ptr),
        post.it_mp.spec_index(iommu_table_ptr).view() == pre.it_mp.spec_index(iommu_table_ptr).view(),
        post.it_mp.spec_index(iommu_table_ptr).locking_thread() is Write,
    ensures
        iommu_map_4k_enter_step_pre(kernel_k_to_kernel_u(*pre), cpu_id, iommu_map_4k_syscall_range(va, range), iommu_map_4k_syscall_range(iova, range)),
        iommu_map_4k_enter_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id, iommu_map_4k_syscall_range(va, range), iommu_map_4k_syscall_range(iova, range)),
{
    reveal(iommu_map_4k_enter_step_pre); reveal(iommu_map_4k_enter_step);
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let process = pre_u.process_map.spec_index(process_ptr);
    assert(pre.prc_mp.dom().contains(process_ptr) && !pre.prc_mp.spec_index(process_ptr).view().zombie && pre.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr
        && pre.pt_mp.dom().contains(pagetable_ptr) && pre.it_mp.dom().contains(iommu_table_ptr)) by { reveal(process_cpu_wf); reveal(process_pagetable_match); reveal(process_iommu_table_match); };
    kernel_cpu_projection_at(pre, cpu_id); kernel_cpu_thread_projection_at(pre, cpu_id, process_ptr, thread_ptr, None);
    kernel_thread_projection_at(pre, thread_ptr); kernel_thread_projection_at(post, thread_ptr);
    kernel_process_projection_at(pre, process_ptr); kernel_process_projection_at(post, process_ptr);
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, ..pre_u.cpu_array[cpu_id as int] }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); }
    });
    assert_maps_equal!(post_u.container_map, pre_u.container_map, c => {
        if pre.ctn_mp.dom().contains(c) { kernel_container_projection_at(pre, c); } if post.ctn_mp.dom().contains(c) { kernel_container_projection_at(post, c); }
    });
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(process_ptr, ProcessU {
        lock_state: LockStateU::WriteLocked, pagetable: Some(PageTableU { lock_state: LockStateU::ReadLocked, ..process.pagetable->Some_0 }),
        iommu_table: Some(PageTableU { lock_state: LockStateU::WriteLocked, ..process.iommu_table->Some_0 }), ..process
    }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); }
        reveal(process_pagetable_match); reveal(process_iommu_table_match);
    });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thread_ptr, ThreadU {
        lock_state: LockStateU::WriteLocked, syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(), ..pre_u.thread_map.spec_index(thread_ptr)
    }), t => { if pre.thr_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thr_mp.dom().contains(t) { kernel_thread_projection_at(post, t); } });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => {
        if pre.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(pre, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(post, e); }
    });
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
        *post == (KernelK { cpu_arr: post.cpu_arr, prc_mp: post.prc_mp, thr_mp: post.thr_mp, pt_mp: post.pt_mp, pt_lower: post.pt_lower, it_mp: post.it_mp, ..*pre }),
        post.cpu_arr.unchanged_except(&pre.cpu_arr, cpu_id),
        post.cpu_arr.spec_index(cpu_id).view().view() == pre.cpu_arr.spec_index(cpu_id).view().view(),
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
        post.it_mp.unchanged_except(&pre.it_mp, iommu_table_ptr),
        post.it_mp.spec_index(iommu_table_ptr).view() == pre.it_mp.spec_index(iommu_table_ptr).view(),
        post.it_mp.spec_index(iommu_table_ptr).locking_thread() is None,
    ensures
        iommu_map_4k_exit_step_pre(kernel_k_to_kernel_u(*pre), cpu_id),
        iommu_map_4k_exit_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id),
{
    reveal(iommu_map_4k_exit_step_pre); reveal(iommu_map_4k_exit_step);
    assert(pre.cpu_arr.spec_index(cpu_id).value.locking_thread() is Write) by { reveal(LockedArray::typed_lock_map_aligned); };
    pre.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), process_ptr); pre.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr);
    pre.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); pre.it_mp.typed_lock_map_aligned_write_at(lctx.iommu_table_lock_map(), lctx.thread_id(), iommu_table_ptr);
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let process = pre_u.process_map.spec_index(process_ptr);
    let table_lock = post.pt_mp.spec_index(pagetable_ptr).lock_state_u();
    assert(pre.prc_mp.dom().contains(process_ptr) && !pre.prc_mp.spec_index(process_ptr).view().zombie && pre.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr
        && pre.pt_mp.dom().contains(pagetable_ptr) && pre.it_mp.dom().contains(iommu_table_ptr)) by { reveal(process_cpu_wf); reveal(process_pagetable_match); reveal(process_iommu_table_match); };
    kernel_cpu_projection_at(pre, cpu_id); kernel_cpu_thread_projection_at(pre, cpu_id, process_ptr, thread_ptr, None);
    kernel_thread_projection_at(pre, thread_ptr); kernel_thread_projection_at(post, thread_ptr);
    kernel_process_projection_at(pre, process_ptr); kernel_process_projection_at(post, process_ptr);
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, ..pre_u.cpu_array[cpu_id as int] }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); }
    });
    assert_maps_equal!(post_u.container_map, pre_u.container_map, c => {
        if pre.ctn_mp.dom().contains(c) { kernel_container_projection_at(pre, c); } if post.ctn_mp.dom().contains(c) { kernel_container_projection_at(post, c); }
    });
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(process_ptr, ProcessU {
        lock_state: LockStateU::Unlocked, pagetable: Some(PageTableU { lock_state: table_lock, ..process.pagetable->Some_0 }),
        iommu_table: Some(PageTableU { lock_state: LockStateU::Unlocked, ..process.iommu_table->Some_0 }), ..process
    }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); }
        reveal(process_pagetable_match); reveal(process_iommu_table_match);
    });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thread_ptr, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..pre_u.thread_map.spec_index(thread_ptr) }), t => {
        if pre.thr_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thr_mp.dom().contains(t) { kernel_thread_projection_at(post, t); }
    });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => {
        if pre.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(pre, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(post, e); }
    });
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

/// Publishing the page table's entry for the next va at the next iova of the write-held IOMMU table, recording its page's
/// IOMMU mapping, and advancing progress under the IOMMU-map locks is one leaf step.
pub(super) proof fn iommu_map_4k_leaf_step_from_k(
    pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, pagetable_ptr: RwLockPageTableRoot,
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
        *post == (KernelK { it_mp: post.it_mp, pg_arr: post.pg_arr, thr_mp: post.thr_mp, ..*pre }),
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
            &&& post.it_mp.spec_index(iommu_table_ptr).view().mapping_4k() == pre.it_mp.spec_index(iommu_table_ptr).view().mapping_4k().insert(iova, table.mapping_4k()[va])
        }),
        post.it_mp.unchanged_except(&pre.it_mp, iommu_table_ptr),
        post.it_mp.spec_index(iommu_table_ptr).locking_thread() == pre.it_mp.spec_index(iommu_table_ptr).locking_thread(),
        post.it_mp.spec_index(iommu_table_ptr).view().mapping_2m() == pre.it_mp.spec_index(iommu_table_ptr).view().mapping_2m(),
        post.it_mp.spec_index(iommu_table_ptr).view().mapping_1g() == pre.it_mp.spec_index(iommu_table_ptr).view().mapping_1g(),
        pre.thr_mp.dom().contains(thread_ptr),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread_ptr),
        post.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..pre.thr_mp.spec_index(thread_ptr).view() }),
        post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == iommu_map_4k_progress_after_leaf(pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()),
        post.thr_mp.spec_index(thread_ptr).being_killed() == pre.thr_mp.spec_index(thread_ptr).being_killed(),
        post.thr_mp.spec_index(thread_ptr).locking_thread() == pre.thr_mp.spec_index(thread_ptr).locking_thread(),
    ensures
        iommu_map_4k_leaf_step_pre(kernel_k_to_kernel_u(*pre), cpu_id),
        iommu_map_4k_leaf_step(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id),
{
    reveal(iommu_map_4k_leaf_step_pre); reveal(iommu_map_4k_leaf_step);
    iommu_map_4k_locked_from_k(pre, lctx, cpu_id, process_ptr, thread_ptr, pagetable_ptr, iommu_table_ptr);
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let process = pre_u.process_map.spec_index(process_ptr);
    let progress = pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view();
    let table = pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr);
    let va = progress->Some_0->IommuMap4k_va_range.view()[progress->Some_0->IommuMap4k_mapped as int];
    let iova = progress->Some_0->IommuMap4k_iova_range.view()[progress->Some_0->IommuMap4k_mapped as int];
    let it = process.iommu_table->Some_0;
    assert(pre.prc_mp.dom().contains(process_ptr) && !pre.prc_mp.spec_index(process_ptr).view().zombie && pre.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr
        && pre.pt_mp.dom().contains(pagetable_ptr) && pre.it_mp.dom().contains(iommu_table_ptr)) by { reveal(process_cpu_wf); reveal(process_pagetable_match); reveal(process_iommu_table_match); };
    kernel_cpu_projection_at(pre, cpu_id); kernel_thread_projection_at(pre, thread_ptr); kernel_thread_projection_at(post, thread_ptr);
    kernel_process_projection_at(pre, process_ptr); kernel_process_projection_at(post, process_ptr);
    kernel_iommu_table_mappings_projection_at(pre, process_ptr);
    kernel_iommu_table_mappings_projection_at(post, process_ptr);
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(process_ptr, ProcessU {
        iommu_table: Some(PageTableU { mapping_4k: it.mapping_4k.insert(iova, process.pagetable->Some_0.mapping_4k.spec_index(va)), ..it }), ..process
    }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); }
        reveal(process_iommu_table_match);
    });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thread_ptr, ThreadU { syscall_progress: iommu_map_4k_progress_after_leaf(pre_u.thread_map[thread_ptr].syscall_progress), ..pre_u.thread_map[thread_ptr] }),
        t => { if pre.thr_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thr_mp.dom().contains(t) { kernel_thread_projection_at(post, t); } });
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); } });
    assert_maps_equal!(post_u.container_map, pre_u.container_map, c => {
        if pre.ctn_mp.dom().contains(c) { kernel_container_projection_at(pre, c); } if post.ctn_mp.dom().contains(c) { kernel_container_projection_at(post, c); }
    });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => {
        if pre.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(pre, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(post, e); }
    });
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
        pre.thr_mp.dom().contains(thread_ptr),
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
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    assert(pre.prc_mp.dom().contains(process_ptr) && pre.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr && pre.it_mp.dom().contains(iommu_table_ptr)) by {
        reveal(process_cpu_wf); reveal(process_iommu_table_match);
    };
    kernel_cpu_projection_at(pre, cpu_id); kernel_thread_projection_at(pre, thread_ptr); kernel_thread_projection_at(post, thread_ptr);
    assert_maps_equal!(post_u.process_map, pre_u.process_map, p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); }
        reveal(process_iommu_table_match);
    });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thread_ptr, ThreadU {
        quota_4k: (pre_u.thread_map[thread_ptr].quota_4k - 1) as usize, syscall_progress: post.thr_mp.spec_index(thread_ptr).view().syscall_progress.view(), ..pre_u.thread_map[thread_ptr]
    }), t => { if pre.thr_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thr_mp.dom().contains(t) { kernel_thread_projection_at(post, t); } });
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); } });
    assert_maps_equal!(post_u.container_map, pre_u.container_map, c => {
        if pre.ctn_mp.dom().contains(c) { kernel_container_projection_at(pre, c); } if post.ctn_mp.dom().contains(c) { kernel_container_projection_at(post, c); }
    });
    assert_maps_equal!(post_u.endpoint_map, pre_u.endpoint_map, e => {
        if pre.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(pre, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(post, e); }
    });
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
