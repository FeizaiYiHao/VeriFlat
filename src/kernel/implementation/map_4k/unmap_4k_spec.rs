use vstd::prelude::*;
use crate::*;

verus! {
/// Longest unmap_4k range flushed per address, a longer one flushes the whole PCID: one INVPCID costs about 142 cycles, a CR3 reload about 380 plus the refill of the working set (KVM, 2026-11-05).
pub const TLB_FLUSH_VA_RANGE_MAX_PAGES_4K: usize = 8;
/// Longest unmap_2m range flushed per address, a longer one flushes the whole PCID: one INVPCID costs about 142 cycles, a CR3 reload about 380, with no refill gain measured for 2M pages (KVM, 2026-11-05).
pub const TLB_FLUSH_VA_RANGE_MAX_PAGES_2M: usize = 2;

/// Every leaf of `table` the user cannot see in a window of `pagetable` that `window_lock_map` holds lies in a per-address
/// flush of `count` pages from `va`, 4K or 2M apart by `stride_2m`, and no such window's L2 entry hides its L1 page.
pub open spec fn held_windows_hidden_leaves_va_flushed(table: WholePageTable<PT_TYPE>, window_lock_map: Map<(RwLockPageTableRoot, WindowVa), TypedHeldLock>, pagetable: RwLockPageTableRoot,
    va: VAddr, count: usize, stride_2m: bool) -> bool
{
    &&& forall|w: WindowVa| #![trigger window_lock_map.dom().contains((pagetable, w))] window_lock_map.dom().contains((pagetable, w)) ==> {
        &&& !table.lower.l2_entry_hides_l1(table.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
        &&& table.mapping_2m().dom().contains(w.va) && !table.mapping_2m().spec_index(w.va).present ==> va_range_flush_drops_2m(va, count, stride_2m, w.va)
    }
    &&& forall|w: WindowVa, v: VAddr| #![trigger window_lock_map.dom().contains((pagetable, w)), table.mapping_4k().dom().contains(v)]
        window_lock_map.dom().contains((pagetable, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va)
            && table.mapping_4k().dom().contains(v) && !table.mapping_4k().spec_index(v).present ==> va_range_flush_drops_4k(va, count, stride_2m, v)
}

/// A leaf step clears the next VA of the recorded range, which is still mapped, before the flush.
#[verifier::opaque]
pub open spec fn unmap_4k_leaf_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& thread_pagetable_op_in_progress(old_u, cpu_id)
    &&& progress is Unmap4k
    &&& progress->Unmap4k_unmapped < progress->Unmap4k_range.len
    &&& !progress->Unmap4k_flushed
    &&& old_u.process_map.spec_index(thread.owning_proc).pagetable->Some_0.mapping_4k.dom().contains(progress->Unmap4k_range.view()[progress->Unmap4k_unmapped as int])
}

/// A leaf step removes the next VA of the recorded range from the process's user mapping and advances unmap progress.
#[verifier::opaque]
pub open spec fn unmap_4k_leaf_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let process = old_u.process_map.spec_index(thread.owning_proc);
    let pagetable = process.pagetable->Some_0;
    let progress = thread.syscall_progress->Some_0;
    let range = progress->Unmap4k_range;
    let unmapped = progress->Unmap4k_unmapped;
    new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: Some(SyscallProgress::Unmap4k { range, unmapped: (unmapped + 1) as usize, flushed: false }), ..thread }),
        process_map: old_u.process_map.insert(thread.owning_proc, ProcessU { pagetable: Some(PageTableU { mapping_4k: pagetable.mapping_4k.remove(range.view()[unmapped as int]), ..pagetable }), ..process }),
        ..old_u
    })
}

/// A flush step runs after every recorded VA has been cleared and before the flush is recorded, while the thread's
/// container exists.
#[verifier::opaque]
pub open spec fn unmap_4k_flush_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& thread_pagetable_op_in_progress(old_u, cpu_id)
    &&& old_u.container_map.dom().contains(thread.owning_container)
    &&& progress is Unmap4k
    &&& progress->Unmap4k_unmapped == progress->Unmap4k_range.len
    &&& !progress->Unmap4k_flushed
}

/// A TLB flush step takes or keeps this cpu's read hold on the cpu set of the thread's container and clears at most one
/// TLB entry for the process's PCID.
#[verifier::opaque]
pub open spec fn unmap_4k_tlb_flush_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let locked = KernelU {
        container_map: old_u.container_map.insert(thread.owning_container, ContainerU { cpu_set_lock: old_u.container_map.spec_index(thread.owning_container).cpu_set_lock.with_reader(cpu_id), ..old_u.container_map.spec_index(thread.owning_container) }),
        ..old_u
    };
    new_u == locked || kernel_u_cpu_tlb_cleared(locked, new_u, old_u.process_map.spec_index(thread.owning_proc).pcid)
}

/// A per-address TLB flush step takes or keeps this cpu's read hold on the cpu set of the thread's container, and every TLB
/// entry it changes is a flush of the `count` pages from `va`, 4K or 2M apart by `stride_2m`, under the process's PCID on
/// that entry's cpu, which changes no other entry.
#[verifier::opaque]
pub open spec fn unmap_4k_tlb_va_flush_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, va: VAddr, count: usize, stride_2m: bool) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let pcid = old_u.process_map.spec_index(thread.owning_proc).pcid;
    let locked = KernelU {
        container_map: old_u.container_map.insert(thread.owning_container, ContainerU { cpu_set_lock: old_u.container_map.spec_index(thread.owning_container).cpu_set_lock.with_reader(cpu_id), ..old_u.container_map.spec_index(thread.owning_container) }),
        ..old_u
    };
    new_u == locked || ({
        &&& new_u == (KernelU { cpu_tlb: new_u.cpu_tlb, ..locked })
        &&& locked.cpu_tlb.dom().subset_of(new_u.cpu_tlb.dom())
        &&& forall|key: (CpuId, Pcid)| #![trigger new_u.cpu_tlb.dom().contains(key)]
            new_u.cpu_tlb.dom().contains(key) && !(locked.cpu_tlb.dom().contains(key) && locked.cpu_tlb[key] == new_u.cpu_tlb[key])
                ==> key.1 == pcid && kernel_u_cpu_tlb_va_flushed(locked, new_u, key.0, pcid, va, count, stride_2m)
    })
}

/// Recording the flush changes unmap progress and releases this cpu's read hold on the cpu set of the thread's container.
#[verifier::opaque]
pub open spec fn unmap_4k_flushed_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    let progress = thread.syscall_progress->Some_0;
    let cpu_set_lock = old_u.container_map.spec_index(thread.owning_container).cpu_set_lock;
    &&& cpu_set_lock.read_held_by(cpu_id)
    &&& new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: Some(SyscallProgress::Unmap4k { range: progress->Unmap4k_range, unmapped: progress->Unmap4k_unmapped, flushed: true }), ..thread }),
        container_map: old_u.container_map.insert(thread.owning_container, ContainerU { cpu_set_lock: cpu_set_lock.without_reader(cpu_id), ..old_u.container_map.spec_index(thread.owning_container) }),
        ..old_u
    })
}

/// A refund step, and the exit step, run after every page of the recorded range has been cleared and the flush has been
/// recorded.
#[verifier::opaque]
pub open spec fn unmap_4k_refund_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& thread_pagetable_op_in_progress(old_u, cpu_id)
    &&& progress is Unmap4k
    &&& progress->Unmap4k_unmapped == progress->Unmap4k_range.len
    &&& progress->Unmap4k_flushed
}

/// A step inside the unmap range clears one leaf, flushes on one cpu the process's PCID or, for a range of at most
/// `TLB_FLUSH_VA_RANGE_MAX_PAGES_4K` pages, the range's addresses, records the flush, or refunds 4K quota to the thread's
/// container chain.
#[verifier::opaque]
pub open spec fn unmap_4k_range_step(step: KernelStep, cpu_id: CpuId) -> bool {
    let thread = step.old_u.thread_map.spec_index(step.old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let range = thread.syscall_progress->Some_0->Unmap4k_range;
    ||| unmap_4k_leaf_step_pre(step.old_u, cpu_id) && unmap_4k_leaf_step(step.old_u, step.new_u, cpu_id)
    ||| unmap_4k_flush_step_pre(step.old_u, cpu_id) && TLB_FLUSH_VA_RANGE_MAX_PAGES_4K < range.len && unmap_4k_tlb_flush_step(step.old_u, step.new_u, cpu_id)
    ||| unmap_4k_flush_step_pre(step.old_u, cpu_id) && range.len <= TLB_FLUSH_VA_RANGE_MAX_PAGES_4K && unmap_4k_tlb_va_flush_step(step.old_u, step.new_u, cpu_id, range.start, range.len, false)
    ||| unmap_4k_flush_step_pre(step.old_u, cpu_id) && unmap_4k_flushed_step(step.old_u, step.new_u, cpu_id)
    ||| unmap_4k_refund_step_pre(step.old_u, cpu_id) && kernel_u_container_quota_4k_increased(step.old_u, step.new_u, thread.owning_container)
}
} // verus!
