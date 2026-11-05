use vstd::prelude::*;
use crate::*;

verus! {
/// The cpu and its running thread are write-locked, and the pagetable of the thread's process is locked in either mode.
pub open spec fn thread_pagetable_op_locked(u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = u.cpu_array[cpu_id as int].current_thread->Some_0;
    let prc_ptr = u.thread_map.spec_index(thrd_ptr).owning_proc;
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& u.cpu_array[cpu_id as int].lock_state is WriteLocked
    &&& u.cpu_array[cpu_id as int].current_thread is Some
    &&& u.thread_map.dom().contains(thrd_ptr)
    &&& u.thread_map.spec_index(thrd_ptr).lock_state is WriteLocked
    &&& u.process_map.dom().contains(prc_ptr)
    &&& u.process_map.spec_index(prc_ptr).pagetable is Some
    &&& !(u.process_map.spec_index(prc_ptr).pagetable->Some_0.lock_state is Unlocked)
}

/// A pagetable operation holds its locks and the running thread records a syscall in progress.
pub open spec fn thread_pagetable_op_in_progress(old_u: KernelU, cpu_id: CpuId) -> bool {
    &&& thread_pagetable_op_locked(old_u, cpu_id)
    &&& old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0).syscall_progress is Some
}

/// At syscall entry the live running cpu runs its live current thread, which belongs to the cpu's current process and
/// has no syscall in progress.
pub open spec fn cpu_runs_live_thread_at_entry(old_u: KernelU, cpu_id: CpuId) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let thread = old_u.thread_map[cpu.current_thread->Some_0];
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.state is Running
    &&& !cpu.killed
    &&& cpu.current_process is Some
    &&& cpu.current_thread is Some
    &&& old_u.process_map.dom().contains(cpu.current_process->Some_0)
    &&& old_u.thread_map.dom().contains(cpu.current_thread->Some_0)
    &&& thread.owning_proc == cpu.current_process->Some_0
    &&& thread.state == (ThreadState::RUNNING { cpu_id })
    &&& thread.syscall_progress is None
    &&& !thread.killed
}

/// `va` keys an entry of `o` in its 4K, 2M or 1G mappings or its window locks that `n` no longer keys.
pub open spec fn process_table_key_dropped(o: PageTableU, n: PageTableU, va: VAddr) -> bool {
    ||| o.mapping_4k.dom().contains(va) && !n.mapping_4k.dom().contains(va)
    ||| o.mapping_2m.dom().contains(va) && !n.mapping_2m.dom().contains(va)
    ||| o.mapping_1g.dom().contains(va) && !n.mapping_1g.dom().contains(va)
    ||| o.pagetable_window_locks.dom().contains(WindowVa { va }) && !n.pagetable_window_locks.dom().contains(WindowVa { va })
}

/// Hiding a root entry of process `prc_ptr`'s page table drops from that table every 4K, 2M and 1G mapping and every window
/// lock under one root entry chosen by the kernel and keeps everything else: every dropped key shares one L4 index, and every
/// key with that index is dropped.
#[verifier::opaque]
pub open spec fn process_table_hidden_step(old_u: KernelU, new_u: KernelU, prc_ptr: RwLockProcessPtr) -> bool {
    let process = old_u.process_map[prc_ptr];
    let o = process.pagetable->Some_0;
    let n = new_u.process_map[prc_ptr].pagetable->Some_0;
    &&& process.pagetable is Some
    &&& n.mapping_4k.dom().subset_of(o.mapping_4k.dom()) && n.mapping_2m.dom().subset_of(o.mapping_2m.dom()) && n.mapping_1g.dom().subset_of(o.mapping_1g.dom())
    &&& n.pagetable_window_locks.dom().subset_of(o.pagetable_window_locks.dom())
    &&& forall|a: VAddr, b: VAddr| #![trigger process_table_key_dropped(o, n, a), process_table_key_dropped(o, n, b)]
        process_table_key_dropped(o, n, a) && process_table_key_dropped(o, n, b) ==> spec_v2l4index(a) == spec_v2l4index(b)
    &&& forall|a: VAddr, b: VAddr| #![trigger process_table_key_dropped(o, n, a), spec_v2l4index(b)]
        process_table_key_dropped(o, n, a) && spec_v2l4index(b) == spec_v2l4index(a) ==> !n.mapping_4k.dom().contains(b) && !n.mapping_2m.dom().contains(b) && !n.mapping_1g.dom().contains(b) && !n.pagetable_window_locks.dom().contains(WindowVa { va: b })
    &&& new_u == (KernelU {
        process_map: old_u.process_map.insert(prc_ptr, ProcessU {
            pagetable: Some(PageTableU {
                mapping_4k: o.mapping_4k.restrict(n.mapping_4k.dom()), mapping_2m: o.mapping_2m.restrict(n.mapping_2m.dom()), mapping_1g: o.mapping_1g.restrict(n.mapping_1g.dom()),
                pagetable_window_locks: o.pagetable_window_locks.restrict(n.pagetable_window_locks.dom()), ..o
            }),
            ..process
        }),
        ..old_u
    })
}

/// No valid user VA at or above the kernel's L4 end has a 4K mapping in `pagetable`.
pub open spec fn process_user_4k_unmapped(u: KernelU, pagetable: PageTableU) -> bool {
    forall|va: VAddr| #![trigger pagetable.mapping_4k.dom().contains(va)] spec_va_4k_valid(va) && u.kernel_l4_end <= spec_v2l4index(va) ==> !pagetable.mapping_4k.dom().contains(va)
}

/// No IOVA has a 4K mapping in `iommu_table`.
pub open spec fn process_iommu_4k_unmapped(iommu_table: PageTableU) -> bool {
    forall|iova: VAddr| #![trigger iommu_table.mapping_4k.dom().contains(iova)] !iommu_table.mapping_4k.dom().contains(iova)
}
} // verus!
