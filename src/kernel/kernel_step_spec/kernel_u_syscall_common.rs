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
        process_table_key_dropped(o, n, a) && spec_v2l4index(b) == spec_v2l4index(a)
            ==> !n.mapping_4k.dom().contains(b) && !n.mapping_2m.dom().contains(b) && !n.mapping_1g.dom().contains(b) && !n.pagetable_window_locks.dom().contains(WindowVa { va: b })
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

/// No IOVA has a 4K mapping in `iommu_table`.
pub open spec fn process_iommu_4k_unmapped(iommu_table: PageTableU) -> bool {
    forall|iova: VAddr| #![trigger iommu_table.mapping_4k.dom().contains(iova)] !iommu_table.mapping_4k.dom().contains(iova)
}

/// The attached flags of `table` after every function in `functions` is detached.
pub open spec fn pci_functions_detached_attached(table: IommuRootTableU, functions: Set<PciBdf>) -> Seq3<bool> {
    Seq::new(PCI_BUS_COUNT as nat, |bus: int| Seq::new(PCI_DEVICE_COUNT as nat, |device: int| Seq::new(PCI_FUNCTION_COUNT as nat,
        |function: int| table.attached[bus][device][function] && !functions.contains((bus as usize, device as usize, function as usize)))))
}

/// Process `prc_ptr` gives up its PCI functions on cpu `cpu_id`: a process with an IOMMU table write-locks it, every
/// function of its page table's array is detached, the table drops its DID, and the IOTLB domain of that DID, if any, is
/// emptied; then every function of the array becomes unowned and the array is emptied.
pub open spec fn process_pci_functions_unowned(old_u: KernelU, new_u: KernelU, prc_ptr: RwLockProcessPtr, cpu_id: CpuId) -> bool {
    let process = old_u.process_map[prc_ptr];
    let pagetable = process.pagetable->Some_0;
    let functions = pagetable.pci_functions.dom();
    let table = old_u.iommu_root_table;
    new_u == (KernelU {
        process_map: old_u.process_map.insert(prc_ptr, ProcessU {
            pagetable: Some(PageTableU { pci_functions: Map::empty(), ..pagetable }),
            iommu_table: match process.iommu_table { Some(t) => Some(PageTableU { lock_state: LockStateU::WriteLocked { writer: cpu_id }, did: None, ..t }), None => None },
            ..process
        }),
        iommu_root_table: IommuRootTableU {
            owners: if functions == Set::<PciBdf>::empty() { table.owners } else { pci_owners_released(table.owners, functions) },
            attached: if process.iommu_table is Some { pci_functions_detached_attached(table, functions) } else { table.attached },
        },
        iommu_tlb: if process.iommu_table is Some && process.iommu_table->Some_0.did is Some {
            old_u.iommu_tlb.insert(process.iommu_table->Some_0.did->Some_0, SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })
        } else { old_u.iommu_tlb },
        ..old_u
    })
}

/// Exactly one 4K mapping leaves the write-locked IOMMU table of process `prc_ptr` and every other entry stays; the kernel
/// chooses the IOVA.
pub open spec fn process_iommu_leaf_removed(old_u: KernelU, new_u: KernelU, prc_ptr: RwLockProcessPtr) -> bool {
    let process = old_u.process_map[prc_ptr];
    let iommu_table = process.iommu_table->Some_0;
    let kept = new_u.process_map[prc_ptr].iommu_table->Some_0.mapping_4k.dom();
    let removed = iommu_table.mapping_4k.dom().difference(kept);
    &&& process.iommu_table is Some
    &&& iommu_table.lock_state is WriteLocked
    &&& kept.subset_of(iommu_table.mapping_4k.dom())
    &&& removed.len() == 1
    &&& new_u == (KernelU {
        process_map: old_u.process_map.insert(prc_ptr, ProcessU { iommu_table: Some(PageTableU { mapping_4k: iommu_table.mapping_4k.restrict(kept), ..iommu_table }), ..process }),
        ..old_u
    })
}

/// At most this many steps of a kill or an exit work on the tables of one process: 512 * 512 * 512 * 513 = 68,853,694,464
/// IOMMU cursor positions plus 10,000 for locking the tables, the hidden root entries, the TLB flushes, the refunds, the
/// quota and unlock steps, and for a kill the zombie, retire, and walk steps.
pub open spec fn process_tables_step_bound() -> nat { 68_853_704_464 }
} // verus!
