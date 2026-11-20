use vstd::prelude::*;
use crate::*;

verus! {
/// The result of `syscall_pci_attach_dma` from the state at entry: the running process must be alive,
/// hold `(bus, device, function)` in its page table's PCI function array, and have an IOMMU table, and the function must not be attached yet.
/// A cpu no longer Running or marked by a killer returns CpuIdle first.
pub open spec fn pci_attach_dma_syscall_result(pre: KernelU, cpu_id: CpuId, bus: usize, device: usize, function: usize) -> RetValueType {
    let cpu = pre.cpu_array[cpu_id as int];
    let process = pre.process_map[cpu.current_process.unwrap()];
    if !(cpu.state is Running) || cpu.killed { RetValueType::CpuIdle }
    else if process.killed { RetValueType::ErrorProcessKilled }
    else if !process.pagetable->Some_0.pci_functions.dom().contains((bus, device, function)) { RetValueType::ErrorPciOwnerMismatch }
    else if process.iommu_table is None { RetValueType::ErrorPciNoIommuTable }
    else if pre.iommu_root_table.attached[bus as int][device as int][function as int] { RetValueType::ErrorPciAlreadyAttached }
    else { RetValueType::Success }
}

/// The cpu, the running process, and its IOMMU table are unlocked; the process is alive, holds `(bus, device, function)` in
/// its page table's PCI function array, and has an IOMMU table, and the function is not attached.
#[verifier::opaque]
pub open spec fn pci_attach_dma_step_pre(old_u: KernelU, cpu_id: CpuId, bus: usize, device: usize, function: usize) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let process = old_u.process_map[cpu.current_process.unwrap()];
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is Unlocked
    &&& cpu.state is Running
    &&& cpu.current_process is Some
    &&& old_u.process_map.dom().contains(cpu.current_process.unwrap())
    &&& process.lock_state is Unlocked
    &&& !process.killed
    &&& pci_bdf_valid(bus, device, function)
    &&& process.pagetable is Some
    &&& process.pagetable->Some_0.pci_functions.dom().contains((bus, device, function))
    &&& process.iommu_table is Some
    &&& process.iommu_table->Some_0.lock_state is Unlocked
    &&& !old_u.iommu_root_table.attached[bus as int][device as int][function as int]
}

/// DMA translation of `(bus, device, function)` is attached; the caller's IOMMU table keeps its DID or, on first
/// attach, adopts the function's candidate DID. The IOTLB and context cache are unchanged.
pub open spec fn pci_attach_dma_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, bus: usize, device: usize, function: usize) -> bool {
    kernel_u_pci_attach_changed(old_u, new_u, cpu_id, bus, device, function)
}

/// Complete trace of the call; rejections stutter.
#[verifier::opaque]
pub open spec fn pci_attach_dma_syscall_trace(
    trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, bus: usize, device: usize, function: usize, ret: RetValueType,
) -> bool {
    if ret is Success {
        &&& trace.len() == 1
        &&& trace[0].old_u == pre
        &&& trace[0].new_u == post
        &&& pci_attach_dma_step_pre(pre, cpu_id, bus, device, function)
        &&& pci_attach_dma_step(pre, post, cpu_id, bus, device, function)
    } else {
        &&& trace.len() == 0
        &&& post == pre
    }
}

/// The result of `syscall_pci_claim` from the state at entry: the running process must be alive and the root process of the
/// root container, its page table's PCI function array must have a free entry, and `(bus, device, function)` must be
/// unowned. A cpu no longer Running or marked by a killer returns CpuIdle first.
pub open spec fn pci_claim_syscall_result(pre: KernelU, cpu_id: CpuId, bus: usize, device: usize, function: usize) -> RetValueType {
    let cpu = pre.cpu_array[cpu_id as int];
    let process = pre.process_map[cpu.current_process.unwrap()];
    if !(cpu.state is Running) || cpu.killed { RetValueType::CpuIdle }
    else if process.killed { RetValueType::ErrorProcessKilled }
    else if process.parent is Some || pre.container_map[process.owning_container].parent is Some { RetValueType::ErrorPciNotRootProcess }
    else if process.pagetable->Some_0.pci_functions.dom().len() >= PCI_FUNCTIONS_PER_PROCESS { RetValueType::ErrorPciFunctionArrayFull }
    else if pre.iommu_root_table.owners[bus as int][device as int][function as int] is Some { RetValueType::ErrorPciAlreadyOwned }
    else { RetValueType::Success }
}

/// The cpu, the running process, and its page table are unlocked; the process is alive and the root process of the root
/// container, its page table's PCI function array has a free entry, and `(bus, device, function)` is unowned.
#[verifier::opaque]
pub open spec fn pci_claim_step_pre(old_u: KernelU, cpu_id: CpuId, bus: usize, device: usize, function: usize) -> bool {
    let cpu = old_u.cpu_array[cpu_id as int];
    let process = old_u.process_map[cpu.current_process.unwrap()];
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& cpu.lock_state is Unlocked
    &&& cpu.state is Running
    &&& cpu.current_process is Some
    &&& old_u.process_map.dom().contains(cpu.current_process.unwrap())
    &&& process.lock_state is Unlocked
    &&& !process.killed
    &&& process.parent is None
    &&& old_u.container_map.dom().contains(process.owning_container)
    &&& old_u.container_map[process.owning_container].parent is None
    &&& process.pagetable is Some
    &&& process.pagetable->Some_0.lock_state is Unlocked
    &&& process.pagetable->Some_0.pci_functions.dom().len() < PCI_FUNCTIONS_PER_PROCESS
    &&& pci_bdf_valid(bus, device, function)
    &&& old_u.iommu_root_table.owners[bus as int][device as int][function as int] is None
}

/// `(bus, device, function)` enters the running process's PCI function array with no BAR mapping and becomes owned by it.
pub open spec fn pci_claim_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, bus: usize, device: usize, function: usize) -> bool {
    kernel_u_pci_claim_changed(old_u, new_u, cpu_id, bus, device, function)
}

/// Complete trace of the claim; rejections stutter.
#[verifier::opaque]
pub open spec fn pci_claim_syscall_trace(
    trace: Seq<KernelStep>, pre: KernelU, post: KernelU, cpu_id: CpuId, bus: usize, device: usize, function: usize, ret: RetValueType,
) -> bool {
    if ret is Success {
        &&& trace.len() == 1
        &&& trace[0].old_u == pre
        &&& trace[0].new_u == post
        &&& pci_claim_step_pre(pre, cpu_id, bus, device, function)
        &&& pci_claim_step(pre, post, cpu_id, bus, device, function)
    } else {
        &&& trace.len() == 0
        &&& post == pre
    }
}
} // verus!
