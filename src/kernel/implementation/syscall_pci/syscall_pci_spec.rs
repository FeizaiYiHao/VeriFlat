use vstd::prelude::*;
use crate::*;

verus! {
/// The result of `syscall_pci_attach_dma` from the state at entry: the running process must be alive,
/// own `(bus, device, function)`, and have an IOMMU table, and the function must not be attached yet.
/// A cpu no longer Running or marked by a killer returns CpuIdle first.
pub open spec fn pci_attach_dma_syscall_result(pre: KernelU, cpu_id: CpuId, bus: usize, device: usize, function: usize) -> RetValueType {
    let process = pre.process_map[pre.cpu_array[cpu_id as int].current_process.unwrap()];
    if !(pre.cpu_array[cpu_id as int].state is Running) || pre.cpu_array[cpu_id as int].killed { RetValueType::CpuIdle }
    else if process.killed { RetValueType::ErrorProcessKilled }
    else if !process.owned_pci_functions.contains((bus, device, function)) { RetValueType::ErrorPciOwnerMismatch }
    else if process.iommu_table is None { RetValueType::ErrorPciNoIommuTable }
    else if pre.iommu_root_table.attached[bus as int][device as int][function as int] { RetValueType::ErrorPciAlreadyAttached }
    else { RetValueType::Success }
}

/// The cpu and the running process are unlocked; the process is alive, owns `(bus, device, function)`,
/// and has an IOMMU table, and the function is not attached.
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
    &&& process.owned_pci_functions.contains((bus, device, function))
    &&& process.iommu_table is Some
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
} // verus!
