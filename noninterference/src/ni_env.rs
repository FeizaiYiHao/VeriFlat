use vstd::prelude::*;
use crate::*;

verus! {
/// A cpu TLB fill changes only `cpu_tlb`, which no domain view contains.
pub proof fn cpu_tlb_filled_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, pcid: Pcid, added: SingleTLB, b: RwLockContainerPtr)
    requires kernel_u_cpu_tlb_filled_step(old_u, new_u, cpu_id, pcid, added),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(kernel_u_cpu_tlb_filled_step); }

/// The step of `cpu_tlb_filled_step_lr` preserves isolation, which does not read `cpu_tlb`.
pub proof fn cpu_tlb_filled_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, pcid: Pcid, added: SingleTLB, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        isolated(old_u, a, b),
        kernel_u_cpu_tlb_filled_step(old_u, new_u, cpu_id, pcid, added),
    ensures isolated(new_u, a, b),
{ reveal(kernel_u_cpu_tlb_filled_step); }

/// An IOTLB fill changes only `iommu_tlb`, which no domain view contains.
pub proof fn iommu_tlb_filled_step_lr(old_u: KernelU, new_u: KernelU, did: VtdDomainId, added: SingleTLB, b: RwLockContainerPtr)
    requires kernel_u_iommu_tlb_filled_step(old_u, new_u, did, added),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(kernel_u_iommu_tlb_filled_step); }

/// The step of `iommu_tlb_filled_step_lr` preserves isolation, which does not read `iommu_tlb`.
pub proof fn iommu_tlb_filled_step_iso(old_u: KernelU, new_u: KernelU, did: VtdDomainId, added: SingleTLB, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        isolated(old_u, a, b),
        kernel_u_iommu_tlb_filled_step(old_u, new_u, did, added),
    ensures isolated(new_u, a, b),
{ reveal(kernel_u_iommu_tlb_filled_step); }

/// An IOMMU context-cache fill leaves the user state unchanged.
pub proof fn iommu_context_cache_filled_step_lr(old_u: KernelU, new_u: KernelU, b: RwLockContainerPtr)
    requires kernel_u_iommu_context_cache_filled_step(old_u, new_u),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(kernel_u_iommu_context_cache_filled_step); }

/// The step of `iommu_context_cache_filled_step_lr` preserves isolation.
pub proof fn iommu_context_cache_filled_step_iso(old_u: KernelU, new_u: KernelU, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        isolated(old_u, a, b),
        kernel_u_iommu_context_cache_filled_step(old_u, new_u),
    ensures isolated(new_u, a, b),
{ reveal(kernel_u_iommu_context_cache_filled_step); }
} // verus!
