---
name: project_iommu_identity_and_static_root_table
description: Current IOMMU identity, ownership, static VT-d root-table, and IOTLB model
metadata:
  node_type: memory
  type: project
---

# IOMMU model

## Identity and ownership

- There is no software IOID or hardware-DID allocator. Legacy VT-d DID is
  derived from BDF as `(bus * 256) + (device * 8) + function`.
- A process has at most one IOMMU page table through
  `Process::iommu_table: Option<RwLockPageTableRoot>`. The table object/root is
  its software identity; it carries no separate DID.
- Every valid BDF has exactly one process owner, independently of whether DMA
  translation is enabled. `None` in the root-table interface means the context
  entry is not present; it does not remove ownership.
- `Process::owned_pci_functions` is the reverse index and
  `pci_function_ref_counter` equals its length. Together with
  `process_pci_function_ownership_wf`, a zero counter proves that no BDF slot
  names the process without scanning all 65,536 slots.

## Static root table

- `IommuRootTable` is an opaque, pinned legacy VT-d image with logical
  `owners` and `iommu_roots` `Seq3` views. External specs should use
  `spec_index_owner` and `spec_index_iommu_root`, not nested sequence indexing.
- Physical lookup is root entry `[bus]`, then context entry
  `[(device << 3) | function]`. The object contains one 4 KiB root page, 256
  4 KiB context tables, and 128 pages of owner metadata: 385 pages / 1,576,960
  bytes total.
- The object must remain pinned after its embedded addresses are initialized;
  never construct or return it as a large stack value.
- Boot code still needs to establish that hardware `CAP.ND` supports the full
  active BDF-derived DID range.

## IOTLB

- The current model has one global `IommuTLB` for one VT-d remapping unit. Its
  domain map is keyed by the BDF-derived DID; each `SingleIotlb` has separate
  4K/2M/1G translation maps.
- `iommu_tlb_wf_spec` ties cached entries to the owner process's IOMMU table. A
  BDF with no present root must have an empty domain IOTLB even though ownership
  remains assigned.
- There is no IOTLB dirty bitmap. Invalidation is modeled as monotonic removal,
  allowing hardware to invalidate more broadly than requested.
- Context-cache state, ATS/device-TLB state, executable invalidation primitives,
  and DMA reverse-mapping/refcount rules remain future work unless live code now
  says otherwise.

Primary code: `src/iommu/root_table.rs`, `src/iommu/iotlb.rs`,
`src/kernel/process_management/process_pci_function_spec.rs`, and
`src/kernel/iommu_tlb_management/iotlb_wf_spec.rs`.
