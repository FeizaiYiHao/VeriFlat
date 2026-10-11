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
- `ProcessGhost.owned_pci_functions` (lock-free ghost) is the reverse index;
  the root-table lock serializes its updates. `process_pci_function_ownership_wf`
  aligns it with the owner slots both ways and keeps a zombie's set empty.
  There is no exec counter.
- Ownership moves only through an IPC `Pci` rendezvous: the slot's owner and
  both reverse sets change, the function is detached, and its IOTLB domain is
  emptied in the same step. `syscall_pci_attach_dma` attaches an owned
  function to its owner's IOMMU table through `ProcessRO.iommu_cr3`, the
  read-only mirror of that table's root; there is no detach syscall.

## Root table

- `KernelK.irt` is one `RwLock` over the whole table
  (`IOMMU_ROOT_TABLE_LOCK_MAJOR = IOMMU_TABLE_LOCK_MAJOR + 1`); it is taken and
  released inside one step and is not U-visible. Its exec operations are
  `owner`, `is_attached`, `set_owner`, `attach`, and `detach`; kernel code
  mutates it only through `iommu_subsystem_mutation.rs`.
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
  domain map is keyed by the BDF-derived DID; each domain reuses the CPU
  `SingleTLB` (4K/2M/1G maps keyed by IOVA).
- `iommu_tlb_wf_spec` only constrains cached translations: a BDF with no present
  root has an empty domain IOTLB even though ownership remains assigned, and a
  present root's domain IOTLB is a `single_tlb_subset_of_pagetable` of the owner's
  IOMMU table. Owner/table/root agreement lives in `iommu_root_table_process_wf`.
- The root-table lock also guards the IOTLB. The trusted primitive
  `IommuTLB::invalidate_domain` empties one domain; there is no IOTLB dirty
  bitmap.
- Context-cache state, ATS/device-TLB state, and DMA reverse-mapping/refcount
  rules remain future work unless live code now says otherwise.

## Shared page-table machinery

- CPU (`pt_mp`) and IOMMU (`it_mp`) tables are both `PageTable<TABLE_TYPE>` in
  `PageTableLockedMapOf<TABLE_TYPE>`. Their page states are
  `Allocated4k{AsPageTableRoot{table_type}}` and
  `Allocated4k{PageTable{pagetable_root, table_type}}`, so `pagetable_pages_wf`,
  `pagetables_inv`, `kernel_pagetable_nonlock_fields_unchanged`, and
  `pagetable_map_user_view` are generic over the table type.
- IOMMU tables are still only created empty; there is no IOMMU map/unmap path
  and no `wlock_iommu_table`. Adding IOMMU unmap needs the CPU-side
  hidden-leaves-only-when-wlocked rule in `iommu_table_perms_wf`.

Primary code: `src/iommu/root_table.rs`, `src/iommu/iotlb.rs`,
`src/kernel/memory_management/pages_pagetable_spec.rs`,
`src/kernel/process_management/process_pci_function_spec.rs`,
`src/kernel/iommu_tlb_management/iotlb_wf_spec.rs`,
`src/kernel/iommu_tlb_management/iommu_subsystem_mutation.rs`, and
`src/kernel/implementation/syscall_pci/`.
