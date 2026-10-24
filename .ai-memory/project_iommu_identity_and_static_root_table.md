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
  aligns it with the owner slots both ways; a zombie keeps its functions.
  There is no exec counter.
- Ownership moves only through an IPC `Pci` rendezvous: the slot's owner and
  both reverse sets change, the function is detached, and its IOTLB domain is
  emptied in the same step. `syscall_pci_attach_dma` attaches an owned
  function to its owner's IOMMU table through `ProcessRO.iommu_cr3`, the
  read-only mirror of that table's root; there is no detach syscall.

## Root table

- `KernelK.irt` is one `RwLock` over the whole table
  (`IOMMU_ROOT_TABLE_LOCK_MAJOR = PAGE_TABLE_LOCK_MAJOR + 1`, below
  `IOMMU_TABLE_LOCK_MAJOR`, so exit can lock its IOMMU table under it); it is
  taken and released inside one step and is not U-visible. Its exec operations are
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
- `boot/kernel/src/iommu.rs::init_unit` checks `CAP.ND >= 6` (16-bit DIDs),
  `CAP.CM = 0`, 4-level SAGAW, `ECAP.C` (or hypervisor), and `ECAP.IR`, and
  panics otherwise.

## IOTLB

- `IommuTLB` holds one logical IOTLB and one logical context cache for all
  remapping units (they share the one root table). Both are `KernelK`-level,
  outside the root-table lock. The IOTLB domain map is keyed by the BDF-derived
  DID; each domain reuses the CPU `SingleTLB` (4K/2M/1G maps keyed by IOVA).
  `context_cache: Map<VtdDomainId, PageTableRoot>` is partial: a key means a
  unit may cache that DID's context entry, the value is its root.
- `iommu_tlb_wf_spec` only constrains cached state: a BDF with no present root
  has an empty domain IOTLB even though ownership remains assigned; a present
  root's domain IOTLB is a `single_tlb_subset_of_pagetable` of the owner's
  IOMMU table, and a `single_tlb_subset_of_present_pagetable` when that table
  is not write-locked; a cached context entry equals the current present root.
  Owner/table/root agreement lives in `iommu_root_table_process_wf`.
- The IOMMU table's write lock is the IOTLB dirty marker (`iommu_table_lock_wf`
  is deleted). A write holder may hide leaves of an attached table;
  `iommu_table_tlb_entries_present(iommu_tlb, root_table, it_mp, it)` is the
  per-table flushed fact, and `kernel_step_boundary_raw` and the step-boundary
  wrappers keep it for write-held IOMMU tables (TCB: hidden leaves are never
  re-cached, `CAP.CM = 0`).
- The trusted primitive `IommuTLB::invalidate_domain`, called under the
  root-table lock, drops the DID's context-cache key and empties its IOTLB
  domain together; the two detach helpers ensure the same.
  `IommuTLB::flush_all_iotlb` empties every domain, keeps the context cache,
  and takes no kernel lock (boot hook `veriflat_iommu_flush_all_iotlb` shares
  a platform spinlock with `veriflat_iommu_invalidate_domain`); the K helper
  `flush_iommu_tlb_for_table` wraps it and establishes the flushed fact.
- `CAP.CM = 0`, so only present roots and leaves are cached; attach and IOMMU
  map need no invalidation. Device-TLB is excluded by TT = 0
  (`IommuRootTable::wf`); paging-structure caches are folded into `SingleTLB`.

## Shared page-table machinery

- CPU (`pt_mp`) and IOMMU (`it_mp`) tables are both `PageTable<TABLE_TYPE>` in
  `PageTableLockedMapOf<TABLE_TYPE>`. Their page states are
  `Allocated4k{AsPageTableRoot{table_type}}` and
  `Allocated4k{PageTable{pagetable_root, table_type}}`, so `pagetable_pages_wf`,
  `pagetables_inv`, `kernel_pagetable_nonlock_fields_unchanged`, and
  `pagetable_map_user_view` are generic over the table type.
- IOMMU tables are created empty. `syscall_iommu_map_4k` maps pages already
  mapped in the caller's CPU page table into its IOMMU table (spec final, exec
  in progress). Unmap paths hide leaves with `clear_iommu_4k_mapping_present`
  under `wlock_iommu_table`, flush once with `flush_iommu_tlb_for_table`, then
  remove them with `reclaim_unmapped_iommu_4k_page`: `syscall_iommu_unmap_4k`,
  and the thread-exit and kill-process reclaim. `iommu_table_perms_wf` allows
  hidden leaves only while the table is write-locked.
- Pages count IOMMU references in `Page.iommu_mappings`; `ref_count` is
  `mappings.len() + iommu_mappings.len()`, and `page_iommu_table_wf` ties the
  set to the IOMMU tables' leaves.

Primary code: `src/iommu/root_table.rs`, `src/iommu/iotlb.rs`,
`src/kernel/memory_management/pages_pagetable_spec.rs`,
`src/kernel/process_management/process_pci_function_spec.rs`,
`src/kernel/iommu_tlb_management/iotlb_wf_spec.rs`,
`src/kernel/iommu_tlb_management/iommu_subsystem_mutation.rs`,
`src/kernel/implementation/syscall_pci/`,
`src/kernel/implementation/syscall_iommu_map_4k/`,
`src/kernel/implementation/syscall_iommu_unmap_4k/`, and
`src/kernel/implementation/map_4k/{map_iommu_4k,unmap_iommu_4k,flush_iommu_tlb}*.rs`.
