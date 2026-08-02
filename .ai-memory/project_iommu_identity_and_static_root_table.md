---
name: project_iommu_identity_and_static_root_table
description: VeriFlat IOMMU identity model and implemented static legacy VT-d root-table skeleton
---

IOMMU identity decision:

- There is no software IOID or hardware-DID allocator.
- A process has at most one IOMMU page table, represented directly by
  `Process::iommu_table: Option<RwLockPageTableRoot>`.
- `PageTable<IOMMU_TYPE>` carries no IOID/DID. Its identity is its table object
  and its `cr3`/second-stage root.
- Every PCI function has exactly one process owner. A process may own multiple
  functions. Translation enablement is independent of ownership: a function
  may remain owned while its root-table interface contains `None`.
- Each process maintains a runtime `pci_function_ref_counter` and a ghost
  `owned_pci_functions: Set<(bus, device, function)>`. `Process::inv` equates
  the counter with the set length and requires every member to be a valid BDF.
- `process_pci_function_ownership_wf` is bidirectional between the static root
  metadata owner and the process reverse set. Consequently a zero counter
  proves that no root-table BDF owner points to the process; the deletion path
  does not scan the 65,536 BDF slots at runtime.
- In legacy VT-d mode, the context-entry DID is derived from the requester ID:
  `(bus << 8) | (device << 3) | function`. This requires boot-time confirmation
  that VT-d `CAP.ND` supports the full active DID range.
- `IommuRootTable::wf` is opaque outside its module. Its only logical data
  interfaces are two three-dimensional sequences indexed by `[bus][device]
  [function]`: `owners: Seq3<RwLockProcessPtr>` and
  `iommu_roots: Seq3<Option<PageTableRoot>>`.
- External specs index those views only through `spec_index_owner(b, d, f)`
  and `spec_index_iommu_root(b, d, f)`. Both recommend `root_table.wf()` and a
  valid BDF; nested `Seq` indexing remains internal to the root-table module.
- The owner interface is total, so no BDF ownership slot can be leaked. The
  process/root-table ownership invariant requires every valid BDF's owner to
  exist in the process map and records the BDF in that process's reverse set.
- `None` in `iommu_roots` means that the VT-d context Present bit is clear; it
  does not remove ownership and the BDF still contributes to the process-local
  counter/set. `Some(root)` requires the owner to have an IOMMU table whose
  `cr3` equals `root`.
- DID, Present, translation type, address width, legacy context encoding, and
  physical root/context-table layout are internal consequences of the opaque
  root-table `wf`; external invariants use only the two sequence interfaces.

Static root-table skeleton:

- Use one 4 KiB root-table page with 256 16-byte root entries.
- Embed 256 page-aligned context/device tables. Each has
  `32 * 8` 16-byte context entries and is exactly 4 KiB.
- Logical indexing is `[bus][device][function]`; physical lookup is root entry
  `[bus]` followed by context entry `[(device << 3) | function]`.
- The 3-D runtime owner table is `[256][32][8]` of total `usize` process
  pointers. On this 64-bit target each slot is 8 bytes, so metadata is 128
  pages = 512 KiB.
- Total `IommuRootTable` storage per PCI segment is therefore 385 pages =
  1,576,960 bytes: 257 hardware pages plus 128 metadata pages. Ghost state
  adds no runtime storage.
- Place the object in pinned static/BSS storage; never construct or return the
  approximately 1.5 MiB value on a kernel stack.

IOTLB status:

- The current model has one global `IommuTLB`, representing one VT-d remapping
  unit. It is not per-CPU. `domain_tlbs` is keyed by the BDF-derived DID and
  each `SingleIotlb` has 4K/2M/1G translation maps.
- `iommu_tlb_wf_spec` resolves DID through the static BDF interfaces and
  requires each cached translation to remain a subset of that process's IOMMU
  page table. A BDF for which `spec_index_iommu_root(b, d, f) == None` must
  have an empty IOTLB even though it remains owned.
- There is no IOTLB dirty bitmap. Root-table ownership already identifies the
  process and IOMMU table for each DID.
- Global/domain/page invalidation specs permit monotonic removal from unrelated
  domains because hardware may execute an invalidation at coarser granularity.
- Context-cache state, ATS/device-TLB state, actual invalidation primitives,
  and DMA reverse-mapping/refcount rules remain deferred.
- The independent CPU-TLB 2MiB typo found during this audit was fixed:
  its clause now guards on `tlb_2m().dom()`.

DMA mapping/reverse-mapping invariants remain deliberately deferred as recorded
in `veriflat-project-notes.md`.
