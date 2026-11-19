---
name: project_iommu_identity_and_static_root_table
description: Current IOMMU identity (anchor DIDs), ownership, static VT-d root-table, and IOTLB model
metadata:
  node_type: memory
  type: project
---

# IOMMU model

## Identity: anchor DIDs

- There is no software IOID or DID allocator. The VT-d DID is a per-IOMMU-table
  identity: `PageTable.did: Option<VtdDomainId>` (always `None` for CPU
  tables, `did_wf`), projected as `PageTableU.did`. A new table has `None`.
- `pci_bdf_did(bus, device, function) = bus * 256 + device * 8 + function` is
  only a function's candidate DID (and its flat slot index); `pci_bdf_of_did`
  is its inverse and `pci_bdf_lt` the lexicographic B/D/F order, which equals
  the flat slot order.
- Anchor rule (`iommu_root_table_process_wf`): every present context entry
  carries its owner table's root and `Some` DID, so all attached functions of
  a table share its DID and a DID-less table has no attached function. A
  table DID `d` is anchored at `pci_bdf_of_did(d)`: that B/D/F is owned by the
  table's process, attached to the table, and carries `d`. Hence distinct
  tables never share a DID, without any allocator.
- Life cycle: the first attach of a DID-less table adopts the attaching
  function's candidate DID (that function becomes the anchor); later
  attaches reuse the table's DID. An IPC transfer of an attached non-anchor
  function invalidates the DID and keeps it. Transferring the anchor
  re-anchors deterministically at the lexicographically smallest other
  function of the sender's PCI function array attached in that DID
  (`iommu_root_table_detach_owned`, `IommuRootTable::first_attached_in_did`),
  moving every such entry to that B/D/F's candidate DID
  (`iommu_root_table_migrate_did`: clear, invalidate the old DID, republish,
  with the old DID invalidated before and after), or drops the DID when none
  remains; the U contract is `pci_handoff_table_did`. Thread exit and kill
  (`iommu_root_table_detach_array`) clear the context entry of every function
  in the owner's array, invalidate the DID once, and drop it.
- Every DID change (`iommu_table_map_set_did`) happens inside an
  `iommu_subsystem_mutation.rs` helper with the root-table lock and the
  table's write lock held (root table 10005 before IOMMU table 10006).

## Ownership

- A process has at most one IOMMU table (`Process::iommu_table`).
  `ProcessRO.iommu_cr3` mirrors its root and `ProcessRO.iommu_table_ptr`
  (K-only) the table pointer (`process_iommu_table_match`), so IPC locks the
  sender's table without locking the sender process.
- A valid B/D/F is owned by at most one process. The root table keeps a real
  `owned` flag and a ghost owner per function; the owner's page table keeps
  the function in its sealed 8-entry `PciFunctionArray`
  (`PageTableHigher.pci`, under the page-table big lock) with its BAR mapping
  count and ghost mapping set (memory-model note).
  `pci_function_ownership_wf` keeps both sides in agreement; both change only
  with the owner's page-table write lock and the root-table lock held, through
  `KernelK::update_pci_entry` (Claim or Release of one entry) and
  `KernelK::release_pci_functions` (every entry). "Not attached" means the
  context entry is not present; it does not remove ownership.
- Every function starts unowned at boot (`IommuRootTable::new_disabled`).
  Only the root process of the root container (no parent process, container
  without parent) claims an unowned function (`syscall_pci_claim`): cpu,
  process unless killed, page table write lock, a free entry, then the root
  table lock and the ownership check.
- An IPC `Pci` rendezvous moves a function between the two arrays: both page
  tables write-locked (`wlock_pagetable_pair`), the sender must hold it with
  count 0 and the receiver must have a free entry; then the root table lock,
  the sender's IOMMU table when the function is attached (detached first), and
  Release plus Claim. Otherwise the peer gets `ErrorIpcPciOwnerMismatch`,
  `ErrorIpcPciBarMapped`, or `ErrorIpcPciReceiverFull` and nothing moves.
- Kill and last-thread exit: lock the page table, hide the user root entries,
  flush, then release every function (the IOMMU table write-locked and
  detached under the root table lock, `iommu_root_table_detach_array`, then
  `release_pci_functions`); nothing goes to the killer. The root-table lock is
  taken only when the array is non-empty; a process with an IOMMU table and no
  function only write-locks that table, which has no DID. No path scans the
  65,536-entry table. `process_emptied_tables_wf` keeps a TablesEmptied or
  zombie process's array empty.
- `syscall_pci_attach_dma` reads ownership from the array under the
  page-table read lock, then takes the root-table lock and the IOMMU table
  write lock to attach; there is no detach syscall.

## Root table

- `KernelK.irt` is one `LockCell` over the whole table
  (`IOMMU_ROOT_TABLE_LOCK_MAJOR = PAGE_TABLE_LOCK_MAJOR + 1`, below
  `IOMMU_TABLE_LOCK_MAJOR`, so DID changes can write-lock an IOMMU table under
  it); it is taken and released inside one step and is not U-visible. It is
  taken by claim, IPC PCI transfer, attach, and the release of a dying
  process that owns functions.
- `IommuRootTable` is an opaque, pinned legacy VT-d image with logical
  `owners` (Option-valued), `iommu_roots`, and `iommu_dids` `Seq3` views.
  External specs use `spec_index_owner`, `spec_index_iommu_root`, and
  `spec_index_iommu_did` (`context_wf_at`: a DID is present exactly when a
  root is, and is valid), not nested sequence indexing. Exec operations:
  `is_owned`, `is_attached`, `iommu_did`, `claim`, `release`, `attach(…, root,
  did)`, `detach`, `first_attached_in_did`, `detach_array`. Kernel code
  mutates it through `iommu_subsystem_mutation.rs` and
  `pci_ownership_mutation.rs`.
- Context entries are written only through the trusted volatile stores
  `publish_context_entry` (upper word with DID and address width first,
  P-carrying lower word last) and `clear_context_entry` (lower word first).
- Physical lookup is root entry `[bus]`, then context entry
  `[(device << 3) | function]`. The object contains one 4 KiB root page, 256
  4 KiB context tables, and 16 pages of `owned` flags: 273 pages / 1,118,208
  bytes total.
- The object must remain pinned after its embedded addresses are initialized;
  never construct or return it as a large stack value.
- `boot/kernel/src/iommu.rs::init_unit` fails closed unless `CAP.CM = 0`,
  `CAP.RWBF = 0`, `CAP.ND >= 6` (16-bit DIDs), 4-level SAGAW, `ECAP.C` (or a
  hypervisor), and `ECAP.IR`, the registers fit the mapped page, translation
  and interrupt remapping start off, and the root table address is 4 KiB
  aligned below 48 bits. The invalidation hooks check that CAIG / IAIG cover
  the requested granularity and panic on a DID at or above 2^16.

## IOTLB

- `IommuTLB` holds one logical IOTLB and one logical context cache for all
  remapping units (they share the one root table); both are ghost,
  `KernelK`-level, and outside the root-table lock. The IOTLB is a map from
  DID to a CPU-shaped `SingleTLB` (4K/2M/1G maps keyed by IOVA).
  `context_cache: Map<PciBdf, (PageTableRoot, VtdDomainId)>` is keyed by
  B/D/F: a key means a unit may cache that function's present entry with
  that root and DID (`CAP.CM = 0`: never a not-present entry). `inv` makes
  the domains exactly the valid DIDs and the cache keys valid B/D/Fs with
  valid DIDs.
- `iommu_tlb_wf_spec` only constrains cached state: a cached entry equals
  the current present root and DID; a present entry's domain (its owner
  table's DID) is a `single_tlb_subset_of_pagetable` of that table, and a
  `single_tlb_subset_of_present_pagetable` when the table is not
  write-locked; a candidate DID whose anchor does not carry it is inactive
  and its domain is empty. Owner/table/root/DID agreement lives in
  `iommu_root_table_process_wf`.
- The IOMMU table's write lock is the dirty marker: a write holder may hide
  leaves; `iommu_table_tlb_entries_present(iommu_tlb, root_table, it_mp, it)`
  is the per-table flushed fact (trivial for a DID-less table), and
  `kernel_step_boundary_raw` and the step-boundary wrappers keep it for
  write-held IOMMU tables (TCB: hidden leaves are never re-cached).
- Trusted invalidations: `IommuTLB::invalidate_domain(did)`, under the
  root-table lock, drops every cached B/D/F tagged `did`, then empties domain
  `did`; every clear or DID migration of a present entry is followed by it.
  `IommuTLB::invalidate_iotlb_domain(did)`, under a held IOMMU-table lock,
  empties only domain `did`; `flush_iommu_tlb_for_table` issues it for the
  write-held table's DID and touches no hardware for a DID-less table. A
  platform spinlock serializes the two boot hooks. There is no global flush.
- Attach and IOMMU map need no invalidation: `CAP.CM = 0`, and the candidate
  DID adopted on first attach is inactive, so its domain is already empty.
  Device-TLB is excluded by TT = 0 (`IommuRootTable::wf`); paging-structure
  caches are folded into `SingleTLB`.

## Shared page-table machinery

- CPU (`pt_mp`) and IOMMU (`it_mp`) tables are both `PageTable<TABLE_TYPE>` in
  `PageTableLockedMapOf<TABLE_TYPE>`. Their page states are
  `Allocated4k{AsPageTableRoot{table_type}}` and
  `Allocated4k{PageTable{pagetable_root, table_type}}`, so `pagetable_pages_wf`,
  `pagetables_inv`, `kernel_pagetable_nonlock_fields_unchanged`, and
  `pagetable_map_user_view` are generic over the table type.
- `syscall_iommu_map_4k` maps pages already mapped in the caller's CPU page
  table into its IOMMU table. `syscall_iommu_unmap_4k` hides leaves with
  `clear_iommu_4k_mapping_present` under `wlock_iommu_table`, empties the
  table's DID domain once with `flush_iommu_tlb_for_table`, then removes them
  with `reclaim_unmapped_iommu_4k_page`. Thread exit and kill-process detach
  the table first, so it has no DID and its present leaves are removed
  directly with `reclaim_detached_iommu_4k_page`; a kill_container scope
  hides each leaf and then unmaps it, also without a flush.
  `iommu_table_perms_wf` allows hidden leaves only while the table is
  write-locked.
- Pages count IOMMU references in `Page.iommu_mappings`; `ref_count` is
  `mappings.len() + iommu_mappings.len()`, and `page_iommu_table_wf` ties the
  set to the IOMMU tables' leaves.

Primary code: `src/iommu/root_table.rs`, `src/iommu/root_table_u.rs`,
`src/iommu/iotlb.rs`, `src/kernel/memory_management/iommu_root_table_spec.rs`,
`src/kernel/memory_management/process_iommu_table_spec.rs`,
`src/kernel/memory_management/pages_pagetable_spec.rs`,
`src/kernel/process_management/process_pci_function_spec.rs`,
`src/pagetable_concurrent/pci_function_array.rs`,
`src/kernel/iommu_tlb_management/pci_ownership_mutation.rs`,
`src/kernel/iommu_tlb_management/iotlb_wf_spec.rs`,
`src/kernel/iommu_tlb_management/iommu_subsystem_mutation.rs`,
`src/kernel/implementation/syscall_pci/`,
`src/kernel/implementation/syscall_ipc/syscall_ipc_pci*.rs`,
`src/kernel/implementation/syscall_iommu_map_4k/`,
`src/kernel/implementation/syscall_iommu_unmap_4k/`,
`src/kernel/implementation/map_4k/{map_iommu_4k,unmap_iommu_4k,flush_iommu_tlb}*.rs`,
and `boot/kernel/src/iommu.rs`.
