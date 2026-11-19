---
name: project_memory_model_core_concepts
description: Current page metadata, address/index, physical-memory permission, and IO (BAR) page model
metadata:
  node_type: memory
  type: project
---

# Memory model

- `PagePtr` is a physical address and `PageIndex` selects the corresponding
  metadata slot in `KernelK::pg_arr`. Valid pointers and indices are related
  by `page_ptr2page_index` and `page_index2page_ptr`.
- `Page` is the metadata payload stored in the locked page array. It currently
  includes `addr`, `state`, ownership/mapping metadata, list-node storage, and
  tracked physical-memory permissions.
- `page_array_wf` ties the slot address to
  `page_index2page_ptr(page_index)`; do not treat a pointer, an index, and the
  `Page` payload as interchangeable without that invariant.
- Physical byte ownership uses `PagePerm4k`, `PagePerm2m`, and `PagePerm1g`
  (`PointsTo` tokens). The fields are
  `Tracked<Option<PagePerm*>>`, not `Option<Tracked<_>>`.
- `Page::perm_inv` makes the appropriate permission present for ordinary
  `Free*`/`Owned*` states and absent for other states, including published
  `Mapped*` pages. An unmap path must reclaim a fresh permission after mappings
  and stale TLB entries are gone; it must not resurrect a pre-publication token.
- TODO (2026-10-12): the contents of physical pages are not modeled. A page
  freed by one owner and handed to another (unmap/free, quota transfer,
  `send_pages`) keeps its old bytes; the dom0 test observed a re-mapped page
  still holding its previous contents. Zeroing or content ownership must be
  modeled before any cross-container page flow counts as isolating.
- `PcidAllocator` has one machine-word counter for each of the 4096 PCIDs. Its
  payload size is compile-time checked, the complete `LockCell` object must fit in
  one 2 MiB page, and `pcid_allocator_pages_wf` ties each allocator object to an
  `Allocated2m { AsPcidAllocator }` backing page.

## IO (device) pages

- Device memory is described by BAR slots, not by the page array. The PCI
  table (`IommuRootTable`) holds sealed ghost `PciBarSlots`: a map from
  `(PciBdf, BAR index 0..5)` to the exact byte range of one memory BAR
  (`BarRegion`, ending at or below 2^48). Only the unverified boot glue builds
  it (`PciBarSlots::new` has `requires false`, like `CpuTLB::new_empty`); no
  operation changes it. There is no global IO registry and no RAM set.
- A BAR page is a 4K page inside the outward-rounded 4K envelope of some slot
  (`pci_bar_page`). A page-array page that is a BAR page stays `Unavailable`
  (`pci_bar_pages_unavailable_wf`); `Page` has no IO flag. Small BARs of
  different functions may share an envelope page.
- IO leaves are page-table and IOMMU leaves with software bit 53
  (`PAGE_ENTRY_IO_MASK`) plus PCD|PWT (`PAGE_ENTRY_IO_CACHE_MASK`); `is_io` is
  part of `PageEntryPerm`, `MapEntry`, and the IOMMU entry. `io_mappings_wf`
  says every IO leaf, present or held, maps BAR pages over its whole span.
  The page and IOMMU reverse-map invariants cover RAM leaves only: an IO
  mapping has no owner, reference count, or quota.
- IO leaves are created only at boot (dom0's 4K IO leaves of every BAR page),
  then copied from a present 4K IO leaf (IPC pages, process/container sharing,
  `iommu_map_4k`) or cleared (unmap, IOMMU unmap, last-thread exit, kills).
  Once every holder has unmapped an IO page it cannot be mapped again.
  PCI ownership transfer does not revoke IO mappings. Sharing out of a 2M/1G
  IO leaf (`project_4k_source`) is not wired.
- The boot contract (`finish_init_from_boot`) takes the slots and dom0's 4K,
  2M, and 1G manifests and requires `pci_bar_slots_wf`,
  `pci_bar_pages_unavailable_wf`, and `boot_dom0_io_manifests_wf`; the glue
  (`boot/kernel/src/glue.rs`) checks these at boot.

Primary code: `src/page/page_def.rs`, `src/define/types.rs`,
`src/kernel/memory_management/page_array_spec.rs`, and
`src/util/page_ptr_util_u.rs`, plus `src/proc/pcid_allocator.rs` and
`src/kernel/memory_management/pages_pcid_allocator_spec.rs`; for IO,
`src/define/pci_bar.rs` and `src/kernel/memory_management/io_mappings_spec.rs`.
