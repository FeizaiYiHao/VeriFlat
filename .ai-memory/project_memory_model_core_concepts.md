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

- Device memory is described by the PCI BAR table, not by the page array.
  `KernelK.pci_bars: &'static PciBarTable` (`KernelU.pci_bars`) is a sealed,
  read-only sequence of at most 1024 `PciBarEntry`s, each a function's B/D/F,
  a BAR index below 6, and the BAR's exact byte range (ending at or below
  2^48). Only the unverified boot glue builds it (`PciBarTable::new` has
  `requires false`), copying the loader's BAR slots in order, so slot `i` is
  table index `i`; no operation changes it and it is read without a lock.
  `pci_bar_table_wf`: entries are pairwise byte-disjoint, and BARs whose 4K
  envelopes share a page belong to the same function. The glue checks this
  and the other boot assumptions at boot and panics otherwise. There is no
  global IO registry and no RAM set.
- A BAR page is a 4K page in the outward-rounded 4K envelope of some entry
  (`pci_bar_page`, through `pci_bar_entry_of_page`, the one approved
  `choose`; `pci_bar_function_of_page` names its function). A page-array page
  that is a BAR page stays `Unavailable` (`pci_bar_pages_unavailable_wf`);
  `Page` has no IO flag. A 2M IO target is a 2M-aligned chunk lying wholly in
  one BAR (`pci_bar_2m_chunk`, `pci_bar_2m_chunk_of`).
- IO leaves are CPU page-table leaves with software bit 53
  (`PAGE_ENTRY_IO_MASK`) plus PCD|PWT (`PAGE_ENTRY_IO_CACHE_MASK`); `is_io` is
  part of `PageEntryPerm` and `MapEntry`. Only 4K and 2M leaves can be IO
  leaves: IOMMU tables map RAM pages only and every 1G leaf is a RAM leaf. The
  page reverse-map invariants cover RAM leaves only: an IO mapping has no
  page-array owner, reference count, or quota.
- Each process's page table carries its owned PCI functions in a sealed
  8-entry `PciFunctionArray` (`PageTableHigher.pci`, under the page-table big
  lock): per function a mapping count and a ghost set of its BAR mappings
  `(va, SZ4k | SZ2m)` (`PageTableU.pci_functions` shows the counts).
  `pagetable_pci_mappings_wf`: a recorded mapping is a held IO leaf of that
  table whose target belongs to the function; every present 4K or 2M IO leaf
  is recorded under its function, which the array holds; every held IO leaf,
  hidden ones included, targets BAR pages. So a process maps BARs only of
  functions it owns. Ownership itself is in the IOMMU note.
- IO leaves are created only by `syscall_map_pci_bar_4k` / `_2m` (one page or
  chunk per call, the page-table write lock held, `install_io_4k_mapping` /
  `install_io_2m_mapping` add the leaf and the mapping in one step) and removed
  only by `syscall_unmap_pci_bar_4k` / `_2m` (hide, flush, then
  `remove_io_4k_mapping` / `remove_io_2m_mapping`) or by the held-leaf reclaim
  of kill and last-thread exit, which runs after the functions are released
  and removes IO leaves like RAM leaves with no bookkeeping. Generic
  `unmap_4k` / `unmap_2m` refuse a range holding an IO leaf; IO leaves are
  never shared by IPC, process/container creation, or `iommu_map_4k`. A
  function cannot be sent by IPC while its count is not 0.
- The count increment's `len < usize::MAX` comes from the trusted axiom
  `pci_function_mapping_count_lt_usize_max`
  (`src/kernel/lemma/kernel_cardinality_axioms.rs`).
- Boot maps no IO leaf: the loader reports the BAR slots and maps none, and
  `finish_init_from_boot` takes the BAR table on trust (`pci_bar_table_wf`,
  `pci_bar_pages_unavailable_wf`) and accepts RAM leaves only
  (`boot_dom0_manifest_wf` requires `!entry.is_io`); the glue
  (`boot/kernel/src/glue.rs`, `check_bar_slots`, `walk_dom0`) checks these.

Primary code: `src/page/page_def.rs`, `src/define/types.rs`,
`src/kernel/memory_management/page_array_spec.rs`, and
`src/util/page_ptr_util_u.rs`, plus `src/proc/pcid_allocator.rs` and
`src/kernel/memory_management/pages_pcid_allocator_spec.rs`; for IO,
`src/define/pci_bar.rs`, `src/kernel/memory_management/io_mappings_spec.rs`,
`src/pagetable_concurrent/pci_function_array.rs`,
`src/kernel/implementation/map_4k/{map_io_leaf,unmap_io_leaf}.rs`, and
`src/kernel/implementation/syscall_pci_bar/`.
