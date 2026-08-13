---
name: project_memory_model_core_concepts
description: Current page metadata, address/index, and physical-memory permission model
metadata:
  node_type: memory
  type: project
---

# Memory model

- `PagePtr` is a physical address and `PageIndex` selects the corresponding
  metadata slot in `KernelK::page_array`. Valid pointers and indices are related
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

Primary code: `src/page/page_def.rs`, `src/define/types.rs`,
`src/kernel/memory_management/page_array_spec.rs`, and
`src/util/page_ptr_util_u.rs`.
