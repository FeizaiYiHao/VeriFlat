# VeriFlat AI memory

This directory contains only durable project context that is not already
captured by the repository instructions or obvious from one implementation.

## Authority

1. `AGENTS.md` is the repository-wide source of truth.
2. Live code and contracts are the semantic authority.
3. The matching skill under `.codex/skills/` owns detailed workflow and current
   model rules.
4. These notes are orientation aids, not specifications. Re-check them against
   live code and the matching skill before making a design decision.

## Current notes

- [Memory model](project_memory_model_core_concepts.md) — page metadata,
  addresses, indices, and tracked physical-memory permissions.
- [Runtime protocols](project_runtime_protocols.md) — user-view syscall
  contracts, `KernelSteps`, staged allocation, and unlock cleanliness.
- [IOMMU model](project_iommu_identity_and_static_root_table.md) — BDF-derived
  identity, the static VT-d root table, ownership, and IOTLB state.
- [NUMA plan](project_numa_plan.md) — single-kernel NUMA design: node tags,
  per-node arrays/pools, per-node RwLock reader counts, lazy page-table replicas.

## Open tasks

- Rename existing lemmas whose names do not state what implies what (e.g.
  `lemma_l4_index_path_le_successor` in `src/pagetable_seq/pagetable_range.rs`;
  `kernel_walk_state_preserved_for_held_objects_unchanged`-style names are fine)
  to the `<premise>_implies_<conclusion>` form, repo-wide, as a separate
  rlimit-neutral rename round (user request 2026-10-29).

## Deliberately omitted

Historical verification counters, timing snapshots, completed migration
handoffs, old proof scaffolding, and superseded lock-map designs belong in Git
history. In particular, do not recover `LocalContext::wf()`, `lock_seq`,
`user_view_locking_state`, or former scalar/object-parallel ledgers from old
commits. The current `LocalContext` uses typed held-lock maps only (the former exact
`lock_id_set` ledger was removed); see the kernel-model skill and live code.

When a durable design changes, update the relevant note in place instead of
adding another dated milestone file.
