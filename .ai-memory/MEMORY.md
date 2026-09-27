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

## Deliberately omitted

Historical verification counters, timing snapshots, completed migration
handoffs, old proof scaffolding, and superseded lock-map designs belong in Git
history. In particular, do not recover `LocalContext::wf()`, `lock_seq`,
`user_view_locking_state`, or former scalar/object-parallel ledgers from old
commits. The current `LocalContext` uses typed held-lock maps only (the former exact
`lock_id_set` ledger was removed); see the kernel-model skill and live code.

When a durable design changes, update the relevant note in place instead of
adding another dated milestone file.
