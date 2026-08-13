# VeriFlat AI memory

This directory contains only durable project context that is not already
captured by the repository instructions or obvious from one implementation.

## Authority

1. `AGENTS.md` is the source of truth for workflow, proof style, and the
   current lock model.
2. Live code and contracts override every note in this directory.
3. These notes are orientation aids, not specifications. Re-check them against
   the touched code before making a design decision.

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
history. In particular, do not recover typed per-object lock maps,
`LocalContext::wf()`, or the former scalar/object-parallel ledgers from old
commits; the pair-set model in `AGENTS.md` is authoritative.

When a durable design changes, update the relevant note in place instead of
adding another dated milestone file.
