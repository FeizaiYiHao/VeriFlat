# VeriFlat

VeriFlat models kernel objects, locking, memory management, and syscall
transitions in Rust and verifies their contracts with Verus.

## Source layout

- [`KernelK`](src/kernel/kernel_k_define_spec.rs) holds concrete kernel state.
- [`KernelU`](src/kernel/kernel_u_define_spec.rs) projects CPUs, containers,
  processes, threads, endpoints, the IOMMU root table, CPU TLBs, and IOTLBs
  into the abstract user state.
- [`K wrappers`](src/kernel/kernel_step_wrappers.rs) prove how concrete
  operations change that projection and record the resulting kernel steps.
- [`Kernel implementations`](src/kernel/implementation/) contain allocation,
  mapping, object creation, and syscalls; [`locks`](src/locks/) contains the
  lock primitives and `LocalContext`.

The monolith and split Cargo workspace use the same sources. Shared definitions
and primitives belong to kernel core; allocation, mapping, and syscall crates
follow the dependency boundaries in the
[build skill](.codex/skills/veriflat-build/SKILL.md).

## Verification

```sh
./verify-workspace.sh
./verify.sh --num-threads 32 --time
python3 -B -m unittest discover -s tests -p 'test_*.py'
```

See [AGENTS.md](AGENTS.md) and the repository-owned skills it routes to for
proof discipline, focused verification, performance comparisons, and handoff.

## Concurrent interleaving between kernel sections

[`KernelK::kernel_step_boundary_raw`](src/kernel/kernel_k_define_spec.rs) models
concurrent interleaving between a completed `Release` section and the next
`Acquire` section. Its contract preserves objects whose locks remain held and
allows other state to change subject to the boundary's explicit guarantees.
Proofs across this boundary use those guarantees and subsequent lock contracts
to determine which earlier facts remain available.

[`LocalContext`](src/locks/local_context.rs) records held locks in typed maps, one per
object family, holding the exact dynamic `LockId` and mode. `typed_lock_maps_aligned`
relates the typed maps to the kernel objects, and the acyclicity check for a new lock
quantifies over those maps directly. Lock operations maintain the alignment, and the
boundary preserves it.

## Invariant obligations and trusted boundaries

The caller must establish `KernelK::inv()` and both lock alignments before
the raw boundary. The boundary guarantees them again after the modeled
interleaving and restores the `Acquire` phase. It is an `external_body` proof
function: preservation by concurrent execution is part of the trusted model.
The current source contains no explicit `assume(...)` or `admit()` calls.

[`KernelSteps`](src/kernel/kernel_step_wrappers.rs) records changes to the
user projection, `kernel_k_to_kernel_u`. At a boundary, it records the completed
section's change before refreshing the snapshot after interleaving. At syscall
exit, the `end_kernel_step_*` wrappers record the final section without introducing another
interleaving point. Sections whose user projection is unchanged add no user step.
The recording and operation-specific projection proofs are verified in the K
wrappers. The raw interleaving boundary remains trusted; callers use K-state
conditions to establish each wrapper's user-visible transition.

The trusted code also includes low-level lock and memory primitives, permission
construction using `Tracked::assume_new()` inside `external_body` functions, and
the explicit
[cardinality](src/kernel/lemma/kernel_cardinality_axioms.rs) axioms (the fold lemmas in
`src/kernel/lemma/kernel_fold_lemmas.rs` are proven). Verification
results depend on these contracts and axioms.
