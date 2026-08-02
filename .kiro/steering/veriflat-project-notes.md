# VeriFlat — operational notes

Concrete things to remember when working on this codebase. Read
`Methodology.md` and `README.md` for the conceptual model.

## Project shape

- Microkernel verified with Verus, in `src/`.
- `verus/` is a submodule; the verifier binary lives at
  `verus/source/target-verus/release/verus`.
- Run `./verify.sh` from project root to verify everything (works in
  both bash and zsh).
- `./activate` sources the Verus build environment.


## Proof gap protocol

When you discover a proof gap or spec gap (e.g., a missing postcondition,
a lock ordering incompatibility, a `closed spec` blocking a proof, or a
Verus/SMT limitation), **stop and flag it to the user** before adding any
`#[verifier::external_body]` axiom or `assume(...)` workaround. Explain:
1. What property can't be proved.
2. Whether it's a spec gap (fixable by strengthening specs) or a Verus
   limitation (e.g., `closed spec` + opaque datatype field restrictions).
3. What the narrow TCB axiom would look like if the user chooses to accept it.

## Module layout

- `src/lib.rs` — crate root; re-exports everything.
- `src/locks/` — trusted base. `RwLock`, `LocalContext`, `LockedMap`,
  `LockedArray`, `PointsTo` glue. Mostly `external_body`.
- `src/define/` — types, constants, traits.
- `src/page/`, `src/proc/`, `src/cpu/`, `src/allocator/` — kernel object
  definitions (`Page`, `Container`, `Process`, `Thread`, `Endpoint`,
  `Scheduler`, `Cpu`, `PageAllocator`).
- `src/pagetable_seq/` — page table machinery.
- `src/kernel/` — global kernel state and invariants.
  - `kernel_k_define_spec.rs` — `KernelK` struct and the global `inv()`.
  - `kernel_u_define_spec.rs` — `KernelU` user-view projection.
  - `kernel_total_define_spec.rs` — `KernelStep`, `KernelSteps` ledger.
  - `spec_util.rs` — preservation lemmas, narrow trusted set-fold axioms.
  - `memory_management/`, `process_management/`, `cpu_tlb_management/` —
    spec files, one bidirectional relation per file.
  - `implementation/` — verified syscall implementations.
- `src/lemma/`, `src/util/`, `src/primitive/`, `src/linkedlist/` — proof
  helpers and data structures.

## RwLock — five generic params

```rust
RwLock<T, ROT, KGhostT, UGhostT, const HAS_KILL_STATE: bool>
```

- `T` — lock-protected payload. Always kernel-visible; user-visible iff
  `T::is_user_visible()`.
- `ROT` — read-only data. Same visibility as `T`. `borrow_rodata()` works
  without a lock.
- `KGhostT` — kernel-view-only ghost. Never user-visible.
  `update_kernel_ghost` mutates without a lock; kernel-view Release op.
- `UGhostT` — user-view-visible ghost. Same visibility as `T`.
  `update_user_ghost` mutates without a lock; kernel-view Release; if
  `T::is_user_visible()`, also requires user-view Release.
- `HAS_KILL_STATE` — `bool` const generic. Toggles whether the rwlock
  carries a `killer_info: Option<KillerInfo>` (kill-protocol marker).

Most concrete sites pass `(), (), ()` for ROT/KGhostT/UGhostT. Container,
process, thread, endpoint, scheduler, page-table all use
`HAS_KILL_STATE`. Page array, allocator's internal pieces use
`NO_KILL_STATE`.

## RwLock API split

- `RwLock<…, NO_KILL_STATE>` exposes `wlock` (no kill check).
- `RwLock<…, HAS_KILL_STATE>` exposes `wlock_unless_killed` and
  `try_wlock_and_mark_kill`. Both fail if `killer_info.is_some()`.
- `wlock_external` / `wunlock_external` exist for TCB construction code;
  gated by `requires false`. Use only inside the TCB.

## LocalContext

Tracked ghost type minted by the TCB at syscall entry, threaded through
every kernel call by ownership.

- `kernel_view_locking_state`: per atomic section (`Acquire → Release`).
  Acquire = locks may be taken. Release = no more acquires; releases
  only.
- `user_view_locking_state`: per user-step (`Acquire → Release`). Same
  shape. Flipped both directions by `begin/end_user_view_step`.
- `lock_seq: Seq<LockId>` — strictly ascending under `LockId::spec_gt`,
  enforcing global lock ordering for deadlock-freedom.
- `unlock_requires<T>(...)`: `T::is_user_visible() ==>
  user_view_locking_state is Release`. Wired into both `wunlock`
  variants. The user-view linearization point is mandatory before any
  user-visible lock can be released.

## KernelSteps + snap_shot discipline

`KernelSteps` is a tracked ledger threaded through a syscall, recording
user-visible atomic transitions:

```rust
pub tracked struct KernelSteps {
    pub ghost steps: Seq<KernelStep>,
    pub ghost snap_shot: KernelU,  // user-view at last refresh point
}
```

Each `KernelStep` has `old_u`, `old_k`, `new_u`, `new_k`. Steps are
opened by `begin_user_view_step` and closed by `end_user_view_step`.

The `snap_shot` field is the discipline mechanism that catches
unrecorded U-mutations:

- **Syscall entry** (precondition): `old(steps).snap_shot ==
  kernel_k_to_kernel_u(*old(self))`. Caller hands us a fresh snapshot.
- **`begin_user_view_step`**: snap_shot preserved.
- **`end_user_view_step`**: snap_shot refreshed to current projection
  (the user-step's mutations are now recorded in the ledger).
- **`kernel_step_boundary`**:
  - requires: `kernel_k_to_kernel_u(*self) == steps.snap_shot` (no
    unrecorded U-mutation).
  - ensures: snap_shot refreshed to post-interleaving projection.

If a syscall mutates U outside of a `begin/end_user_view_step` pair, the
snap_shot stays stale, and the next `kernel_step_boundary` will fail to
verify. This mechanically enforces "U-mutations only inside user-steps."

## Open design issue: DMA mappings

The IOMMU-table structural model deliberately does not yet connect
`PageTable<IOMMU_TYPE>::mapping_{4k,2m,1g}` to `Page` reverse mappings or
reference counts. Do not reuse `Page::mappings` for this without first fixing
the DMA model: it currently represents CPU page-table mappings, and a physical
page may need simultaneous CPU and DMA mappings. Before adding IOMMU map/unmap
operations, decide at least:

- whether `Page` gets a separate `io_mappings` relation;
- whether `ref_count` counts CPU and DMA references together or separately;
- how mapping size and I/O pages interact with `PageState::Mapped*`;
- which container/process ownership rule applies to DMA-visible pages.

The IOTLB layer has its own `iova_{4k,2m,1g}_valid` predicates and does not
apply the CPU kernel-VA range restriction. The underlying
`PageTable<IOMMU_TYPE>` still reuses `VAddr` and the CPU page-table mapping
model, so specialize that table's address-validity rules before implementing
DMA map/unmap operations.

Until those choices are made, keep DMA mapping invariants and operations out
of `KernelK::memory_management_inv`.

## PCID allocator backing page

`PcidAllocator` contains `[usize; PCID_MAX]`, so its 4096 runtime counters
occupy 32 KiB on the 64-bit target. The allocator map object, including the
generic `RwLock` header, is backed by one 2 MiB page. A compile-time assertion
checks that the complete lock object fits, while `pcid_allocator_pages_wf`
connects it to an `Allocated2m { AsPcidAllocator }` base page. The global
`hugepage_2m_wf` invariant supplies the 2 MiB base alignment and the associated
`Merged2m` tail-page structure.
