# VeriFlat Verification Methodology

Living document of the high-level ideas used in VeriFlat. Add a new section per
methodological pillar.

## Two views of kernel state

- **Kernel view**: full ground truth — every counter, lock-protected datum, and
  intermediate state inside the kernel.
- **User view**: strict subset, only what user code can observe through
  syscalls (e.g., address-space mappings, syscall return codes). Excludes
  things like physical-page refcounts, scheduler queue position, allocator
  bitmaps.

We pick atomicity granularity to match each view:

- Kernel-view atomicity → individual atomic sections inside the kernel.
- User-view atomicity → the whole syscall.

A syscall may consist of multiple kernel-view atomic sections, all merged into
one user-view step.

## Kernel-view atomicity

**Goal.** A kernel-view atomic section appears atomic to all other kernel
threads.

**Rule.** Two-phase shape: acquire all locks first, then release. Once any
lock is released, no further lock may be acquired in the same section.

Why it works: while an object is write-locked, no other thread can read it.
The first unlock is the serialization point — every other thread agrees on
"before all unlocks" vs. "after all unlocks". Interleaving `unlock; lock`
would expose `o1` post-state alongside `o2` pre-state, breaking atomicity.

### How `LocalContext` enforces it

`LocalContext` (`src/locks/local_context.rs`) is a tracked ghost value
threaded through every kernel call. Relevant field:
`state.kernel_view_locking_state ∈ {Acquire, Release}`.

State machine:

- `lock` precondition: state is `Acquire`. Postcondition: state stays
  `Acquire`, `lock_seq.push(lock_id)`.
- `unlock` postcondition: state becomes `Release` (regardless of input).
  `lock_seq.remove_value(lock_id)`.

`Release` is a sink. Any `lock; ...; unlock; ...; lock` pattern fails to
verify because the second `lock` requires `Acquire` and the state is now
`Release`.

Result: every section is statically two-phase. Downstream proofs treat the
section as one atomic kernel-state transition; invariants only need to hold
at the section boundary.

## User-view atomicity

**Goal.** Every syscall appears atomic to user code.

**Mechanism.** The `LockUserVisibilityTrait::is_user_visible()` predicate
marks each kernel object as user-visible or not. `LocalContext` tracks a
second sink state, `user_view_locking_state`, that flips to `Release` only
when an `is_user_visible()` object is unlocked.

Consequences:

- Syscalls that touch no user-visible state (pure bookkeeping) never flip
  `user_view_locking_state` — invisible to the user.
- Syscalls that do touch user-visible state commit to the user view exactly
  once, at the first user-visible unlock.

This lets the user-facing spec describe only the user-view delta. Internal
kernel-view-only changes (e.g., bumping a page refcount) appear in the
implementation and the kernel-view spec but not in the user spec.

## Invariants between atomic sections

**Goal.** Each kernel-view atomic section starts from a clean slate: it sees
the global kernel invariants as `true`, but it must not carry forward any
specific facts from the previous section about objects it does not currently
hold locks on.

**Rule.** At the boundary between two kernel-view atomic sections:

1. The kernel must check that all global invariants hold. Only then is the
   section permitted to end.
2. `LocalContext` transitions back to `Acquire`, allowing the next section to
   begin acquiring locks.
3. Knowledge about every kernel object the thread does *not* currently hold a
   lock on is wiped — Verus must forget the concrete state of those objects.

Why the wipe matters: between two sections of the same syscall, other threads
can run. They may have legitimately mutated any object whose lock we released.
If Verus carries forward facts learned in the previous section about now-
unlocked objects, those facts are unsound in the new section. The wipe forces
proofs in the new section to re-establish whatever they need from invariants
and freshly-acquired locks.

### What gets wiped

For each unlocked kernel object: its concrete state becomes unknown.

For tracked maps that index kernel objects (e.g., the container map):

- The domain becomes partially unknown. Entries we still hold locks on are
  guaranteed present; everything else is unknown — entries may have been
  added or removed by other threads.
- The values for entries we do not hold locks on become unknown.

The global invariants, by contrast, are *not* wiped — they are exactly the
facts we are allowed to keep, because they hold across all threads and all
sections by construction.

### Mechanism

A set of trusted proof functions performs the wipe. They are invoked at the
section boundary, alongside the invariant check and the `LocalContext`
transition back to `Acquire`. (Not implemented yet.)


## Open items

- Lock ordering / deadlock freedom: `lock_seq` + `lock_id_acyclic` / `wf`.
  See `LockId.md`.
- User-visible objects without locks (page-table user view, PCI root table) —
  trigger `inv()` immediately on update; mechanization in progress.
