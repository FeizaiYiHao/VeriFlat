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

### Why this is unforgeable

`LocalContext` is a tracked ghost type. Three facts make it tamper-proof:

1. **No public constructor.** Nothing outside the trusted base can mint a
   `LocalContext`. The TCB mints one at the start of each system call,
   initialized with the calling thread's id, an empty `lock_seq`, and
   `Acquire` state.
2. **State fields are only mutated by trusted operations.** `lock_seq` and
   the two locking states have no public setters. They change only as side
   effects of `lock`, `unlock`, and the section-boundary trusted proof
   functions.
3. **Threading via ownership.** A syscall receives a `LocalContext` as
   input and must return one as output. Rust ownership forces the syscall
   to thread the same value through every kernel call along the way — there
   is no way to drop it mid-syscall, swap in a fresh one, or duplicate it.

Together, these mean the only `LocalContext` a syscall can present at exit
is the one it received at entry, evolved exclusively by the lock and section-
boundary primitives. Whatever invariant those primitives maintain about its
state is maintained for the whole syscall.

## User-view atomicity

**Goal.** Every syscall appears atomic to user code.

**Mechanism.** The `LockUserVisibilityTrait::is_user_visible()` predicate
marks each kernel object as user-visible or not. `LocalContext` tracks a
second sink state, `user_view_locking_state`, with the same `Acquire →
Release` two-phase shape as `kernel_view_locking_state`, but applied at
syscall granularity rather than per-section.

The syscall picks its **linearization point** explicitly: a (not-yet-
implemented) trusted proof function transitions `user_view_locking_state`
from `Acquire` to `Release`. After the flip, no further locks may be
acquired for the rest of the syscall.

The relevant clauses on `unlock` are:

```rust
// unlock_requires
T::is_user_visible() ==> old.user_view_locking_state is Release
```

```rust
// unlock_ensures (user-view component)
new.user_view_locking_state == old.user_view_locking_state
```

In other words: a syscall **cannot release a user-visible lock until it has
manually flipped `user_view_locking_state` to `Release`**. If it tries, the
precondition fails and verification rejects the syscall.

This forces every syscall that touches user-visible state to make its
linearization point explicit. Without the manual flip, there is no point in
the program where `old_user` can be captured, and the syscall's user-view
spec would be incomplete.

`lock` and `unlock` themselves never change `user_view_locking_state` —
only the manual flip does.

Consequences:

- A syscall that touches no user-visible state never flips
  `user_view_locking_state` — invisible to the user view.
- A syscall that does touch user-visible state commits to the user view
  exactly once, at the manually chosen linearization point.

This lets the user-facing spec describe only the user-view delta. Internal
kernel-view-only changes (e.g., bumping a page refcount) appear in the
implementation and the kernel-view spec but not in the user spec.

### Mapping kernel view to user view

The relationship between the two views is given by a single spec function:

```
spec fn user_view_of(k: KernelView) -> UserView
```

`user_view_of` extracts the user-visible projection of a kernel state. Two
kernel states `k1` and `k2` are user-indistinguishable iff
`user_view_of(k1) == user_view_of(k2)`.

The user-view spec for a syscall is then a relation between two snapshots:

- **`old_user`** — `user_view_of(kernel)` captured *at the linearization
  point*, immediately after the manual flip to `Release`.
- **`new_user`** — `user_view_of(kernel)` captured at syscall exit.

The syscall's user-facing pre/postcondition is then `old_user → new_user`.

### Why this is sound

Between the linearization point and syscall exit, two facts hold:

1. The user-view phase is `Release`, so no further locks can be acquired.
2. Every user-visible lock the syscall ever wanted is already held — it
   was acquired before the flip, and the `unlock` precondition
   `is_user_visible() ==> user_view_locking_state is Release` is satisfied
   only after the flip, but releasing them here is still constrained by
   the kernel-view two-phase shape inside the current section.

Therefore, throughout this entire interval, no other thread can observe any
user-visible kernel object — they are all write-locked by us. From every
other thread's perspective the interval is a single instantaneous step.

`old_user` is the state every other thread agrees was the user view before
us — we hold the locks, so the kernel-view value at the linearization
point is exactly what those threads believe is current.

`new_user` is the state every other thread will see once we eventually
unlock. Anything we do between the two snapshots is invisible by
construction.

So the projection
`(user_view_of(kernel@linearization), user_view_of(kernel@exit))` is a valid
single atomic transition over the user view.

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

## Killing objects

Some kernel objects can be destroyed (containers, processes, threads,
endpoints, ...). Their lifecycle ends with the underlying memory being
retyped back into a free physical page (2 MiB for a container, 4 KiB for the
rest) and returned to the allocator.

### Lifecycle

Killing happens inside a single kernel-view atomic section:

1. **Acquire wlock.** The killer must hold a write lock on the object,
   plus write locks on every map or parent that holds a pointer to it.
2. **Mark.** The killer atomically takes the wlock and stamps
   `killer_info` onto the rwlock — `try_wlock_and_mark_kill` does both in
   one runtime step. From this point, every other thread's `try_*` on
   this object returns `Err(KillerInfo)`.
3. **Cleanup.** The killer runs the kill logic on the object's contents
   while holding the wlock.
4. **Retype.** The trusted retype primitive consumes the rwlock storage
   and produces an allocator-side free-page perm. The address that used
   to be an `RwLock<T>` is no longer one.

### Mark and retype are both Release operations

Two distinct events in this lifecycle change what other threads can
observe.

- **Mark** is the actual Release transition. It flips `try_*` from
  "succeeds" to "fails with `Err`", which is externally observable, so the
  kernel-view phase moves from `Acquire` to `Release` here.
- **Retype-from-object** runs in the Release phase that mark already
  established. It consumes the rwlock storage and produces an allocator
  free-page perm. By the time it runs, cleanup has already removed every
  pointer to the object, so retype itself doesn't expose new information
  — it's a resource-consumption operation that lives inside the Release
  phase, not a fresh Release transition.

If the killed object is `is_user_visible()`, mark is also user-view-
relevant, so it requires `user_view_locking_state is Release` at entry —
the syscall must have manually picked its linearization point beforehand.
Same precondition shape as `unlock`. Retype-from-object inherits the same
requirement transitively (it can only run on an already-marked object).

Note: **retype-to-object** (allocator → new `RwLock<T>`) is *not* a
Release. The new object is born wlocked by the caller, reachable only
through wlocks the caller already holds, so no other thread can observe
it. It first becomes externally visible at the eventual unlock, which is
a normal Release in the existing sense. Retype-to-object stays in the
`Acquire` phase.

So the contract for the verified `try_wlock_and_mark_kill` wrapper is:

```text
requires:
  !old(self).locked_by(lctx)
  !old(self).being_killed()                       // can't mark twice
  lctx.kernel_view_locking_state() is Acquire     // standard wlock precondition
  is_user_visible() ==> lctx.user_view_locking_state() is Release
  lctx.lock_id_acyclic(lock_id@)
  ... (other lock_id constraints)

ensures (success):
  new(self).locking_thread() is Write{thread_id, lock_id}
  new(self).being_killed() == true
  new(lctx).kernel_view_locking_state() is Release  // mark IS the release
  new(lctx).user_view_locking_state() unchanged     // already Release if applicable
  new(lctx).lock_seq pushes lock_id
  lock_perm minted
```

Note the asymmetry with `wlock`: a successful `try_wlock_and_mark_kill`
acquires the wlock perm *and* flips kernel-view to `Release`, so within
the same section the killer cannot acquire any further locks. Cleanup
must be doable with the locks already held at mark time.

The retype-from-object primitive runs in Release phase and does not flip
the phase further:

```text
requires:
  old(self).wlocked_by(lctx)
  old(self).being_killed() == true
  old(lctx).kernel_view_locking_state() is Release   // already Release from mark
  is_user_visible() ==> old(lctx).user_view_locking_state() is Release
  ... lock_perm matches the wlock

ensures:
  the RwLock<T> storage is consumed
  an allocator free-page perm is produced
  new(lctx).kernel_view_locking_state() is Release   // unchanged
  new(lctx).user_view_locking_state() unchanged
```

### Temporal safety of pointers

The protocol guarantees no other thread holds a pointer to the killed
object when retype runs. The argument has three pieces:

1. **inv() at section end.** The kernel invariant says every reference in
   the kernel points to a live object. After retype the killed object no
   longer exists, so any thread that still held a reference to it would
   leave the inv unsatisfiable. The mandatory inv() check at the section
   boundary therefore enforces cleanup completeness.
2. **All pointer-holding maps were wlocked.** Threads acquire pointers
   only through locked maps. The killer holds wlocks on every map that
   could contain a pointer to the victim, so all pointer-acquisition is
   serialized against the kill.
3. **Cross-section pointer leakage is blocked by the section-boundary
   wipe.** No raw pointer survives across sections without re-derivation
   from current kernel state, and the post-kill kernel state has no
   entry for the killed object.

So the temporal safety guarantee — "no use-after-free" — falls out of the
existing inv mechanism plus the section-boundary wipe. There is no kill-
specific runtime check.

### Once marked, the object cannot be revived

`killer_info.is_some()` is one-way. `wunlock` on a tombstoned object is
disallowed by the verified API; the only legal exit from the wlock-after-
mark state is retype. This means cleanup must be doable in-section. If
the kill runs into an unrecoverable error during cleanup, there is no
"abort kill, restore object" path — the contract is mark-then-retype, no
backing out.

### Lock-id continuity

`LockId.minor` is `addr` for most objects (see `LockId.md`). After retype
the address is recycled and may later host a fresh, unrelated object with
the same `LockId.minor`. Lock IDs are therefore unique only across
simultaneously-live objects, not across time. Proofs that say "this is
the same `LockId` I had earlier" must be backed by continuous lock
holding (which `LocalContext.lock_seq` already provides for any single
syscall) rather than by ID equality alone.


## Open items

- Lock ordering / deadlock freedom: `lock_seq` + `lock_id_acyclic` / `wf`.
  See `LockId.md`.
- User-visible objects without locks (page-table user view, PCI root table) —
  trigger `inv()` immediately on update; mechanization in progress.
