# VeriFlat Verification Methodology

Living document of the high-level ideas used in VeriFlat. Add a new section per
methodological pillar.

## Two views of kernel state

- **Kernel view** (`KernelK`): full ground truth — every counter,
  lock-protected datum, and intermediate state inside the kernel.
- **User view** (`KernelU`, `src/kernel/kernel_u_define_spec.rs`): the
  projection `kernel_k_to_kernel_u(k)` sampled at atomic-section boundaries.
  It includes address-space mappings, scheduler queues, quotas, TLBs, and
  object lock modes (`LockStateU`) and each container's dynamic lock owner
  (`lock_process_owner`); it excludes other lock owners, reader counts, the
  page array, and allocator internals.

We pick atomicity granularity to match each view:

- Kernel-view atomicity → individual atomic sections inside the kernel.
- User-view atomicity → the same sections: each section that changes the user
  projection is one user-visible step.

A syscall may consist of multiple kernel-view atomic sections; its user-facing
spec is the trace of the user steps they record (`SystemCalls.md` §1).

## Kernel-view atomicity

**Goal.** A kernel-view atomic section appears atomic to all other kernel
threads.

**Rule.** Two-phase shape: acquire all locks first, then release. Once any
lock is released, no further lock may be acquired in the same section.

Why it works: while an object is write-locked, no other thread can read it,
and while it is read-locked, no other thread can write it.
The first unlock is the serialization point — every other thread agrees on
"before all unlocks" vs. "after all unlocks". Interleaving `unlock; lock`
would expose `o1` post-state alongside `o2` pre-state, breaking atomicity.

### How `LocalContext` enforces it

`LocalContext` (`src/locks/local_context.rs`) is a tracked ghost value
threaded through every kernel call. It records the thread and CPU ids, one
typed held-lock map per object family (`thread_lock_map()`,
`pagetable_lock_map()`, `iommu_root_table_lock_map()`, …; each entry is a
`TypedHeldLock { lock_id, mode }`, read through `typed_lock_entry` and
`lock_entry_contains`), and `kernel_view_locking_state ∈ {Acquire, Release}`.

State machine:

- `wlock`/`rlock` precondition: state is `Acquire` and
  `lock_id_acyclic(lock_id)` (the new id is strictly above every held id,
  ordered over `LockId { container, process, major, minor }`).
  Postcondition: state stays `Acquire`; the exact entry is inserted into the
  object's typed map (`lock_ensures`, `rlock_lctx_ensures`).
- `unlock` postcondition: state becomes `Release` (regardless of input); the
  entry is removed (`unlock_ensures`).
- `enter_kernel_view_release` (TCB) closes the Acquire phase without changing
  the maps; `update_lock_id` (TCB) replaces a held object's dynamic id during
  `Release`.

`LockId` order is concrete: structural equality and lexicographic comparison
of container owner, process owner, major, then minor, with owners ordered
`High < Some(depth) < None` and no wildcard. Each owner component has an
`OwnerSource` (`Payload`, `Fixed`, or `Dynamic`); `None` is an intentional
ownerless component. `Dynamic` (only a container's process component) is an
acquisition policy: the acquirer requests a concrete owner, a shallower live
holder is reported as a conflict instead of waited for, and the lock records
the requested owner until unlock. Per-family owners are in `LockId.md`.

`Release` is a sink within a section. Any `lock; ...; unlock; ...; lock`
pattern fails to verify because the second `lock` requires `Acquire` and the
state is now `Release`. Only the step boundary returns the state to `Acquire`.

Result: every section is statically two-phase. Downstream proofs treat the
section as one atomic kernel-state transition; invariants only need to hold
at the section boundary.

### Why this is unforgeable

`LocalContext` is a tracked ghost type. Three facts constrain it:

1. **Single constructor.** `LocalContext::new_bootstrap` is the only
   constructor; it returns an `Acquire` context with every typed map empty.
   It is `pub` and its callers are boot-time object creation
   (`src/proc/thread_util_t.rs`), so its restriction to boot is by
   convention, not visibility. Syscalls do not construct one: their
   contracts (e.g. `syscall_alloc_quota_4k`) require `Acquire` and
   `no_locks_held()` at entry and ensure `no_locks_held()` at exit.
2. **State fields are only mutated by trusted operations.** The typed maps
   and the locking state are private and have no setters. They change only
   as side effects of the lock primitives, `enter_kernel_view_release`,
   `update_lock_id`, the retype primitives, and the section-boundary trusted
   proof function.
3. **Threading via ownership.** A syscall receives
   `Tracked<&mut LocalContext>` and threads the same value through every
   kernel call; it cannot drop or duplicate it.

Together, these mean the `LocalContext` a syscall presents at exit is the one
it received at entry, evolved exclusively by the lock and section-boundary
primitives. Whatever invariant those primitives maintain about its state is
maintained for the whole syscall.

## User-view atomicity

**Goal.** Every user-visible change appears atomic to user code.

**Mechanism.** An earlier design flipped a per-syscall
`user_view_locking_state` at a manually chosen linearization point; it was
never implemented and has been replaced by the `KernelSteps` ledger.

`KernelSteps` (`src/kernel/kernel_step_wrappers.rs`) is a tracked ledger
`Seq<KernelStep>` of `KernelStep { old_u, new_u }` plus snapshots
`snapshot_k()` and `snapshot_u()`, with type invariant
`snapshot_u() == kernel_k_to_kernel_u(snapshot_k())`. The trusted boundary
`KernelK::kernel_step_boundary_raw` (`src/kernel/kernel_k_define_spec.rs`)
and its verified `kernel_step_boundary_*` wrappers
(`src/kernel/kernel_step_wrappers/boundary.rs`) ensure:

```rust
final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(self))),
final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
```

`record_user_view_change` (`src/kernel/kernel_total_define_spec.rs`) appends
one step when the completed section changed the projection and leaves the
ledger unchanged otherwise (the section stutters). The snapshot is then
refreshed to the post-interleaving state, so the next step's `old_u` reflects
other threads' steps.

A syscall's user-facing contract is a `*_syscall_trace` over the steps it
appended, each step satisfying its `*_step_pre(old_u, ...)` and
`*_step(old_u, new_u, ...)` (`SystemCalls.md` §1–2).
`KernelSteps::nonlock_view` filters out steps that change only lock modes,
for business contracts.

Internal kernel-view-only changes (e.g., bumping a page refcount) appear in
the implementation and the kernel-view spec but not in the user spec.

### Mapping kernel view to user view

The relationship between the two views is given by a single spec function:

```
spec fn kernel_k_to_kernel_u(krnl: KernelK) -> KernelU
```

`kernel_k_to_kernel_u` extracts the user-visible projection of a kernel
state. Two kernel states `k1` and `k2` are user-indistinguishable iff
`kernel_k_to_kernel_u(k1) == kernel_k_to_kernel_u(k2)`.

Each recorded step relates two snapshots:

- **`old_u`** — the projection stored at the previous boundary, after
  interleaving.
- **`new_u`** — the projection at the end of the current section.

### Why this is sound

Within a section the thread holds the lock of every lock-protected object it
reads or mutates, so other threads cannot observe the section's intermediate
states. `KernelU` exposes lock modes, and a step that acquires a U-visible
object requires it `Unlocked` in `old_u`, so steps of different CPUs exclude
each other in the user view (`SystemCalls.md` §1–2).

Across a boundary, `held_*_unchanged` frames every object the thread still
holds, and everything else may change. State of a multi-step syscall that
must survive the boundary lives in the affected object's own (ghost) state,
such as a kill flag, constrained by that object's invariant; invariants are
never keyed on a thread's `SyscallProgress`. The thread's
`syscall_progress` itself is in `KernelU` and records the syscall's phase.

## Invariants between atomic sections

**Goal.** Each kernel-view atomic section starts from a clean slate: it sees
the global kernel invariants as `true`, but it must not carry forward any
specific facts from the previous section about objects it does not currently
hold locks on.

**Rule.** At the boundary between two kernel-view atomic sections:

1. The kernel must check that all global invariants hold. Only then is the
   section permitted to end.
2. `LocalContext` transitions back to `Acquire`, allowing the next section to
   begin acquiring locks. The typed lock maps are unchanged: held locks stay
   held across the boundary.
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
sections by construction. The boundary also keeps the fixed-size array
domains, the local CPU's CR3/PCID, container and process read-only data, and
the default page table.

### Mechanism

`KernelK::kernel_step_boundary_raw` (`src/kernel/kernel_k_define_spec.rs`,
`external_body`, TCB) performs the invariant check, the wipe, the
`LocalContext` transition back to `Acquire`, and the `KernelSteps` recording
above. Its ensures frame each held object with `held_*_unchanged`. Kernel code
calls the verified wrappers in `src/kernel/kernel_step_wrappers/boundary.rs`.

## Killing objects

Some kernel objects can be destroyed (containers, processes, threads,
endpoints, ...). Their lifecycle ends with the underlying memory being
retyped back into a raw page permission (2 MiB for a container, 4 KiB for
most others) and returned to the allocator.

### Lifecycle

A kill spans several kernel-view atomic sections (see `SystemCalls.md`
§17–19):

1. **Mark.** `try_wlock_and_mark_kill` takes the wlock of an unmarked
   object and stamps `killer_info` in one runtime step; it fails if the
   object is already marked. `mark_kill` marks an object the caller already
   write-holds. From this point, every other thread's `*_unless_killed` lock
   on this object fails.
2. **Sink the id.** A marked object reports the minimal lock id
   `(High, High, KILLED_LOCK_MAJOR = 0, minor)` (`src/define/lock_id.rs`);
   the caller moves its typed-map entry with `update_lock_id`. The killer can
   therefore keep it held across sections and still acquire every ordinary
   lock afterwards.
3. **Cleanup.** The killer runs the kill logic over several sections while
   the marked object stays write-held.
4. **Retype.** A trusted `retype_*_rwlock_to_*_page_perm` primitive (e.g.
   `src/proc/thread_util_t.rs`) consumes the rwlock storage, returns a raw
   page perm, and removes the held entry from `lctx`. The address that used
   to be an `RwLock<T>` is no longer one.

### Mark and retype are both Release operations

Two distinct events in this lifecycle change what other threads can
observe.

- **Mark** is a Release transition. It flips `*_unless_killed` from
  "succeeds" to "fails", which is externally observable:
  `try_wlock_and_mark_kill` ends in `Release`, and `mark_kill` requires
  `Release`.
- **Retype-from-object** requires `Release`. It consumes the rwlock storage
  and produces a raw page perm. By the time it runs, cleanup has already
  removed every pointer to the object, so retype itself doesn't expose new
  information — it's a resource-consumption operation that lives inside the
  Release phase, not a fresh Release transition.

The mark is U-visible as the object's `killed` field in `KernelU` and is
recorded at the next boundary like any other change.

Note: **retype-to-object** (raw page → new `RwLock<T>`,
`retype_page_perm_to_rwlock`) is *not* a Release. The new object is born
wlocked by the caller, reachable only through wlocks the caller already
holds, so no other thread can observe it. It first becomes externally
visible at the eventual unlock, which is a normal Release in the existing
sense. Retype-to-object requires the `Acquire` phase and preserves it.

So the contract for the verified `LockedMap::try_wlock_and_mark_kill`
wrapper (`src/locks/locked_map.rs`) is:

```text
requires:
  wlock_requires(obj, lctx)        // !obj.locked_by(lctx), lctx Acquire
  !obj.being_killed() ==> lctx.lock_id_acyclic(lock_id_by_key(key))

ensures (failure): obj was already being_killed; obj and lctx unchanged
ensures (success):
  !old.being_killed(), !old.locked()
  new.being_killed(), new.killer_info() == Some(killer_info)
  new.locking_thread() is Write{thread_id, lock_id}
  view, view_rodata, view_ghost unchanged
  lock_id_by_key(key) == (High, High, KILLED_LOCK_MAJOR, [key])
  new(lctx).kernel_view_locking_state() is Release   // mark IS the release
  typed map gains (old lock id, Write)               // caller then update_lock_id
  lock_perm minted
```

Note the asymmetry with `wlock`: a successful `try_wlock_and_mark_kill`
acquires the wlock perm *and* flips kernel-view to `Release`, so within
the same section the killer cannot acquire any further locks.

The retype-from-object primitives run in Release phase and do not flip
the phase further:

```text
requires:
  object write-held by lctx, lock_perm matches the wlock
  old(lctx).kernel_view_locking_state() is Release

ensures:
  the RwLock<T> storage is consumed
  a raw page perm is produced
  the held entry is removed from lctx
  new(lctx).kernel_view_locking_state() unchanged
```

### Temporal safety of pointers

The protocol guarantees no other thread holds a pointer to the killed
object when retype runs. The argument has three pieces:

1. **inv() at section end.** The kernel invariant says every reference in
   the kernel points to a live object. After retype the killed object no
   longer exists, so any thread that still held a reference to it would
   leave the inv unsatisfiable. The mandatory inv() check at the section
   boundary therefore enforces cleanup completeness.
2. **Marked objects reject new holders.** After the mark, every other
   thread's `*_unless_killed` lock on the object fails, so no other thread
   starts using it.
3. **Cross-section pointer leakage is blocked by the section-boundary
   wipe.** No raw pointer survives across sections without re-derivation
   from current kernel state, and the post-kill kernel state has no
   entry for the killed object.

So the temporal safety guarantee — "no use-after-free" — falls out of the
existing inv mechanism plus the section-boundary wipe. There is no kill-
specific runtime check.

### Once marked, the object cannot be revived

`killer_info.is_some()` is one-way except on CPU locks: only
`LockedArray::unkill` on a CPU clears a mark (remote eviction); every other
object keeps its mark until it is destroyed (`src/locks/lock_array.rs`).
`wunlock` does not require an unmarked object and preserves the mark; the
kill paths keep each marked process or thread write-held until its retire or
reclaim step (`SystemCalls.md` §18). There is no "abort kill, restore
object" path.

### Lock-id continuity

`LockId.minor` is `addr` for most objects (see `LockId.md`). After retype
the address is recycled and may later host a fresh, unrelated object with
the same `LockId.minor`. Lock IDs are therefore unique only across
simultaneously-live objects, not across time. Proofs that say "this is
the same `LockId` I had earlier" must be backed by continuous lock
holding (which the typed lock maps and the boundary's `held_*_unchanged`
framing provide within a syscall) rather than by ID equality alone.


## Bi-directional relations

Most kernel invariants are bi-directional relations between two object
collections (e.g., container ↔ process, thread ↔ endpoint, page ↔ thread).
The standard skeleton:

```rust
forall|c_ptr|
    container_map.contains(c_ptr) ==>
    /* forward: c.owned_processes ⊆ process_map.dom(),
                cross-link to root_process, etc. */

forall|c_ptr, p_ptr| where c.owned_processes.contains(p_ptr) ==>
    /* derived field consistency: p.owning_container == c_ptr,
                                  p.container_depth == c.depth, etc. */

forall|p_ptr|
    process_map.contains(p_ptr) ==>
    /* backward: p.owning_container ∈ container_map.dom(),
                 c[p.owning_container].owned_processes.contains(p_ptr) */
```

Three clauses, two directions. Each side independently asserts both
directions, which is what makes the relation bi-directional.

Structural pattern:

- **Forward link** = ghost set/seq on the parent, often in the lock-free
  `view_ghost()` (e.g.,
  `ContainerGhost.owned_processes: Ghost<Set<RwLockProcessPtr>>`).
- **Back link** = pointer/seq on the child, often in `view_rodata()` for
  immutability (e.g., `ProcessRO.owning_container: RwLockContainerPtr`).
- **Triggers** match the lookup chain: when the formula does
  `m.spec_index(k).view().some_field`, that's the trigger.

Special cases worth knowing:

- **Page state-as-link.** When one side is a `Page`, the page's *address*
  is the link. `container_map.contains(addr_of_page)` says "the container
  exists at exactly this page's address." See `pages_container_spec.rs`
  for the canonical shape.
- **Page state with payload.** `Owned4k{thread_ptr}` is read as
  `state is Owned4k && state->Owned4k_thread_ptr == ...` (e.g.,
  `pages_owned_spec.rs`). Verus auto-generates the `_thread_ptr` accessor
  from the variant.
- **Multi-hop / tree relations.** `container_thread_spec` uses both
  `owned_threads` (direct) and `owned_indirect_threads` (transitive
  closure). The back-link is a `Seq<RwLockContainerPtr>` (the thread's
  ancestor list), not a single pointer.

## Opaque spec functions

Spec functions whose bodies should not be auto-unfolded by the SMT solver
are marked `#[verifier::opaque]`. Callers who need the body unfolded write
`reveal(spec_name);` inside a proof block.

```rust
#[verifier::opaque]
pub open spec fn FOO(...) -> bool { /* body */ }

// elsewhere:
assert(FOO(...)) by { reveal(FOO); };
```

This is a performance/automation control mechanism — a heavy `forall` body
unfolding everywhere causes quantifier blow-up. It's *not* about modular
abstraction (`closed` is for that).

When an exec function needs many specs unfolded, batch the reveals at the
top:

```rust
{
    proof {
        reveal(spec_a);
        reveal(spec_b);
        reveal(spec_c);
    }
    // function body — all reveals stay in scope
}
```

Use opaque on:

- Bi-directional relations (`container_process_wf`, etc.)
- Tree-shape predicates (`container_root_wf`, `container_uppertree_seq_wf`)
- Anything with quantifier-heavy body that's used as a kernel-inv constituent

Do NOT use opaque on:

- Top-level conjunction wrappers like `container_tree_wf` (just ANDs the
  parts together — the parts are opaque, the wrapper is open).
- Simple structural predicates (auxiliary helpers that should unfold freely
  inside their module).


## Open items

- The `evict_remote_cpu` IPI wait is `external_body`; TODO at
  `src/cpu/atomic_pcid_cr3.rs:61` to model it as a virtual lock in the lock
  order.
- 2M/1G user mappings are not modeled; kill and thread_exit reclaim remove
  only 4K leaves (`src/kernel/memory_management/process_emptied_tables_spec.rs:6`).
- Demand paging: `PageFault { vaddr }` IPC payload TODO
  (`src/proc/thread_def.rs:1004`).
- `wlock`/`wunlock` on `PPtr<RwLock>` in `src/locks/locked_points_to.rs`
  (lines 37–39, 60–62) are `external_body` raw-pointer glue (TCB).
