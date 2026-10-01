# Lock model

- `LocalContext` has typed held-lock maps plus one exact pair ledger:
  `Set<(LockId, KernelObjId)>`. Do not add object-only sets, scalar lock-id
  sets, or another pair ledger.
- `typed_lock_maps_aligned(k, lctx)` aligns each physical object family with
  its typed map. The typed maps are the only held-lock ledger; lock mode and
  the exact dynamic id are both represented there. `lock_id_acyclic` and
  `held_lock_majors_lt` quantify directly over every typed map.
- Acquire inserts the exact typed entry and current pair; unlock removes both;
  a dynamic-id change overwrites the typed entry and replaces the pair during
  the transition. Producers close both alignments at their wrapper boundary.
- Lock membership, counts, scopes, and finish conditions read typed maps.
  Deadlock checks and major bounds quantify only the exact pair set. Syscalls
  and transitions do not reveal either alignment or rebuild it manually.
- Upper-layer contracts, assertions, and loop invariants express thread-held
  ownership through typed-map membership and `typed_lock_map_contains_mode`.
  This includes `locked_by`, `rlocked_by`, `wlocked_by`, and their `_thread`
  variants. Alignment and lock-order (acyclic) reasoning belongs in lock
  (locker/unlocker) and update wrappers: they derive physical ownership from
  alignment locally and may export physical `locking_thread()` facts, and
  callers may pass such physical facts on instead of re-deriving them. Callers
  do not re-prove lock order that a lock wrapper already checks. Preserve the
  distinction between absence and non-Write mode.
  Physical predicates remain in the lock model, alignment definitions, and
  low-level operation proofs, including `all_objects_unlocked` below.
  Permission-token matching remains separate from typed ordering-lock ids.
- Do not restore the deleted per-object `*_objects_unlocked` and
  `*_unlocked_except` families, exact held-lock-set wrappers, or CPU-context
  bundles over facts available directly from typed maps and object fields.
- Keep the approved `all_objects_unlocked`, `no_locks_held`,
  `holds_no_allocator_locks`, and `allocator_caches_unlocked` predicates.
  `allocator_caches_unlocked` describes physical cache locks; the allocator
  predicate on `LocalContext` describes that context's held quota, cache, and
  pool locks. These are distinct guarantees, not interchangeable empty-map facts.
- Preserve the approved held-object, read-only-field, invariant-field, quota,
  and operation relations, low-level map/array `unchanged_except` relations, and
  existing EOF optimizations. Judge each by its meaning and consumers, not its
  name. New framing specs and framing lemmas require approval; ordinary edits
  to function `requires`/`ensures`, including typed-map preservation clauses,
  do not. Approval to retain an existing abstraction does not authorize a new one.
- Thread ownership metadata never disappears. Running, scheduled, and blocked
  states use their established dynamic lock-id majors; `NotApp` changes only
  lock ordering and does not restrict IPC topology.
- Container-scoped transitions may hold a non-empty set of CPU locks when every
  CPU belongs to that container. Process/thread scopes require at least one CPU
  carrying the target process; the remaining held CPUs are contextless or carry
  that same process. Exclude `Off` CPUs from these ordinary scopes.
- Container CPU membership and closed slots live in `KernelK.cpu_set_mp`;
  `ContainerRO.cpu_set` discovers the independently locked 4K object. CPU-set
  locks follow mapped pages and precede schedulers. Their owner-order fields
  are `NotApp`; acquire multiple CPU sets in increasing pointer order.
- `CPU_LOCK_MAJOR_OFF` is the terminal major. `wlock_off_cpu` requires the
  owning CPU-set write lock and a closed slot in that set. Keep it above the
  ordinary object-lock majors; do not use it to justify acquiring another
  ordinary object lock afterward.
- An Off CPU has no current process or thread and no dirty records for valid
  non-default PCIDs. A shutdown transition must establish this before
  publishing Off; CPU ownership transfer preserves the cleared state.
- Do not infer local lock state backwards from alignment. Lower-level lock
  operations should expose target state, id changes, ledger changes, and
  unchanged fields directly.
- At a kernel-step boundary, frame held objects explicitly. Preserve
  `all_objects_unlocked` directly rather than deriving it from an empty ledger.
- `KernelU` projects the outer physical lock mode as
  `LockStateU::{Unlocked, ReadLocked, WriteLocked}` on containers, processes,
  threads, endpoints, CPUs, and both page-table views, and each container's
  CPU-set lock as `ContainerU.cpu_set_lock`. Complete snapshots and
  traces retain these modes; record changes only at existing kernel boundaries
  and syscall finish. `kernel_u_nonlock_fields` normalizes only these modes,
  and `KernelSteps::nonlock_view` filters lock-only transitions for business
  contracts. Never use the normalized projection for actual snapshots or
  recording. The strict no-step wrapper also requires equal observable modes.
