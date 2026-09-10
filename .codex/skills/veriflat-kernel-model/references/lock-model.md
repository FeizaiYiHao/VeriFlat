# Lock model

- `LocalContext` has typed held-lock maps plus one exact pair ledger:
  `Set<(LockId, KernelObjId)>`. Do not add object-only sets, scalar lock-id
  sets, or another pair ledger.
- `typed_lock_maps_aligned(k, lctx)` aligns each physical object family with
  its typed map. `lock_id_set_aligned(lctx)` aligns typed entries with exact
  `(id, object)` pairs; lock mode is represented only in the typed maps.
- Acquire inserts the exact typed entry and current pair; unlock removes both;
  a dynamic-id change overwrites the typed entry and replaces the pair during
  the transition. Producers close both alignments at their wrapper boundary.
- Lock membership, counts, scopes, and finish conditions read typed maps.
  Deadlock checks and major bounds quantify only the exact pair set. Syscalls
  and transitions do not reveal either alignment or rebuild it manually.
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
  name. Approval to retain one does not waive approval for any new framing spec.
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
