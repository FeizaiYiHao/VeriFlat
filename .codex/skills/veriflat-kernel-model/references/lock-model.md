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
- Thread ownership metadata never disappears. Running, scheduled, and blocked
  states use their established dynamic lock-id majors; `NotApp` changes only
  lock ordering and does not restrict IPC topology.
- Container-scoped transitions may hold a non-empty set of CPU locks when every
  CPU belongs to that container. Process/thread scopes require at least one CPU
  carrying the target process; the remaining held CPUs are contextless or carry
  that same process. Exclude `Off` CPUs from these ordinary scopes.
- `CPU_LOCK_MAJOR_OFF` is the terminal major used only after the owning
  container has established the corresponding closed CPU slot. Keep it above
  the ordinary object-lock majors; do not use it to justify acquiring another
  ordinary object lock afterward.
- Do not infer local lock state backwards from alignment. Lower-level lock
  operations should expose target state, id changes, ledger changes, and
  unchanged fields directly.
- At a kernel-step boundary, frame held objects explicitly. Preserve
  `all_objects_unlocked` directly rather than deriving it from an empty ledger.
