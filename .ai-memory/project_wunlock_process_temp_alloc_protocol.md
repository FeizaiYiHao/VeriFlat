---
name: project-wunlock-process-temp-alloc-protocol
description: wunlock_process requires temp_alloc_clean(process_ptr); the flushed-before-wunlock protocol
metadata: 
  node_type: memory
  type: project
  originSessionId: 09b9b08b-8e2f-401b-97c7-f2b90ab2b24b
---

`wunlock_process` (in `src/kernel/implementation/syscall_alloc_quota.rs`) requires
`old(self).process_map.spec_index(process_ptr).view().temp_alloc_clean()` as a
precondition — the "flushed before wunlock" protocol documented on
`Process.temp_alloc_cache_*` fields ([process_def.rs]).

**Why:** `process_perms_wf`'s conjunct `process_temp_alloc_empty_unless_wlocked`
demands an empty temp-alloc cache for any process NOT write-locked. Releasing the
process flips it out of `Write`, so the cache must be clean at that moment.
`wunlock_process`'s `old(self).inv()` cannot supply this (the invariant exempts the
still-write-locked process).

**How to apply:** The fact is sourced from `wlock_process_unless_killed`'s
success-ensures (`view().temp_alloc_clean()`) and threaded through release helpers
(`release_all_with_process_and_finish`, `transfer_quota_4k_and_finish`,
`release_cpu_and_process_and_finish`). Any NEW syscall that stages pages into
`temp_alloc_cache_*` MUST drain them before calling `wunlock_process`.

This was discovered while converting `lemma_process_perms_wf_preserved_for_process_lock_op`
from an `external_body` axiom to a proven lemma — the axiom had been silently
fabricating the cleanliness. See [[feedback-proof-gaps]].
