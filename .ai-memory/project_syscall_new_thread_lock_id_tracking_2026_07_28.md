# syscall lock-id/object-state tracking cleanup (2026-07-28)

## Current proof boundary

- Outside raw lock wrappers, track the held objects directly
  (`locked_by`/`wlocked_by` plus token/object state), `LocalContext::lock_id_set()`,
  `LocalContext::wf()`, `lock_id_aligned`, and the opaque exact relation
  `locked_objects_match_lctx`.
- Do **not** expose or carry typed `container/process/thread/page/cpu/allocator`
  lock-map equations through syscall/helper contracts.
- Raw wrappers derive the typed map key/value facts internally immediately before
  calling the primitive lock/unlock implementation. `locker_unlocker.rs` has no
  typed lock-map or `lock_ensures`/`unlock_ensures` in any public wrapper
  contract.
- CPU/process/thread/page/scheduler/cache/global-pool wrappers already used this
  form. Container and allocator-quota lock/unlock were converted too.
- `syscall_alloc_quota_4k`, `commit_alloc_quota_4k`, `syscall_new_thread`, and
  their release/commit helpers now carry direct object states plus
  `lock_id_set`, never typed maps.
- `retype_staged_page_to_thread` derives fresh thread-map membership internally
  and now returns `locked_objects_match_lctx`; neither thread-create wrapper
  requires caller-visible `obj_id_fresh`.

## Allocator/new-thread composition

- `allocate_free_4k_page` now accepts the actually held `scheduler_ptr` and
  explicitly preserves that scheduler and the running CPU. This replaced the
  public generic scheduler/CPU preservation foralls that required explicit
  callsite instantiation.
- The new-thread callsite consequently verifies without the former empty
  `assert ... by {}` trigger assertions.
- The allocator call chain tracks only the process/page/object state and set
  changes publicly. Typed page/allocator map reasoning remains scoped inside
  the staged-page mutation wrappers.
- `syscall_new_thread.rs` and `allocate_free_4k_page.rs` contain no empty
  `by {}` proofs, no empty proof blocks, and no ghost captures. Assertions that
  open invariants use scoped `assert(...) by { reveal(...) }`; structural
  sequence/tree/fold foralls remain only where the invariant actually needs
  them. No new ad-hoc lemma hides a failed ground proof.

## Verification

- `kernel::implementation::locker_unlocker`: 17 verified, 0 errors.
- `kernel::implementation::syscall_alloc_quota`: 3 verified, 0 errors.
- `kernel::implementation::syscall_new_thread`: 12 verified, 0 errors.
- `kernel::implementation::allocate_free_4k_page`: 15 verified, 0 errors.
- Persistent verification counter reached **419**. Runs **342–419** belong to
  this continuation (78 invocations, including failed/invalid diagnostic runs).

## SMT timing and profiler evidence

Timing run after the refactor:

- Allocator module total: **32,678.1 ms** SMT.
  `allocate_free_4k_page` 12,163.2 ms / 14,978,645 rlimit;
  `alloc_4k_scan_all_caches_and_pool` 9,092.4 ms / 11,856,505;
  `pop_stage_4k_page` 5,862.1 ms / 7,450,438;
  `pop_stage_global_4k_page` 4,717.1 ms / 5,875,369.
- New-thread module total: **8,794.6 ms** SMT.
  Old `create_thread_from_staged_page` is 4,314.4 ms / 5,876,158;
  the active `add_new_thread_to_proc_container_and_scheduler` is 3,006.3 ms;
  merged create is 256.6 ms; top syscall is 392.7 ms.

Using the earlier `LinkedList::remove_helper` 3,337.9 ms reference, exactly five
functions remain above it. Profiler results, not guesses:

- `allocate_free_4k_page`: 22,373 user-quantifier instantiations. Dominant
  sources are `Set` axioms, the process locked-object↔typed-map quantifier
  (`kernel_k_define_spec.rs:819`), allocator-cache typed-map alignment
  (`:963`), map axioms, container/process ownership, allocator `inv()`, and
  CPU-cache `inv()`.
- `alloc_4k_scan_all_caches_and_pool`: 18,814 instantiations. Highest costs are
  CPU-cache `inv()`, container/process ownership relations, page typed-map
  alignment (`:908`), set axioms, allocator `inv()`, and
  `cache_perms_match_lctx`.
- `pop_stage_4k_page`: 14,956 instantiations. Dominated by map/set axioms, the
  explicit Free4k preservation forall in this function, `LockedArray`
  unchanged-except, page typed-map alignment, and allocator/page ownership.
- `pop_stage_global_4k_page`: 12,932 instantiations. Dominated by map/set
  axioms, `LockedArray` unchanged-except, page typed-map alignment, and
  allocator quota/global/cache exact-match quantifiers.
- Old `create_thread_from_staged_page`: 7,767 instantiations. The largest
  hotspot is `container_endpoint_wf`; next are `LockedMap::wf`,
  thread/process/container relation foralls, and the function's explicit
  process-thread preservation forall.

## `allocate_free_4k_page` assume-false ablation

Runs 393–412 used temporary `assert(false) by { assume(false); }` cuts and then
removed every cut. The restored final baseline (#412) verifies at exactly
**14,978,645 rlimit**, **10,906 ms SMT**.

The dominant proof is the slow-path post-boundary forall at
`allocate_free_4k_page.rs:891`: all allocator CPU caches must be unlocked in the
new `lctx`. The expensive inner ground assertion is the bridge from
`cpu_caches[c].locked_by(lctx)` to `lctx.lock_id_set().contains(cache_lock_id)`
at lines 900–907.

- Cut before that cache forall: **4,826,085 rlimit / 3,336 ms SMT** (#404).
- Cut immediately after proving it: **13,239,406 / 9,544 ms** (#405).
- Admit the forall proof body: **4,826,085 / 3,313 ms** (#406).
- Prove only its lock-id-set membership assertion, then cut:
  **14,483,409 / 10,497 ms** (#407).

Thus the membership assertion alone nearly reproduces the whole function's
cost. It activates the bidirectional allocator lock-map quantifiers
(`allocator_locked_match_lctx`, especially the cache forward/reverse clauses)
and `LocalContext::wf`, then the map-values/Set axioms needed to bridge
object-locked state through the typed allocator map into `lock_id_set`.
The scheduler, CPU-preservation, and held-major foralls before it were not the
hotspot. Measurements are intentionally treated as non-additive: later facts
can reduce rlimit, and cutting immediately after the two unlocks was cheaper
than cutting immediately before them.

## Direct boundary lock-ownership preservation

The indirect cache-membership hotspot was not inherent: the allocator function
already required the direct negative forall
`cpu_caches[c].locked_by(lctx) == false`, but `kernel_step_boundary` preserved
only objects positively held before the boundary. It did not directly expose
the sound converse that the same `LocalContext` cannot acquire a new object
across an interleaving.

`kernel_step_boundary` now ensures the opaque object-level
`boundary_no_new_locks(pre, post, pre_lctx, post_lctx)`. It covers every locked
map/array family plus quota/cache/global-pool for all three allocator sizes.
`allocate_free_4k_page` restores its entry cache/pool negative facts directly
after its lock/unlock pair and carries them through the boundary with this
predicate. The former cache/global-pool proofs through typed maps,
`LocalContext::wf`, `lock_id_set`, and lock majors are gone.

- Old restored baseline: **14,978,645 rlimit / 10,906 ms SMT**.
- Direct boundary ownership version: **6,384,331 / 5,008 ms**.
- Reduction: **8,594,314 rlimit (57.4%)** and about **5.9 s SMT**.
- Allocator module: **15 verified, 0 errors**.
- New-thread module: **12 verified, 0 errors**.
