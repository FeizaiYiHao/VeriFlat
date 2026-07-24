---
name: feedback_lock_id_ordering_frozen_at_acquire
description: "An RwLock's lock_id (incl. major) is FROZEN at acquire time from the payload state then, not the current state — check the state-at-lock for acyclicity"
metadata: 
  node_type: memory
  type: project
  originSessionId: 11731d4e-6c71-43b7-b3d9-440871f93b17
---

An RwLock's `lock_id` — including its `major` (from `current_lock_major()`) — is
**computed at acquire time from the payload state AT THAT MOMENT** and then frozen
in the `locking_thread()`/`LockPerm`/`lock_map`. Retyping the payload AFTER locking
does NOT recompute the id.

**Concrete gotcha that reshaped the whole thread-wiring design:** the staged 4k
page in `allocate_free_4k_page` is `wlock_page`'d while still `Free4k`, so its lock
id freezes at `FREE_PAGE_LOCK_MAJOR = 30000` — even though it's retyped to
`Owned4k` before being returned. So the "owned" page you hold locks like a FREE
page (major 30000, top of the hierarchy).

**Consequence for lock ordering (`lock_id_acyclic`):** to acquire lock X while
holding the page, X's major must exceed 30000. The scheduler was at
`SCHEDULER_LOCK_MAJOR = 20000` < 30000, so `create_thread` (which holds both the
page AND the scheduler) could not acquire the scheduler over the held page. FIX
(Xiangdong's call): moved `SCHEDULER_LOCK_MAJOR` 20000 → **103** (container tier,
below process 105), forcing lock order **cpu(1) → scheduler(103) → process(105) →
[alloc: cache(106), page(30000)]** — scheduler acquired BEFORE the process/alloc.

**Rule:** when reasoning about `lock_id_acyclic` for a held object whose payload was
retyped, use its **state-at-lock-time**, not its current state. `LockId::spec_gt`
compares container-owner (`spec_eq`, NotApp is wildcard), then process-owner, then
`major`, then `minor`. Majors live in `src/define/lock_id.rs`. A page carries
container/process = `None` (not NotApp), so ordering vs a `NotApp/NotApp` object
(scheduler) is decided purely by `major`.

See [[project_thread_wiring_milestone]].
