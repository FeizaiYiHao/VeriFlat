---
name: project_lockedmap_insert_tcb
description: "New TCB LockedMap::insert primitive (grows the map domain) — first step toward thread creation; awaiting Xiangdong's review"
metadata: 
  node_type: memory
  type: project
  originSessionId: 11731d4e-6c71-43b7-b3d9-440871f93b17
---

Added `LockedMap::insert` — a NEW TCB `#[verifier::external_body]` primitive in
`src/locks/locked_map.rs` (on the `impl<T:LockInvTrait+LockMajorTrait+
LockOwnerIdTrait+LockUserVisibilityTrait, ROT:LockOwnerIdTrait, KGhostT, UGhostT>
LockedMap<usize,...,HAS_KILL_STATE>` block, next to `lock_id_by_key`). It is the
FIRST piece of the "add new TCB stuff for thread creation" task, written for
Xiangdong to review before building on it.

**What it does:** the ONLY operation that GROWS a LockedMap's domain (every other
method fixes `dom()`). Mints a fresh `RwLock<T>` at a fresh `key`, holding
caller-supplied `value`/`rodata`/`kernel_ghost`/`user_ghost`, `is_init`,
`being_killed()==false`, and WRITE-LOCKED by the caller (so caller can `borrow_mut`
→ finish wiring → `wunlock`). Registers the lock id in `lctx` via `lock_ensures`
(adds `obj_id`), returns the `LockPerm`. Same lock-id discipline as `wlock`
(container/process/major from value+rodata via `current_lock_major`, minor=key;
`lock_id_acyclic` + `obj_id_fresh` preconditions).

**Verifies:** `locks::locked_map` 10 verified 0 errors; full crate 462, 0 errors.
Purely additive.

**Gotchas hit:** (1) a bare `RwLockState::Write {...}` / `LockId{...}` struct literal
as the RHS of `==` in an `ensures` clause fails Rust's parser (struct-literal
ambiguity) — must wrap in parens `(RwLockState::Write {...})`. (`wlock_ensures`
avoids it by being inside a spec-fn body.) (2) The IDE code-analyzer flags these
struct literals as syntax errors even parenthesized — IGNORE it; the real Verus
verifier accepts them. (3) body is `unimplemented!()` (TCB idiom; real alloc is
hardware/out-of-model). (4) owner-id must use `current_lock_major()` (the
predicate-driven selector `wlock` uses), NOT `lock_major_1()`.

**STILL NEEDED for thread creation (see [[project_syscall_new_thread.md]]):**
still blocked on (a) a fold-insert-of-zero axiom for
`container_process_allocator_quota_*_wf` (kernel_fold_axioms.rs), and (b) the
page-retype-to-`Allocated4k{AsThread}` + `thread_pages_wf` machinery. `insert`
solves only the "grow thread_map" blocker. Next: wait for Xiangdong's review of
`insert`, then the fold axiom + retype.
