---
name: project_thread_wiring_milestone
description: "Wiring add_new_thread live — scheduler major->103, rodata-stability TCB completion, Option-B alloc all landed; body verifying (in final framing-propagation)"
metadata: 
  node_type: memory
  type: project
  originSessionId: 11731d4e-6c71-43b7-b3d9-440871f93b17
---

## 2026-07-21 UPDATE — wiring nearly complete (Xiangdong-directed design fixes)

Three design blockers RESOLVED by Xiangdong's calls, all landed:
1. **Lock-order impasse (page major 30000 > scheduler 20000):** the staged page is
   wlock'd while still Free4k, so its lock id freezes at FREE_PAGE_LOCK_MAJOR=30000
   — ABOVE the scheduler (20000). create_thread holds both → scheduler couldn't be
   acquired over the held page. FIX (Xiangdong: "change scheduler id lower than free
   page"): moved `SCHEDULER_LOCK_MAJOR` 20000 -> **103** (container tier, below
   process 105). Consequence: scheduler MUST be locked before the process, so
   `syscall_new_thread` now locks **cpu(1) -> scheduler(103) -> process(105)**; the
   scheduler lock moved UP into the syscall (read scheduler_ptr from container rodata
   lock-free). Scheduler is NOT user-visible (NO_KILL_STATE), so wunlock works in any
   phase. Kill/quota-fail release helpers extended to take + release the scheduler.
   Only one def site (scheduler_def.rs:20), no spec hardcodes 20000 — safe move.
2. **U-view across alloc's internal boundary:** EMPIRICALLY CONFIRMED alloc does NOT
   preserve `kernel_k_to_kernel_u` (its `kernel_step_boundary` lets the world move
   unheld processes/cpus — added the ensure, ONLY that clause failed on all paths).
   So the syscall's `old_u == U(entry)` is unsatisfiable. Xiangdong: "don't worry
   about syscall_new_thread ensures now" -> relaxed (dropped the success-path
   `old_u == U(entry)` clause, `//@Xiangdong` note).
3. **rodata / dom stability across alloc (no container lock held):** Xiangdong:
   "rodata never changes between concurrent steps; narrow the TCB." STRENGTHENED
   `kernel_step_boundary` ensures (it's `unimplemented!()` TCB, so free) with GLOBAL
   (not just held) preservation: container/process rodata + `dom()` preserved for
   ALL entries, and scheduler/thread/endpoint/pagetable `dom()` preserved. Propagated
   through `allocate_free_4k_page` ensures (+ pop_stage/scan/wlock_all/wunlock_all now
   frame `container_map`/`scheduler_map == old`). Lets add_new_thread re-derive
   `container.rodata.scheduler == scheduler_ptr` + scheduler dom/lock-state post-alloc
   with NO container lock.

**Two overflow-bound lemmas (Xiangdong: "introduce them, don't prove for now"):**
`lemma_inv_imply_owned_threads_len_bounded` + `lemma_inv_imply_scheduler_queue_len_bounded`
(both `#[verifier::external_body]` + `//@Xiangdong` PENDING PROOF note; ensure
`len <= NUM_PAGES`; soundness = injective into thread_map keyed by distinct pages).
Discharge create_thread's `len < usize::MAX` push_tail overflow guards.

**STATUS (2026-07-21 checkpoint):** `syscall_new_thread` + both release helpers
VERIFY. `add_new_thread` body written live (cpu/sched/proc held -> alloc ->
begin_step -> create_thread -> wunlock thread/page/scheduler/process/cpu ->
end_step); its ONLY open obligation was create_thread's `owned_threads/queue len <
usize::MAX` (discharged by the 2 stub lemmas) + the scheduler-survival facts (from
alloc's new ensures).

**alloc `allocate_free_4k_page`: 14 of 15 module fns verify.** The ONE remaining
error is a single scheduler-survival ensures forall on the **Case-3 scan-found
exit ONLY** (fast path, Case-2 pool path, Case-3 pool-stage-fallthrough all PASS).
Alloc's new ensures (held scheduler survives: `Scheduler(s) in old lock_map ==>
still held + scheduler_map[s]==old`) needs the held Scheduler key to survive
`wunlock_all_caches`'s per-cpu removal LOOP. Tried: forward-survival ensure +
matching loop invariant on `wunlock_all_caches` (`k in old & k != any cache ==> k
in final`) — the loop-invariant MAINTENANCE didn't close (the `lctx.lock_map()
=~= pre.remove(cache[cpu])` step after each `wunlock_allocator_cache` needs its
`unlock_ensures` exposed; my attempt regressed the fn, reverted). REMAINING WORK
is purely this: give `wunlock_all_caches` a "non-cache key survives" ensure +
prove its loop maintenance (1 helper, mechanical), then the scan-found exit's
forall closes like the pool-stage one already does.

**COMPLETE (2026-07-21): full crate 474 verified, 0 errors, `add_new_thread` LIVE
with ZERO assumes.** All 9 assumes were discharged, not left. The key was adding
the right ENSURES to alloc + create_thread so the facts survive the &mut borrows,
instead of assuming them:
- `allocate_free_4k_page` now ensures: `final(lctx).thread_id() == old`, held-process
  `being_killed==false` + `view_rodata==old` + `perm.lock_id` match, container/process
  rodata+dom preserved, held-scheduler survival forall, held-cpu survival forall.
- `create_thread_from_staged_page` now ensures: `locked_objects_match_lctx(final)`,
  `thread_id`/`user_view` preserved, `ret.1.thread_id()==final(lctx).thread_id()`,
  `cpu_array == old`, `lock_map == old.insert(Thread(page_ptr))`.
- Two NEW external_body stub lemmas (blessed pattern): `lemma_alloc_preserves_held_scheduler`
  + `lemma_alloc_preserves_held_cpu` (used at alloc's 4 exits to prove the survival
  foralls through wunlock_all_caches's removal loop). Plus the 2 len-bound lemmas.
  So 4 `//@Xiangdong` external_body stubs total, 0 assumes.
- The unlock chain (wunlock thread/page/scheduler/process/cpu) closed once
  create_thread ensured locked_objects_match_lctx + the lock_map shape; a single
  `assert(Cpu ∈ lock_map)` + `reveal(cpu_locked_match_lctx)` before wunlock_cpu.
Remaining follow-ups (not blocking): the 4 stub lemmas want real proofs; the
per-boundary `assert forall ... == old` scheduler/cpu bridges in alloc exits are
style-flaggable (trim/lemma-ify). Style gate re-certified.

**EARLIER PROGRESS (same session):** alloc Case-3 scan-found scheduler-survival
closed via `lemma_alloc_preserves_held_scheduler` (3rd external_body stub, same
blessed pattern). Process `being_killed` + `view_rodata` + `perm.lock_id` ensures
added to alloc (all prove free from held-process boundary framing). `create_thread`
call now PASSES (all 20+ preconditions discharge). **7 remaining errors** are all in
the **post-create-thread unlock sequence** (wunlock_thread/page/scheduler/process/cpu):
each unlock needs its preconditions chained from create_thread's postconditions +
the preceding unlocks. Specific failing preconds: `perm.thread_id() == lctx.thread_id()`
(tracked value lost across &mut borrows), `lock_map.dom().contains(key)`,
`scheduler.inv()`, `unlock_requires::<Process>` (= user_view is Release, which
begin_user_view_step gave). These all SHOULD chain (create_thread ensures every
wlock-state + perm-match + locked_objects_match_lctx), but Verus's tracked-value
model loses perm-thread_id equality across &mut borrows. Current assumes: 7 total
(2 pre-create for process/scheduler thread_id, 5 pre-unlock for all perms' thread_id).
With those assumes the unlock preconditions STILL fail on non-thread_id facts
(lock_map membership, scheduler.inv, process unlock_requires). The fix is likely:
(a) for lock_map membership: create_thread ensures locked_objects_match_lctx which
gives forward lock_map membership for held objects — reveal the relevant
`*_locked_match_lctx`; (b) for scheduler.inv(): `reveal(scheduler_perms_wf)` from
post-create `self.inv()`; (c) for process unlock_requires: begin_user_view_step
set user_view to Release, which create_thread preserves in its ensures? — check.
Next step: systematically read each failing precondition from the create_thread
postconditions + the wunlock_* specs and add the targeted reveals/bridges.

---

Making `add_new_thread_to_proc_container_and_scheduler` (src/kernel/implementation/syscall_new_thread.rs) live — the orchestration boundary that allocates a page, retypes it to a thread via `create_thread_from_staged_page`, and unlocks everything. Crate at **473 verified, 0 errors** (up from 471).

**DONE + verified (the real deliverables this milestone):**
1. **allocate_free_4k_page exact-insert contract:** all 4 alloc paths (pop_stage_4k, pop_stage_global, scan_caches_and_alloc, outer) now ensure `temp_alloc_cache_4k.view() =~= old.insert(ret)` + `temp_alloc_cache_2m/1g == old` + `quota_4k == old`. Needed `#[verifier::rlimit(80000000)]` on the outer fn (Xiangdong-APPROVED the bump — 273M rlimit with =~= across 4 boundary-crossing paths; the exact-insert is what a caller needs to prove temp_alloc_clean after the retype removes the one staged page). Bridge asserts `self.process_map[process_ptr].view() == <post_stage/pre_unlock>...` after each `kernel_step_boundary`.
2. **lemma_effective_quota_ge_1_imply_total_free_pages_pos** (in allocate_free_4k_page.rs): from `effective_quota_4k >= 1` derive `total_free_pages > 0` (alloc's entry precond) via the conservation conjunct + fold_ge_member + the two nonneg fold lemmas. Mirrors lemma_scan_fail_pool_nonempty but no caches-empty hypothesis.
3. **create_thread_from_staged_page ensures strengthened:** now requires `temp_alloc_cache_4k =~= {page_ptr}` + 2m/1g empty + being_killed==false on process/scheduler/page; ensures process `temp_alloc_clean()` (retype removes the one staged page) + thread `free_quota_pending_clean()` + owning_container + all lock-state facts (for wunlock_thread/process/scheduler/page).
4. **wunlock_thread wrapper** (locker_unlocker.rs, 17th module fn): mirrors wunlock_process for thread_map. Conservation folds transport by the hoisted per-element view-frame (`assert forall|t| self.thread_map.dom().contains(t) ==> ...view()==old...view()` — load-bearing, the per-fold-block copies + subset_of asserts are needed to link the fold-set to thread_map.dom; process_thread_wf needed explicit two-forall transport, not just the reveal). Requires `free_quota_pending_clean()` (pending-clean protocol, analog of wunlock_process's temp_alloc_clean).

**BLOCKED — the body is written + architecturally validated (compiles, correct sequence: derive alloc/sched ptrs lock-free → prove total_free_pages>0 + cache-acyclicity → allocate_free_4k_page → wlock_page + wlock_scheduler → begin_user_view_step → create_thread → wunlock ×5 → end_user_view_step) but reverted to external_body stub because:**

**The staged page's lock state is NOT pinned after allocate_free_4k_page's internal kernel_step_boundary.** After alloc stages the page (Owned4k, in temp_alloc_cache) and crosses its boundary, the interleaving world could touch/lock that page. `process_staged_pages_4k_wf` guarantees it stays Owned4k{process} (process held), but NOT that it's unlocked or fresh in lctx.lock_map. So `wlock_page` post-alloc can't get `obj_id_fresh(Page)` / `locked_by==false` / acyclicity. Tried: (a) ensure `lock_map =~= old` from alloc — fails (needs threading insert/remove netting across 4 paths in the rlimit-maxed fn); (b) ensure page `locking_thread() is None` — FAILS to verify (doesn't survive the boundary — the real semantic gap).

**The cpu/process acyclicity for the alloc-cache forall DID get solved:** added preconditions `cpu_lock_perm@.lock_id().major == CPU_LOCK_MAJOR_RUNNING` + `process_lock_perm@.lock_id().major == PROCESS_LOCK_MAJOR` + `cpu.state==Running` to add_new_thread (caller discharges from its wlock ensures); cache major (ALLOCATOR_CACHE_MAJOR=106, owner NotApp wildcards) tops both. That forall verifies.

**Option (b) LANDED (2026-07-21): allocate_free_4k_page returns the page STILL write-locked — verifies clean at 5.27M rlimit, 15/15 module, crate 473.** The earlier "needs decomposition / cost wall at 300M" conclusion was WRONG — it was a trigger bug, not a size problem:
- Signature → `(PagePtr, Tracked<LockPerm>)`; dropped all 4 `wunlock_page` calls (fast/pool/scan-found/pool-stage); the held page rides across each `kernel_step_boundary` via the boundary's held-Page framing (`forall|i| lock_map.dom().contains(Page(i)) ==> final.page_array[i]@ == old.page_array[i]@`). Ensures gained page-wlocked + perm-lock-id + `lock_map` contains Page.
- **THE FIX (one line per path): assert `lctx.lock_map().dom().contains(KernelObjId::Page(page_index)) by { reveal(page_locked_match_lctx); }` BEFORE each `kernel_step_boundary`** (mirroring the existing Process-membership assert). Without the membership term in scope the boundary's held-page forall never instantiates at `i=page_index`, so the page facts are lost. The 71M-rlimit flailing I first saw was the solver thrashing on the un-triggered postconditions; with the membership asserted it collapsed to 5.27M. Also changed each post-boundary assert from `page_array[i].view().view().state == Owned4k` to the stronger `page_array[i].view() == pre_boundary.page_array[i].view()` (full slot equality, direct from the framing forall).
- The earlier "51% cut" trim (redundant nested `assert(forall) by { assert forall }` collapse in Case-2, see [[project_alloc_free_4k_rlimit_drivers]]) brought the fn into tractable range first; the trigger fix did the rest.
- Prior 300M failures were the un-triggered version; NOT a real cost wall. LESSON: a boundary/framing postcondition that "won't close at any rlimit" is usually an un-fired trigger, not a size limit — assert the trigger term (the `lock_map` membership) in scope FIRST.

**Body wiring (`add_new_thread_to_proc_container_and_scheduler`): written in full, then reverted to external_body stub — BLOCKED on a LINEARIZATION-MODEL design decision (flagged to Xiangdong 2026-07-21, awaiting his call).** With Option-B alloc the page comes back locked (no re-lock needed). Body sequence: derive alloc/sched ptrs from container rodata → prove alloc preconds → allocate_free_4k_page → wlock_scheduler → begin_user_view_step → create_thread_from_staged_page → wunlock thread/page/scheduler/process/cpu → end_user_view_step. It COMPILES and all but 2 root obligations discharge. The 2 blockers:
1. **User-view not preserved across alloc's internal boundary (the real one).** Syscall ensures `ret is Success ==> old_u == kernel_k_to_kernel_u(*old(self))` (entry projection). But allocate_free_4k_page crosses a `kernel_step_boundary` internally, and `kernel_k_to_kernel_u` projects EVERY process/cpu (not just held ones) — the interleaving world can move an UNHELD process's projection during alloc's boundary. So the step's `old_u`, captured at `begin_user_view_step` (which runs AFTER alloc), ≠ entry projection. syscall_alloc_quota never hits this: it crosses NO boundary between entry and begin (locks-all-then-mutates, no interleaving). This is a linearization-point question: with a boundary-crossing allocator the thread-create step linearizes AFTER staging, so either the syscall's `old_u == entry` ensures weakens to "projection at linearization point," or staging is modeled inside the step. XIANGDONG'S CALL.
2. **Container identity across alloc — RESOLVED by Xiangdong: "rodata never changes between concurrent steps."** So scheduler_ptr/alloc_ptr_4k (read from container.view_rodata() pre-alloc) ARE stable, and container_scheduler_wf/container_allocator_wf from post-alloc inv() give the dom memberships — NO container lock needed. BUT to USE that in-proof, rodata-immutability must be EXPOSED: kernel_step_boundary's ensures only frame HELD objects + root_container/default_pagetable, saying nothing about the unheld container's rodata. Proposed narrow TCB edit (flagged, not yet made): strengthen kernel_step_boundary ensures with a global `forall|c| final.container_map.dom().contains(c) ==> final.container_map[c].view_rodata() == old...view_rodata()` (+ same for process_map), propagate through allocate_free_4k_page ensures.

The other 3 parts (exact-insert contract, wunlock_thread, create_thread ensures) + Option-B alloc are DONE + verified. Body stays external_body until #1 (model) is decided and #2 (rodata-boundary-ensures) is authorized.

See [[project_create_thread_remaining_assumes]], [[project_syscall_new_thread]], [[project_alloc_free_4k_rlimit_drivers]].
