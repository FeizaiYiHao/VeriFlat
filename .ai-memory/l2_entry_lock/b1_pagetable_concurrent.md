# B1 — pagetable_concurrent proofs

**Goal.** B0 has frozen the new structures and exec bodies, and `veriflat_kernel_core` typechecks. Make every proof in the pagetable_concurrent module and the two pagetable_seq window files verify. B2 runs in parallel on other kernel_core files.

**Owned files** (edit only these):
- `src/pagetable_concurrent/*.rs` except `l2_page_map.rs` (frozen)
- `src/pagetable_seq/pagetable_window_stale_eof.rs`, `src/pagetable_seq/pagetable_util_t.rs`

**What to change.**
- Invariants: prove the new bodies of the copied §E.1. They were written by B0; keep the clause text. Delete `l2_tokens_paired` (:497) and its `_at` lemma (pagetable_concurrent_lemma.rs:131) if B0 has not done so.
- `lock_window`/`unlock_window` EOF: re-prove with the S text of the copied §B.3 (`lock_window_eof_transition_framing`, `unlock_window_eof_transition_framing` in pagetable_concurrent_lock_eof.rs:7/:31) and the closures `lock_window_eof` (:51), `lock_window_eof_window_locks` (:79), `unlock_window_eof` (:103), `unlock_window_eof_window_locks` (:130).
- Write-path primitives (copied §B.4) and their EOF families: `*_create_eof.rs`, `*_create_window_eof.rs`, `*_map_eof.rs`, `*_map_2m_eof.rs`, `*_remove_eof.rs`, `*_unmap_eof.rs`, `*_unmap_kernel_eof.rs`.
  - Every S that framed `l2_ghost`/`l2_lock`/`l1_tables`/`locked_windows` now frames `l2_perms` except the touched `(p, i)` entry, `l1_rev_map`, and `pagetable_window_locks`.
  - `create_entry_l3` S states `pagetable_window_locks@ == pagetable_window_locks_after_new_l2_page(old, l4i, l3i, <range of lo..=hi>)`.
  - `remove_l3_entry` S removes the 512 keys of `(l4i, l3i)` (all of them `Unlocked`, by its precondition that every owner is `None`).
- `*_wf_at` point lemmas in pagetable_concurrent_lemma.rs (:147 :157 :178 :189 :220 :231): restate them over the new accessors.
- `pagetable_concurrent_range.rs` (:188-:586, :689, :778) and `structure_scan.rs` (:105 :132 :219 :265): update to the new `get_entry_l1` arguments and accessors.
- `pagetable_window_stale_eof.rs` :15/:25/:89/:91/:154/:156 and `pagetable_util_t.rs` :354/:356: `l2_lock.dom()` → `l2_perms@.dom()`; `l2_lock_of(p).locked_by_thread(i, t)` → `l2_owner(p, i) is Some && l2_owner(p, i)->Some_thread_id == t`.
- Inline accessors: `l2_page`, `l2_entry`, `l2_owner`, `l1_perm`, `l1_page` are `#[verifier::inline]` (a non-inline accessor over `self.lower` breaks congruence of old/new trigger terms; 2026-10-13). Triggers must stay flat `(p, i)`. A deep `l2_perms@[p].value().ar@[i].l1@` trigger is a known mode-flip risk: prefer the `dom().contains(p)` outer forall with an inner `(i)` trigger.
- If an invariant does not close, inspect producer triggers before adding asserts (AGENTS.md). Survey leaves with the two-run naked/reveal batch rule.

**Must not change.** `l2_page_map.rs`, `PageTableLower` fields and accessor signatures, the `pagetable_window_locks_after_*` helpers, and every pub fn signature B0 reported. New invariants or framing lemmas beyond the copied text need approval: stop and report.

**Runs.** One run per batch of fixes:
`systemd-run --user --scope -p MemoryMax=30G ./verify-workspace.sh --package veriflat_kernel_core -- --verify-only-module pagetable_concurrent::pagetable_concurrent_spec --verify-only-module pagetable_concurrent::pagetable_concurrent_lock ...`, listing every pagetable_concurrent module you touched plus `pagetable_seq::pagetable_window_stale_eof` and `pagetable_seq::pagetable_util_t`. Use `--time-expanded` once at the end to report any equation over 10 s SMT.

## Copied design text (authoritative for this batch)

### A.2 `pagetable_concurrent/pagetable_concurrent_spec.rs` — `PageTableLower` (:28-38)

| field | fate |
|---|---|
| `l2_perms: Tracked<Map<PageMapPtr, PointsTo<L2PageMap>>>` | kept; becomes the single owner of L2 *and* L1 permissions |
| `l2_ghost: Ghost<Map<PageMapPtr, L2PageGhost>>` | **deleted**, subsumed by `ar[i].entry` |
| `l2_lock: Ghost<Map<PageMapPtr, L2LockGhost>>` | **deleted**, subsumed by `ar[i].owner` |
| `l1_tables: Tracked<Map<PageMapPtr, PointsTo<PageMap>>>` | **deleted**, moved into `ar[i].l1` |
| `l1_rev_map` | kept; `l1_rev_map.dom()` is now the L1 page set |
| `mapping_4k`, `mapping_2m`, `window_stale_cpus` | kept |
| `locked_windows: Ghost<Set<WindowVa>>` | **replaced** by `pagetable_window_locks: Ghost<Map<WindowVa, LockStateU>>` (decision D1) |

New `#[verifier::inline]` open accessors on `PageTableLower`, following the 2026-10-13 rule that a non-inline accessor over `self.lower` breaks congruence of old/new trigger terms. They replace `l2_page` (:319) and `l2_lock_of` (:322):
- `l2_page(p) = self.l2_perms@[p].value()` (kept name)
- `l2_entry(p, i) = self.l2_page(p).entry_lock(i).view()`
- `l2_owner(p, i) = self.l2_page(p).entry_lock(i).owner()`
- `l1_perm(p, i) = self.l2_page(p).entry_lock(i).l1()->Some_0`
- `l1_page(p, i) = self.l1_perm(p, i).value()`

`PageTableWindowView` (:48), `WindowVa` (:58), `window_lock_id` (:72) and `va_range_2m_windows` (:88) are unchanged.

### B.3 `pagetable_concurrent_lock.rs` rewrite
`lock_window(&self, Tracked(lower): Tracked<&mut PageTableLower>, lctx, l4i, l3i, l2i, lock_id) -> Tracked<LockPerm>` (:10):
- Requires: as today, including `lock_id_acyclic` and `!window_locked_by_thread`.
- Body:
  1. `let tracked perm = lower.l2_perms.tracked_remove(p)`. Removing and re-inserting keeps the `l2_perms` map edit flat; `tracked_borrow_mut` on a `Map` is not available.
  2. `PPtr::borrow_mut(p).ar[l2i].lock(lctx, lock_id, obj)`.
  3. `lower.l2_perms.tracked_insert(p, perm)`.
  4. `lower.pagetable_window_locks@ = pagetable_window_locks.insert(w, WriteLocked)`.
- Ensures `lock_window_eof_transition_framing` + `lock_perm_match` + `lock_ensures`.

`unlock_window` (:53) is symmetric.

New S (`pagetable_concurrent_lock_eof.rs:7/:31`), with the old clauses for `l2_ghost`, `l2_lock`, `l1_tables` and `locked_windows` deleted:
```
lock_window_eof_transition_framing(old, new, p, i, w, t) =
  &&& new.l2_perms@.dom() == old.l2_perms@.dom()
  &&& forall|q| q != p ==> new.l2_perms@[q] == old.l2_perms@[q]       // trigger new.l2_perms@[q]
  &&& new.l2_perms@[p].addr() == old.l2_perms@[p].addr() && new.l2_page(p).addr() == old.l2_page(p).addr()
  &&& forall|j| j != i ==> new.l2_page(p).entry_lock(j) == old.l2_page(p).entry_lock(j)
  &&& new.l2_entry(p, i) == old.l2_entry(p, i) && new.l2_page(p).entry_lock(i).l1() == old.l2_page(p).entry_lock(i).l1()
  &&& new.l2_owner(p, i) == Some(t)
  &&& new.pagetable_window_locks@ == old.pagetable_window_locks@.insert(w, LockStateU::WriteLocked)
  &&& new.l1_rev_map, mapping_4k, mapping_2m, window_stale_cpus == old
```
The EOF closures `lock_window_eof` (:51), `lock_window_eof_window_locks` (:79), `unlock_window_eof` (:103) and `unlock_window_eof_window_locks` (:130) keep their names and are re-proved `[X]`.

### B.4 Write path for L1 / L2 entries (7 lower primitives)
Pattern used by `create_entry_l2` (impl_base:175), `remove_l2_entry` (remove_base:116), `map_2m_page` (impl_map:72) and `remove_structure_page` L1 (structure_scan:132):
```
remove l2 perm → borrow_mut page → e.set_published_locked(&lp, v, lctx)
→ *e.borrow_l1_mut(&lp) = Tracked(Some(l1perm)) | Tracked(None) → reinsert l2 perm
```
`map_4k_page` (:9) and `unmap_4k_page_*` (:9/:65) write into L1. They obtain `&mut PointsTo<PageMap>` through `borrow_l1_mut`, then do `PPtr::<PageMap>::borrow_mut` as in seq. Old: `lower.l1_tables.tracked_borrow_mut` (not available) → `tracked_remove`/`insert`.

These 7 primitives gain `Tracked(window_perm): Tracked<&LockPerm>` (decision D5).

---

### C.1 crate `veriflat_kernel_core` — module `pagetable_concurrent` (B1)
- `l2_page_map.rs`: rewrite (§A.1, §B.1–B.2).
- `pagetable_concurrent_spec.rs`:
  - struct :28; accessors :319/:322.
  - `is_empty` :351 → `pagetable_window_locks@.dom().is_empty()`, `l1_rev_map.dom().is_empty()`.
  - `page_closure` :365 → `l1_rev_map@.dom()` replaces `l1_tables@.dom()`. **This is a cross-crate contract (allocator/page closure)**: the value is equal under `wf`, but the term changes.
  - `spec_resolve_mapping_4k_l1` :407 → `l1_page(l3.addr, l2i)`.
  - `window_locked_by_thread` :437 → `l2_owner(p,i) is Some && l2_owner(p,i)->Some_thread_id == t`.
  - `window_locked` :444 → `pagetable_window_locks@[w] == WriteLocked`.
  - `hidden_leaves_in_locked_windows` :449, `window_view` :465, `window_free_for` :479.
  - wf: `l2_tokens_paired` :497 (delete; covered by `L2PageMap::wf`), `wf_l2` :514, `wf_l1` :542, `user_only` :555, `rwx_upper_level_entries` :567, `table_pages_wf` :577, `tables_reachable_wf` :589, `wf_mapping_4k` :622, `wf_window_locks` :651, `wf` :668 (§E).
- `pagetable_concurrent_lock.rs` :10/:53 and `pagetable_concurrent_lock_eof.rs` :7-:130: §B.3.
- `pagetable_concurrent_impl_base.rs`:
  - `create_entry_l3` :66: no longer receives minted perms. After `page_perm_to_l2_page_map` it locks `lo..=hi` one by one with `e.lock(lctx, window_lock_id(..), ..)`. The loop has `decreases hi+1-k` and runs on the unpublished page, so it has no acyclic obligation. It returns `Tracked<Map<L2Index, LockPerm>>` as today.
  - `pagetable_window_locks@ = pagetable_window_locks_after_new_l2_page(..)` (§D.4) replaces `locked_windows.union`.
  - EOF `create_entry_l3_eof*` re-proved `[X]`.
  - `create_entry_l2` :175 (set_published :229): pattern B.4.
  - `create_entry_l4` :10: unchanged except the S fields.
- `pagetable_concurrent_impl_remove_base.rs`: `unmap_4k_page_user_view` :9, `unmap_4k_page_kernel` :65, `remove_l2_entry` :116 (:166), `remove_l3_entry` :182 (L2 page → `l2_page_map_to_page_perm`, requires all owners None, `pagetable_window_locks` minus 512 keys), `remove_l4_entry` :256.
- `pagetable_concurrent_impl_map.rs`: `map_4k_page` :9, `map_2m_page` :72 (:115).
- `pagetable_concurrent_util.rs`:
  - `get_entry_l2` :100 / `get_entry_2m_l2` :123: `.ar[i].get()`.
  - `get_entry_l1` :146 gains an `l3_entry: &PageEntry` / `l2i` argument and reads `l1_perm(l3.addr, l2i)`.
  - `spec_empty` :178 / `tracked_empty` :186 lose 3 fields.
  - `resolve_mapping_4k_l2/_l1` :266/:299.
- `pagetable_concurrent_structure_scan.rs`: `remove_structure_page` :132 (L1 branch: window perm; L2 branch requires `forall i. l2_owner(p,i) is None`; ensures `pagetable_window_locks@ ==` / `.remove_keys`); `scan_l2_table` :219; `l1_table_has_no_leaf` :265.
- `pagetable_concurrent_range.rs` :188-:586 (`get_entry_l1` argument), :689, :778.
- `pagetable_concurrent_lemma.rs`: `l2_tokens_paired_at` :131 (delete), `wf_l2_at` :147, `wf_l1_at` :157, `tables_reachable_wf_l1_at` :178, `wf_mapping_4k_at` :189, `wf_window_locks_va_at` :220, `wf_window_locks_slot_at` :231. All are restated `[X]`.
- `pagetable_concurrent_util_t.rs:10` `retype_page_to_pagetable_c_and_insert`: empty-lower construction.

### E.1 Invariant changes (`pagetable_concurrent_spec.rs`)
| predicate | new body | approval |
|---|---|---|
| `wf_l2` :514 | per (p∈l2_perms.dom, i): `l2_page(p).wf()`; `addr` matches; clause 2: present ∧ ¬ps ⇔ `l1()` Some, then `l1_perm.addr()==entry.addr` ∧ `l1_rev_map.contains(entry.addr)` | restatement of existing |
| `l2_tokens_paired` :497 | **deleted** (entry `inv` carries it) | delete |
| `wf_l1` :542, `user_only` :555, `rwx_upper_level_entries` :567 | quantify `(p,i)` with `l1() is Some` instead of `l1_tables.dom` | restatement |
| `table_pages_wf` :577 | L1 disjointness over `l1_rev_map.dom()` | restatement |
| `tables_reachable_wf` :589 | L1 part over `l1_rev_map.dom()` | restatement |
| `wf_mapping_4k` :622 | read through `l1_page` | restatement |
| `wf_window_locks` :651 | (a) `forall w ∈ pagetable_window_locks.dom ⇒ window_exists(w) ∧ w ≥ kernel_l4_end ∧ pagetable_window_locks[w] == (owner is Some ? WriteLocked : Unlocked)`; (b) **new dom clause**: `forall p∈l2_perms.dom, i<512 ⇒ pagetable_window_locks.contains_key(w(p,i))` | approved by the user (D1) |
| `pagetable_window_stale_cpus_only_when_locked` (pagetable_map_spec :33) | `l2_owner(p,i) is Some` | restatement |
| `pagetable_window_typed_lock_map_aligned` (:117) | entry owner vs lctx typed map | restatement |

The old "every locked slot ∈ `locked_windows`" two-way alignment becomes clause (a).

### E.2 Lemmas
- `[X]`: all `*_wf_at` restatements in pagetable_concurrent_lemma.rs (:147 :157 :178 :189 :220 :231); `lock_window_eof*` / `unlock_window_eof*` / `create_entry_l3_eof*` closures; trace `_from_u`; kill and thread_exit refund trace lemmas with the optional unlock; EOL summaries for the four range-window loops.
- New approved specs: the three `pagetable_window_locks_after_*` helpers (D7), `kill_process_pagetable_windows_changed_step`, `kill_process_refund_step`, `thread_exit_pagetable_windows_changed_step` and `thread_exit_refund_step`, plus the labels `KillProcessPagetableWindowsChanged` / `ThreadExitPagetableWindowsChanged`.
- Existing lemmas restated in place, with no new statement shape: `pagetable_l2_windows_unlocked_when_wlocker_holds_no_windows` (subsystem_mutation_pagetable_map.rs:948).
- Rename to `<premise>_implies_<conclusion>`: that lemma becomes `wlocker_holds_no_windows_implies_l2_windows_unlocked`. This is an in-scope rename.

## Rules (repository AGENTS.md + skills; read `AGENTS.md` and invoke the `veriflat-proof`, `veriflat-kernel-model` and `veriflat-build` skills before editing)
- Worktree: `/home/xiangdc/VeriFlat/.claude/worktrees/concurrent-pagetable-kill-container-598619` (run all commands from it). Edit **only** the files listed under "Owned files". Never touch other files, never reset/stash/clean, and **never commit**.
- Design reference (read only the sections named here): `/tmp/claude-1000/-home-xiangdc-VeriFlat--claude-worktrees-concurrent-pagetable-kill-container-598619/242142bb-2dbe-4203-89c7-86f8a4fe7835/scratchpad/l2_entry_lock_design.md`.
- **U step span (user principle 2026-10-29):** "所有的 U 步都尽量跨度大一点。每个 syscall 的设计都是性能最优先，然后在不改 exec 代码的前提下 U 跨度尽可能大。runtime 性能是第一优先级."
  - Never reorder locks or add runtime exec work for the U model. Ghost-only exec calls (a `Ghost(..)` argument) are allowed.
  - Between each window lock and its unlock, list every boundary call. A stutter (`kernel_step_boundary_nonlock_fields_unchanged`, `rebase_snapshot_k_if_unchanged`, a u_eq lemma call) that becomes false because of `pagetable_window_locks` is deleted or moved, so the delta folds into the next recorded step. Do not turn it into a new step.
  - If you find a recorded or exec-forced boundary inside a held window that the design's §D.4b table does not list, **stop and report**; do not add a step.
- Exec equations are K-only: no `reveal` of `*_wf`/`*_inv`, no U reasoning. Use wrapper K→U lemmas and the operation's `*_trace.rs` lemmas.
- No `exists`/`choose`, no `assert(forall ..)` in kernel `src/` (the NI crate may use `assert(forall ..)`), no `#[verifier::spinoff_prover]`, and no invariants keyed on `SyscallProgress`.
- New lemmas: only `*_wf_at` point lemmas, EOF closures, fold lemmas, EOL loop summaries, wrapper-layer K→U lemmas, or operation-local trace lemmas (`<op>_<step>_from_u`, `_pre_from_k`, composition) are allowed without approval. Name them `<premise>_implies_<conclusion>`. Any other new lemma, framing spec, or invariant: stop and report. List every added lemma or closure in your report.
- Dense canonical style (proof skill `style-and-discipline.md`; reference: `src/kernel/implementation/syscall_alloc_quota/`).
  - One contract clause per line. Short proofs go on one line.
  - Blocks with `let`: each `let` and each `&&&` on its own line.
  - Pack parameters and arguments into balanced groups; no staircased expressions.
  - Remove diagnostic code before you report.
  - Finish with a style pass over every `src/**/*.rs` file you changed.
- Verification: focused runs only. Command shape (one blocking call; chain all modules of a batch into one run):
  `systemd-run --user --scope -p MemoryMax=30G ./verify-workspace.sh --package <pkg> -- --verify-only-module <mod> [--verify-only-module <mod2> ...]`
  - Module names are rooted at the crate's lib module, e.g. `syscall_ipc::syscall_ipc_pages_lock`, `map_4k::share_mapping_4k_spec`, `pagetable_concurrent::l2_page_map`, `kernel::memory_management::subsystem_mutation_pagetable_map`.
  - Dependencies are built unverified. All runs serialize on one flock, so expect queueing.
  - Do not run whole-package, workspace, NI-wide or monolith runs; the integration agent does those.
- Token economy: wait for your own run inside one blocking shell call (foreground with a timeout, or one polling loop). Do not hand back mid-wait. Grep logs (`error`, `rlimit`, `verified`) instead of reading them whole. Batch all edits before each run, and fix all errors together.
- Kill stray Verus processes only by exact name (`pkill -x rust_verify`, `pkill -x z3`); never use `pkill -f`. Run ad-hoc scripts under `timeout`.
- Frozen API (from B0, do not change): everything in `src/pagetable_concurrent/l2_page_map.rs`; the `PageTableLower` field list and inline accessors in `pagetable_concurrent_spec.rs`; `PageTableU.pagetable_window_locks`; the three `pagetable_window_locks_after_*` helpers; the `Share4k.directory` field. If one of them is wrong, report; do not edit.

## Report (hand back as your final message, ≤40 lines)
- Changed files (absolute paths).
- Every added or deleted lemma, closure, or spec, with file:line.
- Verification run numbers, each with verified/errors counts.
- Module rlimit before → after for every touched module (use the base numbers from the first run's log, or say "no base").
- Any deviation from this brief, any stop-and-report item, and any boundary the §D.4b table missed.
