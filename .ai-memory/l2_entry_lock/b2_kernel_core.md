# B2 — kernel_core: lockers, wrappers, U-equality lemmas, invariants, boot

**Goal.** B0 has frozen the API and `veriflat_kernel_core` typechecks. Make the rest of kernel_core verify. B1 runs in parallel on `src/pagetable_concurrent/*`.

**Owned files** (edit only these; all under `src/kernel/`):
- `memory_management/pagetable_map_spec.rs`, `memory_management/subsystem_mutation_pagetable_map.rs`, `memory_management/subsystem_mutation_eof.rs`
- `implementation/locker_unlocker/{locker_unlocker_pagetable,locker_unlocker_pagetable_eof,locker_unlocker_pagetable_window,locker_unlocker_pagetable_range_windows}.rs`
- `kernel_u_define_spec.rs`, `kernel_step_spec/kernel_u_steps.rs`
- `kernel_step_wrappers.rs`, `kernel_step_wrappers/*.rs`
- `init.rs`

**What to change.**
1. KernelK invariants in `memory_management/pagetable_map_spec.rs`: re-prove with the entry owner in place of `l2_lock`.
   - `pagetable_hidden_leaves_only_when_locked` :16
   - `pagetable_window_stale_cpus_only_when_locked` :33 (`l2_lock.dom()` → `l2_perms@.dom()`; `.locked(i)` → `l2_owner(p, i) is Some`)
   - `pagetable_lower_wf` :59
   - `pagetable_window_holders_hold_pagetable` :80
   - `pagetable_lower_backup_wf` :101
   - `pagetable_window_typed_lock_map_aligned` :117 (owner from the entry)
2. Window lockers. These ensures are the contracts every syscall batch relies on; state them exactly.
   - `lock_pagetable_window` (locker_unlocker_pagetable_window.rs:11): `pagetable_c(post..).lower.pagetable_window_locks@ == pagetable_c(pre..).lower.pagetable_window_locks@.insert(w, LockStateU::WriteLocked)`. Every other table's `pagetable_window_locks` is unchanged. Keep `lock_perm_match`, `typed_lock_maps_inserted`, and the backup sync via `update_ghost`. The framing list drops `l2_ghost`/`l1_tables` in favour of "`l2_perms` equal except entry (p, i)".
   - `unlock_pagetable_window` (:134): `.insert(w, LockStateU::Unlocked)`.
   - `lock_pagetable_range_windows` (range_windows.rs:24) and `lock_pagetable_range_existing_windows` (:470): `pagetable_window_locks@ == pagetable_window_locks_after_locking_range(old.pagetable_window_locks@, *range)`.
   - `unlock_pagetable_range_windows` (:263) and `unlock_pagetable_range_existing_windows` (:723): `pagetable_window_locks_after_unlocking_range`.
   - The loops (:232 :442 :693 :919) carry `pagetable_window_locks@ == pagetable_window_locks_after_locking_range(old, <prefix range>)` (or the unlocking twin). Add an EOL loop summary if a loop exceeds 5 s SMT.
3. Wrappers in `memory_management/subsystem_mutation_pagetable_map.rs` (:9 :86 :174 :259 :355 :448 :583 :663 :742 :809 :878):
   - every `lower.l2_lock ==` ensures becomes `lower.pagetable_window_locks ==`;
   - `pagetable_map_create_entry_l3` (:448) ensures `pagetable_window_locks@ == pagetable_window_locks_after_new_l2_page(old, indices.0, indices.1, <locked range>)`;
   - `pagetable_map_remove_table_page` (:878) ensures `pagetable_window_locks@` minus the 512 keys of the removed L2 page.
   - Restate the lemma at :948 and rename `pagetable_l2_windows_unlocked_when_wlocker_holds_no_windows` → `wlocker_holds_no_windows_implies_l2_windows_unlocked` (update its callers inside owned files; report callers outside).
   - `subsystem_mutation_eof.rs` :19/:217/:278/:481/:776: `l2_lock` clauses → `pagetable_window_locks` / `l2_owner`.
4. U-equality lemmas: apply the copied §E.3 to the 9 lemmas (kernel_step_wrappers/projection.rs :8 :29 :98 :224 :617; bindings.rs :32; release.rs :6; kernel_step_wrappers.rs :158 :265 :387). Other wrapper files (per_map_projection.rs, owner_and_tables_per_map_projection.rs, pagetable_read_mode.rs, new_process_read_mode.rs, projection_ipc.rs, ipc_pages_tables.rs, kill_reclaim.rs, iommu_table_steps.rs, boundary.rs, end_kernel_step_quota_cpu.rs) get the same per-table `pagetable_window_locks` equality premise or conclusion wherever they derive `pagetable_map_user_view` equality. Touch them only where verification fails.
5. Wrapper-layer K→U facts for the new U field: where a wrapper ensures a U fact about a pagetable delta, state the `pagetable_window_locks` part. These are wrapper K→U lemmas, so no approval is needed; list them.
6. `init.rs`:
   - `boot_dom0_pagetable_model` :92-:96: move each boot L1 perm into `ar[i].l1` with a verified nested loop (exec `decreases`; bound 512 × #L2 pages).
   - :276/:288/:640: `locked_windows == empty` → `pagetable_window_locks@` = all windows of the boot L2 pages, `Unlocked`.
   - :872-:953: the same for the cpu tables.

**Must not change.** Any file outside the owned list (pagetable_concurrent belongs to B1). Frozen B0 API. No new framing specs/lemmas or invariants: stop and report.

**Runs.** Batch the modules you touched into one command:
`systemd-run --user --scope -p MemoryMax=30G ./verify-workspace.sh --package veriflat_kernel_core -- --verify-only-module kernel::memory_management::pagetable_map_spec --verify-only-module kernel::memory_management::subsystem_mutation_pagetable_map --verify-only-module kernel::implementation::locker_unlocker::locker_unlocker_pagetable_window ...`
Module names are rooted at the crate root (`kernel::…`). If one is rejected, check `src/kernel/implementation/locker_unlocker/mod.rs` for the exact path.

## Copied design text (authoritative for this batch)

### C.2 crate `veriflat_kernel_core` — other modules (B2)
- `memory_management/pagetable_map_spec.rs`:
  - `pagetable_hidden_leaves_only_when_locked` :16.
  - `pagetable_window_stale_cpus_only_when_locked` :33: `l2_lock.dom()`/`l2_lock_of(p).locked(i)` → `l2_perms@.dom()`/`l2_owner(p,i) is Some`.
  - `pagetable_lower_wf` :59.
  - `pagetable_window_holders_hold_pagetable` :80.
  - `pagetable_lower_backup_wf` :101. The backup `view_ghost()` is a `PageTableLower`, so it carries the new fields automatically.
  - `pagetable_window_typed_lock_map_aligned` :117: owner from the entry, not `l2_lock`.
- `locker_unlocker/locker_unlocker_pagetable_window.rs` :11/:134: ensures frame list `l2_ghost`/`l1_tables` → `l2_perms`-except-entry (reuse the S clauses of B.3 through `lock_window`'s ensures), plus `pagetable_window_locks` insert.
- `locker_unlocker/locker_unlocker_pagetable_range_windows.rs`:
  - `lock_pagetable_range_windows` :24 (loop :232), `unlock` :263 (:442), `_existing` :470 (:693), `unlock_existing` :723 (:919).
  - Each loop invariant gains `pagetable_window_locks@ == pagetable_window_locks_after_locking_range(old, prefix_k)` (or `_after_unlocking_range`).
  - EOL loop summary `[X]` if the loops exceed 5 s.
  - `pagetable_l3_entry_links_l2` :946.
- `kernel_step_wrappers/subsystem_mutation_pagetable_map.rs`:
  - The 11 KernelK wrappers (:9 :86 :174 :259 :355 :448 :583 :663 :742 :809 :878). Each loses its `lower.l2_lock ==` ensures; the 9 window-writing ones gain `Tracked<&LockPerm>`.
  - `remove_table_page` :878 uses `pagetable_l2_windows_unlocked_when_wlocker_holds_no_windows` (:948); its body changes from `l2_lock` to `l2_owner`. It is an existing lemma, restated, not new.
- `kernel_step_wrappers/` U-eq lemmas (9 sites, §E.3).
- `kernel/kernel_u_define_spec.rs` :5/:9 projection (§D.2); `kernel_u_steps.rs` :587/:650 literals.
- `pagetable_seq/pagetable_spec.rs` :59 `PageTableU` field (§D.1).
- `kernel/init.rs`:
  - `boot_dom0_pagetable_model` :92-:96: `l1_tables` → placed into entries.
  - :276/:288 ensures `locked_windows == empty` → `pagetable_window_locks@ == all-unlocked over boot L2 windows`.
  - :640, :872-:953 (cpu tables).
  - The boot builder needs a verified loop that moves `l1_tables[l1]` into `ar[i].l1`. It has an exec `decreases` and is bounded by 512 × (#L2 pages).
- `kernel/cpu_tlb_management/tlb_wf_spec.rs` :72/:80: `window_l2_page` is unchanged; no edit beyond the re-proof.
- `pagetable_seq/pagetable_window_stale_eof.rs`: `l2_lock` → `l2_owner` reads.
- `kernel/projection*.rs` literals: projection.rs :919/:934, projection_publish.rs :98/:269 → `pagetable_window_locks: Map::empty()`.

### D.4 Step table
Three spec helpers live in `pagetable_seq/pagetable_spec.rs`. They are shared by the K lockers and the U steps. **D7 (user-approved): use exactly these three names.**
```
pub open spec fn pagetable_window_locks_after_locking_range(m: Map<WindowVa, LockStateU>, range: VaRange4K) -> Map<WindowVa, LockStateU> {
    Map::new(|w: WindowVa| m.dom().contains(w), |w: WindowVa| if va_range_2m_windows(range).contains(w) { LockStateU::WriteLocked } else { m[w] })
}
pub open spec fn pagetable_window_locks_after_unlocking_range(m: Map<WindowVa, LockStateU>, range: VaRange4K) -> Map<WindowVa, LockStateU> {
    Map::new(|w: WindowVa| m.dom().contains(w), |w: WindowVa| if va_range_2m_windows(range).contains(w) { LockStateU::Unlocked } else { m[w] })
}
pub open spec fn pagetable_window_locks_after_new_l2_page(m: Map<WindowVa, LockStateU>, l4i: L4Index, l3i: L3Index, locked_range: VaRange4K) -> Map<WindowVa, LockStateU> {
    Map::new(|w: WindowVa| m.dom().contains(w) || (w.wf() && spec_v2l4index(w.va) == l4i && spec_v2l3index(w.va) == l3i),
        |w: WindowVa| if m.dom().contains(w) { m[w] } else if va_range_2m_windows(locked_range).contains(w) { LockStateU::WriteLocked } else { LockStateU::Unlocked })
}
```
`locked_range` must give the same window set as the `lo..=hi` that `install_one_mmap_4k_directory_page` passes to `pagetable_map_create_entry_l3` (mmap_4k_install_one.rs:175-:184, mmap_4k_create_entry_install.rs:259). B3b confirms this from live code and reports any mismatch before changing a spec.

| syscall / step (file:line) | pagetable_window_locks clause on the caller's table `t` |
|---|---|
| mmap `enter_step` Read (mmap spec :94) | `pagetable_window_locks_after_locking_range(old, range)` |
| mmap `enter_step` Fill (:94) | `pagetable_window_locks_after_locking_range(old, range)` (existing windows only; the enter boundary moves below the lock, D6) |
| mmap `hold`/`release`/`downgrade`/`leaf` (:136/:161/:185/:216) | unchanged (folded into the existing frame clause) |
| mmap `exit_step` (:257) | `pagetable_window_locks_after_unlocking_range(old, range)` |
| map_4k `mmap_4k_directory_step` (build_structure_spec :78) | **exact**: `new_progress.directory is L3 ⇒ pagetable_window_locks_after_new_l2_page(old, v2l4(range[mapped]), v2l3(range[mapped]), range)`, else unchanged. `MissingPageTableLevel::L3` is the only level that calls `pagetable_map_create_entry_l3` (mmap_4k_create_entry_install.rs:78/:259); L4 (new L3 page) and L2 (new L1 page) add no keys; the level is already recorded (:88-:89) |
| share `share_4k_directory_step` (share spec :112) | **exact** (D8, user decision): `Share4k` progress gains `directory: Mmap4kDirectory` (§D.4a). `new_progress.directory is L3 ⇒ pagetable_window_locks_after_new_l2_page(old, v2l4(target_range[shared]), v2l3(target_range[shared]), target_range)` on the target table; L4/L2 ⇒ unchanged. The rank must rise: `mmap_4k_directory_rank(progress.directory) < mmap_4k_directory_rank(new_progress.directory)`, mirroring build_structure_spec.rs:89 |
| unmap enter/exit (:63/:96) | `pagetable_window_locks_after_locking_range` / `pagetable_window_locks_after_unlocking_range` |
| iommu_map enter/exit (:91/:190) | same, on the process pagetable side |
| ipc `lock_tables` (:469) | source and target tables `pagetable_window_locks_after_locking_range` |
| ipc `check` failure (:505) / `unlock_tables` (:586) | `pagetable_window_locks_after_unlocking_range` on both |
| ipc `downgrade` (:555) | unchanged |
| new_process enter (:79) / finish (:205) | source `pagetable_window_locks_after_locking_range` / `pagetable_window_locks_after_unlocking_range`; child table: windows created at publish (:122) via the share step, all Unlocked at finish |
| new_container enter (:102) / finish (:219) | as for new_process |
| **kill `KillProcessPagetableWindowsChanged` (new; drain path only, §D.4b)** | target `t` only: dom unchanged; `changed = dom.filter(|w| new[w] != old[w])`, `changed.len() <= 2`, at most one changed key goes `Unlocked → WriteLocked` and at most one goes `WriteLocked → Unlocked` (filter-len pattern of `kill_process_leaf_step` :354); everything else in `KernelU` unchanged |
| kill `refund` (new kill-local `kill_process_refund_step`, D9) | optional single-window `WriteLocked → Unlocked` on `t` + `kernel_u_container_quota_4k_increased(KernelU { process_map: new.process_map, ..old }, new, owner)` |
| **thread_exit `ThreadExitPagetableWindowsChanged` (new; drain path only, §D.4b; user-approved)** | same shape as `KillProcessPagetableWindowsChanged`, on the exiting process's table |
| thread_exit `refund` (new local `thread_exit_refund_step`; user-approved) | optional single-window unlock + `kernel_u_container_quota_4k_increased(..)` as today (theorem.rs:193) |
| kill retire on zombie tables | invisible (process projection hides the table) |

Share directory step: exact through the new `Share4k.directory` field (§D.4a).

**L2 removal.** The only producer is `l2_page_map_to_page_perm` (l2_page_map.rs:301). Its call chain is:
`remove_l3_entry` (pagetable_concurrent_impl_remove_base.rs:241) ← `remove_structure_page` L2 branch (structure_scan.rs:175) ← `pagetable_map_remove_table_page` (subsystem_mutation_pagetable_map.rs:954; the IOMMU twin at subsystem_mutation_iommu_table.rs:449 is seq). That wrapper has exactly 2 callers, both in kill_process (also run by kill_container):
- `kill_retire_table_page_to_cache` (syscall_kill_process_retire_pages.rs:714, call :834). Its only caller is :616, in `kill_retire_table_page_and_unlock` (:510), which requires `prc_mp[target].view().zombie` (:562).
- `kill_retire_table_page_scoped_to_cache` (retire_pages_scoped.rs:293, call :400). Its only caller is :273, in `kill_retire_table_page_scoped_and_unlock` (:178). That function's only caller is :163, in `kill_retire_next_table_page_scoped` (:19), which requires zombie (:50). That one is reached from retire_pages.rs:353, inside `kill_retire_table_pages` (:152), which requires zombie (:174).

In both chains the table belongs to a zombie target, and the projection (kernel_u_define_spec.rs:87) sets `pagetable: None` for zombies. **No visible step deletes window keys.** `unmap_4k`, `thread_exit`, `iommu_unmap` and every other syscall have no call to `pagetable_map_remove_table_page` or `remove_structure_page` (grep), so they never free an L2 page and need no remove clause. By contrast, the kill reclaim window lock (reclaim_scoped.rs:146) runs on a target that is `being_killed`, not zombie (:30), so it stays visible and needs `KillProcessPagetableWindowsChanged` on its drain path (§D.4b). L2 creation: the mmap directory, share directory and new_process/new_container publish steps add 512 keys, stated exactly through `add_l2_page`.

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

### E.3 U-equality lemmas (9; premise inlined, no new lemma)
In each per-table lock-mode forall, add:
`pagetable_c(post.pt_mp, post.pt_lower.view(), p).lower.pagetable_window_locks == pagetable_c(pre.pt_mp, pre.pt_lower.view(), p).lower.pagetable_window_locks`
For the `match table` / `Some(p)` variants, add the same for `p`.
- projection.rs: `kernel_thread_write_held_section_implies_u_eq` :8 (`..*pre` shape, nothing to add); `kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq` :29 (~:52); `kernel_lock_states_unchanged_except_tables_of_implies_u_eq` :98 (~:142, zombie excluded); `..._u_process_map` :224; `kernel_restored_locks_implies_u_eq` :617 (~:661).
- bindings.rs: `kernel_snapshot_nonlock_fields_and_lock_states_unchanged_implies_u_eq` :32.
- release.rs: `kernel_page_then_pcid_allocator_unlocks_implies_u_eq` :6 (post == `KernelK{pg_arr, pcid_allc_mp, ..*pre}`, nothing to add).
- kernel_step_wrappers.rs: `end_kernel_step_restored_locks` :158, `_with_iommu_table` :265, `end_kernel_step_unchanged` :387.

Callers that drop and re-take window locks inside one step (kill reclaim_scoped :262 shared branch; unmap reclaim_one :89/:91) must supply equal `pagetable_window_locks`. The lock/unlock pair inside one stretch restores the map; this needs a `insert(w, W).insert(w, U) == insert(w, U)` + `old[w]==U` fact, discharged by `=~=`.

---

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
