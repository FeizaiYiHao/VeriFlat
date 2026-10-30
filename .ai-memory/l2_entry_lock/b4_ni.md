# B4 — noninterference

**Goal.** All kernel crates are green. Make the noninterference workspace verify for the new U field `PageTableU.pagetable_window_locks`, the `Share4k.directory` field, and the new kill and thread_exit steps. Relaxed NI proof rules apply: `assert(forall ..)` is allowed in this crate.

**Owned files** (edit only these): `noninterference/src/*.rs`.

**What to change.**
1. `theorem.rs`:
   - `StepLabel` (:23-:55): add `KillProcessPagetableWindowsChanged` and `ThreadExitPagetableWindowsChanged`.
   - Label → spec map (:154-:193): `KillProcessPagetableWindowsChanged => kill_process_step_pre(old_u, cpu_id) && kill_process_pagetable_windows_changed_step(old_u, new_u, cpu_id)`; `KillProcessRefund` (:172) → `kill_process_step_pre(..) && kill_process_refund_step(old_u, new_u, cpu_id)`; `ThreadExitRefund` (:193) → `thread_exit_refund_step`; `ThreadExitPagetableWindowsChanged => thread_exit_reclaim_step_pre(old_u, cpu_id, false) && thread_exit_pagetable_windows_changed_step(old_u, new_u, cpu_id)`.
   - Dispatch (:331, :382+, :400, :420): call the new `_lr`/`_iso`.
2. `ni_kill_process.rs`:
   - new `kill_process_pagetable_windows_changed_step_lr` / `_iso`. The changed table belongs to the target, which is in the killer's domain (same argument as `kill_process_leaf_step_lr` :670 / `_iso` :692).
   - patch `kill_process_refund_step_lr` (:789) / `_iso` (:810) for the optional unlock.
3. `ni_thread_exit.rs`: new `thread_exit_pagetable_windows_changed_step_lr`/`_iso`, and patch the refund `_lr` (:393) / `_iso` (:403).
4. `ni_share_4k.rs`: `share_4k_directory_step_lr` (:8) / `_iso` (:19) over the exact step (new progress `directory`, target-table `pagetable_window_locks_after_new_l2_page`). The target belongs to the share's domain as in the existing proof.
5. All other `_lr`/`_iso` whose steps changed `pagetable_window_locks` (ni_mmap_4k, ni_unmap_4k, ni_iommu_map_4k, ni_ipc `lock_tables` ~:317/:328, ni_new_process, ni_new_container, ni_kill_container): re-prove.
   - `domain_view` (domain.rs:26) copies `ProcessU`, so `pagetable_window_locks` is part of the view with no edit.
   - Every window change is on the caller's own table (ipc: source + target). The ipc peer-table argument is the same as for the big-lock mode (`isolated`/`endpoint_iso` exclude peer ∈ b).

**Must not change.** Kernel `src/` (report spec problems instead).

**Runs.** `cd noninterference && systemd-run --user --scope -p MemoryMax=30G ./verify-ni.sh --verify-only-module ni_kill_process --verify-only-module ni_share_4k ...` (all touched modules). If module filtering is rejected, report and ask the coordinator before running the whole NI workspace (it counts as heavy).

## Copied design text (authoritative for this batch)

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

### D.4a `Share4k` directory level (D8, user decision)
- `proc/thread_def.rs:83`: `Share4k { source_range, target_range, shared, origin }` → `Share4k { source_range: VaRange4K, target_range: VaRange4K, shared: usize, directory: Mmap4kDirectory, origin: Share4kOrigin }`. This mirrors `IommuMap4k { .., directory: Mmap4kDirectory }` (:77) and `Mmap4k` (:73).
- New `share_4k_progress_after_directory(progress, level)` in map_4k/share_mapping_4k_spec.rs. It is the twin of `mmap_4k_progress_after_directory` (mmap_4k_build_structure_spec.rs:28-:33) and sets `directory: mmap_4k_installed_directory(level)`. `share_4k_progress_after_leaf` (:6-:11) resets `directory: Mmap4kDirectory::None`.
- `share_4k_directory_at` (:26) / `share_4k_directory_step` (:112):
  - the progress thread's `syscall_progress` becomes `share_4k_progress_after_directory`;
  - add the rank clause `mmap_4k_directory_rank(old.directory) < mmap_4k_directory_rank(new.directory)`;
  - add the target-table window clause from §D.4. The `post == KernelU { thread_map: .., container_map: .., ..pre }` form gains `process_map: pre.process_map.insert(target, ProcessU { pagetable: Some(PageTableU { pagetable_window_locks: <clause>, ..t }), ..})`.
- Exec: `install_one_mmap_4k_directory_page` (mmap_4k_install_one.rs:132 says the progress thread's progress is unchanged in the Share4k case) gains one ghost-only `set_thread_syscall_progress(progress_thread, Ghost(share_4k_progress_after_directory(..)))` under the held progress-thread write lock. It has no runtime cost (the argument is `Ghost`).
- Every exhaustive `Share4k { … }` literal or pattern gets `directory: Mmap4kDirectory::None`. Accessor uses (`->Share4k_*`) and `{ .. }` patterns are unchanged.
  - **B0:** proc/thread_def.rs:83.
  - **B3b (map_4k):** share_mapping_4k_spec.rs:8 (+ new fn, :26, :112); share_mapping_4k_trace.rs (directory trace lemma); share_mapping_4k.rs:874/:1006/:1149; share_mapping_4k_child_structure.rs:101/:341/:571; mmap_4k_install_one.rs:132 (+ :329-:355 Share4k branch).
  - **B3d (ipc):** syscall_ipc_spec.rs:514; syscall_ipc_pages_trace.rs:359/:543/:566/:631/:813; syscall_ipc_pages_share.rs:225/:408; syscall_ipc_pages_prepare.rs:57/:218/:366/:556/:716/:1076/:1196.
  - **B3e (new_process):** syscall_new_process_spec.rs:134; syscall_new_process_trace.rs:199/:256; syscall_new_process_publish_step.rs:122/:139; syscall_new_process_publish.rs:165; syscall_new_process_with_iommu_publish.rs:181; syscall_new_process_helpers/finish.rs:80/:281; syscall_new_process_share_finish.rs:112.
  - **B3e (new_container):** syscall_new_container_spec.rs:166; syscall_new_container_trace.rs:138/:176; syscall_new_container_publish.rs:157/:259/:384; syscall_new_container_commit.rs:455/:772/:889; syscall_new_container_commit_share.rs:131; syscall_new_container_share.rs:258/:369/:521/:774/:934.
  - **B4 (NI):** ni_share_4k.rs:8/:19 (`share_4k_directory_step_lr/_iso`); theorem.rs:118/:331 keep the label.
  - Sites that read no `directory` and use `{ .. }` or accessors need no edit: projection_at.rs:406, kernel_u_steps.rs:665-:709, kernel_step_spec.rs:812-:825, syscall_ipc_pages_fill.rs:32-:36, mmap_4k_build_structure.rs:93/:391/:688, ni_share_4k.rs:53-:65, theorem.rs:245.

### D.6 NI
- `KillProcessPagetableWindowsChanged` and `ThreadExitPagetableWindowsChanged` get `_lr`/`_iso`. The changed table belongs to the caller's domain (kill: the target is in the killer's subtree; thread_exit: own process).
- `Share4kDirectory` `_lr`/`_iso` (ni_share_4k.rs:8/:19) are re-proved over the new `directory` field and the target-table window clause.
- `pagetable_window_locks` is a field of `ProcessU.pagetable` and is copied through `domain_view`. Steps change it only on the caller's own table (ipc: source + target). The ipc peer-table argument is identical to the big-lock mode argument (`isolated`/`endpoint_iso` exclude peer ∈ b).
- `refund` `_lr`/`_iso` (ni_kill_process.rs :789/:810; ni_thread_exit.rs :393/:403) are patched for the optional unlock.

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
