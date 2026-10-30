# B3d — syscall_ipc

**Goal.** kernel_core and map_4k are green. Make crate `veriflat_syscall_ipc` verify with `pagetable_window_locks` in U and the new `Share4k.directory` field.

**Owned files** (edit only these): `src/kernel/implementation/syscall_ipc/*.rs` — in particular `syscall_ipc_spec.rs`, `syscall_ipc_trace.rs`, `syscall_ipc_pages_lock.rs`, `syscall_ipc_pages_check.rs`, `syscall_ipc_pages_prepare.rs`, `syscall_ipc_pages_share.rs`, `syscall_ipc_pages_fill.rs`, `syscall_ipc_pages_trace.rs`.

**What to change.**
1. `Share4k` literals and patterns gain `directory: Mmap4kDirectory::None`: syscall_ipc_spec.rs:514; syscall_ipc_pages_trace.rs:359/:543/:566/:631/:813; syscall_ipc_pages_share.rs:225/:408; syscall_ipc_pages_prepare.rs:57/:218/:366/:556/:716/:1076/:1196. Accessor uses (`->Share4k_*`) are unchanged.
2. Windows:
   - Source and target windows lock in `syscall_ipc_pages_lock.rs` :125/:126 (or :134/:135). The recorded step is `kernel_step_boundary_thread_syscall_progress_changed` at :1305 = `ipc_pages_lock_tables` (syscall_ipc_spec.rs:469). It gains `pagetable_window_locks_after_locking_range` on both tables (source with `source_range`, target with `target_range`).
   - Failure unlocks at :231/:342 → `check` failure step (:505) / `unlock_tables` (:586) gain `pagetable_window_locks_after_unlocking_range` on both. If an unlock lands in the same stretch as its lock, there is no clause.
   - `downgrade` (:555): unchanged.
   - The stutter at :749-:750 (`kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq` + `kernel_step_boundary_nonlock_fields_unchanged`) is valid only if all windows locked in that stretch were unlocked again before it. Check this. If not, delete or move it so the delta folds into the next recorded step (span rule). Never add a step.
   - syscall_ipc_pages_fill.rs:8 already says new L2 pages add windows to the held target map. That delta is in `Share4kDirectory` (map_4k); here only plumb perms.
3. `syscall_ipc_pages_check.rs` (8 old hits) and `syscall_ipc_pages_prepare.rs` (13): renames (`locked_windows` → `pagetable_window_locks`) and window-perm plumbing.
4. Update every `_from_u`/`_pre_from_k`/trace lemma touched and list them.
5. Cost watch: `ipc_pages_lock_tables_attempt` 14.1M and `ipc_pages_check_tables` 11.5M rlimit today. State window deltas only through locker ensures and trace lemmas, never inline in the exec equation. Report before/after rlimit for both.

**Must not change.** Other directories; exec order; frozen contracts.

**Runs.** `systemd-run --user --scope -p MemoryMax=30G ./verify-workspace.sh --package veriflat_syscall_ipc -- --verify-only-module syscall_ipc::syscall_ipc_spec --verify-only-module syscall_ipc::syscall_ipc_pages_lock ...` (all touched modules).

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

### D.4b U step span (user principle 2026-10-29)
**Principle.** "所有的 U 步都尽量跨度大一点。每个 syscall 的设计都是性能最优先，然后在不改 exec 代码的前提下 U 跨度尽可能大。runtime 性能是第一优先级."
- Exec code is fixed by runtime performance. Never reorder locks or add exec work for the U model.
- Given that exec code, U boundaries are as coarse as possible. Lock/unlock and ghost-only changes fold into the adjacent recorded step.
- A u_eq / `rebase_snapshot_k_if_unchanged` / `kernel_step_boundary_nonlock_fields_unchanged` stutter that becomes false under `pagetable_window_locks` is deleted or moved, so the stretch merges into the next recorded step. It is not turned into a new step.
- A new step is allowed only when an exec-forced boundary sits between a window lock and its unlock. An exec-forced boundary is one where 2PL forces a boundary because a lock is taken after an unlock.

**Stutter vs. recorded.**
- `kernel_step_boundary_nonlock_fields_unchanged` (kernel_step_wrappers/boundary_steps.rs:9) is a stutter: it records nothing and needs U equality with the snapshot.
- `drain_4k_cache_batch` (free_4k_page/drain_4k_cache_batch.rs:6) opens with `record_user_view_change(steps, snapshot_u, U(old krnl))` (kernel_total_define_spec.rs:15). Its per-page loop (:150 `wlock_page` / :152 `wunlock_page` / :163 boundary) is exec-forced: a page unlock is followed by the next page lock.

**D6 (mmap Fill) has no exec change.** In syscall_mmap_4k_fill_enter.rs, lines :128-:147 between `set_thread_syscall_progress` (:131, ghost-only) and the window lock (:148) are proof blocks only. The `kernel_step_boundary_thread_syscall_progress_changed` block (:134-:146) moves below :148, and the u_eq + `rebase_snapshot_k_if_unchanged` at :149 is deleted. The enter step then covers "progress set + existing range windows locked". No exec statement moves.

**Kill reclaim, analysed in full.** `kill_reclaim_unmapped_4k_page_scoped` (syscall_kill_process_reclaim_scoped.rs:146) runs on a `being_killed`, non-zombie (:30), hence U-visible table. It locks the window at :237.
- *Shared branch* (:258-:275): unlock at :262, then a stutter at :273-:274. Lock and unlock are net-zero, so the u_eq still holds and needs a `pagetable_window_locks` equality fact. **No new step.**
- *Last branch* (`kill_reclaim_last_4k_mapping_scoped`, syscall_kill_process_reclaim_scoped_last.rs:18), between lock (:237) and unlock (:163):
  - (1) stutter :129-:132. It is proof-only (state was Acquire and nothing is published), so delete it.
  - (2) `kill_retire_lock_cache` (syscall_kill_process_retire_pages.rs:638). It requires `steps.snapshot_k() == *old(krnl)` and ends with a stutter at :704-:707.
    - No-drain path (else :700-:702): proof-only, deletable.
    - Drain path (:672-:697): `drain_4k_cache_batch` → its exec-forced per-page boundaries. The pool unlock (:696) before the next lock (`wlock_allocator_quota_4k`, _last.rs:151) is also exec-forced.
  - (3) The recorded credit step at :166-:171 (`kernel_page_freed_to_owner_quota_implies_u_step` + `kernel_step_boundary_user_view_changed`, label `KillProcessRefund`).
  - **Result:** on the no-drain path the lock and unlock fold net-zero into the credit step, which then needs no window clause. On the drain path, drain's opening `record_user_view_change` records `{pre, window locked}`. That step is `KillProcessPagetableWindowsChanged`, and the credit step absorbs the unlock (D9). So `KillProcessWindowLocked` cannot be dropped; it shrinks to the drain path.
  - Contract edits (proof-only, no exec change): delete the :129-:132 stutter. `kill_retire_lock_cache` drops `snapshot_k() == *old(krnl)` in favour of the stutter-precondition set (as `drain_4k_cache_batch` :17-:28 states it) and ensures `steps.view() == record_user_view_change(old.view, old.snapshot_u, U(old krnl))` on the drain path, otherwise unchanged. Its 6 callers must keep proving that: kill_container_retire_root.rs:216, _last.rs:138/:297, retire_pages_scoped.rs:144, retire.rs:273, retire_pages.rs:492. The zombie-table callers see no window change.
- **New finding, same shape:** `reclaim_unmapped_4k_page` (map_4k/unmap_4k_reclaim_one.rs:10, window lock :89, unlock :91) → `reclaim_last_4k_mapping` (unmap_4k_reclaim_last.rs:102: stutter :221-:222, deletable) → `reclaim_last_lock_4k_cache_with_room` (unmap_4k_reclaim_last_cache.rs:7: drain :70, exec-forced pool-unlock boundary :73-:74). It is called from:
  - **thread_exit** `thread_exit_reclaim_unmap_leaves` (syscall_thread_exit_reclaim_release.rs:534; process `!zombie` :300, so visible) → needs `ThreadExitPagetableWindowsChanged` on the drain path, and `ThreadExitRefund` (:553) absorbs the unlock. (Step, label and refund step user-approved.)
  - **kill** `kill_reclaim_unmap_leaves` (syscall_kill_process_reclaim_release.rs:638; target being_killed, visible) → `KillProcessPagetableWindowsChanged` again; refund at :660.
  - These loops run once per page. A drain step in iteration k can carry "window k−1 unlocked + window k locked", hence the ≤2-change shape in §D.4.
- **Zombie retire u_eq sites** (syscall_kill_process_retire_pages.rs:479, syscall_kill_process_retire_pages_scoped.rs:131): the table is hidden, so swap to `kernel_lock_states_unchanged_except_tables_of_implies_u_eq(.., Some(target))`. No step.
- `clear_4k_mapping_present` (unmap_4k_present.rs:68 lock … :89 unlock): no boundary in between, so net-zero folds into the caller's recorded leaf step (thread_exit_reclaim_leaf.rs:95, kill reclaim_release.rs:161). No step.

**Boundaries kept, per syscall** (each one exists because of an exec event; a window delta folds into it):

| syscall | recorded boundaries that carry a window delta | why they cannot be removed |
|---|---|---|
| mmap_4k | enter (Read :286 / Fill moved below :148), directory/leaf steps (unchanged windows), exit (map_range.rs:368) | enter/exit are big-lock acquire/release points; directory steps are page-allocation steps |
| map_4k share | `Share4kDirectory` (adds keys exactly), `Share4kLeaf` | per-page allocation and per-leaf boundaries already exist in exec |
| unmap_4k | enter (syscall_unmap_4k_pagetable.rs:175 lock; next recorded boundary), exit (:316-:323) | big-lock rlock/runlock |
| iommu_map_4k | enter (check.rs:372), exit / failure (:409, exit.rs:121) | same |
| ipc | `lock_tables` (pages_lock.rs:125-:135, recorded at :1305), failure stutter :749-:750 (B3d confirms the windows are unlocked again at :231/:342 before it; otherwise it moves or is deleted per the rule), `unlock_tables` | rendezvous lock retry loop |
| new_process / new_container | enter: new_process lock_helpers.rs:585 (held on precheck success; the :589 unlock on failure is net-zero inside the failure stretch), new_container lock_owners.rs:337; finish: finish_release.rs:156/:158, share_helpers.rs:466/:468, release_source.rs:77 (unlocks fold into the finish/release step) | big-lock and owner-lock acquire/release |
| kill_process | `KillProcessPagetableWindowsChanged` (drain path only), `KillProcessRefund` (absorbs unlock); zombie retire invisible | drain per-page lock/unlock (drain_4k_cache_batch.rs:150-:163) |
| thread_exit | `ThreadExitPagetableWindowsChanged` (drain path only), `ThreadExitRefund` | same drain loop |

Rule for every implementing agent: list every boundary call between each window lock and its unlock. Delete or move stutters. Fold the delta into the next recorded step. If a recorded or exec-forced boundary appears that this table does not list, stop and report before adding a step.

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
