# Window locks in U — design proposal (read-only survey of HEAD f6930d5)

Assumes the nonlock layer (`kernel_k_to_nonlock_kernel_u`, `nonlock_view`, `nonlock_snapshot_u`, `kernel_u_nonlock_fields`,
`nonlock_step`) is already gone. "Step" below = one `KernelStep` recorded at a boundary (`record_user_view_change`,
src/kernel/kernel_total_define_spec.rs:23). Lock operations are never steps by themselves today: `rlock_pagetable` etc. run
inside an Acquire stretch and the change shows in the step recorded at the next boundary (e.g. `mmap_4k_enter_step`
= cpu/thread wlock + table rlock + progress). A lock and an unlock inside one stretch are invisible. This proposal keeps
that convention for windows (Q1).

## 1. Inventory

### 1a. K primitives that change `PageTableLower.locked_windows` (pagetable_concurrent_spec.rs:36)
| primitive | file:line | change |
|---|---|---|
| `PageTableHigher::lock_window` / `unlock_window` | pagetable_concurrent/pagetable_concurrent_lock.rs:10 / :53 (insert :46, remove :83) | +w / −w |
| `PageTableHigher::create_entry_l3` (mints windows lo..=hi of a new L2 page, held by builder) | pagetable_concurrent/pagetable_concurrent_impl_base.rs:66 (union :158) | +{lo..hi} |
| `KernelK::lock_pagetable_window` / `unlock_pagetable_window` | locker_unlocker/locker_unlocker_pagetable_window.rs:11 / :134 | wraps above |
| `lock_pagetable_range_windows` / `unlock_pagetable_range_windows` | locker_unlocker_pagetable_range_windows.rs:22 / :261 (loops call :232 / :440) | all range windows |
| `lock_pagetable_range_existing_windows` / `unlock_..._existing_windows` | same file :468 / :721 (loops :691 / :917) | range windows whose L2 page exists |
| `pagetable_map_create_entry_l3` | memory_management/subsystem_mutation_pagetable_map.rs:448 (call :561) | ← `install_staged_4k_page_table_page` map_4k/mmap_4k_create_entry_install.rs:24 (:259) ← `install_one_mmap_4k_directory_page` map_4k/mmap_4k_install_one.rs:17 |
Every other lower-half primitive already ensures `final(lower).locked_windows == old(lower).locked_windows`
(impl_map.rs:47/:101, impl_remove_base.rs:35/:91/:142/:217, impl_base.rs:215, structure_scan.rs:156). IOMMU tables
(`pagetable_seq`, `subsystem_mutation_iommu_table.rs:333`) have no windows. None of the KernelK lockers currently
ensures anything about `locked_windows` (they ensure lctx/`window_locked_by_thread` facts only).

### 1b. Call sites → syscall, classified
F = folds into a step that is recorded anyway (its step spec becomes incomplete); Z = lock+unlock in one stretch, or table
of a zombie (`ProcessU.pagetable = None`, kernel_u_define_spec.rs:130) → projection unchanged, nothing new;
N = window state differs at a boundary that today asserts U unchanged → NEW step unless restructured.

| syscall | site | class |
|---|---|---|
| mmap read | `lock_pagetable_range_windows` syscall_mmap_4k_read_enter.rs:273 → enter step boundary :291 | F `mmap_4k_enter_step` (Read) |
| mmap read rejected | unlock :278 same stretch | Z |
| mmap fill | `lock_pagetable_range_existing_windows` syscall_mmap_4k_fill_enter.rs:151, then `implies_u_eq` + `rebase_snapshot_k_if_unchanged` :152 | F → first `mmap_4k_directory_step` or `mmap_4k_downgrade_step` (:167); the :152 u_eq/rebase must go |
| mmap fill minting | `install_one_mmap_4k_directory_page` from syscall_mmap_4k_fill_structure.rs:183/:197, syscall_mmap_4k_map_one_leaf.rs:150, map_4k/mmap_4k_build_structure.rs:577/:880/:897; boundary mmap_4k_install_one.rs:798 | F `mmap_4k_directory_step` (map_4k/mmap_4k_build_structure_spec.rs:78) |
| mmap exit | `unlock_pagetable_range_windows` syscall_mmap_4k_map_range.rs:364, boundary :372 | F `mmap_4k_exit_step` |
| unmap | `lock_..._existing_windows` syscall_unmap_4k_pagetable.rs:178 → enter boundary syscall_unmap_4k_helpers.rs:192 | F `unmap_4k_enter_step` |
| unmap rejected | unlock syscall_unmap_4k_pagetable.rs:184 | Z |
| unmap exit | unlock syscall_unmap_4k_helpers.rs:208, boundary :218 | F `unmap_4k_exit_step` |
| unmap leaves | `clear_4k_mapping_present_in_window` / `reclaim_unmapped_4k_page_in_window` (unmap_4k_range.rs:279/:535) | windows held, unchanged |
| iommu_map_4k | lock syscall_iommu_map_4k_check.rs:376 → enter boundary syscall_iommu_map_4k.rs:60; reject unlock check.rs:413 (Z); exit unlock syscall_iommu_map_4k_exit.rs:121, boundary :132 | F enter / F exit |
| ipc pages | `ipc_pages_lock_pair_windows` syscall_ipc_pages_lock.rs:9 (:125/:126/:134/:135) inside `ipc_pages_lock_tables_and_windows` :431 → boundary :1308 | F `ipc_pages_lock_tables_step` |
| ipc pages retry | `ipc_pages_unlock_tables_and_windows` :594 (unlock :726, u_eq :750) | Z (stutter) |
| ipc pages fill | `mmap_4k_build_one_structure` syscall_ipc_pages_fill.rs:215 | F `share_4k_directory_step` (map_4k/share_mapping_4k_spec.rs:112) |
| ipc pages release | `ipc_pages_unlock_pair_windows` :1459 in `ipc_pages_release_tables_and_progress` :1321, boundary :1474; `ipc_pages_unlock_windows_keeping` :146/:338 | F `ipc_pages_unlock_tables_step` / failed `ipc_pages_check_step` (syscall_ipc_spec.rs:586/:505) |
| new_process | `new_process_lock_source_windows` syscall_new_process_lock_helpers.rs:518 (lock :591; reject unlock :595 Z) ← syscall_new_process_common.rs:259 → enter boundary syscall_new_process_enter.rs:112 | F `new_process_enter_step` |
| new_process child | `build_new_child_structure` map_4k/share_mapping_4k_child_structure.rs:285 (mints, :269) | F `share_4k_directory_step` |
| new_process finish | unlocks finish_release.rs:156/:158 → boundary finish.rs:336 | F `new_process_finish_step` |
| new_container | `new_container_lock_source_windows` syscall_new_container_lock_owners.rs:268 (:340) ← syscall_new_container.rs:652 → enter boundary syscall_new_container_enter.rs:174; reject `new_container_release_source_table` release_source.rs:77 (Z, :173 end_kernel_step_unchanged) | F `new_container_enter_step` |
| new_container finish | unlocks syscall_new_container_share_helpers.rs:466/:468 → boundary syscall_new_container_share.rs:980 | F `new_container_finish_step` |
| thread_exit | `clear_4k_mapping_present` (map_4k/unmap_4k_present.rs:68/:89) from syscall_thread_exit_reclaim_leaf.rs:95; `reclaim_unmapped_4k_page` (unmap_4k_reclaim_one.rs:90/:92, boundary :100) from syscall_thread_exit_reclaim_release.rs:534 | Z |
| kill_process reclaim | same two helpers from syscall_kill_process_reclaim_release.rs:161/:638 | Z |
| kill_process / kill_container scoped reclaim | `kill_reclaim_unmapped_4k_page_scoped` syscall_kill_process_reclaim_scoped.rs:237; shared-page branch unlocks :262 (Z); last-mapping branch holds the window into `kill_reclaim_last_4k_mapping_scoped` (…_reclaim_scoped_last.rs:18), whose boundary :131-132 asserts `kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq`; unlock :163 folds into quota step :170 | **N** (table is live, big-write held) |
| kill retire (zombie tables) | `kill_retire_next_table_page` syscall_kill_process_retire_pages.rs:465 (u_eq :479) / `kill_retire_table_page_and_unlock` :622 (`..._except_tables_of_implies_u_eq` :630); scoped :117 (u_eq :131) / :280 | Z, but :479 and scoped :131 use the all-tables u_eq lemma → switch to `kernel_lock_states_unchanged_except_tables_of_implies_u_eq(.., Some(target))` (projection.rs:142) |

Only one N site. Recommended fix (no new step): in `kill_reclaim_unmapped_4k_page_scoped` release the window right after
the leaf is removed (table is big-write held, `unlock_pagetable_window` needs no stale/present clause in write mode,
locker_unlocker_pagetable_window.rs:151-152), i.e. before calling `kill_reclaim_last_4k_mapping_scoped`, and drop its
`window_perm` parameter. Otherwise a new label `KillProcessWindowLocked` is needed (also reached from kill_container's
Process phase).

## 2. Representation in U

`PageTableU` (src/pagetable_seq/pagetable_spec.rs:60) gains `pub locked_windows: Set<WindowVa>`.
- Projection source: K ghost `PageTableLower.locked_windows` directly. It already equals the set of windows whose L2
  lock bit has an owner (`wf_window_locks`, pagetable_concurrent_spec.rs:649-667), so no walk over `l2_lock`/`l2_rev_map`
  is needed. The lock-ghost backup (`pagetable_lower_backup_wf`, memory_management/pagetable_map_spec.rs:96) is not
  involved: the projection already reads `pt_lower`, not the big lock's ghost slot.
- `PageTableC::user_view` (pagetable_concurrent_spec.rs:334): add `locked_windows: self.lower.locked_windows`.
- `PageTable::user_view` (pagetable_seq/pagetable_spec.rs:69, IOMMU tables): `locked_windows: Set::empty()`.
- `kernel_k_user_projection` (kernel_u_define_spec.rs:64): no edit; it goes through `pagetable_map_user_view` (:5).
  Zombie tables stay hidden (`pagetable: None`), so kill retire window traffic stays invisible.
- Empty-table literals without `..` must add `locked_windows: Set::empty()`: kernel_u_steps.rs:587/:650,
  syscall_new_process_spec.rs:130, syscall_new_process_trace.rs:196, projection_publish.rs:98/:269,
  projection.rs:963/:978 (plus multi-line ones found by the compiler). ~230 other `PageTableU {..}` sites use `..t` and
  silently inherit "windows unchanged".
- Owner: none, like `LockStateU` of every big lock. Windows are exclusive, so membership = held. The holder is implied
  by the progress of the thread whose range covers the window. Alternatives rejected: `Map<WindowVa, LockStateU>` (always
  WriteLocked, redundant); holder-keyed map (needs a LockThreadId→thread map that U lacks; only `ContainerU` exposes an
  owner, via `lock_process_owner_u`).
- Key: `WindowVa` within the table (K keys lctx by `(root, WindowVa)`; root is implicit in which `PageTableU`).

## 3. Step specs

Pattern: `PageTableU { lock_state: X, locked_windows: W', ..pt }`. With concurrent read-mode users of one table (other
threads may hold disjoint windows), adds and removes are stated relative to `old`, never as absolute sets. Membership is
stated pointwise against `va_range_2m_windows(range)` (an `ISet`, pagetable_concurrent_spec.rs:88); no `exists`.
- exact add (all range windows exist): `forall|w| new.contains(w) == (old.contains(w) || va_range_2m_windows(r).contains(w))`
- bounded add (only existing windows, which U cannot see): `old ⊆ new` and `forall|w| new.contains(w) && !old.contains(w) ==> va_range_2m_windows(r).contains(w)`;
  precedent: `mmap_4k_directory_step` already leaves L4/L3 open, `ipc_pages_check_step` reads `new_u` lock states.
- exact remove: `forall|w| new.contains(w) == (old.contains(w) && !va_range_2m_windows(r).contains(w))` (exact because no
  one else can hold a window of a range this thread holds or that does not exist; creation needs big write).

| step spec | file:line | new window clause |
|---|---|---|
| `mmap_4k_enter_step` | syscall_mmap_4k_spec.rs:94 | Read: exact add; Fill: unchanged |
| `mmap_4k_directory_step` | map_4k/mmap_4k_build_structure_spec.rs:78 | bounded add on caller's table (covers fill pre-install lock and minting) |
| `mmap_4k_downgrade_step` | syscall_mmap_4k_spec.rs:185 | bounded add (no directory missing case) |
| `mmap_4k_exit_step` | syscall_mmap_4k_spec.rs:257 | exact remove |
| `unmap_4k_enter_step` / `unmap_4k_exit_step` | syscall_unmap_4k_spec.rs:63 / :96 | bounded add / exact remove |
| `iommu_map_4k_enter_step` / `_exit_step` | syscall_iommu_map_4k_spec.rs:91 / :190 | add on CPU table of va range (exact if the check guarantees presence, else bounded) / exact remove |
| `ipc_pages_lock_tables_step` | syscall_ipc_spec.rs:469 | source exact add (Read path) / target bounded add |
| `share_4k_directory_step` | map_4k/share_mapping_4k_spec.rs:112 | bounded add on target table (ipc fill, new_process/new_container child) |
| `ipc_pages_check_step` (failed) / `ipc_pages_unlock_tables_step` | syscall_ipc_spec.rs:505 / :586 | exact remove on both tables (ranges from progress) |
| `new_process_enter_step` / `new_process_finish_step` | syscall_new_process_spec.rs:79 / :205 | source exact add / source + child exact remove |
| `new_container_enter_step` / `new_container_finish_step` | syscall_new_container_spec.rs:102 / :219 | same |
| `new_process_publish_step`, `kernel_u_container_root_published`/`_created` | new_process_spec.rs:122, kernel_u_steps.rs:546/:611 | empty set literal |
| (only if Q3 = keep) new `kill_process_window_locked_step` | syscall_kill_process_spec.rs | exact add of one window |

No `kernel_u_*` generic step spec in kernel_u_steps.rs changes semantics (none covers a window-changing stretch); they
only need the literal fix. Leaf/flush/refund/TLB steps keep "unchanged" via `..t` and now additionally *claim* windows
unchanged — true, but their wrappers must prove it (below).

Syscall traces whose meaning changes (text unchanged, built from the specs above): `mmap_4k_syscall_trace`
(syscall_mmap_4k_spec.rs:314), `unmap_4k_syscall_trace` (syscall_unmap_4k_spec.rs:134), `iommu_map_4k_syscall_trace`
(syscall_iommu_map_4k_spec.rs:219), `ipc_pages_syscall_trace` / `ipc_pages_rendezvous_syscall_trace`
(syscall_ipc_spec.rs:692/:672), `new_process_syscall_trace` (syscall_new_process_spec.rs:282),
`new_container_syscall_trace` (syscall_new_container_spec.rs:295); plus `kill_process_syscall_trace` (:620) and
`kill_container_syscall_trace` (syscall_kill_container_spec.rs:385) only if Q3 keeps the new step. The other 20 traces
(alloc_quota×4, cpu_hotplug×4, schedule, rebalance, new_thread, new_endpoint, ipc ordinary/call×3/endpoint,
iommu_unmap, pci, thread_exit) are untouched.

### Wrapper lemmas (src/kernel/kernel_step_wrappers*)
(a) U-equality lemmas whose page-table premise is mapping + big-lock mode only; each needs a window premise
(recommended: one more conjunct in the existing per-table forall, `pagetable_c(post..,p).lower.locked_windows ==
pagetable_c(pre..,p).lower.locked_windows`): projection.rs:52, :73, :142 (excluding the zombie table), :661;
bindings.rs:32; release.rs:6; kernel_step_wrappers.rs `end_kernel_step_unchanged` :402, `end_kernel_step_restored_locks`
:169, `_with_iommu_table` :278. `kernel_pagetable_window_lock_changed_implies_u_eq` (nonlock_projection.rs:200) is dead
(0 callers) and becomes false: delete with the nonlock layer.
(b) Step lemmas whose stretch folds window changes; ensures must name the change: pagetable_read_mode.rs:59, :150,
:241, :522, :633, :735 (private helper); ipc_pages_tables.rs:9; new_process_read_mode.rs:12, :168, :287; the directory
derivation in mmap_4k_install_one.rs:608 `install_one_mmap_4k_directory_page_end_step` (uses
`kernel_thread_quota_4k_changed_implies_u_step`, boundary.rs:77); new_container finish wrappers in
projection_publish.rs / projection_ipc.rs.
(c) Remaining lemmas that build the process map from mapping-level pagetable facts (would silently stop proving
`process_map` equality): grep count of mapping-only premises — boundary.rs 6, pagetable_read_mode.rs 8, projection.rs 8,
projection_ipc.rs 7, per_map_projection.rs 3 (:23, :322, :493), iommu_table_steps.rs 1, kill_container.rs 1,
ipc_pages_tables.rs 2, projection_publish.rs 2, new_process_read_mode.rs 1, kernel_step_wrappers.rs 3 → ~43 requires
clauses, of which the ~15 in (a)+(b) are the real work; the rest get a mechanical window-equality conjunct whose callers
discharge it from `*post == KernelK { .., ..*pre }` shapes (pt_lower untouched) or from lower-half primitive ensures.

## 4. NI
- `domain_view` (noninterference/src/domain.rs:26) copies whole `ProcessU`, so window locks become visible to the owning
  domain automatically; no `DomainView` edit.
- `StepLabel` (noninterference/src/theorem.rs:23): no new label if Q3 = restructure kill reclaim; otherwise add
  `KillProcessWindowLocked` with `kill_process_window_locked_step_lr/_iso` in ni_kill_process.rs and reuse in
  ni_kill_container.rs (kill_container Process phase reuses the kill_process sub-steps).
- Existing `_lr`/`_iso` lemmas to re-verify / patch (they reveal the step spec): ni_mmap_4k.rs (Enter, Directory,
  Downgrade, Exit), ni_unmap_4k.rs (Enter, Exit), ni_iommu_map_4k.rs (Enter, Exit), ni_ipc.rs (`ipc_pages_lock_tables_step_lr/_iso`
  :317/:328, check, unlock tables), ni_share_4k.rs (Share4kDirectory), ni_new_process.rs, ni_new_container.rs (Enter,
  Publish, Finish). `_iso` lemmas that assert `new.pagetable == old.pagetable` for lock-only steps (e.g. ni_kill_process.rs:44,
  :627) are on steps without window changes and stay true.
- Leak check: who can hold a window of a table of domain A?
  * mmap/unmap/iommu_map/new_process source: the table's own process → same domain.
  * new_process/new_container child tables: child is in the caller's subtree → caller's domain (`in_domain`, domain.rs:6).
  * kill_process/kill_container: target is a descendant of the killer → killer's domain; retire runs on zombie (hidden) tables.
  * ipc pages: the stepper locks the PEER's table (source or target) and the peer may be in another container. This is
    exactly the situation that already exists for the peer table's big-lock mode (`ipc_pages_lock_tables_step_lr`,
    ni_ipc.rs:317: "tables of a and of its peer outside b"): `isolated(u,a,b)` (isolation.rs:84, `endpoint_iso`) rules
    out an endpoint shared between a and b, so the peer is in a or a third domain, never in b. Windows add no new
    channel. Flag only: if NI is ever strengthened to step consistency or to a third observer that owns the peer, the
    peer-table window set and lock mode are the same open question; windows do not create it.
- Concurrency inside one domain: other threads of the same process may hold disjoint windows of the same table under
  big read; step specs are relative (add/remove), so this is consistent.

## 5. Size, risk, order
- Files: ~3 core (PageTableU, two user_view), ~8 literal fixes, ~6 locker/primitive files (KernelK window lockers +
  `pagetable_map_create_entry_l3` chain need `locked_windows` ensures), ~12 wrapper files, ~10 step-spec files,
  ~10 trace files (`*_from_u`/`*_pre_from_k`), ~20 exec files (u_eq / rebase / boundary call sites; 60 `implies_u_eq`
  calls in src/kernel/implementation, 29 of those files touch windows), ~8 NI files. Roughly 70 files.
- Step specs changed: ~17 (table in §3). New step specs: 0 (or 1 for kill). Wrapper lemmas: ~15 substantive + ~30
  mechanical requires conjuncts. Trace lemmas: ~20 `_from_u` lemmas for the specs above.
- New lemmas: none needed if the lockers state `locked_windows` in their ensures. Optional point lemma
  `pagetable_window_locks_wf_at` (`*_wf_at`, approval-free) if a wrapper must derive membership from lctx instead.
- Proof-cost risk: the KernelK range lockers (locker_unlocker_pagetable_range_windows.rs) are the hot loops; they need
  a new loop invariant + ensures `pagetable_c(final..root).lower.locked_windows` = old ∪ (range | existing) windows.
  The PageTableC-level fact already exists for single windows (pagetable_concurrent_lock_eof.rs:25/:46), so per-iteration
  cost is one Set insert; expect a few % on those four loops, plus small widening of every `PageTableU` equality
  (memory note: ~0.1 %/field). Biggest risk is the U-side ipc/share functions already near 14–20M
  (`share_mapping_4k_build_and_share`, `ipc_pages_lock_tables_attempt`): keep window facts out of them by stating the
  window delta in the K→U wrapper ensures, not in exec.
- Order: (0) nonlock deletion lands. (1) PageTableU field + user_view + literals + window equality conjunct in the (a)
  lemmas + locker ensures → compile/verify `kernel_core` focused on wrappers. (2) mmap (both modes; exercises exact
  add, bounded add, minting, exit) + ni_mmap_4k. (3) unmap, iommu_map. (4) share_4k core + new_process, new_container.
  (5) ipc pages (largest). (6) kill reclaim restructure + switch retire u_eq to the zombie variant; thread_exit and
  kill_container only re-verify. (7) NI full run, monolith.

## Open questions (with recommendation)
Q1. Granularity: fold window changes into the step of the stretch (like big locks), or force a boundary after every
    window op? Recommend fold: no new labels, traces stay short; forcing boundaries adds ~2 steps per syscall and per
    directory install.
Q2. Field shape `locked_windows: Set<WindowVa>` without holder. Recommend yes (matches `LockStateU`).
Q3. kill reclaim N site: release the window before `kill_reclaim_last_4k_mapping_scoped` (no new step) vs keep and add
    `KillProcessWindowLocked`. Recommend release early (big write held, semantics unchanged).
Q4. Existing-window acquisitions (mmap fill, unmap, ipc target, possibly iommu_map) are not determined by U (L2 presence
    is K-only). Accept bounded-add specs (old ⊆ new ⊆ old ∪ range windows), or expose L2 presence in U? Recommend bounded
    add; NI here is local respect + isolation only, which non-determinism does not hurt.
Q5. Where the window-equality premise lives: inline conjunct in the existing per-table lock-mode foralls (ordinary
    contract edit, ~43 sites) vs a new named K predicate (framing spec → needs approval) vs folding it into
    `kernel_pagetable_nonlock_fields_unchanged` (kernel_step_spec.rs:29; fewer edits but contradicts the name and breaks
    every window locker's `kernel_cpu_process_thread_nonlock_fields_unchanged` ensures). Recommend inline conjunct.
Q6. Should leaf/flush step specs explicitly require the range windows to be held (e.g. `mmap_4k_leaf_step_pre`)? Not
    needed for NI; recommend no for now.
