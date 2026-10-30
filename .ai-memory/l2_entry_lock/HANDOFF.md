# Handoff: per-entry L2 window locks + window locks in U (2026-10-29)

Branch `claude/concurrent-pagetable-kill-container-598619`. Work stopped mid-batch at the user's request; this file is the
resume point. Delete this directory when the work is merged.

## What this is
Design: `l2_entry_lock_design.md` (§A–G, decisions D1–D12, naming). Older U-side sketch: `window_locks_in_u_design.md`.
Batch briefs: `b0_api_freeze.md`, `b1_pagetable_concurrent.md`, `b2_kernel_core.md`, `b3a_mmap.md`, `b3b_map4k.md`,
`b3c_unmap_iommu.md`, `b3d_ipc.md`, `b3e_new_process_container.md`, `b3f_kill_thread_exit.md`, `b4_ni.md`.
Order: B0 → B1 ∥ B2 → B3b (map_4k, blocks the others) → B3a/c/d/e/f (+B3x/B3y) → B4 NI → integration.

Summary of the design: each L2 entry is a lock object `L2EntryLock { word: AtomicUsize, l1: Tracked<Option<PointsTo<PageMap>>>,
entry: Ghost<PageEntry>, owner: Ghost<SpinLockState> }` (src/pagetable_concurrent/l2_page_map.rs), `L2PageMap { ar: [L2EntryLock;
512], addr }`; the old page-wide `L2PageGhost`/`L2LockGhost` tokens and `PageTableLower.l1_tables` are gone, `PageTableLower` keeps
`l2_perms` (tracked) plus ghost `l1_rev_map`, `mapping_4k/2m`, `pagetable_window_locks: Map<WindowVa, LockStateU>` (dom = all 512
windows of every L2 page, value = owner is Some), `window_stale_cpus`. `PageTableU.pagetable_window_locks` is projected verbatim;
every window lock/unlock is part of a U step (folded into the adjacent recorded step, coarsest span rule in AGENTS.md).

## State of the tree (all uncommitted work is in the last commit of this branch)
Green per crate with focused runs (no whole-package, NI, or monolith run yet):
- B0 API freeze (35 files; typecheck #34778, l2_page_map 8/0).
- B1 pagetable_concurrent (#34786, 192/0). Module total 23.47M → 33.23M (lock_eof 0.76M → 5.23M from the uniqueness broadcast).
- B2 kernel_core (#34790 430/0; #34801 11/0 after the leaf-wrapper fix). Common fns +4.7% rlimit.
- B3x alloc_page + new_thread: unchanged, green (#34796 165/0, #34797 4/0, #34798 21/0).
- B3y alloc_quota, schedule, pci, cpu_hotplug: green (#34792 28/0, #34793 10/0, #34794 36/0, #34795 51/1 → #34803 3/0). Only edit:
  one flat per-cell framing clause in `cpu_offline_request_eof_transition_framing`
  (src/kernel/implementation/syscall_cpu_hotplug/syscall_cpu_offline_request_eof.rs:17-18) because `cpu_offline_flags_wf` has only a
  deep trigger. Two unedited cpu_hotplug fns grew from the kernel_core contracts: `cpu_offline_commit_unlock_and_record` 1.13M →
  2.60M, `cpu_offline_check_recheck` 3.29M → 4.17M.
NOT green:
- B3b map_4k crate: PARTIAL and UNVERIFIED. The agent was stopped while editing. Touched: map_4k/unmap_4k_present.rs,
  unmap_4k_range.rs, unmap_4k_reclaim.rs, unmap_4k_reclaim_last.rs, unmap_4k_reclaim_last_cache.rs, unmap_4k_reclaim_one.rs,
  unmap_4k_remove.rs (window-perm plumbing, `l2_lock ==` ensures → `pagetable_window_locks ==` + per-(p,i) `l2_owner` equality).
  Not started: `progress_thread_lock_perm` plumbing in mmap_4k_build_one_structure / install_one_mmap_4k_directory_page, the two
  directory-step rewrites below, create_entry_l3 callers, share child structure, flush_all loop invariant (its last note:
  "Fix the loop-invariant site in flush_all"). Every crate above map_4k (mmap, unmap, iommu_*, ipc, new_process, new_container,
  kill_process, kill_container, thread_exit, noninterference) does not compile yet.

## Decisions taken after the briefs were written (override the briefs where they differ)
1. create_entry_l3 pre-locks only the new L2 page's windows inside the mmap/share range (lo..=hi), one CAS per window, Linux-style
   ("按 A 继续"); returns `Tracked<Map<L2Index, LockPerm>>`.
2. Directory steps (design §D.4) must NOT index the new L2 page by `range[mapped]` / `target_range[shared]`: live code builds
   directories for pages other than the recorded progress index (mmap fill keeps `mapped == 0`, share child structure keeps
   `shared: 0`, ipc builds page i with unrelated `shared`). Approved shape for both `mmap_4k_directory_step` and
   `share_4k_directory_step`, t_old/t_new = the (target) table's `pagetable_window_locks`:
   - `new_dir is L3 ==> !t_new.dom().subset_of(t_old.dom()) && forall|w: WindowVa| #![trigger t_new.dom().contains(w)]
     t_new.dom().contains(w) && !t_old.dom().contains(w) ==> t_new == pagetable_window_locks_after_new_l2_page(t_old,
     spec_v2l4index(w.va), spec_v2l3index(w.va), range)` (share: target_range on the target table; source table unchanged)
   - `!(new_dir is L3) ==> t_new == t_old`
   - share: drop the `rank(old.directory) < rank(new.directory)` clause; keep "new progress == Share4k with the same
     source_range/target_range/shared/origin and directory = installed level". `Share4k` progress gained `directory: Mmap4kDirectory`
     in B0 (proc/thread_def.rs).
3. New map_4k signatures (frozen for the unmap and kill batches):
   - `unmap_4k_range(.., Tracked(window_perms): Tracked<&Map<WindowVa, LockPerm>>)` as LAST parameter (the map returned by
     `lock_pagetable_range_existing_windows`), requires: for every page j of the range, `window_perms.dom()` contains
     `window_of(range[j])` and that window's `l2_owner` is `Some { thread_id, lock_id }` of `window_perms[window_of(range[j])]`.
   - `clear_4k_mapping_present_in_window`, `reclaim_unmapped_4k_page_in_window`, `remove_4k_mapping_without_free` gain a LAST
     parameter `Tracked(window_perm): Tracked<&LockPerm>` and the requires
     `pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(pagetable_c(..).window_l2_page(
     spec_v2l4index(va), spec_v2l3index(va)), spec_v2l2index(va)) == (SpinLockState::Some { thread_id: window_perm.thread_id(),
     lock_id: window_perm.lock_id() })`. Callers: map_4k/unmap_4k_range.rs:277/:530, syscall_kill_process_reclaim_scoped.rs:260
     (window locked at :237).
   - `install_one_mmap_4k_directory_page`, `mmap_4k_build_one_structure` and their private chain gain
     `Tracked(progress_thread_lock_perm): Tracked<&LockPerm>` right after `Tracked(quota_thread_lock_perm)` (needed only when the
     progress thread's progress is Share4k and write-held). mmap callers (map_one_leaf.rs:149, fill_structure.rs:182/:196) pass the
     quota-thread perm again; ipc (syscall_ipc_pages_fill.rs:214) passes the caller thread's perm.
4. kernel_core facts the B3 batches rely on: the 8 leaf wrappers (`pagetable_map_insert_4k[_wlocked]`, `create_entry_l2[_wlocked]`,
   `clear_4k_present[_rlocked]`, `unmap_4k_kernel[_rlocked]`) end with
   `forall|p: PageMapPtr, i: L2Index| #![trigger pagetable_c(M_post, *final(pt_lower), pagetable_ptr).lower.l2_owner(p, i)]
   ... l2_owner(p, i) == pagetable_c(M_pre, *old(pt_lower), pagetable_ptr).lower.l2_owner(p, i)`;
   `pagetable_map_remove_table_page` has that clause ONLY for `scan is L1` (L2/L3 removals happen only on zombie tables in kill
   retire). If a kill/thread_exit caller holds another window across an L2/L3 removal, B1 must add to `remove_structure_page`
   (src/pagetable_concurrent/structure_scan.rs ~:164): `scan is L2 ==> forall p,i. p != scan->L2_l2_p ==> l2_owner eq` and
   `scan is L3 ==> forall p,i. l2_owner eq`.
   Renamed: `pagetable_l2_windows_unlocked_when_wlocker_holds_no_windows` → `wlocker_holds_no_windows_implies_l2_windows_unlocked`
   (src/kernel/memory_management/subsystem_mutation_eof.rs:773).
5. Steps: no stutter boundaries; `u_eq`/`rebase_snapshot_k_if_unchanged` points that stop holding are deleted (mmap fill_enter.rs:149
   already deleted in B0). New steps only on the drain path: `KillProcessPagetableWindowsChanged`,
   `ThreadExitPagetableWindowsChanged` (+ `thread_exit_refund_step`), ≤2 windows per drain step; kill-local
   `kill_process_refund_step`; zombie-table retire u_eq sites use `kernel_lock_states_unchanged_except_tables_of_implies_u_eq`.
   Names must say they act on the page table (`pagetable_window_*`, never bare `window_*`).
6. Rules added this session: coarsest-U-step rule (AGENTS.md "Runtime performance comes first"); lemma names
   `<premise>_implies_<conclusion>` (AGENTS.md); TCB aliasing argument for many `&mut KernelK` = every top-level field only touched
   under its lock.

## Next steps
1. Relaunch B3b on the whole map_4k crate with `b3b_map4k.md` + items 2–4 above; finish from the partial diff
   (`git diff 9a4bd6a -- src/kernel/implementation/map_4k`), focused runs per module, report the final signatures.
2. Then B3a mmap, B3c unmap_4k + iommu_map_4k + iommu_unmap_4k, B3d ipc, B3e new_process + new_container, B3f kill_process +
   kill_container + thread_exit, concurrently, each with its brief plus items 1–5.
3. B4 NI (`b4_ni.md`). 4. Integration: workspace → `noninterference/verify-ni.sh` → monolith (`./verify.sh --num-threads 32
   --time-expanded --output-json`; last baseline 1,132,563,158 at #34758 before this work) → boot build + KVM; style pass; local
   commits without AI trailers; ask before push.
