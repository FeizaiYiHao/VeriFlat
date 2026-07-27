---
name: project_payload_mutation_wrapper_2026_07_27
description: Payload-mutation wrapper contracts, page dynamic-id refresh boundary, and final verification handoff
---

# Payload-mutation wrapper handoff (2026-07-27)

## Completed work

After the per-type `LocalContext` lock-map refactor, these payload-mutation
boundaries carry `locked_objects_match_lctx` and `lock_id_aligned` across their
contracts:

- `commit_alloc_quota_4k`
- `alloc_4k_scan_all_caches_and_pool`
- `allocate_free_4k_page`
- `create_thread_from_staged_page_merged`
- `add_new_thread_to_proc_container_and_scheduler`

`create_thread_from_staged_page_merged` is the desired final wrapper shape:
it requires Release phase, matching, and alignment; it refreshes the retyped
page's dynamic lock id internally; it ensures matching and alignment, with
precise thread/page map frames.  Its caller no longer refreshes the page id.

Reusable lemmas in `src/kernel/kernel_k_define_spec.rs`:

- `no_held_pages_imply_lock_id_aligned`
- `page_lock_id_aligned_after_refresh`
- `page_lock_id_aligned_preserved`
- `page_lock_id_aligned_after_remove`

## Protocol boundary

Do **not** mechanically add alignment pre/postconditions to raw `wlock_*` or
`wunlock_*` helpers.  Free-to-Owned retyping changes a page's dynamic lock id
while allocator cache/global-pool locks remain held; that intermediate state is
valid and becomes aligned only in the Release-phase refresh sequence.  The
strong contract belongs on payload transaction wrappers.

## Verification and cost

Final verification:

```text
./verify.sh --time --num-threads 4
497 verified, 0 errors
total-time 18.786s; verification-time 15.387s; total SMT 32.531s;
rlimit 127741987
```

`git diff --check` passed.

Compared to the post-lock-map-refactor baseline:

```text
baseline: 494 verified, total 18.023s, verification 14.683s,
          SMT 30.131s, rlimit 125931568
current:  497 verified, total 18.786s, verification 15.387s,
          SMT 32.531s, rlimit 127741987
```

The wrapper pass did not reduce solver cost in this final single run (roughly
+5 percent verification time), but it centralizes proof burden and removes the
page-id-refresh proof from the new-thread callsite.

## Workspace handoff

The worktree is intentionally dirty with the preceding per-type lock-map
refactor and this wrapper work.  Preserve existing changes and do not reset or
discard unrelated files.
