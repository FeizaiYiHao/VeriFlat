# syscall_alloc_quota_4k cleanup (2026-07-28)

## Scope

- Verified syscall_alloc_quota_4k, commit_alloc_quota_4k, their two KernelU helpers, and the direct CPU/container/4k-quota/process acquire-release wrappers.
- Superseding architecture: the callsite tracks direct `locked_by`/`wlocked_by`
  object state, `LocalContext::lock_id_set`, alignment, and `inv`; it does not
  track typed lock maps. Container/quota wrappers derive their typed key/value
  facts internally.

## Proof rules applied

- Retained only scoped assert-by-reveal proofs. No bare assert, function-scope reveal, ghost snapshot/capture, or new wrapper lemma on this path.
- Non-page wrappers establish alignment directly by revealing lock_id_aligned and page_lock_id_aligned. No visible page_lock_id_aligned_preserved call remains.
- Quota acquire/release retain one quantified per-container 4k conservation transport, but the three old fold-equality lemma calls were redundant and removed.

## Confirmed structural proof boundaries

1. CPU-array and process-map extensional forall facts in the two KernelU helpers: empty proof bodies fail.
2. Quota wrappers' per-container 4k conservation instantiation: reveal alone fails.
3. Process wrappers' 4k/2m/1g Set fold transport via the process-effective-quota fold lemmas: removing 4k fails.
4. Per-container process-tree transport via process_no_change_to_tree_fields_imply_wf: removing it fails.
5. Commit's actual 4k transfer plus unchanged 2m/1g conservation folds: existing change-aware forall lemmas remain appropriate structural boundaries.

## Final checks and performance

- locker_unlocker: 17 verified, 0 errors after the direct-object contract refactor.
- syscall_alloc_quota: 3 verified, 0 errors after removing all typed-map callsite contracts.
- syscall_alloc_quota time-expanded: total 20.470 s; verification 12.345 s; SMT 4.559 s; rlimit 6,099,178.
- locker_unlocker time-expanded: total 23.213 s; verification 15.552 s; SMT 17.770 s; rlimit 25,224,263. It uses four verifier threads; aggregate verification work is 30.750 s.

The old timing remains historical and is not a paired baseline for the current
revision. The current cumulative verification counter reached 391; see the
new-thread/object-state memory for the final timing and profiler snapshot.
