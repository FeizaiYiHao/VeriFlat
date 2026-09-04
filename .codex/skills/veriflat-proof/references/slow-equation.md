# Slow-equation EOF/EOL exception

- A function or loop whose single equation exceeds 5 seconds SMT under
  `--time-expanded` may use one S-shaped EOF/EOL summary.
- Define exactly one open spec, optionally `#[verifier::opaque]` for solver
  scheduling: `<operation>_transition_framing`. It contains only entry facts,
  exact pre-to-post mutation/framing, and necessary argument identities. It
  contains no post invariant, post `*_wf`, permission-WF, or derived closure
  result; inline subordinate relations instead of defining more specs.
- Prove S at the mutation producer from constructor/update/callee facts. One
  scoped reveal opens opaque S; do not unfold `KernelK::inv`, subsystem
  invariants, or old invariant leaves merely to state it. Keep
  `typed_lock_maps_aligned` and `lock_id_set_aligned` in exec.
- EOF closure may split only its invariant-closing tail into small proof
  blocks/functions. Framing calls there are limited to existing
  `lemma_no_change_imply_*_wf*` and approved fold lemmas. All other new or
  existing specialized preservation/framing helpers are forbidden; prove
  changed-state leaves inline with S, scoped reveals, and direct algebra.
- Closure still follows subsystem -> memory -> process -> direct leaves ->
  `inv()`, and uses the canonical compact layout.
