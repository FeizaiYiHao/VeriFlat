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
- For full EOF, choose a boundary after the operation's mutations and before
  invariant-dependent consumers such as unlock. S must describe every changed
  object family and preserve the other inputs needed by the complete closure;
  a summary of only memory fields is a partial experiment.
- Move the entire invariant-closing tail into independently verified proof
  functions whose entry invariant, S, and necessary direct callee guarantees
  are explicit inputs. A nested `proof` or `assert ... by` block in the exec
  function retains the surrounding solver
  context; merging such blocks is preparatory work, not EOF isolation.
  The exec producer must establish S without first proving the post invariants
  that the EOF functions are supposed to derive. Keep lock alignment and facts
  required for actual exec/callee safety at their existing producer boundaries.
- Check the interface across the actual crate and abstraction boundaries. A
  callee's local representation-WF guarantee does not follow merely from equal
  abstract views. Preserve such evidence as explicit, narrow EOF inputs when
  it already follows from the executed primitive's verified contract; identify
  its producer. Do not put it in S or a new wrapper. Do not pass post kernel
  invariant groups or other closure results from exec as shortcut preconditions.
  The EOF functions must derive all aggregate invariant closure themselves;
  intermediate groups proved inside EOF may feed subsequent EOF stages.
- EOF framing calls are limited to existing
  `lemma_no_change_imply_*_wf*` and approved fold lemmas. All other new or
  existing specialized preservation/framing helpers are forbidden; prove
  changed-state leaves inline with S, scoped reveals, and direct algebra.
- Closure still follows subsystem -> memory -> process -> direct leaves ->
  `inv()`, and uses the canonical compact layout.
- Before reporting full EOF, audit the exec function for leftover invariant
  closure, verify the S producer and every closure function, and run the required
  split and monolith checks. Measure the producer and all new closure equations
  together under the baseline's cache/thread scope. Report both their individual
  SMT/rlimit costs and total wall time; a faster producer alone is not a speedup.
  Label incomplete or reverted inline experiments separately from EOF results.
