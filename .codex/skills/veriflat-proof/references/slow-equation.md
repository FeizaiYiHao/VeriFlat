# Slow-equation EOF/EOL exception

- A function or loop whose single equation exceeds 5 seconds SMT under
  `--time-expanded` may use one S-shaped EOF/EOL summary.
- Introducing the one operation-specific full-EOF summary S and its independent
  closure functions for a long equation does not require user approval. S may
  be freely reshaped while debugging and optimizing the proof, provided it
  remains a complete transition/framing summary, contains no final invariant or
  `*_wf` closure, and does not change model semantics. This authorization does
  not extend to reusable or cross-operation framing specs or lemmas.
- A structurally large equation may use a higher rlimit while it is diagnosed
  or as its measured final ceiling. High rlimit is not itself a defect, but the
  ceiling must be justified by uncapped measurement and kept no higher than
  practical.
- A single equation exceeding 10 seconds SMT is not acceptable for handoff.
  Simplify accumulated facts and quantified expansion first; if the cost
  persists, isolate or split the equation. Raising rlimit does not replace this
  work.
- Full EOF is defined by its proof boundary, not by the location of an inline
  tail. Define exactly one open spec, optionally `#[verifier::opaque]` for
  solver scheduling: `<operation>_transition_framing`. This S is the complete
  operation-state summary: it records every changed object family, every exact
  pre-to-post mutation, and every preservation or argument-identity fact needed
  by the whole post-state proof. A summary covering only one subsystem or one
  failing invariant is a partial experiment, not EOF.
- S contains only entry facts, exact mutation/framing, and necessary argument
  identities. It contains no post invariant, invariant group, post `*_wf`,
  permission-WF, or other derived closure result; inline subordinate relations
  instead of defining more specs.
- Prove S at the mutation producer from constructor/update/callee facts. The
  main exec equation may retain intermediate facts required to execute later
  mutations and must retain `typed_lock_maps_aligned`, but it must not close
  any final post-state invariant,
  invariant group, or `*_wf` leaf. One scoped reveal opens opaque S; do not
  unfold `KernelK::inv`, subsystem invariants, or old invariant leaves merely
  to state it.
- Choose the EOF boundary after all operation mutations and before any
  invariant-dependent consumer such as unlock. Move all final invariant closure
  into independently verified proof functions outside the exec equation. Their
  explicit inputs are the entry invariants, S, and only necessary narrow
  representation guarantees already produced by executed callees. Every final
  invariant must be derived there through S; the EOF functions may derive and
  pass intermediate invariant groups to later EOF stages.
- A nested `proof` block or `assert ... by` block in the exec function retains
  the surrounding solver context. Moving, merging, or renaming inline
  invariant assertions is preparatory work, not EOF isolation.
- Check the interface across the actual crate and abstraction boundaries. A
  callee's local representation-WF guarantee does not follow merely from equal
  abstract views. Preserve such evidence as explicit, narrow EOF inputs when
  it already follows from the executed primitive's verified contract; identify
  its producer. Do not put it in S or a new wrapper. Do not pass post kernel
  invariant groups or other closure results from exec as shortcut preconditions.
  The EOF functions must derive all aggregate invariant closure themselves;
  post invariants or `*_wf` leaves passed from the exec equation are forbidden
  shortcuts.
- EOF framing calls are limited to existing
  `lemma_no_change_imply_*_wf*` and approved fold lemmas. All other new or
  existing specialized preservation/framing helpers are forbidden; prove
  changed-state leaves inline with S, scoped reveals, and direct algebra.
- Closure still follows subsystem -> memory -> process -> direct leaves ->
  `inv()`, and uses the canonical compact layout.
- Before reporting full EOF, audit the exec function for leftover final
  invariant closure and audit every EOF proof dependency back to S. Verify the S
  producer and every closure function, then run the required split and monolith
  checks. Measure the producer and all new closure equations together under the
  baseline's cache/thread scope. Report both their individual SMT/rlimit costs
  and total wall time; a faster producer alone is not a speedup. Label incomplete
  or reverted inline experiments separately from EOF results.
