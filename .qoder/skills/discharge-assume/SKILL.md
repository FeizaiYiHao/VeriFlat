---
name: discharge-assume
description: Discharge an assume() in a VeriFlat inv() re-establishment by mining the assert-by-reveal recipe a sibling proof already uses for that conjunct. Use when a function verifies green only because a subsystem conjunct is stubbed with assume, and you want to pay it down one conjunct at a time.
---

# Discharge Assume

Turn an `assume(<conjunct>)` in a VeriFlat proof (almost always an `inv()`
re-establishment after a mutation) into a real `assert(<conjunct>) by { ... }`,
by finding a LIVE proof that already re-establishes the SAME conjunct across a
SIMILAR mutation and transplanting its reveal/lemma recipe.

Arguments may name the function / module / file (and optionally which conjunct)
to target. If empty, use the most recently edited proof in the session
(`git diff --name-only -- src`) and its first remaining `assume(...)`.

## The Core Idea

An `assume(P)` in an `inv()` rebuild is almost NEVER a real proof gap. The same
`P` — some `*_wf` conjunct — is re-established after a mutation somewhere in the
LIVE tree already: a fully-verified syscall (`allocate_free_4k_page`'s
`pop_stage_4k_page`, `syscall_alloc_quota_4k` + `commit_alloc_quota_4k`), a lock
wrapper in `locker_unlocker.rs` (`wlock_page`/`wunlock_page`,
`wlock_process`/`wunlock_process`), or a preservation lemma in `lemma_u/`. Your
job is to find that sibling, read the `assert(P) by { reveal(...); lemma(...) }`
recipe it uses, and transplant it — adapting the framing to YOUR mutation. The
recipe you need almost always already exists; you are copying, not inventing.

**Why this beats grinding from scratch:** the reveal set for an opaque `*_wf`
predicate (which sub-predicates to open, which round-trip lemma, which
cross-invariant reveal supplies a `dom().contains`) is non-obvious and expensive
to rediscover. The sibling already paid that cost. Copying its `by {}` shape is
minutes; re-deriving it is hours and usually lands on a worse (over-revealed) proof.

## Recipe Taxonomy — Match Your Mutation to the Sibling's

Pick the recipe by WHAT the mutation did to the maps/arrays the conjunct reads:

1. **Byte-equal map (mutation didn't touch this subsystem's map).** Recipe:
   `assert(P(self.X)) by { reveal(P); reveal(<P's opaque sub-preds>); };`. The
   args are byte-identical, so it closes by congruence + the reveals. Sibling:
   any wrapper's `subsystems_inv` conjuncts for the maps it didn't lock
   (`wlock_cpu` proving `container_perms_wf` etc.).

2. **Page-state flip (one slot's `state` changed, array else unchanged).** Recipe:
   call the `*_preserved_for_page_state_eq` / `*_preserved_for_owning_container_eq`
   family in `lemma_u/pages_wf_page_state_eq.rs` /
   `staged_pages_wf_eq.rs` / `container_page_owner_wf_eq.rs` /
   `hugepage_page_state_eq.rs`, passing `old(self).X, self.X`. For conjuncts
   with no framing lemma (`container_allocator_free_*_page_wf`): the
   `pop_stage_4k_page` reveal set — `reveal(container_allocator_free_Nk_page_wf);
   reveal(allocator_free_page_ptrs_wf); reveal(container_allocator_wf);
   reveal(container_page_owner_wf); page_ptr_lemma1();` — works when the touched
   slot is non-Free before AND after (nothing Free-classed changed).

3. **Map GROWTH (a fresh entry inserted — the create/retype case).** Recipe,
   inside the conjunct's `by {}`:
   - `reveal(P);` then `assert(P(old(self).<maps>));` — bring the OLD opaque
     invariant into scope (free from `old(self).inv()`); the transport needs it.
   - `reveal(<supporting wf>); assert(<supporting wf>(old(self)...));` for each
     invariant that supplies a `dom().contains(...)` the conjunct's reads chain
     through (e.g. `container_endpoint_wf` for endpoint->container-in-dom,
     `container_thread_wf(old)` for thread's owning_container-in-dom).
   - an `assert forall|k ...| <antecedent> implies <goal> by { if k == fresh_key
     { <derive the antecedent is false from the fresh entry's preconditions;
     assert(false) or use view()==fresh_value> } else { assert(self.X[k] ==
     old(self).X[k]); } }` — case-split on the fresh key.
   - for a list-membership goal on the grown list, `seq_push_lemma::<T>()` +
     `assert(self...view() =~= old...view().push(v))`.

4. **Fresh entry violates a forward clause unless constrained.** If the growth
   recipe's `k == fresh_key` branch can't show the antecedent false, the fresh
   value needs a PRECONDITION on the create fn. Add it to the create fn's
   `requires` — it's a legitimate fact about a freshly-minted object — then
   the branch closes by `assert(false)` from the contradiction.

## When Reveals Don't Close It — Three Escalations (in order)

1. **Contract under-framing (fix the primitive, not the caller).** If `P` reads
   a field the mutation primitive's `ensures` never pinned, the honest fix is to
   STRENGTHEN THE PRIMITIVE'S `ensures` to promise what it actually does — a
   TCB-contract completion, not a caller-side hand-proof. Only add ensures the
   primitive genuinely maintains.

2. **Invariant-spec conjunct (ASK FIRST).** If the conjunct is unprovable as
   WRITTEN because the spec is under-specified, the fix is a spec conjunct — an
   invariant change. Present it to Xiangdong: the exact conjunct, why the
   discharge needs it, and confirmation the full crate still verifies.

3. **Genuinely needs a NEW lemma/axiom (flag, move on).** If no sibling recipe
   fits and no contract/spec tweak helps, leave the `assume` with a precise
   `//@Xiangdong` note stating EXACTLY what lemma/axiom shape would close it,
   and move to the next conjunct. Do NOT invent an `external_body` axiom unprompted.

## Procedure

1. **Scope + baseline.** Identify the target fn + its `assume(...)`s.
   Back up: `cp <file> /tmp/<name>.bak`.
   Confirm green NOW and note the per-fn rlimit:
   `./verify.sh --verify-only-module <module> --verify-function <fn> --time-expanded`.

2. **For each `assume(P)`, find the sibling.** `grep -rn "assert(P\b\|<P name>"
   src/kernel/implementation/*.rs src/lemma/lemma_u/*.rs` for a LIVE `assert(P)
   by { ... }` or a `*_preserved_for_*` lemma over the same predicate. Read its
   `by {}` / body — that reveal+lemma set IS your recipe. Classify YOUR mutation
   (byte-equal / state-flip / growth) to pick which recipe clause above applies.
   NEVER calibrate against commented-out / dead-template code.

3. **Transplant one at a time, verify.** Replace `assume(P)` with `assert(P) by {
   <transplanted recipe> };`, adapting the framing. Re-run the isolated
   `--verify-function`. One conjunct per verify so each is attributable.
   - **Closes** -> move to the next assume.
   - **Fails** -> read the `--expand-errors` output: which sub-clause / which
     branch. Usually a missing `dom().contains` (add the supporting-wf reveal) or
     a missing old-invariant-in-scope assert. If it won't close after the full
     recipe, escalate (contract -> spec-ask -> flag) per the section above.

4. **Trim the transplant (mandatory, every conjunct).** The recipe you copied is
   often over-revealed for YOUR simpler mutation. Delete-and-reverify each
   `reveal`/assert farthest-from-goal first: a byte-equal map needs fewer reveals
   than the state-flip sibling did; a fresh-entry branch may not need every
   supporting-wf. Keep only fail-on-delete steps. Audit every `let ghost` for a
   live reader.

5. **Full-crate verify.** Any precondition-add or spec conjunct has a
   crate-wide blast radius — run the WHOLE `./verify.sh` (not just the module),
   confirm verified / 0 errors and nothing else slowed to an rlimit. Report:
   which assumes are now proven (+recipe used), which remain (+the exact
   lemma/axiom each still needs).

## Guardrails

- **Never** leave the target non-green, and never swap one `assume` for another or
  use `admit()` to fake a discharge.
- **Invariant/opaque-spec changes are ASK-FIRST**; primitive-`ensures` completions
  state only what the primitive truly maintains; proof-body transplants are free.
- Follow the proof-gap protocol: a conjunct that needs a new axiom/lemma gets
  FLAGGED, not papered over with `external_body`.
- `#![auto]` for shallow framing foralls, hand `#![trigger]` for deep ones, NEVER
  `#![all_triggers]`. Spell out `.view()` (no `@`) in anything you add. Match the
  sibling's banner/comment discipline (bare `requires`, comment-free `proof {}`).

## Relationship to Sibling Skills

- `/discharge-assume` (this) — BUILDS a proof for an assumed conjunct by
  transplanting a sibling's reveal recipe.
- `/shrink-proof` — SHRINKS a green (over-grind) proof back to its genuine content.
- `/profile-proof` — LOCATES the costly obligation before shrinking.
Typical chain: discharge each assume -> shrink the transplant inline -> verify.
