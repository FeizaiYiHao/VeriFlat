---
name: veriflat-workflow
description: Always-on VeriFlat workflow rules. MANDATORY — before ending any session that edited src/**/*.rs, you MUST run /style-check. If violations are found, fix them and re-run until clean. This replaces the Stop hook from Claude. Use this skill at the start of every coding session that touches Verus source.
---

# VeriFlat Workflow Rules

These rules apply to ALL coding sessions in the VeriFlat project.

## Rule 1: Style Gate (MANDATORY)

**Before ending any session that edited `src/**/*.rs`, you MUST run `/style-check`.**

Procedure:
1. After completing the main editing work, run `/style-check` on all dirty `src/**/*.rs` files.
2. If violations are found, fix them and re-run `/style-check` until it reports **clean**.
3. Only then consider the session done.

This is non-negotiable. A session that edited Verus source but did not pass style-check is incomplete.

## Rule 2: Style Reminder (Pre-Edit)

Before writing or editing any `src/**/*.rs` file, internalize the Verus style:
- Match `.kiro/steering/verus-style.md` and the canonical files:
  - `src/kernel/implementation/syscall_alloc_quota.rs`
  - `src/kernel/implementation/locker_unlocker.rs`
- Open the nearest LIVE sibling and copy its shape.
- Key tells: bare `requires` (no comments); comment-free `proof {}` blocks;
  `#![auto]` on shallow framing foralls, hand `#![trigger]` on deep ones,
  NEVER `#![all_triggers]`; spell out `.view()` (no `@`); spec files hold only specs.
- `inv()` rebuild closes from a few `reveal(...)`s + narrow lemma calls —
  do NOT add `assert forall|..| ..==old(self).. by{if k!=touched{assert(..)}}` scaffolding.

## Rule 3: Proof Hygiene

When writing or modifying proofs:
- Every `let ghost` must have a live reader. If none, delete it.
- No dead scaffolding around `assume(...)` stubs.
- No trigger-compensating asserts — if the quantifier should fire on its own,
  fix the trigger at the spec, not patch at the call site.
- `#[verifier::spinoff_prover]` is Xiangdong's call — never add unprompted.
- Invariant/opaque-spec changes are ASK-FIRST.

## Rule 4: Session Tracking

Track which files you edit during the session:
```bash
.qoder/hooks/style-record.sh   # run after editing to log dirty files
```

## Available Skills

| Skill | Purpose |
|-------|---------|
| `/style-check` | Review diff against Verus style; certify clean pass |
| `/discharge-assume` | Replace `assume(P)` with real proof via sibling recipe |
| `/shrink-proof` | Strip scaffolding from green proof (delete-and-reverify) |
| `/profile-proof` | Ablation-based rlimit attribution to locate costly obligation |
