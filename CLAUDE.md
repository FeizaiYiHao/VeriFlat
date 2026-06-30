# VeriFlat

A microkernel verified with Verus (everything under `src/` is Verus Rust).
Build/verify with `./verify.sh` from the project root.

## Steering docs (auto-loaded via the imports below)

These three files are the working knowledge base. They are imported here so a
fresh session loads them automatically:

- **veriflat-project-notes.md** — durable architecture, conventions, idioms,
  gotchas, and the reference syscall example. Stable; rarely edited.
- **verus-verification.md** — the transferable "how to verify" playbook
  (cost tactics, proof patterns, TCB axiom design, failure strategies).
- **verus-style.md** — the code-style signature: layout, naming, idiom, and
  the concrete proof-structure patterns (nested inv() re-establishment, the
  lock-wrapper-per-object pattern, fold-conjunct discipline). Write edits that
  match it.

@.kiro/steering/veriflat-project-notes.md
@.kiro/steering/verus-verification.md
@.kiro/steering/verus-style.md
