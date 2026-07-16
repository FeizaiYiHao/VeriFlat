#!/usr/bin/env bash
# PreToolUse (Write|Edit) hook: when the edit targets src/**/*.rs, inject the
# VeriFlat Verus style reminder into the model's context BEFORE the edit lands,
# so each new section is written to match Xiangdong's style up front.
# Reads the tool-call JSON on stdin; stays silent (exit 0) for non-src edits.
# Pure grep — no jq/python (unavailable / sandbox-flaky here).
set -euo pipefail
input="$(cat)"
# Extract just the file_path VALUE (not the whole JSON) so edit CONTENT that
# happens to mention a src/*.rs path can't trigger a false positive.
fp="$(printf '%s' "$input" | sed -n 's/.*"file_path"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p')"
case "$fp" in
  */src/*.rs | src/*.rs)
    printf '%s' '{"hookSpecificOutput":{"hookEventName":"PreToolUse","additionalContext":"VeriFlat Verus style — learn it for THIS section BEFORE writing. Match .kiro/steering/verus-style.md and the canonical files (syscall_alloc_quota_4k + the locker_unlocker.rs wrappers); open the nearest LIVE sibling and copy its shape. Tells: bare requires (no // comments); single-line // ---- ---- banners ONLY in ensures and inv() re-establishment; comment-free proof {} blocks; #![auto] on shallow framing foralls, hand #![trigger] on deep ones, NEVER #![all_triggers]; spec files hold only specs; #[verifier::spinoff_prover] on new wrappers/lemmas. inv() rebuild closes from a few reveal(...)s + narrow lemma calls (see wlock_quota_4k) — do NOT add assert forall|..| ..==old(self).. by{if k!=touched{assert(..)}} scaffolding to feed the conjuncts; needing it means a mis-set trigger to fix at the spec, not patch here — delete it and re-verify from bare reveals."}}'
    ;;
esac
exit 0
