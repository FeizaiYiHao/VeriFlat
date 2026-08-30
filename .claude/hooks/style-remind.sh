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
    printf '%s' '{"hookSpecificOutput":{"hookEventName":"PreToolUse","additionalContext":"VeriFlat Verus style — read AGENTS.md and mirror the entire hand-edited src/kernel/implementation/syscall_alloc_quota/ directory before writing. Minimize vertical space in spec/proof/exec contracts and bodies: &&& stays with its operand, one logical contract clause per line, plain calls and tuples stay intact, and short assert-by blocks stay on one line. Rely on NLL in ordinary exec flow; explicitly end a live mutable reference only before invariant closure or for a real alias/callee conflict. Keep proof blocks comment-free; use hand triggers for deep quantifiers, never #![all_triggers]. spinoff_prover is decided only by paired wall time, never rlimit."}}'
    ;;
esac
exit 0
