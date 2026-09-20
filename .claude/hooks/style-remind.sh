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
    printf '%s' '{"hookSpecificOutput":{"hookEventName":"PreToolUse","additionalContext":"VeriFlat Verus style — read AGENTS.md and .codex/skills/veriflat-proof/references/style-and-discipline.md before writing. Use the hand-edited src/kernel/implementation/syscall_alloc_quota/ directory as a style reference. Keep proof facts and reveals narrowly scoped, preserve deliberate triggers, and follow the build skill for verification and performance decisions."}}'
    ;;
esac
exit 0
