#!/usr/bin/env bash
# Stop hook: HARD GATE. Blocks stopping while there are uncommitted changes to
# src/**/*.rs that have not been style-checked since their last edit.
#
# Gate mechanics (sentinel = .claude/.style-checked):
#   - block  if any src/**/*.rs is dirty AND (sentinel missing OR some src *.rs
#            is newer than the sentinel — i.e. edited since the last check).
#   - allow  once /style-check runs a clean pass (it `touch`es the sentinel),
#            so the sentinel is newer than every src *.rs → no infinite loop.
# Pure git/find — no jq/python (unavailable / sandbox-flaky here).
set -euo pipefail
cd "${CLAUDE_PROJECT_DIR:-.}" 2>/dev/null || exit 0

# Nothing dirty under src/ → nothing to gate.
dirty="$(git status --porcelain -- src 2>/dev/null | grep -E '\.rs$' || true)"
[ -z "$dirty" ] && exit 0

sentinel=".claude/.style-checked"
if [ -f "$sentinel" ] && [ -z "$(find src -name '*.rs' -newer "$sentinel" 2>/dev/null | head -1)" ]; then
  # Sentinel exists and no src .rs is newer → style-check is current. Allow.
  exit 0
fi

printf '%s' '{"decision":"block","reason":"Uncommitted src/**/*.rs changes have not passed the style check since their last edit. Run the /style-check slash command — it reviews the diff against verus-style.md and the canonical files (syscall_alloc_quota_4k, the locker_unlocker.rs wrappers), and on a clean pass touches .claude/.style-checked to clear this gate — then stop again. If you are mid-task and still editing, keep working; this only gates stopping."}'
exit 0
