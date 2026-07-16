#!/usr/bin/env bash
# PostToolUse (Write|Edit) hook: record every src/**/*.rs file that THIS session
# actually changed into a per-session ledger, so the Stop gate and /style-check
# only ever consider code this session touched (never pre-existing dirty files).
#
# PostToolUse fires ONLY on a successful tool call, so a file lands in the ledger
# only when its edit truly went through. Session scoping: we stash the current
# session_id in .claude/.session-id; when it changes, the ledger is a new
# session's, so we truncate it and drop the clean-check sentinel (fresh session
# starts unchecked). Pure grep/sed — no jq/python (unavailable / sandbox-flaky).
set -euo pipefail
input="$(cat)"
cd "${CLAUDE_PROJECT_DIR:-.}" 2>/dev/null || exit 0

# Extract the file_path VALUE (not the whole JSON) so edit CONTENT that mentions
# a src/*.rs path can't trigger a false positive. Same idiom as style-remind.sh.
fp="$(printf '%s' "$input" | sed -n 's/.*"file_path"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p')"
sid="$(printf '%s' "$input" | sed -n 's/.*"session_id"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p')"

# Only track Verus source under src/.
case "$fp" in
  */src/*.rs | src/*.rs) ;;
  *) exit 0 ;;
esac

ledger=".claude/.session-edits"
stored_sid=".claude/.session-id"
sentinel=".claude/.style-checked"

# New session (session_id changed) -> this ledger belongs to a prior session.
# Reset it and drop the clean-check sentinel so the fresh session must re-check.
# Guard on non-empty sid: an unparseable id must NOT wipe a live ledger.
if [ -n "$sid" ]; then
  cur=""
  [ -f "$stored_sid" ] && cur="$(cat "$stored_sid" 2>/dev/null || true)"
  if [ "$cur" != "$sid" ]; then
    : > "$ledger"
    printf '%s\n' "$sid" > "$stored_sid"
    rm -f "$sentinel"
  fi
fi

# Record a repo-relative path (cwd is the project root) so the gate's `-nt` test
# and /style-check's `git diff -- <path>` both resolve it. Dedup on append.
rel="$fp"
case "$fp" in
  "$PWD"/*) rel="${fp#"$PWD"/}" ;;
esac
touch "$ledger"
grep -qxF "$rel" "$ledger" 2>/dev/null || printf '%s\n' "$rel" >> "$ledger"
exit 0
