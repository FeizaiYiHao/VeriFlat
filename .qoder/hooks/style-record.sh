#!/usr/bin/env bash
# style-record.sh — Record src/**/*.rs files changed in this session.
# In Claude this was a PostToolUse hook that logged every successfully-edited
# src/**/*.rs into a per-session ledger (.claude/.session-edits).
# In Qoder there is no native hook; this script uses git to identify dirty
# files under src/ and records them into .qoder/.session-edits.
# Run it after an editing session (or wire to a VSCode post-save task).
set -euo pipefail
cd "$(git rev-parse --show-toplevel 2>/dev/null || echo .)" || exit 0

ledger=".qoder/.session-edits"

# Collect all dirty .rs files under src/ (staged + unstaged).
dirty="$(git status --porcelain -- src 2>/dev/null | sed -e 's/^...//' -e 's/.* -> //' | grep -E '\.rs$' || true)"
[ -z "$dirty" ] && exit 0

touch "$ledger"
while IFS= read -r f; do
  [ -z "$f" ] && continue
  grep -qxF "$f" "$ledger" 2>/dev/null || printf '%s\n' "$f" >> "$ledger"
done <<< "$dirty"
exit 0
