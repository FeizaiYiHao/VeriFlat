#!/usr/bin/env bash
# Stop hook: HARD GATE, scoped to THIS session's edits. Blocks stopping while any
# src/**/*.rs that this session actually changed (recorded by style-record.sh in
# .claude/.session-edits) is still dirty AND has been edited since the last clean
# style check. Pre-existing dirty files this session never touched are ignored.
#
# Gate mechanics:
#   - ledger  = .claude/.session-edits  (repo-relative paths this session edited)
#   - sentinel= .claude/.style-checked  (touched by /style-check on a clean pass)
#   - block   if some ledger file is still dirty in git AND (sentinel missing OR
#             that file is newer than the sentinel — i.e. edited since last check).
#   - allow   once /style-check runs clean (touches the sentinel newer than every
#             ledger file) -> no infinite loop; or if nothing session-edited is
#             still dirty. Pure git/find — no jq/python (unavailable/sandbox-flaky).
set -euo pipefail
cd "${CLAUDE_PROJECT_DIR:-.}" 2>/dev/null || exit 0

ledger=".claude/.session-edits"
sentinel=".claude/.style-checked"

# No ledger / empty ledger -> this session edited no src .rs. Nothing to gate.
[ -s "$ledger" ] || exit 0

# Set of paths git currently reports dirty under src/ (staged or unstaged).
dirty="$(git status --porcelain -- src 2>/dev/null | sed -e 's/^...//' -e 's/.* -> //' | grep -E '\.rs$' || true)"
[ -z "$dirty" ] && exit 0

# A ledger file gates iff it is still dirty AND newer than the sentinel (or the
# sentinel is absent). First such file blocks; if none, the check is current.
need_check=""
while IFS= read -r f; do
  [ -z "$f" ] && continue
  printf '%s\n' "$dirty" | grep -qxF "$f" || continue          # not dirty -> skip
  if [ ! -f "$sentinel" ] || [ "$f" -nt "$sentinel" ]; then
    need_check="$f"
    break
  fi
done < "$ledger"

[ -z "$need_check" ] && exit 0

printf '%s' '{"decision":"block","reason":"This session changed src/**/*.rs that has not passed the style check since its last edit. Run the /style-check slash command — it reviews ONLY the files this session touched (.claude/.session-edits) against verus-style.md and the canonical files (syscall_alloc_quota_4k, the locker_unlocker.rs wrappers), and on a clean pass touches .claude/.style-checked to clear this gate — then stop again. If you are mid-task and still editing, keep working; this only gates stopping."}'
exit 0
