#!/usr/bin/env bash
# Stop hook: HARD GATE, scoped to THIS session's edits. Blocks stopping while any
# src/**/*.rs that this session actually changed (recorded by style-record.sh in
# .claude/.session-edits) is still dirty AND its CONTENT differs from what the
# last clean style check certified. Pre-existing dirty files this session never
# touched are ignored.
#
# Gate mechanics:
#   - ledger  = .claude/.session-edits  (repo-relative paths this session edited)
#   - sentinel= .claude/.style-checked  (written by /style-check on a clean pass:
#               one "<git-hash-object><TAB><path>" line per reviewed dirty file).
#   - block   if some ledger file is still dirty in git AND its current content
#             hash does NOT match the hash certified for it in the sentinel AND
#             (sentinel missing OR that file is newer than the sentinel).
#   - allow   once /style-check runs clean (records current hashes + refreshes the
#             sentinel mtime); OR if nothing session-edited is still dirty; OR if a
#             dirty file's content is BYTE-IDENTICAL to its certified hash. That
#             last case is the important one: profiling/measurement that mutates a
#             file and then restores it byte-for-byte (mtime bumped, content same)
#             must NOT re-trip the gate — the certified content was already
#             reviewed. Pure git — no jq/python (unavailable/sandbox-flaky).
set -euo pipefail
cd "${CLAUDE_PROJECT_DIR:-.}" 2>/dev/null || exit 0

ledger=".claude/.session-edits"
sentinel=".claude/.style-checked"

# No ledger / empty ledger -> this session edited no src .rs. Nothing to gate.
[ -s "$ledger" ] || exit 0

# Set of paths git currently reports dirty under src/ (staged or unstaged).
dirty="$(git status --porcelain -- src 2>/dev/null | sed -e 's/^...//' -e 's/.* -> //' | grep -E '\.rs$' || true)"
[ -z "$dirty" ] && exit 0

# The content hash certified for a path at the last clean /style-check, or empty.
# Sentinel lines are "<git-hash-object><TAB><path>"; a legacy empty/touch-only
# sentinel yields no match (every file falls back to the mtime signal, as before).
certified_hash() {
  [ -f "$sentinel" ] || return 0
  local sh sp
  while IFS=$'\t' read -r sh sp; do
    [ "$sp" = "$1" ] && { printf '%s' "$sh"; return 0; }
  done < "$sentinel"
}

# A ledger file gates iff it is still dirty AND its content differs from the last
# certified content AND it is newer than the sentinel (or the sentinel is absent).
# First such file blocks; if none, the check is current.
need_check=""
while IFS= read -r f; do
  [ -z "$f" ] && continue
  printf '%s\n' "$dirty" | grep -qxF "$f" || continue          # not dirty -> skip
  # Byte-identical to the last certified content (e.g. profiling restored it)? OK.
  cur="$(git hash-object "$f" 2>/dev/null || true)"
  cert="$(certified_hash "$f" || true)"
  [ -n "$cur" ] && [ "$cur" = "$cert" ] && continue
  # Otherwise fall back to the mtime signal: edited since last check -> block.
  if [ ! -f "$sentinel" ] || [ "$f" -nt "$sentinel" ]; then
    need_check="$f"
    break
  fi
done < "$ledger"

[ -z "$need_check" ] && exit 0

printf '%s' '{"decision":"block","reason":"This session changed src/**/*.rs that has not passed the style check since its last edit. Run the /style-check slash command — it reviews ONLY the files this session touched (.claude/.session-edits) against verus-style.md and the canonical files (syscall_alloc_quota_4k, the locker_unlocker.rs wrappers), and on a clean pass records their certified content hashes to .claude/.style-checked to clear this gate — then stop again. If you are mid-task and still editing, keep working; this only gates stopping."}'
exit 0
