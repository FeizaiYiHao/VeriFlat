#!/usr/bin/env bash
# style-gate.sh — HARD GATE: block "done" while session-edited src/**/*.rs
# has not passed the style check since its last edit.
# In Claude this was a Stop hook. In Qoder, run it manually or wire to a
# VSCode task before considering work complete.
#
# Gate mechanics:
#   - ledger   = .qoder/.session-edits  (repo-relative paths this session edited)
#   - sentinel = .qoder/.style-checked  (written by /style-check on a clean pass:
#                one "<git-hash-object><TAB><path>" line per reviewed dirty file)
#   - block    if some ledger file is still dirty AND its current content hash
#              does NOT match the hash certified in the sentinel AND the file is
#              newer than the sentinel (or sentinel absent).
#   - allow    once /style-check runs clean; OR nothing session-edited is dirty;
#              OR a dirty file's content is BYTE-IDENTICAL to its certified hash.
set -euo pipefail
cd "$(git rev-parse --show-toplevel 2>/dev/null || echo .)" || exit 0

ledger=".qoder/.session-edits"
sentinel=".qoder/.style-checked"

# No ledger / empty ledger -> nothing to gate.
[ -s "$ledger" ] || { echo "PASS: no session edits recorded."; exit 0; }

# Set of paths git currently reports dirty under src/.
dirty="$(git status --porcelain -- src 2>/dev/null | sed -e 's/^...//' -e 's/.* -> //' | grep -E '\.rs$' || true)"
[ -z "$dirty" ] && { echo "PASS: no dirty src/**/*.rs files."; exit 0; }

# The content hash certified for a path at the last clean /style-check.
certified_hash() {
  [ -f "$sentinel" ] || return 0
  local sh sp
  while IFS=$'\t' read -r sh sp; do
    [ "$sp" = "$1" ] && { printf '%s' "$sh"; return 0; }
  done < "$sentinel"
}

need_check=""
while IFS= read -r f; do
  [ -z "$f" ] && continue
  printf '%s\n' "$dirty" | grep -qxF "$f" || continue
  cur="$(git hash-object "$f" 2>/dev/null || true)"
  cert="$(certified_hash "$f" || true)"
  [ -n "$cur" ] && [ "$cur" = "$cert" ] && continue
  if [ ! -f "$sentinel" ] || [ "$f" -nt "$sentinel" ]; then
    need_check="$f"
    break
  fi
done < "$ledger"

if [ -z "$need_check" ]; then
  echo "PASS: all session-edited files are style-certified."
  exit 0
fi

echo "BLOCKED: $need_check has not passed /style-check since its last edit."
echo "Run /style-check to review and certify, then re-run this gate."
exit 1
