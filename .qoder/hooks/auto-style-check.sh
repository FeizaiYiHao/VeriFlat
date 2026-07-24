#!/usr/bin/env bash
# auto-style-check.sh — PostToolUse hook
# Fires after every Edit (search_replace) or Write (create_file) on src/**/*.rs.
# Violations are printed to stderr so the Agent sees them immediately.
# Exit 0 always (PostToolUse cannot block); stderr is the feedback channel.
set -uo pipefail

# 1. Read stdin JSON and extract file_path via python3 (no jq dependency)
input=$(cat)
file_path=$(echo "$input" | python3 -c "import sys,json; print(json.load(sys.stdin).get('tool_input',{}).get('file_path',''))" 2>/dev/null || true)
[ -z "$file_path" ] && exit 0

# 3. Only care about src/**/*.rs
cd "$(git rev-parse --show-toplevel 2>/dev/null || echo .)" || exit 0
rel="${file_path#"$PWD"/}"
case "$rel" in
  src/*.rs) ;;
  *) exit 0 ;;
esac

# 4. Get the diff for this file
diff_output=$(git diff HEAD -- "$rel" 2>/dev/null || true)
[ -z "$diff_output" ] && exit 0

# 5. Run style checks, collect violations
violations=""

# Check 1: requires block contains comments
if echo "$diff_output" | grep -A 20 "^+.*requires" | grep -q "^+.*//"; then
  violations="${violations}⚠️  requires块中包含注释（应该是bare requires）\n"
fi

# Check 2: #![all_triggers] usage
if echo "$diff_output" | grep -q "^+.*#!\[all_triggers\]"; then
  violations="${violations}❌ 使用了#![all_triggers]（应该避免）\n"
fi

# Check 3: proof block has too many comments
proof_comments=$(echo "$diff_output" | { grep -A 5 "^+.*proof {" || true; } | { grep "^+.*//" || true; } | wc -l)
if [ "$proof_comments" -gt 3 ]; then
  violations="${violations}⚠️  proof块中有较多注释（建议保持简洁）\n"
fi

# Check 4: &&& not on its own line
bad_ampersand=$(echo "$diff_output" | grep "^+" | grep -v "^+++" | { grep "[^& ]&&&[^&]" || true; } | wc -l)
if [ "$bad_ampersand" -gt 0 ]; then
  violations="${violations}⚠️  &&&连接符可能不在独立行\n"
fi

# Check 5: @ operator usage (should use .view())
new_at_usage=$(echo "$diff_output" | grep "^+" | grep -v "^+++" | { grep "@" || true; } | grep -v "@@" | grep -v "//@Xiangdong" | wc -l)
if [ "$new_at_usage" -gt 0 ]; then
  violations="${violations}⚠️  新代码使用了@操作符（建议用.view()）\n"
fi

# Check 6: assume() statements (possible proof gap)
assume_count=$(echo "$diff_output" | { grep "^+.*assume(" || true; } | wc -l)
if [ "$assume_count" -gt 0 ]; then
  violations="${violations}⚠️  发现 $assume_count 个assume语句（可能需要完善证明）\n"
fi

# 6. Report to stderr (Agent sees this)
if [ -n "$violations" ]; then
  echo "" >&2
  echo "🎨 Style Check — $rel" >&2
  echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
  echo -e "$violations" >&2
  echo "📖 参考: .kiro/steering/verus-style.md" >&2
  echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
fi

exit 0
