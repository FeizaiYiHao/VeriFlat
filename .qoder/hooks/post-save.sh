#!/usr/bin/env bash
# Post-save hook: 当保存 src/**/*.rs 文件时，记录到 session ledger
# 用于后续自动触发 style 检查
set -euo pipefail

cd "${QODER_PROJECT_DIR:-.}" 2>/dev/null || exit 0

# 从参数获取文件路径（VSCode会传递保存的文件路径）
fp="${1:-}"

# 只追踪 Verus 源代码
case "$fp" in
  */src/*.rs | src/*.rs) ;;
  *) exit 0 ;;
esac

ledger=".qoder/.session-edits"
stored_sid=".qoder/.session-id"

# 生成简单的session ID（使用时间戳+PID）
sid="session-$(date +%s)-$$"

# 新session检测
if [ -f "$stored_sid" ]; then
  cur="$(cat "$stored_sid" 2>/dev/null || true)"
  if [ "$cur" != "$sid" ]; then
    : > "$ledger"
    printf '%s\n' "$sid" > "$stored_sid"
  fi
else
  printf '%s\n' "$sid" > "$stored_sid"
fi

# 记录相对路径（去重）
rel="$fp"
case "$fp" in
  "$PWD"/*) rel="${fp#"$PWD"/}" ;;
esac

touch "$ledger"
grep -qxF "$rel" "$ledger" 2>/dev/null || printf '%s\n' "$rel" >> "$ledger"

exit 0
