#!/usr/bin/env bash
# 自动Style检查脚本 - 增强版
# 检查本次session修改或当前工作区有改动的src/**/*.rs文件
set -euo pipefail

cd "${QODER_PROJECT_DIR:-.}" 2>/dev/null || exit 0

ledger=".qoder/.session-edits"
style_guide=".kiro/steering/verus-style.md"

echo "=========================================="
echo "  VeriFlat Auto Style Check"
echo "=========================================="
echo ""

# 收集需要检查的文件
declare -A files_to_check

# 1. 从ledger读取本次session修改的文件
if [ -s "$ledger" ]; then
  while IFS= read -r f; do
    [ -z "$f" ] && continue
    files_to_check["$f"]=1
  done < "$ledger"
fi

# 2. 从git status获取所有modified的.rs文件
while IFS= read -r line; do
  file=$(echo "$line" | sed 's/^...//')
  [[ "$file" == *.rs ]] && files_to_check["$file"]=1
done < <(git status --porcelain -- src 2>/dev/null || true)

if [ ${#files_to_check[@]} -eq 0 ]; then
  echo "✓ 没有需要检查的文件"
  echo "=========================================="
  exit 0
fi

echo "📋 检测到以下文件需要检查:"
for f in "${!files_to_check[@]}"; do
  echo "  - $f"
done
echo ""

echo "🔍 开始样式检查..."
echo ""

violations=0
violation_details=""

for file in "${dirty_files[@]}"; do
  echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  echo "📄 检查: $file"
  echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  
  # 获取该文件的diff
  diff_output=$(git diff HEAD -- "$file" 2>/dev/null || true)
  
  if [ -z "$diff_output" ]; then
    echo "  ✓ 无未提交的更改"
    continue
  fi
  
  # === 样式检查规则 ===
  
  file_violations=0
  
  # 检查1: requires块中是否有注释
  if echo "$diff_output" | grep -A 20 "^+.*requires" | grep -q "^+.*//"; then
    echo "  ⚠️  requires块中包含注释（应该是bare requires）"
    file_violations=$((file_violations + 1))
  fi
  
  # 检查2: 是否有#![all_triggers]
  if echo "$diff_output" | grep -q "#!\[all_triggers\]"; then
    echo "  ❌ 使用了#![all_triggers]（应该避免）"
    file_violations=$((file_violations + 1))
  fi
  
  # 检查3: proof块中的注释数量
  proof_comments=$(echo "$diff_output" | grep -A 5 "^+.*proof {" | grep "^+.*//" | wc -l || echo "0")
  if [ "$proof_comments" -gt 3 ]; then
    echo "  ⚠️  proof块中有较多注释（建议保持简洁）"
    file_violations=$((file_violations + 1))
  fi
  
  # 检查4: &&&布局是否正确（&&&应该在独立行）
  bad_ampersand=$(echo "$diff_output" | grep "^+" | grep -v "^+++" | grep "[^& ]&&&[^&]" | wc -l || echo "0")
  if [ "$bad_ampersand" -gt 0 ]; then
    echo "  ⚠️  &&&连接符可能不在独立行"
    file_violations=$((file_violations + 1))
  fi
  
  # 检查5: 新代码是否使用@操作符（应该用.view()）
  new_at_usage=$(echo "$diff_output" | grep "^+" | grep -v "^+++" | grep "@" | grep -v "@@" | grep -v "//@Xiangdong" | wc -l || echo "0")
  if [ "$new_at_usage" -gt 0 ]; then
    echo "  ⚠️  新代码使用了@操作符（建议用.view()）"
    file_violations=$((file_violations + 1))
  fi
  
  # 检查6: 是否有assume语句（可能是证明缺口）
  assume_count=$(echo "$diff_output" | grep "^+.*assume(" | wc -l || echo "0")
  if [ "$assume_count" -gt 0 ]; then
    echo "  ⚠️  发现 $assume_count 个assume语句（可能需要完善证明）"
    file_violations=$((file_violations + 1))
  fi
  
  if [ $file_violations -eq 0 ]; then
    echo "  ✓ 通过基本样式检查"
  else
    violations=$((violations + file_violations))
    echo "  📊 发现 $file_violations 个问题"
  fi
  
  echo ""
done

echo "=========================================="
if [ $violations -eq 0 ]; then
  echo "✅ 样式检查通过！"
  echo ""
  echo "💡 提示: 可以运行 ./verify.sh 进行完整验证"
else
  echo "❌ 发现 $violations 个样式问题"
  echo ""
  echo "💡 建议："
  echo "  1. 查看样式规范: $style_guide"
  echo "  2. 参考规范实现:"
  echo "     - src/kernel/implementation/syscall_alloc_quota.rs"
  echo "     - src/kernel/implementation/locker_unlocker.rs"
  echo "  3. 运行完整检查: .claude/commands/style-check.md"
fi
echo "=========================================="

exit $violations
