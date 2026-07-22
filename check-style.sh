#!/usr/bin/env bash
# 快速启动脚本 - 在Qoder中完成proof后运行此脚本
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

echo ""
echo "🎯 VeriFlat Proof Style Checker"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# 检查是否有未保存的文件
if command -v code &> /dev/null; then
  echo "💡 提示: 确保已保存所有文件 (Ctrl+S)"
  echo ""
fi

# 运行style检查
./.qoder/hooks/style-check.sh
exit_code=$?

echo ""
if [ $exit_code -eq 0 ]; then
  echo "✨ 准备好进行下一步！"
  echo ""
  echo "可选操作:"
  echo "  • 运行完整验证: ./verify.sh"
  echo "  • 提交代码: git add -p && git commit"
else
  echo "⚠️  请先修复上述样式问题"
  echo ""
  echo "参考文档:"
  echo "  • .kiro/steering/verus-style.md"
  echo "  • src/kernel/implementation/syscall_alloc_quota.rs"
fi
echo ""

exit $exit_code
