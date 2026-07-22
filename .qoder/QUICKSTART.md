# Qoder 自动 Style 检查系统 - 快速开始

## ✅ 已部署完成！

你现在拥有了一个完整的自动样式检查系统。

## 🎯 三种使用方式

### 1️⃣ **最简单**: 运行快捷脚本
```bash
./check-style.sh
```
在完成proof编写后直接运行此命令。

### 2️⃣ **VSCode快捷键** (推荐)
- **Ctrl+Alt+S** - 运行样式检查（在.rs文件中）
- **Ctrl+Alt+V** - 运行完整验证

### 3️⃣ **VSCode任务菜单**
1. 按 `Ctrl+Shift+P`
2. 输入 "Tasks: Run Task"
3. 选择 "Auto Style Check"

## 📊 检查内容

系统会自动检测以下问题：

| 检查项 | 说明 | 严重程度 |
|--------|------|----------|
| requires注释 | requires块不应有注释 | ⚠️ |
| all_triggers | 避免使用#![all_triggers] | ❌ |
| proof注释 | proof块应保持简洁 | ⚠️ |
| &&&布局 | 连接符应在独立行 | ⚠️ |
| @操作符 | 新代码应用.view() | ⚠️ |
| assume语句 | 可能需要完善证明 | ⚠️ |

## 🔧 工作原理

```
保存 .rs 文件
    ↓
post-save.sh 记录到 .qoder/.session-edits
    ↓
运行 style-check.sh (手动或快捷键)
    ↓
检查样式规范并报告结果
```

## 💡 最佳实践

1. **写完一个函数后立即检查**
   ```bash
   ./check-style.sh
   ```

2. **修复问题参考规范**
   - 样式指南: `.kiro/steering/verus-style.md`
   - 示例代码: `src/kernel/implementation/syscall_alloc_quota.rs`

3. **通过后再验证**
   ```bash
   ./verify.sh
   ```

## 📁 文件说明

```
.qoder/
├── hooks/
│   ├── post-save.sh      # 自动记录文件修改
│   └── style-check.sh    # 执行样式检查
├── .session-edits         # 本次会话修改的文件
├── .session-id            # 会话ID
└── README.md              # 详细文档

check-style.sh             # 快捷启动脚本
.vscode/
├── tasks.json             # VSCode任务配置
├── keybindings.json       # 快捷键配置
└── verus.code-snippets    # 代码片段模板
```

## 🚀 进阶：完全自动化

如果想实现**保存即检查**，安装VSCode扩展：

1. 搜索并安装 **"Run on Save"** (emeraldwalk.runonsave)
2. 配置已在 `.vscode/settings.json` 中
3. 每次保存 `.rs` 文件会自动记录

## ⚙️ 自定义检查规则

编辑 `.qoder/hooks/style-check.sh` 添加新的检查规则：

```bash
# 示例：检查是否有TODO标记
if echo "$diff_output" | grep "^+.*TODO"; then
  echo "  ⚠️  发现TODO标记"
  file_violations=$((file_violations + 1))
fi
```

## 🎉 开始使用！

现在你可以：
1. 编写Verus代码
2. 保存文件
3. 按 **Ctrl+Alt+S** 检查样式
4. 修复问题
5. 运行 `./verify.sh` 验证

祝编码愉快！✨
