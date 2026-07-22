# Qoder 自动 Style 检查系统

## 📋 概述

本系统会在你编辑 Verus 代码后自动检查代码样式，确保符合 VeriFlat 项目的规范。

## 🔧 工作原理

1. **文件保存追踪**: 当你保存 `src/**/*.rs` 文件时，`post-save.sh` 会记录到 `.qoder/.session-edits`
2. **自动样式检查**: 可以通过快捷键或命令手动触发 `style-check.sh`
3. **Session 隔离**: 每次新会话会清空之前的记录，只检查本次会话的修改

## 🚀 使用方法

### 方法1: 使用 VSCode 任务（推荐）

1. 按 `Ctrl+Shift+P` (Linux/Windows) 或 `Cmd+Shift+P` (Mac)
2. 输入 "Tasks: Run Task"
3. 选择 "Auto Style Check"

### 方法2: 手动运行脚本

```bash
./.qoder/hooks/style-check.sh
```

### 方法3: 安装 "Run on Save" 扩展（全自动）

1. 在 VSCode 中搜索并安装 "Run on Save" 扩展
2. 配置已保存在 `.vscode/settings.json`
3. 每次保存 `.rs` 文件会自动记录

## 📊 检查内容

当前自动检查包括：

- ✅ requires 块中是否包含注释（应该是 bare requires）
- ✅ 是否使用了 `#![all_triggers]`（应该避免）
- ✅ proof 块中的注释数量（建议保持简洁）
- ✅ `&&&` 连接符布局是否正确
- ✅ 新代码是否使用了 `@` 操作符（建议用 `.view()`）

## 📁 文件结构

```
.qoder/
├── hooks/
│   ├── post-save.sh      # 记录文件修改
│   └── style-check.sh    # 执行样式检查
├── .session-edits         # 本次会话修改的文件列表
└── .session-id            # 当前会话ID
```

## 🔍 完整检查

对于更详细的样式检查，可以使用 Claude 的完整系统：

```bash
# 查看完整的样式规范
cat .kiro/steering/verus-style.md

# 参考规范实现
cat src/kernel/implementation/syscall_alloc_quota.rs
cat src/kernel/implementation/locker_unlocker.rs
```

## 💡 提示

- 样式检查是**非阻塞**的，即使有问题也不会阻止你继续工作
- 建议在完成一个函数或模块后运行检查
- 发现 violations 时，对照规范文件和示例代码进行修改
- 所有修改会在 git 中标记，方便对比

## ⚙️ 自定义

如需添加更多检查规则，编辑 `.qoder/hooks/style-check.sh` 文件。
