---
name: feedback_verus_struct_literal_parens
description: Verus ensures/requires struct literals must be wrapped in parentheses
---

Verus 的 ensures/requires 子句中，struct literal（如 `LockId{...}`, `RwLockState::Write{...}`）必须用括号包裹为 `(LockId{...})`，否则编译报错 `struct literals are not allowed here`。

**Fix:** 在 struct 字面量前后添加圆括号。注意：IDE 代码分析器可能误报为语法错误，即使已加括号——忽略它，Verus verifier 会正确接受。
