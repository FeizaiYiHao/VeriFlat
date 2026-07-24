---
name: feedback_upper_container_seq_readonly_no_lock
description: upper_container_seq is read-only access — no lock needed in kernel spec
---

kernel 中对 `upper_container_seq` 的访问是只读操作，无需加锁。该规则适用于所有类似只读 spec 字段的访问场景。

**How to apply:** 在 retype 或其他 kernel 函数中读取 upper_container_seq 时跳过锁检查；新增类似只读字段时参考此安全实践。
