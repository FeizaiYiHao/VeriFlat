---
name: feedback_syscall_postcondition_models_kernel_u
description: syscall postcondition must describe KernelU (user-visible state) changes via old_u/new_u, never KernelK internals
---

syscall的postcondition必须描述KernelU（用户可见状态）的变化，使用old_u/new_u字段表达，不得描述KernelK（内核内部实现）状态变化。

**Why:** KernelK contains internal implementation details (lock state, temp caches, etc.) that are not part of the user-visible contract. The syscall boundary linearizes to a user-view step.
