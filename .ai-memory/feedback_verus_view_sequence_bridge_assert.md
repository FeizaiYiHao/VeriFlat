---
name: feedback_verus_view_sequence_bridge_assert
description: When view() and underlying sequence values don't auto-equate in solver, add explicit forall bridge assert
---

在 Verus 中，当 `view()` 与底层序列（如 `value_list`）的元素值等价性未被 solver 自动识别时，应显式添加 forall 断言进行桥接：

```rust
assert(forall|i| value_list@[i] == view()[i]);
```

该断言能有效对齐 trigger，使后续基于 view 的推理（如 `lemma_len_subset`）得以成立。这是 trigger 未触发问题的又一实例（见 feedback_cost_wall_is_usually_a_bug）。
