// 这是一个测试文件，用于演示style检查系统
// 故意包含一些样式问题来测试检测功能

use vstd::prelude::*;

verus! {

// 测试函数 - 包含一些样式问题
proof fn test_proof_with_issues(
    x: int,
)
    requires
        x > 0, // 这行注释在requires中，应该被检测到
        x < 100,
    ensures
        x >= 0,
{
    proof {
        // 这是第一行注释
        // 这是第二行注释  
        // 这是第三行注释
        // 这是第四行注释 - 超过了3行的阈值
        assert(x > 0);
    }
}

// 另一个测试 - 使用了all_triggers
pub open spec fn test_spec_with_all_triggers(s: Seq<int>) -> bool {
    forall|i: int| #![all_triggers] 0 <= i < s.len() ==> s[i] >= 0
}

// 正确的写法示例
pub open spec fn test_spec_correct(s: Seq<int>) -> bool {
    forall|i: int| #![auto] 0 <= i < s.len() ==> s[i] >= 0
}

} // verus!
