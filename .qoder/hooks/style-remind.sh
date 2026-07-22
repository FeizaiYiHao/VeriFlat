#!/usr/bin/env bash
# style-remind.sh — VeriFlat Verus style reminder.
# In Claude this was a PreToolUse hook injected before Write|Edit on src/**/*.rs.
# In Qoder there is no native hook system; this script can be wired to a VSCode
# task or run manually before an editing session to print the style reminder.
# The canonical style reference is .kiro/steering/verus-style.md and the files:
#   - src/kernel/implementation/syscall_alloc_quota.rs (syscall_alloc_quota_4k)
#   - src/kernel/implementation/locker_unlocker.rs (wlock_cpu, wunlock_quota_4k)
set -euo pipefail

cat <<'EOF'
VeriFlat Verus style — match .kiro/steering/verus-style.md and the canonical
files (syscall_alloc_quota_4k + the locker_unlocker.rs wrappers); open the
nearest LIVE sibling and copy its shape.

Tells:
  - bare requires (no // comments)
  - single-line // ---- ---- banners ONLY in ensures and inv() re-establishment
  - comment-free proof {} blocks
  - #![auto] on shallow framing foralls, hand #![trigger] on deep ones,
    NEVER #![all_triggers]
  - spec files hold only specs
  - #[verifier::spinoff_prover] on new wrappers/lemmas is Xiangdong's call

inv() rebuild closes from a few reveal(...)s + narrow lemma calls (see
wlock_quota_4k) — do NOT add assert forall|..| ..==old(self).. by{if
k!=touched{assert(..)}} scaffolding to feed the conjuncts; needing it means
a mis-set trigger to fix at the spec, not patch here — delete it and re-verify
from bare reveals.
EOF
