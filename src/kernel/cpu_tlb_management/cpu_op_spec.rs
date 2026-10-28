use vstd::prelude::*;
use crate::*;

verus! {
/// Every cpu's running state agrees with its scheduling state, its lock, and where its kernel-call permission sits: a cpu
/// is inside a kernel step exactly when its permission has left the cpu object, and then it write-holds its own lock.
#[verifier::opaque]
pub open spec fn cpu_op_wf(cpu_op: Seq<CpuOpState>, cpus: CpuLockedArray) -> bool {
    forall|c: CpuId|
        #![trigger cpu_op[c as int]]
        #![trigger cpus.spec_index(c).view().view().view()]
        index_valid(NUM_CPUS, c) ==> {
            let lock = cpus.spec_index(c).view();
            let state = lock.view().view().state;
            let perm = lock.view().kernel_call_perm();
            let op = cpu_op[c as int];
            &&& op is InStep ==> lock.wlocked() && lock.view_ghost() == Some(c)
            &&& (op is InStep) == (perm is None)
            &&& perm is Some ==> perm == Some(c)
            &&& op is User || op is Trap ==> state is Running
            &&& op is Idle ==> state is Idle || (state is Running && lock.being_killed())
            &&& op is Off ==> state is Off
            &&& state is Running ==> op is User || op is Trap || op is InStep || (op is Idle && lock.being_killed())
            &&& state is Idle ==> op is Idle || op is InStep
            &&& state is Off ==> op is Off || op is InStep
        }
}

/// The running-state facts of cpu `c`.
pub proof fn cpu_op_wf_at(cpu_op: Seq<CpuOpState>, cpus: CpuLockedArray, c: CpuId)
    requires
        cpu_op_wf(cpu_op, cpus),
        index_valid(NUM_CPUS, c),
    ensures
        ({
            let lock = cpus.spec_index(c).view();
            let state = lock.view().view().state;
            let perm = lock.view().kernel_call_perm();
            let op = cpu_op[c as int];
            &&& op is InStep ==> lock.wlocked() && lock.view_ghost() == Some(c)
            &&& (op is InStep) == (perm is None)
            &&& perm is Some ==> perm == Some(c)
            &&& op is User || op is Trap ==> state is Running
            &&& op is Idle ==> state is Idle || (state is Running && lock.being_killed())
            &&& op is Off ==> state is Off
            &&& state is Running ==> op is User || op is Trap || op is InStep || (op is Idle && lock.being_killed())
            &&& state is Idle ==> op is Idle || op is InStep
            &&& state is Off ==> op is Off || op is InStep
        }),
{ reveal(cpu_op_wf); }
}
