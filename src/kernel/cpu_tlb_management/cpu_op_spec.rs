use vstd::prelude::*;
use crate::*;

verus! {
/// Every cpu's running state agrees with its scheduling state, its lock, and where its kernel-call permission sits: a cpu
/// is inside a kernel step exactly when its permission has left the cpu object, and then it write-holds its own lock.
#[verifier::opaque]
pub open spec fn cpu_op_wf(cpu_op: Seq<CpuOpState>, cpu_arr: CpuLockedArray) -> bool {
    forall|cpu_id: CpuId|
        #![trigger cpu_op[cpu_id as int]]
        #![trigger cpu_arr.spec_index(cpu_id).view().view().view()]
        index_valid(NUM_CPUS, cpu_id) ==> {
            let lock = cpu_arr.spec_index(cpu_id).view();
            let state = lock.view().view().state;
            let perm = lock.view().kernel_call_perm();
            let op = cpu_op[cpu_id as int];
            &&& op is InStep ==> lock.wlocked() && lock.view_ghost() == Some(cpu_id)
            &&& (op is InStep) == (perm is None)
            // A cpu only holds its own kernel-call permission.
            &&& perm is Some ==> perm == Some(cpu_id)
            // Op -> state.
            &&& (op is User || op is Trap) ==> state is Running
            &&& op is Idle ==> state is Idle || (state is Running && lock.being_killed())
            &&& op is Off ==> state is Off
            // State -> op.
            &&& state is Running ==> op is User || op is Trap || op is InStep || (op is Idle && lock.being_killed())
            &&& state is Idle ==> op is Idle || op is InStep
            &&& state is Off ==> op is Off || op is InStep
        }
}

/// The running-state facts of cpu `cpu_id`.
pub proof fn cpu_op_wf_at(cpu_op: Seq<CpuOpState>, cpu_arr: CpuLockedArray, cpu_id: CpuId)
    requires
        cpu_op_wf(cpu_op, cpu_arr),
        index_valid(NUM_CPUS, cpu_id),
    ensures
        ({
            let lock = cpu_arr.spec_index(cpu_id).view();
            let state = lock.view().view().state;
            let perm = lock.view().kernel_call_perm();
            let op = cpu_op[cpu_id as int];
            &&& op is InStep ==> lock.wlocked() && lock.view_ghost() == Some(cpu_id)
            &&& (op is InStep) == (perm is None)
            &&& perm is Some ==> perm == Some(cpu_id)
            &&& (op is User || op is Trap) ==> state is Running
            &&& op is Idle ==> state is Idle || (state is Running && lock.being_killed())
            &&& op is Off ==> state is Off
            &&& state is Running ==> op is User || op is Trap || op is InStep || (op is Idle && lock.being_killed())
            &&& state is Idle ==> op is Idle || op is InStep
            &&& state is Off ==> op is Off || op is InStep
        }),
{ reveal(cpu_op_wf); }
}
