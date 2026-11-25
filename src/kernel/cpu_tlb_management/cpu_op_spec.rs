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

/// A cpu inside a kernel step or Off has an empty store buffer: the LOCKed instruction that granted its own cpu lock drained
/// it, and it issues no user store until it leaves the step.
#[verifier::opaque]
pub open spec fn store_buffers_empty_in_step_or_off(cpu_op: CpuOpArray) -> bool {
    forall|c: CpuId| #![trigger cpu_op.store_buffer(c)]
        index_valid(NUM_CPUS, c) && (cpu_op.view()[c as int] is InStep || cpu_op.view()[c as int] is Off) ==> cpu_op.store_buffer(c) == Set::<PendingStore>::empty()
}

/// The store buffer of cpu `cpu_id` is empty while the cpu is inside a kernel step or Off.
pub proof fn store_buffers_empty_in_step_or_off_at(cpu_op: CpuOpArray, cpu_id: CpuId)
    requires
        store_buffers_empty_in_step_or_off(cpu_op),
        index_valid(NUM_CPUS, cpu_id),
    ensures (cpu_op.view()[cpu_id as int] is InStep || cpu_op.view()[cpu_id as int] is Off) ==> cpu_op.store_buffer(cpu_id) == Set::<PendingStore>::empty(),
{ reveal(store_buffers_empty_in_step_or_off); }
}
