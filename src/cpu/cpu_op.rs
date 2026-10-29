//! Per-cpu running state and the per-cpu kernel-call permission.
//!
//! TCB model of `CpuOpState`. A cpu runs with its interrupt flag clear exactly while it is `InStep`; every other state
//! runs with IF=1. `Off` is a cpu halted in `wait_until_online`; `Idle` is the idle loop, which halts with a plain
//! `hlt`; `User` is ring 3; `Trap` is the IF=1 kernel segment running without the own cpu lock (User to Trap at
//! `syscall` and the interrupt gates, Trap to User at `sysretq`/`iretq`, Trap to Idle when `restore_frame` diverts on
//! `running_to_idle_pending` or CpuIdle); `InStep` is a cpu that write-holds its own cpu lock with its own
//! `KernelCallPerm` in its `LocalContext`. `CpuLockedArray::wlock_own_cpu_enter_step` enters it, clearing IF when the
//! lock is granted, and `CpuLockedArray::exit_step_wunlock_own_cpu` leaves it, setting IF after the release; they are
//! called by `KernelK::wlock_own_cpu` and `KernelK::wunlock_own_cpu`. The only writers are that enter and exit,
//! `ipi_remote_running_to_idle_raw` (to Idle), `ipi_wake` (to Idle), and the boot trampolines, which the trap U steps
//! and the step-boundary havoc model.
use vstd::prelude::*;
use crate::*;

verus! {
pub ghost enum CpuOpState {
    Off,
    Idle,
    User,
    Trap,
    InStep,
}

/// The resting state a cpu returns to when it leaves a kernel step: Running to Trap, Idle to Idle, Off to Off.
pub open spec fn cpu_op_after_step(state: CpuState) -> CpuOpState {
    match state {
        CpuState::Running => CpuOpState::Trap,
        CpuState::Idle => CpuOpState::Idle,
        CpuState::Off => CpuOpState::Off,
    }
}

/// Running state of every cpu, written only by the TCB primitives of this module.
pub tracked struct CpuOpArray {
    ghost ops: Seq<CpuOpState>,
}

impl CpuOpArray {
    pub closed spec fn view(&self) -> Seq<CpuOpState> { self.ops }

    /// TCB: the running state of every cpu when boot hands the machine to the kernel; init only.
    #[verifier::external_body]
    pub(crate) proof fn new_boot(ops: Seq<CpuOpState>) -> (tracked ret: Self)
        ensures
            ret.view() == ops,
    { unimplemented!() }

    /// TCB: cpu `cpu_id` enters a kernel step by write-locking its own cpu in `CpuLockedArray::wlock_own_cpu_enter_step`.
    #[verifier::external_body]
    pub(crate) proof fn enter_step(tracked &mut self, cpu_id: CpuId)
        requires
            index_valid(NUM_CPUS, cpu_id),
        ensures
            final(self).view() == old(self).view().update(cpu_id as int, CpuOpState::InStep),
    { unimplemented!() }

    /// TCB: cpu `cpu_id` leaves its kernel step in `CpuLockedArray::exit_step_wunlock_own_cpu` and rests in the state its
    /// scheduling state implies.
    #[verifier::external_body]
    pub(crate) proof fn exit_step(tracked &mut self, cpu_id: CpuId, state: CpuState)
        requires
            index_valid(NUM_CPUS, cpu_id),
        ensures
            final(self).view() == old(self).view().update(cpu_id as int, cpu_op_after_step(state)),
    { unimplemented!() }

    /// TCB: the IPI of `ipi_remote_running_to_idle_raw` moves remote cpu `cpu_id` to its idle loop; called only there.
    #[verifier::external_body]
    pub(crate) proof fn ipi_running_to_idle(tracked &mut self, cpu_id: CpuId)
        requires
            index_valid(NUM_CPUS, cpu_id),
        ensures
            final(self).view() == old(self).view().update(cpu_id as int, CpuOpState::Idle),
    { unimplemented!() }

    /// TCB: the wake-up IPI of `ipi_wake` releases remote cpu `cpu_id` from `wait_until_online` into its idle loop;
    /// called only there.
    #[verifier::external_body]
    pub(crate) proof fn woken(tracked &mut self, cpu_id: CpuId)
        requires
            index_valid(NUM_CPUS, cpu_id),
        ensures
            final(self).view() == old(self).view().update(cpu_id as int, CpuOpState::Idle),
    { unimplemented!() }
}

/// Permission to run kernel code on, and to interrupt, cpu `cpu_id`. One per cpu, created at boot.
pub tracked struct KernelCallPerm {
    ghost cpu_id: CpuId,
}

impl KernelCallPerm {
    pub closed spec fn cpu_id(&self) -> CpuId { self.cpu_id }

    /// TCB: the single permission of cpu `cpu_id`, created when boot builds that cpu; init only.
    #[verifier::external_body]
    pub(crate) proof fn new_boot(cpu_id: CpuId) -> (tracked ret: Self)
        ensures
            ret.cpu_id() == cpu_id,
    { unimplemented!() }
}
}
