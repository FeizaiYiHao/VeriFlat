//! The hardware register state of every cpu.
//!
//! TCB model of `CpuRegsArray`. Entry `cpu_id` is the general-purpose and interrupt-frame register state of cpu `cpu_id`.
//! The kernel never writes it: besides `new_boot` at init, only the trap-handler env events change it, user code through
//! `kernel_k_regs_changed`, trap entry, which leaves it unconstrained, through `kernel_k_trap_enter`, and trap return, which
//! loads the frame of the thread the cpu runs, through `kernel_k_trap_return`.
use vstd::prelude::*;
use crate::*;

verus! {
/// Hardware registers of every cpu, written only by `new_boot` and the trap-handler env events.
pub tracked struct CpuRegsArray {
    ghost regs: Seq<Registers>,
}

impl CpuRegsArray {
    pub closed spec fn view(&self) -> Seq<Registers> { self.regs }

    /// TCB: boot value; init only.
    #[verifier::external_body]
    pub(crate) proof fn new_boot(regs: Seq<Registers>) -> (tracked ret: Self)
        ensures
            ret.view() == regs,
    { unimplemented!() }
}
}
