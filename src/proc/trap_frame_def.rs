use vstd::prelude::*;
use crate::*;
verus! {
/// The trap-frame slot of a thread page: the address of the saved `Registers` and, while the thread is not RUNNING, the
/// parked sealed permission to them.
pub struct TrapFrameSlot {
    addr: usize,
    perm: Tracked<Option<TrapFramePerm>>,
}

impl TrapFrameSlot {
    pub closed spec fn spec_addr(&self) -> usize { self.addr }

    /// The slot holds the frame permission at `addr()`.
    pub closed spec fn is_some(&self) -> bool { self.perm.view() is Some && self.perm.view()->Some_0.addr() == self.addr }

    pub open spec fn is_none(&self) -> bool { !self.is_some() }

    /// The parked registers, if the slot holds the frame permission.
    pub closed spec fn view(&self) -> Option<Registers> { if self.is_some() { Some(self.perm.view()->Some_0.value()) } else { None } }

    /// The empty slot of the frame at `addr`.
    pub fn new_empty(addr: usize) -> (ret: Self)
        ensures
            ret.is_none(),
            ret.addr() == addr,
    {
        Self { addr, perm: Tracked(None) }
    }

    #[verifier(when_used_as_spec(spec_addr))]
    pub fn addr(&self) -> (ret: usize)
        ensures
            ret == self.addr()
    {
        self.addr
    }

    pub fn take(&mut self) -> (ret: (usize, Tracked<TrapFramePerm>))
        requires
            old(self).is_some(),
        ensures
            final(self).is_none(),
            final(self).addr() == old(self).addr(),
            ret.0 == old(self).addr(),
            ret.1.view().addr() == old(self).addr(),
            ret.1.view().value() == old(self).view()->Some_0,
    {
        let tracked perm = self.perm.borrow_mut().tracked_take();
        (self.addr, Tracked(perm))
    }

    pub fn put(&mut self, frame: Tracked<TrapFramePerm>)
        requires
            old(self).addr() == frame.view().addr(),
        ensures
            final(self).is_some(),
            final(self).addr() == old(self).addr(),
            final(self).view() == Some(frame.view().value()),
    {
        let Tracked(frame) = frame;
        self.perm = Tracked(Some(frame));
    }
}

// This frame is the whole per-thread user register state the kernel model knows: the general registers, the error code,
// and the interrupt frame (rip, cs, rflags, rsp, ss). User floating point (x87/MMX/SSE) is switched off: the boot glue sets
// CR0.TS|MP on every cpu and never clears it, so a user FP instruction faults instead of leaking state between threads.
// TODO: support floating point later by saving/restoring the FP state per thread at a switch and modelling it. The fs/gs
// base and the ds/es/fs/gs selectors are still neither saved per thread nor modelled (see the TODO in
// boot/kernel/src/syscalls/mod.rs).
/// Registers passed to the ISR.
#[repr(C, align(8))]
#[derive(Clone, Copy, Debug)]
pub struct Registers {
    pub r15: u64,
    pub r14: u64,
    pub r13: u64,
    pub r12: u64,
    pub rbp: u64,
    pub rbx: u64,
    pub r11: u64,
    pub r10: u64,
    pub r9: u64,
    pub r8: u64,
    pub rcx: u64,
    pub rdx: u64,
    pub rsi: u64,
    pub rdi: u64,
    pub rax: u64,
    // Original interrupt stack frame
    pub error_code: u64,
    pub rip: u64,
    pub cs: u64,
    pub flags: u64,
    pub rsp: u64,
    pub ss: u64,
}

impl Registers {
    pub const fn zeroed() -> Self {
        Self {
            r15: 0, r14: 0, r13: 0, r12: 0, rbp: 0, rbx: 0, r11: 0, r10: 0, r9: 0, r8: 0, rcx: 0, rdx: 0, rsi: 0, rdi: 0, rax: 0, error_code: 0, rip: 0, cs: 0, flags: 0, rsp: 0, ss: 0,
        }
    }
}
} // verus!
