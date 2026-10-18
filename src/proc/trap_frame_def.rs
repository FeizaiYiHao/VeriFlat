use vstd::prelude::*;
verus! {
pub struct TrapFrameOption {
    pub reg: Registers,
    pub exist: bool,
}

impl TrapFrameOption {
    pub open spec fn spec_is_some(&self) -> bool { self.exist }
    pub open spec fn spec_is_none(&self) -> bool { self.exist == false }

    pub open spec fn get_some_0(&self) -> &Registers
        recommends
            self.is_some(),
    {
        &self.reg
    }

    #[verifier(when_used_as_spec(spec_is_some))]
    pub fn is_some(&self) -> (ret: bool)
        ensures
            ret == self.is_some(),
    {
        self.exist
    }

    #[verifier(when_used_as_spec(spec_is_none))]
    pub fn is_none(&self) -> (ret: bool)
        ensures
            ret == self.is_none(),
    {
        self.exist == false
    }

    pub fn set_self(&mut self, src: &Registers)
        ensures
            final(self).is_some(),
            final(self).get_some_0() =~= src,
    {
        self.exist = true;
        self.reg = *src;
    }

    pub fn set_dst(&self, dst: &mut Registers)
        requires
            self.is_some(),
        ensures
            *final(dst) =~= *self.get_some_0(),
    {
        *dst = self.reg;
    }

    pub fn set_to_none(&mut self)
        ensures
            final(self).is_none(),
    {
        self.exist = false;
    }

    pub fn zeroed_none() -> (ret: Self)
        ensures
            ret.is_none(),
    {
        Self { reg: Registers::zeroed(), exist: false }
    }
}

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
