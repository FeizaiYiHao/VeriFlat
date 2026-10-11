#![feature(adt_const_params)]
#![no_std]

use vstd::prelude::*;
use veriflat_kernel_core::*;

pub mod syscall_schedule;
pub mod rebalance_pull;

verus! {
global size_of usize == 8;
}
