#![feature(adt_const_params)]

use vstd::prelude::*;
use veriflat_kernel_core::*;

pub mod syscall_schedule;

verus! {
global size_of usize == 8;
}
