#![feature(adt_const_params)]
#![no_std]

use vstd::prelude::*;

use veriflat_kernel_core::*;

pub mod syscall_alloc_quota;

verus! {
global size_of usize == 8;
}
