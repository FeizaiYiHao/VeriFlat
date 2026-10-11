#![feature(adt_const_params)]
#![no_std]

use vstd::prelude::*;

use veriflat_kernel_core::*;
use veriflat_map_4k::*;

pub mod syscall_ipc;

verus! {
global size_of usize == 8;
}
