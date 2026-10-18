#![feature(adt_const_params)]
#![no_std]

use vstd::prelude::*;

use veriflat_kernel_core::*;
use veriflat_alloc_page::reclaim_killed_husk::{take_over_dangling_caller, reclaim_killed_husk};
use veriflat_map_4k::*;

pub mod syscall_ipc;

verus! {
global size_of usize == 8;
}
