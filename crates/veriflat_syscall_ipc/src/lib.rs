#![feature(adt_const_params)]

use vstd::prelude::*;

pub use veriflat_kernel_core::*;

#[path = "../../../src/kernel/implementation/syscall_ipc/mod.rs"]
pub mod syscall_ipc;

pub use syscall_ipc::syscall_ipc::{
    syscall_receive_empty,
    syscall_send_empty,
};

verus! {
global size_of usize == 8;
}
