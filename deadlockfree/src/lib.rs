//! Lock-order deadlock freedom over the kernel's own `KernelK` and `LocalContext`: two cpus whose contexts are aligned
//! with one kernel state and whose wanted locks are ordered by `lock_id_acyclic` cannot wait on each other.
#![feature(adt_const_params)]

use vstd::prelude::*;

use veriflat_kernel_core::*;

pub mod lock_order;

pub use lock_order::*;

verus! {
global size_of usize == 8;
}
