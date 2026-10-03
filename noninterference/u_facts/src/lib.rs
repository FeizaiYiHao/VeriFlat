//! Facts that hold in the user projection of every well-formed kernel. Unlike the kernel's step
//! wrappers, these proofs unfold `kernel_k_to_kernel_u` directly, so the crate stays outside the
//! kernel workspace and is imported only by proofs over the user step specifications.
#![feature(adt_const_params)]

use vstd::prelude::*;

pub mod ownership;

pub use ownership::*;

verus! {
global size_of usize == 8;
}
