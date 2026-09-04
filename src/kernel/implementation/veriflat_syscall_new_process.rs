#![feature(adt_const_params)]

use vstd::prelude::*;

use veriflat_alloc_page::allocate_free_4k_page::allocate_free_4k_pages::{
    allocate_free_4k_pages,
    allocated_4k_page_lock_perms_wf,
    page_ptrs_to_indices,
};
use veriflat_alloc_page::allocate_free_4k_page::allocate_free_4k_impl_basd::allocate_free_4k_page;
use veriflat_kernel_core::*;
use veriflat_map_4k::*;

pub mod syscall_new_process;

verus! {
global size_of usize == 8;
}
