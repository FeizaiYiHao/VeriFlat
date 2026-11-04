#![feature(adt_const_params)]
#![no_std]

use vstd::prelude::*;
use veriflat_kernel_core::*;
use veriflat_map_4k::map_4k::unmap_4k_spec::*;
use veriflat_map_4k::map_4k::unmap_4k_lock_running_thread::unmap_4k_lock_current_thread;
use veriflat_map_4k::map_4k::unmap_4k_flush_all::flush_pagetable_tlbs;

pub mod syscall_unmap_2m;

verus! {
global size_of usize == 8;
}
