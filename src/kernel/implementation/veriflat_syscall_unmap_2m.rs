#![no_std]

use vstd::prelude::*;
use veriflat_kernel_core::*;
use veriflat_map_4k::map_4k::unmap_4k_spec::*;
use veriflat_map_4k::map_4k::unmap_4k_lock_running_thread::unmap_4k_lock_current_thread;
use veriflat_map_4k::map_4k::unmap_4k_flush_all::flush_pagetable_tlbs;

#[cfg(verus_keep_ghost)]
use veriflat_map_4k::map_4k::unmap_4k_trace::{unmap_4k_tlb_flush_steps_from_k, unmap_4k_tlb_va_flush_steps_from_k};
pub mod syscall_unmap_2m;

verus! {
global size_of usize == 8;
}
