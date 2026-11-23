#![no_std]

use vstd::prelude::*;
use veriflat_kernel_core::*;

#[cfg(verus_keep_ghost)]
use veriflat_map_4k::map_4k::unmap_4k_trace::unmap_4k_tlb_flush_steps_from_k;
pub mod syscall_pci_bar;

verus! {
global size_of usize == 8;
}
