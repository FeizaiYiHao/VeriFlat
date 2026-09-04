#![feature(adt_const_params)]

use vstd::prelude::*;

pub mod define;
pub mod lemma;
pub mod util;
pub mod primitive;
pub mod locks;
pub mod linkedlist;
pub mod page;
pub mod cpu;
pub mod proc;
pub mod allocator;
pub mod pagetable_seq;
pub mod iommu;

pub use define::*;
pub use lemma::*;
pub use util::*;
pub use primitive::*;
pub use locks::*;
pub use linkedlist::*;
pub use page::*;
pub use cpu::*;
pub use proc::*;
pub use allocator::*;
pub use pagetable_seq::*;
pub use iommu::*;

pub mod kernel;

pub use kernel::kernel_k_define_spec::*;
pub use kernel::kernel_u_define_spec::*;
pub use kernel::kernel_total_define_spec::*;
pub use kernel::held_objects_unchanged_spec::*;
pub use kernel::process_management::*;
pub use kernel::memory_management::*;
pub use kernel::cpu_tlb_management;
pub use kernel::cpu_tlb_management::*;
pub use kernel::iommu_tlb_management::*;
pub use kernel::lemma::*;
pub use kernel::spec_util::*;
pub use kernel::release_and_finish_syscall::*;
pub use kernel::implementation::attach_endpoint_reference_and_unlock::*;
pub use kernel::implementation::create_thread_from_staged_page::*;
pub use kernel::implementation::create_process_from_staged_pages::*;
pub use kernel::implementation::create_process_with_iommu_from_staged_pages::*;

verus! {
global size_of usize == 8;
}
