#![feature(adt_const_params)]

use vstd::prelude::*;

pub use veriflat_model::*;

#[path = "../../../src/kernel/mod.rs"]
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

verus! {
global size_of usize == 8;
}
