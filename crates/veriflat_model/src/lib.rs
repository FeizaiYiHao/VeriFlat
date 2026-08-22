#![feature(adt_const_params)]

use vstd::prelude::*;

#[path = "../../../src/define/mod.rs"]
pub mod define;
#[path = "../../../src/lemma/mod.rs"]
pub mod lemma;
#[path = "../../../src/util/mod.rs"]
pub mod util;
#[path = "../../../src/primitive/mod.rs"]
pub mod primitive;
#[path = "../../../src/locks/mod.rs"]
pub mod locks;
#[path = "../../../src/linkedlist/mod.rs"]
pub mod linkedlist;
#[path = "../../../src/page/mod.rs"]
pub mod page;
#[path = "../../../src/cpu/mod.rs"]
pub mod cpu;
#[path = "../../../src/proc/mod.rs"]
pub mod proc;
#[path = "../../../src/allocator/mod.rs"]
pub mod allocator;
#[path = "../../../src/pagetable_seq/mod.rs"]
pub mod pagetable_seq;
#[path = "../../../src/iommu/mod.rs"]
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

verus! {
global size_of usize == 8;
}
