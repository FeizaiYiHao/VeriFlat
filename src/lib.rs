#![feature(adt_const_params)]

use vstd::prelude::*;
pub mod pagetable_seq;
pub mod define;
pub mod util;
pub mod lemma;
pub mod primitive;
pub mod locks;
pub mod concurrency;
pub mod page;
pub mod linkedlist;
pub mod cpu;
pub mod proc;
pub mod allocator;
pub mod iommu;
pub mod test;
pub mod kernel;

pub use pagetable_seq::*;
pub use define::*;
pub use util::*;
pub use lemma::*;
pub use primitive::*;
pub use locks::*;
pub use concurrency::*;
pub use page::*;
pub use linkedlist::*;
pub use cpu::*;
pub use proc::*;
pub use allocator::*;
pub use iommu::*;
pub use kernel::*;

verus! {
global size_of usize == 8;

fn test(){
    assert(1 + 1 == 2);
}

}

fn main(){

}
