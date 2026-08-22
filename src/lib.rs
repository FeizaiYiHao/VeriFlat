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
pub mod test;
pub mod kernel;

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
pub use kernel::*;

verus! {
global size_of usize == 8;

fn test(){
    assert(1 + 1 == 2);
}

}

fn main(){

}
