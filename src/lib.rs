#![feature(adt_const_params)]

use vstd::prelude::*;
pub mod pagetable_seq;
pub mod pagetable_map;
pub mod define;
pub mod util;
pub mod lemma;
pub mod primitive;
pub mod locks;
pub mod concurrency;
pub mod page_array;
pub mod linkedlist;
pub mod cpu_array;
pub mod container;
pub mod process;
pub mod thread;
pub mod endpoint;
pub mod test;
pub mod kernel;

pub use pagetable_seq::*;
pub use pagetable_map::*;
pub use define::*;
pub use util::*;
pub use lemma::*;
pub use primitive::*;
pub use locks::*;
pub use concurrency::*;
pub use page_array::*;
pub use linkedlist::*;
pub use cpu_array::*;
pub use container::*;
pub use process::*;
pub use thread::*;
pub use endpoint::*;

verus! {
global size_of usize == 8;

fn test(){
    assert(1 + 1 == 2);
}

}

fn main(){

}