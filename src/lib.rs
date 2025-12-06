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
// pub mod kernel;

verus! {
global size_of usize == 8;

fn test(){
    assert(1 + 1 == 2);
}

}

fn main(){

}