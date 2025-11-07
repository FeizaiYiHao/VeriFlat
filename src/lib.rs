use vstd::prelude::*;
pub mod pagetable_seq;
pub mod pagetable_locked;
pub mod define;
pub mod util;
pub mod lemma;
pub mod primitive;

verus! {
global size_of usize == 8;

fn test(){
    assert(1 + 1 == 2);
}

}

fn main(){

}