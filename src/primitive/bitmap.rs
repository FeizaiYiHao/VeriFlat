use vstd::prelude::*;

use crate::*;
verus! {

pub struct BitMap<T, const N: usize>{
    bit_map: Array<T, N>,
    map: Ghost<Map<usize, T>>,
}

impl<T:Copy, const N: usize> BitMap<T, N>{

    pub closed spec fn view(&self) -> Map<usize, T>{
        self.map@
    }

    pub closed spec fn inv(&self) -> bool{
        &&&
        self.bit_map.wf()
        &&&
        forall|i:usize|
        #![auto]
            0 <= i < N <==> self@.dom().contains(i)
        &&&
        forall|i:usize|
        #![auto]
        0 <= i < N
        ==>
        self@[i] == self.bit_map[i]
    }

    pub fn new_with_init_value(value:T) -> (ret:Self)
        ensures 
            ret.inv(),
            ret@ == Map::new(|i:usize|{0 <= i < N}, |k:usize|{value}),
    {
        let ghost_map = Ghost(Map::new(|i:usize|{0 <= i < N}, |k:usize|{value}));
        Self{
            bit_map: Array::new_with_init_value(value),
            map:ghost_map
        }
    }

    pub open spec fn spec_index(&self, index: usize) -> T {
        self@[index]
    }

    pub fn index(&self, index: usize) -> (ret: T)
        requires
            self.inv(),
            0 <= index < N,
        ensures
            ret == self[index],
    {
        *self.bit_map.get(index)
    }

}
}