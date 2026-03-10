use vstd::prelude::*;

use crate::*;
verus! {

pub struct BitMap<const N: usize>{
    bit_map: Array<bool, N>,
    map: Ghost<Map<usize, bool>>,
}

impl<const N: usize> BitMap<N>{

    pub closed spec fn view(&self) -> Map<usize, bool>{
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

    pub fn new_false() -> (ret:Self)
        ensures 
            ret.inv(),
            ret@ == Map::new(|i:usize|{0 <= i < N}, |k:usize|{false}),
    {
        let ghost_map = Ghost(Map::new(|i:usize|{0 <= i < N}, |k:usize|{false}));
        Self{
            bit_map: Array::new_with_init_value(false),
            map:ghost_map
        }
    }

    pub open spec fn spec_index(&self, index: usize) -> bool {
        self@[index]
    }

    pub fn index(&self, index: usize) -> (ret: bool)
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