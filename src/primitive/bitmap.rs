use vstd::prelude::*;
use vstd::map::*;
use vstd::set::*;

use crate::*;
verus! {

pub struct BitMap<T, const N: usize>{
    pub bit_map: Array<T, N>,
    pub map: Ghost<Map<usize, T>>,
}

impl<T:Copy, const N: usize> BitMap<T, N>{

    pub open spec fn view(&self) -> Map<usize, T>{
        self.map@
    }

    pub open spec fn inv(&self) -> bool{
        &&&
        self.bit_map.wf()
        &&&
        forall|i:usize|
        #![trigger self@.dom().contains(i)]
        #![trigger usize_in_range::<N>(i)]
            usize_in_range::<N>(i) == self@.dom().contains(i)
        &&&
        forall|i:usize|
        #![trigger usize_in_range::<N>(i)]
        #![trigger self@[i]]
        #![trigger self.bit_map[i]]
        usize_in_range::<N>(i)
        ==>
        self@[i] == self.bit_map[i]
    }

    pub fn new_with_init_value(value:T) -> (ret:Self)
        ensures 
            ret.inv(),
            ret@ == Map::new(Seq::new(N as nat, |i: int| i as usize).to_set(), |k:usize|{value}),
    {
        proof {
            let s = Seq::new(N as nat, |i: int| i as usize);
            assert forall|i: usize| usize_in_range::<N>(i) implies s.to_set().contains(i) by {
                assert(s[i as int] == i);
            }
            assert forall|i: usize| s.to_set().contains(i) implies usize_in_range::<N>(i) by {
                let j = choose|j: int| 0 <= j < s.len() && s[j] == i;
            }
        }
        let ghost_map = Ghost(Map::new(Seq::new(N as nat, |i: int| i as usize).to_set(), |k:usize|{value}));
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
            usize_in_range::<N>(index),
        ensures
            ret == self[index],
    {
        *self.bit_map.get(index)
    }

    pub fn update(&mut self, index: usize, value:T)
        requires
            old(self).inv(),
            usize_in_range::<N>(index),
        ensures
            final(self).inv(),
            final(self)@ == old(self)@.insert(index, value),
    {
        proof{
            seq_update_lemma::<T>();
        }


        self.bit_map.set(index, value);
        proof {
            self.map@ = self.map@.insert(index, value);
        }


        // assert(        
        //     forall|i:usize|
        //         #![trigger self@.dom().contains(i)]
        //         i != index 
        //         ==> 
        //         (self@.dom().contains(i) == old(self)@.dom().contains(i))
        // );
    }

}
}