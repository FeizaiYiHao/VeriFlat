use vstd::prelude::*;
use crate::define::*;
verus! {

pub open spec fn no_change_except<T>(new: Seq<T>, old: Seq<T>, index:usize) -> bool {
        &&&
        new.len() == old.len()
        &&&
        forall|i:int|
            #![auto]
            0 <= i <  new.len() && i != index
            ==>
            new[i] === old[i]
    }
    
} 
