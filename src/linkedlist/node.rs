use vstd::prelude::*;
use vstd::simple_pptr::*;
verus! {

pub struct Node<T>{
    pub value: T,
    pub next: usize,
    pub prev: usize,
}

pub struct ExternalNode<T>{
    storage: Node<T>,
    is_init: Ghost<bool>,
    addr: Ghost<usize>,
}

impl<T> ExternalNode<T>{
    pub closed spec fn addr(&self) -> usize {
        self.addr@
    }
    pub closed spec fn is_init(&self) -> bool {
        self.is_init@
    }
    #[verifier(external_body)]
    pub fn take(&mut self) -> (ret:(usize, Tracked<PointsTo<Node<T>>>))
        requires
            old(self).is_init(),
        ensures
            self.is_init() == false,
            self.addr() == old(self).addr(),
            self.addr() == ret.0,
            ret.1@.is_init(),
            ret.1@.addr() == self.addr(),
    {
        (&self.storage as *const Node<T> as usize, Tracked::assume_new())
    }
    #[verifier(external_body)]
    pub fn put(&mut self, perm: Tracked<PointsTo<Node<T>>>)
        requires
            old(self).is_init() == false,
            old(self).addr() == perm@.addr(),
            perm@.is_init(),
        ensures
            self.is_init() == true,
            self.addr() == old(self).addr(),
    {
    }
}

#[verifier(external_body)]
pub broadcast proof fn node_has_size<T>()
    ensures
        #![trigger size_of::<Node<T>>()]
        size_of::<Node<T>>() != 0,
{
}
#[verifier(external_body)]
pub proof fn test_node_perm_disjoint<T,K,V>(tracked this: &mut PointsTo<Node<T>>, tracked others: &Map<K, PointsTo<Node<V>>>)
    ensures 
        
        forall|k:K| 
            #![trigger others[k].addr()] 
            others.dom().contains(k) 
            ==> 
            this.addr() != others[k].addr(),
{
}

}