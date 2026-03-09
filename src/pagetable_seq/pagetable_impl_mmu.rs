use vstd::prelude::*;
verus! {

use super::pagemap_util_t::*;
use crate::util::page_ptr_util_u::*;
use super::pagetable_spec::*;
use super::pagemap::*;
use super::entry::*;
use crate::define::*;
use vstd::simple_pptr::*;
use crate::lemma::lemma_u::*;



// exec
pub struct PageTableMMU {
    pub pagetable: PageTable,
}
}