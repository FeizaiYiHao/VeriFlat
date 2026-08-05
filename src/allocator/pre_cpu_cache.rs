use vstd::prelude::*;

use crate::*;
use vstd::simple_pptr::*;
verus! {

pub struct AllocatorCache{
    pub linked_list: LinkedList<PagePtr, 233>,
    pub page_perms_4k: Tracked<Map<PagePtr, PagePerm4k>>,
    pub page_perms_2m: Tracked<Map<PagePtr, PagePerm2m>>,
    pub page_perms_1g: Tracked<Map<PagePtr, PagePerm1g>>,
}

impl LockOwnerIdTrait for AllocatorCache{
    open spec fn container_depth(&self) -> LockOwnerId {
        LockOwnerId::NotApp
    }

    open spec fn process_depth(&self) -> LockOwnerId {
        LockOwnerId::NotApp
    }
}

impl LockInvTrait for AllocatorCache{
    open spec fn inv(&self) -> bool {
        self.wf()
    }
}

impl LockMajorTrait for AllocatorCache{
    open spec fn lock_major_1(&self) -> LockMajorId {
        ALLOCATOR_CACHE_MAJOR
    }

    open spec fn lock_major_2(&self) -> LockMajorId {
        233
    }

    open spec fn lock_major_3(&self) -> LockMajorId {
        233
    }

    open spec fn lock_major_default(&self) -> LockMajorId {
        233
    }

    open spec fn lock_major_1_predicate(&self) -> bool {
        true
    }

    open spec fn lock_major_2_predicate(&self) -> bool {
        false
    }

    open spec fn lock_major_3_predicate(&self) -> bool {
        false
    }

    open spec fn lock_major_default_predicate(&self) -> bool {
        false
    }
}

impl LockUserVisibilityTrait for AllocatorCache{
    open spec fn is_user_visible() -> bool {
        false
    }
}

impl AllocatorCache{
    pub open spec fn wf(&self) -> bool{
        &&&
        self.linked_list.wf()
        &&&
        self.linked_list.view().no_duplicates()
        &&&
        self.watermark_wf()
        //@Xiangdong TODO: add self.perm_wf() once pop_cache_page returns the PagePerm
    }
    pub open spec fn view(&self) -> Seq<PagePtr> {
        self.linked_list.view()
    }
    pub open spec fn dom(&self) -> Set<PagePtr>
    {
        self.linked_list.dom()
    }     
    pub open spec fn map(&self) -> Map<usize, PagePtr>
    {
        self.linked_list.map()
    } 
    pub open spec fn watermark_wf(&self) -> bool{
        &&&
        ALLOCATOR_MIN_WATERMARK <= self.linked_list.view().len() <= ALLOCATOR_MAX_WATERMARK
    }

    /// Exactly one of the three perm maps covers the free pages; the other two
    /// are empty.  Each entry is initialised with the correct address.
    pub open spec fn perm_wf(&self) -> bool {
        let pages = self.linked_list.view().to_set();
        &&& self.page_perms_4k.view().dom().subset_of(pages)
        &&& self.page_perms_2m.view().dom().subset_of(pages)
        &&& self.page_perms_1g.view().dom().subset_of(pages)
        // ---- disjoint: no page in two maps ----
        &&& self.page_perms_4k.view().dom().disjoint(self.page_perms_2m.view().dom())
        &&& self.page_perms_4k.view().dom().disjoint(self.page_perms_1g.view().dom())
        &&& self.page_perms_2m.view().dom().disjoint(self.page_perms_1g.view().dom())
        // ---- coverage: every free page has exactly one perm ----
        &&& self.page_perms_4k.view().dom() + self.page_perms_2m.view().dom() + self.page_perms_1g.view().dom() =~= pages
        // ---- 4k entries: is_init + addr ----
        &&& forall|p: PagePtr|
            #![trigger self.page_perms_4k.view().spec_index(p).is_init()]
            #![trigger self.page_perms_4k.view().spec_index(p).addr()]
            self.page_perms_4k.view().dom().contains(p)
            ==> self.page_perms_4k.view().spec_index(p).is_init() && self.page_perms_4k.view().spec_index(p).addr() == p
        // ---- 2m entries: is_init + addr ----
        &&& forall|p: PagePtr|
            #![trigger self.page_perms_2m.view().spec_index(p).is_init()]
            #![trigger self.page_perms_2m.view().spec_index(p).addr()]
            self.page_perms_2m.view().dom().contains(p)
            ==> self.page_perms_2m.view().spec_index(p).is_init() && self.page_perms_2m.view().spec_index(p).addr() == p
        // ---- 1g entries: is_init + addr ----
        &&& forall|p: PagePtr|
            #![trigger self.page_perms_1g.view().spec_index(p).is_init()]
            #![trigger self.page_perms_1g.view().spec_index(p).addr()]
            self.page_perms_1g.view().dom().contains(p)
            ==> self.page_perms_1g.view().spec_index(p).is_init() && self.page_perms_1g.view().spec_index(p).addr() == p
    }
}

}
