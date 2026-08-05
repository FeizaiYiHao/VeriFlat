use vstd::prelude::*;
use vstd::simple_pptr::*;

use crate::*;
verus! {

pub struct GlobalPool {
    pub linked_list: LinkedList<PagePtr, ALLOCATOR_GLOBAL_POLL_MAJOR>,
    pub page_perms_4k: Tracked<Map<PagePtr, PagePerm4k>>,
    pub page_perms_2m: Tracked<Map<PagePtr, PagePerm2m>>,
    pub page_perms_1g: Tracked<Map<PagePtr, PagePerm1g>>,
}

impl LockOwnerIdTrait for GlobalPool {
    open spec fn container_depth(&self) -> LockOwnerId { LockOwnerId::NotApp }
    open spec fn process_depth(&self) -> LockOwnerId { LockOwnerId::NotApp }
}

impl LockInvTrait for GlobalPool {
    open spec fn inv(&self) -> bool { self.wf() }
}

impl LockMajorTrait for GlobalPool {
    open spec fn lock_major_1(&self) -> LockMajorId { ALLOCATOR_GLOBAL_POLL_MAJOR }
    open spec fn lock_major_2(&self) -> LockMajorId { 233 }
    open spec fn lock_major_3(&self) -> LockMajorId { 233 }
    open spec fn lock_major_default(&self) -> LockMajorId { 233 }
    open spec fn lock_major_1_predicate(&self) -> bool { true }
    open spec fn lock_major_2_predicate(&self) -> bool { false }
    open spec fn lock_major_3_predicate(&self) -> bool { false }
    open spec fn lock_major_default_predicate(&self) -> bool { false }
}

impl LockMinorTrait for GlobalPool {
    open spec fn lock_minor(&self) -> LockMinorId { self.linked_list.lock_minor() }
}

impl LockIdTrait for GlobalPool {
    open spec fn lock_id(&self) -> LockId {
        LockId{
            container: self.container_depth(),
            process: self.process_depth(),
            major: self.current_lock_major(),
            minor: self.lock_minor(),
        }
    }
}

impl LockUserVisibilityTrait for GlobalPool {
    open spec fn is_user_visible() -> bool { false }
}

impl GlobalPool {
    pub open spec fn wf(&self) -> bool {
        &&& self.linked_list.wf()
        &&& self.linked_list.view().no_duplicates()
        //@Xiangdong TODO: add self.perm_wf() once pop_global_pool_page returns the PagePerm
    }

    pub open spec fn view(&self) -> Seq<PagePtr> { self.linked_list.view() }
    pub open spec fn dom(&self) -> Set<PagePtr> { self.linked_list.dom() }
    pub open spec fn map(&self) -> Map<usize, PagePtr> { self.linked_list.map() }

    pub open spec fn spec_len(&self) -> usize {
        self.linked_list.view().len() as usize
    }

    #[verifier(when_used_as_spec(spec_len))]
    pub fn len(&self) -> (ret: usize)
        requires self.linked_list.wf(),
        ensures ret == self.linked_list.len(),
    { self.linked_list.len() }

    pub fn peek_head(&self) -> (ret: (usize, PagePtr))
        where PagePtr: Copy
        requires self.linked_list.wf(), self.linked_list.len() != 0,
        ensures self.linked_list.dom().contains(ret.0),
            self.linked_list.map().dom().contains(ret.0),
            ret.1 == self.linked_list.view().spec_index(0),
            ret.1 == self.linked_list.map().spec_index(ret.0),
    { self.linked_list.peek_head() }

    pub proof fn lemma_len_view(&self)
        requires self.linked_list.wf(),
        ensures self.linked_list.view().len() == self.linked_list.len(),
    { self.linked_list.lemma_len_view(); }

    /// Same invariant as AllocatorCache::perm_wf — see there for details.
    pub open spec fn perm_wf(&self) -> bool {
        let pages = self.linked_list.view().to_set();
        &&& self.page_perms_4k.view().dom().subset_of(pages)
        &&& self.page_perms_2m.view().dom().subset_of(pages)
        &&& self.page_perms_1g.view().dom().subset_of(pages)
        &&& self.page_perms_4k.view().dom().disjoint(self.page_perms_2m.view().dom())
        &&& self.page_perms_4k.view().dom().disjoint(self.page_perms_1g.view().dom())
        &&& self.page_perms_2m.view().dom().disjoint(self.page_perms_1g.view().dom())
        &&& self.page_perms_4k.view().dom() + self.page_perms_2m.view().dom() + self.page_perms_1g.view().dom() =~= pages
        &&& forall|p: PagePtr|
            #![trigger self.page_perms_4k.view().spec_index(p).is_init()]
            #![trigger self.page_perms_4k.view().spec_index(p).addr()]
            self.page_perms_4k.view().dom().contains(p)
            ==> self.page_perms_4k.view().spec_index(p).is_init() && self.page_perms_4k.view().spec_index(p).addr() == p
        &&& forall|p: PagePtr|
            #![trigger self.page_perms_2m.view().spec_index(p).is_init()]
            #![trigger self.page_perms_2m.view().spec_index(p).addr()]
            self.page_perms_2m.view().dom().contains(p)
            ==> self.page_perms_2m.view().spec_index(p).is_init() && self.page_perms_2m.view().spec_index(p).addr() == p
        &&& forall|p: PagePtr|
            #![trigger self.page_perms_1g.view().spec_index(p).is_init()]
            #![trigger self.page_perms_1g.view().spec_index(p).addr()]
            self.page_perms_1g.view().dom().contains(p)
            ==> self.page_perms_1g.view().spec_index(p).is_init() && self.page_perms_1g.view().spec_index(p).addr() == p
    }
}

} // verus!
