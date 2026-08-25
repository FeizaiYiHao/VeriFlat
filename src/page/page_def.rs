use vstd::prelude::*;

use crate::{define::*, primitive::*, va_4k_valid};
use crate::locks::*;
use crate::linkedlist::*;
verus! {
    pub struct Page {
        pub addr: PagePtr,
        pub state: PageState,
        pub is_io_page: bool,
        pub ref_count: usize,
        pub owning_container: RwLockContainerPtr,
        pub mappings: Ghost<Set<(RwLockPageTableRoot, VAddr)>>,
        // pub io_mappings: Ghost<Set<(RwLockPageTableRoot, VAddr)>>,

        pub free_list_node_storage: ExternalNode<PageIndex>,
        pub free_list: RwLockContainerPtr,

        /// Tracked ownership of the physical memory backing this page. Ordinary
        /// Free, Owned, and Mapped pages retain this permission; retyping the
        /// page as a kernel object consumes it.
        pub perm_4k: Tracked<Option<PagePerm4k>>,
        pub perm_2m: Tracked<Option<PagePerm2m>>,
        pub perm_1g: Tracked<Option<PagePerm1g>>,
    }

    impl Page{
        pub open spec fn mappings(&self) -> Set<(RwLockPageTableRoot, VAddr)> {
            self.mappings.view()
        }

        pub open spec fn ref_count_inv(&self) -> bool{
            &&&
            self.ref_count == self.mappings.view().len()
        }

        pub open spec fn mapped_state_inv(&self) -> bool{
            &&&
            match self.state {
                PageState::Mapped4k => {
                    self.ref_count != 0
                },
                PageState::Mapped2m => {
                    self.ref_count != 0
                },
                PageState::Mapped1g => {
                    self.ref_count != 0
                },
                _ => {
                    self.ref_count == 0
                }
            }
        }

        pub open spec fn free_state_inv(&self) -> bool{
            &&&
            match self.state {
                PageState::Free4k { state: FreePageAllocatorState::PreCpuCache { cpu_id }, .. }|
                PageState::Free2m { state: FreePageAllocatorState::PreCpuCache { cpu_id }, .. }|
                PageState::Free1g { state: FreePageAllocatorState::PreCpuCache { cpu_id }, .. } => {
                    index_valid(NUM_CPUS, cpu_id)
                }
                _ => true,
            }
        }

        /// Contents ownership exists while an ordinary page is Free, Owned, or
        /// Mapped. Retyping the page as a kernel object consumes the permission.
        pub open spec fn perm_inv(&self) -> bool {
            &&& match self.state {
                PageState::Free4k{..} | PageState::Owned4k{..} | PageState::Mapped4k => self.perm_4k.view().is_some(),
                _ => self.perm_4k.view().is_none(),
            }
            &&& match self.state {
                PageState::Free2m{..} | PageState::Owned2m{..} | PageState::Mapped2m => self.perm_2m.view().is_some(),
                _ => self.perm_2m.view().is_none(),
            }
            &&& match self.state {
                PageState::Free1g{..} | PageState::Owned1g{..} | PageState::Mapped1g => self.perm_1g.view().is_some(),
                _ => self.perm_1g.view().is_none(),
            }
            // The perm's address matches this page's address.
            &&& self.perm_4k.view().is_some() ==> self.perm_4k.view().unwrap().is_init()
            &&& self.perm_2m.view().is_some() ==> self.perm_2m.view().unwrap().is_init()
            &&& self.perm_1g.view().is_some() ==> self.perm_1g.view().unwrap().is_init()
            &&& self.perm_4k.view().is_some() ==> self.perm_4k.view().unwrap().addr() == self.addr
            &&& self.perm_2m.view().is_some() ==> self.perm_2m.view().unwrap().addr() == self.addr
            &&& self.perm_1g.view().is_some() ==> self.perm_1g.view().unwrap().addr() == self.addr
        }

        pub open spec fn node_storage_inv(&self) -> bool{
            &&&
            match self.state {
                PageState::Free4k { .. }|
                PageState::Free2m { .. }|
                PageState::Free1g { .. } => {
                    self.free_list_node_storage.is_init() == false
                },
                _ => {
                    self.free_list_node_storage.is_init() == true
                }
            }
        }

        pub open spec fn mappings_va_valid(&self) -> bool{
            &&&
            forall|pt_p:RwLockPageTableRoot, va:VAddr|
                self.state is Mapped4k && self.mappings().contains((pt_p, va)) ==> va_4k_valid(va)
            &&&
            forall|pt_p:RwLockPageTableRoot, va:VAddr|
                self.state is Mapped2m && self.mappings().contains((pt_p, va)) ==> crate::va_2m_valid(va)
            &&&
            forall|pt_p:RwLockPageTableRoot, va:VAddr|
                self.state is Mapped1g && self.mappings().contains((pt_p, va)) ==> crate::va_1g_valid(va)
        }

        pub open spec fn mappings_finite(&self) -> bool{
            true
        }
        pub open spec fn is_mapped(&self) -> bool {
            match self.state{
                PageState::Mapped4k 
                |PageState::Mapped2m
                |PageState::Mapped1g => true,
                _ => false,
            }
        }
        pub open spec fn is_free(&self) -> bool {
            match self.state{
                PageState::Free4k { .. }
                |PageState::Free2m { .. }
                |PageState::Free1g { .. } => true,
                _ => false,
            }
        }
        pub open spec fn is_allocated(&self) -> bool {
            match self.state{
                PageState::Allocated4k{..} 
                |PageState::Allocated2m{..} => true,
                _ => false,
            }
        }
        pub open spec fn is_owned(&self) -> bool {
            match self.state{
                PageState::Owned4k{..}
                |PageState::Owned2m{..} => true,
                _ => false,
            }
        }
        pub open spec fn is_merged(&self) -> bool {
            match self.state{
                PageState::Merged2m 
                |PageState::Merged1g => true,
                _ => false,
            }
        }
        pub open spec fn free_page_lock_major() -> LockMajorId{
            FREE_PAGE_LOCK_MAJOR
        }
        pub open spec fn mapped_page_lock_major() -> LockMajorId{
            MAPPED_PAGE_LOCK_MAJOR
        }
        pub open spec fn merged_page_lock_major() -> LockMajorId{
            MERGED_PAGE_LOCK_MAJOR
        }
        pub open spec fn allocated_page_lock_major() -> LockMajorId{
            ALLOCATED_PAGE_MAJOR
        }
    }

    impl LockInvTrait for Page{
        open spec fn inv(&self) -> bool{
            &&&
            self.mappings_va_valid()
            &&&
            self.mappings_finite()
            &&&
            self.ref_count_inv()
            &&&
            self.mapped_state_inv()
            &&&
            self.node_storage_inv()
            &&&
            self.free_state_inv()
            &&&
            self.perm_inv()
            &&&
            self.is_io_page ==> self.state is Mapped4k || self.state is Unavailable
        }
    }

    impl LockMajorTrait for Page{
        open spec fn lock_major_1(&self) -> LockMajorId {
            Self::free_page_lock_major()
        }
        open spec fn lock_major_2(&self) -> LockMajorId {
            Self::mapped_page_lock_major()
        }
        open spec fn lock_major_3(&self) -> LockMajorId {
            Self::merged_page_lock_major()
        }
        open spec fn lock_major_default(&self) -> LockMajorId {
            // TODO: Allocated4k should get a relatively high major (TBD).
            // For now it keeps ALLOCATED_PAGE_MAJOR = 1000.
            if self.is_owned() {
                OWNED_PAGE_LOCK_MAJOR
            } else {
                Self::allocated_page_lock_major()
            }
        }
        open spec fn lock_major_1_predicate(&self) -> bool {
            self.is_free()
        }
        open spec fn lock_major_2_predicate(&self) -> bool {
            self.is_mapped()
        }
        open spec fn lock_major_3_predicate(&self) -> bool {
            self.is_merged()
        }
        open spec fn lock_major_default_predicate(&self) -> bool {
            self.is_allocated()
        }
    }

    
    impl LockOwnerIdTrait for Page{
        open spec fn container_depth(&self) -> LockOwnerId {
            LockOwnerId::None
        }
    
        open spec fn process_depth(&self) -> LockOwnerId {
            LockOwnerId::None
        }
    }

    impl LockUserVisibilityTrait for Page {
        open spec fn is_user_visible() -> bool {
            false
        }
    }

    /// Extract the 4k page perm from a page that is Free4k or Owned4k.
    /// Sets perm_4k to None. The caller must ensure perm_4k is Some.
    pub fn take_perm_4k(page: &mut Page) -> (ret: Tracked<PagePerm4k>)
        requires
            old(page).perm_4k.view().is_some(),
            old(page).perm_inv(),
            old(page).state is Free4k || old(page).state is Owned4k,
        ensures
            final(page).perm_4k.view().is_none(),
            ret.view() == old(page).perm_4k.view().unwrap(),
            ret.view().is_init(),
            ret.view().addr() == final(page).addr,
            // All other fields unchanged.
            final(page).addr == old(page).addr,
            final(page).state == old(page).state,
            final(page).is_io_page == old(page).is_io_page,
            final(page).ref_count == old(page).ref_count,
            final(page).owning_container == old(page).owning_container,
            final(page).mappings.view() == old(page).mappings.view(),
            final(page).free_list_node_storage == old(page).free_list_node_storage,
            final(page).free_list == old(page).free_list,
            final(page).perm_2m.view() == old(page).perm_2m.view(),
            final(page).perm_1g.view() == old(page).perm_1g.view(),
    {
        let tracked ret = page.perm_4k.borrow_mut().tracked_take();
        Tracked(ret)
    }

    /// Add one reverse mapping to an already-published 4K page.
    pub fn add_4k_mapping(
        page: &mut Page,
        pagetable_ptr: RwLockPageTableRoot,
        va: VAddr,
    )
        requires
            old(page).inv(),
            old(page).state is Mapped4k,
            va_4k_valid(va),
            !old(page).mappings().contains((pagetable_ptr, va)),
            old(page).ref_count < usize::MAX,
        ensures
            final(page).inv(),
            final(page).mappings()
                == old(page).mappings().insert((pagetable_ptr, va)),
            final(page).ref_count == old(page).ref_count + 1,
            final(page).addr == old(page).addr,
            final(page).state == old(page).state,
            final(page).is_io_page == old(page).is_io_page,
            final(page).owning_container == old(page).owning_container,
            final(page).free_list_node_storage == old(page).free_list_node_storage,
            final(page).free_list == old(page).free_list,
            final(page).perm_4k.view() == old(page).perm_4k.view(),
            final(page).perm_2m.view() == old(page).perm_2m.view(),
            final(page).perm_1g.view() == old(page).perm_1g.view(),
    {
        proof {
            assert(
                page.mappings().insert((pagetable_ptr, va)).len()
                    == page.mappings().len() + 1
            ) by {
                vstd::set::lemma_set_insert_len(
                    page.mappings(),
                    (pagetable_ptr, va),
                );
            };
        }
        page.mappings = Ghost(page.mappings().insert((pagetable_ptr, va)));
        page.ref_count = page.ref_count + 1;
    }
}
