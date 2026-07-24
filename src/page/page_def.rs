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

        /// Tracked ownership of the physical memory backing this page.
        /// `Some` when the page is Free or Owned (the allocator/process holds
        /// the perm); `None` when Allocated/Mapped/Merged (the perm has been
        /// consumed by a retype or handed to a page table).
        pub perm_4k: Tracked<Option<PagePerm4k>>,
        pub perm_2m: Tracked<Option<PagePerm2m>>,
        pub perm_1g: Tracked<Option<PagePerm1g>>,
    }

    impl Page{
        pub open spec fn mappings(&self) -> Set<(RwLockPageTableRoot, VAddr)> {
            self.mappings@
        }

        pub open spec fn ref_count_inv(&self) -> bool{
            &&&
            self.ref_count == self.mappings@.len()
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
                PageState::Free4k { state: FreePageAllocatorState::PreCpuCache { cpu_id } }|
                PageState::Free2m { state: FreePageAllocatorState::PreCpuCache { cpu_id } }|
                PageState::Free1g { state: FreePageAllocatorState::PreCpuCache { cpu_id } } => {
                    cpu_id_valid(cpu_id)
                }
                _ => true,
            }
        }

        /// The tracked perm for a page size is `Some` iff the page is Free or
        /// Owned for that size (the allocator/process still holds the physical
        /// memory ownership).  Once Allocated/Mapped/Merged the perm has been
        /// consumed by a retype or handed to a page table.
        pub open spec fn perm_inv(&self) -> bool {
            &&& match self.state {
                PageState::Free4k{..} | PageState::Owned4k{..} => self.perm_4k@.is_some(),
                _ => self.perm_4k@.is_none(),
            }
            &&& match self.state {
                PageState::Free2m{..} | PageState::Owned2m{..} => self.perm_2m@.is_some(),
                _ => self.perm_2m@.is_none(),
            }
            &&& match self.state {
                PageState::Free1g{..} | PageState::Owned1g{..} => self.perm_1g@.is_some(),
                _ => self.perm_1g@.is_none(),
            }
            // The perm's address matches this page's address.
            &&& self.perm_4k@.is_some() ==> self.perm_4k@.unwrap().addr() == self.addr
            &&& self.perm_2m@.is_some() ==> self.perm_2m@.unwrap().addr() == self.addr
            &&& self.perm_1g@.is_some() ==> self.perm_1g@.unwrap().addr() == self.addr
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
                PageState::Free4k { state: _ }
                |PageState::Free2m { state: _ }
                |PageState::Free1g { state: _ } => true,
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
            Self::allocated_page_lock_major()
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
    #[verifier::external_body]
    pub fn take_perm_4k(page: &mut Page) -> (ret: Tracked<PagePerm4k>)
        requires
            old(page).perm_4k@.is_some(),
        ensures
            final(page).perm_4k@.is_none(),
            ret@ == old(page).perm_4k@.unwrap(),
            ret@.is_init(),
            ret@.addr() == final(page).addr,
            // All other fields unchanged.
            final(page).addr == old(page).addr,
            final(page).state == old(page).state,
            final(page).is_io_page == old(page).is_io_page,
            final(page).ref_count == old(page).ref_count,
            final(page).owning_container == old(page).owning_container,
            final(page).mappings@ == old(page).mappings@,
            final(page).perm_2m@ == old(page).perm_2m@,
            final(page).perm_1g@ == old(page).perm_1g@,
    {
        unimplemented!()
    }
}