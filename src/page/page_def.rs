use vstd::prelude::*;

use crate::{define::*, primitive::*, va_4k_valid};
use crate::locks::*;
use crate::linkedlist::*;
verus! {
    pub struct Page {
        pub addr: PagePtr,
        pub state: PageState,
        // pub is_io_page: bool,
        pub ref_count: usize,
        pub owning_container: RwLockContainerPtr,
        pub mappings_4k: Ghost<Set<(RwLockPageTableRoot, VAddr)>>,
        pub mappings_2m: Ghost<Set<(RwLockPageTableRoot, VAddr)>>,
        pub mappings_1g: Ghost<Set<(RwLockPageTableRoot, VAddr)>>,
        // pub io_mappings: Ghost<Set<(RwLockPageTableRoot, VAddr)>>,

        pub free_list_node_storage: ExternalNode<PageIndex>,
        pub free_list: RwLockContainerPtr,
    }

    impl Page{
        pub open spec fn mappings_4k(&self) -> Set<(RwLockPageTableRoot, VAddr)> {
            self.mappings_4k@
        }

        pub open spec fn mappings_2m(&self) -> Set<(RwLockPageTableRoot, VAddr)> {
            self.mappings_2m@
        }

        pub open spec fn mappings_1g(&self) -> Set<(RwLockPageTableRoot, VAddr)> {
            self.mappings_1g@
        }

        pub open spec fn ref_count_inv(&self) -> bool{
            &&&
            self.ref_count == self.mappings_4k@.len() + self.mappings_2m@.len() +self.mappings_1g@.len()
        }

        pub open spec fn mapped_state_inv(&self) -> bool{
            &&&
            match self.state {
                PageState::Mapped4k => {
                    self.mappings_4k@.len() != 0
                },
                PageState::Mapped2m => {
                    self.mappings_2m@.len() != 0
                },
                PageState::Mapped1g => {
                    self.mappings_1g@.len() != 0
                },
                _ => {
                    self.ref_count == 0
                }
            }
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
                self.mappings_4k().contains((pt_p, va)) ==> va_4k_valid(va)
            &&&
            forall|pt_p:RwLockPageTableRoot, va:VAddr|
                self.mappings_2m().contains((pt_p, va)) ==> crate::va_2m_valid(va)
            &&&
            forall|pt_p:RwLockPageTableRoot, va:VAddr|
                self.mappings_1g().contains((pt_p, va)) ==> crate::va_1g_valid(va)
        }

        pub open spec fn mappings_finite(&self) -> bool{
            &&&
            self.mappings_4k().finite()
            &&&
            self.mappings_2m().finite()
            &&&
            self.mappings_1g().finite()
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
                PageState::Free4k { allocator_ptr: _, state: _ }
                |PageState::Free2m { allocator_ptr: _, state: _ }
                |PageState::Free1g { allocator_ptr: _, state: _ } => true,
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
}