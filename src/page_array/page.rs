use vstd::prelude::*;

use crate::{define::*, primitive::*};

verus! {

    #[derive(Clone, Copy)]
    pub struct Page {
        pub addr: PagePtr,
        pub state: PageState,
        // pub is_io_page: bool,
        pub ref_count: usize,
        // pub owning_container: Option<ContainerPtr>,
        pub mappings_4k: Ghost<Set<(PageTableRoot, VAddr)>>,
        pub mappings_2m: Ghost<Set<(PageTableRoot, VAddr)>>,
        pub mappings_1g: Ghost<Set<(PageTableRoot, VAddr)>>,
        // pub io_mappings: Ghost<Set<(PageTableRoot, VAddr)>>,
    }

    pub type RwLockPage = RwLock<Page, PHY_PAGE_LOCK_MAJOR>;

    impl Page{
        pub open spec fn mappings_4k(&self) -> Set<(PageTableRoot, VAddr)> {
            self.mappings_4k@
        }

        pub open spec fn mappings_2m(&self) -> Set<(PageTableRoot, VAddr)> {
            self.mappings_2m@
        }

        pub open spec fn mappings_1g(&self) -> Set<(PageTableRoot, VAddr)> {
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
        pub open spec fn mappings_finite(&self) -> bool{
            &&&
            self.mappings_4k().finite()
            &&&
            self.mappings_2m().finite()
            &&&
            self.mappings_1g().finite()
        }
    }

    impl LockedUtil for Page{
        open spec fn inv(&self) -> bool{
            &&&
            self.mappings_finite()
            &&&
            self.ref_count_inv()
            &&&
            self.mapped_state_inv()
        }

        open spec fn lock_minor(&self) -> LockMinorId{
            self.addr
        }
    }
}