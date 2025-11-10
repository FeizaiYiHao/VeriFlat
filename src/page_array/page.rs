use vstd::prelude::*;

use crate::{define::*, primitive::*};

verus! {

    #[derive(Clone, Copy)]
    pub struct PageX {
        pub addr: PagePtr,
        pub state: PageState,
        // pub is_io_page: bool,
        pub ref_count: usize,
        // pub owning_container: Option<ContainerPtr>,
        pub mappings: Ghost<Set<(PageTableRoot, VAddr)>>,
        pub io_mappings: Ghost<Set<(PageTableRoot, VAddr)>>,
    }

    pub type Page = RwLock<PageX, PHY_PAGE_LOCK_MAJOR>;

    impl PageX{
        pub open spec fn ref_count_inv(&self) -> bool{
            &&&
            self.ref_count == self.mappings@.len() + self.io_mappings@.len()
        }

        pub open spec fn mapped_state_inv(&self) -> bool{
            &&&
            match self.state {
                PageState::Mapped4k | PageState::Mapped2m | PageState::Mapped1g => {
                    self.ref_count != 0
                },
                _ => {
                    self.ref_count == 0
                }
            }
        }
    }

    impl LockInv for PageX{
        open spec fn inv(&self) -> bool{
            &&&
            self.ref_count_inv()
            &&&
            self.mapped_state_inv()
        }
    }
}