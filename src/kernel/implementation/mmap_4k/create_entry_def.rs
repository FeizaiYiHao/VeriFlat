use vstd::prelude::*;

verus! {

use crate::*;

/// A mapping update may refresh the dynamic lock id of each held Page slot,
/// but it cannot acquire or release any lock.  Keep that distinction explicit:
/// every non-Page lock map is unchanged and the Page lock-map domain is fixed.
pub open spec fn mmap_4k_lock_domains_framed(
    post: &LocalContext,
    pre: &LocalContext,
) -> bool {
    &&& post.container_lock_map() =~= pre.container_lock_map()
    &&& post.process_lock_map() =~= pre.process_lock_map()
    &&& post.thread_lock_map() =~= pre.thread_lock_map()
    &&& post.endpoint_lock_map() =~= pre.endpoint_lock_map()
    &&& post.scheduler_lock_map() =~= pre.scheduler_lock_map()
    &&& post.pcid_allocator_lock_map() =~= pre.pcid_allocator_lock_map()
    &&& post.pagetable_lock_map() =~= pre.pagetable_lock_map()
    &&& post.iommu_table_lock_map() =~= pre.iommu_table_lock_map()
    &&& post.cpu_lock_map() =~= pre.cpu_lock_map()
    &&& post.allocator_4k_lock_map() =~= pre.allocator_4k_lock_map()
    &&& post.allocator_2m_lock_map() =~= pre.allocator_2m_lock_map()
    &&& post.allocator_1g_lock_map() =~= pre.allocator_1g_lock_map()
    &&& post.page_lock_map().dom() =~= pre.page_lock_map().dom()
}

pub open spec fn mmap_4k_bundle_locks_match(
    pages: Create4kEntryPages,
    lctx: &LocalContext,
    page_lock_perms: &Map<PagePtr, LockPerm>,
) -> bool {
    &&& lctx.page_lock_map().dom() =~= pages.page_index_set()
    &&& page_lock_perms.dom() =~= pages.page_set()
}

/// Exact page roles for creating one fresh 4K mapping.
///
/// The page-table root already exists.  Therefore one mapping consumes the
/// data page plus zero to three page-table pages, depending on the first
/// missing level on the target VA's path. Each variant names the structural
/// roles from the highest missing child table down to the leaf's L1 table.
#[derive(Clone, Copy)]
#[allow(inconsistent_fields)]
pub enum Create4kEntryPages {
    DataOnly {
        data_page: PagePtr,
    },
    L1AndData {
        l1_page: PagePtr,
        data_page: PagePtr,
    },
    L2L1AndData {
        l2_page: PagePtr,
        l1_page: PagePtr,
        data_page: PagePtr,
    },
    L3L2L1AndData {
        l3_page: PagePtr,
        l2_page: PagePtr,
        l1_page: PagePtr,
        data_page: PagePtr,
    },
}

impl Create4kEntryPages {
    pub open spec fn page_set(&self) -> Set<PagePtr> {
        match self {
            Self::DataOnly { data_page } => set![*data_page],
            Self::L1AndData { l1_page, data_page } =>
                set![*l1_page, *data_page],
            Self::L2L1AndData { l2_page, l1_page, data_page } =>
                set![*l2_page, *l1_page, *data_page],
            Self::L3L2L1AndData {
                l3_page, l2_page, l1_page, data_page,
            } => set![*l3_page, *l2_page, *l1_page, *data_page],
        }
    }

    pub open spec fn page_index_set(&self) -> Set<PageIndex> {
        match self {
            Self::DataOnly { data_page } =>
                set![page_ptr2page_index(*data_page)],
            Self::L1AndData { l1_page, data_page } => set![
                page_ptr2page_index(*l1_page),
                page_ptr2page_index(*data_page),
            ],
            Self::L2L1AndData { l2_page, l1_page, data_page } => set![
                page_ptr2page_index(*l2_page),
                page_ptr2page_index(*l1_page),
                page_ptr2page_index(*data_page),
            ],
            Self::L3L2L1AndData {
                l3_page, l2_page, l1_page, data_page,
            } => set![
                page_ptr2page_index(*l3_page),
                page_ptr2page_index(*l2_page),
                page_ptr2page_index(*l1_page),
                page_ptr2page_index(*data_page),
            ],
        }
    }

    pub open spec fn data_page(&self) -> PagePtr {
        match self {
            Self::DataOnly { data_page }
            | Self::L1AndData { data_page, .. }
            | Self::L2L1AndData { data_page, .. }
            | Self::L3L2L1AndData { data_page, .. } => *data_page,
        }
    }

    pub open spec fn count(&self) -> usize {
        match self {
            Self::DataOnly { .. } => 1,
            Self::L1AndData { .. } => 2,
            Self::L2L1AndData { .. } => 3,
            Self::L3L2L1AndData { .. } => 4,
        }
    }

    pub open spec fn add_structure_pages(&self, base: Set<PagePtr>) -> Set<PagePtr> {
        match self {
            Self::DataOnly { .. } => base,
            Self::L1AndData { l1_page, .. } => base.insert(*l1_page),
            Self::L2L1AndData { l2_page, l1_page, .. } =>
                base.insert(*l2_page).insert(*l1_page),
            Self::L3L2L1AndData { l3_page, l2_page, l1_page, .. } =>
                base.insert(*l3_page).insert(*l2_page).insert(*l1_page),
        }
    }

    pub open spec fn remove_pages(&self, base: Set<PagePtr>) -> Set<PagePtr> {
        match self {
            Self::DataOnly { data_page } => base.remove(*data_page),
            Self::L1AndData { l1_page, data_page } =>
                base.remove(*l1_page).remove(*data_page),
            Self::L2L1AndData { l2_page, l1_page, data_page } =>
                base.remove(*l2_page).remove(*l1_page).remove(*data_page),
            Self::L3L2L1AndData { l3_page, l2_page, l1_page, data_page } =>
                base.remove(*l3_page).remove(*l2_page).remove(*l1_page).remove(*data_page),
        }
    }

    /// No physical page may fill two roles in the same mapping operation.
    /// Keeping this finite and explicit lets callers obtain the remaining
    /// staged-page facts after each single-page consume without opening a
    /// quantified sequence-uniqueness proof.
    pub open spec fn roles_distinct(&self) -> bool {
        match self {
            Self::DataOnly { .. } => true,
            Self::L1AndData { l1_page, data_page } => l1_page != data_page,
            Self::L2L1AndData { l2_page, l1_page, data_page } => {
                &&& l2_page != l1_page
                &&& l2_page != data_page
                &&& l1_page != data_page
            },
            Self::L3L2L1AndData { l3_page, l2_page, l1_page, data_page } => {
                &&& l3_page != l2_page
                &&& l3_page != l1_page
                &&& l3_page != data_page
                &&& l2_page != l1_page
                &&& l2_page != data_page
                &&& l1_page != data_page
            },
        }
    }

}

}
