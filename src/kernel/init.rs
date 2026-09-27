use core::mem::offset_of;
use vstd::prelude::*;
use vstd::simple_pptr::*;

const ASSERT_KERNEL_IRT_OFFSET: [(); 379_584_512] =
    [(); offset_of!(crate::KernelK, irt)];

verus! {
use crate::*;

pub const KERNEL_IRT_OFFSET: usize = 379_584_512;

#[derive(Clone, Copy)]
pub struct BootKernelLayout {
    pub kernel_ptr: usize,
    pub root_container: RwLockContainerPtr,
    pub pcid_allocator: RwLockPcidAllocatorPtr,
    pub allocator_4k: RwLockPageAllocatorPtr,
    pub allocator_2m: RwLockPageAllocatorPtr,
    pub allocator_1g: RwLockPageAllocatorPtr,
    pub scheduler: RwLockSchedulerPtr,
    pub cpu_set: RwLockCpuSetPtr,
    pub root_process: RwLockProcessPtr,
    pub cpu_pagetable: RwLockPageTableRoot,
    pub root_thread: RwLockThreadPtr,
    pub root_endpoint: RwLockEndpointPtr,
    pub iommu_table: RwLockPageTableRoot,
    pub iommu_l4: PageMapPtr,
    pub cpu_cr3: PageTableRoot,
}

impl BootKernelLayout {
    pub open spec fn pointers_wf(&self) -> bool {
        &&& page_ptr_2m_valid(self.root_container)
        &&& page_ptr_2m_valid(self.pcid_allocator)
        &&& page_ptr_valid(self.allocator_4k)
        &&& page_ptr_valid(self.allocator_2m)
        &&& page_ptr_valid(self.allocator_1g)
        &&& page_ptr_valid(self.scheduler)
        &&& page_ptr_valid(self.cpu_set)
        &&& page_ptr_valid(self.root_process)
        &&& page_ptr_valid(self.cpu_pagetable)
        &&& page_ptr_valid(self.root_thread)
        &&& page_ptr_valid(self.root_endpoint)
        &&& page_ptr_valid(self.iommu_table)
        &&& page_ptr_valid(self.iommu_l4)
        &&& page_ptr_valid(self.cpu_cr3)
        &&& self.cpu_pagetable != self.iommu_table
    }

    pub open spec fn iommu_root_table_base(&self) -> PAddr
        recommends
            self.kernel_ptr as int
                + KERNEL_IRT_OFFSET as int
                <= usize::MAX as int,
    {
        (self.kernel_ptr as int
            + KERNEL_IRT_OFFSET as int) as usize
    }
}

pub open spec fn boot_page_map_perms_wf(
    perms: Map<PageMapPtr, PointsTo<PageMap>>,
) -> bool {
    forall|ptr: PageMapPtr|
        #![trigger perms.dom().contains(ptr)]
        perms.dom().contains(ptr)
        ==> {
            &&& page_ptr_valid(ptr)
            &&& perms.spec_index(ptr).is_init()
            &&& perms.spec_index(ptr).addr() == ptr
            &&& perms.spec_index(ptr).value().wf()
        }
}

pub open spec fn boot_dom0_manifest_wf(
    manifest: Map<VAddr, MapEntry>,
    root_container: RwLockContainerPtr,
) -> bool {
    forall|va: VAddr|
        #![trigger manifest.dom().contains(va)]
        manifest.dom().contains(va)
        ==> {
            let entry = manifest.spec_index(va);
            &&& va_4k_valid(va)
            &&& page_ptr_valid(entry.addr)
            &&& entry.present
            &&& entry.owning_container.view() == root_container
    }
}

pub open spec fn boot_dom0_pagetable_model(
    raw_cr3: PageTableRoot,
    process_ptr: RwLockProcessPtr,
    kernel_l4_end: usize,
    kernel_entries: Seq<PageEntry>,
    manifest_4k: Map<VAddr, MapEntry>,
    l4_tables: Map<PageMapPtr, PointsTo<PageMap>>,
    l3_tables: Map<PageMapPtr, PointsTo<PageMap>>,
    l2_tables: Map<PageMapPtr, PointsTo<PageMap>>,
    l1_tables: Map<PageMapPtr, PointsTo<PageMap>>,
) -> PageTable<PT_TYPE> {
    PageTable {
        cr3: raw_cr3,
        pcid: Some(1),
        kernel_l4_end,
        l4_table: Tracked(l4_tables),
        l3_rev_map: Ghost(Map::empty()),
        l3_tables: Tracked(l3_tables),
        l2_rev_map: Ghost(Map::empty()),
        l2_tables: Tracked(l2_tables),
        l1_rev_map: Ghost(Map::empty()),
        l1_tables: Tracked(l1_tables),
        mapping_4k: Ghost(manifest_4k),
        mapping_2m: Ghost(Map::empty()),
        mapping_1g: Ghost(Map::empty()),
        kernel_entries: Ghost(kernel_entries),
        proc_ptr: process_ptr,
    }
}

pub open spec fn boot_free_4k_pool_wf(
    page_array: PageLockedArray,
    layout: BootKernelLayout,
    pool: &LinkedList<PagePtr, ALLOCATOR_GLOBAL_POLL_MAJOR>,
) -> bool {
    &&& pool.wf()
    &&& pool.view().no_duplicates()
    &&& pool.container_depth == Some(0)
    &&& pool.minor == Some(layout.root_container)
    &&& forall|page_index: PageIndex|
        #![trigger page_array.spec_index(page_index).view().view().state]
        index_valid(NUM_PAGES, page_index)
        && page_array.spec_index(page_index).view().view().state is Free4k
        ==> {
            let page = page_array.spec_index(page_index).view().view();
            &&& page.state == PageState::Free4k {
                allocator_ptr: Ghost(layout.allocator_4k),
                state: FreePageAllocatorState::GlobalList,
            }
            &&& pool.view().contains(page_index2page_ptr(page_index))
            &&& pool.map().dom().contains(
                page.free_list_node_storage.addr(),
            )
            &&& pool.map().spec_index(
                page.free_list_node_storage.addr(),
            ) == page_index2page_ptr(page_index)
        }
    &&& forall|page_ptr: PagePtr|
        #![trigger pool.view().contains(page_ptr)]
        pool.view().contains(page_ptr)
        ==> {
            let page = page_array.spec_index(
                page_ptr2page_index(page_ptr),
            ).view().view();
            &&& page_ptr_valid(page_ptr)
            &&& page.state == PageState::Free4k {
                allocator_ptr: Ghost(layout.allocator_4k),
                state: FreePageAllocatorState::GlobalList,
            }
            &&& page.owning_container == layout.root_container
        }
}

pub open spec fn boot_free_2m_pool_wf(
    page_array: PageLockedArray,
    layout: BootKernelLayout,
    pool: &LinkedList<PagePtr, ALLOCATOR_GLOBAL_POLL_MAJOR>,
) -> bool {
    &&& pool.wf()
    &&& pool.view().no_duplicates()
    &&& pool.container_depth == Some(0)
    &&& pool.minor == Some(layout.root_container)
    &&& forall|page_index: PageIndex|
        #![trigger page_array.spec_index(page_index).view().view().state]
        index_valid(NUM_PAGES, page_index)
        && page_array.spec_index(page_index).view().view().state is Free2m
        ==> {
            let page = page_array.spec_index(page_index).view().view();
            &&& page.state == PageState::Free2m {
                allocator_ptr: Ghost(layout.allocator_2m),
                state: FreePageAllocatorState::GlobalList,
            }
            &&& pool.view().contains(page_index2page_ptr(page_index))
            &&& pool.map().dom().contains(
                page.free_list_node_storage.addr(),
            )
            &&& pool.map().spec_index(
                page.free_list_node_storage.addr(),
            ) == page_index2page_ptr(page_index)
        }
    &&& forall|page_ptr: PagePtr|
        #![trigger pool.view().contains(page_ptr)]
        pool.view().contains(page_ptr)
        ==> {
            let page = page_array.spec_index(
                page_ptr2page_index(page_ptr),
            ).view().view();
            &&& page_ptr_2m_valid(page_ptr)
            &&& page.state == PageState::Free2m {
                allocator_ptr: Ghost(layout.allocator_2m),
                state: FreePageAllocatorState::GlobalList,
            }
            &&& page.owning_container == layout.root_container
        }
}

pub open spec fn boot_free_1g_pool_wf(
    page_array: PageLockedArray,
    layout: BootKernelLayout,
    pool: &LinkedList<PagePtr, ALLOCATOR_GLOBAL_POLL_MAJOR>,
) -> bool {
    &&& pool.wf()
    &&& pool.view().no_duplicates()
    &&& pool.container_depth == Some(0)
    &&& pool.minor == Some(layout.root_container)
    &&& forall|page_index: PageIndex|
        #![trigger page_array.spec_index(page_index).view().view().state]
        index_valid(NUM_PAGES, page_index)
        && page_array.spec_index(page_index).view().view().state is Free1g
        ==> {
            let page = page_array.spec_index(page_index).view().view();
            &&& page.state == PageState::Free1g {
                allocator_ptr: Ghost(layout.allocator_1g),
                state: FreePageAllocatorState::GlobalList,
            }
            &&& pool.view().contains(page_index2page_ptr(page_index))
            &&& pool.map().dom().contains(
                page.free_list_node_storage.addr(),
            )
            &&& pool.map().spec_index(
                page.free_list_node_storage.addr(),
            ) == page_index2page_ptr(page_index)
        }
    &&& forall|page_ptr: PagePtr|
        #![trigger pool.view().contains(page_ptr)]
        pool.view().contains(page_ptr)
        ==> {
            let page = page_array.spec_index(
                page_ptr2page_index(page_ptr),
            ).view().view();
            &&& page_ptr_1g_valid(page_ptr)
            &&& page.state == PageState::Free1g {
                allocator_ptr: Ghost(layout.allocator_1g),
                state: FreePageAllocatorState::GlobalList,
            }
            &&& page.owning_container == layout.root_container
        }
}

#[verifier::opaque]
pub open spec fn boot_page_array_ready(
    page_array: PageLockedArray,
    layout: BootKernelLayout,
    cpu_page_closure: Set<PagePtr>,
    manifest_4k: Map<VAddr, MapEntry>,
    free_4k_pool: &LinkedList<PagePtr, ALLOCATOR_GLOBAL_POLL_MAJOR>,
    free_2m_pool: &LinkedList<PagePtr, ALLOCATOR_GLOBAL_POLL_MAJOR>,
    free_1g_pool: &LinkedList<PagePtr, ALLOCATOR_GLOBAL_POLL_MAJOR>,
) -> bool {
    &&& page_array_wf(page_array)
    &&& hugepage_2m_wf(page_array)
    &&& hugepage_1g_wf(page_array)
    &&& boot_free_4k_pool_wf(page_array, layout, free_4k_pool)
    &&& boot_free_2m_pool_wf(page_array, layout, free_2m_pool)
    &&& boot_free_1g_pool_wf(page_array, layout, free_1g_pool)
    &&& cpu_page_closure.contains(layout.cpu_cr3)
    &&& !cpu_page_closure.contains(layout.cpu_pagetable)
    &&& forall|page_index: PageIndex|
        #![trigger page_array.spec_index(page_index).view().view().state]
        index_valid(NUM_PAGES, page_index)
        ==> {
            let page_ptr = page_index2page_ptr(page_index);
            let page = page_array.spec_index(page_index).view().view();
            &&& !page_array.spec_index(page_index).view().locked()
            &&& page.owning_container == layout.root_container
            &&& (page.state matches PageState::Allocated2m {
                state: Allocated2MPageState::AsContainer,
            }) <==> page_ptr == layout.root_container
            &&& (page.state matches PageState::Allocated2m {
                state: Allocated2MPageState::AsPcidAllocator,
            }) <==> page_ptr == layout.pcid_allocator
            &&& (page.state matches PageState::Allocated4k {
                state: Allocated4KPageState::As4KAllocator,
            }) <==> page_ptr == layout.allocator_4k
            &&& (page.state matches PageState::Allocated4k {
                state: Allocated4KPageState::As2MAllocator,
            }) <==> page_ptr == layout.allocator_2m
            &&& (page.state matches PageState::Allocated4k {
                state: Allocated4KPageState::As1GAllocator,
            }) <==> page_ptr == layout.allocator_1g
            &&& (page.state matches PageState::Allocated4k {
                state: Allocated4KPageState::AsScheduler,
            }) <==> page_ptr == layout.scheduler
            &&& (page.state matches PageState::Allocated4k {
                state: Allocated4KPageState::AsCpuSet,
            }) <==> page_ptr == layout.cpu_set
            &&& (page.state matches PageState::Allocated4k {
                state: Allocated4KPageState::AsProcess,
            }) <==> page_ptr == layout.root_process
            &&& (page.state matches PageState::Allocated4k {
                state: Allocated4KPageState::AsPageTableRoot,
            }) <==> page_ptr == layout.cpu_pagetable
            &&& (page.state matches PageState::Allocated4k {
                state: Allocated4KPageState::AsThread,
            }) <==> page_ptr == layout.root_thread
            &&& (page.state matches PageState::Allocated4k {
                state: Allocated4KPageState::AsEndpoint,
            }) <==> page_ptr == layout.root_endpoint
            &&& (page.state matches PageState::Allocated4k {
                state: Allocated4KPageState::AsIommuTableRoot,
            }) <==> page_ptr == layout.iommu_table
            &&& (page.state matches PageState::Allocated4k {
                state: Allocated4KPageState::PageTable {
                    pagetable_root: _,
                },
            }) <==> cpu_page_closure.contains(page_ptr)
            &&& (page.state is Allocated4k
                && page.state->Allocated4k_state is PageTable)
                ==> page.state->Allocated4k_state
                    ->PageTable_pagetable_root
                    == layout.cpu_pagetable
            &&& (page.state is IOMMUTable)
                <==> page_ptr == layout.iommu_l4
            &&& page.state is IOMMUTable
                ==> page.state->IOMMUTable_iommu_table_root
                    == layout.iommu_table
            &&& !(page.state is Owned4k)
            &&& !(page.state is Owned2m)
            &&& !(page.state is Owned1g)
            &&& !(page.state is Mapped2m)
            &&& !(page.state is Mapped1g)
            &&& forall|pagetable_ptr: RwLockPageTableRoot, va: VAddr|
                #![trigger page.mappings().contains((pagetable_ptr, va))]
                page.mappings().contains((pagetable_ptr, va))
                <==> {
                    &&& page.state is Mapped4k
                    &&& pagetable_ptr == layout.cpu_pagetable
                    &&& manifest_4k.dom().contains(va)
                    &&& manifest_4k.spec_index(va).addr == page_ptr
                }
        }
    &&& forall|va: VAddr|
        #![trigger manifest_4k.dom().contains(va)]
        manifest_4k.dom().contains(va)
        ==> {
            let page = page_array.spec_index(
                page_ptr2page_index(manifest_4k.spec_index(va).addr),
            ).view().view();
            &&& page.state is Mapped4k
            &&& page.mappings().contains(
                (layout.cpu_pagetable, va),
            )
            &&& page.owning_container
                == manifest_4k.spec_index(va)
                    .owning_container.view()
        }
}

/// The only new startup trust boundary. It adopts the page-table pages already
/// populated by the bootloader and consumes exactly their concrete
/// `PointsTo<PageMap>` permissions. All process identity, PCID, kernel-prefix,
/// closure, and abstract mapping facts are fixed by the postcondition.
#[verifier::external_body]
pub fn adopt_boot_dom0_pagetable(
    raw_cr3: PageTableRoot,
    pagetable_ptr: RwLockPageTableRoot,
    process_ptr: RwLockProcessPtr,
    kernel_l4_end: usize,
    kernel_entries: Ghost<Seq<PageEntry>>,
    manifest_4k: Ghost<Map<VAddr, MapEntry>>,
    root_container: RwLockContainerPtr,
    Tracked(l4_tables):
        Tracked<Map<PageMapPtr, PointsTo<PageMap>>>,
    Tracked(l3_tables):
        Tracked<Map<PageMapPtr, PointsTo<PageMap>>>,
    Tracked(l2_tables):
        Tracked<Map<PageMapPtr, PointsTo<PageMap>>>,
    Tracked(l1_tables):
        Tracked<Map<PageMapPtr, PointsTo<PageMap>>>,
) -> (ret: PageTable<PT_TYPE>)
    requires
        page_ptr_valid(pagetable_ptr),
        page_ptr_valid(process_ptr),
        page_ptr_valid(raw_cr3),
        pei_valid(kernel_l4_end),
        kernel_entries.view().len() == kernel_l4_end,
        l4_tables.dom() =~= set![raw_cr3],
        boot_page_map_perms_wf(l4_tables),
        boot_page_map_perms_wf(l3_tables),
        boot_page_map_perms_wf(l2_tables),
        boot_page_map_perms_wf(l1_tables),
        l4_tables.dom().disjoint(l3_tables.dom()),
        l4_tables.dom().disjoint(l2_tables.dom()),
        l4_tables.dom().disjoint(l1_tables.dom()),
        l3_tables.dom().disjoint(l2_tables.dom()),
        l3_tables.dom().disjoint(l1_tables.dom()),
        l2_tables.dom().disjoint(l1_tables.dom()),
        boot_dom0_manifest_wf(manifest_4k.view(), root_container),
        boot_dom0_pagetable_model(
            raw_cr3, process_ptr, kernel_l4_end, kernel_entries.view(), manifest_4k.view(), l4_tables, l3_tables, l2_tables, l1_tables,
        ).wf(),
    ensures
        ret.wf(),
        ret.cr3 == raw_cr3,
        ret.pcid == Some(1),
        ret.pcid_value() == 1,
        ret.proc_ptr == process_ptr,
        ret.kernel_l4_end == kernel_l4_end,
        ret.kernel_entries == kernel_entries,
        ret.l4_table.view() == l4_tables,
        ret.l3_tables.view() == l3_tables,
        ret.l2_tables.view() == l2_tables,
        ret.l1_tables.view() == l1_tables,
        ret.page_closure()
            =~= l4_tables.dom() + l3_tables.dom()
                + l2_tables.dom() + l1_tables.dom(),
        ret.mapping_4k() == manifest_4k.view(),
        ret.mapping_2m() == Map::<VAddr, MapEntry>::empty(),
        ret.mapping_1g() == Map::<VAddr, MapEntry>::empty(),
{
    PageTable {
        cr3: raw_cr3,
        pcid: Some(1),
        kernel_l4_end,
        l4_table: Tracked(l4_tables),
        l3_rev_map: Ghost(Map::empty()),
        l3_tables: Tracked(l3_tables),
        l2_rev_map: Ghost(Map::empty()),
        l2_tables: Tracked(l2_tables),
        l1_rev_map: Ghost(Map::empty()),
        l1_tables: Tracked(l1_tables),
        mapping_4k: manifest_4k,
        mapping_2m: Ghost(Map::empty()),
        mapping_1g: Ghost(Map::empty()),
        kernel_entries,
        proc_ptr: process_ptr,
    }
}

pub open spec fn boot_default_pagetable_ready(
    default_pagetable: ReadOnlyNode<PageTable<PT_TYPE>>,
    kernel_l4_end: usize,
) -> bool {
    &&& default_pagetable.view().wf()
    &&& default_pagetable.view().pcid_value()
        == KERNEL_DEFAULT_PCID
    &&& default_pagetable.view().is_empty()
    &&& default_pagetable.view().kernel_l4_end
        == kernel_l4_end
}

pub open spec fn boot_pcid_needflush_ready(
    needflush: PcidNeedFlushArray,
) -> bool {
    &&& pcid_needflush_wf(needflush)
    &&& forall|cpu_id: CpuId, pcid: Pcid|
        #![trigger needflush.spec_index(cpu_id, pcid)]
        index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid)
        ==> {
            &&& !needflush.spec_index(cpu_id, pcid).locked()
            &&& needflush.spec_index(cpu_id, pcid)
                .view_ghost() is None
            &&& !needflush.spec_index(cpu_id, pcid)
                .view().needflush
        }
}

pub open spec fn boot_cpu_published_ready(
    published: CpuPublishedArray,
    default_cr3: PageTableRoot,
) -> bool {
    forall|cpu_id: CpuId|
        #![trigger published[cpu_id as int].view()]
        #![trigger published[cpu_id as int].owner_cpu()]
        index_valid(NUM_CPUS, cpu_id)
        ==> {
            &&& published[cpu_id as int].inv()
            &&& published[cpu_id as int].owner_cpu() == cpu_id
            &&& published[cpu_id as int].view()
                == (default_cr3, KERNEL_DEFAULT_PCID)
        }
}

#[verifier::spinoff_prover]
proof fn prove_boot_container_process_allocator_quota_4k_wf(
    krnl: &KernelK,
    layout: BootKernelLayout,
)
    requires
        krnl.ctn_mp.dom() =~= set![layout.root_container],
        krnl.ctn_mp.spec_index(layout.root_container).view()
            .owned_processes.view() =~= set![layout.root_process],
        krnl.ctn_mp.spec_index(layout.root_container).view_ghost()
            .owned_threads.view() =~= set![layout.root_thread],
        krnl.ctn_mp.spec_index(layout.root_container).view_ghost()
            .owned_indirect_threads.view()
            =~= Set::<RwLockThreadPtr>::empty(),
        krnl.ctn_mp.spec_index(layout.root_container).view_rodata()
            .view().depth == 0,
        krnl.ctn_mp.spec_index(layout.root_container).view_rodata()
            .view().allocator_ptr_4k == layout.allocator_4k,
        process_effective_quota_4k(
            krnl.prc_mp.spec_index(layout.root_process),
        ) == 0,
        thread_effective_quota_4k(
            krnl.thr_mp.spec_index(layout.root_thread),
        ) == 0,
        krnl.thr_mp.spec_index(layout.root_thread).view()
            .direct_free_quota_pending_4k.view() == 0,
        krnl.allc_4k_mp.spec_index(layout.allocator_4k)
            .quota.view().view()
            == krnl.allc_4k_mp.spec_index(layout.allocator_4k)
                .total_free_pages.view(),
    ensures
        container_process_allocator_quota_4k_wf(krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_4k_mp),
{
    let ghost owned_processes = krnl.ctn_mp.spec_index(
        layout.root_container,
    ).view().owned_processes.view();
    let ghost owned_threads = krnl.ctn_mp.spec_index(
        layout.root_container,
    ).view_ghost().owned_threads.view();
    let ghost owned_indirect_threads = krnl.ctn_mp.spec_index(
        layout.root_container,
    ).view_ghost().owned_indirect_threads.view();
    let process_value_4k = |process_ptr: RwLockProcessPtr|
        process_effective_quota_4k(
            krnl.prc_mp.spec_index(process_ptr),
        );
    let thread_value_4k = |thread_ptr: RwLockThreadPtr|
        thread_effective_quota_4k(
            krnl.thr_mp.spec_index(thread_ptr),
        );
    let direct_pending_value_4k = |thread_ptr: RwLockThreadPtr|
        krnl.thr_mp.spec_index(thread_ptr).view()
            .direct_free_quota_pending_4k.view() as int;
    let indirect_pending_value_4k = |thread_ptr: RwLockThreadPtr|
        krnl.thr_mp.spec_index(thread_ptr).view()
            .indirect_free_quota_pending_4k.view()
            .spec_index(0) as int;
    let process_fold_4k =
        |sum: int, process_ptr: RwLockProcessPtr|
            sum + process_value_4k(process_ptr);
    let direct_process_fold_4k =
        |sum: int, process_ptr: RwLockProcessPtr|
            sum + process_effective_quota_4k(
                krnl.prc_mp.spec_index(process_ptr),
            );
    let thread_fold_4k =
        |sum: int, thread_ptr: RwLockThreadPtr|
            sum + thread_value_4k(thread_ptr);
    let direct_thread_fold_4k =
        |sum: int, thread_ptr: RwLockThreadPtr|
            sum + thread_effective_quota_4k(
                krnl.thr_mp.spec_index(thread_ptr),
            );
    let direct_pending_fold_4k =
        |sum: int, thread_ptr: RwLockThreadPtr|
            sum + direct_pending_value_4k(thread_ptr);
    let direct_direct_pending_fold_4k =
        |sum: int, thread_ptr: RwLockThreadPtr|
            sum + krnl.thr_mp.spec_index(thread_ptr).view()
                .direct_free_quota_pending_4k.view();
    let indirect_pending_fold_4k =
        |sum: int, thread_ptr: RwLockThreadPtr|
            sum + indirect_pending_value_4k(thread_ptr);
    let direct_indirect_pending_fold_4k =
        |sum: int, thread_ptr: RwLockThreadPtr|
            sum + krnl.thr_mp.spec_index(thread_ptr).view()
                .indirect_free_quota_pending_4k.view()
                .spec_index(0);
    assert({
        &&& process_fold_4k =~= direct_process_fold_4k
        &&& thread_fold_4k =~= direct_thread_fold_4k
        &&& direct_pending_fold_4k =~= direct_direct_pending_fold_4k
        &&& indirect_pending_fold_4k =~= direct_indirect_pending_fold_4k
        &&& owned_processes.fold(0int, process_fold_4k) == 0
        &&& owned_threads.fold(0int, thread_fold_4k) == 0
        &&& owned_threads.fold(0int, direct_pending_fold_4k) == 0
        &&& owned_indirect_threads.fold(0int, indirect_pending_fold_4k) == 0
    }) by {
        lemma_set_fold_int_sum_singleton(owned_processes, layout.root_process, process_value_4k);
        lemma_set_fold_int_sum_singleton(owned_threads, layout.root_thread, thread_value_4k);
        lemma_set_fold_int_sum_singleton(owned_threads, layout.root_thread, direct_pending_value_4k);
        lemma_set_fold_int_sum_empty(owned_indirect_threads, indirect_pending_value_4k);
    };
    reveal(container_process_allocator_quota_4k_wf);
}

#[verifier::spinoff_prover]
proof fn prove_boot_container_process_allocator_quota_2m_wf(
    krnl: &KernelK,
    layout: BootKernelLayout,
)
    requires
        krnl.ctn_mp.dom() =~= set![layout.root_container],
        krnl.ctn_mp.spec_index(layout.root_container).view()
            .owned_processes.view() =~= set![layout.root_process],
        krnl.ctn_mp.spec_index(layout.root_container).view_ghost()
            .owned_threads.view() =~= set![layout.root_thread],
        krnl.ctn_mp.spec_index(layout.root_container).view_ghost()
            .owned_indirect_threads.view()
            =~= Set::<RwLockThreadPtr>::empty(),
        krnl.ctn_mp.spec_index(layout.root_container).view_rodata()
            .view().depth == 0,
        krnl.ctn_mp.spec_index(layout.root_container).view_rodata()
            .view().allocator_ptr_2m == layout.allocator_2m,
        process_effective_quota_2m(
            krnl.prc_mp.spec_index(layout.root_process),
        ) == 0,
        thread_effective_quota_2m(
            krnl.thr_mp.spec_index(layout.root_thread),
        ) == 0,
        krnl.thr_mp.spec_index(layout.root_thread).view()
            .direct_free_quota_pending_2m.view() == 0,
        krnl.allc_2m_mp.spec_index(layout.allocator_2m)
            .quota.view().view()
            == krnl.allc_2m_mp.spec_index(layout.allocator_2m)
                .total_free_pages.view(),
    ensures
        container_process_allocator_quota_2m_wf(krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_2m_mp),
{
    let ghost owned_processes = krnl.ctn_mp.spec_index(
        layout.root_container,
    ).view().owned_processes.view();
    let ghost owned_threads = krnl.ctn_mp.spec_index(
        layout.root_container,
    ).view_ghost().owned_threads.view();
    let ghost owned_indirect_threads = krnl.ctn_mp.spec_index(
        layout.root_container,
    ).view_ghost().owned_indirect_threads.view();
    let process_value_2m = |process_ptr: RwLockProcessPtr|
        process_effective_quota_2m(
            krnl.prc_mp.spec_index(process_ptr),
        );
    let thread_value_2m = |thread_ptr: RwLockThreadPtr|
        thread_effective_quota_2m(
            krnl.thr_mp.spec_index(thread_ptr),
        );
    let direct_pending_value_2m = |thread_ptr: RwLockThreadPtr|
        krnl.thr_mp.spec_index(thread_ptr).view()
            .direct_free_quota_pending_2m.view() as int;
    let indirect_pending_value_2m = |thread_ptr: RwLockThreadPtr|
        krnl.thr_mp.spec_index(thread_ptr).view()
            .indirect_free_quota_pending_2m.view()
            .spec_index(0) as int;
    let process_fold_2m =
        |sum: int, process_ptr: RwLockProcessPtr|
            sum + process_value_2m(process_ptr);
    let direct_process_fold_2m =
        |sum: int, process_ptr: RwLockProcessPtr|
            sum + process_effective_quota_2m(
                krnl.prc_mp.spec_index(process_ptr),
            );
    let thread_fold_2m =
        |sum: int, thread_ptr: RwLockThreadPtr|
            sum + thread_value_2m(thread_ptr);
    let direct_thread_fold_2m =
        |sum: int, thread_ptr: RwLockThreadPtr|
            sum + thread_effective_quota_2m(
                krnl.thr_mp.spec_index(thread_ptr),
            );
    let direct_pending_fold_2m =
        |sum: int, thread_ptr: RwLockThreadPtr|
            sum + direct_pending_value_2m(thread_ptr);
    let direct_direct_pending_fold_2m =
        |sum: int, thread_ptr: RwLockThreadPtr|
            sum + krnl.thr_mp.spec_index(thread_ptr).view()
                .direct_free_quota_pending_2m.view();
    let indirect_pending_fold_2m =
        |sum: int, thread_ptr: RwLockThreadPtr|
            sum + indirect_pending_value_2m(thread_ptr);
    let direct_indirect_pending_fold_2m =
        |sum: int, thread_ptr: RwLockThreadPtr|
            sum + krnl.thr_mp.spec_index(thread_ptr).view()
                .indirect_free_quota_pending_2m.view()
                .spec_index(0);
    assert({
        &&& process_fold_2m =~= direct_process_fold_2m
        &&& thread_fold_2m =~= direct_thread_fold_2m
        &&& direct_pending_fold_2m =~= direct_direct_pending_fold_2m
        &&& indirect_pending_fold_2m =~= direct_indirect_pending_fold_2m
        &&& owned_processes.fold(0int, process_fold_2m) == 0
        &&& owned_threads.fold(0int, thread_fold_2m) == 0
        &&& owned_threads.fold(0int, direct_pending_fold_2m) == 0
        &&& owned_indirect_threads.fold(0int, indirect_pending_fold_2m) == 0
    }) by {
        lemma_set_fold_int_sum_singleton(owned_processes, layout.root_process, process_value_2m);
        lemma_set_fold_int_sum_singleton(owned_threads, layout.root_thread, thread_value_2m);
        lemma_set_fold_int_sum_singleton(owned_threads, layout.root_thread, direct_pending_value_2m);
        lemma_set_fold_int_sum_empty(owned_indirect_threads, indirect_pending_value_2m);
    };
    reveal(container_process_allocator_quota_2m_wf);
}

#[verifier::spinoff_prover]
proof fn prove_boot_container_process_allocator_quota_1g_wf(
    krnl: &KernelK,
    layout: BootKernelLayout,
)
    requires
        krnl.ctn_mp.dom() =~= set![layout.root_container],
        krnl.ctn_mp.spec_index(layout.root_container).view()
            .owned_processes.view() =~= set![layout.root_process],
        krnl.ctn_mp.spec_index(layout.root_container).view_ghost()
            .owned_threads.view() =~= set![layout.root_thread],
        krnl.ctn_mp.spec_index(layout.root_container).view_ghost()
            .owned_indirect_threads.view()
            =~= Set::<RwLockThreadPtr>::empty(),
        krnl.ctn_mp.spec_index(layout.root_container).view_rodata()
            .view().depth == 0,
        krnl.ctn_mp.spec_index(layout.root_container).view_rodata()
            .view().allocator_ptr_1g == layout.allocator_1g,
        process_effective_quota_1g(
            krnl.prc_mp.spec_index(layout.root_process),
        ) == 0,
        thread_effective_quota_1g(
            krnl.thr_mp.spec_index(layout.root_thread),
        ) == 0,
        krnl.thr_mp.spec_index(layout.root_thread).view()
            .direct_free_quota_pending_1g.view() == 0,
        krnl.allc_1g_mp.spec_index(layout.allocator_1g)
            .quota.view().view()
            == krnl.allc_1g_mp.spec_index(layout.allocator_1g)
                .total_free_pages.view(),
    ensures
        container_process_allocator_quota_1g_wf(krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_1g_mp),
{
    let ghost owned_processes = krnl.ctn_mp.spec_index(
        layout.root_container,
    ).view().owned_processes.view();
    let ghost owned_threads = krnl.ctn_mp.spec_index(
        layout.root_container,
    ).view_ghost().owned_threads.view();
    let ghost owned_indirect_threads = krnl.ctn_mp.spec_index(
        layout.root_container,
    ).view_ghost().owned_indirect_threads.view();
    let process_value_1g = |process_ptr: RwLockProcessPtr|
        process_effective_quota_1g(
            krnl.prc_mp.spec_index(process_ptr),
        );
    let thread_value_1g = |thread_ptr: RwLockThreadPtr|
        thread_effective_quota_1g(
            krnl.thr_mp.spec_index(thread_ptr),
        );
    let direct_pending_value_1g = |thread_ptr: RwLockThreadPtr|
        krnl.thr_mp.spec_index(thread_ptr).view()
            .direct_free_quota_pending_1g.view() as int;
    let indirect_pending_value_1g = |thread_ptr: RwLockThreadPtr|
        krnl.thr_mp.spec_index(thread_ptr).view()
            .indirect_free_quota_pending_1g.view()
            .spec_index(0) as int;
    let process_fold_1g =
        |sum: int, process_ptr: RwLockProcessPtr|
            sum + process_value_1g(process_ptr);
    let direct_process_fold_1g =
        |sum: int, process_ptr: RwLockProcessPtr|
            sum + process_effective_quota_1g(
                krnl.prc_mp.spec_index(process_ptr),
            );
    let thread_fold_1g =
        |sum: int, thread_ptr: RwLockThreadPtr|
            sum + thread_value_1g(thread_ptr);
    let direct_thread_fold_1g =
        |sum: int, thread_ptr: RwLockThreadPtr|
            sum + thread_effective_quota_1g(
                krnl.thr_mp.spec_index(thread_ptr),
            );
    let direct_pending_fold_1g =
        |sum: int, thread_ptr: RwLockThreadPtr|
            sum + direct_pending_value_1g(thread_ptr);
    let direct_direct_pending_fold_1g =
        |sum: int, thread_ptr: RwLockThreadPtr|
            sum + krnl.thr_mp.spec_index(thread_ptr).view()
                .direct_free_quota_pending_1g.view();
    let indirect_pending_fold_1g =
        |sum: int, thread_ptr: RwLockThreadPtr|
            sum + indirect_pending_value_1g(thread_ptr);
    let direct_indirect_pending_fold_1g =
        |sum: int, thread_ptr: RwLockThreadPtr|
            sum + krnl.thr_mp.spec_index(thread_ptr).view()
                .indirect_free_quota_pending_1g.view()
                .spec_index(0);
    assert({
        &&& process_fold_1g =~= direct_process_fold_1g
        &&& thread_fold_1g =~= direct_thread_fold_1g
        &&& direct_pending_fold_1g =~= direct_direct_pending_fold_1g
        &&& indirect_pending_fold_1g =~= direct_indirect_pending_fold_1g
        &&& owned_processes.fold(0int, process_fold_1g) == 0
        &&& owned_threads.fold(0int, thread_fold_1g) == 0
        &&& owned_threads.fold(0int, direct_pending_fold_1g) == 0
        &&& owned_indirect_threads.fold(0int, indirect_pending_fold_1g) == 0
    }) by {
        lemma_set_fold_int_sum_singleton(owned_processes, layout.root_process, process_value_1g);
        lemma_set_fold_int_sum_singleton(owned_threads, layout.root_thread, thread_value_1g);
        lemma_set_fold_int_sum_singleton(owned_threads, layout.root_thread, direct_pending_value_1g);
        lemma_set_fold_int_sum_empty(owned_indirect_threads, indirect_pending_value_1g);
    };
    reveal(container_process_allocator_quota_1g_wf);
}

#[verifier::spinoff_prover]
proof fn prove_boot_container_page_owner_wf(
    krnl: &KernelK,
    layout: BootKernelLayout,
    page_array: PageLockedArray,
    cpu_page_closure: Set<PagePtr>,
    manifest_4k: Map<VAddr, MapEntry>,
    free_4k_pool: &LinkedList<PagePtr, ALLOCATOR_GLOBAL_POLL_MAJOR>,
    free_2m_pool: &LinkedList<PagePtr, ALLOCATOR_GLOBAL_POLL_MAJOR>,
    free_1g_pool: &LinkedList<PagePtr, ALLOCATOR_GLOBAL_POLL_MAJOR>,
    all_valid_pages: Set<PagePtr>,
)
    requires
        krnl.pg_arr == page_array,
        boot_page_array_ready(page_array, layout, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool),
        krnl.ctn_mp.dom() =~= set![layout.root_container],
        krnl.ctn_mp.spec_index(layout.root_container).view()
            .owned_pages.view() =~= all_valid_pages,
        forall|page_ptr: PagePtr|
            #![trigger all_valid_pages.contains(page_ptr)]
            all_valid_pages.contains(page_ptr)
                <==> page_ptr_valid(page_ptr),
    ensures
        container_page_owner_wf(krnl.ctn_mp, krnl.pg_arr),
{
    reveal(container_page_owner_wf);
    page_ptr_valid_imply_page_index_valid();
    page_index_valid_imply_page_ptr_valid();
    page_ptr_roundtrip();
    page_index_roundtrip();
    assert forall|container_ptr: RwLockContainerPtr, page_ptr: PagePtr|
        #![trigger krnl.ctn_mp.spec_index(container_ptr).view()
            .owned_pages.view().contains(page_ptr)]
        krnl.ctn_mp.dom().contains(container_ptr)
        && krnl.ctn_mp.spec_index(container_ptr).view()
            .owned_pages.view().contains(page_ptr)
        implies {
            &&& page_ptr_valid(page_ptr)
            &&& krnl.pg_arr.spec_index(
                page_ptr2page_index(page_ptr),
            ).view().view().owning_container == container_ptr
        } by {
        assert(index_valid(NUM_PAGES, page_ptr2page_index(page_ptr)) && !(krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state is Owned4k) && krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == layout.root_container) by { reveal(boot_page_array_ready); page_ptr_valid_imply_page_index_valid(); };
    };
    assert forall|page_index: PageIndex|
        #![trigger krnl.pg_arr.spec_index(page_index).view().view()
            .owning_container]
        index_valid(NUM_PAGES, page_index)
        implies {
            &&& krnl.ctn_mp.dom().contains(
                krnl.pg_arr.spec_index(page_index).view().view()
                    .owning_container,
            )
            &&& krnl.ctn_mp.spec_index(
                krnl.pg_arr.spec_index(page_index).view().view()
                    .owning_container,
            ).view().owned_pages.view().contains(
                page_index2page_ptr(page_index),
            )
        } by {
        assert(all_valid_pages.contains(page_index2page_ptr(page_index))) by { page_index_valid_imply_page_ptr_valid(); };
        reveal(boot_page_array_ready);
    };
}

#[verifier::spinoff_prover]
proof fn prove_boot_iommu_table_pages_wf(
    krnl: &KernelK,
    layout: BootKernelLayout,
    page_array: PageLockedArray,
    cpu_page_closure: Set<PagePtr>,
    manifest_4k: Map<VAddr, MapEntry>,
    free_4k_pool: &LinkedList<PagePtr, ALLOCATOR_GLOBAL_POLL_MAJOR>,
    free_2m_pool: &LinkedList<PagePtr, ALLOCATOR_GLOBAL_POLL_MAJOR>,
    free_1g_pool: &LinkedList<PagePtr, ALLOCATOR_GLOBAL_POLL_MAJOR>,
)
    requires
        krnl.pg_arr == page_array,
        page_ptr_valid(layout.iommu_table),
        page_ptr_valid(layout.iommu_l4),
        boot_page_array_ready(page_array, layout, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool),
        krnl.it_mp.dom() =~= set![layout.iommu_table],
        krnl.it_mp.spec_index(layout.iommu_table).view()
            .page_closure() =~= set![layout.iommu_l4],
    ensures
        iommu_table_pages_wf(krnl.it_mp, krnl.pg_arr),
{
    reveal(iommu_table_pages_wf);
    reveal(boot_page_array_ready);
    page_ptr_valid_imply_page_index_valid();
    page_index_valid_imply_page_ptr_valid();
    page_ptr_roundtrip();
    page_index_roundtrip();
}

#[verifier::spinoff_prover]
proof fn prove_boot_container_thread_scheduler_wf(
    krnl: &KernelK,
    layout: BootKernelLayout,
    scheduler_node_addr: usize,
)
    requires
        krnl.ctn_mp.spec_index(layout.root_container).view_rodata()
            .view().scheduler == layout.scheduler,
        krnl.thr_mp.dom() =~= set![layout.root_thread],
        krnl.thr_mp.spec_index(layout.root_thread).view().state
            is SCHEDULED,
        krnl.thr_mp.spec_index(layout.root_thread).view()
            .owning_container == layout.root_container,
        krnl.thr_mp.spec_index(layout.root_thread).view()
            .scheduler_linkedlist_node.addr() == scheduler_node_addr,
        krnl.sched_mp.dom() =~= set![layout.scheduler],
        krnl.sched_mp.spec_index(layout.scheduler).view()
            .owning_container == layout.root_container,
        krnl.sched_mp.spec_index(layout.scheduler).view()
            .queue.view() =~= seq![layout.root_thread],
        krnl.sched_mp.spec_index(layout.scheduler).view()
            .queue.map()
            =~= Map::<usize, RwLockThreadPtr>::empty()
                .insert(scheduler_node_addr, layout.root_thread),
    ensures
        container_thread_scheduler_wf(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp),
{
    reveal(container_thread_scheduler_wf);
    assert forall|thread_ptr: RwLockThreadPtr|
        #![trigger krnl.thr_mp.spec_index(thread_ptr).view().state]
        #![trigger krnl.thr_mp.spec_index(thread_ptr).view()
            .owning_container]
        krnl.thr_mp.dom().contains(thread_ptr)
        && krnl.thr_mp.spec_index(thread_ptr).view().state
            is SCHEDULED
        implies {
            let scheduler_ptr = krnl.ctn_mp.spec_index(
                krnl.thr_mp.spec_index(thread_ptr).view()
                    .owning_container,
            ).view_rodata().view().scheduler;
            &&& krnl.sched_mp.spec_index(scheduler_ptr).view()
                .queue.view().contains(thread_ptr)
            &&& krnl.sched_mp.spec_index(scheduler_ptr).view()
                .queue.map().dom().contains(
                    krnl.thr_mp.spec_index(thread_ptr).view()
                        .scheduler_linkedlist_node.addr(),
                )
            &&& krnl.sched_mp.spec_index(scheduler_ptr).view()
                .queue.map().spec_index(
                    krnl.thr_mp.spec_index(thread_ptr).view()
                        .scheduler_linkedlist_node.addr(),
                ) == thread_ptr
        } by {
        krnl.sched_mp.spec_index(layout.scheduler).view()
            .queue.view().lemma_index_contains(0);
    };
}

#[verifier::spinoff_prover]
proof fn prove_boot_process_thread_wf(
    krnl: &KernelK,
    layout: BootKernelLayout,
    process_node_addr: usize,
)
    requires
        krnl.prc_mp.dom() =~= set![layout.root_process],
        !krnl.prc_mp.spec_index(layout.root_process).view().zombie,
        krnl.prc_mp.spec_index(layout.root_process).view()
            .owned_threads.view() =~= seq![layout.root_thread],
        krnl.prc_mp.spec_index(layout.root_process).view()
            .owned_threads.map()
            =~= Map::<usize, RwLockThreadPtr>::empty()
                .insert(process_node_addr, layout.root_thread),
        krnl.prc_mp.spec_index(layout.root_process).view_rodata()
            .view().owning_container == layout.root_container,
        krnl.prc_mp.spec_index(layout.root_process).view_rodata()
            .view().container_depth == 0,
        krnl.prc_mp.spec_index(layout.root_process).view_rodata()
            .view().depth == 0,
        krnl.prc_mp.spec_index(layout.root_process).view()
            .pagetable == layout.cpu_pagetable,
        krnl.thr_mp.dom() =~= set![layout.root_thread],
        krnl.thr_mp.spec_index(layout.root_thread).view()
            .owning_proc == layout.root_process,
        krnl.thr_mp.spec_index(layout.root_thread).view()
            .owning_container == layout.root_container,
        krnl.thr_mp.spec_index(layout.root_thread).view()
            .container_depth == 0,
        krnl.thr_mp.spec_index(layout.root_thread).view()
            .process_depth == 0,
        krnl.thr_mp.spec_index(layout.root_thread).view()
            .proc_pagetable_ptr == layout.cpu_pagetable,
        krnl.thr_mp.spec_index(layout.root_thread).view()
            .proc_linkedlist_node.addr() == process_node_addr,
    ensures
        process_thread_wf(krnl.prc_mp, krnl.thr_mp),
{
    reveal(process_empty_lists_wlocked);
    reveal(process_thread_wf);
    assert(process_empty_lists_wlocked(krnl.prc_mp)) by {
    };
    assert forall|thread_ptr: RwLockThreadPtr|
        #![trigger krnl.thr_mp.spec_index(thread_ptr)]
        krnl.thr_mp.dom().contains(thread_ptr)
        implies {
            let process_ptr = krnl.thr_mp.spec_index(thread_ptr)
                .view().owning_proc;
            &&& krnl.prc_mp.dom().contains(process_ptr)
            &&& !krnl.prc_mp.spec_index(process_ptr).view().zombie
            &&& krnl.prc_mp.spec_index(process_ptr).view()
                .owned_threads.view().contains(thread_ptr)
        } by {
        krnl.prc_mp.spec_index(layout.root_process).view()
            .owned_threads.view().lemma_index_contains(0);
    };
}

#[verifier::rlimit(15)]
#[verifier::spinoff_prover]
pub fn finish_init_from_boot(
    layout: BootKernelLayout,
    kernel_l4_end: usize,
    initial_regs: &Registers,
    page_array: PageLockedArray,
    pcid_needflush: PcidNeedFlushArray,
    cpu_published: CpuPublishedArray,
    default_pagetable: ReadOnlyNode<PageTable<PT_TYPE>>,
    free_4k_pool:
        LinkedList<PagePtr, ALLOCATOR_GLOBAL_POLL_MAJOR>,
    free_2m_pool:
        LinkedList<PagePtr, ALLOCATOR_GLOBAL_POLL_MAJOR>,
    free_1g_pool:
        LinkedList<PagePtr, ALLOCATOR_GLOBAL_POLL_MAJOR>,
    kernel_entries: Ghost<Seq<PageEntry>>,
    manifest_4k: Ghost<Map<VAddr, MapEntry>>,
    owned_pages: Ghost<Set<PagePtr>>,
    owned_pci_functions: Ghost<Set<PciBdf>>,
    Tracked(cpu_l4_tables):
        Tracked<Map<PageMapPtr, PointsTo<PageMap>>>,
    Tracked(cpu_l3_tables):
        Tracked<Map<PageMapPtr, PointsTo<PageMap>>>,
    Tracked(cpu_l2_tables):
        Tracked<Map<PageMapPtr, PointsTo<PageMap>>>,
    Tracked(cpu_l1_tables):
        Tracked<Map<PageMapPtr, PointsTo<PageMap>>>,
    Tracked(container_page_perm): Tracked<PagePerm2m>,
    Tracked(pcid_allocator_page_perm): Tracked<PagePerm2m>,
    Tracked(allocator_4k_page_perm): Tracked<PagePerm4k>,
    Tracked(allocator_2m_page_perm): Tracked<PagePerm4k>,
    Tracked(allocator_1g_page_perm): Tracked<PagePerm4k>,
    Tracked(scheduler_page_perm): Tracked<PagePerm4k>,
    Tracked(cpu_set_page_perm): Tracked<PagePerm4k>,
    Tracked(process_page_perm): Tracked<PagePerm4k>,
    Tracked(cpu_pagetable_page_perm): Tracked<PagePerm4k>,
    Tracked(thread_page_perm): Tracked<PagePerm4k>,
    Tracked(endpoint_page_perm): Tracked<PagePerm4k>,
    Tracked(iommu_table_page_perm): Tracked<PagePerm4k>,
    Tracked(iommu_l4_page_perm): Tracked<PagePerm4k>,
    Tracked(kernel_perm): Tracked<PointsTo<KernelK>>,
) -> (ret: Tracked<PointsTo<KernelK>>)
    requires
        0 < NUM_CPUS,
        layout.pointers_wf(),
        layout.kernel_ptr as int + KERNEL_IRT_OFFSET as int
            <= usize::MAX as int,
        layout.iommu_root_table_base() % VTD_TABLE_SIZE == 0,
        layout.iommu_root_table_base() as int
            + IOMMU_ROOT_TABLE_STATIC_SIZE as int
            <= MEM_MASK as int,
        layout.iommu_root_table_base() as int
            + IOMMU_ROOT_TABLE_STATIC_SIZE as int
            <= usize::MAX as int,
        kernel_perm.addr() == layout.kernel_ptr,
        !kernel_perm.is_init(),
        pei_valid(kernel_l4_end),
        kernel_entries.view().len() == kernel_l4_end,
        cpu_l4_tables.dom() =~= set![layout.cpu_cr3],
        boot_page_map_perms_wf(cpu_l4_tables),
        boot_page_map_perms_wf(cpu_l3_tables),
        boot_page_map_perms_wf(cpu_l2_tables),
        boot_page_map_perms_wf(cpu_l1_tables),
        cpu_l4_tables.dom().disjoint(cpu_l3_tables.dom()),
        cpu_l4_tables.dom().disjoint(cpu_l2_tables.dom()),
        cpu_l4_tables.dom().disjoint(cpu_l1_tables.dom()),
        cpu_l3_tables.dom().disjoint(cpu_l2_tables.dom()),
        cpu_l3_tables.dom().disjoint(cpu_l1_tables.dom()),
        cpu_l2_tables.dom().disjoint(cpu_l1_tables.dom()),
        boot_dom0_manifest_wf(manifest_4k.view(), layout.root_container),
        boot_dom0_pagetable_model(
            layout.cpu_cr3, layout.root_process, kernel_l4_end, kernel_entries.view(), manifest_4k.view(), cpu_l4_tables, cpu_l3_tables,
            cpu_l2_tables, cpu_l1_tables,
        ).wf(),
        boot_page_array_ready(
            page_array,
            layout,
            cpu_l4_tables.dom() + cpu_l3_tables.dom()
                + cpu_l2_tables.dom() + cpu_l1_tables.dom(),
            manifest_4k.view(),
            &free_4k_pool,
            &free_2m_pool,
            &free_1g_pool,
        ),
        boot_default_pagetable_ready(default_pagetable, kernel_l4_end),
        boot_pcid_needflush_ready(pcid_needflush),
        boot_cpu_published_ready(cpu_published, default_pagetable.view().cr3),
        owned_pci_functions.view().len() == VTD_DOMAIN_COUNT,
        forall|page_ptr: PagePtr|
            #![trigger owned_pages.view().contains(page_ptr)]
            owned_pages.view().contains(page_ptr)
                <==> page_ptr_valid(page_ptr),
        forall|bdf: PciBdf|
            #![trigger owned_pci_functions.view().contains(bdf)]
            owned_pci_functions.view().contains(bdf)
                <==> pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        container_page_perm.is_init(),
        container_page_perm.addr() == layout.root_container,
        pcid_allocator_page_perm.is_init(),
        pcid_allocator_page_perm.addr() == layout.pcid_allocator,
        allocator_4k_page_perm.is_init(),
        allocator_4k_page_perm.addr() == layout.allocator_4k,
        allocator_2m_page_perm.is_init(),
        allocator_2m_page_perm.addr() == layout.allocator_2m,
        allocator_1g_page_perm.is_init(),
        allocator_1g_page_perm.addr() == layout.allocator_1g,
        scheduler_page_perm.is_init(),
        scheduler_page_perm.addr() == layout.scheduler,
        cpu_set_page_perm.is_init(),
        cpu_set_page_perm.addr() == layout.cpu_set,
        process_page_perm.is_init(),
        process_page_perm.addr() == layout.root_process,
        cpu_pagetable_page_perm.is_init(),
        cpu_pagetable_page_perm.addr() == layout.cpu_pagetable,
        thread_page_perm.is_init(),
        thread_page_perm.addr() == layout.root_thread,
        endpoint_page_perm.is_init(),
        endpoint_page_perm.addr() == layout.root_endpoint,
        iommu_table_page_perm.is_init(),
        iommu_table_page_perm.addr() == layout.iommu_table,
        iommu_l4_page_perm.is_init(),
        iommu_l4_page_perm.addr() == layout.iommu_l4,
    ensures
        ret.view().addr() == layout.kernel_ptr,
        ret.view().is_init(),
        ret.view().value().inv(),
        ret.view().value().rt_ctn == layout.root_container,
        ret.view().value().ctn_mp.dom()
            =~= set![layout.root_container],
        ret.view().value().prc_mp.dom()
            =~= set![layout.root_process],
        ret.view().value().thr_mp.dom()
            =~= set![layout.root_thread],
        ret.view().value().ep_mp.dom()
            =~= set![layout.root_endpoint],
        ret.view().value().pt_mp.dom()
            =~= set![layout.cpu_pagetable],
        ret.view().value().it_mp.dom()
            =~= set![layout.iommu_table],
{
    let tracked mut kernel_perm = kernel_perm;
    let default_cr3 = default_pagetable.borrow().cr3;
    let ghost boot_cpu_page_closure =
        cpu_l4_tables.dom() + cpu_l3_tables.dom()
            + cpu_l2_tables.dom() + cpu_l1_tables.dom();
    let ghost boot_manifest_4k = manifest_4k.view();
    let cpu_pagetable = adopt_boot_dom0_pagetable(
        layout.cpu_cr3, layout.cpu_pagetable, layout.root_process, kernel_l4_end, kernel_entries, manifest_4k, layout.root_container,
        Tracked(cpu_l4_tables), Tracked(cpu_l3_tables), Tracked(cpu_l2_tables), Tracked(cpu_l1_tables),
    );
    let (iommu_l4, Tracked(iommu_l4_perm)) =
        page_perm_to_page_map(layout.iommu_l4, Tracked(iommu_l4_page_perm));
    let iommu_table = PageTable::<IOMMU_TYPE>::new(None, Ghost(Seq::empty()), iommu_l4, Tracked(iommu_l4_perm), 0, layout.root_process);
    let (
        thread,
        scheduler_node_addr,
        scheduler_node_perm,
        process_node_addr,
        process_node_perm,
    ) = Thread::new_boot_root(
        layout.root_thread,
        layout.root_container,
        layout.root_process,
        layout.cpu_pagetable,
        layout.root_endpoint,
        initial_regs,
    );
    let process = Process::new_boot_root(
        layout.root_process, layout.cpu_pagetable, layout.iommu_table, layout.root_thread, process_node_addr, process_node_perm,
        owned_pci_functions,
    );
    let scheduler = Scheduler::new_boot_root(
        layout.scheduler, layout.root_container, layout.root_thread, scheduler_node_addr, scheduler_node_perm,
    );
    let endpoint = Endpoint::new_root(layout.root_endpoint, layout.root_container, layout.root_thread);
    let cpu_set = CpuSet::new_root(layout.root_container);
    let pcid_allocator = PcidAllocator::new_boot_root(layout.root_container, layout.root_process);
    let ghost all_valid_pages = owned_pages.view();
    let container = Container::new_boot_root(layout.root_container, layout.root_process, layout.root_endpoint, owned_pages);
    let quota_4k = free_4k_pool.length;
    let quota_2m = free_2m_pool.length;
    let quota_1g = free_1g_pool.length;
    proof {
        assert(free_4k_pool.wf() && free_4k_pool.container_depth == Some(0) && free_4k_pool.minor == Some(layout.root_container)
            && free_2m_pool.wf() && free_2m_pool.container_depth == Some(0) && free_2m_pool.minor == Some(layout.root_container)
            && free_1g_pool.wf() && free_1g_pool.container_depth == Some(0) && free_1g_pool.minor == Some(layout.root_container)) by { reveal(boot_page_array_ready); };
        reveal(LinkedList::wf_value_list);
    }
    let allocator_4k = PageAllocator::new_with_global_pool(layout.root_container, 0, free_4k_pool, quota_4k);
    let allocator_2m = PageAllocator::new_with_global_pool(layout.root_container, 0, free_2m_pool, quota_2m);
    let allocator_1g = PageAllocator::new_with_global_pool(layout.root_container, 0, free_1g_pool, quota_1g);
    proof { reveal(PageTable::table_pages_wf); }
    let cpu_array = Cpu::new_boot_array(layout.root_container, default_cr3);
    let cpu_tlb = CpuTLB::new_empty();
    let iommu_tlb = IommuTLB::new_empty();
    let irt_base = layout.kernel_ptr + KERNEL_IRT_OFFSET;
    assert(VTD_TABLE_SIZE == 4096) by (compute);
    let irt = IommuRootTable::new_disabled(irt_base, layout.root_process);

    let process_rodata = ReadOnlyNode::new(
        ProcessRO {
            owning_container: layout.root_container,
            container_depth: 0,
            parent: None,
            depth: 0,
            pagetable: layout.cpu_pagetable,
            cr3: layout.cpu_cr3,
            pcid: 1,
        },
        Ghost(layout.root_process),
    );
    let process_ghost = ProcessGhost {
        uppertree_seq: Ghost(Seq::empty()),
        subtree_set: Ghost(Set::empty()),
    };
    let container_rodata = ReadOnlyNode::new(
        ContainerRO {
            parent: None,
            depth: 0,
            scheduler: layout.scheduler,
            pcid_allocator: layout.pcid_allocator,
            cpu_set: layout.cpu_set,
            allocator_ptr_4k: layout.allocator_4k,
            allocator_ptr_2m: layout.allocator_2m,
            allocator_ptr_1g: layout.allocator_1g,
        },
        Ghost(layout.root_container),
    );
    let ghost root_threads = Set::<RwLockThreadPtr>::empty().insert(layout.root_thread);
    let container_ghost = ContainerGhost {
        uppertree_seq: Ghost(Seq::empty()),
        subtree_set: Ghost(Set::empty()),
        owned_threads: Ghost(root_threads),
        owned_indirect_threads: Ghost(Set::empty()),
    };

    let mut pt_mp = PageTableLockedMap::new_empty();
    let mut it_mp = IommuTableLockedMap::new_empty();
    let mut ctn_mp = ContainerLockedMap::new_empty();
    let mut sched_mp = SchedulerLockedMap::new_empty();
    let mut pcid_allc_mp = PcidAllocatorLockedMap::new_empty();
    let mut cpu_set_mp = CpuSetLockedMap::new_empty();
    let mut prc_mp = ProcessLockedMap::new_empty();
    let mut thr_mp = ThreadLockedMap::new_empty();
    let mut ep_mp = EndpointLockedMap::new_empty();
    let mut allc_4k_mp = PageAllocatorUnLockedMap::new_empty();
    let mut allc_2m_mp = PageAllocatorUnLockedMap::new_empty();
    let mut allc_1g_mp = PageAllocatorUnLockedMap::new_empty();

    pt_mp.retype_4k_as_unlocked_singleton(
        layout.cpu_pagetable, cpu_pagetable, (), Ghost(()), Tracked(cpu_pagetable_page_perm), 0, layout.root_thread,
        Ghost(KernelObjId::PageTable(layout.cpu_pagetable)),
    );
    it_mp.retype_4k_as_unlocked_singleton(
        layout.iommu_table, iommu_table, (), Ghost(()), Tracked(iommu_table_page_perm), 0, layout.root_thread,
        Ghost(KernelObjId::IommuTable(layout.iommu_table)),
    );
    ctn_mp.retype_2m_as_unlocked_singleton(
        layout.root_container, container, container_rodata, Ghost(container_ghost), Tracked(container_page_perm), 0, layout.root_thread,
        Ghost(KernelObjId::Container(layout.root_container)),
    );
    sched_mp.retype_4k_as_unlocked_singleton(
        layout.scheduler, scheduler, (), Ghost(()), Tracked(scheduler_page_perm), 0, layout.root_thread,
        Ghost(KernelObjId::Scheduler(layout.scheduler)),
    );
    pcid_allc_mp.retype_2m_as_unlocked_singleton(
        layout.pcid_allocator, pcid_allocator, (), Ghost(()), Tracked(pcid_allocator_page_perm), 0, layout.root_thread,
        Ghost(KernelObjId::PcidAllocator(layout.pcid_allocator)),
    );
    cpu_set_mp.retype_4k_as_unlocked_singleton(
        layout.cpu_set, cpu_set, (), Ghost(()), Tracked(cpu_set_page_perm), 0, layout.root_thread,
        Ghost(KernelObjId::CpuSet(layout.cpu_set)),
    );
    prc_mp.retype_4k_as_unlocked_singleton(
        layout.root_process, process, process_rodata, Ghost(process_ghost), Tracked(process_page_perm), 0, layout.root_thread,
        Ghost(KernelObjId::Process(layout.root_process)),
    );
    thr_mp.retype_4k_as_unlocked_singleton(
        layout.root_thread, thread, (), Ghost(()), Tracked(thread_page_perm), 0, layout.root_thread,
        Ghost(KernelObjId::Thread(layout.root_thread)),
    );
    ep_mp.retype_4k_as_unlocked_singleton(
        layout.root_endpoint, endpoint, (), Ghost(()), Tracked(endpoint_page_perm), 0, layout.root_thread,
        Ghost(KernelObjId::Endpoint(layout.root_endpoint)),
    );
    allc_4k_mp.retype_page_to_allocator_and_insert(layout.allocator_4k, allocator_4k, Tracked(allocator_4k_page_perm));
    allc_2m_mp.retype_page_to_allocator_and_insert(layout.allocator_2m, allocator_2m, Tracked(allocator_2m_page_perm));
    allc_1g_mp.retype_page_to_allocator_and_insert(layout.allocator_1g, allocator_1g, Tracked(allocator_1g_page_perm));

    let krnl = KernelK {
        pt_mp,
        it_mp,
        irt,
        pg_arr: page_array,
        cpu_arr: cpu_array,
        pcid_needflush,
        cpu_published,
        ctn_mp,
        sched_mp,
        pcid_allc_mp,
        cpu_set_mp,
        prc_mp,
        thr_mp,
        ep_mp,
        allc_4k_mp,
        allc_2m_mp,
        allc_1g_mp,
        cpu_tlb,
        iommu_tlb,
        rt_ctn: layout.root_container,
        dflt_pt: default_pagetable,
    };
    proof {
        // Local object construction and unlocks establish each subsystem's
        // intrinsic invariant before any cross-object relation is used.
        assert(krnl.subsystems_inv()) by {
        assert(krnl.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
        assert(pagetable_perms_wf(krnl.pt_mp)) by { reveal(pagetable_perms_wf); };
        assert(iommu_table_perms_wf(krnl.it_mp)) by { reveal(iommu_table_perms_wf); };
        assert(page_array_wf(krnl.pg_arr)) by { reveal(boot_page_array_ready); };
        assert(cpu_array_wf(krnl.cpu_arr, krnl.dflt_pt.view())) by { reveal(cpu_array_wf); };
        assert(cpu_published_wf(
            krnl.cpu_published,
            krnl.cpu_arr,
            krnl.pcid_needflush,
        )) by {
            reveal(cpu_published_wf);
        };
        assert(container_perms_wf(krnl.ctn_mp)) by {
            reveal(container_perms_wf);
            assert(containers_inv(krnl.ctn_mp)) by {
            };
            assert(container_tree_fields_wf(krnl.ctn_mp)) by {
                reveal(container_tree_fields_wf);
            };
        };
        assert(process_perms_wf(krnl.prc_mp)) by { reveal(process_perms_wf); };
        assert(thread_perms_wf(krnl.thr_mp)) by {
            reveal(thread_perms_wf);
            assert(threads_inv(krnl.thr_mp)) by {
            };
            assert(thread_free_quota_pending_empty_unless_wlocked(
                krnl.thr_mp,
            )) by {
                reveal(thread_free_quota_pending_empty_unless_wlocked);
            };
            assert(thread_temp_alloc_empty_unless_wlocked(krnl.thr_mp)) by {
                reveal(thread_temp_alloc_empty_unless_wlocked);
            };
            assert(thread_endpoint_transit_only_when_wlocked(
                krnl.thr_mp,
            )) by {
            };
            assert(thread_syscall_progress_only_when_wlocked(krnl.thr_mp)) by { reveal(thread_syscall_progress_only_when_wlocked); };
        };
        assert(scheduler_perms_wf(krnl.sched_mp)) by { reveal(scheduler_perms_wf); };
        assert(cpu_set_perms_wf(krnl.cpu_set_mp)) by { reveal(cpu_set_perms_wf); };
        assert(pcid_allocator_perms_wf(krnl.pcid_allc_mp)) by { reveal(pcid_allocator_perms_wf); };
        assert(endpoint_perms_wf(krnl.ep_mp)) by { reveal(endpoint_perms_wf); };
        assert(allocator_perms_wf(krnl.allc_4k_mp)) by { reveal(allocator_perms_wf); };
        assert(allocator_perms_wf(krnl.allc_2m_mp)) by { reveal(allocator_perms_wf); };
        assert(allocator_perms_wf(krnl.allc_1g_mp)) by { reveal(allocator_perms_wf); };
        };

        // The boot page manifest is the single source of truth for physical
        // ownership, page roles, page-table closure, and allocator free lists.
        assert(krnl.memory_management_inv()) by {
        assert(allocator_pages_wf(
            krnl.pg_arr,
            krnl.allc_4k_mp,
            krnl.allc_2m_mp,
            krnl.allc_1g_mp,
        )) by {
            reveal(allocator_4k_pages_wf);
            reveal(allocator_2m_pages_wf);
            reveal(allocator_1g_pages_wf);
            reveal(boot_page_array_ready);
        };
        prove_boot_container_page_owner_wf(
            &krnl, layout, page_array, boot_cpu_page_closure, boot_manifest_4k, &free_4k_pool, &free_2m_pool, &free_1g_pool,
            all_valid_pages,
        );
        assert(hugepage_2m_wf(krnl.pg_arr)) by { reveal(boot_page_array_ready); };
        assert(hugepage_1g_wf(krnl.pg_arr)) by { reveal(boot_page_array_ready); };
        assert(page_pagetable_wf(krnl.pt_mp, krnl.pg_arr)) by {
            reveal(mapped_4k_page_pagetable_wf);
            reveal(mapped_2m_page_pagetable_wf);
            reveal(mapped_1g_page_pagetable_wf);
            reveal(boot_page_array_ready);
        };
        assert(container_process_page_pagetable_wf(
            krnl.ctn_mp,
            krnl.prc_mp,
            krnl.pt_mp,
            krnl.pg_arr,
        )) by {
            reveal(container_process_page_pagetable_wf);
            reveal(boot_page_array_ready);
        };
        assert(container_pages_wf(krnl.pg_arr, krnl.ctn_mp)) by {
            reveal(container_pages_wf);
            reveal(boot_page_array_ready);
        };
        assert(process_pages_wf(krnl.pg_arr, krnl.prc_mp)) by {
            reveal(process_pages_wf);
            reveal(boot_page_array_ready);
        };
        assert(pagetable_pages_wf(krnl.pt_mp, krnl.pg_arr)) by {
            reveal(pagetable_pages_wf);
            reveal(boot_page_array_ready);
        };
        prove_boot_iommu_table_pages_wf(
            &krnl, layout, page_array, boot_cpu_page_closure, boot_manifest_4k, &free_4k_pool, &free_2m_pool, &free_1g_pool,
        );
        assert(thread_pages_wf(krnl.thr_mp, krnl.pg_arr)) by {
            reveal(thread_pages_wf);
            reveal(boot_page_array_ready);
        };
        assert(scheduler_pages_wf(krnl.sched_mp, krnl.pg_arr)) by {
            reveal(scheduler_pages_wf);
            reveal(boot_page_array_ready);
        };
        assert(cpu_set_pages_wf(krnl.cpu_set_mp, krnl.pg_arr)) by {
            reveal(cpu_set_pages_wf);
            reveal(boot_page_array_ready);
        };
        assert(pcid_allocator_pages_wf(
            krnl.pg_arr,
            krnl.pcid_allc_mp,
        )) by {
            reveal(pcid_allocator_pages_wf);
            reveal(boot_page_array_ready);
        };
        assert(thread_staged_pages_wf(krnl.thr_mp, krnl.pg_arr)) by {
            reveal(thread_staged_pages_4k_wf);
            reveal(thread_staged_pages_2m_wf);
            reveal(thread_staged_pages_1g_wf);
            reveal(boot_page_array_ready);
        };
        assert(endpoint_pages_wf(krnl.ep_mp, krnl.pg_arr)) by {
            reveal(endpoint_pages_wf);
            reveal(boot_page_array_ready);
        };
        assert(process_pagetable_match(krnl.prc_mp, krnl.pt_mp)) by { reveal(process_pagetable_match); };
        assert(process_iommu_table_match(krnl.prc_mp, krnl.it_mp)) by { reveal(process_iommu_table_match); };
        assert(krnl.allocator_free_pages_wf()) by {
            reveal(allocator_free_page_ptrs_wf);
            reveal(boot_page_array_ready);
        };
        // Root process/thread quotas are zero; all remaining quota equals each
        // allocator's global-pool length. Singleton folds make that equality
        // explicit without expanding a general finite-set induction in this VC.
        prove_boot_container_process_allocator_quota_4k_wf(&krnl, layout);
        prove_boot_container_process_allocator_quota_2m_wf(&krnl, layout);
        prove_boot_container_process_allocator_quota_1g_wf(&krnl, layout);
        assert(container_allocator_wf(
            krnl.ctn_mp,
            krnl.allc_4k_mp,
            krnl.allc_2m_mp,
            krnl.allc_1g_mp,
        )) by {
            reveal(container_allocator_wf);
        };
        assert(container_allocator_free_4k_page_wf(
            krnl.allc_4k_mp,
            krnl.pg_arr,
        )) by {
            reveal(container_allocator_free_4k_page_wf);
            reveal(container_allocator_global_free_4k_page_wf);
            reveal(container_allocator_cpu_cache_free_4k_page_wf);
            reveal(boot_page_array_ready);
        };
        assert(container_allocator_free_2m_page_wf(
            krnl.allc_2m_mp,
            krnl.pg_arr,
        )) by {
            reveal(container_allocator_free_2m_page_wf);
            reveal(container_allocator_global_free_2m_page_wf);
            reveal(container_allocator_cpu_cache_free_2m_page_wf);
            reveal(boot_page_array_ready);
        };
        assert(container_allocator_free_1g_page_wf(
            krnl.allc_1g_mp,
            krnl.pg_arr,
        )) by {
            reveal(container_allocator_free_1g_page_wf);
            reveal(container_allocator_global_free_1g_page_wf);
            reveal(container_allocator_cpu_cache_free_1g_page_wf);
            reveal(boot_page_array_ready);
        };
        };

        // The initial process graph is one root container, one process, one
        // scheduled thread, one endpoint, and the singleton intrusive lists
        // connecting them.
        assert(krnl.process_management_inv()) by {
        assert(container_tree_wf(krnl.rt_ctn, krnl.ctn_mp)) by {
            reveal(container_root_wf);
            reveal(container_children_parent_wf);
            reveal(containers_linkedlist_wf);
            reveal(container_children_depth_wf);
            reveal(container_subtree_set_wf);
            reveal(container_uppertree_seq_wf);
            reveal(container_subtree_set_exclusive);
        };
        assert(container_process_wf(krnl.ctn_mp, krnl.prc_mp)) by { reveal(container_process_wf); };
        assert(per_container_process_tree_wf(
            krnl.ctn_mp,
            krnl.prc_mp,
        )) by {
            reveal(process_root_wf);
            reveal(process_children_parent_wf);
            reveal(process_linkedlist_wf);
            reveal(process_children_depth_wf);
            reveal(process_subtree_set_wf);
            reveal(process_uppertree_seq_wf);
            reveal(process_subtree_set_exclusive);
            reveal(per_container_process_tree_wf);
        };
        assert(container_endpoint_wf(krnl.ctn_mp, krnl.ep_mp)) by { reveal(container_endpoint_wf); };
        assert(container_cpu_wf(
            krnl.ctn_mp,
            krnl.cpu_set_mp,
            krnl.cpu_arr,
        )) by {
            reveal(container_cpu_wf);
        };
        assert(thread_endpoint_ref_counter_wf(
            krnl.thr_mp,
            krnl.ep_mp,
        )) by {
            reveal(thread_endpoint_ref_counter_wf);
        };
        assert(thread_endpoint_queue_wf(krnl.thr_mp, krnl.ep_mp)) by { reveal(thread_endpoint_queue_wf); };
        assert(thread_caller_callee_wf(krnl.thr_mp)) by { reveal(thread_caller_callee_wf); };
        assert(container_thread_endpoint_wf(
            krnl.ctn_mp,
            krnl.thr_mp,
            krnl.ep_mp,
        )) by {
            reveal(container_thread_endpoint_wf);
        };
        assert(container_scheduler_wf(krnl.ctn_mp, krnl.sched_mp)) by { reveal(container_scheduler_wf); };
        assert(container_cpu_set_wf(krnl.ctn_mp, krnl.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
        assert(container_pcid_allocator_wf(
            krnl.ctn_mp,
            krnl.pcid_allc_mp,
        )) by {
            reveal(container_pcid_allocator_wf);
        };
        assert(process_pcid_allocator_wf(
            krnl.ctn_mp,
            krnl.prc_mp,
            krnl.pcid_allc_mp,
        )) by {
            reveal(process_pcid_allocator_wf);
        };
        prove_boot_container_thread_scheduler_wf(&krnl, layout, scheduler_node_addr);
        assert(container_thread_wf(krnl.ctn_mp, krnl.thr_mp)) by { reveal(container_thread_wf); };
        assert(process_cpu_wf(krnl.prc_mp, krnl.cpu_arr)) by { reveal(process_cpu_wf); };
        prove_boot_process_thread_wf(&krnl, layout, process_node_addr);
        assert(thread_cpu_wf(krnl.thr_mp, krnl.cpu_arr)) by { reveal(thread_cpu_wf); };
        };

        // IOMMU ownership and both TLB invariants are vacuous over the freshly
        // disabled root table and empty software TLBs, but still proved from
        // their public specs.
        assert(krnl.inv()) by {
        assert(iommu_root_table_process_wf(
            &krnl.irt,
            krnl.prc_mp,
            krnl.it_mp,
        )) by {
            reveal(iommu_root_table_process_wf);
        };
        assert(process_pci_function_ownership_wf(
            &krnl.irt,
            krnl.prc_mp,
        )) by {
            reveal(process_pci_function_ownership_wf);
        };
        assert(iommu_tlb_wf_spec(
            krnl.iommu_tlb,
            &krnl.irt,
            krnl.prc_mp,
            krnl.it_mp,
        )) by {
            reveal(iommu_tlb_wf_spec);
        };
        assert(cpu_dirty_map_wf(
            krnl.ctn_mp,
            krnl.cpu_set_mp,
            krnl.prc_mp,
            krnl.cpu_arr,
            krnl.cpu_tlb,
            krnl.pt_mp,
            krnl.pcid_needflush,
        )) by {
            reveal(cpu_dirty_map_contains_container_processes);
            reveal(cpu_dirty_map_proc_pcid_match);
            reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
            reveal(cpu_dirty_map_contains_pagetable_pcid_match);
        };
        assert(tlb_wf_spec(
            krnl.cpu_tlb,
            krnl.pt_mp,
            krnl.cpu_arr,
            krnl.pcid_needflush,
        )) by {
            reveal(tlb_wf_spec);
        };
        };
    }
    PPtr::<KernelK>::from_usize(layout.kernel_ptr).put(Tracked(&mut kernel_perm), krnl);
    Tracked(kernel_perm)
}
}
