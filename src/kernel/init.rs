use core::mem::offset_of;
use vstd::prelude::*;
use vstd::simple_pptr::*;

mod boot_eof_pages;
use boot_eof_pages::*;

const ASSERT_KERNEL_IRT_OFFSET: [(); 0] = [(); offset_of!(crate::KernelK, irt)];

verus! {
use crate::*;

/// `irt` leads `KernelK`; the pinned table starts one 4K page after its lock word (`IommuRootTableLock` is `#[repr(C)]`).
pub const KERNEL_IRT_OFFSET: usize = VTD_TABLE_SIZE;

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
            self.kernel_ptr as int + KERNEL_IRT_OFFSET as int <= usize::MAX as int,
    {
        (self.kernel_ptr as int + KERNEL_IRT_OFFSET as int) as usize
    }
}

pub open spec fn boot_page_map_perms_wf(perms: Map<PageMapPtr, PointsTo<PageMap>>) -> bool {
    forall|ptr: PageMapPtr|
        #![trigger perms.dom().contains(ptr)]
        perms.dom().contains(ptr) ==> {
            &&& page_ptr_valid(ptr)
            &&& perms.spec_index(ptr).is_init()
            &&& perms.spec_index(ptr).addr() == ptr
            &&& perms.spec_index(ptr).value().wf()
        }
}

pub open spec fn boot_dom0_manifest_wf(manifest: Map<VAddr, MapEntry>, root_container: RwLockContainerPtr) -> bool {
    forall|va: VAddr|
        #![trigger manifest.dom().contains(va)]
        manifest.dom().contains(va) ==> {
            let entry = manifest.spec_index(va);
            &&& va_4k_valid(va)
            &&& page_ptr_valid(entry.addr)
            &&& entry.present
            &&& entry.owning_container.view() == root_container
        }
}

/// Reverse maps recording where the boot loader linked each L3, L2, and L1 table page of dom0's page table.
pub type BootRevMaps = (Map<PageMapPtr, L4Index>, Map<PageMapPtr, (L4Index, L3Index)>, Map<PageMapPtr, (L4Index, L3Index, L2Index)>);

pub open spec fn boot_dom0_pagetable_model(
    raw_cr3: PageTableRoot, process_ptr: RwLockProcessPtr, kernel_l4_end: usize, kernel_entries: Seq<PageEntry>,
    manifest_4k: Map<VAddr, MapEntry>, l4_tables: Map<PageMapPtr, PointsTo<PageMap>>, l3_tables: Map<PageMapPtr, PointsTo<PageMap>>,
    l2_tables: Map<PageMapPtr, PointsTo<PageMap>>, l1_tables: Map<PageMapPtr, PointsTo<PageMap>>, rev_maps: BootRevMaps,
) -> PageTable<PT_TYPE> {
    PageTable {
        cr3: raw_cr3, pcid: Some(1), did: None, kernel_l4_end, l4_table: Tracked(l4_tables), l3_rev_map: Ghost(rev_maps.0), l3_tables: Tracked(l3_tables),
        l2_rev_map: Ghost(rev_maps.1), l2_tables: Tracked(l2_tables), l1_rev_map: Ghost(rev_maps.2), l1_tables: Tracked(l1_tables),
        mapping_4k: Ghost(manifest_4k), mapping_2m: Ghost(Map::empty()), mapping_1g: Ghost(Map::empty()), kernel_entries: Ghost(kernel_entries), proc_ptr: process_ptr,
    }
}

pub open spec fn boot_free_4k_pool_wf(page_array: PageLockedArray, layout: BootKernelLayout, pool: &LinkedList<PagePtr, 233>) -> bool {
    &&& pool.wf()
    &&& pool.view().no_duplicates()
    &&& pool.container_depth.view() == Some(0)
    &&& pool.minor.view() == Some(layout.root_container)
    &&& forall|page_index: PageIndex|
        #![trigger page_array.spec_index(page_index).view().view().state]
        index_valid(NUM_PAGES, page_index) && page_array.spec_index(page_index).view().view().state is Free4k ==> {
            let page = page_array.spec_index(page_index).view().view();
            &&& page.state == PageState::Free4k { allocator_ptr: Ghost(layout.allocator_4k), state: FreePageAllocatorState::GlobalList }
            &&& pool.view().contains(page_index2page_ptr(page_index))
            &&& pool.map().dom().contains(page.free_list_node_storage.addr())
            &&& pool.map().spec_index(page.free_list_node_storage.addr()) == page_index2page_ptr(page_index)
        }
    &&& forall|page_ptr: PagePtr|
        #![trigger pool.view().contains(page_ptr)]
        pool.view().contains(page_ptr) ==> {
            let page = page_array.spec_index(page_ptr2page_index(page_ptr)).view().view();
            &&& page_ptr_valid(page_ptr)
            &&& page.state == PageState::Free4k { allocator_ptr: Ghost(layout.allocator_4k), state: FreePageAllocatorState::GlobalList }
            &&& page.owning_container == layout.root_container
        }
}

pub open spec fn boot_free_2m_pool_wf(page_array: PageLockedArray, layout: BootKernelLayout, pool: &LinkedList<PagePtr, 233>) -> bool {
    &&& pool.wf()
    &&& pool.view().no_duplicates()
    &&& pool.container_depth.view() == Some(0)
    &&& pool.minor.view() == Some(layout.root_container)
    &&& forall|page_index: PageIndex|
        #![trigger page_array.spec_index(page_index).view().view().state]
        index_valid(NUM_PAGES, page_index) && page_array.spec_index(page_index).view().view().state is Free2m ==> {
            let page = page_array.spec_index(page_index).view().view();
            &&& page.state == PageState::Free2m { allocator_ptr: Ghost(layout.allocator_2m), state: FreePageAllocatorState::GlobalList }
            &&& pool.view().contains(page_index2page_ptr(page_index))
            &&& pool.map().dom().contains(page.free_list_node_storage.addr())
            &&& pool.map().spec_index(page.free_list_node_storage.addr()) == page_index2page_ptr(page_index)
        }
    &&& forall|page_ptr: PagePtr|
        #![trigger pool.view().contains(page_ptr)]
        pool.view().contains(page_ptr) ==> {
            let page = page_array.spec_index(page_ptr2page_index(page_ptr)).view().view();
            &&& page_ptr_2m_valid(page_ptr)
            &&& page.state == PageState::Free2m { allocator_ptr: Ghost(layout.allocator_2m), state: FreePageAllocatorState::GlobalList }
            &&& page.owning_container == layout.root_container
        }
}

pub open spec fn boot_free_1g_pool_wf(page_array: PageLockedArray, layout: BootKernelLayout, pool: &LinkedList<PagePtr, 233>) -> bool {
    &&& pool.wf()
    &&& pool.view().no_duplicates()
    &&& pool.container_depth.view() == Some(0)
    &&& pool.minor.view() == Some(layout.root_container)
    &&& forall|page_index: PageIndex|
        #![trigger page_array.spec_index(page_index).view().view().state]
        index_valid(NUM_PAGES, page_index) && page_array.spec_index(page_index).view().view().state is Free1g ==> {
            let page = page_array.spec_index(page_index).view().view();
            &&& page.state == PageState::Free1g { allocator_ptr: Ghost(layout.allocator_1g), state: FreePageAllocatorState::GlobalList }
            &&& pool.view().contains(page_index2page_ptr(page_index))
            &&& pool.map().dom().contains(page.free_list_node_storage.addr())
            &&& pool.map().spec_index(page.free_list_node_storage.addr()) == page_index2page_ptr(page_index)
        }
    &&& forall|page_ptr: PagePtr|
        #![trigger pool.view().contains(page_ptr)]
        pool.view().contains(page_ptr) ==> {
            let page = page_array.spec_index(page_ptr2page_index(page_ptr)).view().view();
            &&& page_ptr_1g_valid(page_ptr)
            &&& page.state == PageState::Free1g { allocator_ptr: Ghost(layout.allocator_1g), state: FreePageAllocatorState::GlobalList }
            &&& page.owning_container == layout.root_container
        }
}

#[verifier::opaque]
pub open spec fn boot_page_array_ready(
    page_array: PageLockedArray, layout: BootKernelLayout, cpu_page_closure: Set<PagePtr>, manifest_4k: Map<VAddr, MapEntry>,
    free_4k_pool: &LinkedList<PagePtr, 233>, free_2m_pool: &LinkedList<PagePtr, 233>,
    free_1g_pool: &LinkedList<PagePtr, 233>,
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
        #![trigger page_array.spec_index(page_index).view().view().owning_container]
        index_valid(NUM_PAGES, page_index) ==> {
            let page_ptr = page_index2page_ptr(page_index);
            let page = page_array.spec_index(page_index).view().view();
            &&& !page_array.spec_index(page_index).view().locked()
            &&& page.owning_container == layout.root_container
            &&& (page.state matches PageState::Allocated2m { state: Allocated2MPageState::AsContainer }) <==> page_ptr == layout.root_container
            &&& (page.state matches PageState::Allocated2m { state: Allocated2MPageState::AsPcidAllocator }) <==> page_ptr == layout.pcid_allocator
            &&& (page.state matches PageState::Allocated4k { state: Allocated4KPageState::As4KAllocator }) <==> page_ptr == layout.allocator_4k
            &&& (page.state matches PageState::Allocated4k { state: Allocated4KPageState::As2MAllocator }) <==> page_ptr == layout.allocator_2m
            &&& (page.state matches PageState::Allocated4k { state: Allocated4KPageState::As1GAllocator }) <==> page_ptr == layout.allocator_1g
            &&& (page.state matches PageState::Allocated4k { state: Allocated4KPageState::AsScheduler }) <==> page_ptr == layout.scheduler
            &&& (page.state matches PageState::Allocated4k { state: Allocated4KPageState::AsCpuSet }) <==> page_ptr == layout.cpu_set
            &&& (page.state matches PageState::Allocated4k { state: Allocated4KPageState::AsProcess }) <==> page_ptr == layout.root_process
            &&& (page.state == PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: PT_TYPE } }) <==> page_ptr == layout.cpu_pagetable
            &&& (page.state matches PageState::Allocated4k { state: Allocated4KPageState::AsThread }) <==> page_ptr == layout.root_thread
            &&& (page.state matches PageState::Allocated4k { state: Allocated4KPageState::AsEndpoint }) <==> page_ptr == layout.root_endpoint
            &&& (page.state == PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: IOMMU_TYPE } }) <==> page_ptr == layout.iommu_table
            &&& (page.state is Allocated4k && page.state->Allocated4k_state is PageTable && page.state->Allocated4k_state->PageTable_table_type == PT_TYPE) <==> cpu_page_closure.contains(page_ptr)
            &&& (page.state is Allocated4k && page.state->Allocated4k_state is PageTable && page.state->Allocated4k_state->PageTable_table_type == PT_TYPE) ==> page.state->Allocated4k_state->PageTable_pagetable_root == layout.cpu_pagetable
            &&& (page.state is Allocated4k && page.state->Allocated4k_state is PageTable && page.state->Allocated4k_state->PageTable_table_type == IOMMU_TYPE) <==> page_ptr == layout.iommu_l4
            &&& (page.state is Allocated4k && page.state->Allocated4k_state is PageTable && page.state->Allocated4k_state->PageTable_table_type == IOMMU_TYPE) ==> page.state->Allocated4k_state->PageTable_pagetable_root == layout.iommu_table
            &&& !(page.state is Owned4k)
            &&& !(page.state is Owned2m)
            &&& !(page.state is Owned1g)
            &&& !(page.state is Mapped2m)
            &&& !(page.state is Mapped1g)
            &&& forall|pagetable_ptr: RwLockPageTableRoot, va: VAddr|
                #![trigger page.mappings().contains((pagetable_ptr, va))]
                page.mappings().contains((pagetable_ptr, va)) <==> {
                    &&& page.state is Mapped4k
                    &&& pagetable_ptr == layout.cpu_pagetable
                    &&& manifest_4k.dom().contains(va)
                    &&& manifest_4k.spec_index(va).addr == page_ptr
                }
            &&& page.iommu_mappings() == Set::<(RwLockPageTableRoot, VAddr)>::empty()
        }
    &&& forall|va: VAddr|
        #![trigger manifest_4k.dom().contains(va)]
        manifest_4k.dom().contains(va) ==> {
            let page = page_array.spec_index(page_ptr2page_index(manifest_4k.spec_index(va).addr)).view().view();
            &&& page.state is Mapped4k
            &&& page.mappings().contains((layout.cpu_pagetable, va))
            &&& page.owning_container == manifest_4k.spec_index(va).owning_container.view()
        }
}

/// The only new startup trust boundary. It adopts the page-table pages already
/// populated by the bootloader and consumes exactly their concrete
/// `PointsTo<PageMap>` permissions. All process identity, PCID, kernel-prefix,
/// closure, and abstract mapping facts are fixed by the postcondition.
///
/// The L4 and L3 pages stay plain `PageMap`s in the big-lock half. Each L2 page
/// is reinterpreted in place as an `L2PageMap` (the same 512 words, accessed
/// atomically) together with its two ghost tokens, the entry view and the
/// per-entry window locks. This assumes that the bootloader leaves bit 9 (the
/// window lock bit) of every L2 word clear, so that no window lock is held and
/// every window-lock ghost is `None`; the window half therefore starts with no
/// locked window and no stale CPU. L1 pages move to the window half unchanged.
#[verifier::external_body]
pub fn adopt_boot_dom0_pagetable(
    raw_cr3: PageTableRoot, pagetable_ptr: RwLockPageTableRoot, process_ptr: RwLockProcessPtr, kernel_l4_end: usize,
    kernel_entries: Ghost<Seq<PageEntry>>, manifest_4k: Ghost<Map<VAddr, MapEntry>>, root_container: RwLockContainerPtr, rev_maps: Ghost<BootRevMaps>,
    Tracked(l4_tables): Tracked<Map<PageMapPtr, PointsTo<PageMap>>>, Tracked(l3_tables): Tracked<Map<PageMapPtr, PointsTo<PageMap>>>,
    Tracked(l2_tables): Tracked<Map<PageMapPtr, PointsTo<PageMap>>>, Tracked(l1_tables): Tracked<Map<PageMapPtr, PointsTo<PageMap>>>,
) -> (ret: (PageTableHigher<PT_TYPE>, Tracked<PageTableLower<PT_TYPE>>))
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
        boot_dom0_pagetable_model(raw_cr3, process_ptr, kernel_l4_end, kernel_entries.view(), manifest_4k.view(), l4_tables, l3_tables, l2_tables, l1_tables, rev_maps.view()).wf(),
    ensures
        (PageTableC { higher: ret.0, lower: ret.1.view() }).wf(),
        ret.1.view().locked_windows == Set::<WindowVa>::empty(),
        ret.1.view().window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        ret.0.cr3 == raw_cr3,
        ret.0.pcid == Some(1usize),
        ret.0.pcid_value() == 1,
        ret.0.did is None,
        ret.0.proc_ptr == process_ptr,
        ret.0.kernel_l4_end == kernel_l4_end,
        ret.0.kernel_entries == kernel_entries,
        ret.0.l4_table.view() == l4_tables,
        ret.0.l3_tables.view() == l3_tables,
        ret.1.view().l2_perms.dom() == l2_tables.dom(),
        ret.1.view().l1_tables == l1_tables,
        (PageTableC { higher: ret.0, lower: ret.1.view() }).page_closure() =~= l4_tables.dom() + l3_tables.dom() + l2_tables.dom() + l1_tables.dom(),
        (PageTableC { higher: ret.0, lower: ret.1.view() }).mapping_4k() == manifest_4k.view(),
        (PageTableC { higher: ret.0, lower: ret.1.view() }).mapping_2m() == Map::<VAddr, MapEntry>::empty(),
        (PageTableC { higher: ret.0, lower: ret.1.view() }).mapping_1g() == Map::<VAddr, MapEntry>::empty(),
{
    let higher = PageTableHigher {
        cr3: raw_cr3, pcid: Some(1), did: None, kernel_l4_end, l4_table: Tracked(l4_tables), l3_rev_map: Ghost(rev_maps.view().0), l3_tables: Tracked(l3_tables),
        l2_rev_map: Ghost(rev_maps.view().1), mapping_1g: Ghost(Map::empty()), kernel_entries, proc_ptr: process_ptr,
    };
    (higher, Tracked::assume_new())
}

pub open spec fn boot_default_pagetable_ready(default_pagetable: ReadOnlyNode<PageTable<PT_TYPE>>, kernel_l4_end: usize) -> bool {
    &&& default_pagetable.view().wf()
    &&& default_pagetable.view().pcid_value() == KERNEL_DEFAULT_PCID
    &&& default_pagetable.view().is_empty()
    &&& default_pagetable.view().kernel_l4_end == kernel_l4_end
    &&& kernel_l4_end == KERNEL_MEM_END_L4INDEX
}

pub open spec fn boot_pcid_needflush_ready(needflush: PcidNeedFlushArray) -> bool {
    &&& pcid_needflush_wf(needflush)
    &&& forall|cpu_id: CpuId, pcid: Pcid|
        #![trigger needflush.spec_index(cpu_id, pcid)]
        index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) ==> {
            &&& !needflush.spec_index(cpu_id, pcid).locked()
            &&& needflush.spec_index(cpu_id, pcid).view_ghost() is None
            &&& !needflush.spec_index(cpu_id, pcid).view().needflush
        }
}

pub open spec fn boot_cpu_published_ready(published: CpuPublishedArray, default_cr3: PageTableRoot) -> bool {
    forall|cpu_id: CpuId|
        #![trigger published[cpu_id as int].view()]
        #![trigger published[cpu_id as int].owner_cpu()]
        index_valid(NUM_CPUS, cpu_id) ==> {
            &&& published[cpu_id as int].inv()
            &&& published[cpu_id as int].owner_cpu() == cpu_id
            &&& published[cpu_id as int].view() == (default_cr3, KERNEL_DEFAULT_PCID)
        }
}

proof fn prove_boot_container_process_allocator_quota_4k_wf(krnl: &KernelK, layout: BootKernelLayout)
    requires
        krnl.ctn_mp.dom() =~= set![layout.root_container],
        krnl.ctn_mp.spec_index(layout.root_container).view_ghost().owned_processes.view() =~= set![layout.root_process],
        krnl.ctn_mp.spec_index(layout.root_container).view_ghost().owned_threads.view() =~= set![layout.root_thread],
        krnl.ctn_mp.spec_index(layout.root_container).view_ghost().owned_indirect_threads.view() =~= Set::<RwLockThreadPtr>::empty(),
        krnl.ctn_mp.spec_index(layout.root_container).view_rodata().view().depth == 0,
        krnl.ctn_mp.spec_index(layout.root_container).view_rodata().view().allocator_ptr_4k == layout.allocator_4k,
        process_effective_quota_4k(krnl.prc_mp.spec_index(layout.root_process)) == 0,
        thread_effective_quota_4k(krnl.thr_mp.spec_index(layout.root_thread)) == 0,
        krnl.thr_mp.spec_index(layout.root_thread).view().direct_free_quota_pending_4k.view() == 0,
        krnl.allc_4k_mp.spec_index(layout.allocator_4k).quota.view().view() == krnl.allc_4k_mp.spec_index(layout.allocator_4k).total_free_pages.view(),
    ensures
        container_process_allocator_quota_4k_wf(krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_4k_mp),
{
    let ghost owned_processes = krnl.ctn_mp.spec_index(layout.root_container).view_ghost().owned_processes.view();
    let ghost owned_threads = krnl.ctn_mp.spec_index(layout.root_container).view_ghost().owned_threads.view();
    let ghost owned_indirect_threads = krnl.ctn_mp.spec_index(layout.root_container).view_ghost().owned_indirect_threads.view();
    let process_value_4k = |process_ptr: RwLockProcessPtr| process_effective_quota_4k(krnl.prc_mp.spec_index(process_ptr));
    let thread_value_4k = |thread_ptr: RwLockThreadPtr| thread_effective_quota_4k(krnl.thr_mp.spec_index(thread_ptr));
    let direct_pending_value_4k = |thread_ptr: RwLockThreadPtr| krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view() as int;
    let indirect_pending_value_4k = |thread_ptr: RwLockThreadPtr| krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(0) as int;
    let process_fold_4k = |sum: int, process_ptr: RwLockProcessPtr| sum + process_value_4k(process_ptr);
    let direct_process_fold_4k = |sum: int, process_ptr: RwLockProcessPtr| sum + process_effective_quota_4k(krnl.prc_mp.spec_index(process_ptr));
    let thread_fold_4k = |sum: int, thread_ptr: RwLockThreadPtr| sum + thread_value_4k(thread_ptr);
    let direct_thread_fold_4k = |sum: int, thread_ptr: RwLockThreadPtr| sum + thread_effective_quota_4k(krnl.thr_mp.spec_index(thread_ptr));
    let direct_pending_fold_4k = |sum: int, thread_ptr: RwLockThreadPtr| sum + direct_pending_value_4k(thread_ptr);
    let direct_direct_pending_fold_4k = |sum: int, thread_ptr: RwLockThreadPtr| sum + krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view();
    let indirect_pending_fold_4k = |sum: int, thread_ptr: RwLockThreadPtr| sum + indirect_pending_value_4k(thread_ptr);
    let direct_indirect_pending_fold_4k = |sum: int, thread_ptr: RwLockThreadPtr| sum + krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(0);
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

proof fn prove_boot_container_process_allocator_quota_2m_wf(krnl: &KernelK, layout: BootKernelLayout)
    requires
        krnl.ctn_mp.dom() =~= set![layout.root_container],
        krnl.ctn_mp.spec_index(layout.root_container).view_ghost().owned_processes.view() =~= set![layout.root_process],
        krnl.ctn_mp.spec_index(layout.root_container).view_ghost().owned_threads.view() =~= set![layout.root_thread],
        krnl.ctn_mp.spec_index(layout.root_container).view_ghost().owned_indirect_threads.view() =~= Set::<RwLockThreadPtr>::empty(),
        krnl.ctn_mp.spec_index(layout.root_container).view_rodata().view().depth == 0,
        krnl.ctn_mp.spec_index(layout.root_container).view_rodata().view().allocator_ptr_2m == layout.allocator_2m,
        process_effective_quota_2m(krnl.prc_mp.spec_index(layout.root_process)) == 0,
        thread_effective_quota_2m(krnl.thr_mp.spec_index(layout.root_thread)) == 0,
        krnl.thr_mp.spec_index(layout.root_thread).view().direct_free_quota_pending_2m.view() == 0,
        krnl.allc_2m_mp.spec_index(layout.allocator_2m).quota.view().view() == krnl.allc_2m_mp.spec_index(layout.allocator_2m).total_free_pages.view(),
    ensures
        container_process_allocator_quota_2m_wf(krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_2m_mp),
{
    let ghost owned_processes = krnl.ctn_mp.spec_index(layout.root_container).view_ghost().owned_processes.view();
    let ghost owned_threads = krnl.ctn_mp.spec_index(layout.root_container).view_ghost().owned_threads.view();
    let ghost owned_indirect_threads = krnl.ctn_mp.spec_index(layout.root_container).view_ghost().owned_indirect_threads.view();
    let process_value_2m = |process_ptr: RwLockProcessPtr| process_effective_quota_2m(krnl.prc_mp.spec_index(process_ptr));
    let thread_value_2m = |thread_ptr: RwLockThreadPtr| thread_effective_quota_2m(krnl.thr_mp.spec_index(thread_ptr));
    let direct_pending_value_2m = |thread_ptr: RwLockThreadPtr| krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_2m.view() as int;
    let indirect_pending_value_2m = |thread_ptr: RwLockThreadPtr| krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_2m.view().spec_index(0) as int;
    let process_fold_2m = |sum: int, process_ptr: RwLockProcessPtr| sum + process_value_2m(process_ptr);
    let direct_process_fold_2m = |sum: int, process_ptr: RwLockProcessPtr| sum + process_effective_quota_2m(krnl.prc_mp.spec_index(process_ptr));
    let thread_fold_2m = |sum: int, thread_ptr: RwLockThreadPtr| sum + thread_value_2m(thread_ptr);
    let direct_thread_fold_2m = |sum: int, thread_ptr: RwLockThreadPtr| sum + thread_effective_quota_2m(krnl.thr_mp.spec_index(thread_ptr));
    let direct_pending_fold_2m = |sum: int, thread_ptr: RwLockThreadPtr| sum + direct_pending_value_2m(thread_ptr);
    let direct_direct_pending_fold_2m = |sum: int, thread_ptr: RwLockThreadPtr| sum + krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_2m.view();
    let indirect_pending_fold_2m = |sum: int, thread_ptr: RwLockThreadPtr| sum + indirect_pending_value_2m(thread_ptr);
    let direct_indirect_pending_fold_2m = |sum: int, thread_ptr: RwLockThreadPtr| sum + krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_2m.view().spec_index(0);
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

proof fn prove_boot_container_process_allocator_quota_1g_wf(krnl: &KernelK, layout: BootKernelLayout)
    requires
        krnl.ctn_mp.dom() =~= set![layout.root_container],
        krnl.ctn_mp.spec_index(layout.root_container).view_ghost().owned_processes.view() =~= set![layout.root_process],
        krnl.ctn_mp.spec_index(layout.root_container).view_ghost().owned_threads.view() =~= set![layout.root_thread],
        krnl.ctn_mp.spec_index(layout.root_container).view_ghost().owned_indirect_threads.view() =~= Set::<RwLockThreadPtr>::empty(),
        krnl.ctn_mp.spec_index(layout.root_container).view_rodata().view().depth == 0,
        krnl.ctn_mp.spec_index(layout.root_container).view_rodata().view().allocator_ptr_1g == layout.allocator_1g,
        process_effective_quota_1g(krnl.prc_mp.spec_index(layout.root_process)) == 0,
        thread_effective_quota_1g(krnl.thr_mp.spec_index(layout.root_thread)) == 0,
        krnl.thr_mp.spec_index(layout.root_thread).view().direct_free_quota_pending_1g.view() == 0,
        krnl.allc_1g_mp.spec_index(layout.allocator_1g).quota.view().view() == krnl.allc_1g_mp.spec_index(layout.allocator_1g).total_free_pages.view(),
    ensures
        container_process_allocator_quota_1g_wf(krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_1g_mp),
{
    let ghost owned_processes = krnl.ctn_mp.spec_index(layout.root_container).view_ghost().owned_processes.view();
    let ghost owned_threads = krnl.ctn_mp.spec_index(layout.root_container).view_ghost().owned_threads.view();
    let ghost owned_indirect_threads = krnl.ctn_mp.spec_index(layout.root_container).view_ghost().owned_indirect_threads.view();
    let process_value_1g = |process_ptr: RwLockProcessPtr| process_effective_quota_1g(krnl.prc_mp.spec_index(process_ptr));
    let thread_value_1g = |thread_ptr: RwLockThreadPtr| thread_effective_quota_1g(krnl.thr_mp.spec_index(thread_ptr));
    let direct_pending_value_1g = |thread_ptr: RwLockThreadPtr| krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_1g.view() as int;
    let indirect_pending_value_1g = |thread_ptr: RwLockThreadPtr| krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_1g.view().spec_index(0) as int;
    let process_fold_1g = |sum: int, process_ptr: RwLockProcessPtr| sum + process_value_1g(process_ptr);
    let direct_process_fold_1g = |sum: int, process_ptr: RwLockProcessPtr| sum + process_effective_quota_1g(krnl.prc_mp.spec_index(process_ptr));
    let thread_fold_1g = |sum: int, thread_ptr: RwLockThreadPtr| sum + thread_value_1g(thread_ptr);
    let direct_thread_fold_1g = |sum: int, thread_ptr: RwLockThreadPtr| sum + thread_effective_quota_1g(krnl.thr_mp.spec_index(thread_ptr));
    let direct_pending_fold_1g = |sum: int, thread_ptr: RwLockThreadPtr| sum + direct_pending_value_1g(thread_ptr);
    let direct_direct_pending_fold_1g = |sum: int, thread_ptr: RwLockThreadPtr| sum + krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_1g.view();
    let indirect_pending_fold_1g = |sum: int, thread_ptr: RwLockThreadPtr| sum + indirect_pending_value_1g(thread_ptr);
    let direct_indirect_pending_fold_1g = |sum: int, thread_ptr: RwLockThreadPtr| sum + krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_1g.view().spec_index(0);
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

proof fn prove_boot_container_page_owner_wf(
    krnl: &KernelK, layout: BootKernelLayout, page_array: PageLockedArray, cpu_page_closure: Set<PagePtr>, manifest_4k: Map<VAddr, MapEntry>,
    free_4k_pool: &LinkedList<PagePtr, 233>, free_2m_pool: &LinkedList<PagePtr, 233>,
    free_1g_pool: &LinkedList<PagePtr, 233>, all_valid_pages: Set<PagePtr>,
)
    requires
        krnl.pg_arr == page_array,
        boot_page_array_ready(page_array, layout, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool),
        krnl.ctn_mp.dom() =~= set![layout.root_container],
        krnl.ctn_mp.spec_index(layout.root_container).view().owned_pages.view() =~= all_valid_pages,
        forall|page_ptr: PagePtr|
            #![trigger all_valid_pages.contains(page_ptr)]
            all_valid_pages.contains(page_ptr) <==> page_ptr_valid(page_ptr),
    ensures
        container_page_owner_wf(krnl.ctn_mp, krnl.pg_arr),
{ reveal(container_page_owner_wf); reveal(boot_page_array_ready); page_ptr_valid_imply_page_index_valid(); page_index_valid_imply_page_ptr_valid(); page_index_roundtrip(); }

/// Every boot object page is named by the root container, and the root container has no parent.
proof fn prove_boot_page_object_owner_wf(
    krnl: &KernelK, layout: BootKernelLayout, page_array: PageLockedArray, cpu_page_closure: Set<PagePtr>, manifest_4k: Map<VAddr, MapEntry>,
    free_4k_pool: &LinkedList<PagePtr, 233>, free_2m_pool: &LinkedList<PagePtr, 233>, free_1g_pool: &LinkedList<PagePtr, 233>,
)
    requires
        krnl.pg_arr == page_array,
        boot_page_array_ready(page_array, layout, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool),
        krnl.ctn_mp.spec_index(layout.root_container).view_rodata().view() == (ContainerRO {
            parent: None, depth: 0, scheduler: layout.scheduler, pcid_allocator: layout.pcid_allocator, cpu_set: layout.cpu_set,
            allocator_ptr_4k: layout.allocator_4k, allocator_ptr_2m: layout.allocator_2m, allocator_ptr_1g: layout.allocator_1g,
        }),
        krnl.ctn_mp.spec_index(layout.root_container).view_ghost().owned_threads.view() =~= set![layout.root_thread],
        krnl.ctn_mp.spec_index(layout.root_container).view_ghost().owned_endpoints.view() =~= set![layout.root_endpoint],
    ensures
        page_object_owner_wf(krnl.pg_arr, krnl.ctn_mp, krnl.thr_mp),
{ reveal(page_object_owner_wf); reveal(boot_page_array_ready); }

/// Every boot page and the root process belong to the root container.
proof fn prove_boot_process_kernel_pages_owner_wf(
    krnl: &KernelK, layout: BootKernelLayout, page_array: PageLockedArray, cpu_page_closure: Set<PagePtr>, manifest_4k: Map<VAddr, MapEntry>,
    free_4k_pool: &LinkedList<PagePtr, 233>, free_2m_pool: &LinkedList<PagePtr, 233>,
    free_1g_pool: &LinkedList<PagePtr, 233>,
)
    requires
        krnl.pg_arr == page_array,
        boot_page_array_ready(page_array, layout, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool),
        krnl.prc_mp.dom() =~= set![layout.root_process],
        krnl.prc_mp.spec_index(layout.root_process).view_rodata().view().owning_container == layout.root_container,
        process_pages_wf(krnl.pg_arr, krnl.prc_mp),
        pagetable_pages_wf(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr),
        iommu_table_pages_wf(krnl.it_mp, krnl.pg_arr),
        process_pagetable_match(krnl.prc_mp, krnl.pt_mp),
        process_iommu_table_match(krnl.prc_mp, krnl.it_mp),
    ensures
        process_kernel_pages_owner_wf(krnl.pg_arr, krnl.prc_mp, krnl.pt_mp, krnl.it_mp),
{ reveal(process_kernel_pages_owner_wf); reveal(boot_page_array_ready); reveal(process_pages_wf); reveal(pagetable_pages_wf); reveal(iommu_table_pages_wf); reveal(process_pagetable_match); reveal(process_iommu_table_match); }

proof fn prove_boot_iommu_table_pages_wf(
    krnl: &KernelK, layout: BootKernelLayout, page_array: PageLockedArray, cpu_page_closure: Set<PagePtr>,
    manifest_4k: Map<VAddr, MapEntry>, free_4k_pool: &LinkedList<PagePtr, 233>,
    free_2m_pool: &LinkedList<PagePtr, 233>, free_1g_pool: &LinkedList<PagePtr, 233>,
)
    requires
        krnl.pg_arr == page_array,
        page_ptr_valid(layout.iommu_table),
        page_ptr_valid(layout.iommu_l4),
        boot_page_array_ready(page_array, layout, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool),
        krnl.it_mp.dom() =~= set![layout.iommu_table],
        krnl.it_mp.spec_index(layout.iommu_table).view().page_closure() =~= set![layout.iommu_l4],
    ensures
        iommu_table_pages_wf(krnl.it_mp, krnl.pg_arr),
{ reveal(iommu_table_pages_wf); reveal(boot_page_array_ready); page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); }

proof fn prove_boot_container_thread_scheduler_wf(krnl: &KernelK, layout: BootKernelLayout, scheduler_node_addr: usize)
    requires
        krnl.ctn_mp.spec_index(layout.root_container).view_rodata().view().scheduler == layout.scheduler,
        krnl.thr_mp.dom() =~= set![layout.root_thread],
        krnl.thr_mp.spec_index(layout.root_thread).view().state == (ThreadState::SCHEDULED { cpu_id: 0 }),
        krnl.thr_mp.spec_index(layout.root_thread).view().owning_container == layout.root_container,
        krnl.thr_mp.spec_index(layout.root_thread).view().scheduler_linkedlist_node.addr() == scheduler_node_addr,
        krnl.sched_mp.dom() =~= set![layout.scheduler],
        krnl.sched_mp.spec_index(layout.scheduler).owning_container == layout.root_container,
        forall|cpu_id: CpuId| #![trigger krnl.sched_mp.spec_index(layout.scheduler).shards.spec_index(cpu_id)] index_valid(NUM_CPUS, cpu_id) ==> {
            &&& krnl.sched_mp.spec_index(layout.scheduler).shard(cpu_id).queue.view() == if cpu_id == 0 { seq![layout.root_thread] } else { Seq::<RwLockThreadPtr>::empty() }
            &&& krnl.sched_mp.spec_index(layout.scheduler).shard(cpu_id).queue.map() == if cpu_id == 0 {
                Map::<usize, RwLockThreadPtr>::empty().insert(scheduler_node_addr, layout.root_thread)
            } else { Map::<usize, RwLockThreadPtr>::empty() }
        },
    ensures
        container_thread_scheduler_wf(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp),
{
    reveal(container_thread_scheduler_wf);
    let root_queue = krnl.sched_mp.spec_index(layout.scheduler).shard(0).queue;
    assert(root_queue.view().contains(layout.root_thread)) by { root_queue.view().lemma_index_contains(0); };
}

proof fn prove_boot_process_thread_wf(krnl: &KernelK, layout: BootKernelLayout, process_node_addr: usize)
    requires
        krnl.prc_mp.dom() =~= set![layout.root_process],
        !krnl.prc_mp.spec_index(layout.root_process).view().zombie,
        krnl.prc_mp.spec_index(layout.root_process).view().owned_threads.view() =~= seq![layout.root_thread],
        krnl.prc_mp.spec_index(layout.root_process).view().owned_threads.map() =~= Map::<usize, RwLockThreadPtr>::empty().insert(process_node_addr, layout.root_thread),
        krnl.prc_mp.spec_index(layout.root_process).view_rodata().view().owning_container == layout.root_container,
        krnl.prc_mp.spec_index(layout.root_process).view_rodata().view().container_depth == 0,
        krnl.prc_mp.spec_index(layout.root_process).view_rodata().view().depth == 0,
        krnl.prc_mp.spec_index(layout.root_process).view().pagetable == layout.cpu_pagetable,
        krnl.thr_mp.dom() =~= set![layout.root_thread],
        krnl.thr_mp.spec_index(layout.root_thread).view().owning_proc == layout.root_process,
        krnl.thr_mp.spec_index(layout.root_thread).view().owning_container == layout.root_container,
        krnl.thr_mp.spec_index(layout.root_thread).view().container_depth == 0,
        krnl.thr_mp.spec_index(layout.root_thread).view().process_depth == 0,
        krnl.thr_mp.spec_index(layout.root_thread).view().proc_pagetable_ptr == layout.cpu_pagetable,
        krnl.thr_mp.spec_index(layout.root_thread).view().proc_linkedlist_node.addr() == process_node_addr,
        !krnl.thr_mp.spec_index(layout.root_thread).view().proc_linkedlist_node.is_init(),
        !krnl.thr_mp.spec_index(layout.root_thread).being_killed(),
    ensures
        process_thread_wf(krnl.prc_mp, krnl.thr_mp),
{ reveal(process_thread_wf); krnl.prc_mp.spec_index(layout.root_process).view().owned_threads.view().lemma_index_contains(0); }

/// Operation summary of `finish_init_from_boot`: every field of the kernel object it assembles.
pub open spec fn boot_kernel_state(
    krnl: &KernelK, layout: BootKernelLayout, kernel_l4_end: usize, initial_regs: Registers, kernel_entries: Seq<PageEntry>, manifest_4k: Map<VAddr, MapEntry>,
    page_array: PageLockedArray, pcid_needflush: PcidNeedFlushArray, cpu_published: CpuPublishedArray, default_pagetable: ReadOnlyNode<PageTable<PT_TYPE>>,
    cpu_page_closure: Set<PagePtr>, free_4k_pool: &LinkedList<PagePtr, 233>, free_2m_pool: &LinkedList<PagePtr, 233>,
    free_1g_pool: &LinkedList<PagePtr, 233>, owned_pages: Set<PagePtr>, owned_pci_functions: Set<PciBdf>, scheduler_node_addr: usize,
    process_node_addr: usize,
) -> bool {
    &&& krnl.rt_ctn == layout.root_container
    &&& krnl.pg_arr == page_array
    &&& krnl.pcid_needflush == pcid_needflush
    &&& krnl.cpu_published == cpu_published
    &&& krnl.dflt_pt == default_pagetable
    &&& krnl.cpu_arr.inv()
    &&& forall|cpu_id: CpuId| #![trigger krnl.cpu_arr.spec_index(cpu_id)] index_valid(NUM_CPUS, cpu_id) ==> {
        &&& krnl.cpu_arr.spec_index(cpu_id).view().inv()
        &&& !krnl.cpu_arr.spec_index(cpu_id).view().locked()
        &&& !krnl.cpu_arr.spec_index(cpu_id).view().being_killed()
        &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == layout.root_container
        &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().container_depth == 0
        &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().state == if cpu_id == 0 { CpuState::Idle } else { CpuState::Off }
        &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == default_pagetable.view().cr3
        &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == KERNEL_DEFAULT_PCID
    }
    &&& krnl.cpu_tlb.inv()
    &&& forall|cpu_id: CpuId, pcid: Pcid| #![trigger krnl.cpu_tlb.spec_index((cpu_id, pcid))] index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) ==> krnl.cpu_tlb.spec_index((cpu_id, pcid)).is_empty()
    &&& krnl.iommu_tlb.inv()
    &&& forall|did: VtdDomainId| #![trigger krnl.iommu_tlb.spec_index(did)] vtd_domain_id_valid(did) ==> krnl.iommu_tlb.spec_index(did).is_empty()
    &&& krnl.iommu_tlb.context_cache() == Map::<PciBdf, (PageTableRoot, VtdDomainId)>::empty()
    &&& krnl.irt.inv()
    &&& krnl.irt.locking_thread() is None
    &&& !krnl.irt.locked()
    &&& !krnl.irt.being_killed()
    &&& krnl.irt.view().wf()
    &&& krnl.irt.view().table_base() == layout.iommu_root_table_base()
    &&& forall|bus: usize, device: usize, function: usize| #![trigger krnl.irt.view().spec_index_iommu_root(bus, device, function)]
        pci_bdf_valid(bus, device, function) ==> krnl.irt.view().spec_index_iommu_root(bus, device, function) is None
    &&& forall|bus: usize, device: usize, function: usize| #![trigger krnl.irt.view().spec_index_owner(bus, device, function)]
        pci_bdf_valid(bus, device, function) ==> krnl.irt.view().spec_index_owner(bus, device, function) == layout.root_process
    &&& krnl.pt_mp.perms_wf()
    &&& krnl.pt_mp.dom() =~= set![layout.cpu_pagetable]
    &&& krnl.pt_mp.spec_index(layout.cpu_pagetable).is_init()
    &&& krnl.pt_mp.spec_index(layout.cpu_pagetable).inv()
    &&& !krnl.pt_mp.spec_index(layout.cpu_pagetable).being_killed()
    &&& krnl.pt_mp.spec_index(layout.cpu_pagetable).locking_thread() is None
    &&& krnl.pt_lower.view().dom() =~= set![layout.cpu_pagetable]
    &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), layout.cpu_pagetable).wf()
    &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), layout.cpu_pagetable).lower.locked_windows == Set::<WindowVa>::empty()
    &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), layout.cpu_pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty()
    &&& krnl.pt_mp.spec_index(layout.cpu_pagetable).view().cr3 == layout.cpu_cr3
    &&& krnl.pt_mp.spec_index(layout.cpu_pagetable).view().pcid == Some(1usize)
    &&& krnl.pt_mp.spec_index(layout.cpu_pagetable).view().pcid_value() == 1
    &&& krnl.pt_mp.spec_index(layout.cpu_pagetable).view().proc_ptr == layout.root_process
    &&& krnl.pt_mp.spec_index(layout.cpu_pagetable).view().kernel_l4_end == kernel_l4_end
    &&& krnl.pt_mp.spec_index(layout.cpu_pagetable).view().kernel_entries.view() == kernel_entries
    &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), layout.cpu_pagetable).page_closure() =~= cpu_page_closure
    &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), layout.cpu_pagetable).mapping_4k() == manifest_4k
    &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), layout.cpu_pagetable).mapping_2m() == Map::<VAddr, MapEntry>::empty()
    &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), layout.cpu_pagetable).mapping_1g() == Map::<VAddr, MapEntry>::empty()
    &&& krnl.it_mp.perms_wf()
    &&& krnl.it_mp.dom() =~= set![layout.iommu_table]
    &&& krnl.it_mp.spec_index(layout.iommu_table).is_init()
    &&& krnl.it_mp.spec_index(layout.iommu_table).inv()
    &&& !krnl.it_mp.spec_index(layout.iommu_table).being_killed()
    &&& krnl.it_mp.spec_index(layout.iommu_table).locking_thread() is None
    &&& krnl.it_mp.spec_index(layout.iommu_table).view().wf()
    &&& krnl.it_mp.spec_index(layout.iommu_table).view().cr3 == layout.iommu_l4
    &&& krnl.it_mp.spec_index(layout.iommu_table).view().pcid is None
    &&& krnl.it_mp.spec_index(layout.iommu_table).view().did is None
    &&& krnl.it_mp.spec_index(layout.iommu_table).view().kernel_l4_end == 0
    &&& krnl.it_mp.spec_index(layout.iommu_table).view().kernel_entries.view() =~= Seq::<PageEntry>::empty()
    &&& krnl.it_mp.spec_index(layout.iommu_table).view().is_empty()
    &&& krnl.it_mp.spec_index(layout.iommu_table).view().page_closure() =~= set![layout.iommu_l4]
    &&& krnl.it_mp.spec_index(layout.iommu_table).view().proc_ptr == layout.root_process
    &&& krnl.ctn_mp.perms_wf()
    &&& krnl.ctn_mp.dom() =~= set![layout.root_container]
    &&& krnl.ctn_mp.spec_index(layout.root_container).is_init()
    &&& krnl.ctn_mp.spec_index(layout.root_container).inv()
    &&& !krnl.ctn_mp.spec_index(layout.root_container).being_killed()
    &&& krnl.ctn_mp.spec_index(layout.root_container).locking_thread() is None
    &&& krnl.ctn_mp.spec_index(layout.root_container).view().inv()
    &&& krnl.ctn_mp.spec_index(layout.root_container).view().parent_linkedlist_node.is_init()
    &&& krnl.ctn_mp.spec_index(layout.root_container).view().children.view() == Seq::<RwLockContainerPtr>::empty()
    &&& krnl.ctn_mp.spec_index(layout.root_container).view().children.map() == Map::<usize, RwLockContainerPtr>::empty()
    &&& krnl.ctn_mp.spec_index(layout.root_container).view().root_process == layout.root_process
    &&& !krnl.ctn_mp.spec_index(layout.root_container).view().zombie
    &&& krnl.ctn_mp.spec_index(layout.root_container).view().owned_pages.view() == owned_pages
    &&& krnl.ctn_mp.spec_index(layout.root_container).view_rodata().owner_addr() == layout.root_container
    &&& krnl.ctn_mp.spec_index(layout.root_container).view_rodata().view() == (ContainerRO {
        parent: None, depth: 0, scheduler: layout.scheduler, pcid_allocator: layout.pcid_allocator, cpu_set: layout.cpu_set,
        allocator_ptr_4k: layout.allocator_4k, allocator_ptr_2m: layout.allocator_2m, allocator_ptr_1g: layout.allocator_1g,
    })
    &&& krnl.ctn_mp.spec_index(layout.root_container).view_ghost() == (ContainerGhost {
        uppertree_seq: Ghost(Seq::empty()), subtree_set: Ghost(Set::empty()), owned_processes: Ghost(Set::empty().insert(layout.root_process)),
        owned_threads: Ghost(Set::empty().insert(layout.root_thread)), owned_indirect_threads: Ghost(Set::empty()), owned_endpoints: Ghost(Set::empty().insert(layout.root_endpoint)), retire_ready: false,
    })
    &&& krnl.sched_mp.perms_wf()
    &&& krnl.sched_mp.dom() =~= set![layout.scheduler]
    &&& krnl.sched_mp.spec_index(layout.scheduler).inv()
    &&& krnl.sched_mp.spec_index(layout.scheduler).owning_container == layout.root_container
    &&& forall|cpu_id: CpuId| #![trigger krnl.sched_mp.spec_index(layout.scheduler).shards.spec_index(cpu_id)] index_valid(NUM_CPUS, cpu_id) ==> {
        &&& !krnl.sched_mp.spec_index(layout.scheduler).shards.spec_index(cpu_id).view().locked()
        &&& krnl.sched_mp.spec_index(layout.scheduler).shard(cpu_id).queue.view() == if cpu_id == 0 { seq![layout.root_thread] } else { Seq::<RwLockThreadPtr>::empty() }
        &&& krnl.sched_mp.spec_index(layout.scheduler).shard(cpu_id).queue.map() == if cpu_id == 0 {
            Map::<usize, RwLockThreadPtr>::empty().insert(scheduler_node_addr, layout.root_thread)
        } else { Map::<usize, RwLockThreadPtr>::empty() }
    }
    &&& krnl.pcid_allc_mp.perms_wf()
    &&& krnl.pcid_allc_mp.dom() =~= set![layout.pcid_allocator]
    &&& krnl.pcid_allc_mp.spec_index(layout.pcid_allocator).is_init()
    &&& krnl.pcid_allc_mp.spec_index(layout.pcid_allocator).inv()
    &&& !krnl.pcid_allc_mp.spec_index(layout.pcid_allocator).being_killed()
    &&& krnl.pcid_allc_mp.spec_index(layout.pcid_allocator).locking_thread() is None
    &&& krnl.pcid_allc_mp.spec_index(layout.pcid_allocator).view().inv()
    &&& krnl.pcid_allc_mp.spec_index(layout.pcid_allocator).view().owning_container.view() == layout.root_container
    &&& krnl.pcid_allc_mp.spec_index(layout.pcid_allocator).view().container_depth.view() == 0
    &&& krnl.pcid_allc_mp.spec_index(layout.pcid_allocator).view().ref_counters.spec_index(1) == 1
    &&& krnl.pcid_allc_mp.spec_index(layout.pcid_allocator).view().id_to_proc.view().spec_index(1) =~= set![layout.root_process]
    &&& forall|id: Pcid| #![trigger krnl.pcid_allc_mp.spec_index(layout.pcid_allocator).view().ref_counters.spec_index(id)] pcid_valid(id) && id != 1 ==> krnl.pcid_allc_mp.spec_index(layout.pcid_allocator).view().ref_counters.spec_index(id) == 0
    &&& forall|id: Pcid| #![trigger krnl.pcid_allc_mp.spec_index(layout.pcid_allocator).view().id_to_proc.view().spec_index(id as int)] pcid_valid(id) && id != 1 ==> krnl.pcid_allc_mp.spec_index(layout.pcid_allocator).view().id_to_proc.view().spec_index(id as int).is_empty()
    &&& krnl.cpu_set_mp.perms_wf()
    &&& krnl.cpu_set_mp.dom() =~= set![layout.cpu_set]
    &&& krnl.cpu_set_mp.spec_index(layout.cpu_set).is_init()
    &&& krnl.cpu_set_mp.spec_index(layout.cpu_set).inv()
    &&& !krnl.cpu_set_mp.spec_index(layout.cpu_set).being_killed()
    &&& krnl.cpu_set_mp.spec_index(layout.cpu_set).locking_thread() is None
    &&& krnl.cpu_set_mp.spec_index(layout.cpu_set).view().inv()
    &&& krnl.cpu_set_mp.spec_index(layout.cpu_set).view().owning_container.view() == layout.root_container
    &&& krnl.cpu_set_mp.spec_index(layout.cpu_set).view().container_depth.view() == 0
    &&& forall|cpu_id: CpuId| #![trigger krnl.cpu_set_mp.spec_index(layout.cpu_set).view().owned_cpus.view().contains(cpu_id)] krnl.cpu_set_mp.spec_index(layout.cpu_set).view().owned_cpus.view().contains(cpu_id) <==> index_valid(NUM_CPUS, cpu_id)
    &&& forall|cpu_id: CpuId| #![trigger krnl.cpu_set_mp.spec_index(layout.cpu_set).view().owned_cpus.closed_view().contains(cpu_id)]
        krnl.cpu_set_mp.spec_index(layout.cpu_set).view().owned_cpus.closed_view().contains(cpu_id) <==> index_valid(NUM_CPUS, cpu_id) && cpu_id != 0
    &&& krnl.prc_mp.perms_wf()
    &&& krnl.prc_mp.dom() =~= set![layout.root_process]
    &&& krnl.prc_mp.spec_index(layout.root_process).is_init()
    &&& krnl.prc_mp.spec_index(layout.root_process).inv()
    &&& !krnl.prc_mp.spec_index(layout.root_process).being_killed()
    &&& krnl.prc_mp.spec_index(layout.root_process).locking_thread() is None
    &&& krnl.prc_mp.spec_index(layout.root_process).view().inv()
    &&& !krnl.prc_mp.spec_index(layout.root_process).view().zombie
    &&& krnl.prc_mp.spec_index(layout.root_process).view().state.view() is Running
    &&& krnl.prc_mp.spec_index(layout.root_process).view().pcid == 1
    &&& krnl.prc_mp.spec_index(layout.root_process).view().pagetable == layout.cpu_pagetable
    &&& krnl.prc_mp.spec_index(layout.root_process).view().iommu_table == Some(layout.iommu_table)
    &&& krnl.prc_mp.spec_index(layout.root_process).view().quota_4k == 0
    &&& krnl.prc_mp.spec_index(layout.root_process).view().quota_2m == 0
    &&& krnl.prc_mp.spec_index(layout.root_process).view().quota_1g == 0
    &&& krnl.prc_mp.spec_index(layout.root_process).view().parent_linkedlist_node.is_init()
    &&& krnl.prc_mp.spec_index(layout.root_process).view().children.view() == Seq::<RwLockProcessPtr>::empty()
    &&& krnl.prc_mp.spec_index(layout.root_process).view().owned_threads.view() =~= seq![layout.root_thread]
    &&& krnl.prc_mp.spec_index(layout.root_process).view().owned_threads.map() =~= Map::<usize, RwLockThreadPtr>::empty().insert(process_node_addr, layout.root_thread)
    &&& krnl.prc_mp.spec_index(layout.root_process).view_rodata().owner_addr() == layout.root_process
    &&& krnl.prc_mp.spec_index(layout.root_process).view_rodata().view() == (ProcessRO {
        owning_container: layout.root_container, container_depth: 0, parent: None, depth: 0, pagetable: layout.cpu_pagetable, cr3: layout.cpu_cr3,
        iommu_cr3: Some(layout.iommu_l4), iommu_table_ptr: Some(layout.iommu_table), pcid: 1,
    })
    &&& krnl.prc_mp.spec_index(layout.root_process).view_ghost() == (ProcessGhost { uppertree_seq: Ghost(Seq::empty()), subtree_set: Ghost(Set::empty()), owned_pci_functions: Ghost(owned_pci_functions) })
    &&& krnl.thr_mp.perms_wf()
    &&& krnl.thr_mp.dom() =~= set![layout.root_thread]
    &&& krnl.thr_mp.spec_index(layout.root_thread).is_init()
    &&& krnl.thr_mp.spec_index(layout.root_thread).inv()
    &&& !krnl.thr_mp.spec_index(layout.root_thread).being_killed()
    &&& krnl.thr_mp.spec_index(layout.root_thread).locking_thread() is None
    &&& krnl.thr_mp.spec_index(layout.root_thread).view().state == (ThreadState::SCHEDULED { cpu_id: 0 })
    &&& krnl.thr_mp.spec_index(layout.root_thread).view().last_cpu == 0
    &&& krnl.thr_mp.spec_index(layout.root_thread).view().owning_container == layout.root_container
    &&& krnl.thr_mp.spec_index(layout.root_thread).view().container_depth == 0
    &&& krnl.thr_mp.spec_index(layout.root_thread).view().owning_proc == layout.root_process
    &&& krnl.thr_mp.spec_index(layout.root_thread).view().process_depth == 0
    &&& krnl.thr_mp.spec_index(layout.root_thread).view().proc_pagetable_ptr == layout.cpu_pagetable
    &&& krnl.thr_mp.spec_index(layout.root_thread).view().upper_container_seq.view() == Seq::<RwLockContainerPtr>::empty()
    &&& krnl.thr_mp.spec_index(layout.root_thread).view().endpoint_descriptors.spec_index(0) == Some(layout.root_endpoint)
    &&& forall|endpoint_index: EndpointIdx| #![trigger krnl.thr_mp.spec_index(layout.root_thread).view().endpoint_descriptors.spec_index(endpoint_index)]
        edp_idx_valid(endpoint_index) && endpoint_index != 0 ==> krnl.thr_mp.spec_index(layout.root_thread).view().endpoint_descriptors.spec_index(endpoint_index) is None
    &&& krnl.thr_mp.spec_index(layout.root_thread).view().ipc_payload is Empty
    &&& krnl.thr_mp.spec_index(layout.root_thread).view().error_code is None
    &&& krnl.thr_mp.spec_index(layout.root_thread).view().caller is None
    &&& krnl.thr_mp.spec_index(layout.root_thread).view().callee is None
    &&& krnl.thr_mp.spec_index(layout.root_thread).view().trap_frame.is_some()
    &&& *krnl.thr_mp.spec_index(layout.root_thread).view().trap_frame.get_some_0() == initial_regs
    &&& krnl.thr_mp.spec_index(layout.root_thread).view().blocking_endpoint_ptr is None
    &&& krnl.thr_mp.spec_index(layout.root_thread).view().blocking_endpoint_index is None
    &&& krnl.thr_mp.spec_index(layout.root_thread).view().free_quota_pending_clean()
    &&& krnl.thr_mp.spec_index(layout.root_thread).view().syscall_progress.view() is None
    &&& !krnl.thr_mp.spec_index(layout.root_thread).view_ghost().exited
    &&& krnl.thr_mp.spec_index(layout.root_thread).view().temp_alloc_clean()
    &&& krnl.thr_mp.spec_index(layout.root_thread).view().quota_4k == 0
    &&& krnl.thr_mp.spec_index(layout.root_thread).view().quota_2m == 0
    &&& krnl.thr_mp.spec_index(layout.root_thread).view().quota_1g == 0
    &&& krnl.thr_mp.spec_index(layout.root_thread).view().endpoint_linkedlist_node.is_init()
    &&& !krnl.thr_mp.spec_index(layout.root_thread).view().scheduler_linkedlist_node.is_init()
    &&& !krnl.thr_mp.spec_index(layout.root_thread).view().proc_linkedlist_node.is_init()
    &&& krnl.thr_mp.spec_index(layout.root_thread).view().scheduler_linkedlist_node.addr() == scheduler_node_addr
    &&& krnl.thr_mp.spec_index(layout.root_thread).view().proc_linkedlist_node.addr() == process_node_addr
    &&& krnl.ep_mp.perms_wf()
    &&& krnl.ep_mp.dom() =~= set![layout.root_endpoint]
    &&& krnl.ep_mp.spec_index(layout.root_endpoint).is_init()
    &&& krnl.ep_mp.spec_index(layout.root_endpoint).inv()
    &&& !krnl.ep_mp.spec_index(layout.root_endpoint).being_killed()
    &&& krnl.ep_mp.spec_index(layout.root_endpoint).locking_thread() is None
    &&& krnl.ep_mp.spec_index(layout.root_endpoint).view().inv()
    &&& krnl.ep_mp.spec_index(layout.root_endpoint).view().queue.view() == Seq::<RwLockThreadPtr>::empty()
    &&& krnl.ep_mp.spec_index(layout.root_endpoint).view().queue.map() == Map::<usize, RwLockThreadPtr>::empty()
    &&& krnl.ep_mp.spec_index(layout.root_endpoint).view().queue.container_depth.view() == Some(0)
    &&& krnl.ep_mp.spec_index(layout.root_endpoint).view().queue.lock_minor() == seq![layout.root_endpoint]
    &&& krnl.ep_mp.spec_index(layout.root_endpoint).view().queue_state is RECEIVE
    &&& krnl.ep_mp.spec_index(layout.root_endpoint).view().rf_counter == 1
    &&& krnl.ep_mp.spec_index(layout.root_endpoint).view().owning_threads.view() =~= set![(layout.root_thread, 0usize)]
    &&& krnl.ep_mp.spec_index(layout.root_endpoint).view().owning_container == layout.root_container
    &&& krnl.allc_4k_mp.perms_wf()
    &&& krnl.allc_4k_mp.dom() =~= set![layout.allocator_4k]
    &&& krnl.allc_4k_mp.spec_index(layout.allocator_4k).inv()
    &&& krnl.allc_4k_mp.spec_index(layout.allocator_4k).owning_container == layout.root_container
    &&& krnl.allc_4k_mp.spec_index(layout.allocator_4k).total_free_pages.view() == free_4k_pool.view().len()
    &&& krnl.allc_4k_mp.spec_index(layout.allocator_4k).quota.view().view() == free_4k_pool.view().len()
    &&& krnl.allc_4k_mp.spec_index(layout.allocator_4k).quota.view().container_depth == 0
    &&& krnl.allc_4k_mp.spec_index(layout.allocator_4k).quota.view().lock_minor() == seq![layout.root_container]
    &&& !krnl.allc_4k_mp.spec_index(layout.allocator_4k).quota.locked()
    &&& krnl.allc_4k_mp.spec_index(layout.allocator_4k).global_pool.view().view() == free_4k_pool.view()
    &&& krnl.allc_4k_mp.spec_index(layout.allocator_4k).global_pool.view().map() == free_4k_pool.map()
    &&& !krnl.allc_4k_mp.spec_index(layout.allocator_4k).global_pool.locked()
    &&& forall|cpu_id: CpuId| #![trigger krnl.allc_4k_mp.spec_index(layout.allocator_4k).cpu_caches.spec_index(cpu_id)] index_valid(NUM_CPUS, cpu_id) ==> {
        &&& krnl.allc_4k_mp.spec_index(layout.allocator_4k).cpu_caches.spec_index(cpu_id).view().view().linked_list.view() == Seq::<PagePtr>::empty()
        &&& krnl.allc_4k_mp.spec_index(layout.allocator_4k).cpu_caches.spec_index(cpu_id).view().view().linked_list.map() == Map::<usize, PagePtr>::empty()
        &&& !krnl.allc_4k_mp.spec_index(layout.allocator_4k).cpu_caches.spec_index(cpu_id).view().locked()
    }
    &&& krnl.allc_2m_mp.perms_wf()
    &&& krnl.allc_2m_mp.dom() =~= set![layout.allocator_2m]
    &&& krnl.allc_2m_mp.spec_index(layout.allocator_2m).inv()
    &&& krnl.allc_2m_mp.spec_index(layout.allocator_2m).owning_container == layout.root_container
    &&& krnl.allc_2m_mp.spec_index(layout.allocator_2m).total_free_pages.view() == free_2m_pool.view().len()
    &&& krnl.allc_2m_mp.spec_index(layout.allocator_2m).quota.view().view() == free_2m_pool.view().len()
    &&& krnl.allc_2m_mp.spec_index(layout.allocator_2m).quota.view().container_depth == 0
    &&& krnl.allc_2m_mp.spec_index(layout.allocator_2m).quota.view().lock_minor() == seq![layout.root_container]
    &&& !krnl.allc_2m_mp.spec_index(layout.allocator_2m).quota.locked()
    &&& krnl.allc_2m_mp.spec_index(layout.allocator_2m).global_pool.view().view() == free_2m_pool.view()
    &&& krnl.allc_2m_mp.spec_index(layout.allocator_2m).global_pool.view().map() == free_2m_pool.map()
    &&& !krnl.allc_2m_mp.spec_index(layout.allocator_2m).global_pool.locked()
    &&& forall|cpu_id: CpuId| #![trigger krnl.allc_2m_mp.spec_index(layout.allocator_2m).cpu_caches.spec_index(cpu_id)] index_valid(NUM_CPUS, cpu_id) ==> {
        &&& krnl.allc_2m_mp.spec_index(layout.allocator_2m).cpu_caches.spec_index(cpu_id).view().view().linked_list.view() == Seq::<PagePtr>::empty()
        &&& krnl.allc_2m_mp.spec_index(layout.allocator_2m).cpu_caches.spec_index(cpu_id).view().view().linked_list.map() == Map::<usize, PagePtr>::empty()
        &&& !krnl.allc_2m_mp.spec_index(layout.allocator_2m).cpu_caches.spec_index(cpu_id).view().locked()
    }
    &&& krnl.allc_1g_mp.perms_wf()
    &&& krnl.allc_1g_mp.dom() =~= set![layout.allocator_1g]
    &&& krnl.allc_1g_mp.spec_index(layout.allocator_1g).inv()
    &&& krnl.allc_1g_mp.spec_index(layout.allocator_1g).owning_container == layout.root_container
    &&& krnl.allc_1g_mp.spec_index(layout.allocator_1g).total_free_pages.view() == free_1g_pool.view().len()
    &&& krnl.allc_1g_mp.spec_index(layout.allocator_1g).quota.view().view() == free_1g_pool.view().len()
    &&& krnl.allc_1g_mp.spec_index(layout.allocator_1g).quota.view().container_depth == 0
    &&& krnl.allc_1g_mp.spec_index(layout.allocator_1g).quota.view().lock_minor() == seq![layout.root_container]
    &&& !krnl.allc_1g_mp.spec_index(layout.allocator_1g).quota.locked()
    &&& krnl.allc_1g_mp.spec_index(layout.allocator_1g).global_pool.view().view() == free_1g_pool.view()
    &&& krnl.allc_1g_mp.spec_index(layout.allocator_1g).global_pool.view().map() == free_1g_pool.map()
    &&& !krnl.allc_1g_mp.spec_index(layout.allocator_1g).global_pool.locked()
    &&& forall|cpu_id: CpuId| #![trigger krnl.allc_1g_mp.spec_index(layout.allocator_1g).cpu_caches.spec_index(cpu_id)] index_valid(NUM_CPUS, cpu_id) ==> {
        &&& krnl.allc_1g_mp.spec_index(layout.allocator_1g).cpu_caches.spec_index(cpu_id).view().view().linked_list.view() == Seq::<PagePtr>::empty()
        &&& krnl.allc_1g_mp.spec_index(layout.allocator_1g).cpu_caches.spec_index(cpu_id).view().view().linked_list.map() == Map::<usize, PagePtr>::empty()
        &&& !krnl.allc_1g_mp.spec_index(layout.allocator_1g).cpu_caches.spec_index(cpu_id).view().locked()
    }
    &&& krnl.cpu_offline_mp.perms_wf()
    &&& krnl.cpu_offline_mp.dom() =~= set![cpu_offline_flags_ptr(layout.root_container)]
    &&& krnl.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(layout.root_container)).inv()
    &&& krnl.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(layout.root_container)).owning_container.view() == layout.root_container
    &&& krnl.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(layout.root_container)).container_depth.view() == 0
    &&& forall|cpu_id: CpuId| #![trigger krnl.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(layout.root_container)).flags.spec_index(cpu_id)] index_valid(NUM_CPUS, cpu_id) ==> {
        &&& !krnl.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(layout.root_container)).flags.spec_index(cpu_id).view().locked()
        &&& krnl.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(layout.root_container)).flags.spec_index(cpu_id).view().view().index() == (cpu_offline_flags_ptr(layout.root_container), cpu_id)
        &&& !krnl.cpu_offline_mp.spec_index(cpu_offline_flags_ptr(layout.root_container)).flags.spec_index(cpu_id).view().view().requested
    }
}

proof fn boot_subsystems_inv_eof(
    krnl: &KernelK, layout: BootKernelLayout, kernel_l4_end: usize, initial_regs: Registers, kernel_entries: Seq<PageEntry>, manifest_4k: Map<VAddr, MapEntry>,
    page_array: PageLockedArray, pcid_needflush: PcidNeedFlushArray, cpu_published: CpuPublishedArray, default_pagetable: ReadOnlyNode<PageTable<PT_TYPE>>,
    cpu_page_closure: Set<PagePtr>, free_4k_pool: &LinkedList<PagePtr, 233>, free_2m_pool: &LinkedList<PagePtr, 233>,
    free_1g_pool: &LinkedList<PagePtr, 233>, owned_pages: Set<PagePtr>, owned_pci_functions: Set<PciBdf>, scheduler_node_addr: usize,
    process_node_addr: usize,
)
    requires
        0 < NUM_CPUS,
        layout.pointers_wf(),
        layout.kernel_ptr as int + KERNEL_IRT_OFFSET as int <= usize::MAX as int,
        layout.iommu_root_table_base() % VTD_TABLE_SIZE == 0,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= MEM_MASK as int,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= usize::MAX as int,
        pei_valid(kernel_l4_end),
        kernel_entries.len() == kernel_l4_end,
        boot_dom0_manifest_wf(manifest_4k, layout.root_container),
        boot_page_array_ready(page_array, layout, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool),
        forall|page_ptr: PagePtr| #![trigger cpu_page_closure.contains(page_ptr)] cpu_page_closure.contains(page_ptr) ==> page_ptr_valid(page_ptr),
        boot_default_pagetable_ready(default_pagetable, kernel_l4_end),
        boot_pcid_needflush_ready(pcid_needflush),
        boot_cpu_published_ready(cpu_published, default_pagetable.view().cr3),
        owned_pci_functions.len() == VTD_DOMAIN_COUNT,
        forall|page_ptr: PagePtr| #![trigger owned_pages.contains(page_ptr)] owned_pages.contains(page_ptr) <==> page_ptr_valid(page_ptr),
        forall|bdf: PciBdf| #![trigger owned_pci_functions.contains(bdf)] owned_pci_functions.contains(bdf) <==> pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        boot_kernel_state(krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_published, default_pagetable,
            cpu_page_closure, free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr),
    ensures
        krnl.subsystems_inv(),
{
    assert(krnl.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
    assert(pagetable_perms_wf(krnl.pt_mp)) by { reveal(pagetable_perms_wf); };
    assert(pagetable_lower_wf(krnl.pt_mp, krnl.pt_lower.view())) by { reveal(pagetable_lower_wf); };
    assert(pagetable_window_holders_hold_pagetable(krnl.pt_mp, krnl.pt_lower.view())) by {
        reveal(pagetable_window_holders_hold_pagetable); reveal(PageTableC::wf_window_locks); reveal(PageTableC::wf_l3); reveal(PageTableHigher::wf_l4);
    };
    assert(pagetable_hidden_leaves_only_when_locked(krnl.pt_mp, krnl.pt_lower.view())) by { reveal(pagetable_hidden_leaves_only_when_locked); };
    assert(pagetable_window_stale_cpus_only_when_locked(krnl.pt_mp, krnl.pt_lower.view())) by { reveal(pagetable_window_stale_cpus_only_when_locked); };
    assert(pagetable_lower_backup_wf(krnl.pt_mp, krnl.pt_lower.view()));
    assert(iommu_table_perms_wf(krnl.it_mp)) by { reveal(iommu_table_perms_wf); reveal(iommu_table_hidden_leaves_only_when_wlocked); };
    assert(page_array_wf(krnl.pg_arr)) by { reveal(boot_page_array_ready); };
    assert(cpu_array_wf(krnl.cpu_arr, krnl.dflt_pt.view())) by { reveal(cpu_array_wf); };
    assert(cpu_published_wf(krnl.cpu_published, krnl.cpu_arr, krnl.pcid_needflush)) by { reveal(cpu_published_wf); reveal(PageTable::table_pages_wf); };
    assert(cpu_offline_flags_wf(krnl.cpu_offline_mp, krnl.cpu_arr)) by { reveal(cpu_offline_flags_wf); };
    assert(container_perms_wf(krnl.ctn_mp)) by { reveal(container_perms_wf); assert(container_tree_fields_wf(krnl.ctn_mp)) by { reveal(container_tree_fields_wf); }; };
    assert(process_perms_wf(krnl.prc_mp)) by { reveal(process_perms_wf); };
    assert(thread_perms_wf(krnl.thr_mp)) by {
        reveal(thread_perms_wf);
        assert(thread_free_quota_pending_empty_unless_wlocked(krnl.thr_mp)) by { reveal(thread_free_quota_pending_empty_unless_wlocked); };
        assert(thread_temp_alloc_empty_unless_wlocked(krnl.thr_mp)) by { reveal(thread_temp_alloc_empty_unless_wlocked); };
        assert(thread_syscall_progress_only_when_wlocked(krnl.thr_mp)) by { reveal(thread_syscall_progress_only_when_wlocked); };
        assert(thread_exited_only_when_wlocked(krnl.thr_mp)) by { reveal(thread_exited_only_when_wlocked); };
        assert(thread_ipc_transit_wf(krnl.thr_mp)) by { reveal(thread_ipc_transit_wf); };
    };
    assert(scheduler_perms_wf(krnl.sched_mp)) by { reveal(scheduler_perms_wf); };
    assert(cpu_set_perms_wf(krnl.cpu_set_mp)) by { reveal(cpu_set_perms_wf); };
    assert(pcid_allocator_perms_wf(krnl.pcid_allc_mp)) by { reveal(pcid_allocator_perms_wf); };
    assert(endpoint_perms_wf(krnl.ep_mp)) by { reveal(endpoint_perms_wf); };
    assert(allocator_perms_wf(krnl.allc_4k_mp)) by { reveal(allocator_perms_wf); };
    assert(allocator_perms_wf(krnl.allc_2m_mp)) by { reveal(allocator_perms_wf); };
    assert(allocator_perms_wf(krnl.allc_1g_mp)) by { reveal(allocator_perms_wf); };
}

#[verifier::spinoff_prover]
proof fn boot_memory_management_inv_eof_allocator_pages(
    krnl: &KernelK, layout: BootKernelLayout, kernel_l4_end: usize, initial_regs: Registers, kernel_entries: Seq<PageEntry>, manifest_4k: Map<VAddr, MapEntry>,
    page_array: PageLockedArray, pcid_needflush: PcidNeedFlushArray, cpu_published: CpuPublishedArray, default_pagetable: ReadOnlyNode<PageTable<PT_TYPE>>,
    cpu_page_closure: Set<PagePtr>, free_4k_pool: &LinkedList<PagePtr, 233>, free_2m_pool: &LinkedList<PagePtr, 233>,
    free_1g_pool: &LinkedList<PagePtr, 233>, owned_pages: Set<PagePtr>, owned_pci_functions: Set<PciBdf>, scheduler_node_addr: usize,
    process_node_addr: usize,
)
    requires
        0 < NUM_CPUS,
        layout.pointers_wf(),
        layout.kernel_ptr as int + KERNEL_IRT_OFFSET as int <= usize::MAX as int,
        layout.iommu_root_table_base() % VTD_TABLE_SIZE == 0,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= MEM_MASK as int,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= usize::MAX as int,
        pei_valid(kernel_l4_end),
        kernel_entries.len() == kernel_l4_end,
        boot_dom0_manifest_wf(manifest_4k, layout.root_container),
        boot_page_array_ready(page_array, layout, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool),
        forall|page_ptr: PagePtr| #![trigger cpu_page_closure.contains(page_ptr)] cpu_page_closure.contains(page_ptr) ==> page_ptr_valid(page_ptr),
        boot_default_pagetable_ready(default_pagetable, kernel_l4_end),
        boot_pcid_needflush_ready(pcid_needflush),
        boot_cpu_published_ready(cpu_published, default_pagetable.view().cr3),
        owned_pci_functions.len() == VTD_DOMAIN_COUNT,
        forall|page_ptr: PagePtr| #![trigger owned_pages.contains(page_ptr)] owned_pages.contains(page_ptr) <==> page_ptr_valid(page_ptr),
        forall|bdf: PciBdf| #![trigger owned_pci_functions.contains(bdf)] owned_pci_functions.contains(bdf) <==> pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        boot_kernel_state(krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_published, default_pagetable,
            cpu_page_closure, free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr),
    ensures
        allocator_pages_wf(krnl.pg_arr, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp),
{
    assert(allocator_pages_wf(krnl.pg_arr, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by { reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf); reveal(boot_page_array_ready); };
}

proof fn boot_memory_management_inv_eof_allocator_free_pages(
    krnl: &KernelK, layout: BootKernelLayout, kernel_l4_end: usize, initial_regs: Registers, kernel_entries: Seq<PageEntry>, manifest_4k: Map<VAddr, MapEntry>,
    page_array: PageLockedArray, pcid_needflush: PcidNeedFlushArray, cpu_published: CpuPublishedArray, default_pagetable: ReadOnlyNode<PageTable<PT_TYPE>>,
    cpu_page_closure: Set<PagePtr>, free_4k_pool: &LinkedList<PagePtr, 233>, free_2m_pool: &LinkedList<PagePtr, 233>,
    free_1g_pool: &LinkedList<PagePtr, 233>, owned_pages: Set<PagePtr>, owned_pci_functions: Set<PciBdf>, scheduler_node_addr: usize,
    process_node_addr: usize,
)
    requires
        0 < NUM_CPUS,
        layout.pointers_wf(),
        layout.kernel_ptr as int + KERNEL_IRT_OFFSET as int <= usize::MAX as int,
        layout.iommu_root_table_base() % VTD_TABLE_SIZE == 0,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= MEM_MASK as int,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= usize::MAX as int,
        pei_valid(kernel_l4_end),
        kernel_entries.len() == kernel_l4_end,
        boot_dom0_manifest_wf(manifest_4k, layout.root_container),
        boot_page_array_ready(page_array, layout, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool),
        forall|page_ptr: PagePtr| #![trigger cpu_page_closure.contains(page_ptr)] cpu_page_closure.contains(page_ptr) ==> page_ptr_valid(page_ptr),
        boot_default_pagetable_ready(default_pagetable, kernel_l4_end),
        boot_pcid_needflush_ready(pcid_needflush),
        boot_cpu_published_ready(cpu_published, default_pagetable.view().cr3),
        owned_pci_functions.len() == VTD_DOMAIN_COUNT,
        forall|page_ptr: PagePtr| #![trigger owned_pages.contains(page_ptr)] owned_pages.contains(page_ptr) <==> page_ptr_valid(page_ptr),
        forall|bdf: PciBdf| #![trigger owned_pci_functions.contains(bdf)] owned_pci_functions.contains(bdf) <==> pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        boot_kernel_state(krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_published, default_pagetable,
            cpu_page_closure, free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr),
    ensures
        krnl.allocator_free_pages_wf(),
{
    assert(boot_free_4k_pool_wf(page_array, layout, free_4k_pool) && boot_free_2m_pool_wf(page_array, layout, free_2m_pool) && boot_free_1g_pool_wf(page_array, layout, free_1g_pool)) by { reveal(boot_page_array_ready); };
    assert(krnl.allocator_free_pages_wf()) by { reveal(allocator_free_page_ptrs_wf); };
}

proof fn boot_memory_management_inv_eof_free_4k(
    krnl: &KernelK, layout: BootKernelLayout, kernel_l4_end: usize, initial_regs: Registers, kernel_entries: Seq<PageEntry>, manifest_4k: Map<VAddr, MapEntry>,
    page_array: PageLockedArray, pcid_needflush: PcidNeedFlushArray, cpu_published: CpuPublishedArray, default_pagetable: ReadOnlyNode<PageTable<PT_TYPE>>,
    cpu_page_closure: Set<PagePtr>, free_4k_pool: &LinkedList<PagePtr, 233>, free_2m_pool: &LinkedList<PagePtr, 233>,
    free_1g_pool: &LinkedList<PagePtr, 233>, owned_pages: Set<PagePtr>, owned_pci_functions: Set<PciBdf>, scheduler_node_addr: usize,
    process_node_addr: usize,
)
    requires
        0 < NUM_CPUS,
        layout.pointers_wf(),
        layout.kernel_ptr as int + KERNEL_IRT_OFFSET as int <= usize::MAX as int,
        layout.iommu_root_table_base() % VTD_TABLE_SIZE == 0,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= MEM_MASK as int,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= usize::MAX as int,
        pei_valid(kernel_l4_end),
        kernel_entries.len() == kernel_l4_end,
        boot_dom0_manifest_wf(manifest_4k, layout.root_container),
        boot_page_array_ready(page_array, layout, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool),
        forall|page_ptr: PagePtr| #![trigger cpu_page_closure.contains(page_ptr)] cpu_page_closure.contains(page_ptr) ==> page_ptr_valid(page_ptr),
        boot_default_pagetable_ready(default_pagetable, kernel_l4_end),
        boot_pcid_needflush_ready(pcid_needflush),
        boot_cpu_published_ready(cpu_published, default_pagetable.view().cr3),
        owned_pci_functions.len() == VTD_DOMAIN_COUNT,
        forall|page_ptr: PagePtr| #![trigger owned_pages.contains(page_ptr)] owned_pages.contains(page_ptr) <==> page_ptr_valid(page_ptr),
        forall|bdf: PciBdf| #![trigger owned_pci_functions.contains(bdf)] owned_pci_functions.contains(bdf) <==> pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        boot_kernel_state(krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_published, default_pagetable,
            cpu_page_closure, free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr),
    ensures
        container_allocator_free_4k_page_wf(krnl.allc_4k_mp, krnl.pg_arr),
{
    assert(container_allocator_free_4k_page_wf(krnl.allc_4k_mp, krnl.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(boot_page_array_ready); };
}

proof fn boot_memory_management_inv_eof_free_2m(
    krnl: &KernelK, layout: BootKernelLayout, kernel_l4_end: usize, initial_regs: Registers, kernel_entries: Seq<PageEntry>, manifest_4k: Map<VAddr, MapEntry>,
    page_array: PageLockedArray, pcid_needflush: PcidNeedFlushArray, cpu_published: CpuPublishedArray, default_pagetable: ReadOnlyNode<PageTable<PT_TYPE>>,
    cpu_page_closure: Set<PagePtr>, free_4k_pool: &LinkedList<PagePtr, 233>, free_2m_pool: &LinkedList<PagePtr, 233>,
    free_1g_pool: &LinkedList<PagePtr, 233>, owned_pages: Set<PagePtr>, owned_pci_functions: Set<PciBdf>, scheduler_node_addr: usize,
    process_node_addr: usize,
)
    requires
        0 < NUM_CPUS,
        layout.pointers_wf(),
        layout.kernel_ptr as int + KERNEL_IRT_OFFSET as int <= usize::MAX as int,
        layout.iommu_root_table_base() % VTD_TABLE_SIZE == 0,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= MEM_MASK as int,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= usize::MAX as int,
        pei_valid(kernel_l4_end),
        kernel_entries.len() == kernel_l4_end,
        boot_dom0_manifest_wf(manifest_4k, layout.root_container),
        boot_page_array_ready(page_array, layout, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool),
        forall|page_ptr: PagePtr| #![trigger cpu_page_closure.contains(page_ptr)] cpu_page_closure.contains(page_ptr) ==> page_ptr_valid(page_ptr),
        boot_default_pagetable_ready(default_pagetable, kernel_l4_end),
        boot_pcid_needflush_ready(pcid_needflush),
        boot_cpu_published_ready(cpu_published, default_pagetable.view().cr3),
        owned_pci_functions.len() == VTD_DOMAIN_COUNT,
        forall|page_ptr: PagePtr| #![trigger owned_pages.contains(page_ptr)] owned_pages.contains(page_ptr) <==> page_ptr_valid(page_ptr),
        forall|bdf: PciBdf| #![trigger owned_pci_functions.contains(bdf)] owned_pci_functions.contains(bdf) <==> pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        boot_kernel_state(krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_published, default_pagetable,
            cpu_page_closure, free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr),
    ensures
        container_allocator_free_2m_page_wf(krnl.allc_2m_mp, krnl.pg_arr),
{
    assert(container_allocator_free_2m_page_wf(krnl.allc_2m_mp, krnl.pg_arr)) by { reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_global_free_2m_page_wf); reveal(container_allocator_cpu_cache_free_2m_page_wf); reveal(boot_page_array_ready); };
}

proof fn boot_memory_management_inv_eof_free_1g(
    krnl: &KernelK, layout: BootKernelLayout, kernel_l4_end: usize, initial_regs: Registers, kernel_entries: Seq<PageEntry>, manifest_4k: Map<VAddr, MapEntry>,
    page_array: PageLockedArray, pcid_needflush: PcidNeedFlushArray, cpu_published: CpuPublishedArray, default_pagetable: ReadOnlyNode<PageTable<PT_TYPE>>,
    cpu_page_closure: Set<PagePtr>, free_4k_pool: &LinkedList<PagePtr, 233>, free_2m_pool: &LinkedList<PagePtr, 233>,
    free_1g_pool: &LinkedList<PagePtr, 233>, owned_pages: Set<PagePtr>, owned_pci_functions: Set<PciBdf>, scheduler_node_addr: usize,
    process_node_addr: usize,
)
    requires
        0 < NUM_CPUS,
        layout.pointers_wf(),
        layout.kernel_ptr as int + KERNEL_IRT_OFFSET as int <= usize::MAX as int,
        layout.iommu_root_table_base() % VTD_TABLE_SIZE == 0,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= MEM_MASK as int,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= usize::MAX as int,
        pei_valid(kernel_l4_end),
        kernel_entries.len() == kernel_l4_end,
        boot_dom0_manifest_wf(manifest_4k, layout.root_container),
        boot_page_array_ready(page_array, layout, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool),
        forall|page_ptr: PagePtr| #![trigger cpu_page_closure.contains(page_ptr)] cpu_page_closure.contains(page_ptr) ==> page_ptr_valid(page_ptr),
        boot_default_pagetable_ready(default_pagetable, kernel_l4_end),
        boot_pcid_needflush_ready(pcid_needflush),
        boot_cpu_published_ready(cpu_published, default_pagetable.view().cr3),
        owned_pci_functions.len() == VTD_DOMAIN_COUNT,
        forall|page_ptr: PagePtr| #![trigger owned_pages.contains(page_ptr)] owned_pages.contains(page_ptr) <==> page_ptr_valid(page_ptr),
        forall|bdf: PciBdf| #![trigger owned_pci_functions.contains(bdf)] owned_pci_functions.contains(bdf) <==> pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        boot_kernel_state(krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_published, default_pagetable,
            cpu_page_closure, free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr),
    ensures
        container_allocator_free_1g_page_wf(krnl.allc_1g_mp, krnl.pg_arr),
{
    assert(container_allocator_free_1g_page_wf(krnl.allc_1g_mp, krnl.pg_arr)) by { reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_global_free_1g_page_wf); reveal(container_allocator_cpu_cache_free_1g_page_wf); reveal(boot_page_array_ready); };
}

proof fn boot_memory_management_inv_eof_object_pages(
    krnl: &KernelK, layout: BootKernelLayout, kernel_l4_end: usize, initial_regs: Registers, kernel_entries: Seq<PageEntry>, manifest_4k: Map<VAddr, MapEntry>,
    page_array: PageLockedArray, pcid_needflush: PcidNeedFlushArray, cpu_published: CpuPublishedArray, default_pagetable: ReadOnlyNode<PageTable<PT_TYPE>>,
    cpu_page_closure: Set<PagePtr>, free_4k_pool: &LinkedList<PagePtr, 233>, free_2m_pool: &LinkedList<PagePtr, 233>,
    free_1g_pool: &LinkedList<PagePtr, 233>, owned_pages: Set<PagePtr>, owned_pci_functions: Set<PciBdf>, scheduler_node_addr: usize,
    process_node_addr: usize,
)
    requires
        0 < NUM_CPUS,
        layout.pointers_wf(),
        layout.kernel_ptr as int + KERNEL_IRT_OFFSET as int <= usize::MAX as int,
        layout.iommu_root_table_base() % VTD_TABLE_SIZE == 0,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= MEM_MASK as int,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= usize::MAX as int,
        pei_valid(kernel_l4_end),
        kernel_entries.len() == kernel_l4_end,
        boot_dom0_manifest_wf(manifest_4k, layout.root_container),
        boot_page_array_ready(page_array, layout, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool),
        forall|page_ptr: PagePtr| #![trigger cpu_page_closure.contains(page_ptr)] cpu_page_closure.contains(page_ptr) ==> page_ptr_valid(page_ptr),
        boot_default_pagetable_ready(default_pagetable, kernel_l4_end),
        boot_pcid_needflush_ready(pcid_needflush),
        boot_cpu_published_ready(cpu_published, default_pagetable.view().cr3),
        owned_pci_functions.len() == VTD_DOMAIN_COUNT,
        forall|page_ptr: PagePtr| #![trigger owned_pages.contains(page_ptr)] owned_pages.contains(page_ptr) <==> page_ptr_valid(page_ptr),
        forall|bdf: PciBdf| #![trigger owned_pci_functions.contains(bdf)] owned_pci_functions.contains(bdf) <==> pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        boot_kernel_state(krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_published, default_pagetable,
            cpu_page_closure, free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr),
    ensures
        container_pages_wf(krnl.pg_arr, krnl.ctn_mp),
        process_pages_wf(krnl.pg_arr, krnl.prc_mp),
        pagetable_pages_wf(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr),
        thread_pages_wf(krnl.thr_mp, krnl.pg_arr),
        scheduler_pages_wf(krnl.sched_mp, krnl.pg_arr),
        cpu_set_pages_wf(krnl.cpu_set_mp, krnl.pg_arr),
        pcid_allocator_pages_wf(krnl.pg_arr, krnl.pcid_allc_mp),
        thread_staged_pages_wf(krnl.thr_mp, krnl.pg_arr),
        endpoint_pages_wf(krnl.ep_mp, krnl.pg_arr),
{
    boot_memory_management_inv_eof_container_pages(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_published, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    boot_memory_management_inv_eof_process_pages(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_published, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    boot_memory_management_inv_eof_pagetable_pages(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_published, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    boot_memory_management_inv_eof_thread_pages(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_published, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    boot_memory_management_inv_eof_scheduler_pages(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_published, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    boot_memory_management_inv_eof_cpu_set_pages(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_published, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    boot_memory_management_inv_eof_pcid_allocator_pages(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_published, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    boot_memory_management_inv_eof_thread_staged_pages(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_published, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    boot_memory_management_inv_eof_endpoint_pages(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_published, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
}

proof fn boot_memory_management_inv_eof_mappings(
    krnl: &KernelK, layout: BootKernelLayout, kernel_l4_end: usize, initial_regs: Registers, kernel_entries: Seq<PageEntry>, manifest_4k: Map<VAddr, MapEntry>,
    page_array: PageLockedArray, pcid_needflush: PcidNeedFlushArray, cpu_published: CpuPublishedArray, default_pagetable: ReadOnlyNode<PageTable<PT_TYPE>>,
    cpu_page_closure: Set<PagePtr>, free_4k_pool: &LinkedList<PagePtr, 233>, free_2m_pool: &LinkedList<PagePtr, 233>,
    free_1g_pool: &LinkedList<PagePtr, 233>, owned_pages: Set<PagePtr>, owned_pci_functions: Set<PciBdf>, scheduler_node_addr: usize,
    process_node_addr: usize,
)
    requires
        0 < NUM_CPUS,
        layout.pointers_wf(),
        layout.kernel_ptr as int + KERNEL_IRT_OFFSET as int <= usize::MAX as int,
        layout.iommu_root_table_base() % VTD_TABLE_SIZE == 0,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= MEM_MASK as int,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= usize::MAX as int,
        pei_valid(kernel_l4_end),
        kernel_entries.len() == kernel_l4_end,
        boot_dom0_manifest_wf(manifest_4k, layout.root_container),
        boot_page_array_ready(page_array, layout, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool),
        forall|page_ptr: PagePtr| #![trigger cpu_page_closure.contains(page_ptr)] cpu_page_closure.contains(page_ptr) ==> page_ptr_valid(page_ptr),
        boot_default_pagetable_ready(default_pagetable, kernel_l4_end),
        boot_pcid_needflush_ready(pcid_needflush),
        boot_cpu_published_ready(cpu_published, default_pagetable.view().cr3),
        owned_pci_functions.len() == VTD_DOMAIN_COUNT,
        forall|page_ptr: PagePtr| #![trigger owned_pages.contains(page_ptr)] owned_pages.contains(page_ptr) <==> page_ptr_valid(page_ptr),
        forall|bdf: PciBdf| #![trigger owned_pci_functions.contains(bdf)] owned_pci_functions.contains(bdf) <==> pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        boot_kernel_state(krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_published, default_pagetable,
            cpu_page_closure, free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr),
    ensures
        hugepage_2m_wf(krnl.pg_arr),
        hugepage_1g_wf(krnl.pg_arr),
        page_pagetable_wf(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr),
        container_process_page_pagetable_wf(krnl.ctn_mp, krnl.prc_mp, krnl.pt_mp, krnl.pg_arr),
        page_iommu_table_wf(krnl.ctn_mp, krnl.prc_mp, krnl.it_mp, krnl.pg_arr),
{
    assert(hugepage_2m_wf(krnl.pg_arr)) by { reveal(boot_page_array_ready); };
    assert(hugepage_1g_wf(krnl.pg_arr)) by { reveal(boot_page_array_ready); };
    assert(page_pagetable_wf(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr)) by { reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); reveal(boot_page_array_ready); };
    assert(container_process_page_pagetable_wf(krnl.ctn_mp, krnl.prc_mp, krnl.pt_mp, krnl.pg_arr)) by { reveal(container_process_page_pagetable_wf); reveal(boot_page_array_ready); };
    assert(page_iommu_table_wf(krnl.ctn_mp, krnl.prc_mp, krnl.it_mp, krnl.pg_arr)) by { reveal(page_iommu_table_wf); reveal(boot_page_array_ready); };
}

proof fn boot_memory_management_inv_eof(
    krnl: &KernelK, layout: BootKernelLayout, kernel_l4_end: usize, initial_regs: Registers, kernel_entries: Seq<PageEntry>, manifest_4k: Map<VAddr, MapEntry>,
    page_array: PageLockedArray, pcid_needflush: PcidNeedFlushArray, cpu_published: CpuPublishedArray, default_pagetable: ReadOnlyNode<PageTable<PT_TYPE>>,
    cpu_page_closure: Set<PagePtr>, free_4k_pool: &LinkedList<PagePtr, 233>, free_2m_pool: &LinkedList<PagePtr, 233>,
    free_1g_pool: &LinkedList<PagePtr, 233>, owned_pages: Set<PagePtr>, owned_pci_functions: Set<PciBdf>, scheduler_node_addr: usize,
    process_node_addr: usize,
)
    requires
        0 < NUM_CPUS,
        layout.pointers_wf(),
        layout.kernel_ptr as int + KERNEL_IRT_OFFSET as int <= usize::MAX as int,
        layout.iommu_root_table_base() % VTD_TABLE_SIZE == 0,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= MEM_MASK as int,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= usize::MAX as int,
        pei_valid(kernel_l4_end),
        kernel_entries.len() == kernel_l4_end,
        boot_dom0_manifest_wf(manifest_4k, layout.root_container),
        boot_page_array_ready(page_array, layout, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool),
        forall|page_ptr: PagePtr| #![trigger cpu_page_closure.contains(page_ptr)] cpu_page_closure.contains(page_ptr) ==> page_ptr_valid(page_ptr),
        boot_default_pagetable_ready(default_pagetable, kernel_l4_end),
        boot_pcid_needflush_ready(pcid_needflush),
        boot_cpu_published_ready(cpu_published, default_pagetable.view().cr3),
        owned_pci_functions.len() == VTD_DOMAIN_COUNT,
        forall|page_ptr: PagePtr| #![trigger owned_pages.contains(page_ptr)] owned_pages.contains(page_ptr) <==> page_ptr_valid(page_ptr),
        forall|bdf: PciBdf| #![trigger owned_pci_functions.contains(bdf)] owned_pci_functions.contains(bdf) <==> pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        boot_kernel_state(krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_published, default_pagetable,
            cpu_page_closure, free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr),
    ensures
        krnl.memory_management_inv(),
{
    boot_memory_management_inv_eof_allocator_pages(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_published, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    boot_memory_management_inv_eof_allocator_free_pages(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_published, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    boot_memory_management_inv_eof_free_4k(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_published, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    boot_memory_management_inv_eof_free_2m(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_published, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    boot_memory_management_inv_eof_free_1g(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_published, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    boot_memory_management_inv_eof_object_pages(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_published, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    boot_memory_management_inv_eof_mappings(
        krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_published, default_pagetable, cpu_page_closure,
        free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr,
    );
    prove_boot_container_page_owner_wf(krnl, layout, page_array, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool, owned_pages);
    prove_boot_iommu_table_pages_wf(krnl, layout, page_array, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool);
    assert(process_pagetable_match(krnl.prc_mp, krnl.pt_mp)) by { reveal(process_pagetable_match); };
    assert(process_iommu_table_match(krnl.prc_mp, krnl.it_mp)) by { reveal(process_iommu_table_match); };
    assert(pagetable_no_huge_leaf_wf(krnl.pt_mp, krnl.pt_lower.view(), krnl.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(krnl.prc_mp, krnl.pt_mp, krnl.pt_lower.view(), krnl.it_mp)) by { reveal(process_emptied_tables_wf); };
    prove_boot_process_kernel_pages_owner_wf(krnl, layout, page_array, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool);
    prove_boot_page_object_owner_wf(krnl, layout, page_array, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool);
    prove_boot_container_process_allocator_quota_4k_wf(krnl, layout);
    prove_boot_container_process_allocator_quota_2m_wf(krnl, layout);
    prove_boot_container_process_allocator_quota_1g_wf(krnl, layout);
    assert(container_allocator_wf(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by { reveal(container_allocator_wf); };
    assert(container_kill_retire_wf(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by { reveal(container_kill_retire_wf); };
}

proof fn boot_process_management_inv_eof(
    krnl: &KernelK, layout: BootKernelLayout, kernel_l4_end: usize, initial_regs: Registers, kernel_entries: Seq<PageEntry>, manifest_4k: Map<VAddr, MapEntry>,
    page_array: PageLockedArray, pcid_needflush: PcidNeedFlushArray, cpu_published: CpuPublishedArray, default_pagetable: ReadOnlyNode<PageTable<PT_TYPE>>,
    cpu_page_closure: Set<PagePtr>, free_4k_pool: &LinkedList<PagePtr, 233>, free_2m_pool: &LinkedList<PagePtr, 233>,
    free_1g_pool: &LinkedList<PagePtr, 233>, owned_pages: Set<PagePtr>, owned_pci_functions: Set<PciBdf>, scheduler_node_addr: usize,
    process_node_addr: usize,
)
    requires
        0 < NUM_CPUS,
        layout.pointers_wf(),
        layout.kernel_ptr as int + KERNEL_IRT_OFFSET as int <= usize::MAX as int,
        layout.iommu_root_table_base() % VTD_TABLE_SIZE == 0,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= MEM_MASK as int,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= usize::MAX as int,
        pei_valid(kernel_l4_end),
        kernel_entries.len() == kernel_l4_end,
        boot_dom0_manifest_wf(manifest_4k, layout.root_container),
        boot_page_array_ready(page_array, layout, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool),
        forall|page_ptr: PagePtr| #![trigger cpu_page_closure.contains(page_ptr)] cpu_page_closure.contains(page_ptr) ==> page_ptr_valid(page_ptr),
        boot_default_pagetable_ready(default_pagetable, kernel_l4_end),
        boot_pcid_needflush_ready(pcid_needflush),
        boot_cpu_published_ready(cpu_published, default_pagetable.view().cr3),
        owned_pci_functions.len() == VTD_DOMAIN_COUNT,
        forall|page_ptr: PagePtr| #![trigger owned_pages.contains(page_ptr)] owned_pages.contains(page_ptr) <==> page_ptr_valid(page_ptr),
        forall|bdf: PciBdf| #![trigger owned_pci_functions.contains(bdf)] owned_pci_functions.contains(bdf) <==> pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        boot_kernel_state(krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_published, default_pagetable,
            cpu_page_closure, free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr),
    ensures
        krnl.process_management_inv(),
{
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
    assert(per_container_process_tree_wf(krnl.ctn_mp, krnl.prc_mp)) by {
        reveal(process_root_wf);
        reveal(process_children_parent_wf);
        reveal(process_linkedlist_wf);
        reveal(process_children_depth_wf);
        reveal(process_subtree_set_wf);
        reveal(process_uppertree_seq_wf);
        reveal(process_subtree_set_exclusive);
        reveal(per_container_process_tree_wf);
    };
    assert(process_kill_mark_wf(krnl.ctn_mp, krnl.prc_mp)) by { reveal(process_kill_mark_wf); };
    assert(container_kill_mark_wf(krnl.ctn_mp, krnl.prc_mp)) by { reveal(container_kill_mark_wf); };
    assert(cpu_set_kill_mark_wf(krnl.ctn_mp, krnl.cpu_set_mp, krnl.prc_mp)) by { reveal(cpu_set_kill_mark_wf); };
    assert(process_state_lock_wf(krnl.prc_mp)) by { reveal(process_state_lock_wf); };
    assert(container_endpoint_wf(krnl.ctn_mp, krnl.ep_mp)) by { reveal(container_endpoint_wf); };
    assert(container_cpu_wf(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr)) by { reveal(container_cpu_wf); };
    assert(thread_endpoint_ref_counter_wf(krnl.thr_mp, krnl.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); };
    assert(thread_endpoint_queue_wf(krnl.thr_mp, krnl.ep_mp)) by { reveal(thread_endpoint_queue_wf); };
    assert(thread_caller_callee_wf(krnl.thr_mp)) by { reveal(thread_caller_callee_wf); };
    assert(container_thread_endpoint_wf(krnl.ctn_mp, krnl.thr_mp, krnl.ep_mp)) by { reveal(container_thread_endpoint_wf); };
    assert(container_scheduler_wf(krnl.ctn_mp, krnl.sched_mp)) by { reveal(container_scheduler_wf); };
    assert(container_cpu_set_wf(krnl.ctn_mp, krnl.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
    assert(container_cpu_offline_flags_wf(krnl.ctn_mp, krnl.cpu_offline_mp)) by { reveal(container_cpu_offline_flags_wf); };
    assert(container_pcid_allocator_wf(krnl.ctn_mp, krnl.pcid_allc_mp)) by { reveal(container_pcid_allocator_wf); };
    assert(process_pcid_allocator_wf(krnl.ctn_mp, krnl.prc_mp, krnl.pcid_allc_mp)) by { reveal(process_pcid_allocator_wf); };
    prove_boot_container_thread_scheduler_wf(krnl, layout, scheduler_node_addr);
    assert(container_thread_wf(krnl.ctn_mp, krnl.thr_mp)) by { reveal(container_thread_wf); };
    assert(process_cpu_wf(krnl.prc_mp, krnl.cpu_arr)) by { reveal(process_cpu_wf); };
    prove_boot_process_thread_wf(krnl, layout, process_node_addr);
    assert(process_emptied_threads_wf(krnl.prc_mp, krnl.thr_mp)) by { reveal(process_emptied_threads_wf); };
    assert(thread_cpu_wf(krnl.thr_mp, krnl.cpu_arr)) by { reveal(thread_cpu_wf); };
    assert(thread_dangling_chain_end_wf(krnl.thr_mp)) by { reveal(thread_dangling_chain_end_wf); };
}

proof fn boot_kernel_inv_eof(
    krnl: &KernelK, layout: BootKernelLayout, kernel_l4_end: usize, initial_regs: Registers, kernel_entries: Seq<PageEntry>, manifest_4k: Map<VAddr, MapEntry>,
    page_array: PageLockedArray, pcid_needflush: PcidNeedFlushArray, cpu_published: CpuPublishedArray, default_pagetable: ReadOnlyNode<PageTable<PT_TYPE>>,
    cpu_page_closure: Set<PagePtr>, free_4k_pool: &LinkedList<PagePtr, 233>, free_2m_pool: &LinkedList<PagePtr, 233>,
    free_1g_pool: &LinkedList<PagePtr, 233>, owned_pages: Set<PagePtr>, owned_pci_functions: Set<PciBdf>, scheduler_node_addr: usize,
    process_node_addr: usize,
)
    requires
        0 < NUM_CPUS,
        layout.pointers_wf(),
        layout.kernel_ptr as int + KERNEL_IRT_OFFSET as int <= usize::MAX as int,
        layout.iommu_root_table_base() % VTD_TABLE_SIZE == 0,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= MEM_MASK as int,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= usize::MAX as int,
        pei_valid(kernel_l4_end),
        kernel_entries.len() == kernel_l4_end,
        boot_dom0_manifest_wf(manifest_4k, layout.root_container),
        boot_page_array_ready(page_array, layout, cpu_page_closure, manifest_4k, free_4k_pool, free_2m_pool, free_1g_pool),
        forall|page_ptr: PagePtr| #![trigger cpu_page_closure.contains(page_ptr)] cpu_page_closure.contains(page_ptr) ==> page_ptr_valid(page_ptr),
        boot_default_pagetable_ready(default_pagetable, kernel_l4_end),
        boot_pcid_needflush_ready(pcid_needflush),
        boot_cpu_published_ready(cpu_published, default_pagetable.view().cr3),
        owned_pci_functions.len() == VTD_DOMAIN_COUNT,
        forall|page_ptr: PagePtr| #![trigger owned_pages.contains(page_ptr)] owned_pages.contains(page_ptr) <==> page_ptr_valid(page_ptr),
        forall|bdf: PciBdf| #![trigger owned_pci_functions.contains(bdf)] owned_pci_functions.contains(bdf) <==> pci_bdf_valid(bdf.0, bdf.1, bdf.2),
        boot_kernel_state(krnl, layout, kernel_l4_end, initial_regs, kernel_entries, manifest_4k, page_array, pcid_needflush, cpu_published, default_pagetable,
            cpu_page_closure, free_4k_pool, free_2m_pool, free_1g_pool, owned_pages, owned_pci_functions, scheduler_node_addr, process_node_addr),
        krnl.subsystems_inv(),
        krnl.memory_management_inv(),
        krnl.process_management_inv(),
    ensures
        krnl.inv(),
{
    assert(iommu_root_table_process_wf(krnl.irt.view(), krnl.prc_mp, krnl.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(process_pci_function_ownership_wf(krnl.irt.view(), krnl.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
    assert(iommu_tlb_wf_spec(krnl.iommu_tlb, krnl.irt.view(), krnl.prc_mp, krnl.it_mp)) by { reveal(iommu_tlb_wf_spec); };
    assert(cpu_dirty_map_wf(krnl.ctn_mp, krnl.cpu_set_mp, krnl.prc_mp, krnl.cpu_arr, krnl.cpu_tlb, krnl.pt_mp, krnl.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes);
        reveal(cpu_dirty_map_proc_pcid_match);
        reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
        reveal(cpu_dirty_map_contains_pagetable_pcid_match);
    };
    assert(tlb_wf_spec(krnl.cpu_tlb, krnl.pt_mp, krnl.pt_lower.view(), krnl.cpu_arr, krnl.pcid_needflush)) by { reveal(tlb_wf_spec); };
}

pub fn finish_init_from_boot(
    layout: BootKernelLayout, kernel_l4_end: usize, initial_regs: &Registers, page_array: PageLockedArray, pcid_needflush: PcidNeedFlushArray,
    cpu_published: CpuPublishedArray, default_pagetable: ReadOnlyNode<PageTable<PT_TYPE>>, free_4k_pool: LinkedList<PagePtr, 233>,
    free_2m_pool: LinkedList<PagePtr, 233>, free_1g_pool: LinkedList<PagePtr, 233>,
    kernel_entries: Ghost<Seq<PageEntry>>, manifest_4k: Ghost<Map<VAddr, MapEntry>>, owned_pages: Ghost<Set<PagePtr>>,
    owned_pci_functions: Ghost<Set<PciBdf>>, cpu_rev_maps: Ghost<BootRevMaps>, Tracked(cpu_l4_tables): Tracked<Map<PageMapPtr, PointsTo<PageMap>>>,
    Tracked(cpu_l3_tables): Tracked<Map<PageMapPtr, PointsTo<PageMap>>>, Tracked(cpu_l2_tables): Tracked<Map<PageMapPtr, PointsTo<PageMap>>>,
    Tracked(cpu_l1_tables): Tracked<Map<PageMapPtr, PointsTo<PageMap>>>, Tracked(container_page_perm): Tracked<PagePerm2m>,
    Tracked(pcid_allocator_page_perm): Tracked<PagePerm2m>, Tracked(allocator_4k_page_perm): Tracked<PagePerm4k>,
    Tracked(allocator_2m_page_perm): Tracked<PagePerm4k>, Tracked(allocator_1g_page_perm): Tracked<PagePerm4k>,
    Tracked(scheduler_page_perm): Tracked<PagePerm4k>, Tracked(cpu_set_page_perm): Tracked<PagePerm4k>, Tracked(process_page_perm): Tracked<PagePerm4k>,
    Tracked(cpu_pagetable_page_perm): Tracked<PagePerm4k>, Tracked(thread_page_perm): Tracked<PagePerm4k>, Tracked(endpoint_page_perm): Tracked<PagePerm4k>,
    Tracked(iommu_table_page_perm): Tracked<PagePerm4k>, Tracked(iommu_l4_page_perm): Tracked<PagePerm4k>, Tracked(kernel_perm): Tracked<PointsTo<KernelK>>,
) -> (ret: Tracked<PointsTo<KernelK>>)
    requires
        0 < NUM_CPUS,
        layout.pointers_wf(),
        layout.kernel_ptr as int + KERNEL_IRT_OFFSET as int <= usize::MAX as int,
        layout.iommu_root_table_base() % VTD_TABLE_SIZE == 0,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= MEM_MASK as int,
        layout.iommu_root_table_base() as int + IOMMU_ROOT_TABLE_STATIC_SIZE as int <= usize::MAX as int,
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
        boot_dom0_pagetable_model(layout.cpu_cr3, layout.root_process, kernel_l4_end, kernel_entries.view(), manifest_4k.view(), cpu_l4_tables, cpu_l3_tables, cpu_l2_tables, cpu_l1_tables, cpu_rev_maps.view()).wf(),
        boot_page_array_ready(page_array, layout, cpu_l4_tables.dom() + cpu_l3_tables.dom() + cpu_l2_tables.dom() + cpu_l1_tables.dom(), manifest_4k.view(), &free_4k_pool, &free_2m_pool, &free_1g_pool),
        boot_default_pagetable_ready(default_pagetable, kernel_l4_end),
        boot_pcid_needflush_ready(pcid_needflush),
        boot_cpu_published_ready(cpu_published, default_pagetable.view().cr3),
        owned_pci_functions.view().len() == VTD_DOMAIN_COUNT,
        forall|page_ptr: PagePtr|
            #![trigger owned_pages.view().contains(page_ptr)]
            owned_pages.view().contains(page_ptr) <==> page_ptr_valid(page_ptr),
        forall|bdf: PciBdf|
            #![trigger owned_pci_functions.view().contains(bdf)]
            owned_pci_functions.view().contains(bdf) <==> pci_bdf_valid(bdf.0, bdf.1, bdf.2),
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
        ret.view().value().ctn_mp.dom() =~= set![layout.root_container],
        ret.view().value().prc_mp.dom() =~= set![layout.root_process],
        ret.view().value().thr_mp.dom() =~= set![layout.root_thread],
        ret.view().value().ep_mp.dom() =~= set![layout.root_endpoint],
        ret.view().value().pt_mp.dom() =~= set![layout.cpu_pagetable],
        ret.view().value().it_mp.dom() =~= set![layout.iommu_table],
{
    let tracked mut kernel_perm = kernel_perm;
    let default_cr3 = default_pagetable.borrow().cr3;
    let ghost boot_cpu_page_closure = cpu_l4_tables.dom() + cpu_l3_tables.dom() + cpu_l2_tables.dom() + cpu_l1_tables.dom();
    let (cpu_pagetable, Tracked(cpu_pagetable_lower)) = adopt_boot_dom0_pagetable(
        layout.cpu_cr3, layout.cpu_pagetable, layout.root_process, kernel_l4_end, kernel_entries, manifest_4k, layout.root_container, cpu_rev_maps,
        Tracked(cpu_l4_tables), Tracked(cpu_l3_tables), Tracked(cpu_l2_tables), Tracked(cpu_l1_tables),
    );
    let (iommu_l4, Tracked(iommu_l4_perm)) = page_perm_to_page_map(layout.iommu_l4, Tracked(iommu_l4_page_perm));
    let iommu_table = PageTable::<IOMMU_TYPE>::new(None, Ghost(Seq::empty()), iommu_l4, Tracked(iommu_l4_perm), 0, layout.root_process);
    let thread = Thread::new_boot_root(layout.root_container, layout.root_process, layout.cpu_pagetable, layout.root_endpoint);
    let mut thr_mp = ThreadLockedMap::new_empty();
    let (scheduler_node_addr, scheduler_node_perm, process_node_addr, process_node_perm) = retype_boot_root_thread(&mut thr_mp, layout.root_thread, thread, initial_regs, Tracked(thread_page_perm));
    let process = Process::new_boot_root(layout.root_process, layout.cpu_pagetable, layout.iommu_table, layout.root_thread, process_node_addr, process_node_perm);
    let scheduler = Scheduler::new_boot_root(layout.root_container, layout.root_thread, scheduler_node_addr, scheduler_node_perm);
    let endpoint = Endpoint::new_root(layout.root_endpoint, layout.root_container, layout.root_thread);
    let cpu_set = CpuSet::new_root(layout.root_container);
    let pcid_allocator = PcidAllocator::new_boot_root(layout.root_container, layout.root_process);
    let container = Container::new_boot_root(layout.root_container, layout.root_process, owned_pages);
    let quota_4k = free_4k_pool.length;
    let quota_2m = free_2m_pool.length;
    let quota_1g = free_1g_pool.length;
    proof {
        assert(free_4k_pool.wf() && free_4k_pool.container_depth.view() == Some(0) && free_4k_pool.minor.view() == Some(layout.root_container)
            && free_2m_pool.wf() && free_2m_pool.container_depth.view() == Some(0) && free_2m_pool.minor.view() == Some(layout.root_container)
            && free_1g_pool.wf() && free_1g_pool.container_depth.view() == Some(0) && free_1g_pool.minor.view() == Some(layout.root_container)) by { reveal(boot_page_array_ready); };
        reveal(LinkedList::wf_value_list);
    }
    let allocator_4k = PageAllocator::<ALLOCATOR_SIZE_4K>::new_with_global_pool(layout.root_container, 0, free_4k_pool, quota_4k);
    let allocator_2m = PageAllocator::<ALLOCATOR_SIZE_2M>::new_with_global_pool(layout.root_container, 0, free_2m_pool, quota_2m);
    let allocator_1g = PageAllocator::<ALLOCATOR_SIZE_1G>::new_with_global_pool(layout.root_container, 0, free_1g_pool, quota_1g);
    proof { reveal(PageTable::table_pages_wf); }
    let cpu_array = Cpu::new_boot_array(layout.root_container, default_cr3);
    let cpu_tlb = CpuTLB::new_empty();
    let iommu_tlb = IommuTLB::new_empty();
    let irt_base = layout.kernel_ptr + KERNEL_IRT_OFFSET;
    assert(VTD_TABLE_SIZE == 4096) by (compute);
    let irt = RwLock::new_unlocked(IommuRootTable::new_disabled(irt_base, layout.root_process), (), Ghost(()));

    let process_rodata = ReadOnlyNode::new(ProcessRO {
        owning_container: layout.root_container, container_depth: 0, parent: None, depth: 0,
        pagetable: layout.cpu_pagetable, cr3: layout.cpu_cr3, iommu_cr3: Some(layout.iommu_l4), iommu_table_ptr: Some(layout.iommu_table),
        pcid: 1,
    }, Ghost(layout.root_process));
    let process_ghost = ProcessGhost { uppertree_seq: Ghost(Seq::empty()), subtree_set: Ghost(Set::empty()), owned_pci_functions };
    let container_rodata = ReadOnlyNode::new(ContainerRO {
        parent: None, depth: 0, scheduler: layout.scheduler, pcid_allocator: layout.pcid_allocator, cpu_set: layout.cpu_set,
        allocator_ptr_4k: layout.allocator_4k, allocator_ptr_2m: layout.allocator_2m, allocator_ptr_1g: layout.allocator_1g,
    }, Ghost(layout.root_container));
    let ghost root_threads = Set::<RwLockThreadPtr>::empty().insert(layout.root_thread);
    let container_ghost = ContainerGhost {
        uppertree_seq: Ghost(Seq::empty()), subtree_set: Ghost(Set::empty()), owned_processes: Ghost(Set::empty().insert(layout.root_process)),
        owned_threads: Ghost(root_threads), owned_indirect_threads: Ghost(Set::empty()), owned_endpoints: Ghost(Set::empty().insert(layout.root_endpoint)), retire_ready: false,
    };

    let mut pt_mp = PageTableLockedMap::new_empty();
    let mut it_mp = IommuTableLockedMap::new_empty();
    let mut ctn_mp = ContainerLockedMap::new_empty();
    let mut sched_mp = SchedulerUnLockedMap::new_empty();
    let mut pcid_allc_mp = PcidAllocatorLockedMap::new_empty();
    let mut cpu_set_mp = CpuSetLockedMap::new_empty();
    let mut prc_mp = ProcessLockedMap::new_empty();
    let mut ep_mp = EndpointLockedMap::new_empty();
    let mut allc_4k_mp = PageAllocatorUnLockedMap::<ALLOCATOR_SIZE_4K>::new_empty();
    let mut allc_2m_mp = PageAllocatorUnLockedMap::<ALLOCATOR_SIZE_2M>::new_empty();
    let mut allc_1g_mp = PageAllocatorUnLockedMap::<ALLOCATOR_SIZE_1G>::new_empty();

    pt_mp.retype_4k_as_unlocked_singleton(layout.cpu_pagetable, cpu_pagetable, (), Ghost(cpu_pagetable_lower), Tracked(cpu_pagetable_page_perm), 0, layout.root_thread, Ghost(KernelObjId::PageTable(layout.cpu_pagetable)));
    it_mp.retype_4k_as_unlocked_singleton(layout.iommu_table, iommu_table, (), Ghost(()), Tracked(iommu_table_page_perm), 0, layout.root_thread, Ghost(KernelObjId::IommuTable(layout.iommu_table)));
    ctn_mp.retype_2m_as_unlocked_singleton(layout.root_container, container, container_rodata, Ghost(container_ghost), Tracked(container_page_perm),
        0, layout.root_thread, Ghost(KernelObjId::Container(layout.root_container)), LockOwnerId::Some(0));
    let tracked boot_lctx = LocalContext::new_bootstrap(0, layout.root_thread);
    sched_mp.retype_page_to_scheduler_and_insert(layout.scheduler, scheduler, Tracked(scheduler_page_perm), Tracked(&boot_lctx));
    pcid_allc_mp.retype_2m_as_unlocked_singleton(layout.pcid_allocator, pcid_allocator, (), Ghost(()), Tracked(pcid_allocator_page_perm), 0, layout.root_thread, Ghost(KernelObjId::PcidAllocator(layout.pcid_allocator)));
    cpu_set_mp.retype_4k_as_unlocked_singleton(layout.cpu_set, cpu_set, (), Ghost(()), Tracked(cpu_set_page_perm), 0, layout.root_thread, Ghost(KernelObjId::CpuSet(layout.cpu_set)));
    prc_mp.retype_4k_as_unlocked_singleton(layout.root_process, process, process_rodata, Ghost(process_ghost), Tracked(process_page_perm), 0, layout.root_thread, Ghost(KernelObjId::Process(layout.root_process)));
    ep_mp.retype_4k_as_unlocked_singleton(layout.root_endpoint, endpoint, (), Ghost(()), Tracked(endpoint_page_perm), 0, layout.root_thread, Ghost(KernelObjId::Endpoint(layout.root_endpoint)));
    allc_4k_mp.retype_page_to_allocator_and_insert(layout.allocator_4k, allocator_4k, Tracked(allocator_4k_page_perm), Tracked(&boot_lctx));
    allc_2m_mp.retype_page_to_allocator_and_insert(layout.allocator_2m, allocator_2m, Tracked(allocator_2m_page_perm), Tracked(&boot_lctx));
    allc_1g_mp.retype_page_to_allocator_and_insert(layout.allocator_1g, allocator_1g, Tracked(allocator_1g_page_perm), Tracked(&boot_lctx));
    let mut cpu_offline_mp = CpuOfflineFlagsUnLockedMap::new_empty();
    let cpu_offline_flags = CpuOfflineFlags::new_empty(Ghost(layout.root_container), Ghost(0usize), Ghost(cpu_offline_flags_ptr(layout.root_container)));
    cpu_offline_mp.retype_container_page_tail_and_insert(&ctn_mp, layout.root_container, cpu_offline_flags, Tracked(&boot_lctx));

    let tracked mut pt_lower = Map::<RwLockPageTableRoot, PageTableLower<PT_TYPE>>::tracked_empty();
    proof { pt_lower.tracked_insert(layout.cpu_pagetable, cpu_pagetable_lower); }
    let krnl = KernelK {
        pt_mp, pt_lower: Tracked(pt_lower), it_mp, irt, pg_arr: page_array, cpu_arr: cpu_array, pcid_needflush, cpu_offline_mp, cpu_published, ctn_mp, sched_mp, pcid_allc_mp, cpu_set_mp,
        prc_mp, thr_mp, ep_mp, allc_4k_mp, allc_2m_mp, allc_1g_mp, cpu_tlb, iommu_tlb, rt_ctn: layout.root_container, dflt_pt: default_pagetable,
    };
    proof {
        boot_subsystems_inv_eof(&krnl, layout, kernel_l4_end, *initial_regs, kernel_entries.view(), manifest_4k.view(), page_array, pcid_needflush, cpu_published, default_pagetable,
            boot_cpu_page_closure, &free_4k_pool, &free_2m_pool, &free_1g_pool, owned_pages.view(), owned_pci_functions.view(), scheduler_node_addr, process_node_addr);
        boot_memory_management_inv_eof(&krnl, layout, kernel_l4_end, *initial_regs, kernel_entries.view(), manifest_4k.view(), page_array, pcid_needflush, cpu_published, default_pagetable,
            boot_cpu_page_closure, &free_4k_pool, &free_2m_pool, &free_1g_pool, owned_pages.view(), owned_pci_functions.view(), scheduler_node_addr, process_node_addr);
        boot_process_management_inv_eof(&krnl, layout, kernel_l4_end, *initial_regs, kernel_entries.view(), manifest_4k.view(), page_array, pcid_needflush, cpu_published, default_pagetable,
            boot_cpu_page_closure, &free_4k_pool, &free_2m_pool, &free_1g_pool, owned_pages.view(), owned_pci_functions.view(), scheduler_node_addr, process_node_addr);
        boot_kernel_inv_eof(&krnl, layout, kernel_l4_end, *initial_regs, kernel_entries.view(), manifest_4k.view(), page_array, pcid_needflush, cpu_published, default_pagetable,
            boot_cpu_page_closure, &free_4k_pool, &free_2m_pool, &free_1g_pool, owned_pages.view(), owned_pci_functions.view(), scheduler_node_addr, process_node_addr);
    }
    PPtr::<KernelK>::from_usize(layout.kernel_ptr).put(Tracked(&mut kernel_perm), krnl);
    Tracked(kernel_perm)
}
}
