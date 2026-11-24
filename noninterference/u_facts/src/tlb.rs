use vstd::prelude::*;
use veriflat_kernel_core::*;

verus! {
/// The translations of size `size` that `tlb` caches.
pub open spec fn single_tlb_entries_of_size(tlb: SingleTLB, size: PageSize) -> Map<VAddr, TLBEntry> {
    match size {
        PageSize::SZ4k => tlb.tlb_4k,
        PageSize::SZ2m => tlb.tlb_2m,
        PageSize::SZ1g => tlb.tlb_1g,
    }
}

/// The page state of a page that page-table leaves of size `size` map.
pub open spec fn mapped_page_state_of_size(size: PageSize) -> PageState {
    match size {
        PageSize::SZ4k => PageState::Mapped4k,
        PageSize::SZ2m => PageState::Mapped2m,
        PageSize::SZ1g => PageState::Mapped1g,
    }
}

/// The frame `frame` that a leaf of size `size` at `va` of the page table `pt` of `krnl` names is a page of BAR memory (a 4K
/// BAR page or a 2M BAR chunk), or a page of the page array in the mapped state of that size whose mappings list `(pt, va)`.
pub open spec fn kernel_frame_mapped_by_pagetable_at(krnl: KernelK, pt: RwLockPageTableRoot, size: PageSize, va: VAddr, frame: PAddr) -> bool {
    let pg = page_ptr2page_index(frame);
    ||| size is SZ4k && pci_bar_page(krnl.pci_bars.view(), frame)
    ||| size is SZ2m && pci_bar_2m_chunk(krnl.pci_bars.view(), frame)
    ||| {
        &&& index_valid(NUM_PAGES, pg) && page_index2page_ptr(pg) == frame
        &&& krnl.pg_arr.spec_index(pg).view().view().state == mapped_page_state_of_size(size)
        &&& krnl.pg_arr.spec_index(pg).view().view().mappings().contains((pt, va))
    }
}

/// For every valid cpu running a process with a non-default PCID and a page table, every translation the cpu's TLB caches
/// under that PCID at a VA where the table has a present leaf of the same size names that leaf's frame, write and
/// execute-disable bits.
#[verifier::opaque]
pub open spec fn kernel_u_current_tlb_matches_present_wf(u: KernelU) -> bool {
    forall|c: CpuId| #![trigger u.cpu_array[c as int].current_process] index_valid(NUM_CPUS, c) && u.cpu_array[c as int].current_process is Some ==> {
        let p = u.cpu_array[c as int].current_process->Some_0;
        let tlb = u.cpu_tlb[(c, u.process_map[p].pcid)];
        let table = u.process_map[p].pagetable->Some_0;
        u.process_map.dom().contains(p) && u.process_map[p].pcid != KERNEL_DEFAULT_PCID && u.process_map[p].pagetable is Some ==> {
            &&& forall|va: VAddr| #![trigger tlb.tlb_4k[va]] tlb.tlb_4k.dom().contains(va) && table.mapping_4k.dom().contains(va) ==> spec_tlb_entry_equal_to_map_entry(tlb.tlb_4k[va], table.mapping_4k[va])
            &&& forall|va: VAddr| #![trigger tlb.tlb_2m[va]] tlb.tlb_2m.dom().contains(va) && table.mapping_2m.dom().contains(va) ==> spec_tlb_entry_equal_to_map_entry(tlb.tlb_2m[va], table.mapping_2m[va])
            &&& forall|va: VAddr| #![trigger tlb.tlb_1g[va]] tlb.tlb_1g.dom().contains(va) && table.mapping_1g.dom().contains(va) ==> spec_tlb_entry_equal_to_map_entry(tlb.tlb_1g[va], table.mapping_1g[va])
        }
    }
}

/// For a valid cpu `c` whose user record runs process `p`, the kernel's recorded current PCID of `c` is `p`'s PCID, `c`'s
/// current page table and the dirty-bitmap slot of that PCID both name `p`'s page table, and `p`'s user page table is the
/// user view of that table.
pub proof fn kernel_inv_implies_current_pcid_names_current_pagetable(krnl: &KernelK, c: CpuId)
    requires krnl.inv(), index_valid(NUM_CPUS, c), kernel_k_to_kernel_u(*krnl).cpu_array[c as int].current_process is Some,
    ensures
        ({
            let u = kernel_k_to_kernel_u(*krnl);
            let p = u.cpu_array[c as int].current_process->Some_0;
            let cpu = krnl.cpu_arr.spec_index(c).view().view();
            let pt = krnl.prc_mp.spec_index(p).view().pagetable;
            &&& u.process_map.dom().contains(p) && krnl.prc_mp.dom().contains(p)
            &&& cpu.view().current_process == Some(p)
            &&& cpu.view().current_pcid == u.process_map[p].pcid && pcid_valid(u.process_map[p].pcid)
            &&& cpu.view().current_pagetable == Some(pt)
            &&& cpu.tlb_dirty_bitmap().spec_index(u.process_map[p].pcid) is Some && cpu.tlb_dirty_bitmap().spec_index(u.process_map[p].pcid)->Some_0.pagetable_ptr == pt
            &&& krnl.pt_mp.dom().contains(pt)
            &&& u.process_map[p].pagetable == Some(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pt).user_view(krnl.pt_mp.spec_index(pt).lock_state_u()))
        }),
{
    reveal(kernel_k_to_kernel_u);
    let p = kernel_k_to_kernel_u(*krnl).cpu_array[c as int].current_process->Some_0;
    process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, c);
    process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, p);
    cpu_hw_cr3_pcid_wf_at(krnl.cpu_hw_cr3_pcid, krnl.cpu_arr, krnl.pcid_needflush, krnl.cpu_op.view().view(), c);
}

/// For a valid cpu `c` running process `p` with a non-default PCID, the TLB of `c` under that PCID caches only non-empty
/// leaves of `p`'s well-formed page table, present or hidden, with their frame and permissions.
pub proof fn kernel_inv_implies_current_tlb_subset_of_whole_pagetable(krnl: &KernelK, c: CpuId)
    requires
        krnl.inv(), index_valid(NUM_CPUS, c), kernel_k_to_kernel_u(*krnl).cpu_array[c as int].current_process is Some,
        kernel_k_to_kernel_u(*krnl).process_map[kernel_k_to_kernel_u(*krnl).cpu_array[c as int].current_process->Some_0].pcid != KERNEL_DEFAULT_PCID,
    ensures
        ({
            let u = kernel_k_to_kernel_u(*krnl);
            let p = u.cpu_array[c as int].current_process->Some_0;
            let table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), krnl.prc_mp.spec_index(p).view().pagetable);
            &&& table.wf()
            &&& u.cpu_tlb[(c, u.process_map[p].pcid)] == krnl.cpu_tlb.spec_index((c, u.process_map[p].pcid))
            &&& single_tlb_subset_of_whole_pagetable(krnl.cpu_tlb.spec_index((c, u.process_map[p].pcid)), table)
        }),
{
    kernel_inv_implies_current_pcid_names_current_pagetable(krnl, c);
    let u = kernel_k_to_kernel_u(*krnl);
    let p = u.cpu_array[c as int].current_process->Some_0;
    let pt = krnl.prc_mp.spec_index(p).view().pagetable;
    pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pt);
    reveal(kernel_k_to_kernel_u);
    reveal(cpu_tlb_wf);
}

/// The user projection of a well-formed kernel satisfies `kernel_u_current_tlb_matches_present_wf`.
pub proof fn kernel_inv_implies_u_current_tlb_matches_present_wf(krnl: &KernelK)
    requires krnl.inv(),
    ensures kernel_u_current_tlb_matches_present_wf(kernel_k_to_kernel_u(*krnl)),
{
    let u = kernel_k_to_kernel_u(*krnl);
    reveal(kernel_u_current_tlb_matches_present_wf);
    assert forall|c: CpuId| #![trigger u.cpu_array[c as int].current_process] index_valid(NUM_CPUS, c) && u.cpu_array[c as int].current_process is Some implies {
        let p = u.cpu_array[c as int].current_process->Some_0;
        let tlb = u.cpu_tlb[(c, u.process_map[p].pcid)];
        let table = u.process_map[p].pagetable->Some_0;
        u.process_map.dom().contains(p) && u.process_map[p].pcid != KERNEL_DEFAULT_PCID && u.process_map[p].pagetable is Some ==> {
            &&& forall|va: VAddr| #![trigger tlb.tlb_4k[va]] tlb.tlb_4k.dom().contains(va) && table.mapping_4k.dom().contains(va) ==> spec_tlb_entry_equal_to_map_entry(tlb.tlb_4k[va], table.mapping_4k[va])
            &&& forall|va: VAddr| #![trigger tlb.tlb_2m[va]] tlb.tlb_2m.dom().contains(va) && table.mapping_2m.dom().contains(va) ==> spec_tlb_entry_equal_to_map_entry(tlb.tlb_2m[va], table.mapping_2m[va])
            &&& forall|va: VAddr| #![trigger tlb.tlb_1g[va]] tlb.tlb_1g.dom().contains(va) && table.mapping_1g.dom().contains(va) ==> spec_tlb_entry_equal_to_map_entry(tlb.tlb_1g[va], table.mapping_1g[va])
        }
    } by {
        let p = u.cpu_array[c as int].current_process->Some_0;
        let pcid = u.process_map[p].pcid;
        if pcid != KERNEL_DEFAULT_PCID {
            kernel_inv_implies_current_pcid_names_current_pagetable(krnl, c);
            kernel_inv_implies_current_tlb_subset_of_whole_pagetable(krnl, c);
            let pt = krnl.prc_mp.spec_index(p).view().pagetable;
            let whole = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pt);
            let tlb = u.cpu_tlb[(c, pcid)];
            let table = whole.user_view(krnl.pt_mp.spec_index(pt).lock_state_u());
            assert forall|va: VAddr| #![trigger tlb.tlb_4k[va]] tlb.tlb_4k.dom().contains(va) && table.mapping_4k.dom().contains(va)
                implies spec_tlb_entry_equal_to_map_entry(tlb.tlb_4k[va], table.mapping_4k[va]) by {
                assert(tlb.tlb_4k().dom().contains(va));
                spec_va_4k_valid_index_roundtrip(va);
                whole.wf_mapping_4k_at(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va));
                whole.spec_resolve_mapping_4k_l1_some_implies_spec_nonempty_4k_l1_eq(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va));
            };
            assert forall|va: VAddr| #![trigger tlb.tlb_2m[va]] tlb.tlb_2m.dom().contains(va) && table.mapping_2m.dom().contains(va)
                implies spec_tlb_entry_equal_to_map_entry(tlb.tlb_2m[va], table.mapping_2m[va]) by {
                assert(tlb.tlb_2m().dom().contains(va));
                spec_va_2m_valid_index_roundtrip(va);
                whole.wf_mapping_2m_at(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va));
                whole.spec_resolve_mapping_2m_l2_some_implies_spec_nonempty_2m_l2_eq(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va));
            };
            assert forall|va: VAddr| #![trigger tlb.tlb_1g[va]] tlb.tlb_1g.dom().contains(va) && table.mapping_1g.dom().contains(va)
                implies spec_tlb_entry_equal_to_map_entry(tlb.tlb_1g[va], table.mapping_1g[va]) by {
                assert(tlb.tlb_1g().dom().contains(va));
                spec_va_1g_valid_index_roundtrip(va);
                whole.higher.wf_mapping_1g_at(spec_v2l4index(va), spec_v2l3index(va));
                whole.higher.spec_nonempty_l4_resolves_implies_spec_nonempty_1g_l3_eq_resolve(spec_v2l4index(va), spec_v2l3index(va));
            };
        }
    };
}

/// For a valid cpu `c` running process `p` with a non-default PCID, an entry of size `size` at `va` that `c`'s TLB caches
/// under that PCID names a frame mapped by a leaf of `p`'s page table at `va`, present or hidden: a BAR page or chunk, or a
/// page in the mapped state of that size whose mappings list `(p's page table, va)`.
pub proof fn kernel_inv_implies_usable_tlb_entry_names_mapped_page(krnl: &KernelK, c: CpuId, size: PageSize, va: VAddr)
    requires
        krnl.inv(), index_valid(NUM_CPUS, c), kernel_k_to_kernel_u(*krnl).cpu_array[c as int].current_process is Some,
        ({
            let u = kernel_k_to_kernel_u(*krnl);
            let p = u.cpu_array[c as int].current_process->Some_0;
            &&& u.process_map[p].pcid != KERNEL_DEFAULT_PCID
            &&& single_tlb_entries_of_size(u.cpu_tlb[(c, u.process_map[p].pcid)], size).dom().contains(va)
        }),
    ensures
        ({
            let u = kernel_k_to_kernel_u(*krnl);
            let p = u.cpu_array[c as int].current_process->Some_0;
            let frame = single_tlb_entries_of_size(u.cpu_tlb[(c, u.process_map[p].pcid)], size)[va].addr;
            kernel_frame_mapped_by_pagetable_at(*krnl, krnl.prc_mp.spec_index(p).view().pagetable, size, va, frame)
        }),
{
    kernel_inv_implies_current_pcid_names_current_pagetable(krnl, c);
    kernel_inv_implies_current_tlb_subset_of_whole_pagetable(krnl, c);
    let u = kernel_k_to_kernel_u(*krnl);
    let p = u.cpu_array[c as int].current_process->Some_0;
    let pt = krnl.prc_mp.spec_index(p).view().pagetable;
    let whole = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pt);
    let tlb = krnl.cpu_tlb.spec_index((c, u.process_map[p].pcid));
    let bars = krnl.pci_bars.view();
    let (l4i, l3i, l2i, l1i) = (spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va));
    match size {
        PageSize::SZ4k => {
            assert(tlb.tlb_4k().dom().contains(va));
            spec_va_4k_valid_index_roundtrip(va);
            let leaf = whole.spec_nonempty_4k_l1(l4i, l3i, l2i, l1i)->0;
            if leaf.perm.is_io { pagetable_pci_mappings_wf_nonempty_4k_at(bars, krnl.pt_mp, krnl.pt_lower.view(), pt, l4i, l3i, l2i, l1i); } else {
                mapped_4k_page_pagetable_wf_nonempty_leaf_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pt, l4i, l3i, l2i, l1i);
                mapped_4k_page_pagetable_wf_page_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, page_ptr2page_index(leaf.addr), pt, va);
            }
        },
        PageSize::SZ2m => {
            assert(tlb.tlb_2m().dom().contains(va));
            spec_va_2m_valid_index_roundtrip(va);
            let leaf = whole.spec_nonempty_2m_l2(l4i, l3i, l2i)->0;
            if leaf.perm.is_io { pagetable_pci_mappings_wf_nonempty_2m_at(bars, krnl.pt_mp, krnl.pt_lower.view(), pt, l4i, l3i, l2i); } else {
                mapped_2m_page_pagetable_wf_nonempty_leaf_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pt, l4i, l3i, l2i);
                mapped_2m_page_pagetable_wf_page_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, page_ptr2page_index(leaf.addr), pt, va);
            }
        },
        PageSize::SZ1g => {
            assert(tlb.tlb_1g().dom().contains(va));
            spec_va_1g_valid_index_roundtrip(va);
            let leaf = whole.spec_nonempty_1g_l3(l4i, l3i)->0;
            mapped_1g_page_pagetable_wf_nonempty_leaf_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pt, l4i, l3i);
            mapped_1g_page_pagetable_wf_page_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, page_ptr2page_index(leaf.addr), pt, va);
        },
    }
}

/// A 4K entry at `iova` that the IOTLB caches for a domain `did` it holds names a page in the Mapped4k state whose IOMMU
/// mappings list `(it, iova)`, where `it` is the IOMMU table of the process owning the B/D/F that anchors `did`, which
/// carries `did`.
pub proof fn kernel_inv_implies_iotlb_entry_names_iommu_mapped_page(krnl: &KernelK, did: VtdDomainId, iova: VAddr)
    requires krnl.inv(), kernel_k_to_kernel_u(*krnl).iommu_tlb.dom().contains(did), kernel_k_to_kernel_u(*krnl).iommu_tlb[did].tlb_4k.dom().contains(iova),
    ensures
        ({
            let irt = krnl.irt.view();
            let anchor = pci_bdf_of_did(did);
            let owner = irt.spec_index_owner(anchor.0, anchor.1, anchor.2)->Some_0;
            let it = krnl.prc_mp.spec_index(owner).view().iommu_table->Some_0;
            let frame = kernel_k_to_kernel_u(*krnl).iommu_tlb[did].tlb_4k[iova].addr;
            let pg = page_ptr2page_index(frame);
            &&& vtd_domain_id_valid(did) && pci_bdf_valid(anchor.0, anchor.1, anchor.2) && irt.spec_index_iommu_did(anchor.0, anchor.1, anchor.2) == Some(did)
            &&& irt.spec_index_owner(anchor.0, anchor.1, anchor.2) is Some && krnl.prc_mp.dom().contains(owner) && krnl.prc_mp.spec_index(owner).view().iommu_table is Some
            &&& krnl.it_mp.dom().contains(it) && krnl.it_mp.spec_index(it).view().did == Some(did)
            &&& index_valid(NUM_PAGES, pg) && page_index2page_ptr(pg) == frame
            &&& krnl.pg_arr.spec_index(pg).view().view().state == PageState::Mapped4k
            &&& krnl.pg_arr.spec_index(pg).view().view().iommu_mappings().contains((it, iova))
        }),
{
    reveal(kernel_k_to_kernel_u);
    reveal(iommu_tlb_wf);
    reveal(iommu_root_table_process_wf);
    reveal(page_iommu_table_wf);
    reveal(IommuTLB::inv);
    let irt = krnl.irt.view();
    let anchor = pci_bdf_of_did(did);
    assert(pci_bdf_valid(anchor.0, anchor.1, anchor.2)) by (nonlinear_arith) requires vtd_domain_id_valid(did), anchor == pci_bdf_of_did(did);
    assert(krnl.iommu_tlb.spec_index(did).tlb_4k().dom().contains(iova));
    irt.wf_context_entry_at(anchor.0, anchor.1, anchor.2);
    let owner = irt.spec_index_owner(anchor.0, anchor.1, anchor.2)->Some_0;
    let it = krnl.prc_mp.spec_index(owner).view().iommu_table->Some_0;
    assert(krnl.it_mp.spec_index(it).view().mapping_4k().contains_key(iova));
    iommu_table_perms_wf_at(krnl.it_mp, it); page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
    let pg = page_ptr2page_index(krnl.it_mp.spec_index(it).view().mapping_4k().spec_index(iova).addr);
    assert(krnl.pg_arr.spec_index(pg).view().view().iommu_mappings().contains((it, iova)));
}
}
