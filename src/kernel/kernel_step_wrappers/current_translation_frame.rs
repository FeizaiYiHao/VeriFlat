use vstd::prelude::*;
use crate::*;

verus! {
/// The `size` frame at `frame`, whose head page is `Owned4k`, `Owned2m` or `Owned1g` as `size` says, is named by no translation
/// a cpu may use right now and by no IOTLB translation in the projection of `k`.
pub proof fn kernel_owned_page_implies_u_frame_named_by_no_current_translation(k: KernelK, size: PageSize, frame: PAddr)
    requires
        k.inv(),
        page_ptr_valid(frame),
        ({
            let state = k.pg_arr.spec_index(page_ptr2page_index(frame)).view().view().state;
            match size { PageSize::SZ4k => state is Owned4k, PageSize::SZ2m => state is Owned2m, PageSize::SZ1g => state is Owned1g }
        }),
    ensures kernel_u_frame_named_by_no_current_translation(kernel_k_to_kernel_u(k), size, frame),
{
    broadcast use kernel_owned_page_implies_u_current_tlb_4k_entry_outside_frame_at, kernel_owned_page_implies_u_current_tlb_2m_entry_outside_frame_at,
        kernel_owned_page_implies_u_current_tlb_1g_entry_outside_frame_at, kernel_owned_page_implies_u_iotlb_4k_entry_outside_frame_at;
}

/// A valid cpu `c` that runs a process whose PCID is the non-default `pcid` caches under `pcid`, in the projection of `k` as in
/// `k`, only non-empty user leaves of that process's page table.
pub proof fn kernel_cpu_current_pcid_implies_tlb_subset_of_current_pagetable(k: KernelK, c: CpuId, pcid: Pcid)
    requires
        k.inv(),
        index_valid(NUM_CPUS, c),
        kernel_k_to_kernel_u(k).cpu_array[c as int].current_process is Some,
        kernel_k_to_kernel_u(k).process_map[kernel_k_to_kernel_u(k).cpu_array[c as int].current_process->Some_0].pcid == pcid,
        pcid != KERNEL_DEFAULT_PCID,
    ensures
        ({
            let pt = k.prc_mp.spec_index(kernel_k_to_kernel_u(k).cpu_array[c as int].current_process->Some_0).view().pagetable;
            &&& k.pt_mp.dom().contains(pt)
            &&& kernel_k_to_kernel_u(k).cpu_tlb[(c, pcid)] == k.cpu_tlb.spec_index((c, pcid))
            &&& single_tlb_subset_of_whole_pagetable(k.cpu_tlb.spec_index((c, pcid)), whole_pagetable(k.pt_mp, k.pt_lower.view(), pt))
        }),
{
    let p = kernel_k_to_kernel_u(k).cpu_array[c as int].current_process->Some_0;
    kernel_u_domains_projection(&k); kernel_cpu_projection_at(&k, c); process_cpu_wf_at(k.prc_mp, k.cpu_arr, c);
    kernel_process_projection_at(&k, p); process_pagetable_wf_process_at(k.prc_mp, k.pt_mp, p);
    cpu_hw_cr3_pcid_wf_at(k.cpu_hw_cr3_pcid, k.cpu_arr, k.pcid_needflush, k.cpu_op.view().view(), c); cpu_tlb_wf_at(k.cpu_tlb, k.pt_mp, k.pt_lower.view(), k.cpu_arr, k.pcid_needflush, c, pcid);
}

/// Point form of the CPU 4K clause of `kernel_owned_page_implies_u_frame_named_by_no_current_translation` at one cpu, PCID and VA:
/// the translation names a `Mapped4k` page or an `Unavailable` BAR page, while the frame's pages are its owned head and merged tails.
broadcast proof fn kernel_owned_page_implies_u_current_tlb_4k_entry_outside_frame_at(k: KernelK, frame: PAddr, c: CpuId, pcid: Pcid, va: VAddr)
    requires
        k.inv(),
        page_ptr_valid(frame),
        k.pg_arr.spec_index(page_ptr2page_index(frame)).view().view().state is Owned4k || k.pg_arr.spec_index(page_ptr2page_index(frame)).view().view().state is Owned2m
            || k.pg_arr.spec_index(page_ptr2page_index(frame)).view().view().state is Owned1g,
    ensures
        #![trigger kernel_k_to_kernel_u(k).cpu_tlb[(c, pcid)].tlb_4k[va], k.pg_arr.spec_index(page_ptr2page_index(frame))]
        ({
            let u = kernel_k_to_kernel_u(k);
            let state = k.pg_arr.spec_index(page_ptr2page_index(frame)).view().view().state;
            let end = frame + if state is Owned4k { 0x1000int } else if state is Owned2m { 0x200000int } else { 0x40000000int };
            index_valid(NUM_CPUS, c) && u.cpu_array[c as int].current_process is Some && u.process_map.dom().contains(u.cpu_array[c as int].current_process->Some_0)
                && u.process_map[u.cpu_array[c as int].current_process->Some_0].pcid == pcid && pcid != KERNEL_DEFAULT_PCID && u.cpu_tlb[(c, pcid)].tlb_4k.dom().contains(va)
                ==> !(frame < u.cpu_tlb[(c, pcid)].tlb_4k[va].addr + 0x1000 && u.cpu_tlb[(c, pcid)].tlb_4k[va].addr < end)
        }),
{
    let u = kernel_k_to_kernel_u(k);
    let fidx = page_ptr2page_index(frame);
    let state = k.pg_arr.spec_index(fidx).view().view().state;
    let end = frame + if state is Owned4k { 0x1000int } else if state is Owned2m { 0x200000int } else { 0x40000000int };
    page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); hugepage_2m_wf_head_at(k.pg_arr, fidx); hugepage_1g_wf_head_at(k.pg_arr, fidx);
    if index_valid(NUM_CPUS, c) && u.cpu_array[c as int].current_process is Some && u.process_map[u.cpu_array[c as int].current_process->Some_0].pcid == pcid && pcid != KERNEL_DEFAULT_PCID {
        let pt = k.prc_mp.spec_index(u.cpu_array[c as int].current_process->Some_0).view().pagetable;
        let (l4i, l3i, l2i, l1i) = (spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va));
        kernel_cpu_current_pcid_implies_tlb_subset_of_current_pagetable(k, c, pcid);
        if k.cpu_tlb.spec_index((c, pcid)).tlb_4k().dom().contains(va) {
            let leaf = whole_pagetable(k.pt_mp, k.pt_lower.view(), pt).spec_nonempty_4k_l1(l4i, l3i, l2i, l1i)->0;
            let idx = page_ptr2page_index(leaf.addr);
            spec_va_4k_valid_index_roundtrip(va);
            if leaf.perm.is_io {
                pagetable_pci_mappings_wf_nonempty_4k_at(k.pci_bars.view(), k.pt_mp, k.pt_lower.view(), pt, l4i, l3i, l2i, l1i);
                assert(PAGE_SZ_4K == 0x1000 && PAGE_SZ_2M == 0x200000 && PAGE_SZ_1G == 0x40000000) by (compute);
                if frame <= leaf.addr && leaf.addr < end {
                    assert(idx < NUM_PAGES && page_index2page_ptr(idx) == leaf.addr) by (nonlinear_arith)
                        requires
                            leaf.addr % 0x1000 == 0, idx == leaf.addr / 4096, frame % 0x1000 == 0, fidx == frame / 4096, fidx < NUM_PAGES, NUM_PAGES == 0x100000,
                            leaf.addr < frame + 0x1000 || (fidx % 512 == 0 && leaf.addr < frame + 0x200000) || (fidx % 0x40000 == 0 && leaf.addr < frame + 0x40000000),
                            frame <= leaf.addr;
                    pci_bar_pages_unavailable_wf_at(k.pci_bars.view(), k.pg_arr, idx);
                }
            } else {
                mapped_4k_page_pagetable_wf_nonempty_leaf_at(k.pt_mp, k.pt_lower.view(), k.pg_arr, pt, l4i, l3i, l2i, l1i);
                mapped_4k_page_pagetable_wf_page_at(k.pt_mp, k.pt_lower.view(), k.pg_arr, idx, pt, va);
            }
            hugepage_2m_wf_tail_forward_at(k.pg_arr, fidx, idx); hugepage_1g_wf_tail_forward_at(k.pg_arr, fidx, idx);
        }
    }
}

/// Point form of the CPU 2M clause of `kernel_owned_page_implies_u_frame_named_by_no_current_translation` at one cpu, PCID and VA:
/// the translation names a 2M-aligned `Mapped2m` head with `Merged2m` tails or a 2M chunk of `Unavailable` BAR pages.
broadcast proof fn kernel_owned_page_implies_u_current_tlb_2m_entry_outside_frame_at(k: KernelK, frame: PAddr, c: CpuId, pcid: Pcid, va: VAddr)
    requires
        k.inv(),
        page_ptr_valid(frame),
        k.pg_arr.spec_index(page_ptr2page_index(frame)).view().view().state is Owned4k || k.pg_arr.spec_index(page_ptr2page_index(frame)).view().view().state is Owned2m
            || k.pg_arr.spec_index(page_ptr2page_index(frame)).view().view().state is Owned1g,
    ensures
        #![trigger kernel_k_to_kernel_u(k).cpu_tlb[(c, pcid)].tlb_2m[va], k.pg_arr.spec_index(page_ptr2page_index(frame))]
        ({
            let u = kernel_k_to_kernel_u(k);
            let state = k.pg_arr.spec_index(page_ptr2page_index(frame)).view().view().state;
            let end = frame + if state is Owned4k { 0x1000int } else if state is Owned2m { 0x200000int } else { 0x40000000int };
            index_valid(NUM_CPUS, c) && u.cpu_array[c as int].current_process is Some && u.process_map.dom().contains(u.cpu_array[c as int].current_process->Some_0)
                && u.process_map[u.cpu_array[c as int].current_process->Some_0].pcid == pcid && pcid != KERNEL_DEFAULT_PCID && u.cpu_tlb[(c, pcid)].tlb_2m.dom().contains(va)
                ==> !(frame < u.cpu_tlb[(c, pcid)].tlb_2m[va].addr + 0x200000 && u.cpu_tlb[(c, pcid)].tlb_2m[va].addr < end)
        }),
{
    let u = kernel_k_to_kernel_u(k);
    let fidx = page_ptr2page_index(frame);
    let state = k.pg_arr.spec_index(fidx).view().view().state;
    let end = frame + if state is Owned4k { 0x1000int } else if state is Owned2m { 0x200000int } else { 0x40000000int };
    page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); hugepage_2m_wf_head_at(k.pg_arr, fidx); hugepage_1g_wf_head_at(k.pg_arr, fidx);
    if index_valid(NUM_CPUS, c) && u.cpu_array[c as int].current_process is Some && u.process_map[u.cpu_array[c as int].current_process->Some_0].pcid == pcid && pcid != KERNEL_DEFAULT_PCID {
        let pt = k.prc_mp.spec_index(u.cpu_array[c as int].current_process->Some_0).view().pagetable;
        let (l4i, l3i, l2i) = (spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va));
        kernel_cpu_current_pcid_implies_tlb_subset_of_current_pagetable(k, c, pcid);
        if k.cpu_tlb.spec_index((c, pcid)).tlb_2m().dom().contains(va) {
            let leaf = whole_pagetable(k.pt_mp, k.pt_lower.view(), pt).spec_nonempty_2m_l2(l4i, l3i, l2i)->0;
            let idx = page_ptr2page_index(leaf.addr);
            spec_va_2m_valid_index_roundtrip(va);
            if leaf.perm.is_io {
                let bars = k.pci_bars.view();
                pagetable_pci_mappings_wf_nonempty_2m_at(bars, k.pt_mp, k.pt_lower.view(), pt, l4i, l3i, l2i);
                assert(PAGE_SZ_4K == 0x1000 && PAGE_SZ_2M == 0x200000 && PAGE_SZ_1G == 0x40000000) by (compute);
                if leaf.addr <= frame && frame < leaf.addr + 0x200000 {
                    assert(pci_bar_page(bars, frame)) by {
                        assert(bars[pci_bar_entry_of_page(bars, leaf.addr)->0].envelope_contains(frame)) by { assert(PAGE_SZ_4K == 0x1000) by (compute); };
                    };
                    pci_bar_pages_unavailable_wf_at(bars, k.pg_arr, fidx);
                }
                if frame < leaf.addr && leaf.addr < end {
                    assert(idx < NUM_PAGES && page_index2page_ptr(idx) == leaf.addr) by (nonlinear_arith)
                        requires
                            leaf.addr % 0x1000 == 0, idx == leaf.addr / 4096, frame % 0x1000 == 0, fidx == frame / 4096, fidx < NUM_PAGES, NUM_PAGES == 0x100000,
                            leaf.addr < frame + 0x1000 || (fidx % 512 == 0 && leaf.addr < frame + 0x200000) || (fidx % 0x40000 == 0 && leaf.addr < frame + 0x40000000),
                            frame < leaf.addr;
                    pci_bar_pages_unavailable_wf_at(bars, k.pg_arr, idx);
                }
            } else {
                mapped_2m_page_pagetable_wf_nonempty_leaf_at(k.pt_mp, k.pt_lower.view(), k.pg_arr, pt, l4i, l3i, l2i);
                mapped_2m_page_pagetable_wf_page_at(k.pt_mp, k.pt_lower.view(), k.pg_arr, idx, pt, va);
                hugepage_2m_wf_head_at(k.pg_arr, idx); hugepage_2m_wf_tail_forward_at(k.pg_arr, idx, fidx);
            }
            hugepage_1g_wf_tail_forward_at(k.pg_arr, fidx, idx);
        }
    }
}

/// Point form of the CPU 1G clause of `kernel_owned_page_implies_u_frame_named_by_no_current_translation` at one cpu, PCID and VA:
/// the translation names a 1G-aligned `Mapped1g` head with `Merged1g` tails.
broadcast proof fn kernel_owned_page_implies_u_current_tlb_1g_entry_outside_frame_at(k: KernelK, frame: PAddr, c: CpuId, pcid: Pcid, va: VAddr)
    requires
        k.inv(),
        page_ptr_valid(frame),
        k.pg_arr.spec_index(page_ptr2page_index(frame)).view().view().state is Owned4k || k.pg_arr.spec_index(page_ptr2page_index(frame)).view().view().state is Owned2m
            || k.pg_arr.spec_index(page_ptr2page_index(frame)).view().view().state is Owned1g,
    ensures
        #![trigger kernel_k_to_kernel_u(k).cpu_tlb[(c, pcid)].tlb_1g[va], k.pg_arr.spec_index(page_ptr2page_index(frame))]
        ({
            let u = kernel_k_to_kernel_u(k);
            let state = k.pg_arr.spec_index(page_ptr2page_index(frame)).view().view().state;
            let end = frame + if state is Owned4k { 0x1000int } else if state is Owned2m { 0x200000int } else { 0x40000000int };
            index_valid(NUM_CPUS, c) && u.cpu_array[c as int].current_process is Some && u.process_map.dom().contains(u.cpu_array[c as int].current_process->Some_0)
                && u.process_map[u.cpu_array[c as int].current_process->Some_0].pcid == pcid && pcid != KERNEL_DEFAULT_PCID && u.cpu_tlb[(c, pcid)].tlb_1g.dom().contains(va)
                ==> !(frame < u.cpu_tlb[(c, pcid)].tlb_1g[va].addr + 0x40000000 && u.cpu_tlb[(c, pcid)].tlb_1g[va].addr < end)
        }),
{
    let u = kernel_k_to_kernel_u(k);
    let fidx = page_ptr2page_index(frame);
    page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); hugepage_2m_wf_head_at(k.pg_arr, fidx); hugepage_1g_wf_head_at(k.pg_arr, fidx);
    if index_valid(NUM_CPUS, c) && u.cpu_array[c as int].current_process is Some && u.process_map[u.cpu_array[c as int].current_process->Some_0].pcid == pcid && pcid != KERNEL_DEFAULT_PCID {
        let pt = k.prc_mp.spec_index(u.cpu_array[c as int].current_process->Some_0).view().pagetable;
        let (l4i, l3i) = (spec_v2l4index(va), spec_v2l3index(va));
        kernel_cpu_current_pcid_implies_tlb_subset_of_current_pagetable(k, c, pcid);
        if k.cpu_tlb.spec_index((c, pcid)).tlb_1g().dom().contains(va) {
            let leaf = whole_pagetable(k.pt_mp, k.pt_lower.view(), pt).spec_nonempty_1g_l3(l4i, l3i)->0;
            let idx = page_ptr2page_index(leaf.addr);
            spec_va_1g_valid_index_roundtrip(va);
            mapped_1g_page_pagetable_wf_nonempty_leaf_at(k.pt_mp, k.pt_lower.view(), k.pg_arr, pt, l4i, l3i);
            mapped_1g_page_pagetable_wf_page_at(k.pt_mp, k.pt_lower.view(), k.pg_arr, idx, pt, va);
            hugepage_1g_wf_head_at(k.pg_arr, idx); hugepage_1g_wf_tail_forward_at(k.pg_arr, idx, fidx);
        }
    }
}

/// Point form of the IOTLB clause of `kernel_owned_page_implies_u_frame_named_by_no_current_translation` at one domain and IOVA:
/// the translation names a `Mapped4k` page of the IOMMU table attached at the domain's anchor B/D/F.
broadcast proof fn kernel_owned_page_implies_u_iotlb_4k_entry_outside_frame_at(k: KernelK, frame: PAddr, did: VtdDomainId, va: VAddr)
    requires
        k.inv(),
        page_ptr_valid(frame),
        k.pg_arr.spec_index(page_ptr2page_index(frame)).view().view().state is Owned4k || k.pg_arr.spec_index(page_ptr2page_index(frame)).view().view().state is Owned2m
            || k.pg_arr.spec_index(page_ptr2page_index(frame)).view().view().state is Owned1g,
    ensures
        #![trigger kernel_k_to_kernel_u(k).iommu_tlb[did].tlb_4k[va], k.pg_arr.spec_index(page_ptr2page_index(frame))]
        ({
            let u = kernel_k_to_kernel_u(k);
            let state = k.pg_arr.spec_index(page_ptr2page_index(frame)).view().view().state;
            let end = frame + if state is Owned4k { 0x1000int } else if state is Owned2m { 0x200000int } else { 0x40000000int };
            u.iommu_tlb.dom().contains(did) && u.iommu_tlb[did].tlb_4k.dom().contains(va) ==> !(frame < u.iommu_tlb[did].tlb_4k[va].addr + 0x1000 && u.iommu_tlb[did].tlb_4k[va].addr < end)
        }),
{
    let fidx = page_ptr2page_index(frame);
    page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip(); hugepage_2m_wf_head_at(k.pg_arr, fidx); hugepage_1g_wf_head_at(k.pg_arr, fidx);
    kernel_u_domains_projection(&k);
    if k.iommu_tlb.view().dom().contains(did) && k.iommu_tlb.spec_index(did).tlb_4k().dom().contains(va) {
        let irt = k.irt.view();
        let anchor = pci_bdf_of_did(did);
        assert(vtd_domain_id_valid(did)) by { reveal(IommuTLB::inv); };
        assert(pci_bdf_valid(anchor.0, anchor.1, anchor.2)) by (nonlinear_arith) requires vtd_domain_id_valid(did), anchor == pci_bdf_of_did(did);
        irt.wf_context_entry_at(anchor.0, anchor.1, anchor.2);
        let it = k.prc_mp.spec_index(irt.spec_index_owner(anchor.0, anchor.1, anchor.2)->Some_0).view().iommu_table->Some_0;
        assert(k.it_mp.dom().contains(it) && k.it_mp.spec_index(it).view().mapping_4k().contains_key(va)
            && k.iommu_tlb.spec_index(did).tlb_4k().spec_index(va).addr == k.it_mp.spec_index(it).view().mapping_4k().spec_index(va).addr) by {
            reveal(iommu_tlb_wf); reveal(iommu_root_table_process_wf);
        };
        iommu_table_perms_wf_at(k.it_mp, it);
        page_iommu_table_wf_table_at(k.ctn_mp, k.prc_mp, k.it_mp, k.pg_arr, it, va);
        let idx = page_ptr2page_index(k.it_mp.spec_index(it).view().mapping_4k().spec_index(va).addr);
        hugepage_2m_wf_tail_forward_at(k.pg_arr, fidx, idx); hugepage_1g_wf_tail_forward_at(k.pg_arr, fidx, idx);
    }
}
}
