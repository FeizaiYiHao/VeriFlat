use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal};
use crate::*;

verus! {
/// In the projection, the 2M window `w` of the unlocked page table of the live process `prc_ptr` is unlocked when the table lists it: a
/// thread that holds a window holds the table too.
pub proof fn pagetable_unlocked_implies_projected_window_unlocked(krnl: &KernelK, prc_ptr: RwLockProcessPtr, w: WindowVa)
    requires
        pagetable_lower_wf(krnl.pt_mp, krnl.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(krnl.pt_mp, krnl.pt_lower.view()),
        krnl.prc_mp.dom().contains(prc_ptr),
        !krnl.prc_mp.spec_index(prc_ptr).view().zombie,
        krnl.pt_mp.dom().contains(krnl.prc_mp.spec_index(prc_ptr).view().pagetable),
        !krnl.pt_mp.spec_index(krnl.prc_mp.spec_index(prc_ptr).view().pagetable).locked(),
    ensures
        ({
            let pagetable = kernel_k_to_kernel_u(*krnl).process_map[prc_ptr].pagetable->Some_0;
            &&& kernel_k_to_kernel_u(*krnl).process_map[prc_ptr].pagetable is Some
            &&& pagetable.pagetable_window_locks.dom().contains(w) ==> pagetable.pagetable_window_locks[w] is Unlocked
        }),
{
    let pt = krnl.prc_mp.spec_index(prc_ptr).view().pagetable;
    let e = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pt);
    kernel_process_projection_at(krnl, prc_ptr);
    if e.lower.pagetable_window_locks.dom().contains(w) {
        pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pt); e.wf_window_locks_va_at(w); spec_va_2m_valid_index_roundtrip(w.va);
        pagetable_window_holders_hold_pagetable_at(krnl.pt_mp, krnl.pt_lower.view(), pt, spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va),
            e.lower.l2_owner(e.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))->Write_thread_id);
    }
}

/// Installing the present IO leaf of size `size` (4K or 2M) at `va` in page table `pagetable` of the live process together with
/// one more BAR mapping of its function `f` adds that leaf to the process's user mapping of that size and raises `f`'s
/// mapped-BAR-page count by one.
pub proof fn kernel_pci_bar_mapped_implies_u_step(pre: &KernelK, post: &KernelK, pagetable: RwLockPageTableRoot, va: VAddr, f: PciBdf, size: PageSize)
    requires
        process_pagetable_wf(pre.prc_mp, pre.pt_mp),
        pre.pt_mp.dom().contains(pagetable),
        !pre.prc_mp.spec_index(pre.pt_mp.spec_index(pagetable).view().higher.proc_ptr).view().zombie,
        *post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..*pre }),
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable),
        post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable)),
        post.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread(),
        post.pt_mp.spec_index(pagetable).view().higher == (PageTableHigher { pci: post.pt_mp.spec_index(pagetable).view().higher.pci, ..pre.pt_mp.spec_index(pagetable).view().higher }),
        pre.pt_mp.spec_index(pagetable).view().higher.pci.view().dom().contains(f),
        post.pt_mp.spec_index(pagetable).view().higher.pci.mapping_counts()
            == pre.pt_mp.spec_index(pagetable).view().higher.pci.mapping_counts().insert(f, (pre.pt_mp.spec_index(pagetable).view().higher.pci.mapping_counts()[f] + 1) as nat),
        size is SZ4k ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k()
            == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().insert(va, whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k()[va]),
        size is SZ4k ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k()[va].present,
        !(size is SZ4k) ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k(),
        size is SZ2m ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_2m()
            == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().insert(va, whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_2m()[va]),
        size is SZ2m ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_2m()[va].present,
        !(size is SZ2m) ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_1g(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).lower.pagetable_window_locks == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.pagetable_window_locks,
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let prc_ptr = pre.pt_mp.spec_index(pagetable).view().higher.proc_ptr;
            let p = a.process_map[prc_ptr];
            let t = p.pagetable->Some_0;
            let c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
            &&& a.process_map.dom().contains(prc_ptr)
            &&& p.pagetable is Some
            &&& t.pci_functions == pre.pt_mp.spec_index(pagetable).view().higher.pci.mapping_counts()
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                process_map: a.process_map.insert(prc_ptr, ProcessU {
                    pagetable: Some(PageTableU {
                        mapping_4k: if size is SZ4k { t.mapping_4k.insert(va, c.mapping_4k()[va]) } else { t.mapping_4k },
                        mapping_2m: if size is SZ2m { t.mapping_2m.insert(va, c.mapping_2m()[va]) } else { t.mapping_2m },
                        pci_functions: t.pci_functions.insert(f, (t.pci_functions[f] + 1) as nat), ..t
                    }), ..p
                }),
                ..a
            })
        }),
{
    kernel_k_to_kernel_u_implies_domains_and_scalars_from_k(pre); kernel_k_to_kernel_u_implies_domains_and_scalars_from_k(post); reveal(process_pagetable_wf);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    let prc_ptr = pre.pt_mp.spec_index(pagetable).view().higher.proc_ptr;
    kernel_process_projection_at(pre, prc_ptr); kernel_process_projection_at(post, prc_ptr);
    let p = a.process_map[prc_ptr];
    let t = p.pagetable->Some_0;
    let c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
    let new_t = PageTableU {
        mapping_4k: if size is SZ4k { t.mapping_4k.insert(va, c.mapping_4k()[va]) } else { t.mapping_4k },
        mapping_2m: if size is SZ2m { t.mapping_2m.insert(va, c.mapping_2m()[va]) } else { t.mapping_2m },
        pci_functions: t.pci_functions.insert(f, (t.pci_functions[f] + 1) as nat), ..t
    };
    if size is SZ4k {
        assert_maps_equal!(b.process_map[prc_ptr].pagetable->Some_0.mapping_4k, new_t.mapping_4k, v => {});
    } else if size is SZ2m {
        assert_maps_equal!(b.process_map[prc_ptr].pagetable->Some_0.mapping_2m, new_t.mapping_2m, v => {});
    }
    assert_maps_equal!(b.process_map, a.process_map.insert(prc_ptr, ProcessU { pagetable: Some(new_t), ..p }), q => {
        if pre.prc_mp.dom().contains(q) { kernel_process_projection_at(pre, q); kernel_process_projection_at(post, q); }
    });
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_container_maps_unchanged_implies_u_container_map(pre, post);
    kernel_thread_map_unchanged_implies_u_thread_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}

/// Removing the IO leaf of size `size` (4K or 2M) at `va`, which the user no longer sees, from page table `pagetable` of the live
/// process together with the BAR mapping `(va, size)` of its function `f` lowers only `f`'s mapped-BAR-page count, by one.
pub proof fn kernel_pci_bar_unmapped_implies_u_step(pre: &KernelK, post: &KernelK, pagetable: RwLockPageTableRoot, va: VAddr, f: PciBdf, size: PageSize)
    requires
        process_pagetable_wf(pre.prc_mp, pre.pt_mp),
        pre.pt_mp.dom().contains(pagetable),
        !pre.prc_mp.spec_index(pre.pt_mp.spec_index(pagetable).view().higher.proc_ptr).view().zombie,
        *post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..*pre }),
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable),
        post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable)),
        post.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread(),
        post.pt_mp.spec_index(pagetable).view().higher == (PageTableHigher { pci: post.pt_mp.spec_index(pagetable).view().higher.pci, ..pre.pt_mp.spec_index(pagetable).view().higher }),
        pre.pt_mp.spec_index(pagetable).view().higher.pci.view().dom().contains(f),
        pre.pt_mp.spec_index(pagetable).view().higher.pci.view()[f].contains((va, size)),
        post.pt_mp.spec_index(pagetable).view().higher.pci.mapping_counts()
            == pre.pt_mp.spec_index(pagetable).view().higher.pci.mapping_counts().insert(f, (pre.pt_mp.spec_index(pagetable).view().higher.pci.mapping_counts()[f] - 1) as nat),
        size is SZ4k ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().remove(va),
        size is SZ4k && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom().contains(va) ==> !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k()[va].present,
        !(size is SZ4k) ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k(),
        size is SZ2m ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().remove(va),
        size is SZ2m && whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().dom().contains(va) ==> !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m()[va].present,
        !(size is SZ2m) ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_1g(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).lower.pagetable_window_locks == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.pagetable_window_locks,
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let prc_ptr = pre.pt_mp.spec_index(pagetable).view().higher.proc_ptr;
            let p = a.process_map[prc_ptr];
            let t = p.pagetable->Some_0;
            &&& a.process_map.dom().contains(prc_ptr)
            &&& p.pagetable is Some
            &&& t.pci_functions == pre.pt_mp.spec_index(pagetable).view().higher.pci.mapping_counts()
            &&& t.pci_functions.dom().contains(f) && t.pci_functions[f] > 0
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                process_map: a.process_map.insert(prc_ptr, ProcessU { pagetable: Some(PageTableU { pci_functions: t.pci_functions.insert(f, (t.pci_functions[f] - 1) as nat), ..t }), ..p }),
                ..a
            })
            &&& a != kernel_k_to_kernel_u(*post)
        }),
{
    kernel_k_to_kernel_u_implies_domains_and_scalars_from_k(pre); kernel_k_to_kernel_u_implies_domains_and_scalars_from_k(post); reveal(process_pagetable_wf);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    let prc_ptr = pre.pt_mp.spec_index(pagetable).view().higher.proc_ptr;
    kernel_process_projection_at(pre, prc_ptr); kernel_process_projection_at(post, prc_ptr);
    let p = a.process_map[prc_ptr];
    let t = p.pagetable->Some_0;
    let new_t = PageTableU { pci_functions: t.pci_functions.insert(f, (t.pci_functions[f] - 1) as nat), ..t };
    assert(t.pci_functions[f] > 0) by { broadcast use vstd::set::lemma_set_contains_len; };
    if size is SZ4k {
        assert_maps_equal!(b.process_map[prc_ptr].pagetable->Some_0.mapping_4k, t.mapping_4k, v => {});
    } else if size is SZ2m {
        assert_maps_equal!(b.process_map[prc_ptr].pagetable->Some_0.mapping_2m, t.mapping_2m, v => {});
    }
    assert_maps_equal!(b.process_map, a.process_map.insert(prc_ptr, ProcessU { pagetable: Some(new_t), ..p }), q => {
        if pre.prc_mp.dom().contains(q) { kernel_process_projection_at(pre, q); kernel_process_projection_at(post, q); }
    });
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_container_maps_unchanged_implies_u_container_map(pre, post);
    kernel_thread_map_unchanged_implies_u_thread_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
    assert(a != b) by { assert(b.process_map[prc_ptr].pagetable->Some_0.pci_functions[f] != t.pci_functions[f]); };
}

}
