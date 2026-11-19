use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal};
use crate::*;

verus! {
/// Installing the present IO 4K leaf at `va` in page table `pagetable` of the live process together with one more BAR mapping of
/// its function `f` adds that leaf to the process's 4K user mapping and raises `f`'s mapped-BAR-page count by one.
pub proof fn kernel_pci_bar_4k_mapped_implies_u_step(pre: &KernelK, post: &KernelK, pagetable: RwLockPageTableRoot, va: VAddr, f: PciBdf)
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
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k()
            == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().insert(va, whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k()[va]),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k()[va].present,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_1g(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).lower.pagetable_window_locks == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.pagetable_window_locks,
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let prc_ptr = pre.pt_mp.spec_index(pagetable).view().higher.proc_ptr;
            let p = a.process_map[prc_ptr];
            let t = p.pagetable->Some_0;
            let entry = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k()[va];
            &&& a.process_map.dom().contains(prc_ptr)
            &&& p.pagetable is Some
            &&& t.pci_functions == pre.pt_mp.spec_index(pagetable).view().higher.pci.mapping_counts()
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                process_map: a.process_map.insert(prc_ptr, ProcessU {
                    pagetable: Some(PageTableU { mapping_4k: t.mapping_4k.insert(va, entry), pci_functions: t.pci_functions.insert(f, (t.pci_functions[f] + 1) as nat), ..t }), ..p
                }),
                ..a
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post); reveal(process_pagetable_wf);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    let prc_ptr = pre.pt_mp.spec_index(pagetable).view().higher.proc_ptr;
    kernel_process_projection_at(pre, prc_ptr); kernel_process_projection_at(post, prc_ptr);
    let p = a.process_map[prc_ptr];
    let t = p.pagetable->Some_0;
    let entry = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k()[va];
    let new_t = PageTableU { mapping_4k: t.mapping_4k.insert(va, entry), pci_functions: t.pci_functions.insert(f, (t.pci_functions[f] + 1) as nat), ..t };
    assert_maps_equal!(b.process_map[prc_ptr].pagetable->Some_0.mapping_4k, new_t.mapping_4k, v => {});
    assert_maps_equal!(b.process_map, a.process_map.insert(prc_ptr, ProcessU { pagetable: Some(new_t), ..p }), q => {
        if pre.prc_mp.dom().contains(q) { kernel_process_projection_at(pre, q); kernel_process_projection_at(post, q); }
    });
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_container_maps_unchanged_implies_u_container_map(pre, post);
    kernel_thread_map_unchanged_implies_u_thread_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}

/// Installing the present IO 2M leaf at `va` in page table `pagetable` of the live process together with one more BAR mapping of
/// its function `f` adds that leaf to the process's 2M user mapping and raises `f`'s mapped-BAR-page count by one.
pub proof fn kernel_pci_bar_2m_mapped_implies_u_step(pre: &KernelK, post: &KernelK, pagetable: RwLockPageTableRoot, va: VAddr, f: PciBdf)
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
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_2m()
            == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().insert(va, whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_2m()[va]),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_2m()[va].present,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_1g(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).lower.pagetable_window_locks == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.pagetable_window_locks,
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let prc_ptr = pre.pt_mp.spec_index(pagetable).view().higher.proc_ptr;
            let p = a.process_map[prc_ptr];
            let t = p.pagetable->Some_0;
            let entry = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_2m()[va];
            &&& a.process_map.dom().contains(prc_ptr)
            &&& p.pagetable is Some
            &&& t.pci_functions == pre.pt_mp.spec_index(pagetable).view().higher.pci.mapping_counts()
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                process_map: a.process_map.insert(prc_ptr, ProcessU {
                    pagetable: Some(PageTableU { mapping_2m: t.mapping_2m.insert(va, entry), pci_functions: t.pci_functions.insert(f, (t.pci_functions[f] + 1) as nat), ..t }), ..p
                }),
                ..a
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post); reveal(process_pagetable_wf);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    let prc_ptr = pre.pt_mp.spec_index(pagetable).view().higher.proc_ptr;
    kernel_process_projection_at(pre, prc_ptr); kernel_process_projection_at(post, prc_ptr);
    let p = a.process_map[prc_ptr];
    let t = p.pagetable->Some_0;
    let entry = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_2m()[va];
    let new_t = PageTableU { mapping_2m: t.mapping_2m.insert(va, entry), pci_functions: t.pci_functions.insert(f, (t.pci_functions[f] + 1) as nat), ..t };
    assert_maps_equal!(b.process_map[prc_ptr].pagetable->Some_0.mapping_2m, new_t.mapping_2m, v => {});
    assert_maps_equal!(b.process_map, a.process_map.insert(prc_ptr, ProcessU { pagetable: Some(new_t), ..p }), q => {
        if pre.prc_mp.dom().contains(q) { kernel_process_projection_at(pre, q); kernel_process_projection_at(post, q); }
    });
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_container_maps_unchanged_implies_u_container_map(pre, post);
    kernel_thread_map_unchanged_implies_u_thread_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}

/// Removing the IO 4K leaf at `va`, which the user no longer sees, from page table `pagetable` of the live process together with the
/// BAR mapping `(va, 4K)` of its function `f` lowers only `f`'s mapped-BAR-page count, by one.
pub proof fn kernel_pci_bar_4k_unmapped_implies_u_step(pre: &KernelK, post: &KernelK, pagetable: RwLockPageTableRoot, va: VAddr, f: PciBdf)
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
        pre.pt_mp.spec_index(pagetable).view().higher.pci.view()[f].contains((va, PageSize::SZ4k)),
        post.pt_mp.spec_index(pagetable).view().higher.pci.mapping_counts()
            == pre.pt_mp.spec_index(pagetable).view().higher.pci.mapping_counts().insert(f, (pre.pt_mp.spec_index(pagetable).view().higher.pci.mapping_counts()[f] - 1) as nat),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().remove(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom().contains(va) ==> !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k()[va].present,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m(),
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
            &&& kernel_u_pci_bar_counts_changed(a, kernel_k_to_kernel_u(*post), prc_ptr)
            &&& a != kernel_k_to_kernel_u(*post)
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post); reveal(process_pagetable_wf);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    let prc_ptr = pre.pt_mp.spec_index(pagetable).view().higher.proc_ptr;
    kernel_process_projection_at(pre, prc_ptr); kernel_process_projection_at(post, prc_ptr);
    let p = a.process_map[prc_ptr];
    let t = p.pagetable->Some_0;
    let new_t = PageTableU { pci_functions: t.pci_functions.insert(f, (t.pci_functions[f] - 1) as nat), ..t };
    assert(t.pci_functions[f] > 0) by { broadcast use vstd::set::lemma_set_contains_len; };
    assert_maps_equal!(b.process_map[prc_ptr].pagetable->Some_0.mapping_4k, t.mapping_4k, v => {});
    assert_maps_equal!(b.process_map, a.process_map.insert(prc_ptr, ProcessU { pagetable: Some(new_t), ..p }), q => {
        if pre.prc_mp.dom().contains(q) { kernel_process_projection_at(pre, q); kernel_process_projection_at(post, q); }
    });
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_container_maps_unchanged_implies_u_container_map(pre, post);
    kernel_thread_map_unchanged_implies_u_thread_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
    assert(a != b) by { assert(b.process_map[prc_ptr].pagetable->Some_0.pci_functions[f] != t.pci_functions[f]); };
    assert(kernel_u_pci_bar_counts_changed(a, b, prc_ptr)) by { reveal(kernel_u_pci_bar_counts_changed); assert(new_t.pci_functions.dom() =~= t.pci_functions.dom()); };
}

/// Removing the IO 2M leaf at `va`, which the user no longer sees, from page table `pagetable` of the live process together with the
/// BAR mapping `(va, 2M)` of its function `f` lowers only `f`'s mapped-BAR-page count, by one.
pub proof fn kernel_pci_bar_2m_unmapped_implies_u_step(pre: &KernelK, post: &KernelK, pagetable: RwLockPageTableRoot, va: VAddr, f: PciBdf)
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
        pre.pt_mp.spec_index(pagetable).view().higher.pci.view()[f].contains((va, PageSize::SZ2m)),
        post.pt_mp.spec_index(pagetable).view().higher.pci.mapping_counts()
            == pre.pt_mp.spec_index(pagetable).view().higher.pci.mapping_counts().insert(f, (pre.pt_mp.spec_index(pagetable).view().higher.pci.mapping_counts()[f] - 1) as nat),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().remove(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().dom().contains(va) ==> !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m()[va].present,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k(),
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
            &&& kernel_u_pci_bar_counts_changed(a, kernel_k_to_kernel_u(*post), prc_ptr)
            &&& a != kernel_k_to_kernel_u(*post)
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post); reveal(process_pagetable_wf);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    let prc_ptr = pre.pt_mp.spec_index(pagetable).view().higher.proc_ptr;
    kernel_process_projection_at(pre, prc_ptr); kernel_process_projection_at(post, prc_ptr);
    let p = a.process_map[prc_ptr];
    let t = p.pagetable->Some_0;
    let new_t = PageTableU { pci_functions: t.pci_functions.insert(f, (t.pci_functions[f] - 1) as nat), ..t };
    assert(t.pci_functions[f] > 0) by { broadcast use vstd::set::lemma_set_contains_len; };
    assert_maps_equal!(b.process_map[prc_ptr].pagetable->Some_0.mapping_2m, t.mapping_2m, v => {});
    assert_maps_equal!(b.process_map, a.process_map.insert(prc_ptr, ProcessU { pagetable: Some(new_t), ..p }), q => {
        if pre.prc_mp.dom().contains(q) { kernel_process_projection_at(pre, q); kernel_process_projection_at(post, q); }
    });
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_container_maps_unchanged_implies_u_container_map(pre, post);
    kernel_thread_map_unchanged_implies_u_thread_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
    assert(a != b) by { assert(b.process_map[prc_ptr].pagetable->Some_0.pci_functions[f] != t.pci_functions[f]); };
    assert(kernel_u_pci_bar_counts_changed(a, b, prc_ptr)) by { reveal(kernel_u_pci_bar_counts_changed); assert(new_t.pci_functions.dom() =~= t.pci_functions.dom()); };
}
}
