use vstd::prelude::*;
use crate::*;

verus! {

    /// User-level projection of the kernel state.
    ///
    /// This is a sound capture of the kernel user-level view because
    /// `LocalContext` does not provide any interface that allows
    /// Lock → Operate → Unlock → Lock on user-visible objects within a
    /// single syscall. Therefore, all operations on the user view can
    /// be seen as atomic from the syscall's perspective.
    pub ghost struct KernelU{
        pub cpu_array: Seq<CpuU>,
        pub process_map: Map<RwLockProcessPtr, ProcessU>,
    }

    /// Project a `KernelK` into its user-visible `KernelU`. This is the
    /// spec-level mapping that defines the user-view linearization point:
    /// at the moment the syscall declares it has reached its user-view
    /// linearization point, the user-visible state is exactly
    /// `kernel_k_to_kernel_u(kernel_k)`.
    pub open spec fn kernel_k_to_kernel_u(kernel_k: KernelK) -> KernelU {
        KernelU {
            cpu_array: Seq::new(
                NUM_CPUS as nat,
                |i: int| {
                    let c = kernel_k.cpu_array.spec_index(i as usize).value.view();
                    CpuU {
                        owning_container: c.owning_container,
                        state: c.state,
                        current_process: c.current_process,
                        current_thread: c.current_thread,
                    }
                },
            ),
            process_map: Map::new(
                kernel_k.process_map.dom(),
                |ptr: RwLockProcessPtr| {
                    let p = kernel_k.process_map.spec_index(ptr).view();
                    let p_ro = kernel_k.process_map.spec_index(ptr).view_rodata().view();
                    ProcessU {
                        pagetable: kernel_k.get_process_pagetable(ptr),
                        quota_4k: p.quota_4k,
                        quota_2m: p.quota_2m,
                        quota_1g: p.quota_1g,
                        parent: p_ro.parent,
                        children: p.children.view(),
                        depth: p_ro.depth,
                        uppertree_seq: p.uppertree_seq.view(),
                        subtree_set: p.subtree_set@,
                        owned_threads: p.owned_threads.view(),
                        killed: kernel_k.process_map.spec_index(ptr).being_killed(),
                    }
                },
            ),
        }
    }

    /// Framing lemma: `kernel_k_to_kernel_u` reads only a handful of per-element
    /// projections, NOT whole fields. So the user-view projections of two
    /// `KernelK`s are equal whenever they agree on exactly those projections:
    ///   - per cpu slot, the payload `value.view()`;
    ///   - per process, `view()` / `view_rodata()` / `being_killed()`, plus the
    ///     process domain;
    ///   - per pagetable entry, `view()` (the only thing `get_process_pagetable`
    ///     reads — lock state is irrelevant).
    /// Stated per-element (not as `process_map == ..` / `pagetable_map == ..`)
    /// so a caller that moved lock state on a held pagetable / process — which
    /// leaves the WHOLE map unequal but every `.view()` intact — can still use
    /// it. Mirror of `container_no_change_to_tree_fields_imply_wf`.
    pub proof fn kernel_no_change_to_user_view_fields_imply_kernel_u_eq(pre: &KernelK, post: &KernelK)
        requires
            // pagetable_map: only the per-entry `view()` is read (via
            // `get_process_pagetable`), not lock state.
            forall|pt: RwLockPageTableRoot|
                #![trigger post.pagetable_map.spec_index(pt).view()]
                post.pagetable_map.spec_index(pt).view() == pre.pagetable_map.spec_index(pt).view(),
            // process_map: same domain, and per process only the fields
            // `ProcessU` projects are read — quota/tree fields off `view()`,
            // `parent`/`depth` off `view_rodata()`, and `being_killed()`. NOT
            // the whole `view()`: `temp_alloc_cache_*` is unprojected, so a
            // caller that stages a page (mutating `view()` but no `ProcessU`
            // field) can still use this.
            post.process_map.dom() =~= pre.process_map.dom(),
            forall|ptr: RwLockProcessPtr|
                #![trigger post.process_map.spec_index(ptr)]
                pre.process_map.dom().contains(ptr) ==>
                    post.process_map.spec_index(ptr).view().quota_4k == pre.process_map.spec_index(ptr).view().quota_4k
                    && post.process_map.spec_index(ptr).view().quota_2m == pre.process_map.spec_index(ptr).view().quota_2m
                    && post.process_map.spec_index(ptr).view().quota_1g == pre.process_map.spec_index(ptr).view().quota_1g
                    && post.process_map.spec_index(ptr).view().children.view() == pre.process_map.spec_index(ptr).view().children.view()
                    && post.process_map.spec_index(ptr).view().uppertree_seq.view() == pre.process_map.spec_index(ptr).view().uppertree_seq.view()
                    && post.process_map.spec_index(ptr).view().subtree_set.view() == pre.process_map.spec_index(ptr).view().subtree_set.view()
                    && post.process_map.spec_index(ptr).view().owned_threads.view() == pre.process_map.spec_index(ptr).view().owned_threads.view()
                    && post.process_map.spec_index(ptr).view().pagetable == pre.process_map.spec_index(ptr).view().pagetable
                    && post.process_map.spec_index(ptr).view_rodata() == pre.process_map.spec_index(ptr).view_rodata()
                    && post.process_map.spec_index(ptr).being_killed() == pre.process_map.spec_index(ptr).being_killed(),
            // cpu_array: per-slot payload `view()`.
            forall|i: int|
                #![trigger post.cpu_array.spec_index(i as usize).value.view()]
                0 <= i < NUM_CPUS ==>
                    post.cpu_array.spec_index(i as usize).value.view()
                        == pre.cpu_array.spec_index(i as usize).value.view(),
        ensures
            kernel_k_to_kernel_u(*pre) == kernel_k_to_kernel_u(*post),
    {
        let pre_u = kernel_k_to_kernel_u(*pre);
        let post_u = kernel_k_to_kernel_u(*post);
        assert(post_u.cpu_array =~= pre_u.cpu_array) by {
            assert forall|i: int|
                0 <= i < NUM_CPUS
                implies #[trigger] post_u.cpu_array[i] == pre_u.cpu_array[i]
            by {}
        };
        assert(post_u.process_map =~= pre_u.process_map) by {
            assert forall|ptr: RwLockProcessPtr|
                #[trigger] post_u.process_map.dom().contains(ptr)
                implies post_u.process_map[ptr] == pre_u.process_map[ptr]
            by {}
        };
    }

}
