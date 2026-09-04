use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal};
use crate::*;

verus! {

    pub open spec fn pagetable_map_user_view(
        pagetable_map: PageTableLockedMap,
    ) -> Map<RwLockPageTableRoot, PageTableU> {
        Map::new(
            pagetable_map.dom(),
            |ptr: RwLockPageTableRoot|
                pagetable_map.spec_index(ptr).view().user_view(),
        )
    }

    pub open spec fn iommu_table_map_user_view(
        iommu_table_map: IommuTableLockedMap,
    ) -> Map<RwLockPageTableRoot, PageTableU> {
        Map::new(
            iommu_table_map.dom(),
            |ptr: RwLockPageTableRoot|
                iommu_table_map.spec_index(ptr).view().user_view(),
        )
    }

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
    /// spec-level mapping used at every kernel boundary.  The boundary
    /// compares this projection with the preceding snapshot; only a changed
    /// projection is recorded as a user-visible step.
    pub open spec fn kernel_k_to_kernel_u(krnl: KernelK) -> KernelU {
        KernelU {
            cpu_array: Seq::new(
                NUM_CPUS as nat,
                |i: int| {
                    let c = krnl.cpu_arr.spec_index(i as usize).value.view();
                    CpuU {
                        owning_container: c.owning_container,
                        state: c.state,
                        current_process: c.current_process,
                        current_thread: c.current_thread,
                    }
                },
            ),
            process_map: Map::new(
                krnl.prc_mp.dom(),
                |ptr: RwLockProcessPtr| {
                    let p = krnl.prc_mp.spec_index(ptr).view();
                    let p_ghost = krnl.prc_mp.spec_index(ptr).view_ghost();
                    let p_ro = krnl.prc_mp.spec_index(ptr).view_rodata().view();
                    ProcessU {
                        pagetable: pagetable_map_user_view(krnl.pt_mp)
                            .spec_index(p.pagetable),
                        iommu_table: match p.iommu_table {
                            Some(iommu_table) => Some(
                                iommu_table_map_user_view(krnl.it_mp)
                                    .spec_index(iommu_table),
                            ),
                            None => None,
                        },
                        quota_4k: p.quota_4k,
                        quota_2m: p.quota_2m,
                        quota_1g: p.quota_1g,
                        parent: p_ro.parent,
                        children: p.children.view(),
                        depth: p_ro.depth,
                        uppertree_seq: p_ghost.uppertree_seq.view(),
                        subtree_set: p_ghost.subtree_set.view(),
                        owned_threads: p.owned_threads.view(),
                        killed: krnl.prc_mp.spec_index(ptr).being_killed(),
                    }
                },
            ),
        }
    }

    /// Framing lemma: `kernel_k_to_kernel_u` reads only a handful of per-element
    /// projections, NOT whole fields. So the user-view projections of two
    /// `KernelK`s are equal whenever they agree on exactly those projections:
    ///   - per cpu slot, the payload `value.view()`;
    ///   - per process, `view()` / `view_rodata()` / `view_ghost()` /
    ///     `being_killed()`, plus the process domain;
    ///   - per CPU/IOMMU pagetable entry, `view().user_view()`; directory
    ///     topology and lock state are irrelevant.
    /// Stated per-element (not as `process_map == ..` / `pagetable_map == ..`)
    /// so a caller that moved lock state on a held pagetable / process — which
    /// leaves the WHOLE map unequal but every `.view()` intact — can still use
    /// it. Mirror of `container_no_change_to_tree_fields_imply_wf`.
    pub proof fn kernel_no_change_to_user_view_fields_imply_kernel_u_eq(pre: &KernelK, post: &KernelK)
        requires
            // This connects each process's projected pagetable pointer to the
            // domain on which the per-entry framing premise below applies.
            // Domain equality alone does not constrain `Map::spec_index` at a
            // process-referenced key unless that key is known to be present.
            process_pagetable_match(pre.prc_mp, pre.pt_mp),
            process_iommu_table_match(pre.prc_mp, pre.it_mp),
            // pagetable_map: only the abstract mapping projection is read.
            post.pt_mp.dom() =~= pre.pt_mp.dom(),
            forall|pt: RwLockPageTableRoot|
                #![trigger post.pt_mp.spec_index(pt).view().user_view()]
                pre.pt_mp.dom().contains(pt) ==>
                    post.pt_mp.spec_index(pt).view().user_view()
                        == pre.pt_mp.spec_index(pt).view().user_view(),
            post.it_mp.dom() =~= pre.it_mp.dom(),
            forall|pt: RwLockPageTableRoot|
                #![trigger post.it_mp.spec_index(pt).view().user_view()]
                pre.it_mp.dom().contains(pt) ==>
                    post.it_mp.spec_index(pt).view().user_view()
                        == pre.it_mp.spec_index(pt).view().user_view(),
            post.irt == pre.irt,
            // process_map: same domain, and per process only the fields
            // `ProcessU` projects are read — quota/children fields off `view()`,
            // tree closure fields off `view_ghost()`, `parent`/`depth` off
            // `view_rodata()`, and `being_killed()`. NOT
            // the whole `view()`: other kernel-only fields are unprojected.
            post.prc_mp.dom() =~= pre.prc_mp.dom(),
            forall|ptr: RwLockProcessPtr|
                #![trigger post.prc_mp.spec_index(ptr)]
                pre.prc_mp.dom().contains(ptr) ==>
                    post.prc_mp.spec_index(ptr).view().quota_4k == pre.prc_mp.spec_index(ptr).view().quota_4k
                    && post.prc_mp.spec_index(ptr).view().quota_2m == pre.prc_mp.spec_index(ptr).view().quota_2m
                    && post.prc_mp.spec_index(ptr).view().quota_1g == pre.prc_mp.spec_index(ptr).view().quota_1g
                    && post.prc_mp.spec_index(ptr).view().children.view() == pre.prc_mp.spec_index(ptr).view().children.view()
                    && post.prc_mp.spec_index(ptr).view_ghost().uppertree_seq.view() == pre.prc_mp.spec_index(ptr).view_ghost().uppertree_seq.view()
                    && post.prc_mp.spec_index(ptr).view_ghost().subtree_set.view() == pre.prc_mp.spec_index(ptr).view_ghost().subtree_set.view()
                    && post.prc_mp.spec_index(ptr).view().owned_threads.view() == pre.prc_mp.spec_index(ptr).view().owned_threads.view()
                    && post.prc_mp.spec_index(ptr).view().pagetable == pre.prc_mp.spec_index(ptr).view().pagetable
                    && post.prc_mp.spec_index(ptr).view().iommu_table == pre.prc_mp.spec_index(ptr).view().iommu_table
                    && post.prc_mp.spec_index(ptr).view_rodata() == pre.prc_mp.spec_index(ptr).view_rodata()
                    && post.prc_mp.spec_index(ptr).being_killed() == pre.prc_mp.spec_index(ptr).being_killed(),
            // cpu_array: per-slot payload `view()`.
            forall|i: usize|
                #![trigger post.cpu_arr.spec_index(i).value.view()]
                index_valid(NUM_CPUS, i) ==>
                    post.cpu_arr.spec_index(i).value.view()
                        == pre.cpu_arr.spec_index(i).value.view(),
        ensures
            kernel_k_to_kernel_u(*pre) == kernel_k_to_kernel_u(*post),
    {
        let pre_u = kernel_k_to_kernel_u(*pre);
        let post_u = kernel_k_to_kernel_u(*post);
        assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array);
        assert_maps_equal!(post_u.process_map, pre_u.process_map, ptr => {
            reveal(process_pagetable_match);
            reveal(process_iommu_table_match);
        });
    }

}
