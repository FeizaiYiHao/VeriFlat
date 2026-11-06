use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal};
use crate::*;

verus! {
pub proof fn kernel_process_1g_mapping_changed_implies_u_neq(pre: &KernelK, post: &KernelK, prc_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires kernel_process_1g_mapping_changed(pre, post, prc_ptr, pagetable_ptr, va),
    ensures kernel_k_to_kernel_u(*pre) != kernel_k_to_kernel_u(*post),
{
    assert(kernel_k_to_kernel_u(*pre).process_map.spec_index(prc_ptr).pagetable.unwrap().mapping_1g.dom().contains(va) != kernel_k_to_kernel_u(*post).process_map.spec_index(prc_ptr).pagetable.unwrap().mapping_1g.dom().contains(va)) by {
        reveal(kernel_process_1g_mapping_changed); kernel_process_projection_at(pre, prc_ptr); kernel_process_projection_at(post, prc_ptr);
    };
}

impl KernelK {
    /// Records the section that changed the 1G leaf `va` of `prc_ptr`'s write-held pagetable.
    pub proof fn kernel_step_boundary_process_1g_mapping_changed(
        tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, prc_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr,
    )
        requires
            old(self).inv(),
            kernel_process_1g_mapping_changed(&old(steps).snapshot_k(), old(self), prc_ptr, pagetable_ptr, va),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            kernel_step_boundary_framing(*old(self), *final(self), *old(lctx)),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|p: RwLockPageTableRoot| #![trigger old(lctx).pagetable_lock_map().dom().contains(p)] typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), p, TypedLockMode::Write)
                ==> whole_pagetable(final(self).pt_mp, final(self).pt_lower.view(), p) == whole_pagetable(old(self).pt_mp, old(self).pt_lower.view(), p),
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == old(steps).view().push(KernelStep { old_u: old(steps).snapshot_u(), new_u: kernel_k_to_kernel_u(*old(self)) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).snapshot_k() == *final(self),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(self)),
    {
        use_type_invariant(&*steps);
        kernel_process_1g_mapping_changed_implies_u_neq(&steps.snapshot_k(), &*self, prc_ptr, pagetable_ptr, va);
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        reveal(LockedMap::typed_lock_map_aligned);
        old(self).pt_mp.typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
        pagetable_lower_backup_wf_at(old(self).pt_mp, old(self).pt_lower.view(), pagetable_ptr); pagetable_lower_backup_wf_at(self.pt_mp, self.pt_lower.view(), pagetable_ptr);
        reveal(process_pagetable_wf); reveal(process_iommu_table_wf);
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*self);
    }
}

/// The 1G frame at `addr`, whose head page is `Owned1g`, shares no frame with any 1G mapping and overlaps no 2M, 4K, or IOMMU 4K mapping in the projection of `k`.
pub proof fn kernel_owned_1g_page_implies_u_mappings_outside_its_frame(k: KernelK, addr: PagePtr)
    requires
        k.inv(),
        page_ptr_valid(addr),
        k.pg_arr.spec_index(page_ptr2page_index(addr)).view().view().state is Owned1g,
    ensures
        forall|p: RwLockProcessPtr, v: VAddr| #![trigger kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_1g[v]]
            kernel_k_to_kernel_u(k).process_map.dom().contains(p) && kernel_k_to_kernel_u(k).process_map[p].pagetable is Some && kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_1g.dom().contains(v)
            ==> kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_1g[v].addr != addr,
        forall|p: RwLockProcessPtr, v: VAddr| #![trigger kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_2m[v]]
            kernel_k_to_kernel_u(k).process_map.dom().contains(p) && kernel_k_to_kernel_u(k).process_map[p].pagetable is Some && kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_2m.dom().contains(v)
            ==> !(addr <= kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_2m[v].addr < addr + 0x40000000),
        forall|p: RwLockProcessPtr, v: VAddr| #![trigger kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_4k[v]]
            kernel_k_to_kernel_u(k).process_map.dom().contains(p) && kernel_k_to_kernel_u(k).process_map[p].pagetable is Some && kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_4k.dom().contains(v)
            ==> !(addr <= kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_4k[v].addr < addr + 0x40000000),
        forall|p: RwLockProcessPtr, v: VAddr| #![trigger kernel_k_to_kernel_u(k).process_map[p].iommu_table->Some_0.mapping_4k[v]]
            kernel_k_to_kernel_u(k).process_map.dom().contains(p) && kernel_k_to_kernel_u(k).process_map[p].iommu_table is Some && kernel_k_to_kernel_u(k).process_map[p].iommu_table->Some_0.mapping_4k.dom().contains(v)
            ==> !(addr <= kernel_k_to_kernel_u(k).process_map[p].iommu_table->Some_0.mapping_4k[v].addr < addr + 0x40000000),
{
    broadcast use kernel_owned_1g_page_implies_u_1g_mapping_frame_differs_at, kernel_owned_1g_page_implies_u_2m_mapping_outside_its_frame_at,
        kernel_owned_1g_page_implies_u_4k_mapping_outside_its_frame_at, kernel_owned_1g_page_implies_u_iommu_4k_mapping_outside_its_frame_at;
}

/// Point form of the 1G clause of `kernel_owned_1g_page_implies_u_mappings_outside_its_frame` at one process and VA.
broadcast proof fn kernel_owned_1g_page_implies_u_1g_mapping_frame_differs_at(k: KernelK, addr: PagePtr, p: RwLockProcessPtr, v: VAddr)
    requires
        k.inv(),
        page_ptr_valid(addr),
        k.pg_arr.spec_index(page_ptr2page_index(addr)).view().view().state is Owned1g,
    ensures
        #![trigger kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_1g[v], k.pg_arr.spec_index(page_ptr2page_index(addr))]
        kernel_k_to_kernel_u(k).process_map.dom().contains(p) && kernel_k_to_kernel_u(k).process_map[p].pagetable is Some && kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_1g.dom().contains(v)
            ==> kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_1g[v].addr != addr,
{
    kernel_u_domains_projection(&k);
    if k.prc_mp.dom().contains(p) {
        kernel_process_projection_at(&k, p); process_pagetable_wf_process_at(k.prc_mp, k.pt_mp, p);
        reveal(mapped_1g_page_pagetable_wf);
    }
}

/// Point form of the 2M clause of `kernel_owned_1g_page_implies_u_mappings_outside_its_frame` at one process and VA: a 2M mapping names a `Mapped2m` page, while the pages of the frame are its `Owned1g` head and `Merged1g` tails.
broadcast proof fn kernel_owned_1g_page_implies_u_2m_mapping_outside_its_frame_at(k: KernelK, addr: PagePtr, p: RwLockProcessPtr, v: VAddr)
    requires
        k.inv(),
        page_ptr_valid(addr),
        k.pg_arr.spec_index(page_ptr2page_index(addr)).view().view().state is Owned1g,
    ensures
        #![trigger kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_2m[v], k.pg_arr.spec_index(page_ptr2page_index(addr))]
        kernel_k_to_kernel_u(k).process_map.dom().contains(p) && kernel_k_to_kernel_u(k).process_map[p].pagetable is Some && kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_2m.dom().contains(v)
            ==> !(addr <= kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_2m[v].addr < addr + 0x40000000),
{
    kernel_u_domains_projection(&k);
    if k.prc_mp.dom().contains(p) {
        let pt = k.prc_mp.spec_index(p).view().pagetable;
        let head = page_ptr2page_index(addr);
        kernel_process_projection_at(&k, p); process_pagetable_wf_process_at(k.prc_mp, k.pt_mp, p);
        hugepage_1g_wf_head_at(k.pg_arr, head);
        if whole_pagetable(k.pt_mp, k.pt_lower.view(), pt).mapping_2m().contains_key(v) {
            let a = whole_pagetable(k.pt_mp, k.pt_lower.view(), pt).mapping_2m().spec_index(v).addr;
            let idx = page_ptr2page_index(a);
            assert(k.pg_arr.spec_index(idx).view().view().state == PageState::Mapped2m) by { reveal(mapped_2m_page_pagetable_wf); };
            if addr <= a < addr + 0x40000000 {
                assert(head <= idx < head + 0x40000 && idx < NUM_PAGES) by (nonlinear_arith)
                    requires addr % 0x1000 == 0, head == addr / 4096, idx == a / 4096, addr <= a < addr + 0x40000000, head % 0x40000 == 0, head < NUM_PAGES, NUM_PAGES % 0x40000 == 0;
                hugepage_1g_wf_tail_forward_at(k.pg_arr, head, idx);
            }
        }
    }
}

/// Point form of the 4K clause of `kernel_owned_1g_page_implies_u_mappings_outside_its_frame` at one process and VA: a 4K mapping names a `Mapped4k` page, while the pages of the frame are its `Owned1g` head and `Merged1g` tails.
broadcast proof fn kernel_owned_1g_page_implies_u_4k_mapping_outside_its_frame_at(k: KernelK, addr: PagePtr, p: RwLockProcessPtr, v: VAddr)
    requires
        k.inv(),
        page_ptr_valid(addr),
        k.pg_arr.spec_index(page_ptr2page_index(addr)).view().view().state is Owned1g,
    ensures
        #![trigger kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_4k[v], k.pg_arr.spec_index(page_ptr2page_index(addr))]
        kernel_k_to_kernel_u(k).process_map.dom().contains(p) && kernel_k_to_kernel_u(k).process_map[p].pagetable is Some && kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_4k.dom().contains(v)
            ==> !(addr <= kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_4k[v].addr < addr + 0x40000000),
{
    kernel_u_domains_projection(&k);
    if k.prc_mp.dom().contains(p) {
        let pt = k.prc_mp.spec_index(p).view().pagetable;
        let head = page_ptr2page_index(addr);
        kernel_process_projection_at(&k, p); process_pagetable_wf_process_at(k.prc_mp, k.pt_mp, p);
        mapped_4k_page_pagetable_wf_pagetable_at(k.pt_mp, k.pt_lower.view(), k.pg_arr, pt, v);
        hugepage_1g_wf_head_at(k.pg_arr, head);
        let a = whole_pagetable(k.pt_mp, k.pt_lower.view(), pt).mapping_4k().spec_index(v).addr;
        let idx = page_ptr2page_index(a);
        if addr <= a < addr + 0x40000000 {
            assert(head <= idx < head + 0x40000 && idx < NUM_PAGES) by (nonlinear_arith)
                requires addr % 0x1000 == 0, head == addr / 4096, idx == a / 4096, addr <= a < addr + 0x40000000, head % 0x40000 == 0, head < NUM_PAGES, NUM_PAGES % 0x40000 == 0;
            hugepage_1g_wf_tail_forward_at(k.pg_arr, head, idx);
        }
    }
}

/// Point form of the IOMMU clause of `kernel_owned_1g_page_implies_u_mappings_outside_its_frame` at one process and IOVA.
broadcast proof fn kernel_owned_1g_page_implies_u_iommu_4k_mapping_outside_its_frame_at(k: KernelK, addr: PagePtr, p: RwLockProcessPtr, v: VAddr)
    requires
        k.inv(),
        page_ptr_valid(addr),
        k.pg_arr.spec_index(page_ptr2page_index(addr)).view().view().state is Owned1g,
    ensures
        #![trigger kernel_k_to_kernel_u(k).process_map[p].iommu_table->Some_0.mapping_4k[v], k.pg_arr.spec_index(page_ptr2page_index(addr))]
        kernel_k_to_kernel_u(k).process_map.dom().contains(p) && kernel_k_to_kernel_u(k).process_map[p].iommu_table is Some && kernel_k_to_kernel_u(k).process_map[p].iommu_table->Some_0.mapping_4k.dom().contains(v)
            ==> !(addr <= kernel_k_to_kernel_u(k).process_map[p].iommu_table->Some_0.mapping_4k[v].addr < addr + 0x40000000),
{
    kernel_u_domains_projection(&k);
    if k.prc_mp.dom().contains(p) { kernel_process_projection_at(&k, p); }
    if k.prc_mp.dom().contains(p) && k.prc_mp.spec_index(p).view().iommu_table is Some {
        let it = k.prc_mp.spec_index(p).view().iommu_table->Some_0;
        let head = page_ptr2page_index(addr);
        process_iommu_table_wf_process_at(k.prc_mp, k.it_mp, p);
        if k.it_mp.spec_index(it).view().mapping_4k().dom().contains(v) {
            page_iommu_table_wf_table_at(k.ctn_mp, k.prc_mp, k.it_mp, k.pg_arr, it, v);
            hugepage_1g_wf_head_at(k.pg_arr, head);
            let a = k.it_mp.spec_index(it).view().mapping_4k().spec_index(v).addr;
            let idx = page_ptr2page_index(a);
            if addr <= a < addr + 0x40000000 {
                assert(head <= idx < head + 0x40000 && idx < NUM_PAGES) by (nonlinear_arith)
                    requires addr % 0x1000 == 0, head == addr / 4096, idx == a / 4096, addr <= a < addr + 0x40000000, head % 0x40000 == 0, head < NUM_PAGES, NUM_PAGES % 0x40000 == 0;
                hugepage_1g_wf_tail_forward_at(k.pg_arr, head, idx);
            }
        }
    }
}

/// The `Owned4k` page at `addr` lies in no 1G frame that a pagetable maps in the projection of `k`.
pub proof fn kernel_owned_4k_page_implies_u_outside_1g_mapping_frames(k: KernelK, addr: PagePtr)
    requires
        k.inv(),
        k.pg_arr.spec_index(page_ptr2page_index(addr)).view().view().state is Owned4k,
    ensures
        forall|p: RwLockProcessPtr, v: VAddr| #![trigger kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_1g[v]]
            kernel_k_to_kernel_u(k).process_map.dom().contains(p) && kernel_k_to_kernel_u(k).process_map[p].pagetable is Some && kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_1g.dom().contains(v)
            ==> !(kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_1g[v].addr <= addr < kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_1g[v].addr + 0x40000000),
{ broadcast use kernel_owned_4k_page_implies_u_outside_1g_mapping_frame_at; }

/// Point form of `kernel_owned_4k_page_implies_u_outside_1g_mapping_frames` at one process and VA: a 1G mapping names a 1G-aligned `Mapped1g` head whose frame's other pages are `Merged1g` tails.
broadcast proof fn kernel_owned_4k_page_implies_u_outside_1g_mapping_frame_at(k: KernelK, addr: PagePtr, p: RwLockProcessPtr, v: VAddr)
    requires
        k.inv(),
        k.pg_arr.spec_index(page_ptr2page_index(addr)).view().view().state is Owned4k,
    ensures
        #![trigger kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_1g[v], k.pg_arr.spec_index(page_ptr2page_index(addr))]
        kernel_k_to_kernel_u(k).process_map.dom().contains(p) && kernel_k_to_kernel_u(k).process_map[p].pagetable is Some && kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_1g.dom().contains(v)
            ==> !(kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_1g[v].addr <= addr < kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_1g[v].addr + 0x40000000),
{
    kernel_u_domains_projection(&k);
    if k.prc_mp.dom().contains(p) {
        let pt = k.prc_mp.spec_index(p).view().pagetable;
        kernel_process_projection_at(&k, p); process_pagetable_wf_process_at(k.prc_mp, k.pt_mp, p);
        pagetable_lower_wf_at(k.pt_mp, k.pt_lower.view(), pt);
        if whole_pagetable(k.pt_mp, k.pt_lower.view(), pt).mapping_1g().contains_key(v) {
            let m = whole_pagetable(k.pt_mp, k.pt_lower.view(), pt).mapping_1g().spec_index(v).addr;
            let head = page_ptr2page_index(m);
            let idx = page_ptr2page_index(addr);
            assert(k.pg_arr.spec_index(head).view().view().state == PageState::Mapped1g) by { reveal(mapped_1g_page_pagetable_wf); };
            if m <= addr < m + 0x40000000 {
                assert(head <= idx < head + 0x40000 && index_valid(NUM_PAGES, head) && index_valid(NUM_PAGES, idx)) by (nonlinear_arith)
                    requires m % 0x40000000 == 0, m / 4096 < NUM_PAGES, head == m / 4096, idx == addr / 4096, m <= addr < m + 0x40000000, NUM_PAGES % 0x40000 == 0;
                if idx != head { hugepage_1g_wf_tail_forward_at(k.pg_arr, head, idx); }
            }
        }
    }
}

/// The `Owned2m` 2M head page at `addr` lies in no 1G frame that a pagetable maps in the projection of `k`.
pub proof fn kernel_owned_2m_page_implies_u_outside_1g_mapping_frames(k: KernelK, addr: PagePtr)
    requires
        k.inv(),
        k.pg_arr.spec_index(page_ptr2page_index(addr)).view().view().state is Owned2m,
    ensures
        forall|p: RwLockProcessPtr, v: VAddr| #![trigger kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_1g[v]]
            kernel_k_to_kernel_u(k).process_map.dom().contains(p) && kernel_k_to_kernel_u(k).process_map[p].pagetable is Some && kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_1g.dom().contains(v)
            ==> !(kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_1g[v].addr <= addr < kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_1g[v].addr + 0x40000000),
{ broadcast use kernel_owned_2m_page_implies_u_outside_1g_mapping_frame_at; }

/// Point form of `kernel_owned_2m_page_implies_u_outside_1g_mapping_frames` at one process and VA: a 1G mapping names a 1G-aligned `Mapped1g` head whose frame's other pages are `Merged1g` tails.
broadcast proof fn kernel_owned_2m_page_implies_u_outside_1g_mapping_frame_at(k: KernelK, addr: PagePtr, p: RwLockProcessPtr, v: VAddr)
    requires
        k.inv(),
        k.pg_arr.spec_index(page_ptr2page_index(addr)).view().view().state is Owned2m,
    ensures
        #![trigger kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_1g[v], k.pg_arr.spec_index(page_ptr2page_index(addr))]
        kernel_k_to_kernel_u(k).process_map.dom().contains(p) && kernel_k_to_kernel_u(k).process_map[p].pagetable is Some && kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_1g.dom().contains(v)
            ==> !(kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_1g[v].addr <= addr < kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_1g[v].addr + 0x40000000),
{
    kernel_u_domains_projection(&k);
    if k.prc_mp.dom().contains(p) {
        let pt = k.prc_mp.spec_index(p).view().pagetable;
        kernel_process_projection_at(&k, p); process_pagetable_wf_process_at(k.prc_mp, k.pt_mp, p);
        pagetable_lower_wf_at(k.pt_mp, k.pt_lower.view(), pt);
        if whole_pagetable(k.pt_mp, k.pt_lower.view(), pt).mapping_1g().contains_key(v) {
            let m = whole_pagetable(k.pt_mp, k.pt_lower.view(), pt).mapping_1g().spec_index(v).addr;
            let head = page_ptr2page_index(m);
            let idx = page_ptr2page_index(addr);
            assert(k.pg_arr.spec_index(head).view().view().state == PageState::Mapped1g) by { reveal(mapped_1g_page_pagetable_wf); };
            if m <= addr < m + 0x40000000 {
                assert(head <= idx < head + 0x40000 && index_valid(NUM_PAGES, head) && index_valid(NUM_PAGES, idx)) by (nonlinear_arith)
                    requires m % 0x40000000 == 0, m / 4096 < NUM_PAGES, head == m / 4096, idx == addr / 4096, m <= addr < m + 0x40000000, NUM_PAGES % 0x40000 == 0;
                if idx != head { hugepage_1g_wf_tail_forward_at(k.pg_arr, head, idx); }
            }
        }
    }
}

/// Publishing a present 1G leaf at `va` in the write-held pagetable of the cpu's current process from an `Owned1g` page, with the thread's 1G quota, temporary 1G cache, and progress replaced, adds that leaf to the process's 1G user mapping and changes only that thread's 1G quota and
/// progress. The L3 entry of `va` links no L2 page, so no 2M or 4K leaf lies under it, and the frame overlaps no mapping.
pub proof fn kernel_thread_quota_1g_progress_and_1g_mapping_added_pagetable_wlocked_implies_u_step(pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(post, lctx),
        pre.thrd_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        pre.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        *post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, pg_arr: post.pg_arr, thrd_mp: post.thrd_mp, ..*pre }),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).view() == (Thread {
            quota_1g: post.thrd_mp.spec_index(thrd_ptr).view().quota_1g,
            temp_alloc_cache_1g: post.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g,
            syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress,
            ..pre.thrd_mp.spec_index(thrd_ptr).view()
        }),
        post.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        pre.prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr,
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        post.pt_mp.spec_index(pagetable_ptr).locking_thread() == pre.pt_mp.spec_index(pagetable_ptr).locking_thread(),
        post.pt_lower.view() == pre.pt_lower.view().insert(pagetable_ptr, post.pt_lower.view().spec_index(pagetable_ptr)),
        !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_1g().dom().contains(va),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_1g().insert(va, whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g().spec_index(va)),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g().spec_index(va).present,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks,
        spec_va_1g_valid(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is None,
        page_ptr_valid(whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g().spec_index(va).addr),
        pre.pg_arr.spec_index(page_ptr2page_index(whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g().spec_index(va).addr)).view().view().state is Owned1g,
    ensures
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let thread = pre.thrd_mp.spec_index(thrd_ptr).view();
            let process = pre_u.process_map.spec_index(prc_ptr);
            let l4i = spec_v2l4index(va);
            let l3i = spec_v2l3index(va);
            let addr = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g().spec_index(va).addr;
            &&& pre_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& pre_u.cpu_array[cpu_id as int].current_thread == pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread
            &&& pre_u.thread_map.dom().contains(thrd_ptr)
            &&& pre_u.thread_map.spec_index(thrd_ptr).lock_state is WriteLocked
            &&& pre_u.thread_map.spec_index(thrd_ptr).owning_container == thread.owning_container
            &&& pre_u.thread_map.spec_index(thrd_ptr).owning_proc == thread.owning_proc
            &&& pre_u.thread_map.spec_index(thrd_ptr).quota_1g == thread.quota_1g
            &&& pre_u.thread_map.spec_index(thrd_ptr).syscall_progress == thread.syscall_progress.view()
            &&& pre_u.process_map.dom().contains(prc_ptr)
            &&& process.pagetable is Some
            &&& process.pagetable->Some_0.lock_state is WriteLocked
            &&& !process.pagetable->Some_0.mapping_1g.dom().contains(va)
            &&& forall|l2i: L2Index| #![trigger process.pagetable->Some_0.mapping_2m.dom().contains(spec_index2va((l4i, l3i, l2i, 0)))]
                pei_valid(l2i) ==> !process.pagetable->Some_0.mapping_2m.dom().contains(spec_index2va((l4i, l3i, l2i, 0)))
            &&& forall|l2i: L2Index, l1i: L1Index| #![trigger process.pagetable->Some_0.mapping_4k.dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                pei_valid(l2i) && pei_valid(l1i) ==> !process.pagetable->Some_0.mapping_4k.dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
            &&& forall|p: RwLockProcessPtr, v: VAddr| #![trigger pre_u.process_map[p].pagetable->Some_0.mapping_1g[v]]
                pre_u.process_map.dom().contains(p) && pre_u.process_map[p].pagetable is Some && pre_u.process_map[p].pagetable->Some_0.mapping_1g.dom().contains(v)
                ==> pre_u.process_map[p].pagetable->Some_0.mapping_1g[v].addr != addr
            &&& forall|p: RwLockProcessPtr, v: VAddr| #![trigger pre_u.process_map[p].pagetable->Some_0.mapping_2m[v]]
                pre_u.process_map.dom().contains(p) && pre_u.process_map[p].pagetable is Some && pre_u.process_map[p].pagetable->Some_0.mapping_2m.dom().contains(v)
                ==> !(addr <= pre_u.process_map[p].pagetable->Some_0.mapping_2m[v].addr < addr + 0x40000000)
            &&& forall|p: RwLockProcessPtr, v: VAddr| #![trigger pre_u.process_map[p].pagetable->Some_0.mapping_4k[v]]
                pre_u.process_map.dom().contains(p) && pre_u.process_map[p].pagetable is Some && pre_u.process_map[p].pagetable->Some_0.mapping_4k.dom().contains(v)
                ==> !(addr <= pre_u.process_map[p].pagetable->Some_0.mapping_4k[v].addr < addr + 0x40000000)
            &&& forall|p: RwLockProcessPtr, v: VAddr| #![trigger pre_u.process_map[p].iommu_table->Some_0.mapping_4k[v]]
                pre_u.process_map.dom().contains(p) && pre_u.process_map[p].iommu_table is Some && pre_u.process_map[p].iommu_table->Some_0.mapping_4k.dom().contains(v)
                ==> !(addr <= pre_u.process_map[p].iommu_table->Some_0.mapping_4k[v].addr < addr + 0x40000000)
        }),
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let process = pre_u.process_map.spec_index(prc_ptr);
            let pagetable = process.pagetable->Some_0;
            let entry = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g().spec_index(va);
            kernel_k_to_kernel_u(*post) == (KernelU {
                thread_map: pre_u.thread_map.insert(thrd_ptr, ThreadU {
                    quota_1g: post.thrd_mp.spec_index(thrd_ptr).view().quota_1g,
                    syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(),
                    ..pre_u.thread_map.spec_index(thrd_ptr)
                }),
                process_map: pre_u.process_map.insert(prc_ptr, ProcessU {
                    pagetable: Some(PageTableU { mapping_1g: pagetable.mapping_1g.insert(va, entry), ..pagetable }),
                    ..process
                }),
                ..pre_u
            })
        }),
{
    pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr);
    spec_va_1g_valid_index_roundtrip(va);
    reveal(WholePageTable::wf_mapping_2m); reveal(WholePageTable::wf_mapping_4k);
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let process = pre_u.process_map.spec_index(prc_ptr);
    let pagetable = process.pagetable->Some_0;
    let entry = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g().spec_index(va);
    let new_pagetable = PageTableU { mapping_1g: pagetable.mapping_1g.insert(va, entry), ..pagetable };
    pre.thrd_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thrd_ptr);
    post.thrd_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thrd_ptr);
    pre.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
    post.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
    kernel_cpu_projection_at(post, cpu_id);
    if pre.prc_mp.dom().contains(prc_ptr) { kernel_process_projection_at(pre, prc_ptr); } if post.prc_mp.dom().contains(prc_ptr) { kernel_process_projection_at(post, prc_ptr); }
    if pre.thrd_mp.dom().contains(thrd_ptr) { kernel_thread_projection_at(pre, thrd_ptr); } if post.thrd_mp.dom().contains(thrd_ptr) { kernel_thread_projection_at(post, thrd_ptr); }
    assert(pre.cpu_arr.spec_index(cpu_id).view().wlocked_by_thread(lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); };
    assert(pre.prc_mp.dom().contains(prc_ptr) && !pre.prc_mp.spec_index(prc_ptr).view().zombie && pre.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr) by { reveal(process_cpu_wf); reveal(process_pagetable_wf); };
    assert(post_u.process_map.spec_index(prc_ptr).pagetable == Some(new_pagetable)) by {
        assert_maps_equal!(whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).user_view(post.pt_mp.spec_index(pagetable_ptr).lock_state_u()).mapping_1g, new_pagetable.mapping_1g);
    };
    kernel_owned_1g_page_implies_u_mappings_outside_its_frame(*pre, entry.addr);
    kernel_container_maps_unchanged_implies_u_container_map(pre, post);
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(prc_ptr, ProcessU { pagetable: Some(new_pagetable), ..process }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); } reveal(process_pagetable_wf);
    });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thrd_ptr, ThreadU {
        quota_1g: post.thrd_mp.spec_index(thrd_ptr).view().quota_1g,
        syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(),
        ..pre_u.thread_map.spec_index(thrd_ptr)
    }), t => { if pre.thrd_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thrd_mp.dom().contains(t) { kernel_thread_projection_at(post, t); } });
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}

/// Clearing one present 1G entry and replacing one thread's progress removes that VA from the owning process's 1G user mapping and changes only that thread's progress.
pub proof fn kernel_pagetable_1g_present_cleared_and_progress_changed_implies_u_step(pre: &KernelK, post: &KernelK, pagetable: RwLockPageTableRoot, va: VAddr, thrd_ptr: RwLockThreadPtr)
    requires
        process_pagetable_wf(pre.prc_mp, pre.pt_mp),
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        pre.pt_mp.dom().contains(pagetable),
        *post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, thrd_mp: post.thrd_mp, ..*pre }),
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable),
        post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable)),
        post.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread(),
        post.pt_mp.spec_index(pagetable).view().proc_ptr == pre.pt_mp.spec_index(pagetable).view().proc_ptr,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_1g().dom().contains(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_1g()[va].present,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_1g().insert(va, MapEntry { present: false, ..whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_1g()[va] }),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).lower.pagetable_window_locks == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.pagetable_window_locks,
        pre.thrd_mp.dom().contains(thrd_ptr),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..pre.thrd_mp.spec_index(thrd_ptr).view() }),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() == pre.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        post.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
        !pre.prc_mp.spec_index(pre.pt_mp.spec_index(pagetable).view().proc_ptr).view().zombie,
    ensures
        ({
            let before = kernel_k_to_kernel_u(*pre);
            let process = pre.pt_mp.spec_index(pagetable).view().proc_ptr;
            &&& before.process_map.dom().contains(process)
            &&& before.process_map[process].pagetable is Some
            &&& before.process_map[process].pagetable->Some_0.mapping_1g.dom().contains(va)
            &&& before.thread_map.dom().contains(thrd_ptr)
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                process_map: before.process_map.insert(process, ProcessU {
                    pagetable: Some(PageTableU { mapping_1g: before.process_map[process].pagetable->Some_0.mapping_1g.remove(va), ..before.process_map[process].pagetable->Some_0 }),
                    ..before.process_map[process]
                }),
                thread_map: before.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(), ..before.thread_map[thrd_ptr] }),
                ..before
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post); reveal(process_pagetable_wf);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    let process = pre.pt_mp.spec_index(pagetable).view().proc_ptr;
    if pre.prc_mp.dom().contains(process) { kernel_process_projection_at(pre, process); } if post.prc_mp.dom().contains(process) { kernel_process_projection_at(post, process); }
    if pre.thrd_mp.dom().contains(thrd_ptr) { kernel_thread_projection_at(pre, thrd_ptr); }
    assert_maps_equal!(after.process_map[process].pagetable->Some_0.mapping_1g, before.process_map[process].pagetable->Some_0.mapping_1g.remove(va), a => {});
    assert_maps_equal!(after.process_map, before.process_map.insert(process, ProcessU {
        pagetable: Some(PageTableU { mapping_1g: before.process_map[process].pagetable->Some_0.mapping_1g.remove(va), ..before.process_map[process].pagetable->Some_0 }),
        ..before.process_map[process]
    }), p => { if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); } });
    assert_maps_equal!(after.thread_map, before.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(), ..before.thread_map[thrd_ptr] }), t => {
        if pre.thrd_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thrd_mp.dom().contains(t) { kernel_thread_projection_at(post, t); }
    });
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_container_maps_unchanged_implies_u_container_map(pre, post);
    kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}

/// Hiding L3 entries of a pagetable that link L2 pages without a resolving leaf, and replacing one thread's progress, drops the windows `removed` from the owning process's user window locks and changes only that thread's progress.
pub proof fn kernel_pagetable_l3_hidden_and_progress_changed_implies_u_step(pre: &KernelK, post: &KernelK, pagetable: RwLockPageTableRoot, removed: Set<WindowVa>, thrd_ptr: RwLockThreadPtr)
    requires
        process_pagetable_wf(pre.prc_mp, pre.pt_mp),
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        pre.pt_mp.dom().contains(pagetable),
        *post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, thrd_mp: post.thrd_mp, ..*pre }),
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable),
        post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable)),
        post.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread(),
        post.pt_mp.spec_index(pagetable).view().proc_ptr == pre.pt_mp.spec_index(pagetable).view().proc_ptr,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_1g(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).lower.pagetable_window_locks == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.pagetable_window_locks.remove_keys(removed),
        pre.thrd_mp.dom().contains(thrd_ptr),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..pre.thrd_mp.spec_index(thrd_ptr).view() }),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() == pre.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        post.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
        !pre.prc_mp.spec_index(pre.pt_mp.spec_index(pagetable).view().proc_ptr).view().zombie,
    ensures
        ({
            let before = kernel_k_to_kernel_u(*pre);
            let process = pre.pt_mp.spec_index(pagetable).view().proc_ptr;
            &&& before.process_map.dom().contains(process)
            &&& before.process_map[process].pagetable is Some
            &&& before.thread_map.dom().contains(thrd_ptr)
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                process_map: before.process_map.insert(process, ProcessU {
                    pagetable: Some(PageTableU {
                        pagetable_window_locks: before.process_map[process].pagetable->Some_0.pagetable_window_locks.remove_keys(removed), ..before.process_map[process].pagetable->Some_0
                    }),
                    ..before.process_map[process]
                }),
                thread_map: before.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(), ..before.thread_map[thrd_ptr] }),
                ..before
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post); reveal(process_pagetable_wf);
    let before = kernel_k_to_kernel_u(*pre);
    let after = kernel_k_to_kernel_u(*post);
    let process = pre.pt_mp.spec_index(pagetable).view().proc_ptr;
    if pre.prc_mp.dom().contains(process) { kernel_process_projection_at(pre, process); } if post.prc_mp.dom().contains(process) { kernel_process_projection_at(post, process); }
    if pre.thrd_mp.dom().contains(thrd_ptr) { kernel_thread_projection_at(pre, thrd_ptr); }
    assert_maps_equal!(after.process_map, before.process_map.insert(process, ProcessU {
        pagetable: Some(PageTableU {
            pagetable_window_locks: before.process_map[process].pagetable->Some_0.pagetable_window_locks.remove_keys(removed), ..before.process_map[process].pagetable->Some_0
        }),
        ..before.process_map[process]
    }), p => { if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); } });
    assert_maps_equal!(after.thread_map, before.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(), ..before.thread_map[thrd_ptr] }), t => {
        if pre.thrd_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thrd_mp.dom().contains(t) { kernel_thread_projection_at(post, t); }
    });
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_container_maps_unchanged_implies_u_container_map(pre, post);
    kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}
} // verus!
