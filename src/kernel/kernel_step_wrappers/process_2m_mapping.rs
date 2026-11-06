use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal};
use crate::*;

verus! {
pub proof fn kernel_process_2m_mapping_changed_implies_u_neq(pre: &KernelK, post: &KernelK, prc_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires kernel_process_2m_mapping_changed(pre, post, prc_ptr, pagetable_ptr, va),
    ensures kernel_k_to_kernel_u(*pre) != kernel_k_to_kernel_u(*post),
{
    assert(kernel_k_to_kernel_u(*pre).process_map.spec_index(prc_ptr).pagetable.unwrap().mapping_2m.dom().contains(va) != kernel_k_to_kernel_u(*post).process_map.spec_index(prc_ptr).pagetable.unwrap().mapping_2m.dom().contains(va)) by {
        reveal(kernel_process_2m_mapping_changed); reveal(kernel_k_to_kernel_u);
    };
}

impl KernelK {
    /// Records the section that changed the 2M leaf `va` of `prc_ptr`'s pagetable when the tables are held in either mode: the
    /// changed table is write-held or its window around `va` is held. Only the held windows of the stable table keep their 4K
    /// mappings, and this cpu keeps its hold on the stable table: the same write hold, or a read hold among readers that
    /// other cpus may change across the boundary.
    pub proof fn kernel_step_boundary_process_2m_mapping_changed_windowed(
        tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, prc_ptr: RwLockProcessPtr,
        pagetable_ptr: RwLockPageTableRoot, va: VAddr, stable_prc_ptr: RwLockProcessPtr, stable_pagetable_ptr: RwLockPageTableRoot,
        stable_thrd_ptr: RwLockThreadPtr, stable_owner_thrd_ptr: RwLockThreadPtr,
    )
        requires
            old(self).inv(),
            kernel_process_2m_mapping_changed(&old(steps).snapshot_k(), old(self), prc_ptr, pagetable_ptr, va),
            old(self).thrd_mp.dom().contains(stable_thrd_ptr),
            old(lctx).kernel_view_locking_state() is Release,
            old(self).prc_mp.dom().contains(stable_prc_ptr),
            old(self).prc_mp.spec_index(stable_prc_ptr).view().pagetable == stable_pagetable_ptr,
            old(lctx).pagetable_lock_map().dom().contains(stable_pagetable_ptr),
            old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write) || old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, window_of(va))),
            old(lctx).thread_lock_map().dom().contains(stable_thrd_ptr),
            old(lctx).thread_lock_map().dom().contains(stable_owner_thrd_ptr),
            old(self).thrd_mp.dom().contains(stable_owner_thrd_ptr),
            old(self).thrd_mp.spec_index(stable_owner_thrd_ptr).view().owning_proc == stable_prc_ptr,
            !thread_is_dangling(old(self).thrd_mp.spec_index(stable_owner_thrd_ptr)),
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
            final(steps).view().last().new_u.process_map.dom().contains(stable_prc_ptr) && final(steps).view().last().new_u.process_map.spec_index(stable_prc_ptr).pagetable is Some,
            kernel_k_to_kernel_u(*final(self)).process_map.dom().contains(stable_prc_ptr) && kernel_k_to_kernel_u(*final(self)).process_map.spec_index(stable_prc_ptr).pagetable is Some,
            ({
                let recorded = final(steps).view().last().new_u.process_map.spec_index(stable_prc_ptr).pagetable->Some_0.lock_state;
                let current = kernel_k_to_kernel_u(*final(self)).process_map.spec_index(stable_prc_ptr).pagetable->Some_0.lock_state;
                if typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), stable_pagetable_ptr, TypedLockMode::Write) {
                    &&& recorded == (LockStateU::WriteLocked { writer: old(lctx).cpu_id() })
                    &&& current == (LockStateU::WriteLocked { writer: old(lctx).cpu_id() })
                } else {
                    &&& recorded.read_held_by(old(lctx).cpu_id())
                    &&& current.read_held_by(old(lctx).cpu_id())
                }
            }),
    {
        use_type_invariant(&*steps);
        assert(old(self).prc_mp.dom().contains(prc_ptr) && !old(self).prc_mp.spec_index(prc_ptr).view().zombie && old(self).prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr) by { reveal(kernel_process_2m_mapping_changed); };
        kernel_process_2m_mapping_changed_implies_u_neq(&steps.snapshot_k(), &*self, prc_ptr, pagetable_ptr, va);
        assert(!self.prc_mp.spec_index(stable_prc_ptr).view().zombie) by { process_thread_wf_thread_at(self.prc_mp, self.thrd_mp, stable_owner_thrd_ptr); };
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        reveal(LockedMap::typed_lock_map_aligned);
        assert(!self.prc_mp.spec_index(stable_prc_ptr).view().zombie) by { process_thread_wf_thread_at(self.prc_mp, self.thrd_mp, stable_owner_thrd_ptr); };
        if typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write) {
            old(self).pt_mp.typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
            pagetable_lower_backup_wf_at(old(self).pt_mp, old(self).pt_lower.view(), pagetable_ptr); pagetable_lower_backup_wf_at(self.pt_mp, self.pt_lower.view(), pagetable_ptr);
        }
        if typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), stable_pagetable_ptr, TypedLockMode::Write) {
            old(self).pt_mp.typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), stable_pagetable_ptr);
        } else {
            old(self).pt_mp.typed_lock_map_aligned_read_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), stable_pagetable_ptr);
        }
        reveal(process_pagetable_wf); reveal(process_iommu_table_wf);
        kernel_process_projection_at(old(self), stable_prc_ptr); kernel_process_projection_at(&*self, stable_prc_ptr);
        kernel_held_pagetable_windows_unchanged_implies_u_window_mappings_eq(old(self), &*self, old(lctx), stable_prc_ptr, stable_pagetable_ptr);
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*self);
    }
}

/// The 2M frame at `addr`, whose head page is `Owned2m`, shares no frame with any 2M mapping, overlaps no 4K mapping, and
/// overlaps no IOMMU 4K mapping in the projection of `k`.
pub proof fn kernel_owned_2m_page_implies_u_mappings_outside_its_frame(k: KernelK, addr: PagePtr)
    requires
        k.inv(),
        page_ptr_valid(addr),
        k.pg_arr.spec_index(page_ptr2page_index(addr)).view().view().state is Owned2m,
    ensures
        forall|p: RwLockProcessPtr, v: VAddr| #![trigger kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_2m[v]]
            kernel_k_to_kernel_u(k).process_map.dom().contains(p) && kernel_k_to_kernel_u(k).process_map[p].pagetable is Some && kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_2m.dom().contains(v)
            ==> kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_2m[v].addr != addr,
        forall|p: RwLockProcessPtr, v: VAddr| #![trigger kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_4k[v]]
            kernel_k_to_kernel_u(k).process_map.dom().contains(p) && kernel_k_to_kernel_u(k).process_map[p].pagetable is Some && kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_4k.dom().contains(v)
            ==> !(addr <= kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_4k[v].addr < addr + 0x200000),
        forall|p: RwLockProcessPtr, v: VAddr| #![trigger kernel_k_to_kernel_u(k).process_map[p].iommu_table->Some_0.mapping_4k[v]]
            kernel_k_to_kernel_u(k).process_map.dom().contains(p) && kernel_k_to_kernel_u(k).process_map[p].iommu_table is Some && kernel_k_to_kernel_u(k).process_map[p].iommu_table->Some_0.mapping_4k.dom().contains(v)
            ==> !(addr <= kernel_k_to_kernel_u(k).process_map[p].iommu_table->Some_0.mapping_4k[v].addr < addr + 0x200000),
{
    broadcast use kernel_owned_2m_page_implies_u_2m_mapping_frame_differs_at, kernel_owned_2m_page_implies_u_4k_mapping_outside_its_frame_at,
        kernel_owned_2m_page_implies_u_iommu_4k_mapping_outside_its_frame_at;
}

/// Point form of the 2M clause of `kernel_owned_2m_page_implies_u_mappings_outside_its_frame` at one process and VA.
broadcast proof fn kernel_owned_2m_page_implies_u_2m_mapping_frame_differs_at(k: KernelK, addr: PagePtr, p: RwLockProcessPtr, v: VAddr)
    requires
        k.inv(),
        page_ptr_valid(addr),
        k.pg_arr.spec_index(page_ptr2page_index(addr)).view().view().state is Owned2m,
    ensures
        #![trigger kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_2m[v], k.pg_arr.spec_index(page_ptr2page_index(addr))]
        kernel_k_to_kernel_u(k).process_map.dom().contains(p) && kernel_k_to_kernel_u(k).process_map[p].pagetable is Some && kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_2m.dom().contains(v)
            ==> kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_2m[v].addr != addr,
{
    kernel_u_domains_projection(&k);
    if k.prc_mp.dom().contains(p) {
        kernel_process_projection_at(&k, p); process_pagetable_wf_process_at(k.prc_mp, k.pt_mp, p);
        reveal(mapped_2m_page_pagetable_wf);
    }
}

/// Point form of the 4K clause of `kernel_owned_2m_page_implies_u_mappings_outside_its_frame` at one process and VA: a 4K
/// mapping names a `Mapped4k` page, while the pages of the frame are its `Owned2m` head and `Merged2m` tails.
broadcast proof fn kernel_owned_2m_page_implies_u_4k_mapping_outside_its_frame_at(k: KernelK, addr: PagePtr, p: RwLockProcessPtr, v: VAddr)
    requires
        k.inv(),
        page_ptr_valid(addr),
        k.pg_arr.spec_index(page_ptr2page_index(addr)).view().view().state is Owned2m,
    ensures
        #![trigger kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_4k[v], k.pg_arr.spec_index(page_ptr2page_index(addr))]
        kernel_k_to_kernel_u(k).process_map.dom().contains(p) && kernel_k_to_kernel_u(k).process_map[p].pagetable is Some && kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_4k.dom().contains(v)
            ==> !(addr <= kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_4k[v].addr < addr + 0x200000),
{
    kernel_u_domains_projection(&k);
    if k.prc_mp.dom().contains(p) {
        let pt = k.prc_mp.spec_index(p).view().pagetable;
        let head = page_ptr2page_index(addr);
        kernel_process_projection_at(&k, p); process_pagetable_wf_process_at(k.prc_mp, k.pt_mp, p);
        mapped_4k_page_pagetable_wf_pagetable_at(k.pt_mp, k.pt_lower.view(), k.pg_arr, pt, v);
        hugepage_2m_wf_head_at(k.pg_arr, head);
        let a = whole_pagetable(k.pt_mp, k.pt_lower.view(), pt).mapping_4k().spec_index(v).addr;
        let idx = page_ptr2page_index(a);
        if addr <= a < addr + 0x200000 {
            assert(head <= idx < head + 512) by (nonlinear_arith) requires addr % 0x1000 == 0, head == addr / 4096, idx == a / 4096, addr <= a < addr + 0x200000;
            hugepage_2m_wf_tail_forward_at(k.pg_arr, head, idx);
        }
    }
}

/// Point form of the IOMMU clause of `kernel_owned_2m_page_implies_u_mappings_outside_its_frame` at one process and IOVA.
broadcast proof fn kernel_owned_2m_page_implies_u_iommu_4k_mapping_outside_its_frame_at(k: KernelK, addr: PagePtr, p: RwLockProcessPtr, v: VAddr)
    requires
        k.inv(),
        page_ptr_valid(addr),
        k.pg_arr.spec_index(page_ptr2page_index(addr)).view().view().state is Owned2m,
    ensures
        #![trigger kernel_k_to_kernel_u(k).process_map[p].iommu_table->Some_0.mapping_4k[v], k.pg_arr.spec_index(page_ptr2page_index(addr))]
        kernel_k_to_kernel_u(k).process_map.dom().contains(p) && kernel_k_to_kernel_u(k).process_map[p].iommu_table is Some && kernel_k_to_kernel_u(k).process_map[p].iommu_table->Some_0.mapping_4k.dom().contains(v)
            ==> !(addr <= kernel_k_to_kernel_u(k).process_map[p].iommu_table->Some_0.mapping_4k[v].addr < addr + 0x200000),
{
    kernel_u_domains_projection(&k);
    if k.prc_mp.dom().contains(p) { kernel_process_projection_at(&k, p); }
    if k.prc_mp.dom().contains(p) && k.prc_mp.spec_index(p).view().iommu_table is Some {
        let it = k.prc_mp.spec_index(p).view().iommu_table->Some_0;
        let head = page_ptr2page_index(addr);
        process_iommu_table_wf_process_at(k.prc_mp, k.it_mp, p);
        if k.it_mp.spec_index(it).view().mapping_4k().dom().contains(v) {
            page_iommu_table_wf_table_at(k.ctn_mp, k.prc_mp, k.it_mp, k.pg_arr, it, v);
            hugepage_2m_wf_head_at(k.pg_arr, head);
            let a = k.it_mp.spec_index(it).view().mapping_4k().spec_index(v).addr;
            let idx = page_ptr2page_index(a);
            if addr <= a < addr + 0x200000 {
                assert(head <= idx < head + 512 && idx < NUM_PAGES) by (nonlinear_arith)
                    requires addr % 0x1000 == 0, head == addr / 4096, idx == a / 4096, addr <= a < addr + 0x200000, head % 512 == 0, head < NUM_PAGES, NUM_PAGES % 512 == 0;
                hugepage_2m_wf_tail_forward_at(k.pg_arr, head, idx);
            }
        }
    }
}

/// The `Owned4k` page at `addr` lies in no 2M frame that a pagetable maps in the projection of `k`.
pub proof fn kernel_owned_4k_page_implies_u_outside_2m_mapping_frames(k: KernelK, addr: PagePtr)
    requires
        k.inv(),
        k.pg_arr.spec_index(page_ptr2page_index(addr)).view().view().state is Owned4k,
    ensures
        forall|p: RwLockProcessPtr, v: VAddr| #![trigger kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_2m[v]]
            kernel_k_to_kernel_u(k).process_map.dom().contains(p) && kernel_k_to_kernel_u(k).process_map[p].pagetable is Some && kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_2m.dom().contains(v)
            ==> !(kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_2m[v].addr <= addr < kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_2m[v].addr + 0x200000),
{ broadcast use kernel_owned_4k_page_implies_u_outside_2m_mapping_frame_at; }

/// Point form of `kernel_owned_4k_page_implies_u_outside_2m_mapping_frames` at one process and VA: a 2M mapping names a
/// 2M-aligned `Mapped2m` head whose frame's other pages are `Merged2m` tails.
broadcast proof fn kernel_owned_4k_page_implies_u_outside_2m_mapping_frame_at(k: KernelK, addr: PagePtr, p: RwLockProcessPtr, v: VAddr)
    requires
        k.inv(),
        k.pg_arr.spec_index(page_ptr2page_index(addr)).view().view().state is Owned4k,
    ensures
        #![trigger kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_2m[v], k.pg_arr.spec_index(page_ptr2page_index(addr))]
        kernel_k_to_kernel_u(k).process_map.dom().contains(p) && kernel_k_to_kernel_u(k).process_map[p].pagetable is Some && kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_2m.dom().contains(v)
            ==> !(kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_2m[v].addr <= addr < kernel_k_to_kernel_u(k).process_map[p].pagetable->Some_0.mapping_2m[v].addr + 0x200000),
{
    kernel_u_domains_projection(&k);
    if k.prc_mp.dom().contains(p) {
        let pt = k.prc_mp.spec_index(p).view().pagetable;
        kernel_process_projection_at(&k, p); process_pagetable_wf_process_at(k.prc_mp, k.pt_mp, p);
        pagetable_lower_wf_at(k.pt_mp, k.pt_lower.view(), pt);
        if whole_pagetable(k.pt_mp, k.pt_lower.view(), pt).mapping_2m().contains_key(v) {
            let m = whole_pagetable(k.pt_mp, k.pt_lower.view(), pt).mapping_2m().spec_index(v).addr;
            let head = page_ptr2page_index(m);
            let idx = page_ptr2page_index(addr);
            assert(k.pg_arr.spec_index(head).view().view().state == PageState::Mapped2m) by { reveal(mapped_2m_page_pagetable_wf); };
            if m <= addr < m + 0x200000 {
                assert(head <= idx < head + 512 && index_valid(NUM_PAGES, head) && index_valid(NUM_PAGES, idx)) by (nonlinear_arith)
                    requires m % 0x200000 == 0, m / 4096 < NUM_PAGES, head == m / 4096, idx == addr / 4096, m <= addr < m + 0x200000, NUM_PAGES % 512 == 0;
                if idx != head { hugepage_2m_wf_tail_forward_at(k.pg_arr, head, idx); }
            }
        }
    }
}

/// Publishing a present 2M leaf at `va` in the read-held pagetable of the cpu's current process from an `Owned2m` page, with
/// the thread's 2M quota, temporary 2M cache, and progress replaced, adds that leaf to the process's 2M user mapping and changes
/// only that thread's 2M quota and progress. The window of `va` links no L1 table under a directory L3 entry, so it holds no 4K or
/// 1G leaf, and the frame overlaps no mapping.
pub proof fn kernel_thread_quota_2m_progress_and_2m_mapping_added_pagetable_rlocked_implies_u_step(pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(post, lctx),
        pre.thrd_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        pre.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        *post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, pg_arr: post.pg_arr, thrd_mp: post.thrd_mp, ..*pre }),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).view() == (Thread {
            quota_2m: post.thrd_mp.spec_index(thrd_ptr).view().quota_2m,
            temp_alloc_cache_2m: post.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_2m,
            syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress,
            ..pre.thrd_mp.spec_index(thrd_ptr).view()
        }),
        post.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        pre.prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr,
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        post.pt_mp.spec_index(pagetable_ptr).locking_thread() == pre.pt_mp.spec_index(pagetable_ptr).locking_thread(),
        post.pt_lower.view() == pre.pt_lower.view().insert(pagetable_ptr, post.pt_lower.view().spec_index(pagetable_ptr)),
        !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m().dom().contains(va),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m().insert(va, whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_2m().spec_index(va)),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_2m().spec_index(va).present,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_1g(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks,
        spec_va_2m_valid(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).window_view(window_of(va)).l1_table is None,
        page_ptr_valid(whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_2m().spec_index(va).addr),
        pre.pg_arr.spec_index(page_ptr2page_index(whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_2m().spec_index(va).addr)).view().view().state is Owned2m,
    ensures
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let thread = pre.thrd_mp.spec_index(thrd_ptr).view();
            let process = pre_u.process_map.spec_index(prc_ptr);
            let idx = spec_va2index(va);
            let addr = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_2m().spec_index(va).addr;
            &&& pre_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& pre_u.cpu_array[cpu_id as int].current_thread == pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread
            &&& pre_u.thread_map.dom().contains(thrd_ptr)
            &&& pre_u.thread_map.spec_index(thrd_ptr).lock_state is WriteLocked
            &&& pre_u.thread_map.spec_index(thrd_ptr).owning_container == thread.owning_container
            &&& pre_u.thread_map.spec_index(thrd_ptr).owning_proc == thread.owning_proc
            &&& pre_u.thread_map.spec_index(thrd_ptr).quota_2m == thread.quota_2m
            &&& pre_u.thread_map.spec_index(thrd_ptr).syscall_progress == thread.syscall_progress.view()
            &&& pre_u.process_map.dom().contains(prc_ptr)
            &&& process.pagetable is Some
            &&& process.pagetable->Some_0.lock_state is ReadLocked
            &&& !process.pagetable->Some_0.mapping_2m.dom().contains(va)
            &&& !process.pagetable->Some_0.mapping_1g.dom().contains(spec_index2va((idx.0, idx.1, 0, 0)))
            &&& forall|l1i: L1Index| #![trigger process.pagetable->Some_0.mapping_4k.dom().contains(spec_index2va((idx.0, idx.1, idx.2, l1i)))]
                pei_valid(l1i) ==> !process.pagetable->Some_0.mapping_4k.dom().contains(spec_index2va((idx.0, idx.1, idx.2, l1i)))
            &&& forall|p: RwLockProcessPtr, v: VAddr| #![trigger pre_u.process_map[p].pagetable->Some_0.mapping_2m[v]]
                pre_u.process_map.dom().contains(p) && pre_u.process_map[p].pagetable is Some && pre_u.process_map[p].pagetable->Some_0.mapping_2m.dom().contains(v)
                ==> pre_u.process_map[p].pagetable->Some_0.mapping_2m[v].addr != addr
            &&& forall|p: RwLockProcessPtr, v: VAddr| #![trigger pre_u.process_map[p].pagetable->Some_0.mapping_4k[v]]
                pre_u.process_map.dom().contains(p) && pre_u.process_map[p].pagetable is Some && pre_u.process_map[p].pagetable->Some_0.mapping_4k.dom().contains(v)
                ==> !(addr <= pre_u.process_map[p].pagetable->Some_0.mapping_4k[v].addr < addr + 0x200000)
            &&& forall|p: RwLockProcessPtr, v: VAddr| #![trigger pre_u.process_map[p].iommu_table->Some_0.mapping_4k[v]]
                pre_u.process_map.dom().contains(p) && pre_u.process_map[p].iommu_table is Some && pre_u.process_map[p].iommu_table->Some_0.mapping_4k.dom().contains(v)
                ==> !(addr <= pre_u.process_map[p].iommu_table->Some_0.mapping_4k[v].addr < addr + 0x200000)
        }),
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let process = pre_u.process_map.spec_index(prc_ptr);
            let pagetable = process.pagetable->Some_0;
            let entry = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_2m().spec_index(va);
            kernel_k_to_kernel_u(*post) == (KernelU {
                thread_map: pre_u.thread_map.insert(thrd_ptr, ThreadU {
                    quota_2m: post.thrd_mp.spec_index(thrd_ptr).view().quota_2m,
                    syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(),
                    ..pre_u.thread_map.spec_index(thrd_ptr)
                }),
                process_map: pre_u.process_map.insert(prc_ptr, ProcessU {
                    pagetable: Some(PageTableU { mapping_2m: pagetable.mapping_2m.insert(va, entry), ..pagetable }),
                    ..process
                }),
                ..pre_u
            })
        }),
{
    let table = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr);
    let idx = spec_va2index(va);
    pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr);
    spec_va_2m_valid_index_roundtrip(va);
    table.higher.wf_l4_at(idx.0);
    table.l3_links_l2_wf_at(table.spec_resolve_mapping_l4(idx.0)->0.addr, idx.1);
    table.higher.spec_resolve_mapping_l3_some_implies_spec_held_l3_eq(idx.0, idx.1);
    table.wf_l2_at(table.window_l2_page(idx.0, idx.1), idx.2);
    table.higher.wf_mapping_1g_at(idx.0, idx.1);
    reveal(WholePageTable::wf_mapping_4k);
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let process = pre_u.process_map.spec_index(prc_ptr);
    let pagetable = process.pagetable->Some_0;
    let entry = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_2m().spec_index(va);
    let new_pagetable = PageTableU { mapping_2m: pagetable.mapping_2m.insert(va, entry), ..pagetable };
    pre.thrd_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thrd_ptr);
    post.thrd_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thrd_ptr);
    pre.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
    post.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
    kernel_cpu_projection_at(post, cpu_id);
    if pre.prc_mp.dom().contains(prc_ptr) { kernel_process_projection_at(pre, prc_ptr); } if post.prc_mp.dom().contains(prc_ptr) { kernel_process_projection_at(post, prc_ptr); }
    if pre.thrd_mp.dom().contains(thrd_ptr) { kernel_thread_projection_at(pre, thrd_ptr); } if post.thrd_mp.dom().contains(thrd_ptr) { kernel_thread_projection_at(post, thrd_ptr); }
    assert(pre.cpu_arr.spec_index(cpu_id).view().wlocked_by_thread(lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); };
    assert(pre.prc_mp.dom().contains(prc_ptr) && !pre.prc_mp.spec_index(prc_ptr).view().zombie && pre.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr) by { reveal(process_cpu_wf); reveal(process_pagetable_wf); };
    assert(pagetable == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).user_view(pre.pt_mp.spec_index(pagetable_ptr).lock_state_u()));
    assert(post_u.process_map.spec_index(prc_ptr).pagetable == Some(new_pagetable)) by {
        assert_maps_equal!(whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).user_view(post.pt_mp.spec_index(pagetable_ptr).lock_state_u()).mapping_2m, new_pagetable.mapping_2m);
    };
    kernel_owned_2m_page_implies_u_mappings_outside_its_frame(*pre, entry.addr);
    kernel_container_maps_unchanged_implies_u_container_map(pre, post);
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(prc_ptr, ProcessU { pagetable: Some(new_pagetable), ..process }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); } reveal(process_pagetable_wf);
    });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thrd_ptr, ThreadU {
        quota_2m: post.thrd_mp.spec_index(thrd_ptr).view().quota_2m,
        syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(),
        ..pre_u.thread_map.spec_index(thrd_ptr)
    }), t => { if pre.thrd_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thrd_mp.dom().contains(t) { kernel_thread_projection_at(post, t); } });
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}

/// Clearing one present 2M entry and replacing one thread's progress removes that VA from the owning process's 2M user mapping
/// and changes only that thread's progress.
pub proof fn kernel_pagetable_2m_present_cleared_and_progress_changed_implies_u_step(pre: &KernelK, post: &KernelK, pagetable: RwLockPageTableRoot, va: VAddr, thrd_ptr: RwLockThreadPtr)
    requires
        process_pagetable_wf(pre.prc_mp, pre.pt_mp),
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        pre.pt_mp.dom().contains(pagetable),
        *post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, thrd_mp: post.thrd_mp, ..*pre }),
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable),
        post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable)),
        post.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread(),
        post.pt_mp.spec_index(pagetable).view().proc_ptr == pre.pt_mp.spec_index(pagetable).view().proc_ptr,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().dom().contains(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m()[va].present,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().insert(va, MapEntry { present: false, ..whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m()[va] }),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_1g(),
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
            &&& before.process_map[process].pagetable->Some_0.mapping_2m.dom().contains(va)
            &&& before.thread_map.dom().contains(thrd_ptr)
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                process_map: before.process_map.insert(process, ProcessU {
                    pagetable: Some(PageTableU { mapping_2m: before.process_map[process].pagetable->Some_0.mapping_2m.remove(va), ..before.process_map[process].pagetable->Some_0 }),
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
    assert_maps_equal!(after.process_map[process].pagetable->Some_0.mapping_2m, before.process_map[process].pagetable->Some_0.mapping_2m.remove(va), a => {});
    assert_maps_equal!(after.process_map, before.process_map.insert(process, ProcessU {
        pagetable: Some(PageTableU { mapping_2m: before.process_map[process].pagetable->Some_0.mapping_2m.remove(va), ..before.process_map[process].pagetable->Some_0 }),
        ..before.process_map[process]
    }), p => { if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); } });
    assert_maps_equal!(after.thread_map, before.thread_map.insert(thrd_ptr, ThreadU { syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(), ..before.thread_map[thrd_ptr] }), t => {
        if pre.thrd_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thrd_mp.dom().contains(t) { kernel_thread_projection_at(post, t); }
    });
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_container_maps_unchanged_implies_u_container_map(pre, post);
    kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}
} // verus!
