use vstd::prelude::*;
use crate::*;

verus! {
/// Under the kernel invariant, what CPU `cpu_id` may hold under `pcid` in K right after a per-address flush it may also
/// hold in the user projection.
pub proof fn kernel_cpu_tlb_va_range_flushed_implies_u_va_range_flushed(krnl: &KernelK, cpu_id: CpuId, pcid: Pcid, va: VAddr, count: usize, stride_2m: bool, old_tlb: SingleTLB, tlb: SingleTLB,
    cache: PagingStructureCache)
    requires
        krnl.inv(),
        index_valid(NUM_CPUS, cpu_id),
        pcid != KERNEL_DEFAULT_PCID,
        cpu_tlb_va_range_flushed(*krnl, cpu_id, pcid, va, count, stride_2m, old_tlb, tlb, cache),
    ensures
        cpu_tlb_va_range_flushed_u(kernel_k_to_kernel_u(*krnl), cpu_id, pcid, va, count, stride_2m, old_tlb, tlb),
{
    let cpu = krnl.cpu_arr.spec_index(cpu_id).view().view().view();
    kernel_cpu_user_projection_at(krnl, cpu_id);
    if cpu.current_pcid == pcid && cpu.current_pagetable is Some {
        cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), cpu_id); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id);
        process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, cpu.current_process->Some_0); kernel_process_user_projection_at(krnl, cpu.current_process->Some_0);
        pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), cpu.current_pagetable->Some_0); reveal(WholePageTable::wf_mapping_4k); reveal(WholePageTable::wf_mapping_2m);
        broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip, WholePageTable::spec_resolve_mapping_4k_l1_some_implies_spec_held_4k_l1_eq, WholePageTable::spec_resolve_mapping_2m_l2_some_implies_spec_held_2m_l2_eq;
    }
    assert(kernel_k_to_kernel_u(*krnl) == kernel_k_user_projection(*krnl)) by { reveal(kernel_k_to_kernel_u); };
}

/// A section that changes only the TLB projection, by a per-address flush of the entry of cpu `cpu_id` for `pcid` in K, is
/// that flush in the projection.
pub proof fn kernel_cpu_tlb_va_flushed_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId, pcid: Pcid, va: VAddr, count: usize, stride_2m: bool)
    requires
        post.inv(),
        index_valid(NUM_CPUS, cpu_id),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        kernel_k_to_kernel_u(*post) == (KernelU { cpu_tlb: post.cpu_tlb.view(), ..kernel_k_to_kernel_u(*pre) }),
        post.cpu_tlb.view() == pre.cpu_tlb.view().insert((cpu_id, pcid), post.cpu_tlb.spec_index((cpu_id, pcid))),
        cpu_tlb_va_range_flushed(*post, cpu_id, pcid, va, count, stride_2m, pre.cpu_tlb.spec_index((cpu_id, pcid)), post.cpu_tlb.spec_index((cpu_id, pcid)), post.cpu_tlb.structure_cache((cpu_id, pcid))),
    ensures
        kernel_u_cpu_tlb_va_flushed(kernel_k_to_kernel_u(*pre), kernel_k_to_kernel_u(*post), cpu_id, pcid, va, count, stride_2m),
{
    reveal(kernel_u_cpu_tlb_va_flushed); kernel_u_domains_projection(pre);
    kernel_cpu_tlb_va_range_flushed_implies_u_va_range_flushed(post, cpu_id, pcid, va, count, stride_2m, pre.cpu_tlb.spec_index((cpu_id, pcid)), post.cpu_tlb.spec_index((cpu_id, pcid)),
        post.cpu_tlb.structure_cache((cpu_id, pcid)));
}

impl KernelK {
    /// The per-address twin of `kernel_step_boundary_cpu_tlb_updated_cpu_set_rlocked`: the recorded step adds the running
    /// cpu to the readers of the cpu set of the container `ctn_ptr` in the projection and, at most, flushes the `count`
    /// addresses, 4K or 2M apart by `stride_2m`, from `va` in the TLB entry of cpu `cpu_id` for `pcid`.
    pub proof fn kernel_step_boundary_cpu_tlb_va_flushed_cpu_set_rlocked(
        tracked &mut self, tracked lctx: &mut LocalContext, tracked steps: &mut KernelSteps, cpu_id: CpuId, pcid: Pcid, va: VAddr, count: usize, stride_2m: bool, flushed: bool,
        ctn_ptr: RwLockContainerPtr,
    )
        requires
            *old(self) == (KernelK {
                cpu_arr: old(self).cpu_arr, cpu_tlb: old(self).cpu_tlb, pcid_needflush: old(self).pcid_needflush, pt_mp: old(self).pt_mp, pt_lower: old(self).pt_lower,
                cpu_set_mp: old(self).cpu_set_mp, ..old(steps).snapshot_k()
            }),
            forall|cpu: CpuId| #![trigger old(self).cpu_arr.spec_index(cpu)] index_valid(NUM_CPUS, cpu) ==> old(self).cpu_arr.spec_index(cpu).value.locking_thread() == old(steps).snapshot_k().cpu_arr.spec_index(cpu).value.locking_thread(),
            old(self).pt_mp.dom() == old(steps).snapshot_k().pt_mp.dom(),
            forall|pt: RwLockPageTableRoot| #![trigger old(self).pt_mp.spec_index(pt)] old(steps).snapshot_k().pt_mp.dom().contains(pt) ==> {
                &&& old(self).pt_mp.spec_index(pt).locking_thread() == old(steps).snapshot_k().pt_mp.spec_index(pt).locking_thread()
                &&& whole_pagetable(old(self).pt_mp, old(self).pt_lower.view(), pt).mapping_4k() == whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pt).mapping_4k()
                &&& whole_pagetable(old(self).pt_mp, old(self).pt_lower.view(), pt).mapping_2m() == whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pt).mapping_2m()
                &&& whole_pagetable(old(self).pt_mp, old(self).pt_lower.view(), pt).mapping_1g() == whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pt).mapping_1g()
                &&& whole_pagetable(old(self).pt_mp, old(self).pt_lower.view(), pt).lower.pagetable_window_locks == whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pt).lower.pagetable_window_locks
            },
            old(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(self)),
            index_valid(NUM_CPUS, cpu_id),
            pcid_valid(pcid),
            old(self).cpu_tlb.view() == if flushed {
                old(steps).snapshot_k().cpu_tlb.view().insert((cpu_id, pcid), old(self).cpu_tlb.spec_index((cpu_id, pcid)))
            } else { old(steps).snapshot_k().cpu_tlb.view() },
            flushed ==> pcid != KERNEL_DEFAULT_PCID,
            flushed ==> cpu_tlb_va_range_flushed(*old(self), cpu_id, pcid, va, count, stride_2m, old(steps).snapshot_k().cpu_tlb.spec_index((cpu_id, pcid)), old(self).cpu_tlb.spec_index((cpu_id, pcid)),
                old(self).cpu_tlb.structure_cache((cpu_id, pcid))),
            old(self).ctn_mp.dom().contains(ctn_ptr),
            old(self).cpu_set_mp.unchanged_except(&old(steps).snapshot_k().cpu_set_mp, old(self).ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set),
            old(self).cpu_set_mp.spec_index(old(self).ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).being_killed() == old(steps).snapshot_k().cpu_set_mp.spec_index(old(self).ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).being_killed(),
            old(self).cpu_set_mp.spec_index(old(self).ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).lock_state_u() == old(steps).snapshot_k().cpu_set_mp.spec_index(old(self).ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set).lock_state_u().with_reader(old(lctx).cpu_id()),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==> {
                let old_u = final(steps).view()[j].old_u;
                let locked = KernelU { container_map: old_u.container_map.insert(ctn_ptr, ContainerU { cpu_set_lock: old_u.container_map[ctn_ptr].cpu_set_lock.with_reader(old(lctx).cpu_id()), ..old_u.container_map[ctn_ptr] }), ..old_u };
                final(steps).view()[j].new_u == locked || kernel_u_cpu_tlb_va_flushed(locked, final(steps).view()[j].new_u, cpu_id, pcid, va, count, stride_2m)
            },
            old(steps).snapshot_u().container_map.dom().contains(ctn_ptr),
            kernel_k_to_kernel_u(*old(self)) == (KernelU {
                cpu_tlb: old(self).cpu_tlb.view(),
                container_map: old(steps).snapshot_u().container_map.insert(ctn_ptr, ContainerU { cpu_set_lock: old(steps).snapshot_u().container_map[ctn_ptr].cpu_set_lock.with_reader(old(lctx).cpu_id()), ..old(steps).snapshot_u().container_map[ctn_ptr] }),
                ..old(steps).snapshot_u()
            }),
            old(steps).snapshot_u() == kernel_k_to_kernel_u(old(steps).snapshot_k()),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            kernel_step_boundary_framing(*old(self), *final(self), *old(lctx)),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(self))),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(steps).snapshot_u() == kernel_k_to_kernel_u(*final(self)),
            final(steps).snapshot_k() == *final(self),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(self)),
            forall|p: RwLockPageTableRoot| #![trigger old(lctx).pagetable_lock_map().dom().contains(p)] typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), p, TypedLockMode::Write)
                ==> whole_pagetable(final(self).pt_mp, final(self).pt_lower.view(), p) == whole_pagetable(old(self).pt_mp, old(self).pt_lower.view(), p),
    {
        use_type_invariant(&*steps);
        let snap = steps.snapshot_k();
        let mid = KernelK { cpu_set_mp: self.cpu_set_mp, ..snap };
        let locked = KernelU {
            container_map: steps.snapshot_u().container_map.insert(ctn_ptr, ContainerU { cpu_set_lock: steps.snapshot_u().container_map[ctn_ptr].cpu_set_lock.with_reader(lctx.cpu_id()), ..steps.snapshot_u().container_map[ctn_ptr] }),
            ..steps.snapshot_u()
        };
        kernel_cpu_set_lock_mode_changed_implies_u_step(&snap, &mid, ctn_ptr); kernel_container_projection_at(&snap, ctn_ptr);
        assert(kernel_k_to_kernel_u(*self) == (KernelU { cpu_tlb: self.cpu_tlb.view(), ..locked })) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); kernel_cpu_tlb_updated_implies_u_step(&mid, &*self); };
        if flushed { kernel_cpu_tlb_va_flushed_implies_u_step(&mid, &*self, cpu_id, pcid, va, count, stride_2m); } else { kernel_u_domains_projection(&snap); }
        steps.end_kernel_step_raw(&*self, &*lctx);
        self.kernel_step_boundary_raw(lctx, steps);
        reveal(LockedMap::typed_lock_map_aligned);
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*self);
    }
}
}
