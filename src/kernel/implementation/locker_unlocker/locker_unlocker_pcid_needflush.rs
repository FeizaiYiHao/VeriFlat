use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
    pub fn wlock_pcid_needflush(&mut self, cpu_id: CpuId, pcid: Pcid, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).inv(),
            index_valid(NUM_CPUS, cpu_id),
            pcid_valid(pcid),
            index_valid(NUM_CPUS, old(lctx).cpu_id()),
            old(lctx).kernel_view_locking_state() is Acquire,
            !typed_lock_map_contains_mode(old(lctx).pcid_needflush_lock_map(), (cpu_id, pcid), TypedLockMode::Write),
            old(lctx).held_lock_majors_lt(PCID_NEEDFLUSH_LOCK_MAJOR)
                || old(lctx).lock_id_acyclic(old(self).pcid_needflush.lock_id_by_index(cpu_id, pcid)),
            typed_lock_maps_aligned(old(self), old(lctx)),
            lock_id_set_aligned(old(lctx)),
        ensures
            final(self).inv(),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(final(self), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map().insert((cpu_id, pcid), TypedHeldLock { lock_id: final(self).pcid_needflush.lock_id_by_index(cpu_id, pcid), mode: TypedLockMode::Write }),
            final(lctx).page_lock_map() == old(lctx).page_lock_map(),
            final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
            final(lctx).container_lock_map() == old(lctx).container_lock_map(),
            final(lctx).process_lock_map() == old(lctx).process_lock_map(),
            final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
            final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            final(lctx).allocator_quota_4k_lock_map() == old(lctx).allocator_quota_4k_lock_map(),
            final(lctx).allocator_cache_4k_lock_map() == old(lctx).allocator_cache_4k_lock_map(),
            final(lctx).allocator_global_pool_4k_lock_map() == old(lctx).allocator_global_pool_4k_lock_map(),
            final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(self).pcid_needflush.lock_id_by_index(cpu_id, pcid), KernelObjId::PcidNeedFlush(cpu_id, pcid))),
            final(self).pcid_needflush.spec_index(cpu_id, pcid).wlocked_by(final(lctx)),
            final(self).pcid_needflush.spec_index(cpu_id, pcid).inv(),
            final(self).pcid_needflush.spec_index(cpu_id, pcid).view().index() == (cpu_id, pcid),
            final(self).cpu_published[cpu_id as int].owner_cpu() == cpu_id,
            final(self).pcid_needflush.spec_index(cpu_id, pcid).view_ghost() == Some(final(lctx).cpu_id()),
            final(self).pcid_needflush.spec_index(cpu_id, pcid).locking_thread() == (RwLockState::Write { thread_id: final(lctx).thread_id(), lock_id: ret.view().lock_id() }),
            ret.view().state() is WriteLock,
            ret.view().thread_id() == final(lctx).thread_id(),
            ret.view().ordering_lock_id() == final(self).pcid_needflush.lock_id_by_index(cpu_id, pcid),
            forall|c: CpuId, p: Pcid| #![trigger final(self).pcid_needflush.spec_index(c, p)] #![trigger old(self).pcid_needflush.spec_index(c, p)] index_valid(NUM_CPUS, c) && pcid_valid(p) ==> {
                &&& final(self).pcid_needflush.spec_index(c, p).view() == old(self).pcid_needflush.spec_index(c, p).view()
                &&& ((c != cpu_id || p != pcid) ==> final(self).pcid_needflush.spec_index(c, p) == old(self).pcid_needflush.spec_index(c, p))
            },
            final(self).pt_mp == old(self).pt_mp,
            final(self).it_mp == old(self).it_mp,
            final(self).irt == old(self).irt,
            final(self).pg_arr == old(self).pg_arr,
            final(self).cpu_arr == old(self).cpu_arr,
            final(self).cpu_published == old(self).cpu_published,
            final(self).ctn_mp == old(self).ctn_mp,
            final(self).sched_mp == old(self).sched_mp,
            final(self).pcid_allc_mp == old(self).pcid_allc_mp,
            final(self).cpu_set_mp == old(self).cpu_set_mp,
            final(self).prc_mp == old(self).prc_mp,
            final(self).thr_mp == old(self).thr_mp,
            final(self).ep_mp == old(self).ep_mp,
            final(self).allc_4k_mp == old(self).allc_4k_mp,
            final(self).allc_2m_mp == old(self).allc_2m_mp,
            final(self).allc_1g_mp == old(self).allc_1g_mp,
            final(self).cpu_tlb == old(self).cpu_tlb,
            final(self).iommu_tlb == old(self).iommu_tlb,
            final(self).rt_ctn == old(self).rt_ctn,
            final(self).dflt_pt == old(self).dflt_pt,
    {
        assert({
            &&& self.pcid_needflush.spec_index(cpu_id, pcid).inv()
            &&& self.pcid_needflush.spec_index(cpu_id, pcid).view().index() == (cpu_id, pcid)
            &&& wlock_requires(self.pcid_needflush.spec_index(cpu_id, pcid), &*lctx)
        }) by { reveal(pcid_needflush_wf); reveal(LockedArray2D::typed_lock_map_aligned); };
        let ret = self.pcid_needflush.wlock(cpu_id, pcid, Tracked(&mut *lctx), Ghost(KernelObjId::PcidNeedFlush(cpu_id, pcid)));
        self.pcid_needflush.set_ghost(cpu_id, pcid, Ghost(Some(lctx.cpu_id())), Tracked(&*lctx), Tracked(ret.borrow()));
        proof {
            assert(self.subsystems_inv()) by { reveal(pcid_needflush_wf); reveal(cpu_published_wf); reveal(KernelK::default_pagetable_wf); };
            assert(self.inv()) by { reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(tlb_wf_spec); };
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedArray2D::typed_lock_map_aligned); };
        }
        assert(self.cpu_published[cpu_id as int].owner_cpu() == cpu_id) by { reveal(cpu_published_wf); };
        ret
    }

    pub fn wunlock_pcid_needflush(&mut self, cpu_id: CpuId, pcid: Pcid, Tracked(lctx): Tracked<&mut LocalContext>, lp: Tracked<LockPerm>)
        requires
            old(self).inv(),
            index_valid(NUM_CPUS, cpu_id),
            pcid_valid(pcid),
            typed_lock_maps_aligned(old(self), old(lctx)),
            lock_id_set_aligned(old(lctx)),
            typed_lock_map_contains_mode(old(lctx).pcid_needflush_lock_map(), (cpu_id, pcid), TypedLockMode::Write),
            lp.view().state() is WriteLock,
            lp.view().thread_id() == old(lctx).thread_id(),
            lp.view().lock_id() == old(self).pcid_needflush.spec_index(cpu_id, pcid).locking_thread()->Write_lock_id,
            old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid
                || old(self).cpu_published[cpu_id as int].view() == (old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, pcid),
        ensures
            final(self).inv(),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(final(self), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map().remove((cpu_id, pcid)),
            final(lctx).page_lock_map() == old(lctx).page_lock_map(),
            final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
            final(lctx).container_lock_map() == old(lctx).container_lock_map(),
            final(lctx).process_lock_map() == old(lctx).process_lock_map(),
            final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
            final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            final(lctx).allocator_quota_4k_lock_map() == old(lctx).allocator_quota_4k_lock_map(),
            final(lctx).allocator_cache_4k_lock_map() == old(lctx).allocator_cache_4k_lock_map(),
            final(lctx).allocator_global_pool_4k_lock_map() == old(lctx).allocator_global_pool_4k_lock_map(),
            final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            final(lctx).lock_id_set() == old(lctx).lock_id_set().remove((old(self).pcid_needflush.lock_id_by_index(cpu_id, pcid), KernelObjId::PcidNeedFlush(cpu_id, pcid))),
            !final(self).pcid_needflush.spec_index(cpu_id, pcid).locked(),
            final(self).pcid_needflush.spec_index(cpu_id, pcid).view_ghost() is None,
            forall|c: CpuId, p: Pcid| #![trigger final(self).pcid_needflush.spec_index(c, p)] #![trigger old(self).pcid_needflush.spec_index(c, p)] index_valid(NUM_CPUS, c) && pcid_valid(p) ==> {
                &&& final(self).pcid_needflush.spec_index(c, p).view() == old(self).pcid_needflush.spec_index(c, p).view()
                &&& ((c != cpu_id || p != pcid) ==> final(self).pcid_needflush.spec_index(c, p) == old(self).pcid_needflush.spec_index(c, p))
            },
            final(self).pt_mp == old(self).pt_mp,
            final(self).it_mp == old(self).it_mp,
            final(self).irt == old(self).irt,
            final(self).pg_arr == old(self).pg_arr,
            final(self).cpu_arr == old(self).cpu_arr,
            final(self).cpu_published == old(self).cpu_published,
            final(self).ctn_mp == old(self).ctn_mp,
            final(self).sched_mp == old(self).sched_mp,
            final(self).pcid_allc_mp == old(self).pcid_allc_mp,
            final(self).cpu_set_mp == old(self).cpu_set_mp,
            final(self).prc_mp == old(self).prc_mp,
            final(self).thr_mp == old(self).thr_mp,
            final(self).ep_mp == old(self).ep_mp,
            final(self).allc_4k_mp == old(self).allc_4k_mp,
            final(self).allc_2m_mp == old(self).allc_2m_mp,
            final(self).allc_1g_mp == old(self).allc_1g_mp,
            final(self).cpu_tlb == old(self).cpu_tlb,
            final(self).iommu_tlb == old(self).iommu_tlb,
            final(self).rt_ctn == old(self).rt_ctn,
            final(self).dflt_pt == old(self).dflt_pt,
    {
        assert(self.pcid_needflush.spec_index(cpu_id, pcid).inv()) by { reveal(pcid_needflush_wf); };
        assert(self.pcid_needflush.spec_index(cpu_id, pcid).wlocked_by(&*lctx)) by { reveal(LockedArray2D::typed_lock_map_aligned); };
        assert(lctx.lock_entry_contains(self.pcid_needflush.lock_id_by_index(cpu_id, pcid), KernelObjId::PcidNeedFlush(cpu_id, pcid))) by { reveal(LockedArray2D::typed_lock_map_aligned); };
        assert(lctx.lock_id_set().contains((self.pcid_needflush.lock_id_by_index(cpu_id, pcid), KernelObjId::PcidNeedFlush(cpu_id, pcid)))) by { reveal(lock_id_set_aligned); };
        self.pcid_needflush.set_ghost(cpu_id, pcid, Ghost(None), Tracked(&*lctx), Tracked(lp.borrow()));
        self.pcid_needflush.wunlock(cpu_id, pcid, Tracked(&mut *lctx), lp, Ghost(KernelObjId::PcidNeedFlush(cpu_id, pcid)));
        proof {
            assert(self.subsystems_inv()) by { reveal(pcid_needflush_wf); reveal(cpu_published_wf); reveal(KernelK::default_pagetable_wf); };
            assert(self.inv()) by { reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(tlb_wf_spec); };
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedArray2D::typed_lock_map_aligned); };
        }
    }

    /// Mark an entry conservatively while retaining its write lock. Marking
    /// permits stale translations only when this PCID is inactive.
    pub fn mark_pcid_needflush(&mut self, cpu_id: CpuId, pcid: Pcid, Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&LockPerm>)
        requires
            old(self).inv(),
            index_valid(NUM_CPUS, cpu_id),
            pcid_valid(pcid),
            typed_lock_maps_aligned(old(self), lctx),
            typed_lock_map_contains_mode(lctx.pcid_needflush_lock_map(), (cpu_id, pcid), TypedLockMode::Write),
            lp.view().state() is WriteLock,
            lp.view().thread_id() == lctx.thread_id(),
            lp.view().lock_id() == old(self).pcid_needflush.spec_index(cpu_id, pcid).locking_thread()->Write_lock_id,
        ensures
            final(self).inv(),
            typed_lock_maps_aligned(final(self), lctx),
            final(self).pcid_needflush.spec_index(cpu_id, pcid).view() == (PcidNeedFlush { needflush: true, ..old(self).pcid_needflush.spec_index(cpu_id, pcid).view() }),
            final(self).pcid_needflush.spec_index(cpu_id, pcid).locking_thread() == old(self).pcid_needflush.spec_index(cpu_id, pcid).locking_thread(),
            final(self).pcid_needflush.spec_index(cpu_id, pcid).view_ghost() == old(self).pcid_needflush.spec_index(cpu_id, pcid).view_ghost(),
            final(self).pcid_needflush.spec_index(cpu_id, pcid).view_rodata() == old(self).pcid_needflush.spec_index(cpu_id, pcid).view_rodata(),
            final(self).pcid_needflush.spec_index(cpu_id, pcid).is_init(),
            final(self).pcid_needflush.spec_index(cpu_id, pcid).being_killed() == old(self).pcid_needflush.spec_index(cpu_id, pcid).being_killed(),
            forall|c: CpuId, p: Pcid| #![trigger final(self).pcid_needflush.spec_index(c, p)] #![trigger old(self).pcid_needflush.spec_index(c, p)] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid) ==> final(self).pcid_needflush.spec_index(c, p) == old(self).pcid_needflush.spec_index(c, p),
            final(self).pt_mp == old(self).pt_mp,
            final(self).it_mp == old(self).it_mp,
            final(self).irt == old(self).irt,
            final(self).pg_arr == old(self).pg_arr,
            final(self).cpu_arr == old(self).cpu_arr,
            final(self).cpu_published == old(self).cpu_published,
            final(self).ctn_mp == old(self).ctn_mp,
            final(self).sched_mp == old(self).sched_mp,
            final(self).pcid_allc_mp == old(self).pcid_allc_mp,
            final(self).cpu_set_mp == old(self).cpu_set_mp,
            final(self).prc_mp == old(self).prc_mp,
            final(self).thr_mp == old(self).thr_mp,
            final(self).ep_mp == old(self).ep_mp,
            final(self).allc_4k_mp == old(self).allc_4k_mp,
            final(self).allc_2m_mp == old(self).allc_2m_mp,
            final(self).allc_1g_mp == old(self).allc_1g_mp,
            final(self).cpu_tlb == old(self).cpu_tlb,
            final(self).iommu_tlb == old(self).iommu_tlb,
            final(self).rt_ctn == old(self).rt_ctn,
            final(self).dflt_pt == old(self).dflt_pt,
    {
        assert(self.pcid_needflush.spec_index(cpu_id, pcid).is_init()) by { reveal(pcid_needflush_wf); };
        let entry = self.pcid_needflush.borrow_mut_typed(cpu_id, pcid, Ghost(lctx.pcid_needflush_lock_map()), Tracked(lctx), lp);
        entry.set(true);
        proof {
            assert(self.subsystems_inv()) by { reveal(pcid_needflush_wf); reveal(cpu_published_wf); reveal(KernelK::default_pagetable_wf); };
            assert(self.inv()) by { reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(tlb_wf_spec); };
            assert(typed_lock_maps_aligned(self, lctx)) by { reveal(LockedArray2D::typed_lock_map_aligned); };
        }
    }
}
}
