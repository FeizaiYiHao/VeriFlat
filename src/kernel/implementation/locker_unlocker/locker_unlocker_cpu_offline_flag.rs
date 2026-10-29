#[cfg(verus_keep_ghost)]
use super::locker_unlocker_cpu_offline_flag_eof::{cpu_offline_flag_lock_op_eof};
use vstd::prelude::*;
use vstd::assert_seqs_equal;
use crate::*;

verus! {

impl KernelK {
    pub fn wlock_cpu_offline_flag(&mut self, flags_ptr: RwLockCpuOfflineFlagsPtr, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).cpu_offline_mp.dom().contains(flags_ptr),
            index_valid(NUM_CPUS, cpu_id),
            old(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(old(self), old(lctx)),
            // An ordinary caller holds only non-Off cpus and containers no deeper than the table and, when the table is its own
            // running cpu's, that cpu's process and thread. A killer of a deeper table holds its own cpu, Idle cpus no deeper
            // than the table, its process, thread, and container, objects it marked, and flags below this one.
            ({
                let depth = old(self).cpu_offline_mp.spec_index(flags_ptr).container_depth.view();
                let cpu_i = old(lctx).cpu_id();
                let cpu = old(self).cpu_arr.spec_index(cpu_i).view().view().view();
                ||| {
                    &&& old(lctx).cpu_offline_flag_lock_map().dom().is_empty()
                    &&& forall|i: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(i)] old(lctx).cpu_lock_map().dom().contains(i) ==> !(old(self).cpu_arr.spec_index(i).view().view().view().state is Off)
                    &&& forall|p: RwLockProcessPtr| #![trigger old(lctx).process_lock_map().dom().contains(p)] old(lctx).process_lock_map().dom().contains(p)
                        ==> index_valid(NUM_CPUS, cpu_i) && old(lctx).cpu_lock_map().dom().contains(cpu_i) && cpu.state is Running && cpu.current_process == Some(p) && flags_ptr == cpu_offline_flags_ptr(cpu.owning_container)
                    &&& forall|t: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(t)] old(lctx).thread_lock_map().dom().contains(t)
                        ==> index_valid(NUM_CPUS, cpu_i) && old(lctx).cpu_lock_map().dom().contains(cpu_i) && cpu.state is Running && cpu.current_thread == Some(t) && flags_ptr == cpu_offline_flags_ptr(cpu.owning_container)
                    &&& old(lctx).cpu_set_lock_map().dom().is_empty()
                    &&& old(lctx).page_lock_map().dom().is_empty() && old(lctx).pcid_needflush_lock_map().dom().is_empty() && old(lctx).endpoint_lock_map().dom().is_empty()
                    &&& old(lctx).scheduler_lock_map().dom().is_empty() && old(lctx).pcid_allocator_lock_map().dom().is_empty() && old(lctx).pagetable_lock_map().dom().is_empty()
                    &&& old(lctx).iommu_table_lock_map().dom().is_empty() && old(lctx).iommu_root_table_lock_map().dom().is_empty()
                    &&& old(lctx).holds_no_allocator_locks(PageSize::SZ4k) && old(lctx).holds_no_allocator_locks(PageSize::SZ2m) && old(lctx).holds_no_allocator_locks(PageSize::SZ1g)
                    &&& forall|i: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(i)] old(lctx).cpu_lock_map().dom().contains(i) ==> old(self).cpu_arr.spec_index(i).view().view().view().container_depth <= depth
                    &&& forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> old(self).ctn_mp.spec_index(c).view_rodata().view().depth <= depth
                }
                ||| {
                    &&& index_valid(NUM_CPUS, cpu_i)
                    &&& old(lctx).cpu_lock_map().dom().contains(cpu_i)
                    &&& forall|i: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(i)] old(lctx).cpu_lock_map().dom().contains(i) && i != cpu_i
                        ==> old(self).cpu_arr.spec_index(i).view().view().view().state is Idle && old(self).cpu_arr.spec_index(i).view().view().view().container_depth <= depth
                    &&& cpu.state is Running
                    &&& cpu.container_depth < depth
                    &&& forall|p: RwLockProcessPtr| #![trigger old(lctx).process_lock_map().dom().contains(p)] old(lctx).process_lock_map().dom().contains(p) && cpu.current_process != Some(p) ==> old(self).prc_mp.spec_index(p).being_killed()
                    &&& forall|t: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(t)] old(lctx).thread_lock_map().dom().contains(t) && cpu.current_thread != Some(t) ==> old(self).thr_mp.spec_index(t).being_killed()
                    &&& forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) && c != cpu.owning_container ==> old(self).ctn_mp.spec_index(c).being_killed()
                    &&& forall|s: RwLockCpuSetPtr| #![trigger old(lctx).cpu_set_lock_map().dom().contains(s)] old(lctx).cpu_set_lock_map().dom().contains(s) ==> old(self).cpu_set_mp.spec_index(s).being_killed()
                    &&& typed_lock_map_2d_ids_lt(old(lctx).cpu_offline_flag_lock_map(), old(self).cpu_offline_mp.spec_index(flags_ptr).flags.lock_id_by_index(cpu_id))
                    &&& old(lctx).page_lock_map().dom().is_empty() && old(lctx).pcid_needflush_lock_map().dom().is_empty() && old(lctx).endpoint_lock_map().dom().is_empty()
                    &&& old(lctx).scheduler_lock_map().dom().is_empty() && old(lctx).pcid_allocator_lock_map().dom().is_empty() && old(lctx).pagetable_lock_map().dom().is_empty()
                    &&& old(lctx).iommu_table_lock_map().dom().is_empty() && old(lctx).iommu_root_table_lock_map().dom().is_empty()
                    &&& old(lctx).holds_no_allocator_locks(PageSize::SZ4k) && old(lctx).holds_no_allocator_locks(PageSize::SZ2m) && old(lctx).holds_no_allocator_locks(PageSize::SZ1g)
                }
            }),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            *final(self) == (KernelK { cpu_offline_mp: final(self).cpu_offline_mp, ..*old(self) }),
            final(self).cpu_offline_mp.unchanged_except(&old(self).cpu_offline_mp, flags_ptr),
            final(self).cpu_offline_mp.perms_wf(),
            final(self).cpu_offline_mp.spec_index(flags_ptr).inv(),
            final(self).cpu_offline_mp.spec_index(flags_ptr).owning_container == old(self).cpu_offline_mp.spec_index(flags_ptr).owning_container,
            final(self).cpu_offline_mp.spec_index(flags_ptr).container_depth == old(self).cpu_offline_mp.spec_index(flags_ptr).container_depth,
            final(self).cpu_offline_mp.spec_index(flags_ptr).flags.unchanged_except(&old(self).cpu_offline_mp.spec_index(flags_ptr).flags, cpu_id),
            final(self).cpu_offline_mp.spec_index(flags_ptr).flags.lock_id_by_index(cpu_id) == old(self).cpu_offline_mp.spec_index(flags_ptr).flags.lock_id_by_index(cpu_id),
            final(self).cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view().view().container_depth == old(self).cpu_offline_mp.spec_index(flags_ptr).container_depth,
            cpu_offline_requests_of(final(self).cpu_offline_mp.spec_index(flags_ptr)) == cpu_offline_requests_of(old(self).cpu_offline_mp.spec_index(flags_ptr)),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            wlock_ensures(old(self).cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view(), final(self).cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view(),
                old(self).cpu_offline_mp.spec_index(flags_ptr).flags.lock_id_by_index(cpu_id), final(lctx), ret.view()),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::CpuOfflineFlag(flags_ptr, cpu_id), TypedHeldLock { lock_id: final(self).cpu_offline_mp.spec_index(flags_ptr).flags.lock_id_by_index(cpu_id), mode: TypedLockMode::Write }),
    {
        proof {
            cpu_offline_flags_wf_map(old(self).cpu_offline_mp, old(self).cpu_arr); cpu_offline_flags_wf_at(old(self).cpu_offline_mp, old(self).cpu_arr, flags_ptr);
            assert(old(lctx).lock_id_acyclic(old(self).cpu_offline_mp.spec_index(flags_ptr).flags.lock_id_by_index(cpu_id))) by {
                let cpu_i = old(lctx).cpu_id();
                let cpu = old(self).cpu_arr.spec_index(cpu_i).view().view().view();
                thread_cpu_wf_cpu_at(old(self).thr_mp, old(self).cpu_arr, cpu_i); process_cpu_wf_at(old(self).prc_mp, old(self).cpu_arr, cpu_i);
                container_cpu_wf_cpu_at(old(self).ctn_mp, old(self).cpu_set_mp, old(self).cpu_arr, cpu_i);
                if index_valid(NUM_CPUS, cpu_i) && cpu.state is Running {
                    thread_perms_wf_at(old(self).thr_mp, cpu.current_thread->Some_0); process_thread_wf_at(old(self).prc_mp, old(self).thr_mp, cpu.current_thread->Some_0);
                    container_process_wf_process_at(old(self).ctn_mp, old(self).prc_mp, cpu.current_process->Some_0);
                }
                reveal(LocalContext::lock_id_acyclic); reveal(pagetable_window_typed_lock_map_aligned); reveal(UnLockedMap::typed_flag_lock_map_aligned); reveal(iommu_root_table_typed_lock_map_aligned);
                reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned);
            };
            assert(!old(self).cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view().locked_by_thread(old(lctx).thread_id())) by { reveal(UnLockedMap::typed_flag_lock_map_aligned); };
        }
        let ret = self.cpu_offline_mp.wlock_flag(flags_ptr, cpu_id, Tracked(&mut *lctx));
        proof {
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(UnLockedMap::typed_flag_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
            assert(cpu_offline_requests_of(self.cpu_offline_mp.spec_index(flags_ptr)) == cpu_offline_requests_of(old(self).cpu_offline_mp.spec_index(flags_ptr))) by {
                reveal(cpu_offline_requests_of);
                assert_seqs_equal!(cpu_offline_requests_of(self.cpu_offline_mp.spec_index(flags_ptr)) == cpu_offline_requests_of(old(self).cpu_offline_mp.spec_index(flags_ptr)));
            };
            cpu_offline_flag_lock_op_eof(*old(self), *self, flags_ptr, cpu_id);
        }
        ret
    }

    pub fn wunlock_cpu_offline_flag(&mut self, flags_ptr: RwLockCpuOfflineFlagsPtr, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).cpu_offline_mp.dom().contains(flags_ptr),
            index_valid(NUM_CPUS, cpu_id),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).cpu_offline_flag_lock_map(), (flags_ptr, cpu_id), TypedLockMode::Write),
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            *final(self) == (KernelK { cpu_offline_mp: final(self).cpu_offline_mp, ..*old(self) }),
            final(self).cpu_offline_mp.unchanged_except(&old(self).cpu_offline_mp, flags_ptr),
            final(self).cpu_offline_mp.perms_wf(),
            final(self).cpu_offline_mp.spec_index(flags_ptr).inv(),
            final(self).cpu_offline_mp.spec_index(flags_ptr).owning_container == old(self).cpu_offline_mp.spec_index(flags_ptr).owning_container,
            final(self).cpu_offline_mp.spec_index(flags_ptr).container_depth == old(self).cpu_offline_mp.spec_index(flags_ptr).container_depth,
            final(self).cpu_offline_mp.spec_index(flags_ptr).flags.unchanged_except(&old(self).cpu_offline_mp.spec_index(flags_ptr).flags, cpu_id),
            cpu_offline_requests_of(final(self).cpu_offline_mp.spec_index(flags_ptr)) == cpu_offline_requests_of(old(self).cpu_offline_mp.spec_index(flags_ptr)),
            wunlock_ensures(old(self).cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view(), final(self).cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view()),
            unlock_ensures(old(lctx), final(lctx), KernelObjId::CpuOfflineFlag(flags_ptr, cpu_id), old(self).cpu_offline_mp.spec_index(flags_ptr).flags.lock_id_by_index(cpu_id)),
    {
        proof {
            cpu_offline_flags_wf_map(old(self).cpu_offline_mp, old(self).cpu_arr); cpu_offline_flags_wf_at(old(self).cpu_offline_mp, old(self).cpu_arr, flags_ptr);
            assert(old(lctx).lock_entry_contains(old(self).cpu_offline_mp.spec_index(flags_ptr).flags.lock_id_by_index(cpu_id), KernelObjId::CpuOfflineFlag(flags_ptr, cpu_id))) by { reveal(UnLockedMap::typed_flag_lock_map_aligned); };
            assert(old(self).cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view().wlocked_by(old(lctx))) by { reveal(UnLockedMap::typed_flag_lock_map_aligned); };
        }
        self.cpu_offline_mp.wunlock_flag(flags_ptr, cpu_id, Tracked(&mut *lctx), lock_perm);
        proof {
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(UnLockedMap::typed_flag_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
            assert(cpu_offline_requests_of(self.cpu_offline_mp.spec_index(flags_ptr)) == cpu_offline_requests_of(old(self).cpu_offline_mp.spec_index(flags_ptr))) by {
                reveal(cpu_offline_requests_of);
                assert_seqs_equal!(cpu_offline_requests_of(self.cpu_offline_mp.spec_index(flags_ptr)) == cpu_offline_requests_of(old(self).cpu_offline_mp.spec_index(flags_ptr)));
            };
            cpu_offline_flag_lock_op_eof(*old(self), *self, flags_ptr, cpu_id);
        }
    }
}
}
