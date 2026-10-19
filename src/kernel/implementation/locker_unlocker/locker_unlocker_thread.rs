#[cfg(verus_keep_ghost)]
use super::locker_unlocker_thread_eof::{wlock_thread_eof, mark_thread_kill_eof, wunlock_thread_eof, set_thread_syscall_progress_eof};
use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
    #[verifier::spinoff_prover]
    pub fn wlock_thread_unless_killed(&mut self, thread_ptr: RwLockThreadPtr, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Option<Tracked<LockPerm>>)
        requires
            old(self).inv(),
            old(self).thr_mp.dom().contains(thread_ptr),
            !old(lctx).thread_lock_map().dom().contains(thread_ptr),
            old(lctx).kernel_view_locking_state() is Acquire,
            (!old(self).thr_mp.spec_index(thread_ptr).being_killed() ==> old(lctx).lock_id_acyclic(old(self).thr_mp.lock_id_by_key(thread_ptr))) || {
                let cpus = old(lctx).cpu_lock_map().dom();
                let thread = old(self).thr_mp.spec_index(thread_ptr).view();
                &&& (forall|held_cpu_id: CpuId|
                    #![trigger cpus.contains(held_cpu_id)]
                    cpus.contains(held_cpu_id) ==> {
                        &&& index_valid(NUM_CPUS, held_cpu_id)
                        &&& !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off)
                    })
                &&& match thread.state {
                    ThreadState::RUNNING { cpu_id } => {
                        let containers = old(lctx).container_lock_map().dom();
                        &&& cpus.contains(cpu_id)
                        &&& (forall|held_cpu_id: CpuId|
                            #![trigger cpus.contains(held_cpu_id)]
                            cpus.contains(held_cpu_id) ==> {
                                &&& index_valid(NUM_CPUS, held_cpu_id)
                                &&& old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().owning_container == thread.owning_container
                                &&& old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().current_process is None || old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().current_process == Some(thread.owning_proc)
                                &&& old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().container_depth == thread.container_depth
                                &&& old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().current_process is Some ==> old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().process_depth == thread.process_depth
                            })
                        &&& old(lctx).process_lock_map().dom().contains(thread.owning_proc) ==> {
                            &&& old(self).prc_mp.spec_index(thread.owning_proc).view_rodata().view().container_depth == thread.container_depth
                            &&& old(self).prc_mp.spec_index(thread.owning_proc).view_rodata().view().depth == thread.process_depth
                        }
                        &&& containers.contains(thread.owning_container) ==> old(self).ctn_mp.spec_index(thread.owning_container).view_rodata().view().depth == thread.container_depth
                        &&& old(lctx).page_lock_map().dom().is_empty()
                        &&& old(lctx).process_lock_map().dom().subset_of(set![thread.owning_proc])
                        &&& old(lctx).thread_lock_map().dom().is_empty()
                        &&& old(lctx).endpoint_lock_map().dom().is_empty()
                        &&& old(lctx).scheduler_lock_map().dom().is_empty()
                        &&& old(lctx).cpu_set_lock_map().dom().is_empty()
                        &&& old(lctx).pagetable_lock_map().dom().is_empty()
                        &&& old(lctx).iommu_table_lock_map().dom().is_empty()
                        &&& old(lctx).iommu_root_table_lock_map().dom().is_empty()
                        &&& old(lctx).allocator_quota_4k_lock_map().dom().is_empty()
                        &&& old(lctx).allocator_cache_4k_lock_map().dom().is_empty()
                        &&& old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty()
                        &&& old(lctx).allocator_quota_2m_lock_map().dom().is_empty()
                        &&& old(lctx).allocator_cache_2m_lock_map().dom().is_empty()
                        &&& old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty()
                        &&& old(lctx).allocator_quota_1g_lock_map().dom().is_empty()
                        &&& old(lctx).allocator_cache_1g_lock_map().dom().is_empty()
                        &&& old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty()
                        &&& old(lctx).pcid_needflush_lock_map().dom().is_empty()
                        &&& containers.subset_of(set![thread.owning_container])
                        &&& old(lctx).pcid_allocator_lock_map().dom().is_empty()
                    },
                    ThreadState::SCHEDULED { .. } => {
                        let cpu_id = old(lctx).cpu_id();
                        let cpu = old(self).cpu_arr.spec_index(cpu_id).view().view().view();
                        let scheduler_ptr = old(self).ctn_mp.spec_index(thread.owning_container).view_rodata().view().scheduler;
                        &&& index_valid(NUM_CPUS, cpu_id)
                        &&& cpus =~= set![cpu_id]
                        &&& typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write)
                        &&& cpu.owning_container == thread.owning_container
                        &&& forall|held: (RwLockSchedulerPtr, CpuId)| #![trigger old(lctx).scheduler_lock_map().dom().contains(held)]
                            old(lctx).scheduler_lock_map().dom().contains(held) ==> held.0 == scheduler_ptr
                        &&& typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (scheduler_ptr, thread.state->SCHEDULED_cpu_id), TypedLockMode::Write)
                        &&& old(lctx).process_lock_map().dom() =~= match cpu.current_process { Some(ptr) => set![ptr], None => Set::empty() }
                        &&& old(lctx).thread_lock_map().dom() =~= match cpu.current_thread { Some(ptr) => set![ptr], None => Set::empty() }
                        &&& old(lctx).page_lock_map().dom().is_empty()
                        &&& old(lctx).container_lock_map().dom().is_empty()
                        &&& old(lctx).endpoint_lock_map().dom().is_empty()
                        &&& old(lctx).cpu_set_lock_map().dom().is_empty()
                        &&& old(lctx).pcid_allocator_lock_map().dom().is_empty()
                        &&& old(lctx).pagetable_lock_map().dom().is_empty()
                        &&& old(lctx).iommu_table_lock_map().dom().is_empty()
                        &&& old(lctx).iommu_root_table_lock_map().dom().is_empty()
                        &&& old(lctx).allocator_quota_4k_lock_map().dom().is_empty()
                        &&& old(lctx).allocator_cache_4k_lock_map().dom().is_empty()
                        &&& old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty()
                        &&& old(lctx).allocator_quota_2m_lock_map().dom().is_empty()
                        &&& old(lctx).allocator_cache_2m_lock_map().dom().is_empty()
                        &&& old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty()
                        &&& old(lctx).allocator_quota_1g_lock_map().dom().is_empty()
                        &&& old(lctx).allocator_cache_1g_lock_map().dom().is_empty()
                        &&& old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty()
                        &&& old(lctx).pcid_needflush_lock_map().dom().is_empty()
                    },
                    ThreadState::WAITING_REPLY | ThreadState::DANGLING => {
                        let callee_ptr = thread.callee->Some_0;
                        let callee = old(self).thr_mp.spec_index(callee_ptr).view();
                        &&& thread.callee is Some
                        &&& old(self).thr_mp.dom().contains(callee_ptr)
                        &&& callee.state is RUNNING
                        &&& cpus =~= set![callee.state->RUNNING_cpu_id]
                        &&& old(lctx).thread_lock_map().dom() =~= set![callee_ptr]
                        &&& old(lctx).endpoint_lock_map().dom().len() <= 1
                        &&& old(lctx).page_lock_map().dom().is_empty()
                        &&& old(lctx).container_lock_map().dom().subset_of(set![callee.owning_container])
                        &&& old(lctx).process_lock_map().dom().subset_of(set![callee.owning_proc])
                        &&& old(lctx).scheduler_lock_map().dom().is_empty()
                        &&& old(lctx).pcid_allocator_lock_map().dom().is_empty()
                        &&& old(lctx).cpu_set_lock_map().dom().is_empty()
                        &&& old(lctx).pagetable_lock_map().dom().is_empty()
                        &&& old(lctx).iommu_table_lock_map().dom().is_empty()
                        &&& old(lctx).iommu_root_table_lock_map().dom().is_empty()
                        &&& old(lctx).allocator_quota_4k_lock_map().dom().is_empty()
                        &&& old(lctx).allocator_cache_4k_lock_map().dom().is_empty()
                        &&& old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty()
                        &&& old(lctx).allocator_quota_2m_lock_map().dom().is_empty()
                        &&& old(lctx).allocator_cache_2m_lock_map().dom().is_empty()
                        &&& old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty()
                        &&& old(lctx).allocator_quota_1g_lock_map().dom().is_empty()
                        &&& old(lctx).allocator_cache_1g_lock_map().dom().is_empty()
                        &&& old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty()
                        &&& old(lctx).pcid_needflush_lock_map().dom().is_empty()
                    },
                    _ => {
                        &&& thread.state.is_endpoint_waiting()
                        &&& thread.blocking_endpoint_ptr is Some
                        &&& old(lctx).process_lock_map().dom().len() <= 1
                        &&& !old(lctx).thread_lock_map().dom().is_empty()
                        &&& forall|current_thread_ptr: RwLockThreadPtr|
                            #![trigger old(lctx).thread_lock_map().dom().contains(current_thread_ptr)]
                            old(lctx).thread_lock_map().dom().contains(current_thread_ptr) ==> {
                                let current_thread = old(self).thr_mp.spec_index(current_thread_ptr).view();
                                &&& current_thread_ptr != thread_ptr
                                &&& current_thread.state is RUNNING
                                &&& cpus.contains(current_thread.state->RUNNING_cpu_id)
                                &&& (forall|held_cpu_id: CpuId|
                                    #![trigger cpus.contains(held_cpu_id)]
                                    cpus.contains(held_cpu_id) ==> {
                                        &&& index_valid(NUM_CPUS, held_cpu_id)
                                        &&& old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().owning_container == current_thread.owning_container
                                    })
                                &&& old(lctx).page_lock_map().dom().is_empty()
                                &&& old(lctx).container_lock_map().dom().is_empty()
                                &&& old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr]
                                &&& old(lctx).endpoint_lock_map().dom() =~= set![thread.blocking_endpoint_ptr->Some_0]
                                &&& old(lctx).scheduler_lock_map().dom().is_empty()
                                &&& old(lctx).pcid_allocator_lock_map().dom().is_empty()
                                &&& old(lctx).cpu_set_lock_map().dom().is_empty()
                                &&& old(lctx).pagetable_lock_map().dom().is_empty()
                                &&& old(lctx).iommu_table_lock_map().dom().is_empty()
                                &&& old(lctx).iommu_root_table_lock_map().dom().is_empty()
                                &&& old(lctx).allocator_quota_4k_lock_map().dom().is_empty()
                                &&& old(lctx).allocator_cache_4k_lock_map().dom().is_empty()
                                &&& old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty()
                                &&& old(lctx).allocator_quota_2m_lock_map().dom().is_empty()
                                &&& old(lctx).allocator_cache_2m_lock_map().dom().is_empty()
                                &&& old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty()
                                &&& old(lctx).allocator_quota_1g_lock_map().dom().is_empty()
                                &&& old(lctx).allocator_cache_1g_lock_map().dom().is_empty()
                                &&& old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty()
                                &&& old(lctx).pcid_needflush_lock_map().dom().is_empty()
                            }
                    },
                }
            } || killer_any_thread_lock_context(*old(self), *old(lctx), thread_ptr, old(lctx).container_lock_map().dom())
                || (old(self).thr_mp.spec_index(thread_ptr).view().state.is_reply_waiting() && killed_thread_reclaim_lock_context(*old(self), *old(lctx))),
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            *final(self) == (KernelK { thr_mp: final(self).thr_mp, ..*old(self) }),
            final(self).thr_mp.unchanged_except(&old(self).thr_mp, thread_ptr),
            final(self).thr_mp.perms_wf(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            ret is None ==> {
                &&& old(self).thr_mp.spec_index(thread_ptr).being_killed()
                &&& final(self).thr_mp.spec_index(thread_ptr) == old(self).thr_mp.spec_index(thread_ptr)
                &&& typed_lock_maps_unchanged(old(lctx), final(lctx))
            },
            ret is Some ==> {
                &&& old(self).thr_mp.spec_index(thread_ptr).being_killed() == false
                &&& wlock_ensures(old(self).thr_mp.spec_index(thread_ptr), final(self).thr_mp.spec_index(thread_ptr), old(self).thr_mp.lock_id_by_key(thread_ptr), final(lctx), ret.unwrap().view())
                &&& final(self).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean()
                &&& final(self).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean()
                &&& final(self).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None
                &&& typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Thread(thread_ptr), TypedHeldLock { lock_id: final(self).thr_mp.lock_id_by_key(thread_ptr), mode: TypedLockMode::Write })
            },
    {
        proof {
            thread_perms_wf_map(old(self).thr_mp);
            thread_perms_wf_at(old(self).thr_mp, thread_ptr);
            let target_thread = old(self).thr_mp.spec_index(thread_ptr).view();
            if old(self).thr_mp.spec_index(thread_ptr).being_killed() {} else if killer_any_thread_lock_context(*old(self), *old(lctx), thread_ptr, old(lctx).container_lock_map().dom()) {
                assert(old(lctx).lock_id_acyclic(old(self).thr_mp.lock_id_by_key(thread_ptr))) by {
                    let cpu_id = old(lctx).cpu_id();
                    let cpu = old(self).cpu_arr.spec_index(cpu_id).view().view().view();
                    thread_cpu_wf_cpu_at(old(self).thr_mp, old(self).cpu_arr, cpu_id); process_cpu_wf_at(old(self).prc_mp, old(self).cpu_arr, cpu_id);
                    container_cpu_wf_cpu_at(old(self).ctn_mp, old(self).cpu_set_mp, old(self).cpu_arr, cpu_id);
                    thread_perms_wf_at(old(self).thr_mp, cpu.current_thread->Some_0); process_thread_wf_at(old(self).prc_mp, old(self).thr_mp, cpu.current_thread->Some_0);
                    container_process_wf_process_at(old(self).ctn_mp, old(self).prc_mp, cpu.current_process->Some_0);
                    reveal(LocalContext::lock_id_acyclic); reveal(UnLockedMap::typed_flag_lock_map_aligned); reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned);
                };
            } else if target_thread.state.is_reply_waiting() && killed_thread_reclaim_lock_context(*old(self), *old(lctx)) {
                assert(old(lctx).lock_id_acyclic(old(self).thr_mp.lock_id_by_key(thread_ptr))) by {
                    thread_cpu_wf_cpu_at(old(self).thr_mp, old(self).cpu_arr, old(lctx).cpu_id());
                    reveal(LocalContext::lock_id_acyclic); reveal(UnLockedMap::typed_flag_lock_map_aligned); reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned);
                };
            } else {
                match target_thread.state {
                    ThreadState::RUNNING { cpu_id } => {
                        assert(old(lctx).lock_id_acyclic(old(self).thr_mp.lock_id_by_key(thread_ptr))) by {
                            reveal(LocalContext::lock_id_acyclic); reveal(UnLockedMap::typed_flag_lock_map_aligned); reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned);
                        };
                    },
                    ThreadState::SCHEDULED { .. } => {
                        assert(old(lctx).lock_id_acyclic(old(self).thr_mp.lock_id_by_key(thread_ptr))) by {
                            let cpu_id = old(lctx).cpu_id();
                            let cpu = old(self).cpu_arr.spec_index(cpu_id).view().view().view();
                            cpu_array_wf_at(old(self).cpu_arr, old(self).dflt_pt.view(), cpu_id); thread_cpu_wf_cpu_at(old(self).thr_mp, old(self).cpu_arr, cpu_id);
                            process_cpu_wf_at(old(self).prc_mp, old(self).cpu_arr, cpu_id); container_cpu_wf_cpu_at(old(self).ctn_mp, old(self).cpu_set_mp, old(self).cpu_arr, cpu_id);
                            process_thread_wf_at(old(self).prc_mp, old(self).thr_mp, thread_ptr); container_process_wf_process_at(old(self).ctn_mp, old(self).prc_mp, target_thread.owning_proc);
                            if index_valid(NUM_CPUS, cpu_id) && cpu.state is Running { thread_perms_wf_at(old(self).thr_mp, cpu.current_thread->Some_0); process_thread_wf_at(old(self).prc_mp, old(self).thr_mp, cpu.current_thread->Some_0); }
                            if cpu.current_process is Some { container_process_wf_process_at(old(self).ctn_mp, old(self).prc_mp, cpu.current_process->Some_0); }
                            reveal(LocalContext::lock_id_acyclic); reveal(UnLockedMap::typed_flag_lock_map_aligned); reveal(UnLockedMap::typed_shard_lock_map_aligned);
                            reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned);
                        };
                    },
                    ThreadState::WAITING_REPLY | ThreadState::DANGLING => {
                        assert(old(lctx).lock_id_acyclic(old(self).thr_mp.lock_id_by_key(thread_ptr))) by {
                            reveal(LocalContext::lock_id_acyclic); reveal(UnLockedMap::typed_flag_lock_map_aligned); reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned);
                        };
                    },
                    _ => {
                        assert(old(lctx).lock_id_acyclic(old(self).thr_mp.lock_id_by_key(thread_ptr))) by {
                            reveal(LocalContext::lock_id_acyclic); reveal(UnLockedMap::typed_flag_lock_map_aligned); reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned);
                        };
                    },
                }
            }
        }
        proof {
            assert(!old(self).thr_mp.spec_index(thread_ptr).locked_by_thread(old(lctx).thread_id())) by {
                if old(self).thr_mp.spec_index(thread_ptr).locked_by_thread(old(lctx).thread_id()) {
                    assert(old(lctx).thread_lock_map().dom().contains(thread_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
                }
            };
        }
        let res = self.thr_mp.wlock_unless_killed(thread_ptr, Tracked(&mut *lctx), Ghost(KernelObjId::Thread(thread_ptr)));
        proof {
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by {
                broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
            };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
            wlock_thread_eof(*old(self), *self, thread_ptr, *lctx, res);
        }
        res
    }

    /// Mark a thread of a process the killer marked and holds; the killer already write-holds the thread. A marked
    /// thread is held by whoever holds its marked owner, and the held entry moves to the sunk id.
    pub fn mark_thread_kill(&mut self, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, killer_info: KillerInfo, Tracked(lctx): Tracked<&mut LocalContext>)
        requires
            old(self).inv(),
            old(self).prc_mp.dom().contains(process_ptr),
            old(self).prc_mp.spec_index(process_ptr).being_killed(),
            typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
            old(self).prc_mp.spec_index(process_ptr).view().owned_threads.view().contains(thread_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
            !old(self).thr_mp.spec_index(thread_ptr).being_killed(),
            !old(self).thr_mp.spec_index(thread_ptr).view().state.is_reply_waiting(),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            final(self).inv(),
            typed_lock_maps_aligned(final(self), final(lctx)),
            *final(self) == (KernelK { thr_mp: final(self).thr_mp, ..*old(self) }),
            final(self).thr_mp.unchanged_except(&old(self).thr_mp, thread_ptr),
            final(self).thr_mp.perms_wf(),
            final(self).thr_mp.spec_index(thread_ptr).being_killed(),
            final(self).thr_mp.spec_index(thread_ptr).locking_thread() == old(self).thr_mp.spec_index(thread_ptr).locking_thread(),
            final(self).thr_mp.spec_index(thread_ptr).view() == old(self).thr_mp.spec_index(thread_ptr).view(),
            final(self).thr_mp.lock_id_by_key(thread_ptr) == (LockId { container: LockOwnerId::High, process: LockOwnerId::High, major: KILLED_LOCK_MAJOR, minor: thread_ptr }),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Thread(thread_ptr), TypedHeldLock { lock_id: final(self).thr_mp.lock_id_by_key(thread_ptr), mode: TypedLockMode::Write }),
    {
        proof {
            assert(old(self).thr_mp.dom().contains(thread_ptr)) by { process_thread_wf_process_at(old(self).prc_mp, old(self).thr_mp, process_ptr, thread_ptr); };
            thread_perms_wf_map(old(self).thr_mp);
            thread_perms_wf_at(old(self).thr_mp, thread_ptr);
            old(self).prc_mp.typed_lock_map_aligned_write_at(old(lctx).process_lock_map(), old(lctx).thread_id(), process_ptr);
            old(self).thr_mp.typed_lock_map_aligned_write_at(old(lctx).thread_lock_map(), old(lctx).thread_id(), thread_ptr);
            assert(old(lctx).lock_entry_contains(old(self).thr_mp.lock_id_by_key(thread_ptr), KernelObjId::Thread(thread_ptr))) by { reveal(LockedMap::typed_lock_map_aligned); };
        }
        self.thr_mp.mark_kill(thread_ptr, Tracked(&*lctx), killer_info);
        proof {
            let entry = TypedHeldLock { lock_id: old(self).thr_mp.lock_id_by_key(thread_ptr), mode: TypedLockMode::Write };
            lctx.update_lock_id(KernelObjId::Thread(thread_ptr), old(self).thr_mp.lock_id_by_key(thread_ptr), self.thr_mp.lock_id_by_key(thread_ptr));
            map_insert_overwrite_lemma(old(lctx).thread_lock_map(), thread_ptr, entry, TypedHeldLock { lock_id: self.thr_mp.lock_id_by_key(thread_ptr), mode: TypedLockMode::Write });
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            mark_thread_kill_eof(*old(self), *self, *old(lctx), thread_ptr, process_ptr);
        }
    }

    /// Companion of the thread write-lock for the unlock side. Wraps
    /// `LockedMap::wunlock` for `thread_map` and re-establishes `inv()`. Only
    /// the targeted `thread_map` entry's lock state moves; every thread
    /// payload view, every other entry, and every other KernelK field is
    /// byte-equal pre/post — so the conservation folds transport by
    /// byte-equality (thread payloads unchanged).
    ///
    /// The pending-clean protocol: the thread must be `free_quota_pending_clean`
    /// before releasing the write lock, because once unlocked the global
    /// invariant `thread_free_quota_pending_empty_unless_wlocked` demands it.
    /// A freshly-created thread satisfies this (its pendings are all zero).
    pub fn wunlock_thread(&mut self, thread_ptr: RwLockThreadPtr, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).thr_mp.dom().contains(thread_ptr),
            old(self).thr_mp.spec_index(thread_ptr).being_killed() == false,
            !(old(self).thr_mp.spec_index(thread_ptr).view().state is IPC_ENDPOINT_TRANSIT),
            !(old(self).thr_mp.spec_index(thread_ptr).view().state is KILLED),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            // The pending-clean protocol: pendings must be flushed before
            // releasing the write lock (see doc comment above).
            old(self).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            old(self).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(self).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            // ---- Kernel-wide invariant re-established ----
            final(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
            // ---- Every held lock still matches lctx (thread now released) ----
            typed_lock_maps_aligned(final(self), final(lctx)),
            *final(self) == (KernelK { thr_mp: final(self).thr_mp, ..*old(self) }),
            // ---- thread_map: only the targeted entry's lock state changed (now unlocked) ----
            final(self).thr_mp.unchanged_except(&old(self).thr_mp, thread_ptr),
            final(self).thr_mp.perms_wf(),
            final(self).thr_mp.lock_id_by_key(thread_ptr) == old(self).thr_mp.lock_id_by_key(thread_ptr),
            wunlock_ensures(old(self).thr_mp.spec_index(thread_ptr), final(self).thr_mp.spec_index(thread_ptr)),
            // ---- LocalContext: lock dropped; thread preserved ----
            // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
            // `unlock_ensures` transitions it Acquire -> Release (same trap as
            // the NOTE on wunlock_process / LockedArray::wunlock).
            final(lctx).kernel_view_locking_state() is Release,
            unlock_ensures(old(lctx), final(lctx), KernelObjId::Thread(thread_ptr), old(self).thr_mp.lock_id_by_key(thread_ptr)),
    {
        proof {
            assert({ &&& old(self).thr_mp.perms_wf() &&& old(self).thr_mp.spec_index(thread_ptr).inv() }) by { thread_perms_wf_map(old(self).thr_mp); thread_perms_wf_at(old(self).thr_mp, thread_ptr); };
            assert(old(lctx).lock_entry_contains(old(self).thr_mp.lock_id_by_key(thread_ptr), KernelObjId::Thread(thread_ptr))) by { reveal(LockedMap::typed_lock_map_aligned); };
        }
        assert(self.thr_mp.spec_index(thread_ptr).wlocked_by(&*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
        self.thr_mp.wunlock(thread_ptr, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::Thread(thread_ptr)));
        proof {
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by {
                broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
            };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
            wunlock_thread_eof(*old(self), *self, thread_ptr);
        }
    }

    /// Record the running syscall's progress on its write-locked thread.
    pub fn set_thread_syscall_progress(&mut self, thread_ptr: RwLockThreadPtr, progress: Ghost<Option<SyscallProgress>>, Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&LockPerm>)
        requires
            old(self).inv(),
            old(self).thr_mp.dom().contains(thread_ptr),
            typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == lctx.thread_id(),
            lock_perm.view().lock_id() == old(self).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            old(self).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitZombie) ==> progress.view() == Some(SyscallProgress::ThreadExitZombie),
            typed_lock_maps_aligned(old(self), lctx),
        ensures
            final(self).inv(),
            typed_lock_maps_aligned(final(self), lctx),
            *final(self) == (KernelK { thr_mp: final(self).thr_mp, ..*old(self) }),
            final(self).thr_mp.unchanged_except(&old(self).thr_mp, thread_ptr),
            final(self).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: progress, ..old(self).thr_mp.spec_index(thread_ptr).view() }),
            final(self).thr_mp.spec_index(thread_ptr).locking_thread() == old(self).thr_mp.spec_index(thread_ptr).locking_thread(),
            final(self).thr_mp.spec_index(thread_ptr).being_killed() == old(self).thr_mp.spec_index(thread_ptr).being_killed(),
            final(self).thr_mp.lock_id_by_key(thread_ptr) == old(self).thr_mp.lock_id_by_key(thread_ptr),
    {
        assert(self.thr_mp.perms_wf() && self.thr_mp.spec_index(thread_ptr).is_init()) by { thread_perms_wf_map(self.thr_mp); thread_perms_wf_at(self.thr_mp, thread_ptr); };
        {
            let thread = self.thr_mp.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), lock_perm);
            thread.syscall_progress = progress;
        }
        proof {
            assert(typed_lock_maps_aligned(self, lctx) && self.thr_mp.lock_id_by_key(thread_ptr) == old(self).thr_mp.lock_id_by_key(thread_ptr)) by { lock_id_fields_eq_imply_eq(); };
            set_thread_syscall_progress_eof(*old(self), *self, *lctx, thread_ptr, progress);
        }
    }
}
} // verus!
