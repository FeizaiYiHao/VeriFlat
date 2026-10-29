#[cfg(verus_keep_ghost)]
use super::locker_unlocker_cpu_eof::{wlock_cpu_eof, wunlock_cpu_eof, wunlock_own_cpu_eof};
use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
    /// Write-lock the own cpu `cpu_id` unless a killer marked it, and enter its kernel step; a marked cpu returns `None` at
    /// once and nothing changes. The lock records this cpu as its holder, the cpu's kernel-call permission moves from the
    /// cpu object into the local context, and its running state becomes InStep.
    pub fn wlock_own_cpu(&mut self, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Option<Tracked<LockPerm>>)
        requires
            old(self).inv(),
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            old(lctx).kernel_view_locking_state() is Acquire,
            !old(lctx).cpu_lock_map().dom().contains(cpu_id),
            old(lctx).no_locks_held(),
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            (ret is None) == old(self).cpu_arr.spec_index(cpu_id).view().being_killed(),
            ret is None ==> *final(self) == *old(self) && *final(lctx) == *old(lctx),
            ret is Some ==> final(self).cpu_hw_cr3_pcid[cpu_id as int].view() == (final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            final(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            *final(self) == (KernelK { cpu_arr: final(self).cpu_arr, cpu_op: final(self).cpu_op, ..*old(self) }),
            ret is Some ==> final(self).cpu_op.view().view() == old(self).cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
            final(self).cpu_arr.entries_unchanged_except(&old(self).cpu_arr, cpu_id),
            final(self).cpu_arr.spec_index(cpu_id).view().view().view() == old(self).cpu_arr.spec_index(cpu_id).view().view().view(),
            final(self).cpu_arr.inv(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            ret is Some ==> final(lctx).kernel_call_perm() == Some(cpu_id),
            ret is Some ==> {
                let pre = old(self).cpu_arr.spec_index(cpu_id).view();
                let post = final(self).cpu_arr.spec_index(cpu_id).view();
                let perm = ret->Some_0.view();
                &&& post.wlocked_by(final(lctx))
                &&& post.locking_thread() == RwLockState::Write { thread_id: final(lctx).thread_id(), lock_id: perm.lock_id() }
                &&& post.inv()
                &&& post.view().kernel_call_perm() is None
                &&& post.view_rodata() == pre.view_rodata()
                &&& post.view_ghost() == Some(cpu_id)
                &&& post.being_killed() == pre.being_killed()
                &&& post.killer_info() == pre.killer_info()
                &&& post.control() == pre.control()
                &&& pre.locked() == false
                &&& perm.state() is WriteLock
                &&& post.locking_thread()->Write_lock_id == perm.lock_id()
                &&& perm.ordering_lock_id() == old(self).cpu_arr.lock_id_by_index(cpu_id)
                &&& perm.thread_id() == final(lctx).thread_id()
            },
            ret is Some ==> typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Cpu(cpu_id), TypedHeldLock { lock_id: final(self).cpu_arr.lock_id_by_index(cpu_id), mode: TypedLockMode::Write }),
    {
        proof {
            assert(old(self).cpu_arr.inv() && old(self).cpu_arr.spec_index(cpu_id).view().inv()) by { cpu_array_wf_map(old(self).cpu_arr, old(self).dflt_pt.view()); cpu_array_wf_at(old(self).cpu_arr, old(self).dflt_pt.view(), cpu_id); };
            assert(old(lctx).lock_id_acyclic(old(self).cpu_arr.lock_id_by_index(cpu_id))) by { reveal(LocalContext::lock_id_acyclic); };
            cpu_op_wf_at(old(self).cpu_op.view().view(), old(self).cpu_arr, cpu_id);
        }
        assert(wlock_requires(self.cpu_arr.spec_index(cpu_id).view(), &*lctx)) by { reveal(LockedArray::typed_lock_map_aligned); };
        let ret = self.cpu_arr.wlock_own_cpu_enter_step(cpu_id, Tracked(self.cpu_op.borrow_mut()), Tracked(&mut *lctx));
        if ret.is_none() {
            proof {
                assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by {
                    broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
                    reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
                };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
            }
            return ret;
        }
        proof {
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedArray::typed_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by {
                broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
            };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
            wlock_cpu_eof(*old(self), *self, cpu_id, cpu_id, true);
        }
        ret
    }

    /// Write-lock the remote cpu `cpu_id` unless a killer marked it; a marked cpu returns `None` at once and nothing
    /// changes. The lock records this thread's cpu as its holder.
    pub fn wlock_cpu(&mut self, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Option<Tracked<LockPerm>>)
        requires
            old(self).inv(),
            index_valid(NUM_CPUS, cpu_id),
            cpu_id != old(lctx).cpu_id(),
            !(old(self).cpu_arr.spec_index(cpu_id).view().view().view().state is Off),
            old(lctx).kernel_view_locking_state() is Acquire,
            !old(lctx).cpu_lock_map().dom().contains(cpu_id),
            old(lctx).no_locks_held() || {
                let cpu = old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view();
                let target = old(self).cpu_arr.spec_index(cpu_id).view().view().view();
                &&& killer_held_context(*old(self), *old(lctx), cpu.current_process->Some_0, cpu.current_thread->Some_0, old(lctx).container_lock_map().dom())
                &&& target.state is Running || target.state is Idle
                &&& target.container_depth > cpu.container_depth || (target.state is Running && target.container_depth == cpu.container_depth && target.process_depth > cpu.process_depth
                    && !old(lctx).container_lock_map().dom().contains(cpu.owning_container))
            },
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            (ret is None) == old(self).cpu_arr.spec_index(cpu_id).view().being_killed(),
            ret is None ==> *final(self) == *old(self) && *final(lctx) == *old(lctx),
            ret is Some ==> final(self).cpu_hw_cr3_pcid[cpu_id as int].view() == (final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            // ---- Kernel-wide invariant re-established ----
            final(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
            // ---- Every held lock still matches lctx (cpu now locked) ----
            // ---- Dynamic lock ids remain aligned ----
            typed_lock_maps_aligned(final(self), final(lctx)),
            // ---- Field framing: only the target cpu slot moves ----
            *final(self) == (KernelK { cpu_arr: final(self).cpu_arr, ..*old(self) }),
            // ---- cpu_array: only the targeted slot changed; the cpu object is untouched ----
            final(self).cpu_arr.entries_unchanged_except(&old(self).cpu_arr, cpu_id),
            final(self).cpu_arr.spec_index(cpu_id).view().view().view() == old(self).cpu_arr.spec_index(cpu_id).view().view().view(),
            final(self).cpu_arr.unchanged_except(&old(self).cpu_arr, cpu_id),
            final(self).cpu_arr.inv(),
            // ---- LocalContext: phases preserved ----
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            // ---- The lock: `wlock_ensures` with this cpu recorded as holder ----
            ret is Some ==> {
                let pre = old(self).cpu_arr.spec_index(cpu_id).view();
                let post = final(self).cpu_arr.spec_index(cpu_id).view();
                let perm = ret->Some_0.view();
                &&& post.wlocked_by(final(lctx))
                &&& post.locking_thread() == RwLockState::Write { thread_id: final(lctx).thread_id(), lock_id: perm.lock_id() }
                &&& post.inv()
                &&& post.view() == pre.view()
                &&& post.view_rodata() == pre.view_rodata()
                &&& post.view_ghost() == Some(old(lctx).cpu_id())
                &&& post.being_killed() == pre.being_killed()
                &&& post.killer_info() == pre.killer_info()
                &&& post.control() == pre.control()
                &&& pre.locked() == false
                &&& perm.state() is WriteLock
                &&& post.locking_thread()->Write_lock_id == perm.lock_id()
                &&& perm.ordering_lock_id() == old(self).cpu_arr.lock_id_by_index(cpu_id)
                &&& perm.thread_id() == final(lctx).thread_id()
            },
            ret is Some ==> typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Cpu(cpu_id), TypedHeldLock { lock_id: final(self).cpu_arr.lock_id_by_index(cpu_id), mode: TypedLockMode::Write }),
    {
        proof {
            assert(old(self).cpu_arr.inv() && old(self).cpu_arr.spec_index(cpu_id).view().inv()) by { cpu_array_wf_map(old(self).cpu_arr, old(self).dflt_pt.view()); cpu_array_wf_at(old(self).cpu_arr, old(self).dflt_pt.view(), cpu_id); };
            assert(old(lctx).lock_id_acyclic(old(self).cpu_arr.lock_id_by_index(cpu_id))) by {
                reveal(LocalContext::lock_id_acyclic); reveal(pagetable_window_typed_lock_map_aligned);
                let cpu = old(self).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view();
                if killer_held_context(*old(self), *old(lctx), cpu.current_process->Some_0, cpu.current_thread->Some_0, old(lctx).container_lock_map().dom()) {
                    thread_cpu_wf_cpu_at(old(self).thr_mp, old(self).cpu_arr, old(lctx).cpu_id()); thread_cpu_wf_cpu_at(old(self).thr_mp, old(self).cpu_arr, cpu_id);
                    process_cpu_wf_at(old(self).prc_mp, old(self).cpu_arr, old(lctx).cpu_id()); container_cpu_wf_cpu_at(old(self).ctn_mp, old(self).cpu_set_mp, old(self).cpu_arr, old(lctx).cpu_id());
                    thread_perms_wf_at(old(self).thr_mp, cpu.current_thread->Some_0); process_thread_wf_at(old(self).prc_mp, old(self).thr_mp, cpu.current_thread->Some_0);
                    container_process_wf_process_at(old(self).ctn_mp, old(self).prc_mp, cpu.current_process->Some_0);
                    reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned);
                }
            };
        }
        assert(wlock_requires(self.cpu_arr.spec_index(cpu_id).view(), &*lctx)) by { reveal(LockedArray::typed_lock_map_aligned); };
        let ret = self.cpu_arr.wlock_unless_killed(cpu_id, Tracked(&mut *lctx), Ghost(KernelObjId::Cpu(cpu_id)));
        if ret.is_none() {
            proof {
                assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by {
                    broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
                    reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
                };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
            }
            return ret;
        }
        let Tracked(perm) = ret.unwrap();
        self.cpu_arr.set_ghost(cpu_id, Ghost(Some(lctx.cpu_id())), Tracked(&*lctx), Tracked(&perm));
        proof {
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedArray::typed_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by {
                broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
            };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
            wlock_cpu_eof(*old(self), *self, cpu_id, lctx.cpu_id(), false);
        }
        Some(Tracked(perm))
    }

    /// Acquire the terminal-major lock for a CPU already Off in a closed slot of the held CPU set; the lock records this
    /// thread's cpu as its holder.
    pub fn wlock_off_cpu(&mut self, cpu_id: CpuId, cpu_set_ptr: RwLockCpuSetPtr, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).inv(),
            index_valid(NUM_CPUS, cpu_id),
            old(self).cpu_set_mp.dom().contains(cpu_set_ptr),
            typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), cpu_set_ptr, TypedLockMode::Write),
            old(self).cpu_set_mp.spec_index(cpu_set_ptr).view().owned_cpus.closed_view().contains(cpu_id),
            forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            old(lctx).kernel_view_locking_state() is Acquire,
            !old(lctx).cpu_lock_map().dom().contains(cpu_id),
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(self).cpu_hw_cr3_pcid[cpu_id as int].view() == (final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            final(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            *final(self) == (KernelK { cpu_arr: final(self).cpu_arr, ..*old(self) }),
            final(self).cpu_arr.unchanged_except(&old(self).cpu_arr, cpu_id),
            final(self).cpu_arr.inv(),
            final(self).cpu_arr.view().len() == old(self).cpu_arr.view().len(),
            final(self).cpu_arr.spec_index(cpu_id).view().is_init() == old(self).cpu_arr.spec_index(cpu_id).view().is_init(),
            ({
                let pre = old(self).cpu_arr.spec_index(cpu_id).view();
                let post = final(self).cpu_arr.spec_index(cpu_id).view();
                &&& post.wlocked_by(final(lctx))
                &&& post.locking_thread() == RwLockState::Write { thread_id: final(lctx).thread_id(), lock_id: ret.view().lock_id() }
                &&& post.inv()
                &&& post.view() == pre.view()
                &&& post.view_rodata() == pre.view_rodata()
                &&& post.view_ghost() == Some(old(lctx).cpu_id())
                &&& post.being_killed() == pre.being_killed()
                &&& post.killer_info() == pre.killer_info()
                &&& post.control() == pre.control()
                &&& pre.locked() == false
                &&& ret.view().state() is WriteLock
                &&& post.locking_thread()->Write_lock_id == ret.view().lock_id()
                &&& ret.view().ordering_lock_id() == old(self).cpu_arr.lock_id_by_index(cpu_id)
                &&& ret.view().thread_id() == final(lctx).thread_id()
            }),
            lock_ensures(old(lctx), final(lctx), final(self).cpu_arr.lock_id_by_index(cpu_id), KernelObjId::Cpu(cpu_id)),
            final(self).cpu_arr.spec_index(cpu_id).view().view().view().state is Off,
            !final(self).cpu_arr.spec_index(cpu_id).view().being_killed(),
    {
        proof {
            assert(old(self).cpu_arr.inv() && old(self).cpu_arr.spec_index(cpu_id).view().inv()) by { cpu_array_wf_map(old(self).cpu_arr, old(self).dflt_pt.view()); cpu_array_wf_at(old(self).cpu_arr, old(self).dflt_pt.view(), cpu_id); };
            assert(old(self).cpu_arr.spec_index(cpu_id).view().view().view().state is Off) by {
                container_cpu_set_wf_cpu_set_at(old(self).ctn_mp, old(self).cpu_set_mp, cpu_set_ptr); cpu_set_perms_wf_at(old(self).cpu_set_mp, cpu_set_ptr);
                container_cpu_wf_container_at(old(self).ctn_mp, old(self).cpu_set_mp, old(self).cpu_arr, old(self).cpu_set_mp.spec_index(cpu_set_ptr).view().owning_container.view(), cpu_id);
            };
            assert(old(lctx).lock_id_acyclic(old(self).cpu_arr.lock_id_by_index(cpu_id))) by {
                reveal(LocalContext::lock_id_acyclic); reveal(pagetable_window_typed_lock_map_aligned); reveal(UnLockedMap::typed_flag_lock_map_aligned); reveal(iommu_root_table_typed_lock_map_aligned); reveal(UnLockedMap::typed_shard_lock_map_aligned);
                reveal(LockedArray::typed_lock_map_aligned); reveal(LockedArray2D::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned);
                reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned); reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
            };
        }
        assert(wlock_requires(self.cpu_arr.spec_index(cpu_id).view(), &*lctx)) by { reveal(LockedArray::typed_lock_map_aligned); };
        assert(!self.cpu_arr.spec_index(cpu_id).view().being_killed()) by { thread_cpu_wf_killed_cpu_at(self.thr_mp, self.cpu_arr, cpu_id); };
        let Tracked(perm) = self.cpu_arr.wlock_unless_killed(cpu_id, Tracked(&mut *lctx), Ghost(KernelObjId::Cpu(cpu_id))).unwrap();
        self.cpu_arr.set_ghost(cpu_id, Ghost(Some(lctx.cpu_id())), Tracked(&*lctx), Tracked(&perm));
        proof {
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedArray::typed_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by {
                broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
            };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
            wlock_cpu_eof(*old(self), *self, cpu_id, lctx.cpu_id(), false);
        }
        Tracked(perm)
    }

    /// Leave the kernel step of the own cpu `cpu_id` and release its lock: the cpu's running state becomes the resting state
    /// its scheduling state implies, its kernel-call permission goes back from the local context into the cpu object, and
    /// the holder record is cleared.
    pub fn wunlock_own_cpu(&mut self, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>)
        requires
            old(self).inv(),
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            old(self).cpu_op.view().view()[cpu_id as int] is InStep,
            old(self).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            typed_lock_maps_aligned(old(self), old(lctx)),
            old(self).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(self).cpu_hw_cr3_pcid[cpu_id as int].view() == (final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            final(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            *final(self) == (KernelK { cpu_arr: final(self).cpu_arr, cpu_op: final(self).cpu_op, ..*old(self) }),
            final(self).cpu_op.view().view() == old(self).cpu_op.view().view().update(cpu_id as int, cpu_op_after_step(old(self).cpu_arr.spec_index(cpu_id).view().view().view().state)),
            final(self).cpu_arr.entries_unchanged_except(&old(self).cpu_arr, cpu_id),
            final(self).cpu_arr.inv(),
            final(self).cpu_arr.lock_id_by_index(cpu_id) == old(self).cpu_arr.lock_id_by_index(cpu_id),
            ({
                let pre = old(self).cpu_arr.spec_index(cpu_id).view();
                let post = final(self).cpu_arr.spec_index(cpu_id).view();
                &&& post.locking_thread() == RwLockState::None
                &&& post.inv()
                &&& post.view().view() == pre.view().view()
                &&& post.view().kernel_call_perm() == Some(cpu_id)
                &&& post.view_rodata() == pre.view_rodata()
                &&& post.view_ghost() is None
                &&& post.being_killed() == pre.being_killed()
                &&& post.killer_info() == pre.killer_info()
                &&& post.control() == pre.control()
            }),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Cpu(cpu_id)),
            final(lctx).no_locks_held() ==> final(self).all_objects_unlocked(final(lctx)),
            final(lctx).kernel_call_perm() is None,
    {
        proof {
            assert(old(self).cpu_arr.inv()) by { cpu_array_wf_map(old(self).cpu_arr, old(self).dflt_pt.view()); };
            assert(old(lctx).lock_entry_contains(old(self).cpu_arr.lock_id_by_index(cpu_id), KernelObjId::Cpu(cpu_id))) by { reveal(LockedArray::typed_lock_map_aligned); };
        }
        assert(self.cpu_arr.spec_index(cpu_id).view().wlocked_by(&*lctx)) by { reveal(LockedArray::typed_lock_map_aligned); };
        self.cpu_arr.exit_step_wunlock_own_cpu(cpu_id, Tracked(self.cpu_op.borrow_mut()), Tracked(&mut *lctx), lock_perm);
        proof {
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedArray::typed_lock_map_aligned); };
            assert(lctx.no_locks_held() ==> self.all_objects_unlocked(lctx)) by { if lctx.no_locks_held() { no_locks_held_imply_all_objects_unlocked(&*self, &*lctx); } };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by {
                broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
            };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
            wunlock_own_cpu_eof(*old(self), *self, cpu_id);
        }
    }

    /// Release the remote cpu `cpu_id`, which this thread write-holds with its own cpu recorded as holder, and clear the
    /// holder record.
    pub fn wunlock_cpu(&mut self, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>)
        requires
            old(self).inv(),
            index_valid(NUM_CPUS, cpu_id),
            old(self).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            cpu_id != old(lctx).cpu_id(),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            typed_lock_maps_aligned(old(self), old(lctx)),
            old(self).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(self).cpu_hw_cr3_pcid[cpu_id as int].view() == (final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, final(self).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            // ---- Kernel-wide invariant re-established ----
            final(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
            // ---- Every held lock still matches lctx (cpu now released) ----
            // ---- Dynamic lock ids remain aligned ----
            typed_lock_maps_aligned(final(self), final(lctx)),
            // ---- Field framing: only cpu_array's lock state moves ----
            *final(self) == (KernelK { cpu_arr: final(self).cpu_arr, ..*old(self) }),
            // ---- cpu_array: only the targeted slot's lock state changed (now unlocked) ----
            final(self).cpu_arr.unchanged_except(&old(self).cpu_arr, cpu_id),
            final(self).cpu_arr.inv(),
            final(self).cpu_arr.lock_id_by_index(cpu_id) == old(self).cpu_arr.lock_id_by_index(cpu_id),
            ({
                let pre = old(self).cpu_arr.spec_index(cpu_id).view();
                let post = final(self).cpu_arr.spec_index(cpu_id).view();
                &&& post.locking_thread() == RwLockState::None
                &&& post.inv()
                &&& post.view() == pre.view()
                &&& post.view_rodata() == pre.view_rodata()
                &&& post.view_ghost() is None
                &&& post.being_killed() == pre.being_killed()
                &&& post.killer_info() == pre.killer_info()
                &&& post.control() == pre.control()
            }),
            // ---- LocalContext: lock dropped; thread preserved ----
            // NOTE: do NOT assert `kernel_view_locking_state() == old` here —
            // `unlock_ensures` transitions it Acquire -> Release, so restating
            // `== old` would contradict it and make the postcondition `false`
            // in an Acquire section. `unlock_ensures` is the source of truth
            // for the phase transition (same trap as the NOTE on
            // `LockedArray::wunlock`). user_view is separately preserved.
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Cpu(cpu_id)),
            final(lctx).no_locks_held() ==> final(self).all_objects_unlocked(final(lctx)),
            final(lctx).kernel_call_perm() == old(lctx).kernel_call_perm(),
    {
        proof {
            assert(old(self).cpu_arr.inv()) by { cpu_array_wf_map(old(self).cpu_arr, old(self).dflt_pt.view()); };
            assert(old(lctx).lock_entry_contains(old(self).cpu_arr.lock_id_by_index(cpu_id), KernelObjId::Cpu(cpu_id))) by { reveal(LockedArray::typed_lock_map_aligned); };
            cpu_op_wf_at(old(self).cpu_op.view().view(), old(self).cpu_arr, cpu_id);
        }
        assert(self.cpu_arr.spec_index(cpu_id).view().wlocked_by(&*lctx)) by { reveal(LockedArray::typed_lock_map_aligned); };
        let Tracked(lock_perm) = lock_perm;
        self.cpu_arr.set_ghost(cpu_id, Ghost(None), Tracked(&*lctx), Tracked(&lock_perm));
        let tracked slot = lctx.take_kernel_call_perm();
        self.cpu_arr.wunlock(cpu_id, Tracked(&mut *lctx), Tracked(lock_perm), Ghost(KernelObjId::Cpu(cpu_id)));
        proof {
            lctx.put_kernel_call_perm(slot);
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedArray::typed_lock_map_aligned); };
            assert(lctx.no_locks_held() ==> self.all_objects_unlocked(lctx)) by { if lctx.no_locks_held() { no_locks_held_imply_all_objects_unlocked(&*self, &*lctx); } };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by {
                broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
            };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
            wunlock_cpu_eof(*old(self), *self, cpu_id);
        }
    }
}
} // verus!
