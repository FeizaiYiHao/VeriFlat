use vstd::prelude::*;
use vstd::assert_seqs_equal;
use crate::*;

verus! {
impl KernelK {
    pub fn wlock_cpu_offline_flag(
        &mut self,
        flags_ptr: RwLockCpuOfflineFlagsPtr,
        cpu_id: CpuId,
        Tracked(lctx): Tracked<&mut LocalContext>,
    ) -> (ret: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).cpu_offline_mp.dom().contains(flags_ptr),
            index_valid(NUM_CPUS, cpu_id),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
            old(lctx).held_lock_majors_lt(CPU_OFFLINE_FLAG_LOCK_MAJOR),
            typed_lock_maps_aligned(old(self), old(lctx)),
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
            final(self).cpu_offline_mp.spec_index(flags_ptr).flags.unchanged_except(&old(self).cpu_offline_mp.spec_index(flags_ptr).flags, cpu_id),
            final(self).cpu_offline_mp.spec_index(flags_ptr).flags.lock_id_by_index(cpu_id) == old(self).cpu_offline_mp.spec_index(flags_ptr).flags.lock_id_by_index(cpu_id),
            cpu_offline_requests_of(final(self).cpu_offline_mp.spec_index(flags_ptr)) == cpu_offline_requests_of(old(self).cpu_offline_mp.spec_index(flags_ptr)),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            wlock_ensures(old(self).cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view(), final(self).cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view(), old(self).cpu_offline_mp.spec_index(flags_ptr).flags.lock_id_by_index(cpu_id), final(lctx), ret.view()),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::CpuOfflineFlag(flags_ptr, cpu_id), TypedHeldLock { lock_id: final(self).cpu_offline_mp.spec_index(flags_ptr).flags.lock_id_by_index(cpu_id), mode: TypedLockMode::Write }),
    {
        proof {
            assert(old(self).cpu_offline_mp.perms_wf() && old(self).cpu_offline_mp.spec_index(flags_ptr).inv()) by { reveal(cpu_offline_flags_wf); };
            assert(old(lctx).lock_id_acyclic(old(self).cpu_offline_mp.spec_index(flags_ptr).flags.lock_id_by_index(cpu_id))) by { reveal(LocalContext::lock_id_acyclic); };
            assert(!old(self).cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view().locked_by_thread(old(lctx).thread_id())) by { reveal(UnLockedMap::typed_flag_lock_map_aligned); };
            assert(wlock_requires(self.cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view(), &*lctx)) by { reveal(UnLockedMap::typed_flag_lock_map_aligned); };
        }
        let ret = self.cpu_offline_mp.wlock_flag(flags_ptr, cpu_id, Tracked(&mut *lctx));
        proof {
            assert(cpu_offline_flags_wf(self.cpu_offline_mp, self.cpu_arr)) by { reveal(cpu_offline_flags_wf); };
            assert(container_cpu_offline_flags_wf(self.ctn_mp, self.cpu_offline_mp)) by { reveal(container_cpu_offline_flags_wf); };
            assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(UnLockedMap::typed_flag_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
            assert(cpu_offline_requests_of(self.cpu_offline_mp.spec_index(flags_ptr)) == cpu_offline_requests_of(old(self).cpu_offline_mp.spec_index(flags_ptr))) by {
                reveal(cpu_offline_requests_of);
                assert_seqs_equal!(cpu_offline_requests_of(self.cpu_offline_mp.spec_index(flags_ptr)) == cpu_offline_requests_of(old(self).cpu_offline_mp.spec_index(flags_ptr)));
            };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_cpu_offline_flags_wf); };
        }
        ret
    }

    pub fn wunlock_cpu_offline_flag(
        &mut self,
        flags_ptr: RwLockCpuOfflineFlagsPtr,
        cpu_id: CpuId,
        Tracked(lctx): Tracked<&mut LocalContext>,
        lock_perm: Tracked<LockPerm>,
    )
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
            final(self).cpu_offline_mp.spec_index(flags_ptr).flags.unchanged_except(&old(self).cpu_offline_mp.spec_index(flags_ptr).flags, cpu_id),
            cpu_offline_requests_of(final(self).cpu_offline_mp.spec_index(flags_ptr)) == cpu_offline_requests_of(old(self).cpu_offline_mp.spec_index(flags_ptr)),
            final(lctx).thread_id() == old(lctx).thread_id(),
            wunlock_ensures(old(self).cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view(), final(self).cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view()),
            unlock_ensures(old(lctx), final(lctx), KernelObjId::CpuOfflineFlag(flags_ptr, cpu_id), old(self).cpu_offline_mp.spec_index(flags_ptr).flags.lock_id_by_index(cpu_id)),
    {
        proof {
            assert(old(self).cpu_offline_mp.perms_wf() && old(self).cpu_offline_mp.spec_index(flags_ptr).inv()) by { reveal(cpu_offline_flags_wf); };
            assert(old(lctx).lock_entry_contains(old(self).cpu_offline_mp.spec_index(flags_ptr).flags.lock_id_by_index(cpu_id), KernelObjId::CpuOfflineFlag(flags_ptr, cpu_id))) by { reveal(UnLockedMap::typed_flag_lock_map_aligned); };
            assert(old(self).cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view().wlocked_by(old(lctx))) by { reveal(UnLockedMap::typed_flag_lock_map_aligned); };
        }
        self.cpu_offline_mp.wunlock_flag(flags_ptr, cpu_id, Tracked(&mut *lctx), lock_perm);
        proof {
            assert(cpu_offline_flags_wf(self.cpu_offline_mp, self.cpu_arr)) by { reveal(cpu_offline_flags_wf); };
            assert(container_cpu_offline_flags_wf(self.ctn_mp, self.cpu_offline_mp)) by { reveal(container_cpu_offline_flags_wf); };
            assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(UnLockedMap::typed_flag_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
            assert(cpu_offline_requests_of(self.cpu_offline_mp.spec_index(flags_ptr)) == cpu_offline_requests_of(old(self).cpu_offline_mp.spec_index(flags_ptr))) by {
                reveal(cpu_offline_requests_of);
                assert_seqs_equal!(cpu_offline_requests_of(self.cpu_offline_mp.spec_index(flags_ptr)) == cpu_offline_requests_of(old(self).cpu_offline_mp.spec_index(flags_ptr)));
            };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_cpu_offline_flags_wf); };
        }
    }
}
}
