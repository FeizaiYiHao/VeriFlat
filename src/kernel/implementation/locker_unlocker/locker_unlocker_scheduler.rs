#[cfg(verus_keep_ghost)]
use super::locker_unlocker_scheduler_eof::{scheduler_shard_lock_op_eof};
use vstd::prelude::*;
use vstd::assert_seqs_equal;
use crate::*;

verus! {
impl KernelK {
    /// Shards of one scheduler are locked in ascending cpu id; shards of different schedulers
    /// are never held together with an equal or higher cpu id.
    pub fn wlock_scheduler_shard(&mut self, scheduler_ptr: RwLockSchedulerPtr, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).sched_mp.dom().contains(scheduler_ptr),
            index_valid(NUM_CPUS, cpu_id),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(self).pg_arr.spec_index(held_page).view().view().orders_below_allocator_locks(),
            forall|held_thread: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(held_thread)] old(lctx).thread_lock_map().dom().contains(held_thread)
                ==> !(old(self).thr_mp.spec_index(held_thread).view().state is SCHEDULED) || old(self).thr_mp.spec_index(held_thread).being_killed(),
            forall|held_scheduler: RwLockSchedulerPtr, held_cpu: CpuId| #![trigger old(lctx).scheduler_lock_map().dom().contains((held_scheduler, held_cpu))] old(lctx).scheduler_lock_map().dom().contains((held_scheduler, held_cpu)) ==> held_cpu < cpu_id,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            *final(self) == (KernelK { sched_mp: final(self).sched_mp, ..*old(self) }),
            final(self).sched_mp.unchanged_except(&old(self).sched_mp, scheduler_ptr),
            final(self).sched_mp.spec_index(scheduler_ptr).inv(),
            final(self).sched_mp.spec_index(scheduler_ptr).owning_container == old(self).sched_mp.spec_index(scheduler_ptr).owning_container,
            final(self).sched_mp.spec_index(scheduler_ptr).shards.unchanged_except(&old(self).sched_mp.spec_index(scheduler_ptr).shards, cpu_id),
            final(self).sched_mp.spec_index(scheduler_ptr).shards.lock_id_by_index(cpu_id) == old(self).sched_mp.spec_index(scheduler_ptr).shards.lock_id_by_index(cpu_id),
            scheduler_shards_of(final(self).sched_mp.spec_index(scheduler_ptr)) == scheduler_shards_of(old(self).sched_mp.spec_index(scheduler_ptr)),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            wlock_ensures(old(self).sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view(), final(self).sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view(),
                old(self).sched_mp.spec_index(scheduler_ptr).shards.lock_id_by_index(cpu_id), final(lctx), ret.view()),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::SchedulerShard(scheduler_ptr, cpu_id),
                TypedHeldLock { lock_id: final(self).sched_mp.spec_index(scheduler_ptr).shards.lock_id_by_index(cpu_id), mode: TypedLockMode::Write }),
    {
        proof {
            scheduler_perms_wf_map(old(self).sched_mp);
            scheduler_perms_wf_at(old(self).sched_mp, scheduler_ptr);
            assert(old(lctx).lock_id_acyclic(old(self).sched_mp.spec_index(scheduler_ptr).shards.lock_id_by_index(cpu_id))) by {
                reveal(LocalContext::lock_id_acyclic); reveal(pagetable_window_typed_lock_map_aligned); reveal(UnLockedMap::typed_shard_lock_map_aligned); reveal(UnLockedMap::typed_flag_lock_map_aligned); reveal(iommu_root_table_typed_lock_map_aligned);
                reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned);
            };
            assert(!old(self).sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locked_by_thread(old(lctx).thread_id())) by { reveal(UnLockedMap::typed_shard_lock_map_aligned); };
        }
        let ret = self.sched_mp.wlock_shard(scheduler_ptr, cpu_id, Tracked(&mut *lctx));
        proof {
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(UnLockedMap::typed_shard_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
            assert(scheduler_shards_of(self.sched_mp.spec_index(scheduler_ptr)) == scheduler_shards_of(old(self).sched_mp.spec_index(scheduler_ptr))) by {
                reveal(scheduler_shards_of);
                assert_seqs_equal!(scheduler_shards_of(self.sched_mp.spec_index(scheduler_ptr)) == scheduler_shards_of(old(self).sched_mp.spec_index(scheduler_ptr)));
            };
            scheduler_shard_lock_op_eof(*old(self), *self, scheduler_ptr, cpu_id);
        }
        ret
    }

    pub fn wunlock_scheduler_shard(&mut self, scheduler_ptr: RwLockSchedulerPtr, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).sched_mp.dom().contains(scheduler_ptr),
            index_valid(NUM_CPUS, cpu_id),
            typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (scheduler_ptr, cpu_id), TypedLockMode::Write),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            *final(self) == (KernelK { sched_mp: final(self).sched_mp, ..*old(self) }),
            final(self).sched_mp.unchanged_except(&old(self).sched_mp, scheduler_ptr),
            final(self).sched_mp.spec_index(scheduler_ptr).inv(),
            final(self).sched_mp.spec_index(scheduler_ptr).owning_container == old(self).sched_mp.spec_index(scheduler_ptr).owning_container,
            final(self).sched_mp.spec_index(scheduler_ptr).shards.unchanged_except(&old(self).sched_mp.spec_index(scheduler_ptr).shards, cpu_id),
            final(self).sched_mp.spec_index(scheduler_ptr).shards.lock_id_by_index(cpu_id) == old(self).sched_mp.spec_index(scheduler_ptr).shards.lock_id_by_index(cpu_id),
            !final(self).sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locked(),
            forall|s: RwLockSchedulerPtr| #![trigger scheduler_shards_of(final(self).sched_mp.spec_index(s))]
                old(self).sched_mp.dom().contains(s) ==> scheduler_shards_of(final(self).sched_mp.spec_index(s)) == scheduler_shards_of(old(self).sched_mp.spec_index(s)),
            // NOTE: `unlock_ensures` flips the locking phase Acquire → Release.
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            wunlock_ensures(old(self).sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view(), final(self).sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view()),
            typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::SchedulerShard(scheduler_ptr, cpu_id)),
            unlock_ensures(old(lctx), final(lctx), KernelObjId::SchedulerShard(scheduler_ptr, cpu_id), old(self).sched_mp.spec_index(scheduler_ptr).shards.lock_id_by_index(cpu_id)),
    {
        proof {
            scheduler_perms_wf_map(old(self).sched_mp);
            scheduler_perms_wf_at(old(self).sched_mp, scheduler_ptr);
            assert(old(lctx).lock_entry_contains(old(self).sched_mp.spec_index(scheduler_ptr).shards.lock_id_by_index(cpu_id), KernelObjId::SchedulerShard(scheduler_ptr, cpu_id))) by { reveal(UnLockedMap::typed_shard_lock_map_aligned); };
            assert(old(self).sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().wlocked_by(old(lctx))) by { reveal(UnLockedMap::typed_shard_lock_map_aligned); };
        }
        self.sched_mp.wunlock_shard(scheduler_ptr, cpu_id, Tracked(&mut *lctx), lock_perm);
        proof {
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(UnLockedMap::typed_shard_lock_map_aligned); };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
            assert(scheduler_shards_of(self.sched_mp.spec_index(scheduler_ptr)) == scheduler_shards_of(old(self).sched_mp.spec_index(scheduler_ptr))) by {
                reveal(scheduler_shards_of);
                assert_seqs_equal!(scheduler_shards_of(self.sched_mp.spec_index(scheduler_ptr)) == scheduler_shards_of(old(self).sched_mp.spec_index(scheduler_ptr)));
            };
            scheduler_shard_lock_op_eof(*old(self), *self, scheduler_ptr, cpu_id);
        }
    }
}
} // verus!
