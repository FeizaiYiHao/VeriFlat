use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
    pub fn wlock_pcid_allocator(
        &mut self,
        allocator_ptr: RwLockPcidAllocatorPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
    ) -> (ret: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).pcid_allc_mp.dom().contains(allocator_ptr),
            old(lctx).kernel_view_locking_state() is Acquire,
            !typed_lock_map_contains_mode(old(lctx).pcid_allocator_lock_map(), allocator_ptr, TypedLockMode::Write),
            {
                let cpus = old(lctx).cpu_lock_map().dom();
                let container_ptr = old(self).pcid_allc_mp.spec_index(allocator_ptr).view().owning_container.view();
                &&& !cpus.is_empty()
                &&& old(lctx).page_lock_map().dom().is_empty()
                &&& old(lctx).container_lock_map().dom() =~= set![container_ptr]
                &&& old(lctx).process_lock_map().dom().is_empty()
                &&& old(lctx).thread_lock_map().dom().is_empty()
                &&& old(lctx).endpoint_lock_map().dom().is_empty()
                &&& old(lctx).scheduler_lock_map().dom().is_empty()
                &&& old(lctx).pcid_allocator_lock_map().dom().is_empty()
                &&& old(lctx).cpu_set_lock_map().dom().is_empty()
                &&& old(lctx).pagetable_lock_map().dom().is_empty()
                &&& old(lctx).iommu_table_lock_map().dom().is_empty()
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
                &&& (forall|held_cpu_id: CpuId|
                    #![trigger cpus.contains(held_cpu_id)]
                    cpus.contains(held_cpu_id) ==> {
                        &&& index_valid(NUM_CPUS, held_cpu_id)
                        &&& old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().owning_container == container_ptr
                        &&& !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off)
                    })
            },
            typed_lock_maps_aligned(old(self), old(lctx)),
            lock_id_set_aligned(old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(self).inv(),
            kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            *final(self) == (KernelK { pcid_allc_mp: final(self).pcid_allc_mp, ..*old(self) }),
            final(self).pcid_allc_mp.unchanged_except(&old(self).pcid_allc_mp, allocator_ptr),
            final(self).pcid_allc_mp.perms_wf(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            wlock_ensures(old(self).pcid_allc_mp.spec_index(allocator_ptr), final(self).pcid_allc_mp.spec_index(allocator_ptr), old(self).pcid_allc_mp.lock_id_by_key(allocator_ptr), final(lctx), ret.view()),
            final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(self).pcid_allc_mp.lock_id_by_key(allocator_ptr), KernelObjId::PcidAllocator(allocator_ptr))),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::PcidAllocator(allocator_ptr), TypedHeldLock { lock_id: final(self).pcid_allc_mp.lock_id_by_key(allocator_ptr), mode: TypedLockMode::Write }),
            final(lctx).held_lock_majors_lt(PROCESS_LOCK_MAJOR),
    {
        proof {
            assert(old(self).subsystems_inv());
            pcid_allocator_perms_wf_at(
                old(self).pcid_allc_mp,
                allocator_ptr,
            );
            assert(old(lctx).held_lock_majors_lt(PCID_ALLOCATOR_LOCK_MAJOR)) by { reveal(lock_id_set_aligned); reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned); reveal(cpu_array_wf); reveal(container_perms_wf); };
            assert(old(lctx).lock_id_acyclic(old(self).pcid_allc_mp.lock_id_by_key(allocator_ptr))) by { reveal(lock_id_set_aligned); reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned); reveal(container_cpu_wf); reveal(container_pcid_allocator_wf); reveal(container_perms_wf); };
            assert(!old(self).pcid_allc_mp.spec_index(allocator_ptr)
                .wlocked_by_thread(old(lctx).thread_id())) by {
                if old(self).pcid_allc_mp.spec_index(allocator_ptr)
                    .wlocked_by_thread(old(lctx).thread_id())
                {
                    assert(typed_lock_map_contains_mode(
                        old(lctx).pcid_allocator_lock_map(),
                        allocator_ptr,
                        TypedLockMode::Write,
                    )) by {
                        reveal(typed_lock_maps_aligned);
                        reveal(LockedMap::typed_lock_map_aligned);
                    };
                }
            };
            assert(!old(self).pcid_allc_mp.spec_index(allocator_ptr)
                .wlocked_by(&*old(lctx))) by {
                reveal(RwLock::wlocked_by);
                reveal(RwLock::wlocked_by_thread);
            };
        }
        assert(wlock_requires(self.pcid_allc_mp.spec_index(allocator_ptr), &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
        let ret = self.pcid_allc_mp.wlock(allocator_ptr, Tracked(&mut *lctx), Ghost(KernelObjId::PcidAllocator(allocator_ptr)));
        proof {
            assert(pcid_allocator_perms_wf(self.pcid_allc_mp)) by { reveal(pcid_allocator_perms_wf); };
            assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
            assert(self.memory_management_inv()) by { reveal(pcid_allocator_pages_wf); };
            assert(self.process_management_inv()) by { reveal(container_pcid_allocator_wf); reveal(process_pcid_allocator_wf); };
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(lctx.held_lock_majors_lt(PROCESS_LOCK_MAJOR)) by { reveal(pcid_allocator_perms_wf); assert(PCID_ALLOCATOR_LOCK_MAJOR < PROCESS_LOCK_MAJOR) by (compute); broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different; };
            assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
        }
        ret
    }

    pub fn wunlock_pcid_allocator(
        &mut self,
        allocator_ptr: RwLockPcidAllocatorPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
        lock_perm: Tracked<LockPerm>,
    )
        requires
            old(self).inv(),
            old(self).pcid_allc_mp.dom().contains(allocator_ptr),
            typed_lock_map_contains_mode(old(lctx).pcid_allocator_lock_map(), allocator_ptr, TypedLockMode::Write),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).pcid_allc_mp.spec_index(allocator_ptr).locking_thread()->Write_lock_id,
            typed_lock_maps_aligned(old(self), old(lctx)),
            lock_id_set_aligned(old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(self).inv(),
            kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            *final(self) == (KernelK { pcid_allc_mp: final(self).pcid_allc_mp, ..*old(self) }),
            final(self).pcid_allc_mp.unchanged_except(&old(self).pcid_allc_mp, allocator_ptr),
            final(self).pcid_allc_mp.perms_wf(),
            final(self).pcid_allc_mp.spec_index(allocator_ptr).locking_thread() is None,
            !final(self).pcid_allc_mp.spec_index(allocator_ptr).locked(),
            final(self).pcid_allc_mp.lock_id_by_key(allocator_ptr) == old(self).pcid_allc_mp.lock_id_by_key(allocator_ptr),
            wunlock_ensures(old(self).pcid_allc_mp.spec_index(allocator_ptr), final(self).pcid_allc_mp.spec_index(allocator_ptr)),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).lock_id_set() == old(lctx).lock_id_set().remove((old(self).pcid_allc_mp.lock_id_by_key(allocator_ptr), KernelObjId::PcidAllocator(allocator_ptr))),
            typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::PcidAllocator(allocator_ptr)),
            unlock_ensures(old(lctx), final(lctx), KernelObjId::PcidAllocator(allocator_ptr), old(self).pcid_allc_mp.lock_id_by_key(allocator_ptr)),
    {
        proof {
            assert({ &&& old(self).pcid_allc_mp.perms_wf() &&& old(self).pcid_allc_mp.spec_index(allocator_ptr).inv() }) by { reveal(pcid_allocator_perms_wf); };
            assert(old(lctx).lock_entry_contains(old(self).pcid_allc_mp.lock_id_by_key(allocator_ptr), KernelObjId::PcidAllocator(allocator_ptr))) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(old(lctx).lock_id_set().contains((old(self).pcid_allc_mp.lock_id_by_key(allocator_ptr), KernelObjId::PcidAllocator(allocator_ptr)))) by { reveal(lock_id_set_aligned); };
        }
        assert(self.pcid_allc_mp.spec_index(allocator_ptr).wlocked_by(&*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
        self.pcid_allc_mp.wunlock(allocator_ptr, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::PcidAllocator(allocator_ptr)));
        proof {
            assert(pcid_allocator_perms_wf(self.pcid_allc_mp)) by { reveal(pcid_allocator_perms_wf); };
            assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
            assert(self.memory_management_inv()) by { reveal(pcid_allocator_pages_wf); };
            assert(self.process_management_inv()) by { reveal(container_pcid_allocator_wf); reveal(process_pcid_allocator_wf); };
            assert(typed_lock_maps_aligned(self, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self); };
        }
    }
}
} // verus!
