#[cfg(verus_keep_ghost)]
use super::locker_unlocker_pagetable_window_eof::{lock_pagetable_window_eof, unlock_pagetable_window_eof, lock_pagetable_window_eof_transition_framing, unlock_pagetable_window_eof_transition_framing};
use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
    /// Lock 2M window `(l4i, l3i, l2i)` of page table `root`, whose big lock this thread holds in either mode through
    /// `big`; a write-held table's ghost slot follows the new window half, every other window keeps its view, and under
    /// a read-held table the window's leaves are present and it lists no stale CPU.
    pub fn lock_pagetable_window(&mut self, root: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, Tracked(big): Tracked<&LockPerm>,
        Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).pt_mp.dom().contains(root),
            pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).kernel_l4_end() <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
            page_table_key_2m_valid::<PT_TYPE>(spec_index2va((l4i, l3i, l2i, 0))),
            pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).window_exists(l4i, l3i),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(self).pg_arr.spec_index(held_page).view().view().orders_below_table_locks(),
            forall|held_thread: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(held_thread)] old(lctx).thread_lock_map().dom().contains(held_thread)
                ==> old(self).thr_mp.spec_index(held_thread).being_killed() || !(old(self).thr_mp.spec_index(held_thread).view().state is SCHEDULED),
            typed_lock_map_2d_ids_lt(old(lctx).pagetable_window_lock_map(), window_lock_id(root, l4i, l3i, l2i)),
            old(lctx).pagetable_lock_map().dom().contains(root),
            big.thread_id() == old(lctx).thread_id(),
            big.state() is WriteLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), root, TypedLockMode::Write),
            big.state() is WriteLock ==> big.lock_id() == old(self).pt_mp.spec_index(root).locking_thread()->Write_lock_id,
            big.state() is ReadLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), root, TypedLockMode::Read),
            big.state() is ReadLock ==> old(self).pt_mp.spec_index(root).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), big.lock_id()),
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            final(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            *final(self) == (KernelK { pt_mp: final(self).pt_mp, pt_lower: final(self).pt_lower, ..*old(self) }),
            final(self).pt_mp.unchanged_except(&old(self).pt_mp, root),
            update_ghost_ensures(old(self).pt_mp.spec_index(root), final(self).pt_mp.spec_index(root),
                if old(self).pt_mp.spec_index(root).wlocked() { final(self).pt_lower.view().spec_index(root) } else { old(self).pt_mp.spec_index(root).view_ghost() }),
            final(self).pt_lower.view() =~= old(self).pt_lower.view().insert(root, final(self).pt_lower.view().spec_index(root)),
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).mapping_4k() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_4k(),
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).mapping_2m() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_2m(),
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).mapping_1g() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_1g(),
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).higher == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).higher,
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.l2_perms.dom() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l2_perms.dom(),
            forall|p: PageMapPtr, i: L2Index| #![trigger pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.l2_page(p).entry_lock(i)]
                pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.l2_entry(p, i) == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l2_entry(p, i)
                    && pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1(),
            forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).spec_resolve_mapping_4k_l1(i4, i3, i2, i1)]
                pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).spec_resolve_mapping_4k_l1(i4, i3, i2, i1) == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).spec_resolve_mapping_4k_l1(i4, i3, i2, i1),
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.l1_rev_map == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l1_rev_map,
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.window_stale_cpus == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.window_stale_cpus,
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.pagetable_window_locks == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.pagetable_window_locks.insert(WindowVa { va: spec_index2va((l4i, l3i, l2i, 0)) }, LockStateU::WriteLocked),
            pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.pagetable_window_locks.dom().contains(WindowVa { va: spec_index2va((l4i, l3i, l2i, 0)) }),
            pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.pagetable_window_locks[WindowVa { va: spec_index2va((l4i, l3i, l2i, 0)) }] is Unlocked,
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).page_closure() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).page_closure(),
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).window_locked_by_thread(l4i, l3i, l2i, final(lctx).thread_id()),
            forall|w: WindowVa|
                #![trigger pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).window_view(w)]
                page_table_key_2m_valid::<PT_TYPE>(w.va) && pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).kernel_l4_end() <= spec_v2l4index(w.va)
                    && pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).window_exists(spec_v2l4index(w.va), spec_v2l3index(w.va)) && w.va != spec_index2va((l4i, l3i, l2i, 0))
                    ==> pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).window_view(w) == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).window_view(w),
            big.state() is ReadLock ==> pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).window_leaves_present(WindowVa { va: spec_index2va((l4i, l3i, l2i, 0)) }),
            big.state() is ReadLock ==> !pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.window_stale_cpus.dom().contains((pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).window_l2_page(l4i, l3i), l2i)),
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.l2_owner(pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).window_l2_page(l4i, l3i), l2i) == (SpinLockState::Some { thread_id: ret.view().thread_id(), lock_id: ret.view().lock_id() }),
            ret.view().state() is WriteLock,
            ret.view().thread_id() == final(lctx).thread_id(),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::PageTableWindow(root, WindowVa { va: spec_index2va((l4i, l3i, l2i, 0)) }),
                TypedHeldLock { lock_id: window_lock_id_of(root, WindowVa { va: spec_index2va((l4i, l3i, l2i, 0)) }), mode: TypedLockMode::Write }),
    {
        let ghost w = WindowVa { va: spec_index2va((l4i, l3i, l2i, 0)) };
        let ghost pre_c = pagetable_c(self.pt_mp, self.pt_lower.view(), root);
        proof {
            pagetable_perms_wf_map(old(self).pt_mp);
            pagetable_perms_wf_at(old(self).pt_mp, root);
            pagetable_lower_wf_at(old(self).pt_mp, old(self).pt_lower.view(), root);
            assert(spec_v2l4index(w.va) == l4i && spec_v2l3index(w.va) == l3i && spec_v2l2index(w.va) == l2i) by { broadcast use spec_va_2m_valid_index_roundtrip; spec_index2va_injective(); };
            assert(old(lctx).lock_id_acyclic(window_lock_id(root, l4i, l3i, l2i))) by {
                iommu_table_perms_wf_map(old(self).it_mp);
                reveal(LocalContext::lock_id_acyclic); reveal(UnLockedMap::typed_flag_lock_map_aligned); reveal(iommu_root_table_typed_lock_map_aligned);
                reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned);
            };
            assert(!pre_c.window_locked_by_thread(l4i, l3i, l2i, old(lctx).thread_id())) by {
                pagetable_window_typed_lock_map_aligned_locked_at(old(self).pt_mp, old(self).pt_lower.view(), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id(),
                    root, l4i, l3i, l2i);
                if old(lctx).pagetable_window_lock_map().dom().contains((root, w)) {
                    pagetable_window_typed_lock_map_aligned_at(old(self).pt_mp, old(self).pt_lower.view(), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id(),
                        root, w);
                    assert(!window_lock_id(root, l4i, l3i, l2i).spec_gt(window_lock_id(root, l4i, l3i, l2i))) by { reveal_with_fuel(lock_minor_lt, 5); };
                }
            };
            assert(pre_c.lower.pagetable_window_locks.dom().contains(w)) by {
                broadcast use PageTableHigher::resolve_l3_addr_unique_at;
                pre_c.higher.wf_l4_at(l4i); pre_c.wf_l3_at(pre_c.spec_resolve_mapping_l4(l4i)->0.addr, l3i);
                pre_c.tables_reachable_wf_l2_at(pre_c.window_l2_page(l4i, l3i)); pre_c.wf_window_locks_slot_at(pre_c.window_l2_page(l4i, l3i), l2i);
            };
        }
        let higher = self.pt_mp.borrow_typed(root, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(big));
        let tracked mut lower = self.pt_lower.borrow_mut().tracked_remove(root);
        let ret = higher.lock_window(Tracked(&mut lower), Ghost(root), l4i, l3i, l2i, Tracked(&mut *lctx));
        proof {
            self.pt_lower.borrow_mut().tracked_insert(root, lower);
            if old(self).pt_mp.spec_index(root).wlocked() { self.pt_mp.update_ghost(root, self.pt_lower.view().spec_index(root)); }
            assert(old(self).pt_mp.spec_index(root).locked_by_thread(lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(pagetable_c(self.pt_mp, self.pt_lower.view(), root).mapping_4k() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_4k()
                && pagetable_c(self.pt_mp, self.pt_lower.view(), root).mapping_2m() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_2m()
                && pagetable_c(self.pt_mp, self.pt_lower.view(), root).mapping_1g() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_1g());
            assert(pagetable_c(self.pt_mp, self.pt_lower.view(), root).page_closure() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).page_closure()
                && pagetable_c(self.pt_mp, self.pt_lower.view(), root).leaves_present() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).leaves_present());
            assert(lock_pagetable_window_eof_transition_framing(*old(self), *self, root, l4i, l3i, l2i, lctx.thread_id(), ret.view().lock_id())) by {
                reveal(lock_pagetable_window_eof_transition_framing); broadcast use PageTableHigher::resolve_l3_addr_unique_at, spec_va_2m_valid_index_roundtrip;
                pagetable_lock_op_preserves_invariant_fields(old(self).pt_mp, self.pt_mp, self.pt_lower.view(), root);
            };
            assert(pre_c.lower.pagetable_window_locks[w] is Unlocked) by { reveal(lock_pagetable_window_eof_transition_framing); pre_c.wf_window_locks_va_at(w); };
            assert(typed_lock_maps_aligned(self, &*lctx)) by {
                reveal(lock_pagetable_window_eof_transition_framing); reveal(pagetable_window_typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned);
                broadcast use spec_va_2m_valid_index_roundtrip; spec_index2va_injective();
            };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by {
                reveal(lock_pagetable_window_eof_transition_framing); broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged);
            };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
            assert(big.state() is ReadLock ==> !(old(self).pt_mp.spec_index(root).locking_thread() is Write)) by { reveal(LockedMap::typed_lock_map_aligned); };
            lock_pagetable_window_eof(*old(self), *self, root, l4i, l3i, l2i, lctx.thread_id(), ret.view().lock_id());
        }
        ret
    }

    /// Release 2M window `(l4i, l3i, l2i)` of page table `root`, whose big lock this thread holds in either mode through
    /// `big`; a write-held table's ghost slot follows the new window half and every other window keeps its view.
    pub fn unlock_pagetable_window(&mut self, root: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, Tracked(big): Tracked<&LockPerm>,
        Tracked(lctx): Tracked<&mut LocalContext>, lp: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).pt_mp.dom().contains(root),
            pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
            typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (root, WindowVa { va: spec_index2va((l4i, l3i, l2i, 0)) }), TypedLockMode::Write),
            lp.view().state() is WriteLock,
            lp.view().thread_id() == old(lctx).thread_id(),
            pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l2_owner(pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).window_l2_page(l4i, l3i), l2i) == (SpinLockState::Some { thread_id: lp.view().thread_id(), lock_id: lp.view().lock_id() }),
            big.thread_id() == old(lctx).thread_id(),
            big.state() is WriteLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), root, TypedLockMode::Write),
            big.state() is WriteLock ==> big.lock_id() == old(self).pt_mp.spec_index(root).locking_thread()->Write_lock_id,
            big.state() is ReadLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), root, TypedLockMode::Read),
            big.state() is ReadLock ==> old(self).pt_mp.spec_index(root).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), big.lock_id()),
            !(big.state() is WriteLock) ==> pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).window_leaves_present(WindowVa { va: spec_index2va((l4i, l3i, l2i, 0)) }),
            !(big.state() is WriteLock) ==> !pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.window_stale_cpus.dom().contains((pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).window_l2_page(l4i, l3i), l2i)),
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            final(self).inv(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), final(self)),
            kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, final(self).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(self), final(self)),
            typed_lock_maps_aligned(final(self), final(lctx)),
            *final(self) == (KernelK { pt_mp: final(self).pt_mp, pt_lower: final(self).pt_lower, ..*old(self) }),
            final(self).pt_mp.unchanged_except(&old(self).pt_mp, root),
            update_ghost_ensures(old(self).pt_mp.spec_index(root), final(self).pt_mp.spec_index(root),
                if old(self).pt_mp.spec_index(root).wlocked() { final(self).pt_lower.view().spec_index(root) } else { old(self).pt_mp.spec_index(root).view_ghost() }),
            final(self).pt_lower.view() =~= old(self).pt_lower.view().insert(root, final(self).pt_lower.view().spec_index(root)),
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).mapping_4k() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_4k(),
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).mapping_2m() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_2m(),
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).mapping_1g() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_1g(),
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).higher == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).higher,
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.l2_perms.dom() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l2_perms.dom(),
            forall|p: PageMapPtr, i: L2Index| #![trigger pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.l2_page(p).entry_lock(i)]
                pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.l2_entry(p, i) == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l2_entry(p, i)
                    && pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l2_page(p).entry_lock(i).l1(),
            forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).spec_resolve_mapping_4k_l1(i4, i3, i2, i1)]
                pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).spec_resolve_mapping_4k_l1(i4, i3, i2, i1) == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).spec_resolve_mapping_4k_l1(i4, i3, i2, i1),
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.l1_rev_map == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l1_rev_map,
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.window_stale_cpus == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.window_stale_cpus,
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.pagetable_window_locks == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.pagetable_window_locks.insert(WindowVa { va: spec_index2va((l4i, l3i, l2i, 0)) }, LockStateU::Unlocked),
            pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.pagetable_window_locks.dom().contains(WindowVa { va: spec_index2va((l4i, l3i, l2i, 0)) }),
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).page_closure() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).page_closure(),
            typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::PageTableWindow(root, WindowVa { va: spec_index2va((l4i, l3i, l2i, 0)) })),
            forall|w: WindowVa|
                #![trigger pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).window_view(w)]
                page_table_key_2m_valid::<PT_TYPE>(w.va) && pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).kernel_l4_end() <= spec_v2l4index(w.va)
                    && pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).window_exists(spec_v2l4index(w.va), spec_v2l3index(w.va)) && w.va != spec_index2va((l4i, l3i, l2i, 0))
                    ==> pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).window_view(w) == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).window_view(w),
    {
        let ghost w = WindowVa { va: spec_index2va((l4i, l3i, l2i, 0)) };
        let ghost pre_c = pagetable_c(self.pt_mp, self.pt_lower.view(), root);
        proof {
            pagetable_perms_wf_map(old(self).pt_mp);
            pagetable_perms_wf_at(old(self).pt_mp, root);
            pagetable_lower_wf_at(old(self).pt_mp, old(self).pt_lower.view(), root);
            pagetable_window_typed_lock_map_aligned_at(old(self).pt_mp, old(self).pt_lower.view(), old(lctx).pagetable_window_lock_map(), old(lctx).pagetable_lock_map(), old(lctx).thread_id(),
                root, w);
            assert(spec_v2l4index(w.va) == l4i && spec_v2l3index(w.va) == l3i && spec_v2l2index(w.va) == l2i) by { broadcast use spec_va_2m_valid_index_roundtrip; spec_index2va_injective(); };
            assert(pre_c.lower.pagetable_window_locks.dom().contains(w)) by {
                broadcast use PageTableHigher::resolve_l3_addr_unique_at;
                pre_c.higher.wf_l4_at(l4i); pre_c.wf_l3_at(pre_c.spec_resolve_mapping_l4(l4i)->0.addr, l3i);
                pre_c.tables_reachable_wf_l2_at(pre_c.window_l2_page(l4i, l3i)); pre_c.wf_window_locks_slot_at(pre_c.window_l2_page(l4i, l3i), l2i);
            };
        }
        let higher = self.pt_mp.borrow_typed(root, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(big));
        let tracked mut lower = self.pt_lower.borrow_mut().tracked_remove(root);
        higher.unlock_window(Tracked(&mut lower), Ghost(root), l4i, l3i, l2i, Tracked(&mut *lctx), lp);
        proof {
            self.pt_lower.borrow_mut().tracked_insert(root, lower);
            if old(self).pt_mp.spec_index(root).wlocked() { self.pt_mp.update_ghost(root, self.pt_lower.view().spec_index(root)); }
            assert(pagetable_c(self.pt_mp, self.pt_lower.view(), root).mapping_4k() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_4k()
                && pagetable_c(self.pt_mp, self.pt_lower.view(), root).mapping_2m() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_2m()
                && pagetable_c(self.pt_mp, self.pt_lower.view(), root).mapping_1g() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_1g());
            assert(pagetable_c(self.pt_mp, self.pt_lower.view(), root).page_closure() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).page_closure()
                && pagetable_c(self.pt_mp, self.pt_lower.view(), root).leaves_present() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).leaves_present());
            assert(unlock_pagetable_window_eof_transition_framing(*old(self), *self, root, l4i, l3i, l2i)) by {
                reveal(unlock_pagetable_window_eof_transition_framing); broadcast use PageTableHigher::resolve_l3_addr_unique_at, spec_va_2m_valid_index_roundtrip;
            };
            assert(typed_lock_maps_aligned(self, &*lctx)) by {
                reveal(unlock_pagetable_window_eof_transition_framing); reveal(pagetable_window_typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned);
                broadcast use spec_va_2m_valid_index_roundtrip; spec_index2va_injective();
            };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by {
                reveal(unlock_pagetable_window_eof_transition_framing); broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged);
            };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
            if big.state() is WriteLock { old(self).pt_mp.typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), root); }
            unlock_pagetable_window_eof(*old(self), *self, root, l4i, l3i, l2i);
        }
    }
}
} // verus!
