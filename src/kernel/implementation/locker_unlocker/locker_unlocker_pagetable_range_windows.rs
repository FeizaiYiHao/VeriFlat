use vstd::prelude::*;
use crate::*;

verus! {
impl KernelK {
    /// Lock, in ascending address order, every 2M window of page table `root` that covers `range`, while this thread
    /// holds the big lock of `root` in either mode through `big` and holds windows only of tables below `root`; each
    /// window keeps its lock state until this call returns, and under a read-held table each locked window has its
    /// leaves present and lists no stale CPU.
    pub fn lock_pagetable_range_windows(&mut self, root: RwLockPageTableRoot, range: &VaRange4K, Tracked(big): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>)
        -> (ret: Tracked<Map<WindowVa, LockPerm>>)
        requires
            old(self).inv(),
            old(self).pt_mp.dom().contains(root),
            range.wf(),
            range.len > 0,
            pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).kernel_l4_end() <= spec_va2index(range.start).0,
            pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).higher.spec_mapping_4k_va_range_windows_exist(range),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(self).pg_arr.spec_index(held_page).view().view().orders_below_table_locks(),
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))] old(lctx).pagetable_window_lock_map().dom().contains((p, w)) ==> p < root,
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
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.l2_perms == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l2_perms,
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.l2_ghost == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l2_ghost,
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.l1_tables == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l1_tables,
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.l1_rev_map == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l1_rev_map,
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.window_stale_cpus == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.window_stale_cpus,
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).page_closure() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).page_closure(),
            final(lctx).page_lock_map() == old(lctx).page_lock_map(),
            final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
            final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
            final(lctx).container_lock_map() == old(lctx).container_lock_map(),
            final(lctx).process_lock_map() == old(lctx).process_lock_map(),
            final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
            final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
            final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
            final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            forall|p: RwLockPageTableRoot, w: WindowVa|
                #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (old(lctx).pagetable_window_lock_map().dom().contains((p, w)) || (p == root && va_range_2m_windows(*range).contains(w))),
            forall|p: RwLockPageTableRoot, w: WindowVa|
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                old(lctx).pagetable_window_lock_map().dom().contains((p, w)) ==> final(lctx).pagetable_window_lock_map().index((p, w)) == old(lctx).pagetable_window_lock_map().index((p, w)),
            forall|w: WindowVa| #![trigger ret.view().dom().contains(w)] ret.view().dom().contains(w) ==> va_range_2m_windows(*range).contains(w),
            forall|w: WindowVa|
                #![trigger va_range_2m_windows(*range).contains(w)]
                va_range_2m_windows(*range).contains(w) ==> {
                    &&& ret.view().dom().contains(w)
                    &&& ret.view().index(w).state() is WriteLock
                    &&& ret.view().index(w).thread_id() == final(lctx).thread_id()
                    &&& typed_lock_map_contains_mode(final(lctx).pagetable_window_lock_map(), (root, w), TypedLockMode::Write)
                    &&& pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).window_locked_by_thread(spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va), final(lctx).thread_id())
                    &&& pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.l2_lock_of(pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                        .lock_perm_match(spec_v2l2index(w.va), &ret.view().index(w))
                    &&& big.state() is ReadLock ==> pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).window_leaves_present(w)
                    &&& big.state() is ReadLock ==> !pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.window_stale_cpus.dom().contains((
                        pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
                },
    {
        let (first_l4i, first_l3i, first_l2i, _) = va2index(range.start);
        let last_va = range.index(range.len - 1);
        let (last_l4i, last_l3i, last_l2i, _) = va2index(last_va);
        proof {
            assert(KERNEL_MEM_END_L4INDEX <= first_l4i && pei_valid(last_l4i) && pei_valid(last_l3i) && pei_valid(last_l2i)) by { broadcast use spec_va_4k_valid_index_roundtrip; };
            assert(first_l4i < last_l4i || (first_l4i == last_l4i && (first_l3i < last_l3i || (first_l3i == last_l3i && first_l2i <= last_l2i)))) by {
                range.va_range_lemma(); broadcast use spec_va_4k_valid_index_roundtrip;
                spec_index2va_le_implies_4k_indices_lex_le(spec_va2index(range.start), spec_va2index(last_va));
            };
            pagetable_lower_wf_at(old(self).pt_mp, old(self).pt_lower.view(), root);
            reveal(pagetable_window_typed_lock_map_aligned);
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
        }
        let tracked mut perms = Map::<WindowVa, LockPerm>::tracked_empty();
        let mut l4i = first_l4i;
        let mut l3i = first_l3i;
        let mut l2i = first_l2i;
        while l4i < last_l4i || (l4i == last_l4i && (l3i < last_l3i || (l3i == last_l3i && l2i <= last_l2i)))
            invariant
                (first_l4i, first_l3i, first_l2i) == (spec_va2index(range.start).0, spec_va2index(range.start).1, spec_va2index(range.start).2),
                (last_l4i, last_l3i, last_l2i) == (spec_va2index(range.view().spec_index(range.len - 1)).0, spec_va2index(range.view().spec_index(range.len - 1)).1,
                    spec_va2index(range.view().spec_index(range.len - 1)).2),
                KERNEL_MEM_END_L4INDEX <= first_l4i,
                pei_valid(last_l4i) && pei_valid(last_l3i) && pei_valid(last_l2i),
                pei_valid(l3i) && pei_valid(l2i) && l4i <= 512,
                first_l4i < l4i || (first_l4i == l4i && (first_l3i < l3i || (first_l3i == l3i && first_l2i <= l2i))),
                old(self).pt_mp.dom().contains(root),
                pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).kernel_l4_end() <= first_l4i,
                pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).higher.spec_mapping_4k_va_range_windows_exist(range),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).scheduler_lock_map().dom().is_empty(),
                old(lctx).cpu_set_lock_map().dom().is_empty(),
                old(lctx).pcid_needflush_lock_map().dom().is_empty(),
                old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
                old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
                old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
                forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
                forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(self).pg_arr.spec_index(held_page).view().view().orders_below_table_locks(),
                forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))] old(lctx).pagetable_window_lock_map().dom().contains((p, w)) ==> p < root,
                old(lctx).pagetable_lock_map().dom().contains(root),
                big.thread_id() == old(lctx).thread_id(),
                big.state() is WriteLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), root, TypedLockMode::Write),
                big.state() is WriteLock ==> big.lock_id() == old(self).pt_mp.spec_index(root).locking_thread()->Write_lock_id,
                big.state() is ReadLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), root, TypedLockMode::Read),
                big.state() is ReadLock ==> old(self).pt_mp.spec_index(root).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), big.lock_id()),
                self.inv(),
                kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self),
                typed_lock_maps_aligned(self, lctx),
                *self == (KernelK { pt_mp: self.pt_mp, pt_lower: self.pt_lower, ..*old(self) }),
                self.pt_mp.unchanged_except(&old(self).pt_mp, root),
                update_ghost_ensures(old(self).pt_mp.spec_index(root), self.pt_mp.spec_index(root),
                    if old(self).pt_mp.spec_index(root).wlocked() { self.pt_lower.view().spec_index(root) } else { old(self).pt_mp.spec_index(root).view_ghost() }),
                self.pt_lower.view() =~= old(self).pt_lower.view().insert(root, self.pt_lower.view().spec_index(root)),
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).mapping_4k() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_4k(),
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).mapping_2m() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_2m(),
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).mapping_1g() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_1g(),
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).higher == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).higher,
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).lower.l2_perms == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l2_perms,
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).lower.l2_ghost == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l2_ghost,
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).lower.l1_tables == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l1_tables,
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).lower.l1_rev_map == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l1_rev_map,
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).lower.window_stale_cpus == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.window_stale_cpus,
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).page_closure() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).page_closure(),
                lctx.cpu_id() == old(lctx).cpu_id(),
                lctx.thread_id() == old(lctx).thread_id(),
                lctx.kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                lctx.page_lock_map() == old(lctx).page_lock_map(),
                lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
                lctx.pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
                lctx.cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
                lctx.container_lock_map() == old(lctx).container_lock_map(),
                lctx.process_lock_map() == old(lctx).process_lock_map(),
                lctx.thread_lock_map() == old(lctx).thread_lock_map(),
                lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
                lctx.scheduler_lock_map() == old(lctx).scheduler_lock_map(),
                lctx.pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
                lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
                lctx.pagetable_lock_map() == old(lctx).pagetable_lock_map(),
                lctx.iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
                lctx.iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
                lctx.allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
                lctx.allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
                lctx.allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
                forall|p: RwLockPageTableRoot, w: WindowVa|
                    #![trigger lctx.pagetable_window_lock_map().dom().contains((p, w))]
                    lctx.pagetable_window_lock_map().dom().contains((p, w)) == (old(lctx).pagetable_window_lock_map().dom().contains((p, w)) || (p == root && perms.dom().contains(w))),
                forall|p: RwLockPageTableRoot, w: WindowVa|
                    #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                    old(lctx).pagetable_window_lock_map().dom().contains((p, w)) ==> lctx.pagetable_window_lock_map().index((p, w)) == old(lctx).pagetable_window_lock_map().index((p, w)),
                forall|p: RwLockPageTableRoot, w: WindowVa|
                    #![trigger lctx.pagetable_window_lock_map().dom().contains((p, w))]
                    lctx.pagetable_window_lock_map().dom().contains((p, w)) ==> lctx.pagetable_window_lock_map().index((p, w)) == (TypedHeldLock { lock_id: window_lock_id_at(p, w), mode: TypedLockMode::Write }),
                forall|w: WindowVa|
                    #![trigger perms.dom().contains(w)]
                    perms.dom().contains(w) ==> {
                        &&& va_range_2m_windows(*range).contains(w)
                        &&& !spec_l4_index_path_le((l4i, l3i, l2i, 0usize), spec_va2index(w.va))
                        &&& perms.index(w).state() is WriteLock
                        &&& perms.index(w).thread_id() == old(lctx).thread_id()
                        &&& typed_lock_map_contains_mode(lctx.pagetable_window_lock_map(), (root, w), TypedLockMode::Write)
                        &&& pagetable_c(self.pt_mp, self.pt_lower.view(), root).window_view(w).lock_state == (SpinLockState::Some { thread_id: old(lctx).thread_id(), lock_id: perms.index(w).lock_id() })
                        &&& big.state() is ReadLock ==> pagetable_c(self.pt_mp, self.pt_lower.view(), root).window_leaves_present(w)
                        &&& big.state() is ReadLock ==> !pagetable_c(self.pt_mp, self.pt_lower.view(), root).lower.window_stale_cpus.dom().contains((
                            pagetable_c(self.pt_mp, self.pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
                    },
                forall|w: WindowVa|
                    #![trigger va_range_2m_windows(*range).contains(w)]
                    va_range_2m_windows(*range).contains(w) && !spec_l4_index_path_le((l4i, l3i, l2i, 0usize), spec_va2index(w.va)) ==> perms.dom().contains(w),
            decreases 512 - l4i, 512 - l3i, 512 - l2i,
        {
            let ghost window_va = WindowVa { va: spec_index2va((l4i, l3i, l2i, 0usize)) };
            proof {
                assert(spec_va_2m_valid(spec_index2va((l4i, l3i, l2i, 0usize)))) by (bit_vector) requires KERNEL_MEM_END_L4INDEX <= l4i < 512, l3i < 512, l2i < 512;
                spec_va_4k_index_roundtrip_at(window_va.va, l4i, l3i, l2i, 0);
                assert(va_range_2m_windows(*range).contains(window_va));
                assert(typed_lock_map_2d_ids_lt(lctx.pagetable_window_lock_map(), window_lock_id(root, l4i, l3i, l2i))) by {
                    reveal_with_fuel(lock_minor_lt, 4);
                };
            }
            let Tracked(perm) = self.lock_pagetable_window(root, l4i, l3i, l2i, Tracked(big), Tracked(&mut *lctx));
            proof {
                perms.tracked_insert(window_va, perm);
                broadcast use spec_va_2m_valid_index_roundtrip;
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
            }
            if l2i < 511 {
                l2i = l2i + 1;
            } else if l3i < 511 {
                l2i = 0;
                l3i = l3i + 1;
            } else {
                l2i = 0;
                l3i = 0;
                l4i = l4i + 1;
            }
        }
        proof {
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
        }
        Tracked(perms)
    }

    /// Release every 2M window of page table `root` that covers `range`, in ascending address order, while this thread
    /// holds the big lock of `root` in either mode through `big`; under a read-held table each window must have its
    /// leaves present and list no stale CPU.
    pub fn unlock_pagetable_range_windows(&mut self, root: RwLockPageTableRoot, range: &VaRange4K, Tracked(big): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(perms): Tracked<Map<WindowVa, LockPerm>>)
        requires
            old(self).inv(),
            old(self).pt_mp.dom().contains(root),
            range.wf(),
            range.len > 0,
            pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).kernel_l4_end() <= spec_va2index(range.start).0,
            pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).higher.spec_mapping_4k_va_range_windows_exist(range),
            big.thread_id() == old(lctx).thread_id(),
            big.state() is WriteLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), root, TypedLockMode::Write),
            big.state() is WriteLock ==> big.lock_id() == old(self).pt_mp.spec_index(root).locking_thread()->Write_lock_id,
            big.state() is ReadLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), root, TypedLockMode::Read),
            big.state() is ReadLock ==> old(self).pt_mp.spec_index(root).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), big.lock_id()),
            forall|w: WindowVa|
                #![trigger va_range_2m_windows(*range).contains(w)]
                va_range_2m_windows(*range).contains(w) ==> {
                    &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (root, w), TypedLockMode::Write)
                    &&& perms.dom().contains(w)
                    &&& perms.index(w).state() is WriteLock
                    &&& perms.index(w).thread_id() == old(lctx).thread_id()
                    &&& pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l2_lock_of(pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                        .lock_perm_match(spec_v2l2index(w.va), &perms.index(w))
                    &&& !(big.state() is WriteLock) ==> pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).window_leaves_present(w)
                    &&& !(big.state() is WriteLock) ==> !pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.window_stale_cpus.dom().contains((
                        pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
                },
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
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.l2_perms == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l2_perms,
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.l2_ghost == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l2_ghost,
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.l1_tables == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l1_tables,
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.l1_rev_map == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l1_rev_map,
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.window_stale_cpus == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.window_stale_cpus,
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).page_closure() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).page_closure(),
            final(lctx).page_lock_map() == old(lctx).page_lock_map(),
            final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
            final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
            final(lctx).container_lock_map() == old(lctx).container_lock_map(),
            final(lctx).process_lock_map() == old(lctx).process_lock_map(),
            final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
            final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
            final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
            final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            forall|p: RwLockPageTableRoot, w: WindowVa|
                #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (old(lctx).pagetable_window_lock_map().dom().contains((p, w)) && !(p == root && va_range_2m_windows(*range).contains(w))),
            forall|p: RwLockPageTableRoot, w: WindowVa|
                #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                final(lctx).pagetable_window_lock_map().dom().contains((p, w)) ==> final(lctx).pagetable_window_lock_map().index((p, w)) == old(lctx).pagetable_window_lock_map().index((p, w)),
            (forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))] old(lctx).pagetable_window_lock_map().dom().contains((p, w)) ==> p == root && va_range_2m_windows(*range).contains(w))
                ==> final(lctx).pagetable_window_lock_map().dom().is_empty(),
    {
        let tracked mut perms = perms;
        let (first_l4i, first_l3i, first_l2i, _) = va2index(range.start);
        let last_va = range.index(range.len - 1);
        let (last_l4i, last_l3i, last_l2i, _) = va2index(last_va);
        proof {
            assert(KERNEL_MEM_END_L4INDEX <= first_l4i && pei_valid(last_l4i) && pei_valid(last_l3i) && pei_valid(last_l2i)) by { broadcast use spec_va_4k_valid_index_roundtrip; };
            assert(first_l4i < last_l4i || (first_l4i == last_l4i && (first_l3i < last_l3i || (first_l3i == last_l3i && first_l2i <= last_l2i)))) by {
                range.va_range_lemma(); broadcast use spec_va_4k_valid_index_roundtrip;
                spec_index2va_le_implies_4k_indices_lex_le(spec_va2index(range.start), spec_va2index(last_va));
            };
            pagetable_lower_wf_at(old(self).pt_mp, old(self).pt_lower.view(), root);
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
        }
        let mut l4i = first_l4i;
        let mut l3i = first_l3i;
        let mut l2i = first_l2i;
        while l4i < last_l4i || (l4i == last_l4i && (l3i < last_l3i || (l3i == last_l3i && l2i <= last_l2i)))
            invariant
                (first_l4i, first_l3i, first_l2i) == (spec_va2index(range.start).0, spec_va2index(range.start).1, spec_va2index(range.start).2),
                (last_l4i, last_l3i, last_l2i) == (spec_va2index(range.view().spec_index(range.len - 1)).0, spec_va2index(range.view().spec_index(range.len - 1)).1,
                    spec_va2index(range.view().spec_index(range.len - 1)).2),
                KERNEL_MEM_END_L4INDEX <= first_l4i,
                pei_valid(last_l4i) && pei_valid(last_l3i) && pei_valid(last_l2i),
                first_l4i < last_l4i || (first_l4i == last_l4i && (first_l3i < last_l3i || (first_l3i == last_l3i && first_l2i <= last_l2i))),
                pei_valid(l3i) && pei_valid(l2i) && l4i <= 512,
                first_l4i < l4i || (first_l4i == l4i && (first_l3i < l3i || (first_l3i == l3i && first_l2i <= l2i))),
                (l4i, l3i, l2i) != (first_l4i, first_l3i, first_l2i) ==> lctx.kernel_view_locking_state() is Release,
                old(self).pt_mp.dom().contains(root),
                pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).kernel_l4_end() <= first_l4i,
                pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).higher.spec_mapping_4k_va_range_windows_exist(range),
                big.thread_id() == old(lctx).thread_id(),
                big.state() is WriteLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), root, TypedLockMode::Write),
                big.state() is WriteLock ==> big.lock_id() == old(self).pt_mp.spec_index(root).locking_thread()->Write_lock_id,
                big.state() is ReadLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), root, TypedLockMode::Read),
                big.state() is ReadLock ==> old(self).pt_mp.spec_index(root).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), big.lock_id()),
                self.inv(),
                kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self),
                typed_lock_maps_aligned(self, lctx),
                *self == (KernelK { pt_mp: self.pt_mp, pt_lower: self.pt_lower, ..*old(self) }),
                self.pt_mp.unchanged_except(&old(self).pt_mp, root),
                update_ghost_ensures(old(self).pt_mp.spec_index(root), self.pt_mp.spec_index(root),
                    if old(self).pt_mp.spec_index(root).wlocked() { self.pt_lower.view().spec_index(root) } else { old(self).pt_mp.spec_index(root).view_ghost() }),
                self.pt_lower.view() =~= old(self).pt_lower.view().insert(root, self.pt_lower.view().spec_index(root)),
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).mapping_4k() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_4k(),
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).mapping_2m() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_2m(),
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).mapping_1g() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_1g(),
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).higher == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).higher,
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).lower.l2_perms == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l2_perms,
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).lower.l2_ghost == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l2_ghost,
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).lower.l1_tables == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l1_tables,
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).lower.l1_rev_map == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l1_rev_map,
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).lower.window_stale_cpus == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.window_stale_cpus,
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).page_closure() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).page_closure(),
                lctx.cpu_id() == old(lctx).cpu_id(),
                lctx.thread_id() == old(lctx).thread_id(),
                lctx.page_lock_map() == old(lctx).page_lock_map(),
                lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
                lctx.pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
                lctx.cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
                lctx.container_lock_map() == old(lctx).container_lock_map(),
                lctx.process_lock_map() == old(lctx).process_lock_map(),
                lctx.thread_lock_map() == old(lctx).thread_lock_map(),
                lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
                lctx.scheduler_lock_map() == old(lctx).scheduler_lock_map(),
                lctx.pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
                lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
                lctx.pagetable_lock_map() == old(lctx).pagetable_lock_map(),
                lctx.iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
                lctx.iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
                lctx.allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
                lctx.allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
                lctx.allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
                forall|p: RwLockPageTableRoot, w: WindowVa|
                    #![trigger lctx.pagetable_window_lock_map().dom().contains((p, w))]
                    lctx.pagetable_window_lock_map().dom().contains((p, w)) == (old(lctx).pagetable_window_lock_map().dom().contains((p, w))
                        && !(p == root && va_range_2m_windows(*range).contains(w) && !spec_l4_index_path_le((l4i, l3i, l2i, 0usize), spec_va2index(w.va)))),
                forall|p: RwLockPageTableRoot, w: WindowVa|
                    #![trigger lctx.pagetable_window_lock_map().dom().contains((p, w))]
                    lctx.pagetable_window_lock_map().dom().contains((p, w)) ==> lctx.pagetable_window_lock_map().index((p, w)) == old(lctx).pagetable_window_lock_map().index((p, w)),
                forall|k: (RwLockPageTableRoot, WindowVa)|
                    #![trigger lctx.pagetable_window_lock_map().dom().contains(k)]
                    lctx.pagetable_window_lock_map().dom().contains(k) ==> lctx.pagetable_window_lock_map().dom().contains((k.0, k.1)),
                forall|w: WindowVa|
                    #![trigger va_range_2m_windows(*range).contains(w)]
                    va_range_2m_windows(*range).contains(w) && spec_l4_index_path_le((l4i, l3i, l2i, 0usize), spec_va2index(w.va)) ==> {
                        &&& typed_lock_map_contains_mode(lctx.pagetable_window_lock_map(), (root, w), TypedLockMode::Write)
                        &&& perms.dom().contains(w)
                        &&& perms.index(w).state() is WriteLock
                        &&& perms.index(w).thread_id() == old(lctx).thread_id()
                        &&& pagetable_c(self.pt_mp, self.pt_lower.view(), root).window_view(w).lock_state == (SpinLockState::Some { thread_id: old(lctx).thread_id(), lock_id: perms.index(w).lock_id() })
                        &&& !(big.state() is WriteLock) ==> pagetable_c(self.pt_mp, self.pt_lower.view(), root).window_leaves_present(w)
                        &&& !(big.state() is WriteLock) ==> !pagetable_c(self.pt_mp, self.pt_lower.view(), root).lower.window_stale_cpus.dom().contains((
                            pagetable_c(self.pt_mp, self.pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
                    },
            decreases 512 - l4i, 512 - l3i, 512 - l2i,
        {
            let ghost window_va = WindowVa { va: spec_index2va((l4i, l3i, l2i, 0usize)) };
            proof {
                assert(spec_va_2m_valid(spec_index2va((l4i, l3i, l2i, 0usize)))) by (bit_vector) requires KERNEL_MEM_END_L4INDEX <= l4i < 512, l3i < 512, l2i < 512;
                spec_va_4k_index_roundtrip_at(window_va.va, l4i, l3i, l2i, 0);
                assert(va_range_2m_windows(*range).contains(window_va));
            }
            let tracked perm = perms.tracked_remove(window_va);
            self.unlock_pagetable_window(root, l4i, l3i, l2i, Tracked(big), Tracked(&mut *lctx), Tracked(perm));
            proof {
                broadcast use spec_va_2m_valid_index_roundtrip;
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            }
            if l2i < 511 {
                l2i = l2i + 1;
            } else if l3i < 511 {
                l2i = 0;
                l3i = l3i + 1;
            } else {
                l2i = 0;
                l3i = 0;
                l4i = l4i + 1;
            }
        }
        proof {
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
        }
    }

    /// Lock, in ascending address order, every 2M window of page table `root` that covers `range` and whose L3 entry
    /// links an L2 page, skipping the others, while this thread holds the big lock of `root` in either mode through
    /// `big` and holds windows only of tables below `root`; each locked window keeps its lock state until this call
    /// returns, and under a read-held table each locked window has its leaves present and lists no stale CPU.
    pub fn lock_pagetable_range_existing_windows(&mut self, root: RwLockPageTableRoot, range: &VaRange4K, Tracked(big): Tracked<&LockPerm>,
        Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<Map<WindowVa, LockPerm>>)
        requires
            old(self).inv(),
            old(self).pt_mp.dom().contains(root),
            range.wf(),
            range.len > 0,
            pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).kernel_l4_end() <= spec_va2index(range.start).0,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(self).pg_arr.spec_index(held_page).view().view().orders_below_table_locks(),
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))] old(lctx).pagetable_window_lock_map().dom().contains((p, w)) ==> p < root,
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
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.l2_perms == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l2_perms,
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.l2_ghost == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l2_ghost,
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.l1_tables == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l1_tables,
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.l1_rev_map == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l1_rev_map,
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.window_stale_cpus == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.window_stale_cpus,
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).page_closure() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).page_closure(),
            final(lctx).page_lock_map() == old(lctx).page_lock_map(),
            final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
            final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
            final(lctx).container_lock_map() == old(lctx).container_lock_map(),
            final(lctx).process_lock_map() == old(lctx).process_lock_map(),
            final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
            final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
            final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
            final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            forall|p: RwLockPageTableRoot, w: WindowVa|
                #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (old(lctx).pagetable_window_lock_map().dom().contains((p, w)) || (p == root && ret.view().dom().contains(w))),
            forall|p: RwLockPageTableRoot, w: WindowVa|
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                old(lctx).pagetable_window_lock_map().dom().contains((p, w)) ==> final(lctx).pagetable_window_lock_map().index((p, w)) == old(lctx).pagetable_window_lock_map().index((p, w)),
            forall|w: WindowVa|
                #![trigger va_range_2m_windows(*range).contains(w)]
                va_range_2m_windows(*range).contains(w) && pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> ret.view().dom().contains(w),
            forall|w: WindowVa|
                #![trigger ret.view().dom().contains(w)]
                ret.view().dom().contains(w) ==> {
                    &&& va_range_2m_windows(*range).contains(w)
                    &&& pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                    &&& ret.view().index(w).state() is WriteLock
                    &&& ret.view().index(w).thread_id() == final(lctx).thread_id()
                    &&& typed_lock_map_contains_mode(final(lctx).pagetable_window_lock_map(), (root, w), TypedLockMode::Write)
                    &&& pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).window_locked_by_thread(spec_v2l4index(w.va), spec_v2l3index(w.va), spec_v2l2index(w.va), final(lctx).thread_id())
                    &&& pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.l2_lock_of(pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                        .lock_perm_match(spec_v2l2index(w.va), &ret.view().index(w))
                    &&& big.state() is ReadLock ==> pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).window_leaves_present(w)
                    &&& big.state() is ReadLock ==> !pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.window_stale_cpus.dom().contains((
                        pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
                },
    {
        let (first_l4i, first_l3i, first_l2i, _) = va2index(range.start);
        let last_va = range.index(range.len - 1);
        let (last_l4i, last_l3i, last_l2i, _) = va2index(last_va);
        proof {
            assert(KERNEL_MEM_END_L4INDEX <= first_l4i && pei_valid(last_l4i) && pei_valid(last_l3i) && pei_valid(last_l2i)) by { broadcast use spec_va_4k_valid_index_roundtrip; };
            assert(first_l4i < last_l4i || (first_l4i == last_l4i && (first_l3i < last_l3i || (first_l3i == last_l3i && first_l2i <= last_l2i)))) by {
                range.va_range_lemma(); broadcast use spec_va_4k_valid_index_roundtrip;
                spec_index2va_le_implies_4k_indices_lex_le(spec_va2index(range.start), spec_va2index(last_va));
            };
            pagetable_lower_wf_at(old(self).pt_mp, old(self).pt_lower.view(), root);
            reveal(pagetable_window_typed_lock_map_aligned);
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
        }
        let tracked mut perms = Map::<WindowVa, LockPerm>::tracked_empty();
        let mut l4i = first_l4i;
        let mut l3i = first_l3i;
        let mut l2i = first_l2i;
        while l4i < last_l4i || (l4i == last_l4i && (l3i < last_l3i || (l3i == last_l3i && l2i <= last_l2i)))
            invariant
                (first_l4i, first_l3i, first_l2i) == (spec_va2index(range.start).0, spec_va2index(range.start).1, spec_va2index(range.start).2),
                (last_l4i, last_l3i, last_l2i) == (spec_va2index(range.view().spec_index(range.len - 1)).0, spec_va2index(range.view().spec_index(range.len - 1)).1,
                    spec_va2index(range.view().spec_index(range.len - 1)).2),
                KERNEL_MEM_END_L4INDEX <= first_l4i,
                pei_valid(last_l4i) && pei_valid(last_l3i) && pei_valid(last_l2i),
                pei_valid(l3i) && pei_valid(l2i) && l4i <= 512,
                first_l4i < l4i || (first_l4i == l4i && (first_l3i < l3i || (first_l3i == l3i && first_l2i <= l2i))),
                old(self).pt_mp.dom().contains(root),
                pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).kernel_l4_end() <= first_l4i,
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).scheduler_lock_map().dom().is_empty(),
                old(lctx).cpu_set_lock_map().dom().is_empty(),
                old(lctx).pcid_needflush_lock_map().dom().is_empty(),
                old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
                old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
                old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
                forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(self).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
                forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(self).pg_arr.spec_index(held_page).view().view().orders_below_table_locks(),
                forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))] old(lctx).pagetable_window_lock_map().dom().contains((p, w)) ==> p < root,
                old(lctx).pagetable_lock_map().dom().contains(root),
                big.thread_id() == old(lctx).thread_id(),
                big.state() is WriteLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), root, TypedLockMode::Write),
                big.state() is WriteLock ==> big.lock_id() == old(self).pt_mp.spec_index(root).locking_thread()->Write_lock_id,
                big.state() is ReadLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), root, TypedLockMode::Read),
                big.state() is ReadLock ==> old(self).pt_mp.spec_index(root).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), big.lock_id()),
                self.inv(),
                kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self),
                typed_lock_maps_aligned(self, lctx),
                *self == (KernelK { pt_mp: self.pt_mp, pt_lower: self.pt_lower, ..*old(self) }),
                self.pt_mp.unchanged_except(&old(self).pt_mp, root),
                update_ghost_ensures(old(self).pt_mp.spec_index(root), self.pt_mp.spec_index(root),
                    if old(self).pt_mp.spec_index(root).wlocked() { self.pt_lower.view().spec_index(root) } else { old(self).pt_mp.spec_index(root).view_ghost() }),
                self.pt_lower.view() =~= old(self).pt_lower.view().insert(root, self.pt_lower.view().spec_index(root)),
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).mapping_4k() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_4k(),
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).mapping_2m() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_2m(),
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).mapping_1g() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_1g(),
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).higher == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).higher,
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).lower.l2_perms == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l2_perms,
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).lower.l2_ghost == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l2_ghost,
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).lower.l1_tables == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l1_tables,
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).lower.l1_rev_map == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l1_rev_map,
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).lower.window_stale_cpus == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.window_stale_cpus,
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).page_closure() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).page_closure(),
                lctx.cpu_id() == old(lctx).cpu_id(),
                lctx.thread_id() == old(lctx).thread_id(),
                lctx.kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                lctx.page_lock_map() == old(lctx).page_lock_map(),
                lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
                lctx.pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
                lctx.cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
                lctx.container_lock_map() == old(lctx).container_lock_map(),
                lctx.process_lock_map() == old(lctx).process_lock_map(),
                lctx.thread_lock_map() == old(lctx).thread_lock_map(),
                lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
                lctx.scheduler_lock_map() == old(lctx).scheduler_lock_map(),
                lctx.pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
                lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
                lctx.pagetable_lock_map() == old(lctx).pagetable_lock_map(),
                lctx.iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
                lctx.iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
                lctx.allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
                lctx.allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
                lctx.allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
                forall|p: RwLockPageTableRoot, w: WindowVa|
                    #![trigger lctx.pagetable_window_lock_map().dom().contains((p, w))]
                    lctx.pagetable_window_lock_map().dom().contains((p, w)) == (old(lctx).pagetable_window_lock_map().dom().contains((p, w)) || (p == root && perms.dom().contains(w))),
                forall|p: RwLockPageTableRoot, w: WindowVa|
                    #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                    old(lctx).pagetable_window_lock_map().dom().contains((p, w)) ==> lctx.pagetable_window_lock_map().index((p, w)) == old(lctx).pagetable_window_lock_map().index((p, w)),
                forall|p: RwLockPageTableRoot, w: WindowVa|
                    #![trigger lctx.pagetable_window_lock_map().dom().contains((p, w))]
                    lctx.pagetable_window_lock_map().dom().contains((p, w)) ==> lctx.pagetable_window_lock_map().index((p, w)) == (TypedHeldLock { lock_id: window_lock_id_at(p, w), mode: TypedLockMode::Write }),
                forall|w: WindowVa|
                    #![trigger perms.dom().contains(w)]
                    perms.dom().contains(w) ==> {
                        &&& va_range_2m_windows(*range).contains(w)
                        &&& pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                        &&& !spec_l4_index_path_le((l4i, l3i, l2i, 0usize), spec_va2index(w.va))
                    },
                forall|w: WindowVa|
                    #![trigger perms.index(w)]
                    perms.dom().contains(w) ==> {
                        &&& perms.index(w).state() is WriteLock
                        &&& perms.index(w).thread_id() == old(lctx).thread_id()
                        &&& typed_lock_map_contains_mode(lctx.pagetable_window_lock_map(), (root, w), TypedLockMode::Write)
                        &&& pagetable_c(self.pt_mp, self.pt_lower.view(), root).window_view(w).lock_state == (SpinLockState::Some { thread_id: old(lctx).thread_id(), lock_id: perms.index(w).lock_id() })
                        &&& big.state() is ReadLock ==> pagetable_c(self.pt_mp, self.pt_lower.view(), root).window_leaves_present(w)
                        &&& big.state() is ReadLock ==> !pagetable_c(self.pt_mp, self.pt_lower.view(), root).lower.window_stale_cpus.dom().contains((
                            pagetable_c(self.pt_mp, self.pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
                    },
                forall|w: WindowVa|
                    #![trigger va_range_2m_windows(*range).contains(w)]
                    va_range_2m_windows(*range).contains(w) && pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                        && !spec_l4_index_path_le((l4i, l3i, l2i, 0usize), spec_va2index(w.va)) ==> perms.dom().contains(w),
            decreases 512 - l4i, 512 - l3i, 512 - l2i,
        {
            let ghost window_va = WindowVa { va: spec_index2va((l4i, l3i, l2i, 0usize)) };
            proof {
                assert(spec_va_2m_valid(spec_index2va((l4i, l3i, l2i, 0usize)))) by (bit_vector) requires KERNEL_MEM_END_L4INDEX <= l4i < 512, l3i < 512, l2i < 512;
                spec_va_4k_index_roundtrip_at(window_va.va, l4i, l3i, l2i, 0);
                assert(va_range_2m_windows(*range).contains(window_va));
            }
            let l2_exists = self.pagetable_l3_entry_links_l2(root, l4i, l3i, Tracked(big), Tracked(&*lctx));
            if l2_exists {
                proof {
                    assert(typed_lock_map_2d_ids_lt(lctx.pagetable_window_lock_map(), window_lock_id(root, l4i, l3i, l2i))) by {
                        reveal_with_fuel(lock_minor_lt, 4);
                    };
                }
                let Tracked(perm) = self.lock_pagetable_window(root, l4i, l3i, l2i, Tracked(big), Tracked(&mut *lctx));
                proof {
                    perms.tracked_insert(window_va, perm);
                    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                }
            }
            proof { broadcast use spec_va_2m_valid_index_roundtrip; }
            if l2i < 511 {
                l2i = l2i + 1;
            } else if l3i < 511 {
                l2i = 0;
                l3i = l3i + 1;
            } else {
                l2i = 0;
                l3i = 0;
                l4i = l4i + 1;
            }
        }
        proof {
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
        }
        Tracked(perms)
    }

    /// Release exactly the windows in `perms`, in ascending address order: the 2M windows of page table `root` that
    /// cover `range` and whose L3 entry links an L2 page, while this thread holds the big lock of `root` in either mode
    /// through `big`; under a read-held table each of them must have its leaves present and list no stale CPU.
    pub fn unlock_pagetable_range_existing_windows(&mut self, root: RwLockPageTableRoot, range: &VaRange4K, Tracked(big): Tracked<&LockPerm>,
        Tracked(lctx): Tracked<&mut LocalContext>, Tracked(perms): Tracked<Map<WindowVa, LockPerm>>)
        requires
            old(self).inv(),
            old(self).pt_mp.dom().contains(root),
            range.wf(),
            range.len > 0,
            pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).kernel_l4_end() <= spec_va2index(range.start).0,
            big.thread_id() == old(lctx).thread_id(),
            big.state() is WriteLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), root, TypedLockMode::Write),
            big.state() is WriteLock ==> big.lock_id() == old(self).pt_mp.spec_index(root).locking_thread()->Write_lock_id,
            big.state() is ReadLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), root, TypedLockMode::Read),
            big.state() is ReadLock ==> old(self).pt_mp.spec_index(root).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), big.lock_id()),
            forall|w: WindowVa|
                #![trigger va_range_2m_windows(*range).contains(w)]
                va_range_2m_windows(*range).contains(w) && pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> perms.dom().contains(w),
            forall|w: WindowVa|
                #![trigger perms.dom().contains(w)]
                perms.dom().contains(w) ==> {
                    &&& va_range_2m_windows(*range).contains(w)
                    &&& pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                    &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (root, w), TypedLockMode::Write)
                    &&& perms.index(w).state() is WriteLock
                    &&& perms.index(w).thread_id() == old(lctx).thread_id()
                    &&& pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l2_lock_of(pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                        .lock_perm_match(spec_v2l2index(w.va), &perms.index(w))
                    &&& !(big.state() is WriteLock) ==> pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).window_leaves_present(w)
                    &&& !(big.state() is WriteLock) ==> !pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.window_stale_cpus.dom().contains((
                        pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
                },
            typed_lock_maps_aligned(old(self), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release || final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
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
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.l2_perms == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l2_perms,
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.l2_ghost == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l2_ghost,
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.l1_tables == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l1_tables,
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.l1_rev_map == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l1_rev_map,
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).lower.window_stale_cpus == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.window_stale_cpus,
            pagetable_c(final(self).pt_mp, final(self).pt_lower.view(), root).page_closure() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).page_closure(),
            final(lctx).page_lock_map() == old(lctx).page_lock_map(),
            final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
            final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
            final(lctx).container_lock_map() == old(lctx).container_lock_map(),
            final(lctx).process_lock_map() == old(lctx).process_lock_map(),
            final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
            final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
            final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
            final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            forall|p: RwLockPageTableRoot, w: WindowVa|
                #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (old(lctx).pagetable_window_lock_map().dom().contains((p, w)) && !(p == root && perms.dom().contains(w))),
            forall|p: RwLockPageTableRoot, w: WindowVa|
                #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                final(lctx).pagetable_window_lock_map().dom().contains((p, w)) ==> final(lctx).pagetable_window_lock_map().index((p, w)) == old(lctx).pagetable_window_lock_map().index((p, w)),
            (forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))] old(lctx).pagetable_window_lock_map().dom().contains((p, w)) ==> p == root && perms.dom().contains(w))
                ==> final(lctx).pagetable_window_lock_map().dom().is_empty(),
    {
        let tracked mut remaining = perms;
        let (first_l4i, first_l3i, first_l2i, _) = va2index(range.start);
        let last_va = range.index(range.len - 1);
        let (last_l4i, last_l3i, last_l2i, _) = va2index(last_va);
        proof {
            assert(KERNEL_MEM_END_L4INDEX <= first_l4i && pei_valid(last_l4i) && pei_valid(last_l3i) && pei_valid(last_l2i)) by { broadcast use spec_va_4k_valid_index_roundtrip; };
            assert(first_l4i < last_l4i || (first_l4i == last_l4i && (first_l3i < last_l3i || (first_l3i == last_l3i && first_l2i <= last_l2i)))) by {
                range.va_range_lemma(); broadcast use spec_va_4k_valid_index_roundtrip;
                spec_index2va_le_implies_4k_indices_lex_le(spec_va2index(range.start), spec_va2index(last_va));
            };
            pagetable_lower_wf_at(old(self).pt_mp, old(self).pt_lower.view(), root);
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
        }
        let mut l4i = first_l4i;
        let mut l3i = first_l3i;
        let mut l2i = first_l2i;
        while l4i < last_l4i || (l4i == last_l4i && (l3i < last_l3i || (l3i == last_l3i && l2i <= last_l2i)))
            invariant
                (first_l4i, first_l3i, first_l2i) == (spec_va2index(range.start).0, spec_va2index(range.start).1, spec_va2index(range.start).2),
                (last_l4i, last_l3i, last_l2i) == (spec_va2index(range.view().spec_index(range.len - 1)).0, spec_va2index(range.view().spec_index(range.len - 1)).1,
                    spec_va2index(range.view().spec_index(range.len - 1)).2),
                KERNEL_MEM_END_L4INDEX <= first_l4i,
                pei_valid(last_l4i) && pei_valid(last_l3i) && pei_valid(last_l2i),
                first_l4i < last_l4i || (first_l4i == last_l4i && (first_l3i < last_l3i || (first_l3i == last_l3i && first_l2i <= last_l2i))),
                pei_valid(l3i) && pei_valid(l2i) && l4i <= 512,
                first_l4i < l4i || (first_l4i == l4i && (first_l3i < l3i || (first_l3i == l3i && first_l2i <= l2i))),
                lctx.kernel_view_locking_state() is Release || lctx.kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                old(self).pt_mp.dom().contains(root),
                pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).kernel_l4_end() <= first_l4i,
                big.thread_id() == old(lctx).thread_id(),
                big.state() is WriteLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), root, TypedLockMode::Write),
                big.state() is WriteLock ==> big.lock_id() == old(self).pt_mp.spec_index(root).locking_thread()->Write_lock_id,
                big.state() is ReadLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), root, TypedLockMode::Read),
                big.state() is ReadLock ==> old(self).pt_mp.spec_index(root).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), big.lock_id()),
                forall|w: WindowVa|
                    #![trigger va_range_2m_windows(*range).contains(w)]
                    va_range_2m_windows(*range).contains(w) && pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> perms.dom().contains(w),
                forall|w: WindowVa|
                    #![trigger perms.dom().contains(w)]
                    perms.dom().contains(w) ==> {
                        &&& va_range_2m_windows(*range).contains(w)
                        &&& pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                        &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (root, w), TypedLockMode::Write)
                        &&& perms.index(w).state() is WriteLock
                        &&& perms.index(w).thread_id() == old(lctx).thread_id()
                        &&& pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l2_lock_of(pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                            .lock_perm_match(spec_v2l2index(w.va), &perms.index(w))
                        &&& !(big.state() is WriteLock) ==> pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).window_leaves_present(w)
                        &&& !(big.state() is WriteLock) ==> !pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.window_stale_cpus.dom().contains((
                            pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
                    },
                self.inv(),
                kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self),
                typed_lock_maps_aligned(self, lctx),
                *self == (KernelK { pt_mp: self.pt_mp, pt_lower: self.pt_lower, ..*old(self) }),
                self.pt_mp.unchanged_except(&old(self).pt_mp, root),
                update_ghost_ensures(old(self).pt_mp.spec_index(root), self.pt_mp.spec_index(root),
                    if old(self).pt_mp.spec_index(root).wlocked() { self.pt_lower.view().spec_index(root) } else { old(self).pt_mp.spec_index(root).view_ghost() }),
                self.pt_lower.view() =~= old(self).pt_lower.view().insert(root, self.pt_lower.view().spec_index(root)),
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).mapping_4k() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_4k(),
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).mapping_2m() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_2m(),
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).mapping_1g() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).mapping_1g(),
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).higher == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).higher,
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).lower.l2_perms == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l2_perms,
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).lower.l2_ghost == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l2_ghost,
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).lower.l1_tables == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l1_tables,
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).lower.l1_rev_map == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.l1_rev_map,
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).lower.window_stale_cpus == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).lower.window_stale_cpus,
                pagetable_c(self.pt_mp, self.pt_lower.view(), root).page_closure() == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).page_closure(),
                lctx.cpu_id() == old(lctx).cpu_id(),
                lctx.thread_id() == old(lctx).thread_id(),
                lctx.page_lock_map() == old(lctx).page_lock_map(),
                lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
                lctx.pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
                lctx.cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
                lctx.container_lock_map() == old(lctx).container_lock_map(),
                lctx.process_lock_map() == old(lctx).process_lock_map(),
                lctx.thread_lock_map() == old(lctx).thread_lock_map(),
                lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
                lctx.scheduler_lock_map() == old(lctx).scheduler_lock_map(),
                lctx.pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
                lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
                lctx.pagetable_lock_map() == old(lctx).pagetable_lock_map(),
                lctx.iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
                lctx.iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
                lctx.allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
                lctx.allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
                lctx.allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
                forall|p: RwLockPageTableRoot, w: WindowVa|
                    #![trigger lctx.pagetable_window_lock_map().dom().contains((p, w))]
                    lctx.pagetable_window_lock_map().dom().contains((p, w)) == (old(lctx).pagetable_window_lock_map().dom().contains((p, w)) && !(p == root && va_range_2m_windows(*range).contains(w)
                        && pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some && !spec_l4_index_path_le((l4i, l3i, l2i, 0usize), spec_va2index(w.va)))),
                forall|p: RwLockPageTableRoot, w: WindowVa|
                    #![trigger lctx.pagetable_window_lock_map().dom().contains((p, w))]
                    lctx.pagetable_window_lock_map().dom().contains((p, w)) ==> lctx.pagetable_window_lock_map().index((p, w)) == old(lctx).pagetable_window_lock_map().index((p, w)),
                forall|k: (RwLockPageTableRoot, WindowVa)|
                    #![trigger lctx.pagetable_window_lock_map().dom().contains(k)]
                    lctx.pagetable_window_lock_map().dom().contains(k) ==> lctx.pagetable_window_lock_map().dom().contains((k.0, k.1)),
                forall|w: WindowVa|
                    #![trigger va_range_2m_windows(*range).contains(w)]
                    va_range_2m_windows(*range).contains(w) && pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some && spec_l4_index_path_le((l4i, l3i, l2i, 0usize), spec_va2index(w.va)) ==> {
                        &&& remaining.dom().contains(w)
                        &&& typed_lock_map_contains_mode(lctx.pagetable_window_lock_map(), (root, w), TypedLockMode::Write)
                        &&& remaining.index(w) == perms.index(w)
                        &&& pagetable_c(self.pt_mp, self.pt_lower.view(), root).window_view(w) == pagetable_c(old(self).pt_mp, old(self).pt_lower.view(), root).window_view(w)
                    },
            decreases 512 - l4i, 512 - l3i, 512 - l2i,
        {
            let ghost window_va = WindowVa { va: spec_index2va((l4i, l3i, l2i, 0usize)) };
            proof {
                assert(spec_va_2m_valid(spec_index2va((l4i, l3i, l2i, 0usize)))) by (bit_vector) requires KERNEL_MEM_END_L4INDEX <= l4i < 512, l3i < 512, l2i < 512;
                spec_va_4k_index_roundtrip_at(window_va.va, l4i, l3i, l2i, 0);
                assert(va_range_2m_windows(*range).contains(window_va));
            }
            let l2_exists = self.pagetable_l3_entry_links_l2(root, l4i, l3i, Tracked(big), Tracked(&*lctx));
            if l2_exists {
                let tracked perm = remaining.tracked_remove(window_va);
                self.unlock_pagetable_window(root, l4i, l3i, l2i, Tracked(big), Tracked(&mut *lctx), Tracked(perm));
                proof {
                    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(self), self)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
                }
            }
            proof { broadcast use spec_va_2m_valid_index_roundtrip; }
            if l2i < 511 {
                l2i = l2i + 1;
            } else if l3i < 511 {
                l2i = 0;
                l3i = l3i + 1;
            } else {
                l2i = 0;
                l3i = 0;
                l4i = l4i + 1;
            }
        }
        proof {
            assert(kernel_endpoint_nonlock_fields_unchanged(old(self).ep_mp, self.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(self), self)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
        }
    }

    /// Whether the L3 entry `(l4i, l3i)` of page table `root` links an L2 page, read while this thread holds the big lock of
    /// `root` in either mode through `big`.
    fn pagetable_l3_entry_links_l2(&self, root: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, Tracked(big): Tracked<&LockPerm>, Tracked(lctx): Tracked<&LocalContext>) -> (ret: bool)
        requires
            self.inv(),
            self.pt_mp.dom().contains(root),
            pagetable_c(self.pt_mp, self.pt_lower.view(), root).kernel_l4_end() <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            big.thread_id() == lctx.thread_id(),
            big.state() is WriteLock ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), root, TypedLockMode::Write),
            big.state() is WriteLock ==> big.lock_id() == self.pt_mp.spec_index(root).locking_thread()->Write_lock_id,
            big.state() is ReadLock ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), root, TypedLockMode::Read),
            big.state() is ReadLock ==> self.pt_mp.spec_index(root).locking_thread()->Read_reader_map.contains_pair(lctx.thread_id(), big.lock_id()),
            typed_lock_maps_aligned(self, lctx),
        ensures ret == pagetable_c(self.pt_mp, self.pt_lower.view(), root).higher.spec_resolve_mapping_l3(l4i, l3i) is Some,
    {
        proof { pagetable_perms_wf_map(self.pt_mp); pagetable_perms_wf_at(self.pt_mp, root); }
        let higher = self.pt_mp.borrow_typed(root, Ghost(lctx.pagetable_lock_map()), Tracked(lctx), Tracked(big));
        match higher.get_entry_l4(l4i) { Some(l4_entry) => higher.get_entry_l3(l4i, l3i, &l4_entry).is_some(), None => false }
    }
}
} // verus!
