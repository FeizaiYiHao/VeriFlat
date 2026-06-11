use vstd::prelude::*;
use crate::*;
verus! {
    impl KernelK{
        // #[verifier::rlimit(600)]
        #[verifier::spinoff_prover]
        pub fn syscall_alloc_quota_4k(&mut self, tracked mut lctx: Tracked<LocalContext>, tracked mut steps: Tracked<KernelSteps>, cpu_id: CpuId, alloc_amount: usize) -> (ret: bool)
            requires
                cpu_id_valid(cpu_id),
                old(self).inv(),
                old(self).all_objects_unlocked(&lctx),
                old(self).cpu_array.spec_index(cpu_id).view().view().state == CpuState::Running,
                lctx.lock_map() == Map::<KernelObjId, LockId>::empty(),
                lctx.kernel_view_locking_state() is Acquire,
                lctx.user_view_locking_state() is Acquire,
        {
            // Lock preconditions and several reconstruction asserts need the
            // `subsystems_inv` conjuncts and the `all_objects_unlocked` pieces
            // for cpu_array / container / allocator. Revealing them once here
            // (function-wide) is markedly faster than re-revealing per use.
            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
                assert(self.cpu_array.inv());
                assert(self.container_map.perms_wf());
                assert(self.allocator_4k_map.perms_wf());
                reveal(cpu_objects_unlocked);
                reveal(container_objects_unlocked);
                reveal(allocator_objects_unlocked);
            }
            assert(
                {
                    &&&
                    self.container_map.dom().contains(self.cpu_array.spec_index(cpu_id).view().view().owning_container)
                    &&&
                    self.cpu_array.spec_index(cpu_id).view().view().current_process is Some
                    &&&
                    self.process_map.dom().contains(self.cpu_array.spec_index(cpu_id).view().view().current_process.unwrap())
                    &&&
                    self.cpu_array.spec_index(cpu_id).view().view().process_depth == self.process_map.spec_index(self.cpu_array.spec_index(cpu_id).view().view().current_process.unwrap()).view_rodata().view().depth
                    &&&
                    self.cpu_array.spec_index(cpu_id).view().view().container_depth == self.container_map.spec_index(self.cpu_array.spec_index(cpu_id).view().view().owning_container).view_rodata().view().depth
                    &&&
                    self.process_map.spec_index(self.cpu_array.spec_index(cpu_id).view().view().current_process.unwrap()).view_rodata().view().container_depth
                        ==
                        self.container_map.spec_index(self.cpu_array.spec_index(cpu_id).view().view().owning_container).view_rodata().view().depth
                }
            ) by {
                reveal(container_cpu_wf);
                reveal(process_cpu_wf);
                reveal(container_process_wf);
            };

            let cpu_obj_id = Ghost(KernelObjId::Cpu(cpu_id));

            // Snapshot the entry LocalContext so we can refer back to the
            // "all objects unlocked at entry" precondition after `lctx` has
            // been threaded through the lock/unlock calls. `thread_id` is
            // preserved by every op, so the entry unlocked-ness transfers.
            let ghost entry_lctx = lctx@;

            let Tracked(cpu_lock_perm) = self.cpu_array.wlock(cpu_id, Tracked(&mut lctx), cpu_obj_id);
            let cpu = self.cpu_array.borrow(cpu_id, Tracked(&cpu_lock_perm));
            let thread_ptr = cpu.current_thread.unwrap();
            let process_ptr = cpu.current_process.unwrap();
            let container_ptr = cpu.owning_container;

            let container_obj_id = Ghost(KernelObjId::Container(container_ptr));

            let container_res = self.container_map.wlock_unless_killed(container_ptr, Tracked(&mut lctx), container_obj_id);
            if let (false, _) = container_res{
                assert(self.container_map.spec_index(container_ptr).being_killed() == true);
                // TODO: release cpu lock, open/close user step
                return false;
            }
            assume(false);
            // let Tracked(container_lock_perm) = container_res.1.unwrap();
            // let container = self.container_map.borrow(container_ptr, Tracked(&container_lock_perm));

            // // Read the container's 4k allocator pointer from rodata.
            // let container_ro = self.container_map.borrow_rodata(container_ptr);
            // let alloc_ptr_4k = container_ro.borrow().allocator_ptr_4k;

            // // `container_allocator_wf` gives: the allocator exists in the 4k
            // // map, is wf, and its quota's container depth matches the
            // // container's depth (needed for the acyclic lock-ordering check).
            // assert(
            //     {
            //         &&&
            //         self.allocator_4k_map.dom().contains(alloc_ptr_4k)
            //         &&&
            //         self.allocator_4k_map.spec_index(alloc_ptr_4k).wf()
            //         &&&
            //         self.allocator_4k_map.spec_index(alloc_ptr_4k).quota.view().container_depth
            //             == self.container_map.spec_index(container_ptr).view_rodata().view().depth
            //         &&&
            //         self.allocator_4k_map.spec_index(alloc_ptr_4k).quota.locked_by(&lctx) == false
            //     }
            // ) by {
            //     reveal(container_allocator_wf);
            //     reveal(allocator_objects_unlocked);
            //     assert(old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.locked_by(&entry_lctx) == false);
            // };

            // // Lock the container's 4k allocator quota, then mutably borrow it.
            // let Tracked(quota_lock_perm) = self.allocator_4k_map.wlock_quota(
            //     alloc_ptr_4k, Tracked(&mut lctx), Ghost(PageSize::SZ4k),
            // );
            // let quota_mut = self.allocator_4k_map.borrow_mut_quota(
            //     alloc_ptr_4k, Tracked(&lctx), Tracked(&quota_lock_perm),
            // );
            // // TODO: when quota is sufficient, allocate pages and return
            // // true. Until the success path is implemented, every outcome is
            // // a user-visible no-op: release the three locks (recording the
            // // user step) and return false.
            // let _quota_sufficient = quota_mut.value >= alloc_amount;
            // {
            //     // Prove inv() still holds (only lock bits changed, not views).
            //     proof {
            //         assert(self.container_map.dom() =~= old(self).container_map.dom());
            //         assert forall|c_ptr: RwLockContainerPtr|
            //             #![trigger self.container_map.spec_index(c_ptr)]
            //             self.container_map.dom().contains(c_ptr)
            //         implies
            //             self.container_map.spec_index(c_ptr).view()
            //                 == old(self).container_map.spec_index(c_ptr).view()
            //             && self.container_map.spec_index(c_ptr).view_rodata()
            //                 == old(self).container_map.spec_index(c_ptr).view_rodata()
            //         by {};
            //         assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
            //         assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
            //         assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
            //         assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
            //         assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
            //             reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf); };
            //         assert(container_page_owner_wf(self.container_map, self.page_array)) by { reveal(container_page_owner_wf); };
            //         assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by {
            //             reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf); };
            //         assert(self.container_pages_wf()) by { reveal(KernelK::container_pages_wf); };
            //         assert(self.process_pages_wf()) by { reveal(KernelK::process_pages_wf); };
            //         assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
            //             reveal(container_process_allocator_quota_4k_wf); reveal(container_process_allocator_quota_2m_wf);
            //             reveal(container_process_allocator_quota_1g_wf); reveal(container_allocator_wf); reveal(container_process_wf); reveal(container_thread_wf); };
            //         assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by { reveal(container_allocator_wf); };
            //         assert(self.allocator_free_pages_wf());
            //         assert(self.memory_management_inv());
            //         container_no_change_to_tree_fields_imply_wf(self.root_container, old(self).container_map, self.container_map);
            //         assert(container_process_wf(self.container_map, self.process_map)) by { reveal(container_process_wf); };
            //         assert(per_container_process_tree_wf(self.container_map, self.process_map)) by { reveal(container_process_wf); reveal(per_container_process_tree_wf); };
            //         assert(container_endpoint_wf(self.container_map, self.endpoint_map)) by { reveal(container_endpoint_wf); };
            //         assert(container_cpu_wf(self.container_map, self.cpu_array)) by { reveal(container_cpu_wf); };
            //         assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
            //             reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf); };
            //         assert(container_scheduler_wf(self.container_map, self.scheduler_map)) by { reveal(container_scheduler_wf); };
            //         assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
            //             reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf); };
            //         assert(container_thread_wf(self.container_map, self.thread_map)) by { reveal(container_thread_wf); };
            //         assert(process_cpu_wf(self.process_map, self.cpu_array)) by { reveal(process_cpu_wf); };
            //         assert(self.process_management_inv());
            //         assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
            //             reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
            //             reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(container_cpu_wf); };
            //         assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
            //         assert(self.inv());
            //     }
            //     // Hand off to helper.
            //     self.release_all_and_finish(
            //         Tracked(lctx.get()),
            //         Tracked(steps.borrow_mut()),
            //         cpu_id, container_ptr, alloc_ptr_4k,
            //         Tracked(quota_lock_perm),
            //         Tracked(container_lock_perm),
            //         Tracked(cpu_lock_perm),
            //     );
                // return false;
            // }
            return false;
        }

        /// Lemma: releasing locks (which preserves every cpu payload view,
        /// the process map, and the pagetable map) leaves the user-view
        /// projection unchanged. Isolated into its own proof query so the
        /// element-wise quantifier doesn't perturb the caller's `inv()`
        /// re-establishment proof.
        proof fn lemma_release_preserves_user_view(pre: KernelK, post: KernelK, cpu_id: CpuId)
            requires
                cpu_id_valid(cpu_id),
                pre.cpu_array.inv(),
                post.cpu_array.inv(),
                post.process_map == pre.process_map,
                post.pagetable_map == pre.pagetable_map,
                post.cpu_array.unchanged_except(&pre.cpu_array, cpu_id),
                post.cpu_array.spec_index(cpu_id).view().view()
                    == pre.cpu_array.spec_index(cpu_id).view().view(),
            ensures
                kernel_k_to_kernel_u(pre) == kernel_k_to_kernel_u(post),
        {
            pre.cpu_array.lemma_view_len();
            post.cpu_array.lemma_view_len();
            assert(kernel_k_to_kernel_u(pre).cpu_array
                =~= kernel_k_to_kernel_u(post).cpu_array) by {
                assert forall|i: int|
                    0 <= i < pre.cpu_array.view().len()
                implies
                    #[trigger] post.cpu_array.view()[i].view()
                        == pre.cpu_array.view()[i].view()
                by {
                    if i == cpu_id as int {
                        assert(post.cpu_array.view()[i]
                            == post.cpu_array.spec_index(cpu_id).view());
                        assert(pre.cpu_array.view()[i]
                            == pre.cpu_array.spec_index(cpu_id).view());
                    } else {
                        assert(post.cpu_array.spec_index(i as usize)
                            == pre.cpu_array.spec_index(i as usize));
                    }
                };
            };
            assert(kernel_k_to_kernel_u(pre).process_map
                =~= kernel_k_to_kernel_u(post).process_map);
        }
        /// Helper: open user-view step, release the 3 locks (quota →
        /// container → cpu), re-establish `inv()`, and close the user-view
        /// step.
        ///
        /// Factored out of `syscall_alloc_quota_4k` so the main body stays
        /// short and the heavy exit-path proof is isolated.
        #[verifier::spinoff_prover]
        fn release_all_and_finish(
            &mut self,
            tracked mut lctx: Tracked<LocalContext>,
            Tracked(steps): Tracked<&mut KernelSteps>,
            cpu_id: CpuId,
            container_ptr: RwLockContainerPtr,
            alloc_ptr_4k: RwLockPageAllocatorPtr,
            quota_lock_perm: Tracked<LockPerm>,
            container_lock_perm: Tracked<LockPerm>,
            cpu_lock_perm: Tracked<LockPerm>,
        )
            requires
                cpu_id_valid(cpu_id),
                old(self).inv(),
                // Locking phase
                lctx.kernel_view_locking_state() is Acquire,
                lctx.user_view_locking_state() is Acquire,
                // The 3 locks are held.
                lctx.lock_map().dom() =~= set![
                    KernelObjId::Cpu(cpu_id),
                    KernelObjId::Container(container_ptr),
                    KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k),
                ],
                // CPU array lock perm
                cpu_lock_perm@.state() is WriteLock,
                cpu_lock_perm@.thread_id() == lctx.thread_id(),
                cpu_lock_perm@.lock_id() == lctx.lock_map()[KernelObjId::Cpu(cpu_id)],
                cpu_lock_perm@.lock_id() == old(self).cpu_array.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
                old(self).cpu_array.spec_index(cpu_id).view().wlocked_by(&lctx),
                old(self).cpu_array.spec_index(cpu_id).view().being_killed() == false,
                old(self).cpu_array.inv(),
                // Container lock perm
                container_lock_perm@.state() is WriteLock,
                container_lock_perm@.thread_id() == lctx.thread_id(),
                container_lock_perm@.lock_id() == lctx.lock_map()[KernelObjId::Container(container_ptr)],
                container_lock_perm@.lock_id() == old(self).container_map.spec_index(container_ptr).locking_thread()->Write_lock_id,
                old(self).container_map.dom().contains(container_ptr),
                old(self).container_map.spec_index(container_ptr).wlocked_by(&lctx),
                old(self).container_map.spec_index(container_ptr).inv(),
                old(self).container_map.perms_wf(),
                // Allocator quota lock perm
                quota_lock_perm@.state() is WriteLock,
                quota_lock_perm@.thread_id() == lctx.thread_id(),
                quota_lock_perm@.lock_id() == lctx.lock_map()[KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k)],
                quota_lock_perm@.lock_id() == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.locking_thread()->Write_lock_id,
                old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.wlocked_by(&lctx),
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.inv(),
                old(self).allocator_4k_map.perms_wf(),
            ensures
                // A user-view step was opened and closed.
                final(steps).steps.len() > 0,
                // The recorded step captures the post-section kernel state,
                // and `new_u` is the user-view projection of that state.
                final(steps).steps.last().new_k == *final(self),
                final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(self)),
                // The release path is a user-visible no-op: the step's
                // user view at exit equals its user view at entry.
                final(steps).steps.last().old_u == final(steps).steps.last().new_u,
        {
            let tracked quota_lock_perm = quota_lock_perm.get();
            let tracked container_lock_perm = container_lock_perm.get();
            let tracked cpu_lock_perm = cpu_lock_perm.get();

            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
                reveal(cpu_objects_unlocked);
                reveal(container_objects_unlocked);
                reveal(allocator_objects_unlocked);
            }

            // Snapshot the entry lctx for the "others unlocked" derivation.
            let ghost entry_lctx = lctx@;

            // Open the user-view atomic step: user-view -> Release.
            proof { steps.begin_user_view_step(&*self, lctx.borrow_mut()); }

            // Release Quota -> Container -> CPU.
            self.allocator_4k_map.wunlock_quota(alloc_ptr_4k, Tracked(&mut lctx), Tracked(quota_lock_perm), Ghost(PageSize::SZ4k));
            self.container_map.wunlock(container_ptr, Tracked(&mut lctx), Tracked(container_lock_perm), Ghost(KernelObjId::Container(container_ptr)));
            // The quota/container unlocks are on other fields, so cpu_array
            // is still the entry value here. Snapshot it to bridge the cpu
            // unlock's frame back to `old(self)`.
            let ghost cpu_array_before_unlock = self.cpu_array;
            assert(cpu_array_before_unlock == old(self).cpu_array);
            self.cpu_array.wunlock(cpu_id, Tracked(&mut lctx), Tracked(cpu_lock_perm), Ghost(KernelObjId::Cpu(cpu_id)));

            // All locks released. Re-establish inv() (lock-state changed).
            proof {
                assert(self.container_map.dom() =~= old(self).container_map.dom());
                assert forall|c_ptr: RwLockContainerPtr|
                    #![trigger self.container_map.spec_index(c_ptr)]
                    self.container_map.dom().contains(c_ptr)
                implies
                    self.container_map.spec_index(c_ptr).view()
                        == old(self).container_map.spec_index(c_ptr).view()
                    && self.container_map.spec_index(c_ptr).view_rodata()
                        == old(self).container_map.spec_index(c_ptr).view_rodata()
                by {};
                // ---- subsystems_inv ----
                assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
                assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
                assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                // ---- memory_management_inv ----
                assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf);
                };
                assert(container_page_owner_wf(self.container_map, self.page_array)) by {
                    reveal(container_page_owner_wf);
                };
                assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by {
                    reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
                };
                assert(self.container_pages_wf()) by {
                    reveal(KernelK::container_pages_wf);
                };
                assert(self.process_pages_wf()) by {
                    reveal(KernelK::process_pages_wf);
                };
                assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    reveal(container_process_allocator_quota_4k_wf);
                    reveal(container_process_allocator_quota_2m_wf);
                    reveal(container_process_allocator_quota_1g_wf); reveal(container_allocator_wf); reveal(container_process_wf); reveal(container_thread_wf);
                };
                assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    reveal(container_allocator_wf);
                };
                assert(self.allocator_free_pages_wf());
                assert(self.memory_management_inv());
                // ---- process_management_inv ----
                container_no_change_to_tree_fields_imply_wf(self.root_container, old(self).container_map, self.container_map);
                assert(container_process_wf(self.container_map, self.process_map)) by {
                    reveal(container_process_wf);
                };
                assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                    reveal(container_process_wf); reveal(per_container_process_tree_wf);
                };
                assert(container_endpoint_wf(self.container_map, self.endpoint_map)) by {
                    reveal(container_endpoint_wf);
                };
                assert(container_cpu_wf(self.container_map, self.cpu_array)) by {
                    reveal(container_cpu_wf);
                };
                assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
                    reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
                    reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf);
                };
                assert(container_scheduler_wf(self.container_map, self.scheduler_map)) by {
                    reveal(container_scheduler_wf);
                };
                assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
                    reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
                };
                assert(container_thread_wf(self.container_map, self.thread_map)) by {
                    reveal(container_thread_wf);
                    reveal(container_perms_wf);
                    assert(container_thread_wf(old(self).container_map, old(self).thread_map));
                    assert(self.thread_map == old(self).thread_map);
                    assert(self.container_map.dom() =~= old(self).container_map.dom());
                    // Instantiate each sub-quantifier manually via framing
                    assert forall|c_ptr: RwLockContainerPtr, t_ptr: RwLockThreadPtr|
                        #![trigger self.container_map.spec_index(c_ptr).view(), self.thread_map.spec_index(t_ptr).view()]
                        self.container_map.dom().contains(c_ptr) && self.container_map.spec_index(c_ptr).view().owned_threads.view().contains(t_ptr)
                    implies
                        self.thread_map.dom().contains(t_ptr)
                        && self.thread_map.spec_index(t_ptr).view().owning_container == c_ptr
                        && self.thread_map.spec_index(t_ptr).view().container_depth == self.container_map.spec_index(c_ptr).view_rodata().view().depth
                        && self.thread_map.spec_index(t_ptr).view().upper_container_seq == self.container_map.spec_index(c_ptr).view().uppertree_seq
                    by {
                        assert(self.container_map.spec_index(c_ptr).view() == old(self).container_map.spec_index(c_ptr).view());
                        assert(self.container_map.spec_index(c_ptr).view_rodata() == old(self).container_map.spec_index(c_ptr).view_rodata());
                    };
                    assert forall|t_ptr: RwLockThreadPtr|
                        #![trigger self.container_map.dom().contains(self.thread_map.spec_index(t_ptr).view().owning_container)]
                        self.thread_map.dom().contains(t_ptr)
                    implies
                        self.container_map.dom().contains(self.thread_map.spec_index(t_ptr).view().owning_container)
                        && self.container_map.spec_index(self.thread_map.spec_index(t_ptr).view().owning_container).view().owned_threads.view().contains(t_ptr)
                    by {
                        let oc = self.thread_map.spec_index(t_ptr).view().owning_container;
                        assert(self.container_map.spec_index(oc).view() == old(self).container_map.spec_index(oc).view());
                    };
                    assert forall|c_ptr: RwLockContainerPtr, t_ptr: RwLockThreadPtr|
                        #![trigger self.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().contains(t_ptr)]
                        self.container_map.dom().contains(c_ptr) && self.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().contains(t_ptr)
                    implies
                        self.thread_map.dom().contains(t_ptr) && self.thread_map.spec_index(t_ptr).view().upper_container_seq.view().contains(c_ptr)
                    by {
                        assert(self.container_map.spec_index(c_ptr).view() == old(self).container_map.spec_index(c_ptr).view());
                    };
                    assert forall|t_ptr: RwLockThreadPtr, c_ptr: RwLockContainerPtr|
                        #![trigger self.thread_map.spec_index(t_ptr).view().upper_container_seq.view().contains(c_ptr)]
                        self.thread_map.dom().contains(t_ptr) && self.thread_map.spec_index(t_ptr).view().upper_container_seq.view().contains(c_ptr)
                    implies
                        self.container_map.dom().contains(c_ptr) && self.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().contains(t_ptr)
                    by {
                        assert(self.container_map.spec_index(c_ptr).view() == old(self).container_map.spec_index(c_ptr).view());
                    };
                };
                assert(process_cpu_wf(self.process_map, self.cpu_array)) by {
                    reveal(process_cpu_wf);
                };
                assert(self.process_management_inv());
                // ---- inv() direct conjuncts ----
                assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
                    reveal(cpu_dirty_map_contains_container_processes);
                    reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                    reveal(cpu_dirty_map_proc_pcid_match);
                    reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                    reveal(container_cpu_wf);
                };
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by {
                    reveal(tlb_wf_spec);
                };
                assert(self.inv());
            }
            // The release path is a user-visible no-op: the three unlocks
            // touch only lock state, not the cpu/process views read by
            // `kernel_k_to_kernel_u`. Delegate the projection equality to an
            // isolated lemma so its element-wise quantifier stays out of the
            // inv() proof's SMT query above.
            proof {
                // process_map / pagetable_map are untouched (the unlocks are
                // on cpu_array, container_map, allocator_4k_map).
                assert(self.process_map == old(self).process_map);
                assert(self.pagetable_map == old(self).pagetable_map);
                // cpu_array changed only at `cpu_id` (relative to its
                // pre-unlock snapshot, which equals the entry value).
                assert(self.cpu_array.unchanged_except(&cpu_array_before_unlock, cpu_id));
                assert(self.cpu_array.unchanged_except(&old(self).cpu_array, cpu_id));
                // cpu_id payload view preserved by `wunlock_ensures`.
                assert(self.cpu_array.spec_index(cpu_id).view().view()
                    == old(self).cpu_array.spec_index(cpu_id).view().view());
                assert(self.cpu_array.inv()) by { reveal(cpu_array_wf); };
                KernelK::lemma_release_preserves_user_view(*old(self), *self, cpu_id);
                assert(kernel_k_to_kernel_u(*old(self))
                    == kernel_k_to_kernel_u(*self));
            }
            // Close the user-view step (no kernel_step_boundary needed —
            // end_user_view_step accepts kernel-view Release directly).
            proof {
                steps.end_user_view_step(&*self, lctx.borrow_mut());
                // Surface the recorded-step facts for the postcondition.
                assert(steps.steps.len() > 0);
                assert(steps.steps.last().new_k == *self);
                assert(steps.steps.last().new_u == kernel_k_to_kernel_u(*self));
                assert(steps.steps.last().old_u == steps.steps.last().new_u);
            }
        }
    }
}
