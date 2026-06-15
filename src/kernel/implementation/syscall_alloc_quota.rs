use vstd::prelude::*;
use crate::*;
verus! {
    impl KernelK{
        // #[verifier::rlimit(600)]
        //
        // syscall_alloc_quota_4k: the calling thread asks to reserve
        // `alloc_amount` 4k pages of quota from its container's 4k page
        // allocator into its running process. Returns `true` on success,
        // `false` on any failure (container being torn down, process being
        // torn down, insufficient container quota, or per-process quota
        // overflow).
        //
        // Concurrency model (see veriflat-project-notes.md "User-view
        // linearization"): the syscall runs as one user-visible atomic
        // transition. It acquires locks in the deadlock-free order
        //   cpu  ->  container  ->  4k-allocator-quota  ->  process
        // (ascending LockId; see LockId.md), reads/decides, then RELEASES
        // every lock before returning. Somewhere in the section it
        // "linearizes" by opening a user-view step (begin_user_view_step),
        // which flips both lctx phases to Release; from that point no more
        // locks may be acquired, only released. The step is closed
        // (end_user_view_step) once inv() is re-established, recording the
        // post-section user view.
        //
        // Every exit path records exactly one user step:
        //  - FAILURE paths route through a `release_*_and_finish` helper;
        //    no kernel state changed, so `old_u == new_u` (a user-visible
        //    no-op).
        //  - SUCCESS path routes through `transfer_quota_4k_and_finish`
        //    which performs the transfer (`process.quota_4k += alloc_amount`,
        //    `quota.value -= alloc_amount`) before releasing. Since
        //    `kernel_k_to_kernel_u` reads `process.view().quota_4k`, the
        //    user view changes — `old_u` captures the pre-transfer
        //    projection and `new_u` the post-transfer one.
        //
        // Path summary (all branches verified):
        //  - container-killed → `release_cpu_and_finish` (1 lock held)
        //  - quota-insufficient → `release_all_and_finish` (3 locks held)
        //  - process-killed → `release_all_and_finish` (3 locks held; the
        //    failed wlock_process_unless_killed is a no-op on `self`)
        //  - process-quota-overflow → `release_all_with_process_and_finish`
        //    (4 locks held)
        //  - all checks passed → `transfer_quota_4k_and_finish` (4 locks
        //    held; opens user step, mutates, releases, closes step,
        //    returns true)
        #[verifier::spinoff_prover]
        pub fn syscall_alloc_quota_4k(&mut self, tracked mut lctx: Tracked<LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, alloc_amount: usize) -> (ret: RetValueType)
            requires
                cpu_id_valid(cpu_id),
                old(self).inv(),
                old(self).all_objects_unlocked(&lctx),
                old(self).cpu_array.spec_index(cpu_id).view().view().state == CpuState::Running,
                lctx.lock_map() == Map::<KernelObjId, LockId>::empty(),
                lctx.kernel_view_locking_state() is Acquire,
                lctx.user_view_locking_state() is Acquire,
                old(steps).steps.len() == 0,
                // Snapshot precondition: the caller hands us a fresh
                // snapshot equal to the syscall-entry user view. Anything
                // we do that mutates U has to be bracketed by
                // `begin/end_user_view_step` (which refresh the snapshot)
                // for the next `kernel_step_boundary` snapshot check to
                // succeed.
                old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
            ensures
                // The syscall linearizes as exactly one user-view atomic
                // step. The return value classifies the outcome:
                //
                //  - `Success`: quota transferred (`process.quota_4k +=
                //    alloc_amount`); user view changes by exactly that
                //    bump on the running process.
                //  - `ErrorContainerKilled`: container being torn down;
                //    user-visible no-op.
                //  - `ErrorContainerQuotaInsufficient`: container's 4k
                //    allocator has < alloc_amount; user-visible no-op.
                //  - `ErrorProcessKilled`: process being torn down;
                //    user-visible no-op.
                //  - `ErrorProcessQuotaOverflow`: adding alloc_amount to
                //    process.quota_4k would overflow `usize::MAX`;
                //    user-visible no-op.
                //
                // Every outcome records exactly one user step. Failure
                // outcomes are user-visible no-ops (`old_u == new_u`).
                // Success records the genuine quota_4k delta.
                final(steps).steps.len() == 1,
                final(steps).steps.last().new_k == *final(self),
                final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(self)),
                // The result must be one of these specific variants.
                ret is Success
                    || ret is ErrorContainerKilled
                    || ret is ErrorContainerQuotaInsufficient
                    || ret is ErrorProcessKilled
                    || ret is ErrorProcessQuotaOverflow,
                // Failure: user view unchanged.
                !(ret is Success) ==> {
                    &&& final(steps).steps.last().old_u == final(steps).steps.last().new_u
                },
                // Success: the transfer's exact user-view delta.
                ret is Success ==> {
                    let process_ptr = old(self).cpu_array.spec_index(cpu_id).view().view().current_process->Some_0;
                    &&& final(steps).steps.last().old_u == kernel_k_to_kernel_u(*old(self))
                    &&& kernel_u_only_process_quota_4k_changed(
                            final(steps).steps.last().old_u,
                            final(steps).steps.last().new_u,
                            process_ptr,
                            alloc_amount as int,
                        )
                },
        {
            // Lock preconditions and several reconstruction asserts need the
            // `subsystems_inv` conjuncts and the `all_objects_unlocked` pieces
            // for cpu_array / container / allocator / process. Revealing them
            // once here (function-wide) is markedly faster than re-revealing
            // per use.
            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
                reveal(process_perms_wf);
                assert(self.cpu_array.inv());
                assert(self.container_map.perms_wf());
                assert(self.allocator_4k_map.perms_wf());
                assert(self.process_map.perms_wf());
                reveal(cpu_objects_unlocked);
                reveal(container_objects_unlocked);
                reveal(allocator_objects_unlocked);
                reveal(process_objects_unlocked);
            }
            // Establish the entry well-formedness facts derived from the
            // global invariant: the running cpu's owning container exists,
            // it has a current process that exists, and the cpu/process/
            // container depth fields agree. These come from the bidirectional
            // container<->cpu, process<->cpu, and container<->process specs
            // (revealed in the `by` block) and are needed both for the lock
            // ordering below and for re-establishing inv() on the exit paths.
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

            // Snapshot the entry LocalContext so we can refer back to the
            // "all objects unlocked at entry" precondition after `lctx` has
            // been threaded through the lock/unlock calls. `thread_id` is
            // preserved by every op, so the entry unlocked-ness transfers.
            let ghost entry_lctx = lctx@;

            // ---- Acquire lock #1: the running cpu (lowest in lock order). ----
            // `wlock_cpu` is a thin wrapper around `LockedArray::wlock` for
            // `cpu_array` that re-establishes `inv()` after the lock — so no
            // manual inv block needed here.
            let Tracked(cpu_lock_perm) = self.wlock_cpu(cpu_id, Tracked(&mut lctx));
            let cpu = self.cpu_array.borrow(cpu_id, Tracked(&cpu_lock_perm));
            let thread_ptr = cpu.current_thread.unwrap();
            let process_ptr = cpu.current_process.unwrap();
            let container_ptr = cpu.owning_container;

            // ---- Re-establish inv() after the cpu wlock, before invoking the
            // container wrapper.
            //
            // Now that `wlock_cpu` is a wrapper that re-establishes `inv()`
            // for us, this manual block is no longer needed — leaving the
            // explanatory comment as a marker.

            // ---- Acquire lock #2: the owning container, UNLESS it is being
            // killed. `wlock_container_unless_killed` is a thin wrapper around
            // `LockedMap::wlock_unless_killed` for `container_map` that
            // re-establishes `inv()` after the lock attempt — see its contract
            // for the full pre/post breakdown. On the killed-branch it's a
            // complete no-op on `self`, both lctx phases are preserved
            // (Acquire/Acquire), and `lctx.lock_map` is unchanged.
            let container_res = self.wlock_container_unless_killed(container_ptr, Tracked(&mut lctx));
            if let (false, _) = container_res{
                // ===== CONTAINER-KILLED EXIT =====
                // The container is being torn down, so the syscall fails. Only
                // the cpu lock is held; hand off to `release_cpu_and_finish`,
                // which opens the user step, releases the cpu lock,
                // re-establishes inv() post-unlock, and closes the step —
                // recording a user-visible no-op.
                assert(self.container_map.spec_index(container_ptr).being_killed() == true);
                proof {
                    // The cpu lock is the only one held.
                    assert(lctx@.lock_map().dom() =~= set![ KernelObjId::Cpu(cpu_id) ]);
                }
                self.release_cpu_and_finish(
                    Tracked(lctx.get()),
                    Tracked(&mut *steps),
                    cpu_id,
                    Tracked(cpu_lock_perm),
                );
                return RetValueType::ErrorContainerKilled;
            }
            // ===== CONTAINER ACQUIRED =====
            // The container is alive and now write-locked by us (cpu + container
            // held). Read the container's 4k page allocator pointer from
            // rodata, take lock #3 on its quota, and decide whether the
            // requested `alloc_amount` fits.
            //
            // Lock order recap (deadlock-free; see LockId.md):
            //   cpu (held)  ->  container (held)  ->  quota (about to take).
            let Tracked(container_lock_perm) = container_res.1.unwrap();
            let container_ro = self.container_map.borrow_rodata(container_ptr);
            let alloc_ptr_4k = container_ro.borrow().allocator_ptr_4k;

            // `container_allocator_wf` gives, for the container's
            // `allocator_ptr_4k`: the entry exists in the 4k map, is wf, and
            // its quota's `container_depth` matches the container's depth
            // (needed below for the `lock_id_acyclic` ordering check). The
            // unlocked-ness fact is transferred from the entry precondition
            // `all_objects_unlocked` via the entry-lctx snapshot.
            assert(
                {
                    &&&
                    self.allocator_4k_map.dom().contains(alloc_ptr_4k)
                    &&&
                    self.allocator_4k_map.spec_index(alloc_ptr_4k).wf()
                    &&&
                    self.allocator_4k_map.spec_index(alloc_ptr_4k).quota.view().container_depth
                        == self.container_map.spec_index(container_ptr).view_rodata().view().depth
                    &&&
                    self.allocator_4k_map.spec_index(alloc_ptr_4k).quota.locked_by(&lctx) == false
                }
            ) by {
                reveal(container_allocator_wf);
                reveal(allocator_objects_unlocked);
                assert(old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.locked_by(&entry_lctx) == false);
            };

            // ---- Acquire lock #3: the container's 4k allocator quota
            // (via wrapper, which re-establishes inv() for us). ----
            let Tracked(quota_lock_perm) = self.wlock_quota_4k(alloc_ptr_4k, Tracked(&mut lctx));

            proof {
                // The 3 locks are the only ones held now.
                assert(lctx@.lock_map().dom() =~= set![
                    KernelObjId::Cpu(cpu_id),
                    KernelObjId::Container(container_ptr),
                    KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k),
                ]);
            }

            // Read the quota's value via a SHARED borrow (no `&mut self`
            // invalidation, so the inv() fact above carries through).
            let quota_ref = self.allocator_4k_map.borrow_quota(
                alloc_ptr_4k, Tracked(&quota_lock_perm),
            );
            if quota_ref.value < alloc_amount {
                // ===== INSUFFICIENT QUOTA =====
                // Fail the syscall and release all 3 locks. Still a
                // user-visible no-op (the user view doesn't include the
                // allocator quota).
                self.release_all_and_finish(
                    Tracked(lctx.get()),
                    Tracked(&mut *steps),
                    cpu_id, container_ptr, alloc_ptr_4k,
                    Tracked(quota_lock_perm),
                    Tracked(container_lock_perm),
                    Tracked(cpu_lock_perm),
                );
                return RetValueType::ErrorContainerQuotaInsufficient;
            }

            // ===== QUOTA SUFFICIENT — now check the running process's quota.
            // Lock the running process to read its current quota_4k. Lock
            // ordering: cpu(1) < container(101) < quota(102) < process(105),
            // so process is acquired LAST. Use the kill-aware wrapper:
            // a concurrent teardown could be racing with us, in which case
            // we treat the process as gone and bail out via the existing
            // 3-lock release helper.
            assert(
                {
                    &&& self.process_map.dom().contains(process_ptr)
                    &&& self.process_map.spec_index(process_ptr).locked_by(&lctx) == false
                }
            ) by {
                reveal(process_objects_unlocked);
                assert(old(self).process_map.spec_index(process_ptr).locked_by(&entry_lctx) == false);
            };
            let process_res = self.wlock_process_unless_killed(process_ptr, Tracked(&mut lctx));
            if let (false, _) = process_res {
                // ===== PROCESS KILLED =====
                // The process is being torn down. The wrapper restored the
                // process_map (false branch is a no-op on `self`), so only
                // cpu+container+quota are still held. Route through the
                // 3-lock release helper.
                self.release_all_and_finish(
                    Tracked(lctx.get()),
                    Tracked(&mut *steps),
                    cpu_id, container_ptr, alloc_ptr_4k,
                    Tracked(quota_lock_perm),
                    Tracked(container_lock_perm),
                    Tracked(cpu_lock_perm),
                );
                return RetValueType::ErrorProcessKilled;
            }
            let Tracked(process_lock_perm) = process_res.1.unwrap();

            // Read the process's existing 4k quota, then check whether
            // adding `alloc_amount` would overflow `usize::MAX`. The check
            // is written as `alloc_amount > usize::MAX - process.quota_4k`
            // to avoid the overflow itself.
            let process_ref = self.process_map.borrow(process_ptr, Tracked(&process_lock_perm));
            let process_quota_4k = process_ref.quota_4k;
            if alloc_amount > usize::MAX - process_quota_4k {
                // ===== PROCESS QUOTA OVERFLOW =====
                // Adding `alloc_amount` to this process's `quota_4k` would
                // overflow. Fail the syscall and release all 4 locks. Still
                // a user-visible no-op (no allocator/process state changed).
                self.release_all_with_process_and_finish(
                    Tracked(lctx.get()),
                    Tracked(&mut *steps),
                    cpu_id, container_ptr, process_ptr, alloc_ptr_4k,
                    Tracked(quota_lock_perm),
                    Tracked(container_lock_perm),
                    Tracked(cpu_lock_perm),
                    Tracked(process_lock_perm),
                );
                return RetValueType::ErrorProcessQuotaOverflow;
            }

            // ===== ALL CHECKS PASSED — perform the quota transfer =====
            // Hand off to the success-path helper, which performs the
            // mutations (process.quota_4k += alloc_amount, quota.value -=
            // alloc_amount), releases all 4 locks, and closes the
            // user-view atomic step. The bookkeeping facts the helper
            // requires (process_ptr ∈ container.owned_processes,
            // container's allocator_ptr_4k == alloc_ptr_4k) are derivable
            // from the running cpu's bidirectional invariants here.
            proof {
                reveal(process_cpu_wf);
                reveal(container_process_wf);
                assert(self.container_map.spec_index(container_ptr).view().owned_processes@.contains(process_ptr)) by {
                    assert(self.process_map.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr);
                };
                // Bridge: `kernel_k_to_kernel_u` reads only cpu_array
                // payload views, process_map views/rodata/being_killed,
                // and pagetable_map. None of those are affected by the 4
                // wlock acquisitions (which only changed lock state), so
                // the user-view projection is preserved across them.
                // Used downstream to lift the helper's
                // `old_u == kernel_k_to_kernel_u(*old(helper))` ensure
                // up to `*old(syscall)`.
                reveal(cpu_array_wf);
                assert(self.cpu_array.inv());
                assert(old(self).cpu_array.inv());
                assert(self.cpu_array.unchanged_except(&old(self).cpu_array, cpu_id));
                assert(self.cpu_array.spec_index(cpu_id).view().view()
                    == old(self).cpu_array.spec_index(cpu_id).view().view());
                assert forall|p_ptr: RwLockProcessPtr|
                    #![trigger self.process_map.spec_index(p_ptr).view()]
                    #![trigger self.process_map.spec_index(p_ptr).view_rodata()]
                    self.process_map.dom().contains(p_ptr)
                implies
                    self.process_map.spec_index(p_ptr).view() == old(self).process_map.spec_index(p_ptr).view()
                    && self.process_map.spec_index(p_ptr).view_rodata() == old(self).process_map.spec_index(p_ptr).view_rodata()
                by {};
                lemma_release_with_process_preserves_user_view(*old(self), *self, cpu_id);
                assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self)));
            }
            return self.transfer_quota_4k_and_finish(
                Tracked(lctx.get()),
                Tracked(&mut *steps),
                cpu_id, container_ptr, process_ptr, alloc_ptr_4k, alloc_amount,
                Tracked(quota_lock_perm),
                Tracked(container_lock_perm),
                Tracked(cpu_lock_perm),
                Tracked(process_lock_perm),
            );
        }

        /// Lemma: `container_thread_wf` is preserved when every container
        /// `view`/`view_rodata` is unchanged and the thread map is untouched
        /// (i.e. only container *lock state* moved). Isolated into its own
        /// proof query: this 4-quantifier reverse-direction reasoning is too
        /// heavy to discharge reliably inside the large `syscall_alloc_quota_4k`
        /// SMT query when the container is held write-locked.
        proof fn lemma_container_thread_wf_preserved(pre: KernelK, post: KernelK)
            requires
                container_thread_wf(pre.container_map, pre.thread_map),
                post.thread_map == pre.thread_map,
                post.container_map.dom() == pre.container_map.dom(),
                forall|c: RwLockContainerPtr|
                    #![trigger post.container_map.spec_index(c)]
                    post.container_map.dom().contains(c) ==>
                        post.container_map.spec_index(c).view() == pre.container_map.spec_index(c).view()
                        && post.container_map.spec_index(c).view_rodata() == pre.container_map.spec_index(c).view_rodata(),
            ensures
                container_thread_wf(post.container_map, post.thread_map),
        {
            reveal(container_thread_wf);
            assert(post.container_map.dom() =~= pre.container_map.dom());
            assert forall|c_ptr: RwLockContainerPtr, t_ptr: RwLockThreadPtr|
                #![trigger post.container_map.spec_index(c_ptr).view(), post.thread_map.spec_index(t_ptr).view()]
                post.container_map.dom().contains(c_ptr) && post.container_map.spec_index(c_ptr).view().owned_threads.view().contains(t_ptr)
            implies
                post.thread_map.dom().contains(t_ptr)
                && post.thread_map.spec_index(t_ptr).view().owning_container == c_ptr
                && post.thread_map.spec_index(t_ptr).view().container_depth == post.container_map.spec_index(c_ptr).view_rodata().view().depth
                && post.thread_map.spec_index(t_ptr).view().upper_container_seq == post.container_map.spec_index(c_ptr).view().uppertree_seq
            by {
                assert(post.container_map.spec_index(c_ptr).view() == pre.container_map.spec_index(c_ptr).view());
                assert(post.container_map.spec_index(c_ptr).view_rodata() == pre.container_map.spec_index(c_ptr).view_rodata());
            };
            assert forall|t_ptr: RwLockThreadPtr|
                #![trigger post.container_map.dom().contains(post.thread_map.spec_index(t_ptr).view().owning_container)]
                post.thread_map.dom().contains(t_ptr)
            implies
                post.container_map.dom().contains(post.thread_map.spec_index(t_ptr).view().owning_container)
                && post.container_map.spec_index(post.thread_map.spec_index(t_ptr).view().owning_container).view().owned_threads.view().contains(t_ptr)
            by {
                let oc = post.thread_map.spec_index(t_ptr).view().owning_container;
                assert(post.container_map.spec_index(oc).view() == pre.container_map.spec_index(oc).view());
            };
            assert forall|c_ptr: RwLockContainerPtr, t_ptr: RwLockThreadPtr|
                #![trigger post.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().contains(t_ptr)]
                post.container_map.dom().contains(c_ptr) && post.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().contains(t_ptr)
            implies
                post.thread_map.dom().contains(t_ptr) && post.thread_map.spec_index(t_ptr).view().upper_container_seq.view().contains(c_ptr)
            by {
                assert(post.container_map.spec_index(c_ptr).view() == pre.container_map.spec_index(c_ptr).view());
            };
            assert forall|t_ptr: RwLockThreadPtr, c_ptr: RwLockContainerPtr|
                #![trigger post.thread_map.spec_index(t_ptr).view().upper_container_seq.view().contains(c_ptr)]
                post.thread_map.dom().contains(t_ptr) && post.thread_map.spec_index(t_ptr).view().upper_container_seq.view().contains(c_ptr)
            implies
                post.container_map.dom().contains(c_ptr) && post.container_map.spec_index(c_ptr).view().owned_indirect_threads.view().contains(t_ptr)
            by {
                assert(post.container_map.spec_index(c_ptr).view() == pre.container_map.spec_index(c_ptr).view());
            };
        }
        /// Lemma: `container_endpoint_wf` is preserved when every container
        /// `view` is unchanged and the endpoint map is untouched. Isolated into
        /// its own query so this reverse-direction reasoning stays out of the
        /// large `syscall_alloc_quota_4k` SMT query.
        proof fn lemma_container_endpoint_wf_preserved(pre: KernelK, post: KernelK)
            requires
                container_endpoint_wf(pre.container_map, pre.endpoint_map),
                post.endpoint_map == pre.endpoint_map,
                post.container_map.dom() == pre.container_map.dom(),
                forall|c: RwLockContainerPtr|
                    #![trigger post.container_map.spec_index(c)]
                    post.container_map.dom().contains(c) ==>
                        post.container_map.spec_index(c).view() == pre.container_map.spec_index(c).view()
                        && post.container_map.spec_index(c).view_rodata() == pre.container_map.spec_index(c).view_rodata(),
            ensures
                container_endpoint_wf(post.container_map, post.endpoint_map),
        {
            reveal(container_endpoint_wf);
            assert(post.container_map.dom() =~= pre.container_map.dom());
            assert forall|c_ptr: RwLockContainerPtr, e_ptr: RwLockEndpointPtr|
                #![trigger post.container_map.spec_index(c_ptr).view().owned_endpoints.view().contains(e_ptr)]
                post.container_map.dom().contains(c_ptr) && post.container_map.spec_index(c_ptr).view().owned_endpoints.view().contains(e_ptr)
            implies
                post.endpoint_map.dom().contains(e_ptr) && post.endpoint_map.spec_index(e_ptr).view().owning_container == c_ptr
            by {
                assert(post.container_map.spec_index(c_ptr).view() == pre.container_map.spec_index(c_ptr).view());
            };
            assert forall|e_ptr: RwLockEndpointPtr|
                #![trigger post.container_map.dom().contains(post.endpoint_map.spec_index(e_ptr).view().owning_container)]
                post.endpoint_map.dom().contains(e_ptr)
            implies
                post.container_map.dom().contains(post.endpoint_map.spec_index(e_ptr).view().owning_container)
                && post.container_map.spec_index(post.endpoint_map.spec_index(e_ptr).view().owning_container).view().owned_endpoints.view().contains(e_ptr)
            by {
                let oc = post.endpoint_map.spec_index(e_ptr).view().owning_container;
                assert(post.container_map.spec_index(oc).view() == pre.container_map.spec_index(oc).view());
            };
        }
        /// Lemma: `container_scheduler_wf` is preserved when every container
        /// `view_rodata` is unchanged and the scheduler map is untouched.
        proof fn lemma_container_scheduler_wf_preserved(pre: KernelK, post: KernelK)
            requires
                container_scheduler_wf(pre.container_map, pre.scheduler_map),
                post.scheduler_map == pre.scheduler_map,
                post.container_map.dom() == pre.container_map.dom(),
                forall|c: RwLockContainerPtr|
                    #![trigger post.container_map.spec_index(c)]
                    post.container_map.dom().contains(c) ==>
                        post.container_map.spec_index(c).view() == pre.container_map.spec_index(c).view()
                        && post.container_map.spec_index(c).view_rodata() == pre.container_map.spec_index(c).view_rodata(),
            ensures
                container_scheduler_wf(post.container_map, post.scheduler_map),
        {
            reveal(container_scheduler_wf);
            assert(post.container_map.dom() =~= pre.container_map.dom());
            assert forall|c_ptr: RwLockContainerPtr|
                #![trigger post.container_map.spec_index(c_ptr).view_rodata().view().scheduler]
                post.container_map.dom().contains(c_ptr)
            implies
                post.scheduler_map.dom().contains(post.container_map.spec_index(c_ptr).view_rodata().view().scheduler)
                && post.scheduler_map.spec_index(post.container_map.spec_index(c_ptr).view_rodata().view().scheduler).view().owning_container == c_ptr
            by {
                assert(post.container_map.spec_index(c_ptr).view_rodata() == pre.container_map.spec_index(c_ptr).view_rodata());
            };
            assert forall|s_ptr: RwLockSchedulerPtr|
                #![trigger post.container_map.dom().contains(post.scheduler_map.spec_index(s_ptr).view().owning_container)]
                post.scheduler_map.dom().contains(s_ptr)
            implies
                post.container_map.dom().contains(post.scheduler_map.spec_index(s_ptr).view().owning_container)
                && post.container_map.spec_index(post.scheduler_map.spec_index(s_ptr).view().owning_container).view_rodata().view().scheduler == s_ptr
            by {
                let oc = post.scheduler_map.spec_index(s_ptr).view().owning_container;
                assert(post.container_map.spec_index(oc).view_rodata() == pre.container_map.spec_index(oc).view_rodata());
            };
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

        /// Wrapper around `LockedMap::wlock_unless_killed` for `container_map`
        /// that re-establishes the kernel-wide `inv()` after the lock attempt.
        ///
        /// The motivation: post-`wlock_unless_killed`, every caller has to run
        /// the same large reveal-laden proof block to lift `unchanged_except`
        /// (lock state on one container changed) back to `KernelK::inv()`.
        /// That block reveals every bidirectional `container ↔ X` invariant
        /// and calls the cpu-independent `lemma_container_*_wf_preserved`
        /// helpers below. Factoring it into this wrapper means call sites just
        /// dispatch on the returned `bool` — no proof block needed.
        ///
        /// Behaviour exactly mirrors `LockedMap::wlock_unless_killed`:
        ///  * SUCCESS (`ret.0 == true`): the container is now write-locked by
        ///    the calling thread; `lctx.lock_map` gained the new entry; the
        ///    returned perm carries the write-lock witness; every kernel field
        ///    other than `container_map` is byte-for-byte unchanged; only
        ///    `container_map[container_ptr]`'s lock state moved (view, rodata,
        ///    every other entry preserved).
        ///  * FAILURE (`ret.0 == false`): the container is being killed; the
        ///    `LockedMap` is fully restored to its entry value (no-op on
        ///    `self`); `lctx.lock_map` is unchanged; the returned `Option`
        ///    is `None`. Every other field is also unchanged.
        ///
        /// Both branches preserve `lctx.kernel_view_locking_state()` and
        /// `lctx.user_view_locking_state()` (Acquire ↔ Acquire / Release ↔
        /// Release), and preserve `lctx.thread_id()`.
        ///
        /// Preconditions match `wlock_unless_killed` plus `self.inv()`. The
        /// `lock_id_acyclic` clause is unavoidable — it encodes the global
        /// lock-ordering check, which depends on what locks the caller already
        /// holds, so the caller must establish it.
        #[verifier::spinoff_prover]
        pub fn wlock_container_unless_killed(
            &mut self,
            container_ptr: RwLockContainerPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: (bool, Option<Tracked<LockPerm>>))
            requires
                old(self).inv(),
                old(self).container_map.dom().contains(container_ptr),
                old(self).container_map.spec_index(container_ptr).locked_by(old(lctx)) == false,
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).user_view_locking_state() is Acquire,
                old(lctx).lock_id_acyclic(LockId{
                    container: old(self).container_map@[container_ptr].container_depth(),
                    process: old(self).container_map@[container_ptr].process_depth(),
                    major: old(self).container_map@[container_ptr].value()@.current_lock_major(),
                    minor: container_ptr,
                }),
                old(lctx).obj_id_fresh(KernelObjId::Container(container_ptr)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Field framing: only container_map's lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).scheduler_map     == old(self).scheduler_map,
                final(self).process_map       == old(self).process_map,
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_4k_map  == old(self).allocator_4k_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- container_map: only the targeted entry's lock state
                // ---- (success) or nothing at all (failure) changed.
                final(self).container_map.unchanged_except(&old(self).container_map, container_ptr),
                final(self).container_map.perms_wf(),

                // ---- LocalContext phase preservation ----
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),

                // ---- Failure: container is being killed; complete no-op ----
                ret.0 == false ==>
                {
                    &&& old(self).container_map.spec_index(container_ptr).being_killed() == true
                    &&& final(self).container_map.spec_index(container_ptr) == old(self).container_map.spec_index(container_ptr)
                    &&& ret.1 is None
                    &&& final(lctx).lock_map() =~= old(lctx).lock_map()
                },

                // ---- Success: container locked by us, perm returned ----
                ret.0 == true ==>
                {
                    &&& old(self).container_map.spec_index(container_ptr).being_killed() == false
                    &&& ret.1 is Some
                    &&& wlock_ensures(
                        old(self).container_map.spec_index(container_ptr),
                        final(self).container_map.spec_index(container_ptr),
                        LockId{
                            container: old(self).container_map@[container_ptr].container_depth(),
                            process: old(self).container_map@[container_ptr].process_depth(),
                            major: old(self).container_map@[container_ptr].value()@.current_lock_major(),
                            minor: container_ptr,
                        },
                        final(lctx).thread_id(),
                        ret.1.unwrap()@,
                    )
                    &&& lock_ensures(
                        old(lctx),
                        final(lctx),
                        old(self).container_map.spec_index(container_ptr).view(),
                        LockId{
                            container: old(self).container_map@[container_ptr].container_depth(),
                            process: old(self).container_map@[container_ptr].process_depth(),
                            major: old(self).container_map@[container_ptr].value()@.current_lock_major(),
                            minor: container_ptr,
                        },
                        KernelObjId::Container(container_ptr),
                    )
                },
        {
            // Reveals needed for the inv() re-establishment block below;
            // hoisted here so they're in scope for both the call and the
            // proof block.
            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
            }
            let res = self.container_map.wlock_unless_killed(
                container_ptr,
                Tracked(&mut *lctx),
                Ghost(KernelObjId::Container(container_ptr)),
            );
            // Re-establish inv(). The only change to `self` since entry is
            // *lock state on container_map[container_ptr]* (success branch)
            // or nothing at all (failure branch — wlock_unless_killed fully
            // restores the LockedMap on a killed container). Every payload
            // view, every rodata, every other LockedMap entry, and every
            // other KernelK field is unchanged. Same proof template as the
            // one originally inlined in `syscall_alloc_quota_4k` after the
            // wlock_unless_killed call.
            proof {
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
                KernelK::lemma_container_endpoint_wf_preserved(*old(self), *self);
                assert(container_cpu_wf(self.container_map, self.cpu_array)) by {
                    reveal(container_cpu_wf);
                };
                assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
                    reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
                    reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf);
                };
                KernelK::lemma_container_scheduler_wf_preserved(*old(self), *self);
                assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
                    reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
                };
                KernelK::lemma_container_thread_wf_preserved(*old(self), *self);
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
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
                assert(self.inv());
            }
            res
        }

        /// Companion of `wlock_container_unless_killed` for the unlock side.
        ///
        /// Wraps `LockedMap::wunlock` for `container_map` and re-establishes
        /// the kernel-wide `inv()` immediately afterwards. The motivation is
        /// the same: every caller would otherwise have to run the same
        /// reveal-laden proof block to lift `unchanged_except` (lock state
        /// on one container moved from `WriteLock` to `None`) back to
        /// `KernelK::inv()`. Wrapping it once means callers just call
        /// `self.wunlock_container(...)` and `inv()` is re-established for
        /// them.
        ///
        /// What changes in this lock phase:
        ///  * `container_map[container_ptr]`'s `locking_thread()` becomes
        ///    `None`; its payload view, rodata, and ghost state are all
        ///    preserved (`wunlock_ensures`).
        ///  * Every other entry of `container_map` is byte-equal pre/post
        ///    (`unchanged_except`).
        ///  * Every other `KernelK` field is byte-equal pre/post.
        ///  * `lctx.lock_map` loses the entry for
        ///    `KernelObjId::Container(container_ptr)`; the lock_seq has the
        ///    corresponding lock id removed (encapsulated by `unlock_ensures`).
        ///  * Both lctx phases are preserved as-is — note that the caller
        ///    must ALREADY have flipped `user_view_locking_state` to Release
        ///    (the standard linearization-point precondition for unlocking
        ///    a user-visible object), enforced via `unlock_requires`.
        #[verifier::spinoff_prover]
        pub fn wunlock_container(
            &mut self,
            container_ptr: RwLockContainerPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                old(self).container_map.dom().contains(container_ptr),
                old(self).container_map.spec_index(container_ptr).wlocked_by(old(lctx)),
                unlock_requires::<Container>(old(lctx)),
                lock_perm@.state() is WriteLock,
                lock_perm@.thread_id() == old(lctx).thread_id(),
                lock_perm@.lock_id() == old(self).container_map.spec_index(container_ptr).locking_thread()->Write_lock_id,
                old(lctx).lock_map().dom().contains(KernelObjId::Container(container_ptr)),
                old(lctx).lock_map()[KernelObjId::Container(container_ptr)] == lock_perm@.lock_id(),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Field framing: only container_map's lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).scheduler_map     == old(self).scheduler_map,
                final(self).process_map       == old(self).process_map,
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_4k_map  == old(self).allocator_4k_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- container_map: only the targeted entry's lock state changed ----
                final(self).container_map.unchanged_except(&old(self).container_map, container_ptr),
                final(self).container_map.perms_wf(),
                final(self).container_map.spec_index(container_ptr).locking_thread() is None,
                wunlock_ensures(
                    old(self).container_map.spec_index(container_ptr),
                    final(self).container_map.spec_index(container_ptr),
                ),

                // ---- LocalContext: lock dropped, phases preserved ----
                unlock_ensures(
                    old(lctx),
                    final(lctx),
                    final(self).container_map.spec_index(container_ptr).view(),
                    lock_perm@.lock_id(),
                    KernelObjId::Container(container_ptr),
                ),
        {
            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
            }
            self.container_map.wunlock(
                container_ptr,
                Tracked(&mut *lctx),
                lock_perm,
                Ghost(KernelObjId::Container(container_ptr)),
            );
            // Re-establish inv(). The only change to `self` since entry is
            // *lock state on container_map[container_ptr]*: it went from
            // WriteLock(us) to None. Every payload view, every rodata, every
            // other LockedMap entry, and every other KernelK field is
            // unchanged. Same proof template as wlock_container_unless_killed.
            proof {
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
                KernelK::lemma_container_endpoint_wf_preserved(*old(self), *self);
                assert(container_cpu_wf(self.container_map, self.cpu_array)) by {
                    reveal(container_cpu_wf);
                };
                assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
                    reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
                    reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf);
                };
                KernelK::lemma_container_scheduler_wf_preserved(*old(self), *self);
                assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
                    reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
                };
                KernelK::lemma_container_thread_wf_preserved(*old(self), *self);
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
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
                assert(self.inv());
            }
        }

        /// Wrapper around `LockedArray::wlock` for `cpu_array` that
        /// re-establishes the kernel-wide `inv()` after the lock attempt.
        ///
        /// Same shape as `wlock_container_unless_killed`, but for the cpu
        /// array. The cpu array is `LockedArray<Cpu, …, NUM_CPUS,
        /// CPU_HAS_KILL_STATE>` and is unlocked with the plain
        /// `wlock`/`wunlock` (NO_KILL API), so this wrapper has no
        /// killed-branch return.
        ///
        /// What changes in this lock phase:
        ///  * `cpu_array[cpu_id]`'s lock state moves from None to
        ///    `WriteLock(us)`; its payload view, rodata, and ghost state are
        ///    all preserved.
        ///  * Every other element of `cpu_array` is byte-equal pre/post
        ///    (`unchanged_except`).
        ///  * Every other `KernelK` field is byte-equal pre/post.
        ///  * `lctx.lock_map` gains the entry for `KernelObjId::Cpu(cpu_id)`;
        ///    `lctx.lock_seq` gains the corresponding lock id (encapsulated
        ///    by `lock_ensures`).
        ///  * Both lctx phases are preserved.
        #[verifier::spinoff_prover]
        pub fn wlock_cpu(
            &mut self,
            cpu_id: CpuId,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Tracked<LockPerm>)
            requires
                old(self).inv(),
                cpu_id_valid(cpu_id),
                wlock_requires(old(self).cpu_array[cpu_id]@, old(lctx)),
                old(lctx).lock_id_acyclic(LockId{
                    container: old(self).cpu_array[cpu_id].container_depth(),
                    process: old(self).cpu_array[cpu_id].process_depth(),
                    major: old(self).cpu_array[cpu_id]@@.current_lock_major(),
                    minor: old(self).cpu_array[cpu_id].lock_minor(),
                }),
                old(lctx).obj_id_fresh(KernelObjId::Cpu(cpu_id)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Field framing: only cpu_array's lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).scheduler_map     == old(self).scheduler_map,
                final(self).process_map       == old(self).process_map,
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_4k_map  == old(self).allocator_4k_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- cpu_array: only the targeted slot's lock state changed ----
                final(self).cpu_array.unchanged_except(&old(self).cpu_array, cpu_id),
                final(self).cpu_array.inv(),

                // ---- LocalContext: phases preserved ----
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),

                // ---- The lock perm + lock ensures (forwarded from LockedArray::wlock) ----
                wlock_ensures(
                    old(self).cpu_array[cpu_id]@,
                    final(self).cpu_array[cpu_id]@,
                    LockId{
                        container: old(self).cpu_array[cpu_id].container_depth(),
                        process: old(self).cpu_array[cpu_id].process_depth(),
                        major: old(self).cpu_array[cpu_id]@@.current_lock_major(),
                        minor: old(self).cpu_array[cpu_id].lock_minor(),
                    },
                    final(lctx).thread_id(),
                    ret@,
                ),
                lock_ensures(
                    old(lctx),
                    final(lctx),
                    final(self).cpu_array[cpu_id]@@,
                    LockId{
                        container: old(self).cpu_array[cpu_id].container_depth(),
                        process: old(self).cpu_array[cpu_id].process_depth(),
                        major: old(self).cpu_array[cpu_id]@@.current_lock_major(),
                        minor: old(self).cpu_array[cpu_id].lock_minor(),
                    },
                    KernelObjId::Cpu(cpu_id),
                ),
        {
            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
            }
            let ret = self.cpu_array.wlock(cpu_id, Tracked(&mut *lctx), Ghost(KernelObjId::Cpu(cpu_id)));
            // Re-establish inv(). Only `cpu_array[cpu_id]`'s lock state
            // moved; every payload view, every other slot, and every other
            // KernelK field is unchanged.
            proof {
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
                KernelK::lemma_container_endpoint_wf_preserved(*old(self), *self);
                assert(container_cpu_wf(self.container_map, self.cpu_array)) by {
                    reveal(container_cpu_wf);
                };
                assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
                    reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
                    reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf);
                };
                KernelK::lemma_container_scheduler_wf_preserved(*old(self), *self);
                assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
                    reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
                };
                KernelK::lemma_container_thread_wf_preserved(*old(self), *self);
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
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
                assert(self.inv());
            }
            ret
        }

        /// Companion of `wlock_cpu` for the unlock side. Wraps
        /// `LockedArray::wunlock` for `cpu_array` and re-establishes the
        /// kernel-wide `inv()` immediately afterwards.
        ///
        /// What changes in this lock phase:
        ///  * `cpu_array[cpu_id]`'s `locking_thread()` becomes `None`; its
        ///    payload view, rodata, and ghost state are all preserved
        ///    (`wunlock_ensures`).
        ///  * Every other element of `cpu_array` is byte-equal pre/post.
        ///  * Every other `KernelK` field is byte-equal pre/post.
        ///  * `lctx.lock_map` loses the entry for `KernelObjId::Cpu(cpu_id)`;
        ///    `lctx.lock_seq` has the corresponding lock id removed
        ///    (encapsulated by `unlock_ensures`).
        ///  * Both lctx phases are preserved as-is — caller must already have
        ///    flipped `user_view_locking_state` to Release.
        #[verifier::spinoff_prover]
        pub fn wunlock_cpu(
            &mut self,
            cpu_id: CpuId,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                cpu_id_valid(cpu_id),
                old(self).cpu_array[cpu_id]@.wlocked_by(old(lctx)),
                old(self).cpu_array[cpu_id]@.being_killed() == false,
                unlock_requires::<Cpu>(old(lctx)),
                lock_perm@.state() is WriteLock,
                lock_perm@.thread_id() == old(lctx).thread_id(),
                lock_perm@.lock_id() == old(self).cpu_array[cpu_id]@.locking_thread()->Write_lock_id,
                old(lctx).lock_map().dom().contains(KernelObjId::Cpu(cpu_id)),
                old(lctx).lock_map()[KernelObjId::Cpu(cpu_id)] == lock_perm@.lock_id(),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Field framing: only cpu_array's lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).scheduler_map     == old(self).scheduler_map,
                final(self).process_map       == old(self).process_map,
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_4k_map  == old(self).allocator_4k_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- cpu_array: only the targeted slot's lock state changed ----
                final(self).cpu_array.unchanged_except(&old(self).cpu_array, cpu_id),
                final(self).cpu_array.inv(),
                final(self).cpu_array[cpu_id]@.locking_thread() is None,
                wunlock_ensures(
                    old(self).cpu_array[cpu_id]@,
                    final(self).cpu_array[cpu_id]@,
                ),

                // ---- LocalContext: lock dropped, phases preserved ----
                unlock_ensures(
                    old(lctx),
                    final(lctx),
                    final(self).cpu_array[cpu_id]@@,
                    lock_perm@.lock_id(),
                    KernelObjId::Cpu(cpu_id),
                ),
        {
            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
            }
            self.cpu_array.wunlock(cpu_id, Tracked(&mut *lctx), lock_perm, Ghost(KernelObjId::Cpu(cpu_id)));
            // Re-establish inv(). Only `cpu_array[cpu_id]`'s lock state moved;
            // every payload view, every other slot, and every other KernelK
            // field is unchanged. Same template as wlock_cpu.
            proof {
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
                KernelK::lemma_container_endpoint_wf_preserved(*old(self), *self);
                assert(container_cpu_wf(self.container_map, self.cpu_array)) by {
                    reveal(container_cpu_wf);
                };
                assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
                    reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
                    reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf);
                };
                KernelK::lemma_container_scheduler_wf_preserved(*old(self), *self);
                assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
                    reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
                };
                KernelK::lemma_container_thread_wf_preserved(*old(self), *self);
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
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
                assert(self.inv());
            }
        }

        /// Wrapper around `LockedMap::wlock_unless_killed` for `process_map`
        /// that re-establishes the kernel-wide `inv()` after the lock attempt.
        ///
        /// Same shape as `wlock_container_unless_killed`, but for the process
        /// map.
        ///
        /// Behaviour mirrors `LockedMap::wlock_unless_killed`:
        ///  * SUCCESS (`ret.0 == true`): the process is now write-locked by us;
        ///    `lctx.lock_map` gained the new entry; the returned perm carries
        ///    the write-lock witness; every kernel field other than
        ///    `process_map` is byte-for-byte unchanged; only
        ///    `process_map[process_ptr]`'s lock state moved (view, rodata,
        ///    every other entry preserved).
        ///  * FAILURE (`ret.0 == false`): the process is being killed; the
        ///    `LockedMap` is fully restored to its entry value (no-op on
        ///    `self`); `lctx.lock_map` is unchanged; the returned `Option`
        ///    is `None`. Every other field is also unchanged.
        ///
        /// Both branches preserve `lctx.kernel_view_locking_state()` and
        /// `lctx.user_view_locking_state()`, and preserve `lctx.thread_id()`.
        #[verifier::spinoff_prover]
        pub fn wlock_process_unless_killed(
            &mut self,
            process_ptr: RwLockProcessPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: (bool, Option<Tracked<LockPerm>>))
            requires
                old(self).inv(),
                old(self).process_map.dom().contains(process_ptr),
                old(self).process_map.spec_index(process_ptr).locked_by(old(lctx)) == false,
                old(lctx).kernel_view_locking_state() is Acquire,
                old(lctx).user_view_locking_state() is Acquire,
                old(lctx).lock_id_acyclic(LockId{
                    container: old(self).process_map@[process_ptr].container_depth(),
                    process: old(self).process_map@[process_ptr].process_depth(),
                    major: old(self).process_map@[process_ptr].value()@.current_lock_major(),
                    minor: process_ptr,
                }),
                old(lctx).obj_id_fresh(KernelObjId::Process(process_ptr)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Field framing: only process_map's lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).scheduler_map     == old(self).scheduler_map,
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_4k_map  == old(self).allocator_4k_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- process_map: only the targeted entry's lock state changed ----
                final(self).process_map.unchanged_except(&old(self).process_map, process_ptr),
                final(self).process_map.perms_wf(),

                // ---- LocalContext phase preservation ----
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),

                // ---- Failure: process is being killed; complete no-op ----
                ret.0 == false ==>
                {
                    &&& old(self).process_map.spec_index(process_ptr).being_killed() == true
                    &&& final(self).process_map.spec_index(process_ptr) == old(self).process_map.spec_index(process_ptr)
                    &&& ret.1 is None
                    &&& final(lctx).lock_map() =~= old(lctx).lock_map()
                },

                // ---- Success: process locked by us, perm returned ----
                ret.0 == true ==>
                {
                    &&& old(self).process_map.spec_index(process_ptr).being_killed() == false
                    &&& ret.1 is Some
                    &&& wlock_ensures(
                        old(self).process_map.spec_index(process_ptr),
                        final(self).process_map.spec_index(process_ptr),
                        LockId{
                            container: old(self).process_map@[process_ptr].container_depth(),
                            process: old(self).process_map@[process_ptr].process_depth(),
                            major: old(self).process_map@[process_ptr].value()@.current_lock_major(),
                            minor: process_ptr,
                        },
                        final(lctx).thread_id(),
                        ret.1.unwrap()@,
                    )
                    &&& lock_ensures(
                        old(lctx),
                        final(lctx),
                        old(self).process_map.spec_index(process_ptr).view(),
                        LockId{
                            container: old(self).process_map@[process_ptr].container_depth(),
                            process: old(self).process_map@[process_ptr].process_depth(),
                            major: old(self).process_map@[process_ptr].value()@.current_lock_major(),
                            minor: process_ptr,
                        },
                        KernelObjId::Process(process_ptr),
                    )
                },
        {
            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
                reveal(process_perms_wf);
            }
            let res = self.process_map.wlock_unless_killed(
                process_ptr,
                Tracked(&mut *lctx),
                Ghost(KernelObjId::Process(process_ptr)),
            );
            // Re-establish inv(). Only `process_map[process_ptr]`'s lock state
            // moved (success branch) or nothing at all (failure branch).
            // container_map and every other field is byte-equal pre/post.
            // Most conjuncts verify via the same reveal pattern as the
            // container wrappers; `container_process_page_pagetable_wf` needs
            // additional reveals on `mapped_*_page_pagetable_wf` to bridge
            // "pt_ptr in mappings ⇒ pt_ptr in pagetable_map.dom()", and
            // `per_container_process_tree_wf` is discharged via the existing
            // `process_no_change_to_tree_fields_imply_wf` lemma. The
            // `container_process_allocator_quota_wf` conjunct uses a
            // narrowly-scoped trusted axiom in spec_util.rs — it's a Set::fold
            // over `owned_processes` summing per-process quotas, which Verus
            // can't reason through without fold extensionality.
            proof {
                assert forall|p_ptr: RwLockProcessPtr|
                    #![trigger self.process_map.spec_index(p_ptr).view()]
                    #![trigger self.process_map.spec_index(p_ptr).view_rodata()]
                    self.process_map.dom().contains(p_ptr)
                implies
                    self.process_map.spec_index(p_ptr).view() == old(self).process_map.spec_index(p_ptr).view()
                    && self.process_map.spec_index(p_ptr).view_rodata() == old(self).process_map.spec_index(p_ptr).view_rodata()
                by {};
                // ---- subsystems_inv ----
                assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
                assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
                assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
                assert(process_perms_wf(self.process_map)) by { reveal(process_perms_wf); };
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
                    reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
                };
                assert(self.container_pages_wf()) by {
                    reveal(KernelK::container_pages_wf);
                };
                assert(self.process_pages_wf()) by {
                    reveal(KernelK::process_pages_wf);
                };
                assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    lemma_container_process_allocator_quota_wf_preserved_for_process_lock_op(*old(self), *self);
                };
                assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    reveal(container_allocator_wf);
                };
                assert(self.allocator_free_pages_wf());
                assert(process_pagetable_match(self.process_map, self.pagetable_map)) by {
                    reveal(process_pagetable_match);
                };
                assert(self.memory_management_inv());
                // ---- process_management_inv ----
                assert(container_tree_wf(self.root_container, self.container_map));
                assert(container_process_wf(self.container_map, self.process_map)) by {
                    reveal(container_process_wf);
                };
                assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                    reveal(container_process_wf); reveal(per_container_process_tree_wf);
                    // pre.inv() gives the pre-state spec; bring it into scope explicitly.
                    assert(per_container_process_tree_wf(old(self).container_map, old(self).process_map));
                    assert forall|c_ptr: RwLockContainerPtr|
                        self.container_map.dom().contains(c_ptr)
                    implies
                        process_tree_wf(
                            self.container_map.spec_index(c_ptr).view().root_process,
                            self.container_map.spec_index(c_ptr).view().owned_processes@,
                            self.process_map,
                        )
                    by {
                        // owned_processes for c_ptr ⊆ process_map.dom() (from container_process_wf,
                        // revealed above; process_map.dom() unchanged so it's also a subset of
                        // post.process_map.dom()). Per-process view + view_rodata equality is
                        // asserted at the top of this proof block, so feed it to the
                        // tree-fields preservation lemma.
                        process_no_change_to_tree_fields_imply_wf(
                            self.container_map.spec_index(c_ptr).view().root_process,
                            self.container_map.spec_index(c_ptr).view().owned_processes@,
                            old(self).process_map,
                            self.process_map,
                        );
                    };
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
                };
                assert(process_cpu_wf(self.process_map, self.cpu_array)) by {
                    reveal(process_cpu_wf);
                };
                assert(process_thread_wf(self.process_map, self.thread_map)) by {
                    reveal(process_thread_wf);
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
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
                assert(self.inv());
            }
            res
        }

        /// Companion of `wlock_process_unless_killed` for the unlock side.
        /// Wraps `LockedMap::wunlock` for `process_map` and re-establishes
        /// the kernel-wide `inv()` immediately afterwards.
        ///
        /// What changes in this lock phase:
        ///  * `process_map[process_ptr]`'s `locking_thread()` becomes `None`;
        ///    its payload view, rodata, and ghost state are all preserved.
        ///  * Every other entry of `process_map` is byte-equal pre/post.
        ///  * Every other `KernelK` field is byte-equal pre/post.
        ///  * `lctx.lock_map` loses the entry for
        ///    `KernelObjId::Process(process_ptr)`.
        ///  * Both lctx phases are preserved as-is — caller must already have
        ///    flipped `user_view_locking_state` to Release.
        #[verifier::spinoff_prover]
        pub fn wunlock_process(
            &mut self,
            process_ptr: RwLockProcessPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                old(self).process_map.dom().contains(process_ptr),
                old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
                unlock_requires::<Process>(old(lctx)),
                lock_perm@.state() is WriteLock,
                lock_perm@.thread_id() == old(lctx).thread_id(),
                lock_perm@.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
                old(lctx).lock_map().dom().contains(KernelObjId::Process(process_ptr)),
                old(lctx).lock_map()[KernelObjId::Process(process_ptr)] == lock_perm@.lock_id(),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Field framing: only process_map's lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).scheduler_map     == old(self).scheduler_map,
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_4k_map  == old(self).allocator_4k_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- process_map: only the targeted entry's lock state changed ----
                final(self).process_map.unchanged_except(&old(self).process_map, process_ptr),
                final(self).process_map.perms_wf(),
                final(self).process_map.spec_index(process_ptr).locking_thread() is None,
                wunlock_ensures(
                    old(self).process_map.spec_index(process_ptr),
                    final(self).process_map.spec_index(process_ptr),
                ),

                // ---- LocalContext: lock dropped, phases preserved ----
                unlock_ensures(
                    old(lctx),
                    final(lctx),
                    final(self).process_map.spec_index(process_ptr).view(),
                    lock_perm@.lock_id(),
                    KernelObjId::Process(process_ptr),
                ),
        {
            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
                reveal(process_perms_wf);
            }
            self.process_map.wunlock(
                process_ptr,
                Tracked(&mut *lctx),
                lock_perm,
                Ghost(KernelObjId::Process(process_ptr)),
            );
            // Re-establish inv(). Only `process_map[process_ptr]`'s lock state
            // moved; every payload view, every other entry, and every other
            // KernelK field is unchanged. Same template as
            // wlock_process_unless_killed.
            proof {
                assert forall|p_ptr: RwLockProcessPtr|
                    #![trigger self.process_map.spec_index(p_ptr).view()]
                    #![trigger self.process_map.spec_index(p_ptr).view_rodata()]
                    self.process_map.dom().contains(p_ptr)
                implies
                    self.process_map.spec_index(p_ptr).view() == old(self).process_map.spec_index(p_ptr).view()
                    && self.process_map.spec_index(p_ptr).view_rodata() == old(self).process_map.spec_index(p_ptr).view_rodata()
                by {};
                // ---- subsystems_inv ----
                assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
                assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
                assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
                assert(process_perms_wf(self.process_map)) by { reveal(process_perms_wf); };
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
                    reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
                };
                assert(self.container_pages_wf()) by {
                    reveal(KernelK::container_pages_wf);
                };
                assert(self.process_pages_wf()) by {
                    reveal(KernelK::process_pages_wf);
                };
                assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    lemma_container_process_allocator_quota_wf_preserved_for_process_lock_op(*old(self), *self);
                };
                assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    reveal(container_allocator_wf);
                };
                assert(self.allocator_free_pages_wf());
                assert(process_pagetable_match(self.process_map, self.pagetable_map)) by {
                    reveal(process_pagetable_match);
                };
                assert(self.memory_management_inv());
                // ---- process_management_inv ----
                assert(container_tree_wf(self.root_container, self.container_map));
                assert(container_process_wf(self.container_map, self.process_map)) by {
                    reveal(container_process_wf);
                };
                assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                    reveal(container_process_wf); reveal(per_container_process_tree_wf);
                    assert(per_container_process_tree_wf(old(self).container_map, old(self).process_map));
                    assert forall|c_ptr: RwLockContainerPtr|
                        self.container_map.dom().contains(c_ptr)
                    implies
                        process_tree_wf(
                            self.container_map.spec_index(c_ptr).view().root_process,
                            self.container_map.spec_index(c_ptr).view().owned_processes@,
                            self.process_map,
                        )
                    by {
                        process_no_change_to_tree_fields_imply_wf(
                            self.container_map.spec_index(c_ptr).view().root_process,
                            self.container_map.spec_index(c_ptr).view().owned_processes@,
                            old(self).process_map,
                            self.process_map,
                        );
                    };
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
                };
                assert(process_cpu_wf(self.process_map, self.cpu_array)) by {
                    reveal(process_cpu_wf);
                };
                assert(process_thread_wf(self.process_map, self.thread_map)) by {
                    reveal(process_thread_wf);
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
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
                assert(self.inv());
            }
        }

        /// Wrapper around `UnLockedMap::wlock_quota` for `allocator_4k_map`
        /// that re-establishes `inv()` after the lock attempt. Same shape as
        /// `wlock_cpu` / `wlock_container_unless_killed`. The 4k allocator
        /// quota uses no kill state, so there's no killed-branch return.
        ///
        /// What changes in this lock phase:
        ///  * `allocator_4k_map[alloc_ptr_4k].quota`'s lock state moves from
        ///    None to `WriteLock(us)`; its payload view, rodata, ghost state
        ///    are all preserved.
        ///  * Every other entry of `allocator_4k_map` is byte-equal pre/post.
        ///  * The touched allocator's other fields (cpu_caches, global_poll,
        ///    owning_container, differential, total_free_pages) are byte-equal.
        ///  * Every other `KernelK` field is byte-equal pre/post.
        ///  * `lctx.lock_map` gains the entry for
        ///    `KernelObjId::AllocatorQuota(SZ4k, alloc_ptr_4k)`; lock_seq
        ///    gains the corresponding lock id (encapsulated by `lock_ensures`).
        ///  * Both lctx phases are preserved.
        #[verifier::spinoff_prover]
        pub fn wlock_quota_4k(
            &mut self,
            alloc_ptr_4k: RwLockPageAllocatorPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
        ) -> (ret: Tracked<LockPerm>)
            requires
                old(self).inv(),
                old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
                wlock_requires(old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota, old(lctx)),
                old(lctx).lock_id_acyclic(LockId{
                    container: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota@.container_depth(),
                    process: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota@.process_depth(),
                    major: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota@.current_lock_major(),
                    minor: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota@.lock_minor(),
                }),
                old(lctx).obj_id_fresh(KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k)),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Field framing: only allocator_4k_map's quota lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).scheduler_map     == old(self).scheduler_map,
                final(self).process_map       == old(self).process_map,
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- allocator_4k_map: dom unchanged; only the targeted entry's quota lock state changed ----
                final(self).allocator_4k_map.dom() == old(self).allocator_4k_map.dom(),
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).owning_container == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).owning_container,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).differential == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).differential,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages,
                forall|k: usize| #![auto] old(self).allocator_4k_map.dom().contains(k) && k != alloc_ptr_4k ==>
                    final(self).allocator_4k_map.spec_index(k) == old(self).allocator_4k_map.spec_index(k),

                // ---- LocalContext: phases preserved ----
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),

                // ---- The lock perm + lock ensures (forwarded from UnLockedMap::wlock_quota) ----
                wlock_ensures(
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
                    final(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
                    LockId{
                        container: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota@.container_depth(),
                        process: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota@.process_depth(),
                        major: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota@.current_lock_major(),
                        minor: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota@.lock_minor(),
                    },
                    final(lctx).thread_id(),
                    ret@,
                ),
                lock_ensures(
                    old(lctx),
                    final(lctx),
                    final(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.view(),
                    LockId{
                        container: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota@.container_depth(),
                        process: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota@.process_depth(),
                        major: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota@.current_lock_major(),
                        minor: old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota@.lock_minor(),
                    },
                    KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k),
                ),
        {
            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
                reveal(process_perms_wf);
            }
            let ret = self.allocator_4k_map.wlock_quota(alloc_ptr_4k, Tracked(&mut *lctx), Ghost(PageSize::SZ4k));
            // Re-establish inv(). Only `allocator_4k_map[alloc_ptr_4k].quota`'s
            // lock state moved; quota.view() preserved; every other allocator
            // entry, every other allocator-side field of this entry, and every
            // other KernelK field is byte-equal pre/post. Same template as
            // the wlock_cpu / wlock_container_unless_killed wrappers.
            proof {
                // ---- subsystems_inv ----
                assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
                assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
                assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
                assert(process_perms_wf(self.process_map)) by { reveal(process_perms_wf); };
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
                    reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
                };
                assert(self.container_pages_wf()) by { reveal(KernelK::container_pages_wf); };
                assert(self.process_pages_wf()) by { reveal(KernelK::process_pages_wf); };
                // The fold conjunct: process_map fully equal pre/post (process not touched);
                // allocator_4k_map per-allocator quota.view() and total_free_pages preserved
                // (lock-state-only change at alloc_ptr_4k); allocator_2m/1g maps fully equal.
                assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    lemma_container_process_allocator_quota_wf_preserved_for_process_lock_op(*old(self), *self);
                };
                assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    reveal(container_allocator_wf);
                };
                assert(self.allocator_free_pages_wf());
                assert(process_pagetable_match(self.process_map, self.pagetable_map)) by { reveal(process_pagetable_match); };
                assert(self.memory_management_inv());
                // ---- process_management_inv: container_map, process_map, etc. all byte-equal ----
                assert(container_tree_wf(self.root_container, self.container_map));
                assert(container_process_wf(self.container_map, self.process_map)) by { reveal(container_process_wf); };
                assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                    reveal(container_process_wf); reveal(per_container_process_tree_wf);
                };
                assert(container_endpoint_wf(self.container_map, self.endpoint_map)) by { reveal(container_endpoint_wf); };
                assert(container_cpu_wf(self.container_map, self.cpu_array)) by { reveal(container_cpu_wf); };
                assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
                    reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
                    reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf);
                };
                assert(container_scheduler_wf(self.container_map, self.scheduler_map)) by { reveal(container_scheduler_wf); };
                assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
                    reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
                };
                assert(container_thread_wf(self.container_map, self.thread_map)) by { reveal(container_thread_wf); };
                assert(process_cpu_wf(self.process_map, self.cpu_array)) by { reveal(process_cpu_wf); };
                assert(process_thread_wf(self.process_map, self.thread_map)) by { reveal(process_thread_wf); };
                assert(self.process_management_inv());
                // ---- inv() direct conjuncts ----
                assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
                    reveal(cpu_dirty_map_contains_container_processes);
                    reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                    reveal(cpu_dirty_map_proc_pcid_match);
                    reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                    reveal(container_cpu_wf);
                };
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
                assert(self.inv());
            }
            ret
        }

        /// Companion of `wlock_quota_4k` for the unlock side. Wraps
        /// `UnLockedMap::wunlock_quota` for `allocator_4k_map` and
        /// re-establishes `inv()` immediately afterwards.
        #[verifier::spinoff_prover]
        pub fn wunlock_quota_4k(
            &mut self,
            alloc_ptr_4k: RwLockPageAllocatorPtr,
            Tracked(lctx): Tracked<&mut LocalContext>,
            lock_perm: Tracked<LockPerm>,
        )
            requires
                old(self).inv(),
                old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.wlocked_by(old(lctx)),
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.inv(),
                unlock_requires::<crate::allocator::allocator_quota::AllocatorQuota>(old(lctx)),
                lock_perm@.state() is WriteLock,
                lock_perm@.thread_id() == old(lctx).thread_id(),
                lock_perm@.lock_id() == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.locking_thread()->Write_lock_id,
                old(lctx).lock_map().dom().contains(KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k)),
                old(lctx).lock_map()[KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k)] == lock_perm@.lock_id(),
            ensures
                // ---- Kernel-wide invariant re-established ----
                final(self).inv(),

                // ---- Field framing: only allocator_4k_map's quota lock state moves ----
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_array         == old(self).cpu_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).container_map     == old(self).container_map,
                final(self).scheduler_map     == old(self).scheduler_map,
                final(self).process_map       == old(self).process_map,
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,

                // ---- allocator_4k_map: dom unchanged; only quota's lock state changed ----
                final(self).allocator_4k_map.dom() == old(self).allocator_4k_map.dom(),
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_poll,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).owning_container == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).owning_container,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).differential == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).differential,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).total_free_pages,
                forall|k: usize| #![auto] old(self).allocator_4k_map.dom().contains(k) && k != alloc_ptr_4k ==>
                    final(self).allocator_4k_map.spec_index(k) == old(self).allocator_4k_map.spec_index(k),

                // ---- wunlock_ensures forwarded ----
                wunlock_ensures(
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
                    final(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
                ),

                // ---- LocalContext: lock dropped, phases preserved ----
                unlock_ensures(
                    old(lctx),
                    final(lctx),
                    final(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.view(),
                    lock_perm@.lock_id(),
                    KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k),
                ),
        {
            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
                reveal(process_perms_wf);
            }
            self.allocator_4k_map.wunlock_quota(alloc_ptr_4k, Tracked(&mut *lctx), lock_perm, Ghost(PageSize::SZ4k));
            // Re-establish inv(). Same template as wlock_quota_4k.
            proof {
                // ---- subsystems_inv ----
                assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
                assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
                assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
                assert(process_perms_wf(self.process_map)) by { reveal(process_perms_wf); };
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
                    reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
                };
                assert(self.container_pages_wf()) by { reveal(KernelK::container_pages_wf); };
                assert(self.process_pages_wf()) by { reveal(KernelK::process_pages_wf); };
                assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    lemma_container_process_allocator_quota_wf_preserved_for_process_lock_op(*old(self), *self);
                };
                assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    reveal(container_allocator_wf);
                };
                assert(self.allocator_free_pages_wf());
                assert(process_pagetable_match(self.process_map, self.pagetable_map)) by { reveal(process_pagetable_match); };
                assert(self.memory_management_inv());
                // ---- process_management_inv ----
                assert(container_tree_wf(self.root_container, self.container_map));
                assert(container_process_wf(self.container_map, self.process_map)) by { reveal(container_process_wf); };
                assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                    reveal(container_process_wf); reveal(per_container_process_tree_wf);
                };
                assert(container_endpoint_wf(self.container_map, self.endpoint_map)) by { reveal(container_endpoint_wf); };
                assert(container_cpu_wf(self.container_map, self.cpu_array)) by { reveal(container_cpu_wf); };
                assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
                    reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
                    reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf);
                };
                assert(container_scheduler_wf(self.container_map, self.scheduler_map)) by { reveal(container_scheduler_wf); };
                assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
                    reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
                };
                assert(container_thread_wf(self.container_map, self.thread_map)) by { reveal(container_thread_wf); };
                assert(process_cpu_wf(self.process_map, self.cpu_array)) by { reveal(process_cpu_wf); };
                assert(process_thread_wf(self.process_map, self.thread_map)) by { reveal(process_thread_wf); };
                assert(self.process_management_inv());
                // ---- inv() direct conjuncts ----
                assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
                    reveal(cpu_dirty_map_contains_container_processes);
                    reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                    reveal(cpu_dirty_map_proc_pcid_match);
                    reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                    reveal(container_cpu_wf);
                };
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
                assert(self.inv());
            }
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
                final(steps).steps.len() == old(steps).steps.len() + 1,
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
            }

            // Snapshot the entry lctx for the "others unlocked" derivation.
            let ghost entry_lctx = lctx@;
            let ghost entry_steps_len = steps.steps.len();

            // Open the user-view atomic step: user-view -> Release.
            proof { steps.begin_user_view_step(&*self, lctx.borrow_mut()); }

            // Release order: Quota -> CPU -> Container, all via wrappers
            // that re-establish `inv()` internally. No manual inv block
            // needed.
            self.wunlock_quota_4k(alloc_ptr_4k, Tracked(&mut lctx), Tracked(quota_lock_perm));
            // The quota unlock is on another field, so cpu_array is still
            // the entry value here. Snapshot it for the user-step closing
            // proof's bridge back to `old(self).cpu_array`.
            let ghost cpu_array_before_unlock = self.cpu_array;
            assert(cpu_array_before_unlock == old(self).cpu_array);

            // CPU and Container unlocks via wrappers — each re-establishes
            // `inv()` internally.
            self.wunlock_cpu(cpu_id, Tracked(&mut lctx), Tracked(cpu_lock_perm));
            self.wunlock_container(container_ptr, Tracked(&mut lctx), Tracked(container_lock_perm));
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
                assert(steps.steps.len() == entry_steps_len + 1);
                assert(steps.steps.last().new_k == *self);
                assert(steps.steps.last().new_u == kernel_k_to_kernel_u(*self));
                assert(steps.steps.last().old_u == steps.steps.last().new_u);
            }
        }

        /// 4-lock analogue of `release_all_and_finish`: also releases the
        /// running process. Used by `syscall_alloc_quota_4k`'s success-path
        /// (TODO) and process-quota-overflow exits, which both hold cpu +
        /// container + quota + process locks at the point of failure.
        ///
        /// Order of unlocks: process (via wrapper, re-establishes inv()) →
        /// quota (direct, breaks inv()) → cpu (direct) → container (via
        /// wrapper, re-establishes inv()). The single manual inv block
        /// covers ONLY the quota+cpu unlocks.
        #[verifier::spinoff_prover]
        fn release_all_with_process_and_finish(
            &mut self,
            tracked mut lctx: Tracked<LocalContext>,
            Tracked(steps): Tracked<&mut KernelSteps>,
            cpu_id: CpuId,
            container_ptr: RwLockContainerPtr,
            process_ptr: RwLockProcessPtr,
            alloc_ptr_4k: RwLockPageAllocatorPtr,
            quota_lock_perm: Tracked<LockPerm>,
            container_lock_perm: Tracked<LockPerm>,
            cpu_lock_perm: Tracked<LockPerm>,
            process_lock_perm: Tracked<LockPerm>,
        )
            requires
                cpu_id_valid(cpu_id),
                old(self).inv(),
                lctx.kernel_view_locking_state() is Acquire,
                lctx.user_view_locking_state() is Acquire,
                // The 4 locks are held.
                lctx.lock_map().dom() =~= set![
                    KernelObjId::Cpu(cpu_id),
                    KernelObjId::Container(container_ptr),
                    KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k),
                    KernelObjId::Process(process_ptr),
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
                // Process lock perm
                process_lock_perm@.state() is WriteLock,
                process_lock_perm@.thread_id() == lctx.thread_id(),
                process_lock_perm@.lock_id() == lctx.lock_map()[KernelObjId::Process(process_ptr)],
                process_lock_perm@.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
                old(self).process_map.dom().contains(process_ptr),
                old(self).process_map.spec_index(process_ptr).wlocked_by(&lctx),
                old(self).process_map.spec_index(process_ptr).inv(),
                old(self).process_map.perms_wf(),
            ensures
                final(steps).steps.len() == old(steps).steps.len() + 1,
                final(steps).steps.last().new_k == *final(self),
                final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(self)),
                final(steps).steps.last().old_u == final(steps).steps.last().new_u,
        {
            let tracked quota_lock_perm = quota_lock_perm.get();
            let tracked container_lock_perm = container_lock_perm.get();
            let tracked cpu_lock_perm = cpu_lock_perm.get();

            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
                reveal(process_perms_wf);
            }

            let ghost entry_steps_len = steps.steps.len();

            // Open the user-view atomic step: user-view -> Release.
            proof { steps.begin_user_view_step(&*self, lctx.borrow_mut()); }

            // Release process FIRST via wrapper; the wrapper re-establishes
            // inv() so the rest of this body looks identical to
            // release_all_and_finish.
            self.wunlock_process(process_ptr, Tracked(&mut lctx), Tracked(process_lock_perm.get()));

            // Release order: Quota -> CPU -> Container, all via wrappers.
            self.wunlock_quota_4k(alloc_ptr_4k, Tracked(&mut lctx), Tracked(quota_lock_perm));
            let ghost cpu_array_before_unlock = self.cpu_array;
            assert(cpu_array_before_unlock == old(self).cpu_array);
            self.wunlock_cpu(cpu_id, Tracked(&mut lctx), Tracked(cpu_lock_perm));

            // Final unlock: container, via the wrapper.
            self.wunlock_container(container_ptr, Tracked(&mut lctx), Tracked(container_lock_perm));

            // User-step closing. Per-process view + view_rodata equality
            // (process_map went through wunlock_process; view stable, the
            // touched key has wunlock_ensures-style preservation).
            proof {
                assert forall|p_ptr: RwLockProcessPtr|
                    #![trigger self.process_map.spec_index(p_ptr).view()]
                    #![trigger self.process_map.spec_index(p_ptr).view_rodata()]
                    self.process_map.dom().contains(p_ptr)
                implies
                    self.process_map.spec_index(p_ptr).view() == old(self).process_map.spec_index(p_ptr).view()
                    && self.process_map.spec_index(p_ptr).view_rodata() == old(self).process_map.spec_index(p_ptr).view_rodata()
                by {};
                assert(self.pagetable_map == old(self).pagetable_map);
                assert(self.cpu_array.unchanged_except(&cpu_array_before_unlock, cpu_id));
                assert(self.cpu_array.unchanged_except(&old(self).cpu_array, cpu_id));
                assert(self.cpu_array.spec_index(cpu_id).view().view()
                    == old(self).cpu_array.spec_index(cpu_id).view().view());
                assert(self.cpu_array.inv()) by { reveal(cpu_array_wf); };
                lemma_release_with_process_preserves_user_view(*old(self), *self, cpu_id);
                assert(kernel_k_to_kernel_u(*old(self))
                    == kernel_k_to_kernel_u(*self));
            }
            // Close the user-view step.
            proof {
                steps.end_user_view_step(&*self, lctx.borrow_mut());
                assert(steps.steps.len() == entry_steps_len + 1);
                assert(steps.steps.last().new_k == *self);
                assert(steps.steps.last().new_u == kernel_k_to_kernel_u(*self));
                assert(steps.steps.last().old_u == steps.steps.last().new_u);
            }
        }

        /// Success-path helper for `syscall_alloc_quota_4k`: when all four
        /// locks (cpu + container + quota_4k + process) are held and every
        /// pre-transfer check has passed, this function performs the
        /// quota transfer (`process.quota_4k += alloc_amount`,
        /// `allocator.quota.value -= alloc_amount`), releases all four
        /// locks, and closes the user-view atomic step.
        ///
        /// Because the allocator's per-cpu/global quota machinery and the
        /// per-process `quota_4k` field are kernel-internal — they're not
        /// part of `kernel_k_to_kernel_u` — the transfer is a user-visible
        /// no-op. The recorded user step therefore has `old_u == new_u ==
        /// kernel_k_to_kernel_u(*final(self))`, exactly the same shape as
        /// the failure-path `release_*_and_finish` helpers.
        ///
        /// Lock release order: process → quota → cpu → container. Each
        /// unlock goes through its wrapper, so `inv()` is re-established
        /// after each release with no manual proof block needed in
        /// between. The single inv-re-establishment proof block here
        /// covers the post-mutation / pre-release point, where the
        /// fold-based `container_process_allocator_quota_wf` conjunct
        /// changes by exactly the per-process / per-allocator delta —
        /// closed by the verified
        /// `lemma_container_process_allocator_quota_wf_preserved_for_quota_transfer`.
        #[verifier::spinoff_prover]
        fn transfer_quota_4k_and_finish(
            &mut self,
            tracked mut lctx: Tracked<LocalContext>,
            Tracked(steps): Tracked<&mut KernelSteps>,
            cpu_id: CpuId,
            container_ptr: RwLockContainerPtr,
            process_ptr: RwLockProcessPtr,
            alloc_ptr_4k: RwLockPageAllocatorPtr,
            alloc_amount: usize,
            quota_lock_perm: Tracked<LockPerm>,
            container_lock_perm: Tracked<LockPerm>,
            cpu_lock_perm: Tracked<LockPerm>,
            process_lock_perm: Tracked<LockPerm>,
        ) -> (ret: RetValueType)
            requires
                cpu_id_valid(cpu_id),
                old(self).inv(),
                lctx.kernel_view_locking_state() is Acquire,
                lctx.user_view_locking_state() is Acquire,
                // The 4 locks are held.
                lctx.lock_map().dom() =~= set![
                    KernelObjId::Cpu(cpu_id),
                    KernelObjId::Container(container_ptr),
                    KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k),
                    KernelObjId::Process(process_ptr),
                ],
                // CPU array lock perm.
                cpu_lock_perm@.state() is WriteLock,
                cpu_lock_perm@.thread_id() == lctx.thread_id(),
                cpu_lock_perm@.lock_id() == lctx.lock_map()[KernelObjId::Cpu(cpu_id)],
                cpu_lock_perm@.lock_id() == old(self).cpu_array.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
                old(self).cpu_array.spec_index(cpu_id).view().wlocked_by(&lctx),
                old(self).cpu_array.spec_index(cpu_id).view().being_killed() == false,
                old(self).cpu_array.inv(),
                // Container lock perm.
                container_lock_perm@.state() is WriteLock,
                container_lock_perm@.thread_id() == lctx.thread_id(),
                container_lock_perm@.lock_id() == lctx.lock_map()[KernelObjId::Container(container_ptr)],
                container_lock_perm@.lock_id() == old(self).container_map.spec_index(container_ptr).locking_thread()->Write_lock_id,
                old(self).container_map.dom().contains(container_ptr),
                old(self).container_map.spec_index(container_ptr).wlocked_by(&lctx),
                old(self).container_map.spec_index(container_ptr).inv(),
                old(self).container_map.perms_wf(),
                // Allocator quota lock perm.
                quota_lock_perm@.state() is WriteLock,
                quota_lock_perm@.thread_id() == lctx.thread_id(),
                quota_lock_perm@.lock_id() == lctx.lock_map()[KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k)],
                quota_lock_perm@.lock_id() == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.locking_thread()->Write_lock_id,
                old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).wf(),
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.wlocked_by(&lctx),
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.inv(),
                old(self).allocator_4k_map.perms_wf(),
                // Process lock perm.
                process_lock_perm@.state() is WriteLock,
                process_lock_perm@.thread_id() == lctx.thread_id(),
                process_lock_perm@.lock_id() == lctx.lock_map()[KernelObjId::Process(process_ptr)],
                process_lock_perm@.lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
                old(self).process_map.dom().contains(process_ptr),
                old(self).process_map.spec_index(process_ptr).wlocked_by(&lctx),
                old(self).process_map.spec_index(process_ptr).inv(),
                old(self).process_map.perms_wf(),
                // Bookkeeping for the transfer:
                //   * process_ptr is owned by container_ptr;
                //   * container_ptr's 4k allocator is alloc_ptr_4k.
                old(self).container_map.spec_index(container_ptr).view().owned_processes@.contains(process_ptr),
                old(self).container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
                // The process's `quota_4k` won't overflow when increased
                // by `alloc_amount`, and the allocator's quota has at
                // least `alloc_amount` to give.
                old(self).process_map.spec_index(process_ptr).view().quota_4k + alloc_amount <= usize::MAX,
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.view().view() >= alloc_amount,
            ensures
                // Always returns `RetValueType::Success` (this is the
                // success path).
                ret is Success,
                // Exactly one user-view step has been recorded; it
                // captures the syscall's atomic linearization.
                final(steps).steps.len() == old(steps).steps.len() + 1,
                final(steps).steps.last().new_k == *final(self),
                final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(self)),
                // The step's `old_u` is the user view AT entry to the
                // helper (i.e. just before the quota transfer). Unlike the
                // failure-path `release_*_and_finish` helpers, the user
                // view is NOT preserved across the quota transfer:
                // `kernel_k_to_kernel_u` reads `process_map[p].view().quota_4k`,
                // which increases by `alloc_amount` at `process_ptr`. So
                // `old_u != new_u` in general — the user step records a
                // genuine transition.
                final(steps).steps.last().old_u == kernel_k_to_kernel_u(*old(self)),
                // Precise user-view delta: nothing changes except
                // `process_map[process_ptr].quota_4k`, which increases by
                // exactly `alloc_amount`.
                kernel_u_only_process_quota_4k_changed(
                    final(steps).steps.last().old_u,
                    final(steps).steps.last().new_u,
                    process_ptr,
                    alloc_amount as int,
                ),
        {
            let tracked quota_lock_perm = quota_lock_perm.get();
            let tracked container_lock_perm = container_lock_perm.get();
            let tracked cpu_lock_perm = cpu_lock_perm.get();
            let tracked process_lock_perm = process_lock_perm.get();

            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
                reveal(process_perms_wf);
            }

            let ghost entry_self = *self;
            let ghost entry_steps_len = steps.steps.len();

            // Open the user-view step BEFORE the mutations so the step's
            // `old_u` captures the pre-transfer user view.
            proof { steps.begin_user_view_step(&*self, lctx.borrow_mut()); }

            // Mutate process.quota_4k += alloc_amount.
            {
                let process_mut = self.process_map.borrow_mut(
                    process_ptr,
                    Tracked(lctx.borrow()),
                    Tracked(&process_lock_perm),
                );
                process_mut.quota_4k = process_mut.quota_4k + alloc_amount;
            }
            // Mutate quota.value -= alloc_amount.
            {
                let quota_mut = self.allocator_4k_map.borrow_mut_quota(
                    alloc_ptr_4k,
                    Tracked(lctx.borrow()),
                    Tracked(&quota_lock_perm),
                );
                quota_mut.value = quota_mut.value - alloc_amount;
            }
            let ghost post_transfer_self = *self;

            // Re-establish inv() after the transfer. Each conjunct other
            // than `container_process_allocator_quota_wf` is verified by
            // reveals — those conjuncts don't read the changed fields.
            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
                reveal(process_perms_wf);
                // ---- subsystems_inv ----
                assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by { reveal(cpu_array_wf); };
                assert(container_perms_wf(self.container_map)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
                assert(allocator_perms_wf(self.allocator_4k_map)) by { reveal(allocator_perms_wf); };
                assert(process_perms_wf(self.process_map)) by { reveal(process_perms_wf); };
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
                    reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
                };
                assert(self.container_pages_wf()) by { reveal(KernelK::container_pages_wf); };
                assert(self.process_pages_wf()) by { reveal(KernelK::process_pages_wf); };
                // The fold-based conjunct: verified preservation lemma.
                // `process_ptr ∈ container_ptr.owned_processes` and
                // `container_ptr.allocator_ptr_4k == alloc_ptr_4k` come
                // from the function's preconditions directly.
                assert(container_process_allocator_quota_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    lemma_container_process_allocator_quota_wf_preserved_for_quota_transfer(
                        entry_self, post_transfer_self,
                        process_ptr, container_ptr, alloc_ptr_4k, alloc_amount,
                    );
                };
                assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    reveal(container_allocator_wf);
                };
                assert(self.allocator_free_pages_wf());
                assert(process_pagetable_match(self.process_map, self.pagetable_map)) by {
                    reveal(process_pagetable_match);
                };
                assert(self.memory_management_inv());
                // ---- process_management_inv ----
                assert(container_tree_wf(self.root_container, self.container_map));
                assert(container_process_wf(self.container_map, self.process_map)) by {
                    reveal(container_process_wf);
                };
                assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                    reveal(container_process_wf); reveal(per_container_process_tree_wf);
                    assert(per_container_process_tree_wf(entry_self.container_map, entry_self.process_map));
                    assert forall|c_ptr: RwLockContainerPtr|
                        self.container_map.dom().contains(c_ptr)
                    implies
                        process_tree_wf(
                            self.container_map.spec_index(c_ptr).view().root_process,
                            self.container_map.spec_index(c_ptr).view().owned_processes@,
                            self.process_map,
                        )
                    by {
                        // Quota transfer changes only process_ptr's view().quota_4k.
                        // Tree fields and view_rodata() are unchanged, so the
                        // tree-fields-only preservation lemma applies for every
                        // container's process tree.
                        lemma_process_tree_wf_preserved_for_tree_fields_eq(
                            self.container_map.spec_index(c_ptr).view().root_process,
                            self.container_map.spec_index(c_ptr).view().owned_processes@,
                            entry_self.process_map,
                            self.process_map,
                        );
                    };
                };
                assert(container_endpoint_wf(self.container_map, self.endpoint_map)) by { reveal(container_endpoint_wf); };
                assert(container_cpu_wf(self.container_map, self.cpu_array)) by { reveal(container_cpu_wf); };
                assert(container_thread_endpoint_wf(self.container_map, self.thread_map, self.endpoint_map)) by {
                    reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf);
                    reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf);
                };
                assert(container_scheduler_wf(self.container_map, self.scheduler_map)) by { reveal(container_scheduler_wf); };
                assert(container_thread_scheduler_wf(self.container_map, self.thread_map, self.scheduler_map)) by {
                    reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
                };
                assert(container_thread_wf(self.container_map, self.thread_map)) by { reveal(container_thread_wf); };
                assert(process_cpu_wf(self.process_map, self.cpu_array)) by { reveal(process_cpu_wf); };
                assert(process_thread_wf(self.process_map, self.thread_map)) by { reveal(process_thread_wf); };
                assert(self.process_management_inv());
                // ---- inv() direct conjuncts ----
                assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by {
                    reveal(cpu_dirty_map_contains_container_processes);
                    reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                    reveal(cpu_dirty_map_proc_pcid_match);
                    reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                    reveal(container_cpu_wf);
                };
                assert(tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)) by { reveal(tlb_wf_spec); };
                assert(self.inv());
            }

            // Now release all 4 locks. Order: process -> quota -> cpu ->
            // container. Each unlock goes through its wrapper, which
            // re-establishes `inv()` internally.
            self.wunlock_process(process_ptr, Tracked(&mut lctx), Tracked(process_lock_perm));
            self.wunlock_quota_4k(alloc_ptr_4k, Tracked(&mut lctx), Tracked(quota_lock_perm));
            // The previous two unlocks don't touch cpu_array, so it still
            // equals post_transfer_self.cpu_array. Snapshot for the cpu
            // unlock's frame bridge below.
            let ghost cpu_array_before_unlock = self.cpu_array;
            assert(cpu_array_before_unlock == post_transfer_self.cpu_array);
            self.wunlock_cpu(cpu_id, Tracked(&mut lctx), Tracked(cpu_lock_perm));

            // Final unlock: container, via the wrapper.
            self.wunlock_container(container_ptr, Tracked(&mut lctx), Tracked(container_lock_perm));

            // User-step closing: user view preserved across the unlocks
            // (the mutations happened BEFORE this section).
            proof {
                assert forall|p_ptr: RwLockProcessPtr|
                    #![trigger self.process_map.spec_index(p_ptr).view()]
                    #![trigger self.process_map.spec_index(p_ptr).view_rodata()]
                    self.process_map.dom().contains(p_ptr)
                implies
                    self.process_map.spec_index(p_ptr).view() == post_transfer_self.process_map.spec_index(p_ptr).view()
                    && self.process_map.spec_index(p_ptr).view_rodata() == post_transfer_self.process_map.spec_index(p_ptr).view_rodata()
                by {};
                assert(self.pagetable_map == post_transfer_self.pagetable_map);
                assert(self.cpu_array.unchanged_except(&cpu_array_before_unlock, cpu_id));
                assert(self.cpu_array.unchanged_except(&post_transfer_self.cpu_array, cpu_id));
                assert(self.cpu_array.spec_index(cpu_id).view().view()
                    == post_transfer_self.cpu_array.spec_index(cpu_id).view().view());
                assert(self.cpu_array.inv()) by { reveal(cpu_array_wf); };
                assert(post_transfer_self.cpu_array.inv()) by { reveal(cpu_array_wf); };
                lemma_release_with_process_preserves_user_view(post_transfer_self, *self, cpu_id);
                assert(kernel_k_to_kernel_u(post_transfer_self) == kernel_k_to_kernel_u(*self));
            }
            // Close the user-view step.
            proof {
                steps.end_user_view_step(&*self, lctx.borrow_mut());
                // Surface the recorded-step facts for the postcondition.
                assert(steps.steps.len() == entry_steps_len + 1);
                assert(steps.steps.last().new_k == *self);
                assert(steps.steps.last().new_u == kernel_k_to_kernel_u(*self));
                assert(steps.steps.last().old_u == kernel_k_to_kernel_u(entry_self));
            }
            RetValueType::Success
        }

        /// Helper: open a user-view step, release the container then cpu lock
        /// (deadlock order is acquire cpu -> container, so release
        /// container -> cpu), re-establish `inv()`, and close the step. This is
        /// the container-acquired exit path of `syscall_alloc_quota_4k` while
        /// the quota-reservation step is unimplemented: both locks are held and
        /// nothing user-visible changed, so the syscall is a user-visible
        /// no-op.
        ///
        /// A 2-lock analogue of `release_all_and_finish` (no allocator quota).
        #[verifier::spinoff_prover]
        fn release_container_cpu_and_finish(
            &mut self,
            tracked mut lctx: Tracked<LocalContext>,
            Tracked(steps): Tracked<&mut KernelSteps>,
            cpu_id: CpuId,
            container_ptr: RwLockContainerPtr,
            container_lock_perm: Tracked<LockPerm>,
            cpu_lock_perm: Tracked<LockPerm>,
        )
            requires
                cpu_id_valid(cpu_id),
                old(self).inv(),
                // Locking phase: still acquiring (no step open yet).
                lctx.kernel_view_locking_state() is Acquire,
                lctx.user_view_locking_state() is Acquire,
                // Exactly the cpu and container locks are held.
                lctx.lock_map().dom() =~= set![
                    KernelObjId::Cpu(cpu_id),
                    KernelObjId::Container(container_ptr),
                ],
                // CPU array lock perm.
                cpu_lock_perm@.state() is WriteLock,
                cpu_lock_perm@.thread_id() == lctx.thread_id(),
                cpu_lock_perm@.lock_id() == lctx.lock_map()[KernelObjId::Cpu(cpu_id)],
                cpu_lock_perm@.lock_id() == old(self).cpu_array.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
                old(self).cpu_array.spec_index(cpu_id).view().wlocked_by(&lctx),
                old(self).cpu_array.spec_index(cpu_id).view().being_killed() == false,
                old(self).cpu_array.inv(),
                // Container lock perm.
                container_lock_perm@.state() is WriteLock,
                container_lock_perm@.thread_id() == lctx.thread_id(),
                container_lock_perm@.lock_id() == lctx.lock_map()[KernelObjId::Container(container_ptr)],
                container_lock_perm@.lock_id() == old(self).container_map.spec_index(container_ptr).locking_thread()->Write_lock_id,
                old(self).container_map.dom().contains(container_ptr),
                old(self).container_map.spec_index(container_ptr).wlocked_by(&lctx),
                old(self).container_map.spec_index(container_ptr).inv(),
                old(self).container_map.perms_wf(),
            ensures
                // A user-view step was opened and closed.
                final(steps).steps.len() == old(steps).steps.len() + 1,
                // The recorded step captures the post-section kernel state,
                // and `new_u` is the user-view projection of that state.
                final(steps).steps.last().new_k == *final(self),
                final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(self)),
                // The release path is a user-visible no-op.
                final(steps).steps.last().old_u == final(steps).steps.last().new_u,
        {
            let tracked container_lock_perm = container_lock_perm.get();
            let tracked cpu_lock_perm = cpu_lock_perm.get();

            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
            }

            let ghost entry_steps_len = steps.steps.len();

            // Open the user-view atomic step: user-view -> Release.
            proof { steps.begin_user_view_step(&*self, lctx.borrow_mut()); }

            // Release order: CPU -> Container, both via wrappers that
            // re-establish `inv()` internally. No manual inv block needed.
            //
            // `begin_user_view_step` reads `&*self`, so cpu_array is still
            // the entry value here. Snapshot for the user-step closing
            // proof's bridge.
            let ghost cpu_array_before_unlock = self.cpu_array;
            assert(cpu_array_before_unlock == old(self).cpu_array);
            self.wunlock_cpu(cpu_id, Tracked(&mut lctx), Tracked(cpu_lock_perm));
            self.wunlock_container(container_ptr, Tracked(&mut lctx), Tracked(container_lock_perm));

            // The release path is a user-visible no-op: the two unlocks touch
            // only lock state, not the cpu/process views read by
            // `kernel_k_to_kernel_u`.
            proof {
                assert(self.process_map == old(self).process_map);
                assert(self.pagetable_map == old(self).pagetable_map);
                assert(self.cpu_array.unchanged_except(&cpu_array_before_unlock, cpu_id));
                assert(self.cpu_array.unchanged_except(&old(self).cpu_array, cpu_id));
                assert(self.cpu_array.spec_index(cpu_id).view().view()
                    == old(self).cpu_array.spec_index(cpu_id).view().view());
                assert(self.cpu_array.inv()) by { reveal(cpu_array_wf); };
                KernelK::lemma_release_preserves_user_view(*old(self), *self, cpu_id);
                assert(kernel_k_to_kernel_u(*old(self))
                    == kernel_k_to_kernel_u(*self));
            }
            // Close the user-view step.
            proof {
                steps.end_user_view_step(&*self, lctx.borrow_mut());
                assert(steps.steps.len() == entry_steps_len + 1);
                assert(steps.steps.last().new_k == *self);
                assert(steps.steps.last().new_u == kernel_k_to_kernel_u(*self));
                assert(steps.steps.last().old_u == steps.steps.last().new_u);
            }
        }

        /// Helper: open a user-view step, release the single CPU lock, and
        /// close the step. This is the container-being-killed exit path of
        /// `syscall_alloc_quota_4k`: at that point only the cpu lock is held
        /// (the container `wlock_unless_killed` failed and left the kernel
        /// untouched), so the syscall is a user-visible no-op.
        ///
        /// A cpu-only analogue of `release_all_and_finish`. Factored out so
        /// the heavy inv()-after-unlock re-establishment proof sits in its own
        /// SMT query (and so the bidirectional `container_cpu_wf` reveal stays
        /// in the same context as the fresh `wunlock` ensures, where it
        /// instantiates — see veriflat-project-notes.md).
        #[verifier::spinoff_prover]
        fn release_cpu_and_finish(
            &mut self,
            tracked mut lctx: Tracked<LocalContext>,
            Tracked(steps): Tracked<&mut KernelSteps>,
            cpu_id: CpuId,
            cpu_lock_perm: Tracked<LockPerm>,
        )
            requires
                cpu_id_valid(cpu_id),
                old(self).inv(),
                // Locking phase: still acquiring (no step open yet).
                lctx.kernel_view_locking_state() is Acquire,
                lctx.user_view_locking_state() is Acquire,
                // Exactly the cpu lock is held.
                lctx.lock_map().dom() =~= set![ KernelObjId::Cpu(cpu_id) ],
                // CPU array lock perm.
                cpu_lock_perm@.state() is WriteLock,
                cpu_lock_perm@.thread_id() == lctx.thread_id(),
                cpu_lock_perm@.lock_id() == lctx.lock_map()[KernelObjId::Cpu(cpu_id)],
                cpu_lock_perm@.lock_id() == old(self).cpu_array.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
                old(self).cpu_array.spec_index(cpu_id).view().wlocked_by(&lctx),
                old(self).cpu_array.spec_index(cpu_id).view().being_killed() == false,
                old(self).cpu_array.inv(),
            ensures
                // A user-view step was opened and closed.
                final(steps).steps.len() == old(steps).steps.len() + 1,
                // The recorded step captures the post-section kernel state,
                // and `new_u` is the user-view projection of that state.
                final(steps).steps.last().new_k == *final(self),
                final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(self)),
                // The release path is a user-visible no-op.
                final(steps).steps.last().old_u == final(steps).steps.last().new_u,
        {
            let tracked cpu_lock_perm = cpu_lock_perm.get();

            proof {
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(allocator_perms_wf);
            }

            let ghost entry_steps_len = steps.steps.len();

            // Open the user-view atomic step: user-view -> Release (legal:
            // self.inv() holds and both phases are Acquire). After this no
            // more locks may be acquired, only released.
            proof { steps.begin_user_view_step(&*self, lctx.borrow_mut()); }

            // `begin_user_view_step` reads `&*self`, so cpu_array is still the
            // entry value here. Snapshot to bridge the unlock's frame back to
            // `old(self)`.
            let ghost cpu_array_before_unlock = self.cpu_array;
            assert(cpu_array_before_unlock == old(self).cpu_array);

            // Release the only held lock: the cpu (via wrapper, which
            // re-establishes `inv()` for us — so no manual block needed).
            self.wunlock_cpu(cpu_id, Tracked(&mut lctx), Tracked(cpu_lock_perm));

            // The release path is a user-visible no-op: the cpu unlock touches
            // only lock state, not the cpu/process views read by
            // `kernel_k_to_kernel_u`. Delegate the projection equality to the
            // isolated lemma so its element-wise quantifier stays out of the
            // inv() proof's SMT query above.
            proof {
                assert(self.process_map == old(self).process_map);
                assert(self.pagetable_map == old(self).pagetable_map);
                assert(self.cpu_array.unchanged_except(&cpu_array_before_unlock, cpu_id));
                assert(self.cpu_array.unchanged_except(&old(self).cpu_array, cpu_id));
                assert(self.cpu_array.spec_index(cpu_id).view().view()
                    == old(self).cpu_array.spec_index(cpu_id).view().view());
                assert(self.cpu_array.inv()) by { reveal(cpu_array_wf); };
                KernelK::lemma_release_preserves_user_view(*old(self), *self, cpu_id);
                assert(kernel_k_to_kernel_u(*old(self))
                    == kernel_k_to_kernel_u(*self));
            }
            // Close the user-view step.
            proof {
                steps.end_user_view_step(&*self, lctx.borrow_mut());
                assert(steps.steps.len() == entry_steps_len + 1);
                assert(steps.steps.last().new_k == *self);
                assert(steps.steps.last().new_u == kernel_k_to_kernel_u(*self));
                assert(steps.steps.last().old_u == steps.steps.last().new_u);
            }
        }
    }
}
