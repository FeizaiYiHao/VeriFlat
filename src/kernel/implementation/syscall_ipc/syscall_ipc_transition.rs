use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_queue::{
    ipc_block_thread_on_endpoint, ipc_dequeue_endpoint_waiter, ipc_enqueue_endpoint_waiter,
    ipc_enqueue_scheduled_thread, ipc_schedule_endpoint_waiter,
};
verus! {
    #[verifier::spinoff_prover]
    pub(super) fn ipc_block_current(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
    waiting_state: ThreadState, payload: IPCPayLoad, pt_regs: &Registers, cpu_lock_perm: Tracked<LockPerm>,
    process_lock_perm: Tracked<LockPerm>, current_thread_lock_perm: Tracked<LockPerm>, endpoint_lock_perm: Tracked<LockPerm>,
    ) -> (ret: RetValueType)
        requires
            old(krnl).inv(),
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            edp_idx_valid(endpoint_index),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(krnl).prc_mp.dom().contains(process_ptr),
            typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
            old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
            old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().len() != 0,
            process_lock_perm.view().state() is WriteLock,
            process_lock_perm.view().thread_id() == old(lctx).thread_id(),
            process_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
            old(krnl).thr_mp.dom().contains(current_thread_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
            old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == false,
            current_thread_lock_perm.view().state() is WriteLock,
            current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
            current_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
            old(krnl).ep_mp.dom().contains(endpoint_ptr),
            typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
            endpoint_lock_perm.view().state() is WriteLock,
            endpoint_lock_perm.view().thread_id() == old(lctx).thread_id(),
            endpoint_lock_perm.view().lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == process_ptr,
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.wf(),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
            old(lctx).container_lock_map().dom().is_empty(),
            old(lctx).process_lock_map().dom() =~= set![process_ptr],
            old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
            old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).pcid_allocator_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pagetable_lock_map().dom().is_empty(),
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            waiting_state.is_endpoint_waiting(),
            payload.wf(),
            waiting_state is RECEIVING_CALL ==> old(krnl).thr_mp.spec_index(current_thread_ptr).view().caller is None,
            !old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(current_thread_ptr),
            old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.len() == 0
                || match old(krnl).ep_mp.spec_index(endpoint_ptr)
                    .view().queue_state {
                    EndpointState::SEND => waiting_state.is_endpoint_send_waiting(),
                    EndpointState::RECEIVE => waiting_state.is_endpoint_receive_waiting(),
                },
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            lock_id_set_aligned(old(lctx)),
            old(lctx).held_lock_majors_lt(PCID_NEEDFLUSH_LOCK_MAJOR),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            ret is CpuIdle,
            final(krnl).inv(),
            final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Idle,
            final(lctx).kernel_view_locking_state() is Release,
            final(steps).steps.len() == old(steps).steps.len() + 1,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
            final(lctx).no_locks_held(),
            final(krnl).all_objects_unlocked(final(lctx)),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            lock_id_set_aligned(final(lctx)),
    {
        let tracked cpu_lock_perm = cpu_lock_perm.get();
        let tracked process_lock_perm = process_lock_perm.get();
        let tracked current_thread_lock_perm = current_thread_lock_perm.get();
        let tracked endpoint_lock_perm = endpoint_lock_perm.get();

        let ghost before_needflush_lock = *krnl;
        let Tracked(needflush_perm) = krnl.wlock_pcid_needflush(cpu_id, KERNEL_DEFAULT_PCID, Tracked(&mut *lctx));
        let ghost old_current_thread_lock_id = krnl.thr_mp.lock_id_by_key(current_thread_ptr);
        proof {
            assert(steps.snap_shot == kernel_k_to_kernel_u(*krnl)) by {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(&before_needflush_lock, krnl);
            };
            assert({
                &&& steps.snap_shot.cpu_array[cpu_id as int].state is Running
                &&& krnl.cpu_arr.inv()
                &&& krnl.cpu_arr.spec_index(cpu_id).view().is_init()
                &&& krnl.cpu_arr.spec_index(cpu_id).view().view().wf()
            }) by {
                krnl.cpu_arr.lemma_view_index(cpu_id);
                reveal(kernel_k_to_kernel_u);
                reveal(cpu_array_wf);
            };
            assert(krnl.ep_mp.spec_index(endpoint_ptr).view().queue.length != usize::MAX) by { endpoint_queue_len_bounded(&*krnl, endpoint_ptr); };
        }

        let (endpoint_node_addr, endpoint_node_perm) = ipc_block_thread_on_endpoint(&mut krnl.thr_mp, Tracked(&*lctx), current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, pt_regs, Tracked(&current_thread_lock_perm));

        ipc_enqueue_endpoint_waiter(&mut krnl.ep_mp, Tracked(&*lctx), endpoint_ptr, current_thread_ptr, waiting_state, endpoint_node_addr, endpoint_node_perm, Tracked(&endpoint_lock_perm));

        let ghost old_cpu_lock_id = krnl.cpu_arr.lock_id_by_index(cpu_id);
        let default_cr3 = krnl.dflt_pt.borrow().cr3;
        assert(page_ptr_valid(default_cr3)) by { reveal(KernelK::default_pagetable_wf); reveal(PageTable::table_pages_wf); };
        krnl.cpu_arr.block_current(cpu_id, default_cr3, &mut krnl.cpu_tlb, &mut krnl.pcid_needflush, &mut krnl.cpu_published, Tracked(&needflush_perm), Tracked(&mut *lctx), Tracked(&cpu_lock_perm));

        proof {
            lctx.update_lock_id(KernelObjId::Thread(current_thread_ptr), old_current_thread_lock_id, krnl.thr_mp.lock_id_by_key(current_thread_ptr));
            lctx.update_lock_id(KernelObjId::Cpu(cpu_id), old_cpu_lock_id, krnl.cpu_arr.lock_id_by_index(cpu_id));
            assert(krnl.subsystems_inv()) by {
                assert({
                    &&& cpu_array_wf(krnl.cpu_arr, krnl.dflt_pt.view())
                    &&& thread_perms_wf(krnl.thr_mp)
                    &&& endpoint_perms_wf(krnl.ep_mp)
                }) by { reveal(cpu_array_wf); reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(endpoint_perms_wf); };
                reveal(KernelK::default_pagetable_wf);
            };
            assert(krnl.memory_management_inv()) by { memory_management_inv_preserved_for_thread_endpoint_memory_fields(*old(krnl), *krnl); };
            assert(krnl.process_management_inv()) by {
                assert({
                    &&& krnl.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors == old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors
                    &&& old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.wf()
                }) by { reveal(endpoint_perms_wf); };
                assert(thread_endpoint_ref_counter_wf(krnl.thr_mp, krnl.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); };
                assert({
                    &&& container_endpoint_wf(krnl.ctn_mp, krnl.ep_mp)
                    &&& thread_caller_callee_wf(krnl.thr_mp)
                }) by { reveal(container_endpoint_wf); reveal(thread_caller_callee_wf); };
                assert({
                    &&& container_thread_scheduler_wf(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp)
                    &&& container_thread_wf(krnl.ctn_mp, krnl.thr_mp)
                    &&& process_thread_wf(krnl.prc_mp, krnl.thr_mp)
                }) by { reveal(container_thread_scheduler_wf); reveal(container_thread_wf); reveal(process_thread_wf); };
                assert({
                    &&& container_cpu_wf(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr)
                    &&& process_cpu_wf(krnl.prc_mp, krnl.cpu_arr)
                    &&& thread_cpu_wf(krnl.thr_mp, krnl.cpu_arr)
                }) by { reveal(container_cpu_wf); reveal(process_cpu_wf); reveal(thread_cpu_wf); };
                assert(thread_endpoint_queue_wf(krnl.thr_mp, krnl.ep_mp)) by {
                    seq_push_lemma::<RwLockThreadPtr>();
                    reveal(thread_perms_wf); reveal(endpoint_perms_wf); reveal(LinkedList::wf_value_list); reveal(thread_endpoint_ref_counter_wf); reveal(thread_endpoint_queue_wf);
                };
                assert(container_thread_endpoint_wf(krnl.ctn_mp, krnl.thr_mp, krnl.ep_mp)) by { reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf); };
            };
            assert(cpu_dirty_map_wf(krnl.ctn_mp, krnl.cpu_set_mp, krnl.prc_mp, krnl.cpu_arr, krnl.cpu_tlb, krnl.pt_mp, krnl.pcid_needflush)) by { reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(container_cpu_wf); };
            assert(tlb_wf_spec(krnl.cpu_tlb, krnl.pt_mp, krnl.cpu_arr, krnl.pcid_needflush)) by { reveal(tlb_wf_spec); };
        }

        krnl.wunlock_pcid_needflush(cpu_id, KERNEL_DEFAULT_PCID, Tracked(&mut *lctx), Tracked(needflush_perm));
        krnl.wunlock_endpoint(endpoint_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm));
        krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
        krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(
                steps.snap_shot.cpu_array[cpu_id as int].state
                    != kernel_k_to_kernel_u(*krnl)
                        .cpu_array[cpu_id as int].state
            ) by {
                krnl.cpu_arr.lemma_view_index(cpu_id);
                reveal(kernel_k_to_kernel_u);
            };
            let ghost step_old_u = steps.snap_shot;
            steps.end_kernel_step(&*krnl, &*lctx);
            assert(steps.steps == old(steps).steps.push(KernelStep {
                old_u: step_old_u,
                new_u: kernel_k_to_kernel_u(*krnl),
            }));
        }
        RetValueType::CpuIdle
    }

    #[verifier::spinoff_prover]
    pub(super) fn ipc_schedule_waiting_peer_and_finish(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
    peer_thread_ptr: RwLockThreadPtr, result: RetValueType, cpu_lock_perm: Tracked<LockPerm>, process_lock_perm: Tracked<LockPerm>,
    current_thread_lock_perm: Tracked<LockPerm>, endpoint_lock_perm: Tracked<LockPerm>, peer_thread_lock_perm: Tracked<LockPerm>,
    ) -> (ret: RetValueType)
        requires
            old(krnl).inv(),
            index_valid(NUM_CPUS, cpu_id),
            old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
            current_thread_ptr != peer_thread_ptr,
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(krnl).prc_mp.dom().contains(process_ptr),
            typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
            old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
            process_lock_perm.view().state() is WriteLock,
            process_lock_perm.view().thread_id() == old(lctx).thread_id(),
            process_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
            old(krnl).thr_mp.dom().contains(current_thread_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
            old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == false,
            current_thread_lock_perm.view().state() is WriteLock,
            current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
            current_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
            old(krnl).ep_mp.dom().contains(endpoint_ptr),
            typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
            endpoint_lock_perm.view().state() is WriteLock,
            endpoint_lock_perm.view().thread_id() == old(lctx).thread_id(),
            endpoint_lock_perm.view().lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
            old(krnl).thr_mp.dom().contains(peer_thread_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).being_killed() == false,
            peer_thread_lock_perm.view().state() is WriteLock,
            peer_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
            peer_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == process_ptr,
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state.is_endpoint_waiting(),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(peer_thread_ptr).view().temp_alloc_clean(),
            old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.len() != 0,
            old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.view().spec_index(0) == peer_thread_ptr,
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
            old(lctx).container_lock_map().dom().is_empty(),
            old(lctx).process_lock_map().dom() =~= set![process_ptr],
            old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
            old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).pcid_allocator_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pagetable_lock_map().dom().is_empty(),
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(lctx).held_lock_majors_lt(SCHEDULER_LOCK_MAJOR),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            lock_id_set_aligned(old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state,
            final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread,
            ret == result,
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
            final(lctx).no_locks_held(),
            final(krnl).all_objects_unlocked(final(lctx)),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            lock_id_set_aligned(final(lctx)),
    {
        let tracked cpu_lock_perm = cpu_lock_perm.get();
        let tracked process_lock_perm = process_lock_perm.get();
        let tracked current_thread_lock_perm = current_thread_lock_perm.get();
        let tracked endpoint_lock_perm = endpoint_lock_perm.get();
        let tracked peer_thread_lock_perm = peer_thread_lock_perm.get();

        proof {
            assert(
                krnl.thr_mp.perms_wf()
                    && krnl.thr_mp.spec_index(peer_thread_ptr).is_init()
            ) by {
                thread_perms_wf_at(krnl.thr_mp, peer_thread_ptr);
            };
        }
        let peer_thread_ref = krnl.thr_mp.borrow_typed(peer_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&peer_thread_lock_perm));
        let peer_container_ptr = peer_thread_ref.owning_container;
        proof {
            assert({
                &&& krnl.ctn_mp.dom().contains(peer_container_ptr)
                &&& krnl.ctn_mp.view().spec_index(peer_container_ptr)
                    .is_init()
                &&& krnl.ctn_mp.view().spec_index(peer_container_ptr)
                    .addr() == peer_container_ptr
            }) by {
                reveal(container_thread_wf);
                container_perms_wf_at(krnl.ctn_mp, peer_container_ptr);
            };
        }
        let peer_scheduler_ptr = krnl.ctn_mp
            .borrow_rodata(peer_container_ptr).borrow().scheduler;
        proof {
            assert({
                &&& krnl.sched_mp.dom().contains(peer_scheduler_ptr)
                &&& krnl.sched_mp.lock_id_by_key(peer_scheduler_ptr)
                    .major == SCHEDULER_LOCK_MAJOR
                &&& !lctx.scheduler_lock_map().dom().contains(peer_scheduler_ptr)
            }) by {
                reveal(container_scheduler_wf); reveal(process_perms_wf); reveal(thread_perms_wf); reveal(endpoint_perms_wf);
                reveal(scheduler_perms_wf);
            };
        }
        let Tracked(peer_scheduler_lock_perm) = krnl.wlock_scheduler(peer_scheduler_ptr, Tracked(&mut *lctx));
        proof {
            assert({
                let peer_container = krnl.thr_mp
                    .spec_index(peer_thread_ptr).view().owning_container;
                &&& krnl.ctn_mp.dom().contains(peer_container)
                &&& krnl.ctn_mp.spec_index(peer_container)
                    .view_rodata().view().scheduler == peer_scheduler_ptr
                &&& krnl.sched_mp.spec_index(peer_scheduler_ptr).view()
                    .owning_container == peer_container
                &&& !krnl.sched_mp.spec_index(peer_scheduler_ptr).view()
                    .queue.view().contains(peer_thread_ptr)
            }) by { reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf); };
            assert(krnl.prc_mp.spec_index(process_ptr).view().owned_threads.view().len() != 0) by { reveal(process_thread_wf); };
        }
        let ghost old_peer_thread_lock_id = krnl.thr_mp.lock_id_by_key(peer_thread_ptr);
        assert(krnl.sched_mp.spec_index(peer_scheduler_ptr).view().queue.length != usize::MAX) by { scheduler_queue_len_bounded(&*krnl, peer_scheduler_ptr); };
        let (_, Tracked(endpoint_node_perm)) = ipc_dequeue_endpoint_waiter(&mut krnl.ep_mp, Tracked(&*lctx), endpoint_ptr, peer_thread_ptr, Tracked(&endpoint_lock_perm));
        proof {
            assert({
                let peer_node_addr = old(krnl).thr_mp.spec_index(peer_thread_ptr).view().endpoint_linkedlist_node.addr();
                &&& old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.map().dom().contains(peer_node_addr)
                &&& old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.map().spec_index(peer_node_addr) == peer_thread_ptr
                &&& endpoint_node_perm.addr() == peer_node_addr
            }) by {
                reveal(thread_endpoint_queue_wf);
                endpoint_perms_wf_at(old(krnl).ep_mp, endpoint_ptr);
                reveal(LinkedList::wf_map);
            };
        }
        let (scheduler_node_addr, scheduler_node_perm) = ipc_schedule_endpoint_waiter(&mut krnl.thr_mp, Tracked(&*lctx), peer_thread_ptr, current_thread_ptr, result, Tracked(endpoint_node_perm), Tracked(&peer_thread_lock_perm));
        ipc_enqueue_scheduled_thread(&mut krnl.sched_mp, Tracked(&*lctx), peer_scheduler_ptr, peer_thread_ptr, scheduler_node_addr, scheduler_node_perm, Tracked(&peer_scheduler_lock_perm));
        proof {
            lctx.enter_kernel_view_release();
            lctx.update_lock_id(KernelObjId::Thread(peer_thread_ptr), old_peer_thread_lock_id, krnl.thr_mp.lock_id_by_key(peer_thread_ptr));
            assert(krnl.subsystems_inv()) by {
                assert({
                    &&& thread_perms_wf(krnl.thr_mp)
                    &&& endpoint_perms_wf(krnl.ep_mp)
                    &&& scheduler_perms_wf(krnl.sched_mp)
                }) by { reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(endpoint_perms_wf); reveal(scheduler_perms_wf); };
                reveal(KernelK::default_pagetable_wf);
            };
            assert(krnl.memory_management_inv()) by { memory_management_inv_preserved_for_thread_endpoint_memory_fields(*old(krnl), *krnl); };
            assert(krnl.process_management_inv()) by {
                assert(thread_endpoint_ref_counter_wf(krnl.thr_mp, krnl.ep_mp)) by { reveal(thread_perms_wf); reveal(thread_endpoint_ref_counter_wf); };
                assert({
                    &&& container_endpoint_wf(krnl.ctn_mp, krnl.ep_mp)
                    &&& thread_caller_callee_wf(krnl.thr_mp)
                }) by { reveal(container_endpoint_wf); reveal(thread_caller_callee_wf); };
                assert({
                    &&& container_scheduler_wf(krnl.ctn_mp, krnl.sched_mp)
                    &&& container_thread_wf(krnl.ctn_mp, krnl.thr_mp)
                    &&& process_thread_wf(krnl.prc_mp, krnl.thr_mp)
                }) by { reveal(container_scheduler_wf); reveal(container_thread_wf); reveal(process_thread_wf); };
                assert({
                    &&& container_cpu_wf(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr)
                    &&& process_cpu_wf(krnl.prc_mp, krnl.cpu_arr)
                    &&& thread_cpu_wf(krnl.thr_mp, krnl.cpu_arr)
                }) by { reveal(container_cpu_wf); reveal(process_cpu_wf); reveal(thread_cpu_wf); };
                assert(thread_endpoint_queue_wf(krnl.thr_mp, krnl.ep_mp)) by {
                    seq_skip_lemma::<RwLockThreadPtr>();
                    lemma_seq_remove_value_membership::<RwLockThreadPtr>();
                    reveal(thread_perms_wf); reveal(endpoint_perms_wf); reveal(LinkedList::wf_value_list); reveal(LinkedList::wf_map); reveal(thread_endpoint_ref_counter_wf); reveal(thread_endpoint_queue_wf);
                };
                assert(container_thread_endpoint_wf(krnl.ctn_mp, krnl.thr_mp, krnl.ep_mp)) by { reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(thread_endpoint_queue_wf); reveal(container_thread_endpoint_wf); };
                assert(container_thread_scheduler_wf(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp)) by {
                    seq_push_lemma::<RwLockThreadPtr>();
                    reveal(container_thread_wf); reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf); reveal(LinkedList::wf_value_list); reveal(LinkedList::wf_map);
                };
            };
            assert({
                &&& cpu_dirty_map_wf(krnl.ctn_mp, krnl.cpu_set_mp, krnl.prc_mp, krnl.cpu_arr, krnl.cpu_tlb, krnl.pt_mp, krnl.pcid_needflush)
                &&& tlb_wf_spec(krnl.cpu_tlb, krnl.pt_mp, krnl.cpu_arr, krnl.pcid_needflush)
                &&& typed_lock_maps_aligned(krnl, &*lctx)
                &&& lock_id_set_aligned(&*lctx)
            }) by { reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(container_cpu_wf); reveal(tlb_wf_spec); };
        }
        krnl.wunlock_thread(peer_thread_ptr, Tracked(&mut *lctx), Tracked(peer_thread_lock_perm));
        krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
        krnl.wunlock_scheduler(peer_scheduler_ptr, Tracked(&mut *lctx), Tracked(peer_scheduler_lock_perm));
        krnl.wunlock_endpoint(endpoint_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm));
        krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(steps.snap_shot == kernel_k_to_kernel_u(*krnl)) by {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl);
            };
            steps.end_kernel_step(&*krnl, &*lctx);
        }
        result
    }
} // verus!
