use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_dispatch::{ipc_lock_entry, IpcEntryLocked};
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_dispatch::running_thread_not_in_endpoint_queue;
use super::syscall_ipc_queue::ipc_enqueue_endpoint_waiter;
use super::syscall_ipc_spec::*;
use super::syscall_ipc_call_spec::*;
use super::syscall_ipc_call_trace::*;
use super::syscall_ipc_call_helpers::ipc_reply_handoff_release_and_end_step;
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_call_eof::ipc_reply_handoff_eof;

verus! {
    /// Under cpu, callee, endpoint, and caller locks: switch the CPU to the recorded caller's process and
    /// resume it, and park the replying callee at the endpoint tail as a receive-call waiter.
    #[verifier::spinoff_prover]
    fn ipc_reply_handoff(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
        process_ptr: RwLockProcessPtr, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
        caller_ptr: RwLockThreadPtr, Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(callee_lock_perm): Tracked<LockPerm>,
        Tracked(endpoint_lock_perm): Tracked<LockPerm>, Tracked(caller_lock_perm): Tracked<LockPerm>, pt_regs: &mut Registers,
    )
        requires
            old(krnl).inv(),
            *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, thr_mp: old(krnl).thr_mp, ep_mp: old(krnl).ep_mp, ..old(steps).snapshot_k() }),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view(),
            forall|p: RwLockContainerPtr| #![trigger old(krnl).ctn_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ctn_mp.spec_index(p)]
                old(steps).snapshot_k().ctn_mp.dom().contains(p) && old(krnl).ctn_mp.dom().contains(p) ==> if old(lctx).container_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).ctn_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() },
            forall|p: RwLockProcessPtr| #![trigger old(krnl).prc_mp.spec_index(p)] #![trigger old(steps).snapshot_k().prc_mp.spec_index(p)]
                old(steps).snapshot_k().prc_mp.dom().contains(p) && old(krnl).prc_mp.dom().contains(p) ==> if old(lctx).process_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).prc_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() },
            forall|p: RwLockThreadPtr| #![trigger old(krnl).thr_mp.spec_index(p)] #![trigger old(steps).snapshot_k().thr_mp.spec_index(p)]
                old(steps).snapshot_k().thr_mp.dom().contains(p) && old(krnl).thr_mp.dom().contains(p) ==> if old(lctx).thread_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().thr_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).thr_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().thr_mp.spec_index(p).locking_thread() },
            forall|p: RwLockEndpointPtr| #![trigger old(krnl).ep_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ep_mp.spec_index(p)]
                old(steps).snapshot_k().ep_mp.dom().contains(p) && old(krnl).ep_mp.dom().contains(p) ==> if old(lctx).endpoint_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).ep_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() },
            forall|p: RwLockPageTableRoot| #![trigger old(krnl).pt_mp.spec_index(p)] #![trigger old(steps).snapshot_k().pt_mp.spec_index(p)]
                old(steps).snapshot_k().pt_mp.dom().contains(p) && old(krnl).pt_mp.dom().contains(p) ==> if old(lctx).pagetable_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).pt_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() },
            forall|p: RwLockPageTableRoot| #![trigger old(krnl).it_mp.spec_index(p)] #![trigger old(steps).snapshot_k().it_mp.spec_index(p)]
                old(steps).snapshot_k().it_mp.dom().contains(p) && old(krnl).it_mp.dom().contains(p) ==> if old(lctx).iommu_table_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().it_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).it_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().it_mp.spec_index(p).locking_thread() },
            forall|i: CpuId| #![trigger old(krnl).cpu_arr.spec_index(i)] #![trigger old(steps).snapshot_k().cpu_arr.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> if old(lctx).cpu_lock_map().dom().contains(i) {
                    old(steps).snapshot_k().cpu_arr.spec_index(i).value.locking_thread() is None
                } else { old(krnl).cpu_arr.spec_index(i).value.locking_thread() == old(steps).snapshot_k().cpu_arr.spec_index(i).value.locking_thread() },
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
            old(steps).snapshot_k().cpu_op.view().view()[cpu_id as int] is Trap,
            edp_idx_valid(endpoint_index),
            old(lctx).kernel_view_locking_state() is Acquire,
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            cpu_lock_perm.state() is WriteLock,
            cpu_lock_perm.thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            old(krnl).prc_mp.dom().contains(process_ptr),
            old(krnl).thr_mp.dom().contains(callee_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), callee_ptr, TypedLockMode::Write),
            old(krnl).thr_mp.spec_index(callee_ptr).being_killed() == false,
            callee_lock_perm.state() is WriteLock,
            callee_lock_perm.thread_id() == old(lctx).thread_id(),
            callee_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(callee_ptr).locking_thread()->Write_lock_id,
            old(krnl).ep_mp.dom().contains(endpoint_ptr),
            typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
            endpoint_lock_perm.state() is WriteLock,
            endpoint_lock_perm.thread_id() == old(lctx).thread_id(),
            endpoint_lock_perm.lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
            old(krnl).thr_mp.dom().contains(caller_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), caller_ptr, TypedLockMode::Write),
            old(krnl).thr_mp.spec_index(caller_ptr).being_killed() == false,
            caller_lock_perm.state() is WriteLock,
            caller_lock_perm.thread_id() == old(lctx).thread_id(),
            caller_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(caller_ptr).locking_thread()->Write_lock_id,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(callee_ptr),
            old(krnl).thr_mp.spec_index(callee_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
            old(krnl).thr_mp.spec_index(callee_ptr).view().owning_proc == process_ptr,
            old(krnl).thr_mp.spec_index(callee_ptr).view().owning_container == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
            old(krnl).thr_mp.spec_index(callee_ptr).view().caller == Some(caller_ptr),
            old(krnl).thr_mp.spec_index(callee_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
            old(krnl).thr_mp.spec_index(callee_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(callee_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(callee_ptr).view().syscall_progress.view() is None,
            !old(krnl).thr_mp.spec_index(callee_ptr).view_ghost().exited,
            old(krnl).thr_mp.spec_index(caller_ptr).view().state is WAITING_REPLY,
            old(krnl).thr_mp.spec_index(caller_ptr).view().callee == Some(callee_ptr),
            old(krnl).thr_mp.spec_index(caller_ptr).view().owning_container == old(krnl).thr_mp.spec_index(callee_ptr).view().owning_container,
            old(krnl).thr_mp.spec_index(caller_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(caller_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(caller_ptr).view().syscall_progress.view() is None,
            !old(krnl).thr_mp.spec_index(caller_ptr).view_ghost().exited,
            old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.len() == 0 || old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue_state is RECEIVE,
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
            old(lctx).container_lock_map().dom().is_empty(),
            old(lctx).process_lock_map().dom().is_empty(),
            old(lctx).thread_lock_map().dom() =~= set![callee_ptr, caller_ptr],
            old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).pcid_allocator_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pagetable_lock_map().dom().is_empty(),
            old(lctx).pagetable_window_lock_map().dom().is_empty(),
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).iommu_root_table_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
            old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(krnl).all_objects_unlocked(final(lctx)),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            final(steps).snapshot_k() == *final(krnl),
            final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(old(steps).snapshot_k()), new_u: kernel_k_to_kernel_u(*final(krnl)) }),
            ipc_reply_handoff_step_pre(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index),
            ipc_reply_handoff_step(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, endpoint_index, *old(pt_regs), context_switch_flushed_pcid(old(steps).snapshot_k(), cpu_id, caller_ptr)),
            final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            *final(pt_regs) == *old(steps).snapshot_k().thr_mp.spec_index(caller_ptr).view().trap_frame.get_some_0(),
    {
        proof {
            thread_perms_wf_at(krnl.thr_mp, caller_ptr); thread_perms_wf_map(krnl.thr_mp); thread_perms_wf_at(krnl.thr_mp, callee_ptr);
            running_thread_not_in_endpoint_queue(&*krnl, endpoint_ptr, callee_ptr);
            container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, callee_ptr);
            assert(krnl.cpu_arr.inv()) by { cpu_array_wf_map(krnl.cpu_arr, krnl.dflt_pt.view()); };
            assert(krnl.ep_mp.spec_index(endpoint_ptr).view().queue.length != usize::MAX) by { endpoint_queue_len_bounded(&*krnl, endpoint_ptr); };
            assert(krnl.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() == krnl.ep_mp.spec_index(endpoint_ptr).view().queue.length) by { endpoint_perms_wf_at(krnl.ep_mp, endpoint_ptr); reveal(LinkedList::wf_value_list); };
        }
        let caller = krnl.thr_mp.borrow_typed(caller_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&caller_lock_perm));
        let next_process = caller.owning_proc;
        assert({
            &&& krnl.prc_mp.dom().contains(next_process)
            &&& !krnl.prc_mp.spec_index(next_process).view().zombie
            &&& krnl.prc_mp.spec_index(next_process).is_init()
            &&& krnl.prc_mp.view().spec_index(next_process).is_init()
            &&& krnl.prc_mp.view().spec_index(next_process).addr() == next_process
        }) by { process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, caller_ptr); process_perms_wf_at(krnl.prc_mp, next_process); };
        let process = krnl.prc_mp.borrow_rodata(next_process).borrow();
        let next_pagetable = process.pagetable;
        let cr3 = process.cr3;
        let pcid = process.pcid;
        let depth = process.depth;
        assert(page_ptr_valid(cr3) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID && krnl.pt_mp.dom().contains(next_pagetable) && krnl.pt_mp.spec_index(next_pagetable).view().cr3 == cr3) by {
            process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, next_process); process_perms_wf_at(krnl.prc_mp, next_process); pagetable_perms_wf_at(krnl.pt_mp, next_pagetable); process_pcid_allocator_wf_process_at(krnl.ctn_mp, krnl.prc_mp, krnl.pcid_allc_mp, next_process);
            krnl.pt_mp.spec_index(next_pagetable).view().table_pages_wf_cr3_at();
        };
        let Tracked(needflush_perm) = krnl.wlock_pcid_needflush(cpu_id, pcid, Tracked(&mut *lctx));
        let ghost before_switch = *krnl;
        proof {
            assert({
                &&& krnl.cpu_arr.spec_index(cpu_id).view().is_init()
                &&& krnl.cpu_arr.spec_index(cpu_id).view().view().wf()
            }) by { cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), cpu_id); };
        }
        krnl.cpu_arr.switch_to_thread(cpu_id, next_process, caller_ptr, next_pagetable, cr3, pcid, depth, &mut krnl.cpu_tlb, &mut krnl.pcid_needflush, &mut krnl.cpu_hw_cr3_pcid, Ghost(before_switch), Tracked(&needflush_perm), Tracked(&mut *lctx), Tracked(&cpu_lock_perm));
        proof { lctx.update_lock_id(KernelObjId::Cpu(cpu_id), before_switch.cpu_arr.lock_id_by_index(cpu_id), krnl.cpu_arr.lock_id_by_index(cpu_id)); }
        let callee = krnl.thr_mp.borrow_mut_typed(callee_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&callee_lock_perm));
        callee.release_caller();
        let (endpoint_node_addr, endpoint_node_perm) = callee.block_on_endpoint(callee_ptr, endpoint_ptr, endpoint_index, ThreadState::RECEIVING_CALL, IPCPayLoad::Empty, &*pt_regs);
        proof { lctx.update_lock_id(KernelObjId::Thread(callee_ptr), before_switch.thr_mp.lock_id_by_key(callee_ptr), krnl.thr_mp.lock_id_by_key(callee_ptr)); }
        ipc_enqueue_endpoint_waiter(&mut krnl.ep_mp, Tracked(&*lctx), endpoint_ptr, callee_ptr, ThreadState::RECEIVING_CALL, endpoint_node_addr, endpoint_node_perm, Tracked(&endpoint_lock_perm));
        let caller = krnl.thr_mp.borrow_mut_typed(caller_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&caller_lock_perm));
        caller.waiting_reply_to_running(cpu_id, pt_regs);
        proof {
            lctx.update_lock_id(KernelObjId::Thread(caller_ptr), before_switch.thr_mp.lock_id_by_key(caller_ptr), krnl.thr_mp.lock_id_by_key(caller_ptr));
            assert(ipc_reply_handoff_eof_transition_framing(before_switch, *krnl, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, *old(pt_regs))) by { reveal(ipc_reply_handoff_eof_transition_framing); };
            ipc_reply_handoff_eof(before_switch, *krnl, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, *old(pt_regs));
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&before_switch, &*krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
        }
        ipc_reply_handoff_release_and_end_step(
            krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, pcid, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, &*pt_regs, Ghost(*old(pt_regs)),
            Ghost(*old(krnl)), Ghost(*old(lctx)), Ghost(before_switch), Tracked(cpu_lock_perm), Tracked(callee_lock_perm), Tracked(endpoint_lock_perm),
            Tracked(caller_lock_perm), Tracked(needflush_perm),
        );
    }

    /// Under cpu, callee, endpoint, and dangling-thread locks with a dangling caller: take the dangling thread over and release the endpoint,
    /// reclaim the dangling thread and the killed callers it takes over, and release the cpu and the running thread, one step per
    /// change.
    fn ipc_reply_dangling_caller(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
        process_ptr: RwLockProcessPtr, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
        caller_ptr: RwLockThreadPtr, Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(callee_lock_perm): Tracked<LockPerm>,
        Tracked(endpoint_lock_perm): Tracked<LockPerm>, Tracked(caller_lock_perm): Tracked<LockPerm>,
    )
        requires
            old(krnl).inv(),
            *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, thr_mp: old(krnl).thr_mp, ep_mp: old(krnl).ep_mp, ..old(steps).snapshot_k() }),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view(),
            forall|p: RwLockContainerPtr| #![trigger old(krnl).ctn_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ctn_mp.spec_index(p)]
                old(steps).snapshot_k().ctn_mp.dom().contains(p) && old(krnl).ctn_mp.dom().contains(p) ==> if old(lctx).container_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).ctn_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() },
            forall|p: RwLockProcessPtr| #![trigger old(krnl).prc_mp.spec_index(p)] #![trigger old(steps).snapshot_k().prc_mp.spec_index(p)]
                old(steps).snapshot_k().prc_mp.dom().contains(p) && old(krnl).prc_mp.dom().contains(p) ==> if old(lctx).process_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).prc_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() },
            forall|p: RwLockThreadPtr| #![trigger old(krnl).thr_mp.spec_index(p)] #![trigger old(steps).snapshot_k().thr_mp.spec_index(p)]
                old(steps).snapshot_k().thr_mp.dom().contains(p) && old(krnl).thr_mp.dom().contains(p) ==> if old(lctx).thread_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().thr_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).thr_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().thr_mp.spec_index(p).locking_thread() },
            forall|p: RwLockEndpointPtr| #![trigger old(krnl).ep_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ep_mp.spec_index(p)]
                old(steps).snapshot_k().ep_mp.dom().contains(p) && old(krnl).ep_mp.dom().contains(p) ==> if old(lctx).endpoint_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).ep_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() },
            forall|p: RwLockPageTableRoot| #![trigger old(krnl).pt_mp.spec_index(p)] #![trigger old(steps).snapshot_k().pt_mp.spec_index(p)]
                old(steps).snapshot_k().pt_mp.dom().contains(p) && old(krnl).pt_mp.dom().contains(p) ==> if old(lctx).pagetable_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).pt_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() },
            forall|p: RwLockPageTableRoot| #![trigger old(krnl).it_mp.spec_index(p)] #![trigger old(steps).snapshot_k().it_mp.spec_index(p)]
                old(steps).snapshot_k().it_mp.dom().contains(p) && old(krnl).it_mp.dom().contains(p) ==> if old(lctx).iommu_table_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().it_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).it_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().it_mp.spec_index(p).locking_thread() },
            forall|i: CpuId| #![trigger old(krnl).cpu_arr.spec_index(i)] #![trigger old(steps).snapshot_k().cpu_arr.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> if old(lctx).cpu_lock_map().dom().contains(i) {
                    old(steps).snapshot_k().cpu_arr.spec_index(i).value.locking_thread() is None
                } else { old(krnl).cpu_arr.spec_index(i).value.locking_thread() == old(steps).snapshot_k().cpu_arr.spec_index(i).value.locking_thread() },
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
            old(steps).snapshot_k().cpu_op.view().view()[cpu_id as int] is Trap,
            edp_idx_valid(endpoint_index),
            old(lctx).kernel_view_locking_state() is Acquire,
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
            old(krnl).irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
            old(krnl).irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
            old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            cpu_lock_perm.state() is WriteLock,
            cpu_lock_perm.thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(krnl).prc_mp.dom().contains(process_ptr),
            old(krnl).thr_mp.dom().contains(callee_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), callee_ptr, TypedLockMode::Write),
            old(krnl).thr_mp.spec_index(callee_ptr).being_killed() == false,
            callee_lock_perm.state() is WriteLock,
            callee_lock_perm.thread_id() == old(lctx).thread_id(),
            callee_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(callee_ptr).locking_thread()->Write_lock_id,
            old(krnl).ep_mp.dom().contains(endpoint_ptr),
            typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
            endpoint_lock_perm.state() is WriteLock,
            endpoint_lock_perm.thread_id() == old(lctx).thread_id(),
            endpoint_lock_perm.lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
            old(krnl).thr_mp.dom().contains(caller_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), caller_ptr, TypedLockMode::Write),
            old(krnl).thr_mp.spec_index(caller_ptr).being_killed() == false,
            caller_lock_perm.state() is WriteLock,
            caller_lock_perm.thread_id() == old(lctx).thread_id(),
            caller_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(caller_ptr).locking_thread()->Write_lock_id,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(callee_ptr),
            old(krnl).thr_mp.spec_index(callee_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
            old(krnl).thr_mp.spec_index(callee_ptr).view().owning_proc == process_ptr,
            old(krnl).thr_mp.spec_index(callee_ptr).view().owning_container == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
            old(krnl).thr_mp.spec_index(callee_ptr).view().caller == Some(caller_ptr),
            old(krnl).thr_mp.spec_index(callee_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
            old(krnl).thr_mp.spec_index(callee_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(callee_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(callee_ptr).view().syscall_progress.view() is None,
            !old(krnl).thr_mp.spec_index(callee_ptr).view_ghost().exited,
            old(krnl).thr_mp.spec_index(caller_ptr).view().state is DANGLING,
            old(krnl).thr_mp.spec_index(caller_ptr).view().callee == Some(callee_ptr),
            old(krnl).thr_mp.spec_index(caller_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(caller_ptr).view().temp_alloc_clean(),
            old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.len() == 0 || old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue_state is RECEIVE,
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
            old(lctx).container_lock_map().dom().is_empty(),
            old(lctx).process_lock_map().dom().is_empty(),
            old(lctx).thread_lock_map().dom() =~= set![callee_ptr, caller_ptr],
            old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).pcid_allocator_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pagetable_lock_map().dom().is_empty(),
            old(lctx).pagetable_window_lock_map().dom().is_empty(),
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).iommu_root_table_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
            old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            !old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(callee_ptr),
            caller_ptr != callee_ptr,
        ensures
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(krnl).all_objects_unlocked(final(lctx)),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            final(steps).snapshot_k() == *final(krnl),
            final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            ({
                let n = old(steps).view().len() as int;
                let trace = final(steps).view();
                let last = trace.len() - 1;
                &&& trace.len() >= n + 3
                &&& trace[n].old_u == kernel_k_to_kernel_u(old(steps).snapshot_k())
                &&& ipc_reply_dangling_caller_step_pre(trace[n].old_u, cpu_id, endpoint_index)
                &&& ipc_reply_dangling_caller_taken_over_step(trace[n].old_u, trace[n].new_u, cpu_id)
                &&& forall|j: int| #![trigger trace[j]] n < j < last ==> ipc_reply_dangling_caller_held_step_pre(trace[j].old_u, cpu_id) && kernel_u_killed_thread_reclaim_step(trace[j].old_u, trace[j].new_u, cpu_id)
                &&& ipc_reply_dangling_caller_held_step_pre(trace[last].old_u, cpu_id)
                &&& ipc_reply_dangling_caller_released_step(trace[last].old_u, trace[last].new_u, cpu_id)
                &&& trace[last].new_u == kernel_k_to_kernel_u(*final(krnl))
            }),
    {
        proof { thread_perms_wf_at(krnl.thr_mp, caller_ptr); container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, callee_ptr); }
        let ghost locked_k = *krnl;
        let ghost locked_lctx = *lctx;
        take_over_dangling_caller(krnl, Tracked(&mut *lctx), callee_ptr, caller_ptr, Tracked(&callee_lock_perm), Tracked(&caller_lock_perm));
        krnl.wunlock_endpoint(endpoint_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm));
        proof {
            let pre_k = steps.snapshot_k();
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged); reveal(kernel_endpoint_nonlock_fields_unchanged);
            reveal(kernel_thread_state_changed);
            locked_k.thr_mp.typed_lock_map_aligned_write_at(locked_lctx.thread_lock_map(), locked_lctx.thread_id(), caller_ptr);
            kernel_cpu_and_two_threads_lock_modes_changed_implies_u_step(&pre_k, &locked_k, &locked_lctx, cpu_id, callee_ptr, caller_ptr, endpoint_ptr, None);
            kernel_dangling_caller_taken_over_implies_u_step(&locked_k, &*krnl, callee_ptr, caller_ptr, Some(endpoint_ptr));
            endpoint_perms_wf_at(locked_k.ep_mp, endpoint_ptr); locked_k.ep_mp.spec_index(endpoint_ptr).view().queue.lemma_len_view();
            ipc_reply_dangling_caller_step_pre_from_k(&pre_k, cpu_id, endpoint_index, process_ptr, callee_ptr, endpoint_ptr, caller_ptr);
            ipc_reply_dangling_caller_taken_over_step_from_u(kernel_k_to_kernel_u(pre_k), kernel_k_to_kernel_u(locked_k), kernel_k_to_kernel_u(*krnl), cpu_id, callee_ptr, caller_ptr, endpoint_ptr);
            krnl.kernel_step_boundary_thread_state_changed(&mut *lctx, &mut *steps, caller_ptr, ThreadState::DANGLING, ThreadState::KILLED);
        }
        let ghost reclaim_k = *krnl;
        let ghost reclaim_lctx = *lctx;
        let ghost reclaim_before = steps.view();
        proof {
            assert(kernel_steps_prefix_unchanged(reclaim_before, reclaim_before)) by { reveal(kernel_steps_prefix_unchanged); };
            process_cpu_wf_at(reclaim_k.prc_mp, reclaim_k.cpu_arr, cpu_id);
            ipc_reply_dangling_caller_held_step_pre_from_k(&reclaim_k, &reclaim_lctx, cpu_id, process_ptr, callee_ptr);
        }
        reclaim_killed_thread_chain(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, caller_ptr, Tracked(caller_lock_perm));
        let ghost release_k = *krnl;
        let ghost release_lctx = *lctx;
        let ghost release_before = steps.view();
        proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
        release_cpu_and_thread_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, callee_ptr, Tracked(callee_lock_perm), Tracked(cpu_lock_perm));
        proof {
            process_cpu_wf_at(release_k.prc_mp, release_k.cpu_arr, cpu_id);
            ipc_reply_dangling_caller_held_step_pre_from_k(&release_k, &release_lctx, cpu_id, process_ptr, callee_ptr);
            kernel_cpu_and_thread_unlocked_implies_u_step(&release_k, &*krnl, cpu_id, callee_ptr);
            assert(release_before[reclaim_before.len() - 1] == reclaim_before[reclaim_before.len() - 1]) by { kernel_steps_prefix_unchanged_index(reclaim_before, release_before, reclaim_before.len() - 1); };
        }
    }

    /// Under cpu, callee, endpoint, and caller locks with the callee's recorded reply-waiting caller: reclaim a dangling caller
    /// and fail with `ErrorIpcCallerKilled`, or hand the CPU to the live caller and wait for the next call.
    fn ipc_reply_locked_caller(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
        process_ptr: RwLockProcessPtr, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
        caller_ptr: RwLockThreadPtr, payload: IPCPayLoad, Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(callee_lock_perm): Tracked<LockPerm>,
        Tracked(endpoint_lock_perm): Tracked<LockPerm>, Tracked(caller_lock_perm): Tracked<LockPerm>, pt_regs: &mut Registers,
    ) -> (ret: RetValueType)
        requires
            old(krnl).inv(),
            old(krnl).thr_mp.perms_wf(),
            *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, thr_mp: old(krnl).thr_mp, ep_mp: old(krnl).ep_mp, ..old(steps).snapshot_k() }),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view(),
            forall|p: RwLockContainerPtr| #![trigger old(krnl).ctn_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ctn_mp.spec_index(p)]
                old(steps).snapshot_k().ctn_mp.dom().contains(p) && old(krnl).ctn_mp.dom().contains(p) ==> if old(lctx).container_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).ctn_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() },
            forall|p: RwLockProcessPtr| #![trigger old(krnl).prc_mp.spec_index(p)] #![trigger old(steps).snapshot_k().prc_mp.spec_index(p)]
                old(steps).snapshot_k().prc_mp.dom().contains(p) && old(krnl).prc_mp.dom().contains(p) ==> if old(lctx).process_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).prc_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() },
            forall|p: RwLockThreadPtr| #![trigger old(krnl).thr_mp.spec_index(p)] #![trigger old(steps).snapshot_k().thr_mp.spec_index(p)]
                old(steps).snapshot_k().thr_mp.dom().contains(p) && old(krnl).thr_mp.dom().contains(p) ==> if old(lctx).thread_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().thr_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).thr_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().thr_mp.spec_index(p).locking_thread() },
            forall|p: RwLockEndpointPtr| #![trigger old(krnl).ep_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ep_mp.spec_index(p)]
                old(steps).snapshot_k().ep_mp.dom().contains(p) && old(krnl).ep_mp.dom().contains(p) ==> if old(lctx).endpoint_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).ep_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() },
            forall|p: RwLockPageTableRoot| #![trigger old(krnl).pt_mp.spec_index(p)] #![trigger old(steps).snapshot_k().pt_mp.spec_index(p)]
                old(steps).snapshot_k().pt_mp.dom().contains(p) && old(krnl).pt_mp.dom().contains(p) ==> if old(lctx).pagetable_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).pt_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() },
            forall|p: RwLockPageTableRoot| #![trigger old(krnl).it_mp.spec_index(p)] #![trigger old(steps).snapshot_k().it_mp.spec_index(p)]
                old(steps).snapshot_k().it_mp.dom().contains(p) && old(krnl).it_mp.dom().contains(p) ==> if old(lctx).iommu_table_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().it_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).it_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().it_mp.spec_index(p).locking_thread() },
            forall|i: CpuId| #![trigger old(krnl).cpu_arr.spec_index(i)] #![trigger old(steps).snapshot_k().cpu_arr.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> if old(lctx).cpu_lock_map().dom().contains(i) {
                    old(steps).snapshot_k().cpu_arr.spec_index(i).value.locking_thread() is None
                } else { old(krnl).cpu_arr.spec_index(i).value.locking_thread() == old(steps).snapshot_k().cpu_arr.spec_index(i).value.locking_thread() },
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
            old(steps).snapshot_k().cpu_op.view().view()[cpu_id as int] is Trap,
            edp_idx_valid(endpoint_index),
            old(lctx).kernel_view_locking_state() is Acquire,
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
            old(krnl).irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
            old(krnl).irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
            old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            cpu_lock_perm.state() is WriteLock,
            cpu_lock_perm.thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            old(krnl).prc_mp.dom().contains(process_ptr),
            old(krnl).thr_mp.dom().contains(callee_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), callee_ptr, TypedLockMode::Write),
            old(krnl).thr_mp.spec_index(callee_ptr).being_killed() == false,
            callee_lock_perm.state() is WriteLock,
            callee_lock_perm.thread_id() == old(lctx).thread_id(),
            callee_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(callee_ptr).locking_thread()->Write_lock_id,
            old(krnl).ep_mp.dom().contains(endpoint_ptr),
            typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
            endpoint_lock_perm.state() is WriteLock,
            endpoint_lock_perm.thread_id() == old(lctx).thread_id(),
            endpoint_lock_perm.lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
            old(krnl).thr_mp.dom().contains(caller_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), caller_ptr, TypedLockMode::Write),
            old(krnl).thr_mp.spec_index(caller_ptr).being_killed() == false,
            caller_lock_perm.state() is WriteLock,
            caller_lock_perm.thread_id() == old(lctx).thread_id(),
            caller_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(caller_ptr).locking_thread()->Write_lock_id,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(callee_ptr),
            old(krnl).thr_mp.spec_index(callee_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
            old(krnl).thr_mp.spec_index(callee_ptr).view().owning_proc == process_ptr,
            old(krnl).thr_mp.spec_index(callee_ptr).view().owning_container == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
            old(krnl).thr_mp.spec_index(callee_ptr).view().caller == Some(caller_ptr),
            old(krnl).thr_mp.spec_index(callee_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
            old(krnl).thr_mp.spec_index(callee_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(callee_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(callee_ptr).view().syscall_progress.view() is None,
            !old(krnl).thr_mp.spec_index(callee_ptr).view_ghost().exited,
            old(krnl).thr_mp.spec_index(caller_ptr).view().state.is_reply_waiting(),
            old(krnl).thr_mp.spec_index(caller_ptr).view().callee == Some(callee_ptr),
            old(krnl).thr_mp.spec_index(caller_ptr).view().owning_container == old(krnl).thr_mp.spec_index(callee_ptr).view().owning_container,
            old(krnl).thr_mp.spec_index(caller_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(caller_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(caller_ptr).view().syscall_progress.view() is None,
            !old(krnl).thr_mp.spec_index(caller_ptr).view_ghost().exited,
            old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.len() == 0 || old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue_state is RECEIVE,
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
            old(lctx).container_lock_map().dom().is_empty(),
            old(lctx).process_lock_map().dom().is_empty(),
            old(lctx).thread_lock_map().dom() =~= set![callee_ptr, caller_ptr],
            old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).pcid_allocator_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pagetable_lock_map().dom().is_empty(),
            old(lctx).pagetable_window_lock_map().dom().is_empty(),
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).iommu_root_table_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
            old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            !old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(callee_ptr),
            caller_ptr != callee_ptr,
        ensures
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            old(steps).view().len() <= final(steps).view().len(),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(krnl).all_objects_unlocked(final(lctx)),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            final(steps).snapshot_k() == *final(krnl),
            final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            ret is ErrorIpcCallerKilled || ret == ipc_call_result(payload),
            ipc_reply_and_receive_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()),
                kernel_k_to_kernel_u(*final(krnl)), cpu_id, endpoint_index, payload, *old(pt_regs), context_switch_flushed_pcid(old(steps).snapshot_k(), cpu_id, caller_ptr), ret),
            ret is ErrorIpcCallerKilled ==> *final(pt_regs) == *old(pt_regs),
            !(ret is ErrorIpcCallerKilled) ==> *final(pt_regs) == *old(steps).snapshot_k().thr_mp.spec_index(caller_ptr).view().trap_frame.get_some_0(),
    {
        proof { thread_perms_wf_at(krnl.thr_mp, caller_ptr); }
        let caller_dangling = match krnl.thr_mp.borrow_typed(caller_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&caller_lock_perm)).state {
            ThreadState::DANGLING => true,
            _ => false,
        };
        if caller_dangling {
            ipc_reply_dangling_caller(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr,
                Tracked(cpu_lock_perm), Tracked(callee_lock_perm), Tracked(endpoint_lock_perm), Tracked(caller_lock_perm));
            proof {
                ipc_reply_and_receive_trace_from_dangling(&*steps, old(steps).view(), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, endpoint_index, payload, *old(pt_regs),
                    context_switch_flushed_pcid(old(steps).snapshot_k(), cpu_id, caller_ptr));
            }
            return RetValueType::ErrorIpcCallerKilled;
        }
        ipc_reply_handoff(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr,
            Tracked(cpu_lock_perm), Tracked(callee_lock_perm), Tracked(endpoint_lock_perm), Tracked(caller_lock_perm), pt_regs);
        let ret = match payload { IPCPayLoad::Usize { value } => RetValueType::SuccessUsize { value }, _ => RetValueType::Success, };
        proof {
            ipc_reply_and_receive_trace_handoff_step(&*steps, old(steps).view(), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, endpoint_index, payload, *old(pt_regs),
                context_switch_flushed_pcid(old(steps).snapshot_k(), cpu_id, caller_ptr), ret);
        }
        ret
    }

    /// Under the reply entry's cpu, current-thread, and endpoint locks: reject a send-direction queue or a killed caller,
    /// otherwise lock the recorded caller and reply to it.
    fn ipc_reply_entry_locked(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, endpoint_index: EndpointIdx,
        payload: IPCPayLoad, process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, queue_len: usize, queue_is_send: bool,
        Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(current_thread_lock_perm): Tracked<LockPerm>, Tracked(endpoint_lock_perm): Tracked<LockPerm>, pt_regs: &mut Registers,
    ) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
            old(steps).snapshot_k().cpu_op.view().view()[cpu_id as int] is Trap,
            edp_idx_valid(endpoint_index),
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, thr_mp: old(krnl).thr_mp, ep_mp: old(krnl).ep_mp, ..old(steps).snapshot_k() }),
            old(krnl).cpu_arr.entries_unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
            old(krnl).thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, current_thread_ptr),
            old(krnl).ep_mp.unchanged_except(&old(steps).snapshot_k().ep_mp, endpoint_ptr),
            old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
            old(steps).snapshot_k().thr_mp.spec_index(current_thread_ptr).locking_thread() is None,
            old(steps).snapshot_k().ep_mp.spec_index(endpoint_ptr).locking_thread() is None,
            !old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().being_killed() && !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            forall|p: RwLockContainerPtr| #![trigger old(krnl).ctn_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ctn_mp.spec_index(p)]
                old(steps).snapshot_k().ctn_mp.dom().contains(p) && old(krnl).ctn_mp.dom().contains(p) ==> if old(lctx).container_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).ctn_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() },
            forall|p: RwLockProcessPtr| #![trigger old(krnl).prc_mp.spec_index(p)] #![trigger old(steps).snapshot_k().prc_mp.spec_index(p)]
                old(steps).snapshot_k().prc_mp.dom().contains(p) && old(krnl).prc_mp.dom().contains(p) ==> if old(lctx).process_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).prc_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() },
            forall|p: RwLockThreadPtr| #![trigger old(krnl).thr_mp.spec_index(p)] #![trigger old(steps).snapshot_k().thr_mp.spec_index(p)]
                old(steps).snapshot_k().thr_mp.dom().contains(p) && old(krnl).thr_mp.dom().contains(p) ==> if old(lctx).thread_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().thr_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).thr_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().thr_mp.spec_index(p).locking_thread() },
            forall|p: RwLockEndpointPtr| #![trigger old(krnl).ep_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ep_mp.spec_index(p)]
                old(steps).snapshot_k().ep_mp.dom().contains(p) && old(krnl).ep_mp.dom().contains(p) ==> if old(lctx).endpoint_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).ep_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() },
            forall|p: RwLockPageTableRoot| #![trigger old(krnl).pt_mp.spec_index(p)] #![trigger old(steps).snapshot_k().pt_mp.spec_index(p)]
                old(steps).snapshot_k().pt_mp.dom().contains(p) && old(krnl).pt_mp.dom().contains(p) ==> if old(lctx).pagetable_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).pt_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() },
            forall|p: RwLockPageTableRoot| #![trigger old(krnl).it_mp.spec_index(p)] #![trigger old(steps).snapshot_k().it_mp.spec_index(p)]
                old(steps).snapshot_k().it_mp.dom().contains(p) && old(krnl).it_mp.dom().contains(p) ==> if old(lctx).iommu_table_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().it_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).it_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().it_mp.spec_index(p).locking_thread() },
            forall|i: CpuId| #![trigger old(krnl).cpu_arr.spec_index(i)] #![trigger old(steps).snapshot_k().cpu_arr.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> if old(lctx).cpu_lock_map().dom().contains(i) {
                    old(steps).snapshot_k().cpu_arr.spec_index(i).value.locking_thread() is None
                } else { old(krnl).cpu_arr.spec_index(i).value.locking_thread() == old(steps).snapshot_k().cpu_arr.spec_index(i).value.locking_thread() },
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            cpu_lock_perm.state() is WriteLock && cpu_lock_perm.thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
            current_thread_lock_perm.state() is WriteLock && current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
            current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
            endpoint_lock_perm.state() is WriteLock && endpoint_lock_perm.thread_id() == old(lctx).thread_id(),
            endpoint_lock_perm.lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
            old(krnl).prc_mp.dom().contains(process_ptr),
            old(krnl).thr_mp.dom().contains(current_thread_ptr) && !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
            old(krnl).ep_mp.dom().contains(endpoint_ptr),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view(),
            ({
                let cpu = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
                let thread = old(krnl).thr_mp.spec_index(current_thread_ptr).view();
                let endpoint = old(krnl).ep_mp.spec_index(endpoint_ptr).view();
                &&& cpu.state is Running && cpu.current_process == Some(process_ptr) && cpu.current_thread == Some(current_thread_ptr)
                &&& thread.state == (ThreadState::RUNNING { cpu_id }) && thread.owning_proc == process_ptr && thread.owning_container == cpu.owning_container
                &&& thread.endpoint_descriptors.wf() && thread.endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr)
                &&& thread.free_quota_pending_clean() && thread.temp_alloc_clean() && thread.syscall_progress.view() is None
                &&& !old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited
                &&& thread.caller is Some
                &&& old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (cpu.current_cr3, cpu.current_pcid)
                &&& !endpoint.queue.view().contains(current_thread_ptr)
                &&& queue_len == endpoint.queue.len() && queue_is_send == (endpoint.queue_state is SEND)
                &&& ipc_reply_entry_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index) == if queue_len != 0 && queue_is_send { Some(RetValueType::ErrorIpcSameDirection) }
                    else if old(steps).snapshot_k().thr_mp.spec_index(thread.caller->Some_0).being_killed() { Some(RetValueType::ErrorIpcPeerKilled) } else { None }
            }),
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
            old(lctx).container_lock_map().dom().is_empty(),
            old(lctx).process_lock_map().dom().is_empty(),
            old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
            old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).pcid_allocator_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pagetable_lock_map().dom().is_empty(),
            old(lctx).pagetable_window_lock_map().dom().is_empty(),
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).iommu_root_table_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
            old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(krnl).all_objects_unlocked(final(lctx)),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            final(steps).snapshot_k() == *final(krnl),
            old(steps).view().len() <= final(steps).view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            ipc_reply_and_receive_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)),
                cpu_id, endpoint_index, payload, *old(pt_regs), context_switch_flushed_pcid(old(steps).snapshot_k(), cpu_id, ipc_recorded_caller(old(steps).snapshot_k(), cpu_id)), ret),
            ipc_rejection(ret) == ipc_reply_entry_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index),
            ret is Success || ret is SuccessUsize || ret is ErrorIpcSameDirection || ret is ErrorIpcPeerKilled || ret is ErrorIpcCallerKilled,
            ret is Success || ret is SuccessUsize ==> *final(pt_regs) == *old(steps).snapshot_k().thr_mp.spec_index(ipc_recorded_caller(old(steps).snapshot_k(), cpu_id)).view().trap_frame.get_some_0(),
            !(ret is Success || ret is SuccessUsize) ==> *final(pt_regs) == *old(pt_regs),
    {
        if queue_len != 0 && queue_is_send {
            krnl.wunlock_endpoint(endpoint_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm));
            proof {
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
            }
            release_cpu_and_thread_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, current_thread_ptr, Tracked(current_thread_lock_perm), Tracked(cpu_lock_perm));
            proof {
                assert(krnl.cpu_op.view().view() =~= old(steps).snapshot_k().cpu_op.view().view());
                assert(kernel_k_to_kernel_u(old(steps).snapshot_k()) == kernel_k_to_kernel_u(*krnl)) by {
                    kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&old(steps).snapshot_k(), &*krnl);
                };
                ipc_reply_and_receive_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index, payload, *old(pt_regs),
                    context_switch_flushed_pcid(old(steps).snapshot_k(), cpu_id, ipc_recorded_caller(old(steps).snapshot_k(), cpu_id)), RetValueType::ErrorIpcSameDirection);
            }
            return RetValueType::ErrorIpcSameDirection;
        }
        proof { thread_perms_wf_map(krnl.thr_mp); thread_perms_wf_at(krnl.thr_mp, current_thread_ptr); }
        let callee_ref = krnl.thr_mp.borrow_typed(current_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&current_thread_lock_perm));
        let caller_ptr = callee_ref.caller.unwrap();
        proof {
            assert({
                &&& krnl.thr_mp.dom().contains(caller_ptr)
                &&& caller_ptr != current_thread_ptr
                &&& krnl.thr_mp.spec_index(caller_ptr).view().state.is_reply_waiting()
                &&& krnl.thr_mp.spec_index(caller_ptr).view().callee == Some(current_thread_ptr)
                &&& krnl.thr_mp.spec_index(caller_ptr).view().owning_container == krnl.thr_mp.spec_index(current_thread_ptr).view().owning_container
            }) by { thread_caller_callee_wf_at(krnl.thr_mp, current_thread_ptr); };
            assert({
                &&& ipc_recorded_caller(old(steps).snapshot_k(), cpu_id) == caller_ptr
                &&& old(steps).snapshot_k().thr_mp.spec_index(caller_ptr).being_killed() == krnl.thr_mp.spec_index(caller_ptr).being_killed()
            }) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged); };
        }
        let caller_res = krnl.wlock_reply_waiting_caller_unless_killed(caller_ptr, Tracked(&mut *lctx));
        if caller_res.is_none() {
            krnl.wunlock_endpoint(endpoint_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm));
            proof {
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
            }
            release_cpu_and_thread_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, current_thread_ptr, Tracked(current_thread_lock_perm), Tracked(cpu_lock_perm));
            proof {
                assert(krnl.cpu_op.view().view() =~= old(steps).snapshot_k().cpu_op.view().view());
                assert(kernel_k_to_kernel_u(old(steps).snapshot_k()) == kernel_k_to_kernel_u(*krnl)) by {
                    kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&old(steps).snapshot_k(), &*krnl);
                };
                ipc_reply_and_receive_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index, payload, *old(pt_regs),
                    context_switch_flushed_pcid(old(steps).snapshot_k(), cpu_id, ipc_recorded_caller(old(steps).snapshot_k(), cpu_id)), RetValueType::ErrorIpcPeerKilled);
            }
            return RetValueType::ErrorIpcPeerKilled;
        }
        let Tracked(caller_lock_perm) = caller_res.unwrap();
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        }
        ipc_reply_locked_caller(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, endpoint_index, caller_ptr, payload,
            Tracked(cpu_lock_perm), Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm), Tracked(caller_lock_perm), pt_regs)
    }

    /// `reply_and_receive(ep)` / `reply_and_receive_usize(ep, v)`: reply `payload` to the recorded caller by
    /// handing it the CPU and wait for the next call on the endpoint; reclaim the dangling thread of a killed caller and fail with
    /// `ErrorIpcCallerKilled`; otherwise stutter with the rejection.
    #[verifier::spinoff_prover]
    pub fn syscall_reply_and_receive(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, endpoint_index: EndpointIdx, payload: IPCPayLoad, pt_regs: &mut Registers) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
            edp_idx_valid(endpoint_index),
            payload is Empty || payload is Usize,
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).no_locks_held(),
            old(steps).snapshot_k() == *old(krnl),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(krnl).all_objects_unlocked(final(lctx)),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            final(steps).snapshot_k() == *final(krnl),
            old(steps).view().len() <= final(steps).view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            !(ret is CpuIdle) ==> final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            ipc_reply_and_receive_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)),
                cpu_id, endpoint_index, payload, *old(pt_regs), context_switch_flushed_pcid(*old(krnl), cpu_id, ipc_recorded_caller(*old(krnl), cpu_id)), ret),
            ipc_rejection(ret) == ipc_reply_entry_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, endpoint_index),
            ret is Success || ret is SuccessUsize || ret is CpuIdle || ret is ErrorThreadKilled || ret is ErrorReplyOutOfPhase || ret is ErrorInvalidEndpoint || ret is ErrorIpcSameDirection || ret is ErrorIpcPeerKilled || ret is ErrorIpcCallerKilled,
            ret is Success || ret is SuccessUsize ==> *final(pt_regs) == *old(krnl).thr_mp.spec_index(ipc_recorded_caller(*old(krnl), cpu_id)).view().trap_frame.get_some_0(),
            !(ret is Success || ret is SuccessUsize) ==> *final(pt_regs) == *old(pt_regs),
    {
        proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
        let entry = match ipc_lock_entry(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, endpoint_index, ThreadState::RECEIVING_CALL, IPCPayLoad::Empty, true, true, &*pt_regs) {
            Ok(entry) => entry,
            Err(ret) => {
                proof {
                    ipc_rejection_trace_stutters(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), cpu_id, endpoint_index,
                        ThreadState::RECEIVING_CALL, IPCPayLoad::Empty, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id), ret);
                    ipc_reply_and_receive_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, endpoint_index, payload, *old(pt_regs),
                        context_switch_flushed_pcid(*old(krnl), cpu_id, ipc_recorded_caller(*old(krnl), cpu_id)), ret);
                }
                return ret;
            },
        };
        let IpcEntryLocked { process_ptr, current_thread_ptr, endpoint_ptr, queue_len, queue_is_send, cpu_lock_perm, current_thread_lock_perm, endpoint_lock_perm } = entry;
        ipc_reply_entry_locked(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, endpoint_index, payload, process_ptr, current_thread_ptr, endpoint_ptr, queue_len, queue_is_send,
            cpu_lock_perm, current_thread_lock_perm, endpoint_lock_perm, pt_regs)
    }
} // verus!
