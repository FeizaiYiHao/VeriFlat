use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_transition::{ipc_block_current, ipc_schedule_waiting_peer_and_finish};
use super::syscall_ipc_endpoint::ipc_rendezvous_endpoint;
use super::syscall_ipc_pages::ipc_rendezvous_pages;
use super::syscall_ipc_cpu::ipc_rendezvous_cpu;
use super::syscall_ipc_pci::ipc_rendezvous_pci;
use super::syscall_ipc_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_call_spec::ipc_reply_entry_result;
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_call_trace::ipc_reply_entry_result_from_k;
use super::syscall_ipc_trace::*;

verus! {
    pub(super) proof fn running_thread_not_in_endpoint_queue(krnl: &KernelK, ep_ptr: RwLockEndpointPtr, thrd_ptr: RwLockThreadPtr)
        requires
            krnl.inv(),
            krnl.ep_mp.dom().contains(ep_ptr),
            krnl.thrd_mp.dom().contains(thrd_ptr),
            krnl.thrd_mp.spec_index(thrd_ptr).view().state is RUNNING,
        ensures
            !krnl.ep_mp.spec_index(ep_ptr).view().queue.view().contains(thrd_ptr),
    { reveal(thread_endpoint_queue_wf); }

    pub(super) proof fn endpoint_queue_member_implies_thread_waiting_on_endpoint(krnl: &KernelK, ep_ptr: RwLockEndpointPtr, thrd_ptr: RwLockThreadPtr)
        requires
            krnl.inv(),
            krnl.ep_mp.dom().contains(ep_ptr),
            krnl.ep_mp.spec_index(ep_ptr).view().queue.view().contains(thrd_ptr),
        ensures
            krnl.thrd_mp.dom().contains(thrd_ptr),
            krnl.thrd_mp.spec_index(thrd_ptr).view().state.is_endpoint_waiting(),
            krnl.thrd_mp.spec_index(thrd_ptr).view().blocking_endpoint_ptr == Some(ep_ptr),
    { reveal(thread_endpoint_queue_wf); thread_perms_wf_at(krnl.thrd_mp, thrd_ptr); }

    pub(super) struct IpcEntryLocked {
        pub process_ptr: RwLockProcessPtr, pub current_thread_ptr: RwLockThreadPtr, pub endpoint_ptr: RwLockEndpointPtr, pub queue_len: usize, pub queue_is_send: bool,
        pub cpu_lock_perm: Tracked<LockPerm>, pub current_thread_lock_perm: Tracked<LockPerm>, pub endpoint_lock_perm: Tracked<LockPerm>,
    }

    /// Locks the endpoint `ep_ptr` of the locked current thread and reads its queue length and direction,
    /// rejecting a non-blocking call with no opposite waiter with every lock released. Results are stated against the
    /// syscall-entry state `steps.snapshot_k()`, from which only the cpu and current-thread locks were taken.
    fn ipc_lock_entry_endpoint(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
        ep_idx: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, blocking: bool, expect_caller: bool, pt_regs: &Registers,
        prc_ptr: RwLockProcessPtr, current_thrd_ptr: RwLockThreadPtr, ep_ptr: RwLockEndpointPtr,
        Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(current_thread_lock_perm): Tracked<LockPerm>,
    ) -> (ret: Result<IpcEntryLocked, RetValueType>)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            edp_idx_valid(ep_idx),
            waiting_state.is_endpoint_waiting(),
            expect_caller ==> waiting_state is RECEIVING_CALL && blocking,
            old(krnl).inv(),
            old(steps).snapshot_k().inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, thrd_mp: old(krnl).thrd_mp, ..old(steps).snapshot_k() }),
            old(krnl).cpu_arr.entries_unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
            old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
            old(steps).snapshot_k().cpu_op.view().view()[cpu_id as int] is Trap,
            old(krnl).thrd_mp.unchanged_except(&old(steps).snapshot_k().thrd_mp, current_thrd_ptr),
            old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
            old(steps).snapshot_k().thrd_mp.spec_index(current_thrd_ptr).locking_thread() is None,
            old(steps).snapshot_k().thrd_mp.dom().contains(current_thrd_ptr) && !old(steps).snapshot_k().thrd_mp.spec_index(current_thrd_ptr).being_killed(),
            !old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().being_killed() && !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view(),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view() == old(steps).snapshot_k().thrd_mp.spec_index(current_thrd_ptr).view(),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            cpu_lock_perm.state() is WriteLock && cpu_lock_perm.thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thrd_ptr, TypedLockMode::Write),
            current_thread_lock_perm.state() is WriteLock && current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
            current_thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(current_thrd_ptr).locking_thread()->Write_lock_id,
            old(krnl).prc_mp.dom().contains(prc_ptr),
            old(krnl).thrd_mp.dom().contains(current_thrd_ptr) && !old(krnl).thrd_mp.spec_index(current_thrd_ptr).being_killed(),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thrd_ptr),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().owning_proc == prc_ptr,
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().owning_container == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().endpoint_descriptors.wf(),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().endpoint_descriptors.spec_index(ep_idx) == Some(ep_ptr),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().free_quota_pending_clean(),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().temp_alloc_clean(),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().syscall_progress.view() is None,
            !old(krnl).thrd_mp.spec_index(current_thrd_ptr).view_ghost().exited,
            waiting_state is RECEIVING_CALL ==> (old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().caller is Some) == expect_caller,
            old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
            old(lctx).container_lock_map().dom().is_empty(),
            old(lctx).process_lock_map().dom().is_empty(),
            old(lctx).thread_lock_map().dom() =~= set![current_thrd_ptr],
            old(lctx).endpoint_lock_map().dom().is_empty(),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).pcid_allocator_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pagetable_lock_map().dom().is_empty(),
            old(lctx).pagetable_window_lock_map().dom().is_empty(),
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).iommu_root_table_lock_map().dom().is_empty(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(krnl).inv(),
            old(steps).view().len() <= final(steps).view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            ret is Err ==> ({
                let r = ret->Err_0;
                let entry_thrd_ptr = old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view().current_thread.unwrap();
                let endpoint_option = old(steps).snapshot_k().thrd_mp.spec_index(entry_thrd_ptr).view().endpoint_descriptors.view().spec_index(ep_idx as int);
                let entry_ep_ptr = endpoint_option.unwrap();
                &&& r is ErrorIpcNoPeer || r is ErrorIpcSameDirection
                &&& !blocking
                &&& ipc_rejection(r) == ipc_entry_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, ep_idx, waiting_state, blocking)
                &&& final(lctx).kernel_view_locking_state() is Release
                &&& final(lctx).no_locks_held()
                &&& final(krnl).all_objects_unlocked(final(lctx))
                &&& typed_lock_maps_aligned(final(krnl), final(lctx))
                &&& final(steps).snapshot_k() == *final(krnl)
                &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running
                &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view().current_thread
                &&& payload is Pages ==> ipc_pages_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                    kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx, waiting_state, payload->Pages_va_range,
                    *pt_regs, ipc_block_flushes_default_pcid(old(steps).snapshot_k(), cpu_id), r)
                &&& payload is Endpoint ==> ipc_endpoint_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                    kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx, waiting_state, payload->Endpoint_endpoint_index,
                    *pt_regs, ipc_block_flushes_default_pcid(old(steps).snapshot_k(), cpu_id), r)
                &&& (payload is Empty || payload is Usize || payload is Cpu || payload is ReceiveCpu || payload is Pci) ==> ipc_ordinary_syscall_trace(
                    final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                    kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx, waiting_state, payload, *pt_regs,
                    ipc_block_flushes_default_pcid(old(steps).snapshot_k(), cpu_id), r)
                &&& endpoint_option is Some
                &&& old(steps).snapshot_k().ep_mp.dom().contains(entry_ep_ptr)
                &&& final(krnl).ep_mp.dom().contains(entry_ep_ptr)
                &&& final(krnl).ep_mp.spec_index(entry_ep_ptr).view().queue == old(steps).snapshot_k().ep_mp.spec_index(entry_ep_ptr).view().queue
                &&& if r is ErrorIpcNoPeer {
                    old(steps).snapshot_k().ep_mp.spec_index(entry_ep_ptr).view().queue.len() == 0
                } else {
                    &&& old(steps).snapshot_k().ep_mp.spec_index(entry_ep_ptr).view().queue.len() > 0
                    &&& old(steps).snapshot_k().ep_mp.spec_index(entry_ep_ptr).view().queue_state == if waiting_state.is_endpoint_send_waiting() { EndpointState::SEND } else { EndpointState::RECEIVE }
                }
            }),
            ret is Ok ==> ({
                let e = ret->Ok_0;
                let cpu = final(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
                let thread = final(krnl).thrd_mp.spec_index(e.current_thread_ptr).view();
                let endpoint = final(krnl).ep_mp.spec_index(e.endpoint_ptr).view();
                &&& *final(steps) == *old(steps)
                &&& final(lctx).kernel_view_locking_state() is Acquire
                &&& *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, cpu_op: final(krnl).cpu_op, thrd_mp: final(krnl).thrd_mp, ep_mp: final(krnl).ep_mp, ..old(steps).snapshot_k() })
                &&& final(krnl).cpu_arr.entries_unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id)
                &&& final(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep)
                &&& final(krnl).thrd_mp.unchanged_except(&old(steps).snapshot_k().thrd_mp, e.current_thread_ptr)
                &&& final(krnl).ep_mp.unchanged_except(&old(steps).snapshot_k().ep_mp, e.endpoint_ptr)
                &&& old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None
                &&& old(steps).snapshot_k().thrd_mp.spec_index(e.current_thread_ptr).locking_thread() is None
                &&& old(steps).snapshot_k().ep_mp.spec_index(e.endpoint_ptr).locking_thread() is None
                &&& !old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().being_killed() && !final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed()
                &&& kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), final(krnl))
                &&& kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, final(krnl).ep_mp)
                &&& kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), final(krnl))
                &&& forall|p: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ctn_mp.spec_index(p)]
                    old(steps).snapshot_k().ctn_mp.dom().contains(p) && final(krnl).ctn_mp.dom().contains(p) ==> if final(lctx).container_lock_map().dom().contains(p) {
                        old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() is None
                    } else { final(krnl).ctn_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() && final(krnl).ctn_mp.spec_index(p).lock_process_owner_u() == old(steps).snapshot_k().ctn_mp.spec_index(p).lock_process_owner_u() }
                &&& forall|p: RwLockProcessPtr| #![trigger final(krnl).prc_mp.spec_index(p)] #![trigger old(steps).snapshot_k().prc_mp.spec_index(p)]
                    old(steps).snapshot_k().prc_mp.dom().contains(p) && final(krnl).prc_mp.dom().contains(p) ==> if final(lctx).process_lock_map().dom().contains(p) {
                        old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() is None
                    } else { final(krnl).prc_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() }
                &&& forall|p: RwLockThreadPtr| #![trigger final(krnl).thrd_mp.spec_index(p)] #![trigger old(steps).snapshot_k().thrd_mp.spec_index(p)]
                    old(steps).snapshot_k().thrd_mp.dom().contains(p) && final(krnl).thrd_mp.dom().contains(p) ==> if final(lctx).thread_lock_map().dom().contains(p) {
                        old(steps).snapshot_k().thrd_mp.spec_index(p).locking_thread() is None
                    } else { final(krnl).thrd_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().thrd_mp.spec_index(p).locking_thread() }
                &&& forall|p: RwLockEndpointPtr| #![trigger final(krnl).ep_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ep_mp.spec_index(p)]
                    old(steps).snapshot_k().ep_mp.dom().contains(p) && final(krnl).ep_mp.dom().contains(p) ==> if final(lctx).endpoint_lock_map().dom().contains(p) {
                        old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() is None
                    } else { final(krnl).ep_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() }
                &&& forall|p: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(p)] #![trigger old(steps).snapshot_k().pt_mp.spec_index(p)]
                    old(steps).snapshot_k().pt_mp.dom().contains(p) && final(krnl).pt_mp.dom().contains(p) ==> if final(lctx).pagetable_lock_map().dom().contains(p) {
                        old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() is None
                    } else { final(krnl).pt_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() }
                &&& final(krnl).pt_lower == old(steps).snapshot_k().pt_lower
                &&& forall|p: RwLockPageTableRoot| #![trigger final(krnl).it_mp.spec_index(p)] #![trigger old(steps).snapshot_k().it_mp.spec_index(p)]
                    old(steps).snapshot_k().it_mp.dom().contains(p) && final(krnl).it_mp.dom().contains(p) ==> if final(lctx).iommu_table_lock_map().dom().contains(p) {
                        old(steps).snapshot_k().it_mp.spec_index(p).locking_thread() is None
                    } else { final(krnl).it_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().it_mp.spec_index(p).locking_thread() }
                &&& forall|i: CpuId| #![trigger final(krnl).cpu_arr.spec_index(i)] #![trigger old(steps).snapshot_k().cpu_arr.spec_index(i)]
                    index_valid(NUM_CPUS, i) ==> if final(lctx).cpu_lock_map().dom().contains(i) {
                        old(steps).snapshot_k().cpu_arr.spec_index(i).value.locking_thread() is None
                    } else { final(krnl).cpu_arr.spec_index(i).value.locking_thread() == old(steps).snapshot_k().cpu_arr.spec_index(i).value.locking_thread() }
                &&& typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write)
                &&& e.cpu_lock_perm.view().state() is WriteLock && e.cpu_lock_perm.view().thread_id() == final(lctx).thread_id()
                &&& e.cpu_lock_perm.view().lock_id() == final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id
                &&& typed_lock_map_contains_mode(final(lctx).thread_lock_map(), e.current_thread_ptr, TypedLockMode::Write)
                &&& e.current_thread_lock_perm.view().state() is WriteLock && e.current_thread_lock_perm.view().thread_id() == final(lctx).thread_id()
                &&& e.current_thread_lock_perm.view().lock_id() == final(krnl).thrd_mp.spec_index(e.current_thread_ptr).locking_thread()->Write_lock_id
                &&& typed_lock_map_contains_mode(final(lctx).endpoint_lock_map(), e.endpoint_ptr, TypedLockMode::Write)
                &&& e.endpoint_lock_perm.view().state() is WriteLock && e.endpoint_lock_perm.view().thread_id() == final(lctx).thread_id()
                &&& e.endpoint_lock_perm.view().lock_id() == final(krnl).ep_mp.spec_index(e.endpoint_ptr).locking_thread()->Write_lock_id
                &&& final(krnl).prc_mp.dom().contains(e.process_ptr)
                &&& final(krnl).thrd_mp.dom().contains(e.current_thread_ptr) && !final(krnl).thrd_mp.spec_index(e.current_thread_ptr).being_killed()
                &&& final(krnl).ep_mp.dom().contains(e.endpoint_ptr)
                &&& cpu.state is Running && cpu.current_process == Some(e.process_ptr) && cpu.current_thread == Some(e.current_thread_ptr)
                &&& thread.state == (ThreadState::RUNNING { cpu_id }) && thread.owning_proc == e.process_ptr && thread.owning_container == cpu.owning_container
                &&& thread.endpoint_descriptors.wf() && thread.endpoint_descriptors.spec_index(ep_idx) == Some(e.endpoint_ptr)
                &&& thread.free_quota_pending_clean() && thread.temp_alloc_clean() && thread.syscall_progress.view() is None
                &&& !final(krnl).thrd_mp.spec_index(e.current_thread_ptr).view_ghost().exited
                &&& final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (cpu.current_cr3, cpu.current_pcid)
                &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view()
                &&& !endpoint.queue.view().contains(e.current_thread_ptr)
                &&& e.queue_len == endpoint.queue.len() && e.queue_is_send == (endpoint.queue_state is SEND)
                &&& (e.queue_len == 0 || e.queue_is_send == waiting_state.is_endpoint_send_waiting()) ==> blocking
                &&& waiting_state is RECEIVING_CALL ==> (thread.caller is Some) == expect_caller
                &&& final(lctx).page_lock_map().dom().is_empty()
                &&& final(lctx).cpu_lock_map().dom() =~= set![cpu_id]
                &&& final(lctx).container_lock_map().dom().is_empty()
                &&& final(lctx).process_lock_map().dom().is_empty()
                &&& final(lctx).thread_lock_map().dom() =~= set![e.current_thread_ptr]
                &&& final(lctx).endpoint_lock_map().dom() =~= set![e.endpoint_ptr]
                &&& final(lctx).scheduler_lock_map().dom().is_empty()
                &&& final(lctx).pcid_allocator_lock_map().dom().is_empty()
                &&& final(lctx).cpu_set_lock_map().dom().is_empty()
                &&& final(lctx).pagetable_lock_map().dom().is_empty()
                &&& final(lctx).pagetable_window_lock_map().dom().is_empty()
                &&& final(lctx).iommu_table_lock_map().dom().is_empty()
                &&& final(lctx).iommu_root_table_lock_map().dom().is_empty()
                &&& final(lctx).allocator_quota_4k_lock_map().dom().is_empty()
                &&& final(lctx).allocator_cache_4k_lock_map().dom().is_empty()
                &&& final(lctx).allocator_global_pool_4k_lock_map().dom().is_empty()
                &&& final(lctx).allocator_quota_2m_lock_map().dom().is_empty()
                &&& final(lctx).allocator_cache_2m_lock_map().dom().is_empty()
                &&& final(lctx).allocator_global_pool_2m_lock_map().dom().is_empty()
                &&& final(lctx).allocator_quota_1g_lock_map().dom().is_empty()
                &&& final(lctx).allocator_cache_1g_lock_map().dom().is_empty()
                &&& final(lctx).allocator_global_pool_1g_lock_map().dom().is_empty()
                &&& final(lctx).cpu_offline_flag_lock_map().dom().is_empty()
                &&& final(lctx).pcid_needflush_lock_map().dom().is_empty()
                &&& typed_lock_maps_aligned(final(krnl), final(lctx))
                &&& !expect_caller ==> ipc_entry_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, ep_idx, waiting_state, blocking) == if e.queue_len == 0 || e.queue_is_send == waiting_state.is_endpoint_send_waiting() { Some(RetValueType::CpuIdle) }
                    else if old(steps).snapshot_k().thrd_mp.spec_index(old(steps).snapshot_k().ep_mp.spec_index(e.endpoint_ptr).view().queue.view()[0]).being_killed() { Some(RetValueType::ErrorIpcPeerKilled) }
                    else { None }
                &&& expect_caller ==> ipc_reply_entry_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, ep_idx) == if e.queue_len != 0 && e.queue_is_send { Some(RetValueType::ErrorIpcSameDirection) }
                    else if old(steps).snapshot_k().thrd_mp.spec_index(thread.caller->Some_0).being_killed() { Some(RetValueType::ErrorIpcPeerKilled) }
                    else { None }
            }),
    {
        proof { assert(krnl.ep_mp.dom().contains(ep_ptr)) by { thread_endpoint_ref_counter_wf_thread_at(krnl.thrd_mp, krnl.ep_mp, current_thrd_ptr, ep_idx); }; }
        let Tracked(endpoint_lock_perm) = krnl.wlock_endpoint(ep_ptr, Tracked(&mut *lctx));
        proof {
            assert({
                &&& krnl.ep_mp.perms_wf()
                &&& krnl.thrd_mp.spec_index(current_thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id })
            }) by { endpoint_perms_wf_map(krnl.ep_mp); endpoint_perms_wf_at(krnl.ep_mp, ep_ptr); };
        }
        let endpoint_ref = krnl.ep_mp.borrow_typed(ep_ptr, Ghost(lctx.endpoint_lock_map()), Tracked(&*lctx), Tracked(&endpoint_lock_perm));
        let queue_len = endpoint_ref.queue.len();
        let queue_is_send = endpoint_ref.queue_state.is_send();
        let waiting_is_send = match waiting_state { ThreadState::SENDING | ThreadState::CALLING => true, _ => false };
        proof {
            running_thread_not_in_endpoint_queue(krnl, ep_ptr, current_thrd_ptr);
            assert({
                &&& steps.snapshot_k().ep_mp.spec_index(ep_ptr).view().queue.view().len() == queue_len
                &&& (steps.snapshot_k().ep_mp.spec_index(ep_ptr).view().queue_state is SEND) == queue_is_send
            }) by { reveal(kernel_endpoint_nonlock_fields_unchanged); endpoint_perms_wf_at(krnl.ep_mp, ep_ptr); krnl.ep_mp.spec_index(ep_ptr).view().queue.wf_implies_view_len_eq_len(); };
        }

        if (queue_len == 0 || queue_is_send == waiting_is_send) && !blocking {
            let result = if queue_len == 0 { RetValueType::ErrorIpcNoPeer } else { RetValueType::ErrorIpcSameDirection };
            krnl.wunlock_endpoint(ep_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm));

            proof {
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
            }
            release_cpu_and_thread_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, current_thrd_ptr, Tracked(current_thread_lock_perm), Tracked(cpu_lock_perm));
            proof {
                assert(krnl.cpu_op.view().view() =~= old(steps).snapshot_k().cpu_op.view().view());
                assert(kernel_k_to_kernel_u(old(steps).snapshot_k()) == kernel_k_to_kernel_u(*krnl)) by {
                    kernel_restored_locks_implies_u_eq(&old(steps).snapshot_k(), &*krnl, cpu_id, None, None, Some(current_thrd_ptr), Some(ep_ptr), None);
                };
            }
            proof {
                ipc_syscall_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, ep_idx,
                    waiting_state, payload, *pt_regs, ipc_block_flushes_default_pcid(old(steps).snapshot_k(), cpu_id), result);
            }
            proof { ipc_entry_result_from_k(&old(steps).snapshot_k(), cpu_id, ep_idx, waiting_state, blocking, Some(result)); }
            return Err(result);
        }
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), &*krnl)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            if expect_caller {
                ipc_reply_entry_result_from_k(&old(steps).snapshot_k(), cpu_id, ep_idx, if queue_len != 0 && queue_is_send { Some(RetValueType::ErrorIpcSameDirection) }
                    else if old(steps).snapshot_k().thrd_mp.spec_index(krnl.thrd_mp.spec_index(current_thrd_ptr).view().caller->Some_0).being_killed() { Some(RetValueType::ErrorIpcPeerKilled) } else { None });
            } else {
                ipc_entry_result_from_k(&old(steps).snapshot_k(), cpu_id, ep_idx, waiting_state, blocking, if queue_len == 0 || queue_is_send == waiting_is_send { Some(RetValueType::CpuIdle) }
                    else if old(steps).snapshot_k().thrd_mp.spec_index(old(steps).snapshot_k().ep_mp.spec_index(ep_ptr).view().queue.view()[0]).being_killed() { Some(RetValueType::ErrorIpcPeerKilled) } else { None });
            }
        }
        Ok(IpcEntryLocked {
            process_ptr: prc_ptr, current_thread_ptr: current_thrd_ptr, endpoint_ptr: ep_ptr, queue_len, queue_is_send,
            cpu_lock_perm: Tracked(cpu_lock_perm), current_thread_lock_perm: Tracked(current_thread_lock_perm),
            endpoint_lock_perm: Tracked(endpoint_lock_perm),
        })
    }

    /// Locks the cpu, its thread, and the endpoint at `ep_idx`, rejecting a killed thread, a
    /// receive-call thread whose recorded caller is present unless `expect_caller` (or absent when
    /// `expect_caller`), a missing descriptor, and a non-blocking call with no opposite waiter; otherwise the
    /// three locks are returned held with the queue length and direction, and the entry result is pinned to the
    /// state at entry.
    #[verifier::spinoff_prover]
    pub(super) fn ipc_lock_entry(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
        ep_idx: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, blocking: bool, expect_caller: bool, pt_regs: &Registers,
    ) -> (ret: Result<IpcEntryLocked, RetValueType>)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            edp_idx_valid(ep_idx),
            waiting_state.is_endpoint_waiting(),
            expect_caller ==> waiting_state is RECEIVING_CALL && blocking,
            blocking || payload is Empty,
            match payload {
                IPCPayLoad::Empty => true,
                IPCPayLoad::Usize { .. } => waiting_state is CALLING,
                IPCPayLoad::Cpu { cpu_id } => index_valid(NUM_CPUS, cpu_id) && waiting_state is SENDING,
                IPCPayLoad::ReceiveCpu => waiting_state is RECEIVING,
                IPCPayLoad::Pages { va_range } => {
                    &&& waiting_state is SENDING || waiting_state is RECEIVING
                    &&& va_range.wf()
                    &&& va_range.len > 0
                },
                IPCPayLoad::Endpoint { endpoint_index: ep_idx } => (waiting_state is SENDING || waiting_state is RECEIVING) && edp_idx_valid(ep_idx),
                IPCPayLoad::Pci { bus, dev, fun } => (waiting_state is SENDING || waiting_state is RECEIVING) && pci_bdf_valid(bus as usize, dev as usize, fun as usize),
                _ => false,
            },
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
            old(lctx).no_locks_held(),
            old(steps).snapshot_k() == *old(krnl),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(krnl).inv(),
            old(steps).view().len() <= final(steps).view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            ret is Err ==> ({
                let r = ret->Err_0;
                let current_thrd_ptr = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread.unwrap();
                let endpoint_option = old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().endpoint_descriptors.view().spec_index(ep_idx as int);
                let ep_ptr = endpoint_option.unwrap();
                &&& r is ErrorThreadKilled || r is ErrorInvalidEndpoint || r is ErrorIpcNoPeer || r is ErrorIpcSameDirection || r is ErrorReplyOutOfPhase || r is CpuIdle
                &&& r is CpuIdle ==> !(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running) || old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed()
                &&& r is CpuIdle ==> ipc_entry_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, waiting_state, false) == Some(RetValueType::CpuIdle)
                &&& r is ErrorIpcNoPeer || r is ErrorIpcSameDirection ==> !blocking
                &&& r is ErrorReplyOutOfPhase ==> waiting_state is RECEIVING_CALL
                &&& !expect_caller ==> ipc_rejection(r) == ipc_entry_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, waiting_state, blocking)
                &&& expect_caller ==> ipc_rejection(r) == ipc_reply_entry_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx)
                &&& final(lctx).kernel_view_locking_state() is Release
                &&& final(lctx).no_locks_held()
                &&& final(krnl).all_objects_unlocked(final(lctx))
                &&& typed_lock_maps_aligned(final(krnl), final(lctx))
                &&& final(steps).snapshot_k() == *final(krnl)
                &&& !(r is CpuIdle) ==> final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running
                &&& !(r is CpuIdle) ==> final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread
                &&& payload is Pages ==> ipc_pages_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                    kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx, waiting_state, payload->Pages_va_range,
                    *pt_regs, ipc_block_flushes_default_pcid(*old(krnl), cpu_id), r)
                &&& payload is Endpoint ==> ipc_endpoint_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                    kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx, waiting_state, payload->Endpoint_endpoint_index,
                    *pt_regs, ipc_block_flushes_default_pcid(*old(krnl), cpu_id), r)
                &&& (payload is Empty || payload is Usize || payload is Cpu || payload is ReceiveCpu || payload is Pci) ==> ipc_ordinary_syscall_trace(
                    final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                    kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx, waiting_state, payload, *pt_regs,
                    ipc_block_flushes_default_pcid(*old(krnl), cpu_id), r)
                &&& r is ErrorIpcNoPeer || r is ErrorIpcSameDirection ==> {
                    &&& endpoint_option is Some
                    &&& old(krnl).ep_mp.dom().contains(ep_ptr)
                    &&& final(krnl).ep_mp.dom().contains(ep_ptr)
                    &&& final(krnl).ep_mp.spec_index(ep_ptr).view().queue == old(krnl).ep_mp.spec_index(ep_ptr).view().queue
                    &&& if r is ErrorIpcNoPeer {
                        old(krnl).ep_mp.spec_index(ep_ptr).view().queue.len() == 0
                    } else {
                        &&& old(krnl).ep_mp.spec_index(ep_ptr).view().queue.len() > 0
                        &&& old(krnl).ep_mp.spec_index(ep_ptr).view().queue_state == if waiting_state.is_endpoint_send_waiting() { EndpointState::SEND } else { EndpointState::RECEIVE }
                    }
                }
            }),
            ret is Ok ==> ({
                let e = ret->Ok_0;
                let cpu = final(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
                let thread = final(krnl).thrd_mp.spec_index(e.current_thread_ptr).view();
                let endpoint = final(krnl).ep_mp.spec_index(e.endpoint_ptr).view();
                &&& *final(steps) == *old(steps)
                &&& final(lctx).kernel_view_locking_state() is Acquire
                &&& *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, cpu_op: final(krnl).cpu_op, thrd_mp: final(krnl).thrd_mp, ep_mp: final(krnl).ep_mp, ..*old(krnl) })
                &&& final(krnl).cpu_arr.entries_unchanged_except(&old(krnl).cpu_arr, cpu_id)
                &&& final(krnl).cpu_op.view().view() == old(krnl).cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep)
                &&& final(krnl).thrd_mp.unchanged_except(&old(krnl).thrd_mp, e.current_thread_ptr)
                &&& final(krnl).ep_mp.unchanged_except(&old(krnl).ep_mp, e.endpoint_ptr)
                &&& old(krnl).cpu_arr.spec_index(cpu_id).value.locking_thread() is None
                &&& old(krnl).thrd_mp.spec_index(e.current_thread_ptr).locking_thread() is None
                &&& old(krnl).ep_mp.spec_index(e.endpoint_ptr).locking_thread() is None
                &&& !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() && !final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed()
                &&& kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl))
                &&& kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp)
                &&& kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl))
                &&& forall|p: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(p)] #![trigger old(krnl).ctn_mp.spec_index(p)]
                    old(krnl).ctn_mp.dom().contains(p) && final(krnl).ctn_mp.dom().contains(p) ==> if final(lctx).container_lock_map().dom().contains(p) {
                        old(krnl).ctn_mp.spec_index(p).locking_thread() is None
                    } else { final(krnl).ctn_mp.spec_index(p).locking_thread() == old(krnl).ctn_mp.spec_index(p).locking_thread() && final(krnl).ctn_mp.spec_index(p).lock_process_owner_u() == old(krnl).ctn_mp.spec_index(p).lock_process_owner_u() }
                &&& forall|p: RwLockProcessPtr| #![trigger final(krnl).prc_mp.spec_index(p)] #![trigger old(krnl).prc_mp.spec_index(p)]
                    old(krnl).prc_mp.dom().contains(p) && final(krnl).prc_mp.dom().contains(p) ==> if final(lctx).process_lock_map().dom().contains(p) {
                        old(krnl).prc_mp.spec_index(p).locking_thread() is None
                    } else { final(krnl).prc_mp.spec_index(p).locking_thread() == old(krnl).prc_mp.spec_index(p).locking_thread() }
                &&& forall|p: RwLockThreadPtr| #![trigger final(krnl).thrd_mp.spec_index(p)] #![trigger old(krnl).thrd_mp.spec_index(p)]
                    old(krnl).thrd_mp.dom().contains(p) && final(krnl).thrd_mp.dom().contains(p) ==> if final(lctx).thread_lock_map().dom().contains(p) {
                        old(krnl).thrd_mp.spec_index(p).locking_thread() is None
                    } else { final(krnl).thrd_mp.spec_index(p).locking_thread() == old(krnl).thrd_mp.spec_index(p).locking_thread() }
                &&& forall|p: RwLockEndpointPtr| #![trigger final(krnl).ep_mp.spec_index(p)] #![trigger old(krnl).ep_mp.spec_index(p)]
                    old(krnl).ep_mp.dom().contains(p) && final(krnl).ep_mp.dom().contains(p) ==> if final(lctx).endpoint_lock_map().dom().contains(p) {
                        old(krnl).ep_mp.spec_index(p).locking_thread() is None
                    } else { final(krnl).ep_mp.spec_index(p).locking_thread() == old(krnl).ep_mp.spec_index(p).locking_thread() }
                &&& forall|p: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(p)] #![trigger old(krnl).pt_mp.spec_index(p)]
                    old(krnl).pt_mp.dom().contains(p) && final(krnl).pt_mp.dom().contains(p) ==> if final(lctx).pagetable_lock_map().dom().contains(p) {
                        old(krnl).pt_mp.spec_index(p).locking_thread() is None
                    } else { final(krnl).pt_mp.spec_index(p).locking_thread() == old(krnl).pt_mp.spec_index(p).locking_thread() }
                &&& forall|p: RwLockPageTableRoot| #![trigger final(krnl).it_mp.spec_index(p)] #![trigger old(krnl).it_mp.spec_index(p)]
                    old(krnl).it_mp.dom().contains(p) && final(krnl).it_mp.dom().contains(p) ==> if final(lctx).iommu_table_lock_map().dom().contains(p) {
                        old(krnl).it_mp.spec_index(p).locking_thread() is None
                    } else { final(krnl).it_mp.spec_index(p).locking_thread() == old(krnl).it_mp.spec_index(p).locking_thread() }
                &&& forall|i: CpuId| #![trigger final(krnl).cpu_arr.spec_index(i)] #![trigger old(krnl).cpu_arr.spec_index(i)]
                    index_valid(NUM_CPUS, i) ==> if final(lctx).cpu_lock_map().dom().contains(i) {
                        old(krnl).cpu_arr.spec_index(i).value.locking_thread() is None
                    } else { final(krnl).cpu_arr.spec_index(i).value.locking_thread() == old(krnl).cpu_arr.spec_index(i).value.locking_thread() }
                &&& typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write)
                &&& e.cpu_lock_perm.view().state() is WriteLock && e.cpu_lock_perm.view().thread_id() == final(lctx).thread_id()
                &&& e.cpu_lock_perm.view().lock_id() == final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id
                &&& typed_lock_map_contains_mode(final(lctx).thread_lock_map(), e.current_thread_ptr, TypedLockMode::Write)
                &&& e.current_thread_lock_perm.view().state() is WriteLock && e.current_thread_lock_perm.view().thread_id() == final(lctx).thread_id()
                &&& e.current_thread_lock_perm.view().lock_id() == final(krnl).thrd_mp.spec_index(e.current_thread_ptr).locking_thread()->Write_lock_id
                &&& typed_lock_map_contains_mode(final(lctx).endpoint_lock_map(), e.endpoint_ptr, TypedLockMode::Write)
                &&& e.endpoint_lock_perm.view().state() is WriteLock && e.endpoint_lock_perm.view().thread_id() == final(lctx).thread_id()
                &&& e.endpoint_lock_perm.view().lock_id() == final(krnl).ep_mp.spec_index(e.endpoint_ptr).locking_thread()->Write_lock_id
                &&& final(krnl).prc_mp.dom().contains(e.process_ptr)
                &&& final(krnl).thrd_mp.dom().contains(e.current_thread_ptr) && !final(krnl).thrd_mp.spec_index(e.current_thread_ptr).being_killed()
                &&& final(krnl).ep_mp.dom().contains(e.endpoint_ptr)
                &&& cpu.state is Running && cpu.current_process == Some(e.process_ptr) && cpu.current_thread == Some(e.current_thread_ptr)
                &&& thread.state == (ThreadState::RUNNING { cpu_id }) && thread.owning_proc == e.process_ptr && thread.owning_container == cpu.owning_container
                &&& thread.endpoint_descriptors.wf() && thread.endpoint_descriptors.spec_index(ep_idx) == Some(e.endpoint_ptr)
                &&& thread.free_quota_pending_clean() && thread.temp_alloc_clean() && thread.syscall_progress.view() is None
                &&& !final(krnl).thrd_mp.spec_index(e.current_thread_ptr).view_ghost().exited
                &&& final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (cpu.current_cr3, cpu.current_pcid)
                &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view()
                &&& !endpoint.queue.view().contains(e.current_thread_ptr)
                &&& e.queue_len == endpoint.queue.len() && e.queue_is_send == (endpoint.queue_state is SEND)
                &&& (e.queue_len == 0 || e.queue_is_send == waiting_state.is_endpoint_send_waiting()) ==> blocking
                &&& waiting_state is RECEIVING_CALL ==> (thread.caller is Some) == expect_caller
                &&& final(lctx).page_lock_map().dom().is_empty()
                &&& final(lctx).cpu_lock_map().dom() =~= set![cpu_id]
                &&& final(lctx).container_lock_map().dom().is_empty()
                &&& final(lctx).process_lock_map().dom().is_empty()
                &&& final(lctx).thread_lock_map().dom() =~= set![e.current_thread_ptr]
                &&& final(lctx).endpoint_lock_map().dom() =~= set![e.endpoint_ptr]
                &&& final(lctx).scheduler_lock_map().dom().is_empty()
                &&& final(lctx).pcid_allocator_lock_map().dom().is_empty()
                &&& final(lctx).cpu_set_lock_map().dom().is_empty()
                &&& final(lctx).pagetable_lock_map().dom().is_empty()
                &&& final(lctx).pagetable_window_lock_map().dom().is_empty()
                &&& final(lctx).iommu_table_lock_map().dom().is_empty()
                &&& final(lctx).iommu_root_table_lock_map().dom().is_empty()
                &&& final(lctx).allocator_quota_4k_lock_map().dom().is_empty()
                &&& final(lctx).allocator_cache_4k_lock_map().dom().is_empty()
                &&& final(lctx).allocator_global_pool_4k_lock_map().dom().is_empty()
                &&& final(lctx).allocator_quota_2m_lock_map().dom().is_empty()
                &&& final(lctx).allocator_cache_2m_lock_map().dom().is_empty()
                &&& final(lctx).allocator_global_pool_2m_lock_map().dom().is_empty()
                &&& final(lctx).allocator_quota_1g_lock_map().dom().is_empty()
                &&& final(lctx).allocator_cache_1g_lock_map().dom().is_empty()
                &&& final(lctx).allocator_global_pool_1g_lock_map().dom().is_empty()
                &&& final(lctx).cpu_offline_flag_lock_map().dom().is_empty()
                &&& final(lctx).pcid_needflush_lock_map().dom().is_empty()
                &&& typed_lock_maps_aligned(final(krnl), final(lctx))
                &&& !expect_caller ==> ipc_entry_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, waiting_state, blocking) == if e.queue_len == 0 || e.queue_is_send == waiting_state.is_endpoint_send_waiting() { Some(RetValueType::CpuIdle) }
                    else if old(krnl).thrd_mp.spec_index(old(krnl).ep_mp.spec_index(e.endpoint_ptr).view().queue.view()[0]).being_killed() { Some(RetValueType::ErrorIpcPeerKilled) }
                    else { None }
                &&& expect_caller ==> ipc_reply_entry_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx) == if e.queue_len != 0 && e.queue_is_send { Some(RetValueType::ErrorIpcSameDirection) }
                    else if old(krnl).thrd_mp.spec_index(thread.caller->Some_0).being_killed() { Some(RetValueType::ErrorIpcPeerKilled) }
                    else { None }
            }),
    {
        proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
        let cpu_lock_res = wlock_cpu_if_running(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id);
        if cpu_lock_res.is_none() {
            proof {
                ipc_entry_result_from_k(&*old(krnl), cpu_id, ep_idx, waiting_state, false, Some(RetValueType::CpuIdle));
                if expect_caller { ipc_reply_entry_result_from_k(&*old(krnl), cpu_id, ep_idx, Some(RetValueType::CpuIdle)); }
                else { ipc_entry_result_from_k(&*old(krnl), cpu_id, ep_idx, waiting_state, blocking, Some(RetValueType::CpuIdle)); }
                ipc_syscall_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, ep_idx,
                    waiting_state, payload, *pt_regs, ipc_block_flushes_default_pcid(*old(krnl), cpu_id), RetValueType::CpuIdle);
            }
            return Err(RetValueType::CpuIdle);
        }
        let Tracked(cpu_lock_perm) = cpu_lock_res.unwrap();

        let cpu_ref = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
        let prc_ptr = cpu_ref.current_process().unwrap();
        let current_thrd_ptr = cpu_ref.current_thread().unwrap();

        proof {
            assert(krnl.prc_mp.dom().contains(prc_ptr)) by { process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); };
            process_perms_wf_at(krnl.prc_mp, prc_ptr);
            assert({
                &&& krnl.prc_mp.dom().contains(prc_ptr)
                &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container
            }) by { process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); };
        }

        proof {
            assert({
                &&& krnl.thrd_mp.dom().contains(current_thrd_ptr)
                &&& krnl.thrd_mp.spec_index(current_thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id })
                &&& krnl.thrd_mp.spec_index(current_thrd_ptr).view().owning_proc == prc_ptr
                &&& krnl.thrd_mp.spec_index(current_thrd_ptr).view().owning_container == krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container
                &&& krnl.thrd_mp.spec_index(current_thrd_ptr).view().container_depth == krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().container_depth
                &&& krnl.thrd_mp.spec_index(current_thrd_ptr).view().process_depth == krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().depth
            }) by { thread_cpu_wf_cpu_at(krnl.thrd_mp, krnl.cpu_arr, cpu_id); process_thread_wf_at(krnl.prc_mp, krnl.thrd_mp, current_thrd_ptr); };
            assert({
                &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().container_depth == krnl.thrd_mp.spec_index(current_thrd_ptr).view().container_depth
                &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().process_depth == krnl.thrd_mp.spec_index(current_thrd_ptr).view().process_depth
            }) by { process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id); container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, prc_ptr); };
        }
        let current_thread_res = krnl.wlock_current_running_thread_unless_killed(current_thrd_ptr, Tracked(&mut *lctx));

        if current_thread_res.is_none() {
            proof { assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; }; }
            proof { assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; }; }
            release_cpu_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Tracked(cpu_lock_perm));
            proof {
                assert(krnl.cpu_op.view().view() =~= old(steps).snapshot_k().cpu_op.view().view());
                assert(kernel_k_to_kernel_u(old(steps).snapshot_k()) == kernel_k_to_kernel_u(*krnl)) by { kernel_restored_locks_implies_u_eq(&old(steps).snapshot_k(), &*krnl, cpu_id, None, None, Some(current_thrd_ptr), None, None); };
            }
            proof {
                ipc_syscall_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, ep_idx,
                    waiting_state, payload, *pt_regs, ipc_block_flushes_default_pcid(*old(krnl), cpu_id), RetValueType::ErrorThreadKilled);
            }
            proof {
                if expect_caller { ipc_reply_entry_result_from_k(&*old(krnl), cpu_id, ep_idx, Some(RetValueType::ErrorThreadKilled)); }
                else { ipc_entry_result_from_k(&*old(krnl), cpu_id, ep_idx, waiting_state, blocking, Some(RetValueType::ErrorThreadKilled)); }
            }
            return Err(RetValueType::ErrorThreadKilled);
        }
        let Tracked(current_thread_lock_perm) = current_thread_res.unwrap();
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        }

        let current_thread_ref = krnl.thrd_mp.borrow_typed(current_thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&current_thread_lock_perm));
        let receives_call = match waiting_state { ThreadState::RECEIVING_CALL => true, _ => false };
        if receives_call && current_thread_ref.caller.is_some() != expect_caller {
            release_cpu_and_thread_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, current_thrd_ptr, Tracked(current_thread_lock_perm), Tracked(cpu_lock_perm));
            proof {
                assert(krnl.cpu_op.view().view() =~= old(steps).snapshot_k().cpu_op.view().view());
                assert(kernel_k_to_kernel_u(old(steps).snapshot_k()) == kernel_k_to_kernel_u(*krnl)) by { kernel_restored_locks_implies_u_eq(&old(steps).snapshot_k(), &*krnl, cpu_id, None, None, Some(current_thrd_ptr), None, None); };
                ipc_syscall_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, ep_idx,
                    waiting_state, payload, *pt_regs, ipc_block_flushes_default_pcid(*old(krnl), cpu_id), RetValueType::ErrorReplyOutOfPhase);
                if expect_caller { ipc_reply_entry_result_from_k(&*old(krnl), cpu_id, ep_idx, Some(RetValueType::ErrorReplyOutOfPhase)); }
                else { ipc_entry_result_from_k(&*old(krnl), cpu_id, ep_idx, waiting_state, blocking, Some(RetValueType::ErrorReplyOutOfPhase)); }
            }
            return Err(RetValueType::ErrorReplyOutOfPhase);
        }
        let ep_ptr = match *current_thread_ref.endpoint_descriptors.get(ep_idx) {
            Some(ep_ptr) => ep_ptr,
            None => {
                release_cpu_and_thread_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, current_thrd_ptr, Tracked(current_thread_lock_perm), Tracked(cpu_lock_perm));
                proof {
                    assert(krnl.cpu_op.view().view() =~= old(steps).snapshot_k().cpu_op.view().view());
                    assert(kernel_k_to_kernel_u(old(steps).snapshot_k()) == kernel_k_to_kernel_u(*krnl)) by { kernel_restored_locks_implies_u_eq(&old(steps).snapshot_k(), &*krnl, cpu_id, None, None, Some(current_thrd_ptr), None, None); };
                }
                proof {
                    ipc_syscall_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, ep_idx,
                        waiting_state, payload, *pt_regs, ipc_block_flushes_default_pcid(*old(krnl), cpu_id), RetValueType::ErrorInvalidEndpoint);
                }
                proof {
                    if expect_caller { ipc_reply_entry_result_from_k(&*old(krnl), cpu_id, ep_idx, Some(RetValueType::ErrorInvalidEndpoint)); }
                    else { ipc_entry_result_from_k(&*old(krnl), cpu_id, ep_idx, waiting_state, blocking, Some(RetValueType::ErrorInvalidEndpoint)); }
                }
                return Err(RetValueType::ErrorInvalidEndpoint);
            },
        };
        ipc_lock_entry_endpoint(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, ep_idx, waiting_state, payload, blocking, expect_caller, pt_regs, prc_ptr,
            current_thrd_ptr, ep_ptr, Tracked(cpu_lock_perm), Tracked(current_thread_lock_perm))
    }

    pub(super) fn syscall_ipc_ordinary(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
        ep_idx: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, blocking: bool, pt_regs: &mut Registers,
    ) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
            edp_idx_valid(ep_idx),
            waiting_state is SENDING || waiting_state is RECEIVING,
            blocking || payload is Empty,
            match payload {
                IPCPayLoad::Empty => true,
                IPCPayLoad::Cpu { cpu_id } => index_valid(NUM_CPUS, cpu_id) && waiting_state is SENDING,
                IPCPayLoad::ReceiveCpu => waiting_state is RECEIVING,
                IPCPayLoad::Pages { va_range } => {
                    &&& va_range.wf()
                    &&& va_range.len > 0
                },
                IPCPayLoad::Endpoint { endpoint_index: ep_idx } => edp_idx_valid(ep_idx),
                IPCPayLoad::Pci { bus, dev, fun } => pci_bdf_valid(bus as usize, dev as usize, fun as usize),
                _ => false,
            },
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).no_locks_held(),
            old(steps).snapshot_k() == *old(krnl),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            old(steps).view().len() <= final(steps).view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            payload is Pages ==> ipc_pages_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                waiting_state, payload->Pages_va_range, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id), ret),
            payload is Endpoint ==> ipc_endpoint_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                waiting_state, payload->Endpoint_endpoint_index, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id), ret),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(steps).snapshot_k() == *final(krnl),
            (payload is Empty || payload is Cpu || payload is ReceiveCpu || payload is Pci) ==> ipc_ordinary_syscall_trace(
                final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()),
                kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx, waiting_state, payload, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id), ret),
            final(krnl).all_objects_unlocked(final(lctx)),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            !blocking && !(ret is CpuIdle) ==> final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            !blocking && !(ret is CpuIdle) ==> final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread,
            !blocking && old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running && !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() ==> !(ret is CpuIdle),
            ret is ErrorIpcNoPeer || ret is ErrorIpcSameDirection ==> !blocking,
            ret is ErrorIpcNoPeer || ret is ErrorIpcSameDirection ==> {
                let current_thrd_ptr = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread.unwrap();
                let endpoint_option = old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().endpoint_descriptors.view().spec_index(ep_idx as int);
                let ep_ptr = endpoint_option.unwrap();
                &&& endpoint_option is Some
                &&& old(krnl).ep_mp.dom().contains(ep_ptr)
                &&& final(krnl).ep_mp.dom().contains(ep_ptr)
                &&& final(krnl).ep_mp.spec_index(ep_ptr).view().queue == old(krnl).ep_mp.spec_index(ep_ptr).view().queue
                &&& if ret is ErrorIpcNoPeer {
                    old(krnl).ep_mp.spec_index(ep_ptr).view().queue.len() == 0
                } else {
                    &&& old(krnl).ep_mp.spec_index(ep_ptr).view().queue.len() > 0
                    &&& old(krnl).ep_mp.spec_index(ep_ptr).view().queue_state == if waiting_state is SENDING { EndpointState::SEND } else { EndpointState::RECEIVE }
                }
            },
            payload is Cpu && ret is Success ==> final(krnl).cpu_arr.spec_index(payload->Cpu_cpu_id).view().view().view().state is Off
                && final(krnl).cpu_arr.spec_index(payload->Cpu_cpu_id).view().view().view().owning_container != old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
            ret is SuccessUsize ==> final(krnl).cpu_arr.spec_index(ret->SuccessUsize_value).view().view().view().state is Off
                && final(krnl).cpu_arr.spec_index(ret->SuccessUsize_value).view().view().view().owning_container == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
            ret is CpuIdle && old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running && !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() ==> {
                &&& final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(*old(krnl)), new_u: kernel_k_to_kernel_u(*final(krnl)) })
                &&& ipc_block_step_pre(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, waiting_state)
                &&& ipc_block_step(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                    waiting_state, payload, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id))
            },
            ret is SuccessUsize ==> payload is ReceiveCpu && index_valid(NUM_CPUS, ret->SuccessUsize_value),
            payload is Empty ==> (ret is Success || ret is CpuIdle || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch || ret is ErrorIpcNoPeer || ret is ErrorIpcSameDirection),
            payload is Pages ==> (ret is Success || ret is CpuIdle || ret is Error || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled
                || ret is ErrorIpcTypeMismatch || ret is ErrorIpcSameProcess || ret is ErrorIpcSourceUnmapped || ret is ErrorIpcPageOwnerMismatch || ret is ErrorNoQuota || ret is ErrorVaInUse),
            payload is Cpu || payload is ReceiveCpu ==> (ret is Success || ret is SuccessUsize || ret is CpuIdle || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint
                || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch || ret is ErrorIpcSameContainer || ret is ErrorIpcCpuOwnerMismatch || ret is ErrorIpcCpuNotOff),
            payload is ReceiveCpu ==> !(ret is Success),
            payload is Pci ==> (ret is Success || ret is CpuIdle || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled
                || ret is ErrorIpcTypeMismatch || ret is ErrorIpcSameProcess || ret is ErrorIpcPciOwnerMismatch),
            payload is Endpoint ==> (ret is Success || ret is CpuIdle || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled
                || ret is ErrorIpcTypeMismatch || ret is ErrorIpcEndpointSourceInvalid || ret is ErrorIpcEndpointTargetInUse || ret is ErrorIpcEndpointOwnerMismatch),
            ipc_rejection(ret) == ipc_entry_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, waiting_state, blocking),
    {
        hide(Set::is_empty);
        let entry = match ipc_lock_entry(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, ep_idx, waiting_state, payload, blocking, false, &*pt_regs) { Ok(entry) => entry, Err(ret) => return ret };
        let IpcEntryLocked { process_ptr: prc_ptr, current_thread_ptr: current_thrd_ptr, endpoint_ptr: ep_ptr, queue_len, queue_is_send, cpu_lock_perm, current_thread_lock_perm, endpoint_lock_perm } = entry;
        let waiting_is_send = match waiting_state { ThreadState::SENDING => true, _ => false };
        if queue_len == 0 || queue_is_send == waiting_is_send {
            let ret = ipc_block_current(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, current_thrd_ptr, ep_ptr, ep_idx, waiting_state, payload, &*pt_regs, cpu_lock_perm, current_thread_lock_perm, endpoint_lock_perm);
            proof {
                ipc_syscall_trace_from_block(&*steps, old(steps).view(), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, ep_idx, waiting_state,
                    payload, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id));
            }
            return ret;
        }
        let ret = ipc_rendezvous_from_queue(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, current_thrd_ptr, ep_ptr, ep_idx, waiting_state, payload, waiting_is_send, cpu_lock_perm, current_thread_lock_perm, endpoint_lock_perm);
        proof {
            ipc_syscall_trace_from_rendezvous(&*steps, old(steps).view(), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, ep_idx, waiting_state,
                payload, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id), ret);
        }
        ret
    }

    /// Performs the rendezvous with the locked, live queue head `peer_thrd_ptr`: dispatches on the two payloads to the
    /// matching transfer, or finishes a payload-free or mismatched rendezvous by scheduling the peer.
    fn ipc_rendezvous_locked_peer(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
        prc_ptr: RwLockProcessPtr, current_thrd_ptr: RwLockThreadPtr, ep_ptr: RwLockEndpointPtr, ep_idx: EndpointIdx,
        waiting_state: ThreadState, payload: IPCPayLoad, waiting_is_send: bool, Tracked(cpu_lock_perm): Tracked<LockPerm>,
        Tracked(current_thread_lock_perm): Tracked<LockPerm>, Tracked(endpoint_lock_perm): Tracked<LockPerm>, peer_thrd_ptr: RwLockThreadPtr,
        Tracked(peer_thread_lock_perm): Tracked<LockPerm>,
    ) -> (ret: RetValueType)
        requires
            old(krnl).inv(),
            forall|p: RwLockContainerPtr| #![trigger old(krnl).ctn_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ctn_mp.spec_index(p)]
                old(steps).snapshot_k().ctn_mp.dom().contains(p) && old(krnl).ctn_mp.dom().contains(p) ==> if old(lctx).container_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).ctn_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() && old(krnl).ctn_mp.spec_index(p).lock_process_owner_u() == old(steps).snapshot_k().ctn_mp.spec_index(p).lock_process_owner_u() },
            forall|p: RwLockProcessPtr| #![trigger old(krnl).prc_mp.spec_index(p)] #![trigger old(steps).snapshot_k().prc_mp.spec_index(p)]
                old(steps).snapshot_k().prc_mp.dom().contains(p) && old(krnl).prc_mp.dom().contains(p) ==> if old(lctx).process_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).prc_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() },
            forall|p: RwLockThreadPtr| #![trigger old(krnl).thrd_mp.spec_index(p)] #![trigger old(steps).snapshot_k().thrd_mp.spec_index(p)]
                old(steps).snapshot_k().thrd_mp.dom().contains(p) && old(krnl).thrd_mp.dom().contains(p) ==> if old(lctx).thread_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().thrd_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).thrd_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().thrd_mp.spec_index(p).locking_thread() },
            forall|p: RwLockEndpointPtr| #![trigger old(krnl).ep_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ep_mp.spec_index(p)]
                old(steps).snapshot_k().ep_mp.dom().contains(p) && old(krnl).ep_mp.dom().contains(p) ==> if old(lctx).endpoint_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).ep_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() },
            forall|p: RwLockPageTableRoot| #![trigger old(krnl).pt_mp.spec_index(p)] #![trigger old(steps).snapshot_k().pt_mp.spec_index(p)]
                old(steps).snapshot_k().pt_mp.dom().contains(p) && old(krnl).pt_mp.dom().contains(p) ==> if old(lctx).pagetable_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).pt_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() },
            old(krnl).pt_lower == old(steps).snapshot_k().pt_lower,
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
            edp_idx_valid(ep_idx),
            old(lctx).kernel_view_locking_state() is Acquire,
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
            old(krnl).irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
            old(krnl).irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
            old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            old(krnl).cpu_tlb.structure_caches.view() == old(steps).snapshot_k().cpu_tlb.structure_caches.view(),
            old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            old(krnl).cpu_set_mp == old(steps).snapshot_k().cpu_set_mp,
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            cpu_lock_perm.state() is WriteLock,
            cpu_lock_perm.thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            old(krnl).prc_mp.dom().contains(prc_ptr),
            old(krnl).thrd_mp.dom().contains(current_thrd_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thrd_ptr, TypedLockMode::Write),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).being_killed() == false,
            current_thread_lock_perm.state() is WriteLock,
            current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
            current_thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(current_thrd_ptr).locking_thread()->Write_lock_id,
            old(krnl).ep_mp.dom().contains(ep_ptr),
            typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), ep_ptr, TypedLockMode::Write),
            endpoint_lock_perm.state() is WriteLock,
            endpoint_lock_perm.thread_id() == old(lctx).thread_id(),
            endpoint_lock_perm.lock_id() == old(krnl).ep_mp.spec_index(ep_ptr).locking_thread()->Write_lock_id,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thrd_ptr),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().owning_proc == prc_ptr,
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().owning_container == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
            old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().endpoint_descriptors.wf(),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().endpoint_descriptors.spec_index(ep_idx) == Some(ep_ptr),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().free_quota_pending_clean(),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().temp_alloc_clean(),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().syscall_progress.view() is None,
            !old(krnl).thrd_mp.spec_index(current_thrd_ptr).view_ghost().exited,
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
            old(lctx).container_lock_map().dom().is_empty(),
            old(lctx).process_lock_map().dom().is_empty(),
            old(lctx).thread_lock_map().dom() =~= set![current_thrd_ptr, peer_thrd_ptr],
            old(lctx).endpoint_lock_map().dom() =~= set![ep_ptr],
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
            waiting_state is SENDING || waiting_state is RECEIVING,
            waiting_is_send == (waiting_state is SENDING),
            old(krnl).ep_mp.spec_index(ep_ptr).view().queue.len() > 0,
            old(krnl).ep_mp.spec_index(ep_ptr).view().queue.view()[0] == peer_thrd_ptr,
            old(krnl).thrd_mp.perms_wf(),
            old(krnl).thrd_mp.dom().contains(peer_thrd_ptr) && peer_thrd_ptr != current_thrd_ptr,
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thrd_ptr, TypedLockMode::Write),
            old(krnl).thrd_mp.spec_index(peer_thrd_ptr).being_killed() == false,
            peer_thread_lock_perm.state() is WriteLock && peer_thread_lock_perm.thread_id() == old(lctx).thread_id(),
            peer_thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(peer_thrd_ptr).locking_thread()->Write_lock_id,
            old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().state.is_endpoint_waiting(),
            old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().blocking_endpoint_ptr == Some(ep_ptr),
            old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().free_quota_pending_clean(),
            old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().temp_alloc_clean(),
            old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view().syscall_progress.view() is None,
            !old(krnl).thrd_mp.spec_index(peer_thrd_ptr).view_ghost().exited,
            (old(krnl).ep_mp.spec_index(ep_ptr).view().queue_state is SEND) != waiting_is_send,
            match payload {
                IPCPayLoad::Empty => true,
                IPCPayLoad::Cpu { cpu_id } => index_valid(NUM_CPUS, cpu_id) && waiting_state is SENDING,
                IPCPayLoad::ReceiveCpu => waiting_state is RECEIVING,
                IPCPayLoad::Pages { va_range } => va_range.wf() && va_range.len > 0,
                IPCPayLoad::Endpoint { endpoint_index: ep_idx } => edp_idx_valid(ep_idx),
                IPCPayLoad::Pci { bus, dev, fun } => pci_bdf_valid(bus as usize, dev as usize, fun as usize),
                _ => false,
            },
        ensures
            old(steps).view().len() <= final(steps).view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            payload is Pages ==> ipc_pages_rendezvous_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                waiting_state, payload->Pages_va_range, ret),
            payload is Endpoint ==> ipc_endpoint_rendezvous_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                waiting_state, payload->Endpoint_endpoint_index, ret),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(steps).snapshot_k() == *final(krnl),
            (payload is Empty || payload is Cpu || payload is ReceiveCpu || payload is Pci) ==> {
                &&& if ipc_rendezvous_ret(ret) {
                    &&& final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(old(steps).snapshot_k()), new_u: kernel_k_to_kernel_u(*final(krnl)) })
                    &&& ret == ipc_rendezvous_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, ep_idx, waiting_state, payload)
                    &&& ipc_rendezvous_step_pre(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, ep_idx, waiting_state, payload)
                    &&& ipc_rendezvous_step(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx, waiting_state, payload)
                } else {
                    &&& final(steps).view() == old(steps).view()
                    &&& kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(old(steps).snapshot_k())
                }
            },
            final(krnl).all_objects_unlocked(final(lctx)),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            payload is Empty ==> final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            payload is Empty ==> final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thrd_ptr),
            payload is Cpu && ret is Success ==> final(krnl).cpu_arr.spec_index(payload->Cpu_cpu_id).view().view().view().state is Off
                && final(krnl).cpu_arr.spec_index(payload->Cpu_cpu_id).view().view().view().owning_container != old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
            ret is SuccessUsize ==> final(krnl).cpu_arr.spec_index(ret->SuccessUsize_value).view().view().view().state is Off
                && final(krnl).cpu_arr.spec_index(ret->SuccessUsize_value).view().view().view().owning_container == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
            ret is SuccessUsize ==> payload is ReceiveCpu && index_valid(NUM_CPUS, ret->SuccessUsize_value),
            payload is Empty ==> (ret is Success || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch),
            payload is Pages ==> (ret is Success || ret is Error || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled
                || ret is ErrorIpcTypeMismatch || ret is ErrorIpcSameProcess || ret is ErrorIpcSourceUnmapped || ret is ErrorIpcPageOwnerMismatch || ret is ErrorNoQuota || ret is ErrorVaInUse),
            payload is Cpu || payload is ReceiveCpu ==> (ret is Success || ret is SuccessUsize || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint
                || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch || ret is ErrorIpcSameContainer || ret is ErrorIpcCpuOwnerMismatch || ret is ErrorIpcCpuNotOff),
            payload is ReceiveCpu ==> !(ret is Success),
            payload is Pci ==> (ret is Success || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled
                || ret is ErrorIpcTypeMismatch || ret is ErrorIpcSameProcess || ret is ErrorIpcPciOwnerMismatch),
            payload is Endpoint ==> (ret is Success || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch
                || ret is ErrorIpcEndpointSourceInvalid || ret is ErrorIpcEndpointTargetInUse || ret is ErrorIpcEndpointOwnerMismatch),
            ipc_rejection(ret) is None,
    {
        proof {
            assert({
                let pre = steps.snapshot_k();
                &&& pre.thrd_mp.dom().contains(current_thrd_ptr) && pre.thrd_mp.dom().contains(peer_thrd_ptr) && pre.ep_mp.dom().contains(ep_ptr)
                &&& pre.cpu_arr.spec_index(cpu_id).value.view().view().current_thread == Some(current_thrd_ptr)
                &&& pre.thrd_mp.spec_index(current_thrd_ptr).view().endpoint_descriptors.view()[ep_idx as int] == Some(ep_ptr)
                &&& pre.ep_mp.spec_index(ep_ptr).view().queue.view()[0] == peer_thrd_ptr
                &&& pre.thrd_mp.spec_index(peer_thrd_ptr).view().ipc_payload == krnl.thrd_mp.spec_index(peer_thrd_ptr).view().ipc_payload
                &&& pre.thrd_mp.spec_index(peer_thrd_ptr).view().state == krnl.thrd_mp.spec_index(peer_thrd_ptr).view().state
            }) by {
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
                reveal(kernel_thread_nonlock_fields_unchanged); reveal(kernel_endpoint_nonlock_fields_unchanged);
            };
            thread_perms_wf_at(krnl.thrd_mp, peer_thrd_ptr);
        }
        let peer_thread_ref = krnl.thrd_mp.borrow_typed(peer_thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&peer_thread_lock_perm));
        let rendezvous_result = match (waiting_state, payload, peer_thread_ref.state, peer_thread_ref.ipc_payload) {
            (ThreadState::SENDING, IPCPayLoad::Cpu { cpu_id: transfer_cpu_id }, ThreadState::RECEIVING, IPCPayLoad::ReceiveCpu)
                | (ThreadState::RECEIVING, IPCPayLoad::ReceiveCpu, ThreadState::SENDING, IPCPayLoad::Cpu { cpu_id: transfer_cpu_id }) => {
                let step_result = ipc_rendezvous_cpu(
                    krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, current_thrd_ptr, ep_ptr, Ghost(ep_idx),
                    Ghost(waiting_state), peer_thrd_ptr, waiting_is_send, transfer_cpu_id, Ghost(payload), Tracked(cpu_lock_perm),
                    Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm), Tracked(peer_thread_lock_perm),
                );
                return step_result;
            },
            (ThreadState::SENDING, IPCPayLoad::Endpoint { endpoint_index: source_ep_idx },
                ThreadState::RECEIVING, IPCPayLoad::Endpoint { endpoint_index: target_ep_idx }) => {
                let step_result = ipc_rendezvous_endpoint(
                    krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, current_thrd_ptr, ep_ptr, peer_thrd_ptr,
                    current_thrd_ptr, peer_thrd_ptr, source_ep_idx, target_ep_idx, Tracked(cpu_lock_perm),
                    Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm), Ghost(ep_idx), Ghost(waiting_state), Tracked(peer_thread_lock_perm),
                );
                return step_result;
            },
            (ThreadState::RECEIVING, IPCPayLoad::Endpoint { endpoint_index: target_ep_idx },
                ThreadState::SENDING, IPCPayLoad::Endpoint { endpoint_index: source_ep_idx }) => {
                let step_result = ipc_rendezvous_endpoint(
                    krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, current_thrd_ptr, ep_ptr, peer_thrd_ptr,
                    peer_thrd_ptr, current_thrd_ptr, source_ep_idx, target_ep_idx, Tracked(cpu_lock_perm),
                    Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm), Ghost(ep_idx), Ghost(waiting_state), Tracked(peer_thread_lock_perm),
                );
                return step_result;
            },
            (ThreadState::SENDING, IPCPayLoad::Pages { va_range: source_range },
                ThreadState::RECEIVING, IPCPayLoad::Pages { va_range: target_range }) if source_range.len == target_range.len => {
                let step_result = ipc_rendezvous_pages(
                    krnl, &source_range, &target_range, current_thrd_ptr, peer_thrd_ptr, cpu_id, prc_ptr, current_thrd_ptr, ep_ptr,
                    peer_thrd_ptr, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(cpu_lock_perm),
                    Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm), Tracked(peer_thread_lock_perm), Ghost(ep_idx), Ghost(waiting_state),
                );
                return step_result;
            },
            (ThreadState::RECEIVING, IPCPayLoad::Pages { va_range: target_range },
                ThreadState::SENDING, IPCPayLoad::Pages { va_range: source_range }) if source_range.len == target_range.len => {
                let step_result = ipc_rendezvous_pages(
                    krnl, &source_range, &target_range, peer_thrd_ptr, current_thrd_ptr, cpu_id, prc_ptr, current_thrd_ptr, ep_ptr,
                    peer_thrd_ptr, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(cpu_lock_perm),
                    Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm), Tracked(peer_thread_lock_perm), Ghost(ep_idx), Ghost(waiting_state),
                );
                return step_result;
            },
            (ThreadState::SENDING, IPCPayLoad::Pci { bus, dev, fun }, ThreadState::RECEIVING, IPCPayLoad::Pci { bus: peer_bus, dev: peer_dev, fun: peer_fun })
                if bus == peer_bus && dev == peer_dev && fun == peer_fun => {
                let step_result = ipc_rendezvous_pci(
                    krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, current_thrd_ptr, ep_ptr, Ghost(ep_idx),
                    Ghost(waiting_state), peer_thrd_ptr, waiting_is_send, bus, dev, fun, Ghost(payload), Tracked(cpu_lock_perm),
                    Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm), Tracked(peer_thread_lock_perm),
                );
                return step_result;
            },
            (ThreadState::RECEIVING, IPCPayLoad::Pci { bus, dev, fun }, ThreadState::SENDING, IPCPayLoad::Pci { bus: peer_bus, dev: peer_dev, fun: peer_fun })
                if bus == peer_bus && dev == peer_dev && fun == peer_fun => {
                let step_result = ipc_rendezvous_pci(
                    krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, current_thrd_ptr, ep_ptr, Ghost(ep_idx),
                    Ghost(waiting_state), peer_thrd_ptr, waiting_is_send, bus, dev, fun, Ghost(payload), Tracked(cpu_lock_perm),
                    Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm), Tracked(peer_thread_lock_perm),
                );
                return step_result;
            },
            (ThreadState::SENDING, IPCPayLoad::Empty, ThreadState::RECEIVING, IPCPayLoad::Empty) => RetValueType::Success,
            (ThreadState::RECEIVING, IPCPayLoad::Empty, ThreadState::SENDING, IPCPayLoad::Empty) => RetValueType::Success,
            _ => RetValueType::ErrorIpcTypeMismatch,
        };
        proof { ipc_rendezvous_result_from_k(&steps.snapshot_k(), cpu_id, ep_idx, waiting_state, payload, current_thrd_ptr, ep_ptr, peer_thrd_ptr, rendezvous_result); }

        let step_result = ipc_schedule_waiting_peer_and_finish(
            krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, current_thrd_ptr, ep_ptr, Ghost(ep_idx), Ghost(waiting_state), Ghost(payload),
            peer_thrd_ptr, rendezvous_result, Tracked(cpu_lock_perm), Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm),
            Tracked(peer_thread_lock_perm),
        );
        proof { ipc_rendezvous_trace_error_step(&*steps, old(steps).view(), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, ep_idx, waiting_state, payload, step_result); }
        step_result
    }

    #[verifier::spinoff_prover]
    pub(super) fn ipc_rendezvous_from_queue(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
        prc_ptr: RwLockProcessPtr, current_thrd_ptr: RwLockThreadPtr, ep_ptr: RwLockEndpointPtr, ep_idx: EndpointIdx,
        waiting_state: ThreadState, payload: IPCPayLoad, waiting_is_send: bool, Tracked(cpu_lock_perm): Tracked<LockPerm>,
        Tracked(current_thread_lock_perm): Tracked<LockPerm>, Tracked(endpoint_lock_perm): Tracked<LockPerm>,
    ) -> (ret: RetValueType)
        requires
            old(krnl).inv(),
            forall|p: RwLockContainerPtr| #![trigger old(krnl).ctn_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ctn_mp.spec_index(p)]
                old(steps).snapshot_k().ctn_mp.dom().contains(p) && old(krnl).ctn_mp.dom().contains(p) ==> if old(lctx).container_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).ctn_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() && old(krnl).ctn_mp.spec_index(p).lock_process_owner_u() == old(steps).snapshot_k().ctn_mp.spec_index(p).lock_process_owner_u() },
            forall|p: RwLockProcessPtr| #![trigger old(krnl).prc_mp.spec_index(p)] #![trigger old(steps).snapshot_k().prc_mp.spec_index(p)]
                old(steps).snapshot_k().prc_mp.dom().contains(p) && old(krnl).prc_mp.dom().contains(p) ==> if old(lctx).process_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).prc_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() },
            forall|p: RwLockThreadPtr| #![trigger old(krnl).thrd_mp.spec_index(p)] #![trigger old(steps).snapshot_k().thrd_mp.spec_index(p)]
                old(steps).snapshot_k().thrd_mp.dom().contains(p) && old(krnl).thrd_mp.dom().contains(p) ==> if old(lctx).thread_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().thrd_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).thrd_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().thrd_mp.spec_index(p).locking_thread() },
            forall|p: RwLockEndpointPtr| #![trigger old(krnl).ep_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ep_mp.spec_index(p)]
                old(steps).snapshot_k().ep_mp.dom().contains(p) && old(krnl).ep_mp.dom().contains(p) ==> if old(lctx).endpoint_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).ep_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() },
            forall|p: RwLockPageTableRoot| #![trigger old(krnl).pt_mp.spec_index(p)] #![trigger old(steps).snapshot_k().pt_mp.spec_index(p)]
                old(steps).snapshot_k().pt_mp.dom().contains(p) && old(krnl).pt_mp.dom().contains(p) ==> if old(lctx).pagetable_lock_map().dom().contains(p) {
                    old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() is None
                } else { old(krnl).pt_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() },
            old(krnl).pt_lower == old(steps).snapshot_k().pt_lower,
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
            edp_idx_valid(ep_idx),
            old(lctx).kernel_view_locking_state() is Acquire,
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
            old(krnl).irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
            old(krnl).irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
            old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            old(krnl).cpu_tlb.structure_caches.view() == old(steps).snapshot_k().cpu_tlb.structure_caches.view(),
            old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            old(krnl).cpu_set_mp == old(steps).snapshot_k().cpu_set_mp,
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            cpu_lock_perm.state() is WriteLock,
            cpu_lock_perm.thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            old(krnl).prc_mp.dom().contains(prc_ptr),
            old(krnl).thrd_mp.dom().contains(current_thrd_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thrd_ptr, TypedLockMode::Write),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).being_killed() == false,
            current_thread_lock_perm.state() is WriteLock,
            current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
            current_thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(current_thrd_ptr).locking_thread()->Write_lock_id,
            old(krnl).ep_mp.dom().contains(ep_ptr),
            typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), ep_ptr, TypedLockMode::Write),
            endpoint_lock_perm.state() is WriteLock,
            endpoint_lock_perm.thread_id() == old(lctx).thread_id(),
            endpoint_lock_perm.lock_id() == old(krnl).ep_mp.spec_index(ep_ptr).locking_thread()->Write_lock_id,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thrd_ptr),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().owning_proc == prc_ptr,
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().owning_container == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
            old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().endpoint_descriptors.wf(),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().endpoint_descriptors.spec_index(ep_idx) == Some(ep_ptr),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().free_quota_pending_clean(),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().temp_alloc_clean(),
            old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().syscall_progress.view() is None,
            !old(krnl).thrd_mp.spec_index(current_thrd_ptr).view_ghost().exited,
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
            old(lctx).container_lock_map().dom().is_empty(),
            old(lctx).process_lock_map().dom().is_empty(),
            old(lctx).thread_lock_map().dom() =~= set![current_thrd_ptr],
            old(lctx).endpoint_lock_map().dom() =~= set![ep_ptr],
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
            waiting_state is SENDING || waiting_state is RECEIVING,
            waiting_is_send == (waiting_state is SENDING),
            old(krnl).ep_mp.spec_index(ep_ptr).view().queue.len() > 0,
            (old(krnl).ep_mp.spec_index(ep_ptr).view().queue_state is SEND) != waiting_is_send,
            match payload {
                IPCPayLoad::Empty => true,
                IPCPayLoad::Cpu { cpu_id } => index_valid(NUM_CPUS, cpu_id) && waiting_state is SENDING,
                IPCPayLoad::ReceiveCpu => waiting_state is RECEIVING,
                IPCPayLoad::Pages { va_range } => va_range.wf() && va_range.len > 0,
                IPCPayLoad::Endpoint { endpoint_index: ep_idx } => edp_idx_valid(ep_idx),
                IPCPayLoad::Pci { bus, dev, fun } => pci_bdf_valid(bus as usize, dev as usize, fun as usize),
                _ => false,
            },
        ensures
            old(steps).view().len() <= final(steps).view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            payload is Pages ==> ipc_pages_rendezvous_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                waiting_state, payload->Pages_va_range, ret),
            payload is Endpoint ==> ipc_endpoint_rendezvous_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                waiting_state, payload->Endpoint_endpoint_index, ret),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(steps).snapshot_k() == *final(krnl),
            (payload is Empty || payload is Cpu || payload is ReceiveCpu || payload is Pci) ==> {
                &&& if ipc_rendezvous_ret(ret) {
                    &&& final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(old(steps).snapshot_k()), new_u: kernel_k_to_kernel_u(*final(krnl)) })
                    &&& ret == ipc_rendezvous_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, ep_idx, waiting_state, payload)
                    &&& ipc_rendezvous_step_pre(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, ep_idx, waiting_state, payload)
                    &&& ipc_rendezvous_step(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx, waiting_state, payload)
                } else {
                    &&& final(steps).view() == old(steps).view()
                    &&& kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(old(steps).snapshot_k())
                }
            },
            final(krnl).all_objects_unlocked(final(lctx)),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            payload is Empty ==> final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            payload is Empty ==> final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thrd_ptr),
            payload is Cpu && ret is Success ==> final(krnl).cpu_arr.spec_index(payload->Cpu_cpu_id).view().view().view().state is Off
                && final(krnl).cpu_arr.spec_index(payload->Cpu_cpu_id).view().view().view().owning_container != old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
            ret is SuccessUsize ==> final(krnl).cpu_arr.spec_index(ret->SuccessUsize_value).view().view().view().state is Off
                && final(krnl).cpu_arr.spec_index(ret->SuccessUsize_value).view().view().view().owning_container == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
            ret is SuccessUsize ==> payload is ReceiveCpu && index_valid(NUM_CPUS, ret->SuccessUsize_value),
            payload is Empty ==> (ret is Success || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch),
            payload is Pages ==> (ret is Success || ret is Error || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled
                || ret is ErrorIpcTypeMismatch || ret is ErrorIpcSameProcess || ret is ErrorIpcSourceUnmapped || ret is ErrorIpcPageOwnerMismatch || ret is ErrorNoQuota || ret is ErrorVaInUse),
            payload is Cpu || payload is ReceiveCpu ==> (ret is Success || ret is SuccessUsize || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint
                || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch || ret is ErrorIpcSameContainer || ret is ErrorIpcCpuOwnerMismatch || ret is ErrorIpcCpuNotOff),
            payload is ReceiveCpu ==> !(ret is Success),
            payload is Pci ==> (ret is Success || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled
                || ret is ErrorIpcTypeMismatch || ret is ErrorIpcSameProcess || ret is ErrorIpcPciOwnerMismatch),
            payload is Endpoint ==> (ret is Success || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch
                || ret is ErrorIpcEndpointSourceInvalid || ret is ErrorIpcEndpointTargetInUse || ret is ErrorIpcEndpointOwnerMismatch),
            ipc_rejection(ret) == if old(steps).snapshot_k().thrd_mp.spec_index(old(steps).snapshot_k().ep_mp.spec_index(ep_ptr).view().queue.view()[0]).being_killed() {
                Some(RetValueType::ErrorIpcPeerKilled)
            } else { None },
    {
        assert(krnl.ep_mp.perms_wf() && krnl.ep_mp.spec_index(ep_ptr).is_init() && krnl.ep_mp.spec_index(ep_ptr).view().queue.wf()) by { endpoint_perms_wf_map(krnl.ep_mp); endpoint_perms_wf_at(krnl.ep_mp, ep_ptr); };
        let endpoint_ref = krnl.ep_mp.borrow_typed(ep_ptr, Ghost(lctx.endpoint_lock_map()), Tracked(&*lctx), Tracked(&endpoint_lock_perm));
        let (_, peer_thrd_ptr) = endpoint_ref.queue.peek_head();

        proof {
            assert({
                &&& krnl.thrd_mp.dom().contains(peer_thrd_ptr)
                &&& krnl.thrd_mp.spec_index(peer_thrd_ptr).view().state.is_endpoint_waiting()
                &&& krnl.thrd_mp.spec_index(peer_thrd_ptr).view().blocking_endpoint_ptr == Some(ep_ptr)
                &&& peer_thrd_ptr != current_thrd_ptr
            }) by { endpoint_queue_member_implies_thread_waiting_on_endpoint(krnl, ep_ptr, peer_thrd_ptr); };
        }
        proof {
            assert({
                &&& steps.snapshot_k().ep_mp.spec_index(ep_ptr).view().queue.view()[0] == peer_thrd_ptr
                &&& steps.snapshot_k().thrd_mp.spec_index(peer_thrd_ptr).being_killed() == krnl.thrd_mp.spec_index(peer_thrd_ptr).being_killed()
            }) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged); reveal(kernel_endpoint_nonlock_fields_unchanged); };
        }
        let peer_thread_res = krnl.wlock_endpoint_waiting_peer_unless_killed(peer_thrd_ptr, Tracked(&mut *lctx));

        if peer_thread_res.is_none() {
            krnl.wunlock_endpoint(ep_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm));

            proof {
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
            }
            release_cpu_and_thread_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, current_thrd_ptr, Tracked(current_thread_lock_perm), Tracked(cpu_lock_perm));
            proof {
                assert(krnl.cpu_op.view().view() =~= old(steps).snapshot_k().cpu_op.view().view());
                assert(kernel_k_to_kernel_u(old(steps).snapshot_k()) == kernel_k_to_kernel_u(*krnl)) by { kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&old(steps).snapshot_k(), &*krnl); };
                ipc_rendezvous_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, ep_idx, waiting_state, payload, RetValueType::ErrorIpcPeerKilled);
            }
            return RetValueType::ErrorIpcPeerKilled;
        }
        let Tracked(peer_thread_lock_perm) = peer_thread_res.unwrap();
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        }
        ipc_rendezvous_locked_peer(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, current_thrd_ptr, ep_ptr, ep_idx, waiting_state, payload,
            waiting_is_send, Tracked(cpu_lock_perm), Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm), peer_thrd_ptr, Tracked(peer_thread_lock_perm))
    }
} // verus!
