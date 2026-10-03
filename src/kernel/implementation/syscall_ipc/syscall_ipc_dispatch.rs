use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_transition::{ipc_block_current, ipc_schedule_waiting_peer_and_finish};
use super::syscall_ipc_endpoint::ipc_rendezvous_endpoint;
use super::syscall_ipc_pages::ipc_rendezvous_pages;
use super::syscall_ipc_cpu::ipc_rendezvous_cpu;
use super::syscall_ipc_spec::*;
use super::syscall_ipc_trace::*;

verus! {
    pub(super) proof fn running_thread_not_in_endpoint_queue(krnl: &KernelK, endpoint_ptr: RwLockEndpointPtr, thread_ptr: RwLockThreadPtr)
        requires
            krnl.inv(),
            krnl.ep_mp.dom().contains(endpoint_ptr),
            krnl.thr_mp.dom().contains(thread_ptr),
            krnl.thr_mp.spec_index(thread_ptr).view().state is RUNNING,
        ensures
            !krnl.ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(thread_ptr),
    {
        reveal(thread_endpoint_queue_wf);
    }

    proof fn endpoint_queue_member_thread_facts(krnl: &KernelK, endpoint_ptr: RwLockEndpointPtr, thread_ptr: RwLockThreadPtr)
        requires
            krnl.inv(),
            krnl.ep_mp.dom().contains(endpoint_ptr),
            krnl.ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(thread_ptr),
        ensures
            krnl.thr_mp.dom().contains(thread_ptr),
            krnl.thr_mp.spec_index(thread_ptr).view().state.is_endpoint_waiting(),
            krnl.thr_mp.spec_index(thread_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
    {
        reveal(thread_endpoint_queue_wf);
        thread_perms_wf_at(krnl.thr_mp, thread_ptr);
    }

    pub(super) struct IpcEntryLocked {
        pub process_ptr: RwLockProcessPtr, pub current_thread_ptr: RwLockThreadPtr, pub endpoint_ptr: RwLockEndpointPtr, pub queue_len: usize, pub queue_is_send: bool,
        pub cpu_lock_perm: Tracked<LockPerm>, pub process_lock_perm: Tracked<LockPerm>, pub current_thread_lock_perm: Tracked<LockPerm>, pub endpoint_lock_perm: Tracked<LockPerm>,
    }

    /// Locks the cpu, its process, its thread, and the endpoint at `endpoint_index`, rejecting a killed process or
    /// thread, a missing descriptor, and a non-blocking call with no opposite waiter; otherwise the four locks are
    /// returned held with the queue length and direction, and the entry result is pinned to the state at entry.
    #[verifier::spinoff_prover]
    pub(super) fn ipc_lock_entry(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, blocking: bool, pt_regs: &Registers,
    ) -> (ret: Result<IpcEntryLocked, RetValueType>)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            edp_idx_valid(endpoint_index),
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
                IPCPayLoad::Endpoint { endpoint_index } =>
                    edp_idx_valid(endpoint_index),
                _ => false,
            },
            old(krnl).inv(),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).no_locks_held(),
            old(steps).nonlock_view().len() == 0,
            old(steps).snapshot_k() == *old(krnl),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
            old(krnl).irt.owners() == old(steps).snapshot_k().irt.owners(),
            old(krnl).irt.iommu_roots() == old(steps).snapshot_k().irt.iommu_roots(),
            old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(krnl).inv(),
            old(steps).view().len() <= final(steps).view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            ret is Err ==> ({
                let r = ret->Err_0;
                let current_thread_ptr = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread.unwrap();
                let endpoint_option = old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view().spec_index(endpoint_index as int);
                let endpoint_ptr = endpoint_option.unwrap();
                &&& r is ErrorProcessKilled || r is ErrorThreadKilled || r is ErrorInvalidEndpoint || r is ErrorIpcNoPeer || r is ErrorIpcSameDirection
                &&& r is ErrorIpcNoPeer || r is ErrorIpcSameDirection ==> !blocking
                &&& ipc_rejection(r) == ipc_entry_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, endpoint_index, waiting_state, blocking)
                &&& final(lctx).kernel_view_locking_state() is Release
                &&& final(lctx).no_locks_held()
                &&& final(krnl).all_objects_unlocked(final(lctx))
                &&& typed_lock_maps_aligned(final(krnl), final(lctx))
                &&& final(steps).nonlock_view().len() == 0
                &&& final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl))
                &&& final(steps).snapshot_k() == *final(krnl)
                &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running
                &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread
                    == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread
                &&& payload is Pages ==> ipc_pages_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                    kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, endpoint_index, waiting_state, payload->Pages_va_range,
                    *pt_regs, ipc_block_flushes_default_pcid(*old(krnl), cpu_id), r)
                &&& payload is Endpoint ==> ipc_endpoint_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                    kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, endpoint_index, waiting_state, payload->Endpoint_endpoint_index,
                    *pt_regs, ipc_block_flushes_default_pcid(*old(krnl), cpu_id), r)
                &&& (payload is Empty || payload is Cpu || payload is ReceiveCpu) ==> ipc_ordinary_syscall_trace(
                    final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                    kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, endpoint_index, waiting_state, payload, *pt_regs,
                    ipc_block_flushes_default_pcid(*old(krnl), cpu_id), r)
                &&& r is ErrorIpcNoPeer || r is ErrorIpcSameDirection ==> {
                    &&& endpoint_option is Some
                    &&& old(krnl).ep_mp.dom().contains(endpoint_ptr)
                    &&& final(krnl).ep_mp.dom().contains(endpoint_ptr)
                    &&& final(krnl).ep_mp.spec_index(endpoint_ptr).view().queue == old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue
                    &&& if r is ErrorIpcNoPeer {
                        old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.len() == 0
                    } else {
                        &&& old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.len() > 0
                        &&& old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue_state == if waiting_state is SENDING { EndpointState::SEND } else { EndpointState::RECEIVE }
                    }
                }
            }),
            ret is Ok ==> ({
                let e = ret->Ok_0;
                let cpu = final(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
                let thread = final(krnl).thr_mp.spec_index(e.current_thread_ptr).view();
                let endpoint = final(krnl).ep_mp.spec_index(e.endpoint_ptr).view();
                &&& *final(steps) == *old(steps)
                &&& final(lctx).kernel_view_locking_state() is Acquire
                &&& *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, prc_mp: final(krnl).prc_mp, thr_mp: final(krnl).thr_mp, ep_mp: final(krnl).ep_mp, ..*old(krnl) })
                &&& final(krnl).cpu_arr.unchanged_except(&old(krnl).cpu_arr, cpu_id)
                &&& final(krnl).prc_mp.unchanged_except(&old(krnl).prc_mp, e.process_ptr)
                &&& final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, e.current_thread_ptr)
                &&& final(krnl).ep_mp.unchanged_except(&old(krnl).ep_mp, e.endpoint_ptr)
                &&& old(krnl).cpu_arr.spec_index(cpu_id).value.locking_thread() is None
                &&& old(krnl).prc_mp.spec_index(e.process_ptr).locking_thread() is None
                &&& old(krnl).thr_mp.spec_index(e.current_thread_ptr).locking_thread() is None
                &&& old(krnl).ep_mp.spec_index(e.endpoint_ptr).locking_thread() is None
                &&& kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl))
                &&& kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp)
                &&& kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl))
                &&& forall|p: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(p)] #![trigger old(krnl).ctn_mp.spec_index(p)]
                    old(krnl).ctn_mp.dom().contains(p) && final(krnl).ctn_mp.dom().contains(p) ==> if final(lctx).container_lock_map().dom().contains(p) {
                        old(krnl).ctn_mp.spec_index(p).locking_thread() is None
                    } else { final(krnl).ctn_mp.spec_index(p).locking_thread() == old(krnl).ctn_mp.spec_index(p).locking_thread() }
                &&& forall|p: RwLockProcessPtr| #![trigger final(krnl).prc_mp.spec_index(p)] #![trigger old(krnl).prc_mp.spec_index(p)]
                    old(krnl).prc_mp.dom().contains(p) && final(krnl).prc_mp.dom().contains(p) ==> if final(lctx).process_lock_map().dom().contains(p) {
                        old(krnl).prc_mp.spec_index(p).locking_thread() is None
                    } else { final(krnl).prc_mp.spec_index(p).locking_thread() == old(krnl).prc_mp.spec_index(p).locking_thread() }
                &&& forall|p: RwLockThreadPtr| #![trigger final(krnl).thr_mp.spec_index(p)] #![trigger old(krnl).thr_mp.spec_index(p)]
                    old(krnl).thr_mp.dom().contains(p) && final(krnl).thr_mp.dom().contains(p) ==> if final(lctx).thread_lock_map().dom().contains(p) {
                        old(krnl).thr_mp.spec_index(p).locking_thread() is None
                    } else { final(krnl).thr_mp.spec_index(p).locking_thread() == old(krnl).thr_mp.spec_index(p).locking_thread() }
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
                &&& e.cpu_lock_perm@.state() is WriteLock && e.cpu_lock_perm@.thread_id() == final(lctx).thread_id()
                &&& e.cpu_lock_perm@.lock_id() == final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id
                &&& typed_lock_map_contains_mode(final(lctx).process_lock_map(), e.process_ptr, TypedLockMode::Write)
                &&& e.process_lock_perm@.state() is WriteLock && e.process_lock_perm@.thread_id() == final(lctx).thread_id()
                &&& e.process_lock_perm@.lock_id() == final(krnl).prc_mp.spec_index(e.process_ptr).locking_thread()->Write_lock_id
                &&& typed_lock_map_contains_mode(final(lctx).thread_lock_map(), e.current_thread_ptr, TypedLockMode::Write)
                &&& e.current_thread_lock_perm@.state() is WriteLock && e.current_thread_lock_perm@.thread_id() == final(lctx).thread_id()
                &&& e.current_thread_lock_perm@.lock_id() == final(krnl).thr_mp.spec_index(e.current_thread_ptr).locking_thread()->Write_lock_id
                &&& typed_lock_map_contains_mode(final(lctx).endpoint_lock_map(), e.endpoint_ptr, TypedLockMode::Write)
                &&& e.endpoint_lock_perm@.state() is WriteLock && e.endpoint_lock_perm@.thread_id() == final(lctx).thread_id()
                &&& e.endpoint_lock_perm@.lock_id() == final(krnl).ep_mp.spec_index(e.endpoint_ptr).locking_thread()->Write_lock_id
                &&& final(krnl).prc_mp.dom().contains(e.process_ptr) && !final(krnl).prc_mp.spec_index(e.process_ptr).being_killed()
                &&& final(krnl).prc_mp.spec_index(e.process_ptr).view().owned_threads.view().len() != 0
                &&& final(krnl).thr_mp.dom().contains(e.current_thread_ptr) && !final(krnl).thr_mp.spec_index(e.current_thread_ptr).being_killed()
                &&& final(krnl).ep_mp.dom().contains(e.endpoint_ptr)
                &&& cpu.state is Running && cpu.current_process == Some(e.process_ptr) && cpu.current_thread == Some(e.current_thread_ptr)
                &&& thread.state == (ThreadState::RUNNING { cpu_id }) && thread.owning_proc == e.process_ptr && thread.owning_container == cpu.owning_container
                &&& thread.endpoint_descriptors.wf() && thread.endpoint_descriptors.spec_index(endpoint_index) == Some(e.endpoint_ptr)
                &&& thread.free_quota_pending_clean() && thread.temp_alloc_clean() && thread.syscall_progress.view() is None
                &&& final(krnl).cpu_published[cpu_id as int].view() == (cpu.current_cr3, cpu.current_pcid)
                &&& !endpoint.queue.view().contains(e.current_thread_ptr)
                &&& e.queue_len == endpoint.queue.len() && e.queue_is_send == (endpoint.queue_state is SEND)
                &&& (e.queue_len == 0 || e.queue_is_send == (waiting_state is SENDING)) ==> blocking
                &&& final(lctx).page_lock_map().dom().is_empty()
                &&& final(lctx).cpu_lock_map().dom() =~= set![cpu_id]
                &&& final(lctx).container_lock_map().dom().is_empty()
                &&& final(lctx).process_lock_map().dom() =~= set![e.process_ptr]
                &&& final(lctx).thread_lock_map().dom() =~= set![e.current_thread_ptr]
                &&& final(lctx).endpoint_lock_map().dom() =~= set![e.endpoint_ptr]
                &&& final(lctx).scheduler_lock_map().dom().is_empty()
                &&& final(lctx).pcid_allocator_lock_map().dom().is_empty()
                &&& final(lctx).cpu_set_lock_map().dom().is_empty()
                &&& final(lctx).pagetable_lock_map().dom().is_empty()
                &&& final(lctx).iommu_table_lock_map().dom().is_empty()
                &&& final(lctx).allocator_quota_4k_lock_map().dom().is_empty()
                &&& final(lctx).allocator_cache_4k_lock_map().dom().is_empty()
                &&& final(lctx).allocator_global_pool_4k_lock_map().dom().is_empty()
                &&& final(lctx).allocator_quota_2m_lock_map().dom().is_empty()
                &&& final(lctx).allocator_cache_2m_lock_map().dom().is_empty()
                &&& final(lctx).allocator_global_pool_2m_lock_map().dom().is_empty()
                &&& final(lctx).allocator_quota_1g_lock_map().dom().is_empty()
                &&& final(lctx).allocator_cache_1g_lock_map().dom().is_empty()
                &&& final(lctx).allocator_global_pool_1g_lock_map().dom().is_empty()
                &&& final(lctx).pcid_needflush_lock_map().dom().is_empty()
                &&& typed_lock_maps_aligned(final(krnl), final(lctx))
                &&& ipc_entry_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, endpoint_index, waiting_state, blocking)
                    == if e.queue_len == 0 || e.queue_is_send == (waiting_state is SENDING) { Some(RetValueType::CpuIdle) }
                    else if kernel_k_to_kernel_u(*old(krnl)).thread_map[kernel_k_to_kernel_u(*old(krnl)).endpoint_map[e.endpoint_ptr].queue[0]].killed { Some(RetValueType::ErrorIpcPeerKilled) }
                    else { None }
            }),
    {
        let Tracked(cpu_lock_perm) = krnl.wlock_cpu(cpu_id, Tracked(&mut *lctx));

        let cpu_ref = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
        let process_ptr = cpu_ref.current_process().unwrap();
        let current_thread_ptr = cpu_ref.current_thread().unwrap();

        proof {
            assert(krnl.prc_mp.dom().contains(process_ptr)) by { reveal(process_cpu_wf); };
            process_perms_wf_at(krnl.prc_mp, process_ptr);
            assert({
                &&& krnl.prc_mp.dom().contains(process_ptr)
                &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == krnl.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container
            }) by { reveal(container_cpu_wf); reveal(process_cpu_wf); reveal(container_process_wf); };
        }
        let process_res = krnl.wlock_process_unless_killed(process_ptr, Ghost(cpu_id), Tracked(&mut *lctx));

        if process_res.is_none() {
            proof { assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; }; }
            proof { assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; }; }
            release_cpu_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Tracked(cpu_lock_perm));
            proof {
                assert(kernel_k_to_kernel_u(old(steps).snapshot_k()) == kernel_k_to_kernel_u(*krnl)) by {
                    kernel_restored_locks_implies_u_eq(&old(steps).snapshot_k(), &*krnl, cpu_id, None, Some(process_ptr), None, None, None);
                };
            }
            proof {
                ipc_syscall_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index,
                    waiting_state, payload, *pt_regs, ipc_block_flushes_default_pcid(*old(krnl), cpu_id), RetValueType::ErrorProcessKilled);
            }
            proof {
                assert(ipc_entry_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, endpoint_index, waiting_state, blocking) == Some(RetValueType::ErrorProcessKilled)) by {
                    reveal(ipc_entry_result); kernel_cpu_projection_at(&*old(krnl), cpu_id); kernel_process_projection_at(&*old(krnl), process_ptr);
                };
            }
            return Err(RetValueType::ErrorProcessKilled);
        }
        let Tracked(process_lock_perm) = process_res.unwrap();

        proof {
            assert(krnl.thr_mp.dom().contains(current_thread_ptr)) by { reveal(thread_cpu_wf); };
            process_perms_wf_at(krnl.prc_mp, process_ptr);
            thread_perms_wf_at(krnl.thr_mp, current_thread_ptr);
            assert({
                &&& krnl.thr_mp.dom().contains(current_thread_ptr)
                &&& krnl.thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id })
                &&& krnl.thr_mp.spec_index(current_thread_ptr).view().owning_proc == process_ptr
                &&& krnl.thr_mp.spec_index(current_thread_ptr).view().owning_container == krnl.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container
                &&& krnl.thr_mp.spec_index(current_thread_ptr).view().container_depth == krnl.prc_mp.spec_index(process_ptr).view_rodata().view().container_depth
                &&& krnl.thr_mp.spec_index(current_thread_ptr).view().process_depth == krnl.prc_mp.spec_index(process_ptr).view_rodata().view().depth
                &&& krnl.prc_mp.spec_index(process_ptr).view().owned_threads.view().len() != 0
            }) by { reveal(thread_cpu_wf); reveal(process_thread_wf); };
        }
        let current_thread_res = krnl.wlock_thread_unless_killed(current_thread_ptr, Tracked(&mut *lctx));

        if current_thread_res.is_none() {
            proof { assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; }; }
            proof { assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; }; }
            release_cpu_and_process_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, Tracked(process_lock_perm), Tracked(cpu_lock_perm));
            proof {
                assert(kernel_k_to_kernel_u(old(steps).snapshot_k()) == kernel_k_to_kernel_u(*krnl)) by {
                    kernel_restored_locks_implies_u_eq(&old(steps).snapshot_k(), &*krnl, cpu_id, None, Some(process_ptr), Some(current_thread_ptr), None, None);
                };
            }
            proof {
                ipc_syscall_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index,
                    waiting_state, payload, *pt_regs, ipc_block_flushes_default_pcid(*old(krnl), cpu_id), RetValueType::ErrorThreadKilled);
            }
            proof {
                assert(ipc_entry_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, endpoint_index, waiting_state, blocking) == Some(RetValueType::ErrorThreadKilled)) by {
                    reveal(ipc_entry_result); kernel_cpu_thread_projection_at(&*old(krnl), cpu_id, process_ptr, current_thread_ptr, None);
                };
            }
            return Err(RetValueType::ErrorThreadKilled);
        }
        let Tracked(current_thread_lock_perm) = current_thread_res.unwrap();

        let current_thread_ref = krnl.thr_mp.borrow_typed(current_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&current_thread_lock_perm));
        let endpoint_ptr = match *current_thread_ref.endpoint_descriptors.get(endpoint_index) {
            Some(endpoint_ptr) => endpoint_ptr,
            None => {
                proof {
                    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                    assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
                }
                release_cpu_and_process_and_thread_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, Tracked(current_thread_lock_perm), Tracked(process_lock_perm), Tracked(cpu_lock_perm));
                proof {
                    assert(kernel_k_to_kernel_u(old(steps).snapshot_k()) == kernel_k_to_kernel_u(*krnl)) by {
                        kernel_restored_locks_implies_u_eq(&old(steps).snapshot_k(), &*krnl, cpu_id, None, Some(process_ptr), Some(current_thread_ptr), None, None);
                    };
                }
                proof {
                    ipc_syscall_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index,
                        waiting_state, payload, *pt_regs, ipc_block_flushes_default_pcid(*old(krnl), cpu_id), RetValueType::ErrorInvalidEndpoint);
                }
                proof {
                    assert(ipc_entry_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, endpoint_index, waiting_state, blocking) == Some(RetValueType::ErrorInvalidEndpoint)) by {
                        reveal(ipc_entry_result); kernel_cpu_thread_projection_at(&*old(krnl), cpu_id, process_ptr, current_thread_ptr, None);
                    };
                }
                return Err(RetValueType::ErrorInvalidEndpoint);
            },
        };

        proof {
            assert(krnl.ep_mp.dom().contains(endpoint_ptr)) by { reveal(thread_endpoint_ref_counter_wf); };
            assert({
                &&& krnl.ep_mp.dom().contains(endpoint_ptr)
                &&& current_thread_lock_perm.ordering_lock_id().major == THREAD_LOCK_MAJOR
                &&& krnl.ep_mp.lock_id_by_key(endpoint_ptr).major == ENDPOINT_LOCK_MAJOR
                &&& !typed_lock_map_contains_mode(lctx.endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write)
            }) by { thread_perms_wf_at(krnl.thr_mp, current_thread_ptr); endpoint_perms_wf_at(krnl.ep_mp, endpoint_ptr); };
        }
        let Tracked(endpoint_lock_perm) = krnl.wlock_endpoint(endpoint_ptr, Tracked(&mut *lctx));
        proof {
            assert({
                &&& krnl.ep_mp.perms_wf()
                &&& krnl.thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id })
            }) by { endpoint_perms_wf_at(krnl.ep_mp, endpoint_ptr); };
        }
        let endpoint_ref = krnl.ep_mp.borrow_typed(endpoint_ptr, Ghost(lctx.endpoint_lock_map()), Tracked(&*lctx), Tracked(&endpoint_lock_perm));
        let queue_len = endpoint_ref.queue.len();
        let queue_is_send = endpoint_ref.queue_state.is_send();
        let waiting_is_send = match waiting_state {
            ThreadState::SENDING => true,
            _ => false,
        };
        proof {
            running_thread_not_in_endpoint_queue(krnl, endpoint_ptr, current_thread_ptr);
            assert({
                let pre = kernel_k_to_kernel_u(*old(krnl));
                &&& pre.endpoint_map[endpoint_ptr].queue.len() == queue_len
                &&& (pre.endpoint_map[endpoint_ptr].queue_state is SEND) == queue_is_send
            }) by {
                reveal(kernel_endpoint_nonlock_fields_unchanged); reveal(endpoint_perms_wf); reveal(LinkedList::wf_value_list);
                endpoint_perms_wf_at(krnl.ep_mp, endpoint_ptr); kernel_endpoint_projection_at(&*old(krnl), endpoint_ptr);
            };
        }

        if (queue_len == 0 || queue_is_send == waiting_is_send) && !blocking {
            let result = if queue_len == 0 { RetValueType::ErrorIpcNoPeer } else { RetValueType::ErrorIpcSameDirection };
            krnl.wunlock_endpoint(endpoint_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm));

            proof {
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
            }
            release_cpu_and_process_and_thread_and_finish_syscall(
                krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr,
                Tracked(current_thread_lock_perm), Tracked(process_lock_perm), Tracked(cpu_lock_perm),
            );
            proof {
                assert(kernel_k_to_kernel_u(old(steps).snapshot_k()) == kernel_k_to_kernel_u(*krnl)) by {
                    kernel_restored_locks_implies_u_eq(&old(steps).snapshot_k(), &*krnl, cpu_id, None, Some(process_ptr), Some(current_thread_ptr), Some(endpoint_ptr), None);
                };
            }
            proof {
                ipc_syscall_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index,
                    waiting_state, payload, *pt_regs, ipc_block_flushes_default_pcid(*old(krnl), cpu_id), result);
            }
            proof {
                assert(ipc_entry_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, endpoint_index, waiting_state, blocking) == Some(result)) by {
                    reveal(ipc_entry_result); kernel_cpu_thread_projection_at(&*old(krnl), cpu_id, process_ptr, current_thread_ptr, Some(endpoint_ptr));
                };
            }
            return Err(result);
        }
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
            assert(ipc_entry_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, endpoint_index, waiting_state, blocking)
                == if queue_len == 0 || queue_is_send == waiting_is_send { Some(RetValueType::CpuIdle) }
                else if kernel_k_to_kernel_u(*old(krnl)).thread_map[kernel_k_to_kernel_u(*old(krnl)).endpoint_map[endpoint_ptr].queue[0]].killed { Some(RetValueType::ErrorIpcPeerKilled) }
                else { None })
                by { reveal(ipc_entry_result); kernel_cpu_thread_projection_at(&*old(krnl), cpu_id, process_ptr, current_thread_ptr, Some(endpoint_ptr)); };
        }
        Ok(IpcEntryLocked {
            process_ptr, current_thread_ptr, endpoint_ptr, queue_len, queue_is_send,
            cpu_lock_perm: Tracked(cpu_lock_perm), process_lock_perm: Tracked(process_lock_perm), current_thread_lock_perm: Tracked(current_thread_lock_perm),
            endpoint_lock_perm: Tracked(endpoint_lock_perm),
        })
    }

    #[verifier::spinoff_prover]
    pub(super) fn syscall_ipc_ordinary(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, blocking: bool, pt_regs: &mut Registers,
    ) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            edp_idx_valid(endpoint_index),
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
                IPCPayLoad::Endpoint { endpoint_index } =>
                    edp_idx_valid(endpoint_index),
                _ => false,
            },
            old(krnl).inv(),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).no_locks_held(),
            old(steps).nonlock_view().len() == 0,
            old(steps).snapshot_k() == *old(krnl),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
            old(krnl).irt.owners() == old(steps).snapshot_k().irt.owners(),
            old(krnl).irt.iommu_roots() == old(steps).snapshot_k().irt.iommu_roots(),
            old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            old(steps).view().len() <= final(steps).view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            payload is Pages ==> ipc_pages_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, endpoint_index,
                waiting_state, payload->Pages_va_range, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id), ret),
            payload is Endpoint ==> ipc_endpoint_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, endpoint_index,
                waiting_state, payload->Endpoint_endpoint_index, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id), ret),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            final(steps).snapshot_k() == *final(krnl),
            (payload is Empty || payload is Cpu || payload is ReceiveCpu) ==> ipc_ordinary_syscall_trace(
                final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()),
                kernel_k_to_kernel_u(*final(krnl)), cpu_id, endpoint_index, waiting_state, payload, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id), ret),
            final(krnl).all_objects_unlocked(final(lctx)),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            !blocking ==> final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            !blocking ==> final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread,
            !blocking ==> !(ret is CpuIdle),
            ret is ErrorIpcNoPeer || ret is ErrorIpcSameDirection ==> !blocking,
            ret is ErrorIpcNoPeer || ret is ErrorIpcSameDirection ==> {
                let current_thread_ptr = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread.unwrap();
                let endpoint_option = old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view().spec_index(endpoint_index as int);
                let endpoint_ptr = endpoint_option.unwrap();
                &&& endpoint_option is Some
                &&& old(krnl).ep_mp.dom().contains(endpoint_ptr)
                &&& final(krnl).ep_mp.dom().contains(endpoint_ptr)
                &&& final(krnl).ep_mp.spec_index(endpoint_ptr).view().queue == old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue
                &&& if ret is ErrorIpcNoPeer {
                    old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.len() == 0
                } else {
                    &&& old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.len() > 0
                    &&& old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue_state == if waiting_state is SENDING { EndpointState::SEND } else { EndpointState::RECEIVE }
                }
            },
            payload is Cpu && ret is Success ==> final(krnl).cpu_arr.spec_index(payload->Cpu_cpu_id).view().view().view().state is Off && final(krnl).cpu_arr.spec_index(payload->Cpu_cpu_id).view().view().view().owning_container != old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
            ret is SuccessUsize ==> final(krnl).cpu_arr.spec_index(ret->SuccessUsize_value).view().view().view().state is Off && final(krnl).cpu_arr.spec_index(ret->SuccessUsize_value).view().view().view().owning_container == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
            ret is CpuIdle ==> final(steps).nonlock_view().len() == 1,
            ret is CpuIdle ==> {
                &&& final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(*old(krnl)), new_u: kernel_k_to_kernel_u(*final(krnl)) })
                &&& ipc_block_step_pre(kernel_k_to_kernel_u(*old(krnl)), cpu_id, endpoint_index, waiting_state)
                &&& ipc_block_step(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, endpoint_index,
                    waiting_state, payload, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id))
            },
            ret is Success ==> match payload {
                IPCPayLoad::Pages { va_range } => va_range.len + 5 <= final(steps).nonlock_view().len() <= 4 * va_range.len + 5,
                IPCPayLoad::Endpoint { .. } => final(steps).nonlock_view().len() == 2,
                _ => final(steps).nonlock_view().len() == 1,
            },
            ret is SuccessUsize ==> payload is ReceiveCpu && index_valid(NUM_CPUS, ret->SuccessUsize_value) && final(steps).nonlock_view().len() == 1,
            !(payload is Pages) && !(ret is CpuIdle) && !(ret is Success) && !(ret is SuccessUsize) ==> final(steps).nonlock_view().len() <= 2,
            payload is Empty || payload is Cpu || payload is ReceiveCpu ==> final(steps).nonlock_view().len() <= 1,
            ret is CpuIdle ==> {
                let step = final(steps).nonlock_view()[0];
                &&& final(steps).nonlock_view().len() == 1
                &&& step.old_u == kernel_k_to_nonlock_kernel_u(old(steps).snapshot_k())
                &&& step.new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
                &&& ipc_block_step_pre(step.old_u, cpu_id, endpoint_index, waiting_state)
                &&& ipc_block_step(step.old_u, step.new_u, cpu_id, endpoint_index, waiting_state, payload, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id))
            },
            (payload is Empty || payload is Cpu || payload is ReceiveCpu) && ipc_rendezvous_ret(ret) ==> {
                let step = final(steps).nonlock_view()[0];
                &&& final(steps).nonlock_view().len() == 1
                &&& step.old_u == kernel_k_to_nonlock_kernel_u(old(steps).snapshot_k())
                &&& step.new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
                &&& ret == ipc_rendezvous_result(step.old_u, cpu_id, endpoint_index, waiting_state, payload)
                &&& ipc_rendezvous_step_pre(step.old_u, cpu_id, endpoint_index, waiting_state, payload)
                &&& ipc_rendezvous_step(step.old_u, step.new_u, cpu_id, endpoint_index, waiting_state, payload)
            },
            payload is Pages && !(ret is Success) ==> final(steps).nonlock_view().len() <= 4,
            payload is Empty ==> (ret is Success || ret is CpuIdle || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch || ret is ErrorIpcNoPeer || ret is ErrorIpcSameDirection),
            payload is Pages ==> (ret is Success || ret is CpuIdle || ret is Error || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch || ret is ErrorIpcSameProcess || ret is ErrorIpcSourceUnmapped || ret is ErrorIpcPageOwnerMismatch || ret is ErrorNoQuota || ret is ErrorVaInUse),
            payload is Cpu || payload is ReceiveCpu ==> (ret is Success || ret is SuccessUsize || ret is CpuIdle || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch || ret is ErrorIpcSameContainer || ret is ErrorIpcCpuOwnerMismatch || ret is ErrorIpcCpuNotOff),
            payload is ReceiveCpu ==> !(ret is Success),
            payload is Endpoint ==> (ret is Success || ret is CpuIdle || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch || ret is ErrorIpcEndpointSourceInvalid || ret is ErrorIpcEndpointTargetInUse || ret is ErrorIpcEndpointOwnerMismatch),
            ipc_rejection(ret) == ipc_entry_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, endpoint_index, waiting_state, blocking),
    {
        let entry = match ipc_lock_entry(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, endpoint_index, waiting_state, payload, blocking, &*pt_regs) {
            Ok(entry) => entry,
            Err(ret) => return ret,
        };
        let IpcEntryLocked { process_ptr, current_thread_ptr, endpoint_ptr, queue_len, queue_is_send, cpu_lock_perm, process_lock_perm, current_thread_lock_perm, endpoint_lock_perm } = entry;
        let waiting_is_send = match waiting_state {
            ThreadState::SENDING => true,
            _ => false,
        };
        if queue_len == 0 || queue_is_send == waiting_is_send {
            let ret = ipc_block_current(
                krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, &*pt_regs,
                cpu_lock_perm, process_lock_perm, current_thread_lock_perm, endpoint_lock_perm,
            );
            proof {
                ipc_syscall_trace_from_block(&*steps, old(steps).view(), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, endpoint_index, waiting_state,
                    payload, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id));
            }
            return ret;
        }
        let ret = ipc_rendezvous_from_queue(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr,
            current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, waiting_is_send,
            cpu_lock_perm, process_lock_perm, current_thread_lock_perm, endpoint_lock_perm);
        proof {
            ipc_syscall_trace_from_rendezvous(&*steps, old(steps).view(), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, endpoint_index, waiting_state,
                payload, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id), ret);
        }
        ret
    }

    #[verifier::spinoff_prover]
    fn ipc_rendezvous_from_queue(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
        process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx,
        waiting_state: ThreadState, payload: IPCPayLoad, waiting_is_send: bool, Tracked(cpu_lock_perm): Tracked<LockPerm>,
        Tracked(process_lock_perm): Tracked<LockPerm>, Tracked(current_thread_lock_perm): Tracked<LockPerm>,
        Tracked(endpoint_lock_perm): Tracked<LockPerm>,
    ) -> (ret: RetValueType)
        requires
            old(krnl).inv(),
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
            edp_idx_valid(endpoint_index),
            old(lctx).kernel_view_locking_state() is Acquire,
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
            old(krnl).irt.owners() == old(steps).snapshot_k().irt.owners(),
            old(krnl).irt.iommu_roots() == old(steps).snapshot_k().irt.iommu_roots(),
            old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            old(krnl).cpu_set_mp == old(steps).snapshot_k().cpu_set_mp,
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            cpu_lock_perm.state() is WriteLock,
            cpu_lock_perm.thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(krnl).prc_mp.dom().contains(process_ptr),
            typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
            old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
            old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().len() != 0,
            process_lock_perm.state() is WriteLock,
            process_lock_perm.thread_id() == old(lctx).thread_id(),
            process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
            old(krnl).thr_mp.dom().contains(current_thread_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
            old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == false,
            current_thread_lock_perm.state() is WriteLock,
            current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
            current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
            old(krnl).ep_mp.dom().contains(endpoint_ptr),
            typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
            endpoint_lock_perm.state() is WriteLock,
            endpoint_lock_perm.thread_id() == old(lctx).thread_id(),
            endpoint_lock_perm.lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == process_ptr,
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
            old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.wf(),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
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
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(steps).nonlock_view().len() == 0,
            waiting_state is SENDING || waiting_state is RECEIVING,
            waiting_is_send == (waiting_state is SENDING),
            old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.len() > 0,
            (old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue_state is SEND) != waiting_is_send,
            match payload {
                IPCPayLoad::Empty => true,
                IPCPayLoad::Cpu { cpu_id } => index_valid(NUM_CPUS, cpu_id) && waiting_state is SENDING,
                IPCPayLoad::ReceiveCpu => waiting_state is RECEIVING,
                IPCPayLoad::Pages { va_range } => va_range.wf() && va_range.len > 0,
                IPCPayLoad::Endpoint { endpoint_index } => edp_idx_valid(endpoint_index),
                _ => false,
            },
        ensures
            old(steps).view().len() <= final(steps).view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            payload is Pages ==> ipc_pages_rendezvous_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, endpoint_index,
                waiting_state, payload->Pages_va_range, ret),
            payload is Endpoint ==> ipc_endpoint_rendezvous_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, endpoint_index,
                waiting_state, payload->Endpoint_endpoint_index, ret),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(steps).snapshot_k() == *final(krnl),
            (payload is Empty || payload is Cpu || payload is ReceiveCpu) ==> {
                &&& if ipc_rendezvous_ret(ret) {
                    &&& final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(old(steps).snapshot_k()), new_u: kernel_k_to_kernel_u(*final(krnl)) })
                    &&& ret == ipc_rendezvous_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index, waiting_state, payload)
                    &&& ipc_rendezvous_step_pre(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index, waiting_state, payload)
                    &&& ipc_rendezvous_step(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, endpoint_index, waiting_state, payload)
                } else {
                    &&& final(steps).view() == old(steps).view()
                    &&& kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(old(steps).snapshot_k())
                }
            },
            final(krnl).all_objects_unlocked(final(lctx)),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            payload is Empty ==> final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            payload is Empty ==> final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
            payload is Cpu && ret is Success ==> final(krnl).cpu_arr.spec_index(payload->Cpu_cpu_id).view().view().view().state is Off && final(krnl).cpu_arr.spec_index(payload->Cpu_cpu_id).view().view().view().owning_container != old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
            ret is SuccessUsize ==> final(krnl).cpu_arr.spec_index(ret->SuccessUsize_value).view().view().view().state is Off && final(krnl).cpu_arr.spec_index(ret->SuccessUsize_value).view().view().view().owning_container == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
            ret is Success ==> match payload {
                IPCPayLoad::Pages { va_range } => va_range.len + 5 <= final(steps).nonlock_view().len() <= 4 * va_range.len + 5,
                IPCPayLoad::Endpoint { .. } => final(steps).nonlock_view().len() == 2,
                _ => final(steps).nonlock_view().len() == 1,
            },
            ret is SuccessUsize ==> payload is ReceiveCpu && index_valid(NUM_CPUS, ret->SuccessUsize_value) && final(steps).nonlock_view().len() == 1,
            !(payload is Pages) && !(ret is Success) && !(ret is SuccessUsize) ==> final(steps).nonlock_view().len() <= 2,
            payload is Empty || payload is Cpu || payload is ReceiveCpu ==> final(steps).nonlock_view().len() <= 1,
            (payload is Empty || payload is Cpu || payload is ReceiveCpu) && ipc_rendezvous_ret(ret) ==> {
                let step = final(steps).nonlock_view()[0];
                &&& final(steps).nonlock_view().len() == 1
                &&& step.old_u == kernel_k_to_nonlock_kernel_u(old(steps).snapshot_k())
                &&& step.new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
                &&& ret == ipc_rendezvous_result(step.old_u, cpu_id, endpoint_index, waiting_state, payload)
                &&& ipc_rendezvous_step_pre(step.old_u, cpu_id, endpoint_index, waiting_state, payload)
                &&& ipc_rendezvous_step(step.old_u, step.new_u, cpu_id, endpoint_index, waiting_state, payload)
            },
            payload is Pages && !(ret is Success) ==> final(steps).nonlock_view().len() <= 4,
            payload is Empty ==> (ret is Success || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch),
            payload is Pages ==> (ret is Success || ret is Error || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch || ret is ErrorIpcSameProcess || ret is ErrorIpcSourceUnmapped || ret is ErrorIpcPageOwnerMismatch || ret is ErrorNoQuota || ret is ErrorVaInUse),
            payload is Cpu || payload is ReceiveCpu ==> (ret is Success || ret is SuccessUsize || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch || ret is ErrorIpcSameContainer || ret is ErrorIpcCpuOwnerMismatch || ret is ErrorIpcCpuNotOff),
            payload is ReceiveCpu ==> !(ret is Success),
            payload is Endpoint ==> (ret is Success || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch || ret is ErrorIpcEndpointSourceInvalid || ret is ErrorIpcEndpointTargetInUse || ret is ErrorIpcEndpointOwnerMismatch),
            ({
                let pre = kernel_k_to_kernel_u(old(steps).snapshot_k());
                ipc_rejection(ret) == if pre.thread_map[pre.endpoint_map[endpoint_ptr].queue[0]].killed { Some(RetValueType::ErrorIpcPeerKilled) } else { None }
            }),
    {
        assert(krnl.ep_mp.perms_wf() && krnl.ep_mp.spec_index(endpoint_ptr).is_init() && krnl.ep_mp.spec_index(endpoint_ptr).view().queue.wf()) by { reveal(endpoint_perms_wf); endpoint_perms_wf_at(krnl.ep_mp, endpoint_ptr); };
        let endpoint_ref = krnl.ep_mp.borrow_typed(endpoint_ptr, Ghost(lctx.endpoint_lock_map()), Tracked(&*lctx), Tracked(&endpoint_lock_perm));
        let (_, peer_thread_ptr) = endpoint_ref.queue.peek_head();

        proof {
            assert({
                &&& krnl.thr_mp.dom().contains(peer_thread_ptr)
                &&& krnl.thr_mp.spec_index(peer_thread_ptr).view().state.is_endpoint_waiting()
                &&& krnl.thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr)
                &&& peer_thread_ptr != current_thread_ptr
                &&& !typed_lock_map_contains_mode(lctx.thread_lock_map(), peer_thread_ptr, TypedLockMode::Write)
            }) by { endpoint_queue_member_thread_facts(krnl, endpoint_ptr, peer_thread_ptr); };
        }
        proof {
            assert({
                let pre = kernel_k_to_kernel_u(steps.snapshot_k());
                &&& pre.endpoint_map[endpoint_ptr].queue[0] == peer_thread_ptr
                &&& pre.thread_map[peer_thread_ptr].killed == krnl.thr_mp.spec_index(peer_thread_ptr).being_killed()
            }) by {
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged); reveal(kernel_endpoint_nonlock_fields_unchanged);
                kernel_thread_projection_at(&steps.snapshot_k(), peer_thread_ptr); kernel_endpoint_queue_projection_at(&steps.snapshot_k(), endpoint_ptr);
            };
        }
        let peer_thread_res = krnl.wlock_thread_unless_killed(peer_thread_ptr, Tracked(&mut *lctx));

        if peer_thread_res.is_none() {
            krnl.wunlock_endpoint(endpoint_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm));

            proof {
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
            }
            release_cpu_and_process_and_thread_and_finish_syscall(
                krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, Tracked(current_thread_lock_perm),
                Tracked(process_lock_perm), Tracked(cpu_lock_perm),
            );
            proof {
                assert(kernel_k_to_kernel_u(old(steps).snapshot_k()) == kernel_k_to_kernel_u(*krnl)) by {
                    broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, kernel_container_nonlock_fields_and_quotas_unchanged_transitive, group_kernel_endpoint_nonlock_fields_unchanged_transitive;
                    kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&old(steps).snapshot_k(), &*krnl);
                };
                ipc_rendezvous_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index, waiting_state, payload, RetValueType::ErrorIpcPeerKilled);
            }
            return RetValueType::ErrorIpcPeerKilled;
        }
        let Tracked(peer_thread_lock_perm) = peer_thread_res.unwrap();
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        }
        proof {
            use_type_invariant(&*steps);
            assert({
                let pre = kernel_k_to_kernel_u(steps.snapshot_k());
                &&& pre.cpu_array[cpu_id as int].current_process == Some(process_ptr)
                &&& pre.cpu_array[cpu_id as int].current_thread == Some(current_thread_ptr)
                &&& pre.thread_map[current_thread_ptr].endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
                &&& pre.endpoint_map[endpoint_ptr].queue[0] == peer_thread_ptr
                &&& pre.thread_map[peer_thread_ptr].ipc_payload == krnl.thr_mp.spec_index(peer_thread_ptr).view().ipc_payload
                &&& pre.thread_map[peer_thread_ptr].state == krnl.thr_mp.spec_index(peer_thread_ptr).view().state
            }) by {
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
                reveal(kernel_thread_nonlock_fields_unchanged); reveal(kernel_endpoint_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged);
                kernel_cpu_thread_projection_at(&steps.snapshot_k(), cpu_id, process_ptr, current_thread_ptr, None);
                kernel_cpu_thread_projection_at(&steps.snapshot_k(), cpu_id, process_ptr, peer_thread_ptr, None);
                kernel_endpoint_queue_projection_at(&steps.snapshot_k(), endpoint_ptr);
            };
        }
        let peer_thread_ref = krnl.thr_mp.borrow_typed(peer_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&peer_thread_lock_perm));
        let rendezvous_result = match (waiting_state, payload, peer_thread_ref.state, peer_thread_ref.ipc_payload) {
            (ThreadState::SENDING, IPCPayLoad::Cpu { cpu_id: transfer_cpu_id }, ThreadState::RECEIVING, IPCPayLoad::ReceiveCpu) => {
                let step_result = ipc_rendezvous_cpu(
                    krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, Ghost(endpoint_index),
                    Ghost(waiting_state), peer_thread_ptr, waiting_is_send, transfer_cpu_id, Ghost(payload), Tracked(cpu_lock_perm), Tracked(process_lock_perm),
                    Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm), Tracked(peer_thread_lock_perm),
                );
                return step_result;
            },
            (ThreadState::RECEIVING, IPCPayLoad::ReceiveCpu, ThreadState::SENDING, IPCPayLoad::Cpu { cpu_id: transfer_cpu_id }) => {
                let step_result = ipc_rendezvous_cpu(
                    krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, Ghost(endpoint_index),
                    Ghost(waiting_state), peer_thread_ptr, waiting_is_send, transfer_cpu_id, Ghost(payload), Tracked(cpu_lock_perm), Tracked(process_lock_perm),
                    Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm), Tracked(peer_thread_lock_perm),
                );
                return step_result;
            },
            (ThreadState::SENDING, IPCPayLoad::Endpoint { endpoint_index: source_endpoint_index },
                ThreadState::RECEIVING, IPCPayLoad::Endpoint { endpoint_index: target_endpoint_index }) => {
                let step_result = ipc_rendezvous_endpoint(
                    krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr,
                    current_thread_ptr, peer_thread_ptr, source_endpoint_index, target_endpoint_index, Tracked(cpu_lock_perm), Tracked(process_lock_perm),
                    Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm), Ghost(endpoint_index), Ghost(waiting_state), Tracked(peer_thread_lock_perm),
                );
                return step_result;
            },
            (ThreadState::RECEIVING, IPCPayLoad::Endpoint { endpoint_index: target_endpoint_index },
                ThreadState::SENDING, IPCPayLoad::Endpoint { endpoint_index: source_endpoint_index }) => {
                let step_result = ipc_rendezvous_endpoint(
                    krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr,
                    peer_thread_ptr, current_thread_ptr, source_endpoint_index, target_endpoint_index, Tracked(cpu_lock_perm), Tracked(process_lock_perm),
                    Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm), Ghost(endpoint_index), Ghost(waiting_state), Tracked(peer_thread_lock_perm),
                );
                return step_result;
            },
            (ThreadState::SENDING, IPCPayLoad::Pages { va_range: source_range },
                ThreadState::RECEIVING, IPCPayLoad::Pages { va_range: target_range }) if source_range.len == target_range.len => {
                let step_result = ipc_rendezvous_pages(
                    krnl, &source_range, &target_range, current_thread_ptr, peer_thread_ptr, cpu_id, process_ptr, current_thread_ptr, endpoint_ptr,
                    peer_thread_ptr, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(cpu_lock_perm), Tracked(process_lock_perm),
                    Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm), Tracked(peer_thread_lock_perm), Ghost(endpoint_index), Ghost(waiting_state),
                );
                return step_result;
            },
            (ThreadState::RECEIVING, IPCPayLoad::Pages { va_range: target_range },
                ThreadState::SENDING, IPCPayLoad::Pages { va_range: source_range }) if source_range.len == target_range.len => {
                let step_result = ipc_rendezvous_pages(
                    krnl, &source_range, &target_range, peer_thread_ptr, current_thread_ptr, cpu_id, process_ptr, current_thread_ptr, endpoint_ptr,
                    peer_thread_ptr, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(cpu_lock_perm), Tracked(process_lock_perm),
                    Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm), Tracked(peer_thread_lock_perm), Ghost(endpoint_index), Ghost(waiting_state),
                );
                return step_result;
            },
            (ThreadState::SENDING, IPCPayLoad::Empty, ThreadState::RECEIVING, IPCPayLoad::Empty) => RetValueType::Success,
            (ThreadState::RECEIVING, IPCPayLoad::Empty, ThreadState::SENDING, IPCPayLoad::Empty) => RetValueType::Success,
            _ => RetValueType::ErrorIpcTypeMismatch,
        };

        let step_result = ipc_schedule_waiting_peer_and_finish(
            krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, Ghost(Some((endpoint_index, waiting_state, payload))),
            peer_thread_ptr, rendezvous_result, Tracked(cpu_lock_perm), Tracked(process_lock_perm), Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm),
            Tracked(peer_thread_lock_perm),
        );
        proof {
            ipc_rendezvous_trace_error_step(&*steps, old(steps).view(), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, endpoint_index, waiting_state, payload, step_result);
        }
        step_result
    }
} // verus!
