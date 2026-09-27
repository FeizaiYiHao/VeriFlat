use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_dispatch::syscall_ipc_ordinary;
use super::syscall_ipc_spec::*;
verus! {
    pub fn syscall_send_empty(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    endpoint_index: EndpointIdx, pt_regs: &mut Registers,
    ) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            edp_idx_valid(endpoint_index),
            old(krnl).inv(),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).no_locks_held(),
            old(steps).nonlock_view().len() == 0,
            old(steps).snapshot_k() == *old(krnl),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            final(steps).snapshot_k() == *final(krnl),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            ret is CpuIdle || ret is Success ==> final(steps).nonlock_view().len() == 1,
            final(steps).nonlock_view().len() <= 1,
            ret is CpuIdle ==> {
                let step = final(steps).nonlock_view()[0];
                &&& step.old_u == kernel_k_to_nonlock_kernel_u(*old(krnl))
                &&& step.new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
                &&& ipc_block_step_pre(step.old_u, cpu_id, endpoint_index, ThreadState::SENDING)
                &&& ipc_block_step(
                    step.old_u, step.new_u, cpu_id, endpoint_index, ThreadState::SENDING, IPCPayLoad::Empty, *old(pt_regs),
                    ipc_block_flushes_default_pcid(*old(krnl), cpu_id),
                )
            },
            ipc_rendezvous_ret(ret) ==> {
                let step = final(steps).nonlock_view()[0];
                &&& final(steps).nonlock_view().len() == 1
                &&& step.old_u == kernel_k_to_nonlock_kernel_u(*old(krnl))
                &&& step.new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
                &&& ipc_rendezvous_step_pre(step.old_u, cpu_id, endpoint_index, ThreadState::SENDING)
                &&& ipc_rendezvous_step(
                    step.old_u, step.new_u, cpu_id, endpoint_index, ipc_peer_result(IPCPayLoad::Empty, ret),
                    ipc_cpu_transfer(step.old_u, cpu_id, endpoint_index, IPCPayLoad::Empty, ret),
                )
            },
            ret is Success || ret is CpuIdle || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch,
    {
        proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
        syscall_ipc_ordinary(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, endpoint_index, ThreadState::SENDING, IPCPayLoad::Empty, true, pt_regs)
    }

    pub fn syscall_send_empty_no_block(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    endpoint_index: EndpointIdx, pt_regs: &mut Registers,
    ) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            edp_idx_valid(endpoint_index),
            old(krnl).inv(),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).no_locks_held(),
            old(steps).nonlock_view().len() == 0,
            old(steps).snapshot_k() == *old(krnl),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            final(steps).snapshot_k() == *final(krnl),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            ret is Success ==> final(steps).nonlock_view().len() == 1,
            final(steps).nonlock_view().len() <= 1,
            final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread,
            final(krnl).thr_mp.spec_index(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread.unwrap()).view().state == (ThreadState::RUNNING { cpu_id }),
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
                    &&& old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue_state == EndpointState::SEND
                }
            },
            ipc_rendezvous_ret(ret) ==> {
                let step = final(steps).nonlock_view()[0];
                &&& final(steps).nonlock_view().len() == 1
                &&& step.old_u == kernel_k_to_nonlock_kernel_u(*old(krnl))
                &&& step.new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
                &&& ipc_rendezvous_step_pre(step.old_u, cpu_id, endpoint_index, ThreadState::SENDING)
                &&& ipc_rendezvous_step(
                    step.old_u, step.new_u, cpu_id, endpoint_index, ipc_peer_result(IPCPayLoad::Empty, ret),
                    ipc_cpu_transfer(step.old_u, cpu_id, endpoint_index, IPCPayLoad::Empty, ret),
                )
            },
            ret is Success || ret is ErrorIpcNoPeer || ret is ErrorIpcSameDirection || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch,
    {
        proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
        let ret = syscall_ipc_ordinary(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, endpoint_index, ThreadState::SENDING, IPCPayLoad::Empty, false, pt_regs);
        proof {
            assert(krnl.thr_mp.spec_index(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread.unwrap()).view().state == (ThreadState::RUNNING { cpu_id })) by { reveal(thread_cpu_wf); };
        }
        ret
    }

    pub fn syscall_receive_empty(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    endpoint_index: EndpointIdx, pt_regs: &mut Registers,
    ) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            edp_idx_valid(endpoint_index),
            old(krnl).inv(),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).no_locks_held(),
            old(steps).nonlock_view().len() == 0,
            old(steps).snapshot_k() == *old(krnl),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            final(steps).snapshot_k() == *final(krnl),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            ret is CpuIdle || ret is Success ==> final(steps).nonlock_view().len() == 1,
            final(steps).nonlock_view().len() <= 1,
            ret is CpuIdle ==> {
                let step = final(steps).nonlock_view()[0];
                &&& step.old_u == kernel_k_to_nonlock_kernel_u(*old(krnl))
                &&& step.new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
                &&& ipc_block_step_pre(step.old_u, cpu_id, endpoint_index, ThreadState::RECEIVING)
                &&& ipc_block_step(
                    step.old_u, step.new_u, cpu_id, endpoint_index, ThreadState::RECEIVING, IPCPayLoad::Empty, *old(pt_regs),
                    ipc_block_flushes_default_pcid(*old(krnl), cpu_id),
                )
            },
            ipc_rendezvous_ret(ret) ==> {
                let step = final(steps).nonlock_view()[0];
                &&& final(steps).nonlock_view().len() == 1
                &&& step.old_u == kernel_k_to_nonlock_kernel_u(*old(krnl))
                &&& step.new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
                &&& ipc_rendezvous_step_pre(step.old_u, cpu_id, endpoint_index, ThreadState::RECEIVING)
                &&& ipc_rendezvous_step(
                    step.old_u, step.new_u, cpu_id, endpoint_index, ipc_peer_result(IPCPayLoad::Empty, ret),
                    ipc_cpu_transfer(step.old_u, cpu_id, endpoint_index, IPCPayLoad::Empty, ret),
                )
            },
            ret is Success || ret is CpuIdle || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch,
    {
        proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
        syscall_ipc_ordinary(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, endpoint_index, ThreadState::RECEIVING, IPCPayLoad::Empty, true, pt_regs)
    }

    pub fn syscall_receive_empty_no_block(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    endpoint_index: EndpointIdx, pt_regs: &mut Registers,
    ) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            edp_idx_valid(endpoint_index),
            old(krnl).inv(),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).no_locks_held(),
            old(steps).nonlock_view().len() == 0,
            old(steps).snapshot_k() == *old(krnl),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            final(steps).snapshot_k() == *final(krnl),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            ret is Success ==> final(steps).nonlock_view().len() == 1,
            final(steps).nonlock_view().len() <= 1,
            final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread,
            final(krnl).thr_mp.spec_index(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread.unwrap()).view().state == (ThreadState::RUNNING { cpu_id }),
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
                    &&& old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue_state == EndpointState::RECEIVE
                }
            },
            ipc_rendezvous_ret(ret) ==> {
                let step = final(steps).nonlock_view()[0];
                &&& final(steps).nonlock_view().len() == 1
                &&& step.old_u == kernel_k_to_nonlock_kernel_u(*old(krnl))
                &&& step.new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
                &&& ipc_rendezvous_step_pre(step.old_u, cpu_id, endpoint_index, ThreadState::RECEIVING)
                &&& ipc_rendezvous_step(
                    step.old_u, step.new_u, cpu_id, endpoint_index, ipc_peer_result(IPCPayLoad::Empty, ret),
                    ipc_cpu_transfer(step.old_u, cpu_id, endpoint_index, IPCPayLoad::Empty, ret),
                )
            },
            ret is Success || ret is ErrorIpcNoPeer || ret is ErrorIpcSameDirection || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch,
    {
        proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
        let ret = syscall_ipc_ordinary(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, endpoint_index, ThreadState::RECEIVING, IPCPayLoad::Empty, false, pt_regs);
        proof {
            assert(krnl.thr_mp.spec_index(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread.unwrap()).view().state == (ThreadState::RUNNING { cpu_id })) by { reveal(thread_cpu_wf); };
        }
        ret
    }

    pub fn syscall_send_cpu(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    endpoint_index: EndpointIdx, transfer_cpu_id: CpuId, pt_regs: &mut Registers,
    ) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            edp_idx_valid(endpoint_index),
            index_valid(NUM_CPUS, transfer_cpu_id),
            old(krnl).inv(),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).no_locks_held(),
            old(steps).nonlock_view().len() == 0,
            old(steps).snapshot_k() == *old(krnl),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            final(steps).snapshot_k() == *final(krnl),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            ret is Success ==> final(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().state is Off && final(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().owning_container != old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
            ret is CpuIdle || ret is Success ==> final(steps).nonlock_view().len() == 1,
            final(steps).nonlock_view().len() <= 1,
            ret is CpuIdle ==> {
                let step = final(steps).nonlock_view()[0];
                &&& step.old_u == kernel_k_to_nonlock_kernel_u(*old(krnl))
                &&& step.new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
                &&& ipc_block_step_pre(step.old_u, cpu_id, endpoint_index, ThreadState::SENDING)
                &&& ipc_block_step(
                    step.old_u, step.new_u, cpu_id, endpoint_index, ThreadState::SENDING, IPCPayLoad::Cpu { cpu_id: transfer_cpu_id }, *old(pt_regs),
                    ipc_block_flushes_default_pcid(*old(krnl), cpu_id),
                )
            },
            ipc_rendezvous_ret(ret) ==> {
                let step = final(steps).nonlock_view()[0];
                &&& final(steps).nonlock_view().len() == 1
                &&& step.old_u == kernel_k_to_nonlock_kernel_u(*old(krnl))
                &&& step.new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
                &&& ipc_rendezvous_step_pre(step.old_u, cpu_id, endpoint_index, ThreadState::SENDING)
                &&& ipc_rendezvous_step(
                    step.old_u, step.new_u, cpu_id, endpoint_index, ipc_peer_result(IPCPayLoad::Cpu { cpu_id: transfer_cpu_id }, ret),
                    ipc_cpu_transfer(step.old_u, cpu_id, endpoint_index, IPCPayLoad::Cpu { cpu_id: transfer_cpu_id }, ret),
                )
            },
            ret is Success || ret is CpuIdle || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch || ret is ErrorIpcSameContainer || ret is ErrorIpcCpuOwnerMismatch || ret is ErrorIpcCpuNotOff,
    {
        proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
        syscall_ipc_ordinary(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, endpoint_index, ThreadState::SENDING, IPCPayLoad::Cpu { cpu_id: transfer_cpu_id }, true, pt_regs)
    }

    pub fn syscall_receive_cpu(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    endpoint_index: EndpointIdx, pt_regs: &mut Registers,
    ) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            edp_idx_valid(endpoint_index),
            old(krnl).inv(),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).no_locks_held(),
            old(steps).nonlock_view().len() == 0,
            old(steps).snapshot_k() == *old(krnl),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            ret is SuccessUsize ==> index_valid(NUM_CPUS, ret->SuccessUsize_value),
            ret is SuccessUsize ==> final(krnl).cpu_arr.spec_index(ret->SuccessUsize_value).view().view().view().state is Off && final(krnl).cpu_arr.spec_index(ret->SuccessUsize_value).view().view().view().owning_container == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            final(steps).snapshot_k() == *final(krnl),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            ret is CpuIdle || ret is SuccessUsize ==> final(steps).nonlock_view().len() == 1,
            final(steps).nonlock_view().len() <= 1,
            ret is CpuIdle ==> {
                let step = final(steps).nonlock_view()[0];
                &&& step.old_u == kernel_k_to_nonlock_kernel_u(*old(krnl))
                &&& step.new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
                &&& ipc_block_step_pre(step.old_u, cpu_id, endpoint_index, ThreadState::RECEIVING)
                &&& ipc_block_step(
                    step.old_u, step.new_u, cpu_id, endpoint_index, ThreadState::RECEIVING, IPCPayLoad::ReceiveCpu, *old(pt_regs),
                    ipc_block_flushes_default_pcid(*old(krnl), cpu_id),
                )
            },
            ipc_rendezvous_ret(ret) ==> {
                let step = final(steps).nonlock_view()[0];
                &&& final(steps).nonlock_view().len() == 1
                &&& step.old_u == kernel_k_to_nonlock_kernel_u(*old(krnl))
                &&& step.new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
                &&& ipc_rendezvous_step_pre(step.old_u, cpu_id, endpoint_index, ThreadState::RECEIVING)
                &&& ipc_rendezvous_step(
                    step.old_u, step.new_u, cpu_id, endpoint_index, ipc_peer_result(IPCPayLoad::ReceiveCpu, ret),
                    ipc_cpu_transfer(step.old_u, cpu_id, endpoint_index, IPCPayLoad::ReceiveCpu, ret),
                )
            },
            ret is SuccessUsize || ret is CpuIdle || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch || ret is ErrorIpcSameContainer || ret is ErrorIpcCpuOwnerMismatch || ret is ErrorIpcCpuNotOff,
    {
        proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
        syscall_ipc_ordinary(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, endpoint_index, ThreadState::RECEIVING, IPCPayLoad::ReceiveCpu, true, pt_regs)
    }

    pub fn syscall_send_endpoint(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    endpoint_index: EndpointIdx, source_endpoint_index: EndpointIdx, pt_regs: &mut Registers,
    ) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            edp_idx_valid(endpoint_index),
            edp_idx_valid(source_endpoint_index),
            old(krnl).inv(),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).no_locks_held(),
            old(steps).nonlock_view().len() == 0,
            old(steps).snapshot_k() == *old(krnl),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            final(steps).snapshot_k() == *final(krnl),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            ret is CpuIdle ==> final(steps).nonlock_view().len() == 1,
            ret is Success ==> final(steps).nonlock_view().len() == 2,
            final(steps).nonlock_view().len() <= 2,
            ret is Success || ret is CpuIdle || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch || ret is ErrorIpcEndpointSourceInvalid || ret is ErrorIpcEndpointTargetInUse || ret is ErrorIpcEndpointOwnerMismatch,
    {
        proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
        syscall_ipc_ordinary(
            krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, endpoint_index, ThreadState::SENDING,
            IPCPayLoad::Endpoint { endpoint_index: source_endpoint_index }, true, pt_regs,
        )
    }

    pub fn syscall_receive_endpoint(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    endpoint_index: EndpointIdx, target_endpoint_index: EndpointIdx, pt_regs: &mut Registers,
    ) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            edp_idx_valid(endpoint_index),
            edp_idx_valid(target_endpoint_index),
            old(krnl).inv(),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).no_locks_held(),
            old(steps).nonlock_view().len() == 0,
            old(steps).snapshot_k() == *old(krnl),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            final(steps).snapshot_k() == *final(krnl),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            ret is CpuIdle ==> final(steps).nonlock_view().len() == 1,
            ret is Success ==> final(steps).nonlock_view().len() == 2,
            final(steps).nonlock_view().len() <= 2,
            ret is Success || ret is CpuIdle || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch || ret is ErrorIpcEndpointSourceInvalid || ret is ErrorIpcEndpointTargetInUse || ret is ErrorIpcEndpointOwnerMismatch,
    {
        proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
        syscall_ipc_ordinary(
            krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, endpoint_index, ThreadState::RECEIVING,
            IPCPayLoad::Endpoint { endpoint_index: target_endpoint_index }, true, pt_regs,
        )
    }

    pub fn syscall_send_pages(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    endpoint_index: EndpointIdx, va: VAddr, range: usize, pt_regs: &mut Registers,
    ) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            edp_idx_valid(endpoint_index),
            old(krnl).inv(),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).no_locks_held(),
            old(steps).nonlock_view().len() == 0,
            old(steps).snapshot_k() == *old(krnl),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            final(steps).snapshot_k() == *final(krnl),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            ret is CpuIdle ==> final(steps).nonlock_view().len() == 1,
            ret is Success ==> range + 1 <= final(steps).nonlock_view().len() <= 4 * range + 1,
            !(ret is CpuIdle) && !(ret is Success) ==> final(steps).nonlock_view().len() <= 1,
            ret is Success || ret is CpuIdle || ret is Error || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch || ret is ErrorIpcSameProcess || ret is ErrorIpcSourceUnmapped || ret is ErrorIpcPageOwnerMismatch || ret is ErrorNoQuota || ret is ErrorVaInUse,
    {
        syscall_pages(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, endpoint_index, ThreadState::SENDING, va, range, pt_regs)
    }

    pub fn syscall_receive_pages(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    endpoint_index: EndpointIdx, va: VAddr, range: usize, pt_regs: &mut Registers,
    ) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            edp_idx_valid(endpoint_index),
            old(krnl).inv(),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).no_locks_held(),
            old(steps).nonlock_view().len() == 0,
            old(steps).snapshot_k() == *old(krnl),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            final(steps).snapshot_k() == *final(krnl),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            ret is CpuIdle ==> final(steps).nonlock_view().len() == 1,
            ret is Success ==> range + 1 <= final(steps).nonlock_view().len() <= 4 * range + 1,
            !(ret is CpuIdle) && !(ret is Success) ==> final(steps).nonlock_view().len() <= 1,
            ret is Success || ret is CpuIdle || ret is Error || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch || ret is ErrorIpcSameProcess || ret is ErrorIpcSourceUnmapped || ret is ErrorIpcPageOwnerMismatch || ret is ErrorNoQuota || ret is ErrorVaInUse,
    {
        syscall_pages(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, endpoint_index, ThreadState::RECEIVING, va, range, pt_regs)
    }

    fn syscall_pages(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    endpoint_index: EndpointIdx, waiting_state: ThreadState, va: VAddr, range: usize, pt_regs: &mut Registers,
    ) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            edp_idx_valid(endpoint_index),
            waiting_state is SENDING || waiting_state is RECEIVING,
            old(krnl).inv(),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).no_locks_held(),
            old(steps).nonlock_view().len() == 0,
            old(steps).snapshot_k() == *old(krnl),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            final(steps).snapshot_k() == *final(krnl),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            ret is CpuIdle ==> final(steps).nonlock_view().len() == 1,
            ret is Success ==> range + 1 <= final(steps).nonlock_view().len() <= 4 * range + 1,
            !(ret is CpuIdle) && !(ret is Success) ==> final(steps).nonlock_view().len() <= 1,
            ret is Success || ret is CpuIdle || ret is Error || ret is ErrorProcessKilled || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch || ret is ErrorIpcSameProcess || ret is ErrorIpcSourceUnmapped || ret is ErrorIpcPageOwnerMismatch || ret is ErrorNoQuota || ret is ErrorVaInUse,
    {
        proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }

        if range == 0
            || range > usize::MAX / 4096usize
            || !va_4k_valid(va)
        {
            proof {
                enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx);
            }
            return RetValueType::Error;
        }
        let span = range * 4096usize;
        if va >= usize::MAX - span || !va_4k_range_valid(va, range) {
            proof {
                enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx);
            }
            return RetValueType::Error;
        }
        let va_range = VaRange4K::new(va, range);
        proof { assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; }; }
        syscall_ipc_ordinary(
            krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, endpoint_index, waiting_state,
            IPCPayLoad::Pages { va_range }, true, pt_regs,
        )
    }
} // verus!
