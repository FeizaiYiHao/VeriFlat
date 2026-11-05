use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_dispatch::syscall_ipc_ordinary;
pub use super::syscall_ipc_call::{syscall_call, syscall_receive_call, syscall_reply_and_receive};
use super::syscall_ipc_spec::*;
use super::syscall_ipc_trace::*;
verus! {
    pub fn syscall_send_empty(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, ep_idx: EndpointIdx, pt_regs: &mut Registers) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
            edp_idx_valid(ep_idx),
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
            final(steps).snapshot_k() == *final(krnl),
            old(steps).view().len() <= final(steps).view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            ipc_ordinary_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                ThreadState::SENDING, IPCPayLoad::Empty, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id), ret),
            ret is CpuIdle && old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running && !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() ==> {
                &&& final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(*old(krnl)), new_u: kernel_k_to_kernel_u(*final(krnl)) })
                &&& ipc_block_step_pre(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, ThreadState::SENDING)
                &&& ipc_block_step(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                    ThreadState::SENDING, IPCPayLoad::Empty, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id))
            },
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            ret is Success || ret is CpuIdle || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch,
            ipc_rejection(ret) == ipc_entry_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, ThreadState::SENDING, true),
    {
        syscall_ipc_ordinary(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, ep_idx, ThreadState::SENDING, IPCPayLoad::Empty, true, pt_regs)
    }

    pub fn syscall_send_empty_no_block(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, ep_idx: EndpointIdx, pt_regs: &mut Registers) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
            edp_idx_valid(ep_idx),
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
            final(steps).snapshot_k() == *final(krnl),
            old(steps).view().len() <= final(steps).view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            ipc_ordinary_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                ThreadState::SENDING, IPCPayLoad::Empty, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id), ret),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            !(ret is CpuIdle) ==> final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            !(ret is CpuIdle) ==> final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread,
            !(ret is CpuIdle) ==> final(krnl).thrd_mp.spec_index(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread.unwrap()).view().state == (ThreadState::RUNNING { cpu_id }),
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
                    &&& old(krnl).ep_mp.spec_index(ep_ptr).view().queue_state == EndpointState::SEND
                }
            },
            ret is Success || ret is CpuIdle || ret is ErrorIpcNoPeer || ret is ErrorIpcSameDirection || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch,
            ipc_rejection(ret) == ipc_entry_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, ThreadState::SENDING, false),
    {
        let ret = syscall_ipc_ordinary(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, ep_idx, ThreadState::SENDING, IPCPayLoad::Empty, false, pt_regs);
        proof { if !(ret is CpuIdle) { assert(krnl.thrd_mp.spec_index(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread.unwrap()).view().state == (ThreadState::RUNNING { cpu_id })) by { thread_cpu_wf_cpu_at(krnl.thrd_mp, krnl.cpu_arr, cpu_id); }; } }
        ret
    }

    pub fn syscall_receive_empty(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, ep_idx: EndpointIdx, pt_regs: &mut Registers) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
            edp_idx_valid(ep_idx),
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
            final(steps).snapshot_k() == *final(krnl),
            old(steps).view().len() <= final(steps).view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            ipc_ordinary_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                ThreadState::RECEIVING, IPCPayLoad::Empty, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id), ret),
            ret is CpuIdle && old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running && !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() ==> {
                &&& final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(*old(krnl)), new_u: kernel_k_to_kernel_u(*final(krnl)) })
                &&& ipc_block_step_pre(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, ThreadState::RECEIVING)
                &&& ipc_block_step(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                    ThreadState::RECEIVING, IPCPayLoad::Empty, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id))
            },
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            ret is Success || ret is CpuIdle || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch,
            ipc_rejection(ret) == ipc_entry_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, ThreadState::RECEIVING, true),
    {
        syscall_ipc_ordinary(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, ep_idx, ThreadState::RECEIVING, IPCPayLoad::Empty, true, pt_regs)
    }

    pub fn syscall_receive_empty_no_block(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, ep_idx: EndpointIdx, pt_regs: &mut Registers) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
            edp_idx_valid(ep_idx),
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
            final(steps).snapshot_k() == *final(krnl),
            old(steps).view().len() <= final(steps).view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            ipc_ordinary_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                ThreadState::RECEIVING, IPCPayLoad::Empty, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id), ret),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            !(ret is CpuIdle) ==> final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            !(ret is CpuIdle) ==> final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread,
            !(ret is CpuIdle) ==> final(krnl).thrd_mp.spec_index(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread.unwrap()).view().state == (ThreadState::RUNNING { cpu_id }),
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
                    &&& old(krnl).ep_mp.spec_index(ep_ptr).view().queue_state == EndpointState::RECEIVE
                }
            },
            ret is Success || ret is CpuIdle || ret is ErrorIpcNoPeer || ret is ErrorIpcSameDirection || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch,
            ipc_rejection(ret) == ipc_entry_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, ThreadState::RECEIVING, false),
    {
        let ret = syscall_ipc_ordinary(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, ep_idx, ThreadState::RECEIVING, IPCPayLoad::Empty, false, pt_regs);
        proof { if !(ret is CpuIdle) { assert(krnl.thrd_mp.spec_index(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread.unwrap()).view().state == (ThreadState::RUNNING { cpu_id })) by { thread_cpu_wf_cpu_at(krnl.thrd_mp, krnl.cpu_arr, cpu_id); }; } }
        ret
    }

    pub fn syscall_send_cpu(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, ep_idx: EndpointIdx, transfer_cpu_id: CpuId, pt_regs: &mut Registers) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
            edp_idx_valid(ep_idx),
            index_valid(NUM_CPUS, transfer_cpu_id),
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
            final(steps).snapshot_k() == *final(krnl),
            old(steps).view().len() <= final(steps).view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            ipc_ordinary_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                ThreadState::SENDING, IPCPayLoad::Cpu { cpu_id: transfer_cpu_id }, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id), ret),
            ret is CpuIdle && old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running && !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() ==> {
                &&& final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(*old(krnl)), new_u: kernel_k_to_kernel_u(*final(krnl)) })
                &&& ipc_block_step_pre(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, ThreadState::SENDING)
                &&& ipc_block_step(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                    ThreadState::SENDING, IPCPayLoad::Cpu { cpu_id: transfer_cpu_id }, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id))
            },
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            ret is Success ==> final(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().state is Off && final(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().owning_container != old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
            ret is Success || ret is CpuIdle || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch || ret is ErrorIpcSameContainer || ret is ErrorIpcCpuOwnerMismatch || ret is ErrorIpcCpuNotOff,
            ipc_rejection(ret) == ipc_entry_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, ThreadState::SENDING, true),
    {
        syscall_ipc_ordinary(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, ep_idx, ThreadState::SENDING, IPCPayLoad::Cpu { cpu_id: transfer_cpu_id }, true, pt_regs)
    }

    pub fn syscall_receive_cpu(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, ep_idx: EndpointIdx, pt_regs: &mut Registers) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
            edp_idx_valid(ep_idx),
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).no_locks_held(),
            old(steps).snapshot_k() == *old(krnl),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            ret is SuccessUsize ==> index_valid(NUM_CPUS, ret->SuccessUsize_value),
            ret is SuccessUsize ==> final(krnl).cpu_arr.spec_index(ret->SuccessUsize_value).view().view().view().state is Off
                && final(krnl).cpu_arr.spec_index(ret->SuccessUsize_value).view().view().view().owning_container == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(steps).snapshot_k() == *final(krnl),
            old(steps).view().len() <= final(steps).view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            ipc_ordinary_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                ThreadState::RECEIVING, IPCPayLoad::ReceiveCpu, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id), ret),
            ret is CpuIdle && old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running && !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() ==> {
                &&& final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(*old(krnl)), new_u: kernel_k_to_kernel_u(*final(krnl)) })
                &&& ipc_block_step_pre(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, ThreadState::RECEIVING)
                &&& ipc_block_step(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                    ThreadState::RECEIVING, IPCPayLoad::ReceiveCpu, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id))
            },
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            ret is SuccessUsize || ret is CpuIdle || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch
                || ret is ErrorIpcSameContainer || ret is ErrorIpcCpuOwnerMismatch || ret is ErrorIpcCpuNotOff,
            ipc_rejection(ret) == ipc_entry_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, ThreadState::RECEIVING, true),
    {
        syscall_ipc_ordinary(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, ep_idx, ThreadState::RECEIVING, IPCPayLoad::ReceiveCpu, true, pt_regs)
    }

    /// Hands the named PCI function to a receiver that names the same B/D/F; blocks when no receiver waits.
    pub fn syscall_send_pci(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, ep_idx: EndpointIdx, bus: u8, dev: u8, fun: u8, pt_regs: &mut Registers) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
            edp_idx_valid(ep_idx),
            pci_bdf_valid(bus as usize, dev as usize, fun as usize),
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
            final(steps).snapshot_k() == *final(krnl),
            old(steps).view().len() <= final(steps).view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            ipc_ordinary_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                ThreadState::SENDING, IPCPayLoad::Pci { bus, dev, fun }, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id), ret),
            ret is CpuIdle && old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running && !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() ==> {
                &&& final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(*old(krnl)), new_u: kernel_k_to_kernel_u(*final(krnl)) })
                &&& ipc_block_step_pre(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, ThreadState::SENDING)
                &&& ipc_block_step(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                    ThreadState::SENDING, IPCPayLoad::Pci { bus, dev, fun }, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id))
            },
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            ret is Success || ret is CpuIdle || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch
                || ret is ErrorIpcSameProcess || ret is ErrorIpcPciOwnerMismatch,
            ipc_rejection(ret) == ipc_entry_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, ThreadState::SENDING, true),
    {
        syscall_ipc_ordinary(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, ep_idx, ThreadState::SENDING, IPCPayLoad::Pci { bus, dev, fun }, true, pt_regs)
    }

    /// Takes the named PCI function from a sender that names the same B/D/F; blocks when no sender waits.
    pub fn syscall_receive_pci(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, ep_idx: EndpointIdx, bus: u8, dev: u8, fun: u8, pt_regs: &mut Registers) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
            edp_idx_valid(ep_idx),
            pci_bdf_valid(bus as usize, dev as usize, fun as usize),
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
            final(steps).snapshot_k() == *final(krnl),
            old(steps).view().len() <= final(steps).view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            ipc_ordinary_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                ThreadState::RECEIVING, IPCPayLoad::Pci { bus, dev, fun }, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id), ret),
            ret is CpuIdle && old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running && !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() ==> {
                &&& final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(*old(krnl)), new_u: kernel_k_to_kernel_u(*final(krnl)) })
                &&& ipc_block_step_pre(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, ThreadState::RECEIVING)
                &&& ipc_block_step(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                    ThreadState::RECEIVING, IPCPayLoad::Pci { bus, dev, fun }, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id))
            },
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            ret is Success || ret is CpuIdle || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch
                || ret is ErrorIpcSameProcess || ret is ErrorIpcPciOwnerMismatch,
            ipc_rejection(ret) == ipc_entry_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, ThreadState::RECEIVING, true),
    {
        syscall_ipc_ordinary(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, ep_idx, ThreadState::RECEIVING, IPCPayLoad::Pci { bus, dev, fun }, true, pt_regs)
    }

    pub fn syscall_send_endpoint(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, ep_idx: EndpointIdx, source_ep_idx: EndpointIdx, pt_regs: &mut Registers) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
            edp_idx_valid(ep_idx),
            edp_idx_valid(source_ep_idx),
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).no_locks_held(),
            old(steps).snapshot_k() == *old(krnl),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            old(steps).view().len() <= final(steps).view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            ipc_endpoint_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                ThreadState::SENDING, source_ep_idx, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id), ret),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(steps).snapshot_k() == *final(krnl),
            ret is CpuIdle && old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running && !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() ==> {
                &&& final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(*old(krnl)), new_u: kernel_k_to_kernel_u(*final(krnl)) })
                &&& ipc_block_step_pre(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, ThreadState::SENDING)
                &&& ipc_block_step(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                    ThreadState::SENDING, IPCPayLoad::Endpoint { endpoint_index: source_ep_idx }, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id))
            },
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            ret is Success || ret is CpuIdle || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch
                || ret is ErrorIpcEndpointSourceInvalid || ret is ErrorIpcEndpointTargetInUse || ret is ErrorIpcEndpointOwnerMismatch,
            ipc_rejection(ret) == ipc_entry_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, ThreadState::SENDING, true),
    {
        syscall_ipc_ordinary(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, ep_idx, ThreadState::SENDING, IPCPayLoad::Endpoint { endpoint_index: source_ep_idx }, true, pt_regs)
    }

    pub fn syscall_receive_endpoint(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, ep_idx: EndpointIdx, target_ep_idx: EndpointIdx, pt_regs: &mut Registers) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
            edp_idx_valid(ep_idx),
            edp_idx_valid(target_ep_idx),
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).no_locks_held(),
            old(steps).snapshot_k() == *old(krnl),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            old(steps).view().len() <= final(steps).view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            ipc_endpoint_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                ThreadState::RECEIVING, target_ep_idx, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id), ret),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(steps).snapshot_k() == *final(krnl),
            ret is CpuIdle && old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running && !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() ==> {
                &&& final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(*old(krnl)), new_u: kernel_k_to_kernel_u(*final(krnl)) })
                &&& ipc_block_step_pre(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, ThreadState::RECEIVING)
                &&& ipc_block_step(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                    ThreadState::RECEIVING, IPCPayLoad::Endpoint { endpoint_index: target_ep_idx }, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id))
            },
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            ret is Success || ret is CpuIdle || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled || ret is ErrorIpcTypeMismatch
                || ret is ErrorIpcEndpointSourceInvalid || ret is ErrorIpcEndpointTargetInUse || ret is ErrorIpcEndpointOwnerMismatch,
            ipc_rejection(ret) == ipc_entry_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, ThreadState::RECEIVING, true),
    {
        syscall_ipc_ordinary(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, ep_idx, ThreadState::RECEIVING, IPCPayLoad::Endpoint { endpoint_index: target_ep_idx }, true, pt_regs)
    }

    pub fn syscall_send_pages(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, ep_idx: EndpointIdx, va: VAddr, range: usize, pt_regs: &mut Registers) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
            edp_idx_valid(ep_idx),
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).no_locks_held(),
            old(steps).snapshot_k() == *old(krnl),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            old(steps).view().len() <= final(steps).view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            ipc_pages_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                ThreadState::SENDING, VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) },
                *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id), ret),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(steps).snapshot_k() == *final(krnl),
            ret is CpuIdle && old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running && !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() ==> {
                &&& final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(*old(krnl)), new_u: kernel_k_to_kernel_u(*final(krnl)) })
                &&& ipc_block_step_pre(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, ThreadState::SENDING)
                &&& ipc_block_step(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                    ThreadState::SENDING, IPCPayLoad::Pages { va_range: VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) } }, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id))
            },
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            ret is Success || ret is CpuIdle || ret is Error || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled
                || ret is ErrorIpcTypeMismatch || ret is ErrorIpcSameProcess || ret is ErrorIpcSourceUnmapped || ret is ErrorIpcPageOwnerMismatch || ret is ErrorNoQuota || ret is ErrorVaInUse || ret is ErrorIpcRangeNotUser,
            ipc_pages_args_invalid(va, range) ==> ret is Error,
            !ipc_pages_args_invalid(va, range) ==> ipc_rejection(ret) == ipc_entry_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, ThreadState::SENDING, true),
    { syscall_pages(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, ep_idx, ThreadState::SENDING, va, range, pt_regs) }

    pub fn syscall_receive_pages(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, ep_idx: EndpointIdx, va: VAddr, range: usize, pt_regs: &mut Registers) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
            edp_idx_valid(ep_idx),
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).no_locks_held(),
            old(steps).snapshot_k() == *old(krnl),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            old(steps).view().len() <= final(steps).view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            ipc_pages_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                ThreadState::RECEIVING, VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) },
                *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id), ret),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(steps).snapshot_k() == *final(krnl),
            ret is CpuIdle && old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running && !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() ==> {
                &&& final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(*old(krnl)), new_u: kernel_k_to_kernel_u(*final(krnl)) })
                &&& ipc_block_step_pre(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, ThreadState::RECEIVING)
                &&& ipc_block_step(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                    ThreadState::RECEIVING, IPCPayLoad::Pages { va_range: VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) } }, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id))
            },
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            ret is Success || ret is CpuIdle || ret is Error || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled
                || ret is ErrorIpcTypeMismatch || ret is ErrorIpcSameProcess || ret is ErrorIpcSourceUnmapped || ret is ErrorIpcPageOwnerMismatch || ret is ErrorNoQuota || ret is ErrorVaInUse || ret is ErrorIpcRangeNotUser,
            ipc_pages_args_invalid(va, range) ==> ret is Error,
            !ipc_pages_args_invalid(va, range) ==> ipc_rejection(ret) == ipc_entry_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, ThreadState::RECEIVING, true),
    { syscall_pages(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, ep_idx, ThreadState::RECEIVING, va, range, pt_regs) }

    fn syscall_pages(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, ep_idx: EndpointIdx, waiting_state: ThreadState, va: VAddr, range: usize, pt_regs: &mut Registers) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
            edp_idx_valid(ep_idx),
            waiting_state is SENDING || waiting_state is RECEIVING,
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).no_locks_held(),
            old(steps).snapshot_k() == *old(krnl),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
        ensures
            old(steps).view().len() <= final(steps).view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            ipc_pages_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                waiting_state, VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) },
                *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id), ret),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).no_locks_held(),
            final(steps).snapshot_k() == *final(krnl),
            ret is CpuIdle && old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running && !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() ==> {
                &&& final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(*old(krnl)), new_u: kernel_k_to_kernel_u(*final(krnl)) })
                &&& ipc_block_step_pre(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, waiting_state)
                &&& ipc_block_step(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx,
                    waiting_state, IPCPayLoad::Pages { va_range: VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) } }, *old(pt_regs), ipc_block_flushes_default_pcid(*old(krnl), cpu_id))
            },
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            ret is Success || ret is CpuIdle || ret is Error || ret is ErrorThreadKilled || ret is ErrorInvalidEndpoint || ret is ErrorIpcPeerKilled
                || ret is ErrorIpcTypeMismatch || ret is ErrorIpcSameProcess || ret is ErrorIpcSourceUnmapped || ret is ErrorIpcPageOwnerMismatch || ret is ErrorNoQuota || ret is ErrorVaInUse || ret is ErrorIpcRangeNotUser,
            ipc_pages_args_invalid(va, range) ==> ret is Error,
            !ipc_pages_args_invalid(va, range) ==> ipc_rejection(ret) == ipc_entry_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, waiting_state, true),
    {
        proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }

        if range == 0 || range > usize::MAX / 4096usize || !va_4k_valid(va) {
            proof {
                enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
                steps.end_kernel_step_unchanged(&*krnl, &*lctx);
                ipc_pages_syscall_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, waiting_state,
                    VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) }, *old(pt_regs),
                    ipc_block_flushes_default_pcid(*old(krnl), cpu_id), RetValueType::Error);
            }
            return RetValueType::Error;
        }
        let span = range * 4096usize;
        if va >= usize::MAX - span || !va_4k_range_valid(va, range) {
            proof {
                enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
                steps.end_kernel_step_unchanged(&*krnl, &*lctx);
                ipc_pages_syscall_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, ep_idx, waiting_state,
                    VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) }, *old(pt_regs),
                    ipc_block_flushes_default_pcid(*old(krnl), cpu_id), RetValueType::Error);
            }
            return RetValueType::Error;
        }
        let va_range = VaRange4K::new(va, range);
        syscall_ipc_ordinary(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, ep_idx, waiting_state, IPCPayLoad::Pages { va_range }, true, pt_regs)
    }
} // verus!
