use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_dispatch::syscall_ipc_ordinary_empty;
verus! {

    /// Send an empty payload through an endpoint.
    pub fn syscall_send_empty(
        kernel: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        endpoint_index: EndpointIdx,
        pt_regs: &mut Registers,
    ) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            edp_idx_valid(endpoint_index),
            old(kernel).inv(),
            old(kernel).cpu_array.spec_index(cpu_id).view().view().state
                is Running,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
            old(steps).steps.len() == 0,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
            old(kernel).all_objects_unlocked(old(lctx)),
            lock_id_aligned(old(kernel), old(lctx)),
        ensures
            final(kernel).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
            final(kernel).all_objects_unlocked(final(lctx)),
            lock_id_aligned(final(kernel), final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            ret is CpuIdle ==> final(steps).steps.len() == 1,
            !(ret is CpuIdle) ==> final(steps).steps.len() == 0,
            ret is Success
                || ret is CpuIdle
                || ret is ErrorProcessKilled
                || ret is ErrorThreadKilled
                || ret is ErrorInvalidEndpoint
                || ret is ErrorIpcPeerKilled
                || ret is ErrorIpcTypeMismatch,
    {
        syscall_ipc_ordinary_empty(kernel, 
            Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id,
            endpoint_index, ThreadState::SENDING, pt_regs,
        )
    }

    /// Receive an empty payload through an endpoint.
    pub fn syscall_receive_empty(
        kernel: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        endpoint_index: EndpointIdx,
        pt_regs: &mut Registers,
    ) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            edp_idx_valid(endpoint_index),
            old(kernel).inv(),
            old(kernel).cpu_array.spec_index(cpu_id).view().view().state
                is Running,
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
            old(steps).steps.len() == 0,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
            old(kernel).all_objects_unlocked(old(lctx)),
            lock_id_aligned(old(kernel), old(lctx)),
        ensures
            final(kernel).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
            final(kernel).all_objects_unlocked(final(lctx)),
            lock_id_aligned(final(kernel), final(lctx)),
            *final(pt_regs) =~= *old(pt_regs),
            ret is CpuIdle ==> final(steps).steps.len() == 1,
            !(ret is CpuIdle) ==> final(steps).steps.len() == 0,
            ret is Success
                || ret is CpuIdle
                || ret is ErrorProcessKilled
                || ret is ErrorThreadKilled
                || ret is ErrorInvalidEndpoint
                || ret is ErrorIpcPeerKilled
                || ret is ErrorIpcTypeMismatch,
    {
        syscall_ipc_ordinary_empty(kernel, 
            Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id,
            endpoint_index, ThreadState::RECEIVING, pt_regs,
        )
    }

} // verus!
