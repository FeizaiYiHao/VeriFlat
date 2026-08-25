use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_dispatch::syscall_ipc_ordinary;
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
        syscall_ipc_ordinary(kernel,
            Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id,
            endpoint_index, ThreadState::SENDING, IPCPayLoad::Empty, pt_regs,
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
        syscall_ipc_ordinary(kernel,
            Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id,
            endpoint_index, ThreadState::RECEIVING, IPCPayLoad::Empty, pt_regs,
        )
    }

    pub fn syscall_send_endpoint(
        kernel: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        endpoint_index: EndpointIdx,
        source_endpoint_index: EndpointIdx,
        pt_regs: &mut Registers,
    ) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            edp_idx_valid(endpoint_index),
            edp_idx_valid(source_endpoint_index),
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
                || ret is ErrorIpcTypeMismatch
                || ret is ErrorIpcEndpointSourceInvalid
                || ret is ErrorIpcEndpointTargetInUse
                || ret is ErrorIpcEndpointOwnerMismatch,
    {
        syscall_ipc_ordinary(
            kernel, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id,
            endpoint_index, ThreadState::SENDING,
            IPCPayLoad::Endpoint {
                endpoint_index: source_endpoint_index,
            },
            pt_regs,
        )
    }

    pub fn syscall_receive_endpoint(
        kernel: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        endpoint_index: EndpointIdx,
        target_endpoint_index: EndpointIdx,
        pt_regs: &mut Registers,
    ) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            edp_idx_valid(endpoint_index),
            edp_idx_valid(target_endpoint_index),
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
                || ret is ErrorIpcTypeMismatch
                || ret is ErrorIpcEndpointSourceInvalid
                || ret is ErrorIpcEndpointTargetInUse
                || ret is ErrorIpcEndpointOwnerMismatch,
    {
        syscall_ipc_ordinary(
            kernel, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id,
            endpoint_index, ThreadState::RECEIVING,
            IPCPayLoad::Endpoint {
                endpoint_index: target_endpoint_index,
            },
            pt_regs,
        )
    }

    pub fn syscall_send_pages(
        kernel: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        endpoint_index: EndpointIdx,
        va: VAddr,
        range: usize,
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
            ret is Success ==> final(steps).steps.len() == range,
            !(ret is CpuIdle) && !(ret is Success)
                ==> final(steps).steps.len() == 0,
            ret is Success
                || ret is CpuIdle
                || ret is Error
                || ret is ErrorProcessKilled
                || ret is ErrorThreadKilled
                || ret is ErrorInvalidEndpoint
                || ret is ErrorIpcPeerKilled
                || ret is ErrorIpcTypeMismatch
                || ret is ErrorIpcSameProcess
                || ret is ErrorIpcSourceUnmapped
                || ret is ErrorIpcPageOwnerMismatch
                || ret is ErrorNoQuota
                || ret is ErrorVaInUse,
    {
        syscall_pages(
            kernel, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id,
            endpoint_index, ThreadState::SENDING, va, range, pt_regs,
        )
    }

    pub fn syscall_receive_pages(
        kernel: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        endpoint_index: EndpointIdx,
        va: VAddr,
        range: usize,
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
            ret is Success ==> final(steps).steps.len() == range,
            !(ret is CpuIdle) && !(ret is Success)
                ==> final(steps).steps.len() == 0,
            ret is Success
                || ret is CpuIdle
                || ret is Error
                || ret is ErrorProcessKilled
                || ret is ErrorThreadKilled
                || ret is ErrorInvalidEndpoint
                || ret is ErrorIpcPeerKilled
                || ret is ErrorIpcTypeMismatch
                || ret is ErrorIpcSameProcess
                || ret is ErrorIpcSourceUnmapped
                || ret is ErrorIpcPageOwnerMismatch
                || ret is ErrorNoQuota
                || ret is ErrorVaInUse,
    {
        syscall_pages(
            kernel, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id,
            endpoint_index, ThreadState::RECEIVING, va, range, pt_regs,
        )
    }

    fn syscall_pages(
        kernel: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        endpoint_index: EndpointIdx,
        waiting_state: ThreadState,
        va: VAddr,
        range: usize,
        pt_regs: &mut Registers,
    ) -> (ret: RetValueType)
        requires
            index_valid(NUM_CPUS, cpu_id),
            edp_idx_valid(endpoint_index),
            waiting_state is SENDING || waiting_state is RECEIVING,
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
            ret is Success ==> final(steps).steps.len() == range,
            !(ret is CpuIdle) && !(ret is Success)
                ==> final(steps).steps.len() == 0,
            ret is Success
                || ret is CpuIdle
                || ret is Error
                || ret is ErrorProcessKilled
                || ret is ErrorThreadKilled
                || ret is ErrorInvalidEndpoint
                || ret is ErrorIpcPeerKilled
                || ret is ErrorIpcTypeMismatch
                || ret is ErrorIpcSameProcess
                || ret is ErrorIpcSourceUnmapped
                || ret is ErrorIpcPageOwnerMismatch
                || ret is ErrorNoQuota
                || ret is ErrorVaInUse,
    {
        if range == 0
            || range > usize::MAX / 4096usize
            || range > usize::MAX / 3usize
            || !va_4k_valid(va)
        {
            proof {
                enter_kernel_view_release_preserving_lock_id_alignment(
                    &*kernel, &mut *lctx,
                );
                steps.end_kernel_step(&*kernel, &*lctx);
            }
            return RetValueType::Error;
        }
        let span = range * 4096usize;
        if va >= usize::MAX - span || !va_4k_range_valid(va, range) {
            proof {
                enter_kernel_view_release_preserving_lock_id_alignment(
                    &*kernel, &mut *lctx,
                );
                steps.end_kernel_step(&*kernel, &*lctx);
            }
            return RetValueType::Error;
        }
        let va_range = VaRange4K::new(va, range);
        syscall_ipc_ordinary(
            kernel, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id,
            endpoint_index, waiting_state,
            IPCPayLoad::Pages { va_range }, pt_regs,
        )
    }

} // verus!
