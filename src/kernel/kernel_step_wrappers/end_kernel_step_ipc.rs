use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::projection_ipc::{
    kernel_ipc_accept_call_fields_implies_u_step, kernel_ipc_block_fields_implies_u_step, kernel_ipc_call_handoff_fields_implies_u_step,
    kernel_ipc_rendezvous_fields_implies_u_step, kernel_ipc_reply_handoff_fields_implies_u_step,
};

verus! {
impl KernelSteps {
    #[verifier::spinoff_prover]
    pub proof fn end_kernel_step_ipc_block(
        tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
        endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, regs: Registers, flushed_default_pcid: bool,
    )
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_ipc_block_fields(&old(self).snapshot_k(), krnl, cpu_id, thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, regs, flushed_default_pcid),
            forall|p: RwLockContainerPtr| #![trigger krnl.ctn_mp.spec_index(p)] old(self).snapshot_k().ctn_mp.dom().contains(p) ==> krnl.ctn_mp.spec_index(p).lock_process_owner_u() == old(self).snapshot_k().ctn_mp.spec_index(p).lock_process_owner_u(),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            kernel_u_ipc_block_changed(old(self).snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, thread_ptr, endpoint_ptr,
                endpoint_index, waiting_state, payload, regs, flushed_default_pcid),
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            kernel_u_ipc_block_changed(final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u, cpu_id, thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, regs, flushed_default_pcid),
            {
                let old_u = final(self).nonlock_view().last().old_u;
                let cpu = old_u.cpu_array[cpu_id as int];
                let thread = old_u.thread_map.spec_index(thread_ptr);
                let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_thread == Some(thread_ptr)
                &&& cpu.current_process == Some(thread.owning_proc)
                &&& cpu.killed == old(self).snapshot_k().cpu_arr.spec_index(cpu_id).value.being_killed()
                &&& old_u.process_map.dom().contains(thread.owning_proc)
                &&& old_u.container_map.dom().contains(thread.owning_container)
                &&& old_u.thread_map.dom().contains(thread_ptr)
                &&& thread.lock_state is Unlocked
                &&& thread.syscall_progress is None
                &&& !thread.killed
                &&& thread.state == (ThreadState::RUNNING { cpu_id })
                &&& edp_idx_valid(endpoint_index)
                &&& thread.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
                &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
                &&& endpoint.lock_state is Unlocked
                &&& !endpoint.queue.contains(thread_ptr)
                &&& waiting_state.is_endpoint_waiting()
                &&& endpoint.queue.len() == 0 || (endpoint.queue_state is SEND) == waiting_state.is_endpoint_send_waiting()
            },
            {
                let old_u = kernel_k_to_kernel_u(old(self).snapshot_k());
                let cpu = old_u.cpu_array[cpu_id as int];
                let thread = old_u.thread_map.spec_index(thread_ptr);
                let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_thread == Some(thread_ptr)
                &&& cpu.current_process == Some(thread.owning_proc)
                &&& cpu.killed == old(self).snapshot_k().cpu_arr.spec_index(cpu_id).value.being_killed()
                &&& old_u.process_map.dom().contains(thread.owning_proc)
                &&& old_u.container_map.dom().contains(thread.owning_container)
                &&& old_u.thread_map.dom().contains(thread_ptr)
                &&& thread.lock_state is Unlocked
                &&& thread.syscall_progress is None
                &&& !thread.killed
                &&& thread.state == (ThreadState::RUNNING { cpu_id })
                &&& edp_idx_valid(endpoint_index)
                &&& thread.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
                &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
                &&& endpoint.lock_state is Unlocked
                &&& !endpoint.queue.contains(thread_ptr)
                &&& waiting_state.is_endpoint_waiting()
                &&& endpoint.queue.len() == 0 || (endpoint.queue_state is SEND) == waiting_state.is_endpoint_send_waiting()
            },
    {
        hide(kernel_k_user_projection);
        reveal(kernel_u_ipc_block_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_nonlock_kernel_u(self.snapshot_k());
            let thread = pre_u.thread_map.spec_index(thread_ptr);
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.cpu_array[cpu_id as int].killed == self.snapshot_k().cpu_arr.spec_index(cpu_id).value.being_killed()
            &&& thread.lock_state is Unlocked
            &&& thread.syscall_progress is None
            &&& pre_u.endpoint_map.spec_index(endpoint_ptr).lock_state is Unlocked
            &&& pre_u.container_map.dom().contains(thread.owning_container)
        }) by {
            reveal(kernel_ipc_block_fields); kernel_u_nonlock_domains_projection(&self.snapshot_k()); kernel_cpu_nonlock_projection_at(&self.snapshot_k(), cpu_id);
            kernel_thread_nonlock_projection_at(&self.snapshot_k(), thread_ptr); kernel_endpoint_nonlock_projection_at(&self.snapshot_k(), endpoint_ptr);
        };
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            let thread = pre_u.thread_map.spec_index(thread_ptr);
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& pre_u.cpu_array[cpu_id as int].killed == self.snapshot_k().cpu_arr.spec_index(cpu_id).value.being_killed()
            &&& thread.lock_state is Unlocked
            &&& thread.syscall_progress is None
            &&& pre_u.endpoint_map.spec_index(endpoint_ptr).lock_state is Unlocked
            &&& pre_u.container_map.dom().contains(thread.owning_container)
        }) by {
            reveal(kernel_ipc_block_fields); kernel_u_domains_projection(&self.snapshot_k()); kernel_cpu_projection_at(&self.snapshot_k(), cpu_id);
            kernel_thread_projection_at(&self.snapshot_k(), thread_ptr); kernel_endpoint_projection_at(&self.snapshot_k(), endpoint_ptr);
        };
        let pre_u = self.nonlock_snapshot_u();
        let post_u = kernel_k_to_nonlock_kernel_u(*krnl);
        assert(kernel_u_ipc_block_changed(pre_u, post_u, cpu_id, thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, regs, flushed_default_pcid)) by {
            kernel_ipc_block_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, regs, flushed_default_pcid, false);
            reveal(kernel_k_to_nonlock_kernel_u);
        };
        assert(kernel_u_ipc_block_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, regs, flushed_default_pcid)) by {
            kernel_ipc_block_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, regs, flushed_default_pcid, true);
            reveal(kernel_k_to_kernel_u);
        };
        self.end_kernel_step_raw(krnl, lctx);
    }

    #[verifier::spinoff_prover]
    pub proof fn end_kernel_step_ipc_call_handoff(
        tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, caller_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
        endpoint_index: EndpointIdx, callee_ptr: RwLockThreadPtr, regs: Registers, flushed_pcid: Option<Pcid>,
    )
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_ipc_call_handoff_fields(&old(self).snapshot_k(), krnl, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, regs, flushed_pcid),
            forall|p: RwLockContainerPtr| #![trigger krnl.ctn_mp.spec_index(p)] old(self).snapshot_k().ctn_mp.dom().contains(p) ==> krnl.ctn_mp.spec_index(p).lock_process_owner_u() == old(self).snapshot_k().ctn_mp.spec_index(p).lock_process_owner_u(),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            kernel_u_ipc_call_handoff_changed(old(self).snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, regs, flushed_pcid),
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            kernel_u_ipc_call_handoff_changed(final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, regs, flushed_pcid),
            {
                let old_u = final(self).nonlock_view().last().old_u;
                let cpu = old_u.cpu_array[cpu_id as int];
                let caller = old_u.thread_map.spec_index(caller_ptr);
                let callee = old_u.thread_map.spec_index(callee_ptr);
                let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_thread == Some(caller_ptr)
                &&& cpu.current_process == Some(caller.owning_proc)
                &&& old_u.process_map.dom().contains(caller.owning_proc)
                &&& old_u.container_map.dom().contains(caller.owning_container)
                &&& old_u.thread_map.dom().contains(caller_ptr)
                &&& caller.lock_state is Unlocked
                &&& caller.syscall_progress is None
                &&& !caller.killed
                &&& caller.state == (ThreadState::RUNNING { cpu_id })
                &&& caller.callee is None
                &&& edp_idx_valid(endpoint_index)
                &&& caller.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
                &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
                &&& endpoint.lock_state is Unlocked
                &&& !endpoint.queue.contains(caller_ptr)
                &&& endpoint.queue.len() > 0
                &&& endpoint.queue[0] == callee_ptr
                &&& endpoint.queue_state is RECEIVE
                &&& callee_ptr != caller_ptr
                &&& old_u.thread_map.dom().contains(callee_ptr)
                &&& callee.lock_state is Unlocked
                &&& !callee.killed
                &&& callee.state is RECEIVING_CALL
                &&& callee.caller is None
                &&& callee.callee is None
                &&& callee.blocking_endpoint_ptr == Some(endpoint_ptr)
                &&& callee.owning_container == caller.owning_container
                &&& old_u.process_map.dom().contains(callee.owning_proc)
            },
            {
                let old_u = kernel_k_to_kernel_u(old(self).snapshot_k());
                let cpu = old_u.cpu_array[cpu_id as int];
                let caller = old_u.thread_map.spec_index(caller_ptr);
                let callee = old_u.thread_map.spec_index(callee_ptr);
                let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_thread == Some(caller_ptr)
                &&& cpu.current_process == Some(caller.owning_proc)
                &&& old_u.process_map.dom().contains(caller.owning_proc)
                &&& old_u.container_map.dom().contains(caller.owning_container)
                &&& old_u.thread_map.dom().contains(caller_ptr)
                &&& caller.lock_state is Unlocked
                &&& caller.syscall_progress is None
                &&& !caller.killed
                &&& caller.state == (ThreadState::RUNNING { cpu_id })
                &&& caller.callee is None
                &&& edp_idx_valid(endpoint_index)
                &&& caller.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
                &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
                &&& endpoint.lock_state is Unlocked
                &&& !endpoint.queue.contains(caller_ptr)
                &&& endpoint.queue.len() > 0
                &&& endpoint.queue[0] == callee_ptr
                &&& endpoint.queue_state is RECEIVE
                &&& callee_ptr != caller_ptr
                &&& old_u.thread_map.dom().contains(callee_ptr)
                &&& callee.lock_state is Unlocked
                &&& !callee.killed
                &&& callee.state is RECEIVING_CALL
                &&& callee.caller is None
                &&& callee.callee is None
                &&& callee.blocking_endpoint_ptr == Some(endpoint_ptr)
                &&& callee.owning_container == caller.owning_container
                &&& old_u.process_map.dom().contains(callee.owning_proc)
            },
    {
        hide(kernel_k_user_projection);
        reveal(kernel_u_ipc_call_handoff_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_nonlock_kernel_u(self.snapshot_k());
            let first = pre_u.thread_map.spec_index(caller_ptr);
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& first.lock_state is Unlocked
            &&& first.syscall_progress is None
            &&& pre_u.thread_map.spec_index(callee_ptr).lock_state is Unlocked
            &&& pre_u.endpoint_map.spec_index(endpoint_ptr).lock_state is Unlocked
            &&& pre_u.container_map.dom().contains(first.owning_container)
        }) by {
            reveal(kernel_ipc_call_handoff_fields); kernel_u_nonlock_domains_projection(&self.snapshot_k()); kernel_cpu_nonlock_projection_at(&self.snapshot_k(), cpu_id);
            kernel_thread_nonlock_projection_at(&self.snapshot_k(), caller_ptr); kernel_thread_nonlock_projection_at(&self.snapshot_k(), callee_ptr);
            kernel_endpoint_nonlock_projection_at(&self.snapshot_k(), endpoint_ptr);
        };
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            let first = pre_u.thread_map.spec_index(caller_ptr);
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& first.lock_state is Unlocked
            &&& first.syscall_progress is None
            &&& pre_u.thread_map.spec_index(callee_ptr).lock_state is Unlocked
            &&& pre_u.endpoint_map.spec_index(endpoint_ptr).lock_state is Unlocked
            &&& pre_u.container_map.dom().contains(first.owning_container)
        }) by {
            reveal(kernel_ipc_call_handoff_fields); kernel_u_domains_projection(&self.snapshot_k()); kernel_cpu_projection_at(&self.snapshot_k(), cpu_id);
            kernel_thread_projection_at(&self.snapshot_k(), caller_ptr); kernel_thread_projection_at(&self.snapshot_k(), callee_ptr); kernel_endpoint_projection_at(&self.snapshot_k(), endpoint_ptr);
        };
        let pre_u = self.nonlock_snapshot_u();
        let post_u = kernel_k_to_nonlock_kernel_u(*krnl);
        assert(kernel_u_ipc_call_handoff_changed(pre_u, post_u, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, regs, flushed_pcid)) by {
            kernel_ipc_call_handoff_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, regs, flushed_pcid, false);
            reveal(kernel_k_to_nonlock_kernel_u);
        };
        assert(kernel_u_ipc_call_handoff_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, regs, flushed_pcid)) by {
            kernel_ipc_call_handoff_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, caller_ptr, endpoint_ptr, endpoint_index, callee_ptr, regs, flushed_pcid, true);
            reveal(kernel_k_to_kernel_u);
        };
        self.end_kernel_step_raw(krnl, lctx);
    }

    #[verifier::spinoff_prover]
    pub proof fn end_kernel_step_ipc_accept_call(tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, caller_ptr: RwLockThreadPtr)
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_ipc_accept_call_fields(&old(self).snapshot_k(), krnl, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            kernel_u_ipc_accept_call_changed(old(self).snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr),
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            kernel_u_ipc_accept_call_changed(final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr),
            {
                let old_u = final(self).nonlock_view().last().old_u;
                let cpu = old_u.cpu_array[cpu_id as int];
                let callee = old_u.thread_map.spec_index(callee_ptr);
                let caller = old_u.thread_map.spec_index(caller_ptr);
                let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_thread == Some(callee_ptr)
                &&& cpu.current_process == Some(callee.owning_proc)
                &&& old_u.process_map.dom().contains(callee.owning_proc)
                &&& old_u.container_map.dom().contains(callee.owning_container)
                &&& old_u.thread_map.dom().contains(callee_ptr)
                &&& callee.lock_state is Unlocked
                &&& callee.syscall_progress is None
                &&& !callee.killed
                &&& callee.state == (ThreadState::RUNNING { cpu_id })
                &&& callee.caller is None
                &&& callee.callee is None
                &&& edp_idx_valid(endpoint_index)
                &&& callee.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
                &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
                &&& endpoint.lock_state is Unlocked
                &&& !endpoint.queue.contains(callee_ptr)
                &&& endpoint.queue.len() > 0
                &&& endpoint.queue[0] == caller_ptr
                &&& endpoint.queue_state is SEND
                &&& caller_ptr != callee_ptr
                &&& old_u.thread_map.dom().contains(caller_ptr)
                &&& caller.lock_state is Unlocked
                &&& !caller.killed
                &&& caller.state is CALLING
                &&& caller.callee is None
                &&& caller.blocking_endpoint_ptr == Some(endpoint_ptr)
                &&& caller.owning_container == callee.owning_container
            },
            {
                let old_u = kernel_k_to_kernel_u(old(self).snapshot_k());
                let cpu = old_u.cpu_array[cpu_id as int];
                let callee = old_u.thread_map.spec_index(callee_ptr);
                let caller = old_u.thread_map.spec_index(caller_ptr);
                let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_thread == Some(callee_ptr)
                &&& cpu.current_process == Some(callee.owning_proc)
                &&& old_u.process_map.dom().contains(callee.owning_proc)
                &&& old_u.container_map.dom().contains(callee.owning_container)
                &&& old_u.thread_map.dom().contains(callee_ptr)
                &&& callee.lock_state is Unlocked
                &&& callee.syscall_progress is None
                &&& !callee.killed
                &&& callee.state == (ThreadState::RUNNING { cpu_id })
                &&& callee.caller is None
                &&& callee.callee is None
                &&& edp_idx_valid(endpoint_index)
                &&& callee.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
                &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
                &&& endpoint.lock_state is Unlocked
                &&& !endpoint.queue.contains(callee_ptr)
                &&& endpoint.queue.len() > 0
                &&& endpoint.queue[0] == caller_ptr
                &&& endpoint.queue_state is SEND
                &&& caller_ptr != callee_ptr
                &&& old_u.thread_map.dom().contains(caller_ptr)
                &&& caller.lock_state is Unlocked
                &&& !caller.killed
                &&& caller.state is CALLING
                &&& caller.callee is None
                &&& caller.blocking_endpoint_ptr == Some(endpoint_ptr)
                &&& caller.owning_container == callee.owning_container
            },
            final(self).nonlock_view().last().old_u.thread_map[caller_ptr].ipc_payload == old(self).snapshot_u().thread_map[caller_ptr].ipc_payload,
    {
        hide(kernel_k_user_projection);
        reveal(kernel_u_ipc_accept_call_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_nonlock_kernel_u(self.snapshot_k());
            let first = pre_u.thread_map.spec_index(callee_ptr);
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& first.lock_state is Unlocked
            &&& first.syscall_progress is None
            &&& pre_u.thread_map.spec_index(caller_ptr).lock_state is Unlocked
            &&& pre_u.endpoint_map.spec_index(endpoint_ptr).lock_state is Unlocked
            &&& pre_u.container_map.dom().contains(first.owning_container)
        }) by {
            reveal(kernel_ipc_accept_call_fields); kernel_u_nonlock_domains_projection(&self.snapshot_k()); kernel_cpu_nonlock_projection_at(&self.snapshot_k(), cpu_id);
            kernel_thread_nonlock_projection_at(&self.snapshot_k(), callee_ptr); kernel_thread_nonlock_projection_at(&self.snapshot_k(), caller_ptr);
            kernel_endpoint_nonlock_projection_at(&self.snapshot_k(), endpoint_ptr);
        };
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            let first = pre_u.thread_map.spec_index(callee_ptr);
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& first.lock_state is Unlocked
            &&& first.syscall_progress is None
            &&& pre_u.thread_map.spec_index(caller_ptr).lock_state is Unlocked
            &&& pre_u.endpoint_map.spec_index(endpoint_ptr).lock_state is Unlocked
            &&& pre_u.container_map.dom().contains(first.owning_container)
        }) by {
            reveal(kernel_ipc_accept_call_fields); kernel_u_domains_projection(&self.snapshot_k()); kernel_cpu_projection_at(&self.snapshot_k(), cpu_id);
            kernel_thread_projection_at(&self.snapshot_k(), callee_ptr); kernel_thread_projection_at(&self.snapshot_k(), caller_ptr); kernel_endpoint_projection_at(&self.snapshot_k(), endpoint_ptr);
        };
        assert(self.nonlock_snapshot_u().thread_map[caller_ptr].ipc_payload == self.snapshot_u().thread_map[caller_ptr].ipc_payload) by {
            reveal(kernel_ipc_accept_call_fields); kernel_thread_projection_at(&self.snapshot_k(), caller_ptr); kernel_thread_nonlock_projection_at(&self.snapshot_k(), caller_ptr);
        };
        let pre_u = self.nonlock_snapshot_u();
        let post_u = kernel_k_to_nonlock_kernel_u(*krnl);
        assert(kernel_u_ipc_accept_call_changed(pre_u, post_u, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr)) by {
            kernel_ipc_accept_call_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, false);
            reveal(kernel_k_to_nonlock_kernel_u);
        };
        assert(kernel_u_ipc_accept_call_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr)) by {
            kernel_ipc_accept_call_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, true);
            reveal(kernel_k_to_kernel_u);
        };
        self.end_kernel_step_raw(krnl, lctx);
    }

    #[verifier::spinoff_prover]
    pub proof fn end_kernel_step_ipc_reply_handoff(
        tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr,
        endpoint_index: EndpointIdx, caller_ptr: RwLockThreadPtr, regs: Registers, flushed_pcid: Option<Pcid>,
    )
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_ipc_reply_handoff_fields(&old(self).snapshot_k(), krnl, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid),
            forall|p: RwLockContainerPtr| #![trigger krnl.ctn_mp.spec_index(p)] old(self).snapshot_k().ctn_mp.dom().contains(p) ==> krnl.ctn_mp.spec_index(p).lock_process_owner_u() == old(self).snapshot_k().ctn_mp.spec_index(p).lock_process_owner_u(),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            kernel_u_ipc_reply_handoff_changed(old(self).snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid),
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            kernel_u_ipc_reply_handoff_changed(final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid),
            {
                let old_u = final(self).nonlock_view().last().old_u;
                let cpu = old_u.cpu_array[cpu_id as int];
                let callee = old_u.thread_map.spec_index(callee_ptr);
                let caller = old_u.thread_map.spec_index(caller_ptr);
                let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_thread == Some(callee_ptr)
                &&& cpu.current_process == Some(callee.owning_proc)
                &&& old_u.process_map.dom().contains(callee.owning_proc)
                &&& old_u.container_map.dom().contains(callee.owning_container)
                &&& old_u.thread_map.dom().contains(callee_ptr)
                &&& callee.lock_state is Unlocked
                &&& callee.syscall_progress is None
                &&& !callee.killed
                &&& callee.state == (ThreadState::RUNNING { cpu_id })
                &&& callee.caller == Some(caller_ptr)
                &&& callee.callee is None
                &&& edp_idx_valid(endpoint_index)
                &&& callee.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
                &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
                &&& endpoint.lock_state is Unlocked
                &&& !endpoint.queue.contains(callee_ptr)
                &&& endpoint.queue.len() == 0 || endpoint.queue_state is RECEIVE
                &&& caller_ptr != callee_ptr
                &&& old_u.thread_map.dom().contains(caller_ptr)
                &&& caller.lock_state is Unlocked
                &&& !caller.killed
                &&& caller.state is WAITING_REPLY
                &&& caller.callee == Some(callee_ptr)
                &&& caller.owning_container == callee.owning_container
                &&& old_u.process_map.dom().contains(caller.owning_proc)
            },
            {
                let old_u = kernel_k_to_kernel_u(old(self).snapshot_k());
                let cpu = old_u.cpu_array[cpu_id as int];
                let callee = old_u.thread_map.spec_index(callee_ptr);
                let caller = old_u.thread_map.spec_index(caller_ptr);
                let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_thread == Some(callee_ptr)
                &&& cpu.current_process == Some(callee.owning_proc)
                &&& old_u.process_map.dom().contains(callee.owning_proc)
                &&& old_u.container_map.dom().contains(callee.owning_container)
                &&& old_u.thread_map.dom().contains(callee_ptr)
                &&& callee.lock_state is Unlocked
                &&& callee.syscall_progress is None
                &&& !callee.killed
                &&& callee.state == (ThreadState::RUNNING { cpu_id })
                &&& callee.caller == Some(caller_ptr)
                &&& callee.callee is None
                &&& edp_idx_valid(endpoint_index)
                &&& callee.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
                &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
                &&& endpoint.lock_state is Unlocked
                &&& !endpoint.queue.contains(callee_ptr)
                &&& endpoint.queue.len() == 0 || endpoint.queue_state is RECEIVE
                &&& caller_ptr != callee_ptr
                &&& old_u.thread_map.dom().contains(caller_ptr)
                &&& caller.lock_state is Unlocked
                &&& !caller.killed
                &&& caller.state is WAITING_REPLY
                &&& caller.callee == Some(callee_ptr)
                &&& caller.owning_container == callee.owning_container
                &&& old_u.process_map.dom().contains(caller.owning_proc)
            },
    {
        hide(kernel_k_user_projection);
        reveal(kernel_u_ipc_reply_handoff_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_nonlock_kernel_u(self.snapshot_k());
            let first = pre_u.thread_map.spec_index(callee_ptr);
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& first.lock_state is Unlocked
            &&& first.syscall_progress is None
            &&& pre_u.thread_map.spec_index(caller_ptr).lock_state is Unlocked
            &&& pre_u.endpoint_map.spec_index(endpoint_ptr).lock_state is Unlocked
            &&& pre_u.container_map.dom().contains(first.owning_container)
        }) by {
            reveal(kernel_ipc_reply_handoff_fields); kernel_u_nonlock_domains_projection(&self.snapshot_k()); kernel_cpu_nonlock_projection_at(&self.snapshot_k(), cpu_id);
            kernel_thread_nonlock_projection_at(&self.snapshot_k(), callee_ptr); kernel_thread_nonlock_projection_at(&self.snapshot_k(), caller_ptr);
            kernel_endpoint_nonlock_projection_at(&self.snapshot_k(), endpoint_ptr);
        };
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            let first = pre_u.thread_map.spec_index(callee_ptr);
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& first.lock_state is Unlocked
            &&& first.syscall_progress is None
            &&& pre_u.thread_map.spec_index(caller_ptr).lock_state is Unlocked
            &&& pre_u.endpoint_map.spec_index(endpoint_ptr).lock_state is Unlocked
            &&& pre_u.container_map.dom().contains(first.owning_container)
        }) by {
            reveal(kernel_ipc_reply_handoff_fields); kernel_u_domains_projection(&self.snapshot_k()); kernel_cpu_projection_at(&self.snapshot_k(), cpu_id);
            kernel_thread_projection_at(&self.snapshot_k(), callee_ptr); kernel_thread_projection_at(&self.snapshot_k(), caller_ptr); kernel_endpoint_projection_at(&self.snapshot_k(), endpoint_ptr);
        };
        let pre_u = self.nonlock_snapshot_u();
        let post_u = kernel_k_to_nonlock_kernel_u(*krnl);
        assert(kernel_u_ipc_reply_handoff_changed(pre_u, post_u, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid)) by {
            kernel_ipc_reply_handoff_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid, false);
            reveal(kernel_k_to_nonlock_kernel_u);
        };
        assert(kernel_u_ipc_reply_handoff_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid)) by {
            kernel_ipc_reply_handoff_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, regs, flushed_pcid, true);
            reveal(kernel_k_to_kernel_u);
        };
        self.end_kernel_step_raw(krnl, lctx);
    }

    #[verifier::spinoff_prover]
    pub proof fn end_kernel_step_ipc_rendezvous(
        tracked &mut self, krnl: &KernelK, tracked lctx: &LocalContext, cpu_id: CpuId, caller_thread_ptr: RwLockThreadPtr,
        endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, waiting_state: ThreadState, peer_thread_ptr: RwLockThreadPtr,
        peer_result: RetValueType, cpu_transfer: Option<(CpuId, RwLockThreadPtr)>, pci_transfer: Option<(PciBdf, RwLockProcessPtr, RwLockProcessPtr)>, payload: IPCPayLoad,
        cpu_sets_locked: bool,
    )
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            kernel_ipc_rendezvous_fields(&old(self).snapshot_k(), krnl, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer),
            krnl.cpu_op.view().view() == old(self).snapshot_k().cpu_op.view().view(),
            krnl.cpu_set_mp.dom() == old(self).snapshot_k().cpu_set_mp.dom(),
            forall|p: RwLockCpuSetPtr| #![trigger krnl.cpu_set_mp.spec_index(p)]
                old(self).snapshot_k().cpu_set_mp.dom().contains(p) ==> krnl.cpu_set_mp.spec_index(p).locking_thread() == old(self).snapshot_k().cpu_set_mp.spec_index(p).locking_thread()
                    && krnl.cpu_set_mp.spec_index(p).being_killed() == old(self).snapshot_k().cpu_set_mp.spec_index(p).being_killed(),
            cpu_sets_locked ==> {
                let snap = old(self).snapshot_k();
                &&& snap.cpu_set_mp.spec_index(snap.ctn_mp.spec_index(snap.thr_mp.spec_index(caller_thread_ptr).view().owning_container).view_rodata().view().cpu_set).locking_thread() is None
                &&& snap.cpu_set_mp.spec_index(snap.ctn_mp.spec_index(snap.thr_mp.spec_index(peer_thread_ptr).view().owning_container).view_rodata().view().cpu_set).locking_thread() is None
            },
            forall|p: RwLockContainerPtr| #![trigger krnl.ctn_mp.spec_index(p)]
                old(self).snapshot_k().ctn_mp.dom().contains(p) && krnl.ctn_mp.dom().contains(p) ==> krnl.ctn_mp.spec_index(p).locking_thread() == old(self).snapshot_k().ctn_mp.spec_index(p).locking_thread()
                    && krnl.ctn_mp.spec_index(p).lock_process_owner_u() == old(self).snapshot_k().ctn_mp.spec_index(p).lock_process_owner_u(),
            forall|p: RwLockProcessPtr| #![trigger krnl.prc_mp.spec_index(p)]
                old(self).snapshot_k().prc_mp.dom().contains(p) && krnl.prc_mp.dom().contains(p) ==> krnl.prc_mp.spec_index(p).locking_thread() == old(self).snapshot_k().prc_mp.spec_index(p).locking_thread(),
            forall|p: RwLockThreadPtr| #![trigger krnl.thr_mp.spec_index(p)]
                old(self).snapshot_k().thr_mp.dom().contains(p) && krnl.thr_mp.dom().contains(p) ==> krnl.thr_mp.spec_index(p).locking_thread() == old(self).snapshot_k().thr_mp.spec_index(p).locking_thread(),
            forall|p: RwLockEndpointPtr| #![trigger krnl.ep_mp.spec_index(p)]
                old(self).snapshot_k().ep_mp.dom().contains(p) && krnl.ep_mp.dom().contains(p) ==> krnl.ep_mp.spec_index(p).locking_thread() == old(self).snapshot_k().ep_mp.spec_index(p).locking_thread(),
            forall|p: RwLockPageTableRoot| #![trigger krnl.pt_mp.spec_index(p)]
                old(self).snapshot_k().pt_mp.dom().contains(p) && krnl.pt_mp.dom().contains(p) ==> krnl.pt_mp.spec_index(p).locking_thread() == old(self).snapshot_k().pt_mp.spec_index(p).locking_thread(),
            forall|p: RwLockPageTableRoot| #![trigger krnl.it_mp.spec_index(p)]
                old(self).snapshot_k().it_mp.dom().contains(p) && krnl.it_mp.dom().contains(p) ==> krnl.it_mp.spec_index(p).locking_thread() == old(self).snapshot_k().it_mp.spec_index(p).locking_thread(),
            forall|i: CpuId| #![trigger krnl.cpu_arr.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> krnl.cpu_arr.spec_index(i).value.locking_thread() == old(self).snapshot_k().cpu_arr.spec_index(i).value.locking_thread(),
        ensures
            old(self).snapshot_u() == kernel_k_to_kernel_u(old(self).snapshot_k()),
            final(self).view() == old(self).view().push(KernelStep { old_u: old(self).snapshot_u(), new_u: kernel_k_to_kernel_u(*krnl) }),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(self).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(self).view()),
            final(self).snapshot_u() == kernel_k_to_kernel_u(*krnl),
            kernel_u_ipc_rendezvous_changed(old(self).snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, caller_thread_ptr,
                endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer),
            final(self).nonlock_view() == old(self).nonlock_view().push(KernelStep { old_u: old(self).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*krnl) }),
            final(self).snapshot_k() == *krnl,
            kernel_u_ipc_rendezvous_changed(final(self).nonlock_view().last().old_u, final(self).nonlock_view().last().new_u, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer),
            {
                let old_u = final(self).nonlock_view().last().old_u;
                let cpu = old_u.cpu_array[cpu_id as int];
                let caller = old_u.thread_map.spec_index(caller_thread_ptr);
                let peer = old_u.thread_map.spec_index(peer_thread_ptr);
                let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_thread == Some(caller_thread_ptr)
                &&& cpu.current_process == Some(caller.owning_proc)
                &&& old_u.process_map.dom().contains(caller.owning_proc)
                &&& old_u.thread_map.dom().contains(caller_thread_ptr)
                &&& caller.lock_state is Unlocked
                &&& caller.syscall_progress is None
                &&& !caller.killed
                &&& caller.state == (ThreadState::RUNNING { cpu_id })
                &&& edp_idx_valid(endpoint_index)
                &&& caller.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
                &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
                &&& endpoint.lock_state is Unlocked
                &&& !endpoint.queue.contains(caller_thread_ptr)
                &&& waiting_state.is_endpoint_waiting()
                &&& endpoint.queue.len() > 0
                &&& endpoint.queue[0] == peer_thread_ptr
                &&& (endpoint.queue_state is SEND) != waiting_state.is_endpoint_send_waiting()
                &&& old_u.thread_map.dom().contains(peer_thread_ptr)
                &&& peer.lock_state is Unlocked
                &&& peer_thread_ptr != caller_thread_ptr
                &&& !peer.killed
                &&& peer.state.is_endpoint_waiting()
                &&& peer.blocking_endpoint_ptr == Some(endpoint_ptr)
                &&& old_u.container_map.dom().contains(peer.owning_container)
                &&& old_u.container_map.dom().contains(caller.owning_container)
                &&& cpu_sets_locked ==> old_u.container_map[caller.owning_container].cpu_set_lock is Unlocked && old_u.container_map[peer.owning_container].cpu_set_lock is Unlocked
                &&& cpu_transfer matches Some((transfer, _)) ==> old_u.cpu_array[transfer as int].lock_state is Unlocked
                &&& pci_transfer matches Some((bdf, sender, _)) ==> old_u.iommu_root_table.attached[bdf.0 as int][bdf.1 as int][bdf.2 as int] && old_u.process_map[sender].iommu_table is Some
                    ==> old_u.process_map[sender].iommu_table->Some_0.lock_state is Unlocked
            },
            {
                let old_u = kernel_k_to_kernel_u(old(self).snapshot_k());
                let cpu = old_u.cpu_array[cpu_id as int];
                let caller = old_u.thread_map.spec_index(caller_thread_ptr);
                let peer = old_u.thread_map.spec_index(peer_thread_ptr);
                let endpoint = old_u.endpoint_map.spec_index(endpoint_ptr);
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& cpu.lock_state is Unlocked
                &&& cpu.state is Running
                &&& cpu.current_thread == Some(caller_thread_ptr)
                &&& cpu.current_process == Some(caller.owning_proc)
                &&& old_u.process_map.dom().contains(caller.owning_proc)
                &&& old_u.thread_map.dom().contains(caller_thread_ptr)
                &&& caller.lock_state is Unlocked
                &&& caller.syscall_progress is None
                &&& !caller.killed
                &&& caller.state == (ThreadState::RUNNING { cpu_id })
                &&& edp_idx_valid(endpoint_index)
                &&& caller.endpoint_descriptors[endpoint_index as int] == Some(endpoint_ptr)
                &&& old_u.endpoint_map.dom().contains(endpoint_ptr)
                &&& endpoint.lock_state is Unlocked
                &&& !endpoint.queue.contains(caller_thread_ptr)
                &&& waiting_state.is_endpoint_waiting()
                &&& endpoint.queue.len() > 0
                &&& endpoint.queue[0] == peer_thread_ptr
                &&& (endpoint.queue_state is SEND) != waiting_state.is_endpoint_send_waiting()
                &&& old_u.thread_map.dom().contains(peer_thread_ptr)
                &&& peer.lock_state is Unlocked
                &&& peer_thread_ptr != caller_thread_ptr
                &&& !peer.killed
                &&& peer.state.is_endpoint_waiting()
                &&& peer.blocking_endpoint_ptr == Some(endpoint_ptr)
                &&& old_u.container_map.dom().contains(peer.owning_container)
                &&& old_u.container_map.dom().contains(caller.owning_container)
                &&& cpu_sets_locked ==> old_u.container_map[caller.owning_container].cpu_set_lock is Unlocked && old_u.container_map[peer.owning_container].cpu_set_lock is Unlocked
                &&& cpu_transfer matches Some((transfer, _)) ==> old_u.cpu_array[transfer as int].lock_state is Unlocked
                &&& pci_transfer matches Some((bdf, sender, _)) ==> old_u.iommu_root_table.attached[bdf.0 as int][bdf.1 as int][bdf.2 as int] && old_u.process_map[sender].iommu_table is Some
                    ==> old_u.process_map[sender].iommu_table->Some_0.lock_state is Unlocked
            },
            ipc_rendezvous_result(final(self).nonlock_view().last().old_u, cpu_id, endpoint_index, waiting_state, payload) == ipc_rendezvous_result(old(self).snapshot_u(), cpu_id, endpoint_index, waiting_state, payload),
            final(self).nonlock_view().last().old_u.thread_map[caller_thread_ptr].owning_proc == old(self).snapshot_u().thread_map[caller_thread_ptr].owning_proc,
            final(self).nonlock_view().last().old_u.thread_map[peer_thread_ptr].owning_proc == old(self).snapshot_u().thread_map[peer_thread_ptr].owning_proc,
    {
        reveal(kernel_u_ipc_rendezvous_changed);
        use_type_invariant(&*self);
        assert({
            let pre_u = kernel_k_to_nonlock_kernel_u(self.snapshot_k());
            let caller = pre_u.thread_map.spec_index(caller_thread_ptr);
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& caller.lock_state is Unlocked
            &&& caller.syscall_progress is None
            &&& pre_u.endpoint_map.spec_index(endpoint_ptr).lock_state is Unlocked
            &&& pre_u.thread_map.spec_index(peer_thread_ptr).lock_state is Unlocked
            &&& pre_u.container_map.dom().contains(caller.owning_container)
            &&& pre_u.container_map[caller.owning_container].cpu_set_lock is Unlocked
            &&& pre_u.container_map[pre_u.thread_map.spec_index(peer_thread_ptr).owning_container].cpu_set_lock is Unlocked
            &&& cpu_transfer matches Some((transfer, _)) ==> pre_u.cpu_array[transfer as int].lock_state is Unlocked
            &&& pci_transfer matches Some((bdf, sender, _)) ==> pre_u.iommu_root_table.attached[bdf.0 as int][bdf.1 as int][bdf.2 as int] && pre_u.process_map[sender].iommu_table is Some
                ==> pre_u.process_map[sender].iommu_table->Some_0.lock_state is Unlocked
        }) by { reveal(kernel_k_to_nonlock_kernel_u); reveal(kernel_ipc_rendezvous_fields); };
        assert({
            let pre_u = kernel_k_to_kernel_u(self.snapshot_k());
            let caller = pre_u.thread_map.spec_index(caller_thread_ptr);
            &&& pre_u.cpu_array[cpu_id as int].lock_state is Unlocked
            &&& caller.lock_state is Unlocked
            &&& caller.syscall_progress is None
            &&& pre_u.endpoint_map.spec_index(endpoint_ptr).lock_state is Unlocked
            &&& pre_u.thread_map.spec_index(peer_thread_ptr).lock_state is Unlocked
            &&& pre_u.container_map.dom().contains(caller.owning_container)
            &&& cpu_sets_locked ==> pre_u.container_map[caller.owning_container].cpu_set_lock is Unlocked
                && pre_u.container_map[pre_u.thread_map.spec_index(peer_thread_ptr).owning_container].cpu_set_lock is Unlocked
            &&& cpu_transfer matches Some((transfer, _)) ==> pre_u.cpu_array[transfer as int].lock_state is Unlocked
            &&& pci_transfer matches Some((bdf, sender, _)) ==> pre_u.iommu_root_table.attached[bdf.0 as int][bdf.1 as int][bdf.2 as int] && pre_u.process_map[sender].iommu_table is Some
                ==> pre_u.process_map[sender].iommu_table->Some_0.lock_state is Unlocked
        }) by { reveal(kernel_k_to_kernel_u); reveal(kernel_ipc_rendezvous_fields); reveal(IommuRootTable::user_view); };
        assert(self.snapshot_k().prc_mp.dom().contains(self.snapshot_k().thr_mp.spec_index(peer_thread_ptr).view().owning_proc)) by {
            reveal(kernel_ipc_rendezvous_fields); reveal(kernel_process_nonlock_fields_unchanged); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, peer_thread_ptr);
        };
        assert({
            &&& ipc_rendezvous_result(self.nonlock_snapshot_u(), cpu_id, endpoint_index, waiting_state, payload) == ipc_rendezvous_result(self.snapshot_u(), cpu_id, endpoint_index, waiting_state, payload)
            &&& self.nonlock_snapshot_u().thread_map[caller_thread_ptr].owning_proc == self.snapshot_u().thread_map[caller_thread_ptr].owning_proc
            &&& self.nonlock_snapshot_u().thread_map[peer_thread_ptr].owning_proc == self.snapshot_u().thread_map[peer_thread_ptr].owning_proc
        }) by { reveal(kernel_k_to_kernel_u); reveal(kernel_k_to_nonlock_kernel_u); reveal(kernel_ipc_rendezvous_fields); };
        let pre_u = self.nonlock_snapshot_u();
        let post_u = kernel_k_to_nonlock_kernel_u(*krnl);
        assert(kernel_u_ipc_rendezvous_changed(pre_u, post_u, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer)) by {
            kernel_ipc_rendezvous_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer, false);
            reveal(kernel_k_to_nonlock_kernel_u);
        };
        assert(kernel_u_ipc_rendezvous_changed(self.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, caller_thread_ptr,
            endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer)) by {
            kernel_ipc_rendezvous_fields_implies_u_step(&self.snapshot_k(), krnl, cpu_id, caller_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, peer_thread_ptr, peer_result, cpu_transfer, pci_transfer, true);
            reveal(kernel_k_to_kernel_u);
        };
        self.end_kernel_step_raw(krnl, lctx);
    }
}
} // verus!
