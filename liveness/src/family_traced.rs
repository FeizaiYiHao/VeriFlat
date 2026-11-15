//! Round 5: the world frames for the syscalls of rounds 1 to 4, `new_endpoint`, `alloc_quota_4k`, `mmap_4k`, and
//! `unmap_4k` (the labels of `traced_label`).
use vstd::prelude::*;
use crate::*;
use crate::trace::*;
use crate::frame::*;
use veriflat_map_4k::*;
use veriflat_syscall_mmap_4k::syscall_mmap_4k::syscall_mmap_4k_spec::*;
use veriflat_syscall_unmap_4k::syscall_unmap_4k::syscall_unmap_4k_spec::*;
use veriflat_syscall_new_thread::syscall_new_endpoint::syscall_new_endpoint_spec::*;
use veriflat_syscall_alloc_quota::syscall_alloc_quota::syscall_alloc_quota_spec::*;

verus! {
/// A traced step keeps every other cpu, and `d` is outside every syscall or inside a traced one before and after it.
pub proof fn traced_step_implies_others_kept(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), traced_label(l), labeled_step(l, u, u2, d),
    ensures
        others_kept(u, u2, d), cpu_outside(u, d) || in_traced(u, d), cpu_outside(u2, d) || in_traced(u2, d),
        unmap_4k_label(l) ==> cpu_outside(u2, d) || in_unmap_4k(u2, d), op_in_step_kept(u, u2, d),
{
    assert forall|x: CpuId| #![trigger cpu_kept(u, u2, x)] index_valid(NUM_CPUS, x) && x != d implies cpu_kept(u, u2, x) by {
        traced_other_step_implies_cpu_slice_unchanged(u, u2, l, d, x);
    };
    reveal(kernel_u_cpu_ownership_wf);
    reveal(thread_pagetable_op_locked);
    match l {
        StepLabel::NewEndpointEnter { slot } => { reveal(new_endpoint_enter_step_pre); reveal(new_endpoint_enter_step); },
        StepLabel::NewEndpointFinish => { reveal(new_endpoint_finish_step_pre); reveal(new_endpoint_finish_step); reveal(kernel_u_new_endpoint_changed); },
        StepLabel::AllocQuota4k { alloc_amount } => { reveal(alloc_quota_4k_step_pre); reveal(kernel_u_only_process_quota_4k_changed); },
        StepLabel::Mmap4kHold { range } => { reveal(mmap_4k_hold_step_pre); reveal(mmap_4k_hold_step); },
        StepLabel::Mmap4kEnter { range, phase } => { reveal(mmap_4k_enter_step_pre); reveal(mmap_4k_enter_step); },
        StepLabel::Mmap4kDirectory => { reveal(mmap_4k_directory_step_pre); reveal(mmap_4k_directory_step); },
        StepLabel::Mmap4kDowngrade => { reveal(mmap_4k_downgrade_step_pre); reveal(mmap_4k_downgrade_step); },
        StepLabel::Mmap4kLeaf => { reveal(mmap_4k_leaf_step_pre); reveal(mmap_4k_leaf_step); },
        StepLabel::Mmap4kExit => { reveal(mmap_4k_exit_step_pre); reveal(mmap_4k_exit_step); },
        StepLabel::Mmap4kRelease => { reveal(mmap_4k_release_step_pre); reveal(mmap_4k_release_step); },
        StepLabel::Unmap4kEnter { range } => { reveal(unmap_4k_enter_step_pre); reveal(unmap_4k_enter_step); },
        StepLabel::Unmap4kLeaf => { reveal(unmap_4k_leaf_step_pre); reveal(unmap_4k_leaf_step); },
        StepLabel::Unmap4kTlbFlush => { reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_tlb_flush_step); reveal(kernel_u_cpu_tlb_cleared); },
        StepLabel::Unmap4kTlbVaFlush => { reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_tlb_va_flush_step); },
        StepLabel::Unmap4kFlushed => { reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_flushed_step); },
        StepLabel::Unmap4kRefund => { reveal(unmap_4k_refund_step_pre); reveal(unmap_4k_refund_step); reveal(kernel_u_container_quota_4k_increased); },
        StepLabel::Unmap4kExit => { reveal(unmap_4k_refund_step_pre); reveal(unmap_4k_exit_step); },
        _ => {},
    }
}

/// A traced step other than endpoint creation changes no container, process, or endpoint lock.
pub proof fn traced_step_implies_object_locks_same(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires traced_label(l), labeled_step(l, u, u2, d), !(l is NewEndpointEnter), !(l is NewEndpointFinish),
    ensures object_locks_same(u, u2),
{
    match l {
        StepLabel::AllocQuota4k { alloc_amount } => { reveal(alloc_quota_4k_step_pre); reveal(kernel_u_only_process_quota_4k_changed); },
        StepLabel::Mmap4kHold { range } => { reveal(mmap_4k_hold_step); },
        StepLabel::Mmap4kEnter { range, phase } => { reveal(mmap_4k_enter_step); },
        StepLabel::Mmap4kDirectory => { reveal(mmap_4k_directory_step); },
        StepLabel::Mmap4kDowngrade => { reveal(mmap_4k_downgrade_step); },
        StepLabel::Mmap4kLeaf => { reveal(mmap_4k_leaf_step); },
        StepLabel::Mmap4kExit => { reveal(mmap_4k_exit_step); },
        StepLabel::Mmap4kRelease => { reveal(mmap_4k_release_step); },
        StepLabel::Unmap4kEnter { range } => { reveal(unmap_4k_enter_step); },
        StepLabel::Unmap4kLeaf => { reveal(unmap_4k_leaf_step); },
        StepLabel::Unmap4kTlbFlush => { reveal(unmap_4k_tlb_flush_step); reveal(kernel_u_cpu_tlb_cleared); },
        StepLabel::Unmap4kTlbVaFlush => { reveal(unmap_4k_tlb_va_flush_step); },
        StepLabel::Unmap4kFlushed => { reveal(unmap_4k_flushed_step); },
        StepLabel::Unmap4kRefund => {
            reveal(unmap_4k_refund_step); reveal(kernel_u_container_quota_4k_increased);
            let ctn = u.thread_map[u.cpu_array[d as int].current_thread->Some_0].owning_container;
            let changed = u.container_map.dom().filter(|c: RwLockContainerPtr| u.container_map[c] != u2.container_map[c]);
            assert forall|c: RwLockContainerPtr| #![trigger u2.container_map[c]] u.container_map.dom().contains(c) implies u2.container_map[c].lock_state == u.container_map[c].lock_state
                && u2.container_map[c].pcid_allocator_lock == u.container_map[c].pcid_allocator_lock && u2.container_map[c].free_pcids == u.container_map[c].free_pcids by {
                if u.container_map[c] != u2.container_map[c] { assert(changed.contains(c)); }
            };
        },
        StepLabel::Unmap4kExit => { reveal(unmap_4k_exit_step); },
        _ => {},
    }
}

/// A traced step gives up no foreign hold: endpoint creation locks only unlocked objects and unlocks only those of `d`.
pub proof fn traced_step_implies_foreign_holds_kept(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), new_endpoint_locks_held(u), traced_label(l), labeled_step(l, u, u2, d),
    ensures foreign_holds_kept(u, u2, d),
{
    match l {
        StepLabel::NewEndpointEnter { slot } => { reveal(new_endpoint_enter_step_pre); reveal(new_endpoint_enter_step); },
        StepLabel::NewEndpointFinish => {
            reveal(new_endpoint_finish_step_pre); reveal(new_endpoint_finish_step); reveal(kernel_u_new_endpoint_changed);
            assert(in_new_endpoint(u, d) && u.cpu_array[d as int] == u.cpu_array[d as int]);
        },
        _ => {
            traced_step_implies_object_locks_same(u, u2, l, d);
            object_locks_same_implies_foreign_holds_kept(u, u2, d);
        },
    }
}

/// A traced step keeps `new_endpoint_locks_held`: rounds 1 and 2 prove it for the pilot labels, and an `unmap_4k` step
/// keeps every other cpu, gives up no foreign hold, and leaves `d` outside endpoint creation.
pub proof fn traced_step_implies_new_endpoint_locks_held_kept(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), new_endpoint_locks_held(u), traced_label(l), labeled_step(l, u, u2, d),
    ensures new_endpoint_locks_held(u2),
{
    if pilot_label(l) { pilot_step_implies_new_endpoint_locks_held(u, u2, l, d); }
    else {
        traced_step_implies_others_kept(u, u2, l, d);
        traced_step_implies_object_locks_same(u, u2, l, d);
        reveal(kernel_u_cpu_ownership_wf);
        assert forall|x: CpuId| #![trigger u2.cpu_array[x as int]] in_new_endpoint(u2, x) implies {
            let cpu = u2.cpu_array[x as int];
            &&& u2.container_map[cpu.owning_container].lock_state == (LockStateU::WriteLocked { writer: x })
            &&& u2.process_map[cpu.current_process->Some_0].lock_state == (LockStateU::WriteLocked { writer: x })
            &&& cur_thread(u2, x).lock_state == (LockStateU::WriteLocked { writer: x })
            &&& edp_idx_valid(cur_thread(u2, x).syscall_progress->Some_0->NewEndpoint_slot)
        } by {
            if x != d {
                assert(cpu_kept(u, u2, x));
                assert(in_new_endpoint(u, x) && u.cpu_array[x as int] == u.cpu_array[x as int]);
            }
        };
    }
}

/// A step that keeps every other cpu and every foreign hold, after which `d` is outside endpoint creation, keeps
/// `new_endpoint_locks_held`.
pub proof fn frame_implies_new_endpoint_locks_held_kept(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), new_endpoint_locks_held(u), others_kept(u, u2, d), foreign_holds_kept(u, u2, d), !in_new_endpoint(u2, d),
    ensures new_endpoint_locks_held(u2),
{
    reveal(kernel_u_cpu_ownership_wf);
    assert forall|x: CpuId| #![trigger u2.cpu_array[x as int]] in_new_endpoint(u2, x) implies {
        let cpu = u2.cpu_array[x as int];
        &&& u2.container_map[cpu.owning_container].lock_state == (LockStateU::WriteLocked { writer: x })
        &&& u2.process_map[cpu.current_process->Some_0].lock_state == (LockStateU::WriteLocked { writer: x })
        &&& cur_thread(u2, x).lock_state == (LockStateU::WriteLocked { writer: x })
        &&& edp_idx_valid(cur_thread(u2, x).syscall_progress->Some_0->NewEndpoint_slot)
    } by {
        assert(cpu_kept(u, u2, x));
        let ux = u.cpu_array[x as int];
        assert(in_new_endpoint(u, x) && u.cpu_array[x as int] == ux);
        assert(u2.container_map[ux.owning_container].lock_state == u.container_map[ux.owning_container].lock_state);
        assert(u2.process_map[ux.current_process->Some_0].lock_state == u.process_map[ux.current_process->Some_0].lock_state);
    };
}
} // verus!
