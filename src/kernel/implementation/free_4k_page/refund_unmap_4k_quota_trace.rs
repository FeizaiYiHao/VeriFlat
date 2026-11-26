use vstd::prelude::*;
use crate::*;

verus! {
/// While the caller write-holds its cpu and thread, write-holds the thread's process unless the thread is not dangling, its
/// thread changes only pending 4K quota, and its held cpus and processes keep their `entry` objects, `krnl` projects the
/// caller's held objects and the thread's process as each refund step requires.
pub proof fn refund_unmap_4k_step_pre_from_k(krnl: &KernelK, entry: &KernelK, lctx: &LocalContext, held: &LocalContext, thrd_ptr: RwLockThreadPtr)
    requires
        krnl.inv(),
        entry.inv(),
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_maps_aligned(entry, held),
        typed_lock_maps_unchanged(held, lctx),
        lctx.cpu_id() == held.cpu_id(),
        index_valid(NUM_CPUS, held.cpu_id()),
        typed_lock_map_contains_mode(held.cpu_lock_map(), held.cpu_id(), TypedLockMode::Write),
        typed_lock_map_contains_mode(held.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(held.process_lock_map(), entry.thrd_mp.spec_index(thrd_ptr).view().owning_proc, TypedLockMode::Write) || !thread_is_dangling(entry.thrd_mp.spec_index(thrd_ptr)),
        entry.thrd_mp.dom().contains(thrd_ptr),
        krnl.thrd_mp.dom().contains(thrd_ptr),
        krnl.thrd_mp.spec_index(thrd_ptr).view() == (Thread { direct_free_quota_pending_4k: krnl.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k,
            indirect_free_quota_pending_4k: krnl.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k, ..entry.thrd_mp.spec_index(thrd_ptr).view() }),
        held_processes_unchanged(entry.prc_mp, krnl.prc_mp, held),
        held_cpus_unchanged(entry.cpu_arr, krnl.cpu_arr, held),
        krnl.cpu_op.view().view()[held.cpu_id() as int] == entry.cpu_op.view().view()[held.cpu_id() as int],
    ensures
        ({
            let u = kernel_k_to_kernel_u(*krnl);
            let entry_u = kernel_k_to_kernel_u(*entry);
            let thread = entry.thrd_mp.spec_index(thrd_ptr).view();
            &&& u.cpu_array[held.cpu_id() as int].lock_state is WriteLocked
            &&& u.cpu_array[held.cpu_id() as int].current_thread == entry.cpu_arr.spec_index(held.cpu_id()).view().view().view().current_thread
            &&& u.thread_map.dom().contains(thrd_ptr)
            &&& u.thread_map[thrd_ptr].lock_state is WriteLocked
            &&& u.thread_map[thrd_ptr].owning_container == thread.owning_container
            &&& u.thread_map[thrd_ptr].owning_proc == thread.owning_proc
            &&& u.thread_map[thrd_ptr].syscall_progress == thread.syscall_progress.view()
            &&& u.process_map.dom().contains(thread.owning_proc)
            &&& typed_lock_map_contains_mode(held.process_lock_map(), thread.owning_proc, TypedLockMode::Write) ==> u.process_map[thread.owning_proc].lock_state is WriteLocked
            &&& !entry.prc_mp.spec_index(thread.owning_proc).view().zombie && typed_lock_map_contains_mode(held.pagetable_lock_map(), entry.prc_mp.spec_index(thread.owning_proc).view().pagetable, TypedLockMode::Write) ==> {
                &&& u.process_map[thread.owning_proc].pagetable is Some
                &&& u.process_map[thread.owning_proc].pagetable->Some_0.lock_state is WriteLocked
            }
            &&& !entry.prc_mp.spec_index(thread.owning_proc).view().zombie && typed_lock_map_contains_mode(held.pagetable_lock_map(), entry.prc_mp.spec_index(thread.owning_proc).view().pagetable, TypedLockMode::Read) ==> {
                &&& u.process_map[thread.owning_proc].pagetable is Some
                &&& u.process_map[thread.owning_proc].pagetable->Some_0.lock_state is ReadLocked
            }
            &&& typed_lock_map_contains_mode(held.container_lock_map(), thread.owning_container, TypedLockMode::Write) ==> {
                &&& u.container_map.dom().contains(thread.owning_container)
                &&& u.container_map[thread.owning_container].lock_state is WriteLocked
            }
            &&& u.cpu_array[held.cpu_id() as int] == entry_u.cpu_array[held.cpu_id() as int]
            &&& forall|p: RwLockProcessPtr| #![trigger held.process_lock_map().dom().contains(p)] held.process_lock_map().dom().contains(p) ==> {
                &&& u.process_map.dom().contains(p)
                &&& u.process_map[p].lock_state == entry_u.process_map[p].lock_state
                &&& u.process_map[p].killed == entry_u.process_map[p].killed
                &&& u.process_map[p].owning_container == entry_u.process_map[p].owning_container
            }
        }),
{
    if !typed_lock_map_contains_mode(held.process_lock_map(), entry.thrd_mp.spec_index(thrd_ptr).view().owning_proc, TypedLockMode::Write) {
        process_thread_wf_thread_at(entry.prc_mp, entry.thrd_mp, thrd_ptr); process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr);
    }
    write_held_context_implies_projected_context_write_locked(krnl, lctx, held.cpu_id(), entry.thrd_mp.spec_index(thrd_ptr).view().owning_proc, thrd_ptr, None);
    kernel_cpu_projection_at(krnl, held.cpu_id()); kernel_cpu_projection_at(entry, held.cpu_id());
    entry.prc_mp.typed_lock_map_aligned_held_in_dom(held.process_lock_map(), held.thread_id()); broadcast use kernel_process_lock_state_projection_at;
    let owner_table = entry.prc_mp.spec_index(entry.thrd_mp.spec_index(thrd_ptr).view().owning_proc).view().pagetable;
    if typed_lock_map_contains_mode(lctx.pagetable_lock_map(), owner_table, TypedLockMode::Read) {
        krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), owner_table); kernel_process_projection_at(krnl, entry.thrd_mp.spec_index(thrd_ptr).view().owning_proc);
    }
}

/// The refund steps `steps[start + k]` taken from the refund snapshots `refunds[k]`, each of which keeps what
/// `refund_unmap_4k_step_pre_from_k` asks of `entry` and `held`, project the caller's held objects and the thread's process
/// as each refund step requires, for the first `count` of them.
pub proof fn refund_unmap_4k_steps_from_k(steps: Seq<KernelStep>, start: int, refunds: Seq<KernelK>, entry: &KernelK, held: &LocalContext, thrd_ptr: RwLockThreadPtr, count: int)
    requires
        0 <= start,
        0 <= count <= refunds.len(),
        start + refunds.len() <= steps.len(),
        entry.inv(),
        typed_lock_maps_aligned(entry, held),
        index_valid(NUM_CPUS, held.cpu_id()),
        typed_lock_map_contains_mode(held.cpu_lock_map(), held.cpu_id(), TypedLockMode::Write),
        typed_lock_map_contains_mode(held.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(held.process_lock_map(), entry.thrd_mp.spec_index(thrd_ptr).view().owning_proc, TypedLockMode::Write) || !thread_is_dangling(entry.thrd_mp.spec_index(thrd_ptr)),
        entry.thrd_mp.dom().contains(thrd_ptr),
        forall|k: int| #![trigger refunds[k]] 0 <= k < refunds.len() ==> {
            &&& steps[start + k].old_u == kernel_k_to_kernel_u(refunds[k])
            &&& kernel_u_container_quota_4k_increased(steps[start + k].old_u, steps[start + k].new_u, entry.thrd_mp.spec_index(thrd_ptr).view().owning_container)
            &&& refunds[k].inv()
            &&& typed_lock_maps_aligned(&refunds[k], held)
            &&& refunds[k].thrd_mp.dom().contains(thrd_ptr)
            &&& refunds[k].thrd_mp.spec_index(thrd_ptr).view() == (Thread { direct_free_quota_pending_4k: refunds[k].thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_4k,
                indirect_free_quota_pending_4k: refunds[k].thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_4k, ..entry.thrd_mp.spec_index(thrd_ptr).view() })
            &&& held_processes_unchanged(entry.prc_mp, refunds[k].prc_mp, held)
            &&& held_cpus_unchanged(entry.cpu_arr, refunds[k].cpu_arr, held)
            &&& refunds[k].cpu_op.view().view()[held.cpu_id() as int] == entry.cpu_op.view().view()[held.cpu_id() as int]
        },
    ensures
        forall|j: int| #![trigger steps[j]] start <= j < start + count ==> {
            let old_u = steps[j].old_u;
            let thread = entry.thrd_mp.spec_index(thrd_ptr).view();
            &&& kernel_u_container_quota_4k_increased(old_u, steps[j].new_u, thread.owning_container)
            &&& old_u.cpu_array[held.cpu_id() as int].lock_state is WriteLocked
            &&& old_u.cpu_array[held.cpu_id() as int].current_thread == entry.cpu_arr.spec_index(held.cpu_id()).view().view().view().current_thread
            &&& old_u.thread_map.dom().contains(thrd_ptr)
            &&& old_u.thread_map[thrd_ptr].lock_state is WriteLocked
            &&& old_u.thread_map[thrd_ptr].owning_container == thread.owning_container
            &&& old_u.thread_map[thrd_ptr].owning_proc == thread.owning_proc
            &&& old_u.thread_map[thrd_ptr].syscall_progress == thread.syscall_progress.view()
            &&& old_u.process_map.dom().contains(thread.owning_proc)
            &&& typed_lock_map_contains_mode(held.process_lock_map(), thread.owning_proc, TypedLockMode::Write) ==> old_u.process_map[thread.owning_proc].lock_state is WriteLocked
            &&& !entry.prc_mp.spec_index(thread.owning_proc).view().zombie && typed_lock_map_contains_mode(held.pagetable_lock_map(), entry.prc_mp.spec_index(thread.owning_proc).view().pagetable, TypedLockMode::Write) ==> {
                &&& old_u.process_map[thread.owning_proc].pagetable is Some
                &&& old_u.process_map[thread.owning_proc].pagetable->Some_0.lock_state is WriteLocked
            }
            &&& !entry.prc_mp.spec_index(thread.owning_proc).view().zombie && typed_lock_map_contains_mode(held.pagetable_lock_map(), entry.prc_mp.spec_index(thread.owning_proc).view().pagetable, TypedLockMode::Read) ==> {
                &&& old_u.process_map[thread.owning_proc].pagetable is Some
                &&& old_u.process_map[thread.owning_proc].pagetable->Some_0.lock_state is ReadLocked
            }
            &&& typed_lock_map_contains_mode(held.container_lock_map(), thread.owning_container, TypedLockMode::Write) ==> {
                &&& old_u.container_map.dom().contains(thread.owning_container)
                &&& old_u.container_map[thread.owning_container].lock_state is WriteLocked
            }
            &&& old_u.cpu_array[held.cpu_id() as int] == kernel_k_to_kernel_u(*entry).cpu_array[held.cpu_id() as int]
            &&& forall|p: RwLockProcessPtr| #![trigger held.process_lock_map().dom().contains(p)] held.process_lock_map().dom().contains(p) ==> {
                &&& old_u.process_map.dom().contains(p)
                &&& old_u.process_map[p].lock_state == kernel_k_to_kernel_u(*entry).process_map[p].lock_state
                &&& old_u.process_map[p].killed == kernel_k_to_kernel_u(*entry).process_map[p].killed
                &&& old_u.process_map[p].owning_container == kernel_k_to_kernel_u(*entry).process_map[p].owning_container
            }
        },
    decreases count,
{
    if count > 0 {
        refund_unmap_4k_steps_from_k(steps, start, refunds, entry, held, thrd_ptr, count - 1);
        refund_unmap_4k_step_pre_from_k(&refunds[count - 1], entry, held, held, thrd_ptr);
    }
}
} // verus!
