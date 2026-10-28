use vstd::prelude::*;
use crate::*;

verus! {
/// While the caller write-holds its cpu, thread, and process, its thread changes only pending 4K quota, and its held
/// cpus and processes keep their `entry` objects, `krnl` projects the caller's held objects as each refund step requires.
pub proof fn refund_unmap_4k_step_pre_from_k(krnl: &KernelK, entry: &KernelK, lctx: &LocalContext, held: &LocalContext, thread_ptr: RwLockThreadPtr)
    requires
        typed_lock_maps_aligned(krnl, lctx),
        typed_lock_maps_aligned(entry, held),
        typed_lock_maps_unchanged(held, lctx),
        lctx.cpu_id() == held.cpu_id(),
        index_valid(NUM_CPUS, held.cpu_id()),
        typed_lock_map_contains_mode(held.cpu_lock_map(), held.cpu_id(), TypedLockMode::Write),
        typed_lock_map_contains_mode(held.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(held.process_lock_map(), entry.thr_mp.spec_index(thread_ptr).view().owning_proc, TypedLockMode::Write),
        entry.thr_mp.dom().contains(thread_ptr),
        krnl.thr_mp.dom().contains(thread_ptr),
        krnl.thr_mp.spec_index(thread_ptr).view() == (Thread { direct_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k,
            indirect_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..entry.thr_mp.spec_index(thread_ptr).view() }),
        held_processes_unchanged(entry.prc_mp, krnl.prc_mp, held),
        held_cpus_unchanged(entry.cpu_arr, krnl.cpu_arr, held),
        krnl.cpu_op.view().view()[held.cpu_id() as int] == entry.cpu_op.view().view()[held.cpu_id() as int],
    ensures
        ({
            let u = kernel_k_to_kernel_u(*krnl);
            let entry_u = kernel_k_to_kernel_u(*entry);
            let thread = entry.thr_mp.spec_index(thread_ptr).view();
            &&& u.cpu_array[held.cpu_id() as int].lock_state is WriteLocked
            &&& u.cpu_array[held.cpu_id() as int].current_thread == entry.cpu_arr.spec_index(held.cpu_id()).view().view().view().current_thread
            &&& u.thread_map.dom().contains(thread_ptr)
            &&& u.thread_map[thread_ptr].lock_state is WriteLocked
            &&& u.thread_map[thread_ptr].owning_container == thread.owning_container
            &&& u.thread_map[thread_ptr].owning_proc == thread.owning_proc
            &&& u.thread_map[thread_ptr].syscall_progress == thread.syscall_progress.view()
            &&& u.process_map.dom().contains(thread.owning_proc)
            &&& u.process_map[thread.owning_proc].lock_state is WriteLocked
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
    kernel_write_held_context_projection(krnl, lctx, held.cpu_id(), entry.thr_mp.spec_index(thread_ptr).view().owning_proc, thread_ptr, None);
    kernel_cpu_projection_at(krnl, held.cpu_id()); kernel_cpu_projection_at(entry, held.cpu_id());
    entry.prc_mp.typed_lock_map_aligned_held_in_dom(held.process_lock_map(), held.thread_id()); broadcast use kernel_process_lock_state_projection_at;
    let owner_table = entry.prc_mp.spec_index(entry.thr_mp.spec_index(thread_ptr).view().owning_proc).view().pagetable;
    if typed_lock_map_contains_mode(lctx.pagetable_lock_map(), owner_table, TypedLockMode::Read) {
        krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), owner_table); kernel_process_projection_at(krnl, entry.thr_mp.spec_index(thread_ptr).view().owning_proc);
    }
}
} // verus!
