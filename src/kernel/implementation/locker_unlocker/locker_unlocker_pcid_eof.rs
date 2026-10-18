use vstd::prelude::*;
use crate::*;

verus! {
/// Closes `inv()` after a PCID-allocator write lock or unlock: only the target entry's lock state moved.
pub(super) proof fn pcid_allocator_lock_op_eof(pre: KernelK, post: KernelK, allocator_ptr: RwLockPcidAllocatorPtr)
    requires
        pre.inv(),
        pre.pcid_allc_mp.dom().contains(allocator_ptr),
        post == (KernelK { pcid_allc_mp: post.pcid_allc_mp, ..pre }),
        post.pcid_allc_mp.perms_wf(),
        post.pcid_allc_mp.unchanged_except(&pre.pcid_allc_mp, allocator_ptr),
        post.pcid_allc_mp.spec_index(allocator_ptr).inv(),
        post.pcid_allc_mp.spec_index(allocator_ptr).view() == pre.pcid_allc_mp.spec_index(allocator_ptr).view(),
        post.pcid_allc_mp.spec_index(allocator_ptr).view_rodata() == pre.pcid_allc_mp.spec_index(allocator_ptr).view_rodata(),
        post.pcid_allc_mp.spec_index(allocator_ptr).view_ghost() == pre.pcid_allc_mp.spec_index(allocator_ptr).view_ghost(),
        post.pcid_allc_mp.spec_index(allocator_ptr).being_killed() == pre.pcid_allc_mp.spec_index(allocator_ptr).being_killed(),
    ensures
        post.inv(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post),
{
    assert(pcid_allocator_perms_wf(post.pcid_allc_mp)) by { reveal(pcid_allocator_perms_wf); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.pcid_allc_mp, post.pcid_allc_mp); };
    assert(post.process_management_inv()) by { reveal(container_pcid_allocator_wf); reveal(process_pcid_allocator_wf); };
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_pcid_allocator_wf); };
}

/// Closes `inv()` after `wlock_pcid_needflush`: the entry is write-held and names its holder cpu; every view is unchanged.
pub(super) proof fn wlock_pcid_needflush_eof(pre: KernelK, post: KernelK, cpu_id: CpuId, pcid: Pcid, holder: CpuId)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        pcid_valid(pcid),
        index_valid(NUM_CPUS, holder),
        post == (KernelK { pcid_needflush: post.pcid_needflush, ..pre }),
        post.pcid_needflush.spec_index(cpu_id, pcid).inv(),
        post.pcid_needflush.spec_index(cpu_id, pcid).view().index() == (cpu_id, pcid),
        !pre.pcid_needflush.spec_index(cpu_id, pcid).locked(),
        post.pcid_needflush.spec_index(cpu_id, pcid).view_ghost() == Some(holder),
        post.pcid_needflush.spec_index(cpu_id, pcid).locking_thread() is Write,
        forall|c: CpuId, p: Pcid| #![trigger post.pcid_needflush.spec_index(c, p)] #![trigger pre.pcid_needflush.spec_index(c, p)] index_valid(NUM_CPUS, c) && pcid_valid(p) ==> {
            &&& post.pcid_needflush.spec_index(c, p).view() == pre.pcid_needflush.spec_index(c, p).view()
            &&& ((c != cpu_id || p != pcid) ==> post.pcid_needflush.spec_index(c, p) == pre.pcid_needflush.spec_index(c, p))
        },
    ensures
        post.inv(),
        post.cpu_published[cpu_id as int].owner_cpu() == cpu_id,
{
    assert(post.subsystems_inv()) by { reveal(pcid_needflush_wf); reveal(cpu_published_wf); reveal(KernelK::default_pagetable_wf); };
    assert(post.inv()) by { reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(tlb_wf_spec); };
    assert(post.cpu_published[cpu_id as int].owner_cpu() == cpu_id) by { reveal(cpu_published_wf); };
}

/// Closes `inv()` after `wunlock_pcid_needflush`: the released entry names no holder, and a released active PCID is
/// published with the cpu's current CR3.
pub(super) proof fn wunlock_pcid_needflush_eof(pre: KernelK, post: KernelK, cpu_id: CpuId, pcid: Pcid)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        pcid_valid(pcid),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid != pcid || pre.cpu_published[cpu_id as int].view() == (pre.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, pcid),
        post == (KernelK { pcid_needflush: post.pcid_needflush, ..pre }),
        post.pcid_needflush.spec_index(cpu_id, pcid).inv(),
        !post.pcid_needflush.spec_index(cpu_id, pcid).locked(),
        post.pcid_needflush.spec_index(cpu_id, pcid).view_ghost() is None,
        forall|c: CpuId, p: Pcid| #![trigger post.pcid_needflush.spec_index(c, p)] #![trigger pre.pcid_needflush.spec_index(c, p)] index_valid(NUM_CPUS, c) && pcid_valid(p) ==> {
            &&& post.pcid_needflush.spec_index(c, p).view() == pre.pcid_needflush.spec_index(c, p).view()
            &&& ((c != cpu_id || p != pcid) ==> post.pcid_needflush.spec_index(c, p) == pre.pcid_needflush.spec_index(c, p))
        },
    ensures
        post.inv(),
{
    assert(post.subsystems_inv()) by { reveal(pcid_needflush_wf); reveal(cpu_published_wf); reveal(KernelK::default_pagetable_wf); };
    assert(post.inv()) by { reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(tlb_wf_spec); };
}

/// Closes `inv()` after `mark_pcid_needflush`: the write-held entry's flush flag is set; its lock state and holder are
/// unchanged.
pub(super) proof fn mark_pcid_needflush_eof(pre: KernelK, post: KernelK, lctx: LocalContext, cpu_id: CpuId, pcid: Pcid)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        pcid_valid(pcid),
        typed_lock_maps_aligned(&pre, &lctx),
        typed_lock_map_contains_mode(lctx.pcid_needflush_lock_map(), (cpu_id, pcid), TypedLockMode::Write),
        post == (KernelK { pcid_needflush: post.pcid_needflush, ..pre }),
        post.pcid_needflush.spec_index(cpu_id, pcid).view() == (PcidNeedFlush { needflush: true, ..pre.pcid_needflush.spec_index(cpu_id, pcid).view() }),
        post.pcid_needflush.spec_index(cpu_id, pcid).locking_thread() == pre.pcid_needflush.spec_index(cpu_id, pcid).locking_thread(),
        post.pcid_needflush.spec_index(cpu_id, pcid).view_ghost() == pre.pcid_needflush.spec_index(cpu_id, pcid).view_ghost(),
        post.pcid_needflush.spec_index(cpu_id, pcid).view_rodata() == pre.pcid_needflush.spec_index(cpu_id, pcid).view_rodata(),
        post.pcid_needflush.spec_index(cpu_id, pcid).view().index() == pre.pcid_needflush.spec_index(cpu_id, pcid).view().index(),
        post.pcid_needflush.spec_index(cpu_id, pcid).is_init(),
        post.pcid_needflush.spec_index(cpu_id, pcid).being_killed() == pre.pcid_needflush.spec_index(cpu_id, pcid).being_killed(),
        forall|c: CpuId, p: Pcid| #![trigger post.pcid_needflush.spec_index(c, p)] #![trigger pre.pcid_needflush.spec_index(c, p)] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid)
            ==> post.pcid_needflush.spec_index(c, p) == pre.pcid_needflush.spec_index(c, p),
    ensures
        post.inv(),
{
    assert(post.subsystems_inv()) by { reveal(pcid_needflush_wf); reveal(cpu_published_wf); reveal(KernelK::default_pagetable_wf); };
    assert(post.inv()) by { reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(tlb_wf_spec); };
}
} // verus!
