use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_retire_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_retire_eof_memory::kill_retire_eof_memory;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_retire_eof_process::{kill_retire_eof_container_relations, kill_retire_eof_iommu, kill_retire_eof_process_relations, kill_retire_eof_tlb};
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_retire_eof_tree::kill_retire_eof_tree;

verus! {
/// The retired zombie, its tables, and its pages returned to its container's 4K allocator keep the kernel invariant.
pub(super) proof fn kill_retire_eof(
    pre: KernelK, post: KernelK, lctx: LocalContext, cpu_id: CpuId, target: RwLockProcessPtr, parent_ptr: RwLockProcessPtr,
    container_ptr: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_retire_transition(pre, post, cpu_id, target, parent_ptr, container_ptr, allocator_ptr),
        page_array_wf(post.pg_arr),
        container_perms_wf(post.ctn_mp),
        process_perms_wf(post.prc_mp),
        pagetable_perms_wf(post.pt_mp),
        iommu_table_perms_wf(post.it_mp),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_ptr).wf(),
        pre.prc_mp.typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.process_lock_map(), target, TypedLockMode::Write),
        forall|d: RwLockProcessPtr| #![trigger lctx.process_lock_map().dom().contains(d)] lctx.process_lock_map().dom().contains(d) && pre.prc_mp.spec_index(d).killer_info() is Some
            ==> pre.prc_mp.spec_index(d).killer_info()->Some_0.process != target && pre.prc_mp.spec_index(d).view_rodata().view().owning_container == container_ptr,
    ensures post.inv(),
{
    kill_retire_eof_memory(pre, post, cpu_id, target, parent_ptr, container_ptr, allocator_ptr);
    kill_retire_eof_container_relations(pre, post, cpu_id, target, parent_ptr, container_ptr, allocator_ptr);
    kill_retire_eof_process_relations(pre, post, lctx, cpu_id, target, parent_ptr, container_ptr, allocator_ptr);
    kill_retire_eof_iommu(pre, post, cpu_id, target, parent_ptr, container_ptr, allocator_ptr);
    kill_retire_eof_tlb(pre, post, cpu_id, target, parent_ptr, container_ptr, allocator_ptr);
    kill_retire_eof_tree(pre, post, cpu_id, target, parent_ptr, container_ptr, allocator_ptr);
}
} // verus!
