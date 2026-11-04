//! Per-key and per-map K->U lemmas of the new-thread finish steps.
use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal};
use crate::*;

verus! {
/// Thread publication projects the new thread to its initial unlocked scheduled state.
pub proof fn kernel_new_thread_fields_implies_u_new_thread_entry(
    pre: &KernelK, post: &KernelK, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, cpu_id: CpuId,
    new_thrd_ptr: RwLockThreadPtr, initial_regs: Registers, ep_ptr: Option<RwLockEndpointPtr>, staging_progress: Option<SyscallProgress>,
)
    requires
        kernel_new_thread_fields(pre, post, prc_ptr, thrd_ptr, ctn_ptr, cpu_id, new_thrd_ptr, initial_regs, ep_ptr, staging_progress),
        post.thrd_mp.spec_index(new_thrd_ptr).locking_thread() is None,
    ensures
        kernel_k_to_kernel_u(*post).thread_map.spec_index(new_thrd_ptr) == (ThreadU {
            lock_state: LockStateU::Unlocked, state: ThreadState::SCHEDULED { cpu_id }, caller: None, callee: None, owning_container: ctn_ptr,
            owning_proc: prc_ptr, last_cpu: cpu_id, quota_4k: 0, quota_2m: 0, quota_1g: 0,
            endpoint_descriptors: Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat, |i: int| if i == 0 { ep_ptr } else { None }),
            blocking_endpoint_ptr: None, ipc_payload: IPCPayLoad::Empty, error_code: None, trap_frame: Some(initial_regs), syscall_progress: None,
            killed: false,
        }),
{
    reveal(kernel_new_thread_fields); kernel_thread_projection_at(post, new_thrd_ptr);
    assert_seqs_equal!(kernel_k_to_kernel_u(*post).thread_map.spec_index(new_thrd_ptr).endpoint_descriptors == Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat, |i: int| if i == 0 { ep_ptr } else { None }));
}

/// Read-mode new-container finish projects to the child root process recording the new thread, with the child and the parent
/// process and the child's page table unlocked and the parent's page table released to `lock`, its remaining hold; both page
/// tables take their window lock states from `post`.
pub proof fn kernel_new_thread_fields_and_parent_unlocks_source_runlocked_implies_u_process_map(
    pre: &KernelK, post: &KernelK, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, cpu_id: CpuId,
    new_thrd_ptr: RwLockThreadPtr, initial_regs: Registers, ep_ptr: Option<RwLockEndpointPtr>, source: RwLockProcessPtr,
)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        pre.prc_mp.spec_index(prc_ptr).view().iommu_table is None,
        source != prc_ptr && pre.prc_mp.dom().contains(source) && !pre.prc_mp.spec_index(source).view().zombie && !pre.prc_mp.spec_index(prc_ptr).view().zombie,
        kernel_new_thread_fields(pre, post, prc_ptr, thrd_ptr, ctn_ptr, cpu_id, new_thrd_ptr, initial_regs, ep_ptr, None),
        pre.thrd_mp.spec_index(thrd_ptr).view().owning_proc == source,
        forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)]
            pre.prc_mp.dom().contains(p) ==> if p == prc_ptr || source == p { post.prc_mp.spec_index(p).locking_thread() is None } else { post.prc_mp.spec_index(p).locking_thread() == pre.prc_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) ==> if p == pre.prc_mp.spec_index(prc_ptr).view().pagetable { post.pt_mp.spec_index(p).locking_thread() is None }
                else if p == pre.prc_mp.spec_index(source).view().pagetable { !(post.pt_mp.spec_index(p).locking_thread() is Write) }
                else { post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)]
            pre.it_mp.dom().contains(p) ==> post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread(),
    ensures
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let post_u = kernel_k_to_kernel_u(*post);
            let mode = LockStateU::Unlocked;
            let lock = post_u.process_map[source].pagetable->Some_0.lock_state;
            let source_windows = whole_pagetable(post.pt_mp, post.pt_lower.view(), pre.prc_mp.spec_index(source).view().pagetable).lower.pagetable_window_locks;
            let child_windows = whole_pagetable(post.pt_mp, post.pt_lower.view(), pre.prc_mp.spec_index(prc_ptr).view().pagetable).lower.pagetable_window_locks;
            let unlocked = old_u.process_map.insert(source, ProcessU {
                lock_state: mode, pagetable: Some(PageTableU { lock_state: lock, pagetable_window_locks: source_windows, ..old_u.process_map[source].pagetable->Some_0 }),
                ..old_u.process_map[source]
            }).insert(prc_ptr, ProcessU {
                lock_state: mode, pagetable: Some(PageTableU { lock_state: mode, pagetable_window_locks: child_windows, ..old_u.process_map[prc_ptr].pagetable->Some_0 }),
                iommu_table: None, ..old_u.process_map[prc_ptr]
            });
            let process = unlocked.spec_index(prc_ptr);
            post_u.process_map == unlocked.insert(prc_ptr, ProcessU { owned_threads: process.owned_threads.push(new_thrd_ptr), ..process })
        }),
{
    reveal(kernel_new_thread_fields); kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let old_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let mode = LockStateU::Unlocked;
    let lock = post_u.process_map[source].pagetable->Some_0.lock_state;
    let source_windows = whole_pagetable(post.pt_mp, post.pt_lower.view(), pre.prc_mp.spec_index(source).view().pagetable).lower.pagetable_window_locks;
    let child_windows = whole_pagetable(post.pt_mp, post.pt_lower.view(), pre.prc_mp.spec_index(prc_ptr).view().pagetable).lower.pagetable_window_locks;
    let unlocked = old_u.process_map.insert(source, ProcessU {
        lock_state: mode, pagetable: Some(PageTableU { lock_state: lock, pagetable_window_locks: source_windows, ..old_u.process_map[source].pagetable->Some_0 }),
        ..old_u.process_map[source]
    }).insert(prc_ptr, ProcessU {
        lock_state: mode, pagetable: Some(PageTableU { lock_state: mode, pagetable_window_locks: child_windows, ..old_u.process_map[prc_ptr].pagetable->Some_0 }),
        iommu_table: None, ..old_u.process_map[prc_ptr]
    });
    let process = unlocked.spec_index(prc_ptr);
    assert_maps_equal!(post_u.process_map, unlocked.insert(prc_ptr, ProcessU { owned_threads: process.owned_threads.push(new_thrd_ptr), ..process }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); }
        reveal(process_pagetable_match); reveal(process_iommu_table_match); reveal(kernel_pagetable_nonlock_fields_unchanged);
        assert(post.prc_mp.spec_index(prc_ptr).view().pagetable == pre.prc_mp.spec_index(prc_ptr).view().pagetable);
        assert(post.prc_mp.spec_index(source).view().pagetable == pre.prc_mp.spec_index(source).view().pagetable);
    });
}

} // verus!
