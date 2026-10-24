use vstd::prelude::*;
use crate::*;

verus! {
/// Closes `inv()` after `wlock_process_unless_killed`: only the target entry's lock state moved.
pub(super) proof fn wlock_process_eof(pre: KernelK, post: KernelK, process_ptr: RwLockProcessPtr, lctx: LocalContext, ret: Option<Tracked<LockPerm>>)
    requires
        pre.inv(),
        post == (KernelK { prc_mp: post.prc_mp, ..pre }),
        post.prc_mp.perms_wf(),
        post.prc_mp.unchanged_except(&pre.prc_mp, process_ptr),
        ret is None ==> post.prc_mp.spec_index(process_ptr) == pre.prc_mp.spec_index(process_ptr),
        ret is Some ==> wlock_ensures(pre.prc_mp.spec_index(process_ptr), post.prc_mp.spec_index(process_ptr), pre.prc_mp.lock_id_by_key(process_ptr), &lctx, ret.unwrap().view()),
    ensures
        post.inv(),
        ret is Some ==> post.prc_mp.spec_index(process_ptr).view().state.view() is Running || post.prc_mp.spec_index(process_ptr).view().state.view() is Zombie,
{
    assert(ret is Some ==> post.prc_mp.spec_index(process_ptr).view().state.view() is Running || post.prc_mp.spec_index(process_ptr).view().state.view() is Zombie) by { process_state_lock_wf_at(pre.prc_mp, process_ptr); };
    assert(process_perms_wf(post.prc_mp)) by { reveal(process_perms_wf); };
    assert(process_invariant_fields_unchanged(pre.prc_mp, post.prc_mp)) by { process_lock_op_preserves_invariant_fields(pre.prc_mp, post.prc_mp, process_ptr); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(process_emptied_tables_wf); };
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_process_invariant_fields(pre, post); };
    assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { reveal(process_thread_wf); };
    assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); };
    assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); };
    assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); };
    assert(process_state_lock_wf(post.prc_mp)) by { reveal(process_state_lock_wf); };
    assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
    assert(post.process_management_inv()) by { process_management_inv_preserved_for_process_invariant_fields(pre, post); };
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { lemma_iommu_root_table_process_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
    assert(process_pci_function_ownership_wf(post.irt.view(), post.prc_mp)) by { lemma_process_pci_function_ownership_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { lemma_iommu_tlb_wf_spec_preserved_for_process_invariant_fields_except_quota_forall(); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { lemma_cpu_dirty_map_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
}

/// Closes `inv()` after `try_wlock_process_and_mark_kill`: the target is write-locked by the killer's thread, marked
/// for the killer, and its state moved to `Killing` unless it is a zombie.
pub(super) proof fn mark_kill_process_eof(pre: KernelK, post: KernelK, pre_lctx: LocalContext, process_ptr: RwLockProcessPtr, killer_process: RwLockProcessPtr, killer_thread: RwLockThreadPtr, killer_info: KillerInfo, marked: bool)
    requires
        pre.inv(),
        pre.prc_mp.dom().contains(process_ptr),
        pre.prc_mp.dom().contains(killer_process),
        killer_held_context(pre, pre_lctx, killer_process, killer_thread, pre_lctx.container_lock_map().dom()),
        killer_info.process == killer_process,
        ({
            let process = pre.prc_mp.spec_index(process_ptr).view_rodata().view();
            ||| process.parent is Some && typed_lock_map_contains_mode(pre_lctx.process_lock_map(), process.parent->Some_0, TypedLockMode::Write)
            ||| {
                &&& process.parent is None
                &&& pre.ctn_mp.spec_index(process.owning_container).view().root_process == process_ptr
                &&& pre.ctn_mp.spec_index(process.owning_container).killer_info() == Some(killer_info)
                &&& typed_lock_map_contains_mode(pre_lctx.container_lock_map(), process.owning_container, TypedLockMode::Write)
            }
        }),
        typed_lock_maps_aligned(&pre, &pre_lctx),
        post == (KernelK { prc_mp: post.prc_mp, ..pre }),
        post.prc_mp.perms_wf(),
        post.prc_mp.unchanged_except(&pre.prc_mp, process_ptr),
        post.prc_mp.spec_index(process_ptr).view() == (Process { state: post.prc_mp.spec_index(process_ptr).view().state, ..pre.prc_mp.spec_index(process_ptr).view() }),
        post.prc_mp.spec_index(process_ptr).view_rodata() == pre.prc_mp.spec_index(process_ptr).view_rodata(),
        post.prc_mp.spec_index(process_ptr).view_ghost() == pre.prc_mp.spec_index(process_ptr).view_ghost(),
        !marked ==> post.prc_mp.spec_index(process_ptr) == pre.prc_mp.spec_index(process_ptr),
        marked ==> {
            &&& !pre.prc_mp.spec_index(process_ptr).being_killed()
            &&& !pre.prc_mp.spec_index(process_ptr).locked()
            &&& post.prc_mp.spec_index(process_ptr).being_killed()
            &&& post.prc_mp.spec_index(process_ptr).killer_info() == Some(killer_info)
            &&& post.prc_mp.spec_index(process_ptr).inv()
            &&& post.prc_mp.spec_index(process_ptr).locking_thread() is Write
            &&& post.prc_mp.spec_index(process_ptr).locking_thread()->Write_thread_id == pre_lctx.thread_id()
            &&& post.prc_mp.spec_index(process_ptr).view().state.view() == if pre.prc_mp.spec_index(process_ptr).view().zombie { pre.prc_mp.spec_index(process_ptr).view().state.view() } else { ProcessState::Killing }
        },
    ensures
        post.inv(),
        marked ==> post.prc_mp.spec_index(process_ptr).view().state.view() == if pre.prc_mp.spec_index(process_ptr).view().zombie { ProcessState::Zombie } else { ProcessState::Killing },
{
    assert(process_perms_wf(post.prc_mp)) by { reveal(process_perms_wf); };
    assert(process_invariant_fields_unchanged(pre.prc_mp, post.prc_mp)) by { process_lock_op_preserves_invariant_fields(pre.prc_mp, post.prc_mp, process_ptr); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(process_emptied_tables_wf); };
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_process_invariant_fields(pre, post); };
    assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { reveal(process_thread_wf); };
    assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by {
        let process = pre.prc_mp.spec_index(process_ptr).view_rodata().view();
        reveal(process_kill_mark_wf);
        pre.prc_mp.typed_lock_map_aligned_write_at(pre_lctx.process_lock_map(), pre_lctx.thread_id(), killer_process);
        if process.parent is Some {
            pre.prc_mp.typed_lock_map_aligned_write_at(pre_lctx.process_lock_map(), pre_lctx.thread_id(), process.parent->Some_0);
        } else {
            pre.ctn_mp.typed_lock_map_aligned_write_at(pre_lctx.container_lock_map(), pre_lctx.thread_id(), process.owning_container);
        }
    };
    assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); };
    assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); };
    assert(process_state_lock_wf(post.prc_mp)) by { reveal(process_state_lock_wf); };
    assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
    assert(post.process_management_inv()) by { process_management_inv_preserved_for_process_invariant_fields(pre, post); };
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { lemma_iommu_root_table_process_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
    assert(process_pci_function_ownership_wf(post.irt.view(), post.prc_mp)) by { lemma_process_pci_function_ownership_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { lemma_iommu_tlb_wf_spec_preserved_for_process_invariant_fields_except_quota_forall(); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { lemma_cpu_dirty_map_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
}

/// Closes `inv()` after `wunlock_process`: the target entry is released; no marked process held by this thread names
/// it as killer or parent.
pub(super) proof fn wunlock_process_eof(pre: KernelK, post: KernelK, pre_lctx: LocalContext, process_ptr: RwLockProcessPtr)
    requires
        pre.inv(),
        pre.prc_mp.dom().contains(process_ptr),
        pre.prc_mp.spec_index(process_ptr).being_killed() == false,
        forall|d: RwLockProcessPtr| #![trigger pre_lctx.process_lock_map().dom().contains(d)] pre_lctx.process_lock_map().dom().contains(d) && pre.prc_mp.spec_index(d).killer_info() is Some
            ==> pre.prc_mp.spec_index(d).killer_info()->Some_0.process != process_ptr && pre.prc_mp.spec_index(d).view_rodata().view().parent != Some(process_ptr),
        forall|c: RwLockContainerPtr| #![trigger pre_lctx.container_lock_map().dom().contains(c)] pre_lctx.container_lock_map().dom().contains(c) && pre.ctn_mp.spec_index(c).killer_info() is Some
            ==> pre.ctn_mp.spec_index(c).killer_info()->Some_0.process != process_ptr,
        pre.prc_mp.spec_index(process_ptr).view().state.view() is Running || pre.prc_mp.spec_index(process_ptr).view().state.view() is Zombie,
        typed_lock_map_contains_mode(pre_lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_maps_aligned(&pre, &pre_lctx),
        post == (KernelK { prc_mp: post.prc_mp, ..pre }),
        post.prc_mp.perms_wf(),
        post.prc_mp.unchanged_except(&pre.prc_mp, process_ptr),
        wunlock_ensures(pre.prc_mp.spec_index(process_ptr), post.prc_mp.spec_index(process_ptr)),
    ensures
        post.inv(),
{
    assert(process_perms_wf(post.prc_mp)) by { reveal(process_perms_wf); };
    assert(process_invariant_fields_unchanged(pre.prc_mp, post.prc_mp)) by { process_lock_op_preserves_invariant_fields(pre.prc_mp, post.prc_mp, process_ptr); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(process_emptied_tables_wf); };
    assert(post.memory_management_inv()) by { memory_management_inv_preserved_for_process_invariant_fields(pre, post); };
    assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { reveal(process_thread_wf); };
    assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); reveal(LockedMap::typed_lock_map_aligned); };
    assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); reveal(LockedMap::typed_lock_map_aligned); };
    assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); reveal(container_kill_mark_wf); reveal(LockedMap::typed_lock_map_aligned); };
    assert(process_state_lock_wf(post.prc_mp)) by { reveal(process_state_lock_wf); };
    assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
    assert(post.process_management_inv()) by { process_management_inv_preserved_for_process_invariant_fields(pre, post); };
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { lemma_iommu_root_table_process_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
    assert(process_pci_function_ownership_wf(post.irt.view(), post.prc_mp)) by { lemma_process_pci_function_ownership_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { lemma_iommu_tlb_wf_spec_preserved_for_process_invariant_fields_except_quota_forall(); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { lemma_cpu_dirty_map_wf_preserved_for_process_invariant_fields_except_quota_forall(); };
}
} // verus!
