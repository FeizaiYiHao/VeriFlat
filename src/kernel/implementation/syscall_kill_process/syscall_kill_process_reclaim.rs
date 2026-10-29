use vstd::prelude::*;
use crate::*;
use super::syscall_kill_process_spec::*;
use super::syscall_kill_process_trace::*;
use super::syscall_kill_process_walk::*;
use super::syscall_kill_process_reclaim_release::*;
use super::syscall_kill_process_retire::kill_retire_target;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_reclaim_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_reclaim_eof::*;

verus! {
/// Reclaim the empty target and retire it, walking its parent again; the parent is returned. Its PCI functions go to the
/// killer's process; a live target then has its memory, PCID, and quota reclaimed and becomes a zombie.
pub(crate) fn kill_reclaim_target(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&mut Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
    Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
) -> (parent: RwLockProcessPtr)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        kill_walk_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, None, KillStage::Walk, *cpu_perm, *process_perm, *thread_perm, *old(chain_perms)),
        0 < chain.len(),
        target == chain[chain.len() - 1],
        old(krnl).prc_mp.spec_index(target).view().children.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        scope is Subtree || 1 < chain.len(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_walk_state(*final(krnl), *final(lctx), cpu_id, scope, process_ptr, thread_ptr, chain.drop_last(), None, KillStage::Walk, *cpu_perm, *process_perm, *thread_perm, *final(chain_perms)),
        parent == if chain.len() == 1 { process_ptr } else { chain[chain.len() - 2] },
        chain.len() > 1 ==> parent != process_ptr,
        scope is Subtree ==> final(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set.view().len() < old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set.view().len(),
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
            &&& final(krnl).ctn_mp.dom().contains(c)
            &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
            &&& final(krnl).ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
            &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
            &&& c != scope->Container_container ==> final(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes
            &&& final(krnl).ctn_mp.spec_index(c).view().children == old(krnl).ctn_mp.spec_index(c).view().children
        },
        scope is Container ==> final(krnl).ctn_mp.spec_index(scope->Container_container).view_ghost().owned_processes.view() == old(krnl).ctn_mp.spec_index(scope->Container_container).view_ghost().owned_processes.view().remove(target),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view(),
{
    kill_reassign_functions(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, Ghost(chain), Tracked(&*chain_perms), Tracked(cpu_perm),
        Tracked(process_perm), Tracked(thread_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    proof { process_perms_wf_map(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, target); }
    let zombie = {
        let tracked target_perm = chain_perms.tracked_borrow(target);
        krnl.prc_mp.borrow_typed(target, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(target_perm)).zombie
    };
    if zombie {
        kill_retire_zombie(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, Ghost(chain), Tracked(&*chain_perms), Tracked(cpu_perm),
            Tracked(process_perm), Tracked(thread_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    } else {
        kill_reclaim_live(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, Ghost(chain), Tracked(&*chain_perms), Tracked(cpu_perm),
            Tracked(process_perm), Tracked(thread_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    }
    let parent = kill_retire_target(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, Ghost(chain), Tracked(&mut *chain_perms),
        Tracked(cpu_perm), Tracked(process_perm), Tracked(thread_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    proof { vstd::set::lemma_set_remove_len(old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set.view(), target); }
    parent
}

/// Hand every PCI function of the empty target to the killer's process under the root-table lock and, for a target with an
/// IOMMU table, that table's write lock: every function the target owns is detached and handed to the killer's process,
/// and the table drops its DID, invalidated once. A target owning no function records no step.
pub(crate) fn kill_reassign_functions(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
    Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        kill_walk_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, None, KillStage::Walk, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
        0 < chain.len(),
        target == chain[chain.len() - 1],
        old(krnl).prc_mp.spec_index(target).view().children.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        old(steps).view().len() <= final(steps).view().len(),
        kill_walk_state(*final(krnl), *final(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, None, KillStage::Walk, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
        final(krnl).prc_mp.spec_index(target).view() == old(krnl).prc_mp.spec_index(target).view(),
        final(krnl).prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
        final(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set,
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
            &&& final(krnl).ctn_mp.dom().contains(c)
            &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
            &&& final(krnl).ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
            &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes
            &&& final(krnl).ctn_mp.spec_index(c).view().children == old(krnl).ctn_mp.spec_index(c).view().children
        },
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
{
    let ghost before = *krnl;
    let ghost before_lctx = *lctx;
    let ghost before_steps = steps.view();
    proof { process_perms_wf_map(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, target); process_iommu_table_match_process_at(krnl.prc_mp, krnl.it_mp, target); }
    let iommu_table = {
        let tracked target_perm = chain_perms.tracked_borrow(target);
        krnl.prc_mp.borrow_typed(target, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(target_perm)).iommu_table
    };
    let ghost did = match iommu_table { Some(t) => krnl.it_mp.spec_index(t).view().did, None => None };
    let Tracked(irt_perm) = krnl.wlock_iommu_root_table(Tracked(&mut *lctx));
    let found = kill_reassign_find_owned(&krnl.irt, target, Tracked(&irt_perm));
    if found.is_some() {
        match iommu_table {
            Some(it) => {
                let Tracked(iommu_perm) = krnl.wlock_iommu_table(it, Tracked(&mut *lctx));
                let ghost locked = *krnl;
                iommu_root_table_reassign_detach_all(&mut krnl.irt, &mut krnl.iommu_tlb, &mut krnl.it_mp, it, process_ptr, Ghost(locked), Tracked(&*lctx), Tracked(&irt_perm), Tracked(&iommu_perm));
                proof {
                    assert(locked.it_mp.spec_index(it).view().did matches Some(d) ==> krnl.iommu_tlb.spec_index(d).tlb_4k() =~= Map::empty() && krnl.iommu_tlb.spec_index(d).tlb_2m() =~= Map::empty() && krnl.iommu_tlb.spec_index(d).tlb_1g() =~= Map::empty()) by {
                        iommu_root_table_process_wf_table_at(locked.irt.view(), locked.prc_mp, locked.it_mp, it);
                    };
                    process_perms_wf_map(krnl.prc_mp);
                    let target_ghost = krnl.prc_mp.spec_index(target).view_ghost();
                    let owner_ghost = krnl.prc_mp.spec_index(process_ptr).view_ghost();
                    krnl.prc_mp.update_ghost(target, ProcessGhost { owned_pci_functions: Ghost(Set::empty()), ..target_ghost });
                    krnl.prc_mp.update_ghost(process_ptr, ProcessGhost { owned_pci_functions: Ghost(owner_ghost.owned_pci_functions.view().union(target_ghost.owned_pci_functions.view())), ..owner_ghost });
                    assert(krnl.prc_mp.typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
                    assert(kill_reassign_eof_transition_framing(locked, *krnl, target, process_ptr, iommu_table)) by { reveal(kill_reassign_eof_transition_framing); };
                    assert(krnl.it_mp.spec_index(it).view().leaves_present()) by { reveal(kill_reassign_eof_transition_framing); };
                    kill_reassign_eof(locked, *krnl, target, process_ptr, iommu_table);
                }
                krnl.wunlock_iommu_table(it, Tracked(&mut *lctx), Tracked(iommu_perm));
            },
            None => {
                let ghost locked = *krnl;
                iommu_root_table_reassign_owned(&mut krnl.irt, target, process_ptr, Tracked(&*lctx), Tracked(&irt_perm));
                proof {
                    process_perms_wf_map(krnl.prc_mp);
                    let target_ghost = krnl.prc_mp.spec_index(target).view_ghost();
                    let owner_ghost = krnl.prc_mp.spec_index(process_ptr).view_ghost();
                    krnl.prc_mp.update_ghost(target, ProcessGhost { owned_pci_functions: Ghost(Set::empty()), ..target_ghost });
                    krnl.prc_mp.update_ghost(process_ptr, ProcessGhost { owned_pci_functions: Ghost(owner_ghost.owned_pci_functions.view().union(target_ghost.owned_pci_functions.view())), ..owner_ghost });
                    assert(krnl.prc_mp.typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
                    assert(kill_reassign_eof_transition_framing(locked, *krnl, target, process_ptr, iommu_table)) by { reveal(kill_reassign_eof_transition_framing); };
                    kill_reassign_eof(locked, *krnl, target, process_ptr, iommu_table);
                }
            },
        }
    }
    krnl.wunlock_iommu_root_table(Tracked(&mut *lctx), Tracked(irt_perm));
    let ghost after = *krnl;
    proof {
        if found is Some {
            let w = found->Some_0;
            kill_step_pre_from_k(&before, &before_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Walk, scope); kill_reassign_pre_from_k(&before, target);
            assert(before.prc_mp.spec_index(target).view_ghost().owned_pci_functions.view().contains(w)) by { process_pci_function_ownership_wf_at(before.irt.view(), before.prc_mp, w, target); };
            reveal(kill_reassign_eof_transition_framing);
            kernel_process_functions_reassigned_implies_u_step(&before, &after, target, process_ptr, iommu_table, did);
            kill_reassign_step_from_k(&before, &after, cpu_id, process_ptr, target, iommu_table, did);
            assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
            krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
            kill_trace_push(&*steps, before_steps, start, pre, kernel_k_to_kernel_u(before), kernel_k_to_kernel_u(after), cpu_id, ctx);
        } else {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&before, &after)) by {
                broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
            };
            assert(kernel_endpoint_nonlock_fields_unchanged(before.ep_mp, after.ep_mp)) by { broadcast use kernel_endpoint_nonlock_fields_unchanged_for_equal; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&before, &after)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            kernel_restored_locks_implies_u_eq(&before, &after, cpu_id, None, None, None, None, None);
            assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
            krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
            kill_reassign_none_eof(before.irt.view(), before.prc_mp, target);
        }
    }
}

/// Scan every B/D/F under the held root-table lock for a function `target` owns; returns the first one, or none when
/// `target` owns no function.
fn kill_reassign_find_owned(irt: &IommuRootTableLock, target: RwLockProcessPtr, Tracked(irt_perm): Tracked<&LockPerm>) -> (ret: Option<PciBdf>)
    requires
        irt.inv(),
        irt_perm.state() is WriteLock,
        irt.write_lock_perm_match(irt_perm),
    ensures
        ret matches Some(bdf) ==> pci_bdf_valid(bdf.0, bdf.1, bdf.2) && irt.view().spec_index_owner(bdf.0, bdf.1, bdf.2) == target,
        ret is None ==> forall|b: usize, d: usize, f: usize| #![trigger irt.view().spec_index_owner(b, d, f)] pci_bdf_valid(b, d, f) ==> irt.view().spec_index_owner(b, d, f) != target,
{
    let mut found: Option<PciBdf> = None;
    let mut bus: usize = 0;
    let mut device: usize = 0;
    let mut function: usize = 0;
    while bus < PCI_BUS_COUNT && found.is_none()
        invariant
            irt.inv(),
            irt_perm.state() is WriteLock,
            irt.write_lock_perm_match(irt_perm),
            bus <= PCI_BUS_COUNT,
            device < PCI_DEVICE_COUNT,
            function < PCI_FUNCTION_COUNT,
            bus == PCI_BUS_COUNT ==> device == 0 && function == 0,
            found matches Some(bdf) ==> pci_bdf_valid(bdf.0, bdf.1, bdf.2) && irt.view().spec_index_owner(bdf.0, bdf.1, bdf.2) == target,
            found is None ==> forall|b: usize, d: usize, f: usize| #![trigger irt.view().spec_index_owner(b, d, f)]
                pci_bdf_valid(b, d, f) && pci_bdf_lt((b, d, f), (bus, device, function)) ==> irt.view().spec_index_owner(b, d, f) != target,
        decreases PCI_BUS_COUNT - bus, PCI_DEVICE_COUNT - device, PCI_FUNCTION_COUNT - function,
    {
        if irt.borrow(Tracked(irt_perm)).owner(bus, device, function) == target {
            found = Some((bus, device, function));
        }
        if function + 1 < PCI_FUNCTION_COUNT {
            function = function + 1;
        } else if device + 1 < PCI_DEVICE_COUNT {
            function = 0;
            device = device + 1;
        } else {
            function = 0;
            device = 0;
            bus = bus + 1;
        }
    }
    found
}

/// Send the empty target, already a zombie that owns no PCI function, straight to retiring.
pub(crate) fn kill_retire_zombie(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
    Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        kill_walk_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, None, KillStage::Walk, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
        0 < chain.len(),
        target == chain[chain.len() - 1],
        old(krnl).prc_mp.spec_index(target).view().children.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view().zombie,
        old(krnl).prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        old(steps).view().len() <= final(steps).view().len(),
        kill_walk_state(*final(krnl), *final(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, None, KillStage::Retire, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
        final(krnl).prc_mp.spec_index(target) == old(krnl).prc_mp.spec_index(target),
        final(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set,
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
            &&& final(krnl).ctn_mp.dom().contains(c)
            &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
            &&& final(krnl).ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
            &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes
            &&& final(krnl).ctn_mp.spec_index(c).view().children == old(krnl).ctn_mp.spec_index(c).view().children
        },
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
{
    let ghost before = *krnl;
    let ghost before_lctx = *lctx;
    let ghost before_steps = steps.view();
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(kill_scope_progress(scope, target, KillStage::Retire)), Tracked(&*lctx), Tracked(thread_perm));
    let ghost after = *krnl;
    proof {
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        let before_u = kernel_k_to_kernel_u(before);
        kill_step_pre_from_k(&before, &before_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Walk, scope); kill_zombie_retire_pre_from_k(&before, target);
        kernel_thread_syscall_progress_changed_implies_u_step(&before, &after, thread_ptr);
        kill_zombie_retire_step_from_u(before_u, kernel_k_to_kernel_u(after), cpu_id, thread_ptr, target, scope);
        kill_trace_push(&*steps, before_steps, start, pre, before_u, kernel_k_to_kernel_u(after), cpu_id, ctx);
    }
}

/// Reclaim the empty live target, which owns no PCI function: write-lock its tables, clear every user 4K leaf, flush its
/// PCID from every cpu once, unmap the cleared pages and every IOMMU 4K leaf while refunding their quota to the killer's
/// container chain, return the target's quota of every size, unlock its tables, and make it a zombie.
pub(crate) fn kill_reclaim_live(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
    Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        kill_walk_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, None, KillStage::Walk, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
        0 < chain.len(),
        target == chain[chain.len() - 1],
        old(krnl).prc_mp.spec_index(target).view().children.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        !old(krnl).prc_mp.spec_index(target).view().zombie,
        old(krnl).prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_walk_state(*final(krnl), *final(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, None, KillStage::Retire, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
        final(krnl).prc_mp.spec_index(target).view().zombie,
        final(krnl).prc_mp.spec_index(target).view().children.view().len() == 0,
        final(krnl).prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        final(krnl).prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
        final(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set,
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
            &&& final(krnl).ctn_mp.dom().contains(c)
            &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
            &&& final(krnl).ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
            &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes
            &&& final(krnl).ctn_mp.spec_index(c).view().children == old(krnl).ctn_mp.spec_index(c).view().children
        },
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view(),
{
    proof { process_perms_wf_map(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, target); }
    let target_container = krnl.prc_mp.borrow_rodata(target).borrow().owning_container;
    proof { thread_perms_wf_map(krnl.thr_mp); thread_perms_wf_at(krnl.thr_mp, thread_ptr); }
    let thread_container = krnl.thr_mp.borrow_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(thread_perm)).owning_container;
    proof {
        process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, thread_ptr);
        container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, target); container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, process_ptr);
        assert(target_container == thread_container <==> scope is Subtree);
    }
    let (pagetable, iommu_table) = {
        let tracked target_perm = chain_perms.tracked_borrow(target);
        let process = krnl.prc_mp.borrow_typed(target, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(target_perm));
        (process.pagetable, process.iommu_table)
    };
    let (Tracked(pagetable_perm), Tracked(iommu_perm)) = kill_reclaim_lock_table(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, Ghost(chain),
        Tracked(chain_perms), Tracked(cpu_perm), Tracked(process_perm), Tracked(thread_perm), pagetable, iommu_table, Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    proof { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); }
    let kernel_l4_end = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(&pagetable_perm)).kernel_l4_end;
    let start_l4 = if kernel_l4_end < KERNEL_MEM_END_L4INDEX { KERNEL_MEM_END_L4INDEX } else { kernel_l4_end };
    let ghost locked_pt = pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
    kill_reclaim_clear_leaves(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, Ghost(chain), Tracked(chain_perms), Tracked(cpu_perm),
        Tracked(process_perm), Tracked(thread_perm), pagetable, iommu_table, Tracked(&pagetable_perm), Tracked(&iommu_perm), Ghost(kernel_l4_end), start_l4, Ghost(locked_pt),
        Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    proof { process_perms_wf_at(krnl.prc_mp, target); }
    let (cr3, pcid) = {
        let target_ro = krnl.prc_mp.borrow_rodata(target).borrow();
        (target_ro.cr3, target_ro.pcid)
    };
    kill_reclaim_flush(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, Ghost(chain), Tracked(chain_perms), Tracked(cpu_perm),
        Tracked(process_perm), Tracked(thread_perm), pagetable, iommu_table, Tracked(&pagetable_perm), Tracked(&iommu_perm), Ghost(kernel_l4_end), Ghost(start_l4), Ghost(locked_pt),
        cr3, pcid, Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    kill_reclaim_unmap_leaves(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, Ghost(chain), Tracked(chain_perms), Tracked(cpu_perm),
        Tracked(process_perm), Tracked(thread_perm), pagetable, iommu_table, Tracked(&pagetable_perm), Tracked(&iommu_perm), Ghost(kernel_l4_end), start_l4, Ghost(locked_pt),
        target_container == thread_container, Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    if let Some(it) = iommu_table {
        kill_reclaim_iommu_leaves(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, Ghost(chain), Tracked(chain_perms), Tracked(cpu_perm),
            Tracked(process_perm), Tracked(thread_perm), pagetable, it, Tracked(&pagetable_perm), Tracked(iommu_perm.tracked_borrow()), Ghost(kernel_l4_end),
            target_container == thread_container, Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    }
    kill_reclaim_return_quota_and_zombify(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, Ghost(chain), Tracked(chain_perms),
        Tracked(cpu_perm), Tracked(process_perm), Tracked(thread_perm), pagetable, iommu_table, Tracked(pagetable_perm), Tracked(iommu_perm), Ghost(kernel_l4_end), Ghost(start),
        Ghost(pre), Ghost(scope), Ghost(ctx));
}

/// Write-lock the empty live target's page table and its IOMMU table, if any, and record that nothing is flushed yet.
pub(crate) fn kill_reclaim_lock_table(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, pagetable: RwLockPageTableRoot,
    iommu_table: Option<RwLockPageTableRoot>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
) -> (ret: (Tracked<LockPerm>, Tracked<Option<LockPerm>>))
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        kill_walk_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, None, KillStage::Walk, *cpu_perm, *process_perm, *thread_perm, *chain_perms),
        0 < chain.len(),
        target == chain[chain.len() - 1],
        old(krnl).prc_mp.spec_index(target).view().children.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        !old(krnl).prc_mp.spec_index(target).view().zombie,
        old(krnl).prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
        old(krnl).prc_mp.spec_index(target).view().pagetable == pagetable,
        old(krnl).prc_mp.spec_index(target).view().iommu_table == iommu_table,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_reclaim_state(*final(krnl), *final(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Reclaim { flushed: false }, *cpu_perm, *process_perm, *thread_perm,
            *chain_perms, pagetable, iommu_table, ret.0.view(), ret.1.view()),
        final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).leaves_present(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        pei_valid(final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end),
        iommu_table is Some ==> final(krnl).it_mp.spec_index(iommu_table->Some_0).view().leaves_present() && final(krnl).it_mp.spec_index(iommu_table->Some_0).view().kernel_l4_end == 0
            && final(krnl).it_mp.spec_index(iommu_table->Some_0).view().did is None,
        final(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set,
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
            &&& final(krnl).ctn_mp.dom().contains(c)
            &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
            &&& final(krnl).ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
            &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes
            &&& final(krnl).ctn_mp.spec_index(c).view().children == old(krnl).ctn_mp.spec_index(c).view().children
        },
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
{
    let ghost before = *krnl;
    let ghost before_lctx = *lctx;
    let ghost before_steps = steps.view();
    proof { process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, target); }
    let Tracked(pagetable_perm) = krnl.wlock_pagetable(pagetable, Tracked(&mut *lctx));
    let iommu_perm = match iommu_table {
        Some(it) => {
            proof { process_iommu_table_match_process_at(krnl.prc_mp, krnl.it_mp, target); }
            let Tracked(perm) = krnl.wlock_iommu_table(it, Tracked(&mut *lctx));
            Tracked(Some(perm))
        },
        None => Tracked(None),
    };
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(kill_scope_progress(scope, target, KillStage::Reclaim { flushed: false })), Tracked(&*lctx), Tracked(thread_perm));
    let ghost after = *krnl;
    let ghost after_lctx = *lctx;
    proof {
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        let before_u = kernel_k_to_kernel_u(before);
        kill_step_pre_from_k(&before, &before_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Walk, scope); kill_lock_table_pre_from_k(&before, target);
        kernel_process_tables_lock_state_and_progress_changed_implies_u_step(&before, &after, &after_lctx, target, pagetable, thread_ptr, true);
        kill_lock_table_step_from_u(before_u, kernel_k_to_kernel_u(after), cpu_id, thread_ptr, target, scope);
        assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        kill_trace_push(&*steps, before_steps, start, pre, before_u, kernel_k_to_kernel_u(after), cpu_id, ctx);
        pagetable_perms_wf_at(krnl.pt_mp, pagetable); krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end_valid();
        if let Some(t) = iommu_table {
            iommu_table_perms_wf_at(krnl.it_mp, t);
            assert(krnl.it_mp.spec_index(t).view().kernel_l4_end == 0) by { krnl.it_mp.spec_index(t).view().kernel_entries_wf_l4_end_at(); };
            assert(krnl.it_mp.spec_index(t).view().did is None) by {
                iommu_root_table_process_wf_table_at(krnl.irt.view(), krnl.prc_mp, krnl.it_mp, t); process_iommu_table_match_process_at(krnl.prc_mp, krnl.it_mp, target);
                process_pci_function_ownership_wf_at(krnl.irt.view(), krnl.prc_mp, pci_bdf_of_did(krnl.it_mp.spec_index(t).view().did->Some_0), target);
            };
        }
    }
    (Tracked(pagetable_perm), iommu_perm)
}
} // verus!
