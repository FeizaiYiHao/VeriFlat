use vstd::assert_seqs_equal;
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
        scope == (KillScope::Subtree { process: process_ptr }),
        kill_walk_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, None, KillStage::Walk, *cpu_perm, *process_perm, *thread_perm, *old(chain_perms)),
        0 < chain.len(),
        target == chain[chain.len() - 1],
        old(krnl).prc_mp.spec_index(target).view().children.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set.view().contains(target),
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
        final(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set.view().len() < old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set.view().len(),
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

/// Hand every PCI function of the empty target to the killer's process under the root-table lock: each function the
/// target owns is detached, its IOTLB domain emptied, and the killer's process made its owner. A target owning no
/// function records no step.
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
        scope == (KillScope::Subtree { process: process_ptr }),
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
{
    let ghost before = *krnl;
    let ghost before_lctx = *lctx;
    let ghost before_steps = steps.view();
    proof { assert(lctx.held_lock_majors_lt(IOMMU_ROOT_TABLE_LOCK_MAJOR)) by { reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned); }; }
    let Tracked(irt_perm) = krnl.wlock_iommu_root_table(Tracked(&mut *lctx));
    let ghost locked = *krnl;
    let (moved, Ghost(witness)) = kill_reassign_scan(krnl, Tracked(&*lctx), target, process_ptr, Tracked(&irt_perm));
    if moved {
        proof {
            process_perms_wf_map(krnl.prc_mp);
            let target_ghost = krnl.prc_mp.spec_index(target).view_ghost();
            let owner_ghost = krnl.prc_mp.spec_index(process_ptr).view_ghost();
            krnl.prc_mp.update_ghost(target, ProcessGhost { owned_pci_functions: Ghost(Set::empty()), ..target_ghost });
            krnl.prc_mp.update_ghost(process_ptr, ProcessGhost { owned_pci_functions: Ghost(owner_ghost.owned_pci_functions.view().union(target_ghost.owned_pci_functions.view())), ..owner_ghost });
            assert(krnl.prc_mp.typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id())) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(kill_reassign_eof_transition_framing(locked, *krnl, target, process_ptr)) by { reveal(kill_reassign_eof_transition_framing); };
            kill_reassign_eof(locked, *krnl, target, process_ptr);
        }
    }
    krnl.wunlock_iommu_root_table(Tracked(&mut *lctx), Tracked(irt_perm));
    let ghost after = *krnl;
    proof {
        let before_u = kernel_k_to_kernel_u(before);
        if moved {
            kill_step_pre_from_k(&before, &before_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Walk); kill_reassign_pre_from_k(&before, target);
            assert(before.prc_mp.spec_index(target).view_ghost().owned_pci_functions.view().contains((witness.0, witness.1, witness.2))) by {
                process_pci_function_ownership_wf_at(before.irt.view(), before.prc_mp, (witness.0, witness.1, witness.2), target);
            };
            reveal(kill_reassign_eof_transition_framing);
            kernel_process_functions_reassigned_implies_u_step(&before, &after, target, process_ptr);
            krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
            kill_reassign_step_from_u(before_u, kernel_k_to_kernel_u(after), cpu_id, process_ptr, target);
            kill_trace_push(&*steps, before_steps, start, pre, before_u, kernel_k_to_kernel_u(after), cpu_id, ctx);
        } else {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&before, &after)) by {
                broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
            };
            assert(kernel_endpoint_nonlock_fields_unchanged(before.ep_mp, after.ep_mp)) by { broadcast use kernel_endpoint_nonlock_fields_unchanged_for_equal; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&before, &after)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            kernel_restored_locks_implies_u_eq(&before, &after, cpu_id, None, None, None, None, None);
            krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
            assert(before.prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() =~= Set::<PciBdf>::empty()) by { reveal(process_pci_function_ownership_wf); };
        }
    }
}

/// Scan every B/D/F under the held root-table lock and hand each function `target` owns to `owner`, detached and with its
/// IOTLB domain emptied. Returns whether a function moved, with one moved B/D/F.
pub(crate) fn kill_reassign_scan(krnl: &mut KernelK, Tracked(lctx): Tracked<&LocalContext>, target: RwLockProcessPtr, owner: RwLockProcessPtr, Tracked(irt_perm): Tracked<&LockPerm>)
    -> (ret: (bool, Ghost<PciBdf>))
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), lctx),
        old(krnl).irt.wlocked_by(lctx),
        typed_lock_map_contains_mode(lctx.iommu_root_table_lock_map(), old(krnl).irt.view().table_base(), TypedLockMode::Write),
        irt_perm.state() is WriteLock,
        irt_perm.thread_id() == lctx.thread_id(),
        irt_perm.lock_id() == old(krnl).irt.locking_thread()->Write_lock_id,
    ensures
        *final(krnl) == (KernelK { irt: final(krnl).irt, iommu_tlb: final(krnl).iommu_tlb, ..*old(krnl) }),
        final(krnl).irt.inv(),
        final(krnl).iommu_tlb.inv(),
        iommu_root_table_typed_lock_map_aligned(final(krnl).irt, lctx.iommu_root_table_lock_map(), lctx.thread_id()),
        final(krnl).irt.locking_thread() == old(krnl).irt.locking_thread(),
        final(krnl).irt.view().table_base() == old(krnl).irt.view().table_base(),
        forall|b: usize, d: usize, f: usize| #![trigger final(krnl).irt.view().spec_index_owner(b, d, f)] #![trigger final(krnl).irt.view().spec_index_iommu_root(b, d, f)] pci_bdf_valid(b, d, f) ==> {
            &&& final(krnl).irt.view().spec_index_owner(b, d, f) == if old(krnl).irt.view().spec_index_owner(b, d, f) == target { owner } else { old(krnl).irt.view().spec_index_owner(b, d, f) }
            &&& final(krnl).irt.view().spec_index_iommu_root(b, d, f) == if old(krnl).irt.view().spec_index_owner(b, d, f) == target { None } else { old(krnl).irt.view().spec_index_iommu_root(b, d, f) }
        },
        final(krnl).iommu_tlb.view().dom() == old(krnl).iommu_tlb.view().dom(),
        forall|b: usize, d: usize, f: usize| #![trigger final(krnl).iommu_tlb.view()[pci_bdf_did(b, d, f)]] pci_bdf_valid(b, d, f) ==> final(krnl).iommu_tlb.view()[pci_bdf_did(b, d, f)]
            == if old(krnl).irt.view().spec_index_owner(b, d, f) == target { SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() } }
            else { old(krnl).iommu_tlb.view()[pci_bdf_did(b, d, f)] },
        !ret.0 ==> final(krnl).irt == old(krnl).irt && final(krnl).iommu_tlb == old(krnl).iommu_tlb,
        !ret.0 ==> forall|b: usize, d: usize, f: usize| #![trigger old(krnl).irt.view().spec_index_owner(b, d, f)] pci_bdf_valid(b, d, f) ==> old(krnl).irt.view().spec_index_owner(b, d, f) != target,
        ret.0 ==> pci_bdf_valid(ret.1.view().0, ret.1.view().1, ret.1.view().2) && old(krnl).irt.view().spec_index_owner(ret.1.view().0, ret.1.view().1, ret.1.view().2) == target,
        ret.0 ==> final(krnl).irt.view().user_view() == kill_process_reassigned_table(old(krnl).irt.view().user_view(), target, owner),
{
    let ghost mut witness: PciBdf = (0, 0, 0);
    let mut moved = false;
    let mut bus: usize = 0;
    let mut device: usize = 0;
    let mut function: usize = 0;
    while bus < PCI_BUS_COUNT
        invariant
            old(krnl).inv(),
            *krnl == (KernelK { irt: krnl.irt, iommu_tlb: krnl.iommu_tlb, ..*old(krnl) }),
            krnl.irt.inv(),
            krnl.iommu_tlb.inv(),
            iommu_root_table_typed_lock_map_aligned(krnl.irt, lctx.iommu_root_table_lock_map(), lctx.thread_id()),
            krnl.irt.locking_thread() == old(krnl).irt.locking_thread(),
            krnl.irt.view().table_base() == old(krnl).irt.view().table_base(),
            old(krnl).irt.wlocked_by(lctx),
            typed_lock_map_contains_mode(lctx.iommu_root_table_lock_map(), old(krnl).irt.view().table_base(), TypedLockMode::Write),
            irt_perm.state() is WriteLock,
            irt_perm.thread_id() == lctx.thread_id(),
            irt_perm.lock_id() == old(krnl).irt.locking_thread()->Write_lock_id,
            bus <= PCI_BUS_COUNT,
            device < PCI_DEVICE_COUNT,
            function < PCI_FUNCTION_COUNT,
            bus == PCI_BUS_COUNT ==> device == 0 && function == 0,
            forall|b: usize, d: usize, f: usize| #![trigger krnl.irt.view().spec_index_owner(b, d, f)] #![trigger krnl.irt.view().spec_index_iommu_root(b, d, f)] pci_bdf_valid(b, d, f) ==> {
                let moves = (b < bus || (b == bus && (d < device || (d == device && f < function)))) && old(krnl).irt.view().spec_index_owner(b, d, f) == target;
                &&& krnl.irt.view().spec_index_owner(b, d, f) == if moves { owner } else { old(krnl).irt.view().spec_index_owner(b, d, f) }
                &&& krnl.irt.view().spec_index_iommu_root(b, d, f) == if moves { None } else { old(krnl).irt.view().spec_index_iommu_root(b, d, f) }
            },
            krnl.iommu_tlb.view().dom() == old(krnl).iommu_tlb.view().dom(),
            forall|b: usize, d: usize, f: usize| #![trigger krnl.iommu_tlb.view()[pci_bdf_did(b, d, f)]] pci_bdf_valid(b, d, f) ==> krnl.iommu_tlb.view()[pci_bdf_did(b, d, f)]
                == if (b < bus || (b == bus && (d < device || (d == device && f < function)))) && old(krnl).irt.view().spec_index_owner(b, d, f) == target {
                    SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }
                } else { old(krnl).iommu_tlb.view()[pci_bdf_did(b, d, f)] },
            !moved ==> krnl.irt == old(krnl).irt && krnl.iommu_tlb == old(krnl).iommu_tlb,
            !moved ==> forall|b: usize, d: usize, f: usize| #![trigger old(krnl).irt.view().spec_index_owner(b, d, f)]
                pci_bdf_valid(b, d, f) && (b < bus || (b == bus && (d < device || (d == device && f < function)))) ==> old(krnl).irt.view().spec_index_owner(b, d, f) != target,
            moved ==> pci_bdf_valid(witness.0, witness.1, witness.2) && old(krnl).irt.view().spec_index_owner(witness.0, witness.1, witness.2) == target,
            moved ==> krnl.irt.view().owners().len() == PCI_BUS_COUNT,
            moved ==> forall|b: int| #![trigger krnl.irt.view().owners()[b]] 0 <= b < PCI_BUS_COUNT ==> krnl.irt.view().owners()[b].len() == PCI_DEVICE_COUNT,
            moved ==> forall|b: int, d: int| #![trigger krnl.irt.view().owners()[b][d]] 0 <= b < PCI_BUS_COUNT && 0 <= d < PCI_DEVICE_COUNT ==> krnl.irt.view().owners()[b][d].len() == PCI_FUNCTION_COUNT,
        decreases PCI_BUS_COUNT - bus, PCI_DEVICE_COUNT - device, PCI_FUNCTION_COUNT - function,
    {
        let current = krnl.irt.borrow(Tracked(irt_perm)).owner(bus, device, function);
        if current == target {
            proof { assert(krnl.iommu_tlb.view().dom().contains(pci_bdf_did(bus, device, function))) by { reveal(IommuTLB::inv); reveal(iommu_tlb_wf_spec); }; }
            iommu_root_table_reassign_detached(&mut krnl.irt, &mut krnl.iommu_tlb, bus, device, function, owner, Tracked(lctx), Tracked(irt_perm));
            moved = true;
            proof { witness = (bus, device, function); }
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
    proof {
        if moved {
            reveal(IommuRootTable::user_view);
            let after = krnl.irt.view().user_view();
            let expected = kill_process_reassigned_table(old(krnl).irt.view().user_view(), target, owner);
            assert_seqs_equal!(after.owners, expected.owners, b => {
                assert_seqs_equal!(after.owners[b], expected.owners[b], d => {
                    assert_seqs_equal!(after.owners[b][d], expected.owners[b][d], f => { assert(krnl.irt.view().spec_index_owner(b as usize, d as usize, f as usize) == after.owners[b][d][f]); });
                });
            });
            assert_seqs_equal!(after.attached, expected.attached, b => {
                assert_seqs_equal!(after.attached[b], expected.attached[b], d => {
                    assert_seqs_equal!(after.attached[b][d], expected.attached[b][d], f => {
                        assert(krnl.irt.view().spec_index_owner(b as usize, d as usize, f as usize) == after.owners[b][d][f]);
                        assert(krnl.irt.view().spec_index_iommu_root(b as usize, d as usize, f as usize) is Some == after.attached[b][d][f]);
                    });
                });
            });
        }
    }
    (moved, Ghost(witness))
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
        scope == (KillScope::Subtree { process: process_ptr }),
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
{
    let ghost before = *krnl;
    let ghost before_lctx = *lctx;
    let ghost before_steps = steps.view();
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(kill_progress(target, KillStage::Retire)), Tracked(&*lctx), Tracked(thread_perm));
    let ghost after = *krnl;
    proof {
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        let before_u = kernel_k_to_kernel_u(before);
        kill_step_pre_from_k(&before, &before_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Walk); kill_zombie_retire_pre_from_k(&before, target);
        kernel_thread_syscall_progress_changed_implies_u_step(&before, &after, thread_ptr);
        kill_zombie_retire_step_from_u(before_u, kernel_k_to_kernel_u(after), cpu_id, thread_ptr, target);
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
        scope == (KillScope::Subtree { process: process_ptr }),
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
{
    proof { process_perms_wf_map(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, target); }
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
    let ghost locked_pt = krnl.pt_mp.spec_index(pagetable).view();
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
        Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    if let Some(it) = iommu_table {
        kill_reclaim_iommu_leaves(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, Ghost(chain), Tracked(chain_perms), Tracked(cpu_perm),
            Tracked(process_perm), Tracked(thread_perm), pagetable, it, Tracked(&pagetable_perm), Tracked(iommu_perm.tracked_borrow()), Ghost(kernel_l4_end), Ghost(start),
            Ghost(pre), Ghost(scope), Ghost(ctx));
    }
    kill_reclaim_return_quota(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, Ghost(chain), Tracked(chain_perms), Tracked(cpu_perm),
        Tracked(process_perm), Tracked(thread_perm), pagetable, iommu_table, Tracked(&pagetable_perm), Tracked(&iommu_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    kill_reclaim_unlock_table(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, Ghost(chain), Tracked(chain_perms), Tracked(cpu_perm),
        Tracked(process_perm), Tracked(thread_perm), pagetable, iommu_table, Tracked(pagetable_perm), Tracked(iommu_perm), Ghost(kernel_l4_end), Ghost(start), Ghost(pre),
        Ghost(scope), Ghost(ctx));
    kill_reclaim_zombify(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, Ghost(chain), Tracked(chain_perms), Tracked(cpu_perm),
        Tracked(process_perm), Tracked(thread_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
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
        scope == (KillScope::Subtree { process: process_ptr }),
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
        final(krnl).pt_mp.spec_index(pagetable).view().leaves_present(),
        pei_valid(final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end),
        iommu_table is Some ==> final(krnl).it_mp.spec_index(iommu_table->Some_0).view().leaves_present() && final(krnl).it_mp.spec_index(iommu_table->Some_0).view().kernel_l4_end == 0,
        final(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set == old(krnl).prc_mp.spec_index(process_ptr).view_ghost().subtree_set,
{
    let ghost before = *krnl;
    let ghost before_lctx = *lctx;
    let ghost before_steps = steps.view();
    proof { process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, target); }
    let Tracked(pagetable_perm) = krnl.wlock_pagetable(pagetable, Tracked(&mut *lctx));
    let iommu_perm = match iommu_table {
        Some(it) => {
            proof { process_iommu_table_match_process_at(krnl.prc_mp, krnl.it_mp, target); reveal(process_pci_function_ownership_wf); }
            let Tracked(perm) = krnl.wlock_iommu_table(it, Tracked(&mut *lctx));
            Tracked(Some(perm))
        },
        None => Tracked(None),
    };
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(kill_progress(target, KillStage::Reclaim { flushed: false })), Tracked(&*lctx), Tracked(thread_perm));
    let ghost after = *krnl;
    let ghost after_lctx = *lctx;
    proof {
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        let before_u = kernel_k_to_kernel_u(before);
        kill_step_pre_from_k(&before, &before_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Walk); kill_lock_table_pre_from_k(&before, target);
        kernel_process_tables_lock_state_and_progress_changed_implies_u_step(&before, &after, &after_lctx, target, pagetable, thread_ptr, true);
        kill_lock_table_step_from_u(before_u, kernel_k_to_kernel_u(after), cpu_id, thread_ptr, target);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        kill_trace_push(&*steps, before_steps, start, pre, before_u, kernel_k_to_kernel_u(after), cpu_id, ctx);
        pagetable_perms_wf_at(krnl.pt_mp, pagetable); krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end_valid();
        if iommu_table is Some {
            iommu_table_perms_wf_at(krnl.it_mp, iommu_table->Some_0);
            assert(krnl.it_mp.spec_index(iommu_table->Some_0).view().kernel_l4_end == 0) by { krnl.it_mp.spec_index(iommu_table->Some_0).view().kernel_entries_wf_l4_end_at(); };
        }
    }
    (Tracked(pagetable_perm), iommu_perm)
}
} // verus!
