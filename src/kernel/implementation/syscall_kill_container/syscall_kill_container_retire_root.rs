use vstd::prelude::*;
use crate::*;
use super::super::syscall_kill_process::syscall_kill_process_spec::*;
use super::super::syscall_kill_process::syscall_kill_process_walk::*;
use super::super::syscall_kill_process::syscall_kill_process_retire::{kill_retire_hold_tables, kill_retire_remove_tables};
use super::super::syscall_kill_process::syscall_kill_process_retire_pages::{kill_retire_structure_pages, kill_retire_lock_cache};
use super::super::syscall_kill_process::syscall_kill_process_retire_pages_lock::{kill_retire_pages_to_cache, wunlock_kill_retire_pages};
use super::super::syscall_kill_process::syscall_kill_process_retire_roots::kill_retire_hold_roots;
#[cfg(verus_keep_ghost)]
use super::super::syscall_kill_process::syscall_kill_process_retire_spec::*;
#[cfg(verus_keep_ghost)]
use super::super::syscall_kill_process::syscall_kill_process_retire_pages::kill_retire_pages_held_and_owned;
#[cfg(verus_keep_ghost)]
use super::super::syscall_kill_process::syscall_kill_process_trace::kill_step_pre_from_k;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_spec::kill_container_progress;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_trace::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_retire_root_eof::*;

verus! {
/// Retire the empty zombie root process `target` of the marked container the kill works on, which owns no PCI function,
/// and walk that container again: write-hold its process page, its tables' object pages, and its tables, unlink their
/// structure pages, then retire the process with its tables and their root pages and clear the container's zombie flag.
/// The killer write-holds the container with `container_perm`.
pub(crate) fn kill_container_retire_root(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&mut Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, Tracked(container_perm): Tracked<&LockPerm>,
    Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        ctx is Container,
        scope is Container,
        kill_walk_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, None, KillStage::Retire, *cpu_perm, *process_perm, *thread_perm, *old(chain_perms)),
        chain.len() == 1,
        target == chain[0],
        old(krnl).prc_mp.spec_index(target).view().zombie,
        old(krnl).prc_mp.spec_index(target).view().children.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
        container_perm.state() is WriteLock,
        container_perm.thread_id() == old(lctx).thread_id(),
        container_perm.lock_id() == old(krnl).ctn_mp.spec_index(scope->Container_container).locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        killer_held_context(*final(krnl), *final(lctx), process_ptr, thread_ptr, final(lctx).container_lock_map().dom()),
        final(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        final(lctx).process_lock_map().dom() =~= set![process_ptr],
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), scope->Container_container, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container, TypedLockMode::Write),
        final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_container_progress(scope->Container_container, ContainerKillStage::Walk),
        !final(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
        *final(chain_perms) == old(chain_perms).remove(target),
        final(krnl).ctn_mp.dom().contains(scope->Container_container),
        final(krnl).ctn_mp.spec_index(scope->Container_container).being_killed(),
        final(krnl).ctn_mp.spec_index(scope->Container_container).view_ghost().owned_processes.view().is_empty(),
        !final(krnl).ctn_mp.spec_index(scope->Container_container).view().zombie,
        container_perm.lock_id() == final(krnl).ctn_mp.spec_index(scope->Container_container).locking_thread()->Write_lock_id,
        cpu_perm.lock_id() == final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        process_perm.lock_id() == final(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        thread_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
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
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
{
    proof { process_perms_wf_map(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, target); }
    let (pagetable, iommu_table) = {
        let tracked target_perm = chain_perms.tracked_borrow(target);
        let process = krnl.prc_mp.borrow_typed(target, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(target_perm));
        (process.pagetable, process.iommu_table)
    };
    let (_, Tracked(page_perms), Tracked(pt_perm), Tracked(it_perm)) = kill_retire_hold_tables(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr,
        thread_ptr, target, Ghost(chain), Tracked(&*chain_perms), Tracked(cpu_perm), Tracked(process_perm), Tracked(thread_perm), pagetable, iommu_table, Ghost(scope));
    kill_retire_structure_pages(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, Ghost(chain), Tracked(&*chain_perms), Tracked(cpu_perm),
        Tracked(process_perm), Tracked(thread_perm), Tracked(&page_perms), Tracked(&pt_perm), Tracked(&it_perm), Ghost(start), Ghost(pre), Ghost(scope), Ghost(ctx));
    kill_container_retire_root_process(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, Ghost(chain), Tracked(&mut *chain_perms),
        Tracked(cpu_perm), Tracked(process_perm), Tracked(thread_perm), Tracked(container_perm), Tracked(page_perms), Tracked(pt_perm), Tracked(it_perm), Ghost(start), Ghost(pre),
        Ghost(scope), Ghost(ctx));
}

/// Retire the empty zombie root `target` in one step once the pages that `kill_retire_hold_tables` returned and its
/// tables, which hold only their root tables, are write-held: take its tables' root pages, the 4K allocator cache on
/// `cpu_id` of its container (drained first when it lacks room for the pages), and that allocator's quota; then the
/// process leaves its container, which clears its zombie flag, its tables leave their maps, its pages return to the
/// cache with their quota, and the killer walks the container again.
pub(crate) fn kill_container_retire_root_process(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, Ghost(chain): Ghost<Seq<RwLockProcessPtr>>, Tracked(chain_perms): Tracked<&mut Map<RwLockProcessPtr, LockPerm>>,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, Tracked(container_perm): Tracked<&LockPerm>,
    Tracked(page_perms): Tracked<Map<PageIndex, LockPerm>>, Tracked(pt_perm): Tracked<LockPerm>, Tracked(it_perm): Tracked<Option<LockPerm>>, Ghost(start): Ghost<int>,
    Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        ctx is Container,
        scope is Container,
        kill_retire_held_state(*old(krnl), *old(lctx), process_ptr, thread_ptr, target, page_perms, pt_perm, it_perm),
        held_locks_order_below(old(krnl), old(lctx), PAGETABLE_PAGE_MAJOR),
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        kill_chain_state(*old(krnl), *old(lctx), cpu_id, scope, process_ptr, thread_ptr, chain, KillStage::Retire, *cpu_perm, *process_perm, *thread_perm, *old(chain_perms)),
        kill_retire_tables_emptied(*old(krnl), target),
        chain.len() == 1,
        target == chain[0],
        old(krnl).prc_mp.spec_index(target).view().zombie,
        old(krnl).prc_mp.spec_index(target).view().children.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
        container_perm.state() is WriteLock,
        container_perm.thread_id() == old(lctx).thread_id(),
        container_perm.lock_id() == old(krnl).ctn_mp.spec_index(scope->Container_container).locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        killer_held_context(*final(krnl), *final(lctx), process_ptr, thread_ptr, final(lctx).container_lock_map().dom()),
        final(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        final(lctx).process_lock_map().dom() =~= set![process_ptr],
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), scope->Container_container, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container, TypedLockMode::Write),
        final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_container_progress(scope->Container_container, ContainerKillStage::Walk),
        !final(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
        *final(chain_perms) == old(chain_perms).remove(target),
        final(krnl).ctn_mp.dom().contains(scope->Container_container),
        final(krnl).ctn_mp.spec_index(scope->Container_container).being_killed(),
        final(krnl).ctn_mp.spec_index(scope->Container_container).view_ghost().owned_processes.view().is_empty(),
        !final(krnl).ctn_mp.spec_index(scope->Container_container).view().zombie,
        container_perm.lock_id() == final(krnl).ctn_mp.spec_index(scope->Container_container).locking_thread()->Write_lock_id,
        cpu_perm.lock_id() == final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        process_perm.lock_id() == final(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        thread_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
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
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
{
    proof { process_perms_wf_map(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, target); }
    let (pagetable, iommu_table) = {
        let tracked target_perm = chain_perms.tracked_borrow(target);
        let process = krnl.prc_mp.borrow_typed(target, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(target_perm));
        (process.pagetable, process.iommu_table)
    };
    let (container_ptr, cr3, iommu_cr3) = {
        let target_ro = krnl.prc_mp.borrow_rodata(target).borrow();
        (target_ro.owning_container, target_ro.cr3, target_ro.iommu_cr3)
    };
    proof {
        let tree = krnl.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view();
        container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, target); per_container_process_tree_wf_at(krnl.ctn_mp, krnl.prc_mp, container_ptr);
        process_root_wf_at(target, tree, krnl.prc_mp, target); process_children_parent_wf_parent_at(target, tree, krnl.prc_mp, target);
        if let Some(parent_ptr) = krnl.prc_mp.spec_index(target).view_rodata().view().parent { process_children_parent_wf_at(target, tree, krnl.prc_mp, parent_ptr, target); }
    }
    let (pages, Tracked(page_lock_perms)) = kill_retire_hold_roots(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, target, Ghost(chain),
        Tracked(&*chain_perms), Tracked(cpu_perm), Tracked(process_perm), Tracked(thread_perm), Tracked(page_perms), Tracked(&pt_perm), Tracked(&it_perm), pagetable, iommu_table, cr3,
        iommu_cr3, container_ptr, Ghost(scope));
    let tracked target_perm = chain_perms.tracked_remove(target);
    proof { container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, target); container_perms_wf_at(krnl.ctn_mp, container_ptr); }
    let allocator_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().allocator_ptr_4k;
    proof {
        assert(krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end == KERNEL_MEM_END_L4INDEX) by { krnl.default_pagetable_wf_at(pagetable); };
        container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr);
    }
    let Tracked(cache_lock_perm) = kill_retire_lock_cache(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), allocator_ptr, cpu_id, pages.len(), Ghost(pages.view()[0]));
    let ghost base = steps.snapshot_k();
    let ghost base_lctx = *lctx;
    let ghost base_steps = steps.view();
    proof {
        lemma_container_allocator_4k_quota_bounded(&*krnl, container_ptr); allocator_perms_wf_at(krnl.allc_4k_mp, allocator_ptr);
        assert(pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable)) by {
            old(krnl).pt_mp.typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable);
            pagetable_lower_backup_wf_at(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable); pagetable_lower_backup_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        };
    }
    let Tracked(quota_lock_perm) = krnl.wlock_allocator_quota_4k(allocator_ptr, Tracked(&mut *lctx));
    kill_container_retire_root_commit(krnl, Tracked(&mut *lctx), cpu_id, target, container_ptr, allocator_ptr, pagetable, iommu_table, &pages, Tracked(target_perm),
        Tracked(container_perm), Tracked(page_lock_perms), Tracked(pt_perm), Tracked(it_perm), Tracked(cache_lock_perm), Tracked(quota_lock_perm), Ghost(base));
    let ghost retired_k = *krnl;
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(kill_container_progress(container_ptr, ContainerKillStage::Walk)), Tracked(&*lctx), Tracked(thread_perm));
    proof {
        let pre_u = kernel_k_to_kernel_u(base);
        let post_u = kernel_k_to_kernel_u(*krnl);
        kill_step_pre_from_k(&base, &base_lctx, cpu_id, process_ptr, thread_ptr, target, KillStage::Retire, scope);
        kill_container_retire_root_pre_from_k(&base, &base_lctx, cpu_id, container_ptr, target);
        kernel_zombie_root_process_retired_implies_u_step(&base, &retired_k, target, container_ptr, allocator_ptr);
        kernel_thread_syscall_progress_changed_implies_u_step(&retired_k, &*krnl, thread_ptr);
        kill_container_retire_root_step_from_u(pre_u, kernel_k_to_kernel_u(retired_k), post_u, cpu_id, thread_ptr, container_ptr, target,
            retired_k.allc_4k_mp.spec_index(allocator_ptr).quota.view().view());
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        kill_container_trace_push(&*steps, base_steps, start, pre, pre_u, post_u, cpu_id, ctx);
    }
}

/// With the zombie root `target`, its pages, tables, its container `container_ptr`, and that container's 4K allocator
/// cache on `cpu_id` and quota write-held, retire the root: its tables leave their maps, it leaves its container, which
/// clears its zombie flag, its pages return to the cache with their quota, and those locks except the container's are
/// released. The caller ends the step.
pub(crate) fn kill_container_retire_root_commit(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, target: RwLockProcessPtr, container_ptr: RwLockContainerPtr,
    allocator_ptr: RwLockPageAllocatorPtr, pagetable: RwLockPageTableRoot, iommu_table: Option<RwLockPageTableRoot>, pages: &ArrayVec<PageIndex, 5>,
    Tracked(target_perm): Tracked<LockPerm>, Tracked(container_perm): Tracked<&LockPerm>, Tracked(page_lock_perms): Tracked<Map<PageIndex, LockPerm>>,
    Tracked(pt_lock_perm): Tracked<LockPerm>, Tracked(it_lock_perm): Tracked<Option<LockPerm>>, Tracked(cache_lock_perm): Tracked<LockPerm>,
    Tracked(quota_lock_perm): Tracked<LockPerm>, Ghost(base): Ghost<KernelK>,
)
    requires
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(krnl).inv(),
        base.inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).prc_mp.dom().contains(target),
        old(krnl).prc_mp.spec_index(target).being_killed(),
        old(krnl).prc_mp.spec_index(target).view().zombie,
        old(krnl).prc_mp.spec_index(target).view().children.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
        old(krnl).prc_mp.spec_index(target).view_rodata().view().parent is None,
        old(krnl).prc_mp.spec_index(target).view_rodata().view().owning_container == container_ptr,
        0 < old(krnl).prc_mp.spec_index(target).view_rodata().view().container_depth,
        old(krnl).prc_mp.spec_index(target).view().pagetable == pagetable,
        old(krnl).prc_mp.spec_index(target).view().iommu_table == iommu_table,
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), target, TypedLockMode::Write),
        target_perm.state() is WriteLock,
        target_perm.thread_id() == old(lctx).thread_id(),
        target_perm.lock_id() == old(krnl).prc_mp.spec_index(target).locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).view().root_process == target,
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        container_perm.state() is WriteLock,
        container_perm.thread_id() == old(lctx).thread_id(),
        container_perm.lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        old(lctx).pagetable_lock_map().dom() == set![pagetable],
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pt_lock_perm.state() is WriteLock,
        pt_lock_perm.thread_id() == old(lctx).thread_id(),
        pt_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        kill_retire_tables_emptied(*old(krnl), target),
        old(lctx).iommu_table_lock_map().dom() == match iommu_table { Some(it) => set![it], None => Set::<RwLockPageTableRoot>::empty() },
        it_lock_perm is Some == iommu_table is Some,
        iommu_table is Some ==> {
            let it = old(krnl).it_mp.spec_index(iommu_table->Some_0);
            &&& typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table->Some_0, TypedLockMode::Write)
            &&& it_lock_perm->Some_0.state() is WriteLock
            &&& it_lock_perm->Some_0.thread_id() == old(lctx).thread_id()
            &&& it_lock_perm->Some_0.lock_id() == it.locking_thread()->Write_lock_id
        },
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        old(krnl).allc_4k_mp.dom().contains(allocator_ptr),
        old(lctx).allocator_cache_4k_lock_map().dom() == set![(allocator_ptr, cpu_id)],
        typed_lock_map_contains_mode(old(lctx).allocator_cache_4k_lock_map(), (allocator_ptr, cpu_id), TypedLockMode::Write),
        forall|d: RwLockProcessPtr| #![trigger old(lctx).process_lock_map().dom().contains(d)] old(lctx).process_lock_map().dom().contains(d) && old(krnl).prc_mp.spec_index(d).killer_info() is Some
            ==> old(krnl).prc_mp.spec_index(d).killer_info()->Some_0.process != target && old(krnl).prc_mp.spec_index(d).view_rodata().view().owning_container == container_ptr,
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) && old(krnl).ctn_mp.spec_index(c).killer_info() is Some
            ==> old(krnl).ctn_mp.spec_index(c).killer_info()->Some_0.process != target,
        cache_lock_perm.state() is WriteLock,
        cache_lock_perm.thread_id() == old(lctx).thread_id(),
        cache_lock_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().len() + pages.view().len() <= ALLOCATOR_MAX_WATERMARK,
        old(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.view().value <= old(krnl).allc_4k_mp.spec_index(allocator_ptr).total_free_pages.view(),
        old(krnl).allc_4k_mp.spec_index(allocator_ptr).total_free_pages.view() <= NUM_PAGES * 4096 + NUM_CPUS * ALLOCATOR_MAX_WATERMARK,
        old(lctx).allocator_quota_4k_lock_map().dom() == set![allocator_ptr],
        typed_lock_map_contains_mode(old(lctx).allocator_quota_4k_lock_map(), allocator_ptr, TypedLockMode::Write),
        quota_lock_perm.state() is WriteLock,
        quota_lock_perm.thread_id() == old(lctx).thread_id(),
        quota_lock_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.locking_thread()->Write_lock_id,
        old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        pages.wf(),
        pages.view() == kill_retire_pages(*old(krnl), target),
        pages.view().no_duplicates(),
        old(lctx).page_lock_map().dom() == pages.view().to_set(),
        page_lock_perms.dom() == pages.view().to_set(),
        forall|p: PageIndex| #![trigger page_lock_perms.dom().contains(p)] page_lock_perms.dom().contains(p) ==> {
            &&& typed_lock_map_contains_mode(old(lctx).page_lock_map(), p, TypedLockMode::Write)
            &&& page_lock_perms[p].state() is WriteLock
            &&& page_lock_perms[p].thread_id() == old(lctx).thread_id()
            &&& page_lock_perms[p].lock_id() == old(krnl).pg_arr.spec_index(p).view().locking_thread()->Write_lock_id
        },
        *old(krnl) == (KernelK { pg_arr: old(krnl).pg_arr, pt_mp: old(krnl).pt_mp, it_mp: old(krnl).it_mp, allc_4k_mp: old(krnl).allc_4k_mp, ..base }),
        old(krnl).pt_mp.dom() == base.pt_mp.dom(),
        forall|t: RwLockPageTableRoot| #![trigger old(krnl).pt_mp.spec_index(t)] old(krnl).pt_mp.dom().contains(t) && t != pagetable ==> old(krnl).pt_mp.spec_index(t) == base.pt_mp.spec_index(t),
        old(krnl).it_mp.dom() == base.it_mp.dom(),
        forall|t: RwLockPageTableRoot| #![trigger old(krnl).it_mp.spec_index(t)] old(krnl).it_mp.dom().contains(t) && Some(t) != iommu_table ==> old(krnl).it_mp.spec_index(t) == base.it_mp.spec_index(t),
        old(krnl).allc_4k_mp.dom() == base.allc_4k_mp.dom(),
        forall|a: RwLockPageAllocatorPtr| #![trigger old(krnl).allc_4k_mp.spec_index(a)]
            old(krnl).allc_4k_mp.dom().contains(a) ==> old(krnl).allc_4k_mp.spec_index(a).quota.view() == base.allc_4k_mp.spec_index(a).quota.view(),
        forall|held_thread: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(held_thread)]
            old(lctx).thread_lock_map().dom().contains(held_thread) ==> !old(krnl).thr_mp.spec_index(held_thread).being_killed(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).process_lock_map() == old(lctx).process_lock_map().remove(target),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).page_lock_map().dom().is_empty(),
        final(lctx).pagetable_lock_map().dom().is_empty(),
        final(lctx).pagetable_window_lock_map().dom().is_empty(),
        final(lctx).iommu_table_lock_map().dom().is_empty(),
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        final(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        final(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        *final(krnl) == (KernelK { prc_mp: final(krnl).prc_mp, ctn_mp: final(krnl).ctn_mp, pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, it_mp: final(krnl).it_mp,
            pg_arr: final(krnl).pg_arr, allc_4k_mp: final(krnl).allc_4k_mp, ..*old(krnl) }),
        final(krnl).prc_mp.dom() == base.prc_mp.dom().remove(target),
        final(krnl).allc_4k_mp.dom().contains(allocator_ptr),
        forall|p: RwLockProcessPtr| #![trigger final(krnl).prc_mp.spec_index(p)] final(krnl).prc_mp.dom().contains(p) ==> final(krnl).prc_mp.spec_index(p) == base.prc_mp.spec_index(p),
        final(krnl).ctn_mp.dom() == base.ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(c)] base.ctn_mp.dom().contains(c) && c != container_ptr ==> final(krnl).ctn_mp.spec_index(c) == base.ctn_mp.spec_index(c),
        final(krnl).ctn_mp.spec_index(container_ptr).view() == (Container { zombie: false, ..base.ctn_mp.spec_index(container_ptr).view() }),
        final(krnl).ctn_mp.spec_index(container_ptr).view_rodata() == base.ctn_mp.spec_index(container_ptr).view_rodata(),
        final(krnl).ctn_mp.spec_index(container_ptr).view_ghost() == (ContainerGhost {
            owned_processes: Ghost(base.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().remove(target)), ..base.ctn_mp.spec_index(container_ptr).view_ghost() }),
        final(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty(),
        final(krnl).ctn_mp.spec_index(container_ptr).locking_thread() == base.ctn_mp.spec_index(container_ptr).locking_thread(),
        final(krnl).ctn_mp.spec_index(container_ptr).being_killed() == base.ctn_mp.spec_index(container_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(container_ptr).killer_info() == base.ctn_mp.spec_index(container_ptr).killer_info(),
        forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_4k_mp.spec_index(a)]
            base.allc_4k_mp.dom().contains(a) && a != allocator_ptr ==> final(krnl).allc_4k_mp.spec_index(a).quota.view() == base.allc_4k_mp.spec_index(a).quota.view(),
        base.allc_4k_mp.spec_index(allocator_ptr).quota.view().view() < final(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.view().view(),
        final(krnl).pt_mp.dom() == base.pt_mp.dom().remove(pagetable),
        forall|t: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(t)]
            final(krnl).pt_mp.dom().contains(t) ==> final(krnl).pt_mp.spec_index(t) == base.pt_mp.spec_index(t) && final(krnl).pt_lower.view().spec_index(t) == base.pt_lower.view().spec_index(t),
        final(krnl).it_mp.dom() == match iommu_table { Some(it) => base.it_mp.dom().remove(it), None => base.it_mp.dom() },
        forall|t: RwLockPageTableRoot| #![trigger final(krnl).it_mp.spec_index(t)] final(krnl).it_mp.dom().contains(t) ==> final(krnl).it_mp.spec_index(t) == base.it_mp.spec_index(t),
{
    let ghost entry = *krnl;
    proof {
        process_perms_wf_map(krnl.prc_mp); container_perms_wf_map(krnl.ctn_mp);
        allocator_perms_wf_map(krnl.allc_4k_mp);
        allocator_perms_wf_at(krnl.allc_4k_mp, allocator_ptr);
        krnl.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), target);
        krnl.ctn_mp.typed_lock_map_aligned_write_at(lctx.container_lock_map(), lctx.thread_id(), container_ptr);
        krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
        if let Some(it) = iommu_table { krnl.it_mp.typed_lock_map_aligned_write_at(lctx.iommu_table_lock_map(), lctx.thread_id(), it); }
        pagetable_pages_wf_closure_entry_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pagetable, krnl.pt_mp.spec_index(pagetable).view().cr3);
        if let Some(it) = iommu_table { iommu_table_pages_wf_closure_entry_at(krnl.it_mp, krnl.pg_arr, it, krnl.it_mp.spec_index(it).view().cr3); }
        process_pages_wf_process_entry_at(krnl.pg_arr, krnl.prc_mp, target);
        pagetable_pages_wf_root_entry_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pagetable);
        if let Some(it) = iommu_table { iommu_table_pages_wf_root_entry_at(krnl.it_mp, krnl.pg_arr, it); }
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        kill_retire_pages_held_and_owned(entry, target, old(lctx).page_lock_map().dom(), allocator_ptr, cpu_id);
    }
    let Tracked(process_page_perm) = kill_container_retire_root_unlink(krnl, Tracked(&mut *lctx), target, container_ptr, Tracked(target_perm), Tracked(container_perm));
    let tables = kill_retire_remove_tables(krnl, Tracked(&mut *lctx), pagetable, iommu_table, Tracked(pt_lock_perm), Tracked(it_lock_perm));
    let tracked mut page_perms = tables.get();
    proof { page_perms.tracked_insert(page_ptr2page_index(target), process_page_perm); }
    kill_retire_pages_to_cache(krnl, pages, Tracked(page_perms), allocator_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&page_lock_perms), Tracked(&cache_lock_perm));
    {
        let quota = krnl.allc_4k_mp.borrow_mut_quota_typed(allocator_ptr, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
            Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(&quota_lock_perm));
        quota.value = quota.value + pages.len();
    }
    let ghost mid = *krnl;
    proof {
        assert(kill_container_retire_root_eof_transition_framing(entry, mid, cpu_id, target, container_ptr, allocator_ptr)) by { reveal(kill_container_retire_root_eof_transition_framing); };
        reveal(LockedMap::typed_lock_map_aligned);
        kill_container_retire_root_eof(entry, mid, *old(lctx), cpu_id, target, container_ptr, allocator_ptr);
    }
    krnl.wunlock_allocator_quota_4k(allocator_ptr, Tracked(&mut *lctx), Tracked(quota_lock_perm));
    krnl.wunlock_allocator_cache_4k(allocator_ptr, cpu_id, Tracked(&mut *lctx), Tracked(cache_lock_perm));
    wunlock_kill_retire_pages(krnl, pages, Tracked(&mut *lctx), Tracked(page_lock_perms));
}

/// With the root `target` of the container `container_ptr` and that container write-held in a released view, take back
/// the root's own list node, drop the root from the container's processes, clear the container's zombie flag, and
/// remove the root from the process map, returning its page permission.
pub(crate) fn kill_container_retire_root_unlink(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, target: RwLockProcessPtr, container_ptr: RwLockContainerPtr, Tracked(target_perm): Tracked<LockPerm>,
    Tracked(container_perm): Tracked<&LockPerm>,
) -> (ret: Tracked<PagePerm4k>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        old(krnl).prc_mp.dom().contains(target),
        old(krnl).prc_mp.spec_index(target).being_killed(),
        old(krnl).prc_mp.spec_index(target).view().children.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        old(krnl).prc_mp.spec_index(target).view_rodata().view().owning_container == container_ptr,
        old(krnl).ctn_mp.spec_index(container_ptr).view().root_process == target,
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), target, TypedLockMode::Write),
        target_perm.state() is WriteLock,
        target_perm.thread_id() == old(lctx).thread_id(),
        target_perm.lock_id() == old(krnl).prc_mp.spec_index(target).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        container_perm.state() is WriteLock,
        container_perm.thread_id() == old(lctx).thread_id(),
        container_perm.lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
    ensures
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Process(target)),
        *final(krnl) == (KernelK { prc_mp: final(krnl).prc_mp, ctn_mp: final(krnl).ctn_mp, ..*old(krnl) }),
        final(krnl).prc_mp.perms_wf(),
        final(krnl).ctn_mp.perms_wf(),
        final(krnl).prc_mp.dom() == old(krnl).prc_mp.dom().remove(target),
        forall|p: RwLockProcessPtr| #![trigger final(krnl).prc_mp.spec_index(p)] final(krnl).prc_mp.dom().contains(p) ==> final(krnl).prc_mp.spec_index(p) == old(krnl).prc_mp.spec_index(p),
        final(krnl).ctn_mp.dom() == old(krnl).ctn_mp.dom(),
        final(krnl).ctn_mp.unchanged_except(&old(krnl).ctn_mp, container_ptr),
        final(krnl).ctn_mp.spec_index(container_ptr).view() == (Container { zombie: false, ..old(krnl).ctn_mp.spec_index(container_ptr).view() }),
        final(krnl).ctn_mp.spec_index(container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata(),
        final(krnl).ctn_mp.spec_index(container_ptr).view_ghost() == (ContainerGhost {
            owned_processes: Ghost(old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().remove(target)), ..old(krnl).ctn_mp.spec_index(container_ptr).view_ghost() }),
        final(krnl).ctn_mp.spec_index(container_ptr).is_init() == old(krnl).ctn_mp.spec_index(container_ptr).is_init(),
        final(krnl).ctn_mp.spec_index(container_ptr).locking_thread() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread(),
        final(krnl).ctn_mp.spec_index(container_ptr).being_killed() == old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(container_ptr).killer_info() == old(krnl).ctn_mp.spec_index(container_ptr).killer_info(),
        ret.view().is_init(),
        ret.view().addr() == target,
{
    proof {
        let tree = krnl.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view();
        process_perms_wf_map(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, target);
        container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, target); per_container_process_tree_wf_at(krnl.ctn_mp, krnl.prc_mp, container_ptr);
        process_root_wf_at(target, tree, krnl.prc_mp, target);
        container_perms_wf_map(krnl.ctn_mp); container_perms_wf_at(krnl.ctn_mp, container_ptr);
    }
    let Tracked(node_perm) = {
        let process = krnl.prc_mp.borrow_mut_typed(target, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(&target_perm));
        let (_, node_perm) = process.parent_linkedlist_node.take();
        node_perm
    };
    proof { container_map_remove_owned_process(&mut krnl.ctn_mp, container_ptr, target, lctx.container_lock_map(), lctx.thread_id()); }
    {
        let container = krnl.ctn_mp.borrow_mut_typed(container_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(container_perm));
        container.zombie = false;
    }
    krnl.remove_process_and_reclaim_4k_page_perm(target, Tracked(node_perm), Tracked(target_perm), Tracked(&mut *lctx))
}
} // verus!
