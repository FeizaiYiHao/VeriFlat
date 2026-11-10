use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_call_spec::*;
use super::syscall_ipc_call_trace::*;

verus! {
/// Switches the running `cpu_id` to `next_thread` of `next_process`: a thread of the running process `prc_ptr` only becomes the
/// current thread; a thread of another process write-locks that process's PCID needflush entry and switches cr3/PCID. Returns
/// the switched PCID, the state `locked` after that needflush lock (`*old(krnl)` for the same process), and the needflush lock.
#[inline(always)]
pub(super) fn ipc_handoff_switch_to_thread(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, prc_ptr: RwLockProcessPtr, next_process: RwLockProcessPtr,
    next_thread: RwLockThreadPtr, Tracked(cpu_lock_perm): Tracked<&LockPerm>,
) -> (ret: (Option<Pcid>, Ghost<KernelK>, Tracked<Option<LockPerm>>))
    requires
        old(krnl).inv(),
        old(krnl).cpu_arr.inv(),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        old(krnl).thrd_mp.dom().contains(next_thread),
        old(krnl).thrd_mp.spec_index(next_thread).view().owning_proc == next_process,
        old(krnl).prc_mp.dom().contains(next_process),
        !old(krnl).prc_mp.spec_index(next_process).view().zombie,
        old(krnl).prc_mp.spec_index(next_process).is_init(),
        old(krnl).prc_mp.view().spec_index(next_process).is_init(),
        old(krnl).prc_mp.view().spec_index(next_process).addr() == next_process,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map().insert(cpu_id, TypedHeldLock { lock_id: final(krnl).cpu_arr.lock_id_by_index(cpu_id), mode: TypedLockMode::Write }),
        final(lctx).pcid_needflush_lock_map().dom() =~= match ret.0 { Some(pcid) => set![(cpu_id, pcid)], None => Set::empty() },
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_quota_4k_lock_map() == old(lctx).allocator_quota_4k_lock_map(),
        final(lctx).allocator_cache_4k_lock_map() == old(lctx).allocator_cache_4k_lock_map(),
        final(lctx).allocator_global_pool_4k_lock_map() == old(lctx).allocator_global_pool_4k_lock_map(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        ret.0 == if old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(next_process) { None } else { Some(old(krnl).prc_mp.spec_index(next_process).view_rodata().view().pcid) },
        pcid_valid(old(krnl).prc_mp.spec_index(next_process).view_rodata().view().pcid),
        ret.0 matches Some(pcid) ==> {
            &&& typed_lock_map_contains_mode(final(lctx).pcid_needflush_lock_map(), (cpu_id, pcid), TypedLockMode::Write)
            &&& ret.2@ matches Some(perm) && perm.state() is WriteLock && perm.thread_id() == old(lctx).thread_id()
            &&& ret.2@.unwrap().lock_id() == final(krnl).pcid_needflush.spec_index(cpu_id, pcid).locking_thread()->Write_lock_id
        },
        ret.1@.inv(),
        ret.1@ == (KernelK { pcid_needflush: ret.1@.pcid_needflush, ..*old(krnl) }),
        forall|c: CpuId, p: Pcid| #![trigger ret.1@.pcid_needflush.spec_index(c, p)] #![trigger old(krnl).pcid_needflush.spec_index(c, p)] index_valid(NUM_CPUS, c) && pcid_valid(p) ==> {
            &&& ret.1@.pcid_needflush.spec_index(c, p).view() == old(krnl).pcid_needflush.spec_index(c, p).view()
            &&& ((c != cpu_id || ret.0 != Some(p)) ==> ret.1@.pcid_needflush.spec_index(c, p) == old(krnl).pcid_needflush.spec_index(c, p))
        },
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &ret.1@),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, ret.1@.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &ret.1@),
        final(krnl).cpu_arr.inv(),
        final(krnl).cpu_tlb.inv(),
        final(krnl).pcid_needflush.inv(),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].inv(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().tlb_dirty_bitmap.inv(),
        ({
            let pre = ret.1@;
            let post = *final(krnl);
            let cpu_before = pre.cpu_arr.spec_index(cpu_id).view();
            let cpu_after = post.cpu_arr.spec_index(cpu_id).view();
            let old_cpu = cpu_before.view().view();
            let new_cpu = cpu_after.view().view();
            let target = pre.prc_mp.spec_index(next_process).view_rodata().view();
            let pcid = target.pcid;
            let dirty = cpu_before.view().tlb_dirty_bitmap().spec_index(pcid);
            let same = old_cpu.current_process == Some(next_process);
            let flush = !same && (pre.pcid_needflush.spec_index(cpu_id, pcid).view().needflush
                || (dirty is Some && (dirty.unwrap().process_ptr != next_process || dirty.unwrap().pagetable_ptr != target.pagetable)));
            let needflush_before = pre.pcid_needflush.spec_index(cpu_id, pcid);
            let needflush_after = post.pcid_needflush.spec_index(cpu_id, pcid);
            &&& post == (KernelK { cpu_arr: post.cpu_arr, pcid_needflush: post.pcid_needflush, cpu_hw_cr3_pcid: post.cpu_hw_cr3_pcid, cpu_tlb: post.cpu_tlb, ..pre })
            &&& post.cpu_arr.view().len() == pre.cpu_arr.view().len()
            &&& (forall|c: CpuId| #![trigger pre.cpu_arr.spec_index(c)] #![trigger post.cpu_arr.spec_index(c)] index_valid(NUM_CPUS, c) && c != cpu_id ==> post.cpu_arr.spec_index(c) == pre.cpu_arr.spec_index(c))
            &&& cpu_after.is_init() == cpu_before.is_init()
            &&& cpu_after.view_rodata() == cpu_before.view_rodata()
            &&& cpu_after.view_ghost() == cpu_before.view_ghost()
            &&& cpu_after.view().kernel_call_perm() == cpu_before.view().kernel_call_perm()
            &&& cpu_after.being_killed() == cpu_before.being_killed()
            &&& cpu_after.killer_info() == cpu_before.killer_info()
            &&& cpu_after.locking_thread() == cpu_before.locking_thread()
            &&& new_cpu == if same { CpuView { current_thread: Some(next_thread), ..old_cpu } } else {
                CpuView {
                    state: CpuState::Running, current_process: Some(next_process), current_thread: Some(next_thread), current_pagetable: Some(target.pagetable),
                    current_cr3: target.cr3, current_pcid: pcid, process_depth: target.depth, tlb_dirty_bitmap: new_cpu.tlb_dirty_bitmap, ..old_cpu
                }
            }
            &&& cpu_after.view().wf()
            &&& cpu_after.view().tlb_dirty_bitmap() == if same { cpu_before.view().tlb_dirty_bitmap() } else {
                cpu_before.view().tlb_dirty_bitmap().insert(pcid, Some(ProcessPageTablePair { process_ptr: next_process, pagetable_ptr: target.pagetable }))
            }
            &&& needflush_after.view().index() == needflush_before.view().index()
            &&& needflush_after.is_init() == needflush_before.is_init()
            &&& needflush_after.view_rodata() == needflush_before.view_rodata()
            &&& needflush_after.view_ghost() == needflush_before.view_ghost()
            &&& needflush_after.being_killed() == needflush_before.being_killed()
            &&& needflush_after.locking_thread() == needflush_before.locking_thread()
            &&& needflush_after.view() == (PcidNeedFlush { needflush: same && needflush_before.view().needflush, ..needflush_before.view() })
            &&& (forall|c: CpuId, p: Pcid| #![trigger pre.pcid_needflush.spec_index(c, p)] #![trigger post.pcid_needflush.spec_index(c, p)]
                index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid) ==> post.pcid_needflush.spec_index(c, p) == pre.pcid_needflush.spec_index(c, p))
            &&& post.cpu_hw_cr3_pcid[cpu_id as int].owner_cpu() == pre.cpu_hw_cr3_pcid[cpu_id as int].owner_cpu()
            &&& post.cpu_hw_cr3_pcid[cpu_id as int].view() == if same { pre.cpu_hw_cr3_pcid[cpu_id as int].view() } else { (target.cr3, pcid) }
            &&& (forall|c: CpuId| #![trigger pre.cpu_hw_cr3_pcid[c as int]] #![trigger post.cpu_hw_cr3_pcid[c as int]] index_valid(NUM_CPUS, c) && c != cpu_id ==> post.cpu_hw_cr3_pcid[c as int] == pre.cpu_hw_cr3_pcid[c as int])
            &&& post.cpu_tlb.view() == if flush { pre.cpu_tlb.view().insert((cpu_id, pcid), post.cpu_tlb.spec_index((cpu_id, pcid))) } else { pre.cpu_tlb.view() }
            &&& post.cpu_tlb.structure_caches.view() == if flush { pre.cpu_tlb.structure_caches.view().insert((cpu_id, pcid), post.cpu_tlb.structure_cache((cpu_id, pcid))) } else { pre.cpu_tlb.structure_caches.view() }
            &&& (forall|c: CpuId, p: Pcid| #![trigger pre.cpu_tlb.spec_index((c, p))] #![trigger post.cpu_tlb.spec_index((c, p))]
                index_valid(NUM_CPUS, c) && pcid_valid(p) && !(flush && c == cpu_id && p == pcid) ==> post.cpu_tlb.spec_index((c, p)) == pre.cpu_tlb.spec_index((c, p)))
            &&& flush ==> single_cpu_single_pcid_tlb_subset_of_present_pagetable(post.cpu_tlb.spec_index((cpu_id, pcid)), whole_pagetable(pre.pt_mp, pre.pt_lower.view(), target.pagetable))
            &&& flush ==> single_structure_cache_subset_of_present_pagetable(post.cpu_tlb.structure_cache((cpu_id, pcid)), whole_pagetable(pre.pt_mp, pre.pt_lower.view(), target.pagetable))
        }),
{
    let ghost mut before_switch = *krnl;
    let tracked mut needflush_perm: Option<LockPerm> = None;
    let switched_pcid = if next_process == prc_ptr {
        proof {
            assert({
                &&& krnl.cpu_arr.spec_index(cpu_id).view().is_init()
                &&& krnl.cpu_arr.spec_index(cpu_id).view().view().wf()
            }) by { cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), cpu_id); };
            assert(pcid_valid(krnl.prc_mp.spec_index(next_process).view_rodata().view().pcid)) by {
                process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, next_process); process_perms_wf_at(krnl.prc_mp, next_process); process_pcid_allocator_wf_process_at(krnl.ctn_mp, krnl.prc_mp, krnl.pcid_allc_mp, next_process);
            };
            pcid_needflush_wf_implies_array_inv(krnl.pcid_needflush); cpu_hw_cr3_pcid_wf_at(krnl.cpu_hw_cr3_pcid, krnl.cpu_arr, krnl.pcid_needflush, cpu_id);
            kernel_cpu_process_thread_nonlock_fields_unchanged_for_equal(&*old(krnl), &before_switch); kernel_endpoint_nonlock_fields_unchanged_for_equal(old(krnl).ep_mp, before_switch.ep_mp);
            kernel_container_nonlock_fields_and_quotas_unchanged_for_equal(&*old(krnl), &before_switch);
        }
        krnl.cpu_arr.switch_to_thread_same_process(cpu_id, next_thread, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        None
    } else {
        let process = krnl.prc_mp.borrow_rodata(next_process).borrow();
        let next_pagetable = process.pagetable;
        let cr3 = process.cr3;
        let pcid = process.pcid;
        let depth = process.depth;
        assert(page_ptr_valid(cr3) && pcid_valid(pcid) && pcid != KERNEL_DEFAULT_PCID && krnl.pt_mp.dom().contains(next_pagetable) && krnl.pt_mp.spec_index(next_pagetable).view().higher.cr3 == cr3) by {
            process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, next_process); process_perms_wf_at(krnl.prc_mp, next_process); pagetable_perms_wf_at(krnl.pt_mp, next_pagetable); process_pcid_allocator_wf_process_at(krnl.ctn_mp, krnl.prc_mp, krnl.pcid_allc_mp, next_process);
            krnl.pt_mp.spec_index(next_pagetable).view().higher.table_pages_wf_cr3_at();
        };
        let Tracked(perm) = krnl.wlock_pcid_needflush(cpu_id, pcid, Tracked(&mut *lctx));
        proof {
            needflush_perm = Some(perm);
            before_switch = *krnl;
            assert({
                &&& krnl.cpu_arr.spec_index(cpu_id).view().is_init()
                &&& krnl.cpu_arr.spec_index(cpu_id).view().view().wf()
            }) by { cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), cpu_id); };
        }
        krnl.cpu_arr.switch_to_thread(cpu_id, next_process, next_thread, next_pagetable, cr3, pcid, depth, &mut krnl.cpu_tlb, &mut krnl.pcid_needflush, &mut krnl.cpu_hw_cr3_pcid,
            Ghost(before_switch), Tracked(needflush_perm.tracked_borrow()), Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        Some(pcid)
    };
    proof { lctx.update_lock_id(KernelObjId::Cpu(cpu_id), before_switch.cpu_arr.lock_id_by_index(cpu_id), krnl.cpu_arr.lock_id_by_index(cpu_id)); }
    (switched_pcid, Ghost(before_switch), Tracked(needflush_perm))
}

/// Releases the caller-pcid needflush (when the handoff switched to the caller's PCID `switched_pcid`), caller, callee, endpoint,
/// and cpu locks after the reply handoff `locked_k` → `*old(krnl)` summarized by `ipc_reply_handoff_eof_transition_framing`,
/// where `locked_k` is `entry_k` with that needflush entry write-locked, and records the reply-handoff step from `steps.snapshot_k()`.
pub(super) fn ipc_reply_handoff_release_and_end_step(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, switched_pcid: Option<Pcid>,
    callee_ptr: RwLockThreadPtr, ep_ptr: RwLockEndpointPtr, ep_idx: EndpointIdx, caller_ptr: RwLockThreadPtr,
    Ghost(entry_k): Ghost<KernelK>, Ghost(entry_lctx): Ghost<LocalContext>, Ghost(locked_k): Ghost<KernelK>,
    Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(callee_lock_perm): Tracked<LockPerm>, Tracked(endpoint_lock_perm): Tracked<LockPerm>,
    Tracked(caller_lock_perm): Tracked<LockPerm>, Tracked(needflush_perm): Tracked<Option<LockPerm>>,
)
    requires
        entry_k == (KernelK { cpu_arr: entry_k.cpu_arr, cpu_op: entry_k.cpu_op, thrd_mp: entry_k.thrd_mp, ep_mp: entry_k.ep_mp, ..old(steps).snapshot_k() }),
        old(steps).snapshot_k().cpu_trap_frame.view().view().dom().contains(cpu_id),
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view(),
        forall|p: RwLockContainerPtr| #![trigger entry_k.ctn_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ctn_mp.spec_index(p)]
            old(steps).snapshot_k().ctn_mp.dom().contains(p) && entry_k.ctn_mp.dom().contains(p) ==> if entry_lctx.container_lock_map().dom().contains(p) {
                old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() is None
            } else { entry_k.ctn_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() },
        forall|p: RwLockProcessPtr| #![trigger entry_k.prc_mp.spec_index(p)] #![trigger old(steps).snapshot_k().prc_mp.spec_index(p)]
            old(steps).snapshot_k().prc_mp.dom().contains(p) && entry_k.prc_mp.dom().contains(p) ==> if entry_lctx.process_lock_map().dom().contains(p) {
                old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() is None
            } else { entry_k.prc_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() },
        forall|p: RwLockThreadPtr| #![trigger entry_k.thrd_mp.spec_index(p)] #![trigger old(steps).snapshot_k().thrd_mp.spec_index(p)]
            old(steps).snapshot_k().thrd_mp.dom().contains(p) && entry_k.thrd_mp.dom().contains(p) ==> if entry_lctx.thread_lock_map().dom().contains(p) {
                old(steps).snapshot_k().thrd_mp.spec_index(p).locking_thread() is None
            } else { entry_k.thrd_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().thrd_mp.spec_index(p).locking_thread() },
        forall|p: RwLockEndpointPtr| #![trigger entry_k.ep_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ep_mp.spec_index(p)]
            old(steps).snapshot_k().ep_mp.dom().contains(p) && entry_k.ep_mp.dom().contains(p) ==> if entry_lctx.endpoint_lock_map().dom().contains(p) {
                old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() is None
            } else { entry_k.ep_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger entry_k.pt_mp.spec_index(p)] #![trigger old(steps).snapshot_k().pt_mp.spec_index(p)]
            old(steps).snapshot_k().pt_mp.dom().contains(p) && entry_k.pt_mp.dom().contains(p) ==> if entry_lctx.pagetable_lock_map().dom().contains(p) {
                old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() is None
            } else { entry_k.pt_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() },
        entry_k.pt_lower == old(steps).snapshot_k().pt_lower,
        forall|p: RwLockPageTableRoot| #![trigger entry_k.it_mp.spec_index(p)] #![trigger old(steps).snapshot_k().it_mp.spec_index(p)]
            old(steps).snapshot_k().it_mp.dom().contains(p) && entry_k.it_mp.dom().contains(p) ==> if entry_lctx.iommu_table_lock_map().dom().contains(p) {
                old(steps).snapshot_k().it_mp.spec_index(p).locking_thread() is None
            } else { entry_k.it_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().it_mp.spec_index(p).locking_thread() },
        forall|i: CpuId| #![trigger entry_k.cpu_arr.spec_index(i)] #![trigger old(steps).snapshot_k().cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> if entry_lctx.cpu_lock_map().dom().contains(i) {
                old(steps).snapshot_k().cpu_arr.spec_index(i).value.locking_thread() is None
            } else { entry_k.cpu_arr.spec_index(i).value.locking_thread() == old(steps).snapshot_k().cpu_arr.spec_index(i).value.locking_thread() },
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), &entry_k),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, entry_k.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), &entry_k),
        entry_lctx.cpu_lock_map().dom() =~= set![cpu_id],
        entry_lctx.container_lock_map().dom().is_empty(),
        entry_lctx.process_lock_map().dom().is_empty(),
        entry_lctx.thread_lock_map().dom() =~= set![callee_ptr, caller_ptr],
        entry_lctx.endpoint_lock_map().dom() =~= set![ep_ptr],
        entry_lctx.pagetable_lock_map().dom().is_empty(),
        entry_lctx.pagetable_window_lock_map().dom().is_empty(),
        entry_lctx.iommu_table_lock_map().dom().is_empty(),
        entry_k.cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(entry_k.thrd_mp.spec_index(callee_ptr).view().owning_proc),
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(callee_ptr),
        entry_k.prc_mp.dom().contains(entry_k.thrd_mp.spec_index(callee_ptr).view().owning_proc),
        entry_k.ctn_mp.dom().contains(entry_k.thrd_mp.spec_index(callee_ptr).view().owning_container),
        entry_k.thrd_mp.dom().contains(callee_ptr),
        entry_k.thrd_mp.spec_index(callee_ptr).being_killed() == false,
        entry_k.thrd_mp.spec_index(callee_ptr).view().syscall_progress.view() is None,
        entry_k.thrd_mp.spec_index(callee_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        entry_k.thrd_mp.spec_index(callee_ptr).view().caller == Some(caller_ptr),
        entry_k.thrd_mp.spec_index(callee_ptr).view().callee is None,
        entry_k.thrd_mp.spec_index(callee_ptr).view().endpoint_descriptors.spec_index(ep_idx) == Some(ep_ptr),
        entry_k.ep_mp.dom().contains(ep_ptr),
        !entry_k.ep_mp.spec_index(ep_ptr).view().queue.view().contains(callee_ptr),
        entry_k.ep_mp.spec_index(ep_ptr).view().queue.view().len() == entry_k.ep_mp.spec_index(ep_ptr).view().queue.length,
        entry_k.ep_mp.spec_index(ep_ptr).view().queue.view().len() == 0 || entry_k.ep_mp.spec_index(ep_ptr).view().queue_state is RECEIVE,
        caller_ptr != callee_ptr,
        entry_k.thrd_mp.dom().contains(caller_ptr),
        entry_k.thrd_mp.spec_index(caller_ptr).being_killed() == false,
        entry_k.thrd_mp.spec_index(caller_ptr).view().state is WAITING_REPLY,
        entry_k.thrd_mp.spec_index(caller_ptr).view().callee == Some(callee_ptr),
        entry_k.thrd_mp.spec_index(caller_ptr).view().owning_container == entry_k.thrd_mp.spec_index(callee_ptr).view().owning_container,
        entry_k.prc_mp.dom().contains(entry_k.thrd_mp.spec_index(caller_ptr).view().owning_proc),
        (switched_pcid is None) == (entry_k.thrd_mp.spec_index(caller_ptr).view().owning_proc == entry_k.thrd_mp.spec_index(callee_ptr).view().owning_proc),
        switched_pcid matches Some(pcid) ==> pcid == entry_k.prc_mp.spec_index(entry_k.thrd_mp.spec_index(caller_ptr).view().owning_proc).view_rodata().view().pcid && pcid_valid(pcid),
        locked_k == (KernelK { pcid_needflush: locked_k.pcid_needflush, ..entry_k }),
        forall|c: CpuId, p: Pcid| #![trigger locked_k.pcid_needflush.spec_index(c, p)] #![trigger entry_k.pcid_needflush.spec_index(c, p)] index_valid(NUM_CPUS, c) && pcid_valid(p) ==> {
            &&& locked_k.pcid_needflush.spec_index(c, p).view() == entry_k.pcid_needflush.spec_index(c, p).view()
            &&& ((c != cpu_id || switched_pcid != Some(p)) ==> locked_k.pcid_needflush.spec_index(c, p) == entry_k.pcid_needflush.spec_index(c, p))
        },
        kernel_cpu_process_thread_nonlock_fields_unchanged(&entry_k, &locked_k),
        kernel_endpoint_nonlock_fields_unchanged(entry_k.ep_mp, locked_k.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&entry_k, &locked_k),
        ipc_reply_handoff_eof_transition_framing(locked_k, *old(krnl), cpu_id, callee_ptr, ep_ptr, ep_idx, caller_ptr),
        kernel_container_nonlock_fields_and_quotas_unchanged(&locked_k, old(krnl)),
        old(krnl).inv(),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        entry_k.cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
        old(steps).snapshot_k().cpu_op.view().view()[cpu_id as int] is Trap,
        edp_idx_valid(ep_idx),
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        switched_pcid matches Some(pcid) ==> old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).thrd_mp.dom().contains(callee_ptr),
        old(krnl).thrd_mp.spec_index(callee_ptr).being_killed() == false,
        !old(krnl).thrd_mp.spec_index(callee_ptr).view().exited.view(),
        old(krnl).thrd_mp.spec_index(callee_ptr).view().state is RECEIVING_CALL,
        old(krnl).thrd_mp.spec_index(callee_ptr).view().free_quota_pending_clean(),
        old(krnl).thrd_mp.spec_index(callee_ptr).view().temp_alloc_clean(),
        old(krnl).thrd_mp.spec_index(callee_ptr).view().syscall_progress.view() is None,
        old(krnl).thrd_mp.dom().contains(caller_ptr),
        old(krnl).thrd_mp.spec_index(caller_ptr).being_killed() == false,
        !old(krnl).thrd_mp.spec_index(caller_ptr).view().exited.view(),
        old(krnl).thrd_mp.spec_index(caller_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thrd_mp.spec_index(caller_ptr).view().free_quota_pending_clean(),
        old(krnl).thrd_mp.spec_index(caller_ptr).view().temp_alloc_clean(),
        old(krnl).thrd_mp.spec_index(caller_ptr).view().syscall_progress.view() is None,
        old(krnl).ep_mp.dom().contains(ep_ptr),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), callee_ptr, TypedLockMode::Write),
        callee_lock_perm.state() is WriteLock,
        callee_lock_perm.thread_id() == old(lctx).thread_id(),
        callee_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(callee_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), caller_ptr, TypedLockMode::Write),
        caller_lock_perm.state() is WriteLock,
        caller_lock_perm.thread_id() == old(lctx).thread_id(),
        caller_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(caller_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), ep_ptr, TypedLockMode::Write),
        endpoint_lock_perm.state() is WriteLock,
        endpoint_lock_perm.thread_id() == old(lctx).thread_id(),
        endpoint_lock_perm.lock_id() == old(krnl).ep_mp.spec_index(ep_ptr).locking_thread()->Write_lock_id,
        switched_pcid matches Some(pcid) ==> {
            &&& typed_lock_map_contains_mode(old(lctx).pcid_needflush_lock_map(), (cpu_id, pcid), TypedLockMode::Write)
            &&& needflush_perm matches Some(perm) && perm.state() is WriteLock && perm.thread_id() == old(lctx).thread_id()
            &&& needflush_perm.unwrap().lock_id() == old(krnl).pcid_needflush.spec_index(cpu_id, pcid).locking_thread()->Write_lock_id
        },
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() =~= set![callee_ptr, caller_ptr],
        old(lctx).endpoint_lock_map().dom() =~= set![ep_ptr],
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom() =~= match switched_pcid { Some(pcid) => set![(cpu_id, pcid)], None => Set::empty() },
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(old(steps).snapshot_k()), new_u: kernel_k_to_kernel_u(*final(krnl)) }),
        ipc_reply_handoff_step_pre(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, ep_idx),
        ipc_reply_handoff_step(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, ep_idx, context_switch_flushed_pcid(old(steps).snapshot_k(), cpu_id, caller_ptr)),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
{
    if let Some(pcid) = switched_pcid {
        let tracked perm = needflush_perm.tracked_unwrap();
        krnl.wunlock_pcid_needflush(cpu_id, pcid, Tracked(&mut *lctx), Tracked(perm));
    }
    krnl.wunlock_thread(caller_ptr, Tracked(&mut *lctx), Tracked(caller_lock_perm));
    krnl.wunlock_thread(callee_ptr, Tracked(&mut *lctx), Tracked(callee_lock_perm));
    krnl.wunlock_endpoint(ep_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm));
    assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { reveal(ipc_reply_handoff_eof_transition_framing); };
    krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view()) by { reveal(ipc_reply_handoff_eof_transition_framing); };
        let ghost flushed_pcid = context_switch_flushed_pcid(old(steps).snapshot_k(), cpu_id, caller_ptr);
        assert(kernel_ipc_reply_handoff_fields(&steps.snapshot_k(), &*krnl, cpu_id, callee_ptr, ep_ptr, ep_idx, caller_ptr, flushed_pcid) && krnl.ctn_mp == steps.snapshot_k().ctn_mp) by {
            broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive;
            reveal(kernel_ipc_reply_handoff_fields); reveal(ipc_reply_handoff_eof_transition_framing);
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
            reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged); reveal(kernel_endpoint_nonlock_fields_unchanged);
            assert(krnl.cpu_trap_frame.view().view().remove(cpu_id) =~= steps.snapshot_k().cpu_trap_frame.view().view().remove(cpu_id));
        };
        steps.end_kernel_step_ipc_reply_handoff(&*krnl, &*lctx, cpu_id, callee_ptr, ep_ptr, ep_idx, caller_ptr, flushed_pcid);
        assert(!old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.being_killed()) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged); };
        ipc_reply_handoff_step_from_u(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, callee_ptr, ep_ptr, ep_idx, caller_ptr, flushed_pcid, old(steps).snapshot_k());
    }
}
}
