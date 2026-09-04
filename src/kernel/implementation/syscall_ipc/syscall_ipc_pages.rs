use vstd::prelude::*;

use crate::*;
use super::syscall_ipc_transition::{
    ipc_schedule_waiting_peer_and_finish,
};

verus! {

#[derive(Clone, Copy)]
pub(super) enum IpcPagesMapping {
    Ready,
    SameProcess,
    SourceUnmapped,
    OwnerMismatch,
    NoQuota,
    Invalid,
    InUse,
}

pub(super) open spec fn ipc_pages_base_roots_context(
    krnl: &KernelK,
    lctx: &LocalContext,
    cpu_id: CpuId,
    process_ptr: RwLockProcessPtr,
    current_thread_ptr: RwLockThreadPtr,
    endpoint_ptr: RwLockEndpointPtr,
    peer_thread_ptr: RwLockThreadPtr,
    cpu_lock_perm: &LockPerm,
    process_lock_perm: &LockPerm,
    current_thread_lock_perm: &LockPerm,
    endpoint_lock_perm: &LockPerm,
    peer_thread_lock_perm: &LockPerm,
) -> bool {
    &&& krnl.inv()
    &&& typed_lock_maps_aligned(krnl, lctx)
    &&& lock_id_set_aligned(lctx)
    &&& lctx.held_lock_majors_lt(SCHEDULER_LOCK_MAJOR)
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& current_thread_ptr != peer_thread_ptr
    &&& krnl.cpu_arr.spec_index(cpu_id).view().wlocked_by(lctx)
    &&& krnl.cpu_arr.spec_index(cpu_id).view().being_killed() == false
    &&& cpu_lock_perm.state() is WriteLock
    &&& cpu_lock_perm.thread_id() == lctx.thread_id()
    &&& cpu_lock_perm.lock_id() == krnl.cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id
    &&& krnl.prc_mp.dom().contains(process_ptr)
    &&& krnl.prc_mp.spec_index(process_ptr).wlocked_by(lctx)
    &&& krnl.prc_mp.spec_index(process_ptr).being_killed() == false
    &&& process_lock_perm.state() is WriteLock
    &&& process_lock_perm.thread_id() == lctx.thread_id()
    &&& process_lock_perm.lock_id() == krnl.prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id
    &&& krnl.thr_mp.dom().contains(current_thread_ptr)
    &&& krnl.thr_mp.spec_index(current_thread_ptr).wlocked_by(lctx)
    &&& krnl.thr_mp.spec_index(current_thread_ptr).being_killed() == false
    &&& current_thread_lock_perm.state() is WriteLock
    &&& current_thread_lock_perm.thread_id() == lctx.thread_id()
    &&& current_thread_lock_perm.lock_id() == krnl.thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id
    &&& krnl.ep_mp.dom().contains(endpoint_ptr)
    &&& krnl.ep_mp.spec_index(endpoint_ptr).wlocked_by(lctx)
    &&& endpoint_lock_perm.state() is WriteLock
    &&& endpoint_lock_perm.thread_id() == lctx.thread_id()
    &&& endpoint_lock_perm.lock_id() == krnl.ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id
    &&& krnl.thr_mp.dom().contains(peer_thread_ptr)
    &&& krnl.thr_mp.spec_index(peer_thread_ptr).wlocked_by(lctx)
    &&& krnl.thr_mp.spec_index(peer_thread_ptr).being_killed() == false
    &&& peer_thread_lock_perm.state() is WriteLock
    &&& peer_thread_lock_perm.thread_id() == lctx.thread_id()
    &&& peer_thread_lock_perm.lock_id() == krnl.thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id
    &&& krnl.cpu_arr.spec_index(cpu_id).view().view().state is Running
    &&& krnl.cpu_arr.spec_index(cpu_id).view().view().current_process == Some(process_ptr)
    &&& krnl.cpu_arr.spec_index(cpu_id).view().view().current_thread == Some(current_thread_ptr)
    &&& krnl.thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id })
    &&& krnl.thr_mp.spec_index(current_thread_ptr).view().owning_proc == process_ptr
    &&& krnl.thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean()
    &&& krnl.thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean()
    &&& (krnl.thr_mp.spec_index(peer_thread_ptr).view().state is SENDING
        || krnl.thr_mp.spec_index(peer_thread_ptr).view().state is RECEIVING)
    &&& krnl.thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr)
    &&& krnl.thr_mp.spec_index(peer_thread_ptr).view().free_quota_pending_clean()
    &&& krnl.thr_mp.spec_index(peer_thread_ptr).view().temp_alloc_clean()
    &&& krnl.ep_mp.spec_index(endpoint_ptr).view().queue.len() != 0
    &&& krnl.ep_mp.spec_index(endpoint_ptr).view().queue.view().spec_index(0) == peer_thread_ptr
}

#[verifier::spinoff_prover]
fn ipc_share_pages_locked(
    krnl: &mut KernelK,
    source_range: &VaRange4K,
    target_range: &VaRange4K,
    source_thread: RwLockThreadPtr,
    target_thread: RwLockThreadPtr,
    source_process: RwLockProcessPtr,
    target_process: RwLockProcessPtr,
    source_container: RwLockContainerPtr,
    target_container: RwLockContainerPtr,
    held_process: RwLockProcessPtr,
    held_endpoint: RwLockEndpointPtr,
    current_thread_ptr: RwLockThreadPtr,
    peer_thread_ptr: RwLockThreadPtr,
    source_pagetable: RwLockPageTableRoot,
    target_pagetable: RwLockPageTableRoot,
    cpu_id: CpuId,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>,
    Tracked(source_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(target_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>,
    Tracked(target_pagetable_lock_perm): Tracked<&LockPerm>,
    Tracked(cpu_lock_perm): Tracked<&LockPerm>,
    Tracked(process_lock_perm): Tracked<&LockPerm>,
    Tracked(current_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(endpoint_lock_perm): Tracked<&LockPerm>,
    Tracked(peer_thread_lock_perm): Tracked<&LockPerm>,
) -> (ret: IpcPagesMapping)
    requires
        share_mapping_4k_held_context(old(krnl), old(lctx), source_thread, target_thread, target_process, target_container, source_pagetable, target_pagetable, source_thread_lock_perm, target_thread_lock_perm, source_pagetable_lock_perm, target_pagetable_lock_perm),
        ipc_pages_base_roots_context(old(krnl), old(lctx), cpu_id, held_process, current_thread_ptr, held_endpoint, peer_thread_ptr, cpu_lock_perm, process_lock_perm, current_thread_lock_perm, endpoint_lock_perm, peer_thread_lock_perm),
        cpu_objects_unlocked_except(old(krnl).cpu_arr, old(lctx).thread_id(), set![cpu_id]),
        container_objects_unlocked(old(krnl).ctn_mp, old(lctx).thread_id()),
        process_objects_unlocked_except(old(krnl).prc_mp, old(lctx).thread_id(), set![held_process]),
        endpoint_objects_unlocked_except(old(krnl).ep_mp, old(lctx).thread_id(), set![held_endpoint]),
        iommu_table_objects_unlocked(old(krnl).it_mp, old(lctx).thread_id()),
        scheduler_objects_unlocked(old(krnl).sched_mp, old(lctx).thread_id()),
        pcid_allocator_objects_unlocked(old(krnl).pcid_allc_mp, old(lctx).thread_id()),
        allocator_objects_unlocked(old(krnl).allc_2m_mp, old(lctx).thread_id()),
        allocator_objects_unlocked(old(krnl).allc_1g_mp, old(lctx).thread_id()),
        (source_thread == current_thread_ptr && target_thread == peer_thread_ptr) || (source_thread == peer_thread_ptr && target_thread == current_thread_ptr),
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        source_range.len <= usize::MAX / 3usize,
        old(krnl).thr_mp.spec_index(source_thread).view().owning_proc == source_process,
        old(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process,
        old(krnl).thr_mp.spec_index(source_thread).view().owning_container == source_container,
        old(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        mmap_4k_allocation_ready(old(krnl), old(lctx)),
        thread_objects_unlocked_except(old(krnl).thr_mp, old(lctx).thread_id(), set![source_thread, target_thread]),
        pagetable_objects_unlocked_except(old(krnl).pt_mp, old(lctx).thread_id(), set![source_pagetable, target_pagetable]),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(krnl).cpu_arr.lock_id_by_index(cpu_id) == old(krnl).cpu_arr.lock_id_by_index(cpu_id),
        final(krnl).prc_mp.lock_id_by_key(held_process) == old(krnl).prc_mp.lock_id_by_key(held_process),
        final(krnl).thr_mp.lock_id_by_key(current_thread_ptr) == old(krnl).thr_mp.lock_id_by_key(current_thread_ptr),
        final(krnl).thr_mp.lock_id_by_key(peer_thread_ptr) == old(krnl).thr_mp.lock_id_by_key(peer_thread_ptr),
        final(krnl).ep_mp.lock_id_by_key(held_endpoint) == old(krnl).ep_mp.lock_id_by_key(held_endpoint),
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        ret is Ready ==> final(steps).steps.len() == old(steps).steps.len() + source_range.len,
        !(ret is Ready) ==> final(steps).steps.len() == old(steps).steps.len(),
        ret is Ready || ret is SourceUnmapped || ret is OwnerMismatch || ret is NoQuota || ret is Invalid || ret is InUse,
        share_mapping_4k_held_context(final(krnl), final(lctx), source_thread, target_thread, target_process, target_container, source_pagetable, target_pagetable, source_thread_lock_perm, target_thread_lock_perm, source_pagetable_lock_perm, target_pagetable_lock_perm),
        ipc_pages_base_roots_context(final(krnl), final(lctx), cpu_id, held_process, current_thread_ptr, held_endpoint, peer_thread_ptr, cpu_lock_perm, process_lock_perm, current_thread_lock_perm, endpoint_lock_perm, peer_thread_lock_perm),
        cpu_objects_unlocked_except(final(krnl).cpu_arr, final(lctx).thread_id(), set![cpu_id]),
        container_objects_unlocked(final(krnl).ctn_mp, final(lctx).thread_id()),
        process_objects_unlocked_except(final(krnl).prc_mp, final(lctx).thread_id(), set![held_process]),
        endpoint_objects_unlocked_except(final(krnl).ep_mp, final(lctx).thread_id(), set![held_endpoint]),
        iommu_table_objects_unlocked(final(krnl).it_mp, final(lctx).thread_id()),
        scheduler_objects_unlocked(final(krnl).sched_mp, final(lctx).thread_id()),
        pcid_allocator_objects_unlocked(final(krnl).pcid_allc_mp, final(lctx).thread_id()),
        allocator_objects_unlocked(final(krnl).allc_2m_mp, final(lctx).thread_id()),
        allocator_objects_unlocked(final(krnl).allc_1g_mp, final(lctx).thread_id()),
        thread_objects_unlocked_except(final(krnl).thr_mp, final(lctx).thread_id(), set![source_thread, target_thread]),
        pagetable_objects_unlocked_except(final(krnl).pt_mp, final(lctx).thread_id(), set![source_pagetable, target_pagetable]),
        mmap_4k_allocation_ready(final(krnl), final(lctx)),
{
    let source_start_indices = va2index(source_range.start);
    proof {
        assert({
            &&& krnl.pt_mp.perms_wf()
            &&& krnl.pt_mp.spec_index(source_pagetable).inv()
            &&& krnl.pt_mp.spec_index(target_pagetable).inv()
            &&& krnl.thr_mp.perms_wf()
            &&& krnl.thr_mp.spec_index(target_thread).inv()
        }) by { reveal(pagetable_perms_wf); reveal(thread_perms_wf); };
    }
    let source_pt = krnl.pt_mp.borrow(source_pagetable, Tracked(source_pagetable_lock_perm));
    if source_start_indices.0 < source_pt.kernel_l4_end {
        return IpcPagesMapping::Invalid;
    }
    if !share_mapping_4k_source_precheck(krnl, source_range, source_pagetable, Tracked(&*lctx), Tracked(source_pagetable_lock_perm)) {
        return IpcPagesMapping::SourceUnmapped;
    }

    let range_len = target_range.len;
    let target_thread_ref = krnl.thr_mp.borrow(target_thread, Tracked(target_thread_lock_perm));
    if target_thread_ref.quota_4k < 3usize * range_len {
        return IpcPagesMapping::NoQuota;
    }
    let target_start = target_range.start;
    let target_start_indices = va2index(target_start);
    let target_pt = krnl.pt_mp.borrow(target_pagetable, Tracked(target_pagetable_lock_perm));
    if target_start_indices.0 < target_pt.kernel_l4_end {
        return IpcPagesMapping::Invalid;
    }
    let target_end_index = range_len - 1;
    let target_end = target_range.index(target_end_index);
    proof {
        assert(target_end == spec_va_add_range(target_start, target_end_index)) by { target_range.va_range_lemma(); };
        assert(target_start <= target_end) by (bit_vector)
            requires
                range_len > 0,
                range_len <= usize::MAX / 4096usize,
                target_start < usize::MAX - range_len * 4096usize,
                target_end_index == range_len - 1,
                target_end == (target_start + target_end_index * 4096usize) as usize,
        ;
    }
    if !target_pt.mapping_4k_va_range_empty(target_start, target_end) {
        return IpcPagesMapping::InUse;
    }
    if !target_pt.mapping_4k_va_range_buildable(target_range) {
        return IpcPagesMapping::InUse;
    }

    proof {
        assert({
            &&& krnl.ctn_mp.dom().contains(source_container)
            &&& krnl.ctn_mp.dom().contains(target_container)
            &&& container_perms_wf(krnl.ctn_mp)
            &&& container_tree_wf(krnl.rt_ctn, krnl.ctn_mp)
        }) by { reveal(container_thread_wf); };
    }
    let containers_compatible = if source_container == target_container {
        true
    } else {
        container_tree_check_is_ancestor(krnl.rt_ctn, &krnl.ctn_mp, source_container, target_container)
    };
    let owners_compatible = if containers_compatible {
        proof {
            assert(share_mapping_4k_range_owner_compatible(krnl, source_pagetable, target_thread, source_range)) by {
                source_range.va_range_lemma();
                reveal(mapped_4k_page_pagetable_wf); reveal(container_process_page_pagetable_wf); reveal(container_page_owner_wf); reveal(container_thread_wf); reveal(process_thread_wf); reveal(process_pagetable_match); reveal(container_perms_wf); reveal(container_subtree_set_wf); reveal(container_uppertree_seq_wf); reveal(container_subtree_set_exclusive);
            };
        }
        true
    } else {
        share_mapping_4k_source_owner_precheck(krnl, source_range, source_thread, target_thread, target_process, target_container, source_pagetable, target_pagetable, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(source_thread_lock_perm), Tracked(target_thread_lock_perm), Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm))
    };
    proof {
        assert({
            &&& krnl.thr_mp.lock_id_by_key(current_thread_ptr) == old(krnl).thr_mp.lock_id_by_key(current_thread_ptr)
            &&& krnl.thr_mp.lock_id_by_key(peer_thread_ptr) == old(krnl).thr_mp.lock_id_by_key(peer_thread_ptr)
        }) by {
            reveal(thread_perms_wf);
            lock_id_fields_eq_imply_eq();
        };
    }
    if !owners_compatible {
        return IpcPagesMapping::OwnerMismatch;
    }

    proof {
        assert({
            &&& krnl.ctn_mp.dom().contains(target_container)
            &&& krnl.ctn_mp.view().spec_index(target_container)
                .is_init()
            &&& krnl.ctn_mp.view().spec_index(target_container).addr() == target_container
        }) by { reveal(container_thread_wf); reveal(container_perms_wf); };
    }
    let target_allocator = krnl.ctn_mp.borrow_rodata(target_container)
        .borrow().allocator_ptr_4k;
    proof {
        assert(mmap_4k_held_context(krnl, &*lctx, target_allocator, target_thread, target_process, target_container, cpu_id, target_pagetable, target_thread_lock_perm, target_pagetable_lock_perm)) by {
            reveal(container_allocator_wf); reveal(container_thread_wf); reveal(process_thread_wf); reveal(process_pagetable_match);
            lock_id_fields_eq_imply_eq();
        };
    }
    share_mapping_4k_build_and_share(krnl, source_range, target_range, target_allocator, source_thread, target_thread, target_process, target_container, cpu_id, source_pagetable, target_pagetable, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(source_thread_lock_perm), Tracked(target_thread_lock_perm), Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm));
    proof {
        assert(krnl.thr_mp.lock_id_by_key(source_thread) == old(krnl).thr_mp.lock_id_by_key(source_thread)) by {
            reveal(thread_perms_wf);
            lock_id_fields_eq_imply_eq();
        };
    }
    IpcPagesMapping::Ready
}

#[verifier::spinoff_prover]
pub(super) fn ipc_share_pages_mapping(
    krnl: &mut KernelK,
    source_range: &VaRange4K,
    target_range: &VaRange4K,
    source_thread: RwLockThreadPtr,
    target_thread: RwLockThreadPtr,
    cpu_id: CpuId,
    process_ptr: RwLockProcessPtr,
    current_thread_ptr: RwLockThreadPtr,
    endpoint_ptr: RwLockEndpointPtr,
    peer_thread_ptr: RwLockThreadPtr,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>,
    Tracked(cpu_lock_perm): Tracked<&LockPerm>,
    Tracked(process_lock_perm): Tracked<&LockPerm>,
    Tracked(current_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(endpoint_lock_perm): Tracked<&LockPerm>,
    Tracked(peer_thread_lock_perm): Tracked<&LockPerm>,
) -> (ret: IpcPagesMapping)
    requires
        ipc_pages_base_roots_context(old(krnl), old(lctx), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr, cpu_lock_perm, process_lock_perm, current_thread_lock_perm, endpoint_lock_perm, peer_thread_lock_perm),
        old(lctx).base_lock_scope(set![cpu_id], Set::empty(), set![process_ptr], set![current_thread_ptr, peer_thread_ptr], set![endpoint_ptr]),
        cpu_objects_unlocked_except(old(krnl).cpu_arr, old(lctx).thread_id(), set![cpu_id]),
        page_objects_unlocked(old(krnl).pg_arr, old(lctx).thread_id()),
        container_objects_unlocked(old(krnl).ctn_mp, old(lctx).thread_id()),
        process_objects_unlocked_except(old(krnl).prc_mp, old(lctx).thread_id(), set![process_ptr]),
        thread_objects_unlocked_except(old(krnl).thr_mp, old(lctx).thread_id(), set![current_thread_ptr, peer_thread_ptr]),
        endpoint_objects_unlocked_except(old(krnl).ep_mp, old(lctx).thread_id(), set![endpoint_ptr]),
        pagetable_objects_unlocked(old(krnl).pt_mp, old(lctx).thread_id()),
        iommu_table_objects_unlocked(old(krnl).it_mp, old(lctx).thread_id()),
        scheduler_objects_unlocked(old(krnl).sched_mp, old(lctx).thread_id()),
        pcid_allocator_objects_unlocked(old(krnl).pcid_allc_mp, old(lctx).thread_id()),
        allocator_objects_unlocked(old(krnl).allc_4k_mp, old(lctx).thread_id()),
        allocator_objects_unlocked(old(krnl).allc_2m_mp, old(lctx).thread_id()),
        allocator_objects_unlocked(old(krnl).allc_1g_mp, old(lctx).thread_id()),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        source_range.len <= usize::MAX / 3usize,
        (source_thread == current_thread_ptr && target_thread == peer_thread_ptr)
            || (source_thread == peer_thread_ptr && target_thread == current_thread_ptr),
    ensures
        ipc_pages_base_roots_context(final(krnl), final(lctx), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr, cpu_lock_perm, process_lock_perm, current_thread_lock_perm, endpoint_lock_perm, peer_thread_lock_perm),
        final(lctx).base_lock_scope(set![cpu_id], Set::empty(), set![process_ptr], set![current_thread_ptr, peer_thread_ptr], set![endpoint_ptr]),
        cpu_objects_unlocked_except(final(krnl).cpu_arr, final(lctx).thread_id(), set![cpu_id]),
        page_objects_unlocked(final(krnl).pg_arr, final(lctx).thread_id()),
        container_objects_unlocked(final(krnl).ctn_mp, final(lctx).thread_id()),
        process_objects_unlocked_except(final(krnl).prc_mp, final(lctx).thread_id(), set![process_ptr]),
        thread_objects_unlocked_except(final(krnl).thr_mp, final(lctx).thread_id(), set![current_thread_ptr, peer_thread_ptr]),
        endpoint_objects_unlocked_except(final(krnl).ep_mp, final(lctx).thread_id(), set![endpoint_ptr]),
        pagetable_objects_unlocked(final(krnl).pt_mp, final(lctx).thread_id()),
        iommu_table_objects_unlocked(final(krnl).it_mp, final(lctx).thread_id()),
        scheduler_objects_unlocked(final(krnl).sched_mp, final(lctx).thread_id()),
        pcid_allocator_objects_unlocked(final(krnl).pcid_allc_mp, final(lctx).thread_id()),
        allocator_objects_unlocked(final(krnl).allc_4k_mp, final(lctx).thread_id()),
        allocator_objects_unlocked(final(krnl).allc_2m_mp, final(lctx).thread_id()),
        allocator_objects_unlocked(final(krnl).allc_1g_mp, final(lctx).thread_id()),
        ret is SameProcess ==>
            final(lctx).kernel_view_locking_state() is Acquire,
        !(ret is SameProcess) ==>
            final(lctx).kernel_view_locking_state() is Release,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        ret is Ready ==>
            final(steps).steps.len() == old(steps).steps.len() + source_range.len,
        !(ret is Ready) ==>
            final(steps).steps.len() == old(steps).steps.len(),
{
    proof {
        assert({
            &&& krnl.thr_mp.perms_wf()
            &&& krnl.thr_mp.spec_index(current_thread_ptr).is_init()
            &&& krnl.thr_mp.spec_index(peer_thread_ptr).is_init()
        }) by { reveal(thread_perms_wf); };
    }
    let source_process;
    let source_container;
    let source_pagetable;
    if source_thread == current_thread_ptr {
        let source_thread_ref = krnl.thr_mp.borrow(source_thread, Tracked(current_thread_lock_perm));
        source_process = source_thread_ref.owning_proc;
        source_container = source_thread_ref.owning_container;
        source_pagetable = source_thread_ref.proc_pagetable_ptr;
    } else {
        let source_thread_ref = krnl.thr_mp.borrow(source_thread, Tracked(peer_thread_lock_perm));
        source_process = source_thread_ref.owning_proc;
        source_container = source_thread_ref.owning_container;
        source_pagetable = source_thread_ref.proc_pagetable_ptr;
    }
    let target_process;
    let target_container;
    let target_pagetable;
    if target_thread == current_thread_ptr {
        let target_thread_ref = krnl.thr_mp.borrow(target_thread, Tracked(current_thread_lock_perm));
        target_process = target_thread_ref.owning_proc;
        target_container = target_thread_ref.owning_container;
        target_pagetable = target_thread_ref.proc_pagetable_ptr;
    } else {
        let target_thread_ref = krnl.thr_mp.borrow(target_thread, Tracked(peer_thread_lock_perm));
        target_process = target_thread_ref.owning_proc;
        target_container = target_thread_ref.owning_container;
        target_pagetable = target_thread_ref.proc_pagetable_ptr;
    }

    if source_process == target_process {
        return IpcPagesMapping::SameProcess;
    }
    proof {
        assert({
            &&& krnl.prc_mp.dom().contains(source_process)
            &&& krnl.prc_mp.dom().contains(target_process)
            &&& krnl.pt_mp.dom().contains(source_pagetable)
            &&& krnl.pt_mp.dom().contains(target_pagetable)
            &&& krnl.pt_mp.spec_index(source_pagetable).view().proc_ptr == source_process
            &&& krnl.pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process
            &&& source_pagetable != target_pagetable
        }) by { reveal(process_thread_wf); reveal(process_pagetable_match); };
        assert({
            &&& krnl.pt_mp.lock_id_by_key(source_pagetable).major == PAGE_TABLE_LOCK_MAJOR
            &&& krnl.pt_mp.lock_id_by_key(target_pagetable).major == PAGE_TABLE_LOCK_MAJOR
        }) by { reveal(pagetable_perms_wf); };
        assert({
            &&& !krnl.pt_mp.spec_index(source_pagetable).locked_by_thread(lctx.thread_id())
            &&& !krnl.pt_mp.spec_index(target_pagetable).locked_by_thread(lctx.thread_id())
        }) by {
            reveal(LockedMap::typed_lock_map_aligned);
        };
    }

    let (Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm)) = krnl.wlock_pagetable_pair(source_pagetable, target_pagetable, Tracked(&mut *lctx));
    proof {
        assert(share_mapping_4k_held_context(
                krnl, &*lctx, source_thread, target_thread,
                target_process, target_container,
                source_pagetable, target_pagetable,
                if source_thread == current_thread_ptr {
                    current_thread_lock_perm
                } else {
                    peer_thread_lock_perm
                },
                if target_thread == current_thread_ptr {
                    current_thread_lock_perm
                } else {
                    peer_thread_lock_perm
                },
                &source_pagetable_lock_perm,
                &target_pagetable_lock_perm,
            )) by { reveal(process_thread_wf); reveal(process_pagetable_match); reveal(pagetable_perms_wf); };
        assert(mmap_4k_allocation_ready(krnl, &*lctx)) by { reveal(LocalContext::holds_no_allocator_locks); };
    }
    let result = ipc_share_pages_locked(
        krnl, source_range, target_range,
        source_thread, target_thread, source_process, target_process,
        source_container, target_container,
        process_ptr, endpoint_ptr, current_thread_ptr, peer_thread_ptr,
        source_pagetable, target_pagetable, cpu_id,
        Tracked(&mut *lctx), Tracked(&mut *steps),
        Tracked(if source_thread == current_thread_ptr {
            current_thread_lock_perm
        } else {
            peer_thread_lock_perm
        }),
        Tracked(if target_thread == current_thread_ptr {
            current_thread_lock_perm
        } else {
            peer_thread_lock_perm
        }),
        Tracked(&source_pagetable_lock_perm),
        Tracked(&target_pagetable_lock_perm),
        Tracked(cpu_lock_perm),
        Tracked(process_lock_perm),
        Tracked(current_thread_lock_perm),
        Tracked(endpoint_lock_perm),
        Tracked(peer_thread_lock_perm),
    );
    if source_pagetable < target_pagetable {
        krnl.wunlock_pagetable(target_pagetable, Tracked(&mut *lctx), Tracked(target_pagetable_lock_perm));
        krnl.wunlock_pagetable(source_pagetable, Tracked(&mut *lctx), Tracked(source_pagetable_lock_perm));
    } else {
        krnl.wunlock_pagetable(source_pagetable, Tracked(&mut *lctx), Tracked(source_pagetable_lock_perm));
        krnl.wunlock_pagetable(target_pagetable, Tracked(&mut *lctx), Tracked(target_pagetable_lock_perm));
    }
    result
}

pub(super) fn ipc_rendezvous_pages(
    krnl: &mut KernelK,
    source_range: &VaRange4K,
    target_range: &VaRange4K,
    source_thread: RwLockThreadPtr,
    target_thread: RwLockThreadPtr,
    cpu_id: CpuId,
    process_ptr: RwLockProcessPtr,
    current_thread_ptr: RwLockThreadPtr,
    endpoint_ptr: RwLockEndpointPtr,
    peer_thread_ptr: RwLockThreadPtr,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>,
    cpu_lock_perm: Tracked<LockPerm>,
    process_lock_perm: Tracked<LockPerm>,
    current_thread_lock_perm: Tracked<LockPerm>,
    endpoint_lock_perm: Tracked<LockPerm>,
    peer_thread_lock_perm: Tracked<LockPerm>,
) -> (ret: RetValueType)
    requires
        ipc_pages_base_roots_context(old(krnl), old(lctx), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr, &cpu_lock_perm.view(), &process_lock_perm.view(), &current_thread_lock_perm.view(), &endpoint_lock_perm.view(), &peer_thread_lock_perm.view()),
        old(lctx).base_lock_scope(set![cpu_id], Set::empty(), set![process_ptr], set![current_thread_ptr, peer_thread_ptr], set![endpoint_ptr]),
        cpu_objects_unlocked_except(old(krnl).cpu_arr, old(lctx).thread_id(), set![cpu_id]),
        page_objects_unlocked(old(krnl).pg_arr, old(lctx).thread_id()),
        container_objects_unlocked(old(krnl).ctn_mp, old(lctx).thread_id()),
        process_objects_unlocked_except(old(krnl).prc_mp, old(lctx).thread_id(), set![process_ptr]),
        thread_objects_unlocked_except(old(krnl).thr_mp, old(lctx).thread_id(), set![current_thread_ptr, peer_thread_ptr]),
        endpoint_objects_unlocked_except(old(krnl).ep_mp, old(lctx).thread_id(), set![endpoint_ptr]),
        pagetable_objects_unlocked(old(krnl).pt_mp, old(lctx).thread_id()),
        iommu_table_objects_unlocked(old(krnl).it_mp, old(lctx).thread_id()),
        scheduler_objects_unlocked(old(krnl).sched_mp, old(lctx).thread_id()),
        pcid_allocator_objects_unlocked(old(krnl).pcid_allc_mp, old(lctx).thread_id()),
        allocator_objects_unlocked(old(krnl).allc_4k_mp, old(lctx).thread_id()),
        allocator_objects_unlocked(old(krnl).allc_2m_mp, old(lctx).thread_id()),
        allocator_objects_unlocked(old(krnl).allc_1g_mp, old(lctx).thread_id()),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        source_range.len <= usize::MAX / 3usize,
        source_thread != target_thread,
        source_thread == current_thread_ptr
            && target_thread == peer_thread_ptr
            || source_thread == peer_thread_ptr
                && target_thread == current_thread_ptr,
    ensures
        ret is Success
            || ret is ErrorIpcSameProcess
            || ret is ErrorIpcSourceUnmapped
            || ret is ErrorIpcPageOwnerMismatch
            || ret is ErrorNoQuota
            || ret is ErrorVaInUse
            || ret is Error,
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
        ret is Success ==> final(steps).steps.len() == old(steps).steps.len() + source_range.len,
        !(ret is Success) ==> final(steps).steps.len() == old(steps).steps.len(),
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
{
    let tracked cpu_lock_perm = cpu_lock_perm.get();
    let tracked process_lock_perm = process_lock_perm.get();
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked endpoint_lock_perm = endpoint_lock_perm.get();
    let tracked peer_thread_lock_perm = peer_thread_lock_perm.get();

    let pages_result = ipc_share_pages_mapping(krnl, source_range, target_range, source_thread, target_thread, cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&cpu_lock_perm), Tracked(&process_lock_perm), Tracked(&current_thread_lock_perm), Tracked(&endpoint_lock_perm), Tracked(&peer_thread_lock_perm));
    let result;
    if let IpcPagesMapping::Ready = pages_result {
        proof {
            krnl.kernel_step_boundary(&mut *lctx, &mut *steps);
        }
        result = RetValueType::Success;
    } else {
        result = match pages_result {
            IpcPagesMapping::SameProcess =>
                RetValueType::ErrorIpcSameProcess,
            IpcPagesMapping::SourceUnmapped =>
                RetValueType::ErrorIpcSourceUnmapped,
            IpcPagesMapping::OwnerMismatch =>
                RetValueType::ErrorIpcPageOwnerMismatch,
            IpcPagesMapping::NoQuota => RetValueType::ErrorNoQuota,
            IpcPagesMapping::InUse => RetValueType::ErrorVaInUse,
            _ => RetValueType::Error,
        };
        match pages_result {
            IpcPagesMapping::SameProcess => {},
            _ => {
                proof {
                    krnl.kernel_step_boundary(&mut *lctx, &mut *steps);
                }
            },
        }
    }
    ipc_schedule_waiting_peer_and_finish(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr, result, Tracked(cpu_lock_perm), Tracked(process_lock_perm), Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm), Tracked(peer_thread_lock_perm))
}

} // verus!
