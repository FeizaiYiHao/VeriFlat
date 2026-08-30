use vstd::prelude::*;
use vstd::assert_sets_equal;

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
    kernel: &KernelK,
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
    &&& kernel.inv()
    &&& typed_lock_maps_aligned(kernel, lctx)
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& current_thread_ptr != peer_thread_ptr
    &&& kernel.cpu_array.spec_index(cpu_id).view().wlocked_by(lctx)
    &&& kernel.cpu_array.spec_index(cpu_id).view().being_killed() == false
    &&& cpu_lock_perm.state() is WriteLock
    &&& cpu_lock_perm.thread_id() == lctx.thread_id()
    &&& cpu_lock_perm.lock_id()
        == kernel.cpu_array.spec_index(cpu_id).view()
            .locking_thread()->Write_lock_id
    &&& kernel.process_map.dom().contains(process_ptr)
    &&& kernel.process_map.spec_index(process_ptr).wlocked_by(lctx)
    &&& kernel.process_map.spec_index(process_ptr).being_killed() == false
    &&& process_lock_perm.state() is WriteLock
    &&& process_lock_perm.thread_id() == lctx.thread_id()
    &&& process_lock_perm.lock_id()
        == kernel.process_map.spec_index(process_ptr)
            .locking_thread()->Write_lock_id
    &&& kernel.thread_map.dom().contains(current_thread_ptr)
    &&& kernel.thread_map.spec_index(current_thread_ptr).wlocked_by(lctx)
    &&& kernel.thread_map.spec_index(current_thread_ptr).being_killed() == false
    &&& current_thread_lock_perm.state() is WriteLock
    &&& current_thread_lock_perm.thread_id() == lctx.thread_id()
    &&& current_thread_lock_perm.lock_id()
        == kernel.thread_map.spec_index(current_thread_ptr)
            .locking_thread()->Write_lock_id
    &&& kernel.endpoint_map.dom().contains(endpoint_ptr)
    &&& kernel.endpoint_map.spec_index(endpoint_ptr).wlocked_by(lctx)
    &&& endpoint_lock_perm.state() is WriteLock
    &&& endpoint_lock_perm.thread_id() == lctx.thread_id()
    &&& endpoint_lock_perm.lock_id()
        == kernel.endpoint_map.spec_index(endpoint_ptr)
            .locking_thread()->Write_lock_id
    &&& kernel.thread_map.dom().contains(peer_thread_ptr)
    &&& kernel.thread_map.spec_index(peer_thread_ptr).wlocked_by(lctx)
    &&& kernel.thread_map.spec_index(peer_thread_ptr).being_killed() == false
    &&& peer_thread_lock_perm.state() is WriteLock
    &&& peer_thread_lock_perm.thread_id() == lctx.thread_id()
    &&& peer_thread_lock_perm.lock_id()
        == kernel.thread_map.spec_index(peer_thread_ptr)
            .locking_thread()->Write_lock_id
    &&& kernel.cpu_array.spec_index(cpu_id).view().view().state is Running
    &&& kernel.cpu_array.spec_index(cpu_id).view().view().current_process
        == Some(process_ptr)
    &&& kernel.cpu_array.spec_index(cpu_id).view().view().current_thread
        == Some(current_thread_ptr)
    &&& kernel.thread_map.spec_index(current_thread_ptr).view().state
        == (ThreadState::RUNNING { cpu_id })
    &&& kernel.thread_map.spec_index(current_thread_ptr).view().owning_proc
        == process_ptr
    &&& kernel.thread_map.spec_index(current_thread_ptr).view()
        .free_quota_pending_clean()
    &&& kernel.thread_map.spec_index(current_thread_ptr).view().temp_alloc_clean()
    &&& (kernel.thread_map.spec_index(peer_thread_ptr).view().state is SENDING
        || kernel.thread_map.spec_index(peer_thread_ptr).view().state is RECEIVING)
    &&& kernel.thread_map.spec_index(peer_thread_ptr).view()
        .blocking_endpoint_ptr == Some(endpoint_ptr)
    &&& kernel.thread_map.spec_index(peer_thread_ptr).view()
        .free_quota_pending_clean()
    &&& kernel.thread_map.spec_index(peer_thread_ptr).view().temp_alloc_clean()
    &&& kernel.endpoint_map.spec_index(endpoint_ptr).view().queue.len() != 0
    &&& kernel.endpoint_map.spec_index(endpoint_ptr).view().queue.view()
        .spec_index(0) == peer_thread_ptr
}

#[verifier::spinoff_prover]
fn ipc_share_pages_locked(
    kernel: &mut KernelK,
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
        share_mapping_4k_held_context(
            old(kernel), old(lctx), source_thread, target_thread,
            source_pagetable, target_pagetable, source_thread_lock_perm,
            target_thread_lock_perm, source_pagetable_lock_perm,
            target_pagetable_lock_perm,
        ),
        ipc_pages_base_roots_context(
            old(kernel), old(lctx), cpu_id, held_process,
            current_thread_ptr, held_endpoint, peer_thread_ptr,
            cpu_lock_perm, process_lock_perm, current_thread_lock_perm,
            endpoint_lock_perm, peer_thread_lock_perm,
        ),
        cpu_objects_unlocked_except(
            old(kernel).cpu_array, old(lctx).thread_id(), set![cpu_id]),
        container_objects_unlocked(
            old(kernel).container_map, old(lctx).thread_id()),
        process_objects_unlocked_except(
            old(kernel).process_map, old(lctx).thread_id(), set![held_process]),
        endpoint_objects_unlocked_except(
            old(kernel).endpoint_map, old(lctx).thread_id(), set![held_endpoint]),
        iommu_table_objects_unlocked(
            old(kernel).iommu_table_map, old(lctx).thread_id()),
        scheduler_objects_unlocked(
            old(kernel).scheduler_map, old(lctx).thread_id()),
        pcid_allocator_objects_unlocked(
            old(kernel).pcid_allocator_map, old(lctx).thread_id()),
        allocator_objects_unlocked(
            old(kernel).allocator_2m_map, old(lctx).thread_id()),
        allocator_objects_unlocked(
            old(kernel).allocator_1g_map, old(lctx).thread_id()),
        (source_thread == current_thread_ptr
            && target_thread == peer_thread_ptr)
            || (source_thread == peer_thread_ptr
                && target_thread == current_thread_ptr),
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        source_range.len <= usize::MAX / 3usize,
        old(kernel).thread_map.spec_index(source_thread).view().owning_proc
            == source_process,
        old(kernel).thread_map.spec_index(target_thread).view().owning_proc
            == target_process,
        old(kernel).thread_map.spec_index(source_thread).view().owning_container
            == source_container,
        old(kernel).thread_map.spec_index(target_thread).view().owning_container
            == target_container,
        old(lctx).lock_entry_contains(
            old(kernel).cpu_array.lock_id_by_index(cpu_id),
            KernelObjId::Cpu(cpu_id),
        ),
        mmap_4k_allocation_ready(old(kernel), old(lctx)),
        thread_objects_unlocked_except(
            old(kernel).thread_map, old(lctx).thread_id(),
            set![source_thread, target_thread],
        ),
        pagetable_objects_unlocked_except(
            old(kernel).pagetable_map, old(lctx).thread_id(),
            set![source_pagetable, target_pagetable],
        ),
    ensures
        final(kernel).inv(),
        typed_lock_maps_aligned(final(kernel), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
        ret is Ready ==>
            final(steps).steps.len() == old(steps).steps.len() + source_range.len,
        !(ret is Ready) ==>
            final(steps).steps.len() == old(steps).steps.len(),
        ret is Ready
            || ret is SourceUnmapped
            || ret is OwnerMismatch
            || ret is NoQuota
            || ret is Invalid
            || ret is InUse,
        share_mapping_4k_held_context(
            final(kernel), final(lctx), source_thread, target_thread,
            source_pagetable, target_pagetable, source_thread_lock_perm,
            target_thread_lock_perm, source_pagetable_lock_perm,
            target_pagetable_lock_perm,
        ),
        ipc_pages_base_roots_context(
            final(kernel), final(lctx), cpu_id, held_process,
            current_thread_ptr, held_endpoint, peer_thread_ptr,
            cpu_lock_perm, process_lock_perm, current_thread_lock_perm,
            endpoint_lock_perm, peer_thread_lock_perm,
        ),
        cpu_objects_unlocked_except(
            final(kernel).cpu_array, final(lctx).thread_id(), set![cpu_id]),
        container_objects_unlocked(
            final(kernel).container_map, final(lctx).thread_id()),
        process_objects_unlocked_except(
            final(kernel).process_map, final(lctx).thread_id(), set![held_process]),
        endpoint_objects_unlocked_except(
            final(kernel).endpoint_map, final(lctx).thread_id(), set![held_endpoint]),
        iommu_table_objects_unlocked(
            final(kernel).iommu_table_map, final(lctx).thread_id()),
        scheduler_objects_unlocked(
            final(kernel).scheduler_map, final(lctx).thread_id()),
        pcid_allocator_objects_unlocked(
            final(kernel).pcid_allocator_map, final(lctx).thread_id()),
        allocator_objects_unlocked(
            final(kernel).allocator_2m_map, final(lctx).thread_id()),
        allocator_objects_unlocked(
            final(kernel).allocator_1g_map, final(lctx).thread_id()),
        thread_objects_unlocked_except(
            final(kernel).thread_map, final(lctx).thread_id(),
            set![source_thread, target_thread],
        ),
        pagetable_objects_unlocked_except(
            final(kernel).pagetable_map, final(lctx).thread_id(),
            set![source_pagetable, target_pagetable],
        ),
        mmap_4k_allocation_ready(final(kernel), final(lctx)),
        held_containers_unchanged(
            old(kernel).container_map, final(kernel).container_map, old(lctx),
        ),
        held_processes_unchanged(
            old(kernel).process_map, final(kernel).process_map, old(lctx),
        ),
        held_endpoints_unchanged(
            old(kernel).endpoint_map, final(kernel).endpoint_map, old(lctx),
        ),
        held_schedulers_unchanged(
            old(kernel).scheduler_map, final(kernel).scheduler_map, old(lctx),
        ),
        held_pcid_allocators_unchanged(
            old(kernel).pcid_allocator_map, final(kernel).pcid_allocator_map,
            old(lctx),
        ),
        held_iommu_tables_unchanged(
            old(kernel).iommu_table_map, final(kernel).iommu_table_map, old(lctx),
        ),
        held_cpus_unchanged(
            old(kernel).cpu_array, final(kernel).cpu_array, old(lctx),
        ),
        allocator_objects_unlocked(
            old(kernel).allocator_2m_map, old(lctx).thread_id(),
        ) ==> allocator_objects_unlocked(
            final(kernel).allocator_2m_map, final(lctx).thread_id(),
        ),
        allocator_objects_unlocked(
            old(kernel).allocator_1g_map, old(lctx).thread_id(),
        ) ==> allocator_objects_unlocked(
            final(kernel).allocator_1g_map, final(lctx).thread_id(),
        ),
        final(kernel).thread_map.spec_index(source_thread).view().owning_proc
            == old(kernel).thread_map.spec_index(source_thread).view().owning_proc,
        final(kernel).thread_map.spec_index(source_thread).view().owning_container
            == old(kernel).thread_map.spec_index(source_thread).view().owning_container,
        final(kernel).thread_map.spec_index(source_thread).view().proc_pagetable_ptr
            == old(kernel).thread_map.spec_index(source_thread).view().proc_pagetable_ptr,
        final(kernel).thread_map.spec_index(target_thread).view().owning_proc
            == old(kernel).thread_map.spec_index(target_thread).view()
                .owning_proc,
        final(kernel).thread_map.spec_index(target_thread).view()
            .owning_container
            == old(kernel).thread_map.spec_index(target_thread).view()
                .owning_container,
        final(kernel).thread_map.spec_index(target_thread).view()
            .proc_pagetable_ptr
            == old(kernel).thread_map.spec_index(target_thread).view()
                .proc_pagetable_ptr,
{
    let source_start_indices = va2index(source_range.start);
    proof {
        assert({
            &&& kernel.pagetable_map.perms_wf()
            &&& kernel.pagetable_map.spec_index(source_pagetable).inv()
            &&& kernel.pagetable_map.spec_index(target_pagetable).inv()
            &&& kernel.thread_map.perms_wf()
            &&& kernel.thread_map.spec_index(target_thread).inv()
        }) by {
            reveal(pagetable_perms_wf);
            reveal(thread_perms_wf);
        };
    }
    let source_pt = kernel.pagetable_map.borrow(
        source_pagetable, Tracked(source_pagetable_lock_perm),
    );
    if source_start_indices.0 < source_pt.kernel_l4_end {
        return IpcPagesMapping::Invalid;
    }
    if !share_mapping_4k_source_precheck(
        kernel, source_range, source_pagetable, Tracked(&*lctx),
        Tracked(source_pagetable_lock_perm),
    ) {
        return IpcPagesMapping::SourceUnmapped;
    }

    let range_len = target_range.len;
    let target_thread_ref = kernel.thread_map.borrow(
        target_thread, Tracked(target_thread_lock_perm),
    );
    if target_thread_ref.quota_4k < 3usize * range_len {
        return IpcPagesMapping::NoQuota;
    }
    let target_start = target_range.start;
    let target_start_indices = va2index(target_start);
    let target_pt = kernel.pagetable_map.borrow(
        target_pagetable, Tracked(target_pagetable_lock_perm),
    );
    if target_start_indices.0 < target_pt.kernel_l4_end {
        return IpcPagesMapping::Invalid;
    }
    let target_end_index = range_len - 1;
    let target_end = target_range.index(target_end_index);
    proof {
        assert(target_end
            == spec_va_add_range(target_start, target_end_index)) by {
            target_range.va_range_lemma();
        };
        assert(target_start <= target_end) by (bit_vector)
            requires
                range_len > 0,
                range_len <= usize::MAX / 4096usize,
                target_start < usize::MAX - range_len * 4096usize,
                target_end_index == range_len - 1,
                target_end == (target_start
                    + target_end_index * 4096usize) as usize,
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
            &&& kernel.container_map.dom().contains(source_container)
            &&& kernel.container_map.dom().contains(target_container)
            &&& container_perms_wf(kernel.container_map)
            &&& container_tree_wf(kernel.root_container, kernel.container_map)
        }) by {
            reveal(container_thread_wf);
        };
    }
    let containers_compatible = if source_container == target_container {
        true
    } else {
        container_tree_check_is_ancestor(
            kernel.root_container,
            &kernel.container_map,
            source_container,
            target_container,
        )
    };
    let owners_compatible = if containers_compatible {
        proof {
            assert(share_mapping_4k_range_owner_compatible(
                kernel, source_pagetable, target_thread, source_range,
            )) by {
                source_range.va_range_lemma();
                reveal(mapped_4k_page_pagetable_wf);
                reveal(container_process_page_pagetable_wf);
                reveal(container_page_owner_wf);
                reveal(container_thread_wf);
                reveal(process_thread_wf);
                reveal(process_pagetable_match);
                reveal(container_perms_wf);
                reveal(container_tree_fields_wf);
                reveal(container_subtree_set_wf);
                reveal(container_uppertree_seq_wf);
                reveal(container_subtree_set_exclusive);
                reveal(PageTable::wf_mapping_4k);
            };
        }
        true
    } else {
        share_mapping_4k_source_owner_precheck(
            kernel, source_range, source_thread, target_thread,
            source_pagetable, target_pagetable, cpu_id,
            Tracked(&mut *lctx), Tracked(&mut *steps),
            Tracked(source_thread_lock_perm),
            Tracked(target_thread_lock_perm),
            Tracked(source_pagetable_lock_perm),
            Tracked(target_pagetable_lock_perm),
        )
    };
    proof {
        assert(ipc_pages_base_roots_context(
            kernel, &*lctx, cpu_id, held_process,
            current_thread_ptr, held_endpoint, peer_thread_ptr,
            cpu_lock_perm, process_lock_perm, current_thread_lock_perm,
            endpoint_lock_perm, peer_thread_lock_perm,
        )) by {
            reveal(process_perms_wf);
            reveal(thread_perms_wf);
            reveal(endpoint_perms_wf);
            lock_id_fields_eq_imply_eq();
        };
    }
    proof {
        assert({
            &&& cpu_objects_unlocked_except(
                kernel.cpu_array, lctx.thread_id(), set![cpu_id])
            &&& process_objects_unlocked_except(
                kernel.process_map, lctx.thread_id(), set![held_process])
            &&& thread_objects_unlocked_except(
                kernel.thread_map, lctx.thread_id(),
                set![current_thread_ptr, peer_thread_ptr])
            &&& endpoint_objects_unlocked_except(
                kernel.endpoint_map, lctx.thread_id(), set![held_endpoint])
        }) by {
            reveal(cpu_objects_unlocked_except);
            reveal(process_objects_unlocked_except);
            reveal(thread_objects_unlocked_except);
            reveal(endpoint_objects_unlocked_except);
        };
    }
    if !owners_compatible {
        return IpcPagesMapping::OwnerMismatch;
    }
    proof {
        assert(share_mapping_4k_held_context(
            kernel, &*lctx, source_thread, target_thread,
            source_pagetable, target_pagetable,
            source_thread_lock_perm, target_thread_lock_perm,
            source_pagetable_lock_perm, target_pagetable_lock_perm,
        )) by {
            lock_id_fields_eq_imply_eq();
        };
        assert({
            &&& share_mapping_4k_source_range_present(
                kernel, source_pagetable, source_range,
            )
            &&& share_mapping_4k_range_owner_compatible(
                kernel, source_pagetable, target_thread, source_range,
            )
        }) by {
            reveal(PageTable::wf_mapping_4k);
        };
        assert({
            &&& mmap_4k_allocation_ready(kernel, &*lctx)
            &&& kernel.thread_map.spec_index(source_thread).view()
                .temp_alloc_clean()
            &&& kernel.thread_map.spec_index(source_thread).view()
                .free_quota_pending_clean()
            &&& kernel.thread_map.spec_index(target_thread).view()
                .temp_alloc_clean()
            &&& kernel.thread_map.spec_index(target_thread).view()
                .free_quota_pending_clean()
            &&& kernel.thread_map.spec_index(target_thread).view().quota_4k
                >= 3 * target_range.len
        }) by {
            lock_id_fields_eq_imply_eq();
        };
        assert({
            &&& kernel.pagetable_map.spec_index(target_pagetable).view()
                .spec_mapping_4k_va_range_empty(
                    target_range.start,
                    target_range.view().spec_index(
                        (target_range.len - 1) as int,
                    ),
                )
            &&& kernel.pagetable_map.spec_index(target_pagetable).view()
                .spec_mapping_4k_va_range_buildable(target_range)
        }) by {
            reveal(PageTable::wf_mapping_4k);
        };
    }

    proof {
        assert({
            &&& kernel.container_map.dom().contains(target_container)
            &&& kernel.container_map.perms_wf()
        }) by {
            reveal(container_thread_wf);
            reveal(container_perms_wf);
        };
    }
    let target_allocator = kernel.container_map.borrow_rodata(target_container)
        .borrow().allocator_ptr_4k;
    proof {
        assert(mmap_4k_held_context(
            kernel, &*lctx, target_allocator, target_thread,
            target_process, target_container, cpu_id, target_pagetable,
            target_thread_lock_perm, target_pagetable_lock_perm,
        )) by {
            reveal(container_allocator_wf);
            reveal(container_thread_wf);
            reveal(process_thread_wf);
            reveal(process_pagetable_match);
            lock_id_fields_eq_imply_eq();
        };
        assert({
            &&& mmap_4k_allocation_ready(kernel, &*lctx)
            &&& kernel.thread_map.spec_index(target_thread).view()
                .temp_alloc_clean()
            &&& kernel.thread_map.spec_index(target_thread).view()
                .free_quota_pending_clean()
            &&& kernel.thread_map.spec_index(target_thread).view().quota_4k
                >= 3 * target_range.len
            &&& kernel.pagetable_map.spec_index(target_pagetable).view().wf()
            &&& kernel.pagetable_map.spec_index(target_pagetable).view()
                .kernel_l4_end <= spec_v2l4index(target_range.start)
            &&& kernel.pagetable_map.spec_index(target_pagetable).view()
                .spec_mapping_4k_va_range_empty(
                    target_range.start,
                    target_range.view().spec_index(
                        (target_range.len - 1) as int,
                    ),
                )
        }) by {
            reveal(pagetable_perms_wf);
        };
        assert({
            &&& source_thread != target_thread
            &&& kernel.thread_map.dom().contains(source_thread)
            &&& kernel.thread_map.spec_index(source_thread)
                .locked_by_thread(lctx.thread_id())
            &&& lctx.lock_entry_contains(
                kernel.thread_map.lock_id_by_key(source_thread),
                KernelObjId::Thread(source_thread),
            )
        }) by {
            lock_id_fields_eq_imply_eq();
        };
    }
    share_mapping_4k_build_and_share(
        kernel,
        source_range,
        target_range,
        target_allocator,
        source_thread,
        target_thread,
        target_process,
        target_container,
        cpu_id,
        source_pagetable,
        target_pagetable,
        Tracked(&mut *lctx),
        Tracked(&mut *steps),
        Tracked(source_thread_lock_perm),
        Tracked(target_thread_lock_perm),
        Tracked(source_pagetable_lock_perm),
        Tracked(target_pagetable_lock_perm),
    );
    proof {
        assert(ipc_pages_base_roots_context(
            kernel, &*lctx, cpu_id, held_process,
            current_thread_ptr, held_endpoint, peer_thread_ptr,
            cpu_lock_perm, process_lock_perm, current_thread_lock_perm,
            endpoint_lock_perm, peer_thread_lock_perm,
        )) by {
            reveal(process_perms_wf);
            reveal(thread_perms_wf);
            reveal(endpoint_perms_wf);
            lock_id_fields_eq_imply_eq();
        };
    }
    proof {
        assert({
            &&& cpu_objects_unlocked_except(
                kernel.cpu_array, lctx.thread_id(), set![cpu_id])
            &&& process_objects_unlocked_except(
                kernel.process_map, lctx.thread_id(), set![held_process])
            &&& thread_objects_unlocked_except(
                kernel.thread_map, lctx.thread_id(),
                set![current_thread_ptr, peer_thread_ptr])
            &&& endpoint_objects_unlocked_except(
                kernel.endpoint_map, lctx.thread_id(), set![held_endpoint])
        }) by {
            reveal(cpu_objects_unlocked_except);
            reveal(process_objects_unlocked_except);
            reveal(thread_objects_unlocked_except);
            reveal(endpoint_objects_unlocked_except);
        };
    }
    IpcPagesMapping::Ready
}

#[verifier::spinoff_prover]
pub(super) fn ipc_share_pages_mapping(
    kernel: &mut KernelK,
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
        ipc_pages_base_roots_context(
            old(kernel), old(lctx), cpu_id, process_ptr,
            current_thread_ptr, endpoint_ptr, peer_thread_ptr,
            cpu_lock_perm, process_lock_perm, current_thread_lock_perm,
            endpoint_lock_perm, peer_thread_lock_perm,
        ),
        cpu_objects_unlocked_except(
            old(kernel).cpu_array, old(lctx).thread_id(), set![cpu_id]),
        page_objects_unlocked(
            old(kernel).page_array, old(lctx).thread_id()),
        container_objects_unlocked(
            old(kernel).container_map, old(lctx).thread_id()),
        process_objects_unlocked_except(
            old(kernel).process_map, old(lctx).thread_id(), set![process_ptr]),
        thread_objects_unlocked_except(
            old(kernel).thread_map, old(lctx).thread_id(),
            set![current_thread_ptr, peer_thread_ptr]),
        endpoint_objects_unlocked_except(
            old(kernel).endpoint_map, old(lctx).thread_id(), set![endpoint_ptr]),
        pagetable_objects_unlocked(
            old(kernel).pagetable_map, old(lctx).thread_id()),
        iommu_table_objects_unlocked(
            old(kernel).iommu_table_map, old(lctx).thread_id()),
        scheduler_objects_unlocked(
            old(kernel).scheduler_map, old(lctx).thread_id()),
        pcid_allocator_objects_unlocked(
            old(kernel).pcid_allocator_map, old(lctx).thread_id()),
        allocator_objects_unlocked(
            old(kernel).allocator_4k_map, old(lctx).thread_id()),
        allocator_objects_unlocked(
            old(kernel).allocator_2m_map, old(lctx).thread_id()),
        allocator_objects_unlocked(
            old(kernel).allocator_1g_map, old(lctx).thread_id()),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        source_range.len <= usize::MAX / 3usize,
        source_thread != target_thread,
        (source_thread == current_thread_ptr && target_thread == peer_thread_ptr)
            || (source_thread == peer_thread_ptr && target_thread == current_thread_ptr),
    ensures
        ipc_pages_base_roots_context(
            final(kernel), final(lctx), cpu_id, process_ptr,
            current_thread_ptr, endpoint_ptr, peer_thread_ptr,
            cpu_lock_perm, process_lock_perm, current_thread_lock_perm,
            endpoint_lock_perm, peer_thread_lock_perm,
        ),
        cpu_objects_unlocked_except(
            final(kernel).cpu_array, final(lctx).thread_id(), set![cpu_id]),
        page_objects_unlocked(
            final(kernel).page_array, final(lctx).thread_id()),
        container_objects_unlocked(
            final(kernel).container_map, final(lctx).thread_id()),
        process_objects_unlocked_except(
            final(kernel).process_map, final(lctx).thread_id(), set![process_ptr]),
        thread_objects_unlocked_except(
            final(kernel).thread_map, final(lctx).thread_id(),
            set![current_thread_ptr, peer_thread_ptr]),
        endpoint_objects_unlocked_except(
            final(kernel).endpoint_map, final(lctx).thread_id(), set![endpoint_ptr]),
        pagetable_objects_unlocked(
            final(kernel).pagetable_map, final(lctx).thread_id()),
        iommu_table_objects_unlocked(
            final(kernel).iommu_table_map, final(lctx).thread_id()),
        scheduler_objects_unlocked(
            final(kernel).scheduler_map, final(lctx).thread_id()),
        pcid_allocator_objects_unlocked(
            final(kernel).pcid_allocator_map, final(lctx).thread_id()),
        allocator_objects_unlocked(
            final(kernel).allocator_4k_map, final(lctx).thread_id()),
        allocator_objects_unlocked(
            final(kernel).allocator_2m_map, final(lctx).thread_id()),
        allocator_objects_unlocked(
            final(kernel).allocator_1g_map, final(lctx).thread_id()),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(kernel).thread_map.spec_index(peer_thread_ptr).view().owning_container
            == old(kernel).thread_map.spec_index(peer_thread_ptr).view().owning_container,
        ret is SameProcess ==>
            final(lctx).kernel_view_locking_state() is Acquire,
        !(ret is SameProcess) ==>
            final(lctx).kernel_view_locking_state() is Release,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
        ret is Ready ==>
            final(steps).steps.len() == old(steps).steps.len() + source_range.len,
        !(ret is Ready) ==>
            final(steps).steps.len() == old(steps).steps.len(),
{
    proof {
        assert({
            &&& kernel.thread_map.perms_wf()
            &&& kernel.thread_map.spec_index(current_thread_ptr).is_init()
            &&& kernel.thread_map.spec_index(peer_thread_ptr).is_init()
        }) by {
            reveal(thread_perms_wf);
        };
    }
    let source_process;
    let source_container;
    let source_pagetable;
    if source_thread == current_thread_ptr {
        let source_thread_ref = kernel.thread_map.borrow(
            source_thread, Tracked(current_thread_lock_perm),
        );
        source_process = source_thread_ref.owning_proc;
        source_container = source_thread_ref.owning_container;
        source_pagetable = source_thread_ref.proc_pagetable_ptr;
    } else {
        let source_thread_ref = kernel.thread_map.borrow(
            source_thread, Tracked(peer_thread_lock_perm),
        );
        source_process = source_thread_ref.owning_proc;
        source_container = source_thread_ref.owning_container;
        source_pagetable = source_thread_ref.proc_pagetable_ptr;
    }
    let target_process;
    let target_container;
    let target_pagetable;
    if target_thread == current_thread_ptr {
        let target_thread_ref = kernel.thread_map.borrow(
            target_thread, Tracked(current_thread_lock_perm),
        );
        target_process = target_thread_ref.owning_proc;
        target_container = target_thread_ref.owning_container;
        target_pagetable = target_thread_ref.proc_pagetable_ptr;
    } else {
        let target_thread_ref = kernel.thread_map.borrow(
            target_thread, Tracked(peer_thread_lock_perm),
        );
        target_process = target_thread_ref.owning_proc;
        target_container = target_thread_ref.owning_container;
        target_pagetable = target_thread_ref.proc_pagetable_ptr;
    }

    if source_process == target_process {
        return IpcPagesMapping::SameProcess;
    }
    proof {
        assert({
            &&& kernel.process_map.dom().contains(source_process)
            &&& kernel.process_map.dom().contains(target_process)
            &&& kernel.pagetable_map.dom().contains(source_pagetable)
            &&& kernel.pagetable_map.dom().contains(target_pagetable)
            &&& kernel.pagetable_map.spec_index(source_pagetable).view().proc_ptr
                == source_process
            &&& kernel.pagetable_map.spec_index(target_pagetable).view().proc_ptr
                == target_process
            &&& source_pagetable != target_pagetable
        }) by {
            reveal(process_thread_wf);
            reveal(process_pagetable_match);
        };
        assert({
            &&& kernel.pagetable_map.dom().contains(source_pagetable)
            &&& kernel.pagetable_map.dom().contains(target_pagetable)
            &&& kernel.pagetable_map.lock_id_by_key(source_pagetable).major
                == PAGE_TABLE_LOCK_MAJOR
            &&& kernel.pagetable_map.lock_id_by_key(target_pagetable).major
                == PAGE_TABLE_LOCK_MAJOR
            &&& lctx.held_lock_majors_lt(PAGE_TABLE_LOCK_MAJOR)
        }) by {
            reveal(process_thread_wf);
            reveal(process_pagetable_match);
            reveal(pagetable_perms_wf);
            reveal(process_perms_wf);
            reveal(thread_perms_wf);
            reveal(endpoint_perms_wf);
        };
    }

    let result;
    if source_pagetable < target_pagetable {
        proof {
            assert(!kernel.pagetable_map.spec_index(source_pagetable)
                .locked_by_thread(lctx.thread_id())) by {
                reveal(pagetable_objects_unlocked);
            };
            assert(wlock_requires(
                kernel.pagetable_map.spec_index(source_pagetable), &*lctx,
            )) by {
                reveal(pagetable_objects_unlocked);
            };
            assert(lctx.lock_id_acyclic(
                kernel.pagetable_map.lock_id_by_key(source_pagetable),
            )) by {
                reveal(process_perms_wf);
                reveal(thread_perms_wf);
                reveal(endpoint_perms_wf);
                reveal(pagetable_perms_wf);
            };
        }
        let Tracked(source_pagetable_lock_perm) = kernel.wlock_pagetable(
            source_pagetable, Tracked(&mut *lctx),
        );
        proof {
            assert(source_pagetable != target_pagetable
                && !set![source_pagetable].contains(target_pagetable)) by {
                reveal(process_pagetable_match);
            };
            assert(pagetable_objects_unlocked_except(
                kernel.pagetable_map, lctx.thread_id(),
                set![source_pagetable],
            )) by {
                reveal(pagetable_objects_unlocked_except);
            };
            assert(!kernel.pagetable_map.spec_index(target_pagetable)
                .locked_by_thread(lctx.thread_id())) by {
                reveal(pagetable_objects_unlocked_except);
            };
            assert(wlock_requires(
                kernel.pagetable_map.spec_index(target_pagetable), &*lctx,
            )) by {
                reveal(pagetable_objects_unlocked_except);
            };
            assert(lctx.lock_id_acyclic(
                kernel.pagetable_map.lock_id_by_key(target_pagetable),
            )) by {
                reveal(pagetable_perms_wf);
            };
        }
        let Tracked(target_pagetable_lock_perm) = kernel.wlock_pagetable(
            target_pagetable, Tracked(&mut *lctx),
        );
        proof {
            assert(pagetable_objects_unlocked_except(
                kernel.pagetable_map, lctx.thread_id(),
                set![source_pagetable, target_pagetable],
            )) by {
                reveal(pagetable_objects_unlocked_except);
            };
            assert(lctx.held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR)) by {
                reveal(pagetable_perms_wf);
            };
            assert({
                &&& kernel.thread_map.dom().contains(source_thread)
                &&& kernel.thread_map.dom().contains(target_thread)
                &&& kernel.thread_map.spec_index(source_thread).view().owning_proc
                    != kernel.thread_map.spec_index(target_thread).view().owning_proc
                &&& kernel.thread_map.spec_index(source_thread).view()
                    .proc_pagetable_ptr == source_pagetable
                &&& kernel.thread_map.spec_index(target_thread).view()
                    .proc_pagetable_ptr == target_pagetable
                &&& kernel.pagetable_map.dom().contains(source_pagetable)
                &&& kernel.pagetable_map.dom().contains(target_pagetable)
                &&& kernel.pagetable_map.spec_index(source_pagetable).view().proc_ptr
                    == kernel.thread_map.spec_index(source_thread).view().owning_proc
                &&& kernel.pagetable_map.spec_index(target_pagetable).view().proc_ptr
                    == kernel.thread_map.spec_index(target_thread).view().owning_proc
            }) by {
                reveal(process_thread_wf);
                reveal(process_pagetable_match);
            };
            assert({
                &&& kernel.thread_map.spec_index(source_thread).wlocked_by(lctx)
                &&& kernel.thread_map.spec_index(source_thread).locked_by(lctx)
                &&& !kernel.thread_map.spec_index(source_thread).being_killed()
                &&& kernel.thread_map.spec_index(target_thread).wlocked_by(lctx)
                &&& kernel.thread_map.spec_index(target_thread).locked_by(lctx)
                &&& !kernel.thread_map.spec_index(target_thread).being_killed()
                &&& (if source_thread == current_thread_ptr {
                    current_thread_lock_perm
                } else {
                    peer_thread_lock_perm
                }).state() is WriteLock
                &&& (if source_thread == current_thread_ptr {
                    current_thread_lock_perm
                } else {
                    peer_thread_lock_perm
                }).thread_id() == lctx.thread_id()
                &&& (if source_thread == current_thread_ptr {
                    current_thread_lock_perm
                } else {
                    peer_thread_lock_perm
                }).lock_id()
                    == kernel.thread_map.spec_index(source_thread)
                        .locking_thread()->Write_lock_id
                &&& (if target_thread == current_thread_ptr {
                    current_thread_lock_perm
                } else {
                    peer_thread_lock_perm
                }).state() is WriteLock
                &&& (if target_thread == current_thread_ptr {
                    current_thread_lock_perm
                } else {
                    peer_thread_lock_perm
                }).thread_id() == lctx.thread_id()
                &&& (if target_thread == current_thread_ptr {
                    current_thread_lock_perm
                } else {
                    peer_thread_lock_perm
                }).lock_id()
                    == kernel.thread_map.spec_index(target_thread)
                        .locking_thread()->Write_lock_id
            }) by {
                lock_id_fields_eq_imply_eq();
            };
            assert({
                &&& kernel.pagetable_map.spec_index(source_pagetable).wlocked_by(lctx)
                &&& kernel.pagetable_map.spec_index(source_pagetable).locked_by(lctx)
                &&& source_pagetable_lock_perm.state() is WriteLock
                &&& source_pagetable_lock_perm.thread_id() == lctx.thread_id()
                &&& source_pagetable_lock_perm.lock_id()
                    == kernel.pagetable_map.spec_index(source_pagetable)
                        .locking_thread()->Write_lock_id
            }) by {
                lock_id_fields_eq_imply_eq();
            };
            assert({
                &&& kernel.pagetable_map.spec_index(target_pagetable).wlocked_by(lctx)
                &&& kernel.pagetable_map.spec_index(target_pagetable).locked_by(lctx)
                &&& target_pagetable_lock_perm.state() is WriteLock
                &&& target_pagetable_lock_perm.thread_id() == lctx.thread_id()
                &&& target_pagetable_lock_perm.lock_id()
                    == kernel.pagetable_map.spec_index(target_pagetable)
                        .locking_thread()->Write_lock_id
            }) by {
                lock_id_fields_eq_imply_eq();
            };
            assert(lctx.lock_entry_contains(
                kernel.pagetable_map.lock_id_by_key(source_pagetable),
                KernelObjId::PageTable(source_pagetable),
            )) by {
                lock_id_fields_eq_imply_eq();
            };
            assert(lctx.lock_entry_contains(
                kernel.pagetable_map.lock_id_by_key(target_pagetable),
                KernelObjId::PageTable(target_pagetable),
            )) by {
                lock_id_fields_eq_imply_eq();
            };

            assert(share_mapping_4k_held_context(
                kernel, &*lctx, source_thread, target_thread,
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
            )) by {
                reveal(process_thread_wf);
                reveal(process_pagetable_match);
                reveal(page_objects_unlocked);
                lock_id_fields_eq_imply_eq();
            };
            assert({
                &&& share_mapping_4k_held_context(
                    kernel, &*lctx, source_thread, target_thread,
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
                )
                &&& mmap_4k_allocation_ready(kernel, &*lctx)
                &&& kernel.cpu_array.spec_index(cpu_id).view()
                    .locked_by_thread(lctx.thread_id())
                &&& thread_objects_unlocked_except(
                    kernel.thread_map, lctx.thread_id(),
                    set![source_thread, target_thread],
                )
                &&& pagetable_objects_unlocked_except(
                    kernel.pagetable_map, lctx.thread_id(),
                    set![source_pagetable, target_pagetable],
                )
            }) by {
                reveal(process_thread_wf);
                reveal(process_pagetable_match);
                reveal(mmap_4k_allocation_ready);
                reveal(mmap_4k_no_page_locks);
                reveal(page_objects_unlocked);
                reveal(allocator_objects_unlocked);
                reveal(thread_objects_unlocked_except);
                reveal(pagetable_objects_unlocked_except);
                lock_id_fields_eq_imply_eq();
            };
        }
        result = ipc_share_pages_locked(
            kernel, source_range, target_range,
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
        kernel.wunlock_pagetable(
            target_pagetable, Tracked(&mut *lctx),
            Tracked(target_pagetable_lock_perm),
        );
        proof {
            assert({
                &&& lctx.lock_entry_contains(
                    kernel.pagetable_map.lock_id_by_key(source_pagetable),
                    KernelObjId::PageTable(source_pagetable),
                )
                &&& pagetable_objects_unlocked_except(
                    kernel.pagetable_map, lctx.thread_id(),
                    set![source_pagetable],
                )
            }) by {
                reveal(pagetable_objects_unlocked_except);
                lock_id_fields_eq_imply_eq();
            };
        }
        kernel.wunlock_pagetable(
            source_pagetable, Tracked(&mut *lctx),
            Tracked(source_pagetable_lock_perm),
        );
    } else {
        proof {
            assert(!kernel.pagetable_map.spec_index(target_pagetable)
                .locked_by_thread(lctx.thread_id())) by {
                reveal(pagetable_objects_unlocked);
            };
            assert(wlock_requires(
                kernel.pagetable_map.spec_index(target_pagetable), &*lctx,
            )) by {
                reveal(pagetable_objects_unlocked);
            };
            assert(lctx.lock_id_acyclic(
                kernel.pagetable_map.lock_id_by_key(target_pagetable),
            )) by {
                reveal(process_perms_wf);
                reveal(thread_perms_wf);
                reveal(endpoint_perms_wf);
                reveal(pagetable_perms_wf);
            };
        }
        let Tracked(target_pagetable_lock_perm) = kernel.wlock_pagetable(
            target_pagetable, Tracked(&mut *lctx),
        );
        proof {
            assert(target_pagetable != source_pagetable
                && !set![target_pagetable].contains(source_pagetable)) by {
                reveal(process_pagetable_match);
            };
            assert(pagetable_objects_unlocked_except(
                kernel.pagetable_map, lctx.thread_id(),
                set![target_pagetable],
            )) by {
                reveal(pagetable_objects_unlocked_except);
            };
            assert(!kernel.pagetable_map.spec_index(source_pagetable)
                .locked_by_thread(lctx.thread_id())) by {
                reveal(pagetable_objects_unlocked_except);
            };
            assert(wlock_requires(
                kernel.pagetable_map.spec_index(source_pagetable), &*lctx,
            )) by {
                reveal(pagetable_objects_unlocked_except);
            };
            assert(lctx.lock_id_acyclic(
                kernel.pagetable_map.lock_id_by_key(source_pagetable),
            )) by {
                reveal(pagetable_perms_wf);
            };
        }
        let Tracked(source_pagetable_lock_perm) = kernel.wlock_pagetable(
            source_pagetable, Tracked(&mut *lctx),
        );
        proof {
            assert(pagetable_objects_unlocked_except(
                kernel.pagetable_map, lctx.thread_id(),
                set![source_pagetable, target_pagetable],
            )) by {
                reveal(pagetable_objects_unlocked_except);
            };
            assert(lctx.held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR)) by {
                reveal(pagetable_perms_wf);
            };
            assert({
                &&& kernel.thread_map.dom().contains(source_thread)
                &&& kernel.thread_map.dom().contains(target_thread)
                &&& kernel.thread_map.spec_index(source_thread).view().owning_proc
                    != kernel.thread_map.spec_index(target_thread).view().owning_proc
                &&& kernel.thread_map.spec_index(source_thread).view()
                    .proc_pagetable_ptr == source_pagetable
                &&& kernel.thread_map.spec_index(target_thread).view()
                    .proc_pagetable_ptr == target_pagetable
                &&& kernel.pagetable_map.dom().contains(source_pagetable)
                &&& kernel.pagetable_map.dom().contains(target_pagetable)
                &&& kernel.pagetable_map.spec_index(source_pagetable).view().proc_ptr
                    == kernel.thread_map.spec_index(source_thread).view().owning_proc
                &&& kernel.pagetable_map.spec_index(target_pagetable).view().proc_ptr
                    == kernel.thread_map.spec_index(target_thread).view().owning_proc
            }) by {
                reveal(process_thread_wf);
                reveal(process_pagetable_match);
            };
            assert({
                &&& kernel.thread_map.spec_index(source_thread).wlocked_by(lctx)
                &&& kernel.thread_map.spec_index(source_thread).locked_by(lctx)
                &&& !kernel.thread_map.spec_index(source_thread).being_killed()
                &&& kernel.thread_map.spec_index(target_thread).wlocked_by(lctx)
                &&& kernel.thread_map.spec_index(target_thread).locked_by(lctx)
                &&& !kernel.thread_map.spec_index(target_thread).being_killed()
                &&& (if source_thread == current_thread_ptr {
                    current_thread_lock_perm
                } else {
                    peer_thread_lock_perm
                }).state() is WriteLock
                &&& (if source_thread == current_thread_ptr {
                    current_thread_lock_perm
                } else {
                    peer_thread_lock_perm
                }).thread_id() == lctx.thread_id()
                &&& (if source_thread == current_thread_ptr {
                    current_thread_lock_perm
                } else {
                    peer_thread_lock_perm
                }).lock_id()
                    == kernel.thread_map.spec_index(source_thread)
                        .locking_thread()->Write_lock_id
                &&& (if target_thread == current_thread_ptr {
                    current_thread_lock_perm
                } else {
                    peer_thread_lock_perm
                }).state() is WriteLock
                &&& (if target_thread == current_thread_ptr {
                    current_thread_lock_perm
                } else {
                    peer_thread_lock_perm
                }).thread_id() == lctx.thread_id()
                &&& (if target_thread == current_thread_ptr {
                    current_thread_lock_perm
                } else {
                    peer_thread_lock_perm
                }).lock_id()
                    == kernel.thread_map.spec_index(target_thread)
                        .locking_thread()->Write_lock_id
            }) by {
                lock_id_fields_eq_imply_eq();
            };
            assert({
                &&& kernel.pagetable_map.spec_index(source_pagetable).wlocked_by(lctx)
                &&& kernel.pagetable_map.spec_index(source_pagetable).locked_by(lctx)
                &&& source_pagetable_lock_perm.state() is WriteLock
                &&& source_pagetable_lock_perm.thread_id() == lctx.thread_id()
                &&& source_pagetable_lock_perm.lock_id()
                    == kernel.pagetable_map.spec_index(source_pagetable)
                        .locking_thread()->Write_lock_id
            }) by {
                lock_id_fields_eq_imply_eq();
            };
            assert({
                &&& kernel.pagetable_map.spec_index(target_pagetable).wlocked_by(lctx)
                &&& kernel.pagetable_map.spec_index(target_pagetable).locked_by(lctx)
                &&& target_pagetable_lock_perm.state() is WriteLock
                &&& target_pagetable_lock_perm.thread_id() == lctx.thread_id()
                &&& target_pagetable_lock_perm.lock_id()
                    == kernel.pagetable_map.spec_index(target_pagetable)
                        .locking_thread()->Write_lock_id
            }) by {
                lock_id_fields_eq_imply_eq();
            };
            assert(lctx.lock_entry_contains(
                kernel.pagetable_map.lock_id_by_key(source_pagetable),
                KernelObjId::PageTable(source_pagetable),
            )) by {
                lock_id_fields_eq_imply_eq();
            };
            assert(lctx.lock_entry_contains(
                kernel.pagetable_map.lock_id_by_key(target_pagetable),
                KernelObjId::PageTable(target_pagetable),
            )) by {
                lock_id_fields_eq_imply_eq();
            };

            assert(share_mapping_4k_held_context(
                kernel, &*lctx, source_thread, target_thread,
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
            )) by {
                reveal(process_thread_wf);
                reveal(process_pagetable_match);
                reveal(page_objects_unlocked);
                lock_id_fields_eq_imply_eq();
            };
            assert({
                &&& share_mapping_4k_held_context(
                    kernel, &*lctx, source_thread, target_thread,
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
                )
                &&& mmap_4k_allocation_ready(kernel, &*lctx)
                &&& kernel.cpu_array.spec_index(cpu_id).view()
                    .locked_by_thread(lctx.thread_id())
                &&& thread_objects_unlocked_except(
                    kernel.thread_map, lctx.thread_id(),
                    set![source_thread, target_thread],
                )
                &&& pagetable_objects_unlocked_except(
                    kernel.pagetable_map, lctx.thread_id(),
                    set![source_pagetable, target_pagetable],
                )
            }) by {
                reveal(process_thread_wf);
                reveal(process_pagetable_match);
                reveal(mmap_4k_allocation_ready);
                reveal(mmap_4k_no_page_locks);
                reveal(page_objects_unlocked);
                reveal(allocator_objects_unlocked);
                reveal(thread_objects_unlocked_except);
                reveal(pagetable_objects_unlocked_except);
                lock_id_fields_eq_imply_eq();
            };
        }
        result = ipc_share_pages_locked(
            kernel, source_range, target_range,
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
        kernel.wunlock_pagetable(
            source_pagetable, Tracked(&mut *lctx),
            Tracked(source_pagetable_lock_perm),
        );
        proof {
            assert({
                &&& lctx.lock_entry_contains(
                    kernel.pagetable_map.lock_id_by_key(target_pagetable),
                    KernelObjId::PageTable(target_pagetable),
                )
                &&& pagetable_objects_unlocked_except(
                    kernel.pagetable_map, lctx.thread_id(),
                    set![target_pagetable],
                )
            }) by {
                reveal(pagetable_objects_unlocked_except);
                lock_id_fields_eq_imply_eq();
            };
        }
        kernel.wunlock_pagetable(
            target_pagetable, Tracked(&mut *lctx),
            Tracked(target_pagetable_lock_perm),
        );
    }
    proof {
        assert_sets_equal!(
            typed_lock_maps_unchanged(old(lctx), lctx),
            held => {}
        );
        assert(ipc_pages_base_roots_context(
            kernel, &*lctx, cpu_id, process_ptr,
            current_thread_ptr, endpoint_ptr, peer_thread_ptr,
            cpu_lock_perm, process_lock_perm, current_thread_lock_perm,
            endpoint_lock_perm, peer_thread_lock_perm,
        )) by {
            reveal(process_perms_wf);
            reveal(thread_perms_wf);
            reveal(endpoint_perms_wf);
            lock_id_fields_eq_imply_eq();
        };
        assert({
            &&& kernel.cpu_array.lock_id_by_index(cpu_id)
                == old(kernel).cpu_array.lock_id_by_index(cpu_id)
            &&& kernel.process_map.lock_id_by_key(process_ptr)
                == old(kernel).process_map.lock_id_by_key(process_ptr)
            &&& kernel.thread_map.lock_id_by_key(current_thread_ptr)
                == old(kernel).thread_map.lock_id_by_key(current_thread_ptr)
            &&& kernel.endpoint_map.lock_id_by_key(endpoint_ptr)
                == old(kernel).endpoint_map.lock_id_by_key(endpoint_ptr)
            &&& kernel.thread_map.lock_id_by_key(peer_thread_ptr)
                == old(kernel).thread_map.lock_id_by_key(peer_thread_ptr)
        }) by {
            reveal(process_perms_wf);
            reveal(thread_perms_wf);
            reveal(endpoint_perms_wf);
            lock_id_fields_eq_imply_eq();
        };
    let result;
    if let IpcPagesMapping::Ready = pages_result {
        proof {
            kernel.kernel_step_boundary(&mut *lctx, &mut *steps);
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
                    kernel.kernel_step_boundary(&mut *lctx, &mut *steps);
                }
            },
        }
    }
    ipc_schedule_waiting_peer_and_finish(
        kernel, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id,
        process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr,
        result, Tracked(cpu_lock_perm), Tracked(process_lock_perm),
        Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm),
        Tracked(peer_thread_lock_perm),
    )
}

} // verus!
