use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal};
use crate::*;

verus! {
/// Read-locking `source_table` and read-locking `target_table` (write-locking it when `write_target`) on cpu `cpu_id`, holding their 2M
/// windows, and replacing `thread`'s progress adds `cpu_id` as a reader of the source table and as a reader or the writer of the target
/// table in the complete projection.
pub proof fn kernel_pagetable_pair_rlocked_and_progress_changed_implies_u_step(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, write_target: bool, source: RwLockProcessPtr, target: RwLockProcessPtr, source_table: RwLockPageTableRoot,
    target_table: RwLockPageTableRoot, thread: RwLockThreadPtr,
)
    requires
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        source != target,
        source_table != target_table,
        pre.prc_mp.dom().contains(source),
        pre.prc_mp.dom().contains(target),
        !pre.prc_mp.spec_index(source).view().zombie,
        !pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(source).view().pagetable == source_table,
        pre.prc_mp.spec_index(target).view().pagetable == target_table,
        *post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, thrd_mp: post.thrd_mp, ..*pre }),
        post.pt_mp.dom() == pre.pt_mp.dom(),
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) && p != source_table && p != target_table ==> post.pt_mp.spec_index(p) == pre.pt_mp.spec_index(p),
        post.pt_lower.view() == pre.pt_lower.view().insert(source_table, post.pt_lower.view().spec_index(source_table)).insert(target_table, post.pt_lower.view().spec_index(target_table)),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), source_table).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), source_table).mapping_4k(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), source_table).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), source_table).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), source_table).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), source_table).mapping_1g(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), target_table).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), target_table).mapping_4k(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), target_table).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), target_table).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), target_table).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), target_table).mapping_1g(),
        pre.thrd_mp.dom().contains(thread),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thread),
        post.thrd_mp.spec_index(thread).view() == (Thread { syscall_progress: post.thrd_mp.spec_index(thread).view().syscall_progress, ..pre.thrd_mp.spec_index(thread).view() }),
        post.thrd_mp.spec_index(thread).locking_thread() == pre.thrd_mp.spec_index(thread).locking_thread(),
        post.thrd_mp.spec_index(thread).being_killed() == pre.thrd_mp.spec_index(thread).being_killed(),
        post.pt_mp.spec_index(source_table).lock_state_u() == pre.pt_mp.spec_index(source_table).lock_state_u().with_reader(cpu_id),
        post.pt_mp.spec_index(target_table).lock_state_u()
            == if write_target { LockStateU::WriteLocked { writer: cpu_id } } else { pre.pt_mp.spec_index(target_table).lock_state_u().with_reader(cpu_id) },
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            &&& a.thread_map.dom().contains(thread)
            &&& a.thread_map[thread].syscall_progress == pre.thrd_mp.spec_index(thread).view().syscall_progress.view()
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                thread_map: a.thread_map.insert(thread, ThreadU { syscall_progress: post.thrd_mp.spec_index(thread).view().syscall_progress.view(), ..a.thread_map[thread] }),
                process_map: a.process_map.insert(source, ProcessU {
                    pagetable: Some(PageTableU { lock_state: a.process_map[source].pagetable->Some_0.lock_state.with_reader(cpu_id),
                        pagetable_window_locks: whole_pagetable(post.pt_mp, post.pt_lower.view(), source_table).lower.pagetable_window_locks, ..a.process_map[source].pagetable->Some_0 }), ..a.process_map[source]
                }).insert(target, ProcessU {
                    pagetable: Some(PageTableU { lock_state: if write_target { LockStateU::WriteLocked { writer: cpu_id } } else { a.process_map[target].pagetable->Some_0.lock_state.with_reader(cpu_id) },
                        pagetable_window_locks: whole_pagetable(post.pt_mp, post.pt_lower.view(), target_table).lower.pagetable_window_locks, ..a.process_map[target].pagetable->Some_0 }), ..a.process_map[target]
                }),
                ..a
            })
        }),
{
    kernel_pagetable_pair_lock_modes_and_progress_changed_implies_u_step(pre, post, source, target, source_table, target_table, thread);
    process_pagetable_wf_process_at(post.prc_mp, post.pt_mp, source); process_pagetable_wf_process_at(post.prc_mp, post.pt_mp, target);
    kernel_pagetable_mappings_projection_at(pre, source); kernel_pagetable_mappings_projection_at(pre, target);
}

/// Releasing cpu `cpu_id`'s read holds on `source_table` and `target_table`, which other readers may keep, dropping their 2M windows, and
/// replacing `thread`'s progress removes `cpu_id` from the readers of both tables in the complete projection.
pub proof fn kernel_pagetable_pair_runlocked_and_progress_changed_implies_u_step(
    pre: &KernelK, post: &KernelK, cpu_id: CpuId, source: RwLockProcessPtr, target: RwLockProcessPtr, source_table: RwLockPageTableRoot, target_table: RwLockPageTableRoot,
    thread: RwLockThreadPtr,
)
    requires
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        source != target,
        source_table != target_table,
        pre.prc_mp.dom().contains(source),
        pre.prc_mp.dom().contains(target),
        !pre.prc_mp.spec_index(source).view().zombie,
        !pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(source).view().pagetable == source_table,
        pre.prc_mp.spec_index(target).view().pagetable == target_table,
        *post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, thrd_mp: post.thrd_mp, ..*pre }),
        post.pt_mp.dom() == pre.pt_mp.dom(),
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) && p != source_table && p != target_table ==> post.pt_mp.spec_index(p) == pre.pt_mp.spec_index(p),
        post.pt_lower.view() == pre.pt_lower.view().insert(source_table, post.pt_lower.view().spec_index(source_table)).insert(target_table, post.pt_lower.view().spec_index(target_table)),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), source_table).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), source_table).mapping_4k(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), source_table).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), source_table).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), source_table).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), source_table).mapping_1g(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), target_table).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), target_table).mapping_4k(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), target_table).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), target_table).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), target_table).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), target_table).mapping_1g(),
        pre.thrd_mp.dom().contains(thread),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thread),
        post.thrd_mp.spec_index(thread).view() == (Thread { syscall_progress: post.thrd_mp.spec_index(thread).view().syscall_progress, ..pre.thrd_mp.spec_index(thread).view() }),
        post.thrd_mp.spec_index(thread).locking_thread() == pre.thrd_mp.spec_index(thread).locking_thread(),
        post.thrd_mp.spec_index(thread).being_killed() == pre.thrd_mp.spec_index(thread).being_killed(),
        post.pt_mp.spec_index(source_table).lock_state_u() == pre.pt_mp.spec_index(source_table).lock_state_u().without_reader(cpu_id),
        post.pt_mp.spec_index(target_table).lock_state_u() == pre.pt_mp.spec_index(target_table).lock_state_u().without_reader(cpu_id),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            &&& a.thread_map.dom().contains(thread)
            &&& a.thread_map[thread].syscall_progress == pre.thrd_mp.spec_index(thread).view().syscall_progress.view()
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                thread_map: a.thread_map.insert(thread, ThreadU { syscall_progress: post.thrd_mp.spec_index(thread).view().syscall_progress.view(), ..a.thread_map[thread] }),
                process_map: a.process_map.insert(source, ProcessU {
                    pagetable: Some(PageTableU { lock_state: a.process_map[source].pagetable->Some_0.lock_state.without_reader(cpu_id),
                        pagetable_window_locks: whole_pagetable(post.pt_mp, post.pt_lower.view(), source_table).lower.pagetable_window_locks, ..a.process_map[source].pagetable->Some_0 }), ..a.process_map[source]
                }).insert(target, ProcessU {
                    pagetable: Some(PageTableU { lock_state: a.process_map[target].pagetable->Some_0.lock_state.without_reader(cpu_id),
                        pagetable_window_locks: whole_pagetable(post.pt_mp, post.pt_lower.view(), target_table).lower.pagetable_window_locks, ..a.process_map[target].pagetable->Some_0 }), ..a.process_map[target]
                }),
                ..a
            })
        }),
{
    kernel_pagetable_pair_lock_modes_and_progress_changed_implies_u_step(pre, post, source, target, source_table, target_table, thread);
    process_pagetable_wf_process_at(post.prc_mp, post.pt_mp, source); process_pagetable_wf_process_at(post.prc_mp, post.pt_mp, target);
    kernel_pagetable_mappings_projection_at(pre, source); kernel_pagetable_mappings_projection_at(pre, target);
}

/// Downgrading cpu `cpu_id`'s write lock on `target_table`, the page table of `target`, to its only read hold under the same token, with
/// the table's contents and every other kernel field kept, adds `cpu_id` as the reader of that table in the complete projection.
pub proof fn kernel_pagetable_downgraded_implies_u_step(pre: &KernelK, post: &KernelK, cpu_id: CpuId, target: RwLockProcessPtr, target_table: RwLockPageTableRoot)
    requires
        process_pagetable_wf(pre.prc_mp, pre.pt_mp),
        pre.prc_mp.dom().contains(target),
        !pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().pagetable == target_table,
        *post == (KernelK { pt_mp: post.pt_mp, ..*pre }),
        post.pt_mp.unchanged_except(&pre.pt_mp, target_table),
        post.pt_mp.spec_index(target_table).view() == pre.pt_mp.spec_index(target_table).view(),
        pre.pt_mp.spec_index(target_table).wlocked_by_thread(cpu_id),
        post.pt_mp.spec_index(target_table).locking_thread() == (RwLockState::Read { reader_map: Map::empty().insert(cpu_id, pre.pt_mp.spec_index(target_table).locking_thread()->Write_lock_id) }),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            &&& a.process_map.dom().contains(target)
            &&& a.process_map[target].pagetable is Some
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                process_map: a.process_map.insert(target, ProcessU {
                    pagetable: Some(PageTableU { lock_state: a.process_map[target].pagetable->Some_0.lock_state.with_reader(cpu_id), ..a.process_map[target].pagetable->Some_0 }), ..a.process_map[target]
                }),
                ..a
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    process_pagetable_wf_process_at(pre.prc_mp, pre.pt_mp, target); kernel_pagetable_mappings_projection_at(pre, target);
    assert(post.pt_mp.spec_index(target_table).lock_state_u() == pre.pt_mp.spec_index(target_table).lock_state_u().with_reader(cpu_id)) by {
        assert(post.pt_mp.spec_index(target_table).locking_thread()->Read_reader_map.dom() =~= Set::empty().insert(cpu_id));
    };
    assert_maps_equal!(b.process_map, a.process_map.insert(target, ProcessU {
        pagetable: Some(PageTableU { lock_state: a.process_map[target].pagetable->Some_0.lock_state.with_reader(cpu_id), ..a.process_map[target].pagetable->Some_0 }), ..a.process_map[target]
    }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); kernel_process_projection_at(post, p); } reveal(process_pagetable_wf);
    });
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_thread_map_unchanged_implies_u_thread_map(pre, post);
    kernel_container_maps_unchanged_implies_u_container_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}

/// Locking or releasing both page tables of a pages rendezvous, holding or dropping their 2M windows, and
/// replacing `thread`'s progress changes only those two page tables' lock states and that thread's progress in the complete
/// projection: window locks rewrite the lower halves of both tables without changing their mappings.
proof fn kernel_pagetable_pair_lock_modes_and_progress_changed_implies_u_step(
    pre: &KernelK, post: &KernelK, source: RwLockProcessPtr, target: RwLockProcessPtr, source_table: RwLockPageTableRoot, target_table: RwLockPageTableRoot,
    thread: RwLockThreadPtr,
)
    requires
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        source != target,
        source_table != target_table,
        pre.prc_mp.dom().contains(source),
        pre.prc_mp.dom().contains(target),
        !pre.prc_mp.spec_index(source).view().zombie,
        !pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(source).view().pagetable == source_table,
        pre.prc_mp.spec_index(target).view().pagetable == target_table,
        *post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, thrd_mp: post.thrd_mp, ..*pre }),
        post.pt_mp.dom() == pre.pt_mp.dom(),
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) && p != source_table && p != target_table ==> post.pt_mp.spec_index(p) == pre.pt_mp.spec_index(p),
        post.pt_lower.view() == pre.pt_lower.view().insert(source_table, post.pt_lower.view().spec_index(source_table)).insert(target_table, post.pt_lower.view().spec_index(target_table)),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), source_table).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), source_table).mapping_4k(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), source_table).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), source_table).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), source_table).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), source_table).mapping_1g(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), target_table).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), target_table).mapping_4k(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), target_table).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), target_table).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), target_table).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), target_table).mapping_1g(),
        pre.thrd_mp.dom().contains(thread),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thread),
        post.thrd_mp.spec_index(thread).view() == (Thread { syscall_progress: post.thrd_mp.spec_index(thread).view().syscall_progress, ..pre.thrd_mp.spec_index(thread).view() }),
        post.thrd_mp.spec_index(thread).locking_thread() == pre.thrd_mp.spec_index(thread).locking_thread(),
        post.thrd_mp.spec_index(thread).being_killed() == pre.thrd_mp.spec_index(thread).being_killed(),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            &&& a.thread_map.dom().contains(thread)
            &&& a.thread_map[thread].syscall_progress == pre.thrd_mp.spec_index(thread).view().syscall_progress.view()
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                thread_map: a.thread_map.insert(thread, ThreadU { syscall_progress: post.thrd_mp.spec_index(thread).view().syscall_progress.view(), ..a.thread_map[thread] }),
                process_map: a.process_map.insert(source, ProcessU {
                    pagetable: Some(PageTableU { lock_state: post.pt_mp.spec_index(source_table).lock_state_u(),
                        pagetable_window_locks: whole_pagetable(post.pt_mp, post.pt_lower.view(), source_table).lower.pagetable_window_locks, ..a.process_map[source].pagetable->Some_0 }), ..a.process_map[source]
                }).insert(target, ProcessU {
                    pagetable: Some(PageTableU { lock_state: post.pt_mp.spec_index(target_table).lock_state_u(),
                        pagetable_window_locks: whole_pagetable(post.pt_mp, post.pt_lower.view(), target_table).lower.pagetable_window_locks, ..a.process_map[target].pagetable->Some_0 }), ..a.process_map[target]
                }),
                ..a
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    kernel_thread_projection_at(pre, thread);
    assert_maps_equal!(b.thread_map, a.thread_map.insert(thread, ThreadU { syscall_progress: post.thrd_mp.spec_index(thread).view().syscall_progress.view(), ..a.thread_map[thread] }), t => {
        if pre.thrd_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thrd_mp.dom().contains(t) { kernel_thread_projection_at(post, t); }
    });
    kernel_pagetable_pair_lock_modes_changed_implies_u_process_map(pre, post, source, target, source_table, target_table);
    assert_seqs_equal!(b.cpu_array == a.cpu_array, i => { if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); } });
    assert_maps_equal!(b.container_map, a.container_map, c => {
        if pre.ctn_mp.dom().contains(c) { kernel_container_projection_at(pre, c); } if post.ctn_mp.dom().contains(c) { kernel_container_projection_at(post, c); }
    });
    assert_maps_equal!(b.endpoint_map, a.endpoint_map, e => {
        if pre.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(pre, e); } if post.ep_mp.dom().contains(e) { kernel_endpoint_projection_at(post, e); }
    });
}

/// Changing only the lock modes, window locks, and lower-level state of the page tables `source_table` and `target_table` of
/// `source` and `target`, with their mappings kept, changes only those two page tables' lock states and window locks in the
/// process map projection.
proof fn kernel_pagetable_pair_lock_modes_changed_implies_u_process_map(
    pre: &KernelK, post: &KernelK, source: RwLockProcessPtr, target: RwLockProcessPtr, source_table: RwLockPageTableRoot, target_table: RwLockPageTableRoot,
)
    requires
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        source != target,
        source_table != target_table,
        pre.prc_mp.dom().contains(source),
        pre.prc_mp.dom().contains(target),
        !pre.prc_mp.spec_index(source).view().zombie,
        !pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(source).view().pagetable == source_table,
        pre.prc_mp.spec_index(target).view().pagetable == target_table,
        post.prc_mp == pre.prc_mp,
        post.it_mp == pre.it_mp,
        post.pt_mp.dom() == pre.pt_mp.dom(),
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)]
            pre.pt_mp.dom().contains(p) && p != source_table && p != target_table ==> post.pt_mp.spec_index(p) == pre.pt_mp.spec_index(p),
        post.pt_lower.view() == pre.pt_lower.view().insert(source_table, post.pt_lower.view().spec_index(source_table)).insert(target_table, post.pt_lower.view().spec_index(target_table)),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), source_table).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), source_table).mapping_4k(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), source_table).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), source_table).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), source_table).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), source_table).mapping_1g(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), target_table).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), target_table).mapping_4k(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), target_table).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), target_table).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), target_table).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), target_table).mapping_1g(),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            kernel_k_to_kernel_u(*post).process_map == a.process_map.insert(source, ProcessU {
                pagetable: Some(PageTableU { lock_state: post.pt_mp.spec_index(source_table).lock_state_u(),
                    pagetable_window_locks: whole_pagetable(post.pt_mp, post.pt_lower.view(), source_table).lower.pagetable_window_locks, ..a.process_map[source].pagetable->Some_0 }), ..a.process_map[source]
            }).insert(target, ProcessU {
                pagetable: Some(PageTableU { lock_state: post.pt_mp.spec_index(target_table).lock_state_u(),
                    pagetable_window_locks: whole_pagetable(post.pt_mp, post.pt_lower.view(), target_table).lower.pagetable_window_locks, ..a.process_map[target].pagetable->Some_0 }), ..a.process_map[target]
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    assert_maps_equal!(b.process_map, a.process_map.insert(source, ProcessU {
        pagetable: Some(PageTableU { lock_state: post.pt_mp.spec_index(source_table).lock_state_u(), pagetable_window_locks: whole_pagetable(post.pt_mp, post.pt_lower.view(), source_table).lower.pagetable_window_locks, ..a.process_map[source].pagetable->Some_0 }), ..a.process_map[source]
    }).insert(target, ProcessU {
        pagetable: Some(PageTableU { lock_state: post.pt_mp.spec_index(target_table).lock_state_u(), pagetable_window_locks: whole_pagetable(post.pt_mp, post.pt_lower.view(), target_table).lower.pagetable_window_locks, ..a.process_map[target].pagetable->Some_0 }), ..a.process_map[target]
    }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); } reveal(process_pagetable_wf);
    });
}
}
