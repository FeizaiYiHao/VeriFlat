use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal};
use crate::*;

verus! {
/// Every 2M window of `pagetable_ptr` held in `lctx` keeps the present 4K mappings inside it and its 2M mapping in both
/// projections of `prc_ptr`, whose pagetable `pagetable_ptr` is before and after.
pub proof fn kernel_held_pagetable_windows_unchanged_implies_u_window_mappings_eq(pre: &KernelK, post: &KernelK, lctx: &LocalContext, prc_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot)
    requires
        held_pagetable_windows_unchanged(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), lctx),
        pre.prc_mp.dom().contains(prc_ptr),
        !pre.prc_mp.spec_index(prc_ptr).view().zombie,
        pre.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr,
        pre.pt_mp.dom().contains(pagetable_ptr),
        post.prc_mp.dom().contains(prc_ptr),
        !post.prc_mp.spec_index(prc_ptr).view().zombie,
        post.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr,
        post.pt_mp.dom().contains(pagetable_ptr),
    ensures
        kernel_k_to_kernel_u(*pre).process_map.dom().contains(prc_ptr) && kernel_k_to_kernel_u(*pre).process_map.spec_index(prc_ptr).pagetable is Some,
        kernel_k_to_kernel_u(*post).process_map.dom().contains(prc_ptr) && kernel_k_to_kernel_u(*post).process_map.spec_index(prc_ptr).pagetable is Some,
        forall|wva: WindowVa, v: VAddr|
            #![trigger lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, wva)), kernel_k_to_kernel_u(*post).process_map.spec_index(prc_ptr).pagetable->Some_0.mapping_4k.dom().contains(v)]
            #![trigger lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, wva)), kernel_k_to_kernel_u(*pre).process_map.spec_index(prc_ptr).pagetable->Some_0.mapping_4k.dom().contains(v)]
            lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, wva)) && spec_v2l4index(v) == spec_v2l4index(wva.va) && spec_v2l3index(v) == spec_v2l3index(wva.va) && spec_v2l2index(v) == spec_v2l2index(wva.va) ==> {
                let pre_t = kernel_k_to_kernel_u(*pre).process_map.spec_index(prc_ptr).pagetable->Some_0;
                let post_t = kernel_k_to_kernel_u(*post).process_map.spec_index(prc_ptr).pagetable->Some_0;
                &&& post_t.mapping_4k.dom().contains(v) == pre_t.mapping_4k.dom().contains(v)
                &&& pre_t.mapping_4k.dom().contains(v) ==> post_t.mapping_4k.spec_index(v) == pre_t.mapping_4k.spec_index(v)
            },
{
    kernel_process_projection_at(pre, prc_ptr); kernel_process_projection_at(post, prc_ptr);
}

/// Read-mode entry: the cpu and thread become write-held, the process pagetable becomes read-held, and the thread's progress
/// is replaced; window locks may rewrite the table's lower half without changing its mappings. `lctx` is aligned with `pre`.
pub proof fn kernel_cpu_thread_wlocked_pagetable_rlocked_and_progress_changed_implies_u_step(pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot)
    requires
        process_cpu_wf(pre.prc_mp, pre.cpu_arr),
        process_pagetable_match(pre.prc_mp, pre.pt_mp),
        typed_lock_maps_aligned(pre, lctx),
        index_valid(NUM_CPUS, cpu_id),
        *post == (KernelK { cpu_arr: post.cpu_arr, cpu_op: post.cpu_op, thrd_mp: post.thrd_mp, pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..*pre }),
        post.cpu_arr.entries_unchanged_except(&pre.cpu_arr, cpu_id),
        post.cpu_arr.spec_index(cpu_id).view().view().view() == pre.cpu_arr.spec_index(cpu_id).view().view().view(),
        forall|i: CpuId| #![trigger post.cpu_op.view().view()[i as int]] index_valid(NUM_CPUS, i) && i != cpu_id ==> post.cpu_op.view().view()[i as int] == pre.cpu_op.view().view()[i as int],
        post.cpu_arr.spec_index(cpu_id).value.being_killed() == pre.cpu_arr.spec_index(cpu_id).value.being_killed(),
        post.cpu_arr.spec_index(cpu_id).value.locking_thread() is Write,
        pre.thrd_mp.dom().contains(thrd_ptr),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..pre.thrd_mp.spec_index(thrd_ptr).view() }),
        post.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() is Write,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        pre.prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr,
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        post.pt_mp.spec_index(pagetable_ptr).locking_thread() is Read,
        post.pt_lower.view() == pre.pt_lower.view().insert(pagetable_ptr, post.pt_lower.view().spec_index(pagetable_ptr)),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_1g(),
    ensures
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let thread = pre.thrd_mp.spec_index(thrd_ptr).view();
            let process = pre_u.process_map.spec_index(prc_ptr);
            &&& pre_u.thread_map.dom().contains(thrd_ptr)
            &&& pre_u.thread_map.spec_index(thrd_ptr).owning_proc == thread.owning_proc
            &&& pre_u.thread_map.spec_index(thrd_ptr).syscall_progress == thread.syscall_progress.view()
            &&& pre_u.process_map.dom().contains(prc_ptr)
            &&& process.pagetable is Some
            &&& typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write) ==> pre_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write) ==> pre_u.thread_map.spec_index(thrd_ptr).lock_state is WriteLocked
            &&& pre_u.cpu_array[cpu_id as int].lock_state == pre.cpu_arr.spec_index(cpu_id).value.lock_state_u()
            &&& pre_u.cpu_array[cpu_id as int].state == pre.cpu_arr.spec_index(cpu_id).view().view().view().state
            &&& pre_u.cpu_array[cpu_id as int].current_thread == pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread
            &&& pre_u.thread_map.spec_index(thrd_ptr).lock_state == pre.thrd_mp.spec_index(thrd_ptr).lock_state_u()
            &&& pre_u.thread_map.spec_index(thrd_ptr).killed == pre.thrd_mp.spec_index(thrd_ptr).being_killed()
            &&& pre_u.thread_map.spec_index(thrd_ptr).quota_4k == thread.quota_4k
            &&& process.pagetable->Some_0.lock_state == pre.pt_mp.spec_index(pagetable_ptr).lock_state_u()
            &&& process.pagetable->Some_0.mapping_4k.dom().subset_of(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k().dom())
            &&& process.pagetable->Some_0.mapping_2m.dom().subset_of(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m().dom())
            &&& process.pagetable->Some_0.mapping_1g.dom().subset_of(whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_1g().dom())
        }),
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let process = pre_u.process_map.spec_index(prc_ptr);
            kernel_k_to_kernel_u(*post) == (KernelU {
                cpu_array: pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, op: post.cpu_op.view().view()[cpu_id as int], ..pre_u.cpu_array[cpu_id as int] }),
                thread_map: pre_u.thread_map.insert(thrd_ptr, ThreadU {
                    lock_state: LockStateU::WriteLocked, syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(), ..pre_u.thread_map.spec_index(thrd_ptr)
                }),
                process_map: pre_u.process_map.insert(prc_ptr, ProcessU { pagetable: Some(PageTableU { lock_state: LockStateU::ReadLocked,
                    pagetable_window_locks: whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks, ..process.pagetable->Some_0 }), ..process }),
                ..pre_u
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let process = pre_u.process_map.spec_index(prc_ptr);
    kernel_cpu_projection_at(pre, cpu_id);
    kernel_thread_projection_at(pre, thrd_ptr);
    assert(pre.prc_mp.dom().contains(prc_ptr) && !pre.prc_mp.spec_index(prc_ptr).view().zombie && pre.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr) by { reveal(process_cpu_wf); reveal(process_pagetable_match); };
    kernel_process_projection_at(pre, prc_ptr); kernel_process_projection_at(post, prc_ptr);
    assert(typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write) ==> pre.cpu_arr.spec_index(cpu_id).view().wlocked_by_thread(lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); };
    if typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write) { pre.thrd_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thrd_ptr); }
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::WriteLocked, op: post.cpu_op.view().view()[cpu_id as int], ..pre_u.cpu_array[cpu_id as int] }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); }
    });
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(prc_ptr, ProcessU { pagetable: Some(PageTableU { lock_state: LockStateU::ReadLocked,
        pagetable_window_locks: whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks, ..process.pagetable->Some_0 }), ..process }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); } reveal(process_pagetable_match);
    });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thrd_ptr, ThreadU {
        lock_state: LockStateU::WriteLocked, syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(), ..pre_u.thread_map.spec_index(thrd_ptr)
    }), t => { if pre.thrd_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thrd_mp.dom().contains(t) { kernel_thread_projection_at(post, t); } });
    kernel_container_maps_unchanged_implies_u_container_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}

/// Read-mode exit: the cpu and thread are released, the thread's read hold on the process pagetable is dropped (other readers
/// may remain), and the thread's progress is replaced; window unlocks may rewrite the table's lower half without changing its
/// mappings. `lctx` is aligned with `pre`.
pub proof fn kernel_cpu_thread_unlocked_pagetable_runlocked_and_progress_changed_implies_u_step(pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot)
    requires
        process_cpu_wf(pre.prc_mp, pre.cpu_arr),
        process_pagetable_match(pre.prc_mp, pre.pt_mp),
        typed_lock_maps_aligned(pre, lctx),
        index_valid(NUM_CPUS, cpu_id),
        *post == (KernelK { cpu_arr: post.cpu_arr, cpu_op: post.cpu_op, thrd_mp: post.thrd_mp, pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..*pre }),
        post.cpu_arr.entries_unchanged_except(&pre.cpu_arr, cpu_id),
        post.cpu_arr.spec_index(cpu_id).view().view().view() == pre.cpu_arr.spec_index(cpu_id).view().view().view(),
        forall|i: CpuId| #![trigger post.cpu_op.view().view()[i as int]] index_valid(NUM_CPUS, i) && i != cpu_id ==> post.cpu_op.view().view()[i as int] == pre.cpu_op.view().view()[i as int],
        post.cpu_arr.spec_index(cpu_id).value.being_killed() == pre.cpu_arr.spec_index(cpu_id).value.being_killed(),
        post.cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        pre.thrd_mp.dom().contains(thrd_ptr),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..pre.thrd_mp.spec_index(thrd_ptr).view() }),
        post.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() is None,
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        pre.prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr,
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        !(post.pt_mp.spec_index(pagetable_ptr).locking_thread() is Write),
        post.pt_lower.view() == pre.pt_lower.view().insert(pagetable_ptr, post.pt_lower.view().spec_index(pagetable_ptr)),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_1g(),
    ensures
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let thread = pre.thrd_mp.spec_index(thrd_ptr).view();
            let process = pre_u.process_map.spec_index(prc_ptr);
            &&& pre_u.thread_map.dom().contains(thrd_ptr)
            &&& pre_u.thread_map.spec_index(thrd_ptr).owning_proc == thread.owning_proc
            &&& pre_u.thread_map.spec_index(thrd_ptr).syscall_progress == thread.syscall_progress.view()
            &&& pre_u.process_map.dom().contains(prc_ptr)
            &&& process.pagetable is Some
            &&& typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write) ==> pre_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write) ==> pre_u.thread_map.spec_index(thrd_ptr).lock_state is WriteLocked
            &&& typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read) ==> process.pagetable->Some_0.lock_state is ReadLocked
            &&& pre_u.cpu_array[cpu_id as int].lock_state == pre.cpu_arr.spec_index(cpu_id).value.lock_state_u()
            &&& pre_u.cpu_array[cpu_id as int].current_thread == pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread
            &&& pre_u.thread_map.spec_index(thrd_ptr).lock_state == pre.thrd_mp.spec_index(thrd_ptr).lock_state_u()
            &&& process.pagetable->Some_0.lock_state == pre.pt_mp.spec_index(pagetable_ptr).lock_state_u()
        }),
        post.pt_mp.spec_index(pagetable_ptr).lock_state_u() is Unlocked || post.pt_mp.spec_index(pagetable_ptr).lock_state_u() is ReadLocked,
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let process = pre_u.process_map.spec_index(prc_ptr);
            kernel_k_to_kernel_u(*post) == (KernelU {
                cpu_array: pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: post.cpu_op.view().view()[cpu_id as int], ..pre_u.cpu_array[cpu_id as int] }),
                thread_map: pre_u.thread_map.insert(thrd_ptr, ThreadU {
                    lock_state: LockStateU::Unlocked, syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(), ..pre_u.thread_map.spec_index(thrd_ptr)
                }),
                process_map: pre_u.process_map.insert(prc_ptr, ProcessU {
                    pagetable: Some(PageTableU { lock_state: post.pt_mp.spec_index(pagetable_ptr).lock_state_u(), pagetable_window_locks: whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks, ..process.pagetable->Some_0 }), ..process
                }),
                ..pre_u
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let process = pre_u.process_map.spec_index(prc_ptr);
    let table_lock_state = post.pt_mp.spec_index(pagetable_ptr).lock_state_u();
    kernel_cpu_projection_at(pre, cpu_id);
    kernel_thread_projection_at(pre, thrd_ptr);
    assert(pre.prc_mp.dom().contains(prc_ptr) && !pre.prc_mp.spec_index(prc_ptr).view().zombie && pre.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr) by { reveal(process_cpu_wf); reveal(process_pagetable_match); };
    kernel_process_projection_at(pre, prc_ptr); kernel_process_projection_at(post, prc_ptr);
    assert(typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write) ==> pre.cpu_arr.spec_index(cpu_id).view().wlocked_by_thread(lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); };
    if typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write) { pre.thrd_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thrd_ptr); }
    if typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read) { pre.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); }
    assert_seqs_equal!(post_u.cpu_array == pre_u.cpu_array.update(cpu_id as int, CpuU { lock_state: LockStateU::Unlocked, op: post.cpu_op.view().view()[cpu_id as int], ..pre_u.cpu_array[cpu_id as int] }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(pre, i as usize); kernel_cpu_projection_at(post, i as usize); }
    });
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(prc_ptr, ProcessU { pagetable: Some(PageTableU { lock_state: table_lock_state,
        pagetable_window_locks: whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks, ..process.pagetable->Some_0 }), ..process }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); } reveal(process_pagetable_match);
    });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thrd_ptr, ThreadU {
        lock_state: LockStateU::Unlocked, syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(), ..pre_u.thread_map.spec_index(thrd_ptr)
    }), t => { if pre.thrd_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thrd_mp.dom().contains(t) { kernel_thread_projection_at(post, t); } });
    kernel_container_maps_unchanged_implies_u_container_map(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}

/// Downgrade: the process pagetable goes from write-held to read-held by the same thread and the thread's progress is
/// replaced, with the cpu and the thread's lock untouched; window locks may rewrite the table's lower half without changing
/// its mappings. `lctx` is aligned with `pre`.
pub proof fn kernel_pagetable_downgraded_and_progress_changed_implies_u_step(pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot)
    requires
        process_cpu_wf(pre.prc_mp, pre.cpu_arr),
        process_pagetable_match(pre.prc_mp, pre.pt_mp),
        typed_lock_maps_aligned(pre, lctx),
        index_valid(NUM_CPUS, cpu_id),
        *post == (KernelK { thrd_mp: post.thrd_mp, pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..*pre }),
        pre.thrd_mp.dom().contains(thrd_ptr),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..pre.thrd_mp.spec_index(thrd_ptr).view() }),
        post.thrd_mp.spec_index(thrd_ptr).locking_thread() == pre.thrd_mp.spec_index(thrd_ptr).locking_thread(),
        post.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        pre.prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr,
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        pre.pt_mp.spec_index(pagetable_ptr).locking_thread() is Write,
        post.pt_mp.spec_index(pagetable_ptr).locking_thread() is Read,
        post.pt_lower.view() == pre.pt_lower.view().insert(pagetable_ptr, post.pt_lower.view().spec_index(pagetable_ptr)),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_1g(),
    ensures
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let thread = pre.thrd_mp.spec_index(thrd_ptr).view();
            let process = pre_u.process_map.spec_index(prc_ptr);
            &&& pre_u.thread_map.dom().contains(thrd_ptr)
            &&& pre_u.thread_map.spec_index(thrd_ptr).owning_proc == thread.owning_proc
            &&& pre_u.thread_map.spec_index(thrd_ptr).syscall_progress == thread.syscall_progress.view()
            &&& pre_u.process_map.dom().contains(prc_ptr)
            &&& process.pagetable is Some
            &&& process.pagetable->Some_0.lock_state is WriteLocked
            &&& typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write) ==> pre_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write) ==> pre_u.thread_map.spec_index(thrd_ptr).lock_state is WriteLocked
            &&& pre_u.cpu_array[cpu_id as int].lock_state == pre.cpu_arr.spec_index(cpu_id).value.lock_state_u()
            &&& pre_u.cpu_array[cpu_id as int].current_thread == pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread
            &&& pre_u.thread_map.spec_index(thrd_ptr).lock_state == pre.thrd_mp.spec_index(thrd_ptr).lock_state_u()
        }),
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let process = pre_u.process_map.spec_index(prc_ptr);
            kernel_k_to_kernel_u(*post) == (KernelU {
                thread_map: pre_u.thread_map.insert(thrd_ptr, ThreadU {
                    syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(), ..pre_u.thread_map.spec_index(thrd_ptr)
                }),
                process_map: pre_u.process_map.insert(prc_ptr, ProcessU { pagetable: Some(PageTableU { lock_state: LockStateU::ReadLocked,
                    pagetable_window_locks: whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks, ..process.pagetable->Some_0 }), ..process }),
                ..pre_u
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let process = pre_u.process_map.spec_index(prc_ptr);
    kernel_cpu_projection_at(pre, cpu_id);
    kernel_thread_projection_at(pre, thrd_ptr);
    assert(pre.prc_mp.dom().contains(prc_ptr) && !pre.prc_mp.spec_index(prc_ptr).view().zombie && pre.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr) by { reveal(process_cpu_wf); reveal(process_pagetable_match); };
    kernel_process_projection_at(pre, prc_ptr); kernel_process_projection_at(post, prc_ptr);
    assert(typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write) ==> pre.cpu_arr.spec_index(cpu_id).view().wlocked_by_thread(lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); };
    if typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write) { pre.thrd_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thrd_ptr); }
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(prc_ptr, ProcessU { pagetable: Some(PageTableU { lock_state: LockStateU::ReadLocked,
        pagetable_window_locks: whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks, ..process.pagetable->Some_0 }), ..process }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); } reveal(process_pagetable_match);
    });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thrd_ptr, ThreadU {
        syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(), ..pre_u.thread_map.spec_index(thrd_ptr)
    }), t => { if pre.thrd_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thrd_mp.dom().contains(t) { kernel_thread_projection_at(post, t); } });
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_container_maps_unchanged_implies_u_container_map(pre, post);
    kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}

/// A section that changes only one thread's quota, temporary cache, and progress plus the
/// kernel-only structure of one pagetable changes only that thread's quota and progress and, for
/// a visible process, that pagetable's window locks in the complete projection. `lctx` is aligned
/// with `post`, write-holds the cpu and thread, and read-holds the pagetable across the section.
pub proof fn kernel_thread_quota_4k_and_progress_changed_pagetable_rlocked_implies_u_step(pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot)
    requires
        process_cpu_wf(pre.prc_mp, pre.cpu_arr),
        process_pagetable_match(pre.prc_mp, pre.pt_mp),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(post, lctx),
        pre.thrd_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        pre.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        *post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, pg_arr: post.pg_arr, thrd_mp: post.thrd_mp, ..*pre }),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).view() == (Thread {
            quota_4k: post.thrd_mp.spec_index(thrd_ptr).view().quota_4k,
            temp_alloc_cache_4k: post.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_4k,
            syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress,
            ..pre.thrd_mp.spec_index(thrd_ptr).view()
        }),
        post.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
        pre.prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr,
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        post.pt_lower.view() == pre.pt_lower.view().insert(pagetable_ptr, post.pt_lower.view().spec_index(pagetable_ptr)),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_1g(),
    ensures
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let thread = pre.thrd_mp.spec_index(thrd_ptr).view();
            let process = pre_u.process_map.spec_index(prc_ptr);
            &&& pre_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& pre_u.cpu_array[cpu_id as int].current_thread == pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread
            &&& pre_u.thread_map.dom().contains(thrd_ptr)
            &&& pre_u.thread_map.spec_index(thrd_ptr).lock_state is WriteLocked
            &&& pre_u.thread_map.spec_index(thrd_ptr).owning_proc == thread.owning_proc
            &&& pre_u.thread_map.spec_index(thrd_ptr).quota_4k == thread.quota_4k
            &&& pre_u.thread_map.spec_index(thrd_ptr).syscall_progress == thread.syscall_progress.view()
            &&& pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr) ==> {
                &&& pre_u.process_map.dom().contains(prc_ptr)
                &&& process.pagetable is Some
                &&& process.pagetable->Some_0.lock_state is ReadLocked
            }
        }),
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let owner = pre.pt_mp.spec_index(pagetable_ptr).view().proc_ptr;
            kernel_k_to_kernel_u(*post) == (KernelU {
                thread_map: pre_u.thread_map.insert(thrd_ptr, ThreadU {
                    quota_4k: post.thrd_mp.spec_index(thrd_ptr).view().quota_4k,
                    syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(),
                    ..pre_u.thread_map.spec_index(thrd_ptr)
                }),
                process_map: if pre_u.process_map.dom().contains(owner) && pre_u.process_map[owner].pagetable is Some {
                    pre_u.process_map.insert(owner, ProcessU {
                        pagetable: Some(PageTableU {
                            pagetable_window_locks: whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks, ..pre_u.process_map[owner].pagetable->Some_0
                        }),
                        ..pre_u.process_map[owner]
                    })
                } else { pre_u.process_map },
                ..pre_u
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    pre.thrd_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thrd_ptr);
    post.thrd_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thrd_ptr);
    pre.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
    post.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
    kernel_cpu_projection_at(pre, cpu_id); kernel_cpu_projection_at(post, cpu_id);
    if pre.prc_mp.dom().contains(prc_ptr) { kernel_process_projection_at(pre, prc_ptr); }
    if pre.thrd_mp.dom().contains(thrd_ptr) { kernel_thread_projection_at(pre, thrd_ptr); }
    assert(pre.cpu_arr.spec_index(cpu_id).view().wlocked_by_thread(lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); };
    assert(pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr)
        ==> pre.prc_mp.dom().contains(prc_ptr) && !pre.prc_mp.spec_index(prc_ptr).view().zombie && pre.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr) by {
        reveal(process_cpu_wf); reveal(process_pagetable_match);
    };
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_container_maps_unchanged_implies_u_container_map(pre, post);
    let owner = pre.pt_mp.spec_index(pagetable_ptr).view().proc_ptr;
    if pre_u.process_map.dom().contains(owner) && pre_u.process_map[owner].pagetable is Some {
        assert(pre.prc_mp.spec_index(owner).view().pagetable == pagetable_ptr) by { reveal(process_pagetable_match); };
        assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(owner, ProcessU {
            pagetable: Some(PageTableU { pagetable_window_locks: whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks, ..pre_u.process_map[owner].pagetable->Some_0 }),
            ..pre_u.process_map[owner]
        }), p => {
            if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); } reveal(process_pagetable_match);
        });
    } else {
        assert_maps_equal!(post_u.process_map, pre_u.process_map, p => {
            if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); } reveal(process_pagetable_match);
        });
    }
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thrd_ptr, ThreadU {
        quota_4k: post.thrd_mp.spec_index(thrd_ptr).view().quota_4k,
        syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(),
        ..pre_u.thread_map.spec_index(thrd_ptr)
    }), t => { if pre.thrd_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thrd_mp.dom().contains(t) { kernel_thread_projection_at(post, t); } });
    kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}

/// A section that changes one thread's quota, temporary cache, and progress and publishes one
/// present 4K entry of the running process's pagetable changes only that thread and that
/// process's pagetable mapping in the complete projection. `lctx` is aligned with `post`,
/// write-holds the cpu and thread, and read-holds the pagetable across the section.
pub proof fn kernel_thread_quota_4k_progress_and_4k_mapping_added_pagetable_rlocked_implies_u_step(pre: &KernelK, post: &KernelK, lctx: &LocalContext, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_maps_aligned(post, lctx),
        pre.thrd_mp.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id()),
        pre.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        *post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, pg_arr: post.pg_arr, thrd_mp: post.thrd_mp, ..*pre }),
        post.thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).view() == (Thread {
            quota_4k: post.thrd_mp.spec_index(thrd_ptr).view().quota_4k,
            temp_alloc_cache_4k: post.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_4k,
            syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress,
            ..pre.thrd_mp.spec_index(thrd_ptr).view()
        }),
        post.thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed(),
        pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        pre.prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr,
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        post.pt_lower.view() == pre.pt_lower.view().insert(pagetable_ptr, post.pt_lower.view().spec_index(pagetable_ptr)),
        !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(va),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k().insert(va, whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(va)),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(va).present,
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_1g(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks,
        pre.pg_arr.spec_index(page_ptr2page_index(whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(va).addr)).view().view().state is Owned4k,
    ensures
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let thread = pre.thrd_mp.spec_index(thrd_ptr).view();
            let process = pre_u.process_map.spec_index(prc_ptr);
            let addr = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(va).addr;
            &&& pre_u.cpu_array[cpu_id as int].lock_state is WriteLocked
            &&& pre_u.cpu_array[cpu_id as int].current_thread == pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread
            &&& pre_u.thread_map.dom().contains(thrd_ptr)
            &&& pre_u.thread_map.spec_index(thrd_ptr).lock_state is WriteLocked
            &&& pre_u.thread_map.spec_index(thrd_ptr).owning_container == thread.owning_container
            &&& pre_u.thread_map.spec_index(thrd_ptr).owning_proc == thread.owning_proc
            &&& pre_u.thread_map.spec_index(thrd_ptr).quota_4k == thread.quota_4k
            &&& pre_u.thread_map.spec_index(thrd_ptr).syscall_progress == thread.syscall_progress.view()
            &&& pre_u.process_map.dom().contains(prc_ptr)
            &&& process.pagetable is Some
            &&& process.pagetable->Some_0.lock_state is ReadLocked
            &&& !process.pagetable->Some_0.mapping_4k.dom().contains(va)
            &&& forall|p: RwLockProcessPtr, v: VAddr| #![trigger pre_u.process_map[p].pagetable->Some_0.mapping_4k[v]]
                pre_u.process_map.dom().contains(p) && pre_u.process_map[p].pagetable is Some && pre_u.process_map[p].pagetable->Some_0.mapping_4k.dom().contains(v)
                ==> pre_u.process_map[p].pagetable->Some_0.mapping_4k[v].addr != addr
        }),
        ({
            let pre_u = kernel_k_to_kernel_u(*pre);
            let process = pre_u.process_map.spec_index(prc_ptr);
            let pagetable = process.pagetable->Some_0;
            let entry = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(va);
            kernel_k_to_kernel_u(*post) == (KernelU {
                thread_map: pre_u.thread_map.insert(thrd_ptr, ThreadU {
                    quota_4k: post.thrd_mp.spec_index(thrd_ptr).view().quota_4k,
                    syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(),
                    ..pre_u.thread_map.spec_index(thrd_ptr)
                }),
                process_map: pre_u.process_map.insert(prc_ptr, ProcessU {
                    pagetable: Some(PageTableU { mapping_4k: pagetable.mapping_4k.insert(va, entry), ..pagetable }),
                    ..process
                }),
                ..pre_u
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let pre_u = kernel_k_to_kernel_u(*pre);
    let post_u = kernel_k_to_kernel_u(*post);
    let process = pre_u.process_map.spec_index(prc_ptr);
    let pagetable = process.pagetable->Some_0;
    let entry = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(va);
    let new_pagetable = PageTableU { mapping_4k: pagetable.mapping_4k.insert(va, entry), ..pagetable };
    pre.thrd_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thrd_ptr);
    post.thrd_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thrd_ptr);
    pre.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
    post.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
    kernel_cpu_projection_at(post, cpu_id);
    if pre.prc_mp.dom().contains(prc_ptr) { kernel_process_projection_at(pre, prc_ptr); } if post.prc_mp.dom().contains(prc_ptr) { kernel_process_projection_at(post, prc_ptr); }
    if pre.thrd_mp.dom().contains(thrd_ptr) { kernel_thread_projection_at(pre, thrd_ptr); } if post.thrd_mp.dom().contains(thrd_ptr) { kernel_thread_projection_at(post, thrd_ptr); }
    assert(pre.cpu_arr.spec_index(cpu_id).view().wlocked_by_thread(lctx.thread_id())) by { reveal(LockedArray::typed_lock_map_aligned); };
    assert(pre.prc_mp.dom().contains(prc_ptr) && !pre.prc_mp.spec_index(prc_ptr).view().zombie && pre.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr) by { reveal(process_cpu_wf); reveal(process_pagetable_match); };
    assert(pagetable == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).user_view(pre.pt_mp.spec_index(pagetable_ptr).lock_state_u()));
    assert(post_u.process_map.spec_index(prc_ptr).pagetable == Some(new_pagetable)) by {
        assert_maps_equal!(whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_ptr).user_view(post.pt_mp.spec_index(pagetable_ptr).lock_state_u()).mapping_4k, new_pagetable.mapping_4k);
    };
    assert(forall|p: RwLockProcessPtr, v: VAddr| #![trigger pre_u.process_map[p].pagetable->Some_0.mapping_4k[v]]
        pre_u.process_map.dom().contains(p) && pre_u.process_map[p].pagetable is Some && pre_u.process_map[p].pagetable->Some_0.mapping_4k.dom().contains(v)
        ==> pre_u.process_map[p].pagetable->Some_0.mapping_4k[v].addr != entry.addr) by { reveal(kernel_k_to_kernel_u); reveal(process_pagetable_match); reveal(mapped_4k_page_pagetable_wf); };
    kernel_container_maps_unchanged_implies_u_container_map(pre, post);
    assert_maps_equal!(post_u.process_map, pre_u.process_map.insert(prc_ptr, ProcessU { pagetable: Some(new_pagetable), ..process }), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); } reveal(process_pagetable_match);
    });
    assert_maps_equal!(post_u.thread_map, pre_u.thread_map.insert(thrd_ptr, ThreadU {
        quota_4k: post.thrd_mp.spec_index(thrd_ptr).view().quota_4k,
        syscall_progress: post.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(),
        ..pre_u.thread_map.spec_index(thrd_ptr)
    }), t => { if pre.thrd_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); } if post.thrd_mp.dom().contains(t) { kernel_thread_projection_at(post, t); } });
    kernel_cpu_array_unchanged_implies_u_cpu_array(pre, post); kernel_endpoint_map_unchanged_implies_u_endpoint_map(pre, post);
}
} // verus!
