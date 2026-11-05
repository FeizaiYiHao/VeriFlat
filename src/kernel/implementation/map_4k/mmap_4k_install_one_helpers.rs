use vstd::prelude::*;
use crate::*;
use super::mmap_4k_create_entry_install::install_staged_4k_page_table_page;
use super::mmap_4k_build_structure::MissingPageTableLevel;
use super::mmap_4k_build_structure_spec::*;
#[cfg(verus_keep_ghost)]
use super::mmap_4k_build_structure_trace::{mmap_4k_directory_step_from_k, mmap_2m_directory_step_from_k};
#[cfg(verus_keep_ghost)]
use super::share_mapping_4k_trace::share_4k_directory_step_from_k;

verus! {
    /// Link the staged page as the missing directory page, then record the installed level in `progress_thread`'s progress and end
    /// the krnl section at the step boundary. `old(krnl)` is the section's start snapshot; `entry_lctx` is the lock context before
    /// the page was staged.
    pub(super) fn install_one_mmap_4k_directory_page_link_and_end_step(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, level: MissingPageTableLevel, cpu_id: CpuId, pg_ptr: PagePtr,
        quota_thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr, pagetable_ptr: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index),
        lo: L2Index, hi: L2Index, write_held: bool, transfer_source: Option<RwLockContainerPtr>, progress_thread: RwLockThreadPtr, Ghost(entry_lctx): Ghost<LocalContext>,
        Ghost(mmap_guard): Ghost<bool>, Ghost(share_guard): Ghost<bool>, Tracked(page_lock_perm): Tracked<LockPerm>, Tracked(quota_thread_lock_perm): Tracked<&LockPerm>,
        Tracked(progress_thread_lock_perm): Tracked<&LockPerm>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>, Tracked(transfer_source_lock_perm): Tracked<Option<&LockPerm>>,
        Tracked(transfer_target_lock_perm): Tracked<Option<&LockPerm>>, Tracked(window_perm): Tracked<Option<&LockPerm>>,
    ) -> (ret: Tracked<Map<L2Index, LockPerm>>)
        requires
            old(krnl).inv(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_inserted(&entry_lctx, old(lctx), KernelObjId::Page(page_ptr2page_index(pg_ptr)), TypedHeldLock {
                lock_id: old(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(pg_ptr)), mode: TypedLockMode::Write }),
            !entry_lctx.page_lock_map().dom().contains(page_ptr2page_index(pg_ptr)),
            page_ptr_valid(pg_ptr),
            old(krnl).thrd_mp.dom().contains(quota_thrd_ptr),
            old(krnl).thrd_mp.spec_index(quota_thrd_ptr).being_killed() == false,
            old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().temp_alloc_cache_4k.view().contains(pg_ptr),
            old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().quota_4k >= 1,
            mmap_4k_quota_thread_container_compatible(old(krnl), old(lctx), quota_thrd_ptr, ctn_ptr),
            old(krnl).prc_mp.dom().contains(prc_ptr),
            old(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container == ctn_ptr,
            old(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr,
            !(old(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is TablesEmptied) && !(old(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is Zombie),
            old(krnl).pt_mp.dom().contains(pagetable_ptr),
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= indices.0,
            pei_valid(indices.0) && pei_valid(indices.1) && pei_valid(indices.2),
            KERNEL_MEM_END_L4INDEX <= indices.0,
            pei_valid(lo) && pei_valid(hi) && lo <= hi,
            page_table_key_2m_valid::<PT_TYPE>(spec_index2va((indices.0, indices.1, indices.2, 0))),
            !(level is L2) ==> write_held,
            level is L2 ==> old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, WindowVa { va: spec_index2va((indices.0, indices.1, indices.2, 0usize)) })),
            level is L2 ==> window_perm is Some
                && whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.l2_owner(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2)
                    == (RwLockState::Write { thread_id: window_perm->Some_0.thread_id(), lock_id: window_perm->Some_0.lock_id() }),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            !old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().being_killed(),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: quota_thrd_ptr }),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == (match transfer_source { Some(source) => source, None => ctn_ptr }),
            typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write),
            page_lock_perm.state() is WriteLock,
            page_lock_perm.thread_id() == old(lctx).thread_id(),
            page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), quota_thrd_ptr, TypedLockMode::Write),
            quota_thread_lock_perm.state() is WriteLock,
            quota_thread_lock_perm.thread_id() == old(lctx).thread_id(),
            quota_thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(quota_thrd_ptr).locking_thread()->Write_lock_id,
            pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
            write_held ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            write_held ==> pagetable_lock_perm.state() is WriteLock,
            write_held ==> pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            !write_held ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
            !write_held ==> pagetable_lock_perm.state() is ReadLock,
            !write_held ==> old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
            transfer_source is Some ==> {
                let source = transfer_source->Some_0;
                &&& source != ctn_ptr
                &&& old(krnl).ctn_mp.dom().contains(source) && old(krnl).ctn_mp.dom().contains(ctn_ptr)
                &&& old(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata().view().parent == Some(source)
                &&& typed_lock_map_contains_mode(old(lctx).container_lock_map(), source, TypedLockMode::Write)
                &&& typed_lock_map_contains_mode(old(lctx).container_lock_map(), ctn_ptr, TypedLockMode::Write)
                &&& !old(krnl).ctn_mp.spec_index(source).being_killed() && !old(krnl).ctn_mp.spec_index(ctn_ptr).being_killed()
                &&& transfer_source_lock_perm is Some && transfer_source_lock_perm->Some_0.state() is WriteLock
                &&& transfer_source_lock_perm->Some_0.thread_id() == old(lctx).thread_id()
                &&& transfer_source_lock_perm->Some_0.lock_id() == old(krnl).ctn_mp.spec_index(source).locking_thread()->Write_lock_id
                &&& transfer_target_lock_perm is Some && transfer_target_lock_perm->Some_0.state() is WriteLock
                &&& transfer_target_lock_perm->Some_0.thread_id() == old(lctx).thread_id()
                &&& transfer_target_lock_perm->Some_0.lock_id() == old(krnl).ctn_mp.spec_index(ctn_ptr).locking_thread()->Write_lock_id
            },
            match level {
                MissingPageTableLevel::L4 => whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(indices.0) is None,
                MissingPageTableLevel::L3 => {
                    &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(indices.0) is Some
                    &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is None
                    &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_1g_l3(indices.0, indices.1) is None
                },
                MissingPageTableLevel::L2 => {
                    &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some
                    &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None
                    &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None
                },
            },
            level is L4 ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_held_l4(indices.0) is None,
            level is L3 ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_held_l3(indices.0, indices.1) is None,
            level is L2 ==> !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.l2_entry_hides_l1(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2),
            old(steps).snapshot_k() == *old(krnl),
            index_valid(NUM_CPUS, cpu_id),
            old(lctx).cpu_id() == cpu_id,
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
            old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()),
            old(krnl).thrd_mp.dom().contains(progress_thread),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), progress_thread, TypedLockMode::Write),
            progress_thread_lock_perm.state() is WriteLock,
            progress_thread_lock_perm.thread_id() == old(lctx).thread_id(),
            progress_thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(progress_thread).locking_thread()->Write_lock_id,
            held_locks_order_below(old(krnl), &entry_lctx, ALLOCATOR_CACHE_4K_MAJOR),
            entry_lctx.thread_id() == old(lctx).thread_id(),
            !thread_is_dangling(old(krnl).thrd_mp.spec_index(quota_thrd_ptr)),
            !old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view_ghost().exited,
            transfer_source is None ==> old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().owning_container == ctn_ptr,
            !write_held ==> transfer_source is None,
            ((old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().owning_proc == prc_ptr && old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr)
                || (typed_lock_map_contains_mode(old(lctx).process_lock_map(), prc_ptr, TypedLockMode::Write) && !old(krnl).prc_mp.spec_index(prc_ptr).view().zombie)),
            mmap_guard ==> {
                let progress = old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().syscall_progress.view();
                &&& transfer_source is None && progress_thread == quota_thrd_ptr
                &&& old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(quota_thrd_ptr)
                &&& old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr)
                &&& old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().owning_proc == prc_ptr
                &&& progress is Some && progress->Some_0 is Mmap4k && progress->Some_0->Mmap4k_mapped < progress->Some_0->Mmap4k_range.len
                &&& progress->Some_0->Mmap4k_phase is Fill ==> level is L4 || level is L3
                &&& !(progress->Some_0->Mmap4k_phase is Fill) ==> mmap_4k_directory_rank(progress->Some_0->Mmap4k_directory) < mmap_4k_directory_rank(mmap_4k_installed_directory(level))
                &&& level is L3 ==> forall|w: WindowVa| #![trigger va_range_2m_windows(progress->Some_0->Mmap4k_range).contains(w)]
                    w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1 ==> va_range_2m_windows(progress->Some_0->Mmap4k_range).contains(w) == (lo <= spec_v2l2index(w.va) <= hi)
            },
            share_guard ==> {
                let objects = share_4k_objects_k(*old(krnl), cpu_id);
                let progress = old(krnl).thrd_mp.spec_index(progress_thread).view().syscall_progress.view();
                &&& old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(progress_thread)
                &&& progress is Some && progress->Some_0 is Share4k && progress->Some_0->Share4k_shared < progress->Some_0->Share4k_source_range.len
                &&& old(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr == prc_ptr
                &&& level is L3 ==> forall|w: WindowVa| #![trigger va_range_2m_windows(progress->Some_0->Share4k_target_range).contains(w)]
                    w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1 ==> va_range_2m_windows(progress->Some_0->Share4k_target_range).contains(w) == (lo <= spec_v2l2index(w.va) <= hi)
                &&& progress->Some_0->Share4k_origin matches Share4kOrigin::IpcPages { peer }
                    ==> old(krnl).thrd_mp.spec_index(peer).view().state is IPC_TRANSIT && old(krnl).thrd_mp.spec_index(peer).view().state->IPC_TRANSIT_partner == progress_thread
                &&& objects.target == prc_ptr && objects.quota_thread == quota_thrd_ptr
                &&& objects.target_container == ctn_ptr && objects.transfer_source == transfer_source
                &&& typed_lock_map_contains_mode(old(lctx).thread_lock_map(), objects.source_thread, TypedLockMode::Write)
                &&& old(krnl).ctn_mp.dom().contains(ctn_ptr)
                &&& !old(krnl).prc_mp.spec_index(prc_ptr).view().zombie && old(krnl).prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr
                &&& progress_thread == quota_thrd_ptr || old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().syscall_progress.view() is None
            },
        ensures
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(steps).view() == old(steps).view().push(final(steps).view().last()),
            mmap_guard ==> mmap_4k_directory_step_pre(final(steps).view().last().old_u, cpu_id) && mmap_4k_directory_step(final(steps).view().last().old_u, final(steps).view().last().new_u, cpu_id),
            share_guard ==> {
                let progress = final(krnl).thrd_mp.spec_index(progress_thread).view().syscall_progress.view();
                &&& share_4k_directory_step_pre(final(steps).view().last().old_u, cpu_id)
                &&& share_4k_directory_step(final(steps).view().last().old_u, final(steps).view().last().new_u, cpu_id)
                &&& share_4k_objects_k(*final(krnl), cpu_id) == share_4k_objects_k(*old(krnl), cpu_id)
                &&& progress == share_4k_progress_after_directory(old(krnl).thrd_mp.spec_index(progress_thread).view().syscall_progress.view(), level)
                &&& progress_thread != quota_thrd_ptr ==> final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().syscall_progress.view() == old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().syscall_progress.view()
                &&& progress->Some_0->Share4k_origin matches Share4kOrigin::IpcPages { peer }
                    ==> final(krnl).thrd_mp.spec_index(peer).view().state is IPC_TRANSIT && final(krnl).thrd_mp.spec_index(peer).view().state->IPC_TRANSIT_partner == progress_thread
            },
            held_locks_order_below(final(krnl), final(lctx), ALLOCATOR_CACHE_4K_MAJOR),
            final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] == old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int],
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            final(krnl).ctn_mp.dom().contains(ctn_ptr),
            final(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata(),
            final(krnl).prc_mp.dom().contains(prc_ptr),
            final(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container == ctn_ptr,
            final(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr,
            !(final(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is TablesEmptied) && !(final(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is Zombie),
            final(krnl).thrd_mp.dom().contains(quota_thrd_ptr),
            final(krnl).thrd_mp.spec_index(quota_thrd_ptr).being_killed() == false,
            !thread_is_dangling(final(krnl).thrd_mp.spec_index(quota_thrd_ptr)),
            mmap_4k_quota_thread_container_compatible(final(krnl), final(lctx), quota_thrd_ptr, ctn_ptr),
            ((final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().owning_proc == prc_ptr && final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr)
                || (typed_lock_map_contains_mode(final(lctx).process_lock_map(), prc_ptr, TypedLockMode::Write) && !final(krnl).prc_mp.spec_index(prc_ptr).view().zombie)),
            quota_thread_lock_perm.lock_id() == final(krnl).thrd_mp.spec_index(quota_thrd_ptr).locking_thread()->Write_lock_id,
            final(krnl).pt_mp.dom().contains(pagetable_ptr),
            write_held ==> pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            !write_held ==> final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(final(lctx).thread_id(), pagetable_lock_perm.lock_id()),
            final(steps).snapshot_k() == *final(krnl),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(krnl)),
            nonwindow_typed_lock_maps_unchanged(&entry_lctx, final(lctx)),
            !(level is L3) ==> final(lctx).pagetable_window_lock_map() == entry_lctx.pagetable_window_lock_map(),
            !(level is L3) ==> ret.view() == Map::<L2Index, LockPerm>::empty(),
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (entry_lctx.pagetable_window_lock_map().dom().contains((p, w))
                    || (level is L3 && p == pagetable_ptr && w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1 && lo <= spec_v2l2index(w.va) <= hi)),
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().index((p, w))]
                entry_lctx.pagetable_window_lock_map().dom().contains((p, w))
                    && !(level is L3 && p == pagetable_ptr && w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1 && lo <= spec_v2l2index(w.va) <= hi)
                    ==> final(lctx).pagetable_window_lock_map().index((p, w)) == entry_lctx.pagetable_window_lock_map().index((p, w)),
            forall|w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().index((pagetable_ptr, w))]
                level is L3 && w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1 && lo <= spec_v2l2index(w.va) <= hi
                    ==> final(lctx).pagetable_window_lock_map().index((pagetable_ptr, w)) == (TypedHeldLock { lock_id: window_lock_id_of(pagetable_ptr, w), mode: TypedLockMode::Write }),
            forall|i: L2Index| #![trigger ret.view().dom().contains(i)] ret.view().dom().contains(i) == (level is L3 && lo <= i <= hi),
            forall|i: L2Index| #![trigger ret.view().index(i)] level is L3 && lo <= i <= hi ==> {
                &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_owner(whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(indices.0, indices.1), i)
                    == (RwLockState::Write { thread_id: ret.view().index(i).thread_id(), lock_id: ret.view().index(i).lock_id() })
                &&& ret.view().index(i).state() is WriteLock
                &&& ret.view().index(i).thread_id() == final(lctx).thread_id()
                &&& !whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_entry_hides_l1(whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(indices.0, indices.1), i)
            },
            held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, &entry_lctx),
            transfer_source is None ==> held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, &entry_lctx),
            transfer_source is Some ==> {
                let source = transfer_source->Some_0;
                let old_source_pages = old(krnl).ctn_mp.spec_index(source).view().owned_pages.view();
                let new_source_pages = final(krnl).ctn_mp.spec_index(source).view().owned_pages.view();
                &&& final(krnl).ctn_mp.dom().contains(source)
                &&& final(krnl).ctn_mp.spec_index(source).is_init() == old(krnl).ctn_mp.spec_index(source).is_init()
                &&& final(krnl).ctn_mp.spec_index(source).view_rodata() == old(krnl).ctn_mp.spec_index(source).view_rodata()
                &&& final(krnl).ctn_mp.spec_index(source).view_ghost() == old(krnl).ctn_mp.spec_index(source).view_ghost()
                &&& final(krnl).ctn_mp.spec_index(source).locking_thread() == old(krnl).ctn_mp.spec_index(source).locking_thread()
                &&& final(krnl).ctn_mp.spec_index(source).being_killed() == old(krnl).ctn_mp.spec_index(source).being_killed()
                &&& final(krnl).ctn_mp.spec_index(source).view() == (Container { owned_pages: final(krnl).ctn_mp.spec_index(source).view().owned_pages, ..old(krnl).ctn_mp.spec_index(source).view() })
                &&& final(krnl).ctn_mp.dom().contains(ctn_ptr)
                &&& final(krnl).ctn_mp.spec_index(ctn_ptr).is_init() == old(krnl).ctn_mp.spec_index(ctn_ptr).is_init()
                &&& final(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata()
                &&& final(krnl).ctn_mp.spec_index(ctn_ptr).view_ghost() == old(krnl).ctn_mp.spec_index(ctn_ptr).view_ghost()
                &&& final(krnl).ctn_mp.spec_index(ctn_ptr).locking_thread() == old(krnl).ctn_mp.spec_index(ctn_ptr).locking_thread()
                &&& final(krnl).ctn_mp.spec_index(ctn_ptr).being_killed() == old(krnl).ctn_mp.spec_index(ctn_ptr).being_killed()
                &&& final(krnl).ctn_mp.spec_index(ctn_ptr).view() == (Container { owned_pages: final(krnl).ctn_mp.spec_index(ctn_ptr).view().owned_pages, ..old(krnl).ctn_mp.spec_index(ctn_ptr).view() })
                &&& new_source_pages.subset_of(old_source_pages)
                &&& final(krnl).ctn_mp.spec_index(ctn_ptr).view().owned_pages.view() =~= old(krnl).ctn_mp.spec_index(ctn_ptr).view().owned_pages.view().union(old_source_pages.difference(new_source_pages))
            },
            held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, &entry_lctx),
            held_threads_unchanged_except(old(krnl).thrd_mp, final(krnl).thrd_mp, &entry_lctx, set![quota_thrd_ptr, progress_thread]),
            held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, &entry_lctx),
            held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, &entry_lctx),
            held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, &entry_lctx),
            held_cpu_sets_unchanged(old(krnl).cpu_set_mp, final(krnl).cpu_set_mp, &entry_lctx),
            held_pagetables_unchanged_except(old(krnl).pt_mp, final(krnl).pt_mp, &entry_lctx, set![pagetable_ptr]),
            held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, &entry_lctx),
            forall|c: CpuId| #![trigger entry_lctx.cpu_lock_map().dom().contains(c)] entry_lctx.cpu_lock_map().dom().contains(c) ==> final(krnl).cpu_arr.spec_index(c).view() == old(krnl).cpu_arr.spec_index(c).view(),
            final(krnl).thrd_mp.spec_index(quota_thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(quota_thrd_ptr).being_killed(),
            final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view() == (Thread {
                quota_4k: final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().quota_4k, temp_alloc_cache_4k: final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().temp_alloc_cache_4k,
                syscall_progress: final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().syscall_progress, ..old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view()
            }),
            final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().temp_alloc_cache_4k.view().remove(pg_ptr),
            final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().quota_4k == old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().quota_4k - 1,
            final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().syscall_progress.view() == if progress_thread == quota_thrd_ptr {
                share_4k_progress_after_directory(mmap_4k_progress_after_directory(old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().syscall_progress.view(), level), level)
            } else { mmap_4k_progress_after_directory(old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().syscall_progress.view(), level) },
            final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view_ghost(),
            final(krnl).thrd_mp.spec_index(progress_thread).view_ghost() == old(krnl).thrd_mp.spec_index(progress_thread).view_ghost(),
            final(krnl).thrd_mp.dom().contains(progress_thread),
            progress_thread_lock_perm.lock_id() == final(krnl).thrd_mp.spec_index(progress_thread).locking_thread()->Write_lock_id,
            progress_thread != quota_thrd_ptr ==> final(krnl).thrd_mp.spec_index(progress_thread).view() == (Thread {
                syscall_progress: Ghost(share_4k_progress_after_directory(old(krnl).thrd_mp.spec_index(progress_thread).view().syscall_progress.view(), level)), ..old(krnl).thrd_mp.spec_index(progress_thread).view()
            }),
            final(krnl).thrd_mp.spec_index(progress_thread).being_killed() == old(krnl).thrd_mp.spec_index(progress_thread).being_killed(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).inv(),
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).wf(),
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr == old(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr,
            write_held ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).user_view(LockStateU::Unlocked)
                == (PageTableU { pagetable_window_locks: whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks, ..whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).user_view(LockStateU::Unlocked) }),
            write_held ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k(),
            write_held ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_2m() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m(),
            write_held ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_1g() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g(),
            write_held ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.window_stale_cpus == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.window_stale_cpus,
            !write_held ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).higher == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).higher,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().table_stale_cpus == old(krnl).pt_mp.spec_index(pagetable_ptr).view().table_stale_cpus,
            forall|l4i: L4Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_l4(l4i)]
                #![trigger final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_held_l4(l4i)]
                whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && !(level is L4 && l4i == indices.0) ==> {
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_l4(l4i) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_held_l4(l4i)
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(l4i) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(l4i)
                },
            write_held && whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows()
                ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows(),
            forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_page(p).entry_lock(i).l1()]
                write_held && pei_valid(i) && (!whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.l2_entry_hides_l1(p, i)
                    || (whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_perms.dom().contains(p) && !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.l2_perms.dom().contains(p)))
                    ==> !whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_entry_hides_l1(p, i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_page(whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i)).entry_lock(l2i).l1()]
                write_held && whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                    && !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.l2_entry_hides_l1(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i), l2i)
                    ==> !whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_entry_hides_l1(whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i), l2i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i)]
                whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && !(level is L3 && l4i == indices.0 && l3i == indices.1)
                    ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i)]
                write_held && whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                    && whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                    ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_owner(whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i), l2i)]
                write_held && whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_exists(l4i, l3i)
                    ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_owner(whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i), l2i)
                        == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.l2_owner(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i), l2i),
            forall|w: WindowVa| #![trigger entry_lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, w))]
                !write_held && entry_lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) ==> {
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_view(w).l2_page == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_view(w).l2_page
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_view(w).lock_state == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_view(w).lock_state
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_view(w).stale_cpus == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_view(w).stale_cpus
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_2m().dom().contains(w.va) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m().dom().contains(w.va)
                    &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m().dom().contains(w.va)
                        ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_2m().spec_index(w.va) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m().spec_index(w.va)
                    &&& !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.l2_entry_hides_l1(
                        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
                        ==> !whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_entry_hides_l1(
                            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
                },
            forall|w: WindowVa, v: VAddr|
                #![trigger entry_lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(v)]
                #![trigger entry_lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(v)]
                !write_held && entry_lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va)
                    && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(v) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(v)
                    &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(v)
                        ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(v) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(v)
                },
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger entry_lctx.pagetable_window_lock_map().dom().contains((p, w))]
                entry_lctx.pagetable_window_lock_map().dom().contains((p, w)) ==> final(lctx).pagetable_window_lock_map().dom().contains((p, w)),
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger entry_lctx.pagetable_window_lock_map().dom().contains((p, w))]
                entry_lctx.pagetable_window_lock_map().dom().contains((p, w)) && final(lctx).pagetable_window_lock_map().dom().contains((p, w)) && entry_lctx.pagetable_lock_map().dom().contains(p) && p != pagetable_ptr ==> {
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), p).window_view(w) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), p).window_view(w)
                    &&& forall|v: VAddr|
                        #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), p).mapping_4k().dom().contains(v)]
                        #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), p).mapping_4k().dom().contains(v)]
                        spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
                            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), p).mapping_4k().dom().contains(v) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), p).mapping_4k().dom().contains(v)
                            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), p).mapping_4k().dom().contains(v)
                                ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), p).mapping_4k().spec_index(v) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), p).mapping_4k().spec_index(v)
                        }
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), p).mapping_2m().dom().contains(w.va) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), p).mapping_2m().dom().contains(w.va)
                    &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), p).mapping_2m().dom().contains(w.va)
                        ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), p).mapping_2m().spec_index(w.va) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), p).mapping_2m().spec_index(w.va)
                },
            match level {
                MissingPageTableLevel::L4 => {
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(indices.0) is Some
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is None
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_1g_l3(indices.0, indices.1) is None
                },
                MissingPageTableLevel::L3 => {
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None
                },
                MissingPageTableLevel::L2 => whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
            },
            level is L3 ==> !whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_entry_hides_l1(whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2),
            (forall|l4i: L4Index, l3i: L3Index| #![trigger old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_held_l3(l4i, l3i)]
                old(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_held_l3(l4i, l3i) is Some
                    ==> old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l3(l4i, l3i) is Some)
                ==> forall|l4i: L4Index, l3i: L3Index| #![trigger final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_held_l3(l4i, l3i)]
                    final(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_held_l3(l4i, l3i) is Some
                        ==> final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l3(l4i, l3i) is Some,
    {
        let ghost share_lctx = *lctx;
        let ghost window_va = WindowVa { va: spec_index2va((indices.0, indices.1, indices.2, 0usize)) };
        proof { krnl.thrd_mp.typed_lock_map_aligned_held_in_dom(lctx.thread_lock_map(), lctx.thread_id()); krnl.pt_mp.typed_lock_map_aligned_held_in_dom(lctx.pagetable_lock_map(), lctx.thread_id()); }
        let windows = install_one_mmap_4k_directory_page_link(krnl, Tracked(&mut *lctx), level, pg_ptr, quota_thrd_ptr, prc_ptr, ctn_ptr, pagetable_ptr, indices, lo, hi,
            write_held, transfer_source, Ghost(entry_lctx), Tracked(page_lock_perm), Tracked(quota_thread_lock_perm), Tracked(pagetable_lock_perm), Tracked(transfer_source_lock_perm),
            Tracked(transfer_target_lock_perm), Tracked(window_perm));
        let ghost directory_lctx = *lctx;
        proof {
            if level is L3 {
                spec_va_4k_index_roundtrip_at(spec_index2va((indices.0, indices.1, 0usize, 0usize)), indices.0, indices.1, 0usize, 0usize);
                if whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks.dom().contains(WindowVa { va: spec_index2va((indices.0, indices.1, 0usize, 0usize)) }) {
                    pagetable_lower_wf_at(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr);
                    whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).wf_window_locks_va_at(WindowVa { va: spec_index2va((indices.0, indices.1, 0usize, 0usize)) });
                }
            }
        }
        install_one_mmap_4k_directory_page_end_step(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), level, cpu_id, quota_thrd_ptr, prc_ptr, ctn_ptr, pagetable_ptr, write_held,
            transfer_source, pg_ptr, indices, lo, hi, progress_thread, Ghost(share_lctx), Ghost(mmap_guard), Ghost(share_guard), Tracked(progress_thread_lock_perm));
        proof {
            assert(krnl.ctn_mp.dom().contains(ctn_ptr)) by { if transfer_source is None { container_thread_wf_thread_at(krnl.ctn_mp, krnl.thrd_mp, quota_thrd_ptr); } };
            assert(krnl.prc_mp.dom().contains(prc_ptr) && ((krnl.thrd_mp.spec_index(quota_thrd_ptr).view().owning_proc == prc_ptr && krnl.thrd_mp.spec_index(quota_thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr)
                || (typed_lock_map_contains_mode(lctx.process_lock_map(), prc_ptr, TypedLockMode::Write) && !krnl.prc_mp.spec_index(prc_ptr).view().zombie))) by { process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, quota_thrd_ptr); };
            assert(!(krnl.prc_mp.spec_index(prc_ptr).view().state.view() is TablesEmptied) && !(krnl.prc_mp.spec_index(prc_ptr).view().state.view() is Zombie)) by {
                if !typed_lock_map_contains_mode(old(lctx).process_lock_map(), prc_ptr, TypedLockMode::Write) {
                    process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, quota_thrd_ptr); process_perms_wf_at(krnl.prc_mp, prc_ptr); process_emptied_threads_wf_at(krnl.prc_mp, krnl.thrd_mp, prc_ptr, quota_thrd_ptr);
                }
            };
            if !write_held {
                spec_va_4k_index_roundtrip_at(window_va.va, indices.0, indices.1, indices.2, 0usize);
                assert(directory_lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, window_va)));
                assert(directory_lctx.pagetable_lock_map().dom().contains(pagetable_ptr));
            }
            assert(krnl.pt_mp.spec_index(pagetable_ptr).inv() && whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).wf()) by {
                pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
            };
        }
        windows
    }

    /// Move the staged page to `ctn_ptr`, publish it as the missing directory page, and release its page lock, ending the
    /// krnl section's mutations in Release.
    pub(super) fn install_one_mmap_4k_directory_page_link(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, level: MissingPageTableLevel, pg_ptr: PagePtr, quota_thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr,
        ctn_ptr: RwLockContainerPtr, pagetable_ptr: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index), lo: L2Index, hi: L2Index, write_held: bool,
        transfer_source: Option<RwLockContainerPtr>, Ghost(entry_lctx): Ghost<LocalContext>, Tracked(page_lock_perm): Tracked<LockPerm>, Tracked(quota_thread_lock_perm): Tracked<&LockPerm>,
        Tracked(pagetable_lock_perm): Tracked<&LockPerm>, Tracked(transfer_source_lock_perm): Tracked<Option<&LockPerm>>, Tracked(transfer_target_lock_perm): Tracked<Option<&LockPerm>>,
        Tracked(window_perm): Tracked<Option<&LockPerm>>,
    ) -> (ret: Tracked<Map<L2Index, LockPerm>>)
        requires
            old(krnl).inv(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_inserted(&entry_lctx, old(lctx), KernelObjId::Page(page_ptr2page_index(pg_ptr)), TypedHeldLock {
                lock_id: old(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(pg_ptr)), mode: TypedLockMode::Write }),
            !entry_lctx.page_lock_map().dom().contains(page_ptr2page_index(pg_ptr)),
            page_ptr_valid(pg_ptr),
            old(krnl).thrd_mp.dom().contains(quota_thrd_ptr),
            old(krnl).thrd_mp.spec_index(quota_thrd_ptr).being_killed() == false,
            old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().temp_alloc_cache_4k.view().contains(pg_ptr),
            old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().quota_4k >= 1,
            mmap_4k_quota_thread_container_compatible(old(krnl), old(lctx), quota_thrd_ptr, ctn_ptr),
            old(krnl).prc_mp.dom().contains(prc_ptr),
            old(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container == ctn_ptr,
            old(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr,
            !(old(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is TablesEmptied) && !(old(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is Zombie),
            old(krnl).pt_mp.dom().contains(pagetable_ptr),
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= indices.0,
            pei_valid(indices.0) && pei_valid(indices.1) && pei_valid(indices.2),
            KERNEL_MEM_END_L4INDEX <= indices.0,
            pei_valid(lo) && pei_valid(hi) && lo <= hi,
            page_table_key_2m_valid::<PT_TYPE>(spec_index2va((indices.0, indices.1, indices.2, 0))),
            !(level is L2) ==> write_held,
            level is L2 ==> old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, WindowVa { va: spec_index2va((indices.0, indices.1, indices.2, 0usize)) })),
            level is L2 ==> window_perm is Some
                && whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.l2_owner(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2)
                    == (RwLockState::Write { thread_id: window_perm->Some_0.thread_id(), lock_id: window_perm->Some_0.lock_id() }),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            !old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().being_killed(),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: quota_thrd_ptr }),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == (match transfer_source { Some(source) => source, None => ctn_ptr }),
            typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write),
            page_lock_perm.state() is WriteLock,
            page_lock_perm.thread_id() == old(lctx).thread_id(),
            page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), quota_thrd_ptr, TypedLockMode::Write),
            quota_thread_lock_perm.state() is WriteLock,
            quota_thread_lock_perm.thread_id() == old(lctx).thread_id(),
            quota_thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(quota_thrd_ptr).locking_thread()->Write_lock_id,
            pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
            write_held ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            write_held ==> pagetable_lock_perm.state() is WriteLock,
            write_held ==> pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            !write_held ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
            !write_held ==> pagetable_lock_perm.state() is ReadLock,
            !write_held ==> old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
            transfer_source is Some ==> {
                let source = transfer_source->Some_0;
                &&& source != ctn_ptr
                &&& old(krnl).ctn_mp.dom().contains(source) && old(krnl).ctn_mp.dom().contains(ctn_ptr)
                &&& old(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata().view().parent == Some(source)
                &&& typed_lock_map_contains_mode(old(lctx).container_lock_map(), source, TypedLockMode::Write)
                &&& typed_lock_map_contains_mode(old(lctx).container_lock_map(), ctn_ptr, TypedLockMode::Write)
                &&& !old(krnl).ctn_mp.spec_index(source).being_killed() && !old(krnl).ctn_mp.spec_index(ctn_ptr).being_killed()
                &&& transfer_source_lock_perm is Some && transfer_source_lock_perm->Some_0.state() is WriteLock
                &&& transfer_source_lock_perm->Some_0.thread_id() == old(lctx).thread_id()
                &&& transfer_source_lock_perm->Some_0.lock_id() == old(krnl).ctn_mp.spec_index(source).locking_thread()->Write_lock_id
                &&& transfer_target_lock_perm is Some && transfer_target_lock_perm->Some_0.state() is WriteLock
                &&& transfer_target_lock_perm->Some_0.thread_id() == old(lctx).thread_id()
                &&& transfer_target_lock_perm->Some_0.lock_id() == old(krnl).ctn_mp.spec_index(ctn_ptr).locking_thread()->Write_lock_id
            },
            match level {
                MissingPageTableLevel::L4 => whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(indices.0) is None,
                MissingPageTableLevel::L3 => {
                    &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(indices.0) is Some
                    &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is None
                    &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_1g_l3(indices.0, indices.1) is None
                },
                MissingPageTableLevel::L2 => {
                    &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some
                    &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None
                    &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None
                },
            },
            level is L4 ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_held_l4(indices.0) is None,
            level is L3 ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_held_l3(indices.0, indices.1) is None,
            level is L2 ==> !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.l2_entry_hides_l1(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            final(krnl).inv(),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            nonwindow_typed_lock_maps_unchanged(&entry_lctx, final(lctx)),
            !(level is L3) ==> final(lctx).pagetable_window_lock_map() == entry_lctx.pagetable_window_lock_map(),
            !(level is L3) ==> ret.view() == Map::<L2Index, LockPerm>::empty(),
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (entry_lctx.pagetable_window_lock_map().dom().contains((p, w))
                    || (level is L3 && p == pagetable_ptr && w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1 && lo <= spec_v2l2index(w.va) <= hi)),
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().index((p, w))]
                entry_lctx.pagetable_window_lock_map().dom().contains((p, w))
                    && !(level is L3 && p == pagetable_ptr && w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1 && lo <= spec_v2l2index(w.va) <= hi)
                    ==> final(lctx).pagetable_window_lock_map().index((p, w)) == entry_lctx.pagetable_window_lock_map().index((p, w)),
            forall|w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().index((pagetable_ptr, w))]
                level is L3 && w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1 && lo <= spec_v2l2index(w.va) <= hi
                    ==> final(lctx).pagetable_window_lock_map().index((pagetable_ptr, w)) == (TypedHeldLock { lock_id: window_lock_id_of(pagetable_ptr, w), mode: TypedLockMode::Write }),
            forall|i: L2Index| #![trigger ret.view().dom().contains(i)] ret.view().dom().contains(i) == (level is L3 && lo <= i <= hi),
            forall|i: L2Index| #![trigger ret.view().index(i)] level is L3 && lo <= i <= hi ==> {
                &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_owner(whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(indices.0, indices.1), i)
                    == (RwLockState::Write { thread_id: ret.view().index(i).thread_id(), lock_id: ret.view().index(i).lock_id() })
                &&& ret.view().index(i).state() is WriteLock
                &&& ret.view().index(i).thread_id() == final(lctx).thread_id()
                &&& !whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_entry_hides_l1(whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(indices.0, indices.1), i)
            },
            quota_thread_lock_perm.lock_id() == final(krnl).thrd_mp.spec_index(quota_thrd_ptr).locking_thread()->Write_lock_id,
            final(krnl).thrd_mp.spec_index(quota_thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(quota_thrd_ptr).being_killed(),
            kernel_thread_quota_4k_changed(old(krnl), final(krnl), quota_thrd_ptr, -1),
            final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view() == (Thread {
                quota_4k: final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().quota_4k, temp_alloc_cache_4k: final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().temp_alloc_cache_4k,
                syscall_progress: final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().syscall_progress, ..old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view()
            }),
            final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().syscall_progress.view() == mmap_4k_progress_after_directory(old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().syscall_progress.view(), level),
            final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view_ghost(),
            final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().temp_alloc_cache_4k.view().remove(pg_ptr),
            final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().quota_4k == old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().quota_4k - 1,
            final(krnl).thrd_mp.unchanged_except(&old(krnl).thrd_mp, quota_thrd_ptr),
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr == old(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr,
            final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, pagetable_ptr),
            final(krnl).pt_lower.view() == old(krnl).pt_lower.view().insert(pagetable_ptr, final(krnl).pt_lower.view().spec_index(pagetable_ptr)),
            final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread() == old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread(),
            final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(pg_ptr)),
            *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, pg_arr: final(krnl).pg_arr, thrd_mp: final(krnl).thrd_mp, ctn_mp: final(krnl).ctn_mp, ..*old(krnl) }),
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k(),
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_2m() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m(),
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_1g() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g(),
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.window_stale_cpus == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.window_stale_cpus,
            level is L2 ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).higher == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).higher,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().table_stale_cpus == old(krnl).pt_mp.spec_index(pagetable_ptr).view().table_stale_cpus,
            forall|l4i: L4Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_l4(l4i)]
                #![trigger final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_held_l4(l4i)]
                whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && !(level is L4 && l4i == indices.0) ==> {
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_l4(l4i) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_held_l4(l4i)
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(l4i) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(l4i)
                },
            write_held && whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows()
                ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.hidden_l1_tables_in_locked_windows(),
            forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_page(p).entry_lock(i).l1()]
                write_held && pei_valid(i) && (!whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.l2_entry_hides_l1(p, i)
                    || (whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_perms.dom().contains(p) && !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.l2_perms.dom().contains(p)))
                    ==> !whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_entry_hides_l1(p, i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_page(whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i)).entry_lock(l2i).l1()]
                write_held && whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                    && !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.l2_entry_hides_l1(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i), l2i)
                    ==> !whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_entry_hides_l1(whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i), l2i),
            forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_page(p).entry_lock(i).l1()]
                !write_held && !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.l2_entry_hides_l1(p, i)
                    ==> !whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_entry_hides_l1(p, i),
            !(level is L3) ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks,
            !(level is L3) ==> forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_owner(p, i)]
                whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_owner(p, i) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.l2_owner(p, i),
            level is L3 ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks == Map::new(
                whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks.dom() + Set::<usize>::range(0, 512).map_by(|i: usize| WindowVa { va: spec_index2va((indices.0, indices.1, i, 0usize)) }, |w: WindowVa| spec_v2l2index(w.va)),
                |w: WindowVa| if whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks.dom().contains(w) {
                    whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks[w]
                } else if lo <= spec_v2l2index(w.va) <= hi { LockStateU::WriteLocked { writer: final(lctx).thread_id() } } else { LockStateU::Unlocked }),
            forall|l4i: L4Index, l3i: L3Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i)]
                whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && !(level is L3 && l4i == indices.0 && l3i == indices.1)
                    ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i)]
                whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i)
                    && pei_valid(l2i) && whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                    ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_owner(whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i), l2i)]
                whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_exists(l4i, l3i)
                    ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_owner(whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i), l2i)
                        == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.l2_owner(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i), l2i),
            match level {
                MissingPageTableLevel::L4 => {
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(indices.0) is Some
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is None
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_1g_l3(indices.0, indices.1) is None
                },
                MissingPageTableLevel::L3 => {
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None
                },
                MissingPageTableLevel::L2 => whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
            },
            level is L3 ==> !whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_entry_hides_l1(whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(indices.0, indices.1), indices.2),
            (forall|l4i: L4Index, l3i: L3Index| #![trigger old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_held_l3(l4i, l3i)]
                old(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_held_l3(l4i, l3i) is Some
                    ==> old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l3(l4i, l3i) is Some)
                ==> forall|l4i: L4Index, l3i: L3Index| #![trigger final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_held_l3(l4i, l3i)]
                    final(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_held_l3(l4i, l3i) is Some
                        ==> final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l3(l4i, l3i) is Some,
            transfer_source is None ==> final(krnl).ctn_mp == old(krnl).ctn_mp,
            transfer_source matches Some(source) ==> {
                &&& old(krnl).ctn_mp.spec_index(source).view().owned_pages.view().contains(pg_ptr)
                &&& final(krnl).ctn_mp.dom() == old(krnl).ctn_mp.dom()
                &&& final(krnl).ctn_mp.spec_index(source).is_init() == old(krnl).ctn_mp.spec_index(source).is_init()
                &&& final(krnl).ctn_mp.spec_index(ctn_ptr).is_init() == old(krnl).ctn_mp.spec_index(ctn_ptr).is_init()
                &&& final(krnl).ctn_mp.spec_index(source).view().owned_pages.view().subset_of(old(krnl).ctn_mp.spec_index(source).view().owned_pages.view())
                &&& final(krnl).ctn_mp.spec_index(ctn_ptr).view().owned_pages.view() =~= old(krnl).ctn_mp.spec_index(ctn_ptr).view().owned_pages.view()
                    .union(old(krnl).ctn_mp.spec_index(source).view().owned_pages.view().difference(final(krnl).ctn_mp.spec_index(source).view().owned_pages.view()))
                &&& forall|c: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(c)] old(krnl).ctn_mp.dom().contains(c) ==> {
                    &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
                    &&& final(krnl).ctn_mp.spec_index(c).view_ghost() == old(krnl).ctn_mp.spec_index(c).view_ghost()
                    &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
                    &&& final(krnl).ctn_mp.spec_index(c).lock_process_owner_u() == old(krnl).ctn_mp.spec_index(c).lock_process_owner_u()
                    &&& final(krnl).ctn_mp.spec_index(c).being_killed() == old(krnl).ctn_mp.spec_index(c).being_killed()
                    &&& final(krnl).ctn_mp.spec_index(c).view() == (Container { owned_pages: final(krnl).ctn_mp.spec_index(c).view().owned_pages, ..old(krnl).ctn_mp.spec_index(c).view() })
                    &&& final(krnl).ctn_mp.spec_index(c).view().owned_pages.view() == if c == source { old(krnl).ctn_mp.spec_index(c).view().owned_pages.view().remove(pg_ptr) }
                        else if c == ctn_ptr { old(krnl).ctn_mp.spec_index(c).view().owned_pages.view().insert(pg_ptr) } else { old(krnl).ctn_mp.spec_index(c).view().owned_pages.view() }
                }
            },
    {
        install_one_mmap_4k_directory_page_transfer_if_source(krnl, Tracked(&mut *lctx), pg_ptr, quota_thrd_ptr, ctn_ptr, transfer_source, Tracked(&page_lock_perm),
            Tracked(transfer_source_lock_perm), Tracked(transfer_target_lock_perm));
        let ghost staged_page_lock_id = krnl.pg_arr.lock_id_by_index(page_ptr2page_index(pg_ptr));
        let windows = install_staged_4k_page_table_page(krnl, level, pg_ptr, quota_thrd_ptr, prc_ptr, ctn_ptr, pagetable_ptr, indices, lo, hi, write_held, Tracked(&mut *lctx),
            Tracked(&page_lock_perm), Tracked(quota_thread_lock_perm), Tracked(pagetable_lock_perm), Tracked(window_perm));
        let ghost installed_page_lock_id = krnl.pg_arr.lock_id_by_index(page_ptr2page_index(pg_ptr));
        krnl.wunlock_page(page_ptr2page_index(pg_ptr), Tracked(&mut *lctx), Tracked(page_lock_perm));
        proof {
            assert(nonwindow_typed_lock_maps_unchanged(&entry_lctx, lctx)) by {
                map_insert_overwrite_lemma(entry_lctx.page_lock_map(), page_ptr2page_index(pg_ptr), TypedHeldLock { lock_id: staged_page_lock_id, mode: TypedLockMode::Write },
                    TypedHeldLock { lock_id: installed_page_lock_id, mode: TypedLockMode::Write });
                map_insert_remove_absent_lemma(entry_lctx.page_lock_map(), page_ptr2page_index(pg_ptr), TypedHeldLock { lock_id: installed_page_lock_id, mode: TypedLockMode::Write });
            };
            assert(kernel_thread_quota_4k_changed(old(krnl), krnl, quota_thrd_ptr, -1)) by { reveal(kernel_thread_quota_4k_changed); };
        }
        windows
    }

    /// Record the installed level in `progress_thread`'s progress, then end the krnl section of one directory install at the
    /// step boundary and derive the running syscall's directory step from the section's start snapshot.
    fn install_one_mmap_4k_directory_page_end_step(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, level: MissingPageTableLevel, cpu_id: CpuId,
        quota_thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr, pagetable_ptr: RwLockPageTableRoot, write_held: bool,
        transfer_source: Option<RwLockContainerPtr>, pg_ptr: PagePtr, indices: (L4Index, L3Index, L2Index), lo: L2Index, hi: L2Index, progress_thread: RwLockThreadPtr,
        Ghost(share_lctx): Ghost<LocalContext>, Ghost(mmap_guard): Ghost<bool>, Ghost(share_guard): Ghost<bool>, Tracked(progress_thread_lock_perm): Tracked<&LockPerm>,
    )
        requires
            old(krnl).inv(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(krnl).thrd_mp.dom().contains(progress_thread),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), progress_thread, TypedLockMode::Write),
            progress_thread_lock_perm.state() is WriteLock,
            progress_thread_lock_perm.thread_id() == old(lctx).thread_id(),
            progress_thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(progress_thread).locking_thread()->Write_lock_id,
            KERNEL_MEM_END_L4INDEX <= indices.0 && pei_valid(indices.0) && pei_valid(indices.1),
            level is L3 ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks == Map::new(
                whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks.dom()
                    + Set::<usize>::range(0, 512).map_by(|i: usize| WindowVa { va: spec_index2va((indices.0, indices.1, i, 0usize)) }, |w: WindowVa| spec_v2l2index(w.va)),
                |w: WindowVa| if whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks.dom().contains(w) {
                    whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks[w]
                } else if lo <= spec_v2l2index(w.va) <= hi { LockStateU::WriteLocked { writer: cpu_id } } else { LockStateU::Unlocked }),
            level is L3 ==> !whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks.dom().contains(WindowVa { va: spec_index2va((indices.0, indices.1, 0usize, 0usize)) }),
            !(level is L3) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks,
            old(lctx).kernel_view_locking_state() is Release,
            kernel_thread_quota_4k_changed(&old(steps).snapshot_k(), old(krnl), quota_thrd_ptr, -1),
            index_valid(NUM_CPUS, cpu_id),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
            old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()),
            write_held ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            mmap_guard || share_guard ==> {
                let pre = old(steps).snapshot_k();
                &&& pre.inv()
                &&& pre.thrd_mp.typed_lock_map_aligned(old(lctx).thread_lock_map(), old(lctx).thread_id())
                &&& pre.pt_mp.typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id())
                &&& old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread() == pre.pt_mp.spec_index(pagetable_ptr).locking_thread()
                &&& typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write)
                &&& typed_lock_map_contains_mode(old(lctx).thread_lock_map(), quota_thrd_ptr, TypedLockMode::Write)
                &&& !write_held ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read)
                &&& transfer_source is None ==> {
                    &&& *old(krnl) == (KernelK { pt_mp: old(krnl).pt_mp, pt_lower: old(krnl).pt_lower, pg_arr: old(krnl).pg_arr, thrd_mp: old(krnl).thrd_mp, ..pre })
                    &&& old(krnl).thrd_mp.unchanged_except(&pre.thrd_mp, quota_thrd_ptr)
                    &&& old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view() == (Thread {
                        quota_4k: old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().quota_4k, temp_alloc_cache_4k: old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().temp_alloc_cache_4k,
                        syscall_progress: old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().syscall_progress, ..pre.thrd_mp.spec_index(quota_thrd_ptr).view()
                    })
                    &&& old(krnl).thrd_mp.spec_index(quota_thrd_ptr).being_killed() == pre.thrd_mp.spec_index(quota_thrd_ptr).being_killed()
                    &&& pre.prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr
                    &&& old(krnl).pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr)
                    &&& old(krnl).pt_lower.view() == pre.pt_lower.view().insert(pagetable_ptr, old(krnl).pt_lower.view().spec_index(pagetable_ptr))
                    &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k()
                    &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m()
                    &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_1g()
                }
            },
            mmap_guard ==> {
                let pre = old(steps).snapshot_k();
                let progress = pre.thrd_mp.spec_index(quota_thrd_ptr).view().syscall_progress.view();
                &&& transfer_source is None
                &&& pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(quota_thrd_ptr)
                &&& pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr)
                &&& pre.prc_mp.dom().contains(prc_ptr) && pre.thrd_mp.spec_index(quota_thrd_ptr).view().owning_proc == prc_ptr
                &&& progress is Some && progress->Some_0 is Mmap4k && progress->Some_0->Mmap4k_mapped < progress->Some_0->Mmap4k_range.len
                &&& progress->Some_0->Mmap4k_phase is Fill ==> level is L4 || level is L3
                &&& !(progress->Some_0->Mmap4k_phase is Fill) ==> mmap_4k_directory_rank(progress->Some_0->Mmap4k_directory) < mmap_4k_directory_rank(mmap_4k_installed_directory(level))
                &&& old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().syscall_progress.view() == mmap_4k_progress_after_directory(progress, level)
                &&& progress_thread == quota_thrd_ptr
                &&& level is L3 ==> forall|w: WindowVa| #![trigger va_range_2m_windows(progress->Some_0->Mmap4k_range).contains(w)]
                    w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1 ==> va_range_2m_windows(progress->Some_0->Mmap4k_range).contains(w) == (lo <= spec_v2l2index(w.va) <= hi)
            },
            share_guard ==> {
                let pre = old(steps).snapshot_k();
                let objects = share_4k_objects_k(pre, cpu_id);
                let progress = pre.thrd_mp.spec_index(progress_thread).view().syscall_progress.view();
                &&& typed_lock_maps_aligned(&pre, &share_lctx)
                &&& typed_lock_map_contains_mode(share_lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write)
                &&& pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(progress_thread)
                &&& pre.prc_mp.dom().contains(prc_ptr) && pre.thrd_mp.dom().contains(progress_thread)
                &&& typed_lock_map_contains_mode(share_lctx.thread_lock_map(), progress_thread, TypedLockMode::Write)
                &&& progress is Some && progress->Some_0 is Share4k && progress->Some_0->Share4k_shared < progress->Some_0->Share4k_source_range.len
                &&& pre.pt_mp.spec_index(pagetable_ptr).view().proc_ptr == prc_ptr
                &&& old(krnl).thrd_mp.spec_index(progress_thread).view().syscall_progress.view() == progress
                &&& level is L3 ==> forall|w: WindowVa| #![trigger va_range_2m_windows(progress->Some_0->Share4k_target_range).contains(w)]
                    w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1 ==> va_range_2m_windows(progress->Some_0->Share4k_target_range).contains(w) == (lo <= spec_v2l2index(w.va) <= hi)
                &&& progress->Some_0->Share4k_origin matches Share4kOrigin::IpcPages { peer }
                    ==> pre.thrd_mp.spec_index(peer).view().state is IPC_TRANSIT && pre.thrd_mp.spec_index(peer).view().state->IPC_TRANSIT_partner == progress_thread
                &&& objects.target == prc_ptr && objects.quota_thread == quota_thrd_ptr
                &&& objects.target_container == ctn_ptr && objects.transfer_source == transfer_source
                &&& pre.thrd_mp.dom().contains(objects.source_thread)
                &&& typed_lock_map_contains_mode(share_lctx.thread_lock_map(), objects.source_thread, TypedLockMode::Write)
                &&& typed_lock_map_contains_mode(old(lctx).thread_lock_map(), objects.source_thread, TypedLockMode::Write)
                &&& pre.thrd_mp.dom().contains(quota_thrd_ptr)
                &&& typed_lock_map_contains_mode(share_lctx.thread_lock_map(), quota_thrd_ptr, TypedLockMode::Write)
                &&& pre.ctn_mp.dom().contains(ctn_ptr)
                &&& pre.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container == ctn_ptr
                &&& !pre.prc_mp.spec_index(prc_ptr).view().zombie && pre.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable_ptr
                &&& typed_lock_map_contains_mode(share_lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read)
                    || typed_lock_map_contains_mode(share_lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write)
                &&& old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().syscall_progress == pre.thrd_mp.spec_index(quota_thrd_ptr).view().syscall_progress
                &&& transfer_source matches Some(source) ==> {
                    &&& pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().parent == Some(source)
                    &&& typed_lock_map_contains_mode(share_lctx.container_lock_map(), source, TypedLockMode::Write)
                    &&& typed_lock_map_contains_mode(share_lctx.container_lock_map(), ctn_ptr, TypedLockMode::Write)
                    &&& typed_lock_map_contains_mode(old(lctx).container_lock_map(), ctn_ptr, TypedLockMode::Write)
                    &&& old(krnl).thrd_mp.typed_lock_map_aligned(old(lctx).thread_lock_map(), old(lctx).thread_id())
                    &&& *old(krnl) == (KernelK { pg_arr: old(krnl).pg_arr, ctn_mp: old(krnl).ctn_mp, thrd_mp: old(krnl).thrd_mp, pt_mp: old(krnl).pt_mp, pt_lower: old(krnl).pt_lower, ..pre })
                    &&& source != ctn_ptr
                    &&& pre.ctn_mp.dom().contains(source)
                    &&& pre.ctn_mp.spec_index(source).view().owned_pages.view().contains(pg_ptr)
                    &&& old(krnl).ctn_mp.dom() == pre.ctn_mp.dom()
                    &&& forall|c: RwLockContainerPtr| #![trigger old(krnl).ctn_mp.spec_index(c)] pre.ctn_mp.dom().contains(c) ==> {
                        &&& old(krnl).ctn_mp.spec_index(c).view_rodata() == pre.ctn_mp.spec_index(c).view_rodata()
                        &&& old(krnl).ctn_mp.spec_index(c).view_ghost() == pre.ctn_mp.spec_index(c).view_ghost()
                        &&& old(krnl).ctn_mp.spec_index(c).locking_thread() == pre.ctn_mp.spec_index(c).locking_thread()
                        &&& old(krnl).ctn_mp.spec_index(c).lock_process_owner_u() == pre.ctn_mp.spec_index(c).lock_process_owner_u()
                        &&& old(krnl).ctn_mp.spec_index(c).being_killed() == pre.ctn_mp.spec_index(c).being_killed()
                        &&& old(krnl).ctn_mp.spec_index(c).view() == (Container { owned_pages: old(krnl).ctn_mp.spec_index(c).view().owned_pages, ..pre.ctn_mp.spec_index(c).view() })
                        &&& old(krnl).ctn_mp.spec_index(c).view().owned_pages.view() == if c == source { pre.ctn_mp.spec_index(c).view().owned_pages.view().remove(pg_ptr) }
                            else if c == ctn_ptr { pre.ctn_mp.spec_index(c).view().owned_pages.view().insert(pg_ptr) } else { pre.ctn_mp.spec_index(c).view().owned_pages.view() }
                    }
                    &&& old(krnl).thrd_mp.unchanged_except(&pre.thrd_mp, quota_thrd_ptr)
                    &&& old(krnl).pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr)
                    &&& old(krnl).pt_lower.view() == pre.pt_lower.view().insert(pagetable_ptr, old(krnl).pt_lower.view().spec_index(pagetable_ptr))
                    &&& pre.pt_mp.typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id())
                    &&& old(krnl).pt_mp.typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id())
                    &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write)
                    &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k()
                    &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m()
                    &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_1g()
                }
            },
        ensures
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(steps).view() == old(steps).view().push(final(steps).view().last()),
            mmap_guard ==> mmap_4k_directory_step_pre(final(steps).view().last().old_u, cpu_id) && mmap_4k_directory_step(final(steps).view().last().old_u, final(steps).view().last().new_u, cpu_id),
            share_guard ==> {
                let progress = final(krnl).thrd_mp.spec_index(progress_thread).view().syscall_progress.view();
                &&& share_4k_directory_step_pre(final(steps).view().last().old_u, cpu_id)
                &&& share_4k_directory_step(final(steps).view().last().old_u, final(steps).view().last().new_u, cpu_id)
                &&& share_4k_objects_k(*final(krnl), cpu_id) == share_4k_objects_k(old(steps).snapshot_k(), cpu_id)
                &&& progress == share_4k_progress_after_directory(old(steps).snapshot_k().thrd_mp.spec_index(progress_thread).view().syscall_progress.view(), level)
                &&& progress_thread != quota_thrd_ptr ==> final(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().syscall_progress.view() == old(steps).snapshot_k().thrd_mp.spec_index(quota_thrd_ptr).view().syscall_progress.view()
                &&& progress->Some_0->Share4k_origin matches Share4kOrigin::IpcPages { peer }
                    ==> final(krnl).thrd_mp.spec_index(peer).view().state is IPC_TRANSIT && final(krnl).thrd_mp.spec_index(peer).view().state->IPC_TRANSIT_partner == progress_thread
            },
            final(steps).snapshot_k() == *final(krnl),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(krnl)),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] == old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int],
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            forall|cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(cpu_id)] old(lctx).cpu_lock_map().dom().contains(cpu_id) ==> final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
            forall|ctn_ptr: RwLockContainerPtr|
                #![trigger old(lctx).container_lock_map().dom().contains(ctn_ptr)]
                old(lctx).container_lock_map().dom().contains(ctn_ptr) ==> {
                    &&& final(krnl).ctn_mp.dom().contains(ctn_ptr)
                    &&& final(krnl).ctn_mp.lock_id_by_key(ctn_ptr) == old(krnl).ctn_mp.lock_id_by_key(ctn_ptr)
                    &&& final(krnl).ctn_mp.spec_index(ctn_ptr) == old(krnl).ctn_mp.spec_index(ctn_ptr)
                },
            forall|prc_ptr: RwLockProcessPtr|
                #![trigger old(lctx).process_lock_map().dom().contains(prc_ptr)]
                old(lctx).process_lock_map().dom().contains(prc_ptr) ==> {
                    &&& final(krnl).prc_mp.dom().contains(prc_ptr)
                    &&& final(krnl).prc_mp.lock_id_by_key(prc_ptr) == old(krnl).prc_mp.lock_id_by_key(prc_ptr)
                    &&& final(krnl).prc_mp.spec_index(prc_ptr) == old(krnl).prc_mp.spec_index(prc_ptr)
                },
            forall|thrd_ptr: RwLockThreadPtr|
                #![trigger old(lctx).thread_lock_map().dom().contains(thrd_ptr)]
                old(lctx).thread_lock_map().dom().contains(thrd_ptr) ==> {
                    &&& final(krnl).thrd_mp.dom().contains(thrd_ptr)
                    &&& thrd_ptr != progress_thread ==> final(krnl).thrd_mp.spec_index(thrd_ptr) == old(krnl).thrd_mp.spec_index(thrd_ptr)
                },
            final(krnl).thrd_mp.spec_index(progress_thread).view() == (Thread {
                syscall_progress: Ghost(share_4k_progress_after_directory(old(krnl).thrd_mp.spec_index(progress_thread).view().syscall_progress.view(), level)), ..old(krnl).thrd_mp.spec_index(progress_thread).view()
            }),
            final(krnl).thrd_mp.spec_index(progress_thread).view_ghost() == old(krnl).thrd_mp.spec_index(progress_thread).view_ghost(),
            final(krnl).thrd_mp.spec_index(progress_thread).locking_thread() == old(krnl).thrd_mp.spec_index(progress_thread).locking_thread(),
            final(krnl).thrd_mp.spec_index(progress_thread).being_killed() == old(krnl).thrd_mp.spec_index(progress_thread).being_killed(),
            forall|pagetable_ptr: RwLockPageTableRoot|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) ==> {
                    &&& final(krnl).pt_mp.dom().contains(pagetable_ptr)
                    &&& final(krnl).pt_mp.lock_id_by_key(pagetable_ptr) == old(krnl).pt_mp.lock_id_by_key(pagetable_ptr)
                    &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write) ==> {
                        &&& final(krnl).pt_mp.spec_index(pagetable_ptr) == old(krnl).pt_mp.spec_index(pagetable_ptr)
                        &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr)
                    }
                    &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read) ==> {
                        &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view() == old(krnl).pt_mp.spec_index(pagetable_ptr).view()
                        &&& final(krnl).pt_mp.spec_index(pagetable_ptr).rlocked_by_thread(old(lctx).thread_id())
                        &&& final(krnl).pt_mp.spec_index(pagetable_ptr).being_killed() == old(krnl).pt_mp.spec_index(pagetable_ptr).being_killed()
                    }
                },
            held_pagetable_windows_unchanged(old(krnl).pt_mp, old(krnl).pt_lower.view(), final(krnl).pt_mp, final(krnl).pt_lower.view(), old(lctx)),
            old(lctx).thread_lock_map().dom().contains(quota_thrd_ptr) ==> {
                let thread = old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view();
                &&& final(krnl).ctn_mp.dom().contains(thread.owning_container)
                &&& final(krnl).ctn_mp.spec_index(thread.owning_container).view_rodata() == old(krnl).ctn_mp.spec_index(thread.owning_container).view_rodata()
                &&& !thread_is_dangling(old(krnl).thrd_mp.spec_index(quota_thrd_ptr)) ==> final(krnl).prc_mp.dom().contains(thread.owning_proc)
                &&& !thread_is_dangling(old(krnl).thrd_mp.spec_index(quota_thrd_ptr)) ==> final(krnl).prc_mp.spec_index(thread.owning_proc).view_rodata() == old(krnl).prc_mp.spec_index(thread.owning_proc).view_rodata()
            },
            held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
            held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
            held_cpu_sets_unchanged(old(krnl).cpu_set_mp, final(krnl).cpu_set_mp, old(lctx)),
            held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
            held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
            held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
            write_held ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr),
    {
        let ghost mid = *krnl;
        krnl.set_thread_syscall_progress(progress_thread, Ghost(share_4k_progress_after_directory(krnl.thrd_mp.spec_index(progress_thread).view().syscall_progress.view(), level)),
            Tracked(&*lctx), Tracked(progress_thread_lock_perm));
        proof {
            let pre = steps.snapshot_k();
            let before = *krnl;
            let before_lctx = *lctx;
            assert(kernel_thread_quota_4k_changed(&pre, &before, quota_thrd_ptr, -1)) by { reveal(kernel_thread_quota_4k_changed); };
            mid.thrd_mp.typed_lock_map_aligned_held_in_dom(before_lctx.thread_lock_map(), before_lctx.thread_id());
            assert({
                let a = mid.thrd_mp.spec_index(progress_thread).view();
                let b = before.thrd_mp.spec_index(progress_thread).view();
                &&& b.owning_container == a.owning_container && b.upper_container_seq == a.upper_container_seq && b.owning_proc == a.owning_proc
                &&& thread_is_dangling(before.thrd_mp.spec_index(progress_thread)) == thread_is_dangling(mid.thrd_mp.spec_index(progress_thread))
            });
            krnl.kernel_step_boundary_thread_quota_4k_changed(&mut *lctx, &mut *steps, quota_thrd_ptr, -1);
            assert(write_held ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr) == whole_pagetable(before.pt_mp, before.pt_lower.view(), pagetable_ptr)) by {
                if write_held { assert(before_lctx.pagetable_lock_map().dom().contains(pagetable_ptr)); }
            };
            if mmap_guard {
                mmap_4k_directory_step_from_k(&pre, &before, &before_lctx, cpu_id, quota_thrd_ptr, prc_ptr, pagetable_ptr, level, write_held, indices.0, indices.1, lo, hi);
            }
            if share_guard {
                share_4k_directory_step_from_k(&pre, &mid, &before, &share_lctx, &before_lctx, cpu_id, progress_thread, quota_thrd_ptr, prc_ptr, ctn_ptr, pagetable_ptr,
                    transfer_source, pg_ptr, level, indices.0, indices.1, lo, hi);
                assert(share_4k_objects_k(*krnl, cpu_id) == share_4k_objects_k(before, cpu_id)) by { reveal(share_4k_objects_k); };
                assert(krnl.thrd_mp.spec_index(progress_thread).view().syscall_progress.view()->Some_0->Share4k_origin matches Share4kOrigin::IpcPages { peer }
                    ==> krnl.thrd_mp.spec_index(peer).view().state is IPC_TRANSIT && krnl.thrd_mp.spec_index(peer).view().state->IPC_TRANSIT_partner == progress_thread) by { reveal(share_4k_objects_k); };
            }
        }
    }

    /// Move the staged page from `transfer_source` into `ctn_ptr` when the quota thread allocated it from the parent container.
    fn install_one_mmap_4k_directory_page_transfer_if_source(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, pg_ptr: PagePtr, quota_thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr,
        transfer_source: Option<RwLockContainerPtr>, Tracked(page_lock_perm): Tracked<&LockPerm>, Tracked(transfer_source_lock_perm): Tracked<Option<&LockPerm>>,
        Tracked(transfer_target_lock_perm): Tracked<Option<&LockPerm>>,
    )
        requires
            old(krnl).inv(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            page_ptr_valid(pg_ptr),
            old(krnl).thrd_mp.dom().contains(quota_thrd_ptr),
            old(krnl).thrd_mp.spec_index(quota_thrd_ptr).view().temp_alloc_cache_4k.view().contains(pg_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), quota_thrd_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write),
            !old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().being_killed(),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: quota_thrd_ptr }),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == (match transfer_source { Some(source) => source, None => ctn_ptr }),
            page_lock_perm.state() is WriteLock,
            page_lock_perm.thread_id() == old(lctx).thread_id(),
            page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id,
            transfer_source is Some ==> {
                let source = transfer_source->Some_0;
                &&& source != ctn_ptr
                &&& old(krnl).ctn_mp.dom().contains(source) && old(krnl).ctn_mp.dom().contains(ctn_ptr)
                &&& old(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata().view().parent == Some(source)
                &&& typed_lock_map_contains_mode(old(lctx).container_lock_map(), source, TypedLockMode::Write)
                &&& typed_lock_map_contains_mode(old(lctx).container_lock_map(), ctn_ptr, TypedLockMode::Write)
                &&& !old(krnl).ctn_mp.spec_index(source).being_killed() && !old(krnl).ctn_mp.spec_index(ctn_ptr).being_killed()
                &&& transfer_source_lock_perm is Some && transfer_source_lock_perm->Some_0.state() is WriteLock
                &&& transfer_source_lock_perm->Some_0.thread_id() == old(lctx).thread_id()
                &&& transfer_source_lock_perm->Some_0.lock_id() == old(krnl).ctn_mp.spec_index(source).locking_thread()->Write_lock_id
                &&& transfer_target_lock_perm is Some && transfer_target_lock_perm->Some_0.state() is WriteLock
                &&& transfer_target_lock_perm->Some_0.thread_id() == old(lctx).thread_id()
                &&& transfer_target_lock_perm->Some_0.lock_id() == old(krnl).ctn_mp.spec_index(ctn_ptr).locking_thread()->Write_lock_id
            },
        ensures
            final(krnl).inv(),
            *final(lctx) == *old(lctx),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, ctn_mp: final(krnl).ctn_mp, ..*old(krnl) }),
            final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(pg_ptr)),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state,
            final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == ctn_ptr,
            !final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().being_killed(),
            page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id,
            transfer_source is None ==> *final(krnl) == *old(krnl),
            transfer_source is Some ==> {
                let source = transfer_source->Some_0;
                &&& old(krnl).ctn_mp.spec_index(source).view().owned_pages.view().contains(pg_ptr)
                &&& final(krnl).ctn_mp.dom() == old(krnl).ctn_mp.dom()
                &&& forall|c: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(c)]
                    old(krnl).ctn_mp.dom().contains(c) && c != source && c != ctn_ptr ==> final(krnl).ctn_mp.spec_index(c) == old(krnl).ctn_mp.spec_index(c)
                &&& final(krnl).ctn_mp.spec_index(source).is_init() == old(krnl).ctn_mp.spec_index(source).is_init()
                &&& final(krnl).ctn_mp.spec_index(source).view_rodata() == old(krnl).ctn_mp.spec_index(source).view_rodata()
                &&& final(krnl).ctn_mp.spec_index(source).view_ghost() == old(krnl).ctn_mp.spec_index(source).view_ghost()
                &&& final(krnl).ctn_mp.spec_index(source).locking_thread() == old(krnl).ctn_mp.spec_index(source).locking_thread()
                &&& final(krnl).ctn_mp.spec_index(source).control() == old(krnl).ctn_mp.spec_index(source).control()
                &&& final(krnl).ctn_mp.spec_index(source).view() == (Container { owned_pages: final(krnl).ctn_mp.spec_index(source).view().owned_pages, ..old(krnl).ctn_mp.spec_index(source).view() })
                &&& final(krnl).ctn_mp.spec_index(ctn_ptr).is_init() == old(krnl).ctn_mp.spec_index(ctn_ptr).is_init()
                &&& final(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata()
                &&& final(krnl).ctn_mp.spec_index(ctn_ptr).view_ghost() == old(krnl).ctn_mp.spec_index(ctn_ptr).view_ghost()
                &&& final(krnl).ctn_mp.spec_index(ctn_ptr).locking_thread() == old(krnl).ctn_mp.spec_index(ctn_ptr).locking_thread()
                &&& final(krnl).ctn_mp.spec_index(ctn_ptr).control() == old(krnl).ctn_mp.spec_index(ctn_ptr).control()
                &&& final(krnl).ctn_mp.spec_index(ctn_ptr).view() == (Container { owned_pages: final(krnl).ctn_mp.spec_index(ctn_ptr).view().owned_pages, ..old(krnl).ctn_mp.spec_index(ctn_ptr).view() })
                &&& final(krnl).ctn_mp.spec_index(source).view().owned_pages.view() =~= old(krnl).ctn_mp.spec_index(source).view().owned_pages.view().remove(pg_ptr)
                &&& final(krnl).ctn_mp.spec_index(ctn_ptr).view().owned_pages.view() =~= old(krnl).ctn_mp.spec_index(ctn_ptr).view().owned_pages.view().insert(pg_ptr)
            },
    {
        if let Some(source) = transfer_source {
            let tracked source_lock_perm = transfer_source_lock_perm.tracked_unwrap();
            let tracked target_lock_perm = transfer_target_lock_perm.tracked_unwrap();
            proof { assert(krnl.ctn_mp.spec_index(source).view().owned_pages.view().contains(pg_ptr)) by { container_owned_pages_wf_backward_at(krnl.ctn_mp, krnl.pg_arr, page_ptr2page_index(pg_ptr)); }; }
            transfer_staged_4k_page_to_child_container(krnl, Tracked(&mut *lctx), pg_ptr, quota_thrd_ptr, source, ctn_ptr, Tracked(page_lock_perm), Tracked(source_lock_perm), Tracked(target_lock_perm));
        }
    }

    /// Record the installed L4 or L3 level in the running thread's 2M mmap progress, then end the krnl section of one directory
    /// install at the step boundary and derive the 2M mmap directory step from the section's start snapshot.
    pub(super) fn install_one_mmap_2m_directory_page_end_step(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, level: MissingPageTableLevel, cpu_id: CpuId,
        thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index), lo: L2Index, hi: L2Index,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
    )
        requires
            old(krnl).inv(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(krnl).thrd_mp.dom().contains(thrd_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
            KERNEL_MEM_END_L4INDEX <= indices.0 && pei_valid(indices.0) && pei_valid(indices.1),
            level is L4 || level is L3,
            level is L3 ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks == Map::new(
                whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks.dom()
                    + Set::<usize>::range(0, 512).map_by(|i: usize| WindowVa { va: spec_index2va((indices.0, indices.1, i, 0usize)) }, |w: WindowVa| spec_v2l2index(w.va)),
                |w: WindowVa| if whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks.dom().contains(w) {
                    whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks[w]
                } else if lo <= spec_v2l2index(w.va) <= hi { LockStateU::WriteLocked { writer: cpu_id } } else { LockStateU::Unlocked }),
            level is L3 ==> !whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks.dom().contains(WindowVa { va: spec_index2va((indices.0, indices.1, 0usize, 0usize)) }),
            level is L4 ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks,
            old(lctx).kernel_view_locking_state() is Release,
            kernel_thread_quota_4k_changed(&old(steps).snapshot_k(), old(krnl), thrd_ptr, -1),
            index_valid(NUM_CPUS, cpu_id),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
            old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            {
                let pre = old(steps).snapshot_k();
                let progress = pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view();
                &&& pre.inv()
                &&& pre.thrd_mp.typed_lock_map_aligned(old(lctx).thread_lock_map(), old(lctx).thread_id())
                &&& pre.pt_mp.typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id())
                &&& *old(krnl) == (KernelK { pt_mp: old(krnl).pt_mp, pt_lower: old(krnl).pt_lower, pg_arr: old(krnl).pg_arr, thrd_mp: old(krnl).thrd_mp, ..pre })
                &&& old(krnl).thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr)
                &&& old(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread {
                    quota_4k: old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_4k, temp_alloc_cache_4k: old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_4k,
                    syscall_progress: old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..pre.thrd_mp.spec_index(thrd_ptr).view()
                })
                &&& old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed()
                &&& pre.prc_mp.dom().contains(prc_ptr) && pre.prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr
                &&& old(krnl).pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr)
                &&& old(krnl).pt_lower.view() == pre.pt_lower.view().insert(pagetable_ptr, old(krnl).pt_lower.view().spec_index(pagetable_ptr))
                &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k()
                &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m()
                &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_1g()
                &&& pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr)
                &&& pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr)
                &&& pre.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr
                &&& progress is Some && progress->Some_0 is Mmap2m && progress->Some_0->Mmap2m_mapped < progress->Some_0->Mmap2m_range.len
                &&& progress->Some_0->Mmap2m_phase is Fill
                &&& old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == mmap_4k_progress_after_directory(progress, level)
                &&& level is L3 ==> forall|w: WindowVa| #![trigger va_range_2m_windows(progress->Some_0->Mmap2m_range.covering_4k_range()).contains(w)]
                    w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1
                        ==> va_range_2m_windows(progress->Some_0->Mmap2m_range.covering_4k_range()).contains(w) == (lo <= spec_v2l2index(w.va) <= hi)
            },
        ensures
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(steps).view() == old(steps).view().push(final(steps).view().last()),
            mmap_2m_directory_step_pre(final(steps).view().last().old_u, cpu_id),
            mmap_2m_directory_step(final(steps).view().last().old_u, final(steps).view().last().new_u, cpu_id),
            final(steps).snapshot_k() == *final(krnl),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(krnl)),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] == old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int],
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            forall|cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(cpu_id)] old(lctx).cpu_lock_map().dom().contains(cpu_id) ==> final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
            forall|ctn_ptr: RwLockContainerPtr|
                #![trigger old(lctx).container_lock_map().dom().contains(ctn_ptr)]
                old(lctx).container_lock_map().dom().contains(ctn_ptr) ==> {
                    &&& final(krnl).ctn_mp.dom().contains(ctn_ptr)
                    &&& final(krnl).ctn_mp.lock_id_by_key(ctn_ptr) == old(krnl).ctn_mp.lock_id_by_key(ctn_ptr)
                    &&& final(krnl).ctn_mp.spec_index(ctn_ptr) == old(krnl).ctn_mp.spec_index(ctn_ptr)
                },
            forall|prc_ptr: RwLockProcessPtr|
                #![trigger old(lctx).process_lock_map().dom().contains(prc_ptr)]
                old(lctx).process_lock_map().dom().contains(prc_ptr) ==> {
                    &&& final(krnl).prc_mp.dom().contains(prc_ptr)
                    &&& final(krnl).prc_mp.lock_id_by_key(prc_ptr) == old(krnl).prc_mp.lock_id_by_key(prc_ptr)
                    &&& final(krnl).prc_mp.spec_index(prc_ptr) == old(krnl).prc_mp.spec_index(prc_ptr)
                },
            forall|t: RwLockThreadPtr|
                #![trigger old(lctx).thread_lock_map().dom().contains(t)]
                old(lctx).thread_lock_map().dom().contains(t) ==> {
                    &&& final(krnl).thrd_mp.dom().contains(t)
                    &&& t != thrd_ptr ==> final(krnl).thrd_mp.spec_index(t) == old(krnl).thrd_mp.spec_index(t)
                },
            final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread {
                syscall_progress: Ghost(mmap_2m_progress_after_directory(old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(), level)), ..old(krnl).thrd_mp.spec_index(thrd_ptr).view()
            }),
            final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
            final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
            final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
            forall|pagetable_ptr: RwLockPageTableRoot|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) ==> {
                    &&& final(krnl).pt_mp.dom().contains(pagetable_ptr)
                    &&& final(krnl).pt_mp.lock_id_by_key(pagetable_ptr) == old(krnl).pt_mp.lock_id_by_key(pagetable_ptr)
                    &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write) ==> {
                        &&& final(krnl).pt_mp.spec_index(pagetable_ptr) == old(krnl).pt_mp.spec_index(pagetable_ptr)
                        &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr)
                    }
                    &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read) ==> {
                        &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view() == old(krnl).pt_mp.spec_index(pagetable_ptr).view()
                        &&& final(krnl).pt_mp.spec_index(pagetable_ptr).rlocked_by_thread(old(lctx).thread_id())
                        &&& final(krnl).pt_mp.spec_index(pagetable_ptr).being_killed() == old(krnl).pt_mp.spec_index(pagetable_ptr).being_killed()
                    }
                },
            held_pagetable_windows_unchanged(old(krnl).pt_mp, old(krnl).pt_lower.view(), final(krnl).pt_mp, final(krnl).pt_lower.view(), old(lctx)),
            {
                let thread = old(krnl).thrd_mp.spec_index(thrd_ptr).view();
                &&& final(krnl).ctn_mp.dom().contains(thread.owning_container)
                &&& final(krnl).ctn_mp.spec_index(thread.owning_container).view_rodata() == old(krnl).ctn_mp.spec_index(thread.owning_container).view_rodata()
                &&& !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)) ==> final(krnl).prc_mp.dom().contains(thread.owning_proc)
                &&& !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)) ==> final(krnl).prc_mp.spec_index(thread.owning_proc).view_rodata() == old(krnl).prc_mp.spec_index(thread.owning_proc).view_rodata()
            },
            held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
            held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
            held_cpu_sets_unchanged(old(krnl).cpu_set_mp, final(krnl).cpu_set_mp, old(lctx)),
            held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
            held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
            held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
    {
        let ghost mid = *krnl;
        krnl.set_thread_syscall_progress(thrd_ptr, Ghost(mmap_2m_progress_after_directory(krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(), level)),
            Tracked(&*lctx), Tracked(thread_lock_perm));
        proof {
            let pre = steps.snapshot_k();
            let before = *krnl;
            let before_lctx = *lctx;
            assert(kernel_thread_quota_4k_changed(&pre, &before, thrd_ptr, -1)) by { reveal(kernel_thread_quota_4k_changed); };
            mid.thrd_mp.typed_lock_map_aligned_held_in_dom(before_lctx.thread_lock_map(), before_lctx.thread_id());
            krnl.kernel_step_boundary_thread_quota_4k_changed(&mut *lctx, &mut *steps, thrd_ptr, -1);
            mmap_2m_directory_step_from_k(&pre, &before, &before_lctx, cpu_id, thrd_ptr, prc_ptr, pagetable_ptr, level, indices.0, indices.1, lo, hi);
        }
    }
} // verus!
