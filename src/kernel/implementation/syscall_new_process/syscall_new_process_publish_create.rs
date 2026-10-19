use vstd::prelude::*;
use crate::*;

verus! {
/// Creates `process_page_ptr` as a child of `parent_ptr` in `container_ptr` with the page table staged on `pagetable_page_ptr` and
/// `l4_page_ptr`, then releases the staged pages, the parent, and the PCID allocator; the child and its page table stay write-held.
pub(super) fn create_and_release_staged_process(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, container_ptr: RwLockContainerPtr, parent_ptr: RwLockProcessPtr,
    current_thread_ptr: RwLockThreadPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, source_pagetable_ptr: RwLockPageTableRoot, pcid: Pcid,
    process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr, process_page_lock_perm: Tracked<LockPerm>,
    pagetable_page_lock_perm: Tracked<LockPerm>, l4_page_lock_perm: Tracked<LockPerm>, pcid_allocator_lock_perm: Tracked<LockPerm>,
    parent_lock_perm: Tracked<LockPerm>, Tracked(current_thread_lock_perm): Tracked<&LockPerm>,
) -> (ret: (RwLockProcessPtr, RwLockPageTableRoot, Tracked<LockPerm>, Tracked<LockPerm>))
    requires
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator == pcid_allocator_ptr,
        old(krnl).pcid_allc_mp.dom().contains(pcid_allocator_ptr),
        typed_lock_map_contains_mode(old(lctx).pcid_allocator_lock_map(), pcid_allocator_ptr, TypedLockMode::Write),
        old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).view().pcid_is_free(pcid),
        pcid_allocator_lock_perm.view().state() is WriteLock,
        pcid_allocator_lock_perm.view().thread_id() == old(lctx).thread_id(),
        pcid_allocator_lock_perm.view().lock_id() == old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(parent_ptr),
        old(krnl).prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == container_ptr,
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), parent_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(parent_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(parent_ptr).view().state.view() is Running || old(krnl).prc_mp.spec_index(parent_ptr).view().state.view() is Zombie,
        parent_lock_perm.view().state() is WriteLock,
        parent_lock_perm.view().thread_id() == old(lctx).thread_id(),
        parent_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(parent_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().proc_pagetable_ptr == source_pagetable_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view() == set![process_page_ptr, pagetable_page_ptr, l4_page_ptr],
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().is_empty(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_cache_1g.view().is_empty(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k >= 3,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().wf(),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Write),
        page_ptr_valid(process_page_ptr) && page_ptr_valid(pagetable_page_ptr) && page_ptr_valid(l4_page_ptr),
        process_page_ptr != pagetable_page_ptr && process_page_ptr != l4_page_ptr && pagetable_page_ptr != l4_page_ptr,
        !old(krnl).prc_mp.dom().contains(process_page_ptr),
        !old(krnl).pt_mp.dom().contains(pagetable_page_ptr),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: current_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().owning_container == container_ptr,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().owning_container == container_ptr,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().owning_container == container_ptr,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(process_page_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pagetable_page_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(l4_page_ptr), TypedLockMode::Write),
        process_page_lock_perm.view().state() is WriteLock && process_page_lock_perm.view().thread_id() == old(lctx).thread_id() && process_page_lock_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().locking_thread()->Write_lock_id,
        pagetable_page_lock_perm.view().state() is WriteLock && pagetable_page_lock_perm.view().thread_id() == old(lctx).thread_id() && pagetable_page_lock_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().locking_thread()->Write_lock_id,
        l4_page_lock_perm.view().state() is WriteLock && l4_page_lock_perm.view().thread_id() == old(lctx).thread_id() && l4_page_lock_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().locking_thread()->Write_lock_id,
        old(lctx).page_lock_map().dom() =~= set![page_ptr2page_index(process_page_ptr), page_ptr2page_index(pagetable_page_ptr), page_ptr2page_index(l4_page_ptr)],
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom() =~= set![parent_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom() =~= set![pcid_allocator_ptr],
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr],
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        ret.0 == process_page_ptr,
        ret.1 == pagetable_page_ptr,
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, prc_mp: final(krnl).prc_mp, thr_mp: final(krnl).thr_mp, ctn_mp: final(krnl).ctn_mp, pt_mp: final(krnl).pt_mp, it_mp: final(krnl).it_mp, pcid_allc_mp: final(krnl).pcid_allc_mp, ..*old(krnl) }),
        final(krnl).prc_mp.dom() == old(krnl).prc_mp.dom().insert(ret.0),
        forall|p: RwLockProcessPtr| #![trigger final(krnl).prc_mp.spec_index(p)] old(krnl).prc_mp.dom().contains(p) ==> {
            &&& final(krnl).prc_mp.spec_index(p).view_rodata() == old(krnl).prc_mp.spec_index(p).view_rodata()
            &&& final(krnl).prc_mp.spec_index(p).view_ghost().uppertree_seq == old(krnl).prc_mp.spec_index(p).view_ghost().uppertree_seq
            &&& final(krnl).prc_mp.spec_index(p).view_ghost().owned_pci_functions == old(krnl).prc_mp.spec_index(p).view_ghost().owned_pci_functions
            &&& final(krnl).prc_mp.spec_index(p).view_ghost().subtree_set.view() == if old(krnl).prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view().push(parent_ptr).contains(p) {
                old(krnl).prc_mp.spec_index(p).view_ghost().subtree_set.view().insert(ret.0)
            } else { old(krnl).prc_mp.spec_index(p).view_ghost().subtree_set.view() }
            &&& final(krnl).prc_mp.spec_index(p).view() == (Process { children: final(krnl).prc_mp.spec_index(p).view().children, ..old(krnl).prc_mp.spec_index(p).view() })
            &&& final(krnl).prc_mp.spec_index(p).view().children.view() == if p == parent_ptr { old(krnl).prc_mp.spec_index(p).view().children.view().push(ret.0) } else { old(krnl).prc_mp.spec_index(p).view().children.view() }
            &&& final(krnl).prc_mp.spec_index(p).being_killed() == old(krnl).prc_mp.spec_index(p).being_killed()
            &&& if p == parent_ptr { final(krnl).prc_mp.spec_index(p).locking_thread() is None } else { final(krnl).prc_mp.spec_index(p).locking_thread() == old(krnl).prc_mp.spec_index(p).locking_thread() }
        },
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), ret.0, TypedLockMode::Write),
        !final(krnl).prc_mp.spec_index(ret.0).being_killed(),
        !final(krnl).prc_mp.spec_index(ret.0).view().zombie,
        final(krnl).prc_mp.spec_index(ret.0).view().state.view() is Creating,
        final(krnl).prc_mp.spec_index(ret.0).view().pagetable == ret.1,
        final(krnl).prc_mp.spec_index(ret.0).view().iommu_table == None,
        final(krnl).prc_mp.spec_index(ret.0).view_ghost().owned_pci_functions.view().is_empty(),
        final(krnl).prc_mp.spec_index(ret.0).view().quota_4k == 0,
        final(krnl).prc_mp.spec_index(ret.0).view().quota_2m == 0,
        final(krnl).prc_mp.spec_index(ret.0).view().quota_1g == 0,
        final(krnl).prc_mp.spec_index(ret.0).view_rodata().view().parent == Some(parent_ptr),
        final(krnl).prc_mp.spec_index(ret.0).view_rodata().view().owning_container == container_ptr,
        final(krnl).prc_mp.spec_index(ret.0).view_rodata().view().pagetable == ret.1,
        final(krnl).prc_mp.spec_index(ret.0).view_rodata().view().depth == old(krnl).prc_mp.spec_index(parent_ptr).view_rodata().view().depth + 1,
        final(krnl).prc_mp.spec_index(ret.0).view().children.view() == Seq::<RwLockProcessPtr>::empty(),
        final(krnl).prc_mp.spec_index(ret.0).view().owned_threads.view() == Seq::<RwLockThreadPtr>::empty(),
        final(krnl).prc_mp.spec_index(ret.0).view_ghost().uppertree_seq.view() == old(krnl).prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view().push(parent_ptr),
        final(krnl).prc_mp.spec_index(ret.0).view_ghost().subtree_set.view().is_empty(),
        final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, current_thread_ptr),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view() == (Thread {
            quota_4k: (old(krnl).thr_mp.spec_index(current_thread_ptr).view().quota_4k - 3) as usize, temp_alloc_cache_4k: Ghost(Set::empty()), ..old(krnl).thr_mp.spec_index(current_thread_ptr).view()
        }),
        final(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread(),
        kernel_thread_quota_4k_changed(old(krnl), final(krnl), current_thread_ptr, -3),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        current_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).ctn_mp.unchanged_except(&old(krnl).ctn_mp, container_ptr),
        final(krnl).ctn_mp.spec_index(container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata(),
        final(krnl).ctn_mp.spec_index(container_ptr).view_ghost() == (ContainerGhost { owned_processes: final(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes, ..old(krnl).ctn_mp.spec_index(container_ptr).view_ghost() }),
        final(krnl).ctn_mp.spec_index(container_ptr).being_killed() == old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(container_ptr).locking_thread() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread(),
        final(krnl).ctn_mp.spec_index(container_ptr).view() == old(krnl).ctn_mp.spec_index(container_ptr).view(),
        final(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view() == old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().insert(ret.0),
        final(krnl).pcid_allc_mp.unchanged_except(&old(krnl).pcid_allc_mp, pcid_allocator_ptr),
        PcidAllocator::free_pcids(old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).view().ref_counters.view()).contains(pcid),
        final(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).view().alloc_ensures(&old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).view(), ret.0, pcid),
        final(krnl).pt_mp.dom() == old(krnl).pt_mp.dom().insert(ret.1),
        forall|p: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(p)] old(krnl).pt_mp.dom().contains(p) ==> final(krnl).pt_mp.spec_index(p) == old(krnl).pt_mp.spec_index(p),
        final(krnl).pt_mp.spec_index(ret.1).view().is_empty(),
        final(krnl).pt_mp.spec_index(ret.1).view().proc_ptr == ret.0,
        final(krnl).it_mp == old(krnl).it_mp,
        final(lctx).page_lock_map().dom().is_empty(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map().dom() =~= set![ret.0],
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map().dom().is_empty(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr, ret.1],
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), ret.1, TypedLockMode::Write),
        ret.2.view().state() is WriteLock,
        ret.2.view().thread_id() == final(lctx).thread_id(),
        ret.2.view().lock_id() == final(krnl).prc_mp.spec_index(ret.0).locking_thread()->Write_lock_id,
        ret.3.view().state() is WriteLock,
        ret.3.view().thread_id() == final(lctx).thread_id(),
        ret.3.view().lock_id() == final(krnl).pt_mp.spec_index(ret.1).locking_thread()->Write_lock_id,
{
    hide(Seq::contains);
    let tracked mut pcid_allocator_lock_perm = pcid_allocator_lock_perm.get();
    let tracked mut parent_lock_perm = parent_lock_perm.get();
    let tracked process_page_lock_perm = process_page_lock_perm.get();
    let tracked pagetable_page_lock_perm = pagetable_page_lock_perm.get();
    let tracked l4_page_lock_perm = l4_page_lock_perm.get();
    proof {
        assert(krnl.prc_mp.spec_index(parent_ptr).view_rodata().view().depth < usize::MAX) by {
            let uppers = krnl.prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view();
            assert(uppers.no_duplicates() && uppers.len() == krnl.prc_mp.spec_index(parent_ptr).view_rodata().view().depth) by { process_perms_wf_at(krnl.prc_mp, parent_ptr); };
            assert(uppers.len() <= NUM_PAGES) by {
                let c = krnl.prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container;
                let tree = krnl.ctn_mp.spec_index(c).view_ghost().owned_processes.view();
                container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, parent_ptr); container_process_wf_container_at(krnl.ctn_mp, krnl.prc_mp, c, parent_ptr);
                per_container_process_tree_wf_at(krnl.ctn_mp, krnl.prc_mp, c); process_uppertree_seq_wf_dom_at(krnl.ctn_mp.spec_index(c).view().root_process, tree, krnl.prc_mp, parent_ptr);
                lemma_kernel_object_ptr_seq_len_bounded(&*krnl, uppers);
            };
        };
        assert(page_ptr2page_index(process_page_ptr) != page_ptr2page_index(pagetable_page_ptr) && page_ptr2page_index(process_page_ptr) != page_ptr2page_index(l4_page_ptr)
            && page_ptr2page_index(pagetable_page_ptr) != page_ptr2page_index(l4_page_ptr)) by {
            page_ptr2page_index_neq(process_page_ptr, pagetable_page_ptr); page_ptr2page_index_neq(process_page_ptr, l4_page_ptr);
            page_ptr2page_index_neq(pagetable_page_ptr, l4_page_ptr);
        };
    }
    let (child_ptr, target_pagetable_ptr, Tracked(child_lock_perm), Tracked(target_pagetable_lock_perm)) = create_process_from_staged_pages(
        krnl, process_page_ptr, pagetable_page_ptr, l4_page_ptr, parent_ptr, current_thread_ptr, container_ptr, pcid_allocator_ptr, pcid,
        Tracked(&mut *lctx), Tracked(&process_page_lock_perm), Tracked(&pagetable_page_lock_perm), Tracked(&l4_page_lock_perm),
        Tracked(&parent_lock_perm), Tracked(&current_thread_lock_perm), Tracked(&pcid_allocator_lock_perm),
    );
    krnl.wunlock_page(page_ptr2page_index(l4_page_ptr), Tracked(&mut *lctx), Tracked(l4_page_lock_perm));
    krnl.wunlock_page(page_ptr2page_index(pagetable_page_ptr), Tracked(&mut *lctx), Tracked(pagetable_page_lock_perm));
    krnl.wunlock_page(page_ptr2page_index(process_page_ptr), Tracked(&mut *lctx), Tracked(process_page_lock_perm));
    proof { assert(krnl.prc_mp.spec_index(parent_ptr).view().state.view() is Running || krnl.prc_mp.spec_index(parent_ptr).view().state.view() is Zombie) by { reveal(create_process_from_staged_pages_eof_transition_framing); }; }
    krnl.wunlock_process(parent_ptr, Tracked(&mut *lctx), Tracked(parent_lock_perm));
    krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
    proof { reveal(create_process_from_staged_pages_eof_transition_framing); reveal(kernel_thread_quota_4k_changed); }
    (child_ptr, target_pagetable_ptr, Tracked(child_lock_perm), Tracked(target_pagetable_lock_perm))
}
} // verus!
