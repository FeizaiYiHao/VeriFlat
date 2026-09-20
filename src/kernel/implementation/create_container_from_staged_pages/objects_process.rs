use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
#[verifier::rlimit(56)]
pub(super) fn publish_new_container_process_and_pagetable(
    krnl: &mut KernelK, child_container_ptr: RwLockContainerPtr, child_process_ptr: RwLockProcessPtr,
    child_pagetable_ptr: RwLockPageTableRoot, l4_page: PagePtr, root_pcid: Pcid, child_depth: usize, process_quota_4k: usize,
    Ghost(funding_pages): Ghost<Seq<PagePtr>>, container_head: PageIndex, pcid_allocator_head: PageIndex,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(process_page_lock_perm): Tracked<&LockPerm>,
    Tracked(pagetable_page_lock_perm): Tracked<&LockPerm>, Tracked(l4_page_lock_perm): Tracked<&LockPerm>,
    Tracked(container_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
    Tracked(pcid_allocator_tail_lock_perms): Tracked<&Map<PageIndex, LockPerm>>,
) -> (ret: (Tracked<LockPerm>, Tracked<LockPerm>))
    requires
        old(krnl).pg_arr.inv(),
        page_array_wf(old(krnl).pg_arr),
        old(krnl).prc_mp.perms_wf(),
        old(krnl).pt_mp.perms_wf(),
        old(krnl).dflt_pt.view().wf(),
        pei_valid(old(krnl).dflt_pt.view().kernel_l4_end),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        pcid_valid(root_pcid),
        root_pcid != KERNEL_DEFAULT_PCID,
        page_ptr_valid(child_process_ptr),
        page_ptr_valid(child_pagetable_ptr),
        page_ptr_valid(l4_page),
        child_process_ptr != child_pagetable_ptr,
        child_process_ptr != l4_page,
        child_pagetable_ptr != l4_page,
        !old(krnl).prc_mp.dom().contains(child_process_ptr),
        !old(krnl).pt_mp.dom().contains(child_pagetable_ptr),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(child_process_ptr),).view().is_init(),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(child_process_ptr),).view().view().perm_inv(),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(child_process_ptr),).view().view().perm_4k.view().is_some(),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(child_process_ptr),).view().view().state is Owned4k,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(child_process_ptr),).view().view().addr == child_process_ptr,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(child_pagetable_ptr),).view().is_init(),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(child_pagetable_ptr),).view().view().perm_inv(),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(child_pagetable_ptr),).view().view().perm_4k.view().is_some(),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(child_pagetable_ptr),).view().view().state is Owned4k,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(child_pagetable_ptr),).view().view().addr == child_pagetable_ptr,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page),).view().is_init(),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page),).view().view().perm_inv(),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page),).view().view().perm_4k.view().is_some(),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page),).view().view().state is Owned4k,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page),).view().view().addr == l4_page,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(child_process_ptr), TypedLockMode::Write,),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(child_pagetable_ptr), TypedLockMode::Write,),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(l4_page), TypedLockMode::Write,),
        process_page_lock_perm.state() is WriteLock,
        process_page_lock_perm.thread_id() == old(lctx).thread_id(),
        process_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(
                page_ptr2page_index(child_process_ptr),
            ).view().locking_thread()->Write_lock_id,
        pagetable_page_lock_perm.state() is WriteLock,
        pagetable_page_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(
                page_ptr2page_index(child_pagetable_ptr),
            ).view().locking_thread()->Write_lock_id,
        l4_page_lock_perm.state() is WriteLock,
        l4_page_lock_perm.thread_id() == old(lctx).thread_id(),
        l4_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(
                page_ptr2page_index(l4_page),
            ).view().locking_thread()->Write_lock_id,
        !funding_pages.to_set().contains(child_process_ptr),
        !funding_pages.to_set().contains(child_pagetable_ptr),
        !funding_pages.to_set().contains(l4_page),
        staged_4k_page_chain(old(krnl).pg_arr, funding_pages),
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, old(krnl).pg_arr, old(lctx), container_head,),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, old(krnl).pg_arr, old(lctx), pcid_allocator_head,),
        !page_2m_tail_indices(container_head).contains(page_ptr2page_index(child_process_ptr),),
        !page_2m_tail_indices(container_head).contains(page_ptr2page_index(child_pagetable_ptr),),
        !page_2m_tail_indices(container_head).contains(page_ptr2page_index(l4_page),),
        !page_2m_tail_indices(pcid_allocator_head).contains(page_ptr2page_index(child_process_ptr),),
        !page_2m_tail_indices(pcid_allocator_head).contains(page_ptr2page_index(child_pagetable_ptr),),
        !page_2m_tail_indices(pcid_allocator_head).contains(page_ptr2page_index(l4_page),),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        lock_id_set_aligned(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)), *final(krnl) == (KernelK {
            pg_arr: final(krnl).pg_arr,
            prc_mp: final(krnl).prc_mp,
            pt_mp: final(krnl).pt_mp,
            ..*old(krnl)
        }),
        final(krnl).pg_arr.inv(),
        page_array_wf(final(krnl).pg_arr),
        final(krnl).prc_mp.perms_wf(),
        process_perms_wf(old(krnl).prc_mp) ==> process_perms_wf(final(krnl).prc_mp),
        final(krnl).pt_mp.perms_wf(),
        pagetable_perms_wf(old(krnl).pt_mp) ==> pagetable_perms_wf(final(krnl).pt_mp),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx),),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx),),
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom(),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index)]
            #![trigger old(krnl).pg_arr.spec_index(index)]
            index_valid(NUM_PAGES, index) && index != page_ptr2page_index(child_process_ptr) && index != page_ptr2page_index(child_pagetable_ptr) && index != page_ptr2page_index(l4_page) ==> final(krnl).pg_arr.spec_index(index) == old(krnl).pg_arr.spec_index(index),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index).view().view().mappings()]
            #![trigger old(krnl).pg_arr.spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index) ==> final(krnl).pg_arr.spec_index(index).view().view().mappings() == old(krnl).pg_arr.spec_index(index).view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(lctx).page_lock_map().get(index)]
            index != page_ptr2page_index(child_process_ptr) && index != page_ptr2page_index(child_pagetable_ptr) && index != page_ptr2page_index(l4_page) ==> final(lctx).page_lock_map().get(index) == old(lctx).page_lock_map().get(index),
        final(krnl).pg_arr.spec_index(
            page_ptr2page_index(child_process_ptr),
        ).view().view().state == (PageState::Allocated4k {
            state: Allocated4KPageState::AsProcess,
        }),
        final(krnl).pg_arr.spec_index(
            page_ptr2page_index(child_pagetable_ptr),
        ).view().view().state == (PageState::Allocated4k {
            state: Allocated4KPageState::AsPageTableRoot,
        }),
        final(krnl).pg_arr.spec_index(
            page_ptr2page_index(l4_page),
        ).view().view().state == (PageState::Allocated4k {
            state: Allocated4KPageState::PageTable {
                pagetable_root: child_pagetable_ptr,
            },
        }),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(child_process_ptr),).view().view().owning_container == child_container_ptr,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(child_pagetable_ptr),).view().view().owning_container == child_container_ptr,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page),).view().view().owning_container == child_container_ptr,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(child_process_ptr), TypedLockMode::Write,),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(child_pagetable_ptr), TypedLockMode::Write,),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(l4_page), TypedLockMode::Write,),
        process_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(
                page_ptr2page_index(child_process_ptr),
            ).view().locking_thread()->Write_lock_id,
        pagetable_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(
                page_ptr2page_index(child_pagetable_ptr),
            ).view().locking_thread()->Write_lock_id,
        l4_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(
                page_ptr2page_index(l4_page),
            ).view().locking_thread()->Write_lock_id,
        final(krnl).prc_mp.dom()
            =~= old(krnl).prc_mp.dom().insert(child_process_ptr),
        forall|ptr: RwLockProcessPtr|
            #![trigger final(krnl).prc_mp.spec_index(ptr)]
            old(krnl).prc_mp.dom().contains(ptr) ==> final(krnl).prc_mp.spec_index(ptr) == old(krnl).prc_mp.spec_index(ptr),
        final(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().owning_container == child_container_ptr,
        final(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().container_depth == child_depth,
        final(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().parent is None,
        final(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().depth == 0,
        final(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().pagetable == child_pagetable_ptr,
        final(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().cr3 == l4_page,
        final(krnl).prc_mp.spec_index(child_process_ptr).view_rodata().view().pcid == root_pcid,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().pcid == root_pcid,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().pagetable == child_pagetable_ptr,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().iommu_table is None,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().pci_function_ref_counter == 0,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().owned_pci_functions.view().is_empty(),
        !final(krnl).prc_mp.spec_index(child_process_ptr).being_killed(),
        !final(krnl).prc_mp.spec_index(child_process_ptr).view().zombie,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().quota_4k == process_quota_4k,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().quota_2m == 0,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().quota_1g == 0,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().children.view().len() == 0,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().owned_threads.view().len() == 0,
        final(krnl).prc_mp.spec_index(child_process_ptr).view().parent_linkedlist_node.is_init(),
        final(krnl).prc_mp.spec_index(child_process_ptr).view_ghost().uppertree_seq.view().len() == 0,
        final(krnl).prc_mp.spec_index(child_process_ptr).view_ghost().subtree_set.view().is_empty(),
        final(krnl).pt_mp.dom()
            =~= old(krnl).pt_mp.dom().insert(child_pagetable_ptr),
        forall|ptr: RwLockPageTableRoot|
            #![trigger final(krnl).pt_mp.spec_index(ptr)]
            old(krnl).pt_mp.dom().contains(ptr) ==> final(krnl).pt_mp.spec_index(ptr) == old(krnl).pt_mp.spec_index(ptr),
        final(krnl).pt_mp.spec_index(child_pagetable_ptr).view().is_empty(),
        !final(krnl).pt_mp.spec_index(child_pagetable_ptr).being_killed(),
        final(krnl).pt_mp.spec_index(child_pagetable_ptr).view().proc_ptr == child_process_ptr,
        final(krnl).pt_mp.spec_index(child_pagetable_ptr).view().pcid is Some,
        final(krnl).pt_mp.spec_index(child_pagetable_ptr).view().pcid_value() == root_pcid,
        final(krnl).pt_mp.spec_index(child_pagetable_ptr).view().cr3 == l4_page,
        final(krnl).pt_mp.spec_index(child_pagetable_ptr).view().kernel_l4_end == old(krnl).dflt_pt.view().kernel_l4_end,
        final(krnl).pt_mp.spec_index(child_pagetable_ptr).view().page_closure() == set![l4_page],
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).process_lock_map().dom() == old(lctx).process_lock_map().dom().insert(child_process_ptr),
        forall|ptr: RwLockProcessPtr|
            #![trigger final(lctx).process_lock_map().get(ptr)]
            ptr != child_process_ptr ==> final(lctx).process_lock_map().get(ptr) == old(lctx).process_lock_map().get(ptr),
        final(lctx).pagetable_lock_map().dom() == old(lctx).pagetable_lock_map().dom().insert(child_pagetable_ptr),
        forall|ptr: RwLockPageTableRoot|
            #![trigger final(lctx).pagetable_lock_map().get(ptr)]
            ptr != child_pagetable_ptr ==> final(lctx).pagetable_lock_map().get(ptr) == old(lctx).pagetable_lock_map().get(ptr),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), child_process_ptr, TypedLockMode::Write,),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), child_pagetable_ptr, TypedLockMode::Write,),
        ret.0.view().state() is WriteLock,
        ret.0.view().thread_id() == final(lctx).thread_id(),
        ret.0.view().lock_id() == final(krnl).prc_mp.spec_index(child_process_ptr).locking_thread()->Write_lock_id,
        final(krnl).prc_mp.spec_index(child_process_ptr).write_lock_perm_match(&ret.0.view()),
        ret.1.view().state() is WriteLock,
        ret.1.view().thread_id() == final(lctx).thread_id(),
        ret.1.view().lock_id() == final(krnl).pt_mp.spec_index(child_pagetable_ptr).locking_thread()->Write_lock_id,
        staged_4k_page_chain(final(krnl).pg_arr, funding_pages),
        owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, final(krnl).pg_arr, final(lctx), container_head,),
        owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, final(krnl).pg_arr, final(lctx), pcid_allocator_head,),
{
    let process_index = page_ptr2page_index(child_process_ptr);
    let pagetable_index = page_ptr2page_index(child_pagetable_ptr);
    let l4_index = page_ptr2page_index(l4_page);
    let ghost pages_before_publish = krnl.pg_arr;
    let ghost lctx_before_publish = *lctx;
    proof {
        page_ptr_valid_imply_page_index_valid();
        assert({
            &&& process_index != pagetable_index
            &&& process_index != l4_index
            &&& pagetable_index != l4_index
        }) by { page_ptr2page_index_injective(); };
    }

    let default_pt = krnl.dflt_pt.borrow();
    let Tracked(l4_page_perm) =
        retype_owned_4k_page_for_new_container(
            &mut krnl.pg_arr,
            child_container_ptr,
            l4_page,
            Allocated4KPageState::PageTable {
                pagetable_root: child_pagetable_ptr,
            },
            Tracked(&mut *lctx),
            Tracked(l4_page_lock_perm),
        );
    let (l4_ptr, Tracked(mut l4_perm)) =
        page_perm_to_page_map(l4_page, Tracked(l4_page_perm));
    proof {
        vstd::set::lemma_set_insert_different(lctx_before_publish.page_lock_map().dom(), pagetable_index, l4_index,);
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), pagetable_index, TypedLockMode::Write,)) by { reveal(typed_lock_maps_inserted); reveal(typed_lock_map_contains_mode); };
    }
    default_pt.copy_kernel_entries_to_unpublished_root(
        l4_ptr,
        Tracked(&mut l4_perm),
    );
    proof {
        assert(default_pt.kernel_entries.view().len() == default_pt.kernel_l4_end) by { reveal(PageTable::kernel_entries_wf); };
    }
    let pagetable_value = PageTable::<PT_TYPE>::new(
        Some(root_pcid),
        Ghost(default_pt.kernel_entries.view()),
        l4_ptr,
        Tracked(l4_perm),
        default_pt.kernel_l4_end,
        child_process_ptr,
    );

    let ghost page_lock_map_before_pagetable = lctx.page_lock_map();
    proof { assert(pagetable_page_lock_perm.lock_id() == krnl.pg_arr.spec_index(pagetable_index).view().locking_thread()->Write_lock_id); }
    let Tracked(pagetable_perm) =
        retype_owned_4k_page_for_new_container(&mut krnl.pg_arr, child_container_ptr, child_pagetable_ptr, Allocated4KPageState::AsPageTableRoot, Tracked(&mut *lctx), Tracked(pagetable_page_lock_perm),);
    proof {
        vstd::set::lemma_set_insert_different(lctx_before_publish.page_lock_map().dom(), process_index, l4_index,);
        vstd::set::lemma_set_insert_different(page_lock_map_before_pagetable.dom(), process_index, pagetable_index,);
        assert(typed_lock_map_contains_mode(lctx.page_lock_map(), process_index, TypedLockMode::Write,)) by { reveal(typed_lock_maps_inserted); reveal(typed_lock_map_contains_mode); };
        assert(typed_lock_maps_aligned(krnl, lctx)) by { reveal(typed_lock_maps_aligned); };
    }
    let ghost pagetable_map_before_insert = krnl.pt_mp;
    let Tracked(child_pagetable_lock_perm) =
        krnl.retype_page_to_pagetable_and_insert(
            child_pagetable_ptr,
            pagetable_value,
            Tracked(pagetable_perm),
            Tracked(&mut *lctx),
        );
    let ghost pagetable_map_after_insert = krnl.pt_mp;
    proof {
        assert(
            pagetable_perms_wf(pagetable_map_before_insert) ==> pagetable_perms_wf(pagetable_map_after_insert)
        );
    }

    let mut process_value = Process::new_fresh(
        child_process_ptr,
        root_pcid,
        child_pagetable_ptr,
        child_depth,
        0,
    );
    process_value.quota_4k = process_quota_4k;
    let process_rodata = ReadOnlyNode::new(
        ProcessRO {
            owning_container: child_container_ptr,
            container_depth: child_depth,
            parent: None,
            depth: 0,
            pagetable: child_pagetable_ptr,
            cr3: l4_ptr,
            pcid: root_pcid,
        },
        Ghost(child_process_ptr),
    );
    let process_ghost = ProcessGhost {
        uppertree_seq: Ghost(Seq::empty()),
        subtree_set: Ghost(Set::empty()),
    };
    proof { assert(process_page_lock_perm.lock_id() == krnl.pg_arr.spec_index(process_index).view().locking_thread()->Write_lock_id); }
    let Tracked(process_perm) =
        retype_owned_4k_page_for_new_container(&mut krnl.pg_arr, child_container_ptr, child_process_ptr, Allocated4KPageState::AsProcess, Tracked(&mut *lctx), Tracked(process_page_lock_perm),);
    proof {
        assert(typed_lock_maps_aligned(krnl, lctx)) by {
            broadcast use vstd::set::lemma_set_insert_different; reveal(typed_lock_maps_aligned);
            reveal(LockedArray::typed_lock_map_aligned); reveal(LockedMap::typed_lock_map_aligned);
            reveal(UnLockedMap::typed_quota_lock_map_aligned); reveal(UnLockedMap::typed_cache_lock_map_aligned);
            reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
        };
    }
    let ghost process_map_before_insert = krnl.prc_mp;
    let Tracked(child_process_lock_perm) =
        krnl.retype_page_to_process_and_insert(
            child_process_ptr,
            process_value,
            process_rodata,
            process_ghost,
            Tracked(process_perm),
            Tracked(&mut *lctx),
        );
    proof {
        assert(old(krnl).prc_mp == process_map_before_insert);
        assert(
            process_perms_wf(old(krnl).prc_mp) ==> process_perms_wf(krnl.prc_mp)
        );
        assert(old(krnl).pt_mp == pagetable_map_before_insert);
        assert(krnl.pt_mp == pagetable_map_after_insert);
        assert(
            pagetable_perms_wf(old(krnl).pt_mp) ==> pagetable_perms_wf(krnl.pt_mp)
        );
        assert({
            &&& lctx.cpu_lock_map() == lctx_before_publish.cpu_lock_map()
            &&& lctx.pcid_needflush_lock_map() == lctx_before_publish.pcid_needflush_lock_map()
            &&& lctx.container_lock_map() == lctx_before_publish.container_lock_map()
            &&& lctx.thread_lock_map() == lctx_before_publish.thread_lock_map()
            &&& lctx.endpoint_lock_map() == lctx_before_publish.endpoint_lock_map()
            &&& lctx.scheduler_lock_map() == lctx_before_publish.scheduler_lock_map()
            &&& lctx.pcid_allocator_lock_map() == lctx_before_publish.pcid_allocator_lock_map()
            &&& lctx.cpu_set_lock_map() == lctx_before_publish.cpu_set_lock_map()
            &&& lctx.iommu_table_lock_map() == lctx_before_publish.iommu_table_lock_map()
            &&& lctx.allocator_4k_lock_maps() == lctx_before_publish.allocator_4k_lock_maps()
            &&& lctx.allocator_2m_lock_maps() == lctx_before_publish.allocator_2m_lock_maps()
            &&& lctx.allocator_1g_lock_maps() == lctx_before_publish.allocator_1g_lock_maps()
        }) by { reveal(typed_lock_maps_inserted); };
        assert(lctx.process_lock_map().dom() == lctx_before_publish.process_lock_map().dom().insert(child_process_ptr)) by { reveal(typed_lock_maps_inserted); };
        assert(lctx.pagetable_lock_map().dom() == lctx_before_publish.pagetable_lock_map().dom().insert(child_pagetable_ptr)) by { reveal(typed_lock_maps_inserted); };
        assert(staged_4k_page_chain(krnl.pg_arr, funding_pages)) by {
            staged_4k_page_chain_page_ptrs_valid(pages_before_publish, funding_pages,);
            page_ptr_seq_indices_excludes_page(funding_pages, child_process_ptr,);
            page_ptr_seq_indices_excludes_page(funding_pages, child_pagetable_ptr,);
            page_ptr_seq_indices_excludes_page(funding_pages, l4_page);
            broadcast use page_ptr_sequence_index_in_equal_set;
            broadcast use page_ptr_sequence_index_in_mapped_set;
            assert forall|i: int|
                #![trigger krnl.pg_arr.spec_index(
                    page_ptr2page_index(funding_pages.spec_index(i)),
                ).view().view().free_list]
                0 <= i < funding_pages.len()
                    implies {
                        &&& page_ptr_valid(funding_pages.spec_index(i))
                        &&& krnl.pg_arr.spec_index(page_ptr2page_index(
                            funding_pages.spec_index(i),
                        )).view().view().free_list == if i == 0 {
                            STAGED_4K_PAGE_CHAIN_END
                        } else {
                            funding_pages.spec_index(i - 1)
                        }
                    } by {
                assert(pages_before_publish.spec_index(page_ptr2page_index(
                    funding_pages.spec_index(i),
                )).view().view().free_list == if i == 0 {
                    STAGED_4K_PAGE_CHAIN_END
                } else {
                    funding_pages.spec_index(i - 1)
                }) by { reveal(staged_4k_page_chain); };
            };
            reveal(staged_4k_page_chain);
        };
        assert(owned_2m_tail_lock_perms_wf(*container_tail_lock_perms, krnl.pg_arr, lctx, container_head,)) by { reveal(owned_2m_tail_lock_perms_wf); reveal(page_2m_tail_indices); };
        assert(owned_2m_tail_lock_perms_wf(*pcid_allocator_tail_lock_perms, krnl.pg_arr, lctx, pcid_allocator_head,)) by { reveal(owned_2m_tail_lock_perms_wf); reveal(page_2m_tail_indices); };
        assert(krnl.pt_mp.spec_index(child_pagetable_ptr).view().page_closure() == set![l4_page]) by { vstd::set::axiom_set_ext_equal(krnl.pt_mp.spec_index(child_pagetable_ptr).view().page_closure(), set![l4_page],); };
        assert(!old(lctx).process_lock_map().dom().contains(child_process_ptr,)) by { reveal(typed_lock_maps_aligned); reveal(LockedMap::typed_lock_map_aligned); };
        assert(held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx),)) by {
            reveal(held_processes_unchanged); reveal(typed_lock_maps_aligned); reveal(LockedMap::typed_lock_map_aligned);
            broadcast use vstd::map::lemma_map_insert_domain; broadcast use vstd::set::lemma_set_insert_different;
        };
        assert(!old(lctx).pagetable_lock_map().dom().contains(child_pagetable_ptr,)) by { reveal(typed_lock_maps_aligned); reveal(LockedMap::typed_lock_map_aligned); };
        assert(held_pagetables_unchanged(old(krnl).pt_mp, krnl.pt_mp, old(lctx),)) by {
            reveal(held_pagetables_unchanged); reveal(typed_lock_maps_aligned); reveal(LockedMap::typed_lock_map_aligned);
            broadcast use vstd::map::lemma_map_insert_domain; broadcast use vstd::set::lemma_set_insert_different;
        };
    }
    (
        Tracked(child_process_lock_perm),
        Tracked(child_pagetable_lock_perm),
    )
}


}
