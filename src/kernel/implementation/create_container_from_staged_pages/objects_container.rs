use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
pub(super) fn publish_new_container_pcid_allocator_and_container(
    krnl: &mut KernelK, child_pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid_allocator_value: PcidAllocator,
    child_container_ptr: RwLockContainerPtr, container_value: Container, container_rodata: ReadOnlyNode<ContainerRO>,
    container_ghost: ContainerGhost, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(pcid_allocator_perm): Tracked<PagePerm2m>,
    Tracked(container_perm): Tracked<PagePerm2m>,
) -> (ret: (Tracked<LockPerm>, Tracked<LockPerm>))
    requires
        old(krnl).pcid_allc_mp.perms_wf(),
        old(krnl).ctn_mp.perms_wf(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        pcid_allocator_value.inv(),
        container_value.inv(),
        !old(krnl).pcid_allc_mp.dom().contains(child_pcid_allocator_ptr),
        !old(krnl).ctn_mp.dom().contains(child_container_ptr),
        pcid_allocator_perm.is_init(),
        pcid_allocator_perm.addr() == child_pcid_allocator_ptr,
        container_perm.is_init(),
        container_perm.addr() == child_container_ptr,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        lock_id_set_aligned(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)), *final(krnl) == (KernelK {
            pcid_allc_mp: final(krnl).pcid_allc_mp,
            ctn_mp: final(krnl).ctn_mp,
            ..*old(krnl)
        }),
        final(krnl).pcid_allc_mp.perms_wf(),
        pcid_allocator_perms_wf(old(krnl).pcid_allc_mp) ==> pcid_allocator_perms_wf(final(krnl).pcid_allc_mp),
        final(krnl).ctn_mp.perms_wf(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).pcid_allocator_lock_map().dom() == old(lctx).pcid_allocator_lock_map().dom().insert(child_pcid_allocator_ptr),
        forall|ptr: RwLockPcidAllocatorPtr|
            #![trigger final(lctx).pcid_allocator_lock_map().get(ptr)]
            ptr != child_pcid_allocator_ptr ==> final(lctx).pcid_allocator_lock_map().get(ptr) == old(lctx).pcid_allocator_lock_map().get(ptr),
        final(lctx).container_lock_map().dom() == old(lctx).container_lock_map().dom().insert(child_container_ptr),
        forall|ptr: RwLockContainerPtr|
            #![trigger final(lctx).container_lock_map().get(ptr)]
            ptr != child_container_ptr ==> final(lctx).container_lock_map().get(ptr) == old(lctx).container_lock_map().get(ptr),
        final(krnl).pcid_allc_mp.dom()
            =~= old(krnl).pcid_allc_mp.dom().insert(child_pcid_allocator_ptr),
        final(krnl).pcid_allc_mp.spec_index(child_pcid_allocator_ptr).view() == pcid_allocator_value,
        forall|ptr: RwLockPcidAllocatorPtr|
            #![trigger final(krnl).pcid_allc_mp.spec_index(ptr)]
            old(krnl).pcid_allc_mp.dom().contains(ptr) ==> final(krnl).pcid_allc_mp.spec_index(ptr) == old(krnl).pcid_allc_mp.spec_index(ptr),
        final(krnl).ctn_mp.dom()
            =~= old(krnl).ctn_mp.dom().insert(child_container_ptr),
        final(krnl).ctn_mp.spec_index(child_container_ptr).is_init(),
        !final(krnl).ctn_mp.spec_index(child_container_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(child_container_ptr).view() == container_value,
        final(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata() == container_rodata,
        final(krnl).ctn_mp.spec_index(child_container_ptr).view_ghost() == container_ghost,
        forall|ptr: RwLockContainerPtr|
            #![trigger final(krnl).ctn_mp.spec_index(ptr)]
            old(krnl).ctn_mp.dom().contains(ptr) ==> final(krnl).ctn_mp.spec_index(ptr) == old(krnl).ctn_mp.spec_index(ptr),
        ret.0.view().state() is WriteLock,
        ret.0.view().thread_id() == final(lctx).thread_id(),
        ret.0.view().lock_id() == final(krnl).pcid_allc_mp.spec_index(
                child_pcid_allocator_ptr,
            ).locking_thread()->Write_lock_id,
        ret.1.view().state() is WriteLock,
        ret.1.view().thread_id() == final(lctx).thread_id(),
        ret.1.view().lock_id() == final(krnl).ctn_mp.spec_index(child_container_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).pcid_allocator_lock_map(), child_pcid_allocator_ptr, TypedLockMode::Write,),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), child_container_ptr, TypedLockMode::Write,),
{
    let ghost lctx_before_publish = *lctx;
    proof {
        assert(lctx.typed_lock_entry(KernelObjId::PcidAllocator(child_pcid_allocator_ptr),) is None) by { reveal(LocalContext::typed_lock_entry); reveal(typed_lock_maps_aligned); reveal(LockedMap::typed_lock_map_aligned); };
    }
    let Tracked(child_pcid_allocator_lock_perm) =
        krnl.pcid_allc_mp.retype_2m_and_insert(
            child_pcid_allocator_ptr,
            pcid_allocator_value,
            (),
            Ghost(()),
            Tracked(pcid_allocator_perm),
            Tracked(&mut *lctx),
            Ghost(KernelObjId::PcidAllocator(child_pcid_allocator_ptr)),
        );
    proof {
        assert(krnl.pcid_allc_mp.typed_lock_map_aligned(lctx.pcid_allocator_lock_map(), lctx.thread_id(),)) by {
            broadcast use vstd::set::lemma_set_insert_different; reveal(typed_lock_maps_inserted);
            reveal(LockedMap::typed_lock_map_aligned); broadcast use vstd::map::lemma_map_insert_domain;
            broadcast use vstd::map::lemma_map_new_index;
        };
        assert(typed_lock_maps_aligned(krnl, lctx)) by {
            broadcast use vstd::set::lemma_set_insert_different;
            reveal(typed_lock_maps_aligned);
            reveal(LockedArray::typed_lock_map_aligned);
            reveal(LockedMap::typed_lock_map_aligned);
            reveal(UnLockedMap::typed_quota_lock_map_aligned);
            reveal(UnLockedMap::typed_cache_lock_map_aligned);
            reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
            broadcast use vstd::map::lemma_map_insert_domain;
            broadcast use vstd::map::lemma_map_new_index;
        };
        assert(lctx.typed_lock_entry(KernelObjId::Container(child_container_ptr),) is None) by { reveal(LocalContext::typed_lock_entry); reveal(typed_lock_maps_aligned); reveal(LockedMap::typed_lock_map_aligned); };
    }
    let Tracked(child_container_lock_perm) =
        krnl.ctn_mp.retype_2m_and_insert(
            child_container_ptr,
            container_value,
            container_rodata,
            Ghost(container_ghost),
            Tracked(container_perm),
            Tracked(&mut *lctx),
            Ghost(KernelObjId::Container(child_container_ptr)),
        );
    proof {
        assert(krnl.ctn_mp.typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id(),)) by {
            broadcast use vstd::set::lemma_set_insert_different; reveal(typed_lock_maps_inserted);
            reveal(LockedMap::typed_lock_map_aligned); broadcast use vstd::map::lemma_map_insert_domain;
            broadcast use vstd::map::lemma_map_new_index;
        };
        assert(typed_lock_maps_aligned(krnl, lctx)) by {
            broadcast use vstd::set::lemma_set_insert_different;
            reveal(typed_lock_maps_aligned);
            reveal(LockedArray::typed_lock_map_aligned);
            reveal(LockedMap::typed_lock_map_aligned);
            reveal(UnLockedMap::typed_quota_lock_map_aligned);
            reveal(UnLockedMap::typed_cache_lock_map_aligned);
            reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
            broadcast use vstd::map::lemma_map_insert_domain;
            broadcast use vstd::map::lemma_map_new_index;
        };
        assert({
            &&& lctx.cpu_lock_map() == lctx_before_publish.cpu_lock_map()
            &&& lctx.pcid_needflush_lock_map() == lctx_before_publish.pcid_needflush_lock_map()
            &&& lctx.page_lock_map() == lctx_before_publish.page_lock_map()
            &&& lctx.process_lock_map() == lctx_before_publish.process_lock_map()
            &&& lctx.thread_lock_map() == lctx_before_publish.thread_lock_map()
            &&& lctx.endpoint_lock_map() == lctx_before_publish.endpoint_lock_map()
            &&& lctx.scheduler_lock_map() == lctx_before_publish.scheduler_lock_map()
            &&& lctx.cpu_set_lock_map() == lctx_before_publish.cpu_set_lock_map()
            &&& lctx.pagetable_lock_map() == lctx_before_publish.pagetable_lock_map()
            &&& lctx.iommu_table_lock_map() == lctx_before_publish.iommu_table_lock_map()
            &&& lctx.allocator_4k_lock_maps() == lctx_before_publish.allocator_4k_lock_maps()
            &&& lctx.allocator_2m_lock_maps() == lctx_before_publish.allocator_2m_lock_maps()
            &&& lctx.allocator_1g_lock_maps() == lctx_before_publish.allocator_1g_lock_maps()
        }) by { reveal(typed_lock_maps_inserted); };
        assert(lctx.pcid_allocator_lock_map().dom() == lctx_before_publish.pcid_allocator_lock_map().dom().insert(child_pcid_allocator_ptr)) by { reveal(typed_lock_maps_inserted); };
        assert(lctx.container_lock_map().dom() == lctx_before_publish.container_lock_map().dom().insert(child_container_ptr)) by { reveal(typed_lock_maps_inserted); };
        if pcid_allocator_perms_wf(old(krnl).pcid_allc_mp) {
            assert(pcid_allocator_perms_wf(krnl.pcid_allc_mp)) by { reveal(pcid_allocator_perms_wf); };
        }
    }
    (
        Tracked(child_pcid_allocator_lock_perm),
        Tracked(child_container_lock_perm),
    )
}

}
