#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::split_2m_metadata_eof::*;

verus! {
// The managed arena's aligned parent permission is consumed exactly once. The
// child permissions retain its provenance and bytes; this does no physical write.
#[verifier::external_body]
fn retype_managed_2m_region_to_4k(Ghost(head): Ghost<PageIndex>, Ghost(source): Ghost<PageLockedArray>,
    Tracked(perm): Tracked<PagePerm2m>) -> (ret: Tracked<Map<usize, PagePerm4k>>)
    requires
        page_index_2m_valid(head),
        page_array_wf(source),
        source.spec_index(head).view().view().state is Free2m,
        source.spec_index(head).view().view().perm_2m.view() == Some(perm),
        perm.is_init(),
        perm.addr() == head * PAGE_SZ_4K,
    ensures
        ret.view().dom() == Set::<usize>::range(1, 512).insert(0),
        forall|i: usize| #![trigger ret.view().spec_index(i)] i < 512 ==> {
            &&& ret.view().spec_index(i).is_init()
            &&& ret.view().spec_index(i).addr() == (head + i) * PAGE_SZ_4K
            &&& ret.view().spec_index(i).value().view() == perm.value().view().subrange(i * PAGE_SZ_4K, (i + 1) * PAGE_SZ_4K)
        },
{
    Tracked::assume_new()
}

pub fn split_2m_head(page: &mut Page, Ghost(head): Ghost<PageIndex>, Ghost(allocator): Ghost<RwLockPageAllocatorPtr>,
    Ghost(source): Ghost<PageLockedArray>) -> (ret: Tracked<Map<usize, PagePerm4k>>)
    requires
        old(page).inv(),
        old(page).state is Free2m,
        page_index_2m_valid(head),
        page_array_wf(source),
        *old(page) == source.spec_index(head).view().view(),
        old(page).addr == head * PAGE_SZ_4K,
    ensures
        final(page).inv(),
        split_2m_head_eof_transition_framing(*old(page), *final(page), allocator),
        ret.view().dom() == Set::<usize>::range(1, 512),
        forall|i: usize| #![trigger ret.view().spec_index(i)] 1 <= i < 512 ==> {
            &&& ret.view().spec_index(i).is_init()
            &&& ret.view().spec_index(i).addr() == (head + i) * PAGE_SZ_4K
            &&& ret.view().spec_index(i).value().view() == old(page).perm_2m.view().unwrap().value().view().subrange(i * PAGE_SZ_4K, (i + 1) * PAGE_SZ_4K)
        },
        final(page).perm_4k.view().unwrap().value().view() == old(page).perm_2m.view().unwrap().value().view().subrange(0, PAGE_SZ_4K as int),
        final(page).current_lock_major() == old(page).current_lock_major(),
{
    let Tracked(parent) = take_perm_2m(page);
    let Tracked(mut children) = retype_managed_2m_region_to_4k(Ghost(head), Ghost(source), Tracked(parent));
    let tracked child = children.tracked_remove(0);
    page.perm_4k = Tracked(Some(child));
    page.state = PageState::Free4k { allocator_ptr: Ghost(allocator), state: FreePageAllocatorState::GlobalList };
    proof { split_2m_head_eof_implies_page_inv(*old(page), *page, allocator); }
    Tracked(children)
}

pub fn split_2m_tail(page: &mut Page, _allocator: RwLockPageAllocatorPtr, owner: RwLockContainerPtr,
    Tracked(perm): Tracked<PagePerm4k>) -> (ret: (usize, Tracked<PointsTo<Node<PagePtr>>>))
    requires
        old(page).inv(),
        old(page).state is Merged2m,
        perm.is_init(),
        perm.addr() == old(page).addr,
    ensures
        final(page).inv(),
        split_2m_tail_eof_transition_framing(*old(page), *final(page), _allocator, owner),
        final(page).perm_4k.view() == Some(perm),
        ret.0 == old(page).free_list_node_storage.addr(),
        ret.1.view().is_init(),
        ret.1.view().addr() == ret.0,
        ret.1.view().value().view() == old(page).addr,
        final(page).current_lock_major() == old(page).current_lock_major(),
{
    let (node_addr, mut node_perm) = page.free_list_node_storage.take();
    node_update_value(node_addr, &mut node_perm, page.addr);
    page.perm_4k = Tracked(Some(perm));
    page.owning_container = owner;
    page.state = PageState::Free4k { allocator_ptr: Ghost(_allocator), state: FreePageAllocatorState::GlobalList };
    proof { split_2m_tail_eof_implies_page_inv(*old(page), *page, _allocator, owner); }
    (node_addr, node_perm)
}
}
