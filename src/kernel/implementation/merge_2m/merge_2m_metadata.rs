#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::merge_2m_metadata_eof::*;

verus! {
// The managed physical arena supplies one provenance for each aligned 2M region.
// The exact tokens recorded in its 512 free 4K metadata cells are consumed here;
// this boundary neither joins arbitrary heap allocations nor touches the bytes.
#[verifier::external_body]
fn retype_managed_4k_region_to_2m(Ghost(head): Ghost<PageIndex>, Ghost(source): Ghost<PageLockedArray>,
    Tracked(perms): Tracked<Map<usize, PagePerm4k>>) -> (ret: Tracked<PagePerm2m>)
    requires
        page_index_2m_valid(head),
        page_array_wf(source),
        perms.dom() == Set::<usize>::range(1, 512).insert(0),
        forall|i: usize| #![trigger perms.spec_index(i)] i < 512 ==> {
            &&& source.spec_index((head + i) as usize).view().view().state is Free4k
            &&& source.spec_index((head + i) as usize).view().view().perm_4k.view() == Some(perms.spec_index(i))
            &&& perms.spec_index(i).is_init()
            &&& perms.spec_index(i).addr() == (head + i) * PAGE_SZ_4K
        },
    ensures
        ret.view().is_init(),
        ret.view().addr() == head * PAGE_SZ_4K,
        ret.view().value().view().len() == PAGE_SZ_2M,
        forall|i: usize| #![trigger ret.view().value().view().subrange(i * PAGE_SZ_4K, (i + 1) * PAGE_SZ_4K)] i < 512 ==>
            ret.view().value().view().subrange(i * PAGE_SZ_4K, (i + 1) * PAGE_SZ_4K) == perms.spec_index(i).value().view(),
{
    Tracked::assume_new()
}

pub fn merge_2m_tail(page: &mut Page, Tracked(node): Tracked<PointsTo<Node<PagePtr>>>) -> (ret: Tracked<PagePerm4k>)
    requires
        old(page).inv(),
        old(page).state is Free4k,
        node.is_init(),
        node.addr() == old(page).free_list_node_storage.addr(),
    ensures
        final(page).inv(),
        merge_2m_tail_eof_transition_framing(*old(page), *final(page)),
        ret.view() == old(page).perm_4k.view().unwrap(),
        ret.view().is_init(),
        ret.view().addr() == old(page).addr,
        final(page).perm_2m.view().is_none(),
        final(page).current_lock_major() == old(page).current_lock_major(),
{
    let ret = take_perm_4k(page);
    page.free_list_node_storage.put(Tracked(node));
    page.state = PageState::Merged2m;
    proof { merge_2m_tail_eof_implies_page_inv(*old(page), *page); }
    ret
}

pub fn merge_2m_head(page: &mut Page, Ghost(head): Ghost<PageIndex>, Ghost(allocator): Ghost<RwLockPageAllocatorPtr>,
    Ghost(source): Ghost<PageLockedArray>, Tracked(tail_perms): Tracked<Map<usize, PagePerm4k>>)
    requires
        old(page).inv(),
        old(page).state is Free4k,
        page_index_2m_valid(head),
        page_array_wf(source),
        *old(page) == source.spec_index(head).view().view(),
        old(page).addr == head * PAGE_SZ_4K,
        tail_perms.dom() == Set::<usize>::range(1, 512),
        forall|i: usize| #![trigger tail_perms.spec_index(i)] 1 <= i < 512 ==> {
            &&& source.spec_index((head + i) as usize).view().view().state is Free4k
            &&& source.spec_index((head + i) as usize).view().view().perm_4k.view() == Some(tail_perms.spec_index(i))
            &&& tail_perms.spec_index(i).is_init()
            &&& tail_perms.spec_index(i).addr() == (head + i) * PAGE_SZ_4K
        },
    ensures
        final(page).inv(),
        merge_2m_head_eof_transition_framing(*old(page), *final(page), allocator),
        final(page).perm_2m.view().is_some(),
        final(page).perm_2m.view().unwrap().is_init(),
        final(page).perm_2m.view().unwrap().value().view().len() == PAGE_SZ_2M,
        final(page).current_lock_major() == old(page).current_lock_major(),
        forall|i: usize| #![trigger final(page).perm_2m.view().unwrap().value().view().subrange(i * PAGE_SZ_4K, (i + 1) * PAGE_SZ_4K)] i < 512 ==>
            final(page).perm_2m.view().unwrap().value().view().subrange(i * PAGE_SZ_4K, (i + 1) * PAGE_SZ_4K) == if i == 0 {
                old(page).perm_4k.view().unwrap().value().view()
            } else {
                tail_perms.spec_index(i).value().view()
            },
{
    let Tracked(head_perm) = take_perm_4k(page);
    let tracked mut perms = tail_perms;
    proof { perms.tracked_insert(0, head_perm); }
    let Tracked(perm) = retype_managed_4k_region_to_2m(Ghost(head), Ghost(source), Tracked(perms));
    page.perm_2m = Tracked(Some(perm));
    page.state = PageState::Free2m { allocator_ptr: Ghost(allocator), state: FreePageAllocatorState::GlobalList };
    proof { merge_2m_head_eof_implies_page_inv(*old(page), *page, allocator); }
}
}
