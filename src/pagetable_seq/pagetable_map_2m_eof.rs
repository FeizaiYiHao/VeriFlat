use vstd::prelude::*;
verus! {
use crate::*;
use super::pagetable_spec::*;
use super::entry::*;

impl<const TABLE_TYPE: PTType> PageTable<TABLE_TYPE> {
    /// Operation-state summary of `map_2m_page`: entry `target_l2i` of the L2 map `target_l2_p` now maps `target_entry` as a
    /// 2M page and the kernel 2M mapping records it at that address; every other field is unchanged.
    #[verifier::opaque]
    pub open spec fn map_2m_page_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry) -> bool {
        &&& post == (Self { l2_tables: post.l2_tables, mapping_2m: post.mapping_2m, ..pre })
        &&& post.mapping_2m() == pre.mapping_2m().insert(spec_index2va((target_l4i, target_l3i, target_l2i, 0)), target_entry)
        &&& post.l2_tables.view() =~= pre.l2_tables.view().insert(target_l2_p, post.l2_tables.view().spec_index(target_l2_p))
        &&& post.l2_tables.view().spec_index(target_l2_p).addr() == target_l2_p
        &&& post.l2_tables.view().spec_index(target_l2_p).is_init()
        &&& post.l2_tables.view().spec_index(target_l2_p).value().wf()
        &&& forall|i: usize| #![trigger pre.l2_tables.view().spec_index(target_l2_p).value().spec_index(i)] #![trigger post.l2_tables.view().spec_index(target_l2_p).value().spec_index(i)]
            pei_valid(i) && i != target_l2i ==> post.l2_tables.view().spec_index(target_l2_p).value().spec_index(i) =~= pre.l2_tables.view().spec_index(target_l2_p).value().spec_index(i)
        &&& post.l2_tables.view().spec_index(target_l2_p).value().spec_index(target_l2i) =~= (PageEntry { addr: target_entry.addr, perm: PageEntryPerm {
            present: true, ps: true, write: target_entry.write, execute_disable: target_entry.execute_disable, user: true, kernel_present: true } })
    }

    /// EOF closure of `map_2m_page`: every page-table invariant leaf.
    pub(super) proof fn map_2m_page_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None || pre.mapping_2m().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, 0))) == false,
            pre.page_closure().contains(target_entry.addr) == false,
            page_ptr_2m_valid(target_entry.addr),
            page_table_key_2m_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, 0,))),
            target_entry.present,
            pre.l2_tables.view().dom().contains(target_l2_p),
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.wf(),
    {
        Self::map_2m_page_eof_wf_l4(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
        Self::map_2m_page_eof_wf_l3(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
        Self::map_2m_page_eof_wf_l2(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
        Self::map_2m_page_eof_wf_l1(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
        Self::map_2m_page_eof_disjoint_l4(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
        Self::map_2m_page_eof_disjoint_l3(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
        Self::map_2m_page_eof_disjoint_l2(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
        Self::map_2m_page_eof_wf_mapping_4k(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
        Self::map_2m_page_eof_wf_mapping_2m(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
        Self::map_2m_page_eof_wf_mapping_1g(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
        Self::map_2m_page_eof_user_only(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
        Self::map_2m_page_eof_rwx_upper_level_entries(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
        Self::map_2m_page_eof_table_pages_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
        Self::map_2m_page_eof_tables_reachable_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
        Self::map_2m_page_eof_kernel_entries_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
        Self::map_2m_page_eof_va_addr_valid_and_pcid_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
    }

    /// EOF closure of `map_2m_page`: `wf_l4`.
    proof fn map_2m_page_eof_wf_l4(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None || pre.mapping_2m().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, 0))) == false,
            pre.page_closure().contains(target_entry.addr) == false,
            page_ptr_2m_valid(target_entry.addr),
            page_table_key_2m_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, 0,))),
            target_entry.present,
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.wf_l4(),
    {
        reveal(PageTable::map_2m_page_eof_transition_framing);
        assert(post.wf_l4()) by { reveal(PageTable::wf_l4); };
    }

    /// EOF closure of `map_2m_page`: `wf_l3`.
    proof fn map_2m_page_eof_wf_l3(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None || pre.mapping_2m().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, 0))) == false,
            pre.page_closure().contains(target_entry.addr) == false,
            page_ptr_2m_valid(target_entry.addr),
            page_table_key_2m_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, 0,))),
            target_entry.present,
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.wf_l3(),
    {
        reveal(PageTable::map_2m_page_eof_transition_framing);
        assert(post.wf_l3()) by { reveal(PageTable::wf_l3); };
    }

    /// EOF closure of `map_2m_page`: `wf_l2`.
    proof fn map_2m_page_eof_wf_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None || pre.mapping_2m().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, 0))) == false,
            pre.page_closure().contains(target_entry.addr) == false,
            page_ptr_2m_valid(target_entry.addr),
            page_table_key_2m_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, 0,))),
            target_entry.present,
            pre.l2_tables.view().dom().contains(target_l2_p),
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.wf_l2(),
    {
        reveal(PageTable::map_2m_page_eof_transition_framing);
        assert(post.wf_l2()) by { reveal(PageTable::wf_l2); };
    }

    /// EOF closure of `map_2m_page`: `wf_l1`.
    proof fn map_2m_page_eof_wf_l1(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None || pre.mapping_2m().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, 0))) == false,
            pre.page_closure().contains(target_entry.addr) == false,
            page_ptr_2m_valid(target_entry.addr),
            page_table_key_2m_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, 0,))),
            target_entry.present,
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.wf_l1(),
    {
        reveal(PageTable::map_2m_page_eof_transition_framing);
        assert(post.wf_l1()) by { reveal(PageTable::wf_l1); };
    }

    /// EOF closure of `map_2m_page`: `disjoint_l4`.
    proof fn map_2m_page_eof_disjoint_l4(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None || pre.mapping_2m().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, 0))) == false,
            pre.page_closure().contains(target_entry.addr) == false,
            page_ptr_2m_valid(target_entry.addr),
            page_table_key_2m_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, 0,))),
            target_entry.present,
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.disjoint_l4(),
    {
        reveal(PageTable::map_2m_page_eof_transition_framing);
        assert(post.disjoint_l4()) by { reveal(PageTable::disjoint_l4); };
    }

    /// EOF closure of `map_2m_page`: `disjoint_l3`.
    proof fn map_2m_page_eof_disjoint_l3(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None || pre.mapping_2m().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, 0))) == false,
            pre.page_closure().contains(target_entry.addr) == false,
            page_ptr_2m_valid(target_entry.addr),
            page_table_key_2m_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, 0,))),
            target_entry.present,
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.disjoint_l3(),
    {
        reveal(PageTable::map_2m_page_eof_transition_framing);
        assert(post.disjoint_l3()) by { reveal(PageTable::disjoint_l3); };
    }

    /// EOF closure of `map_2m_page`: `disjoint_l2`.
    proof fn map_2m_page_eof_disjoint_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None || pre.mapping_2m().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, 0))) == false,
            pre.page_closure().contains(target_entry.addr) == false,
            page_ptr_2m_valid(target_entry.addr),
            page_table_key_2m_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, 0,))),
            target_entry.present,
            pre.l2_tables.view().dom().contains(target_l2_p),
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.disjoint_l2(),
    {
        reveal(PageTable::map_2m_page_eof_transition_framing);
        assert(post.disjoint_l2()) by { reveal(PageTable::disjoint_l2); };
    }

    /// EOF closure of `map_2m_page`: `wf_mapping_4k`.
    proof fn map_2m_page_eof_wf_mapping_4k(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None || pre.mapping_2m().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, 0))) == false,
            pre.page_closure().contains(target_entry.addr) == false,
            page_ptr_2m_valid(target_entry.addr),
            page_table_key_2m_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, 0,))),
            target_entry.present,
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.wf_mapping_4k(),
    {
        reveal(PageTable::map_2m_page_eof_transition_framing);
        assert(post.wf_mapping_4k()) by { reveal(PageTable::wf_mapping_4k); };
    }

    /// EOF closure of `map_2m_page`: `wf_mapping_2m`.
    proof fn map_2m_page_eof_wf_mapping_2m(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None || pre.mapping_2m().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, 0))) == false,
            pre.page_closure().contains(target_entry.addr) == false,
            page_ptr_2m_valid(target_entry.addr),
            page_table_key_2m_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, 0,))),
            target_entry.present,
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.wf_mapping_2m(),
    {
        reveal(PageTable::map_2m_page_eof_transition_framing);
        assert(post.wf_mapping_2m()) by { reveal(PageTable::wf_mapping_2m); spec_index2va_injective(); reveal(PageTable::wf_l4); reveal(PageTable::disjoint_l4); reveal(PageTable::disjoint_l3); };
    }

    /// EOF closure of `map_2m_page`: `wf_mapping_1g`.
    proof fn map_2m_page_eof_wf_mapping_1g(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None || pre.mapping_2m().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, 0))) == false,
            pre.page_closure().contains(target_entry.addr) == false,
            page_ptr_2m_valid(target_entry.addr),
            page_table_key_2m_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, 0,))),
            target_entry.present,
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.wf_mapping_1g(),
    {
        reveal(PageTable::map_2m_page_eof_transition_framing);
        assert(post.wf_mapping_1g()) by { reveal(PageTable::wf_mapping_1g); };
    }

    /// EOF closure of `map_2m_page`: `user_only`.
    proof fn map_2m_page_eof_user_only(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None || pre.mapping_2m().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, 0))) == false,
            pre.page_closure().contains(target_entry.addr) == false,
            page_ptr_2m_valid(target_entry.addr),
            page_table_key_2m_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, 0,))),
            target_entry.present,
            pre.l2_tables.view().dom().contains(target_l2_p),
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.user_only(),
    {
        reveal(PageTable::map_2m_page_eof_transition_framing);
        assert(post.user_only()) by { reveal(PageTable::user_only); };
    }

    /// EOF closure of `map_2m_page`: `rwx_upper_level_entries`.
    proof fn map_2m_page_eof_rwx_upper_level_entries(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None || pre.mapping_2m().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, 0))) == false,
            pre.page_closure().contains(target_entry.addr) == false,
            page_ptr_2m_valid(target_entry.addr),
            page_table_key_2m_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, 0,))),
            target_entry.present,
            pre.l2_tables.view().dom().contains(target_l2_p),
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.rwx_upper_level_entries(),
    {
        reveal(PageTable::map_2m_page_eof_transition_framing);
        assert(post.rwx_upper_level_entries()) by { reveal(PageTable::rwx_upper_level_entries); };
    }

    /// EOF closure of `map_2m_page`: `table_pages_wf`.
    proof fn map_2m_page_eof_table_pages_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None || pre.mapping_2m().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, 0))) == false,
            pre.page_closure().contains(target_entry.addr) == false,
            page_ptr_2m_valid(target_entry.addr),
            page_table_key_2m_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, 0,))),
            target_entry.present,
            pre.l2_tables.view().dom().contains(target_l2_p),
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.table_pages_wf(),
    {
        reveal(PageTable::map_2m_page_eof_transition_framing);
        assert(post.table_pages_wf()) by { reveal(PageTable::table_pages_wf); };
    }

    /// EOF closure of `map_2m_page`: `tables_reachable_wf`.
    proof fn map_2m_page_eof_tables_reachable_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None || pre.mapping_2m().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, 0))) == false,
            pre.page_closure().contains(target_entry.addr) == false,
            page_ptr_2m_valid(target_entry.addr),
            page_table_key_2m_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, 0,))),
            target_entry.present,
            pre.l2_tables.view().dom().contains(target_l2_p),
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.tables_reachable_wf(),
    {
        reveal(PageTable::map_2m_page_eof_transition_framing);
        assert(post.tables_reachable_wf()) by { reveal(PageTable::tables_reachable_wf); };
    }

    /// EOF closure of `map_2m_page`: `kernel_entries_wf`.
    proof fn map_2m_page_eof_kernel_entries_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None || pre.mapping_2m().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, 0))) == false,
            pre.page_closure().contains(target_entry.addr) == false,
            page_ptr_2m_valid(target_entry.addr),
            page_table_key_2m_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, 0,))),
            target_entry.present,
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.kernel_entries_wf(),
    {
        reveal(PageTable::map_2m_page_eof_transition_framing);
        assert(post.kernel_entries_wf()) by { reveal(PageTable::kernel_entries_wf); };
    }

    /// EOF closure of `map_2m_page`: `va_addr_valid`, `pcid_wf`, and `did_wf`.
    proof fn map_2m_page_eof_va_addr_valid_and_pcid_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None || pre.mapping_2m().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, 0))) == false,
            pre.page_closure().contains(target_entry.addr) == false,
            page_ptr_2m_valid(target_entry.addr),
            page_table_key_2m_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, 0,))),
            target_entry.present,
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.va_addr_valid(),
            post.pcid_wf(),
            post.did_wf(),
    {
        reveal(PageTable::map_2m_page_eof_transition_framing);
    }
}
} // verus!
