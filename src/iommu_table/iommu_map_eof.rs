use vstd::prelude::*;
verus! {
use crate::*;
use super::entry::*;
use super::page_map::*;

impl IommuTable {
    /// Operation-state summary of `map_4k_page`: entry `target_l1i` of the L1 map `target_l1_p` now maps `target_entry` and the kernel 4K mapping records it at that address; every other field is unchanged.
    #[verifier::opaque]
    pub open spec fn map_4k_page_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry) -> bool {
        &&& post == (Self { l1_tables: post.l1_tables, mapping_4k: post.mapping_4k, ..pre })
        &&& post.l1_tables.view().dom() == pre.l1_tables.view().dom()
        &&& forall|p: PageMapPtr| #![trigger post.l1_tables.view().spec_index(p)] pre.l1_tables.view().dom().contains(p) && p != target_l1_p ==> post.l1_tables.view().spec_index(p) == pre.l1_tables.view().spec_index(p)
        &&& post.l1_tables.view().spec_index(target_l1_p).addr() == target_l1_p
        &&& post.l1_tables.view().spec_index(target_l1_p).is_init()
        &&& post.l1_tables.view().spec_index(target_l1_p).value().iommu_wf()
        &&& forall|i: usize| #![trigger post.l1_tables.view().spec_index(target_l1_p).value().spec_index(i)] pei_valid(i) && i != target_l1i ==> post.l1_tables.view().spec_index(target_l1_p).value().spec_index(i) =~= pre.l1_tables.view().spec_index(target_l1_p).value().spec_index(i)
        &&& post.l1_tables.view().spec_index(target_l1_p).value().spec_index(target_l1i) =~= (PageEntry { addr: target_entry.addr,
            perm: PageEntryPerm { is_io: target_entry.is_io, present: true, ps: false, write: target_entry.write, execute_disable: target_entry.execute_disable, user: false, kernel_present: true } })
        &&& post.mapping_4k() == pre.mapping_4k().insert(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)), target_entry)
    }

    /// EOF closure of `map_4k_page`: every page-table invariant leaf.
    pub(super) proof fn map_4k_page_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            iova_4k_valid(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            !target_entry.is_io,
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.wf(),
    {
        Self::map_4k_page_eof_wf_l4(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_wf_l3(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_wf_l2(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_wf_l1(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_disjoint_l4(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_disjoint_l3(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_disjoint_l2(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_wf_mapping_4k(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_user_only(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_rwx_upper_level_entries(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_table_pages_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_tables_reachable_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_va_addr_valid_and_did_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
    }

    /// EOF closure of `map_4k_page`: `wf_l4`.
    proof fn map_4k_page_eof_wf_l4(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            iova_4k_valid(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            !target_entry.is_io,
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.wf_l4(),
    {
        reveal(IommuTable::map_4k_page_eof_transition_framing);
        assert(post.wf_l4()) by { reveal(IommuTable::wf_l4); };
    }

    /// EOF closure of `map_4k_page`: `wf_l3`.
    proof fn map_4k_page_eof_wf_l3(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            iova_4k_valid(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            !target_entry.is_io,
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.wf_l3(),
    {
        reveal(IommuTable::map_4k_page_eof_transition_framing);
        assert(post.wf_l3()) by { reveal(IommuTable::wf_l3); };
    }

    /// EOF closure of `map_4k_page`: `wf_l2`.
    proof fn map_4k_page_eof_wf_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            iova_4k_valid(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            !target_entry.is_io,
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.wf_l2(),
    {
        reveal(IommuTable::map_4k_page_eof_transition_framing);
        assert(post.wf_l2()) by { reveal(IommuTable::wf_l2); };
    }

    /// EOF closure of `map_4k_page`: `wf_l1`.
    proof fn map_4k_page_eof_wf_l1(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            iova_4k_valid(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            !target_entry.is_io,
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.wf_l1(),
    {
        reveal(IommuTable::map_4k_page_eof_transition_framing);
        assert(post.wf_l1()) by { reveal(IommuTable::wf_l1); };
    }

    /// EOF closure of `map_4k_page`: `disjoint_l4`.
    proof fn map_4k_page_eof_disjoint_l4(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            iova_4k_valid(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            !target_entry.is_io,
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.disjoint_l4(),
    {
        reveal(IommuTable::map_4k_page_eof_transition_framing);
        assert(post.disjoint_l4()) by { reveal(IommuTable::disjoint_l4); };
    }

    /// EOF closure of `map_4k_page`: `disjoint_l3`.
    proof fn map_4k_page_eof_disjoint_l3(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            iova_4k_valid(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            !target_entry.is_io,
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.disjoint_l3(),
    {
        reveal(IommuTable::map_4k_page_eof_transition_framing);
        assert(post.disjoint_l3()) by { reveal(IommuTable::disjoint_l3); };
    }

    /// EOF closure of `map_4k_page`: `disjoint_l2`.
    proof fn map_4k_page_eof_disjoint_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            iova_4k_valid(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            !target_entry.is_io,
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.disjoint_l2(),
    {
        reveal(IommuTable::map_4k_page_eof_transition_framing);
        assert(post.disjoint_l2()) by { reveal(IommuTable::disjoint_l2); };
    }

    /// EOF closure of `map_4k_page`: `wf_mapping_4k`.
    proof fn map_4k_page_eof_wf_mapping_4k(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            iova_4k_valid(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            !target_entry.is_io,
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.wf_mapping_4k(),
    {
        reveal(IommuTable::map_4k_page_eof_transition_framing);
        assert(post.wf_mapping_4k()) by {
            reveal(IommuTable::wf_mapping_4k);
            reveal(IommuTable::wf_l4);
            reveal(IommuTable::wf_l3);
            reveal(IommuTable::wf_l2);
            assert(post.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) == Some(PageEntry { addr: target_entry.addr,
                perm: PageEntryPerm { is_io: target_entry.is_io, present: true, ps: false, write: target_entry.write, execute_disable: target_entry.execute_disable, user: false, kernel_present: true } })) by {
                pre.wf_l4_at(target_l4i);
            };
            spec_index2va_injective();
            post.resolve_l2_unchanged(&pre);
            broadcast use IommuTable::disjoint_l2_implies_resolve_l2_addr_unique_at;
        };
    }

    /// EOF closure of `map_4k_page`: `user_only`.
    proof fn map_4k_page_eof_user_only(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            iova_4k_valid(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            !target_entry.is_io,
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.user_only(),
    {
        reveal(IommuTable::map_4k_page_eof_transition_framing);
        assert(post.user_only()) by { reveal(IommuTable::user_only); };
    }

    /// EOF closure of `map_4k_page`: `rwx_upper_level_entries`.
    proof fn map_4k_page_eof_rwx_upper_level_entries(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            iova_4k_valid(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            !target_entry.is_io,
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.rwx_upper_level_entries(),
    {
        reveal(IommuTable::map_4k_page_eof_transition_framing);
        assert(post.rwx_upper_level_entries()) by { reveal(IommuTable::rwx_upper_level_entries); };
    }

    /// EOF closure of `map_4k_page`: `table_pages_wf`.
    proof fn map_4k_page_eof_table_pages_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            iova_4k_valid(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            !target_entry.is_io,
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.table_pages_wf(),
    {
        reveal(IommuTable::map_4k_page_eof_transition_framing);
        assert(post.table_pages_wf()) by { reveal(IommuTable::table_pages_wf); };
    }

    /// EOF closure of `map_4k_page`: `tables_reachable_wf`.
    proof fn map_4k_page_eof_tables_reachable_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            iova_4k_valid(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            !target_entry.is_io,
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.tables_reachable_wf(),
    {
        reveal(IommuTable::map_4k_page_eof_transition_framing);
        assert(post.tables_reachable_wf()) by { reveal(IommuTable::tables_reachable_wf); post.resolve_l2_unchanged(&pre); };
    }

    /// EOF closure of `map_4k_page`: `va_addr_valid` and `did_wf`.
    proof fn map_4k_page_eof_va_addr_valid_and_did_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            iova_4k_valid(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            !target_entry.is_io,
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.va_addr_valid(),
            post.did_wf(),
    {
        reveal(IommuTable::map_4k_page_eof_transition_framing);
    }
}
} // verus!
