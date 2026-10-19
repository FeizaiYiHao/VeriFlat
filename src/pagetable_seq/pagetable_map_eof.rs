use vstd::prelude::*;
verus! {
use crate::*;
use super::pagetable_spec::*;
use super::entry::*;

impl<const TABLE_TYPE: PTType> PageTable<TABLE_TYPE> {
    /// Operation-state summary of `map_4k_page`: entry `target_l1i` of the L1 map `target_l1_p` now maps `target_entry`
    /// and the kernel 4K mapping records it at that address; every other field is unchanged.
    #[verifier::opaque]
    pub open spec fn map_4k_page_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry) -> bool {
        &&& post == (Self { l1_tables: post.l1_tables, mapping_4k: post.mapping_4k, ..pre })
        &&& post.l1_tables.view().dom() == pre.l1_tables.view().dom()
        &&& forall|p: PageMapPtr| #![trigger post.l1_tables.view().spec_index(p)] pre.l1_tables.view().dom().contains(p) && p != target_l1_p ==> post.l1_tables.view().spec_index(p) == pre.l1_tables.view().spec_index(p)
        &&& post.l1_tables.view().spec_index(target_l1_p).addr() == target_l1_p
        &&& post.l1_tables.view().spec_index(target_l1_p).is_init()
        &&& post.l1_tables.view().spec_index(target_l1_p).value().wf()
        &&& forall|i: usize| #![trigger post.l1_tables.view().spec_index(target_l1_p).value().spec_index(i)] pei_valid(i) && i != target_l1i ==> post.l1_tables.view().spec_index(target_l1_p).value().spec_index(i) =~= pre.l1_tables.view().spec_index(target_l1_p).value().spec_index(i)
        &&& post.l1_tables.view().spec_index(target_l1_p).value().spec_index(target_l1i) =~= (PageEntry { addr: target_entry.addr,
            perm: PageEntryPerm { present: true, ps: false, write: target_entry.write, execute_disable: target_entry.execute_disable, user: true, kernel_present: true } })
        &&& post.mapping_4k() == pre.mapping_4k().insert(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)), target_entry)
    }

    /// EOF closure of `map_4k_page`: every page-table invariant leaf.
    pub(super) proof fn map_4k_page_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            page_table_key_4k_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
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
        Self::map_4k_page_eof_wf_mapping_2m(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_wf_mapping_1g(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_user_only(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_rwx_upper_level_entries(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_table_pages_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_tables_reachable_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_kernel_entries_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_va_addr_valid_and_pcid_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
    }

    /// EOF closure of `map_4k_page`: `wf_l4`.
    proof fn map_4k_page_eof_wf_l4(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            page_table_key_4k_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.wf_l4(),
    {
        reveal(PageTable::map_4k_page_eof_transition_framing);
        assert(post.wf_l4()) by { reveal(PageTable::wf_l4); };
    }

    /// EOF closure of `map_4k_page`: `wf_l3`.
    proof fn map_4k_page_eof_wf_l3(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            page_table_key_4k_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.wf_l3(),
    {
        reveal(PageTable::map_4k_page_eof_transition_framing);
        assert(post.wf_l3()) by { reveal(PageTable::wf_l3); };
    }

    /// EOF closure of `map_4k_page`: `wf_l2`.
    proof fn map_4k_page_eof_wf_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            page_table_key_4k_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.wf_l2(),
    {
        reveal(PageTable::map_4k_page_eof_transition_framing);
        assert(post.wf_l2()) by { reveal(PageTable::wf_l2); };
    }

    /// EOF closure of `map_4k_page`: `wf_l1`.
    proof fn map_4k_page_eof_wf_l1(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            page_table_key_4k_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.wf_l1(),
    {
        reveal(PageTable::map_4k_page_eof_transition_framing);
        assert(post.wf_l1()) by { reveal(PageTable::wf_l1); };
    }

    /// EOF closure of `map_4k_page`: `disjoint_l4`.
    proof fn map_4k_page_eof_disjoint_l4(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            page_table_key_4k_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.disjoint_l4(),
    {
        reveal(PageTable::map_4k_page_eof_transition_framing);
        assert(post.disjoint_l4()) by { reveal(PageTable::disjoint_l4); };
    }

    /// EOF closure of `map_4k_page`: `disjoint_l3`.
    proof fn map_4k_page_eof_disjoint_l3(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            page_table_key_4k_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.disjoint_l3(),
    {
        reveal(PageTable::map_4k_page_eof_transition_framing);
        assert(post.disjoint_l3()) by { reveal(PageTable::disjoint_l3); };
    }

    /// EOF closure of `map_4k_page`: `disjoint_l2`.
    proof fn map_4k_page_eof_disjoint_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            page_table_key_4k_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.disjoint_l2(),
    {
        reveal(PageTable::map_4k_page_eof_transition_framing);
        assert(post.disjoint_l2()) by { reveal(PageTable::disjoint_l2); };
    }

    /// EOF closure of `map_4k_page`: `wf_mapping_4k`.
    proof fn map_4k_page_eof_wf_mapping_4k(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            page_table_key_4k_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.wf_mapping_4k(),
    {
        reveal(PageTable::map_4k_page_eof_transition_framing);
        assert(post.wf_mapping_4k()) by {
            reveal(PageTable::wf_mapping_4k);
            reveal(PageTable::wf_l4);
            reveal(PageTable::wf_l3);
            reveal(PageTable::wf_l2);
            assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L2Index| #![trigger post.mapping_4k.view().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                #![trigger pre.mapping_4k.view().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))]
                post.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (target_l4i, target_l3i, target_l2i, target_l1i) != (l4i, l3i, l2i, l1i)
                ==> post.mapping_4k.view().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))) == pre.mapping_4k.view().dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))) by { spec_index2va_injective(); };
            assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_resolve_mapping_l2(l4i, l3i, l2i)] #![trigger pre.spec_resolve_mapping_l2(l4i, l3i, l2i)]
                post.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (target_l4i, target_l3i, target_l2i) != (l4i, l3i, l2i)
                ==> post.spec_resolve_mapping_l2(l4i, l3i, l2i) == pre.spec_resolve_mapping_l2(l4i, l3i, l2i)) by { post.resolve_l2_unchanged(&pre); };
            assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_resolve_mapping_l2(l4i,l3i,l2i)]
                post.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && post.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some && !((target_l4i,target_l3i,target_l2i,) =~= (l4i, l3i, l2i))
                ==> post.spec_resolve_mapping_l2(l4i,l3i,l2i)->0.addr != target_l1_p) by { broadcast use PageTable::resolve_l2_addr_unique_at; };
        };
    }

    /// EOF closure of `map_4k_page`: `wf_mapping_2m`.
    proof fn map_4k_page_eof_wf_mapping_2m(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            page_table_key_4k_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.wf_mapping_2m(),
    {
        reveal(PageTable::map_4k_page_eof_transition_framing);
        assert(post.wf_mapping_2m()) by { reveal(PageTable::wf_mapping_2m); };
    }

    /// EOF closure of `map_4k_page`: `wf_mapping_1g`.
    proof fn map_4k_page_eof_wf_mapping_1g(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            page_table_key_4k_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.wf_mapping_1g(),
    {
        reveal(PageTable::map_4k_page_eof_transition_framing);
        assert(post.wf_mapping_1g()) by { reveal(PageTable::wf_mapping_1g); };
    }

    /// EOF closure of `map_4k_page`: `user_only`.
    proof fn map_4k_page_eof_user_only(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            page_table_key_4k_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.user_only(),
    {
        reveal(PageTable::map_4k_page_eof_transition_framing);
        assert(post.user_only()) by { reveal(PageTable::user_only); };
    }

    /// EOF closure of `map_4k_page`: `rwx_upper_level_entries`.
    proof fn map_4k_page_eof_rwx_upper_level_entries(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            page_table_key_4k_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.rwx_upper_level_entries(),
    {
        reveal(PageTable::map_4k_page_eof_transition_framing);
        assert(post.rwx_upper_level_entries()) by { reveal(PageTable::rwx_upper_level_entries); };
    }

    /// EOF closure of `map_4k_page`: `table_pages_wf`.
    proof fn map_4k_page_eof_table_pages_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            page_table_key_4k_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.table_pages_wf(),
    {
        reveal(PageTable::map_4k_page_eof_transition_framing);
        assert(post.table_pages_wf()) by { reveal(PageTable::table_pages_wf); };
    }

    /// EOF closure of `map_4k_page`: `tables_reachable_wf`.
    proof fn map_4k_page_eof_tables_reachable_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            page_table_key_4k_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.tables_reachable_wf(),
    {
        reveal(PageTable::map_4k_page_eof_transition_framing);
        assert(post.tables_reachable_wf()) by { reveal(PageTable::tables_reachable_wf); post.resolve_l2_unchanged(&pre); };
    }

    /// EOF closure of `map_4k_page`: `kernel_entries_wf`.
    proof fn map_4k_page_eof_kernel_entries_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            page_table_key_4k_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.kernel_entries_wf(),
    {
        reveal(PageTable::map_4k_page_eof_transition_framing);
        assert(post.kernel_entries_wf()) by { reveal(PageTable::kernel_entries_wf); };
    }

    /// EOF closure of `map_4k_page`: `va_addr_valid` and `pcid_wf`.
    proof fn map_4k_page_eof_va_addr_valid_and_pcid_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            page_table_key_4k_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == false,
            page_ptr_valid(target_entry.addr),
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.va_addr_valid(),
            post.pcid_wf(),
    {
        reveal(PageTable::map_4k_page_eof_transition_framing);
    }
}
} // verus!
